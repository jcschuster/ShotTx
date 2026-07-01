defmodule ShotTx.Prover.ContradictionAgent do
  @moduledoc """
  GenServer that detects global closure and extracts countermodels.

  Subscribes to `local_closures_<session>` and `branch_events_<session>` PubSub
  channels and maintains two stores:

    * `branch_closures` — branches discharged by ground contradiction. A closed
      branch is dropped from `active_branches` immediately and its closure is
      retained only for proof reconstruction.
    * `clashing_local_pairs` — unifiable literal pairs from still-open
      branches, indexed by branch id and inherited by descendant branches.

  Closure is detected through three coordinated triggers, all funneling into
  `find_global_closure/2`:

    * `check_global_closure` — eager, async via `dispatch_csp`. Runs after
      every clash or split as long as no other search is in flight.
    * `:settle` — sync call from the manager when workers stall but branches
      are still parked. Reuses the eager path and replies once the task
      completes via `settle_waiter`.
    * `:verify_all_closed` / `:verify_csa` — manager-coordinated settle points
      when no work remains. The former short-circuits to `:unsat` when every
      branch has already closed; the latter falls back to SAT/`:unknown` if
      the CSP cannot find a global unifier.

  Closures and clashes are kept disjoint by construction: once a branch is in
  `branch_closures` it is no longer in `active_branches`, so the CSP only sees
  open branches' rigid-unification options.
  """

  use GenServer
  require Logger

  alias ShotTx.Prover.EtsKeeper
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Stats
  alias ShotDs.Data.Term
  alias ShotUn
  alias ShotUn.UnifSolution

  # State tracking
  defstruct session_id: nil,
            ets_tables: %{},
            active_branches: MapSet.new(),
            clashing_local_pairs: %{},
            branch_closures: %{},
            params: %Parameters{},
            pending_search: nil,
            settle_waiter: nil

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  @doc "Starts the ContradictionAgent for the given session."
  @spec start_link({String.t(), Parameters.t()}) :: GenServer.on_start()
  def start_link({session_id, params}) do
    name = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :ca}}}

    GenServer.start_link(__MODULE__, {session_id, params}, name: name)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init({session_id, params}) do
    Registry.register(ShotTx.Prover.PubSub, "local_closures_#{session_id}", [])
    Registry.register(ShotTx.Prover.PubSub, "branch_events_#{session_id}", [])

    ets_tables = EtsKeeper.get_tables(session_id)
    active_branches = MapSet.new(["root"])
    Stats.record_max(ets_tables, :active_branches_max, 1)
    Stats.incr(ets_tables, :branches_activated_total)

    {:ok,
     %__MODULE__{
       session_id: session_id,
       params: params,
       ets_tables: ets_tables,
       active_branches: active_branches
     }}
  end

  @impl true
  def handle_info(event, state) do
    if aborted?(state) do
      {:noreply, cancel_pending_search(state)}
    else
      do_handle_info(event, state)
    end
  end

  @impl true
  def handle_cast(event, state) do
    if aborted?(state) do
      {:noreply, cancel_pending_search(state)}
    else
      do_handle_cast(event, state)
    end
  end

  @impl true
  def handle_call(:settle, from, state) do
    if aborted?(state) do
      {:reply, :closed, cancel_pending_search(state)}
    else
      do_settle(from, state)
    end
  end

  @impl true
  def handle_call(event, from, state) do
    if aborted?(state) do
      {:reply, :aborted, cancel_pending_search(state)}
    else
      do_handle_call(event, from, state)
    end
  end

  defp aborted?(state) do
    case Map.get(state.ets_tables, :stats) do
      nil -> true
      t -> :ets.lookup(t, :aborted) == [{:aborted, true}]
    end
  end

  # --- CALL CALLBACKS ---------------------------------------------------------

  defp do_settle(from, %{pending_search: nil} = state) do
    option_lists = option_lists_for(state.active_branches, state)

    if insufficient_options?(option_lists) do
      Stats.incr(state.ets_tables, :csp_calls_skipped)
      {:reply, :open, state}
    else
      {:noreply, new_state} = dispatch_csp(state, option_lists)
      {:noreply, %{new_state | settle_waiter: from}}
    end
  end

  defp do_settle(from, state) do
    {:noreply, %{state | settle_waiter: from}}
  end

  defp do_handle_call({:closed, branch_id}, _from, state) do
    new_state = record_branch_closure(state, branch_id)
    {:reply, :ok, react_to_closure(new_state)}
  end

  defp do_handle_call(req, _from, state)
       when elem(req, 0) in [:branch_closed, :branch_split] do
    do_handle_sync(req, state)
  end

  # --- Synchronous Callbacks --------------------------------------------------

  defp do_handle_sync({:branch_split, parent_id, child_ids}, state) do
    new_active =
      state.active_branches
      |> MapSet.delete(parent_id)
      |> MapSet.union(MapSet.new(child_ids))

    Stats.record_max(state.ets_tables, :active_branches_max, MapSet.size(new_active))
    Stats.incr(state.ets_tables, :branches_activated_total, length(child_ids))

    new_state = %{state | active_branches: new_active}
    {:noreply, after_check} = check_global_closure(new_state)
    {:reply, :ok, after_check}
  end

  defp do_handle_sync({:branch_closed, branch_id}, state) do
    new_state = record_branch_closure(state, branch_id)
    {:reply, :ok, react_to_closure(new_state)}
  end

  # --- INFO CALLBACKS ---------------------------------------------------------

  defp do_handle_info(
         {ref, {:closure, solution}},
         %{pending_search: %Task{ref: ref}, settle_waiter: waiter} = state
       ) do
    Process.demonitor(ref, [:flush])
    cleared = %{state | pending_search: nil, settle_waiter: nil}
    broadcast_unsat(solution, cleared)

    if waiter != nil do
      GenServer.reply(waiter, :closed)
    end

    {:noreply, cleared}
  end

  defp do_handle_info(
         {ref, :no_closure},
         %{pending_search: %Task{ref: ref}, settle_waiter: waiter} = state
       ) do
    Process.demonitor(ref, [:flush])

    if waiter != nil do
      GenServer.reply(waiter, :open)
    end

    {:noreply, %{state | pending_search: nil, settle_waiter: nil}}
  end

  defp do_handle_info(
         {:DOWN, ref, :process, _pid, _reason},
         %{pending_search: %Task{ref: ref}, settle_waiter: waiter} = state
       ) do
    if waiter != nil do
      GenServer.reply(waiter, :open)
    end

    {:noreply, %{state | pending_search: nil, settle_waiter: nil}}
  end

  defp do_handle_info(_event, state) do
    {:noreply, state}
  end

  # ---- CAST CALLBACKS ----

  defp do_handle_cast({:verify_csa, saturated_branch_map}, state) do
    saturated = Map.keys(saturated_branch_map)
    all_saturated? = Enum.all?(state.active_branches, &(&1 in saturated))

    branches_to_check =
      state.active_branches
      |> MapSet.to_list()
      |> Kernel.++(saturated)
      |> Enum.uniq()

    option_lists = option_lists_for(branches_to_check, state)

    case try_close_sync(option_lists, state) do
      {:ok, solution} ->
        broadcast_unsat(solution, state)

      :error ->
        case csa_or_unknown(saturated_branch_map, state) do
          {:sat, results} -> send_proof_result({:sat, results}, state)
          unknown -> if all_saturated?, do: send_proof_result(unknown, state)
        end
    end

    {:noreply, state}
  end

  defp do_handle_cast(:verify_all_closed, state) do
    if MapSet.size(state.active_branches) == 0 do
      broadcast_unsat(%UnifSolution{}, state)
    else
      check_global_closure(state)
    end
  end

  defp do_handle_cast({:branch_saturated, branch_id, {model_defs, model_atoms}}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)
    traces = read_traces(state)

    results = %{
      model_branch_id: branch_id,
      model_atoms: model_atoms,
      model_defs: model_defs,
      model_trace: Map.get(traces, branch_id, []),
      closed_traces: Map.delete(traces, branch_id)
    }

    send_proof_result({:sat, results}, state)
    {:noreply, %{state | active_branches: new_active}}
  end

  defp do_handle_cast({:local_clashes, branch_id, new_candidates}, %__MODULE__{} = state) do
    Logger.debug(
      "Agent received #{MapSet.size(new_candidates)} new candidates for local closure from #{branch_id}"
    )

    updated_local_clashes =
      Map.update(
        state.clashing_local_pairs,
        branch_id,
        new_candidates,
        &MapSet.union(&1, new_candidates)
      )

    new_state = %{state | clashing_local_pairs: updated_local_clashes}

    check_global_closure(new_state)
  end

  defp do_handle_cast(_event, state) do
    {:noreply, state}
  end

  defp csa_or_unknown(saturated_branch_map, state) do
    open_branches =
      saturated_branch_map
      |> Map.keys()
      |> Enum.filter(fn b_id ->
        Enum.empty?(get_inherited_closures(b_id, state)) and
          Enum.empty?(get_inherited_clashes(b_id, state))
      end)

    case open_branches do
      [model_branch_id | _] ->
        {model_defs, model_atoms} = Map.fetch!(saturated_branch_map, model_branch_id)
        traces = read_traces(state)

        results = %{
          model_branch_id: model_branch_id,
          model_atoms: model_atoms,
          model_defs: model_defs,
          model_trace: Map.get(traces, model_branch_id, []),
          closed_traces: Map.delete(traces, model_branch_id)
        }

        {:sat, results}

      [] ->
        {:unknown, :conflicting_substitutions}
    end
  end

  defp check_global_closure(%__MODULE__{pending_search: %Task{}} = state) do
    {:noreply, state}
  end

  defp check_global_closure(%__MODULE__{} = state) do
    cond do
      # Empty `active_branches` is a transient eager-path event — the last open
      # branch just closed, but other workers may still be mid-step. The
      # manager's `:verify_all_closed` cast is the authoritative settle point;
      # let it confirm closure rather than racing it from here.
      MapSet.size(state.active_branches) == 0 ->
        {:noreply, state}

      true ->
        option_lists = option_lists_for(state.active_branches, state)

        if insufficient_options?(option_lists) do
          Stats.incr(state.ets_tables, :csp_calls_skipped)
          {:noreply, state}
        else
          Logger.warning(
            "Dispatching CSP. Branches: #{inspect(MapSet.to_list(state.active_branches))}. " <>
              "Candidates: #{inspect(Enum.map(option_lists, &length/1))}"
          )

          dispatch_csp(state, option_lists)
        end
    end
  end

  defp dispatch_csp(state, option_lists) do
    task_sup_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :task_supervisor}}}

    tables = state.ets_tables
    depth = state.params.unification_depth

    task =
      Task.Supervisor.async_nolink(task_sup_via, fn ->
        record_csp_dispatch(tables, option_lists)
        t0 = System.monotonic_time(:microsecond)

        result =
          case find_global_closure(option_lists, depth) do
            {:ok, solution} ->
              Stats.incr(tables, :csp_calls_succeeded)
              {:closure, solution}

            :error ->
              Stats.incr(tables, :csp_calls_failed)
              :no_closure
          end

        Stats.record_sample(tables, :csp_duration_us, System.monotonic_time(:microsecond) - t0)
        result
      end)

    {:noreply, %{state | pending_search: task}}
  end

  defp cancel_pending_search(%{pending_search: nil, settle_waiter: nil} = state), do: state

  defp cancel_pending_search(%{pending_search: nil, settle_waiter: waiter} = state) do
    GenServer.reply(waiter, :closed)
    %{state | settle_waiter: nil}
  end

  defp cancel_pending_search(%{pending_search: %Task{} = task, settle_waiter: waiter} = state) do
    Task.shutdown(task, :brutal_kill)
    if waiter != nil, do: GenServer.reply(waiter, :closed)
    %{state | pending_search: nil, settle_waiter: nil}
  end

  # Each branch contributes a list of *options*; each option is itself a list
  # of pairs to unify (currently always a single pair from `branch_options/2`).
  # The CSP picks one option per branch, concatenates the selected pairs, and
  # tries `ShotUn.unify/2`. Branches already discharged by ground closure are
  # absent from `active_branches` and therefore never appear in `option_lists`.
  @typep option :: [{Term.term_id(), Term.term_id()}]

  @spec find_global_closure([[option()]], non_neg_integer()) ::
          {:ok, UnifSolution.t()} | :error
  defp find_global_closure(option_lists, depth) do
    option_lists
    |> Enum.sort_by(&length/1)
    |> cartesian_product()
    |> Enum.find_value(:error, fn choice ->
      case ShotUn.unify(Enum.concat(choice), depth) |> Enum.take(1) do
        [sol] ->
          Logger.debug("CSP succeeded with: #{inspect(sol.substitutions)}")
          {:ok, sol}

        [] ->
          nil
      end
    end)
  end

  defp try_close_sync(option_lists, %__MODULE__{} = state) do
    if insufficient_options?(option_lists) do
      Stats.incr(state.ets_tables, :csp_calls_skipped)
      :error
    else
      record_csp_dispatch(state.ets_tables, option_lists)
      t0 = System.monotonic_time(:microsecond)

      result =
        case find_global_closure(option_lists, state.params.unification_depth) do
          {:ok, _} = ok ->
            Stats.incr(state.ets_tables, :csp_calls_succeeded)
            ok

          :error ->
            Stats.incr(state.ets_tables, :csp_calls_failed)
            :error
        end

      Stats.record_sample(state.ets_tables, :csp_duration_us, System.monotonic_time(:microsecond) - t0)
      result
    end
  end

  # An empty `option_lists` (no active branches left) is **not** insufficient —
  # it means every branch has already discharged itself and the CSP trivially
  # succeeds with the empty substitution. Insufficiency means some active
  # branch has no way to close.
  defp insufficient_options?(option_lists) do
    Enum.any?(option_lists, &Enum.empty?/1)
  end

  defp record_csp_dispatch(tables, option_lists) do
    domain_sizes = Enum.map(option_lists, &length/1)
    Stats.incr(tables, :csp_calls)
    Stats.record_sample(tables, :csp_branches_count, length(domain_sizes))
    Stats.record_sample(tables, :csp_max_domain_size, Enum.max(domain_sizes, fn -> 0 end))
    Stats.record_sample(tables, :csp_total_candidates, Enum.sum(domain_sizes))
  end

  defp cartesian_product([]), do: [[]]

  defp cartesian_product([list | rest]) do
    rest_stream = cartesian_product(rest)

    Stream.flat_map(list, fn item ->
      Stream.map(rest_stream, fn sub -> [item | sub] end)
    end)
  end

  ##############################################################################
  # SHARED HELPERS
  ##############################################################################

  # Removes a closed branch from `active_branches` and records its (possibly
  # non-empty) closure substitution. Closed branches no longer constrain the
  # global CSP — keeping them in `active_branches` would force the CSP to pick
  # a dummy option for each, inflating the cartesian product unnecessarily.
  defp record_branch_closure(state, branch_id, solution \\ %UnifSolution{}) do
    new_closures =
      Map.update(state.branch_closures, branch_id, [solution], &[solution | &1])

    %{
      state
      | branch_closures: new_closures,
        active_branches: MapSet.delete(state.active_branches, branch_id)
    }
  end

  # Drains the closure side-effects after a `record_branch_closure/3`. If the
  # closure emptied `active_branches`, every leaf has discharged itself — the
  # tableau is closed under the empty substitution and we can broadcast `:unsat`
  # immediately. Otherwise we re-run the eager CSP, since removing a branch may
  # have unblocked the remaining constraints.
  defp react_to_closure(%__MODULE__{active_branches: active} = state) do
    if MapSet.size(active) == 0 do
      {:noreply, broadcast_state} = broadcast_unsat(%UnifSolution{}, state)
      broadcast_state
    else
      {:noreply, after_check} = check_global_closure(state)
      after_check
    end
  end

  defp option_lists_for(branches, %__MODULE__{} = state) do
    Enum.map(branches, &branch_options(&1, state))
  end

  # A branch's options are the unifiable clash pairs it (or any ancestor)
  # observed. Ground closures are tracked separately via `branch_closures` and
  # discharge the branch from `active_branches` outright, so they need no
  # representation here. If a still-active branch has no clashes, it cannot be
  # closed under the current state and the caller skips the CSP entirely.
  defp branch_options(branch_id, %__MODULE__{} = state) do
    branch_id
    |> get_inherited_clashes(state)
    |> Enum.map(&[&1])
  end

  defp get_inherited_clashes(branch_id, %__MODULE__{} = state) do
    prefixes =
      branch_id
      |> String.split("_")
      |> Enum.scan(&(&2 <> "_" <> &1))

    for prefix <- prefixes, reduce: MapSet.new() do
      acc -> Map.get(state.clashing_local_pairs, prefix, MapSet.new()) |> MapSet.union(acc)
    end
  end

  defp get_inherited_closures(branch_id, state) do
    segments = String.split(branch_id, "_")

    prefixes =
      Enum.scan(segments, fn segment, acc -> acc <> "_" <> segment end)

    prefixes
    |> Enum.flat_map(fn prefix -> Map.get(state.branch_closures, prefix, []) end)
    |> Enum.uniq()
  end

  defp broadcast_unsat(solution, state) do
    %UnifSolution{substitutions: final_substs, flex_pairs: flex} = solution

    final_map = Map.new(final_substs, fn s -> {s.fvar, s.term_id} end)

    Logger.warning("GLOBAL CLOSURE FOUND! Status: Theorem")

    send_proof_result({:unsat, final_map, flex, read_traces(state)}, state)

    {:noreply, state}
  end

  defp read_traces(%__MODULE__{ets_tables: %{traces: table}}) do
    Map.new(:ets.tab2list(table))
  end

  defp read_traces(_), do: %{}

  defp send_proof_result(result, state) do
    case Map.get(state.ets_tables, :stats) do
      nil -> :ok
      stats -> :ets.insert(stats, {:aborted, true})
    end

    manager_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :manager}}}

    GenServer.cast(manager_via, {:proof_result, result})
  end
end
