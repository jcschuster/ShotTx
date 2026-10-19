defmodule ShotTx.Prover.ContradictionAgent do
  @moduledoc """
  GenServer that detects global closure and extracts countermodels.

  Subscribes as a *peer of `SuggestionAgent`* to the shared
  `branch_evidence_<session>` PubSub topic. Workers publish every branch
  lifecycle event (`:branch_split`, `:branch_closed`, `:branch_saturated`,
  `:local_clashes`) once; both agents receive them independently. Manager
  commands (`:settle`, `:verify_all_closed`, `:verify_csa`) still arrive
  as direct `GenServer.call`/`cast` since they are coordination, not
  evidence.

  Two stores are maintained:

    * `branch_closures` — branches discharged by ground contradiction. A closed
      branch is dropped from `active_branches` immediately and its closure is
      retained only for proof reconstruction.
    * `clashing_local_pairs` — unifiable literal pairs from still-open
      branches, indexed by branch id and inherited by descendant branches.

  Closure is detected through three coordinated triggers, all funneling into
  `find_global_closure/3`:

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

  ## Out-of-order tolerance

  Losing the sync worker→CA edge means BEAM's cross-sender ordering
  guarantee no longer serializes lifecycle events. In particular, a
  `:branch_closed` for a child may arrive before its parent's
  `:branch_split`. The split handler defensively excludes any child
  already present in `branch_closures`; the closure handler tolerates
  branches it has never seen as active (they get recorded as closures
  and are then filtered out if the split arrives later).
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
            settle_waiter: nil,
            deadline_us: nil,
            # Bumped by every piece of branch evidence. `search_version` records
            # the value a dispatched CSP was built from, so a search that
            # answers "no closure" from a snapshot older than the current
            # evidence can be recognised as stale.
            evidence_version: 0,
            search_version: 0

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
    Registry.register(ShotTx.Prover.PubSub, "branch_evidence_#{session_id}", [])

    ets_tables = EtsKeeper.get_tables(session_id)
    active_branches = MapSet.new(["root"])
    Stats.record_max(ets_tables, :active_branches_max, 1)
    Stats.incr(ets_tables, :branches_activated_total)

    {:ok,
     %__MODULE__{
       session_id: session_id,
       params: params,
       ets_tables: ets_tables,
       active_branches: active_branches,
       deadline_us: proof_deadline_us(ets_tables, params)
     }}
  end

  # Same deadline as the manager, from the session start stamped by `EtsKeeper`.
  defp proof_deadline_us(ets_tables, %Parameters{timeout: timeout}) do
    case :ets.lookup(ets_tables.stats, :proof_started_at_us) do
      [{_key, started_us}] -> started_us + timeout * 1000
      [] -> System.monotonic_time(:microsecond) + timeout * 1000
    end
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

  defp aborted?(state) do
    case Map.get(state.ets_tables, :stats) do
      nil -> true
      t -> :ets.lookup(t, :aborted) == [{:aborted, true}]
    end
  end

  # --- CALL CALLBACKS ---------------------------------------------------------

  # With global closure disabled, settle answers `:open` at once.
  defp do_settle(_from, %{params: %Parameters{contradiction_agent: false}} = state) do
    Stats.incr(state.ets_tables, :csp_calls_skipped)
    {:reply, :open, state}
  end

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

  # --- INFO CALLBACKS ---------------------------------------------------------
  #
  # Worker lifecycle events arrive via the `branch_evidence_<session>` topic.

  defp do_handle_info({:branch_split, parent_id, child_ids}, state) do
    # A child's `:branch_closed` may overtake this split; closed branches must
    # not re-enter `active_branches`.
    live_children = Enum.reject(child_ids, &Map.has_key?(state.branch_closures, &1))

    new_active =
      state.active_branches
      |> MapSet.delete(parent_id)
      |> MapSet.union(MapSet.new(live_children))

    Stats.record_max(state.ets_tables, :active_branches_max, MapSet.size(new_active))
    Stats.incr(state.ets_tables, :branches_activated_total, length(live_children))

    check_global_closure(record_evidence(%{state | active_branches: new_active}))
  end

  defp do_handle_info({:branch_closed, branch_id}, state) do
    state
    |> record_branch_closure(branch_id)
    |> react_to_closure()
    |> then(&{:noreply, &1})
  end

  defp do_handle_info({:branch_saturated, branch_id, {model_defs, model_atoms}}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)

    # A saturated branch is only a countermodel if nothing recorded against it
    # (clash candidates included) can still close it — same filter as
    # `csa_or_unknown/2`.
    if closable?(branch_id, state) do
      {:noreply, %{state | active_branches: new_active}}
    else
      send_proof_result({:sat, model(branch_id, model_defs, model_atoms, state)}, state)
      {:noreply, %{state | active_branches: new_active}}
    end
  end

  defp do_handle_info({:local_clashes, branch_id, new_candidates}, state) do
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

    check_global_closure(record_evidence(%{state | clashing_local_pairs: updated_local_clashes}))
  end

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
    cleared = %{state | pending_search: nil}

    # Evidence that arrived during the search was not searched yet; rerun once
    # before answering `:open`. Bounded: with a waiter, all workers are idle.
    if waiter != nil and stale_search?(cleared) do
      redispatch_for_waiter(cleared)
    else
      if waiter != nil, do: GenServer.reply(waiter, :open)
      {:noreply, %{cleared | settle_waiter: nil}}
    end
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

  defp record_evidence(state), do: %{state | evidence_version: state.evidence_version + 1}

  defp stale_search?(state), do: state.evidence_version != state.search_version

  defp redispatch_for_waiter(state) do
    option_lists = option_lists_for(state.active_branches, state)

    if insufficient_options?(option_lists) do
      Stats.incr(state.ets_tables, :csp_calls_skipped)
      GenServer.reply(state.settle_waiter, :open)
      {:noreply, %{state | settle_waiter: nil}}
    else
      dispatch_csp(state, option_lists)
    end
  end

  # ---- CAST CALLBACKS ----

  defp do_handle_cast({:verify_csa, saturated_branch_map}, state) do
    saturated = Map.keys(saturated_branch_map)
    all_saturated? = Enum.all?(state.active_branches, &(&1 in saturated))

    global_closure_result =
      if state.params.contradiction_agent do
        branches_to_check =
          state.active_branches
          |> MapSet.to_list()
          |> Kernel.++(saturated)
          |> Enum.uniq()

        try_close_sync(option_lists_for(branches_to_check, state), state)
      else
        :error
      end

    case global_closure_result do
      {:ok, solution} ->
        broadcast_unsat(solution, state)

      :error ->
        case csa_or_unknown(saturated_branch_map, state) do
          {:sat, results} ->
            send_proof_result({:sat, results}, state)

          unknown ->
            # The manager must always hear back, or deepening stalls.
            if all_saturated?,
              do: send_proof_result(unknown, state),
              else: notify_manager(:csa_undecided, state)
        end
    end

    {:noreply, state}
  end

  # Every branch has either closed or run out of rules without being provably
  # satisfiable. One last global closure attempt, then `:unknown` — never
  # `:sat`, since no branch here is certified as a model.
  defp do_handle_cast(:verify_exhausted, state) do
    closure =
      if state.params.contradiction_agent do
        try_close_sync(option_lists_for(state.active_branches, state), state)
      else
        :error
      end

    case closure do
      {:ok, solution} -> broadcast_unsat(solution, state)
      :error -> send_proof_result({:unknown, :exhausted_without_model}, state)
    end

    {:noreply, state}
  end

  defp do_handle_cast(:verify_all_closed, state) do
    cond do
      MapSet.size(state.active_branches) == 0 ->
        broadcast_unsat(%UnifSolution{}, state)

      not state.params.contradiction_agent ->
        # Local ground closures did not clear all branches and global closure
        # is disabled — the proof is undecidable at this configuration.
        send_proof_result({:unknown, :contradiction_agent_disabled}, state)
        {:noreply, state}

      true ->
        check_global_closure(state)
    end
  end

  defp do_handle_cast(_event, state) do
    {:noreply, state}
  end

  defp csa_or_unknown(saturated_branch_map, state) do
    saturated_branch_map
    |> Map.keys()
    |> Enum.reject(&closable?(&1, state))
    |> case do
      [model_branch_id | _] ->
        {model_defs, model_atoms} = Map.fetch!(saturated_branch_map, model_branch_id)
        {:sat, model(model_branch_id, model_defs, model_atoms, state)}

      [] ->
        {:unknown, :conflicting_substitutions}
    end
  end

  # Anything recorded against this branch (or an ancestor) that could still
  # discharge it: a closure, or a unifiable literal pair the CSP may yet solve.
  defp closable?(branch_id, state) do
    not Enum.empty?(get_inherited_closures(branch_id, state)) or
      not Enum.empty?(get_inherited_clashes(branch_id, state))
  end

  defp model(branch_id, model_defs, model_atoms, state) do
    traces = read_traces(state)

    %{
      model_branch_id: branch_id,
      model_atoms: model_atoms,
      model_defs: model_defs,
      model_trace: Map.get(traces, branch_id, []),
      closed_traces: Map.delete(traces, branch_id)
    }
  end

  defp check_global_closure(%__MODULE__{pending_search: %Task{}} = state) do
    # One search at a time; checks arriving meanwhile are dropped (and counted).
    Stats.incr(state.ets_tables, :csp_calls_inflight_suppressed)
    {:noreply, state}
  end

  defp check_global_closure(%__MODULE__{params: %Parameters{contradiction_agent: false}} = state) do
    # Ablation: no CSP; ground closures still work.
    {:noreply, state}
  end

  defp check_global_closure(%__MODULE__{} = state) do
    # No active branches is transient here; `:verify_all_closed` confirms closure.
    if MapSet.size(state.active_branches) == 0 do
      {:noreply, state}
    else
      option_lists = option_lists_for(state.active_branches, state)

      if insufficient_options?(option_lists) do
        Stats.incr(state.ets_tables, :csp_calls_skipped)
        {:noreply, state}
      else
        Logger.debug(fn ->
          "Dispatching CSP. Branches: #{inspect(MapSet.to_list(state.active_branches))}. " <>
            "Candidates: #{inspect(Enum.map(option_lists, &length/1))}"
        end)

        dispatch_csp(state, option_lists)
      end
    end
  end

  defp dispatch_csp(state, option_lists) do
    task_sup_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :task_supervisor}}}

    tables = state.ets_tables
    depth = state.params.unification_depth
    deadline_us = state.deadline_us

    task =
      Task.Supervisor.async_nolink(task_sup_via, fn ->
        record_csp_dispatch(tables, option_lists)
        t0 = System.monotonic_time(:microsecond)

        result =
          case find_global_closure(option_lists, depth, deadline_us) do
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

    {:noreply, %{state | pending_search: task, search_version: state.evidence_version}}
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

  # Each open branch contributes options (lists of pairs to unify). The CSP
  # picks one option per branch and unifies their union.
  @typep option :: [{Term.term_id(), Term.term_id()}]

  # The product is exponential in the open branches, so the search stops at
  # the deadline with `:error` — incomplete, never unsound.
  @spec find_global_closure([[option()]], non_neg_integer(), integer()) ::
          {:ok, UnifSolution.t()} | :error
  defp find_global_closure(option_lists, depth, deadline_us) do
    option_lists
    |> Enum.sort_by(&length/1)
    |> cartesian_product()
    |> Enum.reduce_while(:error, fn choice, no_closure ->
      if past_deadline?(deadline_us) do
        {:halt, no_closure}
      else
        case ShotUn.unify(Enum.concat(choice), depth) |> Enum.take(1) do
          [sol] ->
            Logger.debug("CSP succeeded with: #{inspect(sol.substitutions)}")
            {:halt, {:ok, sol}}

          [] ->
            {:cont, no_closure}
        end
      end
    end)
  end

  defp past_deadline?(deadline_us), do: System.monotonic_time(:microsecond) >= deadline_us

  defp try_close_sync(option_lists, %__MODULE__{} = state) do
    if insufficient_options?(option_lists) do
      Stats.incr(state.ets_tables, :csp_calls_skipped)
      :error
    else
      record_csp_dispatch(state.ets_tables, option_lists)
      t0 = System.monotonic_time(:microsecond)

      result =
        case find_global_closure(option_lists, state.params.unification_depth, state.deadline_us) do
          {:ok, _} = ok ->
            Stats.incr(state.ets_tables, :csp_calls_succeeded)
            ok

          :error ->
            Stats.incr(state.ets_tables, :csp_calls_failed)
            :error
        end

      Stats.record_sample(
        state.ets_tables,
        :csp_duration_us,
        System.monotonic_time(:microsecond) - t0
      )

      result
    end
  end

  # Insufficient: some active branch has no way to close. (No branches at all
  # is fine — the CSP trivially succeeds.)
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

  # Records a branch's closure substitution and drops it from the CSP.
  defp record_branch_closure(state, branch_id, solution \\ %UnifSolution{}) do
    new_closures =
      Map.update(state.branch_closures, branch_id, [solution], &[solution | &1])

    %{
      state
      | branch_closures: new_closures,
        active_branches: MapSet.delete(state.active_branches, branch_id)
    }
  end

  # After a closure: if no branch is left the tableau is closed, otherwise
  # retry the CSP on the rest.
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

  # A branch's options: the clash pairs it or any ancestor observed.
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

    notify_manager({:proof_result, result}, state)
  end

  defp notify_manager(message, state) do
    manager_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :manager}}}

    GenServer.cast(manager_via, message)
  end
end
