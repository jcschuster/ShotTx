defmodule ShotTx.Prover.ContradictionAgent do
  # GenServer, listens to PubSub and searches for closure
  use GenServer
  require Logger

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Stats
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn
  alias ShotUn.UnifSolution

  # State tracking
  defstruct session_id: nil,
            ets_tables: %{},
            active_branches: MapSet.new(),
            clashing_local_pairs: %{},
            branch_closures: %{},
            branch_traces: %{},
            params: %Parameters{},
            pending_search: nil,
            settle_waiter: nil

  ##############################################################################
  # PUBLIC API
  ##############################################################################

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
    {:ok, %__MODULE__{session_id: session_id, params: params}}
  end

  @impl true
  def handle_info(event, state) do
    if aborted?(state) do
      {:noreply, state}
    else
      do_handle_info(event, state)
    end
  end

  @impl true
  def handle_cast(event, state) do
    if aborted?(state) do
      {:noreply, state}
    else
      do_handle_cast(event, state)
    end
  end

  @impl true
  def handle_call(:settle, from, state) do
    case Map.get(state.ets_tables, :stats) do
      stats when not is_nil(stats) ->
        case :ets.lookup(stats, :aborted) do
          [{:aborted, true}] -> {:reply, :closed, state}
          _ -> do_settle(from, state)
        end

      _ ->
        do_settle(from, state)
    end
  end

  @impl true
  def handle_call(event, from, state) do
    if aborted?(state) do
      {:reply, :aborted, state}
    else
      do_handle_call(event, from, state)
    end
  end

  defp aborted?(state) do
    case Map.get(state.ets_tables, :stats) do
      nil -> false
      t -> :ets.lookup(t, :aborted) == [{:aborted, true}]
    end
  end

  # --- CALL CALLBACKS ---------------------------------------------------------

  defp do_settle(_from, %{pending_search: nil} = state) do
    case check_global_closure_sync(state) do
      {:ok, solution} ->
        broadcast_unsat(solution, state)
        {:reply, :closed, state}

      :error ->
        {:reply, :open, state}
    end
  end

  defp do_settle(from, state) do
    {:noreply, %{state | settle_waiter: from}}
  end

  defp do_handle_call({:local_clashes, branch_id, new_candidates, trace}, _from, state) do
    {:noreply, new_state} =
      do_handle_cast({:local_clashes, branch_id, new_candidates, trace}, state)

    {:reply, :ok, new_state}
  end

  defp do_handle_call({:closed, branch_id, trace}, _from, state) do
    new_traces = Map.put(state.branch_traces, branch_id, trace)

    new_closures =
      Map.update(state.branch_closures, branch_id, [%UnifSolution{}], fn existing ->
        [%UnifSolution{} | existing]
      end)

    new_state = %{state | branch_closures: new_closures, branch_traces: new_traces}

    {:noreply, new_check_state} = check_global_closure(new_state)
    {:reply, :ok, new_check_state}
  end

  defp do_handle_call(req, _from, state)
       when elem(req, 0) in [
              :branch_active,
              :branch_saturated,
              :branch_closed,
              :branch_split,
              :local_clashes_sync
            ] do
    do_handle_sync(req, state)
  end

  # --- Synchronous Callbacks --------------------------------------------------

  defp do_handle_sync({:branch_active, branch_id}, state) do
    new_active = MapSet.put(state.active_branches, branch_id)
    Stats.record_max(state.ets_tables, :active_branches_max, MapSet.size(new_active))
    Stats.incr(state.ets_tables, :branches_activated_total)
    {:reply, :ok, %{state | active_branches: new_active}}
  end

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

  defp do_handle_sync({:branch_closed, branch_id, trace}, state) do
    new_traces = Map.put(state.branch_traces, branch_id, trace)

    new_closures =
      Map.update(state.branch_closures, branch_id, [%UnifSolution{}], fn existing ->
        [%UnifSolution{} | existing]
      end)

    new_state = %{state | branch_closures: new_closures, branch_traces: new_traces}
    {:noreply, after_check} = check_global_closure(new_state)
    {:reply, :ok, after_check}
  end

  defp do_handle_sync(
         {:branch_saturated, branch_id, {model_defs, model_atoms, model_trace}},
         state
       ) do
    new_active = MapSet.delete(state.active_branches, branch_id)

    results = %{
      model_branch_id: branch_id,
      model_atoms: model_atoms,
      model_defs: model_defs,
      model_trace: model_trace,
      closed_traces: state.branch_traces
    }

    send_proof_result({:sat, results}, state)
    {:noreply, %{state | active_branches: new_active}}
  end

  defp do_handle_sync({:local_clashes_sync, branch_id, candidates, trace}, state) do
    Logger.debug(
      "Agent received #{MapSet.size(candidates)} new candidates for local closure from #{branch_id}"
    )

    updated_local_clashes =
      Map.update(state.clashing_local_pairs, branch_id, candidates, &MapSet.union(&1, candidates))

    updated_traces = Map.put(state.branch_traces, branch_id, trace)

    new_state = %{
      state
      | clashing_local_pairs: updated_local_clashes,
        branch_traces: updated_traces
    }

    {:noreply, after_check} = check_global_closure(new_state)
    {:reply, :ok, after_check}
  end

  # --- INFO CALLBACKS ---------------------------------------------------------

  defp do_handle_info(
         {ref, {:closure, solution}},
         %{pending_search: ref, settle_waiter: waiter} = state
       ) do
    Process.demonitor(ref, [:flush])
    broadcast_unsat(solution, state)

    if waiter != nil do
      GenServer.reply(waiter, :closed)
    end

    {:noreply, %{state | pending_search: nil, settle_waiter: nil}}
  end

  defp do_handle_info({ref, :no_closure}, %{pending_search: ref, settle_waiter: waiter} = state) do
    Process.demonitor(ref, [:flush])

    if waiter != nil do
      GenServer.reply(waiter, :open)
    end

    {:noreply, %{state | pending_search: nil, settle_waiter: nil}}
  end

  defp do_handle_info(_event, state) do
    {:noreply, state}
  end

  # ---- CAST CALLBACKS ----

  defp do_handle_cast({:set_ets_tables, tables}, state) do
    Logger.debug("ContradictionAgent received ETS tables.")
    {:noreply, %{state | ets_tables: tables}}
  end

  defp do_handle_cast({:verify_csa, saturated_branch_map}, state) do
    saturated = Map.keys(saturated_branch_map)

    branch_clash_lists =
      (MapSet.to_list(state.active_branches) ++ saturated)
      |> Enum.uniq()
      |> Enum.map(fn b_id -> get_inherited_clashes(b_id, state) |> Enum.to_list() end)

    all_saturated? = Enum.all?(for b <- state.active_branches, do: b in saturated)

    if Enum.any?(branch_clash_lists, &Enum.empty?/1) do
      case csa_or_unknown(saturated_branch_map, state) do
        {:sat, results} -> send_proof_result({:sat, results}, state)
        unknown -> if all_saturated?, do: send_proof_result(unknown, state)
      end
    else
      sorted = Enum.sort_by(branch_clash_lists, &length/1)

      case solve_groups(sorted, state.params.unification_depth) do
        {:ok, solution} ->
          broadcast_unsat(solution, state)

        :error ->
          case csa_or_unknown(saturated_branch_map, state) do
            {:sat, results} -> send_proof_result({:sat, results}, state)
            unknown -> if all_saturated?, do: send_proof_result(unknown, state)
          end
      end
    end

    {:noreply, state}
  end

  defp do_handle_cast(:verify_all_closed, state) do
    active_options_lists =
      state.active_branches
      |> Enum.map(fn b_id -> get_inherited_closures(b_id, state) end)

    case find_valid_combination(active_options_lists, state.params.unification_depth) do
      {:ok, %UnifSolution{substitutions: final_substs, flex_pairs: flex}} ->
        final_map = Map.new(final_substs, fn s -> {s.fvar, s.term_id} end)

        send_proof_result({:unsat, final_map, flex, state.branch_traces}, state)

      :error ->
        if Enum.empty?(state.active_branches) do
          Logger.warning(
            "All branches closed locally, but global unification failed. Returning UNK."
          )

          send_proof_result({:unknown, :conflicting_substitutions}, state)
        end
    end

    {:noreply, state}
  end

  defp do_handle_cast({:local_clashes, branch_id, new_candidates, trace}, %__MODULE__{} = state) do
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

    updated_traces = Map.put(state.branch_traces, branch_id, trace)

    new_state = %{
      state
      | clashing_local_pairs: updated_local_clashes,
        branch_traces: updated_traces
    }

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
        {model_defs, model_atoms, model_trace} = Map.fetch!(saturated_branch_map, model_branch_id)

        results = %{
          model_branch_id: model_branch_id,
          model_atoms: model_atoms,
          model_defs: model_defs,
          model_trace: model_trace,
          closed_traces: state.branch_traces
        }

        {:sat, results}

      [] ->
        {:unknown, :conflicting_substitutions}
    end
  end

  defp check_global_closure(%__MODULE__{} = state) do
    if state.pending_search != nil do
      {:noreply, state}
    else
      branch_clash_lists =
        Enum.map(state.active_branches, fn b_id ->
          get_inherited_clashes(b_id, state) |> Enum.to_list()
        end)

      if some_branch_cannot_close?(state, branch_clash_lists) do
        Stats.incr(state.ets_tables, :csp_calls_skipped)
        {:noreply, state}
      else
        Logger.warning(
          "Dispatching CSP. Branches: #{inspect(Enum.map(state.active_branches, & &1))}. " <>
            "Candidates: #{inspect(Enum.map(branch_clash_lists, &length/1))}"
        )

        dispatch_csp(state, branch_clash_lists)
      end
    end
  end

  defp check_global_closure_sync(state) do
    branch_clash_lists =
      Enum.map(state.active_branches, fn b_id ->
        get_inherited_clashes(b_id, state) |> Enum.to_list()
      end)

    if some_branch_cannot_close?(state, branch_clash_lists) do
      :error
    else
      sorted = Enum.sort_by(branch_clash_lists, &length/1)
      solve_groups(sorted, state.params.unification_depth)
    end
  end

  defp some_branch_cannot_close?(state, branch_clash_lists) do
    Enum.empty?(state.active_branches) || Enum.any?(branch_clash_lists, &Enum.empty?/1)
  end

  defp dispatch_csp(state, branch_clash_lists) do
    task_sup_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :task_supervisor}}}

    tables = state.ets_tables
    depth = state.params.unification_depth

    task =
      Task.Supervisor.async_nolink(task_sup_via, fn ->
        t0 = System.monotonic_time(:microsecond)
        Stats.incr(tables, :csp_calls)

        domain_sizes = Enum.map(branch_clash_lists, &length/1)
        Stats.record_sample(tables, :csp_branches_count, length(domain_sizes))
        Stats.record_sample(tables, :csp_max_domain_size, Enum.max(domain_sizes, fn -> 0 end))
        Stats.record_sample(tables, :csp_total_candidates, Enum.sum(domain_sizes))

        sorted = Enum.sort_by(branch_clash_lists, &length/1)

        result =
          case solve_groups(sorted, depth) do
            {:ok, solution} ->
              Stats.incr(tables, :csp_calls_succeeded)
              {:closure, solution}

            :error ->
              Stats.incr(tables, :csp_calls_failed)
              :no_closure
          end

        duration_us = System.monotonic_time(:microsecond) - t0
        Stats.record_sample(tables, :csp_duration_us, duration_us)
        result
      end)

    {:noreply, %{state | pending_search: task.ref}}
  end

  @spec solve_groups([[list()]], non_neg_integer()) :: {:ok, UnifSolution.t()} | :error
  defp solve_groups(branch_candidate_lists, depth) do
    branch_candidate_lists
    |> cartesian_product()
    |> Enum.find_value(:error, fn pair_choice ->
      Logger.debug("CSP trying #{length(pair_choice)} pairs: #{inspect(pair_choice)}")

      case ShotUn.unify(pair_choice, depth) |> Enum.take(1) do
        [sol] ->
          Logger.debug("CSP succeeded with: #{inspect(sol.substitutions)}")
          {:ok, sol}

        [] ->
          nil
      end
    end)
  end

  @spec find_valid_combination([[UnifSolution.t()]], non_neg_integer()) ::
          {:ok, UnifSolution.t()} | :error
  defp find_valid_combination(branch_solution_lists, depth) do
    branch_solution_lists
    |> cartesian_product()
    |> Enum.find_value(:error, fn solution_choice ->
      all_pairs =
        Enum.flat_map(solution_choice, fn %UnifSolution{substitutions: s, flex_pairs: f} ->
          Enum.map(s, fn sub -> {TF.make_term(sub.fvar), sub.term_id} end) ++ f
        end)

      case ShotUn.unify(all_pairs, depth) |> Enum.take(1) do
        [sol] -> {:ok, sol}
        [] -> nil
      end
    end)
  end

  defp cartesian_product([]), do: [[]]

  defp cartesian_product([list | rest]) do
    rest_products = cartesian_product(rest)
    for item <- list, sub <- rest_products, do: [item | sub]
  end

  ##############################################################################
  # SHARED HELPERS
  ##############################################################################

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

    send_proof_result({:unsat, final_map, flex, state.branch_traces}, state)

    {:noreply, state}
  end

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
