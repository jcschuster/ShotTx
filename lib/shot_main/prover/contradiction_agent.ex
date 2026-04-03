defmodule ShotMain.Prover.ContradictionAgent do
  # GenServer, listens to PubSub and searches for closure
  use GenServer
  require Logger

  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUnify
  alias ShotUnify.UnifSolution

  @unify_depth 10

  # State tracking
  defstruct session_id: nil,
            ets_tables: %{},
            active_branches: MapSet.new(),
            branch_closures: %{}

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  def start_link(session_id) do
    name = {:via, Registry, {ShotMain.Prover.ProcessRegistry, {session_id, :ca}}}
    GenServer.start_link(__MODULE__, session_id, name: name)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init(session_id) do
    Registry.register(ShotMain.Prover.PubSub, "local_closures_#{session_id}", [])
    Registry.register(ShotMain.Prover.PubSub, "branch_events_#{session_id}", [])
    {:ok, %__MODULE__{session_id: session_id}}
  end

  @impl true
  def handle_info(event, state) do
    stats_table = Map.get(state.ets_tables, :stats)

    if stats_table && :ets.lookup(stats_table, :aborted) == [{:aborted, true}] do
      {:noreply, state}
    else
      do_handle_info(event, state)
    end
  end

  @impl true
  def handle_cast(event, state) do
    stats_table = Map.get(state.ets_tables, :stats)

    if stats_table && :ets.lookup(stats_table, :aborted) == [{:aborted, true}] do
      {:noreply, state}
    else
      do_handle_cast(event, state)
    end
  end

  # ---- INFO CALLBACKS ---- #

  defp do_handle_info({:branch_status, branch_id, :active}, state) do
    new_active = MapSet.put(state.active_branches, branch_id)
    {:noreply, %{state | active_branches: new_active}}
  end

  defp do_handle_info({:branch_status, branch_id, :closed}, state) do
    new_closures =
      Map.update(state.branch_closures, branch_id, [%UnifSolution{}], fn existing ->
        [%UnifSolution{} | existing]
      end)

    new_state = %{state | branch_closures: new_closures}

    check_global_closure(new_state)
  end

  defp do_handle_info({:branch_status, branch_id, :split}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)
    new_state = %{state | active_branches: new_active}

    check_global_closure(new_state)
  end

  defp do_handle_info({:branch_status, branch_id, {:saturated, _}}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)
    {:noreply, %{state | active_branches: new_active}}
  end

  defp do_handle_info({:branch_status, _branch_id, _other}, state) do
    {:noreply, state}
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
    open_branches =
      saturated_branch_map
      |> Map.keys()
      |> Enum.filter(fn b_id ->
        closures = get_inherited_closures(b_id, state)
        Enum.empty?(closures)
      end)

    case open_branches do
      [model_branch_id | _] ->
        {model_defs, model_atoms} = Map.fetch!(saturated_branch_map, model_branch_id)

        Logger.info("Agent confirmed CSA on genuinely open branch #{model_branch_id}")

        Registry.dispatch(
          ShotMain.Prover.PubSub,
          "proof_results_#{state.session_id}",
          fn entries ->
            for {pid, _} <- entries,
                do: send(pid, {:proof_result, {:sat, {model_atoms, model_defs}}})
          end
        )

      [] ->
        Logger.warning(
          "All branches have local closures, but global unification failed. Returning UNK."
        )

        Registry.dispatch(
          ShotMain.Prover.PubSub,
          "proof_results_#{state.session_id}",
          fn entries ->
            for {pid, _} <- entries,
                do: send(pid, {:proof_result, {:unknown, :conflicting_substitutions}})
          end
        )
    end

    {:noreply, state}
  end

  defp do_handle_cast(:verify_all_closed, state) do
    active_options_lists =
      state.active_branches
      |> Enum.map(fn b_id -> get_inherited_closures(b_id, state) end)

    case find_valid_combination(active_options_lists) do
      {:ok, %UnifSolution{substitutions: final_substs, flex_pairs: flex}} ->
        final_map = Map.new(final_substs, fn s -> {s.fvar, s.term_id} end)

        if Enum.empty?(flex) do
          Registry.dispatch(
            ShotMain.Prover.PubSub,
            "proof_results_#{state.session_id}",
            fn entries ->
              for {pid, _} <- entries, do: send(pid, {:proof_result, {:unsat, final_map}})
            end
          )
        else
          Registry.dispatch(
            ShotMain.Prover.PubSub,
            "proof_results_#{state.session_id}",
            fn entries ->
              for {pid, _} <- entries,
                  do: send(pid, {:proof_result, {:cond_unsat, final_map, flex}})
            end
          )
        end

      :error ->
        Logger.warning(
          "All branches closed locally, but global unification failed. Returning UNK."
        )

        Registry.dispatch(
          ShotMain.Prover.PubSub,
          "proof_results_#{state.session_id}",
          fn entries ->
            for {pid, _} <- entries,
                do: send(pid, {:proof_result, {:unknown, :conflicting_substitutions}})
          end
        )
    end

    {:noreply, state}
  end

  defp do_handle_cast({:global_closure_found, solution}, state) do
    %UnifSolution{substitutions: final_substs, flex_pairs: flex} = solution

    final_map = Map.new(final_substs, fn s -> {s.fvar, s.term_id} end)

    if Enum.empty?(flex) do
      Logger.warning("GLOBAL CLOSURE FOUND! Status: Theorem")

      Registry.dispatch(ShotMain.Prover.PubSub, "proof_results_#{state.session_id}", fn entries ->
        for {pid, _} <- entries, do: send(pid, {:proof_result, {:unsat, final_map}})
      end)
    else
      Logger.warning("CONDITIONAL CLOSURE FOUND! Dependent on Flex-Flex constraints.")

      Registry.dispatch(ShotMain.Prover.PubSub, "proof_results_#{state.session_id}", fn entries ->
        for {pid, _} <- entries,
            do: send(pid, {:proof_result, {:cond_unsat, final_map, flex}})
      end)
    end

    {:noreply, state}
  end

  defp do_handle_cast({:local_closures, branch_id, new_closures}, state) do
    Logger.debug("Agent received #{length(new_closures)} valid local closures from #{branch_id}")

    updated_closures =
      Map.update(state.branch_closures, branch_id, new_closures, fn existing ->
        Enum.uniq(existing ++ new_closures)
      end)

    new_state = %{state | branch_closures: updated_closures}
    check_global_closure(new_state)
  end

  defp do_handle_cast(_event, state) do
    {:noreply, state}
  end

  ##############################################################################
  # INTERNAL LOGIC
  ##############################################################################

  defp get_inherited_closures(branch_id, state) do
    segments = String.split(branch_id, "_")

    prefixes =
      Enum.scan(segments, fn segment, acc -> acc <> "_" <> segment end)

    prefixes
    |> Enum.flat_map(fn prefix -> Map.get(state.branch_closures, prefix, []) end)
    |> Enum.uniq()
  end

  defp check_global_closure(state) do
    all_branches_can_close? =
      MapSet.size(state.active_branches) > 0 and
        Enum.all?(state.active_branches, fn b_id ->
          closures = get_inherited_closures(b_id, state)
          not Enum.empty?(closures)
        end)

    if all_branches_can_close? do
      active_options_lists =
        state.active_branches
        |> Enum.map(fn b_id -> get_inherited_closures(b_id, state) end)

      task_sup_via =
        {:via, Registry, {ShotMain.Prover.ProcessRegistry, {state.session_id, :task_supervisor}}}

      Task.Supervisor.start_child(task_sup_via, fn ->
        case find_valid_combination(active_options_lists) do
          {:ok, solution} ->
            ca_via = {:via, Registry, {ShotMain.Prover.ProcessRegistry, {state.session_id, :ca}}}
            GenServer.cast(ca_via, {:global_closure_found, solution})

          :error ->
            :ok
        end
      end)

      {:noreply, state}
    else
      {:noreply, state}
    end
  end

  defp find_valid_combination([]), do: {:ok, %UnifSolution{substitutions: [], flex_pairs: []}}

  defp find_valid_combination([branch_options | rest]) do
    Enum.reduce_while(branch_options, :error, fn current_solution, _acc ->
      with {:ok, remaining_merged_solution} <- find_valid_combination(rest) do
        case merge_solutions(current_solution, remaining_merged_solution) do
          {:ok, final_merged} -> {:halt, {:ok, final_merged}}
          :error -> {:cont, :error}
        end
      else
        :error ->
          {:cont, :error}
      end
    end)
  end

  defp merge_solutions(%UnifSolution{} = sol1, %UnifSolution{} = sol2) do
    pairs1 = Enum.map(sol1.substitutions, fn s -> {TF.make_term(s.fvar), s.term_id} end)
    pairs2 = Enum.map(sol2.substitutions, fn s -> {TF.make_term(s.fvar), s.term_id} end)

    all_pairs = pairs1 ++ pairs2 ++ sol1.flex_pairs ++ sol2.flex_pairs

    stream = ShotUnify.unify(all_pairs, @unify_depth)

    case Enum.take(stream, 1) do
      [] -> :error
      [merged_solution] -> {:ok, merged_solution}
    end
  end

  ##############################################################################
  # HELPERS
  ##############################################################################
end
