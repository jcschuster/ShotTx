defmodule ShotMain.Prover.ContradictionAgent do
  # GenServer, listens to PubSub and searches for closure
  use GenServer
  require Logger

  alias ShotMain.Simplifyer
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUnify
  alias ShotUnify.UnifSolution
  import ShotDs.Hol.{Patterns, Definitions, Dsl}

  @unify_depth 10

  # State tracking
  defstruct active_branches: MapSet.new(),
            branch_closures: %{}

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  def start_link(_opts \\ []) do
    GenServer.start_link(__MODULE__, %__MODULE__{}, name: __MODULE__)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init(state) do
    Registry.register(ShotMain.Prover.PubSub, "atoms", [])
    Registry.register(ShotMain.Prover.PubSub, "branch_events", [])
    {:ok, state}
  end

  @impl true
  def handle_call(:reset_state, _from, _state) do
    Logger.debug("ContradictionAgent safely resetting state.")
    {:reply, :ok, %__MODULE__{}}
  end

  @impl true
  def handle_info(event, state) do
    case :ets.lookup(:tableau_stats, :aborted) do
      [{:aborted, true}] ->
        {:noreply, state}

      _ ->
        do_handle_info(event, state)
    end
  end

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

  defp do_handle_info({:branch_status, _branch_id, _other}, state) do
    {:noreply, state}
  end

  defp do_handle_info({:new_atom, branch_id, term_id}, state) do
    branch_atoms = get_all_atoms_for_branch(branch_id)

    if false_term() in branch_atoms do
      Logger.debug("Branch #{branch_id} closed by semantic falsity.")

      updated_closures =
        Map.update(state.branch_closures, branch_id, [%{}], fn existing ->
          Enum.uniq([%{} | existing])
        end)

      trigger_ground_closure(branch_id)

      new_state = %{state | branch_closures: updated_closures}
      check_global_closure(new_state)
    else
      new_local_closures = find_local_closures(term_id, branch_atoms)

      if Enum.empty?(new_local_closures) do
        {:noreply, state}
      else
        Logger.debug(
          "Branch #{branch_id} found local closure options: #{inspect(new_local_closures)}"
        )

        has_ground_closure? =
          Enum.any?(new_local_closures, fn sol ->
            Enum.empty?(sol.substitutions) && Enum.empty?(sol.flex_pairs)
          end)

        if has_ground_closure? do
          trigger_ground_closure(branch_id)
        end

        updated_closures =
          Map.update(state.branch_closures, branch_id, new_local_closures, fn existing ->
            Enum.uniq(existing ++ new_local_closures)
          end)

        new_state = %{state | branch_closures: updated_closures}
        check_global_closure(new_state)
      end
    end
  end

  defp do_handle_info({:verify_csa, saturated_branch_map}, state) do
    open_branches =
      saturated_branch_map
      |> Map.keys()
      |> Enum.filter(fn b_id ->
        closures = get_inherited_closures(b_id, state)
        Enum.empty?(closures)
      end)

    case open_branches do
      [model_branch_id | _] ->
        model_atoms = get_all_atoms_for_branch(model_branch_id)
        model_defs = Map.fetch!(saturated_branch_map, model_branch_id)

        Logger.info("Agent confirmed CSA on genuinely open branch #{model_branch_id}")

        Registry.dispatch(ShotMain.Prover.PubSub, "proof_results", fn entries ->
          for {pid, _} <- entries,
              do: send(pid, {:proof_result, {:sat, {model_atoms, model_defs}}})
        end)

      [] ->
        Logger.warning(
          "All branches have local closures, but global unification failed. Returning UNK."
        )

        Registry.dispatch(ShotMain.Prover.PubSub, "proof_results", fn entries ->
          for {pid, _} <- entries,
              do: send(pid, {:proof_result, {:unknown, :conflicting_substitutions}})
        end)
    end

    {:noreply, state}
  end

  defp do_handle_info(:verify_all_closed, state) do
    active_options_lists =
      state.active_branches
      |> Enum.map(fn b_id -> get_inherited_closures(b_id, state) end)

    case find_valid_combination(active_options_lists) do
      {:ok, %UnifSolution{substitutions: final_substs, flex_pairs: flex}} ->
        final_map = Map.new(final_substs, fn s -> {s.fvar, s.term_id} end)

        if Enum.empty?(flex) do
          Registry.dispatch(ShotMain.Prover.PubSub, "proof_results", fn entries ->
            for {pid, _} <- entries, do: send(pid, {:proof_result, {:unsat, final_map}})
          end)
        else
          Registry.dispatch(ShotMain.Prover.PubSub, "proof_results", fn entries ->
            for {pid, _} <- entries,
                do: send(pid, {:proof_result, {:cond_unsat, final_map, flex}})
          end)
        end

      :error ->
        Logger.warning(
          "All branches closed locally, but global unification failed. Returning UNK."
        )

        Registry.dispatch(ShotMain.Prover.PubSub, "proof_results", fn entries ->
          for {pid, _} <- entries,
              do: send(pid, {:proof_result, {:unknown, :conflicting_substitutions}})
        end)
    end

    {:noreply, state}
  end

  defp do_handle_info(_, state) do
    {:noreply, state}
  end

  ##############################################################################
  # INTERNAL LOGIC
  ##############################################################################

  defp find_local_closures(new_term, existing_atoms) do
    neg_new_term = lit_neg(new_term)

    Enum.flat_map(existing_atoms, fn existing_term ->
      neg_existing = lit_neg(existing_term)

      sols1 = ShotUnify.unify({neg_new_term, existing_term}, @unify_depth) |> Enum.to_list()
      sols2 = ShotUnify.unify({new_term, neg_existing}, @unify_depth) |> Enum.to_list()

      sols1 ++ sols2
    end)
  end

  defp get_inherited_closures(branch_id, state) do
    branch_id
    |> trace_lineage_ids([])
    |> Enum.flat_map(fn b_id -> Map.get(state.branch_closures, b_id, []) end)
    |> Enum.uniq()
  end

  defp check_global_closure(state) do
    all_branches_can_close? =
      Enum.all?(state.active_branches, fn b_id ->
        closures = get_inherited_closures(b_id, state)
        not Enum.empty?(closures)
      end)

    if all_branches_can_close? do
      active_options_lists =
        state.active_branches
        |> Enum.map(fn b_id -> get_inherited_closures(b_id, state) end)

      case find_valid_combination(active_options_lists) do
        {:ok, %UnifSolution{substitutions: final_substs, flex_pairs: flex}} ->
          final_map = Map.new(final_substs, fn s -> {s.fvar, s.term_id} end)

          if Enum.empty?(flex) do
            Logger.warning("GLOBAL CLOSURE FOUND! Status: Theorem")

            Registry.dispatch(ShotMain.Prover.PubSub, "proof_results", fn entries ->
              for {pid, _} <- entries, do: send(pid, {:proof_result, {:unsat, final_map}})
            end)
          else
            Logger.warning("CONDITIONAL CLOSURE FOUND! Dependent on Flex-Flex constraints.")

            Registry.dispatch(ShotMain.Prover.PubSub, "proof_results", fn entries ->
              for {pid, _} <- entries,
                  do: send(pid, {:proof_result, {:cond_unsat, final_map, flex}})
            end)
          end

          {:noreply, state}

        :error ->
          {:noreply, state}
      end
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

  defp trigger_ground_closure(branch_id) do
    :ets.insert(:tableau_tombstones, {branch_id, true})
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp get_all_atoms_for_branch(branch_id) do
    branch_id
    |> trace_lineage_ids([])
    |> fetch_raw_atoms_from_ids()
    |> Enum.map(&Simplifyer.o_simplify/1)
  end

  defp trace_lineage_ids(nil, acc), do: Enum.reverse(acc)

  defp trace_lineage_ids(branch_id, acc) do
    parent_id =
      case :ets.lookup(:tableau_lineage, branch_id) do
        [{^branch_id, pid}] -> pid
        [] -> nil
      end

    trace_lineage_ids(parent_id, [branch_id | acc])
  end

  defp fetch_raw_atoms_from_ids(branch_ids) do
    Enum.flat_map(branch_ids, fn b_id ->
      :ets.lookup(:tableau_board, b_id)
      |> Enum.map(fn {_id, term} -> term end)
    end)
  end

  defp lit_neg(term_id) do
    case TF.get_term(term_id) do
      negated(inner) -> inner
      _ -> neg(term_id)
    end
  end
end
