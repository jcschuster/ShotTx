defmodule ShotTx.Prover.ContradictionAgent do
  # GenServer, listens to PubSub and searches for closure
  use GenServer
  require Logger

  alias ShotTx.Data.Parameters
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotUn
  alias ShotUn.UnifSolution

  # State tracking
  defstruct session_id: nil,
            ets_tables: %{},
            active_branches: MapSet.new(),
            clashing_local_pairs: %{},
            branch_closures: %{},
            params: %Parameters{}

  @empty_solution %UnifSolution{substitutions: [], flex_pairs: []}

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
          ShotTx.Prover.PubSub,
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
          ShotTx.Prover.PubSub,
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

    case find_valid_combination(active_options_lists, state.params.unification_depth) do
      {:ok, %UnifSolution{substitutions: final_substs, flex_pairs: flex}} ->
        final_map = Map.new(final_substs, fn s -> {s.fvar, s.term_id} end)

        if Enum.empty?(flex) do
          Registry.dispatch(
            ShotTx.Prover.PubSub,
            "proof_results_#{state.session_id}",
            fn entries ->
              for {pid, _} <- entries, do: send(pid, {:proof_result, {:unsat, final_map}})
            end
          )
        else
          Registry.dispatch(
            ShotTx.Prover.PubSub,
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
          ShotTx.Prover.PubSub,
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

      Registry.dispatch(ShotTx.Prover.PubSub, "proof_results_#{state.session_id}", fn entries ->
        for {pid, _} <- entries, do: send(pid, {:proof_result, {:unsat, final_map}})
      end)
    else
      Logger.warning("CONDITIONAL CLOSURE FOUND! Dependent on Flex-Flex constraints.")

      Registry.dispatch(ShotTx.Prover.PubSub, "proof_results_#{state.session_id}", fn entries ->
        for {pid, _} <- entries,
            do: send(pid, {:proof_result, {:cond_unsat, final_map, flex}})
      end)
    end

    {:noreply, state}
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

  ##############################################################################
  # GLOBAL CLOSURE CHECK — DISAGREEMENT PAIRS
  #
  # The CSP: for each active branch, pick one disagreement pair from its
  # inherited clashes such that the union of all chosen pairs is simultaneously
  # unifiable.
  #
  # Optimizations over the naive Cartesian-product approach:
  #   1. MRV ordering — branches with fewer candidates are tried first
  #   2. Constraint decomposition — independent groups (no shared fvars) are
  #      solved separately, turning one large exponential into several small ones
  #   3. Incremental backtracking — the accumulated unification solution is
  #      threaded through the search; incompatible candidates are pruned
  #      immediately without recursing into deeper levels
  #   4. Forward checking — after extending the solution, remaining branches
  #      whose domains are fully wiped out trigger an immediate backtrack
  ##############################################################################

  defp check_global_closure(state) do
    branch_clash_lists =
      Enum.map(state.active_branches, fn b_id ->
        get_inherited_clashes(b_id, state) |> Enum.to_list()
      end)

    some_branch_cannot_close? =
      Enum.empty?(state.active_branches) ||
        Enum.any?(branch_clash_lists, &Enum.empty?/1)

    if some_branch_cannot_close? do
      {:noreply, state}
    else
      depth = state.params.unification_depth

      task_sup_via =
        {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :task_supervisor}}}

      Task.Supervisor.start_child(task_sup_via, fn ->
        # 1. MRV: process the most constrained branches first
        sorted = Enum.sort_by(branch_clash_lists, &length/1)

        # 2. Decompose into independent sub-problems
        groups = partition_independent(sorted)

        # 3. Solve each group, combine results
        case solve_groups(groups, depth) do
          {:ok, solution} ->
            ca_via =
              {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}

            GenServer.cast(ca_via, {:global_closure_found, solution})

          :error ->
            :ok
        end
      end)

      {:noreply, state}
    end
  end

  # Solve each independent group separately, then merge the group solutions.
  # Because the groups share no free variables their solutions are guaranteed
  # compatible, but we still verify through unification to account for flex
  # pairs.
  @spec solve_groups([[list()]], non_neg_integer()) :: {:ok, UnifSolution.t()} | :error
  defp solve_groups(groups, depth) do
    Enum.reduce_while(groups, {:ok, @empty_solution}, fn group, {:ok, acc_solution} ->
      case incremental_search(group, depth, @empty_solution) do
        {:ok, group_solution} ->
          case merge_solutions(acc_solution, group_solution, depth) do
            {:ok, merged} -> {:cont, {:ok, merged}}
            :error -> {:halt, :error}
          end

        :error ->
          {:halt, :error}
      end
    end)
  end

  # Core incremental backtracking search for a single independent group.
  # Threads an accumulated `UnifSolution` through the recursion; at each level
  # a candidate pair is tested against the running solution and pruned
  # immediately if incompatible.
  @spec incremental_search([[{term(), term()}]], non_neg_integer(), UnifSolution.t()) ::
          {:ok, UnifSolution.t()} | :error
  defp incremental_search([], _depth, acc_solution), do: {:ok, acc_solution}

  defp incremental_search([branch_candidates | rest], depth, acc_solution) do
    Enum.reduce_while(branch_candidates, :error, fn pair, _acc ->
      case try_extend_with_pair(acc_solution, pair, depth) do
        {:ok, extended} ->
          # Forward check: verify no remaining branch is fully wiped out
          if forward_check_ok?(rest, extended, depth) do
            case incremental_search(rest, depth, extended) do
              {:ok, final} -> {:halt, {:ok, final}}
              :error -> {:cont, :error}
            end
          else
            {:cont, :error}
          end

        :error ->
          {:cont, :error}
      end
    end)
  end

  # Try adding a single disagreement pair to the accumulated solution.
  # Converts the existing substitutions back to equality pairs and unifies
  # everything together so the unifier checks mutual compatibility.
  @spec try_extend_with_pair(UnifSolution.t(), {integer(), integer()}, non_neg_integer()) ::
          {:ok, UnifSolution.t()} | :error
  defp try_extend_with_pair(%UnifSolution{} = sol, {l_id, r_id}, depth) do
    existing_pairs =
      Enum.map(sol.substitutions, fn s -> {TF.make_term(s.fvar), s.term_id} end)

    all_pairs = [{l_id, r_id} | existing_pairs ++ sol.flex_pairs]

    case ShotUn.unify(all_pairs, depth) |> Enum.take(1) do
      [merged] -> {:ok, merged}
      [] -> :error
    end
  end

  # Lightweight forward check: for each remaining branch, verify that at least
  # one candidate pair is not *trivially* incompatible with the current
  # solution. This catches wipe-outs early without running full unification on
  # every remaining candidate.
  #
  # The quick compatibility test applies the current substitution to both sides
  # of a candidate pair and checks for a rigid-rigid head mismatch — the
  # cheapest possible refutation. Pairs that survive this filter may still fail
  # full unification, but pairs that fail it are guaranteed dead.
  @spec forward_check_ok?([[{integer(), integer()}]], UnifSolution.t(), non_neg_integer()) ::
          boolean()
  defp forward_check_ok?(remaining_branches, solution, _depth) do
    subst_list = solution.substitutions

    Enum.all?(remaining_branches, fn candidates ->
      Enum.any?(candidates, fn {l_id, r_id} ->
        quick_compatible?(l_id, r_id, subst_list)
      end)
    end)
  end

  # Apply the current substitutions and check whether the resulting head
  # symbols are obviously incompatible (two different rigid heads).  This is
  # sound for pruning: if two rigid heads disagree, unification will certainly
  # fail.  The check is intentionally conservative — it returns `true`
  # (compatible) whenever in doubt, including when either side is flex.
  @spec quick_compatible?(integer(), integer(), [ShotDs.Data.Substitution.t()]) :: boolean()
  defp quick_compatible?(l_id, r_id, subst_list) do
    l_applied = ShotDs.Stt.Semantics.subst!(subst_list, l_id)
    r_applied = ShotDs.Stt.Semantics.subst!(subst_list, r_id)

    l_term = TF.get_term!(l_applied)
    r_term = TF.get_term!(r_applied)

    case {l_term.head.kind, r_term.head.kind} do
      # Two rigid constants: must be the same symbol or unification will fail
      {:co, :co} -> l_term.head == r_term.head
      # Two rigid bound vars: must land on the same slot
      {:bv, :bv} -> l_term.head == r_term.head
      # At least one side is flex — can't rule it out cheaply
      _ -> true
    end
  end

  ##############################################################################
  # GLOBAL CLOSURE CHECK — BRANCH CLOSURES (verify_all_closed)
  #
  # Same CSP but the domains are lists of UnifSolution closures rather than
  # raw pairs. Uses the same incremental + MRV strategy.
  ##############################################################################

  @spec find_valid_combination([[UnifSolution.t()]], non_neg_integer()) ::
          {:ok, UnifSolution.t()} | :error
  defp find_valid_combination(branch_options_lists, depth) do
    # MRV: most constrained branches first
    sorted = Enum.sort_by(branch_options_lists, &length/1)
    incremental_search_solutions(sorted, depth, @empty_solution)
  end

  @spec incremental_search_solutions([[UnifSolution.t()]], non_neg_integer(), UnifSolution.t()) ::
          {:ok, UnifSolution.t()} | :error
  defp incremental_search_solutions([], _depth, acc), do: {:ok, acc}

  defp incremental_search_solutions([branch_options | rest], depth, acc) do
    Enum.reduce_while(branch_options, :error, fn candidate_solution, _acc ->
      case merge_solutions(acc, candidate_solution, depth) do
        {:ok, extended} ->
          case incremental_search_solutions(rest, depth, extended) do
            {:ok, final} -> {:halt, {:ok, final}}
            :error -> {:cont, :error}
          end

        :error ->
          {:cont, :error}
      end
    end)
  end

  ##############################################################################
  # CONSTRAINT DECOMPOSITION
  #
  # Partition branches into independent groups based on shared free variables.
  # Two branches are in the same group iff their disagreement pairs share at
  # least one free variable (transitively).  Independent groups can be solved
  # separately, turning one Πᵢ|Dᵢ| search into Σ_g Πᵢ∈g |Dᵢ|.
  ##############################################################################

  @spec partition_independent([[{integer(), integer()}]]) :: [[[{integer(), integer()}]]]
  defp partition_independent([]), do: []
  defp partition_independent([single]), do: [[single]]

  defp partition_independent(branches) do
    n = length(branches)
    indices = 0..(n - 1)

    # Collect fvars reachable from each branch's candidate pairs
    fvar_sets =
      Enum.map(branches, fn candidates ->
        for {l_id, r_id} <- candidates,
            id <- [l_id, r_id],
            fvar <- TF.get_term!(id).fvars,
            into: MapSet.new(),
            do: fvar
      end)

    # Union-Find: merge branches that share at least one fvar
    parent = Map.new(indices, &{&1, &1})
    rank = Map.new(indices, &{&1, 0})

    {new_parent, _rank} =
      for i <- indices,
          j <- indices,
          j > i,
          not MapSet.disjoint?(Enum.at(fvar_sets, i), Enum.at(fvar_sets, j)),
          reduce: {parent, rank} do
        {p, r} -> uf_union(p, r, i, j)
      end

    # Group branch lists by their root representative
    indices
    |> Enum.group_by(&uf_find(new_parent, &1))
    |> Map.values()
    |> Enum.map(fn group_indices ->
      Enum.map(group_indices, &Enum.at(branches, &1))
    end)
  end

  # Union-Find with union-by-rank for near-constant amortised operations.
  # Path compression is omitted because the structure is short-lived and small.

  @spec uf_find(map(), non_neg_integer()) :: non_neg_integer()
  defp uf_find(parent, i) do
    case Map.fetch!(parent, i) do
      ^i -> i
      p -> uf_find(parent, p)
    end
  end

  @spec uf_union(map(), map(), non_neg_integer(), non_neg_integer()) :: {map(), map()}
  defp uf_union(parent, rank, i, j) do
    ri = uf_find(parent, i)
    rj = uf_find(parent, j)

    if ri == rj do
      {parent, rank}
    else
      ri_rank = Map.fetch!(rank, ri)
      rj_rank = Map.fetch!(rank, rj)

      cond do
        ri_rank < rj_rank ->
          {Map.put(parent, ri, rj), rank}

        ri_rank > rj_rank ->
          {Map.put(parent, rj, ri), rank}

        true ->
          {Map.put(parent, rj, ri), Map.put(rank, ri, ri_rank + 1)}
      end
    end
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

  @spec merge_solutions(UnifSolution.t(), UnifSolution.t(), non_neg_integer()) ::
          {:ok, UnifSolution.t()} | :error
  defp merge_solutions(%UnifSolution{} = sol1, %UnifSolution{} = sol2, depth) do
    pairs1 = Enum.map(sol1.substitutions, fn s -> {TF.make_term(s.fvar), s.term_id} end)
    pairs2 = Enum.map(sol2.substitutions, fn s -> {TF.make_term(s.fvar), s.term_id} end)

    all_pairs = pairs1 ++ pairs2 ++ sol1.flex_pairs ++ sol2.flex_pairs

    case ShotUn.unify(all_pairs, depth) |> Enum.take(1) do
      [] -> :error
      [merged_solution] -> {:ok, merged_solution}
    end
  end
end
