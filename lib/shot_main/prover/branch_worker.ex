defmodule ShotMain.Prover.BranchWorker do
  require Logger
  use GenServer
  alias ShotMain.Generation
  alias ShotMain.Data.Parameters
  alias ShotMain.Prover.Rules
  alias ShotMain.Prover.FormulaPqueue, as: FPQ
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.Dsl
  import ShotDs.Hol.Patterns

  # State tracking
  defstruct id: nil,
            queue: nil,
            defs: %{},
            params: nil,
            sleeping_gamma_rules: [],
            sleeping_prim_rules: [],
            current_gamma_limit: 1,
            current_prim_limit: 1

  def start_branch(branch_id, formulas, defs \\ %{}, %Parameters{} = params) do
    initial_queue = Enum.reduce(formulas, FPQ.new(), &insert_formula(&2, &1, params))

    state = %__MODULE__{
      id: branch_id,
      queue: initial_queue,
      defs: defs,
      params: params,
      sleeping_gamma_rules: [],
      current_gamma_limit: params.initial_gamma_limit
    }

    DynamicSupervisor.start_child(ShotMain.Prover.BranchSupervisor, {__MODULE__, state})
  end

  def spawn_child_branch(child_id, new_formula, %__MODULE__{} = parent_state) do
    case :ets.lookup(:tableau_stats, :aborted) do
      [{:aborted, true}] ->
        :ok

      _ ->
        current_count = :ets.update_counter(:tableau_stats, :branch_count, {2, 1})

        if current_count > parent_state.params.max_branches do
          Logger.error(
            "Branch limit (#{parent_state.params.max_branches}) exceeded! Aborting search."
          )

          Registry.dispatch(ShotMain.Prover.PubSub, "proof_results", fn entries ->
            for {pid, _} <- entries do
              send(pid, {:proof_result, {:unknown, :max_branches_reached}})
            end
          end)
        else
          inherited_queue = insert_formula(parent_state.queue, new_formula, parent_state.params)

          child_state = %__MODULE__{
            id: child_id,
            queue: inherited_queue,
            defs: parent_state.defs,
            params: parent_state.params,
            sleeping_gamma_rules: parent_state.sleeping_gamma_rules,
            current_gamma_limit: parent_state.current_gamma_limit
          }

          DynamicSupervisor.start_child(
            ShotMain.Prover.BranchSupervisor,
            {__MODULE__, child_state}
          )
        end
    end
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  def child_spec(state) do
    %{
      id: __MODULE__,
      start: {GenServer, :start_link, [__MODULE__, state, []]},
      restart: :temporary
    }
  end

  @impl true
  def init(%__MODULE__{} = state) do
    if poisoned?(state.id) do
      {:stop, :normal}
    else
      broadcast_manager(state.id, :active)
      send(self(), :process_next)
      {:ok, state}
    end
  end

  @impl true
  def handle_info({:wake_up, new_limit}, %__MODULE__{} = state) do
    Logger.debug("Branch #{state.id} waking up. New Gamma limit: #{new_limit}")

    new_queue =
      Enum.reduce(state.sleeping_gamma_rules, state.queue, &insert_formula(&2, &1, state.params))

    new_state = %{
      state
      | current_gamma_limit: new_limit,
        sleeping_gamma_rules: [],
        queue: new_queue
    }

    broadcast_manager(state.id, :active)
    send(self(), :process_next)

    {:noreply, new_state}
  end

  ##### Main Processing Loop #####

  @impl true
  def handle_info(:process_next, state) do
    cond do
      poisoned?(state.id) ->
        Logger.debug("Branch #{state.id} noticed it is poisoned. Terminating.")
        :ets.update_counter(:tableau_stats, :branch_count, {2, -1})
        {:stop, :normal, state}

      FPQ.empty?(state.queue) and not Enum.empty?(state.sleeping_gamma_rules) ->
        broadcast_manager(state.id, :idle)
        {:noreply, state}

      FPQ.empty?(state.queue) ->
        Logger.info("Branch #{state.id} fully saturated. Found a counter-model!")
        broadcast_manager(state.id, {:saturated, state.defs})

        :ets.update_counter(:tableau_stats, :branch_count, {2, -1})

        {:stop, :normal, state}

      true ->
        {cf, remaining_queue} = FPQ.take_smallest(state.queue)

        case apply_rule(cf, %{state | queue: remaining_queue}) do
          {:stop, reason, final_state} ->
            {:stop, reason, final_state}

          new_state ->
            send(self(), :process_next)
            {:noreply, new_state}
        end
    end
  end

  ##############################################################################
  # RULE APPLICATION
  ##############################################################################

  defp apply_rule(:contradiction, state) do
    Logger.info("Branch #{state.id} closed explicitly.")
    broadcast_manager(state.id, :closed)

    :ets.update_counter(:tableau_stats, :branch_count, {2, -1})

    {:stop, :normal, state}
  end

  defp apply_rule(:tautology, state), do: state

  ##### Linear Decompositions #####

  defp apply_rule({:alpha, formulas}, state) do
    new_queue = Enum.reduce(formulas, state.queue, &insert_formula(&2, &1, state.params))
    %{state | queue: new_queue}
  end

  defp apply_rule({:delta, sk_term}, state) do
    %{state | queue: insert_formula(state.queue, sk_term, state.params)}
  end

  defp apply_rule({:rename, {t1, t2}}, state) do
    new_queue = Enum.reduce([t1, t2], state.queue, &insert_formula(&2, &1, state.params))
    %{state | queue: new_queue}
  end

  ##### Branching #####

  defp apply_rule({:beta, {b1, b2}}, state) do
    my_new_id = state.id <> "_A"
    sibling_id = state.id <> "_B"

    :ets.insert(:tableau_lineage, {my_new_id, state.id})
    :ets.insert(:tableau_lineage, {sibling_id, state.id})

    spawn_child_branch(sibling_id, b2, state)

    broadcast_manager(state.id, :split)
    broadcast_manager(my_new_id, :active)

    new_queue = insert_formula(state.queue, b1, state.params)
    %{state | id: my_new_id, queue: new_queue}
  end

  defp apply_rule({:instantiate, branches_stream, count}, %__MODULE__{} = state) do
    branches = Enum.to_list(branches_stream)

    lineage_atoms =
      state.id
      |> trace_lineage_ids([])
      |> fetch_raw_atoms_from_ids()

    keep_idx = count - 1

    if count == 0 do
      state
    else
      branches
      |> Stream.with_index()
      |> Enum.reduce(nil, fn
        {{keep_branch, {k_decl, k_tid}}, ^keep_idx}, _acc ->
          new_defs = Map.put(state.defs, k_decl, k_tid)

          keep_child_id = "#{state.id}_K"
          :ets.insert(:tableau_lineage, {keep_child_id, state.id})

          broadcast_manager(state.id, :split)
          broadcast_manager(keep_child_id, :active)

          queue_with_unfolded =
            Enum.reduce(lineage_atoms, state.queue, fn term_id, acc_queue ->
              case unfold_if_possible(term_id, new_defs) do
                nil ->
                  acc_queue

                unfolded_cf ->
                  FPQ.insert(acc_queue, unfolded_cf, state.params.formula_cost.(unfolded_cf))
              end
            end)

          final_queue = insert_formula(queue_with_unfolded, keep_branch, state.params)
          %{state | id: keep_child_id, queue: final_queue, defs: new_defs}

        {{b_term, {decl, tid}}, idx}, acc ->
          new_defs = Map.put(state.defs, decl, tid)

          child_id = "#{state.id}_I#{idx}"
          :ets.insert(:tableau_lineage, {child_id, state.id})

          queue_with_unfolded =
            Enum.reduce(lineage_atoms, state.queue, fn term_id, acc_queue ->
              case unfold_if_possible(term_id, new_defs) do
                nil ->
                  acc_queue

                unfolded_cf ->
                  FPQ.insert(acc_queue, unfolded_cf, state.params.formula_cost.(unfolded_cf))
              end
            end)

          final_queue = insert_formula(queue_with_unfolded, b_term, state.params)

          child_state = %{state | id: child_id, queue: final_queue, defs: new_defs}
          spawn_child_branch(child_id, b_term, child_state)

          acc
      end)
    end
  end

  ##### Instantiations #####

  defp apply_rule({:gamma, recipe, type, prev_insts} = rule, state) do
    if prev_insts >= state.current_gamma_limit do
      %{state | sleeping_gamma_rules: [rule | state.sleeping_gamma_rules]}
    else
      instantiated = app(recipe, TF.make_fresh_var_term(type))
      updated_gamma = {:gamma, recipe, type, prev_insts + 1}

      new_queue =
        state.queue
        |> insert_formula(instantiated, state.params)
        |> FPQ.insert(updated_gamma, state.params.formula_cost.(updated_gamma))

      %{state | queue: new_queue}
    end
  end

  defp apply_rule({:gamma_finite, recipe, type}, state) do
    new_queue =
      type
      |> Generation.gen_o()
      |> Enum.reduce(state.queue, fn term_id, acc_queue ->
        instantiated = app(recipe, term_id)
        insert_formula(acc_queue, instantiated, state.params)
      end)

    %{state | queue: new_queue}
  end

  ##### Atoms & Blackboard Publishing #####

  defp apply_rule({:atomic, term_id}, state) do
    unfolded_cf = unfold_if_possible(term_id, state.defs)

    case unfolded_cf do
      nil ->
        :ets.insert(:tableau_board, {state.id, term_id})

        Registry.dispatch(ShotMain.Prover.PubSub, "atoms", fn entries ->
          for {pid, _} <- entries, do: send(pid, {:new_atom, state.id, term_id})
        end)

        state

      cf ->
        %{state | queue: FPQ.insert(state.queue, cf, state.params.formula_cost.(cf))}
    end
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp poisoned?(branch_id) do
    lineage = [branch_id | trace_lineage_ids(branch_id, [])]

    Enum.any?(lineage, fn id ->
      :ets.member(:tableau_tombstones, id)
    end)
  end

  defp insert_formula(queue, formula, params) do
    cf = Rules.classify_formula(formula)
    c = params.formula_cost.(cf)

    FPQ.insert(queue, cf, c)
  end

  defp unfold_if_possible(term_id, defs) do
    case TF.get_term(term_id) do
      %ShotDs.Data.Term{bvars: [], head: head, args: args} when is_map_key(defs, head) ->
        unfolded = app(Map.fetch!(defs, head), args)
        Rules.classify_formula(unfolded)

      _ ->
        case TF.get_term(lit_neg(term_id)) do
          %ShotDs.Data.Term{bvars: [], head: head, args: args} when is_map_key(defs, head) ->
            unfolded = neg(app(Map.fetch!(defs, head), args))
            Rules.classify_formula(unfolded)

          _ ->
            nil
        end
    end
  end

  defp lit_neg(term_id) do
    case TF.get_term(term_id) do
      negated(inner) -> inner
      _ -> neg(term_id)
    end
  end

  defp broadcast_manager(branch_id, status) do
    Registry.dispatch(ShotMain.Prover.PubSub, "branch_events", fn entries ->
      for {pid, _} <- entries, do: send(pid, {:branch_status, branch_id, status})
    end)
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
end
