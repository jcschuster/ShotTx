defmodule ShotTx.Prover.BranchWorker do
  require Logger
  use GenServer
  alias ShotTx.Generation
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Rules
  alias ShotTx.Prover.FormulaPqueue, as: FPQ
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl
  import ShotDs.Hol.Patterns

  # State tracking
  defstruct id: nil,
            session_id: nil,
            ets_tables: %{},
            queue: nil,
            defs: %{},
            params: %Parameters{},
            sleeping_gamma_rules: [],
            current_gamma_limit: 1,
            local_atoms: []

  def start_link(state) do
    GenServer.start_link(__MODULE__, state)
  end

  def start_branch(branch_id, formulas, defs \\ %{}, params, session_id, ets_tables) do
    initial_queue = Enum.reduce(formulas, FPQ.new(), &insert_formula(&2, &1, params))

    state = %__MODULE__{
      id: branch_id,
      session_id: session_id,
      ets_tables: ets_tables,
      queue: initial_queue,
      defs: defs,
      params: params,
      sleeping_gamma_rules: [],
      current_gamma_limit: params.initial_gamma_limit
    }

    supervisor_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :branch_supervisor}}}

    DynamicSupervisor.start_child(supervisor_via, {__MODULE__, state})
  end

  def spawn_child_branch(child_id, new_formula, %__MODULE__{} = parent_state) do
    case :ets.lookup(parent_state.ets_tables.stats, :aborted) do
      [{:aborted, true}] ->
        :ok

      _ ->
        current_count = :ets.update_counter(parent_state.ets_tables.stats, :branch_count, {2, 1})

        if current_count > parent_state.params.max_branches do
          Logger.error(
            "Branch limit (#{parent_state.params.max_branches}) exceeded! Aborting search."
          )

          Registry.dispatch(
            ShotTx.Prover.PubSub,
            "proof_results_#{parent_state.session_id}",
            fn entries ->
              for {pid, _} <- entries do
                send(pid, {:proof_result, {:unknown, :max_branches_reached}})
              end
            end
          )
        else
          inherited_queue = insert_formula(parent_state.queue, new_formula, parent_state.params)

          child_state = %__MODULE__{
            id: child_id,
            session_id: parent_state.session_id,
            ets_tables: parent_state.ets_tables,
            queue: inherited_queue,
            defs: parent_state.defs,
            params: parent_state.params,
            sleeping_gamma_rules: parent_state.sleeping_gamma_rules,
            current_gamma_limit: parent_state.current_gamma_limit,
            local_atoms: parent_state.local_atoms
          }

          supervisor_via =
            {:via, Registry,
             {ShotTx.Prover.ProcessRegistry, {parent_state.session_id, :branch_supervisor}}}

          DynamicSupervisor.start_child(supervisor_via, {__MODULE__, child_state})
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
    Registry.register(ShotTx.Prover.PubSub, "global_branch_control_#{state.session_id}", [])

    if poisoned?(state.id, state.ets_tables) do
      {:stop, :normal, state}
    else
      broadcast_status(state.id, :active, state)
      {:ok, state, {:continue, :process_next}}
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

    broadcast_status(state.id, :active, state)

    {:noreply, new_state, {:continue, :process_next}}
  end

  @impl true
  def handle_info({:poison_prefix, poisoned_prefix}, state) do
    if String.starts_with?(state.id, poisoned_prefix) do
      Logger.debug("Branch #{state.id} caught poison from #{poisoned_prefix}. Terminating.")
      broadcast_status(state.id, :closed, state)
      :ets.update_counter(state.ets_tables.stats, :branch_count, {2, -1})
      {:stop, :normal, state}
    else
      {:noreply, state}
    end
  end

  ##### Main Processing Loop #####

  @impl true
  def handle_continue(:process_next, state) do
    cond do
      poisoned?(state.id, state.ets_tables) ->
        Logger.debug("Branch #{state.id} noticed it is poisoned. Terminating.")
        broadcast_status(state.id, :closed, state)
        :ets.update_counter(state.ets_tables.stats, :branch_count, {2, -1})
        {:stop, :normal, state}

      FPQ.empty?(state.queue) and not Enum.empty?(state.sleeping_gamma_rules) ->
        broadcast_status(state.id, :idle, state)
        {:noreply, state}

      FPQ.empty?(state.queue) ->
        Logger.info("Branch #{state.id} fully saturated. Found a counter-model!")
        broadcast_status(state.id, {:saturated, {state.defs, state.local_atoms}}, state)
        :ets.update_counter(state.ets_tables.stats, :branch_count, {2, -1})
        {:stop, :normal, state}

      true ->
        {cf, remaining_queue} = FPQ.take_smallest(state.queue)

        case apply_rule(cf, %{state | queue: remaining_queue}) do
          {:stop, reason, final_state} ->
            {:stop, reason, final_state}

          new_state ->
            {:noreply, new_state, {:continue, :process_next}}
        end
    end
  end

  ##############################################################################
  # RULE APPLICATION
  ##############################################################################

  defp apply_rule(:contradiction, state) do
    Logger.info("Branch #{state.id} closed explicitly.")
    broadcast_status(state.id, :closed, state)

    :ets.update_counter(state.ets_tables.stats, :branch_count, {2, -1})

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

    spawn_child_branch(sibling_id, b2, state)

    broadcast_status(state.id, :split, state)
    broadcast_status(my_new_id, :active, state)

    new_queue = insert_formula(state.queue, b1, state.params)
    %{state | id: my_new_id, queue: new_queue}
  end

  defp apply_rule({:instantiate, branches_stream, count}, %__MODULE__{} = state) do
    branches = Enum.to_list(branches_stream)

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

          broadcast_status(state.id, :split, state)
          broadcast_status(keep_child_id, :active, state)

          queue_with_unfolded =
            Enum.reduce(state.local_atoms, state.queue, fn term_id, acc_queue ->
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

          queue_with_unfolded =
            Enum.reduce(state.local_atoms, state.queue, fn term_id, acc_queue ->
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
        check_local_closures(term_id, state.local_atoms, state)

        new_atoms = [term_id | state.local_atoms]
        %{state | local_atoms: new_atoms}

      cf ->
        %{state | queue: FPQ.insert(state.queue, cf, state.params.formula_cost.(cf))}
    end
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp poisoned?(branch_id, ets_tables) do
    segments = String.split(branch_id, "_")

    prefixes =
      Enum.scan(segments, fn segment, acc -> acc <> "_" <> segment end)

    Enum.any?(prefixes, fn prefix ->
      :ets.member(ets_tables.tombs, prefix)
    end)
  end

  defp insert_formula(queue, formula, params) do
    cf = Rules.classify_formula(formula)
    c = params.formula_cost.(cf)

    FPQ.insert(queue, cf, c)
  end

  defp unfold_if_possible(term_id, defs) do
    case TF.get_term!(term_id) do
      %ShotDs.Data.Term{bvars: [], head: head, args: args} when is_map_key(defs, head) ->
        unfolded = app(Map.fetch!(defs, head), args)
        Rules.classify_formula(unfolded)

      _ ->
        case TF.get_term!(lit_neg(term_id)) do
          %ShotDs.Data.Term{bvars: [], head: head, args: args} when is_map_key(defs, head) ->
            unfolded = neg(app(Map.fetch!(defs, head), args))
            Rules.classify_formula(unfolded)

          _ ->
            nil
        end
    end
  end

  defp check_local_closures(new_term, existing_atoms, %__MODULE__{} = state) do
    if new_term == false_term() do
      trigger_local_ground_closure(state.id, state.session_id, state.ets_tables)
    else
      neg_new_term = lit_neg(new_term)

      closures =
        Enum.flat_map(existing_atoms, fn existing_term ->
          neg_existing = lit_neg(existing_term)

          sols1 =
            {neg_new_term, existing_term}
            |> ShotUn.unify(state.params.unify_depth)
            |> Enum.to_list()

          sols2 =
            {new_term, neg_existing}
            |> ShotUn.unify(state.params.unify_depth)
            |> Enum.to_list()

          sols1 ++ sols2
        end)

      if not Enum.empty?(closures) do
        has_ground_closure? =
          Enum.any?(closures, &(Enum.empty?(&1.substitutions) && Enum.empty?(&1.flex_pairs)))

        if has_ground_closure? do
          trigger_local_ground_closure(state.id, state.session_id, state.ets_tables)
        else
          ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
          GenServer.cast(ca_via, {:local_closures, state.id, closures})
        end
      end
    end
  end

  defp trigger_local_ground_closure(branch_id, session_id, ets_tables) do
    Logger.debug("Branch #{branch_id} found local ground closure. Initiating tombstone.")

    :ets.insert(ets_tables.tombs, {branch_id, true})

    Registry.dispatch(ShotTx.Prover.PubSub, "global_branch_control_#{session_id}", fn entries ->
      for {pid, _} <- entries, do: send(pid, {:poison_prefix, branch_id})
    end)
  end

  defp lit_neg(term_id) do
    case TF.get_term!(term_id) do
      negated(inner) -> inner
      _ -> neg(term_id)
    end
  end

  defp broadcast_status(branch_id, status, state) do
    Registry.dispatch(ShotTx.Prover.PubSub, "branch_events_#{state.session_id}", fn entries ->
      for {pid, _} <- entries, do: send(pid, {:branch_status, branch_id, status})
    end)
  end
end
