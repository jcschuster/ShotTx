defmodule ShotTx.Prover.BranchWorker do
  require Logger
  use GenServer
  alias ShotTx.Generation
  alias ShotTx.Generation.{GeneralBindings, TypeUniverse}
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Rules
  alias ShotTx.Prover.FormulaPqueue, as: FPQ
  alias ShotDs.Data.{Declaration, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl
  import ShotDs.Hol.Patterns

  @fresh_progress %{base_offset: 0, covered_types: MapSet.new()}

  defstruct id: nil,
            session_id: nil,
            ets_tables: %{},
            queue: nil,
            defs: %{},
            literals: MapSet.new(),
            params: %Parameters{},
            sleeping_gamma_rules: [],
            current_gamma_limit: 1,
            current_prim_depth_limit: 1,
            type_universe: MapSet.new()

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  def start_link(state), do: GenServer.start_link(__MODULE__, state)

  def start_branch(branch_id, formulas, defs \\ %{}, params, session_id, ets_tables) do
    state = %__MODULE__{
      id: branch_id,
      session_id: session_id,
      ets_tables: ets_tables,
      queue: Enum.reduce(formulas, FPQ.new(), &insert_formula(&2, &1, params)),
      defs: defs,
      literals: MapSet.new([true_term(), neg(false_term())]),
      params: params,
      current_gamma_limit: params.initial_gamma_limit,
      current_prim_depth_limit: params.initial_prim_limit,
      type_universe: TypeUniverse.from_formulas(formulas)
    }

    supervisor_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :branch_supervisor}}}

    DynamicSupervisor.start_child(supervisor_via, {__MODULE__, state})
  end

  def spawn_child_branch(child_id, new_formula, %__MODULE__{} = parent) do
    cond do
      :ets.lookup(parent.ets_tables.stats, :aborted) == [{:aborted, true}] ->
        :ok

      :ets.update_counter(parent.ets_tables.stats, :branch_count, {2, 1}) >
          parent.params.max_branches ->
        Logger.error("Branch limit (#{parent.params.max_branches}) exceeded! Aborting search.")

        Registry.dispatch(
          ShotTx.Prover.PubSub,
          "proof_results_#{parent.session_id}",
          fn entries ->
            Enum.each(entries, fn {pid, _} ->
              send(pid, {:proof_result, {:unknown, :max_branches_reached}})
            end)
          end
        )

      true ->
        do_spawn_child_branch(child_id, new_formula, parent)
    end
  end

  defp do_spawn_child_branch(child_id, new_formula, %__MODULE__{} = parent) do
    child = %__MODULE__{
      id: child_id,
      session_id: parent.session_id,
      ets_tables: parent.ets_tables,
      queue: insert_formula(parent.queue, new_formula, parent.params),
      defs: parent.defs,
      literals: parent.literals,
      params: parent.params,
      sleeping_gamma_rules: parent.sleeping_gamma_rules,
      current_gamma_limit: parent.current_gamma_limit,
      current_prim_depth_limit: parent.current_prim_depth_limit,
      type_universe: parent.type_universe
    }

    supervisor_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {parent.session_id, :branch_supervisor}}}

    DynamicSupervisor.start_child(supervisor_via, {__MODULE__, child})
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  def child_spec(state) do
    %{
      id: __MODULE__,
      start: {GenServer, :start_link, [__MODULE__, state, []]},
      restart: :transient
    }
  end

  @impl true
  def init(%__MODULE__{} = state) do
    Registry.register(ShotTx.Prover.PubSub, "branch_control_#{state.session_id}", [])

    if poisoned?(state.id, state.ets_tables) do
      {:stop, :normal, state}
    else
      {:ok, state, {:continue, :process_next}}
    end
  end

  @impl true
  def handle_info({:wake_up, new_gamma, new_prim_depth}, %__MODULE__{} = state) do
    Logger.debug(
      "Branch #{state.id} waking up. Gamma: #{new_gamma}, Prim depth: #{new_prim_depth}"
    )

    new_queue =
      Enum.reduce(state.sleeping_gamma_rules, state.queue, &reinsert_rule(&2, &1, state.params))

    new_state = %{
      state
      | current_gamma_limit: new_gamma,
        current_prim_depth_limit: new_prim_depth,
        sleeping_gamma_rules: [],
        queue: new_queue
    }

    broadcast_status(state.id, :active, state.session_id)
    {:noreply, new_state, {:continue, :process_next}}
  end

  @impl true
  def handle_info({:poison_prefix, prefix}, state) do
    if String.starts_with?(state.id, prefix) do
      Logger.debug("Branch #{state.id} caught poison from #{prefix}. Terminating.")
      broadcast_status(state.id, :closed, state.session_id)
      :ets.update_counter(state.ets_tables.stats, :branch_count, {2, -1})
      {:stop, :normal, state}
    else
      {:noreply, state}
    end
  end

  @impl true
  def handle_continue(:process_next, state) do
    cond do
      poisoned?(state.id, state.ets_tables) ->
        Logger.debug("Branch #{state.id} noticed it is poisoned. Terminating.")
        broadcast_status(state.id, :closed, state.session_id)
        safe_decrement(state.ets_tables)
        {:stop, :normal, state}

      FPQ.empty?(state.queue) and state.sleeping_gamma_rules != [] ->
        broadcast_status(state.id, :idle, state.session_id)
        {:noreply, state}

      FPQ.empty?(state.queue) ->
        Logger.info("Branch #{state.id} fully saturated. Found a counter-model!")
        broadcast_status(state.id, {:saturated, {state.defs, state.literals}}, state.session_id)
        :ets.update_counter(state.ets_tables.stats, :branch_count, {2, -1})
        {:stop, :normal, state}

      true ->
        {cf, rest} = FPQ.take_smallest(state.queue)

        case apply_rule(cf, %{state | queue: rest}) do
          {:stop, reason, final} -> {:stop, reason, final}
          new_state -> {:noreply, new_state, {:continue, :process_next}}
        end
    end
  end

  ##############################################################################
  # RULE APPLICATION
  ##############################################################################

  defp apply_rule(:contradiction, state) do
    Logger.info("Branch #{state.id} closed explicitly.")
    broadcast_status(state.id, :closed, state.session_id)
    :ets.update_counter(state.ets_tables.stats, :branch_count, {2, -1})
    {:stop, :normal, state}
  end

  defp apply_rule(:tautology, state), do: state

  # --- Linear decompositions -------------------------------------------------

  defp apply_rule({:alpha, formulas}, state) do
    %{state | queue: Enum.reduce(formulas, state.queue, &insert_formula(&2, &1, state.params))}
  end

  defp apply_rule({:delta, sk_term_id}, state) do
    %{
      state
      | queue: insert_formula(state.queue, sk_term_id, state.params),
        type_universe: register_new_types(state.type_universe, sk_term_id)
    }
  end

  defp apply_rule({:rename, {t1, t2}}, state) do
    new_queue = Enum.reduce([t1, t2], state.queue, &insert_formula(&2, &1, state.params))

    new_universe =
      state.type_universe |> register_new_types(t1) |> register_new_types(t2)

    %{state | queue: new_queue, type_universe: new_universe}
  end

  # --- Branching --------------------------------------------------------------

  defp apply_rule({:beta, {b1, b2}}, state) do
    my_id = state.id <> "_A"
    sib_id = state.id <> "_B"

    broadcast_status(my_id, :active, state.session_id)
    broadcast_status(sib_id, :active, state.session_id)
    broadcast_status(state.id, :split, state.session_id)

    spawn_child_branch(sib_id, b2, state)

    %{state | id: my_id, queue: insert_formula(state.queue, b1, state.params)}
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
        {{keep_term, {k_decl, k_tid}}, ^keep_idx}, _acc ->
          new_defs = Map.put(state.defs, k_decl, k_tid)
          keep_id = "#{state.id}_K"

          broadcast_status(keep_id, :active, state.session_id)
          broadcast_status(state.id, :split, state.session_id)

          queue =
            state.literals
            |> unfold_literals(state.queue, new_defs, state.params)
            |> insert_formula(keep_term, state.params)

          %{state | id: keep_id, queue: queue, defs: new_defs}

        {{b_term, {decl, tid}}, idx}, acc ->
          new_defs = Map.put(state.defs, decl, tid)
          child_id = "#{state.id}_I#{idx}"

          broadcast_status(child_id, :active, state.session_id)

          queue = unfold_literals(state.literals, state.queue, new_defs, state.params)

          child = %{state | id: child_id, queue: queue, defs: new_defs}
          spawn_child_branch(child_id, b_term, child)

          acc
      end)
    end
  end

  # --- Gamma (fresh variable instantiation) -----------------------------------

  defp apply_rule({:gamma, recipe, type, prev} = rule, state) do
    if prev >= state.current_gamma_limit do
      %{state | sleeping_gamma_rules: [rule | state.sleeping_gamma_rules]}
    else
      instantiated = app(recipe, TF.make_fresh_var_term(type))
      updated_gamma = {:gamma, recipe, type, prev + 1}

      queue =
        state.queue
        |> insert_formula(instantiated, state.params)
        |> reinsert_rule(updated_gamma, state.params)

      # Seed the companion prim_subst rule on the first instantiation, but
      # only for types targeting :o (general bindings require a propositional
      # goal type).
      queue =
        if prev == 0 and type.goal == :o do
          reinsert_rule(queue, {:prim_subst, recipe, type, 1, @fresh_progress}, state.params)
        else
          queue
        end

      %{state | queue: queue}
    end
  end

  defp apply_rule({:gamma_finite, recipe, type}, state) do
    new_queue =
      type
      |> Generation.gen_o()
      |> Enum.reduce(state.queue, fn tid, q ->
        insert_formula(q, app(recipe, tid), state.params)
      end)

    %{state | queue: new_queue}
  end

  # --- Primitive substitution (general bindings) ------------------------------

  defp apply_rule({:prim_subst, recipe, type, depth, progress}, state) do
    batch = state.params.prim_subst_batch_size
    args = type.args

    # Phase 1: polymorphic bindings for types not yet covered at this depth.
    new_types = MapSet.difference(state.type_universe, progress.covered_types)

    poly =
      if MapSet.size(new_types) > 0 do
        args
        |> GeneralBindings.polymorphic_heads(depth, new_types)
        |> Enum.map(&GeneralBindings.build_binding(args, &1))
      else
        []
      end

    covered = MapSet.union(progress.covered_types, new_types)

    # Phase 2: base (propositional) bindings for remaining batch capacity.
    base_cap = max(0, batch - length(poly))

    base =
      args
      |> GeneralBindings.base_heads(depth)
      |> Enum.drop(progress.base_offset)
      |> Enum.take(base_cap)
      |> Enum.map(&GeneralBindings.build_binding(args, &1))

    bindings = poly ++ base

    if bindings == [] do
      advance_or_sleep(recipe, type, depth, state)
    else
      queue =
        Enum.reduce(bindings, state.queue, fn binding, q ->
          insert_formula(q, app(recipe, binding), state.params)
        end)

      new_progress = %{
        base_offset: progress.base_offset + length(base),
        covered_types: covered
      }

      %{
        state
        | queue:
            reinsert_rule(queue, {:prim_subst, recipe, type, depth, new_progress}, state.params)
      }
    end
  end

  # --- Atoms ------------------------------------------------------------------

  defp apply_rule({:atomic, term_id}, state) do
    case unfold_if_possible(term_id, state.defs) do
      nil ->
        check_local_clashes(term_id, state.literals, state)
        %{state | literals: MapSet.put(state.literals, term_id)}

      cf ->
        %{state | queue: FPQ.insert(state.queue, cf, state.params.formula_cost.(cf))}
    end
  end

  ##############################################################################
  # PRIM_SUBST HELPERS
  ##############################################################################

  # All bindings at the current depth have been exhausted. Either advance to
  # the next depth (within the limit) or park the rule for the next iterative
  # deepening round. Progress is reset because deeper depths produce different
  # composed specifications for every type.
  defp advance_or_sleep(recipe, type, depth, state) do
    next = depth + 1
    rule = {:prim_subst, recipe, type, next, @fresh_progress}

    if next <= state.current_prim_depth_limit do
      %{state | queue: reinsert_rule(state.queue, rule, state.params)}
    else
      %{state | sleeping_gamma_rules: [rule | state.sleeping_gamma_rules]}
    end
  end

  ##############################################################################
  # TYPE UNIVERSE MAINTENANCE
  ##############################################################################

  # Walks a term and extends the universe with the types of any fresh constants
  # (skolem symbols or rename constants, identified by reference names).
  @spec register_new_types(MapSet.t(Type.t()), Term.term_id()) :: MapSet.t(Type.t())
  defp register_new_types(universe, term_id) do
    %Term{head: head, args: args} = TF.get_term!(term_id)

    universe =
      case head do
        %Declaration{kind: :co, name: name, type: type} when is_reference(name) ->
          TypeUniverse.extend(universe, type)

        _ ->
          universe
      end

    Enum.reduce(args, universe, &register_new_types(&2, &1))
  end

  ##############################################################################
  # GENERAL HELPERS
  ##############################################################################

  defp poisoned?(branch_id, ets_tables) do
    segments = String.split(branch_id, "_")
    prefixes = Enum.scan(segments, fn seg, acc -> acc <> "_" <> seg end)

    try do
      Enum.any?(prefixes, &:ets.member(ets_tables.tombs, &1))
    rescue
      ArgumentError -> true
    end
  end

  defp insert_formula(queue, formula, params) do
    cf = Rules.classify_formula(formula)
    FPQ.insert(queue, cf, params.formula_cost.(cf))
  end

  defp reinsert_rule(queue, rule, params) do
    FPQ.insert(queue, rule, params.formula_cost.(rule))
  end

  defp unfold_if_possible(term_id, defs) do
    case TF.get_term!(term_id) do
      %Term{bvars: [], head: head, args: args} when is_map_key(defs, head) ->
        unfolded = app(Map.fetch!(defs, head), args)
        Rules.classify_formula(unfolded)

      _ ->
        case TF.get_term!(lit_neg(term_id)) do
          %Term{bvars: [], head: head, args: args} when is_map_key(defs, head) ->
            Rules.classify_formula(neg(app(Map.fetch!(defs, head), args)))

          _ ->
            nil
        end
    end
  end

  defp unfold_literals(literals, queue, defs, params) do
    Enum.reduce(literals, queue, fn tid, q ->
      case unfold_if_possible(tid, defs) do
        nil -> q
        cf -> FPQ.insert(q, cf, params.formula_cost.(cf))
      end
    end)
  end

  defp check_local_clashes(new_term, existing, %__MODULE__{} = state) do
    neg_new = lit_neg(new_term)

    if MapSet.member?(state.literals, neg_new) do
      trigger_local_ground_closure(state.id, state.session_id, state.ets_tables)
    else
      clashes =
        Enum.reduce(existing, MapSet.new(), fn existing_term, acc ->
          neg_existing = lit_neg(existing_term)

          for pair <- [{neg_new, existing_term}, {new_term, neg_existing}],
              !Enum.empty?(ShotUn.unify(pair, state.params.unification_depth)),
              into: acc,
              do: pair
        end)

      if MapSet.size(clashes) > 0 do
        ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
        GenServer.cast(ca_via, {:local_clashes, state.id, clashes})
      end
    end
  end

  defp trigger_local_ground_closure(branch_id, session_id, ets_tables) do
    Logger.debug("Branch #{branch_id} found local ground closure. Initiating tombstone.")
    :ets.insert(ets_tables.tombs, {branch_id, true})

    Registry.dispatch(ShotTx.Prover.PubSub, "branch_control_#{session_id}", fn entries ->
      for {pid, _} <- entries, do: send(pid, {:poison_prefix, branch_id})
    end)
  end

  defp lit_neg(term_id) do
    case TF.get_term!(term_id) do
      negated(inner) -> inner
      _ -> neg(term_id)
    end
  end

  defp safe_decrement(ets_tables) do
    :ets.update_counter(ets_tables.stats, :branch_count, {2, -1})
  rescue
    ArgumentError ->
      Logger.debug("Could not decrement branch counter — ETS already gone.")
  end

  defp broadcast_status(branch_id, status, session_id) do
    Registry.dispatch(ShotTx.Prover.PubSub, "branch_events_#{session_id}", fn entries ->
      for {pid, _} <- entries, do: send(pid, {:branch_status, branch_id, status})
    end)
  end
end
