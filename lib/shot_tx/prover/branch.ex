defmodule ShotTx.Prover.Branch do
  @moduledoc """
  Pure functional core representing a single branch in the proof tree.
  Applies rules and returns the resulting state and any intended side-effects
  (Outbox pattern) for the stateful Worker to execute.

  ## History format

  Each history entry is a triple `{source | nil, rule, [produced_id]}`:

  * `source`   — term id of the formula that was processed. Reinserted γ /
                 prim_subst rules carry the originating formula's id
                 through the queue, so every entry is tagged with a real
                 parent.
  * `rule`     — the classified rule tuple from `Rules`.
  * `produced` — term ids of the formulas that this rule spawned onto the
                 branch. For β / `instantiate`, the produced list mirrors
                 the sibling branches.

  History is recorded _inside_ `apply_rule/6` after the rule runs, so the
  `produced` list is exact and `{:closed, branch}` carries a branch whose
  history includes the closing step.
  """

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
            queue: nil,
            defs: %{},
            literals: MapSet.new(),
            sleeping_gamma_rules: [],
            type_universe: MapSet.new(),
            history: []

  @type history_entry ::
          {Term.term_id() | nil, Rules.rule_t(), [Term.term_id()]}

  @type effect :: :no_effects | {:notify_ca, MapSet.t(), [history_entry()]}
  @type step_result ::
          {:continue, %__MODULE__{}, effect}
          | {:split, my_branch :: %__MODULE__{}, sibling :: %__MODULE__{}}
          | {:instantiate, branches :: [%__MODULE__{}]}
          | {:idle, %__MODULE__{}}
          | {:saturated, {defs :: map(), literals :: MapSet.t()}}
          | {:closed, %__MODULE__{}}

  ##############################################################################
  # INITIALIZATION
  ##############################################################################

  @doc """
  Constructs a new root branch or an explicitly defined child branch.
  """
  def new(id, formulas, defs \\ %{}, params) do
    %__MODULE__{
      id: id,
      queue: Enum.reduce(formulas, FPQ.new(), &insert_formula(&2, &1, params.formula_cost)),
      defs: defs,
      literals: MapSet.new([true_term(), neg(false_term())]),
      type_universe: TypeUniverse.from_formulas(formulas)
    }
  end

  ##############################################################################
  # STEP / EXECUTION LOGIC
  ##############################################################################

  @doc """
  Pops the next formula/rule from the queue and applies it. Returns a tuple
  instructing the Worker on how to proceed. History is recorded inside
  `apply_rule/6`.
  """
  @spec step(%__MODULE__{}, %Parameters{}, integer(), integer()) :: step_result()
  def step(%__MODULE__{} = branch, params, gamma_limit, prim_limit) do
    cond do
      FPQ.empty?(branch.queue) and branch.sleeping_gamma_rules != [] ->
        {:idle, branch}

      FPQ.empty?(branch.queue) ->
        {:saturated, {branch.defs, branch.literals}}

      true ->
        {{source, cf}, rest_queue} = FPQ.take_smallest(branch.queue)
        popped_branch = %{branch | queue: rest_queue}
        apply_rule(cf, source, popped_branch, params, gamma_limit, prim_limit)
    end
  end

  @doc """
  Wakes up a sleeping branch by reinserting its sleeping gamma rules into the queue.
  """
  def wake_up(%__MODULE__{} = branch, cost_fn) do
    new_queue =
      Enum.reduce(branch.sleeping_gamma_rules, branch.queue, fn {source, rule}, acc ->
        reinsert_rule(acc, source, rule, cost_fn)
      end)

    %{branch | sleeping_gamma_rules: [], queue: new_queue}
  end

  ##############################################################################
  # RULE APPLICATION
  ##############################################################################

  defp apply_rule(:contradiction, source, branch, _params, _g_limit, _p_limit) do
    {:closed, record(branch, source, :contradiction, [])}
  end

  defp apply_rule(:tautology, source, branch, _params, _g_limit, _p_limit) do
    {:continue, record(branch, source, :tautology, []), :no_effects}
  end

  # --- Linear decompositions --------------------------------------------------

  defp apply_rule({:alpha, formulas} = rule, source, branch, params, _g_limit, _p_limit) do
    queue = Enum.reduce(formulas, branch.queue, &insert_formula(&2, &1, params.formula_cost))

    updated =
      %{branch | queue: queue}
      |> record(source, rule, formulas)

    {:continue, updated, :no_effects}
  end

  defp apply_rule({:delta, sk_term_id} = rule, source, branch, params, _g_limit, _p_limit) do
    updated =
      %{
        branch
        | queue: insert_formula(branch.queue, sk_term_id, params.formula_cost),
          type_universe: register_new_types(branch.type_universe, sk_term_id)
      }
      |> record(source, rule, [sk_term_id])

    {:continue, updated, :no_effects}
  end

  defp apply_rule({:rename, {t1, t2}} = rule, source, branch, params, _g_limit, _p_limit) do
    new_queue = Enum.reduce([t1, t2], branch.queue, &insert_formula(&2, &1, params.formula_cost))
    new_universe = branch.type_universe |> register_new_types(t1) |> register_new_types(t2)

    updated =
      %{branch | queue: new_queue, type_universe: new_universe}
      |> record(source, rule, [t1, t2])

    {:continue, updated, :no_effects}
  end

  # --- Branching --------------------------------------------------------------

  defp apply_rule({:beta, {b1, b2}} = rule, source, branch, params, _g_limit, _p_limit) do
    # The β step is the last shared history entry for both sibling branches.
    recorded = record(branch, source, rule, [b1, b2])

    my_id = recorded.id <> "_A"
    sib_id = recorded.id <> "_B"

    sib_branch = %{
      recorded
      | id: sib_id,
        queue: insert_formula(recorded.queue, b2, params.formula_cost)
    }

    my_branch = %{
      recorded
      | id: my_id,
        queue: insert_formula(recorded.queue, b1, params.formula_cost)
    }

    {:split, my_branch, sib_branch}
  end

  defp apply_rule({:instantiate, branches_stream, count} = rule, source, branch, params, _g, _p) do
    branches = Enum.to_list(branches_stream)

    if count == 0 do
      {:continue, record(branch, source, rule, []), :no_effects}
    else
      produced = Enum.map(branches, fn {b_term, _def} -> b_term end)
      recorded = record(branch, source, rule, produced)

      final_branches =
        branches
        |> Stream.with_index()
        |> Enum.reduce([], fn
          {{b_term, {decl, tid}}, idx}, acc_branches ->
            new_defs = Map.put(recorded.defs, decl, tid)

            queue =
              unfold_literals(recorded.literals, recorded.queue, new_defs, params.formula_cost)

            queue = insert_formula(queue, b_term, params.formula_cost)

            c_branch = %{recorded | id: "#{recorded.id}_I#{idx}", queue: queue, defs: new_defs}
            [c_branch | acc_branches]
        end)

      {:instantiate, final_branches}
    end
  end

  # --- Gamma (fresh variable instantiation) -----------------------------------

  defp apply_rule({:gamma, recipe, type, prev} = rule, source, branch, params, gamma_limit, _p) do
    if prev >= gamma_limit do
      updated =
        %{branch | sleeping_gamma_rules: [{source, rule} | branch.sleeping_gamma_rules]}
        |> record(source, rule, [])

      {:continue, updated, :no_effects}
    else
      instantiated = app(recipe, TF.make_fresh_var_term(type))
      updated_gamma = {:gamma, recipe, type, prev + 1}

      queue =
        branch.queue
        |> insert_formula(instantiated, params.formula_cost)
        |> reinsert_rule(source, updated_gamma, params.formula_cost)

      queue =
        if prev == params.prim_subst_after and type.goal == :o do
          reinsert_rule(
            queue,
            source,
            {:prim_subst, recipe, type, 1, @fresh_progress},
            params.formula_cost
          )
        else
          queue
        end

      updated =
        %{branch | queue: queue}
        |> record(source, rule, [instantiated])

      {:continue, updated, :no_effects}
    end
  end

  defp apply_rule({:gamma_finite, recipe, type} = rule, source, branch, params, _g, _p) do
    instances = type |> Generation.gen_o() |> Enum.map(&app(recipe, &1))

    new_queue =
      Enum.reduce(instances, branch.queue, fn inst, q ->
        insert_formula(q, inst, params.formula_cost)
      end)

    updated =
      %{branch | queue: new_queue}
      |> record(source, rule, instances)

    {:continue, updated, :no_effects}
  end

  # --- Primitive substitution (general bindings) ------------------------------

  defp apply_rule(
         {:prim_subst, recipe, type, depth, progress} = rule,
         source,
         branch,
         params,
         _g_limit,
         prim_limit
       ) do
    batch = params.prim_subst_batch_size
    args = type.args

    new_types = MapSet.difference(branch.type_universe, progress.covered_types)

    poly =
      if MapSet.size(new_types) > 0 do
        args
        |> GeneralBindings.polymorphic_heads(depth, new_types)
        |> Enum.map(&GeneralBindings.build_binding(args, &1))
      else
        []
      end

    covered = MapSet.union(progress.covered_types, new_types)
    base_cap = max(0, batch - length(poly))

    base =
      args
      |> GeneralBindings.base_heads(depth)
      |> Enum.drop(progress.base_offset)
      |> Enum.take(base_cap)
      |> Enum.map(&GeneralBindings.build_binding(args, &1))

    bindings = poly ++ base

    if bindings == [] do
      advance_or_sleep(recipe, type, depth, branch, params, prim_limit, source, rule)
    else
      instances = Enum.map(bindings, &app(recipe, &1))

      queue =
        Enum.reduce(instances, branch.queue, fn inst, q ->
          insert_formula(q, inst, params.formula_cost)
        end)

      new_progress = %{
        base_offset: progress.base_offset + length(base),
        covered_types: covered
      }

      new_rule = {:prim_subst, recipe, type, depth, new_progress}

      updated =
        %{branch | queue: reinsert_rule(queue, source, new_rule, params.formula_cost)}
        |> record(source, rule, instances)

      {:continue, updated, :no_effects}
    end
  end

  # --- Atoms ------------------------------------------------------------------

  defp apply_rule({:atomic, term_id} = rule, source, branch, params, _g_limit, _p_limit) do
    case unfold_if_possible(term_id, branch.defs) do
      nil ->
        case check_local_clashes(term_id, branch.literals, params) do
          :ground_closure ->
            updated =
              %{branch | literals: MapSet.put(branch.literals, term_id)}
              |> record(source, rule, [])

            {:closed, updated}

          {:clashes_found, new_clashes} ->
            updated =
              %{branch | literals: MapSet.put(branch.literals, term_id)}
              |> record(source, rule, [])

            {:continue, updated, {:notify_ca, new_clashes, Enum.reverse(updated.history)}}

          :ok ->
            updated =
              %{branch | literals: MapSet.put(branch.literals, term_id)}
              |> record(source, rule, [])

            {:continue, updated, :no_effects}
        end

      {unfolded_source, cf} ->
        queue =
          FPQ.insert(
            branch.queue,
            {unfolded_source, cf},
            params.formula_cost.(cf)
          )

        updated =
          %{branch | queue: queue}
          |> record(source, rule, [unfolded_source])

        {:continue, updated, :no_effects}
    end
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp advance_or_sleep(recipe, type, depth, branch, params, prim_limit, source, source_rule) do
    next = depth + 1
    new_rule = {:prim_subst, recipe, type, next, @fresh_progress}

    updated_branch =
      if next <= prim_limit do
        %{branch | queue: reinsert_rule(branch.queue, source, new_rule, params.formula_cost)}
      else
        %{branch | sleeping_gamma_rules: [{source, new_rule} | branch.sleeping_gamma_rules]}
      end

    {:continue, record(updated_branch, source, source_rule, []), :no_effects}
  end

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

  defp insert_formula(queue, formula, cost_fn) do
    cf = Rules.classify_formula(formula)
    FPQ.insert(queue, {formula, cf}, cost_fn.(cf))
  end

  defp reinsert_rule(queue, source, rule, cost_fn) do
    FPQ.insert(queue, {source, rule}, cost_fn.(rule))
  end

  defp record(branch, source, rule, produced) do
    %{branch | history: [{source, rule, produced} | branch.history]}
  end

  defp unfold_if_possible(term_id, defs) do
    unfolded = ShotDs.Stt.Semantics.unfold_defs!(term_id, defs)

    if unfolded == term_id do
      nil
    else
      {unfolded, Rules.classify_formula(unfolded)}
    end
  end

  defp unfold_literals(literals, queue, defs, cost_fn) do
    Enum.reduce(literals, queue, fn tid, q ->
      case unfold_if_possible(tid, defs) do
        nil -> q
        {_source, cf} = wrapped -> FPQ.insert(q, wrapped, cost_fn.(cf))
      end
    end)
  end

  defp check_local_clashes(new_term, existing, params) do
    neg_new = lit_neg(new_term)

    if MapSet.member?(existing, neg_new) do
      :ground_closure
    else
      clashes =
        Enum.reduce(existing, MapSet.new(), fn existing_term, acc ->
          neg_existing = lit_neg(existing_term)

          for pair <- [{neg_new, existing_term}, {new_term, neg_existing}],
              !Enum.empty?(ShotUn.unify(pair, params.unification_depth)),
              into: acc,
              do: pair
        end)

      if MapSet.size(clashes) > 0 do
        {:clashes_found, clashes}
      else
        :ok
      end
    end
  end

  defp lit_neg(term_id) do
    case TF.get_term!(term_id) do
      negated(inner) -> inner
      _ -> neg(term_id)
    end
  end
end
