defmodule ShotTx.Prover.Branch do
  @moduledoc """
  Pure functional core representing a single branch in the proof tree.
  Applies rules and returns the resulting state and any intended side-effects
  (Outbox pattern) for the stateful Worker to execute.

  ## History format

  Each history entry is a triple `{source | nil, rule, [produced_id]}`:

  * `source`   — term id of the formula that was processed. Reinserted gamma /
                 prim_subst rules carry the originating formula's id through the
                 queue, so every entry is tagged with a real parent.
  * `rule`     — the classified rule tuple from `Rules`.
  * `produced` — term ids of the formulas that this rule spawned onto the
                 branch. For beta / `instantiate`, the produced list mirrors the
                 sibling branches.

  History is recorded _inside_ `apply_rule/6` after the rule runs, so the
  `produced` list is exact and `{:closed, branch}` carries a branch whose
  history includes the closing step.

  ## Equality handling

  Every formula added to the branch is run through `insert_formula/5`. This
  preserves the existing decomposition of equality via the
  `:equality_expansion` rule (Leibniz / extensional / o-type iff) and
  additionally invokes `ShotTx.Prover.Demodulation` at two points:

    * **Forward demodulation** — `maybe_demodulate/3` inside
      `insert_formula/5` reduces every incoming term to normal form under
      the current `branch.equations` before it lands on the queue.
    * **Backward demodulation** — when `ingest_equation/4` records a new
      equation, `backward_demodulate/3` re-normalizes every existing
      branch literal under the enlarged equation set and discards any that
      changed.

  Both are traced. A rewrite is buffered in `pending_rewrites` and committed
  by the next `record/4` just after the rule that triggered it, so replaying
  the history yields the terms the branch actually holds — the rule's raw
  output, then its normal form. An untraced rewrite would leave every step
  downstream of it citing a formula the trace never produced.

  Only rewrites whose matcher σ is the empty substitution are admitted (the
  equation LHS must be structurally identical to the target subterm, or a
  primitive η-expansion `λv̄. h(v̄)` matching an applied subterm's head
  declaration). No variable is ever bound at the branch level; free-variable
  commitments are reconciled globally by `ShotTx.Prover.ContradictionAgent`.
  See `ShotTx.Prover.Paramodulation`'s moduledoc for the soundness argument.

  The `:instantiate` rule additionally performs *dual instantiation*: the
  source literal is treated as an atom on the branch in addition to the
  lazily-instantiated variants being branched on.
  """

  alias ShotTx.Generation
  alias ShotTx.Generation.{GeneralBindings, TypeUniverse}
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.{Demodulation, LambdaLift, Paramodulation, Provenance, Rules, TermOrder}
  alias ShotTx.Util.PropSimplify
  alias ShotTx.Prover.FormulaPqueue, as: FPQ
  alias ShotDs.Data.{Declaration, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Stt.Semantics
  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl
  import ShotDs.Hol.Patterns

  @fresh_progress %{
    base_offset: 0,
    covered_types: MapSet.new(),
    covered_constants: MapSet.new()
  }

  @hol_connective_names ~w(⊤ ⊥ ¬ ∨ ∧ ⊃ ≡ = ∀ ∃)

  defstruct id: nil,
            queue: nil,
            defs: %{},
            equations: %{},
            equation_origins: %{},
            literals: MapSet.new(),
            sleeping_gamma_rules: [],
            type_universe: MapSet.new(),
            ground_terms: %{},
            history: [],
            pending_rewrites: [],
            last_clash: nil,
            processed_rules: MapSet.new(),
            term_ids: MapSet.new(),
            pending_closure: nil,
            frontier: MapSet.new(),
            frontier_version: 0

  @type t :: %__MODULE__{}

  @type history_entry ::
          {Term.term_id() | nil, Rules.rule_t(), [Term.term_id()]}

  @type effect ::
          :no_effects
          | {:notify_ca, MapSet.t()}
          | {:record_provenance, [{Term.term_id(), Provenance.t()}]}
  @type step_result ::
          {:continue, %__MODULE__{}, effect()}
          | {:split, my_branch :: %__MODULE__{}, sibling :: %__MODULE__{}}
          | {:instantiate, branches :: [%__MODULE__{}]}
          | {:idle, %__MODULE__{}}
          | {:saturated, {defs :: map(), literals :: MapSet.t()}}
          | {:exhausted, %__MODULE__{}}
          | {:closed, %__MODULE__{}}

  ##############################################################################
  # INITIALIZATION
  ##############################################################################

  @doc """
  Constructs a new root branch or an explicitly defined child branch.
  """
  @spec new(String.t(), [Term.term_id()], Parameters.t(), keyword()) :: %__MODULE__{}
  def new(id, formulas, params, opts \\ []) do
    defs = Keyword.get(opts, :defs, %{})
    equations = Keyword.get(opts, :equations, %{})

    {expanded_formulas, lift_history} = lift_user_formulas(formulas)

    skel = %__MODULE__{
      id: id,
      queue: FPQ.new(),
      defs: defs,
      equations: equations,
      literals: MapSet.new([true_term(), neg(false_term())]),
      term_ids: MapSet.new([true_term(), neg(false_term())]),
      type_universe: TypeUniverse.from_formulas(expanded_formulas),
      history: lift_history,
      frontier: MapSet.new(expanded_formulas),
      frontier_version: 0
    }

    expanded_formulas
    |> Enum.reduce(skel, &insert_formula(&2, &1, defs, params))
    |> then(fn b -> Enum.reduce(expanded_formulas, b, &ingest_formula(&2, &1, params)) end)
    |> flush_rewrites()
  end

  # Runs lambda-lifting once per user formula. For each formula that produces
  # axioms, records a `:lambda_lift` history entry sourced at the original
  # formula. Returns the expanded formula list (lifted form + axioms in place
  # of any lifted original) and the history pre-populated in newest-first
  # order, so chronological replay shows lifts before any rule firing.
  defp lift_user_formulas(formulas) do
    {expanded_rev, history_chrono} =
      Enum.reduce(formulas, {[], []}, fn formula, {acc_terms, acc_hist} ->
        case LambdaLift.lift(formula) do
          {^formula, []} ->
            {[formula | acc_terms], acc_hist}

          {lifted, axioms} ->
            produced = [lifted | axioms]
            entry = {formula, :lambda_lift, produced}
            {Enum.reverse(produced) ++ acc_terms, [entry | acc_hist]}
        end
      end)

    {Enum.reverse(expanded_rev), history_chrono}
  end

  ##############################################################################
  # STEP / EXECUTION LOGIC
  ##############################################################################

  @doc """
  Splices a synthetic `{:suggested_instantiate, recipe, term}` rule onto
  the branch's priority queue. Called by `Worker` when it consumes a
  suggestion from the `:suggestions` ETS table — the rule enters the
  ordinary popping loop and fires via the dedicated `apply_rule/6` clause,
  which adds `app(recipe, term)` to the branch without spawning a child.
  """
  @spec splice_suggested_instantiate(
          t(),
          Term.term_id(),
          Term.term_id(),
          Term.term_id() | nil,
          Parameters.t()
        ) :: t()
  def splice_suggested_instantiate(%__MODULE__{} = branch, recipe, term, source, params) do
    rule = {:suggested_instantiate, recipe, term}
    %{branch | queue: reinsert_rule(branch.queue, source, rule, params.formula_cost)}
  end

  @doc """
  Pops the next formula/rule from the queue and applies it. Returns a tuple
  instructing the Worker on how to proceed. History is recorded inside
  `apply_rule/6`.
  """
  @spec step(%__MODULE__{}, Parameters.t(), non_neg_integer(), non_neg_integer()) :: step_result()
  def step(%__MODULE__{} = branch, params, gamma_limit, prim_limit) do
    cond do
      branch.pending_closure != nil ->
        {source, partner} = branch.pending_closure
        {:closed, record(branch, source, :contradiction, [partner])}

      FPQ.empty?(branch.queue) and not Enum.empty?(branch.sleeping_gamma_rules) ->
        {:idle, branch}

      FPQ.empty?(branch.queue) and model_certain?(branch.literals, branch.equations) ->
        {:saturated, {branch.defs, branch.literals}}

      FPQ.empty?(branch.queue) ->
        {:exhausted, branch}

      true ->
        {{source, cf}, rest_queue} = FPQ.take_smallest(branch.queue)
        popped_branch = %{branch | queue: rest_queue}
        processed = branch.processed_rules

        if MapSet.member?(processed, cf) do
          step(popped_branch, params, gamma_limit, prim_limit)
        else
          updated_branch = %{popped_branch | processed_rules: MapSet.put(processed, cf)}

          {eff_source, eff_cf, branch_after_simp} =
            simplify_formula(source, cf, updated_branch, params)

          apply_rule(eff_cf, eff_source, branch_after_simp, params, gamma_limit, prim_limit)
        end
    end
  end

  @doc """
  Whether a rule-exhausted branch's literal set may be reported as a
  countermodel.

  An empty queue means no *syntactic* rule is left to fire. That is weaker than
  satisfiability: literals `p s̄` and `¬(p t̄)` are complementary as soon as `s̄`
  and `t̄` denote the same values, and ShotTx decides that only inside the
  fragment its equational machinery covers — syntactically identical terms
  (ground closure), unifiable terms (clash candidates handed to the CSP), and
  terms related by an oriented equation (demodulation). Extensional equality of
  two closed λ-terms is left open, so a branch holding `P (λ…)` and `¬(P (λ…))`
  for two extensionally equal but syntactically different arguments has *not*
  been shown satisfiable. Calling it a countermodel is unsound; it is merely
  exhausted, and `step/4` reports it as `:exhausted` instead.

  Returns `true` only when every same-head, opposite-polarity literal pair is
  separated at some argument position by two distinct rigid base-type terms —
  the case a free term model can satisfy by interpreting them as distinct
  elements. `p a` against `¬(p b)` for distinct base constants `a`, `b` is
  therefore still a genuine countermodel.
  """
  @spec model_certain?(MapSet.t(Term.term_id()), %{Term.term_id() => MapSet.t()}) :: boolean()
  def model_certain?(literals, equations) do
    {negative, positive} = literals |> MapSet.to_list() |> Enum.split_with(&negated_literal?/1)
    negative_atoms = Enum.map(negative, &lit_neg/1)

    Enum.all?(positive, fn pos ->
      Enum.all?(negative_atoms, &separated?(pos, &1, equations))
    end)
  end

  defp negated_literal?(term_id), do: match?(negated(_), TF.get_term!(term_id))

  # Can this positive/negative atom pair still turn out complementary?
  defp separated?(positive_atom, negative_atom, equations) do
    p = TF.get_term!(positive_atom)
    n = TF.get_term!(negative_atom)

    cond do
      # Two different rigid heads can never be identified, whatever the
      # arguments denote.
      rigid_head?(p) and rigid_head?(n) and p.head != n.head -> true
      length(p.args) != length(n.args) -> true
      true -> Enum.any?(Enum.zip(p.args, n.args), &distinguishable?(&1, equations))
    end
  end

  defp rigid_head?(%Term{head: %Declaration{kind: :co}}), do: true
  defp rigid_head?(%Term{}), do: false

  # A pair of arguments a free term model may interpret as distinct elements:
  # distinct rigid constants at a base type, neither rewritable by one of the
  # branch's equations. Anything of functional or `$o` type is excluded — that
  # is exactly where extensionality would be needed and is not available.
  defp distinguishable?({same, same}, _equations), do: false

  defp distinguishable?({s, t}, equations) do
    base_typed_rigid?(s) and base_typed_rigid?(t) and
      not Map.has_key?(equations, s) and not Map.has_key?(equations, t) and
      rigid_terms_distinct?(s, t, equations)
  end

  # Rigidity of the *head* is not enough: `h ⊤` and `h ⊥` are two closed rigid
  # base-typed terms, yet no model keeps them apart unless `f ⊤` and `f ⊥` are
  # already apart — and at type `o` they never are, the domain having two
  # elements and `h` no obligation to be injective. Distinct rigid constants
  # separate outright; equal heads only through an argument pair that separates
  # in turn.
  defp rigid_terms_distinct?(s, t, equations) do
    term_s = TF.get_term!(s)
    term_t = TF.get_term!(t)

    cond do
      term_s.head != term_t.head -> true
      length(term_s.args) != length(term_t.args) -> false
      true -> Enum.any?(Enum.zip(term_s.args, term_t.args), &distinguishable?(&1, equations))
    end
  end

  defp base_typed_rigid?(term_id) do
    term = TF.get_term!(term_id)

    match?(%Type{goal: goal, args: []} when goal != :o, term.type) and
      term.bvars == [] and term.head.kind == :co and MapSet.size(term.fvars) == 0
  end

  @doc """
  Wakes up a sleeping branch by reinserting its sleeping gamma rules into the
  queue.
  """
  @spec wake_up(%__MODULE__{}, (Rules.rule_t() -> non_neg_integer())) :: %__MODULE__{}
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
    updated =
      branch
      |> record(source, :tautology, [])
      |> bump_frontier([source], [])

    {:continue, updated, :no_effects}
  end

  # --- Linear decompositions --------------------------------------------------

  defp apply_rule({:alpha, formulas} = rule, source, branch, params, _g_limit, _p_limit) do
    updated =
      formulas
      |> Enum.reduce(branch, &insert_formula(&2, &1, branch.defs, params))
      |> ingest_formulas(formulas, params)
      |> record(source, rule, formulas)
      |> bump_frontier([source], formulas)

    {:continue, updated, :no_effects}
  end

  defp apply_rule(
         {:equality_expansion, _kind, formulas} = rule,
         source,
         branch,
         params,
         _g_limit,
         _p_limit
       ) do
    # The expansion is inserted against every equation on the branch *except*
    # the one `source` itself contributed. Demodulating `s ≡ t` with `s = t`
    # yields `t ≡ t`, i.e. `⊤` — a perfectly valid rewrite that nonetheless
    # throws away precisely the boolean content this expansion exists to
    # expose. For `¬c = c` it discards a contradiction: the expansion
    # `(¬c) ≡ c` simplifies to `⊥` and closes the branch, but only if it
    # survives long enough to be classified. The equation stays in the branch
    # for everything else, and an equation reaching the branch from some other
    # formula still demodulates this one — that case is not circular.
    without_own = %{branch | equations: drop_equation_of(branch.equations, source, params)}

    updated =
      formulas
      |> Enum.reduce(without_own, &insert_formula(&2, &1, branch.defs, params))
      |> Map.put(:equations, branch.equations)
      |> ingest_formulas(formulas, params)
      |> record(source, rule, formulas)
      |> bump_frontier([source], formulas)

    {:continue, updated, :no_effects}
  end

  defp apply_rule({:delta, sk_term_id} = rule, source, branch, params, _g_limit, _p_limit) do
    updated =
      %{branch | type_universe: register_new_types(branch.type_universe, sk_term_id)}
      |> insert_formula(sk_term_id, branch.defs, params)
      |> ingest_formula(sk_term_id, params)
      |> record(source, rule, [sk_term_id])
      |> bump_frontier([source], [sk_term_id])

    {:continue, updated, :no_effects}
  end

  defp apply_rule(
         {:rename, _},
         source,
         branch,
         %Parameters{atom_decomposition: false} = params,
         g,
         p
       ),
       do: apply_rule({:atomic, source}, source, branch, params, g, p)

  defp apply_rule(
         {:instantiate, _, _},
         source,
         branch,
         %Parameters{atom_decomposition: false} = params,
         g,
         p
       ),
       do: apply_rule({:atomic, source}, source, branch, params, g, p)

  defp apply_rule({:rename, {t1, t2}} = rule, source, branch, params, _g_limit, _p_limit) do
    universe = branch.type_universe |> register_new_types(t1) |> register_new_types(t2)

    updated =
      %{branch | type_universe: universe}
      |> insert_formula(t1, branch.defs, params)
      |> insert_formula(t2, branch.defs, params)
      |> ingest_formulas([t1, t2], params)
      |> record(source, rule, [t1, t2])
      |> bump_frontier([source], [t1, t2])

    {:continue, updated, :no_effects}
  end

  # --- Branching --------------------------------------------------------------

  defp apply_rule({:beta, {b1, b2}} = rule, source, branch, params, _g_limit, _p_limit) do
    recorded = record(branch, source, rule, [b1, b2])

    my_branch =
      %{recorded | id: recorded.id <> "_A"}
      |> insert_formula(b1, recorded.defs, params)
      |> ingest_formula(b1, params)
      |> flush_rewrites()
      |> bump_frontier([source], [b1])

    sib_branch =
      %{recorded | id: recorded.id <> "_B"}
      |> insert_formula(b2, recorded.defs, params)
      |> ingest_formula(b2, params)
      |> flush_rewrites()
      |> bump_frontier([source], [b2])

    if params.beta_variant do
      additional = neg(b1)

      variant_sib_branch =
        sib_branch
        |> insert_formula(additional, recorded.defs, params)
        |> ingest_formula(additional, params)
        |> record(source, :beta_variant, [additional])
        |> bump_frontier([], [additional])

      {:split, my_branch, variant_sib_branch}
    else
      {:split, my_branch, sib_branch}
    end
  end

  # --- Instantiation (dual: original literal is also kept on the branch) -----

  defp apply_rule({:instantiate, branches_stream, count} = rule, source, branch, params, _g, _p) do
    case dual_atomize_source(source, branch, params) do
      {:ground_closure, closed_branch} ->
        updated =
          %{closed_branch | last_clash: {:ground, source, [lit_neg(source)]}}
          |> record(source, rule, [])

        {:closed, updated}

      {:continue, lit_branch} ->
        branches = Enum.to_list(branches_stream)

        if count == 0 do
          {:continue, record(lit_branch, source, rule, []), :no_effects}
        else
          instantiate_children(branches, source, lit_branch, params, rule)
        end
    end
  end

  # --- Gamma (fresh variable instantiation) -----------------------------------

  defp apply_rule(
         {:gamma, recipe, type, prev, ibg?} = rule,
         source,
         branch,
         params,
         gamma_limit,
         _p
       ) do
    if prev >= gamma_limit do
      updated =
        %{
          branch
          | sleeping_gamma_rules: [{source, rule} | branch.sleeping_gamma_rules],
            processed_rules: MapSet.delete(branch.processed_rules, rule)
        }
        |> record(source, rule, [])

      {:continue, updated, :no_effects}
    else
      fresh_var = TF.make_fresh_var_term(type)
      fresh_inst = app(recipe, fresh_var)

      ground_insts =
        if prev == 0 and params.instance_based_gamma do
          branch.ground_terms
          |> Map.get(type, MapSet.new())
          |> cap_ground_terms(params.instance_based_gamma_limit)
          |> Enum.map(&app(recipe, &1))
        else
          []
        end

      all_insts = [fresh_inst | ground_insts]

      branch_with_fresh = insert_formula(branch, fresh_inst, branch.defs, params, ibg?)

      branch_with_insts =
        Enum.reduce(ground_insts, branch_with_fresh, fn inst, b ->
          insert_formula(b, inst, b.defs, params, true)
        end)

      updated_gamma = {:gamma, recipe, type, prev + 1, ibg?}

      queue =
        reinsert_rule(branch_with_insts.queue, source, updated_gamma, params.formula_cost)

      queue =
        if params.primitive_substitution and prev == params.prim_subst_after and
             type.goal == :o do
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
        %{branch_with_insts | queue: queue}
        |> ingest_formulas(all_insts, params)
        |> record(source, rule, all_insts)

      provenance = %Provenance{
        recipe: recipe,
        source: source,
        birth_branch: branch.id,
        gamma_iteration: prev,
        origin: :gamma
      }

      {:continue, updated, {:record_provenance, [{fresh_var, provenance}]}}
    end
  end

  defp apply_rule({:gamma_finite, recipe, type} = rule, source, branch, params, _g, _p) do
    instances = type |> Generation.gen_o() |> Enum.map(&app(recipe, &1))

    updated =
      instances
      |> Enum.reduce(branch, fn inst, b -> insert_formula(b, inst, branch.defs, params) end)
      |> ingest_formulas(instances, params)
      |> record(source, rule, instances)
      |> bump_frontier([source], instances)

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
    args = type.args
    current_constants = branch_constants(branch)
    new_constants = MapSet.difference(current_constants, progress.covered_constants)

    # First pass: emit all unit-set bindings (λy. H(y) = c) for every constant
    # already in the branch, bypassing base/poly heads and the batch cap. This
    # front-loads the bindings most likely to close Leibniz-style goals without
    # waiting for propositional heads to exhaust the batch budget.
    if progress == @fresh_progress and MapSet.size(new_constants) > 0 and
         params.instance_based_gamma do
      {unit_set, unit_set_h_terms} =
        args
        |> GeneralBindings.unit_set_heads(new_constants)
        |> Enum.map(&GeneralBindings.build_binding(args, &1))
        |> Enum.unzip()

      instances = Enum.map(unit_set, &app(recipe, &1))

      branch_with_insts =
        Enum.reduce(instances, branch, fn inst, b ->
          insert_formula(b, inst, branch.defs, params)
        end)

      new_rule =
        {:prim_subst, recipe, type, depth,
         %{@fresh_progress | covered_constants: current_constants}}

      updated =
        %{
          branch_with_insts
          | queue: reinsert_rule(branch_with_insts.queue, source, new_rule, params.formula_cost)
        }
        |> ingest_formulas(instances, params)
        |> record(source, rule, instances)

      records = prim_subst_provenance(unit_set_h_terms, recipe, source, branch.id, depth)

      {:continue, updated, {:record_provenance, records}}
    else
      batch = params.prim_subst_batch_size
      new_types = MapSet.difference(branch.type_universe, progress.covered_types)

      {base, base_h_terms} =
        args
        |> GeneralBindings.base_heads(depth)
        |> Enum.drop(progress.base_offset)
        |> Enum.take(batch)
        |> Enum.map(&GeneralBindings.build_binding(args, &1))
        |> Enum.unzip()

      {unit_set, unit_set_h_terms} =
        if MapSet.size(new_constants) > 0 and params.instance_based_gamma do
          args
          |> GeneralBindings.unit_set_heads(new_constants)
          |> Enum.map(&GeneralBindings.build_binding(args, &1))
          |> Enum.unzip()
        else
          {[], []}
        end

      {poly, poly_h_terms} =
        if MapSet.size(new_types) > 0 do
          args
          |> GeneralBindings.polymorphic_heads(depth, new_types)
          |> Enum.map(&GeneralBindings.build_binding(args, &1))
          |> Enum.unzip()
        else
          {[], []}
        end

      bindings = base ++ unit_set ++ poly

      if bindings == [] do
        advance_or_sleep(recipe, type, depth, branch, params, prim_limit, source, rule)
      else
        instances = Enum.map(bindings, &app(recipe, &1))

        branch_with_insts =
          Enum.reduce(instances, branch, fn inst, b ->
            insert_formula(b, inst, branch.defs, params)
          end)

        new_progress = %{
          base_offset: progress.base_offset + length(base),
          covered_types: MapSet.union(progress.covered_types, new_types),
          covered_constants: MapSet.union(progress.covered_constants, new_constants)
        }

        new_rule = {:prim_subst, recipe, type, depth, new_progress}

        updated =
          %{
            branch_with_insts
            | queue: reinsert_rule(branch_with_insts.queue, source, new_rule, params.formula_cost)
          }
          |> ingest_formulas(instances, params)
          |> record(source, rule, instances)

        records =
          prim_subst_provenance(
            base_h_terms ++ unit_set_h_terms ++ poly_h_terms,
            recipe,
            source,
            branch.id,
            depth
          )

        {:continue, updated, {:record_provenance, records}}
      end
    end
  end

  # --- Atoms ------------------------------------------------------------------

  defp apply_rule({:atomic, raw_term_id} = rule, source, branch, params, _g_limit, _p_limit) do
    # An atom is demodulated *here*, on the way into `literals`, and not only
    # in `insert_formula`. A formula is classified and queued under the
    # equations that existed when it was inserted, but equations keep arriving
    # while it waits — `α` even ingests an equation produced by the very same
    # rule that queued this atom. Normalizing at insert time alone therefore
    # lets an atom enter `literals` in a form no longer normal, and the clash
    # check is syntactic, so the clash is missed and the branch is reported
    # saturated: an unsound `CounterSatisfiable`. `backward_demodulate/3`
    # covers the opposite order (equation after literal); together the two
    # keep `literals` in normal form under all equations known to the branch.
    {term_id, branch} = demodulate_atom(raw_term_id, branch, params)

    case unfold_if_possible(term_id, branch.defs) do
      nil ->
        case check_local_clashes(term_id, branch.literals, params) do
          :ground_closure ->
            updated =
              %{
                branch
                | literals: MapSet.put(branch.literals, term_id),
                  last_clash: {:ground, term_id, [lit_neg(term_id)]}
              }
              |> record(source, rule, [])

            {:closed, updated}

          {:clashes_found, new_clashes} ->
            matchings = matchings_from_clashes(new_clashes, term_id)

            updated =
              %{
                branch
                | literals: MapSet.put(branch.literals, term_id),
                  last_clash: {:unification, term_id, matchings}
              }
              |> record(source, rule, [])

            {:continue, updated, {:notify_ca, new_clashes}}

          :ok ->
            updated =
              %{branch | literals: MapSet.put(branch.literals, term_id)}
              |> record(source, rule, [])

            {:continue, updated, :no_effects}
        end

      unfolded_source ->
        updated =
          branch
          |> insert_formula(unfolded_source, branch.defs, params)
          |> ingest_formula(unfolded_source, params)
          |> record(source, rule, [unfolded_source])
          |> bump_frontier([source], [unfolded_source])

        {:continue, updated, :no_effects}
    end
  end

  # --- Suggested instantiate (spliced by SuggestionAgent) --------------------

  defp apply_rule({:suggested_instantiate, recipe, term} = rule, source, branch, params, _g, _p) do
    formula = app(recipe, term)

    updated =
      branch
      |> insert_formula(formula, branch.defs, params)
      |> ingest_formula(formula, params)
      |> record(source, rule, [formula])
      |> bump_frontier([], [formula])

    {:continue, updated, :no_effects}
  end

  # Flattens a list-of-lists of hole ids (one inner list per general binding)
  # into a flat list of `{h_id, %Provenance{}}` records ready for ETS.
  defp prim_subst_provenance(h_term_lists, recipe, source, branch_id, depth) do
    template = %Provenance{
      recipe: recipe,
      source: source,
      birth_branch: branch_id,
      gamma_iteration: depth,
      origin: :prim_subst
    }

    Enum.flat_map(h_term_lists, fn h_terms ->
      Enum.map(h_terms, fn h -> {h, template} end)
    end)
  end

  ##############################################################################
  # SIMPLIFICATION
  ##############################################################################

  defp simplify_formula(source, cf, branch, %Parameters{simplification: :none}),
    do: {source, cf, branch}

  defp simplify_formula(source, cf, branch, %Parameters{} = params) do
    simplified = PropSimplify.simplify(source, params.simplification)

    if simplified == source do
      {source, cf, branch}
    else
      simplified_cf =
        Rules.classify_formula(
          simplified,
          params.finite_o_quantification,
          params.equivalence_processing
        )

      branch_with_simp =
        branch
        |> then(&%{&1 | term_ids: MapSet.put(&1.term_ids, simplified)})
        |> record(source, :bdd_oracle, [simplified])
        |> bump_frontier([source], [simplified])

      {simplified, simplified_cf, branch_with_simp}
    end
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp instantiate_children(branches, source, branch, params, rule) do
    produced = Enum.map(branches, fn {b_term, _def} -> b_term end)
    recorded = record(branch, source, rule, produced)

    final_branches =
      branches
      |> Stream.with_index()
      |> Enum.reduce([], fn {{b_term, {decl, tid}}, idx}, acc_branches ->
        defs = Map.put(recorded.defs, decl, tid)

        c_branch =
          %{recorded | id: "#{recorded.id}_I#{idx}", defs: defs}
          |> unfold_literals(recorded.literals, defs, params)
          |> unfold_equations(recorded.equations, defs, params)
          |> insert_formula(b_term, defs, params)
          |> ingest_formula(b_term, params)
          |> flush_rewrites()
          |> bump_frontier([], [b_term])

        [c_branch | acc_branches]
      end)

    {:instantiate, final_branches}
  end

  defp dual_atomize_source(raw_term_id, branch, params) do
    {term_id, demodulated} = demodulate_atom(raw_term_id, branch, params)

    case check_local_clashes(term_id, demodulated.literals, params) do
      :ground_closure ->
        {:ground_closure, %{demodulated | literals: MapSet.put(demodulated.literals, term_id)}}

      _ ->
        updated = %{demodulated | literals: MapSet.put(demodulated.literals, term_id)}
        {:continue, updated}
    end
  end

  # Normalizes an atom under the branch's current equations on its way into
  # `literals`, recording the rewrite so proof reconstruction can replay it.
  defp demodulate_atom(term_id, branch, params) do
    case maybe_demodulate(term_id, branch.equations, params) do
      ^term_id ->
        {term_id, branch}

      normal ->
        {normal,
         branch
         |> Map.update!(:term_ids, &MapSet.put(&1, normal))
         |> note_rewrite(term_id, normal)}
    end
  end

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

  @spec branch_constants(%__MODULE__{}) :: MapSet.t(Declaration.const_t())
  defp branch_constants(branch) do
    branch.term_ids
    |> Enum.flat_map(&TF.get_term!(&1).consts)
    |> Enum.reject(fn %Declaration{name: name} -> name in @hol_connective_names end)
    |> Enum.into(MapSet.new())
  end

  ##############################################################################
  # GROUND-TERM INDEXING & GAMMA SATURATION
  ##############################################################################

  # Discover closed subterms of `term_id` that aren't yet in `branch.ground_terms`,
  # and add them to the type-indexed map. The map is consulted at γ-rule firings
  # (when `prev == 0`) to seed instance-based instantiation; ground terms added
  # later are picked up the next time the same γ-rule fires under iterative
  # deepening.
  defp register_ground_subterms(%__MODULE__{} = branch, term_id, _params) do
    new_by_type = collect_new_closed_subterms(term_id, branch.ground_terms)

    if map_size(new_by_type) == 0 do
      branch
    else
      merge_ground_terms(branch, new_by_type)
    end
  end

  defp collect_new_closed_subterms(term_id, existing_index) do
    term_id
    |> Paramodulation.subterms()
    |> Enum.reduce(%{}, fn sub_id, acc ->
      sub = TF.get_term!(sub_id)

      if closed_subterm?(sub) do
        existing = Map.get(existing_index, sub.type, MapSet.new())

        if MapSet.member?(existing, sub_id) do
          acc
        else
          Map.update(acc, sub.type, MapSet.new([sub_id]), &MapSet.put(&1, sub_id))
        end
      else
        acc
      end
    end)
  end

  defp closed_subterm?(%Term{fvars: fvars, bvars: bvars, max_num: max_num}) do
    MapSet.size(fvars) == 0 and max_num <= length(bvars)
  end

  defp merge_ground_terms(branch, new_by_type) do
    updated =
      Enum.reduce(new_by_type, branch.ground_terms, fn {type, terms}, acc ->
        Map.update(acc, type, terms, &MapSet.union(&1, terms))
      end)

    %{branch | ground_terms: updated}
  end

  # Truncates the per-fire IBG fan-out so a γ-rule with many candidate
  # constants does not multiply branch instances combinatorially. `:infinity`
  # preserves the unbounded behavior.
  defp cap_ground_terms(terms, :infinity), do: terms
  defp cap_ground_terms(terms, limit) when is_integer(limit), do: Enum.take(terms, limit)

  # Promotes a freshly-classified γ-rule to its IBG-derived variant so the cost
  # function can deprioritize it below β. Non-γ rules pass through unchanged.
  defp mark_ibg({:gamma, recipe, type, prev, _}, true), do: {:gamma, recipe, type, prev, true}
  defp mark_ibg(rule, _), do: rule

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

  defp insert_formula(branch, formula, defs, params, ibg? \\ false)

  defp insert_formula(%__MODULE__{} = branch, formula, defs, %Parameters{} = params, ibg?) do
    effective =
      formula
      |> maybe_unfold(defs, params)
      |> maybe_orient(params)
      |> maybe_demodulate(branch.equations, params)

    cf =
      effective
      |> Rules.classify_formula(
        params.finite_o_quantification,
        params.equivalence_processing
      )
      |> mark_ibg(ibg?)

    pending =
      case branch.pending_closure do
        nil ->
          neg = lit_neg(effective)
          if MapSet.member?(branch.term_ids, neg), do: {effective, neg}, else: nil

        existing ->
          existing
      end

    base = %{
      branch
      | queue: FPQ.insert(branch.queue, {effective, cf}, params.formula_cost.(cf)),
        term_ids: MapSet.put(branch.term_ids, effective),
        pending_closure: pending
    }

    # `effective` — not `formula` — is what the branch queues, classifies and
    # eventually closes on. Leaving the rewrite untraced strands the closing
    # literal outside the proof: it cites a term no recorded step ever produced,
    # so `⊥` comes out with no justification at all.
    base
    |> note_rewrite(formula, effective)
    |> register_ground_subterms(effective, params)
  end

  defp reinsert_rule(queue, source, rule, cost_fn) do
    FPQ.insert(queue, {source, rule}, cost_fn.(rule))
  end

  defp maybe_unfold(term_id, defs, %Parameters{unfold_defs: :eager}) do
    Semantics.unfold_defs!(term_id, defs)
  end

  defp maybe_unfold(term_id, _defs, _params), do: term_id

  # Forward demodulation. Reduces `term_id` to its normal form under the
  # branch's current equations before it enters the priority queue.
  # Cheap when equations is empty (early-branch or `paramodulation: false`)
  # — `Demodulation.normalize/3` short-circuits to identity.
  defp maybe_demodulate(term_id, _equations, %Parameters{demodulation: false}), do: term_id

  defp maybe_demodulate(term_id, equations, %Parameters{term_order: order}) do
    Demodulation.normalize(term_id, equations, order)
  end

  ##############################################################################
  # EQUATION INGESTION & PARAMODULATION
  ##############################################################################

  defp ingest_formulas(branch, formulas, params) do
    Enum.reduce(formulas, branch, &ingest_formula(&2, &1, params))
  end

  defp ingest_formula(branch, term_id, params) do
    effective_id = term_id |> maybe_unfold(branch.defs, params) |> maybe_orient(params)

    case TF.get_term!(effective_id) do
      equality(lhs, rhs) when lhs != rhs ->
        branch
        |> ingest_equation(lhs, rhs, term_id, params)
        |> ingest_asserted_equality(lhs, rhs, term_id, params)

      _ ->
        branch
    end
  end

  # `(s = t) = ⊤` asserts the equality *atom* `s = t`, which licenses `s → t`
  # as a rewrite. Registering only the outer pair records the weaker fact "this
  # boolean atom is true" and loses the term-level equation, so literals
  # mentioning `s` and `t` are never normalized against each other. A branch
  # holding `((h ⊤) = (h ⊥)) = ⊤` together with `P (h ⊤)` and `¬(P (h ⊥))` then
  # looks clash-free and gets reported as a countermodel.
  #
  # The shape arises whenever `:rename` abbreviates an equality as a constant
  # and a later `:instantiate` fixes that constant to `⊤`.
  defp ingest_asserted_equality(branch, lhs, rhs, origin, params) do
    case {TF.get_term!(lhs), TF.get_term!(rhs)} do
      {equality(l, r), truth()} when l != r -> ingest_equation(branch, l, r, origin, params)
      {truth(), equality(l, r)} when l != r -> ingest_equation(branch, l, r, origin, params)
      _ -> branch
    end
  end

  # Removes the oriented equation `source` would contribute, leaving the rest of
  # the branch's equation set intact. See `apply_rule/6` for the
  # `:equality_expansion` rule, its only caller.
  defp drop_equation_of(equations, source, params) do
    case TF.get_term!(source) do
      equality(lhs, rhs) when lhs != rhs ->
        {ol, or_} = orient_pair(lhs, rhs, params.term_order)

        case Map.get(equations, ol) do
          nil -> equations
          rhs_set -> prune_equation(equations, ol, MapSet.delete(rhs_set, or_))
        end

      _ ->
        equations
    end
  end

  defp prune_equation(equations, lhs, remaining) do
    case MapSet.size(remaining) do
      0 -> Map.delete(equations, lhs)
      _ -> Map.put(equations, lhs, remaining)
    end
  end

  # `origin` is the branch formula the equation was read off. The oriented pair
  # is often no formula the branch ever held — `orient_pair/3` may flip it, and
  # `ingest_asserted_equality/5` digs it out of an enclosing `(s = t) = ⊤` — so
  # only the origin gives `unfold_equations/4` a step it can cite.
  defp ingest_equation(branch, lhs, rhs, origin, params) do
    {ol, or_} = orient_pair(lhs, rhs, params.term_order)
    new_equations = Map.update(branch.equations, ol, MapSet.new([or_]), &MapSet.put(&1, or_))

    %{
      branch
      | equations: new_equations,
        equation_origins: Map.put_new(branch.equation_origins, {ol, or_}, origin)
    }
    |> backward_demodulate(params)
  end

  # Backward demodulation: when a new equation lands, sweep existing
  # branch literals and re-normalize them under the enlarged equation
  # set. A literal that reduces is *replaced* — the old form is removed
  # from `branch.literals` and the new form re-enters via
  # `insert_formula` (which will run its own forward-demodulation pass
  # and pick up the classification / queue entry).
  #
  # Normalization uses the branch's *whole* equation set, not just the
  # equation that triggered this pass. Rewriting under the new equation can
  # expose a redex for an older one, and an earlier version of this function
  # passed only the new equation on the assumption that every literal was
  # already normal under the older set — an invariant the branch does not
  # actually maintain, since literals also enter via `apply_rule({:atomic,
  # ...})`. Using the full set makes the normal form independent of the order
  # equations arrived in.
  defp backward_demodulate(branch, %Parameters{demodulation: false}), do: branch

  defp backward_demodulate(branch, params) do
    Enum.reduce(branch.literals, branch, fn lit, acc ->
      normal = Demodulation.normalize(lit, acc.equations, params.term_order)

      cond do
        normal == lit ->
          acc

        MapSet.member?(acc.literals, normal) ->
          # Already present in canonical form; just drop the redundant
          # non-normal duplicate.
          %{acc | literals: MapSet.delete(acc.literals, lit)}

        true ->
          # Replace: drop the un-normalized literal, re-enqueue the
          # normal form through the standard insertion path so it gets
          # classified and paramodulated correctly.
          acc
          |> Map.update!(:literals, &(&1 |> MapSet.delete(lit) |> MapSet.put(normal)))
          |> note_rewrite(lit, normal)
          |> insert_formula(normal, acc.defs, params)
      end
    end)
  end

  # Pick a storage direction for `lhs = rhs`. When NCPO-LNF strictly orients
  # the pair, that direction is used and downstream demodulation will fire
  # (see `Demodulation.normalize/3`). When the pair is incomparable under
  # NCPO-LNF, we still store *some* direction so equational reasoning is
  # not lost — the demodulation gate silently drops it from rewriting, and
  # the Leibniz/extensional α-expansion becomes the completeness fallback.
  # The final `gt?` branch uses the total heuristic extension solely to
  # make the storage direction deterministic.
  defp orient_pair(lhs, rhs, order_params) do
    cond do
      TermOrder.strict_gt?(lhs, rhs, order_params) -> {lhs, rhs}
      TermOrder.strict_gt?(rhs, lhs, order_params) -> {rhs, lhs}
      TermOrder.gt?(lhs, rhs, order_params) -> {lhs, rhs}
      true -> {rhs, lhs}
    end
  end

  defp maybe_orient(term_id, %Parameters{orient: :none}), do: term_id

  defp maybe_orient(term_id, %Parameters{orient: :shallow, term_order: order}),
    do: orient_top(term_id, order)

  defp maybe_orient(term_id, %Parameters{orient: :deep, term_order: order}),
    do: orient_recursive(term_id, order)

  defp orient_top(term_id, order) do
    case TF.get_term!(term_id) do
      disjunction(p, q) -> if TermOrder.gt?(q, p, order), do: q ||| p, else: term_id
      conjunction(p, q) -> if TermOrder.gt?(q, p, order), do: q &&& p, else: term_id
      equivalence(p, q) -> if TermOrder.gt?(q, p, order), do: q <~> p, else: term_id
      equality(p, q) -> if TermOrder.gt?(q, p, order), do: eq(q, p), else: term_id
      _ -> term_id
    end
  end

  # Bottom-up: orient args first, rebuild if any changed, then orient the top level.
  defp orient_recursive(term_id, order) do
    %Term{head: head, args: args, bvars: bvars} = TF.get_term!(term_id)
    oriented_args = Enum.map(args, &orient_recursive(&1, order))

    rebuilt =
      if oriented_args == args do
        term_id
      else
        head_id = TF.make_term(head)
        body_id = TF.fold_apply!(head_id, oriented_args)
        List.foldr(bvars, body_id, &TF.make_abstr_term!(&2, &1))
      end

    orient_top(rebuilt, order)
  end

  # Commits a rule firing, then the rewrites the rule's own insertions
  # performed. History is newest-first, so the buffered rewrites sit *above*
  # the rule entry and replay right after it.
  defp record(branch, source, rule, produced) do
    %{
      branch
      | history: branch.pending_rewrites ++ [{source, rule, produced} | branch.history],
        pending_rewrites: []
    }
  end

  # Buffers a rewrite performed on a formula's way into the branch. The entry
  # cannot go straight into `history`: normalization happens while the rule
  # that produced the formula is still assembling its own record, and `record/4`
  # prepends, so a direct write would place the rewrite *before* the step it
  # rewrites — proof reconstruction would then label the normal form ahead of
  # its source and resolve neither.
  defp note_rewrite(branch, formula, formula), do: branch

  defp note_rewrite(%__MODULE__{} = branch, formula, effective) do
    %{
      branch
      | pending_rewrites: [{formula, :demodulation, [effective]} | branch.pending_rewrites]
    }
  end

  # Commits buffered rewrites without a rule entry to hang them on. Needed by
  # `new/4` (which never records) and by the rules that record *before* they
  # insert (β, `:instantiate`), where `record/4` has already run.
  defp flush_rewrites(%__MODULE__{pending_rewrites: []} = branch), do: branch

  defp flush_rewrites(%__MODULE__{} = branch) do
    %{branch | history: branch.pending_rewrites ++ branch.history, pending_rewrites: []}
  end

  # Frontier is the coarse "what does this branch commit to for a model finder"
  # view. Updated whenever a rule consumes its source (α/β/δ/…) or replaces it
  # with a semantically stronger form (atomic-unfold). γ/prim_subst leave the
  # frontier untouched because their sources remain the true constraint —
  # fresh instances are hints, not new commitments. Paramodulants and γ-fresh
  # atoms flow through `insert_formula` and land in `literals` without ever
  # entering the frontier, which is exactly what we want for a Nitpick probe.
  defp bump_frontier(%__MODULE__{} = branch, remove, add) do
    new_frontier =
      branch.frontier
      |> MapSet.difference(MapSet.new(remove))
      |> MapSet.union(MapSet.new(add))

    if new_frontier == branch.frontier do
      branch
    else
      %{branch | frontier: new_frontier, frontier_version: branch.frontier_version + 1}
    end
  end

  defp unfold_if_possible(term_id, defs) do
    unfolded = Semantics.unfold_defs!(term_id, defs)
    if unfolded == term_id, do: nil, else: unfolded
  end

  defp unfold_literals(branch, literals, defs, %Parameters{} = params) do
    Enum.reduce(literals, branch, fn tid, b ->
      case unfold_if_possible(tid, defs) do
        nil ->
          b

        unfolded ->
          b
          |> insert_formula(unfolded, defs, params)
          |> record(tid, {:atomic, tid}, [unfolded])
      end
    end)
  end

  # An `:instantiate` child fixes a new definition for a constant, and
  # `unfold_literals/4` re-expands the branch's literals under it. Its
  # *equations* need the same treatment. Without it a child can hold a
  # definition set that its own equations refute and still call itself
  # saturated — the `:rename` rule abbreviates `a ∧ b` as a fresh constant `C`
  # and records `a ∧ b = C`, so a child choosing `a := ⊤, b := ⊤, C := ⊥` is
  # inconsistent, yet every literal in it stays clash-free and the branch is
  # reported as a countermodel.
  #
  # Re-inserting the unfolded equality routes it back through classification,
  # where `(⊤ ∧ ⊤) = ⊥` expands to `(⊤ ∧ ⊤) ≡ ⊥` and closes the branch.
  defp unfold_equations(branch, equations, defs, %Parameters{} = params) do
    for {lhs, rhs_set} <- equations, rhs <- rhs_set, reduce: branch do
      acc ->
        equation = equation_origin(acc, lhs, rhs)

        case unfold_if_possible(equation, defs) do
          nil ->
            acc

          unfolded ->
            acc
            |> insert_formula(unfolded, defs, params)
            |> ingest_formula(unfolded, params)
            |> record(equation, {:atomic, equation}, [unfolded])
        end
    end
  end

  # Falls back to rebuilding the equation for pairs seeded through `new/4`'s
  # `:equations` option, which carry no origin.
  defp equation_origin(%__MODULE__{equation_origins: origins}, lhs, rhs) do
    Map.get_lazy(origins, {lhs, rhs}, fn -> eq(lhs, rhs) end)
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

  defp matchings_from_clashes(clashes, term_id) do
    neg_new = lit_neg(term_id)

    clashes
    |> Enum.flat_map(fn {a, b} ->
      cond do
        a == term_id -> [lit_neg(b)]
        b == term_id -> [lit_neg(a)]
        a == neg_new -> [b]
        b == neg_new -> [a]
        true -> []
      end
    end)
    |> Enum.uniq()
  end
end
