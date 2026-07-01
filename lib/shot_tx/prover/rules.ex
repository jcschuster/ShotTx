defmodule ShotTx.Prover.Rules do
  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TermTraversal
  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl
  import ShotTx.Generation
  use ShotDs.Hol.Patterns

  @typep definition_t :: {Declaration.t(), Term.term_id()}

  @typedoc "A tautology disregards the formula as it doesn't add information."
  @type tautology_t :: :tautology

  @typedoc "A contradiction trivially closes the tableau branch."
  @type contradiction_t :: :contradiction

  @typedoc "An alpha-rule decomposes the formula linearly into a list of formulas."
  @type alpha_t :: {:alpha, nonempty_list(Term.term_id())}

  @typedoc "A beta-rule decomposes the formula into two tuples corresponding to branches."
  @type beta_t :: {:beta, {Term.term_id(), Term.term_id()}}

  @typedoc """
  A gamma rule instantiates a universally quantified predicate with a fresh
  variable. As this rule is not consumed due to completeness, the second element
  of the tuple corresponds to the recipe for instantiations, i.e., a formula
  accepting a fresh variable. The third field captures the type of the variable.
  The last field keeps track of the rule instantiations for that formula so far.
  """
  @type gamma_t :: {:gamma, Term.term_id(), Type.t(), non_neg_integer(), boolean()}

  @typedoc "Rule for consuming a gamma-formula when the domain is finite."
  @type gamma_finite_t :: {:gamma_finite, Term.term_id(), Type.t()}

  @typedoc """
  A delta rule instantiates an existentially quantified predicate with a
  skolem term dependent on the predicates free variables.
  """
  @type delta_t :: {:delta, Term.term_id()}

  @typep prim_subst_progress ::
           %{base_offset: non_neg_integer(), covered_types: MapSet.t(Type.t())}

  @typedoc """
  Primitive substitution rule. Instantiates a universally quantified formula
  with general bindings that fix a logical head symbol while leaving
  sub-formula positions as fresh holes. Fields: recipe, element type, current
  binding depth, and a progress map recording consumed base bindings and
  covered types at the current depth.
  """
  @type prim_subst_t ::
          {:prim_subst, Term.term_id(), Type.t(), pos_integer(), prim_subst_progress()}

  @typedoc """
  For introducing extensionality, complex argument terms are renamed with a
  fresh constant. The tuple in the second field captures the term with the
  renamed constant as its first argument and an equality serving as the context
  as its second argument.
  """
  @type rename_t :: {:rename, {Term.term_id(), Term.term_id()}}

  @typedoc """
  This produces a lazy stream of `{instantiated_term, corresponding_def}` if the
  _(rename)_-rule is not applicable and one of the arguments is an _o-type_ that
  can be instantiated. Additionally captures the number of instances.
  """
  @type instantiate_t ::
          {:instantiate, Enumerable.t({Term.term_id(), definition_t()}), pos_integer()}

  @typedoc """
  Formulas not matching any of the rules above are considered _atomic_ and can
  for example be processed with unification.
  """
  @type atomic_t :: {:atomic, Term.term_id()}

  @typedoc """
  Discriminates the three flavors of equality expansion.

    * `:iff_o`       — equality at type `o` is just `↔`.
    * `:extensional` — equality at a functional type expands via
      extensional equality (or, for closed sides, a fresh-constant
      application form).
    * `:leibniz`     — equality at any remaining type expands via the
      Leibniz schema `∀P. P(a) ↔ P(b)`. The expensive one for FO.
  """
  @type equality_kind :: :iff_o | :extensional | :leibniz

  @typedoc """
  Equality expansion rule. Mechanically identical to an α-rule (a linear
  decomposition into a list of produced formulas), but tagged with its
  `equality_kind` so the cost function can charge each kind separately and
  proof-search can de-prioritize Leibniz behind paramodulation.
  """
  @type equality_expansion_t ::
          {:equality_expansion, equality_kind(), nonempty_list(Term.term_id())}

  @type rule_t() ::
          alpha_t()
          | beta_t()
          | gamma_t()
          | gamma_finite_t()
          | delta_t()
          | prim_subst_t()
          | tautology_t()
          | contradiction_t()
          | rename_t()
          | instantiate_t()
          | atomic_t()
          | equality_expansion_t()

  @typedoc """
  Partial override map for `rule_cost/2`. Any kind absent from the map keeps
  its default. Keys not recognised by the rule case are ignored.
  """
  @type cost_overrides :: %{optional(equality_kind()) => non_neg_integer()}

  @doc """
  Returns the priority cost for a rule; lower cost means higher priority in
  the queue. Equivalent to `rule_cost(rule, %{})`.
  """
  @spec rule_cost(rule_t()) :: non_neg_integer()
  def rule_cost(rule), do: rule_cost(rule, %{})

  @doc """
  Returns the priority cost for a rule, allowing per-kind overrides for
  equality expansion. The `overrides` map only needs to mention the kinds
  whose default should change; unlisted kinds keep their defaults.

  Typical use is to pin a heavy cost on Leibniz expansion while letting the
  o-type and extensional forms stay cheap:

      formula_cost: &ShotTx.Prover.Rules.rule_cost(&1, %{leibniz: 100})
  """
  @spec rule_cost(rule_t(), cost_overrides()) :: non_neg_integer()
  def rule_cost(rule, overrides) do
    case rule do
      :contradiction -> 0
      :tautology -> 1
      {:alpha, _} -> 2
      {:beta, _} -> 4
      {:gamma, _, _, c, false} -> 3 + 2 * c
      {:gamma, _, _, c, true} -> 5 + 2 * c
      {:gamma_finite, _, _} -> 3
      {:delta, _} -> 2
      {:prim_subst, _, _, d, %{base_offset: c}} -> 20 + 5 * d + 2 * c
      {:rename, _} -> 3
      {:instantiate, _, c} -> 2 + c
      {:atomic, _} -> 1
      {:equality_expansion, kind, _} -> Map.get(overrides, kind, default_equality_cost(kind))
    end
  end

  @spec default_equality_cost(equality_kind()) :: non_neg_integer()
  defp default_equality_cost(:iff_o), do: 2
  defp default_equality_cost(:extensional), do: 10
  defp default_equality_cost(:leibniz), do: 15

  ##############################################################################
  # CLASSIFICATION
  ##############################################################################

  @typedoc """
  Selects how equivalence (`↔`) is expanded.

    * `:same_polarity`     — current default. Positive `p ↔ q` β-splits into
      `{p ∧ q, ¬p ∧ ¬q}`; negative `¬(p ↔ q)` β-splits into `{¬p ∧ q, ¬q ∧ p}`.
    * `:bidirectional_imp` — rewrites `p ↔ q` as `(p → q) ∧ (q → p)`. Positive
      becomes an α producing both implications; negative becomes a β over the
      two negated implications.
    * `:dual`              — emits both forms in a single α, so the prover can
      exploit either expansion. Positive: `[p → q, q → p, (p ∧ q) ∨ (¬p ∧ ¬q)]`;
      negative: `[¬(p → q) ∨ ¬(q → p), (¬p ∧ q) ∨ (¬q ∧ p)]`.
  """
  @type equivalence_mode :: :same_polarity | :bidirectional_imp | :dual

  @doc """
  Classifies a term ID as the tableau rule that should be applied to it.

  The second argument controls how quantifiers over pure `o`-types are
  handled. When `true` (default) they are routed to the finite γ-rule which
  enumerates the propositional domain; when `false` they fall through to the
  ordinary γ-rule, the same path used for non-`o` quantifiers.

  The third argument selects an equivalence expansion strategy; see
  `t:equivalence_mode/0`.
  """
  @spec classify_formula(Term.term_id(), boolean(), equivalence_mode()) :: rule_t()
  def classify_formula(
        term_id,
        finite_o_quantification \\ true,
        equivalence_mode \\ :same_polarity
      )
      when is_integer(term_id) do
    case TF.get_term!(term_id) do
      negated(inner) ->
        classify_neg_formula(inner, finite_o_quantification, equivalence_mode)

      falsity() ->
        :contradiction

      truth() ->
        :tautology

      equality(a, a) ->
        :tautology

      conjunction(p, q) ->
        {:alpha, [p, q]}

      typed_equality(a, b, %Type{goal: :o, args: []}) ->
        {:equality_expansion, :iff_o, [a <~> b]}

      typed_equality(a, b, %Type{args: [_ | _]} = t) ->
        {:equality_expansion, :extensional, [app(extensional_equality(t), [a, b])]}

      typed_equality(a, b, t) ->
        {:equality_expansion, :leibniz, [app(leibniz_equality(t), [a, b])]}

      disjunction(p, q) ->
        {:beta, {p, q}}

      implication(p, q) ->
        {:beta, {neg(p), q}}

      equivalence(p, q) ->
        expand_pos_equivalence(p, q, equivalence_mode)

      typed_universal_quantification(pred, t) ->
        if finite_o_quantification and pure_o_type?(t) do
          {:gamma_finite, lambda(t, fn x -> app(pred, x) end), t}
        else
          {:gamma, lambda(t, fn x -> app(pred, x) end), t, 0, false}
        end

      typed_existential_quantification(pred, t) ->
        fvars = TF.get_term!(pred).fvars
        {:delta, app(pred, sk_term(fvars, t))}

      atomic ->
        classify_atom(atomic)
    end
  end

  @spec expand_pos_equivalence(Term.term_id(), Term.term_id(), equivalence_mode()) :: rule_t()
  defp expand_pos_equivalence(p, q, :same_polarity), do: {:beta, {p &&& q, neg(q) &&& neg(p)}}
  defp expand_pos_equivalence(p, q, :bidirectional_imp), do: {:alpha, [p ~> q, q ~> p]}

  defp expand_pos_equivalence(p, q, :dual),
    do: {:alpha, [p ~> q, q ~> p, (p &&& q) ||| (neg(p) &&& neg(q))]}

  @spec expand_neg_equivalence(Term.term_id(), Term.term_id(), equivalence_mode()) :: rule_t()
  defp expand_neg_equivalence(p, q, :same_polarity), do: {:beta, {neg(p) &&& q, neg(q) &&& p}}
  defp expand_neg_equivalence(p, q, :bidirectional_imp), do: {:beta, {neg(p ~> q), neg(q ~> p)}}

  defp expand_neg_equivalence(p, q, :dual),
    do: {:alpha, [neg(p ~> q) ||| neg(q ~> p), (neg(p) &&& q) ||| (neg(q) &&& p)]}

  ##############################################################################
  # NEGATED CLASSIFICATION
  ##############################################################################

  @spec classify_neg_formula(Term.term_id(), boolean(), equivalence_mode()) :: rule_t()
  defp classify_neg_formula(term_id, finite_o_quantification, equivalence_mode) do
    case TF.get_term!(term_id) do
      negated(inner) ->
        {:alpha, [inner]}

      falsity() ->
        :tautology

      truth() ->
        :contradiction

      equality(a, a) ->
        :contradiction

      conjunction(p, q) ->
        {:beta, {neg(p), neg(q)}}

      typed_equality(a, b, %Type{goal: :o, args: []}) ->
        {:equality_expansion, :iff_o, [neg(a <~> b)]}

      typed_equality(a, b, %Type{args: [_ | _]} = t) ->
        if closed_term?(a) and closed_term?(b) do
          [h | _] = t.args
          c = sk_term(MapSet.new(), h)
          {:equality_expansion, :extensional, [neg(eq(app(a, c), app(b, c)))]}
        else
          {:equality_expansion, :extensional, [neg(app(extensional_equality(t), [a, b]))]}
        end

      typed_equality(a, b, t) ->
        {:equality_expansion, :leibniz, [neg(app(leibniz_equality(t), [a, b]))]}

      disjunction(p, q) ->
        {:alpha, [neg(p), neg(q)]}

      implication(p, q) ->
        {:alpha, [p, neg(q)]}

      equivalence(p, q) ->
        expand_neg_equivalence(p, q, equivalence_mode)

      typed_universal_quantification(pred, t) ->
        fvars = TF.get_term!(pred).fvars
        {:delta, neg(app(pred, sk_term(fvars, t)))}

      typed_existential_quantification(pred, t) ->
        if finite_o_quantification and pure_o_type?(t) do
          {:gamma_finite, lambda(t, fn x -> neg(app(pred, x)) end), t}
        else
          {:gamma, lambda(t, fn x -> neg(app(pred, x)) end), t, 0, false}
        end

      atomic ->
        case classify_atom(atomic) do
          {:instantiate, branches, c} ->
            {:instantiate, Stream.map(branches, fn {term, def} -> {neg(term), def} end), c}

          {:rename, {renamed, eq_def}} ->
            {:rename, {neg(renamed), eq_def}}

          {:atomic, ^term_id} ->
            {:atomic, neg(term_id)}
        end
    end
  end

  ##############################################################################
  # ATOM CLASSIFICATION
  ##############################################################################

  @spec classify_atom(Term.t()) :: rename_t() | instantiate_t() | atomic_t()
  defp classify_atom(term)

  defp classify_atom(%Term{head: %Declaration{kind: :co}, args: [_ | _] = args} = term) do
    case find_deep_candidates(args) do
      nil ->
        non_val_o_args =
          args
          |> Enum.with_index()
          |> Enum.filter(fn {a_id, _idx} -> non_signature_o_constant?(a_id) end)

        if Enum.empty?(non_val_o_args) do
          {:atomic, TF.memoize(term)}
        else
          [{to_instantiate, idx} | _] = non_val_o_args
          %Term{head: decl, type: type} = TF.get_term!(to_instantiate)

          branches =
            Stream.map(gen_o(type), fn instance ->
              new_args = List.replace_at(args, idx, instance)
              inst_term = TF.with_scratchpad!(fn -> rebuild_term(term, new_args) end)
              {inst_term, {decl, instance}}
            end)

          {:instantiate, branches, o_type_size(type)}
        end

      {:rename, candidate_id} ->
        candidate_term = TF.get_term!(candidate_id)
        c_id = sk_term(candidate_term.fvars, candidate_term.type)

        transform = fn current_term, new_args, _env, acc_cache ->
          if current_term.id == candidate_id do
            {c_id, acc_cache}
          else
            {rebuild_term(current_term, new_args), acc_cache}
          end
        end

        replaced_term_id =
          TF.with_scratchpad!(fn ->
            {id, _cache} = TermTraversal.map_term!(term.id, nil, fn _, env -> env end, transform)
            id
          end)

        {:rename, {replaced_term_id, eq(c_id, candidate_id)}}

      {:instantiate, candidate_id} ->
        %Term{head: decl, type: type} = TF.get_term!(candidate_id)

        branches =
          Stream.map(gen_o(type), fn instance ->
            transform = fn current_term, new_args, _env, acc_cache ->
              if current_term.id == candidate_id do
                {instance, acc_cache}
              else
                {rebuild_term(current_term, new_args), acc_cache}
              end
            end

            inst_term_id =
              TF.with_scratchpad!(fn ->
                {id, _cache} = TermTraversal.map_term!(term.id, nil, fn _, env -> env end, transform)
                id
              end)

            {inst_term_id, {decl, instance}}
          end)

        {:instantiate, branches, o_type_size(type)}
    end
  end

  defp classify_atom(term), do: {:atomic, TF.memoize(term)}

  defp find_deep_candidates(args) do
    fold_fn = fn term, arg_results ->
      existing = Enum.find(arg_results, & &1)

      cond do
        existing ->
          existing

        non_signature_o_constant?(term.id) ->
          case TF.primitive_term?(term.id) do
            {:ok, false} ->
              if is_reference(term.head.name) do
                nil
              else
                {:rename, term.id}
              end

            {:ok, true} ->
              if is_reference(term.head.name) do
                {:instantiate, term.id}
              else
                nil
              end

            _ ->
              nil
          end

        true ->
          nil
      end
    end

    Enum.find_value(args, fn arg_id ->
      {result, _cache} = TermTraversal.fold_term!(arg_id, fold_fn)
      result
    end)
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  @spec closed_term?(Term.term_id()) :: boolean()
  defp closed_term?(term_id), do: MapSet.size(TF.get_term!(term_id).fvars) == 0

  @spec pure_o_type?(Type.t()) :: boolean()
  defp pure_o_type?(%Type{goal: :o, args: args}), do: Enum.all?(args, &pure_o_type?/1)
  defp pure_o_type?(_), do: false

  defp non_signature_o_constant?(term_id) do
    term = TF.get_term!(term_id)

    pure_o_type?(term.type) &&
      term.head.kind == :co &&
      not Enum.member?(gen_o(term.type), term_id)
  end

  @spec sk_term(MapSet.t(Declaration.free_var_t()), Type.t()) :: Term.term_id()
  defp sk_term(fvars, return_type) do
    skolem =
      Type.new(return_type, Enum.map(fvars, & &1.type))
      |> TF.make_fresh_const_term()

    app(skolem, Enum.map(fvars, &TF.make_term/1))
  end

  defp o_type_size(type), do: 2 ** o_occurrences(type)

  defp o_occurrences(%Type{goal: :o, args: args}),
    do: 1 + Enum.sum_by(args, &o_occurrences/1)

  # Rebuild a term from its head and new args, recomputing all metadata fields.
  # Avoids the stale consts/fvars/max_num/tvars left by %{term | args: new_args}.
  defp rebuild_term(%Term{head: head, bvars: bvars}, new_args) do
    head_id = TF.make_term(head)
    body_id = TF.fold_apply!(head_id, new_args)
    List.foldr(bvars, body_id, &TF.make_abstr_term!(&2, &1))
  end
end
