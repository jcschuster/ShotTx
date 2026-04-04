defmodule ShotTx.Prover.Rules do
  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl
  import ShotTx.Generation
  use ShotDs.Hol.Patterns

  @typep definition_t :: {Declaration.t(), Term.term_id()}

  @typedoc """
  A tautology disregards the formula as it doesn't add information.
  """
  @type tautology_t :: :tautology

  @typedoc """
  A contradiction trivially closes the tableau branch.
  """
  @type contradiction_t :: :contradiction

  @typedoc """
  An alpha-rule decomposes the formula linrarly into a list of formulas.
  """
  @type alpha_t :: {:alpha, nonempty_list(Term.term_id())}

  @typedoc """
  A beta-rule decomposes the formula into two tuples corresponding to branches.
  """
  @type beta_t :: {:beta, {Term.term_id(), Term.term_id()}}

  @typedoc """
  A gamma rule instantiates a universally quantified predicate with a fresh
  variable. As this rule is not consumed due to completeness, the second element
  of the tuple corresponds to the recipe for instantiations, i.e., a formula
  accepting a fresh variable. The third field captures the type of the variable.
  The last field keeps track of the rule instantiations for that formula so far.
  """
  @type gamma_t :: {:gamma, Term.term_id(), Type.t(), non_neg_integer()}

  @typedoc """
  Rule for consuming a gamma-formula when the domain is finite.
  """
  @type gamma_finite_t :: {:gamma_finite, Term.term_id(), Type.t()}

  @typedoc """
  A delta rule instantiates an existentially quantified predicate with a
  skolem term dependent on the predicates free variables.
  """
  @type delta_t :: {:delta, Term.term_id()}

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
  can be instantiated. Additionally captures the number or instances.
  """
  @type instantiate_t ::
          {:instantiate, Enumerable.t({Term.term_id(), definition_t()}), pos_integer()}

  @typedoc """
  Formulas not matching any of the rules above are considered _atomic_ and can
  for example processed with unification.
  """
  @type atomic_t :: {:atomic, Term.term_id()}

  @type rule_t() ::
          alpha_t()
          | beta_t()
          | gamma_t()
          | gamma_finite_t()
          | delta_t()
          | tautology_t()
          | contradiction_t()
          | rename_t()
          | instantiate_t()
          | atomic_t()

  @spec rule_cost(rule_t()) :: non_neg_integer()
  def rule_cost(rule) do
    case rule do
      :contradiction -> 0
      :tautology -> 1
      {:alpha, _} -> 2
      {:beta, _} -> 4
      {:gamma, _, _, c} -> 5 + 2 * c
      {:gamma_finite, _, _} -> 3
      {:delta, _} -> 2
      {:rename, _} -> 3
      {:instantiate, _, c} -> 2 + c
      {:atomic, _} -> 1
    end
  end

  @spec classify_formula(Term.term_id()) :: rule_t()
  def classify_formula(term_id) when is_integer(term_id) do
    case TF.get_term!(term_id) do
      negated(inner) ->
        classify_neg_formula(inner)

      falsity() ->
        :contradiction

      truth() ->
        :tautology

      equality(a, a) ->
        :tautology

      conjunction(p, q) ->
        {:alpha, [p, q]}

      typed_equality(a, b, %Type{goal: :o, args: []}) ->
        {:alpha, [a <~> b]}

      typed_equality(a, b, %Type{args: [_ | _]} = t) ->
        {:alpha, [app(extensional_equality(t), [a, b])]}

      typed_equality(a, b, t) ->
        {:alpha, [app(leibniz_equality(t), [a, b])]}

      disjunction(p, q) ->
        {:beta, {p, q}}

      implication(p, q) ->
        {:beta, {neg(p), q}}

      equivalence(p, q) ->
        {:beta, {p &&& q, neg(p) &&& neg(q)}}

      typed_universal_quantification(pred, t) ->
        if pure_o_type?(t) do
          {:gamma_finite, lambda(t, fn x -> app(pred, x) end), t}
        else
          {:gamma, lambda(t, fn x -> app(pred, x) end), t, 0}
        end

      typed_existential_quantification(pred, t) ->
        fvars = TF.get_term!(pred).fvars
        {:delta, app(pred, sk_term(fvars, t))}

      atomic ->
        classify_atom(atomic)
    end
  end

  @spec classify_neg_formula(Term.term_id()) :: rule_t()
  defp classify_neg_formula(term_id) do
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
        {:alpha, [neg(a <~> b)]}

      typed_equality(a, b, %Type{args: [_ | _]} = t) ->
        {:alpha, [neg(app(extensional_equality(t), [a, b]))]}

      typed_equality(a, b, t) ->
        {:alpha, [neg(app(leibniz_equality(t), [a, b]))]}

      disjunction(p, q) ->
        {:alpha, [neg(p), neg(q)]}

      implication(p, q) ->
        {:alpha, [p, neg(q)]}

      equivalence(p, q) ->
        {:beta, {neg(p) &&& q, p &&& neg(q)}}

      typed_universal_quantification(pred, t) ->
        fvars = TF.get_term!(pred).fvars
        {:delta, neg(app(pred, sk_term(fvars, t)))}

      typed_existential_quantification(pred, t) ->
        if pure_o_type?(t) do
          {:gamma_finite, lambda(t, fn x -> neg(app(pred, x)) end), t}
        else
          {:gamma, lambda(t, fn x -> neg(app(pred, x)) end), t, 0}
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

  @spec classify_atom(Term.t()) :: rename_t() | instantiate_t() | atomic_t()
  defp classify_atom(term)

  defp classify_atom(%Term{head: %Declaration{kind: :co}, args: [_ | _] = args} = term) do
    non_val_o_args =
      args
      |> Enum.with_index()
      |> Enum.filter(fn {a_id, _idx} -> non_signature_o_constant?(a_id) end)

    rename_candidate = Enum.find(non_val_o_args, nil, fn {a_id, _idx} -> !simple_term?(a_id) end)

    cond do
      Enum.empty?(non_val_o_args) ->
        {:atomic, TF.memoize(term)}

      is_nil(rename_candidate) ->
        # instantiate
        [{to_instantiate, idx} | _] = non_val_o_args
        %Term{head: decl, type: type} = TF.get_term!(to_instantiate)

        branches =
          Stream.map(gen_o(type), fn instance ->
            inst_term = %Term{term | args: List.replace_at(args, idx, instance)} |> TF.memoize()
            inst_def = {decl, instance}

            {inst_term, inst_def}
          end)

        {:instantiate, branches, o_type_size(type)}

      true ->
        # rename
        {rename_id, idx} = rename_candidate
        rename_term = TF.get_term!(rename_id)

        c = sk_term(rename_term.fvars, rename_term.type)

        replaced_term = %Term{term | args: List.replace_at(args, idx, c)} |> TF.memoize()
        {:rename, {replaced_term, eq(c, rename_id)}}
    end
  end

  defp classify_atom(term), do: {:atomic, TF.memoize(term)}

  @spec pure_o_type?(Type.t()) :: boolean()
  defp pure_o_type?(%Type{goal: :o, args: args}), do: Enum.all?(args, &pure_o_type?/1)
  defp pure_o_type?(_), do: false

  def simple_term?(term_id) when is_integer(term_id) do
    term = TF.get_term!(term_id)

    if length(term.args) === length(term.bvars) do
      pairs = Enum.zip(Enum.reverse(term.bvars), term.args)
      Enum.all?(pairs, fn {bv, arg_id} -> TF.make_term(bv) === arg_id end)
    else
      false
    end
  end

  defp non_signature_o_constant?(term_id) do
    term = TF.get_term!(term_id)

    pure_o_type?(term.type) &&
      term.head.kind == :co &&
      not Enum.member?(gen_o(term.type), term_id)
  end

  @spec sk_term([Declaration.free_var_t()], Type.t()) :: Term.term_id()
  defp sk_term(fvars, return_type) do
    skolem =
      Type.new(return_type, Enum.map(fvars, & &1.type))
      |> TF.make_fresh_const_term()

    app(skolem, Enum.map(fvars, &TF.make_term/1))
  end

  defp o_type_size(type), do: 2 ** o_occurrences(type)

  defp o_occurrences(%Type{goal: :o, args: args}),
    do: 1 + Enum.sum_by(args, &o_occurrences/1)
end
