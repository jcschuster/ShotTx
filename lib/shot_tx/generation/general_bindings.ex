defmodule ShotTx.Generation.GeneralBindings do
  @moduledoc ~S"""
  Generates general bindings for primitive substitution.

  A general binding for a quantified variable of type
  $\alpha_1\to\cdots\to\alpha_n\to o$ fixes a logical head symbol $Q$ while
  leaving the sub-formula positions as fresh free variables (holes):

  $$\lambda y_1^{\alpha_1}\cdots y_n^{\alpha_n}.\;
    Q\bigl(H_1\;\overline{y},\;\ldots,\;H_m\;\overline{y}\bigr)$$

  Generation is split into two independent phases so that an incrementally
  growing type universe can be accommodated without replaying earlier work:

    * **Base heads** — propositional connectives ($\top$, $\bot$, $\lnot$,
      $\land$, $\lor$, $\supset$, $\equiv$) and, at depth $\geq 2$,
      propositional compositions. Stable across the proof.

    * **Polymorphic heads** — $=_\tau$, $\forall_\beta$, $\exists_\beta$ for each
      type in the universe. At depth $\geq 2$, additionally includes
      compositions of polymorphic heads with propositional connectives
      ($\lnot(=_\tau)$, $(\forall_\beta)\land H$, etc.). Depth-dependent,
      requiring per-depth coverage tracking.

  Head specifications are lightweight `{matrix_fn, hole_types}` tuples;
  the expensive term construction happens only in `build_binding/2`.
  """

  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.Definitions
  import ShotDs.Hol.Dsl

  @typedoc """
  A head specification pairs a matrix builder with the types of its holes.

  The builder receives the applied hole terms ($H_i\\;\\overline{y}$, each of
  the appropriate result type) and returns the matrix term ID.
  """
  @type head_spec :: {([Term.term_id()] -> Term.term_id()), [Type.t()]}

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  @doc """
  Returns the base (propositional) head specifications for bindings over the
  given `arg_types` at the given `depth`. Independent of the type universe.
  """
  @spec base_heads([Type.t()], pos_integer()) :: [head_spec()]
  def base_heads(arg_types, depth) do
    hole = Type.new(:o, arg_types)

    propositional_heads(hole) ++
      if(depth >= 2, do: composed_propositional_heads(hole), else: [])
  end

  @doc """
  Returns polymorphic head specifications over the given set of `types` at the
  given `depth`. At depth 1 this produces flat heads; at depth $\\geq 2$ it
  additionally produces compositions with propositional connectives.
  """
  @spec polymorphic_heads([Type.t()], pos_integer(), Enumerable.t(Type.t())) :: [head_spec()]
  def polymorphic_heads(arg_types, depth, types) do
    hole = Type.new(:o, arg_types)

    flat_equality_heads(arg_types, types) ++
      flat_quantifier_heads(arg_types, types) ++
      if depth >= 2 do
        composed_equality_heads(arg_types, hole, types) ++
          composed_quantifier_heads(arg_types, hole, types)
      else
        []
      end
  end

  @doc """
  Constructs a binding term from argument types and a head specification.

  Fresh $H$ variables (holes) and temporary $y$ variables (binders) are
  created; the binders are abstracted away while the holes remain free for
  subsequent unification. Wrapped in `with_scratchpad!/1` so that the
  temporary binder terms are garbage-collected.
  """
  @spec build_binding([Type.t()], head_spec()) :: Term.term_id()
  def build_binding(arg_types, {matrix_fn, h_types}) do
    TF.with_scratchpad!(fn ->
      y_decls = Enum.map(arg_types, &Declaration.fresh_var/1)
      y_terms = Enum.map(y_decls, &TF.make_term/1)

      h_terms = Enum.map(h_types, &TF.make_fresh_var_term/1)
      h_applied = Enum.map(h_terms, &TF.fold_apply!(&1, y_terms))

      matrix = matrix_fn.(h_applied)

      List.foldr(y_decls, matrix, &TF.make_abstr_term!(&2, &1))
    end)
  end

  ##############################################################################
  # BASE (PROPOSITIONAL) HEADS
  ##############################################################################

  @spec propositional_heads(Type.t()) :: [head_spec()]
  defp propositional_heads(hole) do
    [
      {fn [] -> true_term() end, []},
      {fn [] -> false_term() end, []},
      {fn [h] -> neg(h) end, [hole]},
      {fn [h1, h2] -> h1 &&& h2 end, [hole, hole]},
      {fn [h1, h2] -> h1 ||| h2 end, [hole, hole]},
      {fn [h1, h2] -> h1 ~> h2 end, [hole, hole]},
      {fn [h1, h2] -> h1 <~> h2 end, [hole, hole]}
    ]
  end

  @spec composed_propositional_heads(Type.t()) :: [head_spec()]
  defp composed_propositional_heads(hole) do
    [
      {fn [h1, h2] -> neg(h1 &&& h2) end, [hole, hole]},
      {fn [h1, h2] -> neg(h1 ||| h2) end, [hole, hole]},
      {fn [h1, h2] -> neg(h1 ~> h2) end, [hole, hole]},
      {fn [h1, h2] -> neg(h1) &&& h2 end, [hole, hole]},
      {fn [h1, h2] -> h1 &&& neg(h2) end, [hole, hole]}
    ]
  end

  ##############################################################################
  # FLAT POLYMORPHIC HEADS (DEPTH >= 1)
  ##############################################################################

  # =_τ : H₁ =_τ H₂
  @spec flat_equality_heads([Type.t()], Enumerable.t(Type.t())) :: [head_spec()]
  defp flat_equality_heads(arg_types, types) do
    Enum.map(types, fn tau ->
      h_type = Type.new(tau, arg_types)
      {fn [h1, h2] -> app(equals_term(tau), [h1, h2]) end, [h_type, h_type]}
    end)
  end

  # Π_β(H), Σ_β(H) where H : ᾱ→β→o
  @spec flat_quantifier_heads([Type.t()], Enumerable.t(Type.t())) :: [head_spec()]
  defp flat_quantifier_heads(arg_types, types) do
    Enum.flat_map(types, fn beta ->
      h_type = Type.new(:o, arg_types ++ [beta])

      [
        {fn [h] -> app(forall_term(beta), h) end, [h_type]},
        {fn [h] -> app(exists_term(beta), h) end, [h_type]}
      ]
    end)
  end

  ##############################################################################
  # COMPOSED POLYMORPHIC HEADS (DEPTH >= 2)
  ##############################################################################

  # ¬(=_τ), (=_τ) ∧ H, (=_τ) ∨ H, (=_τ) ⊃ H, H ⊃ (=_τ)
  @spec composed_equality_heads([Type.t()], Type.t(), Enumerable.t(Type.t())) :: [head_spec()]
  defp composed_equality_heads(arg_types, hole, types) do
    Enum.flat_map(types, fn tau ->
      h_type = Type.new(tau, arg_types)
      eq = &app(equals_term(tau), [&1, &2])

      [
        {fn [h1, h2] -> neg(eq.(h1, h2)) end, [h_type, h_type]},
        {fn [h1, h2, h3] -> eq.(h1, h2) &&& h3 end, [h_type, h_type, hole]},
        {fn [h1, h2, h3] -> eq.(h1, h2) ||| h3 end, [h_type, h_type, hole]},
        {fn [h1, h2, h3] -> eq.(h1, h2) ~> h3 end, [h_type, h_type, hole]},
        {fn [h1, h2, h3] -> h3 ~> eq.(h1, h2) end, [h_type, h_type, hole]}
      ]
    end)
  end

  # ¬(Q(H)), Q(H₁) ∧ H₂, Q(H₁) ∨ H₂, Q(H₁) ⊃ H₂, H₂ ⊃ Q(H₁)
  # for Q ∈ {Π_β, Σ_β}
  @spec composed_quantifier_heads([Type.t()], Type.t(), Enumerable.t(Type.t())) :: [head_spec()]
  defp composed_quantifier_heads(arg_types, hole, types) do
    Enum.flat_map(types, fn beta ->
      h_type = Type.new(:o, arg_types ++ [beta])

      for qt <- [forall_term(beta), exists_term(beta)],
          spec <- compose_with_connectives(&app(qt, &1), h_type, hole) do
        spec
      end
    end)
  end

  # Given a unary builder (e.g., fn h -> Π_β(h) end), produces specs for its
  # negation and binary compositions with a propositional hole.
  @spec compose_with_connectives(
          (Term.term_id() -> Term.term_id()),
          Type.t(),
          Type.t()
        ) :: [head_spec()]
  defp compose_with_connectives(mk, q_hole, hole) do
    [
      {fn [h] -> neg(mk.(h)) end, [q_hole]},
      {fn [h1, h2] -> mk.(h1) &&& h2 end, [q_hole, hole]},
      {fn [h1, h2] -> mk.(h1) ||| h2 end, [q_hole, hole]},
      {fn [h1, h2] -> mk.(h1) ~> h2 end, [q_hole, hole]},
      {fn [h1, h2] -> h2 ~> mk.(h1) end, [q_hole, hole]}
    ]
  end
end
