defmodule ShotTx.Prover.LambdaLift do
  @moduledoc """
  Lambda-lifting as a tableau α-rule.

  Walks a term and, for every *closed* lambda subterm that occurs as an
  argument of a non-logical rigid constant, replaces the abstraction with a
  fresh constant `c` of the same arrow type and emits a typed-equality axiom
  `c =_τ λx̄. body`. The axiom is a normal branch formula — the
  `:equality_expansion` rule on `typed_equality` (Rules.classify_formula/1)
  decomposes it via `extensional_equality` / `leibniz_equality`, so
  subsequent reasoning rides on the standard γ/α/atomic/paramodulation
  pipeline.

  Importantly, lift constants are *not* added to `branch.defs`; they cannot
  be undone by `Semantics.unfold_defs!`. Definition unfolding and lambda
  lifting therefore do not interact.

  η-expansions of named constants (e.g. `λx. f(x)` for a constant `f` of
  arrow type) are skipped: lifting them would be useless indirection.
  """

  alias ShotDs.Data.{Declaration, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TermTraversal
  import ShotDs.Hol.Dsl, only: [eq: 2]

  @hol_connective_names ~w(⊤ ⊥ ¬ ∨ ∧ ⊃ ≡ = ∀ ∃)

  @doc """
  Returns `{rewritten_term, axioms}`. When no lift applies, `rewritten_term`
  equals the input and `axioms` is `[]`.
  """
  @spec lift(Term.term_id()) :: {Term.term_id(), [Term.term_id()]}
  def lift(term_id) do
    {new_id, final_cache} =
      TermTraversal.map_term!(
        term_id,
        nil,
        fn _term, env -> env end,
        &transform/4,
        fn _term, _env -> false end,
        %{axioms: []}
      )

    {new_id, Enum.reverse(final_cache.axioms)}
  end

  ##############################################################################
  # TRAVERSAL
  ##############################################################################

  defp transform(%Term{} = term, new_args, _env, cache) do
    if liftable_parent?(term.head) and new_args != [] do
      {lifted_args, cache_after} =
        Enum.map_reduce(new_args, cache, &maybe_lift_argument/2)

      {rebuild(term, lifted_args), cache_after}
    else
      {rebuild(term, new_args), cache}
    end
  end

  defp liftable_parent?(%Declaration{kind: :co, name: name})
       when is_binary(name),
       do: name not in @hol_connective_names

  defp liftable_parent?(%Declaration{kind: :co}), do: true
  defp liftable_parent?(_), do: false

  defp maybe_lift_argument(arg_id, cache) do
    arg = TF.get_term!(arg_id)

    cond do
      arg.bvars == [] -> {arg_id, cache}
      not closed_abstraction?(arg) -> {arg_id, cache}
      eta_expansion?(arg) -> {arg_id, cache}
      true -> introduce_lift(arg_id, arg, cache)
    end
  end

  defp closed_abstraction?(%Term{bvars: bvars, max_num: m, fvars: fvars}) do
    MapSet.size(fvars) == 0 and m <= length(bvars)
  end

  defp eta_expansion?(%Term{bvars: bvars, head: %Declaration{kind: kind}, args: args})
       when kind != :bv do
    n = length(bvars)

    length(args) == n and
      args
      |> Enum.with_index(0)
      |> Enum.all?(fn {arg_id, i} ->
        case TF.get_term!(arg_id) do
          %Term{head: %Declaration{kind: :bv, name: idx}, args: [], bvars: []} ->
            idx == n - i

          _ ->
            false
        end
      end)
  end

  defp eta_expansion?(_), do: false

  defp introduce_lift(abstr_id, %Term{type: abstr_type}, cache) do
    c_decl = Declaration.fresh_const(abstr_type)
    c_id = TF.make_term(c_decl)
    axiom_id = eq(c_id, abstr_id)
    {c_id, %{cache | axioms: [axiom_id | cache.axioms]}}
  end

  ##############################################################################
  # REBUILD
  ##############################################################################

  defp rebuild(%Term{id: id, args: args}, new_args) when new_args == args, do: id

  defp rebuild(%Term{head: head, bvars: bvars}, new_args) do
    head_id = TF.make_term(head)
    body_id = TF.fold_apply!(head_id, new_args)
    List.foldr(bvars, body_id, &TF.make_abstr_term!(&2, &1))
  end
end
