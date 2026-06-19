defmodule ShotTx.Util.PropSimplify do
  @moduledoc """
  Propositional simplification of HOL terms via binary decision diagrams.

  Uses a self-contained ROBDD implementation with no dependency on Elixir
  internals. BDD nodes: `:bdd_top`, `:bdd_bot`, or `{var, high, low}` where
  `var` is a term ID integer and the variable ordering is ascending integer.

  `bdd_to_term/1` reads a BDD back as a minimal HOL formula using Shannon
  expansion with short-circuit identities, so the result is always at least
  as simple as the input and often simpler.

  ## Modes

    * `:shallow` — simplify only the term's top-level propositional
      structure. Sub-formulas under quantifiers, abstractions or
      non-logical heads are opaque atoms.

    * `:deep` — bottom-up over the DAG: simplify every type-`o`
      sub-formula, including the bodies of quantifiers and other
      abstractions whose ultimate goal type is `o`.
  """

  alias ShotDs.Data.{Term, Declaration}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TermTraversal
  use ShotDs.Hol.Patterns
  import ShotDs.Hol.Definitions, only: [true_term: 0, false_term: 0, neg_term: 0, or_term: 0, and_term: 0]

  @typedoc "Simplification depth."
  @type mode() :: :shallow | :deep

  ##############################################################################
  ## Public API
  ##############################################################################

  @doc """
  Simplifies the propositional structure of the term with the given ID.
  Defaults to `:deep`.
  """
  @spec simplify(Term.term_id(), mode()) :: Term.term_id()
  def simplify(term_id, mode \\ :deep) when mode in [:shallow, :deep] do
    TF.with_scratchpad!(fn ->
      case mode do
        :shallow -> simplify_top(term_id)
        :deep -> simplify_deep(term_id)
      end
    end)
  end

  ##############################################################################
  ## Atom encoding — ROBDD variable node
  ##
  ## Each propositional atom maps to the variable node {var, ⊤, ⊥}.
  ## var is the integer term_id, giving a consistent total order.
  ##############################################################################

  @compile {:inline, atom_for: 1}
  defp atom_for(term_id) when is_integer(term_id), do: {term_id, :bdd_top, :bdd_bot}

  ##############################################################################
  ## HOL term → BDD
  ##############################################################################

  @doc false
  @spec simplify_top(Term.term_id()) :: Term.term_id()
  def simplify_top(term_id) do
    term_id |> term_to_bdd() |> bdd_to_term()
  end

  defp term_to_bdd(term_id) do
    case TF.get_term!(term_id) do
      truth() -> :bdd_top
      falsity() -> :bdd_bot
      negated(p) -> bdd_neg(term_to_bdd(p))
      disjunction(p, q) -> bdd_or(term_to_bdd(p), term_to_bdd(q))
      conjunction(p, q) -> bdd_and(term_to_bdd(p), term_to_bdd(q))
      implication(p, q) -> bdd_or(bdd_neg(term_to_bdd(p)), term_to_bdd(q))
      equivalence(p, q) ->
        bp = term_to_bdd(p)
        bq = term_to_bdd(q)
        bdd_or(bdd_and(bp, bq), bdd_and(bdd_neg(bp), bdd_neg(bq)))
      _atom -> atom_for(term_id)
    end
  end

  ##############################################################################
  ## ROBDD operations
  ##
  ## mk/3 is the reduction rule: if high == low the variable is irrelevant.
  ## bdd_or and bdd_and apply Shannon expansion with the same variable ordering.
  ##############################################################################

  defp bdd_neg(:bdd_top), do: :bdd_bot
  defp bdd_neg(:bdd_bot), do: :bdd_top
  defp bdd_neg({a, h, l}), do: mk(a, bdd_neg(h), bdd_neg(l))

  defp bdd_or(:bdd_top, _), do: :bdd_top
  defp bdd_or(_, :bdd_top), do: :bdd_top
  defp bdd_or(:bdd_bot, b), do: b
  defp bdd_or(b, :bdd_bot), do: b
  defp bdd_or({a, h1, l1}, {a, h2, l2}), do: mk(a, bdd_or(h1, h2), bdd_or(l1, l2))
  defp bdd_or({a1, h1, l1}, {a2, _, _} = b2) when a1 < a2, do: mk(a1, bdd_or(h1, b2), bdd_or(l1, b2))
  defp bdd_or(b1, {a2, h2, l2}), do: mk(a2, bdd_or(b1, h2), bdd_or(b1, l2))

  defp bdd_and(:bdd_bot, _), do: :bdd_bot
  defp bdd_and(_, :bdd_bot), do: :bdd_bot
  defp bdd_and(:bdd_top, b), do: b
  defp bdd_and(b, :bdd_top), do: b
  defp bdd_and({a, h1, l1}, {a, h2, l2}), do: mk(a, bdd_and(h1, h2), bdd_and(l1, l2))
  defp bdd_and({a1, h1, l1}, {a2, _, _} = b2) when a1 < a2, do: mk(a1, bdd_and(h1, b2), bdd_and(l1, b2))
  defp bdd_and(b1, {a2, h2, l2}), do: mk(a2, bdd_and(b1, h2), bdd_and(b1, l2))

  defp mk(_a, same, same), do: same
  defp mk(a, h, l), do: {a, h, l}

  ##############################################################################
  ## BDD → HOL term (Shannon expansion with short-circuit identities)
  ##
  ## Each node {var, high, low} denotes (var ∧ high) ∨ (¬var ∧ low).
  ## The identities below avoid redundant connectives when one branch is ⊤/⊥:
  ##
  ##   {v, ⊤, ⊥}  = v
  ##   {v, ⊥, ⊤}  = ¬v
  ##   {v, ⊤, L}  = v ∨ L        (since (v ∧ ⊤) ∨ (¬v ∧ L) = v ∨ L)
  ##   {v, H, ⊥}  = v ∧ H
  ##   {v, ⊥, L}  = ¬v ∧ L
  ##   {v, H, ⊤}  = ¬v ∨ H       (since (v ∧ H) ∨ (¬v ∧ ⊤) = H ∨ ¬v)
  ##   {v, H, L}  = (v ∧ H) ∨ (¬v ∧ L)
  ##############################################################################

  defp bdd_to_term(:bdd_top), do: true_term()
  defp bdd_to_term(:bdd_bot), do: false_term()
  defp bdd_to_term({var, :bdd_top, :bdd_bot}), do: var
  defp bdd_to_term({var, :bdd_bot, :bdd_top}), do: TF.make_appl_term!(neg_term(), var)
  defp bdd_to_term({var, :bdd_top, low}) do
    or_term() |> TF.make_appl_term!(var) |> TF.make_appl_term!(bdd_to_term(low))
  end
  defp bdd_to_term({var, high, :bdd_bot}) do
    and_term() |> TF.make_appl_term!(var) |> TF.make_appl_term!(bdd_to_term(high))
  end
  defp bdd_to_term({var, :bdd_bot, low}) do
    neg_var = TF.make_appl_term!(neg_term(), var)
    and_term() |> TF.make_appl_term!(neg_var) |> TF.make_appl_term!(bdd_to_term(low))
  end
  defp bdd_to_term({var, high, :bdd_top}) do
    neg_var = TF.make_appl_term!(neg_term(), var)
    or_term() |> TF.make_appl_term!(neg_var) |> TF.make_appl_term!(bdd_to_term(high))
  end
  defp bdd_to_term({var, high, low}) do
    neg_var = TF.make_appl_term!(neg_term(), var)
    pos_branch = and_term() |> TF.make_appl_term!(var) |> TF.make_appl_term!(bdd_to_term(high))
    neg_branch = and_term() |> TF.make_appl_term!(neg_var) |> TF.make_appl_term!(bdd_to_term(low))
    or_term() |> TF.make_appl_term!(pos_branch) |> TF.make_appl_term!(neg_branch)
  end

  ##############################################################################
  ## :deep — bottom-up simplification
  ##############################################################################

  defp simplify_deep(term_id) do
    transform = fn term, new_args, _env, cache ->
      new_id = rebuild(term, new_args)
      {maybe_simplify_term(new_id), cache}
    end

    {result, _cache} =
      TermTraversal.map_term!(term_id, nil, fn _term, _env -> nil end, transform)

    result
  end

  defp rebuild(%Term{head: head, bvars: bvars}, new_args) do
    head_id = TF.make_term(head)
    body_id = TF.fold_apply!(head_id, new_args)
    List.foldr(bvars, body_id, &TF.make_abstr_term!(&2, &1))
  end

  defp maybe_simplify_term(term_id) do
    term = TF.get_term!(term_id)

    cond do
      term.type.goal != :o ->
        term_id

      not connective_head?(term.head) ->
        term_id

      term.bvars == [] ->
        simplify_top(term_id)

      true ->
        simplified_body = term |> strip_bvars() |> term_to_bdd() |> bdd_to_term()
        List.foldr(term.bvars, simplified_body, &TF.make_abstr_term!(&2, &1))
    end
  end

  defp strip_bvars(%Term{head: head, args: args}) do
    head_id = TF.make_term(head)
    TF.fold_apply!(head_id, args)
  end

  @connective_names ~w(⊤ ⊥ ¬ ∨ ∧ ⊃ ≡)

  defp connective_head?(%Declaration{kind: :co, name: name}) when name in @connective_names,
    do: true

  defp connective_head?(_), do: false
end
