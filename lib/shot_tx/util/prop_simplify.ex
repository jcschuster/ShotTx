defmodule ShotTx.Util.PropSimplify do
  @moduledoc """
  Propositional simplification of HOL terms via binary decision diagrams.

  The BDD operations come from `Module.Types.Descr`, the set-theoretic
  type representation Elixir ships with. The on-disk shape used here is
  the **lazy BDD** documented in the
  [Dec 2025 Elixir blog post](https://elixir-lang.org/blog/2025/12/02/lazier-bdds-for-set-theoretic-types/)
  and still in use as of Elixir 1.19:

    * `:bdd_top` / `:bdd_bot` — the constants
    * `{tag, payload}` — a **leaf**: any 2-tuple, acting as a singleton
      positive literal when used as a BDD on its own
    * `{lit, c, u, d}` — a **lazy node** denoting `(lit ∧ C) ∨ U ∨ (¬lit ∧ D)`

  Each non-connective HOL sub-formula becomes a leaf
  `{:shotds_prop, term_id}`. The tag is unique to this module so the
  generic `bdd_*` operations (which never introspect leaf tags) treat
  them opaquely; a tag-dispatched optimisation like the *eager literal
  intersection* added in Elixir's Feb 2026 update only applies to leaves
  it recognises (`:closed`, `:open`, …) and falls through for ours.

  > #### Caveat {: .warning}
  >
  > `Module.Types.Descr` is marked `@moduledoc false`. Its public
  > functions are reachable from outside, but the module is internal
  > to Elixir's compiler and not covered by backward-compatibility
  > guarantees. The shape changed between the early-BDD (3-tuple
  > leaves, hashed nodes) and lazy-BDD versions; expect more churn.
  > Pin a known-working Elixir version and re-test on upgrades.

  ## Modes

    * `:shallow` — simplify only the term's top-level propositional
      structure. Sub-formulas under quantifiers, abstractions or
      non-logical heads are opaque atoms.

    * `:deep` — bottom-up over the DAG: simplify every type-`o`
      sub-formula, including the bodies of quantifiers and other
      abstractions whose ultimate goal type is `o`.
  """

  alias Module.Types.Descr

  alias ShotDs.Data.{Term, Declaration}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TermTraversal
  use ShotDs.Hol.Patterns
  import ShotDs.Hol.Definitions, only: [true_term: 0, false_term: 0]

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
  ## Atom encoding — lazy-BDD leaf shape
  ##############################################################################

  # A propositional atom becomes a 2-tuple leaf. The tag is unique to this
  # module so the descr operations' tag-dispatched optimisations never
  # claim it; the payload is the HOL term ID, which gives a total order
  # consistent with equality (different term IDs ⇒ different leaves,
  # different leaves ⇒ different Erlang term comparison).
  @compile {:inline, atom_for: 1}
  defp atom_for(term_id) when is_integer(term_id), do: {:shotds_prop, term_id}

  ##############################################################################
  ## :shallow — compile to BDD and read back
  ##############################################################################

  @doc false
  @spec simplify_top(Term.term_id()) :: Term.term_id()
  def simplify_top(term_id) do
    bdd_verdict(term_to_bdd(term_id), term_id)
  end

  defp term_to_bdd(term_id) do
    case TF.get_term!(term_id) do
      truth() ->
        :bdd_top

      falsity() ->
        :bdd_bot

      negated(p) ->
        Descr.bdd_negation(term_to_bdd(p))

      disjunction(p, q) ->
        Descr.bdd_union(term_to_bdd(p), term_to_bdd(q))

      conjunction(p, q) ->
        Descr.bdd_intersection(term_to_bdd(p), term_to_bdd(q))

      implication(p, q) ->
        # p ⊃ q  ≡  ¬p ∨ q
        Descr.bdd_union(Descr.bdd_negation(term_to_bdd(p)), term_to_bdd(q))

      equivalence(p, q) ->
        # p ≡ q  ≡  (p ∧ q) ∨ (¬p ∧ ¬q)
        bp = term_to_bdd(p)
        bq = term_to_bdd(q)

        Descr.bdd_union(
          Descr.bdd_intersection(bp, bq),
          Descr.bdd_intersection(Descr.bdd_negation(bp), Descr.bdd_negation(bq))
        )

      _atom ->
        atom_for(term_id)
    end
  end

  ##############################################################################
  ## BDD → verdict
  ##
  ## Only tautology (⊤) and contradiction (⊥) are detected; any other BDD
  ## shape leaves the formula unchanged.  This keeps the oracle O(n) in the
  ## size of the propositional skeleton with no risk of exponential blowup.
  ##############################################################################

  defp bdd_verdict(:bdd_top, _term_id), do: true_term()
  defp bdd_verdict(:bdd_bot, _term_id), do: false_term()
  defp bdd_verdict(_bdd, term_id), do: term_id

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
        body_id = strip_bvars(term)

        case term_to_bdd(body_id) do
          :bdd_top -> List.foldr(term.bvars, true_term(), &TF.make_abstr_term!(&2, &1))
          :bdd_bot -> List.foldr(term.bvars, false_term(), &TF.make_abstr_term!(&2, &1))
          _ -> term_id
        end
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
