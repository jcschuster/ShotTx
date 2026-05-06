defmodule ShotTx.Prover.Paramodulation do
  @moduledoc """
  Naive lazy paramodulation helpers.

  Given a literal and a map of equations, generates all "paramodulants" —
  variants of the literal where some subterm `s` is replaced by an equal
  term `t`, using equations from the map.

  This implementation is *naive* in two senses:

    * It uses **structural identity** of subterms (term-id equality), without
      higher-order unification. An equation `s = t` rewrites only those
      occurrences of `s` whose memoised term-id matches the LHS exactly.
    * It rewrites by **DAG occurrence**, not tree occurrence: replacing `s`
      with `t` rewrites *all* shared occurrences of `s` simultaneously,
      consistent with the term factory's structure-sharing semantics.

  The module is *lazy* in that no preprocessing is done up front. Variants
  are generated on demand:

    * when a new literal enters the branch, using all known equations, and
    * when a new equation enters the branch, against all existing literals,
      using only the new equation.

  Function-position rewriting is not supported by this naive variant: the
  head of an applied term is a `Declaration`, not a separate term-id node,
  so an equation between two function constants only fires when one of the
  constants appears as a zero-arity term elsewhere in the literal. The
  alpha-decomposition into extensional/Leibniz form remains the complete
  fallback for higher-order equality reasoning.
  """

  alias ShotDs.Data.Term
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TermTraversal

  @typedoc "Map from a term-id to the set of all its known-equal term-ids."
  @type equation_map :: %{Term.term_id() => MapSet.t(Term.term_id())}

  @doc """
  Returns the paramodulants of `term_id` using `equations`.

  For every subterm `s` of `term_id` that is a key in `equations` and every
  replacement `t ∈ equations[s]`, produces the variant where every occurrence
  of `s` (by id) in `term_id` is replaced by `t`. Variants identical to the
  original (which can only happen if a degenerate `s = s` slipped into the
  map) are dropped, and duplicates are de-duplicated.
  """
  @spec paramodulants(Term.term_id(), equation_map()) :: [Term.term_id()]
  def paramodulants(_term_id, equations) when map_size(equations) == 0, do: []

  def paramodulants(term_id, equations) do
    term_id
    |> subterms()
    |> Enum.flat_map(fn s ->
      case Map.get(equations, s) do
        nil ->
          []

        replacements ->
          Enum.flat_map(replacements, fn t ->
            case replace_subterm(term_id, s, t) do
              ^term_id -> []
              result -> [result]
            end
          end)
      end
    end)
    |> Enum.uniq()
  end

  @doc """
  Returns the set of all subterm ids that appear inside `term_id`, including
  `term_id` itself.

  Heads (constants and variables in head position) are not separately
  represented as term-id nodes when applied; they only count as subterms when
  they appear as zero-arity terms.
  """
  @spec subterms(Term.term_id()) :: MapSet.t(Term.term_id())
  def subterms(term_id) do
    {result, _cache} =
      TermTraversal.fold_term!(term_id, fn term, arg_results ->
        arg_results
        |> Enum.reduce(MapSet.new(), &MapSet.union/2)
        |> MapSet.put(term.id)
      end)

    result
  end

  @doc """
  Returns `term_id` with every occurrence of the subterm `target` replaced by
  `replacement`.
  """
  @spec replace_subterm(Term.term_id(), Term.term_id(), Term.term_id()) ::
          Term.term_id()
  def replace_subterm(term_id, target, replacement) when term_id == target,
    do: replacement

  def replace_subterm(term_id, target, replacement) do
    transform = fn current_term, new_args, _env, acc_cache ->
      if current_term.id == target do
        {replacement, acc_cache}
      else
        new_term = %{current_term | args: new_args}
        {TF.memoize(new_term), acc_cache}
      end
    end

    {result_id, _cache} =
      TermTraversal.map_term!(term_id, nil, fn _, env -> env end, transform)

    result_id
  end
end
