defmodule ShotTx.Prover.Paramodulation do
  @moduledoc """
  Utility helpers for term-DAG traversal used by
  `ShotTx.Prover.Demodulation`.

  ## Why this module no longer performs paramodulation

  Classical paramodulation derives a new formula by unifying an
  equation LHS with a subterm of a target literal, producing σ that
  binds variables on either side, and applying σ to the whole
  paramodulant. In ShotTx's rigid-variable tableau architecture
  **that is unsound as a branch-level rule**: γ-instantiation
  placeholders are free variables that `ShotTx.Prover.ContradictionAgent`
  reconciles globally via a CSP. Any branch-level σ commitment can:

    * Close a branch under a σ inconsistent with the σ CA eventually
      chooses (unsoundness on that branch), or
    * Pre-constrain CA's search space (loss of completeness).

  Both structural (identity-based) and unifying paramodulation therefore
  moved out of this module. Equational rewriting that produces **no**
  variable binding — i.e. cases where the matcher σ is empty — is
  handled by `ShotTx.Prover.Demodulation` in canonicalizing form. Cases
  that genuinely require binding are left to Leibniz/extensional
  α-expansion, which produces new atomic literals that `check_local_clashes`
  reports as unification-based clashes to CA — the correct place for
  σ commitments.

  ## What remains here

  Pure term-DAG traversal helpers reused by demodulation:

    * `subterms/1` — every subterm id reachable from a root.
    * `applied_subterms/1` — subterms whose outermost form is
      `h(a₁,…,aₙ)` (used for head-position η-expansion rewriting in
      `Demodulation`).
    * `replace_subterm/3` — DAG rewrite of every occurrence of a
      target subterm by a replacement.
  """

  alias ShotDs.Data.Term
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TermTraversal

  @doc """
  Returns the set of all subterm ids that appear inside `term_id`, including
  `term_id` itself.

  Heads are not separately represented as term-id nodes; they only count as
  subterms when they appear as zero-arity terms. To rewrite at head positions
  see `applied_subterms/1` and `ShotTx.Prover.Demodulation`.
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
  All subterms of `term_id` that are applied terms whose outermost form is
  not an abstraction (i.e. `bvars == []` and `args != []`).

  Public so `ShotTx.Prover.Demodulation` can iterate them for
  head-position rewriting via primitive η-expansion equations.
  """
  @spec applied_subterms(Term.term_id()) :: MapSet.t(Term.term_id())
  def applied_subterms(term_id) do
    {result, _cache} =
      TermTraversal.fold_term!(term_id, fn term, arg_results ->
        children = Enum.reduce(arg_results, MapSet.new(), &MapSet.union/2)

        if term.bvars == [] and term.args != [] do
          MapSet.put(children, term.id)
        else
          children
        end
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
        {rebuild_term(current_term, new_args), acc_cache}
      end
    end

    {result_id, _cache} =
      TermTraversal.map_term!(term_id, nil, fn _, env -> env end, transform)

    result_id
  end

  # Rebuild a term from its head and new args, recomputing all metadata fields.
  # Avoids the stale consts/fvars/max_num/tvars left by %{term | args: new_args}.
  defp rebuild_term(%Term{head: head, bvars: bvars}, new_args) do
    head_id = TF.make_term(head)
    body_id = TF.fold_apply!(head_id, new_args)
    List.foldr(bvars, body_id, &TF.make_abstr_term!(&2, &1))
  end
end
