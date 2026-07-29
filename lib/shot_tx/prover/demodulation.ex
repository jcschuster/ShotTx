defmodule ShotTx.Prover.Demodulation do
  @moduledoc """
  Rewrite-to-normal-form under a set of NCPO-LNF-oriented equations,
  restricted to rewrites that produce **no variable bindings**.

  ## The variable-binding restriction (rigid tableau architecture)

  ShotTx maintains a rigid-variable discipline: every branch-level
  rule is forbidden from committing to a value for any free variable.
  Free variables in branch formulas — γ-instantiation placeholders
  (`X_γ`) and unification variables — must be reconciled *globally*
  across sibling branches by `ShotTx.Prover.ContradictionAgent`, which
  runs a CSP over all recorded clash options and finds a single
  substitution satisfying every open branch's rigid-unification
  requirement. If any branch-level rule locally committed to `X_γ ↦ t`,
  it could:

    * Close a branch using a σ inconsistent with the σ CA eventually
      chooses (unsoundness), or
    * Force CA to solve a strictly harder problem because the local σ
      pre-emptively constrained the search (loss of completeness).

  Neither is acceptable. This module therefore admits **only** rewrites
  whose matcher σ is the empty substitution — i.e. the equation LHS
  must be *structurally identical* (memoized term-id equal) to the
  target subterm. No `ShotUn.unify` call, no σ, no commitment.

  Head-position rewriting via primitive η-expansion equations
  (`λv̄. h(v̄) = rhs`) is also binding-free: it structurally matches
  the head declaration `h` and applies `rhs` to the existing arguments
  via `TF.fold_apply!`. No free-variable substitution occurs.

  ## What this rules out

  The classical paramodulation case where equation `f(X) = a` rewrites
  a subterm `f(sk_b)` via matcher σ = `{X ↦ sk_b}` is **not** performed
  here — binding `X` (a γ-variable from the equation's ∀-quantifier)
  is a local commitment to X's value on this branch. Users get such
  rewrites only after γ produces the necessary instance and the
  resulting concrete equation is added to `branch.equations`, or by
  the Leibniz/extensional α-expansion — never as a shortcut by this
  module.

  ## Requirements this satisfies

    * **Soundness.** Every rewrite replaces `L[s]` with `L[t]` given
      `s = t ∈ equations` and `s` structurally identical to a subterm
      of `L`. Substitutivity of equality; no σ involved.
    * **No variable commitment.** By construction — σ = ∅ throughout.
      The branch's residual free variables are unchanged.
    * **Termination.** Every step is gated by `strict_gt?(s, t, order)`
      (the paper's NCPO). By Theorem 2 of Niederhauser & Middeldorp
      (2025), a chain of such steps is dominated by a well-founded
      CPO⁺ chain; no infinite descent.
    * **Determinism per session.** Term-id equality and equation-map
      iteration order are both deterministic.

  ## Requirements this does *not* satisfy

    * **Confluence.** Not pursued (would require Knuth-Bendix
      completion, out of scope).
    * **Refutational completeness for equational reasoning.** By
      design — the Leibniz/extensional α-expansion is the complete
      fallback. Demodulation is a canonicalization shortcut for the
      binding-free fragment.
  """

  alias ShotDs.Data.{Declaration, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotTx.Prover.{Paramodulation, TermOrder}

  @typedoc "Equation map keyed by LHS term id, values are sets of possible RHSs."
  @type equations :: %{Term.term_id() => MapSet.t(Term.term_id())}

  @doc """
  Reduces `term_id` to its normal form under `equations` and `order`.

  Guarantees:

    * If no equation matches any subterm with an NCPO-strictly-decreasing
      instance, returns `term_id` unchanged.
    * Otherwise returns a term id `t'` such that `term_id →*_{R,order} t'`
      and no further ordered rewrite applies to `t'`.
    * Termination is guaranteed by the paper's `(NCPO-LNF, CPO⁺)`
      reduction-order argument (see module docs).

  Empty equation map short-circuits to identity — used from
  `ShotTx.Prover.Branch.insert_formula/5` on the very first formulas
  where no equations exist yet.
  """
  @spec normalize(Term.term_id(), equations(), ShotTo.Parameters.t()) :: Term.term_id()
  def normalize(term_id, equations, _order) when map_size(equations) == 0, do: term_id

  def normalize(term_id, equations, order) do
    case one_step(term_id, equations, order) do
      :fixpoint -> term_id
      {:rewrote, next_id} -> normalize(next_id, equations, order)
    end
  end

  # Leftmost-outermost single rewrite step. Tries two rewrite kinds and
  # returns the first that succeeds:
  #
  #   1. Subterm rewrite via matching — the classical demodulation case.
  #      Applies when an equation LHS matches a DAG subterm modulo σ.
  #   2. Head rewrite via primitive η-expansion — applies when an
  #      equation LHS is `λv̄. h(v̄)`, an applied subterm has head `h`,
  #      and the resulting instance is strictly smaller under NCPO.
  #      This is the higher-order case where the equation is on the
  #      *function symbol* itself (not on any of its instances) and
  #      matching alone cannot see it because the LHS lives at a
  #      different type than any subterm of the target.
  defp one_step(term_id, equations, order) do
    case match_step(term_id, equations, order) do
      :fixpoint -> head_step(term_id, equations, order)
      rewrote -> rewrote
    end
  end

  defp match_step(term_id, equations, order) do
    term_id
    |> Paramodulation.subterms()
    |> Enum.find_value(:fixpoint, fn sub_id ->
      match_and_rewrite(term_id, sub_id, equations, order)
    end)
  end

  defp head_step(term_id, equations, order) do
    case collect_eta_heads(equations, order) do
      [] ->
        :fixpoint

      eta_heads ->
        term_id
        |> Paramodulation.applied_subterms()
        |> Enum.find_value(:fixpoint, fn s_id ->
          rewrite_head_position(term_id, s_id, eta_heads, order)
        end)
    end
  end

  # Structural identity match: the equation LHS must be the exact same
  # memoized term as the subterm. Term-id equality is precisely
  # structural equality under `ShotDs.Stt.TermFactory`'s hash-consing,
  # so this covers every rewrite whose matcher σ would be empty — the
  # only rewrites this module admits (see the module docs on the
  # variable-binding restriction).
  defp match_and_rewrite(term_id, sub_id, equations, order) do
    case Map.get(equations, sub_id) do
      nil -> nil
      rhs_set -> try_rewrite(term_id, sub_id, rhs_set, order)
    end
  end

  # Rewrites `term_id[sub_id]` by replacing `sub_id` with an
  # NCPO-strictly-smaller RHS from `rhs_set`. Termination follows from
  # the reduction-order argument: every rewrite strictly reduces the
  # target under the paper's `A⁺`.
  defp try_rewrite(term_id, sub_id, rhs_set, order) do
    Enum.find_value(rhs_set, nil, fn rhs_id ->
      if TermOrder.strict_gt?(sub_id, rhs_id, order) do
        new_id = Paramodulation.replace_subterm(term_id, sub_id, rhs_id)
        if new_id == term_id, do: nil, else: {:rewrote, TF.commit_to_global!(new_id)}
      end
    end)
  end

  # ----------------------------------------------------------------------------
  # Head rewriting via primitive η-expansion equations
  # ----------------------------------------------------------------------------
  #
  # Handles equations `λv̄. h(v̄) = rhs` — the higher-order case where the
  # equation is on the function symbol `h` itself. Subterm matching
  # cannot see this because `λv̄. h(v̄)` and any applied subterm `h(t̄)`
  # live at different types.

  # Returns `[{head_decl, arity, rhs_ids}]` for every equation whose LHS
  # is a primitive η-expansion `λv̄. h(v̄)` and whose stored RHS was
  # oriented under NCPO. RHSs that fail the strict-order gate are
  # filtered out here so the per-subterm loop does not waste work.
  defp collect_eta_heads(equations, order) do
    Enum.flat_map(equations, fn {lhs_id, rhs_ids} ->
      case eta_head_pattern(lhs_id) do
        nil ->
          []

        {head_decl, arity} ->
          oriented =
            Enum.filter(rhs_ids, fn rhs_id ->
              TermOrder.strict_gt?(lhs_id, rhs_id, order)
            end)

          if oriented == [], do: [], else: [{head_decl, arity, oriented, lhs_id}]
      end
    end)
  end

  defp eta_head_pattern(term_id) do
    case TF.primitive_term?(term_id) do
      {:ok, true} ->
        %Term{head: head_decl, bvars: bvars} = TF.get_term!(term_id)

        case bvars do
          [] -> nil
          _ -> {head_decl, length(bvars)}
        end

      _ ->
        nil
    end
  end

  defp rewrite_head_position(term_id, s_id, eta_heads, order) do
    s = TF.get_term!(s_id)
    arity = length(s.args)

    Enum.find_value(eta_heads, nil, fn {head_decl, n, rhs_ids, _lhs_id} ->
      cond do
        not head_matches?(s.head, head_decl) -> nil
        n > arity -> nil
        true -> apply_head_rewrite(term_id, s_id, s.args, rhs_ids, order)
      end
    end)
  end

  defp head_matches?(%Declaration{} = h1, %Declaration{} = h2), do: h1 == h2

  defp apply_head_rewrite(term_id, s_id, args, rhs_ids, order) do
    Enum.find_value(rhs_ids, nil, fn rhs_id ->
      rewritten_sub = TF.fold_apply!(rhs_id, args)

      # Per-instance NCPO recheck: the equation's `lhs > rhs` was
      # verified at the primitive η-expansion level, but the actual
      # rewrite happens at an applied instance. `λv̄. h(v̄) > rhs`
      # implies `h(ā) > rhs(ā)` by monotonicity of the paper's `A`
      # layer, but we double-check on the βη-normal forms so a broken
      # `TF.fold_apply!` invariant cannot leak an unsound rewrite.
      if TermOrder.strict_gt?(s_id, rewritten_sub, order) do
        new_id = Paramodulation.replace_subterm(term_id, s_id, rewritten_sub)
        if new_id == term_id, do: nil, else: {:rewrote, TF.commit_to_global!(new_id)}
      end
    end)
  end
end
