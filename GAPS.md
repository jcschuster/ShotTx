# Gap Analysis: Failing Proofs in `examples/structured_hol_problems.livemd`

This document catalogues the timeouts in the structured HOL benchmark livebook,
clusters them by the inference machinery they need, and compares against
Zipperposition output (obtained via the SystemOnTPTP web interface) on
representative cases.

## TL;DR

Most ShotTx timeouts trace back to one of five missing or under-tuned
capabilities. In priority order:

1. ~~**Unifying paramodulation** — by far the biggest gap.~~ ✓ **Done** (R1)
2. ~~**Negative extensionality rule** for ground inequations of arrow type.~~ ✓ **Done** (R2)
3. ~~**Re-prioritised primitive substitution** for unit-set bindings on the
   first pass.~~ ✓ **Done** (R3)
4. **Flex-headed literal shortcut** at depth 1.
5. **Lambda-lifting / rewriting under abstraction** — heavy, fewest payoffs.

Items 4–5 remain open. The Non-Theorems section
(livebook lines 168–263) is intentional countersatisfiables and not a real
failure cluster.

## Failure clusters

### 1. Ordered superposition / paramodulation through unification

ShotTx's paramodulation is **structural-only**:
`lib/shot_tx/prover/paramodulation.ex:9-31` documents that an equation `s = t`
only rewrites a literal when `s` appears as a memoised subterm by id. No
matching, no rewriting under abstractions, no rewriting in head position.

Zipperposition closes every transitivity/congruence/Leibniz instance with
`sup+`/`sup-` (superposition modulo unification) plus `ho_norm` (β/η
normalisation). On transitivity-Leibniz2:

```
sup-(cl0, cl2) → sup+(cl2, cl53) → ho_norm → demod
```

That is HO unification matching `(sk__4 @ sk__3)` against `(sk__4 @ X)` after
instantiating the Leibniz predicate variable.

ShotTx already has higher-order pre-unification available
(`ShotUn.unify/2` in `deps/shot_un/lib/shot_un.ex`); it just is not used in the
rewrite step.

**Affected examples**

- 6c transitivity (leibniz2/3, andrews, extensional)
- 7a congruence under endomorphisms (leibniz3, extensional)
- 7b congruence under predicates (andrews, extensional)
- 9b boolean extensionality (extensional)
- most of 20b/c/d (DeMorgan via predicate equalities)
- 22 set theory (all variants)

### 2. Unit-set primitive substitution under tighter scheduling

Example 8 (`l @ a @ b ⇒ a = b` with leibniz1/2) is the textbook test of
primitive substitution with a unit-set binding `λY. Y = a`. Zipperposition's
`ho_elim_pred` step instantiates the predicate variable with exactly that
binding:

```
∀X0. X0(b) ∨ ¬X0(a)   →   (b = a) ∨ ¬(a = a)   →   b = a
```

ShotTx **does** generate unit-set heads
(`lib/shot_tx/generation/general_bindings.ex:82-89`) and has BDD propositional
simplification, so the proof is reachable in principle. Two reasons it times
out:

- `prim_subst_after: 1` defers prim-subst until after gamma has fired once,
  and the `:prim_subst` rule has base cost `20 + 5·depth`
  (`lib/shot_tx/prover/rules.ex:100`). The iterative-deepening Manager only
  bumps both limits in lockstep when all workers idle
  (`lib/shot_tx/prover/manager.ex:222-285`), so the unit-set binding is buried
  under cheaper but useless instantiations.
- Constants `a, b` only enter `branch_constants` after δ-skolemisation, so
  the unit-set head `λY. H(Y) = a` is only generated on the *next* prim-subst
  pass.

**Affected examples**: 8 (leibniz1/2), 26 (andrews), 28.

### 3. Negative extensionality (`neg_ext`) for inequations

Example 14 (extension of identity): Zipperposition uses
`lambda_lifting + ext_sup + neg_ext`:

```
p(λX. X) ∧ ¬p(f)
→ #l_lift1 ≠ f               (ext_sup after lifting)
→ #l_lift1(#sk2) ≠ f(#sk2)   (neg_ext: introduce skolem)
→ #sk2 ≠ #sk2                (demod with f(X) = X)
→ ⊥
```

ShotTx handles **positive** extensionality
(`lib/shot_tx/prover/rules.ex:132-137`: typed equality at arrow type
decomposes via `extensional_equality`). The **negative** direction — "from
`f ≠ g`, introduce fresh skolem `c` and emit `f(c) ≠ g(c)`" — exists only as a
gamma/δ round-trip after unfolding the extensional definition, which is much
more expensive than Zipperposition's direct one-step rule.

**Note**: Zipperposition also reports **Unknown** on Example 13 (the conclusion
ordered the other way), so the upper bound on Example 13 itself is genuinely
hard. The other Ex 14 variants are tractable for Zipperposition though.

### 4. Flex-resolve / pruning for ∃ at function types

Example 27 (`?[D:$o>$o>$o]: ![P,Q]: D@P@Q <=> (P|Q)`): Zipperposition's whole
proof is `cnf` followed by `flex_resolve` — one step. The clause
`~X1 ∨ ~(X4 @ (sk(X4)) @ (sk1(X4)))` closes by instantiating the flex
(variable-headed) `X4` with `λa b. ¬(a ∨ b)`, making the literal
`¬¬(sk ∨ sk1)` and immediately resolvable.

ShotTx's prim-subst would eventually generate `λa b. ¬(a ∨ b)` (it is in
`composed_propositional_heads`), but only at depth 2 and only after a gamma
has fired. The `flex_resolve`/`flex_imitate` short-circuit on a flex literal
is missing.

**Affected examples**: 27, 28.

### 5. Set theory (Example 22)

Needs superposition through unfolded set definitions plus extensionality at
type `$i>$o`. Other provers use the two ingredients above (clusters 1 + 5)
plus aggressive simplification orientation; ShotTx gets stuck before making
any progress against the definition unfolding.

### Non-issue: the "Non-Theorems" section

Livebook lines 168–263 are intentional countersatisfiables. Timeouts here are
expected unless the SAT-exit path is made more aggressive — not a real failure
cluster.

## Recommendations

In priority order, with rough effort and payoff annotations.

### ✓ R1. Make paramodulation unifying, not just structural (large payoff)

**Implemented.** `lib/shot_tx/prover/paramodulation.ex` now exposes
`unifying_paramodulants/3` which calls `ShotUn.unify/2` to match equation
sides against subterms of existing literals (and new literals against existing
equations). The structural fast path is preserved; the unifying path is called
alongside it in `branch.ex`'s `ingest_formula/3` and
`paramodulate_literal_with_equations/3`.

### ✓ R2. Add a direct `neg_ext` rule (small payoff, very small change)

**Implemented.** `classify_neg_formula/1` in `lib/shot_tx/prover/rules.ex` now
handles `¬(f = g)` at arrow type: when both sides are closed it emits
`¬(f @ c = g @ c)` for a fresh skolem `c` directly (one-step α rule). When
either side has free variables it falls back to the extensional-equality
unfolding. This bypasses the gamma/δ round-trip that previously made these
goals expensive.

### ✓ R3. Re-prioritise primitive substitution (small change, focused payoff)

**Implemented** via two changes:

- `prim_subst_after` default dropped from `1` to `0` in
  `lib/shot_tx/data/parameters.ex`, so prim-subst is scheduled on the very
  first gamma firing.
- First-pass optimisation in `apply_rule({:prim_subst, …})` in
  `lib/shot_tx/prover/branch.ex`: when `progress == @fresh_progress` and the
  branch already has constants, all unit-set bindings (`λy. H(y) = c` for each
  constant `c`) are emitted immediately, bypassing the base/poly heads and the
  batch cap. The rule is then requeued with `covered_constants` set so
  subsequent firings follow the normal batched path.

### R4. Flex-headed shortcut (tiny rule)

When an atomic literal has a free variable in head position, try
instantiating with `⊥`/`⊤` and the connective heads at depth 1 before any
other prim-subst expansion. Closes Examples 27 and 28.

### R5. Lambda-lifting / rewriting under abstraction (heaviest)

Would unlock Examples 13, 14, 22. One of those (Ex 13) Zipperposition also
fails. Worth saving for last.

## Sources

- ShotTx code surveyed: `lib/shot_tx/prover/{branch,rules,paramodulation,contradiction_agent,manager,worker,term_order}.ex`,
  `lib/shot_tx/generation/general_bindings.ex`.
- Higher-order unification primitive: `deps/shot_un/lib/shot_un.ex`.
- Zipperposition traces obtained via SystemOnTPTP for Examples 6c
  (transitivity-leibniz2), 8 (leibniz1), 13, 14, 27. Representative TSTP
  derivations are captured in this document; full HTML responses were saved
  to `/tmp/zp_*.html` during the analysis.
