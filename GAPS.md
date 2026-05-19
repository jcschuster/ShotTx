# Gap Analysis: Failing Proofs in `examples/structured_hol_problems.livemd`

This document catalogues the timeouts in the structured HOL benchmark livebook,
clusters them by the inference machinery they need, and compares against
Zipperposition output (obtained via the SystemOnTPTP web interface) on
representative cases.

## TL;DR

Most ShotTx timeouts trace back to one of five missing or under-tuned
capabilities. In priority order:

1. **Unifying paramodulation** — by far the biggest gap.
2. **Negative extensionality rule** for ground inequations of arrow type.
3. **Re-prioritised primitive substitution** for unit-set bindings on the
   first pass.
4. **Flex-headed literal shortcut** at depth 1.
5. **Lambda-lifting / rewriting under abstraction** — heavy, fewest payoffs.

Items 1–4 cover the bulk of the failures. The Non-Theorems section
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

### R1. Make paramodulation unifying, not just structural (large payoff)

When a new equation `s = t` enters the branch, run `ShotUn.unify({s, sub})`
against subterms of existing literals (and vice versa for new literals against
existing equations). Apply the resulting substitution to produce the
paramodulant. Keep the structural fast path for cases where the unifier is
trivially empty.

This single change unlocks the entire transitivity/congruence cluster and most
of §20.

### R2. Add a direct `neg_ext` rule (small payoff, very small change)

For ground inequations of arrow type — when `¬(f = g)` reaches the atomic
stage with `f, g` closed — emit `¬(f c = g c)` for a fresh skolem `c`
directly, bypassing the gamma round-trip. Completeness-preserving. Large
payoff on Examples 9, 13, 14.

### R3. Re-prioritise primitive substitution (small change, focused payoff)

Either:

- pre-seed `branch.term_ids` constants from the input formulas so unit-set
  heads are generated on the first prim-subst pass, or
- drop `prim_subst_after` to `0` for goal-only branches.

Combined with R1, should close Example 8 in seconds.

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
