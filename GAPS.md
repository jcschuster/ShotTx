# Gap Analysis: Failing Proofs in `examples/structured_hol_problems.livemd`

This document catalogues the gaps in ShotTx's tableau calculus that keep the
"hard" examples in the structured HOL benchmark from closing. Gaps are
identified by comparing ShotTx's behaviour against external traces from
Zipperposition (superposition) and Leo-III (resolution + extensionality
rules), obtained via the SystemOnTPTP web service.

The companion document is [`CALCULUS.md`](./CALCULUS.md), which describes the
rules currently implemented.

## Examples surveyed

| Example | Plain `=` | Leibniz 1/2/3 | Andrews | Extensional |
|---|---|---|---|---|
| 6c Transitivity | passes | timeout | timeout | timeout |
| 13 Extension with Identity | timeout | timeout | timeout | timeout |
| 14 Extension of Identity | timeout | timeout | timeout | timeout |
| 20c DeMorgan (λ form) | passes | timeout | timeout | timeout |
| 20d DeMorgan (`(&)` form) | passes | timeout | timeout | timeout |
| 22a Set distributivity | timeout | timeout | timeout | timeout |
| 22b Powerset of null | passes | timeout | timeout | timeout |
| Inj Cantor (Ex 21) | — | — | — | timeout |

## TL;DR — six gaps

| Gap | Short description | Unlocks |
|---|---|---|
| **G4** | Head-conflict α-rule (same-head positive/negative atoms → argument disequality) | Ex 13, 14, 20c/d-Leibniz/Andrews, 22 variants |
| **G7** | Fixpoint definition unfolding (today `unfold_defs!` is one-pass) | Ex 22a plain + all 22 variants |
| **G1** | Heads of applied terms registered as ground subterms | Ex 6c-Leibniz/Andrews |
| **G6** | Data-driven γ vs prim-subst priority | Ex 6c-extensional, 20c-extensional, 22 |
| **G9** | bool_ext — dual unit encoding of `s =_o t` | Inj Cantor's left-inverse construction |
| **G10** | Demand-driven prim-subst + self-application head specs | Inj Cantor diagonal |
| **G11′** | Worker-side equational-saturation submode | Inj Cantor closure (no external solver) |

G1 and G4 together account for most of the Leibniz/Andrews/extensional family
of failures. G7 is a small implementation change in `shot_ds`. G6, G9, G10
and G11′ stack to unlock the Cantor / set-theoretic cases.

---

## How the reference provers close these

Quoted derivations come from SystemOnTPTP runs against Zipperposition 2.1
and Leo-III 1.7.20, with problem files in `/tmp/ex*.p` during analysis.
Both reference provers agree on the inferential *shape* even when the
sub-strategies differ (Zipperposition: superposition + λ-lifting; Leo-III:
resolution + `paramod_ordered` / `func_ext` / `bool_ext` / `prim_subst`).

### Common pattern: "extract argument disequality from same-head atoms"

Across Ex 13, 14, 20c/d, 22-Leibniz, and Inj Cantor preprocessing, the
critical inference is the same:

> Given `h @ A` and `¬(h @ B)` on the same branch, where `h` is a rigid
> constant and direct unification of `A` with `B` fails, **post `A ≠ B`**.

Zipperposition packages this as `ext_sup` (superposition on a literal of
shape `p @ s = ⊤` against `p @ t = ⊥`); Leo-III packages it as
`paramod_ordered` between two literals of the same predicate head, followed
by `simp`.

ShotTx has no analogous step. The local clash check
(`check_local_clashes/3` in `lib/shot_tx/prover/branch.ex`) calls
`ShotUn.unify({h@A, h@B})`, fails when `A` and `B` have differing rigid
heads or λ-bodies, **and gives up**. The two literals then sit unused.

### Common pattern: "Leibniz universal → Skolem head witness"

For Ex 6c (Leibniz variants), the negated conjecture
`¬(l @ a @ c)` unfolds (with `l₂ = λX,Y. ∀P. P@Y ⇒ P@X`) to
`∃P. P@c ∧ ¬(P@a)`. δ-skolemising gives `q @ c` and `¬(q @ a)` where
`q : $i→$o` is a fresh Skolem. The proof closes by γ-instantiating both
Leibniz universals (`l @ a @ b`, `l @ b @ c`) with `P ↦ q`.

Zipperposition reaches this via `prune_arg_fun` + `condensation` + `sup-` +
`flex_resolve`. Leo-III hands the propositional residue to E after
`defexp_and_simp_and_etaexpand`. Either way, the entry point is the same:
the universal `∀P` should be instantiated with the Skolem head `q` that
already lives on the branch.

---

## G1 — Heads of applied terms not registered as ground subterms

**Where.** `lib/shot_tx/prover/branch.ex` `register_ground_subterms/3`
(via `Paramodulation.subterms/1` in
`lib/shot_tx/prover/paramodulation.ex:126`).

**The bug.** The closed-subterm collector folds over a term's args; the
*head* `Declaration` of an applied term is not represented as a separate
term-id node when args ≠ []. So when `q @ c` and `¬(q @ a)` enter the
branch, the constant `q : $i→$o` is never inserted into
`branch.ground_terms[$i→$o]`. The γ-recipes registered by the two
Leibniz universals (each at recipe type `$i→$o`) therefore never fire
with `P ↦ q`.

**Why it matters.** Without `P ↦ q`, the proof can only close via
flex-rigid HO unification on `P_fresh @ a ≈ q @ a` (which ShotUn supports
via imitation, but routes through the `ContradictionAgent` CSP and is
much more expensive than a ground instance).

**Fix.** In `collect_new_closed_subterms/2`, when visiting `c @ args`
for a closed applied term `c`, also stage `(TF.make_term(c.head), c.head.type)`
into `new_by_type` whenever `c.head.kind == :co` and
`c.head.name ∉ @hol_connective_names`. The cascade then triggers the
right γ-recipes once per Skolem head.

**Unlocks.** Ex 6c (Leibniz 1/2/3, Andrews variants).

---

## G4 — Head-conflict α-rule

**The missing rule.** For every pair `(ℓ⁺, ℓ⁻)` on a branch where:

- `ℓ⁺ = h @ a₁ @ … @ aₙ`,
- `ℓ⁻ = ¬(h @ b₁ @ … @ bₙ)`,
- `h.kind == :co` and `h.name ∉ @hol_connective_names`,
- `ShotUn.unify({ℓ⁺, ℓ⁻})` returned no solutions,

emit `¬(a₁ @ … @ aₙ = b₁ @ … @ bₙ)` (typed equality at the appropriate
type) as a derived α-step.

**Soundness.** `p @ s ∧ ¬(p @ t)` together with `s = t` would give
`p @ s ∧ ¬(p @ s) = ⊥`. So the consistent extension forces `s ≠ t`. The
rule is linear (no branching).

**Where.** `lib/shot_tx/prover/branch.ex`, new clause in
`apply_rule({:atomic, _}, …)` after `paramodulate_literal_with_equations/3`.
New history rule tag `:head_conflict`, with a rendering symbol (e.g. `"⊕"`)
in `lib/shot_tx/proof.ex` `rule_symbol/1`.

**How it closes the family of failures.**

- **Ex 13 / Ex 14:** From `p @ L₁` (post λ-lift of the identity λ) and
  `¬(p @ (λX. f@X))` (η-expanded form of `¬(p @ f)`):
  ```
  head_conflict  →  L₁ ≠ (λX. f@X)
  neg_ext        →  L₁ @ sk ≠ f @ sk
  paramod (L₁@X=X)  →  sk ≠ f @ sk
  paramod (f@X=X)   →  sk ≠ sk   →  ⊥
  ```
  (ShotDs stores βη-NF, so `p @ f` and `p @ (λX. f@X)` are the same
  term-DAG node — Ex 13 and Ex 14 are *identical* inside the prover.)

- **Ex 20c/d (DeMorgan, Leibniz/Andrews variants):** From `q @ (&)` and
  `¬(q @ (λX,Y. ¬(¬X|¬Y)))` (where `q` is the Skolem from the negated
  Leibniz universal):
  ```
  head_conflict  →  (&) ≠ (λX,Y. ¬(¬X|¬Y))
  arrow-type neg_ext (existing, iterated twice)
                 →  (c₀ & c₁) ≠ ¬(¬c₀ | ¬c₁)   (at type $o)
  eq_bool + BDD oracle  →  ⊥
  ```

- **Ex 22 Leibniz/Andrews/extensional:** reduces them to the plain `=`
  form. After G4, all of 22a's variants share the gap of 22a plain (G7).

**Why not just stronger HO unification.** ShotUn does Huet-style imitation
and projection, and can in principle find a unifier between
`p @ L₁` and `p @ (λX. f@X)` by binding `L₁ ↦ λZ. f@Z`. But:

- This *succeeds* on Ex 13/14 only with the extra information `∀X. f@X = X`,
  which the unifier ignores. The local clash check sees a failure.
- For Ex 20c/d, the heads `(&)` and `(λX,Y. ¬(¬X|¬Y))` are genuinely not
  HO-unifiable in βη-NF; their bodies share no rigid head. Imitation has
  nowhere to start.

G4 is the inferential bridge: posting the disequality lets the existing
arrow-type `neg_ext` (`classify_neg_formula/1` in
`lib/shot_tx/prover/rules.ex:191`) and the BDD oracle finish the proof
without HO-unification heroics.

---

## G6 — Data-driven γ vs prim-subst priority

**Today.** `apply_rule({:gamma, …})` in `lib/shot_tx/prover/branch.ex:331`
schedules a `:prim_subst` rule whenever the popped γ has fired for the
first time and `type.goal == :o`. Prim-subst is then in the queue with
its base cost `20 + 5·depth`, and on its first firing the unit-set
front-loading optimisation kicks in.

**The mismatch.** When the branch already carries closed subterms of
type matching the γ-recipe (provided by δ-skolemisation or G1), the
useful instantiation is the *ground* one and prim-subst is pure noise.
Concretely for the extensional variant of Ex 6c, the δ produces a
ground `c₀ : $i`, the ground-subterm cascade fires the γ-recipe with
`Z ↦ c₀`, and paramodulation closes — *except* that prim-subst has
already enqueued `λ_. ⊤`, `λ_. ⊥`, and a depth-1 polynomial in the
holes, all of which insert literals and trigger further β-splits.

**Fix.** In `apply_rule({:gamma, …})` at the prim-subst-trigger site,
gate on `branch.ground_terms[type] == MapSet.new()`. When the cascade
already has a candidate, skip the prim-subst scheduling for that recipe
(it can still be woken later by the iterative-deepening Manager if the
ground instantiation doesn't close).

**Unlocks.** Ex 6c-extensional, Ex 20c-extensional, and contributes to
Ex 22's convergence (without G6 the powerset/distributivity unfolding
chains trigger prim-subst at every nested γ).

---

## G7 — Fixpoint definition unfolding

**Where.** `deps/shot_ds/lib/shot_ds/stt/semantics.ex` `unfold_defs/2`
at line 548.

**The bug.** `unfold_defs/2` does a single bottom-up `map_term/4` pass.
Children are inlined before their parent, so `inter @ b @ c` is expanded
before `union @ a @ (…)`. **But** the RHS of `union` and `inter` introduces
new references to `elem`, and those new references are not in the original
term tree — the bottom-up pass has already left them by the time they
appear. So `elem` survives one unfolding round.

For Ex 22a (`union @ a @ (inter @ b @ c) = inter @ (union @ a @ b) @ (union @ a @ c)`),
full propositional shape requires `O(definition-depth)` re-firings of the
`:atomic` rule's `unfold_if_possible/2` (`branch.ex:822`). Each re-firing
spends a queue cycle, and each intermediate form is α/β-decomposed before
the next round of unfolding — so β-splits compound on partially-unfolded
terms.

**Fix.** Make `unfold_defs/2` iterate to a fixpoint on `by_name`
references — keep re-running the transform until
`term.consts ∩ defs.keys == ∅`. One rule firing then replaces the entire
definition chain. Structural sharing in the term factory deduplicates
intermediate terms, so the cost is `O(defs.depth × term.size)` once,
not `O(defs.depth)` queue cycles each generating `O(term.size)` work.

**Unlocks.** Ex 22a plain `=` (with G6 contributing). With G4 layered on
top, all of Ex 22's Leibniz/Andrews/extensional variants follow.

---

## G9 — bool_ext (dual unit encoding of `s =_o t`)

**Where.** `lib/shot_tx/prover/rules.ex` `classify_formula/1` and
`classify_neg_formula/1`, the `:eq_bool` / `:neq_bool` clauses.

**The asymmetry.** ShotTx's α-rule on `s =_o t` decomposes to
`s ≡ t`, which the β-rule then splits into `(s ∧ t) | (¬s ∧ ¬t)`.
This is logically complete but throws the equation back into the
*branching* search.

Leo-III's `bool_ext` instead emits the **two unit forms** as α-residues:

```
s =_o t   ──bool_ext──▶   ¬s ∨ t,    s ∨ ¬t
```

(and the universal closure `∀x̄. s@x̄ =_o t@x̄` becomes
`∀x̄. ¬(s@x̄) ∨ t@x̄` and `∀x̄. s@x̄ ∨ ¬(t@x̄)`).

**Why it matters for Inj Cantor.** The Leibniz unfolding of
`sk1@P = sk1@Q` produces a universal equation
`∀R. R @ (sk1@P) = R @ (sk1@Q)`. After δ on the existential introduced by
negating the implication, this becomes `sk2 @ (sk1@A) @ B = A @ B` —
the "defining equation of the left inverse sk2". Leo-III then
`bool_ext`s this into `¬(sk2 @ (sk1@A) @ B) ∨ (A @ B)` (and the dual),
which **survives across further γ instantiations as a unit clause** and
participates in subsequent paramodulation / clash detection.

ShotTx's `≡`-then-β path produces the same logical content as a
*branch split*. The split is fine until further γ rules expand on each
branch independently, at which point the duplicated work compounds.

**Fix.** When classifying `s =_o t` (or its negation), in addition to
the existing `≡` decomposition, also enqueue both bool_ext unit forms.
The dual encoding lets paramodulation see the rewrite directions
without requiring a β-split to expose them.

**Unlocks.** The left-inverse extraction step in Inj Cantor; smaller
speedups on extensional-variant proofs that pass through `eq_bool` on
deeply-nested literals.

---

## G10 — Demand-driven prim-subst + self-application head specs

**The hard problem.** Inj Cantor's closure requires synthesising the
diagonal predicate `λx. ¬(sk2 @ x @ x)`. This appears in Leo-III's trace
after `prim_subst` with the binding `λE. C@E | D@E` followed by
`pre_uni` instantiating `C, D` to `sk2 @ z`-projections, and in
Zipperposition's trace via `ho.refine` followed by `lambda_lifting`.

**Two coupled deficiencies in ShotTx.**

### G10a — `polymorphic_heads` can't synthesise self-application

`GeneralBindings.build_binding/2`
(`lib/shot_tx/generation/general_bindings.ex:100-112`) constructs each
hole `H_i` as a *separate* free variable applied to *all* binders. So
the depth-1 polymorphic binding for an `(α→o)→o` quantifier is
`λx. H_1 @ x` with a single fresh `H_1 : α→o`. To realise the diagonal,
HO unification must later bind `H_1 ↦ λz. ¬(sk2 @ z @ z)` — an
imitation step that ShotUn can do in principle, but only inside a
unification clash whose existence presupposes the diagonal *already*
being on the branch.

The bound variable `x` appearing *twice* in the matrix is not in the
grammar.

**Fix (a).** Add to `polymorphic_heads` a small family of self-applied
head specs at depth ≥ 2:

```
λx̄. ¬(H @ x̄ @ x̄)
λx̄. (H @ x̄ @ x̄)
λx̄. (H @ x̄ @ x̄) ⊃ (H₂ @ x̄)        -- and disjunctive variants
```

where `H` is one hole reused at two positions. One explicit head per
arity gives prim-subst direct access to diagonal patterns without
round-tripping through unification. Each head's holes still get applied
to the bound variable, but the *expression-level* self-application makes
the diagonal a single binding, not a unification residue.

### G10b — prim-subst is not informed by unification residue

Currently `:prim_subst` fires according to a static schedule (γ-driven).
For Cantor-style problems, the useful binding is the one that *matches
some existing literal's flex-headed argument*. ShotUn already returns
deferred flex-flex pairs in `flex_pairs` (`shot_un.ex:73-84`); these
are dropped by ShotTx today.

**Fix (b).** Capture `flex_pairs` from `check_local_clashes/3` /
`unifying_paramodulants/3` into a branch-level `flex_residue` map keyed
by hole type. When `:prim_subst` is up for a recipe whose type matches a
flex-residue entry, prefer the head specs that produce a binding of the
right *shape* (arity + return type) over the full enumeration. This is
the spirit of Zipperposition's `ho.refine` — let unification residues
drive prim-subst, instead of generating bindings blindly.

**Unlocks.** Inj Cantor's diagonal. (Surjective Cantor already passes
and would be unaffected or slightly faster.)

---

## G11′ — Equational-saturation submode (no external solver)

**Replaces an earlier draft "delegate to E" gap that was retracted.**
ShotTx is a tableau prover; delegating FO residues to an external
resolver dodges the gap rather than closing it. The replacement is a
Worker-level scheduling change.

**The symptom.** By the time ShotTx has done the HO steps for Inj
Cantor (Leibniz decomp + bool_ext from G9 + one prim-subst firing for
the disjunction head from G10), the branch state is essentially
first-order: a universal equation `sk2 @ (sk1@A) @ B = A@B`, a handful
of bool_ext-derived unit clauses, no remaining λ-abstractions in
literal positions, and a few free `H_i` holes from prim-subst. This
*would* close in a few paramod-and-clash steps — if the search could
focus on it.

Instead, the iterative-deepening Manager bumps `prim_limit` in
lockstep with `gamma_limit` and prim-subst on the next round re-issues
a fresh batch of bindings, generating more holes that themselves want
γ instances. The queue grows; the FO residue never gets a focused round
to close.

**The submode.** Detect that a branch has entered FO-equational
character. Locally:

- `branch.queue` contains no `:prim_subst` rules that haven't fired at
  least once, and
- no `:gamma` recipe is of a type with an arrow above `$o`, and
- new literals arriving via paramodulation in the last `k` cycles all
  type-check as ground or have only first-order free variables (i.e.
  type's `goal == :o` with all `args` base, or all binders base).

When the predicate trips, the Worker enters a saturation sub-loop:

1. Drain the queue keeping only `:atomic`, `:alpha`, `:beta`,
   paramodulation insertions, and `:gamma` instances over base types.
2. Defer all further arrow-type `:gamma` and `:prim_subst` rules to a
   holdback list.
3. Run paramodulation + local clash detection to fixpoint over the
   literal set, allowing only `unifying_paramodulants/3` to introduce
   new HO bindings whose substitutions are first-order (free var ↦
   ground / FO term).
4. If saturation closes the branch → done. If it stabilises without
   closure, replay the holdback list at higher deepening.

**Where.** `lib/shot_tx/prover/worker.ex`. The Worker is already the
right place: it owns the rule-application loop and has access to
branch state and the params. Add a `:saturating` mode flag and a small
predicate function over `branch.queue` + `branch.literals`.

**Soundness / completeness.** No new calculus rules. The held-back
rules come back when the saturation round doesn't close — so refutational
completeness is preserved. The submode is a re-prioritisation, not a
restriction.

**What it costs.** Practically nothing. The trip condition is a
cheap scan over the queue and the literal set.

**Unlocks.** Inj Cantor closure. Also speeds up the post-G7 large
set-theory residues of Ex 22 by preventing wasteful prim-subst
expansions once the propositional residue is in hand.

---

## Where each gap lives

| Gap | File | Approximate location |
|---|---|---|
| G1 | `lib/shot_tx/prover/branch.ex` (`collect_new_closed_subterms/2`) and/or `lib/shot_tx/prover/paramodulation.ex` (`subterms/1`) | Augment to emit synthetic head-only term when `head.kind == :co` and not a connective. |
| G4 | `lib/shot_tx/prover/branch.ex` `apply_rule({:atomic, _}, …)` after `paramodulate_literal_with_equations/3`; `lib/shot_tx/proof.ex` `rule_symbol/1` | New history tag `:head_conflict`, scan literals for opposite-polarity same-head pair, post argument disequality. |
| G6 | `lib/shot_tx/prover/branch.ex` `apply_rule({:gamma, …})` line 331 | Gate `prim_subst_after` trigger on `branch.ground_terms[type] == MapSet.new()`. |
| G7 | `deps/shot_ds/lib/shot_ds/stt/semantics.ex` `unfold_defs/2` (line 548) | Loop until `term.consts ∩ defs.keys == ∅`. |
| G9 | `lib/shot_tx/prover/rules.ex` `classify_formula/1` and `classify_neg_formula/1` `:eq_bool` clauses | Also enqueue `¬s ∨ t` and `s ∨ ¬t` (and the universal-closure variants). |
| G10a | `lib/shot_tx/generation/general_bindings.ex` `composed_quantifier_heads/3` (or a new `self_applied_heads/2`) | Add a small family of `λx̄. … (H @ x̄ @ x̄) …` specs at depth ≥ 2. |
| G10b | `lib/shot_tx/prover/branch.ex` (capture flex residues from clash + paramod), `lib/shot_tx/prover/worker.ex` (use them when scheduling prim-subst) | Capture `flex_pairs` from `ShotUn.unify` results; bias prim-subst head selection by residue type. |
| G11′ | `lib/shot_tx/prover/worker.ex` | Detect FO-equational saturation; defer arrow-type γ and prim-subst rules; run paramod + clash to fixpoint. |

## Dependency graph between gaps

```
                              ┌──── Ex 6c Leibniz/Andrews
                G1 ───────────┤
                              └──── (combines with G6 for Andrews depth)

                              ┌──── Ex 13, Ex 14 (all variants)
                G4 ───────────┼──── Ex 20c, Ex 20d (Leibniz/Andrews/ext)
                              └──── Ex 22 Leibniz/Andrews/ext (with G7)

                G6 ───────────┬──── Ex 6c extensional
                              └──── Ex 20c/22 extensional (with G7)

                G7 ───────────┬──── Ex 22a plain `=`
                              └──── Ex 22 family (with G4)

       G9 ──┐
       G10a ┼─── Inj Cantor diagonal
       G10b ┘    (with G11′ for closure)

                G11′ ───────────── Inj Cantor closure
                                   (also speeds up post-G7 Ex 22)
```

## Sources

- ShotTx code surveyed:
  `lib/shot_tx/prover/{branch,rules,paramodulation,manager,worker}.ex`,
  `lib/shot_tx/generation/general_bindings.ex`,
  `lib/shot_tx/util/prop_simplify.ex`,
  `deps/shot_ds/lib/shot_ds/stt/semantics.ex`.
- Higher-order unification primitive: `deps/shot_un/lib/shot_un.ex`.
- Zipperposition and Leo-III traces obtained via SystemOnTPTP web
  service for Examples 6c (Leibniz 2), 13, 14, 20d (Leibniz 1), 22a
  distributivity, and the Injective Cantor Theorem. Representative
  TSTP derivations are excerpted inline above; full responses captured
  to `/tmp/zp_*.{p,txt}` during analysis.
