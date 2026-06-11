# ShotTx Calculus

ShotTx is a **tableau prover** for Church Simple Type Theory (STT). The core
calculus is the standard α/β/γ/δ refutation tableau; everything else is a
specialised rule, a pre-processing step, or a side-channel that supports the
core. This document catalogues every rule that fires on a branch, names the
design decisions that go beyond a textbook presentation, and points at the code
that implements each piece.

The rule dispatcher lives in `lib/shot_tx/prover/rules.ex` (`classify_formula/1`
+ `classify_neg_formula/1`); rule effects live in
`lib/shot_tx/prover/branch.ex` (`apply_rule/6`).

## 1. Trivial closure / acceptance

| Rule              | When it fires                                       | Effect                  |
| ----------------- | --------------------------------------------------- | ----------------------- |
| `:contradiction`  | `⊥`, `¬⊤`, `¬(a = a)`, or a literal whose negation is already on the branch | Close the branch (`⊥`). |
| `:tautology`      | `⊤`, `¬⊥`, `a = a`                                  | Drop the formula.       |

Pending closure is detected during `insert_formula/4`: if `¬f` already sits in
`branch.term_ids`, the branch is flagged with `:pending_closure` and the next
`step/4` produces `{:closed, …}` without running another rule.

## 2. α (linear) and β (branching)

### α-rules — `classify_formula/1`

| Trigger             | Produced                                       |
| ------------------- | ---------------------------------------------- |
| `p ∧ q`             | `p`, `q`                                       |
| `¬¬p`               | `p`                                            |
| `¬(p ∨ q)`          | `¬p`, `¬q`                                     |
| `¬(p ⊃ q)`          | `p`, `¬q`                                      |
| `s =ₒ t` (type `o`) | `s ≡ t` (boolean equality unfolds to equiv.)   |
| `s =_τ→σ t`         | `extensional_equality(τ→σ)(s, t)` (α-decomp.)  |
| `s =_τ t`           | `leibniz_equality(τ)(s, t)` (α-decomp.)        |

### β-rules

| Trigger      | Branches                  |
| ------------ | ------------------------- |
| `p ∨ q`      | `p` / `q`                 |
| `p ⊃ q`      | `¬p` / `q`                |
| `p ≡ q`      | `p ∧ q` / `¬q ∧ ¬p`       |
| `¬(p ∧ q)`   | `¬p` / `¬q`               |
| `¬(p ≡ q)`   | `¬p ∧ q` / `¬q ∧ p`       |

**Design decision — β-variant.** Controlled by `params.beta_variant` (default
`true`). When set, the *right* β-branch additionally receives `¬B₁` as a free
assumption (`branch.ex` `apply_rule({:beta, _}, …)`). This is the standard
β-variant: it turns disjunction into a complete case split (left has `B₁`, right
has `¬B₁ ∧ B₂`) and is recorded as a separate `:beta_variant` history entry so
the proof renderer can show it. It typically halves the search on β-heavy
goals.

## 3. γ (universal instantiation)

Two flavours:

* **`{:gamma, recipe, type, prev}`** — the general case. The rule is
  *non-consuming*: after firing once with a fresh variable
  `app(recipe, X_fresh)` it is requeued with `prev+1`. The iterative-deepening
  Manager (`lib/shot_tx/prover/manager.ex`) bumps `gamma_limit`/`prim_limit` in
  lockstep when every worker is `:idle`, at which point sleeping gamma rules
  are woken up (`Branch.wake_up/2`).
* **`{:gamma_finite, recipe, type}`** — when the quantifier type is pure-`o`
  (e.g. `∀X:$o`, `∀F:$o→$o`), the domain is finite. The rule fires *once*,
  enumerating every closed term of that type via `ShotTx.Generation.gen_o/1`.
  No reinsertion, no deepening.

**Design decision — instance-based first firing.** When a γ-rule has just
fired for the first time (`prev == 0`) and `instance_based_gamma` is `true`,
every previously-known closed subterm of the matching type
(`branch.ground_terms[type]`, maintained by `register_ground_subterms/3`) is
also fed through the recipe alongside the fresh variable. Ground terms
discovered later are not eagerly re-instantiated; they are picked up the
next time the same γ-rule fires under iterative deepening. This avoids the
self-feeding cascade that occurs when the recipe's body produces fresh
ground subterms of its own input type (e.g. `∀Z:ι. sk0(Z) = sk1(Z)` with
`sk0, sk1 : ι→ι`).

## 4. δ (Skolemisation)

`{:delta, sk_term_id}` replaces an existential `∃X:τ. ϕ` (or `¬∀X:τ. ϕ`) with
`ϕ[sk(fv)/X]`, where `sk` is a fresh constant of type
`τ ← types(free_vars(ϕ))`. Skolemisation is **outer-most** and **eager**: it
runs immediately on the popped formula.

## 5. Negative extensionality (one-step `neg_ext`)

Standard tableau calculi handle `¬(f = g)` at arrow type by unfolding the
extensional-equality definition, then resolving the resulting `∃c. f(c) ≠ g(c)`
via γ + δ. That route requires two rule firings and an instantiation step.

`classify_neg_formula/1` short-circuits the common case directly:

```
¬(f =_{τ→σ} g)   with  f, g closed
→  ¬(f @ c = g @ c)        c = sk_term({}, head_type)   [α-rule, one step]
```

When either side has free variables the fallback (unfold the definition, then
γ/δ) is used. This is the one-step "negative extensionality" rule found in
modern HO provers.

## 6. Primitive substitution `{:prim_subst, recipe, type, depth, progress}`

When a γ-rule fires on a `pred: …→o` variable, prim-subst supplies *general
bindings* that fix the head connective of a sub-formula and leave the rest as
fresh holes. Heads come from `ShotTx.Generation.GeneralBindings`:

* `base_heads/2` — propositional heads (`⊤`, `⊥`, `¬`, `∨`, `∧`, `⊃`, `≡`,
  composed at higher depths).
* `unit_set_heads/2` — `λY. Y = c` for each branch constant `c` of matching
  type.
* `polymorphic_heads/3` — type-driven heads constructed from the branch's
  current type universe.

**Design decision — unit-set front-loading.** On the very first prim-subst
firing of a branch, if the branch already has constants in its term universe,
*all* unit-set bindings are emitted in one batch (no batch cap, no base/poly
heads). This front-loads the binding pattern that closes Leibniz-style goals
(e.g. `λY. Y = a`) where the propositional heads are useless. The rule is then
requeued with `progress.covered_constants` updated, and subsequent firings
follow the regular batched path.

**Design decision — scheduling.** `params.prim_subst_after` (default `0`)
controls how many γ instantiations must precede a prim-subst on a given recipe.
The cost function (`Rules.rule_cost/1`) keeps prim-subst expensive
(`20 + 5·depth + 2·base_offset`) so cheaper rules drain first, but the unit-set
shortcut makes the *first* unit-set pass effectively free in priority terms.

**Iterative deepening.** When a `prim_subst` rule exhausts its heads at the
current depth, it either reinserts itself at `depth+1` (if `next ≤ prim_limit`)
or parks itself in `sleeping_gamma_rules` to wait for the Manager to bump
`prim_limit`.

## 7. Atomic literals + paramodulation

`{:atomic, term_id}` is the catch-all for literals. The atom is registered in
`branch.literals` and:

1. **Local clash detection** — checks `branch.literals` for an identical
   negation (ground closure) or a unifiable negation (via `ShotUn.unify/2`
   up to `params.unification_depth`). Unifiable clashes are forwarded to the
   `ContradictionAgent` for global closure consideration.
2. **Paramodulation** — the new literal is rewritten against every known
   equation in `branch.equations` (see §8).
3. **Unfold-on-demand** — if the literal's head is a definition known to the
   branch (`branch.defs`), the unfolded form is inserted in its place. Lazy
   unfolding is the default (`params.unfold_defs = :lazy`); `:eager` unfolds
   inside every `insert_formula/4` instead.

### Atom sub-classifications

`classify_atom/1` distinguishes three sub-cases:

* **`:rename`** — when an atom contains a complex closed subterm of arrow
  type and free-variable shape that prevents direct closure, a fresh constant
  `c` is introduced; the literal becomes `lit[c/subterm]` and an equation
  `c = subterm` is emitted. This is a *naming* step that lets paramodulation
  later replace `c` back, or extensional reasoning kick in.
* **`:instantiate`** — when an atom's argument is a primitive boolean-typed
  constant variable (a `:co` head with a reference name, of pure-`o` type),
  the rule branches by `ShotTx.Generation.gen_o/1`, enumerating closed
  inhabitants of the type. *Dual instantiation*: the original literal is also
  kept on the branch alongside the instantiated children, so paramodulation
  can still use it.
* **`:atomic`** — the fallback for irreducible literals.

## 8. Paramodulation (equational rewriting)

`lib/shot_tx/prover/paramodulation.ex`. Equations `s = t` enter
`branch.equations` via `ingest_formula/3`, oriented by `orient_pair/3` (LHS is
the side that *contains* the other, breaking ties with `ShotTx.Prover.TermOrder`).
Two flavours run side by side:

* **Structural** (`paramodulants/2`) — replace every memoised occurrence of
  `s` by `t` in the literal. Uses term-id identity, so no matching.
* **Unifying** (`unifying_paramodulants/3`) — for every subterm `u` of the
  literal and every equation LHS `s`, call `ShotUn.unify({s, u}, depth)` and
  rewrite under the resulting substitution. This is what gives ShotTx the
  superposition-style reach for HO transitivity/congruence goals.

Both fire in two situations: (a) a new equation arrives → rewrite every
existing literal; (b) a new literal arrives → rewrite it against all existing
equations. No ordering, no fairness — just two streams of paramodulants pushed
through `insert_formula/4`.

**Limitations.** Paramodulation only fires when the equation LHS appears as
a memoised sub-term (or unifies with one). It does *not* rewrite in head
position (the head of an applied term is a `Declaration`, not a separate
term-id node). The α-decomposition of equalities into extensional/Leibniz
forms remains the complete fallback for HO equality reasoning that
paramodulation cannot reach.

## 9. Lambda-lifting (pre-processing α-rule)

`lib/shot_tx/prover/lambda_lift.ex`. Runs once per user formula at branch
creation (`Branch.new/4`). For every *closed* `λ`-subterm that occurs as an
argument of a non-logical rigid constant, the abstraction is replaced by a
fresh constant `c` of the same arrow type, and an equality axiom
`c =_τ λx̄. body` is emitted as an ordinary branch formula.

Recorded in `branch.history` as `{original_formula, :lambda_lift, [lifted, …axioms]}`,
rendered as `λ↑` in proof output.

**Design decision — axiom, not definition.** The lift equation is *not* added
to `branch.defs`. `Semantics.unfold_defs!` cannot undo it, so the lift survives
into paramodulation and equality decomposition. This is the design choice that
keeps lambda-lifting a tableau α-rule rather than a superposition-style
preprocessing pass.

**Design decision — skip η-expansions.** Terms in ShotDs are stored in
βη-normal form, so a constant like `f: τ→τ` always appears as `λx. f(x)`.
Lifting these is pointless; `eta_expansion?/1` detects them by checking that
the body's arguments are exactly the binder's de Bruijn variables in order,
and skips them.

## 10. Propositional simplification (BDD oracle)

`lib/shot_tx/util/prop_simplify.ex`. Before classifying a popped formula,
`simplify_formula/4` runs `PropSimplify.simplify/2` (mode controlled by
`params.simplification`: `:none`, `:shallow`, `:deep`). The simplifier
reduces purely propositional structure via Elixir's lazy-BDD machinery
(`Module.Types.Descr`). Non-propositional subterms are opaque leaves keyed
on term-id.

If simplification changes the term, the simplified form is requeued (with its
own classification) and a `:bdd_oracle` (`bdd⊢`) history entry is recorded.

## 11. Reading the proof tree

Every rule firing appends a triple `{source, rule, [produced]}` to
`branch.history` (newest first). `ShotTx.Proof.from_refutation/1` reads the ETS
trace dump and reconstructs the proof tree. Rule symbols rendered by
`rule_symbol/1` (`lib/shot_tx/proof.ex`):

| Rule              | Symbol     | Rule                | Symbol      |
| ----------------- | ---------- | ------------------- | ----------- |
| α-shape (generic) | `α`        | β-variant assumpt.  | `β-var`     |
| β (generic)       | `β`        | rename              | `ren`       |
| γ / γ-finite      | `γ` / `γ_fin` | instantiate      | `inst`      |
| δ                 | `δ`        | unfold (def)        | `unfold`    |
| ∧ / ∨ / ⊃ / ≡     | `∧` `∨` `⊃` `≡` | paramodulation | `para`      |
| ¬-variants        | `¬∧` `¬∨` `¬⊃` `¬≡` | prim-subst | `π`         |
| `=ₒ` / `=ext` / `=leib` | `=ₒ` `=ext` `=leib` | BDD oracle | `bdd⊢` |
| `¬=ₒ` / `¬=ext` / `¬=leib` | `¬=ₒ` `¬=ext` `¬=leib` | lambda-lift | `λ↑` |
| atomic            | `atomic`   | closure             | `⊥`         |

## Cheat sheet: where does this rule live?

```
classify (Rules.classify_formula/1)
        │
        ▼
   apply_rule (Branch.apply_rule/6)
        │
        ├─ :contradiction → close branch
        ├─ :tautology     → drop
        ├─ :alpha         → insert N formulas, continue
        ├─ :beta          → split into two branches (optionally with β-variant)
        ├─ :gamma         → fresh var instance + requeue with prev+1
        │                   (first firing: register recipe, instantiate all known
        │                    closed subterms; then optionally schedule prim_subst)
        ├─ :gamma_finite  → exhaustive enumeration on pure-o type
        ├─ :delta         → skolemise outermost
        ├─ :prim_subst    → batch of general bindings (first pass: front-load
        │                   unit-set heads; otherwise base+unit+poly), requeue
        │                   or deepen
        ├─ :rename        → introduce naming constant + equation
        ├─ :instantiate   → branch by gen_o, dual-keep original literal
        └─ :atomic        → register literal, local clash check, paramodulate
                            against all known equations, unfold-on-demand
```

Pre-processing (per user formula, in `Branch.new/4`):

```
lambda-lift  →  recipe constants + axioms  →  enqueue
```

Side-channels (per branch step):

```
register_ground_subterms  →  re-fire registered γ recipes on new closed subterms
ContradictionAgent        →  collects local clashes, asks ShotUn for a global
                             unifier compatible across all open branches
PropSimplify              →  BDD-shaped simplification before classification
```
