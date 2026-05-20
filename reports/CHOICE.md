# Adding Choice to Shot: A Design Study

This document collects findings on what it would mean to add a **choice /
description rule** to the Shot tableau calculus. It is intended as
research notes informing a future calculus extension, not as an
implementation specification.

The motivating problem is the injective Cantor theorem
(`examples/structured_hol_problems.livemd` Ex. 21):

$$\neg\,\exists H:(\iota{\to}o)\to\iota.\;
   \forall P\,Q:\iota{\to}o.\; H\,P = H\,Q \;\supset\; P = Q$$

which the current calculus times out on, in contrast with the surjective
Cantor theorem (Ex. 20), which closes. The literature on automated HOL
(Bishop's TPS examples, Brown's Satallax, Steen's Leo-III) identifies
two principal cures: **iterated primitive substitution** (Option B in our
discussion) and **choice / description** (this document).

## 1. What "choice" means in HOL

Several equivalent or near-equivalent formulations exist; for tableau
automation the most useful is **Hilbert's ε**.

### 1.1 The description operator

For each type $\tau$, introduce a logical constant

$$\varepsilon_\tau : (\tau{\to}o) \to \tau$$

with the schematic axiom

$$\forall P:\tau{\to}o.\;
   (\exists x:\tau.\; P\,x) \;\supset\; P(\varepsilon_\tau\,P) \tag{ε-ax}$$

Read $\varepsilon_\tau\,P$ as "_some_ $x$ of type $\tau$ satisfying
$P$ if one exists; an arbitrary element of $\tau$ otherwise." The
constant is **total**: $\varepsilon_\tau\,P$ is always a well-formed
term, even when no witness exists; (ε-ax) merely constrains its value
when one does.

### 1.2 Relationship to the axiom of choice

Hilbert ε is logically stronger than the standard axiom of choice
(AC$_{\sigma,\tau}$):

$$\forall R:\sigma{\to}\tau{\to}o.\;
   (\forall x.\,\exists y.\, R\,x\,y) \;\supset\;
   \exists f:\sigma{\to}\tau.\,\forall x.\, R\,x\,(f\,x).$$

Given ε we recover AC by setting $f := \lambda x.\;\varepsilon_\tau(R\,x)$.
The converse direction requires extensionality and is given in Andrews
([_An Introduction to Mathematical Logic and Type Theory_](https://link.springer.com/book/10.1007/978-94-015-9934-4),
§5.5). For our purposes the two are interchangeable; ε is preferred
because it produces _terms_ that the prover can match, unify, and
paramodulate against.

### 1.3 Status in Henkin semantics

A Henkin frame in the sense of `theory.md` §1 does **not** automatically
validate (ε-ax). A frame closed under the definable operations of $\Sigma$
may fail to contain a function picking witnesses uniformly. Adding ε
therefore commits the calculus to a strict subclass of Henkin models:
**Henkin frames with choice**.

This is a deliberate semantic strengthening:

  * **Soundness**: every refutation in the extended calculus is sound
    with respect to Henkin-with-choice. It is _also_ sound for plain
    Henkin whenever the refutation does not actually invoke the ε rule.
  * **Completeness**: completeness now targets Henkin-with-choice
    validity. Formulas that are Henkin-valid (without choice) and not
    Henkin-with-choice-refutable are unchanged in status.
  * **Countermodel construction**: `from_countermodel/4` would have to
    produce a Henkin frame in which a choice function exists. The
    saturated branch's $\varepsilon_\tau$ instances supply candidates,
    but verifying their consistency adds work.

Most ATPs target Henkin-with-choice in practice (Leo-II, Leo-III,
Satallax, Zipperposition). Shot's `theory.md` §1 is silent on choice,
which is appropriate for a choice-free calculus. Adopting ε would
require an additional sentence there and a corresponding revision of
§6.

## 2. How choice solves the injective Cantor theorem

The point of choice for our problem is that it makes the witness term
for the diagonal **discoverable by depth-1 primitive substitution**,
rather than requiring the depth-3 nested logical structure that pure
Andrews-style primsub demands.

### 2.1 The left-inverse construction

After Skolemising the negated theorem we have

$$h : (\iota{\to}o) \to \iota \qquad\text{and}\qquad
   \forall P\,Q.\; h\,P = h\,Q \;\supset\; P = Q.\quad(\mathit{Inj})$$

Define

$$h^{-1} \;:=\; \lambda y:\iota.\;
   \varepsilon_{\iota\to o}\,(\lambda P:\iota{\to}o.\; h\,P = y).$$

For any $A : \iota{\to}o$, applying $h^{-1}$ at $h\,A$ yields a preimage:

  1. $\exists P.\; h\,P = h\,A$ holds (with $P := A$).
  2. By (ε-ax), $h(h^{-1}(h\,A)) = h\,A$.
  3. By ($\mathit{Inj}$) at $P := h^{-1}(h\,A),\;Q := A$, we conclude
     $h^{-1}(h\,A) = A$.

So $h^{-1}$ is a **left inverse** of $h$ wherever $h$ is injective. The
term itself is constructed independently of injectivity; injectivity is
what makes it useful.

### 2.2 The depth-1 diagonal

Take

$$A \;:=\; \lambda x:\iota.\; \neg\,(h^{-1}\,x)(x).$$

This term has structure

  * depth 1: head $\neg$
  * inner: $(h^{-1}\,x)(x)$ — rigid head $h^{-1}$, two applications of $x$

Generating it by primsub requires only the depth-1 base binding
$\lambda \bar y.\; \neg(H\,\bar y)$ with $H : \iota \to o$. The hole $H$
is bound by pre-unification against the (now-rigid) $h^{-1}$ on the
branch, producing $H \;\mapsto\; \lambda a.\;(h^{-1}\,a)(a)$ via one
imitation step on $h^{-1}$ and one projection of $a$. This is well
within `unification_depth: 8`.

Contrast with the choice-free diagonal
$\lambda x.\;\exists B.\; h\,B = x \land \neg B\,x$, which needs the
prover to **guess** the conjunction-inside-Σ structure (three nested
levels of logical content) before unification has anything to work with.

### 2.3 The refutation

Once $A$ is on the branch:

  * Apply $A$ to $h\,A$, unfolding the definition:
    $A(h\,A) \;\Leftrightarrow\; \neg(h^{-1}(h\,A))(h\,A)$.
  * Section 2.1 gives $h^{-1}(h\,A) = A$. Paramodulation rewrites
    $(h^{-1}(h\,A))(h\,A)$ to $A(h\,A)$.
  * Result: $A(h\,A) \;\Leftrightarrow\; \neg A(h\,A)$, closed by
    Boolean extensionality.

The proof is essentially Russell's paradox restricted to the range of
$h$. In a textbook it is one paragraph; for the prover it would be
roughly: γ on $\mathit{Inj}$ at two specific terms, one δ via ε, two
paramodulations, one ≡-decomposition.

### 2.4 What choice does _not_ buy

Discovery is still nontrivial:

  * The prover must instantiate $\mathit{Inj}$ at $P := h^{-1}(h\,A)$,
    not at fresh free variables. There is no rigid term forcing this
    binding through pre-unification — the connection
    $h^{-1}(h\,A) = A$ has to be _derived_, not _matched_.
  * Without paramodulation, the equation $h^{-1}(h\,A) = A$ is just
    another fact on the branch; with paramodulation (Shot has it) it
    becomes a rewrite rule that propagates aggressively, which is
    exactly what makes this strategy effective.
  * The diagonal $A$ itself still has to be _proposed_ by primsub. With
    $h^{-1}$ available, depth-1 suffices, but the prover must still try
    the $\neg$-headed binding.

Leo-III sharpens this by **detecting the injectivity pattern**
$\forall x\,y.\; f\,x = f\,y \supset x = y$ syntactically and emitting
$f^{-1}$ as a dedicated Skolem with its defining equation
$\forall x.\; f^{-1}(f\,x) = x$. This is special-purpose machinery on
top of ε. It is the source of Leo-III's ~1.5 s solve on this problem
(Steen & Benzmüller, [_The Higher-Order Prover Leo-III_](https://arxiv.org/abs/1802.02732),
IJCAR 2018, and [JAR 2021](https://arxiv.org/abs/1907.11501)). Whether
to include this pattern detector is an independent design choice from
adopting ε.

## 3. Tableau rule formulations

Three styles, in order of increasing aggressiveness.

### 3.1 δ-as-ε (least invasive)

Replace the current δ-rule

$$\frac{\exists x:\tau.\;\Phi(x)}
       {\Phi(\mathsf{sk}(\bar z))}$$

with

$$\frac{\exists x:\tau.\;\Phi(x)}
       {\Phi(\varepsilon_\tau\,\lambda x.\Phi(x))}\qquad(\delta_\varepsilon)$$

The right-hand side is still a closed term — it just _is_ the ε-term
rather than an opaque Skolem. Downstream effects:

  * Two δ-applications of the **same** existential predicate produce
    the **same** ε-term (modulo αβη), enabling automatic merging.
  * The ε-term is available for unification, paramodulation, and
    further primsub against the rest of the branch.
  * Existentials whose witness term plays a structural role (as in the
    left-inverse construction) become exploitable.

This is the variant Backes & Brown use in
[_Analytic Tableaux for HOL with Choice_](https://link.springer.com/article/10.1007/s10817-011-9233-2).
It is calculus-conservative (the bound on derivable formulas grows from
Henkin to Henkin-with-choice; the search space changes very little).

### 3.2 Predicate-triggered ε-intro

When a term $e : \tau{\to}o$ appears on the branch (not necessarily
wrapped in an explicit existential), enqueue

$$(\exists x:\tau.\; e\,x) \;\supset\; e(\varepsilon_\tau\,e).$$

Stronger than §3.1 because it makes ε-terms available for predicates
the calculus has not yet derived an explicit existential about. Cost:
explodes the branch with one ε-conditional per predicate term.
Fairness needs a "fire once per predicate" guard.

### 3.3 AC schema as an axiom

Inject the AC$_{\sigma,\tau}$ schema globally for each pair of types in
the universe and let γ handle instantiation. Simplest implementation
(no calculus extension at all) but the γ-explosion on a schema with two
quantified types of arbitrary type is severe; this is rarely the
practical choice.

### 3.4 Recommended target

For Shot the natural target is §3.1 — repurposing δ. The existing
infrastructure (Skolem generation in `Rules.classify_formula/1`, history
recording, paramodulation) all carries over with minimal disruption.

## 4. Concrete touchpoints in the codebase

The estimate is **150–250 LOC across 4–6 files**, comparable to
primsub-under-primsub. The changes are wider but shallower.

### 4.1 Theory

  * **`theory.md` §1** — add ε to the signature
    $\Sigma$. Note that the semantics is now Henkin-with-choice.
  * **`theory.md` §2** — new rule statement for δ$_\varepsilon$.
  * **`theory.md` §6** — soundness/completeness statements gain "with
    choice"; (S2) is rewritten in terms of ε-terms; the model
    construction (§6.3) must produce a choice function in the
    constructed Henkin frame. Andrews §5.6 has the standard recipe.

### 4.2 Signature constants

  * **`ShotDs.Hol.Definitions`** (in the upstream `shot_ds` dep) — add
    `eps_term/1` analogous to `forall_term/1`, `exists_term/1`. The
    ε constants are polymorphic per τ, just like Π and Σ.

If modifying `shot_ds` is undesirable, an alternative is to introduce
ε as a tagged Skolem constant (`Declaration` of a special kind) that
the prover recognizes internally without registering it in the formal
signature. Cleaner for separation of concerns, but loses some
ergonomics in pretty-printing.

### 4.3 Rules

  * **`lib/shot_tx/prover/rules.ex`** —
    * Modify the δ classification (`{:delta, app(pred, sk_term(...))}`)
      to produce `{:delta, app(pred, eps_term(pred))}`. The ε-term
      itself becomes the Skolem expression.
    * If §3.2 is also adopted: a new `:choice` rule type for
      predicate-triggered ε-intro, with a cost between α and γ
      (perhaps 4–6 — cheaper than primsub but more expensive than
      decomposition).

### 4.4 Branch ingestion

  * **`lib/shot_tx/prover/branch.ex`** —
    * If two δ applications of αβη-equal predicates produce the same
      ε-term, congruence closure / `term_ids` already merges them.
      Worth verifying that this kicks in for the cases we care about.
    * `register_new_types/2` already extends the type universe when
      Skolems introduce fresh types; ε-terms behave the same, so this
      should work unchanged.
    * If §3.2 is adopted: a new firing path in `ingest_formula/3` that
      detects predicate terms and enqueues ε-conditionals.

### 4.5 Type universe & primsub

  * **`lib/shot_tx/generation/type_universe.ex`** — no changes; ε is
    just another polymorphic constant.
  * **`lib/shot_tx/generation/general_bindings.ex`** — if ε-terms are
    to participate as head symbols in primsub bindings (e.g.,
    $\lambda\bar y.\;(\varepsilon_\tau (H\,\bar y))$ as a primsub
    instantiation), add a `flat_choice_heads/2` analogous to
    `flat_quantifier_heads/2`. Probably not needed for injective
    Cantor specifically.

### 4.6 Proof tracing

  * **`lib/shot_tx/proof.ex`** —
    * `concrete_delta/1` recognises the ε form and prints `ε` instead
      of `∃`.
    * `rule_symbol/1` adds `:choice → "ε"` if §3.2 is adopted.
    * `auto_aliases/1` decides whether to give ε-terms their own
      naming pool (e.g., `ε₁, ε₂, …`) or fold them into the constants
      pool. Probably the latter for compactness.

## 5. Comparison with primsub-under-primsub (Option B)

|                          | **B: primsub-under-primsub**                                       | **C: choice / ε**                                                |
| ------------------------ | ------------------------------------------------------------------ | ---------------------------------------------------------------- |
| Semantics                | Plain Henkin (unchanged)                                           | Henkin + choice (strictly stronger)                              |
| Injective Cantor proof   | Depth-3 binding generation, primsubs on holes                      | Depth-1 binding + left inverse via paramodulation                |
| Soundness obligation     | None new                                                           | Choice-validity in the model constructor                         |
| Theorems unlocked        | Cantor-like problems requiring deeply nested λ-witnesses           | Everything in B _plus_ unique-description, Russell variants, AC  |
| Search-space cost        | Exponential in primsub depth (every fresh hole gets all shapes)    | Linear in #existentials (one ε-term each)                        |
| Proof readability        | Three nested primsubs; trace difficult to follow                   | Synthesises h⁻¹; trace closer to a textbook proof                |
| Code surface             | ~100–200 LOC, deep changes in `branch.ex`/`rules.ex`               | ~150–250 LOC, wide changes across 4–6 files                      |
| Calculus identity        | Preserves "principled, choice-free Henkin tableau"                 | Aligns with Leo-III/Satallax tradition                           |
| Combines with the other? | Yes, B + C is well-founded (Leo-III runs both)                     | Yes                                                              |

The two are complementary, not exclusive. Leo-III ships both. The
question is which to prioritise.

## 6. A note on the user's "don't hard-code injectivity" concern

A few possible objections to choice are worth distinguishing:

  1. **"I don't want a Vampire fallback that recognises injectivity by
     pattern."** This refers to Leo-III's syntactic injectivity
     detector (§2.4). It is independent of ε. You can have ε without
     the pattern detector; you simply lose the dramatic speedup on
     injective Cantor specifically.

  2. **"I don't want to leave Henkin semantics."** Adopting ε does
     leave plain Henkin. If staying in choice-free Henkin is part of
     the prover's identity, this is a real cost. It is not a soundness
     concern (refutations remain logically valid in any reasonable
     foundation), but it does change what the prover _means_.

  3. **"I want general rules, not problem-specific tricks."** Hilbert
     ε is fully general. It is one rule, applied uniformly to every
     existential or every predicate. It is the opposite of
     problem-specific.

The user's stated preference (Option B in the prior turn) addresses
(1) and (2) cleanly: primsub-under-primsub is general, choice-free,
and stays in Henkin. Choice would be the right answer to a different
question — "what is the smallest extension that makes a broad class
of HOL theorems (not just injective Cantor) tractable for this
prover?"

## 7. Recommendation

Three configurations are coherent end states:

  * **Pure Henkin**: implement Option B (primsub-under-primsub) only.
    Accept that some problems requiring choice-style witnesses remain
    out of reach.

  * **Henkin + ε via δ$_\varepsilon$ (§3.1) only**: minimal-impact
    semantic strengthening; gain access to ε-terms throughout; do not
    add the injectivity-detection special case. Injective Cantor
    becomes _possible_ but probably not fast.

  * **Henkin + ε + left-inverse synthesis**: the Leo-III configuration.
    Fast on injective Cantor and similar; broad applicability;
    largest semantic departure from the current `theory.md`.

The two-step landing — Option B first, then revisit whether ε is
needed for problems Option B leaves on the table — keeps the
choice-free identity intact while preserving the option. If, after B,
the prover still misses important targets (and these turn out to be
about choice-style witnesses rather than depth-3 logical structure),
that is the moment to revisit §3.1.

## References

  * [Andrews et al., _TPS_, JAR](https://link.springer.com/article/10.1007/BF00252180)
  * [Andrews, _An Introduction to Mathematical Logic and Type Theory_](https://link.springer.com/book/10.1007/978-94-015-9934-4) — ch. 5 for ε.
  * [Bishop, _Solving for Set Variables_, CADE-17](https://link.springer.com/chapter/10.1007/3-540-45620-1_33)
  * [Backes & Brown, _Analytic Tableaux for HOL with Choice_, JAR](https://link.springer.com/article/10.1007/s10817-011-9233-2)
  * [Brown, _Reducing HO Theorem Proving to a Sequence of SAT Problems_, JAR](https://link.springer.com/article/10.1007/s10817-013-9283-8)
  * [Steen & Benzmüller, _The Higher-Order Prover Leo-III_, IJCAR 2018](https://arxiv.org/abs/1802.02732)
  * [Steen & Benzmüller, _Extensional Higher-Order Paramodulation in Leo-III_, JAR](https://arxiv.org/abs/1907.11501)
  * [Steen, _Extensional Paramodulation for HOL_ (PhD thesis)](https://orbilu.uni.lu/bitstream/10993/40251/1/thesis-steen.pdf)
  * [Bentkamp et al., _Superposition with Lambdas_, JAR](https://matryoshka-project.github.io/pubs/lamsup_article.pdf)
