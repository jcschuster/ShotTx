# SKILL 2026 — Paper Plan

## Submission details

- **Conference:** SKILL 2026 (Studierendenkonferenz Informatik)
- **Format:** Short Paper, 4–6 pages incl. references
- **Template:** GI LNI-Reihe Seminars — https://gi.de/service/publikationen/lni
- **Submission:** https://easychair.org/conferences/?conf=skill2026
- **Language:** English (recommended) or German
- **Co-authors:** Not allowed. Prof. Benzmüller will read a draft (not listed as author).
- **Constraint:** No doctoral candidates; no professor co-authorship.

---

## Scope decision: design paper, not system description

The thesis will be complete and the prover will have evolved before the conference.
Implementation-snapshot claims (benchmark numbers, current gaps, heuristic specifics)
will be outdated by the time of presentation. The paper therefore focuses on
**design rationale and architectural patterns**, not on what ShotTx does on a given day.

**Central question:** *How does higher-order tableau proof search fit into the actor model?*

The contribution is a concrete design that maps tableau proof search onto concurrent
actors; the prover is the existence proof that the design works. The story is positive
(here is how the pieces fit together), not contrastive (here is what's wrong with
sequential approaches).

---

## Framing

**Title:** *A Tableau of Actors: Designing a Concurrent Higher-Order Prover with Equality*

Core claim:
> Tableau proof search decomposes naturally into independent branch computations,
> which makes the actor model a fitting structural match. We present a design that
> realises this fit: branches as immutable snapshots in shared ETS work queues,
> workers as actors stepping rules on those snapshots, an outbox pattern that keeps
> the rule logic pure, and a global ContradictionAgent that closes the proof by
> simultaneous CSP-based unification across all open branches. We demonstrate the
> design with ShotTx, a complete HOL prover in Elixir.

---

## What survives obsolescence (paper anchors here)

- The architectural pattern itself: actors, outbox, immutable snapshots, ETS queues
- Design rationale: why simultaneous closure is forced by concurrency
- Design tradeoffs: lock-free work stealing vs. shared state cost
- The methodology of decomposing a sequential calculus into concurrent components

## What goes stale (avoid as load-bearing claims)

- Benchmark numbers and timings
- Current implementation gaps (G1, G4, G9 — likely closed by submission)
- Heuristic-specific details (unit-set front-loading, current cost weights)
- "We currently do X" present-tense implementation claims

---

## The four-package stack (mention briefly)

| Package   | Role                                                              |
|-----------|-------------------------------------------------------------------|
| ShotDs    | HOL data structures: types, terms, substitutions, semantics, DSL  |
| ShotTo    | NCPO-LNF term ordering (Niederhauser & Middeldorp 2025)           |
| ShotUn    | Higher-order unification: pre-unification, Miller pattern, Huet matching |
| ShotTx    | Concurrent tableau prover (this paper's focus)                    |

Keep each at one sentence. The packages establish scope; the paper is about ShotTx.

---

## Non-standard architectural contributions (the focus)

1. **Simultaneous CSP-based closure** — sequential backtracking is impossible when
   branches live in independent actors. The ContradictionAgent accumulates clashes
   from all open branches and dispatches a single CSP solve. This is the central
   architectural consequence of concurrency.

2. **Outbox pattern** — `Branch.step/4` returns data instructions (`:split`,
   `:instantiate`, `:closed`, …); the Worker interprets them. The proof core is
   pure and side-effect free. Enables independent testing of rule logic.

3. **Immutable branch snapshots + ETS shared state** — each branch is a pure data
   structure; ETS tables hold session-wide state (work queue, idle queue, traces,
   tombs). Workers steal branches lock-free via ordered-set queries.

4. **Branch IDs encode the proof tree** — prefix-check in the tombs table poisons
   descendant branches of a closed ancestor without explicit communication.

The implemented tableau calculus itself (α/β/γ/δ, prim-subst, paramodulation) is
standard. The paper says so plainly — novelty is claimed only for the architecture.

---

## Paper structure (5–6 pages)

| Section | Content | Length |
|---|---|---|
| 1. Introduction | Tableau branches as independent search states; the actor-model fit; the design question | ~0.4p |
| 2. Background | Substantial: HOL/STT, semantic tableau, HOL-specific tableau challenges | **~1.8p** |
| 3. The design pattern | Actor model, outbox pattern, ETS queues, branch ID tree, ContradictionAgent — presented as a reusable pattern | ~1.3p |
| 4. Architectural consequences | Why concurrency forces simultaneous closure; tradeoffs of lock-free work stealing vs. shared state | ~0.6p |
| 5. Instance: ShotTx | Brief sketch; one worked example tracing a proof across multiple workers (qualitative, no timings) | ~0.6p |
| 6. Related work | LEO-III, Satallax, Zipperposition as points of reference for HOL tableau; ask Benzmüller for concurrent ATP prior work | ~0.3p |
| 7. Conclusion | Summary; future work: empirical comparison against sequential backtracking | ~0.2p |

### §2 Background expanded (target ~1.8p)

The substantial background section covers three subsections:

**§2.1 Higher-order logic (Church's STT)** (~0.7p)
- Simple type theory: base types (ι, o), function types τ→σ
- Syntax: variables, constants, λ-abstraction, application; βη-equality
- What makes it "higher-order": quantification over function and predicate variables
- Why this matters for proof search: unification becomes undecidable (Huet 1973),
  instantiation requires primitive substitution (Andrews 1971)
- Brief small worked example (e.g., set extensionality or Cantor)

**§2.2 Semantic tableau** (~0.7p)
- Signed formulas (T:φ, F:φ) or polarity-marked formulas
- The branch-as-conjunction, tableau-as-disjunction reading
- Smullyan's α/β/γ/δ rule schema (with the standard table)
- Closure condition: branch closes on complementary literals
- Soundness and completeness intuition; the systematic nature of the calculus
- One short closed tableau as illustration

**§2.3 HOL tableau and equality** (~0.4p)
- Additional rules HOL requires: primitive substitution, extensionality,
  paramodulation for equality
- The branch-as-unit-of-work observation: each branch is an independent search
  state; closure links branches only through shared substitutions
- This structural independence is what the design in §3 will exploit

---

## 9-day writing plan

| Day | Task |
|---|---|
| 1   | Pick the worked examples: (a) the small HOL example for §2.1, (b) the closed tableau for §2.2, (c) the concurrency-tracing example for §5. Draw the diagrams for (b) and (c). |
| 2   | Write §2 Background in full (it's the largest section) |
| 3   | Write §3 Design pattern |
| 4   | Write §4 Architectural consequences and §5 Instance |
| 5   | Write §1 Introduction, §6 Related work, §7 Conclusion |
| 6   | Send complete draft to Prof. Benzmüller; ask specifically: *"Is there prior work on concurrent or parallel HOL tableau I should cite?"* |
| 7–8 | Revise based on his feedback; check LNI format |
| 9   | Final polish; submit via EasyChair |

---

## Aiming for best paper

Best paper at a student conference is won by clarity, craft and pedagogy, not by
technical depth. Concrete levers, ranked by impact:

**High leverage**

1. **Two excellent diagrams.** Invest a day in TikZ for (a) the architecture diagram
   (Manager / Workers / ContradictionAgent / ETS, message arrows) and (b) the §5
   proof-across-workers trace. These are what reviewers will remember.
2. **§2 as pedagogy, not formality.** Most reviewers will not know HOL or tableau.
   One beautifully typeset closed tableau with a "how to read this" paragraph makes
   the rest of the paper land. Worth more than any extra rule definition.
3. **Abstract and first paragraph.** Spend a full day on these alone. The abstract
   must be readable in 30 seconds by any CS student. The first sentence hooks on the
   actor-model fit, not on HOL.
4. **Frame §3 as a reusable pattern.** Write it so a reader could apply the design
   to other branching search problems (SAT solving, planning, branching model
   checking). Elevates the contribution beyond "one specific prover."
5. **Polish.** Consistent notation, BibTeX entries from DBLP, proper LaTeX math, no
   widows/orphans, no half-empty pages, no broken cross-references. The full final
   day goes here.

**Smaller but real**

- **Prominent artifact link.** Put `hex.pm/packages/shot_*` (and the GitHub URL)
  in the first-page footer or in §5. The four packages are the strongest credibility
  signal in the paper.
- **One non-HOL reader.** Find one CS student outside the ATP world to read for
  clarity. They will catch what Benzmüller skims past.
- **Honest limitations paragraph.** Short, direct list of what the design does not
  do well (no termination guarantees, NCPO-LNF transitivity caveat, no benchmarks
  against sequential implementations). Committees respect this.
- **Memorable talk.** SKILL has talks; best paper considers presentation. Plan one
  striking slide, probably an animated version of the §5 trace.
- **Submit early, not at the deadline.** Early submissions sometimes receive more
  attentive reviews.

**Things to avoid**

- Overclaiming novelty (the calculus is standard; say so).
- Walls of inline formalism without prose anchors.
- Unexplained jargon ("CSP", "OTP", "ETS" all need a line on first use).
- A weak or abrupt conclusion (~0.2p, but make it land — gesture at the design
  pattern's wider applicability).

---

## Key risks

- **Overclaiming.** The architecture is non-standard but the tableau calculus is
  not. Be precise about what is and isn't new. Benzmüller's review is the safety net.
- **Underspecifying.** A pure design paper risks being too abstract. The §5 worked
  example is what grounds the design in concrete proof search behaviour — invest in it.
- **Page count.** 4–6 pages is tight for §3. If it runs long, move the four-package
  stack table and rule list to a footnote.
