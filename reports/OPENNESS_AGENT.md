# OpennessAgent — Design Sketch

Scope: a proposed new component that uses a model finder (Nitpick, via
`isabelle_elixir` or `AtpClient`) to detect that a branch has a satisfying
model, letting the prover abandon that branch — and, in the strongest case,
terminate the session with a global SAT verdict — long before saturation.

Companion to `reports/SUGGESTION_AGENT.md`: SuggestionAgent accelerates
closure of provable branches; OpennessAgent prunes unprovable ones. Together
they are symmetric pruning around the tableau search.

---

## Motivation

The prover currently produces a SAT verdict only through `ContradictionAgent`'s
`csa_or_unknown` path, which fires after a branch has been fully saturated
(empty priority queue, no sleeping γ rules). Two consequences:

1. Branches that are "obviously" open — a small ground model would satisfy
   them — still consume worker time until every α, β, γ, and prim-subst step
   has been exhausted or capped by iterative deepening.
2. Genuinely SAT problems only terminate at the end of the search rather than
   at the first branch that admits a model.

A model finder can answer *is this branch open?* directly. Nitpick's verdict
`Model found` is sound: if it exhibits a finite model of the branch's
formulas, the branch will never close. That's exactly the signal needed to
tomb the branch early.

---

## Where it slots in

```
SessionSupervisor
├─ EtsKeeper                 (adds :openness_verdicts table)
├─ Manager
├─ ContradictionAgent
├─ SuggestionAgent           (proposed — see SUGGESTION_AGENT.md)
├─ OpennessAgent             (proposed, this document)
└─ DynamicSupervisor → Worker × N
```

Sibling to `ContradictionAgent` with the mirror-image job: rather than
searching for a global unifier that closes all branches, it searches for a
model that satisfies *any single* open branch.

New PubSub topic `openness_<session>` — `OpennessAgent` → `Manager` /
`ContradictionAgent` / `SuggestionAgent`. Carries witness verdicts and cache
invalidations.

---

## Per-branch pipeline

1. **Serialise** the branch's formula multiset to a HOL term — literals plus
   reinserted γ-universals plus definitions in scope. Reuse whatever branch
   → term rendering `ShotTx.Proof` already relies on for Mermaid output.
2. **Skolemise** free metavariables. Nitpick needs closed formulas; fresh
   γ-variables become Skolem constants of the appropriate type. Provenance
   from the SuggestionAgent design (see `reports/SUGGESTION_AGENT.md`) carries
   the type and origin information needed to do this cleanly.
3. **Dispatch** to the backend with a bounded search budget: cardinality per
   type, wall-time timeout, at most one call in flight per session.
4. **Interpret** the verdict:
   - `Model M found` → branch is definitively open. Cast
     `{:openness_witness, branch_id, M}` to `Manager` → tomb the branch,
     cancel pending prim-subst work for it, publish on `openness_<session>`
     so `SuggestionAgent` invalidates candidates sourced from that branch.
   - `No model up to bound k` → inconclusive; do not tomb. Optionally
     annotate the ETS entry so the same branch is not re-queried until its
     formula set changes.
   - `Genuine (unbounded) countermodel` → **global SAT verdict**. Cast to
     `Manager`, terminate the session with `{:sat, M}` and skip the current
     saturation-based SAT path entirely.
5. **Cache** the verdict in an ETS `:openness_verdicts` table keyed by a hash
   of the branch's formula multiset, so β-siblings and re-visits are cheap.
   The multiset hash also makes cache invalidation automatic when
   SuggestionAgent applies a hint (see *Interaction* below).

---

## Backend choice

| | `github:jcschuster/AtpClient` | `github:davfuenmayor/isabelle_elixir` |
|---|---|---|
| Backends | Multiple ATPs & model finders | Isabelle only (Nitpick, Nunchaku, sledgehammer) |
| Session model | Per-call process spawn (likely) | Persistent Isabelle session |
| Per-call latency | Higher (JVM startup each call) | Lower once warm |
| Portability | Higher | Lower |
| Right fit for this project | If Vampire/E fallbacks are wanted later | If Nitpick is the sole backend and speed matters |

Recommendation: start with `isabelle_elixir` for the Nitpick fast path
(persistent session amortises JVM cost), behind a small `Backend` behaviour
so `AtpClient` can be added later without rewiring the agent.

```elixir
defmodule ShotTx.Prover.Openness.Backend do
  @callback check(term :: Term.t(), budget :: keyword()) ::
              {:model, model_term()}
              | {:no_model_up_to, non_neg_integer()}
              | {:genuine_countermodel, model_term()}
              | :unknown
              | :timeout
end
```

---

## Design forks

| Fork | Options | Recommendation |
|---|---|---|
| **When to invoke** | Every step / per-β-child / periodic sweep / idle-only | Per-β-child + periodic sweep of the K oldest still-open branches. Skip α/δ-only successors — nothing structurally new. |
| **What to send** | All formulas / ground-only / include sleeping γ | Ground literals + reinserted γ-universals + unfolded defs. **Not** sleeping γ rules — those are pending commitments; including them defeats early detection. |
| **Handling metavariables** | Skolemise vs. existentially close | **Skolemise.** Existential closure asks "does there exist any instantiation making the branch open?"; the CSP is simultaneously searching for one making it closed. Skolemising asks the sharper question: "given current commitments, is this branch open?" |
| **Concurrency** | Fire-and-forget per branch vs. singleton in-flight | Singleton per session with a bounded queue of pending targets. Nitpick calls are expensive; parallelism wastes JVM. |
| **Trust level** | Treat verdict as authoritative vs. as hint | `Model found` is sound and authoritative. `No model` is not sound — treat as inconclusive. Never override `ContradictionAgent`'s closure with an openness verdict; if they disagree, trust closure. |
| **Cost gating** | Always-on vs. `Parameters` flag | Add `openness_check :: :off \| %{interval_ms, timeout_ms, max_cardinality, backend}`. Default `:off` — this is a research feature. |

---

## Interaction with SuggestionAgent

Both agents want the same branch → HOL-term serialisation infrastructure and
the same provenance data. Build both once, reuse.

Interlocks:

- If `OpennessAgent` tombs branch B, `SuggestionAgent` must drop pending
  suggestions whose evidence came from unifiers involving B. A hint derived
  from a false clash is worse than no hint. Handled by subscribing
  `SuggestionAgent` to `openness_<session>`.
- If `SuggestionAgent` applies a hint on branch B, B's formula multiset
  changes and its cached openness verdict is invalidated automatically —
  the multiset-hash key no longer matches.

---

## Risks and open questions

- **Nitpick semantics vs. calculus semantics.** Nitpick's underlying logic
  is HOL as Isabelle understands it; the tableau prover implements STT. If
  the two disagree on, e.g., choice or definite description, an "open"
  verdict from Nitpick may not correspond to an open branch in the calculus.
  Restrict initial deployment to fragments where the two are known to agree
  (first-order + basic HOL, no Hilbert choice).
- **Serialisation fidelity.** Round-tripping branch formulas through
  Isabelle syntax is non-trivial. Bugs here manifest as spurious tombing —
  the prover reports SAT on a genuinely UNSAT problem. Mitigation:
  double-check any `Model found` verdict by re-evaluating the model against
  the branch's formulas inside the Elixir side before acting on it.
- **JVM startup cost.** Even with a persistent Isabelle session, the first
  call has a large cost. Warm the backend at `SessionSupervisor` start when
  `openness_check` is enabled.
- **Cardinality bounds.** Nitpick's default bounds may be too small for the
  branches this prover generates. Expose per-type bounds in the config and
  tune per corpus.
- **Determinism.** Enabling openness detection changes when the session
  terminates. Regression tests must allow either "closed by saturation" or
  "closed by early openness witness" as valid SAT outcomes.
- **Definitions and unfolding.** `Parameters.unfold_defs` affects what the
  branch actually contains. The serialiser must respect the current unfold
  mode so the formula sent to Nitpick matches what the branch is really
  reasoning about.

---

## Thin-slice implementation plan

1. **Serialiser.** Branch multiset → Isabelle/HOL term string. Round-trip
   test on the `examples/` corpus: parse it back, check α-equivalence with
   the source. No agent yet.
2. **Backend behaviour + `isabelle_elixir` adapter.** Implement
   `ShotTx.Prover.Openness.Backend` and one implementation. Exercise it in a
   Livebook with a hand-picked branch that has an obvious 2-element model.
3. **Stub `OpennessAgent`.** GenServer subscribed to `branch_events_<session>`,
   with cache in `:openness_verdicts`, singleton in-flight, no consumer
   downstream — just log verdicts. Verify on saturating examples that
   `Model found` fires before saturation.
4. **Wire consumers.** Cast to `Manager` for tombing / global SAT; publish
   on `openness_<session>` for `SuggestionAgent` cache invalidation.
5. **Gate + defaults.** `Parameters.openness_check` default `:off`. Add an
   A/B pass over the `examples/` corpus at each of the two settings.

Step 1 is the risky one — a bad serialiser produces silent unsoundness under
step 4. Steps 2–3 are mechanical adapter work.

---

## Success criteria

- With `openness_check: :off`, no behavioural change vs. current prover on
  the `examples/` corpus.
- With `openness_check` enabled, previously-saturating examples terminate
  with `{:sat, M}` strictly earlier (wall time and rule count).
- No previously-closing example is spuriously marked SAT.
- The `Model found` verdict passes a second-opinion check on the Elixir side
  (evaluate the model against the branch's formulas before acting).
