# SuggestionAgent — Design Sketch

Scope: a proposed new component that turns unifier evidence discovered during
closure attempts into targeted instantiation hints for the γ- and prim-subst
machinery. The intent is to replace speculative backtracking through
substitution options with evidence-driven instantiation.

---

## Motivation

The prover currently discovers substitutions in two disjoint places:

1. **γ / prim-subst enumeration** (`lib/shot_tx/prover/branch.ex:316–620`)
   generates candidate instantiations of universal quantifiers by minting fresh
   variables and, for prim-subst, iteratively deepening general bindings. This
   is speculative — every candidate is a guess, most guesses lead to open
   branches, and iterative deepening is the fallback when guesses fail.

2. **Closure attempts** in `ContradictionAgent`
   (`lib/shot_tx/prover/contradiction_agent.ex:407–424`) call `shot_un` to find
   a unifier across clashing literal pairs. When `find_global_closure/2`
   succeeds, the resulting substitution `σ` **already tells us what the "right"
   instantiations were** — but today `σ` is only used to close the proof, then
   discarded.

The load-bearing observation: a substitution `X ↦ t` where `X` was born from a
γ-rule on `∀y. φ(y)` is empirical evidence that `t` is the instantiation the
proof needed. If we propagate that back to the γ-rule's source formula, we can
skip the enumeration that would otherwise have to rediscover it — and, more
importantly, we can propagate it to *sibling branches* where the same
quantifier is in force but the CSP hasn't yet closed.

---

## Prerequisites — variable provenance

Nothing today records where a fresh γ-variable came from. In
`branch.ex:337` a fresh var is minted with `TF.make_fresh_var_term(type)`
inside the γ-rule; `recipe` (the `λx.φ(x)` closure) and the originating
`source` formula id are in scope but never persisted per-variable. The same
gap exists in the prim-subst path (`branch.ex:399–485`).

The minimum data required:

```elixir
%Provenance{
  recipe: Term.term_id(),        # the ∀-formula's body abstraction
  source: Term.term_id(),        # the ∀-formula's id in the branch
  birth_branch: BranchId.t(),    # LCA scope for any suggestion
  gamma_iteration: non_neg_integer(),
  origin: :gamma | :prim_subst
}
```

Stored in a new ETS table `:provenance` owned by `EtsKeeper`, keyed by fresh
var id. Written at exactly two sites (the γ fresh-var mint and the prim-subst
enumerator). This is the load-bearing piece — without it, a unifier
`{X ↦ t}` cannot be traced back to any quantifier.

---

## Component design

New GenServer sibling to `ContradictionAgent` under `SessionSupervisor`:

```
SessionSupervisor
├─ EtsKeeper                 (adds :provenance table)
├─ Manager
├─ ContradictionAgent        (publishes unifier candidates, not only global closures)
├─ SuggestionAgent           (new)
└─ DynamicSupervisor → Worker × N
```

New PubSub topics under `ShotTx.Prover.PubSub`:

- `unifier_candidates_<session>` — `ContradictionAgent` → `SuggestionAgent`.
  Carries every successful *pair-level* unifier, not only global CSP
  solutions.
- `suggestions_<session>` — `SuggestionAgent` → `Worker`s. Carries scored,
  scoped instantiation hints.

---

## Lifecycle of a suggestion

1. **Trigger.** `ContradictionAgent` already invokes `shot_un` inside
   `find_global_closure/2` (`contradiction_agent.ex:407`). Widen its output so
   every successful *individual* pair unifier is published to
   `unifier_candidates_<session>`. Today, a substitution that would close 3 of
   4 branches is thrown away; this change turns it into evidence.

2. **Derive.** `SuggestionAgent` walks each incoming σ. For every `X ↦ t`:
   - look up `X` in `:provenance` → `(recipe, source, birth_branch)`
   - compose bindings so `t` is fully grounded w.r.t. the rest of σ
     (`X ↦ f(Y), Y ↦ a` collapses to `X ↦ f(a)`)
   - discard the suggestion if the composed term still contains fresh
     variables whose provenance is outside the current branch's scope

3. **Score & dedupe.** Rank by
   - number of clash pairs the σ closed simultaneously,
   - term size / prim-subst depth-equivalent (cheaper first),
   - evidence count (how often the same `(recipe, term)` pair has been seen).
   Keep bounded top-K per recipe (K ≈ 8).

4. **Deliver.** Broadcast
   `{:suggestion, %Suggestion{recipe, source, term, birth_branch, score}}`
   on `suggestions_<session>`.

5. **Apply.** `Worker.handle_info({:suggestion, s}, state)`:
   - drop if the current branch is not a descendant of `s.birth_branch`
   - drop if the branch is tombed
   - drop if a per-branch counter of suggestion-derived instantiations for
     `s.recipe` has hit a bound (see *Risks*)
   - otherwise splice a synthetic `:instantiate` (using `s.term`) into the
     queue at high priority. The existing `apply_rule({:instantiate, …}, …)`
     path in `branch.ex:296` handles it — no new rule semantics are
     introduced.

---

## Design forks

| Fork | Options | Recommendation |
|---|---|---|
| **Signal source** | (a) only full CSP closures, (b) also partial pair unifiers, (c) also failed near-closures | (b). (a) gives nothing new — the proof already closes; (c) is noisy. |
| **Aggressiveness** | Hint-only (reorder queue) vs. replace prim-subst enumeration for the source formula | **Hint-only.** Keep enumeration running as a fallback; suggestions race ahead. Preserves completeness. |
| **Depth policy** | Respect current `prim_limit` vs. bypass it | **Bypass.** The whole point is that a discovered `t` might exceed the current limit; blocking it defeats the mechanism. Iterative deepening still ticks so a bad suggestion cannot stall. |
| **Cross-branch replay** | Origin branch only vs. all descendants of `birth_branch` | **All descendants.** That is exactly the LCA scope where the ∀ was in force. |
| **Interaction with `instance_based_gamma`** | Fold suggested terms into the IBG ground-terms cap vs. keep as distinct channel | **Distinct channel.** IBG is a static enumeration heuristic; suggestions are dynamic evidence. Conflating them muddies both. |
| **Suggestion lifetime** | Per session vs. TTL vs. per-round | **Per session, bounded top-K per recipe.** Tombing handles stale branches naturally. |

---

## Risks and open questions

- **`shot_un` API surface.** `find_global_closure/2` currently returns
  `{:ok, solution}` or nothing. The design needs it to expose individual
  pair-level unifiers, or at least per-branch partial solutions. This is a
  change in an external dependency — worth confirming feasible before
  committing to the design.

- **Higher-order unifiers.** For HOL, the term bound to `X` may itself contain
  fresh variables. The composition step in *Derive* must fully ground the
  suggested term before broadcast; otherwise the suggestion has to travel
  with its residual constraints, which is essentially re-inventing
  prim-subst. Recommend: publish only suggestions whose composed term is
  closed over session-visible constants and rigid symbols.

- **Non-uniqueness.** Two clash pairs may yield conflicting suggestions for
  the same recipe. Keep them as siblings in the top-K, do not try to unify
  them.

- **Feedback amplification.** An applied suggestion produces new clashes,
  which produce new unifiers, which produce new suggestions. Bound the
  recursion with a per-branch per-recipe counter (e.g. "at most 3
  suggestion-derived instantiations per recipe per branch").

- **`birth_branch` under β-splits.** When a fresh var predates a β-split,
  provenance's `birth_branch` is the pre-split id, which correctly scopes the
  suggestion to both children.

- **Soundness.** Suggestions are hints — they only reorder the queue, never
  remove options. The original γ- and prim-subst enumeration still runs.
  Completeness reduces to the completeness of the current calculus.

- **Termination.** Iterative deepening continues to advance independently of
  suggestions. A pathological stream of unhelpful suggestions can slow
  progress but cannot stall it, provided the per-branch per-recipe cap is
  enforced.

---

## Thin-slice implementation plan

1. **Provenance plumbing.** Add the `:provenance` ETS table in `EtsKeeper`.
   Tag fresh vars at `branch.ex:337` (γ) and inside the prim-subst enumeration
   in `branch.ex:399–485`. No consumer yet — validate the data on an
   `examples/*.livemd` run.
2. **Widen `ContradictionAgent` output.** Publish pair-level unifiers on
   `unifier_candidates_<session>`. Global closure behaviour unchanged.
3. **Stub `SuggestionAgent`.** Subscribes, decomposes σ via `:provenance`,
   scores, logs suggestions. No delivery yet. Validate on an example that is
   currently prim-subst-bound.
4. **Delivery.** Add `Worker.handle_info({:suggestion, _}, _)` and the queue
   splice. Gate the whole feature behind a `Parameters` flag
   (`suggestions_enabled: false` by default) so it can be A/B'd against the
   current prover on the `examples/` corpus.

Steps 1–2 are the risky ones (external `shot_un` cooperation, provenance
plumbing across two rule sites). Steps 3–4 are mechanical once those land.

---

## Success criteria

- With `suggestions_enabled: false`, no behavioural change vs. current prover
  on the `examples/` corpus.
- With `suggestions_enabled: true`, prim-subst-bound examples close at
  strictly lower `prim_limit` values, or in strictly less wall time at the
  same limit.
- Regression: every currently-closing example still closes; every currently
  saturating example still saturates.
