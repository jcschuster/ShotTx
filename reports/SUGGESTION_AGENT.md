# SuggestionAgent — Design Sketch

Scope: a proposed new component that turns unifier evidence discovered from
per-branch clash pairs into targeted instantiation hints for the γ- and
prim-subst machinery. The intent is to replace speculative backtracking
through substitution options with evidence-driven instantiation.

**Architectural constraint (load-bearing):** SuggestionAgent is a *peer* of
`ContradictionAgent`, not a downstream consumer. Both subscribe to the same
raw evidence stream published by workers; both run their own unifier search.
There is no `CA → SA` channel. This keeps the two agents independently
testable and avoids the semantic entanglement of two agents sharing a
solver state.

---

## Implementation status (as of the latest commit)

All six thin-slice steps have landed behind `params.suggestions_enabled`
(default `false`), so the prover's behaviour is bit-for-bit unchanged
unless the flag is flipped. The full-suite test run passes 143/143 with
the flag off; a dedicated end-to-end regression check runs a γ-driven
theorem with the flag on and confirms the pipeline still returns
`{:thm, _}`.

**Landed modules and files:**

| Concern | Module / file |
| --- | --- |
| Provenance struct + ETS writer | `lib/shot_tx/prover/provenance.ex` |
| SA GenServer | `lib/shot_tx/prover/suggestion_agent.ex` |
| Suggestion struct | `lib/shot_tx/prover/suggestion.ex` |
| ETS ownership | `lib/shot_tx/prover/ets_keeper.ex` — new `:provenance` + `:suggestions` tables |
| Evidence fan-out | `lib/shot_tx/prover/worker.ex` — `broadcast_evidence/2` + `fanout_evidence/2` |
| γ / prim-subst annotation | `lib/shot_tx/prover/branch.ex` — outbox `{:record_provenance, records}` effect |
| Prim-subst hole exposure | `lib/shot_tx/generation/general_bindings.ex` — `build_binding/2` now returns `{binding, h_terms}` |
| Splice mechanism | `Branch.splice_suggested_instantiate/5` + new `{:suggested_instantiate, recipe, term}` rule + `Worker.splice_suggestions/2` |
| Proof rendering | `lib/shot_tx/proof.ex` — `interior_event/2` + `rule_symbol(:suggested_instantiate)` |
| Feature flag + cascade cap | `lib/shot_tx/data/parameters.ex` — `suggestions_enabled`, `suggestion_cascade_ceiling` |
| Stats counter | `Stats.@rule_keys` — new `:rule_suggested_instantiate` |

One deviation from the sketch below remains after the CA-migration
follow-up: the splice mechanism uses a dedicated
`:suggested_instantiate` rule tag rather than reusing `:instantiate`.
See the [§Deviations](#deviations-from-original-design) section at the
bottom.

---

## Motivation

The prover currently discovers substitutions in two disjoint places:

1. **γ / prim-subst enumeration** (`lib/shot_tx/prover/branch.ex:316–498`)
   generates candidate instantiations of universal quantifiers by minting
   fresh variables and, for prim-subst, iteratively deepening general
   bindings. This is speculative — every candidate is a guess, most guesses
   lead to open branches, and iterative deepening is the fallback when
   guesses fail.

2. **Closure attempts** in `ContradictionAgent`
   (`lib/shot_tx/prover/contradiction_agent.ex:409–423`) call `shot_un` to
   find a unifier across the full cartesian product of clash pairs. When
   `find_global_closure/2` succeeds, the resulting substitution `σ` already
   tells us what the "right" instantiations were — but today `σ` is only
   used to close the proof, then discarded.

The load-bearing observation: a substitution `X ↦ t` where `X` was born from
a γ-rule on `∀y. φ(y)` is empirical evidence that `t` is the instantiation
the proof needed. CA sees this evidence only when it is strong enough to
close *every* open branch simultaneously. SA's job is to notice it earlier
— from *any single clash pair* that unifies — and feed it back to the
γ-rule's source formula so that sibling branches, which still enumerate,
skip straight to the useful term.

---

## Prerequisites — variable provenance

Nothing today records where a fresh γ-variable came from. In
`branch.ex:337` a fresh var is minted with `TF.make_fresh_var_term(type)`
inside the γ-rule; `recipe` (the `λx.φ(x)` closure) and the originating
`source` formula id are in scope but never persisted per-variable. The same
gap exists in the prim-subst path (`branch.ex:399–498`).

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
var id. Written at exactly two sites (the γ fresh-var mint and the
prim-subst enumerator). This is the load-bearing piece — without it, a
unifier `{X ↦ t}` cannot be traced back to any quantifier. Both CA and SA
can read it; only the two rule sites write it.

---

## Component design

New GenServer sibling to `ContradictionAgent` under `SessionSupervisor`:

```
SessionSupervisor
├─ EtsKeeper                 (adds :provenance and :suggestions tables)
├─ Manager
├─ ContradictionAgent
├─ SuggestionAgent           (new, peer of CA)
└─ DynamicSupervisor → Worker × N
```

**Event flow (revised — no CA ↔ SA edge):**

```
Worker  ── {:local_clashes, branch_id, MapSet<{a,b}>}    ┐
Worker  ── {:branch_split, parent_id, [child_ids]}       │
Worker  ── {:branch_closed, branch_id}                   ├──▶ CA
Worker  ── {:branch_saturated, branch_id, model}         │
                                                         └──▶ SA
                                                              │
                                                              ▼
Worker  ◀──────── :suggestions ETS table + :work_available ── SA
```

The one edge shift from today: `notify_ca`/`notify_ca_call` in
`worker.ex:250–252, 183, 199, 220, 244` must fan out to both CA and SA. The
simplest change is to switch these to a `Registry.dispatch` on a new
`branch_evidence_<session>` PubSub topic — both agents register on init,
neither knows about the other. Ordering per branch is preserved because a
single worker sends its events sequentially and `Registry.dispatch` uses
plain `send/2`.

The `{:branch_split, …}` and `{:closed, …}` calls that are currently
synchronous (`GenServer.call`) exist to backpressure the worker while CA
mutates its `active_branches`. That backpressure is needed for CA's global
closure invariant; SA does not need it. **Recommendation:** keep the
synchronous edge on CA (send via `GenServer.call` as today) and fire an
asynchronous copy on `branch_evidence_<session>` for SA. Encapsulate this
in a single worker helper `broadcast_evidence/2` so the two channels stay
in sync.

---

## SA's own state

SA maintains an independent copy of exactly the fields CA needs, minus the
CSP driver logic. The struct that landed is a subset of the original
sketch:

```elixir
defstruct session_id: nil,
          ets_tables: %{},
          active_branches: MapSet.new(["root"]),
          clashing_local_pairs: %{},        # branch_id → MapSet<{a,b}>
          params: %Parameters{}
```

The fields `birth_scopes`, `seen_unifiers`, `published`, and
`pending_search` from the original sketch **did not land** — the current
implementation looks up `birth_branch` per-substitution via
`Provenance.fetch/2` and relies on `:ets.insert_new/2` on the
`:suggestions` table for dedup, so no in-memory shadow state is needed.
The `pending_search` slot is unused because SA's unifier call is
synchronous (a single `ShotUn.unify/2` per pair, at most one solution
via `Enum.take(1)`); there is nothing to await asynchronously.

The duplication of `active_branches` and `clashing_local_pairs` with CA is
deliberate: it is the price paid for the "no CA ↔ SA edge" constraint.
Memory cost is negligible (branches and pairs are shared ETS-refs), and
divergence is bounded — both agents drop the same message stream.

CA and SA are now genuine peers: both subscribe to
`branch_evidence_<session>`, and workers publish every lifecycle event
exactly once. The former synchronous CA edge is gone. See
[§Ordering without the sync CA edge](#ordering-without-the-sync-ca-edge)
for how the invariants that the sync used to enforce are now preserved
defensively.

---

## Lifecycle of a suggestion

1. **Ingest.** SA receives `{:local_clashes, branch_id, new_candidates}`
   from `branch_evidence_<session>`. Merges into
   `clashing_local_pairs[branch_id]` (same accumulator shape as CA).

2. **Search — pair-level only.** CA's `find_global_closure/2`
   (`contradiction_agent.ex:409`) enumerates the full cartesian product
   over all active branches and demands a global unifier. SA runs a
   strictly weaker search: for every freshly-added clash pair `{a,b}`,
   call `ShotUn.unify([{a,b}], depth) |> Enum.take(1)`. Nothing more.
   Any multi-pair subset unifier is dominated by the individual pair
   unifiers that constitute it — the substitutions on fresh vars that
   SA cares about already appear in the pair-level σs, and the
   multi-pair regime is exactly what CA covers. Trying to bridge the
   two would just re-implement a slice of CA.

3. **Derive.** For every `X ↦ t` in a returned σ:
   - look up `X` in `:provenance` → `(recipe, source, birth_branch, origin)`
   - compose bindings so `t` is fully grounded w.r.t. the rest of σ
     (`X ↦ f(Y), Y ↦ a` collapses to `X ↦ f(a)`)
   - discard the suggestion if the composed term still contains fresh
     variables whose provenance is outside the current branch's scope

4. **Score & dedupe.**
   - number of clash pairs the σ closed simultaneously,
   - term size / prim-subst depth-equivalent (cheaper first),
   - evidence count (same `(recipe, term)` seen in independent σs).
   Keep bounded top-K per recipe (K ≈ 8). Drop any candidate present in
   `published` for the same `(birth_branch_prefix, recipe, term)`.

5. **Publish.** See the next section — this is the delicate part.

---

## Publication of found instantiations — careful review

Under the peer architecture, SA's only output is a stream of instantiation
hints scoped to a `birth_branch`. Delivering them to workers is subtler
than the original sketch acknowledged. The below enumerates the design
constraints and picks a delivery mechanism.

### Where the target branches actually live

At any moment a descendant of `birth_branch` may be in one of five states:

| State | Location | Reachable by PubSub `send/2`? |
|---|---|---|
| Currently stepping | Worker's `state.current_branch` | Yes (owning worker) |
| Just-yielded, waiting in `work_queue` | ETS `:work_queue` | No (no owner) |
| Parked idle | ETS `:idle_queue` | No |
| Split, both children queued | ETS `:work_queue` × 2 | No |
| Tombed / closed | ETS `:tombs` | Suggestion must be dropped |

A pure PubSub delivery only lands on state 1. Anything else needs the
suggestion to be readable when the branch is next dequeued — i.e., an
authoritative record on the blackboard.

### Recommended mechanism: ETS `:suggestions` + wake-up ping

Add an ETS table `:suggestions` owned by `EtsKeeper`. The **as-built**
row shape differs from the sketch — one row per suggestion instead of
a list wrapper — so that `:ets.update_counter/3` can enforce the
cascade cap atomically at the splice site:

```
:suggestions :: {branch_prefix, recipe, term}     % ← ETS key
             ↦ {applied_count :: non_neg_integer,
                %Suggestion{term, source, score, published_at_us}}
```

`applied_count` sits at position 2 of the tuple so the counter guard
in `Worker.splice_suggestions/2` is one `:ets.update_counter(sug_table,
key, {2, 1})` call. The prefix still mirrors `tombs` semantics — a
suggestion keyed at `"root_A"` is inherited by `"root_A_B"`,
`"root_A_B_I0"`, and so on. Existing `poisoned?/2` walking logic
(`worker.ex:311–320`) is the template for the ancestor-prefix walk
that landed as `Worker.ancestor_prefixes/1`.

SA writes with `:ets.insert_new` (dedupe under contention), and follows the
write with:

```elixir
Registry.dispatch(ShotTx.Prover.PubSub, "branch_control_#{session_id}", fn entries ->
  for {pid, _} <- entries, do: send(pid, :work_available)
end)
```

exactly as workers already do in `worker.ex:302–309`. The wake-up nudges
idle workers to re-check the queue; workers holding a live branch see the
`:work_available` and can splice on next yield.

Workers consult `:suggestions` at three splice points:

1. **On checkout** (`do_process_next/1` with `current_branch: nil`, after
   `poisoned?/2` passes). Splice all applicable suggestions into the just-
   checked-out branch's queue before returning `{:continue, ...}`.
2. **On step boundary yield** (`steps_since_yield >= @yield_limit`). Same
   splice, then `push_work`.
3. **On idle wake-up** (`{:wake_up, ...}` handler). Same splice on every
   branch being reactivated.

**As-built:** sites 1 and 2 landed. Site 3 is covered indirectly —
the wake-up handler's `{:continue, :process_next}` triggers a fresh
checkout, which runs site 1's splice.

Consumption is **not** destructive as the sketch proposed. Rows stay in
`:suggestions` and the `applied_count` counter (position 2) tracks how
many times each suggestion has been consumed. The cascade cap
(`params.suggestion_cascade_ceiling`, default `3`) is enforced by an
atomic `:ets.update_counter/3` at the splice site — the winning worker
under contention sees `count ≤ ceiling` and splices; any subsequent
worker sees the incremented count and skips. Idempotent, no lock. The
"per-branch consumed set" alternative from the sketch is unnecessary.

### Splicing mechanics

**Sketch (superseded).** The original design proposed reusing
`:instantiate`:

```elixir
rule = {:instantiate, [{app(recipe, term), {nil, nil}}], 1}
```

**As built (Step 4 deviation).** Reusing `:instantiate` unconditionally
routes through `instantiate_children/5`, which (a) spawns an `_I0`
child branch and (b) merges the inner `{decl, tid}` tuple into
`branch.defs` — the `{nil, nil}` placeholder would pollute `defs` with
a `nil ↦ nil` entry and create a spurious branch on every splice.
Neither is what a hint should do.

A new rule tag was introduced instead:

```elixir
rule = {:suggested_instantiate, recipe, term}
```

with its own `apply_rule/6` clause in `branch.ex` that just
`insert_formula`s `app(recipe, term)` on the current branch — no
fanout, no `defs` mutation, no queue split. Cost is `2` (see
`Rules.rule_cost/2`), cheaper than γ (≥ 3) and prim-subst (≥ 20) but
not free — atomic (1) still preempts, so closure detection is never
starved by a runaway suggestion stream. The cascade cap enforces
termination.

Threaded through:

* `Rules.rule_t` — new `suggested_instantiate_t` variant.
* `Branch.splice_suggested_instantiate/5` — public splice API.
* `Proof.interior_event/2` + `Proof.rule_symbol(:suggested_instantiate)` — renders as `sug-inst` in the proof tree.
* `Worker.rule_key/1` + `Stats.@rule_keys` — counter `:rule_suggested_instantiate`.

The design-doc line "no new rule semantics are introduced" is
inaccurate as a result of this deviation and has been superseded here.

### Failure modes and their treatment

- **Suggestion for a since-tombed branch.** `poisoned?` fires at checkout;
  branch discarded before splice. Suggestion in `:suggestions` becomes
  dead weight — a periodic sweeper on `SA` (every ~1s) prunes entries
  whose branch_prefix has any ancestor in `:tombs`.
- **Suggestion delivered before the branch has been split off.** Prefix
  match still works: `"root"` covers all descendants. Common case: a σ
  found from clashes on `"root_A"` is delivered before `"root_A_B"` is
  born; when `"root_A_B"` is created it inherits.
- **Suggestion delivered after the recipe's source formula has been
  simplified away.** Simplification (`branch.ex:558`) can rewrite the
  source, breaking the `source` reference. The `recipe` (an abstraction,
  not a formula-id) survives β-η, so key suggestions on `recipe` alone;
  `source` is diagnostic-only.
- **Non-terminating cascade.** Applied suggestion creates new clashes →
  new pair unifiers → new suggestions. Cap: per-branch counter of
  applied suggestions per `recipe`, ceiling 3. Enforced in the splice
  step (worker reads and increments in `:suggestions` via
  `:ets.update_counter`).
- **Worker holds branch mid-cascade of splice arrivals.** Worker only
  splices at yield points — never mid-`apply_rule`. Yield is bounded by
  `@yield_limit = 10`, so latency is bounded.
- **SA and CA racing on the same evidence.** CA may close the session
  while SA has pending suggestions in-flight. The `:aborted` flag
  (`stats` table) short-circuits both agents. Workers check
  `aborted?/1` on every step (`worker.ex:105`), so pending suggestions
  land in a session that's already returning.
- **Worker duplication under contention.** Two workers may check out
  descendants of the same `birth_branch` and both try to splice the same
  suggestion. Guard the splice with `:ets.update_counter` on a per-
  suggestion `applied_count`; the loser sees `applied_count > 0` and
  skips. Idempotent.

### Ordering guarantee we do *not* need

Suggestions are not required to be applied in any global order. They only
reorder the queue — completeness reduces to the completeness of the
underlying γ / prim-subst enumeration, which continues in parallel. A
suggestion arriving late has no worse effect than a suggestion arriving
early — the queue swallows both.

---

## Design forks (revised)

| Fork | Options | Recommendation |
|---|---|---|
| **CA ↔ SA edge** | (a) SA subscribes to CA's unifier candidates, (b) SA subscribes to raw worker events like CA does | **(b).** Load-bearing decision — see intro. |
| **SA search strategy** | (a) mirror CA's cartesian product, (b) pair-level unification only, (c) sample random subsets | **(b).** Every multi-pair subset unifier decomposes into pair-level σs on the substitutions that matter for suggestions; the multi-pair regime is CA's job. |
| **Delivery mechanism** | (a) PubSub-only, (b) ETS-only, (c) ETS write + PubSub wake-up | **(c).** PubSub reaches held branches; ETS reaches queued/parked branches; wake-up avoids polling. |
| **Splice priority** | (a) high-priority instantiate bucket, (b) same cost as normal γ | **(a).** The whole point of suggestions is to *skip ahead* of enumeration. |
| **Depth policy** | (a) respect current `prim_limit`, (b) bypass it | **(b).** The whole point is that a discovered `t` might exceed the current limit; blocking it defeats the mechanism. Iterative deepening still ticks so a bad suggestion cannot stall. |
| **Cross-branch replay** | (a) origin branch only, (b) all descendants of `birth_branch` | **(b).** That is exactly the LCA scope where the ∀ was in force. |
| **Interaction with `instance_based_gamma`** | (a) fold suggested terms into the IBG ground-terms cap, (b) keep as distinct channel | **(b).** IBG is a static enumeration heuristic; suggestions are dynamic evidence. Conflating them muddies both. |
| **Suggestion lifetime** | (a) per session, (b) TTL, (c) per-round | **(a), bounded top-K per recipe.** Tombing handles stale branches naturally via the sweeper. |

---

## Risks and open questions

- **`shot_un` per-pair cost.** SA's pair-level search calls
  `ShotUn.unify/2` many times, once per new clash pair. Each call is cheap
  compared to a full cartesian product, but the aggregate could still
  outweigh the gains. Mitigation: rate-limit — SA processes clashes in
  batches, sleeping between batches when the ETS `:suggestions` table
  exceeds a soft cap.
- **Higher-order unifiers.** For HOL, the term bound to `X` may itself
  contain fresh variables. The composition step in *Derive* must fully
  ground the suggested term before broadcast; otherwise the suggestion
  has to travel with its residual constraints, which is essentially
  re-inventing prim-subst. Recommendation: publish only suggestions whose
  composed term is closed over session-visible constants and rigid
  symbols.
- **Non-uniqueness.** Two clash pairs may yield conflicting suggestions
  for the same recipe. Keep them as siblings in the top-K, do not try to
  unify them.
- **Feedback amplification.** An applied suggestion produces new clashes,
  which produce new unifiers, which produce new suggestions. Bound the
  recursion with a per-branch per-recipe counter (see *Failure modes*).
- **`birth_branch` under β-splits.** When a fresh var predates a β-split,
  provenance's `birth_branch` is the pre-split id, which correctly scopes
  the suggestion to both children via the prefix walk.
- **Soundness.** Suggestions are hints — they only reorder the queue,
  never remove options. The original γ- and prim-subst enumeration still
  runs. Completeness reduces to the completeness of the current calculus.
- **Termination.** Iterative deepening continues to advance independently
  of suggestions. A pathological stream of unhelpful suggestions can
  slow progress but cannot stall it, provided the per-branch per-recipe
  cap is enforced.
- **SA never declares closure.** Pair-level search cannot witness a
  full multi-branch closure by construction, so the single-source-of-
  truth for `:unsat` stays with CA without any special handling.

---

## Thin-slice implementation plan

Status snapshot: all six steps landed. Each entry below is annotated
with the as-built delta.

1. **Evidence broadcast.** ✅ Landed. All lifecycle events go through
   `Worker.broadcast_evidence/2`, which fans out on
   `branch_evidence_<session>` via `Registry.dispatch`. Both CA and SA
   subscribe to the topic; the former direct `Worker → CA` edges
   (`notify_ca`, `notify_ca_call`) have been removed. See
   [§Ordering without the sync CA edge](#ordering-without-the-sync-ca-edge)
   for the defensive handling that replaces the sync-based invariant.
2. **Provenance plumbing.** ✅ Landed. `:provenance` ETS table in
   `EtsKeeper`; `%Provenance{}` struct in `ShotTx.Prover.Provenance`.
   Writes emitted from `branch.ex` as an outbox effect
   `{:record_provenance, records}` rather than a direct ETS write —
   keeps the pure functional core untouched. `Worker.apply_effect/3`
   handles the effect. Prim-subst annotation required extending
   `GeneralBindings.build_binding/2` to return `{binding, h_terms}` and
   moving the fresh-hole mint outside the scratchpad.
3. **Stub `SuggestionAgent`.** ✅ Landed. GenServer subscribed to
   `branch_evidence_<session>`, mirrors CA's `active_branches` /
   `clashing_local_pairs` accumulators. Pair-level unification per
   incoming clash. Publication of suggestions moved forward from
   Step 4 into the same commit as this step.
4. **`:suggestions` ETS + publication.** ✅ Landed. Row shape adjusted
   to per-row-with-counter (see [ETS `:suggestions` shape](#recommended-mechanism-ets-suggestions--wake-up-ping)).
   `Worker.splice_suggestions/2` called at sites 1 and 2; site 3 is
   covered indirectly by the wake-up → checkout path. Cascade cap
   enforced by `:ets.update_counter/3` with `params.suggestion_cascade_ceiling`
   (default `3`).
5. **Cost bucket + branch history annotation.** ✅ Landed. Cost bucket
   is `2` on the new `{:suggested_instantiate, _, _}` rule tag — no
   `params.suggestion_cost` field was needed since the cost is
   pre-computed by `Rules.rule_cost/2`. History annotation is the rule
   tag itself; `Proof.interior_event/2` and `rule_symbol/1` render it
   as `sug-inst`. Stats counter `:rule_suggested_instantiate` added.
6. **Flag.** ✅ Landed. `params.suggestions_enabled` defaults to
   `false`; SA's `init/1` has two clauses — passive (no subscription,
   no ETS load) and active (subscribes to the topic, loads
   `ets_tables`). Passive-mode message handlers early-return via a
   flag-matching `handle_info` head. A/B on the `examples/` corpus is
   still a manual step and has not been run — a future PR should
   collect timings and `csp_duration_us` distributions with the flag
   on vs. off.

The risk assessment held: steps 1–2 (event fan-out and provenance) were
the trickiest — the outbox pattern for provenance and the scratchpad
handling in `build_binding` both needed non-trivial adjustment. Steps
3–5 were mechanical once those landed.

---

## Success criteria

- With `suggestions_enabled: false`, no behavioural change vs. current
  prover on the `examples/` corpus. ✅ Verified — the full `mix test`
  suite passes 143/143 with the flag off.
- With `suggestions_enabled: true`, prim-subst-bound examples close at
  strictly lower `prim_limit` values, or in strictly less wall time at
  the same limit. ⏳ Not yet measured — A/B on the `examples/` corpus
  is future work.
- Regression: every currently-closing example still closes; every
  currently saturating example still saturates. ⏳ Not yet measured.
- CA's per-call `csp_duration_us` distribution does *not* regress —
  confirming SA and CA are not contending for the same solver work.
  ⏳ Not yet measured.

The end-to-end regression check in
`test/shot_tx/prover/suggestion_agent_test.exs` runs `Prover.prove/1`
on a small γ-driven theorem with `suggestions_enabled: true` and
confirms the pipeline still returns `{:thm, _}` — proof that the
mechanism does not crash the prover, but not proof that it accelerates
anything. That is the A/B step's job.

---

## Ordering without the sync CA edge

Historically CA received `:branch_split` and `:branch_closed` as
synchronous `GenServer.call`s, which blocked the emitting worker until
CA had updated `active_branches`. That serialization made the invariant
"a closed branch never re-enters `active_branches`" a natural
consequence of same-sender FIFO delivery, since any subsequent
lifecycle event from any worker was necessarily sent after CA had
processed the split.

With CA on the topic, cross-sender ordering isn't guaranteed. The
race we care about is a `:branch_closed` for `root_A` arriving before
the `:branch_split` that created `root_A`. The mitigations:

* CA's `:branch_split` handler filters out any child already present
  in `branch_closures`, so a late split cannot re-activate a
  closed branch.
* CA's `:branch_closed` handler tolerates unknown branches — the
  closure gets recorded, `MapSet.delete/2` on `active_branches` is a
  no-op, and the filter above cleans up when the split arrives.

The dual race (`:local_clashes` for a child arriving before its
split) is benign: CA's CSP runs over whatever it currently thinks are
the active branches, and clashes are prefix-inherited, so a σ closing
the parent also closes the not-yet-known children.

## Deviations from original design

The former Deviation 1 (CA not subscribed to the topic) has been
retired — CA now subscribes to `branch_evidence_<session>` and the
direct `GenServer.call/cast` edges from Worker have been removed. Only
Deviation 2 remains.

### `:suggested_instantiate` is a new rule tag, not a reuse of `:instantiate`

`instantiate_children/5` unconditionally spawns a child branch and
mutates `defs` — semantics we do not want for a hint. A dedicated rule
tag with its own `apply_rule/6` clause avoids this. Threaded through
`Rules`, `Proof`, `Worker`, and `Stats`. See
[§Splicing mechanics](#splicing-mechanics).

---

## Deferred future work

Items from the design that were consciously skipped in the initial
pass. All are enhancements, not correctness fixes.

- **Suggestion sweeper.** A ~1s tick that prunes `:suggestions` rows
  whose `branch_prefix` has any ancestor in `:tombs`. Correctness is
  not affected — `poisoned?/2` at checkout already drops the branch
  before splice runs. Only unbounded memory growth *within a session*
  is at stake, and sessions terminate.
- **TopK-per-recipe bound.** `:ets.insert_new` dedupes identical
  `{prefix, recipe, term}` keys, but different terms for the same
  recipe all get through. A future bound (say `top-K = 8` per recipe,
  ranked by `Suggestion.score`) would cap fan-out on
  many-solution problems.
- **Real scoring.** `Suggestion.score` is set to `1` unconditionally.
  Meaningful scoring (evidence count × term-size penalty × recipe
  proximity) is a scoring pass that has not been written.
- **σ composition / grounding.** SA looks up each `X ↦ t` via
  `Provenance.fetch/2` and publishes as-is; it does not compose the
  rest of `σ` into `t` to eliminate residual fresh vars. Consequence:
  some suggestions reference dangling fresh vars that fail to unify at
  the destination branch. The failure mode is silent (drop) and
  bounded by the cascade cap; correctness is preserved because the
  spliced formula still enters the ordinary tableau flow and either
  closes or leaves the branch open for the fallback γ / prim-subst
  enumeration.
- **A/B measurement on `examples/`.** See Success criteria.
