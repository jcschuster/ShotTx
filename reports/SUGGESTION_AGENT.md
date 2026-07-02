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
CSP driver logic:

```elixir
defstruct session_id: nil,
          ets_tables: %{},
          active_branches: MapSet.new(["root"]),
          clashing_local_pairs: %{},        # branch_id → MapSet<{a,b}>
          birth_scopes: %{},                # recipe → birth_branch (from :provenance)
          seen_unifiers: %{},               # (recipe, term) → score
          published: MapSet.new(),          # (birth_branch_prefix, recipe, term) — dedup
          pending_search: nil,
          params: %Parameters{}
```

The duplication of `active_branches` and `clashing_local_pairs` with CA is
deliberate: it is the price paid for the "no CA ↔ SA edge" constraint.
Memory cost is negligible (branches and pairs are shared ETS-refs), and
divergence is bounded — both agents drop the same message stream.

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

Add an ETS table `:suggestions` owned by `EtsKeeper`, shape:

```
:suggestions :: {branch_prefix :: String.t(), recipe :: term_id()}
             ↦ [%Suggestion{term, source, score, published_at_us}]
```

The prefix mirrors `tombs` semantics — a suggestion keyed at `"root_A"` is
inherited by `"root_A_B"`, `"root_A_B_I0"`, and so on. Existing
`poisoned?/2` walking logic (`worker.ex:311–320`) becomes the template for
`suggestions_for/2`.

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

Consumption is destructive: once a suggestion has been spliced into a
descendant of its `birth_branch`, remove it from `:suggestions` and record
in the branch's `processed_rules` so β-sibling reprocessing does not
double-apply. Alternative: keep the entry, use a per-branch consumed set
in ETS — heavier, no measurable win.

### Splicing mechanics

A `%Suggestion{recipe, source, term}` becomes a synthetic rule:

```elixir
rule = {:instantiate, [{app(recipe, term), {nil, nil}}], 1}
```

with cost `params.formula_cost.({:suggested_instantiate, recipe})` — a new
low-cost bucket that outranks the ambient γ / prim-subst enumeration. The
existing `apply_rule({:instantiate, ...}, ...)` path in `branch.ex:296`
handles the rest. No new rule semantics are introduced.

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

1. **Evidence broadcast.** Refactor `Worker.notify_ca` /
   `notify_ca_call` into a `broadcast_evidence` helper that keeps the
   synchronous CA edge and adds a `Registry.dispatch` on
   `branch_evidence_<session>`. No consumers besides CA yet.
2. **Provenance plumbing.** Add the `:provenance` ETS table in
   `EtsKeeper`. Tag fresh vars at `branch.ex:337` (γ) and inside the
   prim-subst enumeration in `branch.ex:399–498`. Validate the data on
   an `examples/*.livemd` run.
3. **Stub `SuggestionAgent`.** GenServer subscribed to
   `branch_evidence_<session>` with its own `active_branches` /
   `clashing_local_pairs` state. Pair-level search only, logs suggestions,
   no publication. Validate that suggestions correlate with the closures
   CA eventually finds on a prim-subst-bound example.
4. **`:suggestions` ETS + publication.** Add the table in `EtsKeeper`.
   SA writes suggestions with a wake-up ping. Workers gain a
   `splice_suggestions/2` helper called at the three splice points.
5. **Cost bucket + branch history annotation.** Add
   `params.suggestion_cost` and record spliced suggestions in the
   branch's history under a `{:suggestion, recipe, term}` tag so proofs
   remain replayable.
6. **Flag.** `params.suggestions_enabled` default `false`. A/B on the
   `examples/` corpus.

Steps 1–2 are the risky ones (event fan-out and provenance across two
rule sites). Steps 3–5 are mechanical once those land.

---

## Success criteria

- With `suggestions_enabled: false`, no behavioural change vs. current
  prover on the `examples/` corpus.
- With `suggestions_enabled: true`, prim-subst-bound examples close at
  strictly lower `prim_limit` values, or in strictly less wall time at
  the same limit.
- Regression: every currently-closing example still closes; every
  currently saturating example still saturates.
- CA's per-call `csp_duration_us` distribution does *not* regress —
  confirming SA and CA are not contending for the same solver work.

