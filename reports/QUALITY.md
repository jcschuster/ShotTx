# ShotTx Code-Quality Assessment

> **Status (2026-07-28).** This is a snapshot audit; the codebase has moved
> since. Issues **#4, #6, #8, #10** have been fully resolved (mainly by the
> CA peer-architecture refactor and the ablation-parameters commit). Issue
> **#11** is partially resolved (only the `worker_pool_size` bullet).
> Remaining findings — liveness (#1), races (#2, #3), crash recovery (#5,
> #7), lockstep deepening (#12), and the ETS / message-fanout items in the
> "smaller things" list — have not been addressed and remain accurate as
> known technical debt at the thesis cutoff.

Scope: the prover core (`Manager`, `Worker`, `ContradictionAgent`, `EtsKeeper`,
`SessionSupervisor`, `Branch`, `Rules`, `Stats`, `FormulaPqueue`). Proof
rendering and term generation modules were not reviewed in depth.

---

## Severe issues

### 1. Liveness bug in `Manager.check_and_trigger_deepening`
File: `lib/shot_tx/prover/manager.ex:235–265`.

The function dispatches on three terminal branches, and only the third
(`send_wake_up_if_open`) re-arms the workers. The other two fire a cast at the
`ContradictionAgent` and return `{:noreply, state}` without scheduling any
follow-up:

- **`has_saturated?` → `{:verify_csa, ...}` cast.**
  In `ContradictionAgent.do_handle_cast({:verify_csa, ...})`
  (`contradiction_agent.ex:271`) there's a code path where neither `:sat` nor
  `:unsat` is produced: if `all_saturated? == false` and `csa_or_unknown`
  returns `:unknown`, *nothing* is sent. All workers stay idle, Manager's
  `idle_workers` stays full, no fresh `:worker_idle` will be generated, and the
  session hangs until timeout.
- **`idle_queue_empty?` → `:verify_all_closed` cast.**
  Same shape — if `find_valid_combination` returns `:error` and
  `active_branches` is non-empty, no message is sent, no deepening, no
  wake-up.

**Fix:** these should be sync calls returning `:open`/`:closed`/`:retry`, or
the CA must always send a `:proof_result` (possibly `:unknown`) so the Manager
unblocks deterministically.

---

### 2. Race between idle/parked counts and the deepening trigger
The Manager decides whether to wake parked branches by checking
`state.parked_count == 0`, which is a separate cast (`:branch_parked`) from
`:worker_idle`. Per-worker FIFO ordering guarantees the local invariant.
However:

- `transfer_idle_to_work_queue` drains the `idle_queue` ETS table and resets
  `parked_count := 0`.
- A concurrent worker can `:ets.insert(idle_queue, ...)` between the Manager's
  `tab2list` and `delete_all_objects`, leaving the branch in ETS while its
  `:branch_parked` cast is still in flight.
- The newly parked branch is then effectively "lost" until another worker
  happens to go idle and re-trigger deepening.

`parked_count` is a redundant approximation of
`:ets.info(idle_queue, :size)`. Drop the cast and read ETS directly.

---

### 3. CSP retrigger gap in `ContradictionAgent.check_global_closure`
File: `contradiction_agent.ex:379`.

While `pending_search` is set, every `local_clashes_sync` is accepted and the
candidate set grows, but the function early-returns without scheduling a
re-check. The negative `:no_closure` callback (`contradiction_agent.ex:241`)
clears `pending_search` and does **not** re-call `check_global_closure`.
A closable global state arriving during a CSP run is not detected until the
next external event (commonly the next deepening `:settle` round). Liveness
holds eventually, but the prover wastes search budget — and within the user's
timeout, may simply fail to close.

---

### 4. Per-split synchronous round-trip through the ContradictionAgent — ✅ **RESOLVED**
*Fixed by the CA-refactor commit (`2859bb6`).* Workers now `broadcast_evidence/2`
to a shared `branch_evidence_<session>` PubSub topic (`worker.ex:187, 203, 223,
247, 253`); CA and SuggestionAgent subscribe as peers. No more synchronous
per-split funnel through a single GenServer.

<details><summary>Original finding</summary>

Every β-split, every `:instantiate`, every `:closed`, and every `:atomic` that
produces clashes went through `notify_ca_sync`
(`worker.ex:183, 199, 220, 252`). That was a `GenServer.call(:infinity)` per
branching step, serialised through a single CA process.

</details>

---

### 5. `spawn_workers` swallows start failures
File: `manager.ex:215`.

```elixir
for i <- 1..state.worker_count do
  DynamicSupervisor.start_child(...)
end
```

The return value is discarded. If any worker fails to start,
`MapSet.size(idle_workers) == worker_count` is unreachable and the proof can
only terminate by timeout. Either pattern-match `{:ok, _}` and crash, or
decrement `worker_count` on failure.

---

### 6. `worker_pool_size` is silently un-configurable — ✅ **RESOLVED**
*Fixed as part of the ablation-parameters commit.* `Parameters` now has
`worker_pool_size :: :auto | pos_integer()` (default `:auto`); Manager resolves
it via `resolve_worker_count/1` (`manager.ex:53`). Setting it to `1` is the
canonical serial baseline for the ablation matrix.

---

### 7. In-flight branches are lost on worker crash
The worker takes a branch out of the ETS work_queue (`:ets.take`) and stores
it in its own GenServer state. The DynamicSupervisor restarts a fresh worker
on crash, but the held branch is gone. The `rescue e -> reraise e` block in
`worker.ex:151` logs the crash and re-throws.

For an iterative-deepening refutation search this is soundness-preserving
(losing a branch never produces a false `:thm`), but it can silently turn a
provable theorem into `:timeout`. At minimum, `terminate/2` should push
`state.current_branch` back to the queue when it's non-nil and the reason is
abnormal.

---

## Logic / model issues

### 8. Two-stage CA initialization is structural debt — ✅ **RESOLVED**
*Fixed by the CA-refactor commit.* `CA.init/1` (`contradiction_agent.ex:86`)
now calls `EtsKeeper.get_tables(session_id)` directly and subscribes to the
PubSub topic in the same step. No more `set_ets_tables` handshake; no more
dropped-event window.

### 9. The `:aborted` flag is dual-purposed
`send_proof_result` sets `:aborted := true` *as part of reporting success*
(`contradiction_agent.ex:543`). The same predicate is then used by both
workers and CA to decide "stop doing things". The code works, but it
conflates "proof finished successfully" with "abort all work in progress",
which obscures intent — e.g. a late reply path returns `:aborted` to a
worker even though the proof completed normally.

### 10. Dead code in the CA message protocol — ✅ **RESOLVED**
*Fixed by the CA-refactor commit.* Only one handler remains — the topic-driven
`do_handle_info({:local_clashes, ...})` at `contradiction_agent.ex:212`.
The `_sync` and cast variants are gone.

### 11. `Map.get` used to access fields with a known schema — ⚠️ **PARTIAL**
- ~~`Map.get(params, :worker_pool_size, ...)`~~ — resolved with #6.
- `Map.get(state.ets_tables, :stats)` — **still present** in `worker.ex:100`,
  `contradiction_agent.ex:131, 596`, `model_agent.ex:278, 295, 337`. Runs on
  every message. See #20.
- `Map.get(state, :current_branch)` in `worker.ex:60` — **still present**;
  defensive against a field the author guarantees is present.

### 12. Gamma and prim-subst limits increment together
`manager.ex:276`:

```elixir
new_gamma = state.current_gamma_limit + 1
new_prim  = state.current_prim_depth_limit + 1
```

Couples two independent search-space parameters and doubles the cost of each
deepening level. A classical iterative-deepening prover varies them on
different schedules.

### 13. `transfer_idle_to_work_queue` rewakes every parked branch on each level
Every branch in `idle_queue` is woken with `Branch.wake_up/2`, which
re-enqueues *all* sleeping gamma rules at higher costs. With many parked
branches this is `O(N · sleeping_rules)` work per deepening round — even
when most will immediately hit the new gamma cap and re-park.

### 14. `apply_rule({:gamma, ...})` first-firing ground instantiation
`branch.ex`. The first instantiation (`prev == 0`, `instance_based_gamma:
true`) pushes one instance per existing closed term of the right type from
`branch.ground_terms`. Ground terms added later are not eagerly fed back
through past recipes — they are picked up the next time the γ-rule fires
under iterative deepening. The recipe-cascade mechanism that previously
chased every newly-discovered ground subterm was removed because it could
loop forever when a recipe's body produced subterms of its own input type
(e.g. extensional equality of `ι→ι` functions).

### 15. β-variant adds `¬B₁` unconditionally to the right branch
`branch.ex:256`. The "β with extra negated assumption" optimization is sound
for the current β-classifiers (`disjunction`, `implication`, `equivalence`,
`¬conjunction`, `¬equivalence`), but the implementation is unconditional —
soundness rests on an implicit invariant about every β-classifier the
`Rules` module produces. Either move the variant into the rule tuple, or add
a precondition assertion.

---

## Anti-patterns

### 16. Catch-all `handle_info(_msg, state)`
`manager.ex:150`, `worker.ex:93`. Silently swallows every unexpected message,
including `{:'EXIT', ...}` and `{:DOWN, ...}`. Workers subscribe to a
Registry and Managers spawn task children — an unexpected `DOWN` is dropped
instead of surfacing the cause. At minimum, log at debug.

### 17. `:work_available` fan-out on every push
`worker.ex:306`. Each `push_work` fans a `:work_available` message to all N
workers. Non-idle workers ignore it (`handle_info(:work_available, %{current_branch: nil} = ...)`
only continues when idle). Workers already self-trigger via
`{:continue, :process_next}`. The notification is essentially noise.

### 18. Hand-rolled CAS retry loop in `Stats.record_max/record_sample`
`stats.ex:31, 58`. Bounded to 3 retries, otherwise silently no-ops. Under
contention, max/sample values become approximations. Acceptable for stats;
the same pattern with the same `retries: 3` would be wrong anywhere
correctness mattered. Consider `:counters`/`:atomics` for hot counters.

### 19. `:ets.tab2list` in hot paths
`manager.ex:301` (`transfer_idle_to_work_queue`), `contradiction_agent.ex:537`
(`read_traces`), `manager.ex:314` (`gather_traces`). Materializes the entire
table on every deepening level. End-of-session reads are fine; hot-loop reads
are not.

### 20. `Map.get(state.ets_tables, :stats)` per CA message
`contradiction_agent.ex:99`. The `aborted?` check runs first in every
handler. On a hot CA processing thousands of clash notifications per second
that's a `Map.get` plus an ETS lookup per message. Cache the table ref on
the struct after `set_ets_tables`, or move the abort signal to a per-process
field.

### 21. `String.split("_") |> Enum.scan` to walk branch ancestors
`worker.ex:312` (`poisoned?`), `contradiction_agent.ex:502, 514`
(`get_inherited_*`). Branch IDs encode the tree path as `"root_A_B_I0"`, so
ancestor checks devolve into string parsing on every poison/inheritance
test. The same logic is duplicated in three places with subtly different
reductions. A struct `%BranchId{ancestors: [...]}` would be faster and
self-documenting.

### 22. Variable rebinding violates `CLAUDE.md`
The project rule "NEVER rebind a variable name in the same scope" is
routinely violated, e.g. `contradiction_agent.ex:289` `sorted = ...`
immediately after the same name was assigned higher up;
`branch.ex:526` `simplified = ...`; `branch.ex` reduces with `b → b2`
two-deep and creates ad-hoc `acc_branch`, `b`, `b2` names. Either relax the
rule or apply it.

### 23. Three layers of indirection on the proof protocol
`Prover.sat → GenServer.call → Manager.handle_call → CA.send_proof_result
(cast) → Manager.handle_cast({:proof_result, ...}) →
GenServer.reply(active_caller, ...)`.

The `active_caller` `from` reference round-trips through unrelated
processes and `if state.active_caller` nil-checks are scattered across
every callback. The CA's CSP is already off the Manager's event loop via
`Task.Supervisor.async_nolink` — a single GenServer that owns the search
would be simpler.

### 24. β-variant coupling between classifier and branch executor
The `:beta_variant` optimization is hard-coded inside
`Branch.apply_rule({:beta, ...})`. The rule classifier emits
`{:beta, {b1, b2}}` with no marking of which kind of β it was. See #15 —
the safety invariant lives in the gap between two modules.

---

## Smaller things worth noting

- `EtsKeeper` uses `:public` tables with both `read_concurrency: true` and
  `write_concurrency: true` everywhere, including `:set`/`:ordered_set`.
  `write_concurrency` on an `:ordered_set` work_queue is only meaningfully
  concurrent for keys in different lock partitions — under contention the
  queue is still a hot spot.
- `Logger.warning("Dispatching CSP...")` (`contradiction_agent.ex:392`) logs
  every CSP dispatch at warning level — misclassified.
- `notify_ca_sync` uses `:infinity` (`worker.ex:329`). A stuck CA hangs the
  worker forever.
- `Prover.sat/3` calls `DynamicSupervisor.terminate_child` synchronously
  after the result. If a worker's `terminate/2` blocks, so does the caller.
- The `:proof_started_at_us` ETS row is set in `EtsKeeper.init` before
  `start_proof` is called, so timing stats include the setup delay.
- `simplify_formula` compares `PropSimplify.simplify(source, mode)` with `==`
  to detect a no-op (`branch.ex:528`). That's structural-id equality;
  `PropSimplify` must guarantee identity-preservation when no rewrite
  happens. Worth an assertion or test.

---

## Bottom line

Architecturally the design is sound — pure `Branch.step`, immutable branches,
ETS-backed queues, supervised CSP — but the realisation has two recurring
failure modes:

1. **The contradiction agent is both a hot bottleneck and a state machine
   with deadlock-prone branches.** Every interesting worker step funnels
   through it synchronously, and at least two of its decision paths can fail
   to send a reply that some other process is implicitly waiting for
   (see #1, #3, #8). It is the module to rewrite first.
2. **The Manager's protocol relies on derived/cached state that the ETS
   tables already hold directly** (`parked_count`, `idle_workers`,
   `active_branches`), and on side-effects ordered by happens-before
   guarantees that aren't always preserved (see #2, #5, #7). Simplifying the
   Manager by querying ETS directly during deepening checks, rather than
   tracking its own counters, would eliminate a class of races.

The `Branch` module itself is the cleanest part of the codebase — the outbox
pattern is well applied. Most of the issues live in the actor scaffolding
around it.
