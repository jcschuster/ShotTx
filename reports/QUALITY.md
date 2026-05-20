# ShotTx Code-Quality Assessment

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

### 4. Per-split synchronous round-trip through the ContradictionAgent
Every β-split, every `:instantiate`, every `:closed`, and every `:atomic` that
produces clashes goes through `notify_ca_sync`
(`worker.ex:183, 199, 220, 252`). That's a `GenServer.call(:infinity)` per
branching step, serialised through a single CA process. The actor-based
parallelism described in `CLAUDE.md` is largely fictional — the prover funnels
through CA on every interesting step. This is the single biggest scalability
ceiling. The rationale (preserve happens-before for `active_branches`
updates) could likely be solved with a generation counter or by piggybacking
the events onto the same message the worker already sends.

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

### 6. `worker_pool_size` is silently un-configurable
File: `manager.ex:54`.

```elixir
worker_count = Map.get(params, :worker_pool_size, System.schedulers_online())
```

The `%Parameters{}` struct has no `:worker_pool_size` field. `Map.get` on a
struct returns the default if the key is absent. So the lookup always falls
through to `schedulers_online`. Either add the field to `Parameters` or drop
the misleading lookup.

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

### 8. Two-stage CA initialization is structural debt
`contradiction_agent.ex:99` (`aborted?`) returns **`true` when `:stats` is
unset** — i.e. before `set_ets_tables` has been called. So a freshly started
CA silently drops every event until the Manager hand-feeds it the ETS table
refs via a synchronous call (`manager.ex:84`).

This couples the lifecycle to an implicit ordering between sibling
supervisor children — exactly the kind of dependency that proper
supervision is meant to make impossible. Worse, the `aborted?` check returns
spurious `:closed`/`:aborted` replies to anyone calling the CA in that
window. The fix is for `CA.init/1` to fetch tables from `EtsKeeper` directly
(it already has `session_id`).

### 9. The `:aborted` flag is dual-purposed
`send_proof_result` sets `:aborted := true` *as part of reporting success*
(`contradiction_agent.ex:543`). The same predicate is then used by both
workers and CA to decide "stop doing things". The code works, but it
conflates "proof finished successfully" with "abort all work in progress",
which obscures intent — e.g. a late reply path returns `:aborted` to a
worker even though the proof completed normally.

### 10. Dead code in the CA message protocol
`contradiction_agent.ex:127, 328`. Three handlers exist for "branch reports
clashes":

- `do_handle_call({:local_clashes, ...})`
- `do_handle_cast({:local_clashes, ...})`
- `do_handle_sync({:local_clashes_sync, ...})`

Only the sync `_sync` variant has callers in the worker. The cast and call
variants are unreachable. Pick one.

### 11. `Map.get` used to access fields with a known schema
- `Map.get(params, :worker_pool_size, ...)` — see #6.
- `Map.get(state.ets_tables, :stats)` — runs on every CA message (see #20).
- `Map.get(state, :current_branch)` in `worker.ex:58` — defensive against a
  field the author guarantees is present.

These hide mistakes of the kind shown in #6. Pattern-match the struct.

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

### 14. `apply_rule({:gamma, ...})` recipe registration
`branch.ex:295`. The first instantiation (`prev == 0`) registers the recipe in
`gamma_recipes` and pushes one instance per existing ground term of the right
type. Subsequent ground terms are discovered via
`enqueue_for_registered_recipes`. Two formulas with the same recipe and type
register independently, generating duplicate work, with no de-duplication.
Worth a comment at least.

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
