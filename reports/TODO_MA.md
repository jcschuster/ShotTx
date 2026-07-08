# ModelAgent — TODO for continuing work

Status snapshot as of the end of the current session. Landed layers pass on
one machine; this list is what a fresh Claude Code session should pick up on
a different machine to reach production quality.

## What's already landed on `model-agent` branch

- **Layer 1** — `%Branch{}` gains `:frontier` + `:frontier_version`; every rule
  that consumes its source updates the frontier, γ/prim_subst deliberately
  don't. `ShotTx.Prover.ModelAgent.Frontier.to_problem/1` projects a branch
  onto `%ShotDs.Data.Problem{}` for `ShotDs.Tptp.unparse_problem/1`. 11 golden
  tests.
- **Layer 2** — `ShotTx.Prover.ModelAgent` GenServer under `SessionSupervisor`
  as CA's peer. `Backend` behaviour + `Backend.Stub`. 6 knobs on `%Parameters{}`.
  Default `model_agent_backend: :none` — no behavior change in existing tests.
  4 passivity tests.
- **Layer 3** — `IsabelleBridge` (application-level singleton, opt-in via
  `config :shot_tx, isabelle_backend: :nitpick`), `Backend.Nitpick` using
  `nitpick[satisfy, user_axioms=true]`. Uses `IsabelleClient.Shared` for
  concurrent probes over one socket. `trap_exit` + `terminate/2` cleans up the
  Isabelle server. Per-bridge scratch dir in `System.tmp_dir!()` holds a copy
  of `TPTP.thy`. Telemetry events. Configurable Nitpick options via
  `opts[:nitpick_opts]`. Task-crash-safe MA via `Task.Supervisor.async_nolink`
  + monitored `{:DOWN, ...}` cleanup. Transient error → retry on next tick. 8
  `@tag :isabelle` integration tests covering SAT / UNSAT / decomposition /
  concurrent probes / higher-order fixtures (γ, δ, equations).

131 default tests, 8 `@isabelle`-tagged integration tests. `mix dialyzer`
clean.

## Files touched / added

**Modified**: `lib/shot_tx/application.ex`, `lib/shot_tx/data/parameters.ex`,
`lib/shot_tx/prover.ex`, `lib/shot_tx/prover/branch.ex`,
`lib/shot_tx/prover/session_supervisor.ex`, `mix.exs`, `mix.lock`,
`test/shot_tx/prover_test.exs` (transitivity flake mitigation),
`test/test_helper.exs` (excludes `:isabelle` tag by default).

**Added**: `lib/shot_tx/isabelle_bridge.ex`,
`lib/shot_tx/prover/model_agent.ex`,
`lib/shot_tx/prover/model_agent/backend.ex`,
`lib/shot_tx/prover/model_agent/backend/{stub,nitpick}.ex`,
`lib/shot_tx/prover/model_agent/frontier.ex`, plus test fixtures under
`test/shot_tx/` and `examples/model_agent.livemd`.

---

## What still needs work, ordered by priority

### 1. Pre-existing flake: `test "transitivity of equality"`

- 4/10 flake rate even with `model_agent_backend: :none`. The prover itself
  hits its own timeout on this problem under back-to-back test load.
- Isolated it: runs in ~0.8s standalone, up to 120s+ under load. Not a Layer 3
  regression — confirmed by disabling `ModelAgent` in `SessionSupervisor` and
  reproducing the same flake rate.
- Current mitigation: `@tag timeout: 300_000` + `timeout: 120_000` on
  `assert_thm` in `test/shot_tx/prover_test.exs:93`.
- Root cause is somewhere in the CSP + rigid unification retry path when the
  BEAM scheduler is under contention. Fix belongs in `ShotUn` or in the
  Manager's iterative-deepening pacing — **out of scope for this branch** but
  blocks CI green-ness.

### 2. Pre-existing flake: `PropSimplify.simplify(t) == t`

- Observed at least once during flake sweeps
  (`test/shot_tx/util/prop_simplify_test.exs:43`).
- Symptom: term-id equality fails (`left: 2563, right: 1667`).
- Suggests a test-ordering dependency in `PropSimplify` or its cache.
- Not Layer 3 either, but worth a fresh look.

### 3. End-to-end race test: MA wins vs CA on a real problem

- I removed the racy Layer 2 test because `p | ~p` closes in CA before MA
  ticks. What's missing: a fixture that *guarantees* MA fires first.
- Approach: set `model_agent_min_delta_ms: 10`, `model_agent_min_frontier: 0`,
  and use a problem where CA cannot saturate quickly (γ-heavy with no clash
  targets, or a HOL problem whose Leibniz expansion is slow enough).
- Assert both:
  - the result is `:csa`
  - the model string contains `"external model finder"`
    (from `format_agent_witness/1`)
- Live under `@tag :isabelle` — needs real Nitpick since AlwaysSat wouldn't
  exercise the terminal payload.

### 4. Multi-session bridge pool

- Currently `IsabelleBridge` holds **one** `IsabelleClient.Shared` client. It
  parallelizes concurrent Elixir callers via Isabelle's task-id demux, but
  Isabelle itself has one polyml session with a bounded thread pool.
- For sustained throughput, spawn N sessions (each with its own polyml
  process). Round-robin dispatch from the bridge. Config knob:
  `config :shot_tx, :isabelle_pool_size, N` (default 1).
- Each session process should trap-exit, own its socket, and terminate its
  Shared client on bridge stop (same cleanup we already have, applied to
  each pool member).
- Impact: high on multi-tenant use, low if you're proving one theorem at a
  time.

### 5. Bridge auto-recovery after crash

- If the Isabelle server dies mid-session (OOM, Nitpick internal panic), the
  bridge's `handle_info({:EXIT, shared, ...})` currently marks status
  `:failed`. Future probes return `{:error, :bridge_failed}` forever until
  the app is restarted.
- Add: after `:failed`, schedule a `:retry_warmup` message with exponential
  backoff. Cap at N retries. Reset status to `:starting` and spawn a fresh
  warmup worker. Same code path we already have for cold start.
- Emit a telemetry event on each restart attempt so operators can dashboard
  "flapping" bridges.

### 6. Structured countermodel extraction

- Nitpick's `:sat` verdict currently ships a raw string in
  `witness.nitpick_output`. Format looks like:

  ```
  Nitpick found a genuine model:
    Type: ...
    Constants:
      p = λx. True
      q = ...
  ```

- Parse this into a structured witness map `%{types: %{}, constants: %{...}}`.
- Motivation: consumers of the `:csa` result can then render the model in the
  Livebook the same way they render CA's model_atoms today.
- Not urgent because the string is already displayed via
  `Prover.format_agent_witness/1`.

### 7. Configurable Nitpick options — expose more knobs

- Currently supported via `opts[:nitpick_opts]`:
  `[timeout, satisfy, user_axioms, card]`.
- Missing but likely wanted for real problems: `mono`, `iter`, `sat_solver`,
  `verbose`, `max_size`, `max_potential`.
- Just extend `Backend.Nitpick.format_opt/1` — it already handles atoms,
  ints, booleans, and strings.
- Consider a `default_nitpick_opts` module attribute in `%Parameters{}` so
  operators can tune globally without editing every call site.

### 8. Verdict conflict detection from the CA side

- I added `verdict_conflict` telemetry in `ModelAgent.maybe_flag_conflict/1`
  — it fires when MA is about to declare `:sat` but `:aborted` is already
  set by someone else.
- The mirror case (CA declares `:unsat` after MA has already declared
  `:sat`) is not detected. `ContradictionAgent.broadcast_unsat/2` blindly
  calls `send_proof_result`.
- Add: same `:aborted` check in `ContradictionAgent.broadcast_unsat/2`.
  Emit `:verdict_conflict` telemetry, `Logger.error` — same shape as MA.
- Under Fitting's soundness this can't fire on a consistent problem; if it
  does, we want the alarm.

### 9. Higher-order integration coverage

The `@isabelle` suite covers propositional, γ, δ, and equations. Not yet
covered:

- **`:instantiate` def carriers** — the `defs` map projection. Verify a
  branch with `defs = %{c => rhs}` emits a valid TPTP `thf(..., definition,
  c = rhs)` and Nitpick handles it.
- **Paramodulation-generated equations** — turn `paramodulation: true` on
  the fixture, add multiple equations, verify Nitpick's model respects them.
- **Rank-1 polymorphism** — problem with a type variable in a constant's
  scheme. TPTP unparser round-trips via `TypeScheme`; Nitpick needs
  `mono=true` to handle it.

### 10. Locale-safe classifier

- Nitpick's output is English-only in practice. But the environment shows
  `bash: warning: setlocale: LC_ALL: cannot change locale (en_US.UTF-8)`.
  If Isabelle ever runs under a non-English locale, `"Nitpick found a
  model"` may not match.
- Fix: use Isabelle's structured message output instead of string parsing.
  `IsabelleClient.Task` returns typed messages — grep for `%{"kind" =>
  "writeln"}` messages containing the model. Look at
  `deps/isabelle_elixir/lib/isabelle_client/result.ex`.

### 11. Bridge init log noise on `:isabelle_backend, :none`

- Even when the bridge isn't started, MA logs at debug for every session.
  Emit info once at app-start (or on first `:nitpick` session) instead of
  per-session.
- Minor operability polish.

### 12. Documentation

- Add a README section explaining:
  - How to enable the Nitpick backend (config + install Isabelle)
  - Available `%Parameters{}` knobs
  - Telemetry event families
  - How to write a custom backend module
- Add a `docs/` guide for the frontier invariant (parent-of-decomposed
  formula excluded from frontier), which is the semantic contract everything
  else builds on.

### 13. Startup latency measurement

- Log elapsed ms from `IsabelleBridge.init/1` to first `:ready` message.
- Confirmed on this sandbox: 8s cold start with prebuilt HOL image, ~30-60s
  otherwise.
- Wire this into telemetry (`[:shot_tx, :isabelle_bridge, :warmup]` with a
  `duration_ms` measurement) so ops can see when the number drifts.

### 14. Livebook example — verify end-to-end

- `examples/model_agent.livemd` walks through `:none`, `:stub`, and
  `:nitpick` modes but the `:nitpick` example is commented out.
- After (3) lands, uncomment and verify the livebook runs a CSA problem
  producing a Nitpick witness.

---

## Quick-start commands on the new machine

```sh
# fetch deps, including the optional isabelle_elixir
mix deps.get

# default test suite (excludes :isabelle)
mix test

# integration suite (requires Isabelle installed + ISABELLE_TOOL exported)
export ISABELLE_TOOL=/path/to/Isabelle2025/bin/isabelle
export PATH=$(dirname $ISABELLE_TOOL):$PATH
mix test --include isabelle test/shot_tx/prover/model_agent/backend/nitpick_test.exs

# verify no dialyzer regressions
mix dialyzer
```

Isabelle 2025 works. Cold start of the HOL image is fast (~8s) if the heap
is prebuilt (`isabelle build -b HOL` — done once at install). Test env keeps
`isabelle_backend: :none` so the default suite doesn't require Isabelle.

## Notes for the next Claude Code session

- The transitivity flake (item 1) is loud but not blocking. Ignore it while
  working on 3–14.
- The `verdict_conflict` telemetry (item 8) is a soundness alarm — if it
  ever fires in real usage, treat as high priority; likely a bug in the
  frontier maintenance or in rule decomposition, not in MA itself.
- If Nitpick behavior looks wrong, sanity-check by running the emitted
  theory body manually in Isabelle/jEdit. The bridge's scratch dir path is
  logged at `[:shot_tx, :isabelle_bridge, :probe, :start]` — grep telemetry
  for it.
- Don't accidentally re-introduce a per-session Isabelle spawn. The bridge
  is **app-level** (see `lib/shot_tx/application.ex:maybe_isabelle_bridge/0`).
  If the bridge appears under `SessionSupervisor`, that's a regression.
