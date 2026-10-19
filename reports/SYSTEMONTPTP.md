# Shot on SystemOnTPTP — readiness and system description

**Basis.** ShotTx 0.1.2 (changes since v0.1.1, the thesis version, in `CHANGELOG.md`),
ShotDs 1.3.1 (unchanged), the SZS ontology BNF
(`TPTPWorld/SZSOntologies`, `BNF/SZSOntology.bnf`), the CASC-30 design document and the
TPTP system-building conventions. Unless marked otherwise, every item below was run on
x86_64 Linux (Debian trixie, glibc 2.41, 8 cores) against TPTP v9.3.1.

---

## 1. Decisions

1. SZS values are taken from `BNF/SZSOntology.bnf`.
2. Proofs are emitted as TPTP comment lines in a `Comment` output block; the
   `ShotTx.Proof.to_text/1` rendering, Unicode included, is kept unchanged.
3. Models are emitted the same way, the model line first.
4. Countermodels are reported only for pure-*o* problems (decided at input level);
   otherwise the answer is `GaveUp`. Shot is a prover, not a model finder: missing
   models are acceptable, wrong ones are not. The gate is library-wide, switchable with
   `pure_o_models_only`.
5. Parse errors (including non-THF input) yield `Inappropriate`; missing files and
   unresolvable includes yield `InputError`; bad options yield `UsageError`.
6. `$TPTP`, when set, overrides `$TPTP_ROOT`.
7. Wall-clock timeouts are reported as `WCTimeout`; an exhausted search space as
   `Incomplete`; termination by SIGTERM as `Forced`.
8. The system is called `Shot---0.1.2`; `bin/shot -V` prints that string.
9. ShotDs stays unchanged; the CLI works around its limitations (§3, B4).
10. `ModelAgent` stays off (`model_agent_backend: :none`).

**Pure-*o*.** A type is pure-*o* iff its goal is `o` and every argument type is pure-*o*
(`ShotTx.Prover.Rules.pure_o_type?/1`). A problem is pure-*o* iff every type in
`TypeUniverse.from_formulas/1` over its formulas and definition bodies is pure-*o*.

---

## 2. Output contract

| Situation | Status line | Exit | Output block (`--proof`) |
|---|---|---|---|
| Conjecture, tableau closed | `Theorem` | 0 | `Comment`: proof tree |
| Conjecture, saturated branch, pure-*o* | `CounterSatisfiable` | 0 | `Comment`: model, then open branch |
| No conjecture, tableau closed | `Unsatisfiable` | 0 | `Comment`: proof tree |
| No conjecture, saturated branch, pure-*o* | `Satisfiable` | 0 | `Comment`: model, then open branch |
| Search space exhausted, no model | `Incomplete` | 1 | — |
| Saturated branch, not pure-*o*; other give-ups | `GaveUp` | 1 | — |
| Deadline reached | `WCTimeout` | 1 | — |
| SIGTERM | `Forced` | 1 | — |
| Parse failure, non-THF input | `Inappropriate` | 2 | — |
| Missing file, unresolvable include, empty input | `InputError` | 2 | — |
| Bad command-line option | `UsageError` (stdout with `--szs`; message also on stderr) | 2 | — |
| Internal error | `Error` | 2 | — |

```
% SZS status Theorem for SYO002^1.p
% SZS output start Comment for SYO002^1.p
% 1. ...
% SZS output end Comment for SYO002^1.p
```

Failure lines carry the reason after ` : ` on the same line. Every other stdout line is a
`%` comment; logging goes to stderr.

Proposed command line: `bin/shot --szs --proof -t %d000 %s` (limit in seconds → ms).

---

## 3. Checklist

### Blockers

- [x] **B1 — Self-contained package.** `mix release` with `include_erts: true`;
  `rel/overlays/bin/shot` starts it (`eval`, distribution off, `+fnu`). `Containerfile`
  builds it, runs a smoke test on a base image without Erlang (`--target check`), and
  exports `Shot---0.1.2.tgz` (`--target dist`). The source archive is a `git archive`
  one-liner in the Containerfile header.
  The package bundles `libsctp.so.1`: ERTS `dlopen`s it at boot and, where it is
  missing, prints `=ESOCK WARNING MSG` on **stdout** (`esock_warning_msg` in OTP's
  `socket_util.c`). `bin/shot` puts `lib/` on `LD_LIBRARY_PATH` and sets
  `-kernel standard_io_encoding unicode`, since without a locale the BEAM writes
  latin1 (`¬` as a raw byte, `⊥` as `\x{22A5}`); the escript gets the same flag.
  *Caveats:* built on the default (trixie) image, the package needs glibc ≥ 2.38
  (`beam.smp`, `erl_child_setup`, `inet_gethost`), plus `libtinfo6`, `zlib1g` and
  `libstdc++6`, which Debian base images include. For an older server, build with an
  older `BUILDER` image (see the Containerfile header).

- [x] **B2 — Conservative countermodels.** `Prover.sat/3` maps every `{:sat, _}` of a
  non-pure-*o* problem to `{:unknown, :saturation_not_pure_o}`. Pure-*o* models still
  come only from a saturated branch that passes `Branch.model_certain?/2` and that the
  ContradictionAgent cannot close; their soundness rests on B3.

- [x] **B3 — Soundness at HEAD.** Three defects, all fixed in the calculus:
  1. *Stale rewrites after `:instantiate`.* `:rename` introduces `c = h ⊥`; a child sets
     `c := ⊤` but kept the rewrite `h ⊥ → c`, so the unfolded `⊤ = h ⊥` became the
     rewrite `⊤ → c`, and demodulation undid every unfolding of `c` — the clash
     `h ⊥` / `¬h ⊥` was never seen. Fix (`Branch`): equations are stored with branch
     definitions unfolded, and a new definition replaces the rewrites that mention its
     constant.
  2. *Rewrites away from truth values.* The hash precedence could rank `⊤` above `h`, so
     `⊤ = h ⊥` was oriented `⊤ → h ⊥`; every unfolded `⊤` became `h ⊥` again and
     `:rename` abbreviated it afresh, forever. Fix (`TermOrder.default_precedence/1`):
     `⊤` and `⊥` rank below all other constants (`⊤ > ⊥`, so `h ⊤ = h ⊥` still orients).
  3. *Unevaluated `⊤ = ⊥`.* The simplifier treated `=` as an atom, so `h (⊤ = ⊥)` was
     renamed instead of simplified to `h ⊥`, and the rename rewrote every later
     `⊤ = ⊥` to a constant that could then be set to `⊤`. Fix (`PropSimplify`): `=`
     between two truth values is evaluated.

  Release build, 6 runs each at `-t 10000`: `SYO017^1`, `SYO041^2`, `SEU541^2`,
  `SYO345^5` 6 Theorem; `SYO040^2` 6 Incomplete. The former failures are regular tests
  in `test/shot_tx/csa_soundness_test.exs`. Full sweep: §4.

- [x] **B4 — Environment variables and includes** (CLI workarounds; ShotDs unchanged).
  `ShotTx.Config.tptp_root/0` returns `$TPTP || $TPTP_ROOT` and exports the result as
  `$TPTP_ROOT`, which is what ShotDs reads. Before parsing a file, the CLI sets
  `$TPTP_ROOT` to the file's directory if every `include` of the file exists there
  (CASC: including file's directory first). Limitation: an included file's own includes
  are resolved against the same root.

### Important for review

- [x] **I1 — Parse errors → `Inappropriate`.** ShotDs returns plain strings; the CLI maps
  `"Could not read…"` / `"TPTP_ROOT environment variable…"` to `InputError` and
  everything else to `Inappropriate`.
- [x] **I2 — Proofs and models as comments.** One `Comment` block, every line prefixed
  with `% `, model first for CSA/SAT; sat mode renders through `Prover.refute/2`.
- [x] **I3 — Problems without a conjecture** take the sat path (`Satisfiable` /
  `Unsatisfiable`).
- [x] **I4 — The time limit covers the whole run.** Measured from VM start; the search
  gets `t − max(10 %, 500 ms)`, the rest is a hard `Task.yield` deadline that prints
  `WCTimeout`. Measured: `-t 3000` → 2.7 s wall clock with the release.
  *Caveat:* "VM start" is `:erlang.statistics(:wall_clock)`, which misses the shell
  scripts and `erlexec` before the emulator, and the halt after the status line. When
  the hard deadline fires, the process exits up to 121 ms past `-t` (sweep, §4.3:
  1785 of 4321 `WCTimeout` runs over 2000 ms). Every decided answer came in by
  1734 ms, so only `WCTimeout` lines are at risk from a harness that kills at the limit.
- [x] **I5 — Clean stdout.** The Logger handler writes to stderr.

### Detail corrections

- [x] **D1 — Non-ASCII in comments.** Kept (decision 2).
- [x] **D2 — Naming.** `Shot---0.1.2`: `-V` output, package and top directory name.
  The executables are `bin/shot` (release) and `shot_tx` (escript).
- [x] **D3 — README.** THF examples, status/exit-code table, CASC claim removed.
- [x] **D4 — `WCTimeout`.**

### Optional

- [x] **O1 — ModelAgent.** Off by default (`:none`), unchanged. If enabled, its models
  pass through the B2 gate too.
- [x] **O2 — `Incomplete`** for `{:unknown, :exhausted_without_model}`. To carry the
  reason, `prove/3` and `refute/2` now return `{:unknown, reason}` instead of `:unknown`.
- [x] **O3 — `UsageError`** line on stdout (with `--szs`) plus the stderr message.
- [x] **O4 — Benchmark tooling** (`tptp_runner.ex`, `scripts/ca_probe.exs`,
  `scripts/run_ablation.sh`) accepts `$TPTP`, with precedence over `$TPTP_ROOT`.

---

## 4. Verification

1. **Release without Erlang on the host** — `podman build --target check` and
   `--target dist -o dist` pass (podman 5.4.2, default build args). The first run of
   `check` failed: the CounterSatisfiable assertion missed because the ESOCK warning
   came first on stdout, and the proof printed in latin1. Both fixed (B1); `check` now
   also asserts that `⊥` survives, on an image with no locale and no `libsctp`.
2. **B3 problems** — see B3.
3. **THF sweep** — release build, `--szs -t 2000 --worker-pool-size 2`, 4 problems in
   parallel, TPTP v9.3.1. Every run printed exactly one status line.
   - *Before the B3 calculus fixes* (all 5279 problems, model check in place of the fixes):
     zero disagreements with the problem status; 652 Theorem, 6 Unsatisfiable,
     5 CounterSatisfiable, 1 Satisfiable, 188 Inappropriate, 4356 WCTimeout.
   - *With the B3 fixes* (stopped after 1877 problems in alphabetical order, up to `KRS`): **zero disagreements**; 36 Theorem (35 Theorem, 1 ContradictoryAxioms),
     1 Incomplete, 1 GaveUp, 105 Inappropriate, 1734 WCTimeout. On the same problems
     the earlier build proved 32 (5 gained, 1 lost to a timeout).
   - *Full sweep, 0.1.2* (all 5279 problems; the `dist` package; `--szs --proof
     -t 2000 --worker-pool-size 2` in an empty environment, i.e. no locale; 16 cores):
     **zero disagreements**. 683 Theorem (681 Theorem, 2 ContradictoryAxioms),
     8 Unsatisfiable, 6 CounterSatisfiable, 1 Satisfiable — all matching the problem
     status; 63 GaveUp, every one on a CounterSatisfiable (55) or Satisfiable (8)
     problem, i.e. models withheld by the pure-*o* gate; 6 Incomplete (3 Theorem,
     1 Unsatisfiable, 2 CounterSatisfiable); 191 Inappropriate, all ShotDs parse or
     type errors; 4321 WCTimeout. Exactly one status line per run, exit code as in §2,
     nothing on stderr, every stdout line a `%` comment in valid UTF-8, and exactly one
     `Comment` block per decided answer. On the 1877-problem prefix: 44 Theorem,
     1 Incomplete, 1 GaveUp, 105 Inappropriate, 1726 WCTimeout — more theorems than
     above, but on twice the cores. Only 2 workers per problem, so the counts are a
     lower bound.

4. **Clean stdout** — the `check` stage asserts that every non-status line starts with
   `%`; spot-checked with `--proof` on theorems and countermodels.
5. **Includes** — `SYO044^1` (includes `Axioms/…`) proves with only `$TPTP`, with only
   `$TPTP_ROOT`, and gives `InputError` with neither; a problem including a file from its
   own directory proves without either variable.
6. **Signals** — sent to the PID started by `bin/shot` (which execs into `beam.smp`).
   `SIGALRM`: the VM dies at once (exit 142). `SIGXCPU`: dies after the core-dump default
   action (exit 152). `SIGTERM`: prints `Forced`, exit 1. No `beam.smp`,
   `erl_child_setup` or `epmd` is left behind in any case.

---

## 5. System description

> **Shot---0.1.2**
> Johannes Schuster
> University of Bamberg, Germany
>
> Shot is a free-variable tableau prover for Church's simple type theory (TH0, partial
> TH1), written in Elixir. Branch rules never bind free variables; each branch records
> the literal pairs that could close it, and one process searches for a single
> substitution closing all open branches by higher-order pre-unification. A pool of
> worker processes expands branches in parallel. Quantifiers are instantiated with fresh
> variables, ground terms from the branch and general bindings (primitive substitution),
> under iterative deepening; quantifiers over Boolean types are expanded exhaustively.
> Equations are used for ordered demodulation.
>
> Countermodels are reported only from saturated branches of problems whose types are all
> Boolean. Proofs are printed as a TPTP comment block; no TSTP derivation is produced.
>
> Source (MIT): <https://github.com/jcschuster/ShotTx>, DOI 10.5281/zenodo.23044599.

---

## Sources

- SZS ontologies BNF: <https://github.com/TPTPWorld/SZSOntologies/blob/master/BNF/SZSOntology.bnf>
- CASC-30 design: <https://tptp.org/CASC/30/Design.html>
- TPTP system-building conventions: <https://tptp.org/Proposals/SystemBuild.html>
- SystemOnTPTP: <https://tptp.org/cgi-bin/SystemOnTPTP>
