# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.5] - 2026-10-26

### Changed

- Defaults: `unfold_defs: :eager` (was `:lazy`) and `beta_variant: false`
  (was `true`); likewise for the CLI's `--unfold-defs` and `--[no-]beta-variant`.

### Fixed

- Soundness: demodulation no longer uses an equation whose side is a
  λ-abstracted connective (e.g. `λx. ¬x`) as a rewrite rule. Such a rule
  rewrote every negation on the branch, which erased closing literals and
  produced a wrong `CounterSatisfiable` for SYO376^5.

## [0.1.4] - 2026-10-25

### Changed

- CLI: `--proof` prints the derivation tree in an SZS `Proof` output block
  (`Model` for a countermodel), lines no longer `%`-prefixed; `Comment` is gone.

## [0.1.3] - 2026-10-25

The SystemOnTPTP / StarExec release: `Shot---0.1.3`, listed for `TH0_NAR`.

### Added

- CLI `--cpu-timeout MS`: bounds the CPU time of the whole VM (all threads
  summed) and reports `Timeout` when it runs out; SystemOnTPTP limits are CPU
  seconds. Without `-t` it doubles as the wall-clock limit.
- StarExec entry point `bin/starexec_run_default` (reads `$1` and
  `$STAREXEC_WALLCLOCK_LIMIT`) and `starexec_description.txt`; the
  `Containerfile` also emits `Shot---<version>-starexec.tgz` with `bin/` at the
  archive root.
- Release workflow (`.github/workflows/release.yml`): on a `v*` tag, runs the
  Containerfile's smoke test and attaches the packages to the GitHub release.

### Changed

- CLI: internal errors are reported as `GaveUp` with the reason after ` : `;
  the `Error` status is gone.
- CLI: problems using `$ite` are rejected as `Inappropriate` — the prover would
  treat it as an uninterpreted constant, which is sound for proofs but not for
  models.
- `bin/shot` disables crash dumps and core files so a killed run leaves
  nothing in the working directory.
- `Containerfile` defaults target Ubuntu 24.04 (glibc 2.39), the SystemOnTPTP
  host.

### Removed

- `reports/`. The system description now lives in the README; the thesis is
  at <https://github.com/jcschuster/shot-thesis>.

## [0.1.2] - 2026-10-19

The version prepared for SystemOnTPTP. The version described in the Master's
thesis is 0.1.1 (DOI 10.5281/zenodo.23044601).

### Added

- `ShotTx.Prover.refute/2`: runs the tableau on a formula set as given and
  returns a proof or model like `prove/3`.
- `pure_o_models_only` parameter (default `true`, CLI `--[no-]pure-o-models-only`).
- `ShotTx.Config.tptp_root/0`: `$TPTP`, falling back to `$TPTP_ROOT`.
- Self-contained release (`mix release`, `bin/shot` wrapper) and a
  `Containerfile` that packages it as `Shot---<version>.tgz`. The package
  bundles `libsctp`, without which ERTS prints a warning on stdout, and writes
  UTF-8 whatever the locale.
- CLI SZS statuses `Satisfiable`, `Unsatisfiable`, `Incomplete`, `Forced`,
  `Inappropriate`, `InputError` and `UsageError`.

### Changed

- **Countermodels are conservative.** A saturated branch is reported as a model
  only for pure-`o` problems; otherwise the result is `{:unknown, reason}`
  (`GaveUp`). Set
  `pure_o_models_only: false` for the old behaviour.
- `prove/3` and `refute/2` return `{:unknown, reason}` instead of `:unknown`.
- CLI: `--version` prints `Shot---<version>`.
- CLI: timeouts are reported as `WCTimeout`; `-t` bounds the whole run (VM
  start, parsing, search, proof reconstruction).
- CLI: `--proof` output is a single SZS `Comment` block with every line
  prefixed by `% `; countermodels print the model first. Sat mode now renders
  proofs and models too.
- CLI: problems without a conjecture are checked for satisfiability.
- CLI: log output goes to stderr, so stdout carries only the result.
- CLI: includes are resolved against the problem's own directory first, then
  `$TPTP` / `$TPTP_ROOT`.
- Benchmark tooling accepts `$TPTP` as well as `$TPTP_ROOT`.
- Code comments trimmed.

### Fixed

- Wrong `CounterSatisfiable` answers for the TPTP theorems `SYO017^1` and
  `SYO041^2`, from three interacting defects:
  - an `:instantiate` child kept rewrites mentioning the constant it had just
    defined (`⊤ → c` next to `c := ⊤`), so demodulation undid every unfolding.
    Branch definitions are now unfolded inside equations;
  - the default precedence could orient `⊤ = t` as `⊤ → t`. `⊤` and `⊥` now rank
    below every other constant (`TermOrder.default_precedence/1`);
  - `⊤ = ⊥` was never evaluated, so `:rename` abbreviated it instead.
    `PropSimplify` now evaluates `=` between truth values.
- `.gitignore` entry for the escript no longer hides `lib/shot_tx/` and
  `test/shot_tx/` from tools such as `rg` and `fd`.
- Without a UTF-8 locale the escript printed proofs in latin1 (`¬` as a raw
  byte, `⊥` as `\x{22A5}`). Its stdout is now UTF-8 regardless of the locale.

## [0.1.1] - 2026-09-29

### Added

- Citation metadata: `CITATION.cff` and `.zenodo.json` for archiving releases on Zenodo; no functional changes.

## [0.1.0] - 2026-08-18

### Added

- README section on the two operational properties that surprise callers:
  verdicts near the timeout are not reproducible, because a worker pool races
  on a shared queue under a wall-clock budget; and the node-wide `:term_pool`
  accumulates every term the node has seen until
  `ShotTx.Prover.release_term_pool/0` clears it.

### Changed

- Dependencies bumped to `shot_ds` 1.3.1, `shot_un` 0.2.1 and `shot_to` 0.2.0.
- Clearer `gamma_finite` labels; harder parse timeouts and a parse bug report.
- Ablation-study driver improvements and the in-flight CSP counter.

### Fixed

- Demodulation rewrote connectives unsoundly.
- Unsound models reported as `CounterSatisfiable`.
- Unreliable termination and timeouts.
- Resource leaks.
- Parentless nodes in the proof-tree rendering.
- The README and `ShotTx.Config` documented `Prover.prove(problem, [], opts)`,
  which raises `FunctionClauseError`. A `ShotDs.Data.Problem` is proved
  through `prove/2`.
- An unclosed code fence in the README swallowed the License section.

## [0.0.3] - 2026-08-09

Supersedes the unreleased 0.0.2; entries cover everything since 0.0.1.

### Added

- `ShotTx.Benchmark.HolSuite` and `HolRunner`: 130 higher-order problems as
  canonical THF, one fresh BEAM per problem, CSV-scored.
- `scripts/run_hol_benchmark.sh` and `scripts/hol_problem.exs` — resumable,
  with a `STOP` sentinel.
- Global configuration options on `ShotTx.Data.Parameters` (worker pool size,
  ablation switches for the contradiction and suggestion agents).

### Changed

- Demodulation is restricted to **ground** equations. Rewriting with an
  equation carrying rigid γ-variables destroys the literal pair the CSP needs.
- An exhausted rule queue is no longer reported as a countermodel.
  `Branch.model_certain?/2` requires each same-head, opposite-polarity literal
  pair to be separated by two distinct rigid base-type terms; otherwise the
  branch is `:exhausted` and the session answers `:unknown`.
- `suggestions_enabled` and `prim_subst_after` now default to `true` and `1`.

### Fixed

- Unsound `CounterSatisfiable` on seven problems, from formulas queued before
  an equation arrived never being re-normalised under it.
- Crash during proof reconstruction on `:demodulation` traces.
- Two type errors that killed branches mid-search: prim-subst instantiation
  paired a head declaration with an instance typed by the applied term, and
  the suggestion agent published hints ill-typed against their recipe.
- Iterative deepening stalled permanently once any branch saturated.
- The manager's settle call was unbounded, so the timeout stopped applying.

## [0.0.1] - 2026-08-04

Initial pre-release. API is unstable; expect breaking changes before 0.1.0.

### Added

- Parallel, actor-based tableau refutation search for higher-order logic
  (Church Simple Type Theory).
- `ShotTx.Prover` public API: `prove/1,2,3`, `sat/1,2,3`, `prove_string/1,2,3`.
- Iterative deepening over the γ-limit and primitive-substitution depth.
- Global closure detection and SAT countermodel extraction via
  `ShotTx.Prover.ContradictionAgent`.
- Ordered paramodulation with an NCPO-LNF term order
  (Niederhauser & Middeldorp, 2025).
- TPTP TH0 / TH1 problem-file input; SZS-ontology output.
- `ShotTx.Cli` escript entry point with `--szs` flag.
- Proof reconstruction with text and Mermaid renderers.
- `ShotTx.Benchmark.TptpRunner` for resumable, CSV-scored TPTP sweeps.
