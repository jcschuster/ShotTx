# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
