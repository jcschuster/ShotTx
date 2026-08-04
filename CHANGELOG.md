# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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
