# ShotTx

**Shot** is a Church Simple Type Theory (STT) automated theorem prover.
This package, `ShotTx`, is the **tableau** component of the Shot
ecosystem — the `Tx` suffix reads as "Tableaux". Sibling packages cover
the data structures (`ShotDs`), higher-order unification (`ShotUn`) and
term ordering (`ShotTo`) that the prover builds on.

Shot performs automated theorem proving for higher-order logic (HOL) via
a parallel, actor-based refutation search with iterative deepening,
Skolemisation, primitive substitution, and demodulation.

- Written for a Master's thesis on parallel HOL tableau reasoning.
- Reads TPTP TH0 / TH1 problem files or plain THF formulas.
- Emits either a short human-readable verdict or SZS-ontology status
  lines compatible with the standard prover output format used by
  Vampire, E, Leo-III, etc.
- Runnable both as a library and as a stand-alone escript.

---

## Quick start

### Build

```bash
mix deps.get
mix compile
mix escript.build          # produces the `shot_tx` executable
```

### Solve a problem

```bash
./shot_tx problem.p                  # short output: THM / CSA / UNK / Timeout
./shot_tx --szs problem.p            # SZS status line
./shot_tx --szs --proof problem.p    # + reconstructed proof tree
./shot_tx --szs -t 30000 problem.p   # 30-second wall-clock budget
```

Inline problems and stdin are also accepted:

```bash
./shot_tx "thf(em, conjecture, ! [P: \$o] : (P | ~P))."
echo "P | ~P" | ./shot_tx -
```

### Sample SZS output

```
% SZS status Theorem for PUZ001+1.p
% SZS status CounterSatisfiable for SET001+3.p
% SZS status Timeout for HOL024^4.p
% SZS status GaveUp for LCL083-1.p
```

Exit codes: `0` for `Theorem` / `CounterSatisfiable`, `1` for `GaveUp` /
`Timeout`, `2` for parsing or option errors — matching the convention
used by the CASC prover competitions.

---

## Command-line reference

```
shot_tx [OPTIONS] <FILE | "STRING" | ->
```

| Flag                 | Description                                                        |
| -------------------- | ------------------------------------------------------------------ |
| `--szs`              | Emit `% SZS status <verdict> for <name>`                           |
| `--sat`              | Check satisfiability instead of proving (skip conjecture negation) |
| `--proof`            | Print the reconstructed proof / countermodel                       |
| `--stats`            | Print search statistics after the result                           |
| `-t`, `--timeout MS` | Wall-clock budget (default 5000)                                   |
| `-v`, `--verbose`    | Enable prover debug logging on stderr                              |
| `-h`, `--help`       | Show the full option listing                                       |

All fields of `ShotTx.Data.Parameters` are exposed as long flags in
kebab-case; boolean parameters accept `--flag` / `--no-flag`. For the
authoritative list run `./shot_tx --help` or see the
`ShotTx.Data.Parameters` module docs.

---

## Library usage

```elixir
import ShotDs.Hol.Sigils
alias ShotDs.Tptp
alias ShotTx.Prover

# Prove a THF formula directly (no axioms).
Prover.prove(~f"![P : $o]: (P | ~P)")
#=> {:thm, %ShotTx.Proof{...}}

# Parse and prove a TPTP problem.
{:ok, problem} = Tptp.parse_tptp_file("PUZ001+1.p", :tptp_problem)
Prover.prove(problem, timeout: 30_000)

# Ask for satisfiability instead.
Prover.sat(problem_formulas, definitions, timeout: 10_000)
```

Session-wide defaults can be set with `ShotTx.Config`:

```elixir
ShotTx.Config.configure(timeout: 30_000, suggestions_enabled: true)
Prover.prove(problem)                       # uses the globals
Prover.prove(problem, [], timeout: 1_000)   # per-call still wins
```

See `ShotTx.Prover` for the full public API and `ShotTx.Proof` for
proof-tree inspection (text / Mermaid renderers).

---

## Architecture

The prover implements a distributed tableau calculus. Proof search is
split across concurrent worker processes that operate on immutable
branch snapshots, with shared state held in per-session ETS tables.

```
ShotTx.Prover (public API)
  └─ SessionSupervisor (per-proof OTP tree)
       ├─ EtsKeeper           — owns :stats, :tombs, :work_queue, :idle_queue,
       │                        :idle_workers, :traces, :provenance, :suggestions
       ├─ Manager             — spawns N workers, drives iterative
       │                        deepening, owns the result
       ├─ ContradictionAgent  — global closure via unification CSP
       ├─ SuggestionAgent     — instantiation hints from local clashes
       ├─ ModelAgent          — optional Nitpick-backed model finder
       └─ DynamicSupervisor → Worker × N
                                └─ Branch.step/4  (pure functional core)
```

- **Tableau rules**: α (linear), β (branching), γ / γ-finite
  (universal instantiation with reinsertion), δ (Skolemisation),
  primitive substitution (iterative deepening on general bindings),
  atomic clash detection, equality expansion (o-type iff / extensional /
  Leibniz), demodulation (binding-free equational rewriting).
- **Iterative deepening**: γ-limit and prim-subst depth start at 1 and
  grow whenever all workers stall.
- **Global closure**: `ContradictionAgent` unifies clashes across every
  open branch through the `shot_un` CSP.
- **SAT exit**: a branch with an empty queue and no sleeping γ-rules is
  saturated; the agent extracts a countermodel.

See the `ShotTx.Prover.*` module documentation for the details of every
component. Rendered docs are produced by `mix docs`.

---

## Configuration

All proof-search knobs live in the `ShotTx.Data.Parameters` struct. The
common ones:

| Field                    | Default              | Purpose                                                 |
| ------------------------ | -------------------- | ------------------------------------------------------- |
| `timeout`                | `5_000`              | Wall-clock ms before returning `:timeout`               |
| `initial_gamma_limit`    | `1`                  | Starting γ-rule instantiation depth                     |
| `initial_prim_limit`     | `1`                  | Starting primitive-substitution binding depth           |
| `unfold_defs`            | `:lazy`              | `:eager` unfolds definitions immediately                |
| `demodulation`           | `true`               | Binding-free equational rewriting (forward + backward)  |
| `equivalence_processing` | `:bidirectional_imp` | `↔` expansion mode: `:same_polarity`, `:bidirectional_imp`, or `:dual` |
| `contradiction_agent`    | `true`               | Enable global CSP-based closure                         |
| `worker_pool_size`       | `:auto`              | `System.schedulers_online()`                            |
| `iterative_deepening`    | `true`               | Whether to bump limits when workers stall               |
| `formula_cost_strategy`  | `:default`           | `:default`, `:uniform`, `:depth_first`, `{:custom, fn}` |

The full table (with all 33 fields) is in
`ShotTx.Data.Parameters`'s moduledoc. The soundness argument for why
ShotTx does binding-free demodulation instead of classical paramodulation
lives in `ShotTx.Prover.Paramodulation`'s moduledoc — the rigid-variable
tableau architecture requires that free-variable commitments be
reconciled globally by `ContradictionAgent`, not locally by a rewrite
rule.

---

## Testing and quality

```bash
mix test
mix credo --all
mix dialyzer
mix format
```

Interactive examples live in `examples/` as Livebook notebooks; they are
the primary test harness while the formal test suite grows.

An ablation-study driver over the TPTP TH0 / TH1 corpus is included:

```bash
export TPTP_ROOT=/path/to/TPTP
./scripts/run_ablation.sh
```

The full sweep is a multi-day run, so validate the corpus first with a
short pass — a TPTP-version mismatch surfaces as `parser_error` rows:

```bash
PROBLEM_LIMIT=20 ./scripts/run_ablation.sh smoke_results
grep -c parser_error smoke_results/baseline.csv
```

Parsing and proving each run under a hard wall-clock budget
(`PARSE_TIMEOUT`, default 60s; `BASE_TIMEOUT + PROVE_GRACE` for the proof
attempt), so no single problem can stall the sweep — a few TPTP problems
pull in enough `include`s to keep the parser busy for many minutes. A
killed phase still yields a CSV row (`parse_timeout` / `hard_timeout`),
and unparsable problems are recorded in `<output_dir>/parse_cache` so
later configurations replay the verdict instead of re-parsing.

See `ShotTx.Benchmark.Ablation` and `ShotTx.Benchmark.TptpRunner` for
the sweep matrix and per-problem CSV format.

---

## Dependencies

- [`shot_ds`](https://github.com/jcschuster/ShotDs) — HOL data
  structures, term factory, TPTP / THF parser, semantics.
- [`shot_un`](https://hex.pm/packages/shot_un) — higher-order
  unification and CSP solver.
- [`shot_to`](https://hex.pm/packages/shot_to) — NCPO term ordering.
- [`isabelle_elixir`](https://hex.pm/packages/isabelle_elixir)
  (optional) — enables the `ShotTx.Prover.ModelAgent.Backend.Nitpick`
  backend.

---

## License

See `LICENSE`.
