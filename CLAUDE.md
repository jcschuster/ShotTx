# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

**ShotTx** is a Church Simple Type Theory (STT) tableau prover written in Elixir. It implements automated theorem proving for higher-order logic (HOL) via a parallel, actor-based refutation search with iterative deepening.

## Commands

```bash
mix deps.get          # Install dependencies
mix compile           # Compile
mix test              # Run tests
mix test test/foo_test.exs:42  # Run single test
mix credo --all       # Lint
mix dialyzer          # Type check (slow on first run)
mix format            # Format code
```

## Architecture

The prover uses a distributed tableau calculus. Proof search is split across concurrent worker processes that operate on immutable branch snapshots, with shared state held in per-session ETS tables.

```
ShotTx.Prover (public API)
  └─ SessionSupervisor (per-proof OTP tree)
       ├─ EtsKeeper        — creates :stats, :tombs, :work_queue, :idle_queue, :traces tables
       ├─ Manager          — spawns N workers, drives iterative deepening, owns the result
       ├─ ContradictionAgent — global closure detection and SAT countermodel extraction
       └─ DynamicSupervisor → Worker × N
                                └─ Branch.step/4  (pure functional core)
```

### Key modules

| Module                             | Role                                                                                                        |
| ---------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| `ShotTx.Prover`                    | Entry point: `prove/1-3`, `sat/2-3`, `prove_string/2-3`                                                     |
| `ShotTx.Prover.Branch`             | Immutable branch state; `step/4` pops the priority queue and applies one rule                               |
| `ShotTx.Prover.Rules`              | Classifies formulas into α/β/γ/δ/prim_subst/atomic rules with costs                                         |
| `ShotTx.Prover.Worker`             | GenServer that loops on `Branch.step/4`, handles `:split`, `:instantiate`, `:closed`, `:idle`, `:saturated` |
| `ShotTx.Prover.Manager`            | Drives iterative deepening; receives worker results; returns final answer                                   |
| `ShotTx.Prover.ContradictionAgent` | Accumulates branch clashes; calls `shot_un` CSP solver; detects global closure                              |
| `ShotTx.Prover.Paramodulation`     | Equation-based term rewriting (naïve; structural equality only)                                             |
| `ShotTx.Proof`                     | Reconstructs proof trees from ETS traces; renders as text or Mermaid                                        |
| `ShotTx.Generation.*`              | Enumerates HOL terms for `gamma_finite` and primitive substitution                                          |
| `ShotTx.Data.Parameters`           | Configuration struct (timeout, gamma/prim limits, cost function, etc.)                                      |

### Proof search algorithm

1. **Tableau rules**: α (linear), β (branching), γ (universal instantiation — reinsertion loop), δ (Skolemization), prim-subst (iterative deepening with general bindings), atomic (clash detection).
2. **Iterative deepening**: Gamma limit and prim-subst depth start at 1 and increment whenever all workers stall.
3. **Closure detection**: Workers detect local (ground) clashes; `ContradictionAgent` checks global closure via unification across all open branches.
4. **SAT exit**: A branch with an empty queue and no sleeping gamma rules is saturated — `ContradictionAgent` extracts a countermodel.

### Branch IDs encode the proof tree

`"root"` → `"root_A"` / `"root_B"` (β-split) → `"root_A_I0"` (prim-subst child). Prefix-check in `:tombs` ETS poisons descendant branches of a closed ancestor.

### Outbox pattern

`Branch.step/4` returns data instructions (`:split`, `:instantiate`, …); the `Worker` executes them. The proof core stays pure and side-effect free.

## Configuration

`ShotTx.Data.Parameters` controls all proof-search knobs:

```elixir
%Parameters{
  timeout: 5_000,
  initial_gamma_limit: 1,
  initial_prim_limit: 1,
  prim_subst_after: 1,
  prim_subst_batch_size: 8,
  unification_depth: 8,
  unfold_defs: :lazy,          # or :eager
  beta_variant: true,
  formula_cost: &Rules.rule_cost/1
}
```

## Dependencies

- **`shot_ds`** — HOL data structures and semantics (external package)
- **`shot_un`** — Unification/CSP solver (external package)

## Livebook examples

Interactive examples and debugging notebooks live in `examples/`. These are the primary test harness while the formal test suite is minimal.

# Claudeman Notifications

You have access to the `notify` command for sending notifications to the host machine.

## Usage

```bash
notify <type> <message>
```

Types: `complete`, `question`, `idle`, `info`

## When to Notify

**Task Completion**: When you finish a significant task or reach a milestone.

```bash
notify complete "Implemented user authentication"
```

**Questions**: When you need clarification and are waiting for user input.

```bash
notify question "Should I use JWT or session-based auth?"
```

**Info**: For non-urgent updates during long-running tasks.

```bash
notify info "Starting test suite..."
```

## Guidelines

- Use `complete` when you've finished what the user asked for
- Use `question` when you're blocked and need user input
- Keep messages concise (the host will announce them via audio)
- Don't over-notify - only for significant events

# CLI Tools

You have the following modern CLI tools available that are to be preferred over the traditional ones:

- `fzf`: a fuzzy-finder
- `rg`: like `grep` but significantly faster
- `ast-grep`: like `grep` but works on abstract syntax trees
- `fd-find`: a faster and more user-friendly alternative to `find`

# Engineering Directives

- **TODO List:** Always show a todo list with your current goals.
- **Minimalism:** Do not overengineer. Use the simplest tool for the job. Favor Elixir's standard library over complex custom abstractions.
- **Architecture:** Follow Clean Architecture principles. Maintain clear boundaries between your core logic and external interfaces (Livebook, Database).

# Elixir Best Practices

- **Strict Immutability:** NEVER rebind a variable name in the same scope. Once `user` is assigned, do not use `user = ...` again.
- **Data Flow:** Use the pipe operator `|>` for all sequential data transformations.
- **Naming:** If you must transform data without a pipe, use descriptive prefixes (e.g., `user` -> `validated_user` -> `saved_user`).
- **Pattern Matching:** Prefer pattern matching in function heads over `if/else` or `cond` blocks.
- **Tooling:** You may use `mix credo --all` and `mix dialyzer` to check code issues.
- **Role:** Assume the role of José Valim and experts in formal logic when writing Elixir code.
- **Simplicity:** Do not overengineer! Code should always be readable and comprehensible.
