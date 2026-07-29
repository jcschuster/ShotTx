defmodule ShotTx do
  @moduledoc """
  Root module for `ShotTx`, the tableau component of the **Shot**
  ecosystem — a Church Simple Type Theory (STT) automated theorem
  prover. The `Tx` suffix stands for "Tableaux"; sibling packages
  cover the shared data structures (`ShotDs`), higher-order unification
  (`ShotUn`) and term ordering (`ShotTo`).

  Shot performs automated theorem proving for higher-order logic (HOL)
  via a parallel, actor-based refutation search with iterative
  deepening. Proof search is split across concurrent workers that
  operate on immutable branch snapshots, with shared state held in
  per-session ETS tables.

  ## Getting started

  As a library:

      iex> import ShotDs.Hol.Dsl
      iex> {:thm, _proof} = ShotTx.Prover.prove(true_term())

  Load a TPTP problem and let the prover decide it:

      iex> {:ok, problem} = ShotDs.Tptp.Parser.parse_file("problem.p")
      iex> ShotTx.Prover.prove(problem, timeout: 30_000)
      {:thm, %ShotTx.Proof{...}}

  From the command line (after `mix escript.build`):

      $ ./shot_tx --szs problem.p
      % SZS status Theorem for problem.p

  ## Public entry points

    * `ShotTx.Prover`   — `prove/1,2,3`, `sat/1,2,3`, `prove_string/1,2,3`.
    * `ShotTx.Config`   — session-wide defaults for `Parameters`.
    * `ShotTx.Data.Parameters` — the configuration struct.
    * `ShotTx.Proof`    — the reconstructed proof/countermodel tree with
      Mermaid and text renderers.
    * `ShotTx.CLI`      — escript entry point with `--szs` SZS-ontology output.

  See the `README.md` and the module docs above for details.
  """
end
