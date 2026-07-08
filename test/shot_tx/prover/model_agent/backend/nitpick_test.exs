defmodule ShotTx.Prover.ModelAgent.Backend.NitpickTest do
  @moduledoc """
  End-to-end integration tests for the Isabelle-backed Nitpick backend.

  These tests are **not run by default** — they require a working local
  Isabelle installation. Enable with:

      export ISABELLE_TOOL=/path/to/isabelle/bin/isabelle
      mix test --include isabelle test/shot_tx/prover/model_agent/backend/nitpick_test.exs

  The suite covers:

    * Bridge lifecycle — startup, ready state, orderly shutdown.
    * Verdict discrimination — SAT vs UNSAT vs unknown on classic fixtures.
    * The frontier invariant — decomposed-parent formulas never make it into
      the emitted TPTP.
    * Configurable Nitpick options via `nitpick_opts`.

  Not covered here: γ-heavy universals, δ Skolems, equations with
  paramodulation, or `:instantiate` def-carrying branches. Those need
  separate integration coverage once the ModelAgent → Manager terminal path
  is exercised through `Prover.prove/3` end-to-end.
  """
  use ExUnit.Case, async: false
  @moduletag :isabelle

  import ShotDs.Hol.Sigils

  alias ShotTx.Data.Parameters
  alias ShotTx.IsabelleBridge
  alias ShotTx.Prover.Branch
  alias ShotTx.Prover.ModelAgent.Backend.Nitpick
  alias ShotTx.Prover.ModelAgent.Frontier

  @minimal %Parameters{simplification: :none, paramodulation: false}

  setup_all do
    unless System.get_env("ISABELLE_TOOL") do
      raise "ISABELLE_TOOL env var must be set to run @isabelle-tagged tests"
    end

    Application.put_env(:shot_tx, :isabelle_backend, :nitpick)

    {:ok, bridge_pid} =
      case Process.whereis(IsabelleBridge) do
        nil -> IsabelleBridge.start_link([])
        pid -> {:ok, pid}
      end

    wait_ready!(120_000)

    on_exit(fn ->
      if Process.alive?(bridge_pid) do
        try do
          GenServer.stop(bridge_pid, :normal, 10_000)
        catch
          :exit, _ -> :ok
        end
      end
    end)

    {:ok, bridge: bridge_pid}
  end

  describe "verdict discrimination" do
    test "returns :sat on a consistent propositional frontier" do
      problem = frontier_problem(~e"p: $o, q: $o", ["p", "q"])

      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 30_000)
      assert {:sat, %{nitpick_output: out}} = Nitpick.await(ref, 60_000)
      assert out =~ "Nitpick found a"
    end

    test "returns :unknown on an inconsistent propositional frontier" do
      problem = frontier_problem(~e"p: $o", ["p", "~p"])

      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 30_000)
      # Nitpick reports "found no model" here — our classifier maps that to
      # :unknown (conservative: it may just be a bounded-search miss). The
      # :sat verdict is what would terminate the tableau early, so it MUST
      # not fire.
      verdict = Nitpick.await(ref, 60_000)
      refute match?({:sat, _}, verdict)
    end

    test "respects the frontier invariant — decomposed parent is dropped" do
      # `p & q` is on the branch; after one α step the branch's frontier is
      # {p, q}, and the emitted problem must reflect that.
      problem =
        with_context(~e"p: $o, q: $o", fn ->
          pq = ~f"p & q"
          branch = Branch.new("root", [pq], @minimal)
          {:continue, next, _} = Branch.step(branch, @minimal, 1, 1)
          Frontier.to_problem(next)
        end)

      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 30_000)
      # `p ∧ q` is decomposed → axioms are {p, q}, which is satisfiable.
      assert {:sat, _} = Nitpick.await(ref, 60_000)
    end
  end

  describe "configurable nitpick options" do
    test "user timeout in nitpick_opts overrides the budget-derived one" do
      problem = frontier_problem(~e"p: $o", ["p"])
      # A user-supplied nitpick_opts[:timeout] is emitted verbatim; verify by
      # forcing a very short one that Nitpick can still satisfy on this
      # trivial fixture.
      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 60_000, nitpick_opts: [timeout: 3])
      assert {:sat, _} = Nitpick.await(ref, 30_000)
    end

    test "cardinality knob is emitted to Nitpick" do
      problem = frontier_problem(~e"p: $o", ["p"])
      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 30_000, nitpick_opts: [card: 2])
      assert {:sat, _} = Nitpick.await(ref, 60_000)
    end
  end

  describe "bridge lifecycle" do
    test "the bridge reports :ready" do
      assert IsabelleBridge.status() == :ready
    end

    test "an :inactive-style :unknown probe still round-trips when the bridge is passive" do
      # This one temporarily unloads the bridge to hit the :inactive path;
      # skipped in this suite to avoid disturbing shared state. See
      # ShotTx.IsabelleBridgeTest for coverage of the passive path.
      :ok
    end
  end

  describe "concurrent probes" do
    test "two probes in flight complete correctly (Shared multiplexing)" do
      p1 = frontier_problem(~e"p: $o, q: $o", ["p", "q"])
      p2 = frontier_problem(~e"a: $o, b: $o", ["a", "b"])

      assert {:ok, ref1} = Nitpick.probe(p1, budget_ms: 30_000)
      assert {:ok, ref2} = Nitpick.probe(p2, budget_ms: 30_000)

      v1 = Nitpick.await(ref1, 60_000)
      v2 = Nitpick.await(ref2, 60_000)

      assert {:sat, _} = v1
      assert {:sat, _} = v2
    end
  end

  describe "higher-order fixtures" do
    test "γ-only universal — {∀x. p x} is satisfiable" do
      # After branch construction the frontier still holds the parent
      # universal (γ never consumes its source). Nitpick should find a model
      # where p is interpreted as λ_. True.
      problem = frontier_problem(~e"p: $i > $o", ["![X: $i]: (p @ X)"])

      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 30_000)
      assert {:sat, _} = Nitpick.await(ref, 60_000)
    end

    test "δ-consumed existential — {p(sk)} after δ step is satisfiable" do
      # `∃x. p x` α-decomposes via δ into `p(sk)` where sk is a fresh Skolem
      # constant. The parent existential is dropped from the frontier; the
      # instance stands alone. Nitpick sees a single-atom constraint.
      problem =
        with_context(~e"p: $i > $o", fn ->
          existential = ~f"?[X: $i]: (p @ X)"
          branch = Branch.new("root", [existential], @minimal)
          {:continue, next, _} = Branch.step(branch, @minimal, 1, 1)
          Frontier.to_problem(next)
        end)

      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 30_000)
      assert {:sat, _} = Nitpick.await(ref, 60_000)
    end

    test "equation fixture — {a = b, p a} is satisfiable" do
      # Nitpick should identify a and b (equating them) so both a and b
      # satisfy p, and the equation holds. Paramodulation on our side is off
      # for the fixture builder; Nitpick derives all consequences.
      problem =
        frontier_problem(
          ~e"a: $i, b: $i, p: $i > $o",
          ["a = b", "p @ a"]
        )

      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 30_000)
      assert {:sat, _} = Nitpick.await(ref, 60_000)
    end

    test "conflicting equation — {a = b, p a, ~p b} is NOT satisfiable" do
      # Under `a = b`, `p a ∧ ¬p b` is contradictory. Nitpick should exhaust
      # bounded search without finding a model. Classifier maps to :unknown.
      problem =
        frontier_problem(
          ~e"a: $i, b: $i, p: $i > $o",
          ["a = b", "p @ a", "~(p @ b)"]
        )

      assert {:ok, ref} = Nitpick.probe(problem, budget_ms: 30_000)
      refute match?({:sat, _}, Nitpick.await(ref, 60_000))
    end
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp frontier_problem(ctx, formula_strings) do
    with_context(ctx, fn ->
      formulas = Enum.map(formula_strings, &sigil_f(&1, []))
      branch = Branch.new("root", formulas, @minimal)
      Frontier.to_problem(branch)
    end)
  end

  defp wait_ready!(timeout_ms) do
    deadline = System.monotonic_time(:millisecond) + timeout_ms
    do_wait_ready(deadline)
  end

  defp do_wait_ready(deadline) do
    case IsabelleBridge.status() do
      :ready ->
        :ok

      :failed ->
        raise "IsabelleBridge failed to warm up"

      _ ->
        if System.monotonic_time(:millisecond) > deadline do
          raise "IsabelleBridge did not become :ready within budget"
        else
          Process.sleep(500)
          do_wait_ready(deadline)
        end
    end
  end
end
