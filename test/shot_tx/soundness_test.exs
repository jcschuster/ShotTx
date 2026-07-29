defmodule ShotTx.SoundnessTest do
  @moduledoc """
  Soundness regression. Every case here is a *non-theorem*: it may be
  proved `:csa` (countersatisfiable), left `:timeout`, or returned as
  `:unknown` — but **never** `:thm`. A `:thm` verdict is the classical
  soundness signature (the prover claims a false statement is true) and
  should fail loudly.

  Cases drawn from `examples/structured_hol_problems.livemd` §
  Non-Theorems plus canonical simple non-theorems.
  """

  use ShotTx.Test.ProverCase

  @leibniz1 """
  thf(leibniz_t, type, l: A > A > $o).
  thf(leibniz_def, definition,
    l = ^[X, Y]: ![P]: P @ X => P @ Y
  ).
  """

  @leibniz2 """
  thf(leibniz_t, type, l: A > A > $o).
  thf(leibniz_def, definition,
    l = ^[X, Y]: ![P]: P @ X <= P @ Y
  ).
  """

  @leibniz3 """
  thf(leibniz_t, type, l: A > A > $o).
  thf(leibniz_def, definition,
    l = ^[X, Y]: ![P]: P @ X <=> P @ Y
  ).
  """

  @andrews """
  thf(andrews_t, type, a: A > A > $o).
  thf(andrews_def, definition,
    a = ^[X, Y]: ![Q]: ((![Z]: Q @ Z @ Z) => Q @ X @ Y)
  ).
  """

  @extensional """
  thf(extensional_t, type, e: (A>B) > (A>B) > $o).
  thf(extensional_def, definition,
    e = ^[X, Y]: ![Z]: X @ Z = Y @ Z
  ).
  """

  # Runs `prove` in an isolated Task with a hard wall-clock cap so a slow
  # CSP call inside the ContradictionAgent cannot make one non-theorem
  # dominate the whole suite. Verdict `:thm` is the soundness signal;
  # everything else (including hard-kill) is acceptable.
  defp verdict_within!(problem, prover_timeout_ms, wall_ms) do
    task =
      Task.async(fn ->
        elem(Prover.prove(problem, timeout: prover_timeout_ms, progress_interval_ms: 0), 0)
      end)

    case Task.yield(task, wall_ms) || Task.shutdown(task, :brutal_kill) do
      {:ok, verdict} -> verdict
      _ -> :hard_killed
    end
  end

  defp assert_not_theorem(problem) do
    verdict = verdict_within!(problem, 2_000, 4_000)
    refute verdict == :thm, "SOUNDNESS: prover returned :thm for a non-theorem"
    verdict
  end

  describe "Non-Theorems from structured_hol_problems.livemd" do
    @tag timeout: 10_000
    test "drinker-variant-1 (∃X∀Y qXY ∨ ∃U∀V ¬qVU)" do
      assert_not_theorem(~p"""
      thf(q_type, type, q : $i>$i>$o).
      thf(conj, conjecture,
        (?[X:$i]: ![Y: $i]: q @ X @ Y) | (?[U:$i]: ![V:$i]: ~ (q @ V @ U))
      ).
      """)
    end

    @tag timeout: 10_000
    test "quantifier-shuffle" do
      assert_not_theorem(~p"""
      thf(q_type, type, q: $i>$i>$o).
      thf(conj, conjecture,
        ?[Y:$i]: ![X:$i]: ( (![Z:$i]: q @ X @ Z) | ~(q @ X @ Y) )
      ).
      """)
    end

    @tag timeout: 10_000
    test "F has a fixpoint (bare equality)" do
      assert_not_theorem(~p"""
      thf(conj, conjecture,
        ![F:$i>$i]: ?[X:$i]: F @ X = X
      ).
      """)
    end

    @tag timeout: 10_000
    test "F has a fixpoint (Leibniz-forward)" do
      assert_not_theorem(~p"""
      #{@leibniz1}
      thf(conj, conjecture,
        ![F:$i>$i]: ?[X:$i]: l @ (F @ X) @ X
      ).
      """)
    end

    @tag timeout: 10_000
    test "F has a fixpoint (Leibniz-backward)" do
      assert_not_theorem(~p"""
      #{@leibniz2}
      thf(conj, conjecture,
        ![F:$i>$i]: ?[X:$i]: l @ (F @ X) @ X
      ).
      """)
    end

    @tag timeout: 10_000
    test "F has a fixpoint (Leibniz-iff)" do
      assert_not_theorem(~p"""
      #{@leibniz3}
      thf(conj, conjecture,
        ![F:$i>$i]: ?[X:$i]: l @ (F @ X) @ X
      ).
      """)
    end

    @tag timeout: 10_000
    test "F has a fixpoint (Andrews)" do
      assert_not_theorem(~p"""
      #{@andrews}
      thf(conj, conjecture,
        ![F:$i>$i]: ?[X:$i]: a @ (F @ X) @ X
      ).
      """)
    end

    @tag timeout: 10_000
    test "F has a fixpoint (extensional)" do
      assert_not_theorem(~p"""
      #{@extensional}
      thf(conj, conjecture,
        ![F:($i>$i)>$i>$i]: ?[X:$i>$i]: e @ (F @ X) @ X
      ).
      """)
    end
  end

  describe "Canonical simple non-theorems" do
    test "bare atom p" do
      assert :csa =
               verdict_within!(
                 ~p"""
                 thf(p_t, type, p: $o).
                 thf(conj, conjecture, p).
                 """,
                 2_000,
                 4_000
               )
    end

    test "contradiction p ∧ ¬p as conjecture" do
      assert :csa =
               verdict_within!(
                 ~p"""
                 thf(p_t, type, p: $o).
                 thf(conj, conjecture, p & ~p).
                 """,
                 2_000,
                 4_000
               )
    end

    test "$false as conjecture" do
      assert :csa = verdict_within!(~p"thf(conj, conjecture, $false).", 2_000, 4_000)
    end

    test "a = b for two distinct base constants" do
      assert :csa =
               verdict_within!(
                 ~p"""
                 thf(a_t, type, a: $i).
                 thf(b_t, type, b: $i).
                 thf(conj, conjecture, a = b).
                 """,
                 2_000,
                 4_000
               )
    end

    test "unwarranted p ⇒ q" do
      assert :csa =
               verdict_within!(
                 ~p"""
                 thf(p_t, type, p: $o).
                 thf(q_t, type, q: $o).
                 thf(conj, conjecture, p => q).
                 """,
                 2_000,
                 4_000
               )
    end
  end
end
