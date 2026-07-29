defmodule ShotTx.Prover.ModelAgent.FrontierTest do
  @moduledoc """
  Confirms that a `Branch`'s frontier projects cleanly to a
  `ShotDs.Data.Problem` and round-trips through `ShotDs.Tptp.unparse_problem/1`.
  """
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils

  alias ShotDs.Data.Problem
  alias ShotDs.Tptp
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Branch
  alias ShotTx.Prover.ModelAgent.Frontier

  @minimal %Parameters{simplification: :none, demodulation: false, orient: :none}

  test "to_problem/1 emits axioms for every frontier member" do
    ctx = ~e"p: $o, q: $o"

    with_context(ctx, fn ->
      p = ~f"p"
      q = ~f"q"

      branch = Branch.new("root", [p, q], @minimal)
      %Problem{axioms: axioms, conjecture: nil, definitions: defs} = Frontier.to_problem(branch)

      ax_ids = Enum.map(axioms, fn {_name, id} -> id end)
      assert Enum.sort(ax_ids) == Enum.sort([p, q])
      assert defs == %{}
    end)
  end

  test "to_problem/1 output round-trips through the TPTP unparser" do
    ctx = ~e"p: $o, q: $o, r: $o"

    with_context(ctx, fn ->
      p = ~f"p"
      pq = ~f"p | q"
      r = ~f"r"

      branch = Branch.new("root_A", [p, pq, r], @minimal)
      problem = Frontier.to_problem(branch)

      assert {:ok, tptp_str} = Tptp.unparse_problem(problem)
      assert tptp_str =~ "thf(a_1, axiom"
      # every constant used has its own type declaration
      assert tptp_str =~ "p: $o"
      assert tptp_str =~ "q: $o"
      assert tptp_str =~ "r: $o"
      # this is a satisfiability probe — never emits a conjecture
      refute tptp_str =~ "conjecture"
    end)
  end

  test "α-decomposed source disappears from the emitted TPTP" do
    ctx = ~e"p: $o, q: $o"

    with_context(ctx, fn ->
      p = ~f"p"
      q = ~f"q"
      pq = ~f"p & q"

      branch = Branch.new("root", [pq], @minimal)
      {:continue, next, _} = Branch.step(branch, @minimal, 1, 1)
      %Problem{axioms: axioms} = Frontier.to_problem(next)

      ax_ids = Enum.map(axioms, fn {_, id} -> id end)
      refute pq in ax_ids
      assert p in ax_ids
      assert q in ax_ids
    end)
  end
end
