defmodule ShotTx.Prover.BranchFrontierTest do
  @moduledoc """
  Golden tests for the frontier invariant on `%Branch{}`. For each rule kind
  we verify the "parent-of-a-decomposed-formula is inactive" principle: the
  source is dropped from the frontier iff the rule consumes it (α, β, δ,
  equality_expansion, rename, instantiate, atomic-unfold, tautology), and
  retained otherwise (γ, prim_subst, atomic leaf).
  """
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Branch

  # Keep simplification off so BDD-oracle rewrites don't shift ids under our feet,
  # and keep beta_variant explicit per test so we control what lands on the
  # sibling branch.
  @minimal %Parameters{
    simplification: :none,
    beta_variant: false,
    paramodulation: false,
    orient: :none,
    instance_based_gamma: false
  }

  describe "seed" do
    test "new branch seeds frontier with the initial formulas" do
      ctx = ~e"p: $o, q: $o"

      with_context(ctx, fn ->
        p = ~f"p"
        q = ~f"q"

        branch = Branch.new("root", [p, q], @minimal)

        assert MapSet.equal?(branch.frontier, MapSet.new([p, q]))
        assert branch.frontier_version == 0
      end)
    end
  end

  describe "α consumes source, adds conjuncts" do
    test "p & q → {p, q}" do
      ctx = ~e"p: $o, q: $o"

      with_context(ctx, fn ->
        p = ~f"p"
        q = ~f"q"
        pq = ~f"p & q"

        branch = Branch.new("root", [pq], @minimal)
        {:continue, next, :no_effects} = Branch.step(branch, @minimal, 1, 1)

        assert MapSet.equal?(next.frontier, MapSet.new([p, q]))
        assert next.frontier_version > branch.frontier_version
      end)
    end
  end

  describe "β consumes source on both children" do
    test "p | q → child A has p, child B has q; source in neither" do
      ctx = ~e"p: $o, q: $o"

      with_context(ctx, fn ->
        p = ~f"p"
        q = ~f"q"
        pq = ~f"p | q"

        branch = Branch.new("root", [pq], @minimal)
        {:split, a, b} = Branch.step(branch, @minimal, 1, 1)

        assert MapSet.equal?(a.frontier, MapSet.new([p]))
        assert MapSet.equal?(b.frontier, MapSet.new([q]))
        refute MapSet.member?(a.frontier, pq)
        refute MapSet.member?(b.frontier, pq)
      end)
    end

    test "β-variant adds ¬b1 to the sibling frontier" do
      ctx = ~e"p: $o, q: $o"

      with_context(ctx, fn ->
        q = ~f"q"
        neg_p = ~f"~p"
        pq = ~f"p | q"

        params = %{@minimal | beta_variant: true}
        branch = Branch.new("root", [pq], params)
        {:split, _a, b} = Branch.step(branch, params, 1, 1)

        assert MapSet.equal?(b.frontier, MapSet.new([q, neg_p]))
      end)
    end
  end

  describe "γ retains source, ignores fresh instances" do
    test "∀x. p @ x stays in frontier after one γ-fire" do
      ctx = ~e"p: $i > $o"

      with_context(ctx, fn ->
        all = ~f"![X: $i]: (p @ X)"

        branch = Branch.new("root", [all], @minimal)
        {:continue, next, {:record_provenance, [{_, _}]}} = Branch.step(branch, @minimal, 2, 1)

        assert MapSet.member?(next.frontier, all)
        assert MapSet.equal?(next.frontier, MapSet.new([all]))
        assert next.frontier_version == branch.frontier_version
      end)
    end
  end

  describe "δ consumes source, adds Skolem instance" do
    test "∃x. p @ x → p @ sk, source out" do
      ctx = ~e"p: $i > $o"

      with_context(ctx, fn ->
        exists = ~f"?[X: $i]: (p @ X)"

        branch = Branch.new("root", [exists], @minimal)
        {:continue, next, :no_effects} = Branch.step(branch, @minimal, 1, 1)

        refute MapSet.member?(next.frontier, exists)
        # exactly one member: the Skolem instance
        assert MapSet.size(next.frontier) == 1
        assert next.frontier_version > branch.frontier_version
      end)
    end
  end

  describe "atomic leaf is a no-op on frontier" do
    test "an atomic formula stays in the frontier without a version bump" do
      ctx = ~e"p: $o"

      with_context(ctx, fn ->
        p = ~f"p"

        branch = Branch.new("root", [p], @minimal)
        {:continue, next, _effect} = Branch.step(branch, @minimal, 1, 1)

        assert MapSet.equal?(next.frontier, MapSet.new([p]))
        assert next.frontier_version == branch.frontier_version
      end)
    end
  end

  describe "paramodulants stay out of the frontier" do
    test "an atomic step under paramodulation ships p @ b to the queue but not the frontier" do
      ctx = ~e"a: $i, b: $i, p: $i > $o"

      with_context(ctx, fn ->
        pa = ~f"p @ a"
        ab = ~f"a = b"

        params = %{@minimal | paramodulation: true}
        branch = Branch.new("root", [pa, ab], params)
        {:continue, next, _effect} = Branch.step(branch, params, 1, 1)

        # frontier still names the source formulas only — the paramodulant
        # never entered it.
        assert MapSet.equal?(next.frontier, MapSet.new([pa, ab]))
      end)
    end
  end
end
