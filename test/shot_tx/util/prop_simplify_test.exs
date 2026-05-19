defmodule ShotTx.Util.PropSimplifyTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils
  alias ShotDs.Hol.Definitions
  alias ShotTx.Util.PropSimplify

  describe "tautology / contradiction detection" do
    test "p | ~p simplifies to $true" do
      ctx = ~e"p: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert PropSimplify.simplify(~f"p | ~p") == Definitions.true_term()
      end)
    end

    test "p & ~p simplifies to $false" do
      ctx = ~e"p: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert PropSimplify.simplify(~f"p & ~p") == Definitions.false_term()
      end)
    end

    test "(p => q) | (q => p) simplifies to $true" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert PropSimplify.simplify(~f"(p => q) | (q => p)") == Definitions.true_term()
      end)
    end

    test "p & (~p | q) & ~q simplifies to $false" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert PropSimplify.simplify(~f"p & (~p | q) & ~q") == Definitions.false_term()
      end)
    end
  end

  describe "non-tautological terms are left alone" do
    test "p | q stays p | q" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        t = ~f"p | q"
        assert PropSimplify.simplify(t) == t
      end)
    end

    test "shallow mode does not look under quantifier bodies" do
      tid = ~f"![X:$i]: (X = X)"
      assert PropSimplify.simplify(tid, :shallow) == tid
    end
  end

  describe "deep mode" do
    test "deep mode simplifies body of a quantifier when body is a tautology" do
      ctx = ~e"p: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        # ∀ X:i. (p ∨ ¬p)  has a tautological body, so deep mode rewrites the
        # body to $true.
        t = ~f"![X:$i]: (p | ~p)"
        simplified = PropSimplify.simplify(t, :deep)
        refute simplified == t
      end)
    end
  end
end
