defmodule ShotTx.Prover.ParamodulationTest do
  @moduledoc """
  Tests for the term-DAG utilities that remained in
  `ShotTx.Prover.Paramodulation` after unifying paramodulation was
  removed as unsound under ShotTx's rigid-variable architecture. See
  `ShotTx.Prover.DemodulationTest` for the equational-rewriting tests.
  """

  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils
  alias ShotTx.Prover.Paramodulation
  import ShotDs.Util.Formatter, only: [format!: 1]

  describe "subterms/1" do
    test "an atom is its only subterm" do
      ShotDs.Hol.Sigils.with_context(~e"a: $i", fn ->
        a = ~f"a"
        assert Paramodulation.subterms(a) == MapSet.new([a])
      end)
    end

    test "an applied term includes head args and the whole term" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$i, a: $i", fn ->
        a = ~f"a"
        fa = ~f"f @ a"
        subs = Paramodulation.subterms(fa)

        assert MapSet.member?(subs, fa)
        assert MapSet.member?(subs, a)
      end)
    end
  end

  describe "applied_subterms/1" do
    test "atoms are excluded (no args)" do
      ShotDs.Hol.Sigils.with_context(~e"a: $i", fn ->
        assert MapSet.size(Paramodulation.applied_subterms(~f"a")) == 0
      end)
    end

    test "applied constant-headed terms are included" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$i, a: $i", fn ->
        fa = ~f"f @ a"
        subs = Paramodulation.applied_subterms(fa)
        assert MapSet.member?(subs, fa)
      end)
    end
  end

  describe "replace_subterm/3" do
    test "replacing the whole term yields the replacement" do
      ShotDs.Hol.Sigils.with_context(~e"a: $i, b: $i", fn ->
        a = ~f"a"
        b = ~f"b"
        assert Paramodulation.replace_subterm(a, a, b) == b
      end)
    end

    test "replacing a deep subterm rewrites all matching occurrences" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$i>$o, a: $i, b: $i", fn ->
        a = ~f"a"
        b = ~f"b"
        before = ~f"f @ a @ a"
        result = Paramodulation.replace_subterm(before, a, b)
        assert format!(result) == format!(~f"f @ b @ b")
      end)
    end

    test "non-occurring target leaves the term unchanged" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$i, a: $i, b: $i, c: $i", fn ->
        fa = ~f"f @ a"
        b = ~f"b"
        c = ~f"c"
        assert Paramodulation.replace_subterm(fa, b, c) == fa
      end)
    end
  end
end
