defmodule ShotTx.Prover.ParamodulationTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils
  alias ShotTx.Prover.Paramodulation
  import ShotDs.Util.Formatter, only: [format!: 1]

  describe "subterms/1" do
    test "an atom is its only subterm" do
      ctx = ~e"a: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        a = ~f"a"
        assert Paramodulation.subterms(a) == MapSet.new([a])
      end)
    end

    test "an applied term includes head args and the whole term" do
      ctx = ~e"f: $i>$i, a: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        a = ~f"a"
        fa = ~f"f @ a"
        subs = Paramodulation.subterms(fa)

        assert MapSet.member?(subs, fa)
        assert MapSet.member?(subs, a)
      end)
    end
  end

  describe "replace_subterm/3" do
    test "replacing the whole term yields the replacement" do
      ctx = ~e"a: $i, b: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        a = ~f"a"
        b = ~f"b"
        assert Paramodulation.replace_subterm(a, a, b) == b
      end)
    end

    test "replacing a deep subterm rewrites all matching occurrences" do
      ctx = ~e"f: $i>$i>$o, a: $i, b: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        a = ~f"a"
        b = ~f"b"
        before = ~f"f @ a @ a"
        result = Paramodulation.replace_subterm(before, a, b)
        # IDs may differ due to metadata rebuilding; compare formatted output.
        assert format!(result) == format!(~f"f @ b @ b")
      end)
    end

    test "non-occurring target leaves the term unchanged" do
      ctx = ~e"f: $i>$i, a: $i, b: $i, c: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        fa = ~f"f @ a"
        b = ~f"b"
        c = ~f"c"
        assert Paramodulation.replace_subterm(fa, b, c) == fa
      end)
    end
  end

  describe "paramodulants/2" do
    test "empty equation map yields no paramodulants" do
      ctx = ~e"f: $i>$i, a: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert Paramodulation.paramodulants(~f"f @ a", %{}) == []
      end)
    end

    test "a single equation rewrites a matching subterm" do
      ctx = ~e"p: $i>$o, a: $i, b: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        a = ~f"a"
        b = ~f"b"
        pa = ~f"p @ a"
        pb = ~f"p @ b"
        equations = %{a => MapSet.new([b])}
        assert [result] = Paramodulation.paramodulants(pa, equations)
        assert format!(result) == format!(pb)
      end)
    end

    test "non-matching equation produces no rewrite" do
      ctx = ~e"p: $i>$o, a: $i, c: $i, d: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        c = ~f"c"
        d = ~f"d"
        pa = ~f"p @ a"
        equations = %{c => MapSet.new([d])}
        assert Paramodulation.paramodulants(pa, equations) == []
      end)
    end
  end
end
