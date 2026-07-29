defmodule ShotTx.Prover.DemodulationTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils
  alias ShotTo.Parameters, as: ShotToParams
  alias ShotTx.Prover.Demodulation
  import ShotDs.Util.Formatter, only: [format!: 1]

  # Precedence helper: names in decreasing order (first is greatest).
  defp order(names) do
    ShotToParams.from_precedence_list(Enum.map(names, &List.wrap/1))
  end

  describe "normalize/3 — subterm matching" do
    test "empty equation map is identity" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$i, a: $i", fn ->
        fa = ~f"f @ a"
        assert Demodulation.normalize(fa, %{}, order(["f", "a"])) == fa
      end)
    end

    test "ground equation rewrites a matching subterm" do
      ShotDs.Hol.Sigils.with_context(~e"p: $i>$o, a: $i, b: $i", fn ->
        a = ~f"a"
        b = ~f"b"
        pa = ~f"p @ a"
        pb = ~f"p @ b"

        equations = %{a => MapSet.new([b])}
        assert format!(Demodulation.normalize(pa, equations, order(["a", "b"]))) == format!(pb)
      end)
    end

    test "universally-quantified LHS is NOT applied to a differing subterm" do
      # Under the rigid-variable architecture, a rewrite that would
      # require binding a variable (here `X ↦ a` to match `f(X)` against
      # `f(a)`) is deliberately not performed at the branch level. The
      # ContradictionAgent owns σ-commitment globally; branch rules must
      # not pre-empt it. The literal is left unchanged; the Leibniz
      # backstop handles equational reasoning that requires bindings.
      ShotDs.Hol.Sigils.with_context(~e"X: $i, f: $i>$i, p: $i>$o, a: $i, b: $i", fn ->
        fx = ~f"f @ X"
        b = ~f"b"
        equations = %{fx => MapSet.new([b])}
        literal = ~f"p @ (f @ a)"

        ord = order(["f", "a", "b"])
        assert Demodulation.normalize(literal, equations, ord) == literal
      end)
    end

    test "reduces to fixpoint through multiple rewrites" do
      # Transitivity setup: sc1 → sc2, sc3 → sc2. Literal `~(sc1 = sc3)`.
      # Both sides normalize to sc2, giving `~(sc2 = sc2)`.
      ShotDs.Hol.Sigils.with_context(~e"sc1: $i, sc2: $i, sc3: $i", fn ->
        equations = %{
          ~f"sc1" => MapSet.new([~f"sc2"]),
          ~f"sc3" => MapSet.new([~f"sc2"])
        }

        literal = ~f"~(sc1 = sc3)"
        ord = order(["sc1", "sc3", "sc2"])

        normal = Demodulation.normalize(literal, equations, ord)
        assert format!(normal) == format!(~f"~(sc2 = sc2)")
      end)
    end

    test "normalize is idempotent" do
      ShotDs.Hol.Sigils.with_context(~e"p: $i>$o, a: $i, b: $i, c: $i", fn ->
        equations = %{~f"a" => MapSet.new([~f"b"]), ~f"b" => MapSet.new([~f"c"])}
        literal = ~f"p @ a"
        ord = order(["a", "b", "c"])

        once = Demodulation.normalize(literal, equations, ord)
        twice = Demodulation.normalize(once, equations, ord)
        assert once == twice
      end)
    end

    test "post-σ NCPO check blocks σ that inverts orientation" do
      ShotDs.Hol.Sigils.with_context(~e"X: $i, f: $i>$i, p: $i>$o, a: $i, b: $i", fn ->
        # Equation `f(X) = a`. Under a precedence that puts `a` above the
        # potential concrete instance `f(b)`, the ground rewrite would
        # be UP the order and must be blocked.
        fx = ~f"f @ X"
        a = ~f"a"
        equations = %{fx => MapSet.new([a])}
        literal = ~f"p @ (f @ b)"

        # `a` ranked highest so `f(b) < a` in NCPO — blocking.
        blocking = order(["a", "f", "b"])
        assert Demodulation.normalize(literal, equations, blocking) == literal
      end)
    end

    test "equation NCPO-LNF cannot orient is silently ignored" do
      # Permissive defaults leave `a` and `b` incomparable.
      ShotDs.Hol.Sigils.with_context(~e"p: $i>$o, a: $i, b: $i", fn ->
        equations = %{~f"a" => MapSet.new([~f"b"])}
        pa = ~f"p @ a"

        assert Demodulation.normalize(pa, equations, %ShotToParams{}) == pa
      end)
    end
  end

  describe "normalize/3 — head-position (η-expansion) rewriting" do
    test "head equation f = g rewrites f(a) to g(a)" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$o, g: $i>$o, a: $i", fn ->
        f = ~f"f"
        g = ~f"g"
        equations = %{f => MapSet.new([g])}
        fa = ~f"f @ a"
        ga = ~f"g @ a"

        ord = order(["f", "g", "a"])
        assert format!(Demodulation.normalize(fa, equations, ord)) == format!(ga)
      end)
    end

    test "head equation rewrites under a propositional context" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$o, g: $i>$o, a: $i", fn ->
        equations = %{~f"f" => MapSet.new([~f"g"])}
        not_fa = ~f"~(f @ a)"
        not_ga = ~f"~(g @ a)"

        ord = order(["f", "g", "a"])
        assert format!(Demodulation.normalize(not_fa, equations, ord)) == format!(not_ga)
      end)
    end

    test "binary head equation rewrites at every shared occurrence" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$i>$o, g: $i>$i>$o, a: $i, b: $i", fn ->
        equations = %{~f"f" => MapSet.new([~f"g"])}
        fab = ~f"f @ a @ b"
        gab = ~f"g @ a @ b"

        ord = order(["f", "g", "a", "b"])
        assert format!(Demodulation.normalize(fab, equations, ord)) == format!(gab)
      end)
    end

    test "head equation with non-matching head is a no-op" do
      ShotDs.Hol.Sigils.with_context(~e"f: $i>$o, g: $i>$o, h: $i>$o, a: $i", fn ->
        equations = %{~f"f" => MapSet.new([~f"g"])}
        ha = ~f"h @ a"

        ord = order(["f", "g", "h", "a"])
        assert Demodulation.normalize(ha, equations, ord) == ha
      end)
    end
  end

  describe "termination invariant" do
    test "rewriting under a non-terminating-looking equation set still halts" do
      # `a → b` and `b → c` chain. Should terminate at `p(c)`.
      ShotDs.Hol.Sigils.with_context(~e"p: $i>$o, a: $i, b: $i, c: $i", fn ->
        equations = %{
          ~f"a" => MapSet.new([~f"b"]),
          ~f"b" => MapSet.new([~f"c"])
        }

        ord = order(["a", "b", "c"])

        # If the loop did not terminate this test would hang.
        assert format!(Demodulation.normalize(~f"p @ a", equations, ord)) == format!(~f"p @ c")
      end)
    end

    test "cycle-like equations that NCPO does not orient both ways cannot loop" do
      # `a → b` oriented, but the reverse `b → a` would also be present
      # if the ordering were symmetric. Ordering guarantees only one
      # direction is used.
      ShotDs.Hol.Sigils.with_context(~e"p: $i>$o, a: $i, b: $i", fn ->
        equations = %{
          ~f"a" => MapSet.new([~f"b"]),
          # Backward direction: strict_gt?(b, a) is FALSE under `a > b`
          # precedence, so this equation is inert.
          ~f"b" => MapSet.new([~f"a"])
        }

        ord = order(["a", "b"])

        # First rewrite: p(a) → p(b). Second attempt: `b → a` blocked by
        # the post-σ NCPO check (`strict_gt?(b, a)` is false).
        assert format!(Demodulation.normalize(~f"p @ a", equations, ord)) == format!(~f"p @ b")
      end)
    end
  end
end
