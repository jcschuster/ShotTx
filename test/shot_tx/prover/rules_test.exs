defmodule ShotTx.Prover.RulesTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils
  alias ShotDs.Hol.Definitions
  alias ShotTx.Prover.Rules

  describe "rule_cost/1" do
    test "contradiction is the cheapest" do
      assert Rules.rule_cost(:contradiction) == 0
    end

    test "tautology and atomic cost 1" do
      assert Rules.rule_cost(:tautology) == 1
      assert Rules.rule_cost({:atomic, 42}) == 1
    end

    test "alpha is cheaper than beta" do
      assert Rules.rule_cost({:alpha, [1]}) < Rules.rule_cost({:beta, {1, 2}})
    end

    test "gamma grows with iteration count" do
      assert Rules.rule_cost({:gamma, 1, %ShotDs.Data.Type{goal: :i}, 0}) <
               Rules.rule_cost({:gamma, 1, %ShotDs.Data.Type{goal: :i}, 5})
    end

    test "prim_subst grows with depth and base_offset" do
      progress = %{base_offset: 0, covered_types: MapSet.new()}
      progress2 = %{base_offset: 7, covered_types: MapSet.new()}
      t = %ShotDs.Data.Type{goal: :o}
      assert Rules.rule_cost({:prim_subst, 1, t, 1, progress}) <
               Rules.rule_cost({:prim_subst, 1, t, 1, progress2})

      assert Rules.rule_cost({:prim_subst, 1, t, 1, progress}) <
               Rules.rule_cost({:prim_subst, 1, t, 4, progress})
    end

    test "equality_expansion costs default to iff_o < extensional < leibniz" do
      iff_o = {:equality_expansion, :iff_o, [1]}
      ext = {:equality_expansion, :extensional, [1]}
      leib = {:equality_expansion, :leibniz, [1]}

      assert Rules.rule_cost(iff_o) < Rules.rule_cost(ext)
      assert Rules.rule_cost(ext) < Rules.rule_cost(leib)
    end

    test "leibniz expansion is more expensive than gamma so paramodulation gets first crack" do
      gamma = {:gamma, 1, %ShotDs.Data.Type{goal: :i}, 0}
      leib = {:equality_expansion, :leibniz, [1]}
      assert Rules.rule_cost(gamma) < Rules.rule_cost(leib)
    end

    test "equality_expansion overrides apply per-kind and leave other kinds at default" do
      ext = {:equality_expansion, :extensional, [1]}
      leib = {:equality_expansion, :leibniz, [1]}

      overrides = %{leibniz: 5}
      assert Rules.rule_cost(leib, overrides) == 5
      assert Rules.rule_cost(ext, overrides) == Rules.rule_cost(ext)
    end
  end

  describe "classify_formula/1" do
    test "$true is a tautology" do
      assert Rules.classify_formula(Definitions.true_term()) == :tautology
    end

    test "$false is a contradiction" do
      assert Rules.classify_formula(Definitions.false_term()) == :contradiction
    end

    test "~$true is a contradiction" do
      assert Rules.classify_formula(~f"~ $true") == :contradiction
    end

    test "~$false is a tautology" do
      assert Rules.classify_formula(~f"~ $false") == :tautology
    end

    test "conjunction is an alpha rule" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:alpha, [_, _]} = Rules.classify_formula(~f"p & q")
      end)
    end

    test "disjunction is a beta rule" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:beta, {_, _}} = Rules.classify_formula(~f"p | q")
      end)
    end

    test "implication is a beta rule" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:beta, {_, _}} = Rules.classify_formula(~f"p => q")
      end)
    end

    test "double negation decomposes to its inner formula" do
      ctx = ~e"p: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        p = ~f"p"
        assert {:alpha, [^p]} = Rules.classify_formula(~f"~ ~ p")
      end)
    end

    test "universal over $i is a gamma rule" do
      assert {:gamma, _recipe, %ShotDs.Data.Type{goal: :i}, 0} =
               Rules.classify_formula(~f"![X:$i]: X = X")
    end

    test "universal over $o is gamma_finite" do
      assert {:gamma_finite, _recipe, %ShotDs.Data.Type{goal: :o}} =
               Rules.classify_formula(~f"![P:$o]: P | ~P")
    end

    test "universal over $o falls back to gamma when finite_o_quantification is disabled" do
      assert {:gamma, _recipe, %ShotDs.Data.Type{goal: :o}, 0} =
               Rules.classify_formula(~f"![P:$o]: P | ~P", false)
    end

    test "negated existential over $o falls back to gamma when finite_o_quantification is disabled" do
      assert {:gamma, _recipe, %ShotDs.Data.Type{goal: :o}, 0} =
               Rules.classify_formula(~f"~ ?[P:$o]: P & ~P", false)
    end

    test "existential over $i triggers delta (skolemization)" do
      ctx = ~e"p: $i>$o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:delta, _sk_term} = Rules.classify_formula(~f"?[X:$i]: p @ X")
      end)
    end

    test "reflexive equality is a tautology" do
      ctx = ~e"a: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert Rules.classify_formula(~f"a = a") == :tautology
      end)
    end

    test "negated reflexive equality is a contradiction" do
      ctx = ~e"a: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert Rules.classify_formula(~f"~ (a = a)") == :contradiction
      end)
    end

    test "boolean equality unfolds to equivalence (equality_expansion :iff_o)" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:equality_expansion, :iff_o, [_eqv]} = Rules.classify_formula(~f"p = q")
      end)
    end

    test "equality at a base type classifies as Leibniz expansion" do
      ctx = ~e"a: $i, b: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:equality_expansion, :leibniz, [_]} = Rules.classify_formula(~f"a = b")
      end)
    end

    test "equality at a functional type classifies as extensional expansion" do
      ctx = ~e"f: $i>$i, g: $i>$i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:equality_expansion, :extensional, [_]} = Rules.classify_formula(~f"f = g")
      end)
    end

    test "negated boolean equality classifies as equality_expansion :iff_o" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:equality_expansion, :iff_o, [_]} = Rules.classify_formula(~f"~ (p = q)")
      end)
    end

    test "negated base-type equality classifies as Leibniz expansion" do
      ctx = ~e"a: $i, b: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:equality_expansion, :leibniz, [_]} = Rules.classify_formula(~f"~ (a = b)")
      end)
    end

    test "plain atom classifies as :atomic" do
      ctx = ~e"p: $i>$o, a: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        t = ~f"p @ a"
        assert Rules.classify_formula(t) == {:atomic, t}
      end)
    end

    test "neg_ext: ~(f = g) at arrow type with closed sides produces equality_expansion :extensional with skolem application" do
      ctx = ~e"f: $i>$i, g: $i>$i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        neg_eq = ~f"~ (f = g)"
        assert {:equality_expansion, :extensional, [result]} = Rules.classify_formula(neg_eq)
        formatted = ShotDs.Util.Formatter.format!(result)
        assert formatted =~ "f"
        assert formatted =~ "g"
        assert String.starts_with?(formatted, "¬") or String.contains?(formatted, "¬")
      end)
    end

    test "neg_ext: ~(X = g) at arrow type with free variable sides falls back to extensional equality expansion" do
      ctx = ~e"X: $i>$i, g: $i>$i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        neg_eq = ~f"~ (X = g)"
        assert {:equality_expansion, :extensional, [_]} = Rules.classify_formula(neg_eq)
      end)
    end
  end
end
