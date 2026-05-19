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

    test "boolean equality unfolds to equivalence (alpha)" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        assert {:alpha, [_eqv]} = Rules.classify_formula(~f"p = q")
      end)
    end

    test "plain atom classifies as :atomic" do
      ctx = ~e"p: $i>$o, a: $i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        t = ~f"p @ a"
        assert Rules.classify_formula(t) == {:atomic, t}
      end)
    end

    test "neg_ext: ~(f = g) at arrow type with closed sides produces alpha with skolem application" do
      ctx = ~e"f: $i>$i, g: $i>$i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        neg_eq = ~f"~ (f = g)"
        assert {:alpha, [result]} = Rules.classify_formula(neg_eq)
        formatted = ShotDs.Util.Formatter.format!(result)
        assert formatted =~ "f"
        assert formatted =~ "g"
        assert String.starts_with?(formatted, "¬") or String.contains?(formatted, "¬")
      end)
    end

    test "neg_ext: ~(f = g) at arrow type with free variable sides falls back to extensional equality" do
      ctx = ~e"X: $i>$i, g: $i>$i"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        neg_eq = ~f"~ (X = g)"
        assert {:alpha, [_]} = Rules.classify_formula(neg_eq)
      end)
    end
  end
end
