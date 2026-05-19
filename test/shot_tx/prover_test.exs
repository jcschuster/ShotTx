defmodule ShotTx.ProverTest do
  use ShotTx.Test.ProverCase

  describe "trivial cases" do
    test "$true is a theorem" do
      assert_thm(~p"thf(c, conjecture, $true).")
    end

    test "$false is counter-satisfiable" do
      assert_csa(~p"thf(c, conjecture, $false).")
    end

    test "no conjecture in problem returns :error" do
      problem = %ShotDs.Data.Problem{
        path: "memory",
        types: %{},
        definitions: %{},
        axioms: [],
        conjecture: nil
      }

      assert {:error, :no_conjecture} = Prover.prove(problem, timeout: 1_000)
    end
  end

  describe "propositional alpha / beta rules" do
    test "modus ponens" do
      assert_thm(~p"""
      thf(p_t, type, p: $o).
      thf(q_t, type, q: $o).
      thf(ax1, axiom, p).
      thf(ax2, axiom, p => q).
      thf(c, conjecture, q).
      """)
    end

    test "law of excluded middle" do
      assert_thm(~p"""
      thf(p_t, type, p: $o).
      thf(c, conjecture, p | ~p).
      """)
    end

    test "non-contradiction" do
      assert_thm(~p"""
      thf(p_t, type, p: $o).
      thf(c, conjecture, ~(p & ~p)).
      """)
    end

    test "De Morgan: ~(p & q) <=> ~p | ~q" do
      assert_thm(~p"""
      thf(p_t, type, p: $o).
      thf(q_t, type, q: $o).
      thf(c, conjecture, ~(p & q) <=> (~p | ~q)).
      """)
    end

    test "contraposition" do
      assert_thm(~p"""
      thf(p_t, type, p: $o).
      thf(q_t, type, q: $o).
      thf(c, conjecture, (p => q) <=> (~q => ~p)).
      """)
    end

    test "lone atom has a countermodel" do
      assert_csa(~p"""
      thf(p_t, type, p: $o).
      thf(c, conjecture, p).
      """)
    end

    test "p & ~p is unprovable as conjecture (countersatisfiable)" do
      assert_csa(~p"""
      thf(p_t, type, p: $o).
      thf(c, conjecture, p & ~p).
      """)
    end
  end

  describe "first-order gamma / delta" do
    test "reflexivity of equality" do
      assert_thm(~p"thf(c, conjecture, ![X:$i]: X = X).")
    end

    test "symmetry of equality" do
      assert_thm(~p"""
      thf(c, conjecture, ![X:$i, Y:$i]: ( (X = Y) => (Y = X) )).
      """)
    end

    test "transitivity of equality" do
      assert_thm(~p"""
      thf(c, conjecture,
        ![X:$i, Y:$i, Z:$i]: ( ((X = Y) & (Y = Z)) => (X = Z) )
      ).
      """)
    end

    test "congruence under endomorphisms" do
      assert_thm(~p"""
      thf(c, conjecture,
        ![X:$i, Y:$i, F:$i>$i]: ( (X = Y) => ((F @ X) = (F @ Y)) )
      ).
      """)
    end

    test "existential introduction" do
      assert_thm(~p"""
      thf(a_t, type, a: $i).
      thf(p_t, type, p: $i>$o).
      thf(ax, axiom, p @ a).
      thf(c, conjecture, ?[X:$i]: p @ X).
      """)
    end

    test "universal elimination via modus ponens" do
      assert_thm(~p"""
      thf(p_t, type, p: $i>$o).
      thf(q_t, type, q: $i>$o).
      thf(a_t, type, a: $i).
      thf(ax1, axiom, ![X:$i]: ((p @ X) => (q @ X))).
      thf(ax2, axiom, p @ a).
      thf(c, conjecture, q @ a).
      """)
    end

    test "drinker's paradox" do
      assert_thm(
        ~p"""
        thf(p_t, type, p: $i>$o).
        thf(c, conjecture, ?[X:$i]: ((p @ X) => ![Y:$i]: p @ Y)).
        """,
        timeout: 10_000
      )
    end
  end

  describe "definitions / unfolding" do
    test "Leibniz reflexivity" do
      assert_thm(~p"""
      thf(l_t, type, l: $i>$i>$o).
      thf(l_def, definition,
        l = ^[X:$i, Y:$i]: ![P:$i>$o]: ((P @ X) => (P @ Y))
      ).
      thf(c, conjecture, ![X:$i]: l @ X @ X).
      """)
    end

    test "Leibniz symmetry (forward direction)" do
      assert_thm(~p"""
      thf(l_t, type, l: $i>$i>$o).
      thf(l_def, definition,
        l = ^[X:$i, Y:$i]: ![P:$i>$o]: ((P @ X) => (P @ Y))
      ).
      thf(c, conjecture, ![X:$i, Y:$i]: ((l @ X @ Y) => (l @ Y @ X))).
      """)
    end
  end

  describe "format_result strings" do
    test "renders all verdict shapes" do
      assert Prover.format_result({:thm, %ShotTx.Proof{}}) == "THM"
      assert Prover.format_result({:csa, "p", %ShotTx.Proof{}}) =~ "CSA"
      assert Prover.format_result(:unknown) == "UNK"
      assert Prover.format_result({:timeout, %ShotTx.Proof{}}) == "Timeout"
      assert Prover.format_result({:error, :boom}) =~ "Error"
    end
  end

  describe "stats flag" do
    test "returns {result, stats} when :stats is set" do
      problem = ~p"""
      thf(p_t, type, p: $o).
      thf(ax, axiom, p).
      thf(c, conjecture, p).
      """

      assert {{:thm, _proof}, stats} = Prover.prove(problem, timeout: 5_000, stats: true)
      assert is_map(stats) or is_list(stats) or is_tuple(stats) or is_struct(stats)
    end
  end

  describe "proof artefacts" do
    test "proof renders to text and mermaid" do
      proof = assert_thm(~p"thf(c, conjecture, $true).")
      assert is_binary(ShotTx.Proof.to_text(proof))
      assert is_binary(ShotTx.Proof.to_mermaid(proof))
    end
  end
end
