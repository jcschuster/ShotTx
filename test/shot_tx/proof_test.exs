defmodule ShotTx.ProofTest do
  use ShotTx.Test.ProverCase

  describe "from_refutation / rendering" do
    test "empty proof renders to placeholders" do
      assert ShotTx.Proof.to_text(%ShotTx.Proof{}) == "(no proof)\n"
      assert ShotTx.Proof.to_mermaid(%ShotTx.Proof{}) == ""
    end

    test "proof tree carries givens and a closure" do
      proof =
        assert_thm(~p"""
        thf(p_t, type, p: $o).
        thf(ax, axiom, p).
        thf(c, conjecture, p).
        """)

      assert %ShotTx.Proof{root: %ShotTx.Proof.Step{} = root} = proof

      labels = collect_kinds(root)

      assert :given in labels
      assert :closure in labels
    end

    test "to_text and to_mermaid produce non-empty strings" do
      proof = assert_thm(~p"thf(c, conjecture, $true).")
      assert ShotTx.Proof.to_text(proof) =~ ~r/./
      assert ShotTx.Proof.to_mermaid(proof) =~ ~r/./
    end

    test "lambda lifting on a predicate argument is recorded as :lambda_lift" do
      proof =
        assert_thm(~p"""
        thf(p_t, type, p: ($i>$i)>$o).
        thf(c, conjecture, (p @ (^[X:$i]: X)) => (p @ (^[X:$i]: X))).
        """)

      assert :lambda_lift in collect_rules(proof.root)
      assert ShotTx.Proof.to_text(proof) =~ "λ↑"
    end

    test "a rewrite applied on the way into the branch is recorded as :demodulation" do
      proof =
        assert_thm(~p"""
        thf(f_t, type, f: $i>$i).
        thf(g_t, type, g: $i>$i).
        thf(c, conjecture, (f = g) => ![X:$i]: ((f @ X) = (g @ X))).
        """)

      assert :demodulation in collect_rules(proof.root)
      assert ShotTx.Proof.to_text(proof) =~ "demod"
    end

    test "every closure cites the step it closes on" do
      proof =
        assert_thm(~p"""
        thf(f_t, type, f: $i>$i).
        thf(g_t, type, g: $i>$i).
        thf(c, conjecture, (f = g) => ![X:$i]: ((f @ X) = (g @ X))).
        """)

      closures = Enum.filter(collect_steps(proof.root), &(&1.kind == :closure))

      refute Enum.empty?(closures)
      assert Enum.all?(closures, &(&1.sources != []))
    end

    test "every derived step cites the step it was derived from" do
      proof =
        assert_thm(
          ~p"""
          thf(h_type, type, h: $o>$i).
          thf(conj, conjecture, (h @ ((h @ $true) = (h @ $false))) = (h @ $false)).
          """,
          simplification: :none
        )

      derived = Enum.filter(collect_steps(proof.root), &(&1.kind == :rule))

      refute Enum.empty?(derived)
      assert Enum.all?(derived, &(&1.sources != []))
      refute ShotTx.Proof.to_text(proof) =~ "[unfold]"
    end
  end

  defp collect_kinds(%ShotTx.Proof.Step{kind: k, children: cs}) do
    [k | Enum.flat_map(cs, &collect_kinds/1)]
  end

  defp collect_steps(%ShotTx.Proof.Step{children: cs} = step) do
    [step | Enum.flat_map(cs, &collect_steps/1)]
  end

  defp collect_rules(%ShotTx.Proof.Step{rule: r, children: cs}) do
    [r | Enum.flat_map(cs, &collect_rules/1)]
  end
end
