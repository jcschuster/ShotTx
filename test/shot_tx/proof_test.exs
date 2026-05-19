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
  end

  defp collect_kinds(%ShotTx.Proof.Step{kind: k, children: cs}) do
    [k | Enum.flat_map(cs, &collect_kinds/1)]
  end
end
