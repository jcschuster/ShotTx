defmodule ShotTx.CsaSoundnessTest do
  @moduledoc """
  The mirror image of `ShotTx.SoundnessTest`. Every case here is a *theorem*,
  confirmed by Vampire, E, Zipperposition, Leo-III and Satallax on
  SystemOnTPTP. It may come back `:thm`, `:timeout` or `:unknown` — but
  **never** `:csa`. Claiming a countermodel for a valid conjecture is the
  other soundness signature, and it is the one an empty rule queue invites:
  "no rule left to fire" is not "satisfiable".

  Each case is a regression for a distinct mechanism that used to answer
  `:csa` here. They are run repeatedly because the search is parallel and the
  original bugs surfaced as a race against the branch's own refutation — a
  single passing run proves very little.

  Drawn from `ShotTx.Benchmark.HolSuite`, where they were found.
  """

  use ShotTx.Test.ProverCase

  # Enough repetitions to catch a race that used to land roughly half the time,
  # while keeping the file inside a sane wall-clock budget.
  @repeats 4

  defp refute_csa(id) do
    {:ok, problem} = ShotTx.Benchmark.HolSuite.fetch(id)
    refute_csa_thf(id, problem.thf)
  end

  defp refute_csa_thf(id, thf) do
    parsed = ShotDs.Tptp.parse_tptp_string!(thf)

    verdicts =
      for _ <- 1..@repeats do
        task =
          Task.async(fn ->
            elem(Prover.prove(parsed, timeout: 5_000, progress_interval_ms: 0), 0)
          end)

        case Task.yield(task, 20_000) || Task.shutdown(task, :brutal_kill) do
          {:ok, verdict} -> verdict
          _ -> :hard_killed
        end
      end

    refute :csa in verdicts,
           "SOUNDNESS: prover returned :csa for the theorem #{id} " <>
             "(verdicts across #{@repeats} runs: #{inspect(verdicts)})"

    verdicts
  end

  describe "valid conjectures must never be reported CounterSatisfiable" do
    @tag timeout: 120_000
    test "boolean extensionality, trivial direction (equation queued before it existed)" do
      # An atom queued before an equation arrived was never renormalised under
      # it, so `a` and `¬b` sat on one branch with `b = a` unused.
      assert :thm in refute_csa("bool_ext_trivial_prim")
    end

    @tag timeout: 120_000
    test "extensionality for conjunctions (instantiated defs refuted by own equations)" do
      # `:instantiate` chose `a := ⊤, b := ⊤, C := ⊥` while holding `C = a ∧ b`.
      assert :thm in refute_csa("conj_ext")
    end

    @tag timeout: 120_000
    test "nested boolean argument (asserted equality atom never became a rewrite)" do
      # The branch knew `((h ⊤) = (h ⊥)) = ⊤` but never derived `h ⊤ → h ⊥`.
      assert :thm in refute_csa("nested_bool_prim")
    end

    @tag timeout: 120_000
    test "nested boolean argument, Leibniz-iff" do
      refute_csa("nested_bool_leibniz_iff")
    end

    @tag timeout: 120_000
    test "no boolean fixed point (equation erased its own justification)" do
      # `¬c = c` was ingested as the rewrite `¬c → c` and then used to
      # demodulate its own iff-expansion, turning `(¬c) ≡ c` into `c ≡ c` = ⊤
      # and discarding the contradiction that closes the branch.
      assert :thm in refute_csa("no_bool_fixpoint_prim")
    end

    @tag timeout: 120_000
    test "powerset of the empty set, Leibniz-forward (exhausted is not satisfiable)" do
      # Extensional equality of two closed λ-terms is undecided here, so the
      # honest verdict is `:unknown`, not a countermodel.
      refute_csa("set_powerset_empty_leibniz_imp")
    end

    @tag timeout: 120_000
    test "powerset of the empty set, Leibniz-backward" do
      refute_csa("set_powerset_empty_leibniz_rev_imp")
    end

    @tag timeout: 120_000
    test "powerset of the empty set, Leibniz-iff" do
      refute_csa("set_powerset_empty_leibniz_iff")
    end
  end

  # An `:instantiate` child kept `⊤ → c` next to `c := ⊤`, so demodulation
  # undid every unfolding of `c` and hid the clash.
  describe "TPTP theorems once answered CounterSatisfiable" do
    @tag timeout: 120_000
    test "SYO017^1 — boolean extensionality, Example 18b [BB05]" do
      refute_csa_thf("SYO017^1", """
      thf(h, type, h: $o > $o).
      thf(conj, conjecture, (h @ ((h @ $true) = (h @ $false))) = (h @ $false)).
      """)
    end

    @tag timeout: 120_000
    test "SYO041^2 — no boolean function permutes like this" do
      refute_csa_thf("SYO041^2", """
      thf(f, type, f: $o > $o).
      thf(g, type, g: $o > $o).
      thf(x, type, x: $o).
      thf(y, type, y: $o).
      thf(3, conjecture,
        ~ ((x != y) & ((g @ x) = y) & ((g @ y) = x)
           & ((f @ (f @ (f @ x))) = (g @ (f @ x))))).
      """)
    end
  end
end
