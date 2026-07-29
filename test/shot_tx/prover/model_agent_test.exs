defmodule ShotTx.Prover.ModelAgentTest do
  @moduledoc """
  Exercises the ModelAgent plumbing without any external dependency. The
  agent should:

    * start with every session but stay entirely passive when
      `model_agent_backend: :none` — no ticks, no probes.
    * tick under `:stub` without emitting a proof result, since the stub
      always returns `:unknown`.
    * never interfere with the existing CA-driven prove/2 pipeline.
  """
  use ShotTx.Test.ProverCase

  describe "with model_agent_backend: :none (default)" do
    test "existing theorem-proving path still works" do
      assert_thm(~p"""
      thf(p_t, type, p: $o).
      thf(c, conjecture, p | ~p).
      """)
    end

    test "existing CSA path still works" do
      assert_csa(~p"""
      thf(p_t, type, p: $o).
      thf(c, conjecture, p).
      """)
    end
  end

  describe "with model_agent_backend: :stub" do
    test "the agent scans but never terminates the search" do
      assert_thm(
        ~p"""
        thf(p_t, type, p: $o).
        thf(c, conjecture, p | ~p).
        """,
        model_agent_backend: :stub,
        model_agent_min_delta_ms: 50
      )
    end

    test "CSA still comes from ContradictionAgent — MA stays silent" do
      {model, _proof} =
        assert_csa(
          ~p"""
          thf(p_t, type, p: $o).
          thf(c, conjecture, p).
          """,
          model_agent_backend: :stub,
          model_agent_min_delta_ms: 50
        )

      refute model =~ "external model finder"
    end
  end
end
