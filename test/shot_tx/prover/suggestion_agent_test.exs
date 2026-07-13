defmodule ShotTx.Prover.SuggestionAgentTest do
  @moduledoc """
  Unit tests for the SuggestionAgent stub. Verifies:

    * passive mode (`suggestions_enabled: false`) skips subscription and
      state accumulation, so no work is done;
    * active mode maintains `active_branches` / `clashing_local_pairs` as
      raw evidence arrives on the `branch_evidence_<session>` topic.

  Publication and worker splicing are the concern of Step 4 tests and are
  not asserted here.
  """
  use ExUnit.Case, async: false

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.{EtsKeeper, SuggestionAgent}

  # Each test needs a private session_id so its ETS tables, Registry entries,
  # and process names don't collide with sibling tests.
  setup do
    session_id = "sa-test-#{System.unique_integer([:positive])}"
    {:ok, session_id: session_id}
  end

  describe "passive mode (suggestions_enabled: false)" do
    test "starts without subscribing to branch_evidence topic",
         %{session_id: session_id} do
      params = %Parameters{suggestions_enabled: false}
      pid = start_sa!(session_id, params)

      state = :sys.get_state(pid)
      assert state.ets_tables == %{}
      assert state.active_branches == MapSet.new(["root"])

      # No subscribers on the topic — the fanout is a no-op.
      subscribers = Registry.lookup(ShotTx.Prover.PubSub, "branch_evidence_#{session_id}")
      assert subscribers == []
    end

    test "ignores every event without mutating state",
         %{session_id: session_id} do
      params = %Parameters{suggestions_enabled: false}
      pid = start_sa!(session_id, params)

      before = :sys.get_state(pid)

      send(pid, {:branch_split, "root", ["root_A", "root_B"]})
      send(pid, {:local_clashes, "root_A", MapSet.new([{1, 2}])})
      send(pid, {:branch_closed, "root_A"})
      # sync round-trip so all above messages have been processed
      _ = :sys.get_state(pid)

      assert :sys.get_state(pid) == before
    end
  end

  describe "active mode (suggestions_enabled: true)" do
    setup %{session_id: session_id} do
      start_supervised!({EtsKeeper, {session_id, %Parameters{}}})
      :ok
    end

    test "subscribes to branch_evidence_<session>", %{session_id: session_id} do
      params = %Parameters{suggestions_enabled: true}
      pid = start_sa!(session_id, params)

      subscribers = Registry.lookup(ShotTx.Prover.PubSub, "branch_evidence_#{session_id}")
      assert [{^pid, _}] = subscribers
    end

    test "tracks active_branches through split → closed lifecycle",
         %{session_id: session_id} do
      params = %Parameters{suggestions_enabled: true}
      pid = start_sa!(session_id, params)

      send(pid, {:branch_split, "root", ["root_A", "root_B"]})
      _ = :sys.get_state(pid)

      assert :sys.get_state(pid).active_branches ==
               MapSet.new(["root_A", "root_B"])

      send(pid, {:branch_closed, "root_A"})
      _ = :sys.get_state(pid)

      assert :sys.get_state(pid).active_branches == MapSet.new(["root_B"])
    end

    test "accumulates clash pairs per branch (no unifier on synthetic ids)",
         %{session_id: session_id} do
      # Term ids 1 and 2 aren't real terms in the pool; ShotUn.unify will
      # crash or return empty. We only verify that the state accumulator
      # keeps working — a task-supervised or try/rescue-wrapped call would
      # be needed for the unifier itself, but Step 4 is where that matters.
      # For the stub we just want to see that the message routing works.
      params = %Parameters{suggestions_enabled: true}
      pid = start_sa!(session_id, params)

      # Feed empty pairs so unify has nothing to chew on.
      send(pid, {:local_clashes, "root", MapSet.new()})
      _ = :sys.get_state(pid)

      state = :sys.get_state(pid)
      assert Map.get(state.clashing_local_pairs, "root") == MapSet.new()
    end
  end


  describe "integration with Prover" do
    import ShotDs.Hol.Sigils

    test "a γ-driven theorem still closes with SA enabled (no publication yet)" do
      # SA is a passive observer in Step 3, but wiring bugs (bad
      # message routing, ETS misconfiguration, unhandled crashes) would
      # surface as an end-to-end failure here.
      problem =
        ~p"""
        thf(p_t, type, p: $i > $o).
        thf(a_t, type, a: $i).
        thf(ax1, axiom, ![X: $i]: (p @ X)).
        thf(c, conjecture, p @ a).
        """

      assert {:thm, _proof} =
               ShotTx.Prover.prove(problem, timeout: 5_000, suggestions_enabled: true)
    end
  end

  # --- helpers ---------------------------------------------------------------

  defp start_sa!(session_id, params) do
    {:ok, pid} = SuggestionAgent.start_link({session_id, params})
    on_exit(fn -> if Process.alive?(pid), do: GenServer.stop(pid) end)
    pid
  end
end
