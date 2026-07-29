defmodule ShotTx.Prover.SpliceSuggestionsTest do
  @moduledoc """
  Unit tests for the Step 4 splice mechanics:

    * `Branch.splice_suggested_instantiate/5` inserts the synthetic rule
      into the branch's priority queue.
    * When the rule is popped, `apply_rule/6` adds `app(recipe, term)` to
      the branch — with no fanout to a child branch (contrast with
      `:instantiate`).
    * The `:ets.update_counter/3` guard used by `Worker.splice_suggestions/2`
      returns the incremented counter atomically so a runaway cascade is
      capped by `params.suggestion_cascade_ceiling`.
  """
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Branch

  @minimal %Parameters{
    simplification: :none,
    beta_variant: false,
    demodulation: false,
    orient: :none,
    instance_based_gamma: false
  }

  describe "Branch.splice_suggested_instantiate/5" do
    test "single splice adds app(recipe, term) on next step, no fanout" do
      ctx = ~e"p: $i > $o, a: $i"

      with_context(ctx, fn ->
        recipe = ~f"^[X: $i]: (p @ X)"
        term = ~f"a"
        goal = ~f"p @ a"

        branch =
          "root"
          |> Branch.new([], @minimal)
          |> Branch.splice_suggested_instantiate(recipe, term, nil, @minimal)

        # The synthetic rule pops as :suggested_instantiate and yields a
        # :continue with the beta-reduced formula added to the branch.
        assert {:continue, next, :no_effects} = Branch.step(branch, @minimal, 1, 1)

        # No `_I0` child, still on the same branch id.
        assert next.id == "root"
        assert MapSet.member?(next.term_ids, goal)
      end)
    end
  end

  describe "cascade cap guard (raw :ets.update_counter/3)" do
    test "atomic bump returns the new count; capped at ceiling" do
      table = :ets.new(:test_suggestions, [:set, :public])
      key = {"root", 100, 200}
      ceiling = 3

      # Simulate what SA publishes.
      :ets.insert_new(table, {key, 0, :fake_suggestion})

      counts =
        for _ <- 1..5 do
          :ets.update_counter(table, key, {2, 1})
        end

      # Ordinary counter: 1, 2, 3, 4, 5 — the Worker then filters those > 3.
      assert counts == [1, 2, 3, 4, 5]
      admitted = Enum.filter(counts, &(&1 <= ceiling))
      assert admitted == [1, 2, 3]
    end
  end
end
