defmodule ShotTx.Prover.LambdaLiftTest do
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotTx.Prover.LambdaLift

  use ShotDs.Hol.Patterns

  describe "lift/1" do
    test "leaves a propositional formula untouched" do
      ctx = ~e"p: $o, q: $o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        formula = ~f"p | q"
        assert {^formula, []} = LambdaLift.lift(formula)
      end)
    end

    test "leaves an applied named constant untouched (η-expansion is skipped)" do
      ctx = ~e"f: $i>$i, p: ($i>$i)>$o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        formula = ~f"p @ f"
        assert {^formula, []} = LambdaLift.lift(formula)
      end)
    end

    test "lifts the identity lambda passed as a predicate argument" do
      ctx = ~e"p: ($i>$i)>$o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        formula = ~f"p @ (^[X:$i]: X)"
        assert {rewritten, [axiom]} = LambdaLift.lift(formula)

        refute rewritten == formula

        # The rewritten predicate's argument is the lift constant (η-expanded).
        %{args: [arg_id]} = TF.get_term!(rewritten)
        %{head: head} = TF.get_term!(arg_id)
        assert head.kind == :co
        assert is_reference(head.name)

        # The axiom equates the lift constant with the original abstraction.
        assert match?(equality(_lhs, _rhs), TF.get_term!(axiom))
      end)
    end

    test "leaves quantified bodies alone (∀ is not a liftable parent)" do
      ctx = ~e"p: $i>$o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        formula = ~f"![X:$i]: p @ X"
        assert {^formula, []} = LambdaLift.lift(formula)
      end)
    end

    test "leaves the LHS of an equality alone" do
      ctx = ~e"p: ($i>$i)>$o"

      ShotDs.Hol.Sigils.with_context(ctx, fn ->
        # `=` is in the connective list — its abstraction arguments are not
        # lifted (extensional_equality handles them via the α-rule already).
        formula = ~f"(^[X:$i]: X) = (^[X:$i]: X)"
        assert {^formula, []} = LambdaLift.lift(formula)
      end)
    end
  end
end
