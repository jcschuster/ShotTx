defmodule ShotTx.Data.ParametersTest do
  use ExUnit.Case, async: true

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Rules

  test "defaults are sensible" do
    p = %Parameters{}

    assert p.timeout == 5_000
    assert p.initial_gamma_limit == 1
    assert p.initial_prim_limit == 1
    assert p.prim_subst_after == 1
    assert p.prim_subst_batch_size == 8
    assert p.unification_depth == 8
    assert p.unfold_defs == :lazy
    assert p.beta_variant == true
    assert p.simplification == :deep
    assert p.orient == false
    assert is_function(p.formula_cost, 1)
  end

  test "default formula_cost is Rules.rule_cost/1" do
    p = %Parameters{}
    assert p.formula_cost.(:contradiction) == Rules.rule_cost(:contradiction)
    assert p.formula_cost.({:atomic, 1}) == Rules.rule_cost({:atomic, 1})
  end

  test "struct! accepts a keyword list and overrides defaults" do
    p = struct!(Parameters, timeout: 500, unfold_defs: :eager, orient: true)

    assert p.timeout == 500
    assert p.unfold_defs == :eager
    assert p.orient == true
    # untouched fields stay at default
    assert p.initial_gamma_limit == 1
  end
end
