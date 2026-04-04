defmodule ShotTx.Data.Parameters do
  alias ShotTx.Prover.Rules

  defstruct timeout: 30_000,
            initial_gamma_limit: 1,
            initial_prim_limit: 1,
            unification_depth: 8,
            max_branches: 10_000,
            formula_cost: &Rules.rule_cost/1,
            unify_depth: 10

  @type t :: %__MODULE__{
          timeout: pos_integer(),
          initial_gamma_limit: pos_integer(),
          unification_depth: pos_integer(),
          max_branches: pos_integer() | :infinity,
          formula_cost: (Rules.rule_t() -> non_neg_integer()),
          unify_depth: pos_integer()
        }
end
