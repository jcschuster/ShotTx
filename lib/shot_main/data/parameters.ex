defmodule ShotMain.Data.Parameters do
  alias ShotMain.Prover.Rules

  defstruct timeout: 10_000,
            initial_gamma_limit: 1,
            max_gamma_limit: 4,
            unification_depth: 8,
            max_branches: 5_000,
            formula_cost: &Rules.rule_cost/1

  @type t :: %__MODULE__{
          timeout: pos_integer(),
          initial_gamma_limit: pos_integer(),
          max_gamma_limit: pos_integer(),
          unification_depth: pos_integer(),
          max_branches: pos_integer() | :infinity,
          formula_cost: (Rules.rule_t() -> non_neg_integer())
        }
end
