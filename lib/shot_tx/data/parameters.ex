defmodule ShotTx.Data.Parameters do
  alias ShotTx.Prover.Rules

  defstruct timeout: 30_000,
            initial_gamma_limit: 1,
            initial_prim_limit: 1,
            prim_subst_batch_size: 5,
            unification_depth: 8,
            formula_cost: &Rules.rule_cost/1

  @type t :: %__MODULE__{
          timeout: pos_integer(),
          initial_gamma_limit: pos_integer(),
          initial_prim_limit: pos_integer(),
          prim_subst_batch_size: pos_integer(),
          unification_depth: pos_integer(),
          formula_cost: (Rules.rule_t() -> non_neg_integer())
        }
end
