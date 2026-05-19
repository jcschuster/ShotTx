defmodule ShotTx.Data.Parameters do
  alias ShotTx.Prover.Rules

  defstruct timeout: 5_000,
            initial_gamma_limit: 1,
            initial_prim_limit: 1,
            prim_subst_after: 1,
            prim_subst_batch_size: 8,
            unification_depth: 8,
            unfold_defs: :lazy,
            beta_variant: true,
            formula_cost: &Rules.rule_cost/1,
            simplification: :deep,
            orient: false,
            term_order: %ShotTo.Parameters{}

  @type t :: %__MODULE__{
          timeout: pos_integer(),
          initial_gamma_limit: pos_integer(),
          initial_prim_limit: pos_integer(),
          prim_subst_after: pos_integer(),
          prim_subst_batch_size: pos_integer(),
          unification_depth: pos_integer(),
          unfold_defs: :lazy | :eager,
          beta_variant: boolean(),
          formula_cost: (Rules.rule_t() -> non_neg_integer()),
          simplification: :none | :shallow | :deep,
          orient: boolean(),
          term_order: ShotTo.Parameters.t()
        }
end
