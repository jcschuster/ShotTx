defmodule ShotTx.Data.Parameters do
  @moduledoc """
  Proof-search configuration struct. All fields are keyword-settable via `struct!/2`.

  | Field | Default | Description |
  |---|---|---|
  | `timeout` | `5_000` | Milliseconds before the prover gives up and returns `:timeout`. |
  | `initial_gamma_limit` | `1` | Starting γ-rule instantiation depth for iterative deepening. |
  | `initial_prim_limit` | `1` | Starting primitive-substitution binding depth. |
  | `prim_subst_after` | `0` | Number of γ instantiations before prim-subst is scheduled for a formula. |
  | `prim_subst_batch_size` | `8` | Maximum number of general bindings generated per prim-subst step. |
  | `unification_depth` | `8` | Maximum depth passed to the `shot_un` CSP solver. |
  | `unfold_defs` | `:lazy` | `:eager` unfolds definitions immediately; `:lazy` defers until the atomic rule. |
  | `beta_variant` | `true` | When `true`, adds `¬B₁` as an extra assumption to the right β-branch. |
  | `formula_cost` | `&Rules.rule_cost/1` | Cost function used by `FormulaPqueue`; lower cost = higher priority. |
  | `simplification` | `:deep` | Propositional simplification depth: `:none`, `:shallow`, or `:deep`. |
  | `orient` | `false` | When `true`, orient commutative connectives by term order before classifying. |
  | `term_order` | `%ShotTo.Parameters{}` | Parameters forwarded to the `ShotTo` term-order module. |
  """

  alias ShotTx.Prover.Rules

  defstruct timeout: 5_000,
            initial_gamma_limit: 1,
            initial_prim_limit: 1,
            prim_subst_after: 0,
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
          prim_subst_after: non_neg_integer(),
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
