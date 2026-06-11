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
  | `finite_o_quantification` | `true` | When `true`, quantifiers whose bound variable has a pure `o`-type are handled by the finite γ-rule (full enumeration of the propositional domain); when `false`, they are instantiated by the ordinary γ-rule like any other type. |
  | `paramodulation_mode` | `:unification` | Strategy used to align an equation LHS with a literal position. `:unification` runs full higher-order pre-unification (Huet 1975). `:pattern` runs Miller pattern unification — decidable, unitary, restricted to the higher-order pattern fragment (every flex variable applied to distinct bound variables); positions outside the fragment are skipped. `:matching` runs Huet second-order matching — decidable, terminating, but requires the literal position to be ground and every type to be at most second-order; positions outside the fragment are skipped. |
  | `equivalence_processing` | `:same_polarity` | How `↔` is expanded. `:same_polarity` keeps the current β-split into `{p∧q, ¬p∧¬q}` (and dually for negation). `:bidirectional_imp` rewrites `p↔q` as `(p→q) ∧ (q→p)`, producing an α on the positive side. `:dual` does both: emits an α with both implications and the same-polarity disjunction so the prover can exploit either path. |
  | `instance_based_gamma` | `true` | When `true`, the first firing of a γ-rule is also instantiated with every closed term of the matching type currently known on the branch, and prim-subst unit-set bindings (`λy. H(y) = c`) are generated for branch constants. Ground terms discovered later are picked up the next time the same γ-rule fires under iterative deepening. When `false`, only the fresh-variable instantiation is performed and no instance-driven steps are added. |
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
            term_order: %ShotTo.Parameters{},
            finite_o_quantification: true,
            paramodulation_mode: :unification,
            equivalence_processing: :bidirectional_imp,
            instance_based_gamma: true

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
          term_order: ShotTo.Parameters.t(),
          finite_o_quantification: boolean(),
          paramodulation_mode: :unification | :pattern | :matching,
          equivalence_processing: :same_polarity | :bidirectional_imp | :dual,
          instance_based_gamma: boolean()
        }
end
