defmodule ShotTx.Data.Parameters do
  @moduledoc """
  Proof-search configuration struct. All fields are keyword-settable via `struct!/2`.

  | Field | Default | Description |
  |---|---|---|
  | `timeout` | `5_000` | Milliseconds before the prover gives up and returns `:timeout`. |
  | `initial_gamma_limit` | `1` | Starting γ-rule instantiation depth for iterative deepening. |
  | `initial_prim_limit` | `1` | Starting primitive-substitution binding depth. |
  | `prim_subst_after` | `1` | Number of γ instantiations before prim-subst is scheduled for a formula. |
  | `prim_subst_batch_size` | `8` | Maximum number of general bindings generated per prim-subst step. |
  | `unification_depth` | `8` | Maximum depth passed to the `shot_un` CSP solver. |
  | `unfold_defs` | `:lazy` | `:eager` unfolds definitions immediately; `:lazy` defers until the atomic rule. |
  | `beta_variant` | `true` | When `true`, adds `¬B₁` as an extra assumption to the right β-branch. |
  | `formula_cost` | `&Rules.rule_cost/1` | Cost function used by `FormulaPqueue`; lower cost = higher priority. |
  | `simplification` | `:deep` | Propositional simplification depth: `:none`, `:shallow`, or `:deep`. |
  | `orient` | `:none` | Orientation of commutative connectives (∧, ∨, ↔, =) by term order before classifying. `:none` skips orientation entirely. `:shallow` orients only the outermost connective of each formula. `:deep` recurses into all subterms bottom-up, normalising every nested commutative connective (including those embedded in atom arguments). |
  | `term_order` | `%ShotTo.Parameters{const_precedence: &:erlang.phash2/1}` | Parameters forwarded to the `ShotTo` term-order module. The default `const_precedence` is `&:erlang.phash2/1` — every constant name gets a stable hash-based rank. This gives NCPO-LNF a total well-founded precedence on symbols so it can orient equations between arbitrary distinct constants (including Skolem constants generated during δ). The paper's other soundness conditions (basicness, accessibility) remain at their permissive defaults (`:all`), which hold vacuously. A user-supplied map or function overrides this — see `ShotTo.Parameters`. |
  | `finite_o_quantification` | `true` | When `true`, quantifiers whose bound variable has a pure `o`-type are handled by the finite γ-rule (full enumeration of the propositional domain); when `false`, they are instantiated by the ordinary γ-rule like any other type. |
  | `equivalence_processing` | `:bidirectional_imp` | How `↔` is expanded. `:same_polarity` keeps the current β-split into `{p∧q, ¬p∧¬q}` (and dually for negation). `:bidirectional_imp` rewrites `p↔q` as `(p→q) ∧ (q→p)`, producing an α on the positive side. `:dual` does both: emits an α with both implications and the same-polarity disjunction so the prover can exploit either path. |
  | `instance_based_gamma` | `true` | When `true`, the first firing of a γ-rule is also instantiated with every closed term of the matching type currently known on the branch, and prim-subst unit-set bindings (`λy. H(y) = c`) are generated for branch constants. Ground terms discovered later are picked up the next time the same γ-rule fires under iterative deepening. When `false`, only the fresh-variable instantiation is performed and no instance-driven steps are added. |
  | `instance_based_gamma_limit` | `0` | Caps the number of ground instances emitted by a single γ-firing when `instance_based_gamma` is enabled. `0` disables the fan-out (only the fresh-variable instance is added), `:infinity` keeps the historical unbounded behavior, and a positive integer truncates the per-fire fan-out to that many closed terms. The default is `0` because nested quantifiers multiply branch constants combinatorially, and the cheaper first-γ cost (see `Rules.rule_cost/2`) makes each new IBG-derived γ-rule fire ahead of β, cascading the explosion. |
  | `demodulation` | `true` | When `true`, `ShotTx.Prover.Demodulation.normalize/3` runs at two points: (a) *forward* — every incoming formula is reduced to normal form under the current equations before it lands in the branch queue; (b) *backward* — when a new equation is ingested, every existing branch literal is re-normalized under the enlarged equation set and, if changed, its old form is discarded. Only rewrites whose matcher is the empty substitution are admitted (equation LHS must be structurally identical to the target subterm, or a primitive η-expansion `λv̄. h(v̄)` matching an applied subterm's head declaration). No variable is ever bound at the branch level — the `ContradictionAgent` retains its exclusive responsibility for reconciling γ-instantiation placeholders across sibling branches via the global CSP. Termination follows from the paper's `(NCPO-LNF, CPO⁺)` reduction-order pair. When `false`, formulas are enqueued and stored verbatim. |
  | `atom_decomposition` | `true` | When `true`, the `:rename` and `:instantiate` rules fire for atomic formulas with complex or o-type arguments. When `false`, all atoms are sent directly to the atomic clash rule without decomposition. |
  | `model_agent_backend` | `:none` | Selects the external model-finding backend used by `ShotTx.Prover.ModelAgent`. `:none` disables the agent entirely (default; matches historical behavior). `:stub` runs a no-op backend that always returns `:unknown` — useful for tests. `{:custom, module}` plugs in any module implementing `ShotTx.Prover.ModelAgent.Backend`. |
  | `model_agent_budget_ms` | `5_000` | Time budget for a single external probe. |
  | `model_agent_max_in_flight` | `2` | Cap on concurrent probes dispatched by the agent. Isabelle serializes model-finding on one server anyway, so setting this above the number of servers wastes queue slots. |
  | `model_agent_max_frontier` | `100` | Skip branches whose frontier is larger than this — model finders scale poorly on vocabulary. |
  | `model_agent_min_delta_ms` | `200` | Tick interval for the agent's periodic scan of live branches. |
  | `model_agent_min_frontier` | `3` | Skip branches with frontiers below this size; trivially satisfiable frontiers are noise (a single atom `P(a)` is always SAT and tells us nothing). |
  | `suggestions_enabled` | `true` | Feature flag for `ShotTx.Prover.SuggestionAgent`. When `true` (default), SA runs pair-level unification on local clashes and emits instantiation hints. When `false`, SA subscribes to nothing and stays a no-op. |
  | `suggestion_cascade_ceiling` | `3` | Cap on how many times any single suggestion (keyed by `{branch_prefix, recipe, term}`) may be spliced across all descendants of its `birth_branch`. Bounds the feedback loop where an applied suggestion produces fresh clashes → new unifiers → new suggestions. Enforced via `:ets.update_counter/3` at the splice site. |
  | `worker_pool_size` | `:auto` | Number of `Worker` processes the `Manager` spawns. `:auto` uses `System.schedulers_online()`; a positive integer pins the pool. Set to `1` for a serial baseline. |
  | `contradiction_agent` | `true` | When `true`, `ContradictionAgent` performs global unification-based closure across open branches via the `shot_un` CSP. When `false`, the agent still tracks branch state (needed for SAT extraction) but never dispatches a CSP; only local, per-branch ground clashes can close the proof. Ablation switch for "with/without global closure". |
  | `primitive_substitution` | `true` | When `true`, γ-rules whose bound type has goal `:o` schedule a `:prim_subst` companion after `prim_subst_after` firings. When `false`, prim-subst is never scheduled regardless of `initial_prim_limit`. Hard off-switch for the general-bindings enumeration; equality/higher-order reasoning falls back to Leibniz/extensional expansion and paramodulation. |
  | `iterative_deepening` | `true` | When `true`, the `Manager` bumps `gamma_limit` and `prim_depth_limit` by 1 every time all workers stall, then wakes parked branches. When `false`, deepening never fires: once workers are all idle the prover returns `:unknown` with the initial limits. Use with elevated `initial_gamma_limit` / `initial_prim_limit` to run at a fixed depth. |
  | `formula_cost_strategy` | `:default` | Named cost function used by `FormulaPqueue`; resolved at prove-time to `formula_cost`. `:default` → `Rules.rule_cost/1`. `:uniform` → constant cost (breadth-first over the rule queue). `:depth_first` → penalises rules that generate many children (β / prim-subst) so simple decompositions run to completion first. `{:custom, fun}` bypasses the strategy and uses `fun` directly. |
  | `progress_interval_ms` | `2_000` | Interval at which the `Manager` logs a one-line progress report during a proof. Set to `0` to silence the log entirely (useful for benchmark sweeps). |
  """

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
            orient: :none,
            term_order: %ShotTo.Parameters{const_precedence: &:erlang.phash2/1},
            finite_o_quantification: true,
            equivalence_processing: :bidirectional_imp,
            instance_based_gamma: true,
            instance_based_gamma_limit: 0,
            demodulation: true,
            atom_decomposition: true,
            model_agent_backend: :none,
            model_agent_budget_ms: 5_000,
            model_agent_max_in_flight: 2,
            model_agent_max_frontier: 100,
            model_agent_min_delta_ms: 200,
            model_agent_min_frontier: 3,
            suggestions_enabled: true,
            suggestion_cascade_ceiling: 3,
            worker_pool_size: :auto,
            contradiction_agent: true,
            primitive_substitution: true,
            iterative_deepening: true,
            formula_cost_strategy: :default,
            progress_interval_ms: 2_000

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
          orient: :none | :shallow | :deep,
          term_order: ShotTo.Parameters.t(),
          finite_o_quantification: boolean(),
          equivalence_processing: :same_polarity | :bidirectional_imp | :dual,
          instance_based_gamma: boolean(),
          instance_based_gamma_limit: :infinity | non_neg_integer(),
          demodulation: boolean(),
          atom_decomposition: boolean(),
          model_agent_backend: :none | :stub | :nitpick | {:custom, module()},
          model_agent_budget_ms: pos_integer(),
          model_agent_max_in_flight: pos_integer(),
          model_agent_max_frontier: pos_integer(),
          model_agent_min_delta_ms: pos_integer(),
          model_agent_min_frontier: non_neg_integer(),
          suggestions_enabled: boolean(),
          suggestion_cascade_ceiling: non_neg_integer(),
          worker_pool_size: :auto | pos_integer(),
          contradiction_agent: boolean(),
          primitive_substitution: boolean(),
          iterative_deepening: boolean(),
          formula_cost_strategy:
            :default | :uniform | :depth_first | {:custom, (Rules.rule_t() -> non_neg_integer())},
          progress_interval_ms: non_neg_integer()
        }
end
