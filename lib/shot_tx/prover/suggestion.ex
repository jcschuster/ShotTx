defmodule ShotTx.Prover.Suggestion do
  @moduledoc """
  A single instantiation hint produced by `SuggestionAgent` and consumed
  by workers. Persisted in the `:suggestions` ETS table with the row shape:

      {{branch_prefix, recipe, term}, applied_count, %Suggestion{}}

  The counter at position 2 is bumped via `:ets.update_counter/3` on
  splice — see `params.suggestion_cascade_ceiling` and the
  design-doc "Non-terminating cascade" section.

  Fields:
    * `term`         — the closed term to splice as `app(recipe, term)`.
    * `source`       — the recipe's originating formula id (diagnostic;
                       may be simplified away later — see `Provenance.source`).
    * `score`        — bounded relevance score. Higher is better.
    * `published_at_us` — monotonic microseconds at insert time.
  """

  alias ShotDs.Data.Term

  @type t :: %__MODULE__{
          term: Term.term_id(),
          source: Term.term_id() | nil,
          score: number(),
          published_at_us: integer()
        }

  defstruct [:term, :source, score: 0, published_at_us: 0]
end
