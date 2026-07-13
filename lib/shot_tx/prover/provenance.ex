defmodule ShotTx.Prover.Provenance do
  @moduledoc """
  Per-fresh-variable annotation recording which quantifier minted the
  variable and on which branch. Consumed by `ContradictionAgent` and
  `SuggestionAgent` to turn unifier evidence back into instantiation hints.

  Written at exactly two sites in `ShotTx.Prover.Branch`:
    * the γ fresh-var mint, and
    * every hole `H` produced by a general binding in the prim-subst
      enumerator.

  Reads are performed by the agents. Workers never read this table.
  """

  alias ShotDs.Data.Term

  @type origin :: :gamma | :prim_subst

  @type t :: %__MODULE__{
          recipe: Term.term_id(),
          source: Term.term_id(),
          birth_branch: String.t(),
          gamma_iteration: non_neg_integer(),
          origin: origin()
        }

  defstruct [:recipe, :source, :birth_branch, :gamma_iteration, :origin]

  @doc """
  Inserts `provenance` for `fresh_var_id`. Uses `:ets.insert_new/2` so a
  redundant write (which would only happen under a bug — fresh vars are
  minted once) silently returns `false` rather than clobbering an earlier
  entry that another consumer may already have observed.
  """
  @spec record(:ets.tab(), Term.term_id(), t()) :: boolean()
  def record(table, fresh_var_id, %__MODULE__{} = provenance) do
    :ets.insert_new(table, {fresh_var_id, provenance})
  end

  @doc "Fetches the provenance for `fresh_var_id`, or `nil` if unknown."
  @spec fetch(:ets.tab(), Term.term_id()) :: t() | nil
  def fetch(table, fresh_var_id) do
    case :ets.lookup(table, fresh_var_id) do
      [{^fresh_var_id, prov}] -> prov
      [] -> nil
    end
  end
end
