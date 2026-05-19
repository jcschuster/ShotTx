defmodule ShotTx.Prover.TermOrder do
  @moduledoc """
  Total ordering on HOL term IDs extending NCPO-LNF with pragmatic tiebreakers.

  `ShotTo.compare/3` may return `:incomparable` for terms that NCPO-LNF
  cannot relate. When that happens we fall back to two heuristics in order:

    1. Alphabetic ordering on the term's printed representation (`to_string`).
    2. Native Erlang term order on the integer term IDs as a last resort.

  The resulting relation is total and decidable but is not in general a
  reduction order — it is not guaranteed to be well-founded or monotone. It
  is suitable for choosing a rewrite direction heuristically (ordered
  paramodulation, connective canonicalization) without the completeness
  guarantees of a proper reduction order.
  """

  alias ShotDs.Data.Term
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotTo.Parameters

  @doc """
  Returns `:greater`, `:less`, or `:equal` for two term IDs under a total
  extension of NCPO-LNF parameterized by `params`.
  """
  @spec compare(Term.term_id(), Term.term_id(), Parameters.t()) :: :greater | :less | :equal
  def compare(s_id, t_id, _params) when s_id == t_id, do: :equal

  def compare(s_id, t_id, %Parameters{} = params) do
    case ShotTo.compare(s_id, t_id, params) do
      :incomparable -> tiebreak(s_id, t_id)
      result -> result
    end
  end

  @doc """
  Returns `true` iff `s_id` is strictly greater than `t_id` in the total order.
  """
  @spec gt?(Term.term_id(), Term.term_id(), Parameters.t()) :: boolean()
  def gt?(s_id, t_id, %Parameters{} = params), do: compare(s_id, t_id, params) == :greater

  defp tiebreak(s_id, t_id) do
    s_str = TF.get_term!(s_id) |> to_string()
    t_str = TF.get_term!(t_id) |> to_string()

    cond do
      s_str > t_str -> :greater
      s_str < t_str -> :less
      s_id > t_id -> :greater
      s_id < t_id -> :less
      true -> :equal
    end
  end
end
