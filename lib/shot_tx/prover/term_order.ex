defmodule ShotTx.Prover.TermOrder do
  @moduledoc """
  Two orderings on HOL term IDs, both parameterised by an `%ShotTo.Parameters{}`.

  ## `strict_gt?/3` — the paper's NCPO-LNF, unmodified

  A direct passthrough to `ShotTo.gt?/3`. This is the βη-long-normal
  Computability Path Order of Niederhauser & Middeldorp (*NCPO goes
  Beta-Eta-Long Normal Form*, 2025). By the paper's Theorem 2 the pair
  `(NCPO-LNF, CPO⁺)` is a βη-normal higher-order reduction order:

    * `>` is well-founded on βη-long-normal terms;
    * `CPO⁺` is monotone and stability-compatible with `>` for βη-long-normal
      substitutions.

  This is the **only** decision suitable for gating rewriting steps (ordered
  paramodulation, demodulation, superposition restrictions): it may answer
  `false` on both `s > t` and `t > s` for the same pair, and callers must be
  ready to *block* the rewrite in that case.

  ## `gt?/3` and `compare/3` — total heuristic extension

  Wraps `ShotTo.compare/3` and, on `:incomparable`, falls back to two
  deterministic tie-breakers:

    1. Alphabetic ordering on `to_string(term)`.
    2. Native Erlang term order on the integer term IDs.

  The resulting relation is total and decidable but is **not** in general a
  reduction order — it is not guaranteed to be well-founded or monotone. It
  is suitable for choosing a canonical direction heuristically (orientation
  of commutative connectives `∨/∧/↔/=`) where any deterministic answer
  suffices, but must **not** be used to gate rewriting.
  """

  alias ShotDs.Data.Term
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotTo.Parameters

  @doc """
  Returns `true` iff `s_id > t_id` in NCPO-LNF strictly (the paper's
  provably well-founded relation). Returns `false` for the incomparable case.

  Use this — not `gt?/3` — as the gate for any rewriting step whose
  termination or completeness argument depends on a reduction order.
  """
  @spec strict_gt?(Term.term_id(), Term.term_id(), Parameters.t()) :: boolean()
  def strict_gt?(s_id, t_id, %Parameters{} = params), do: ShotTo.gt?(s_id, t_id, params)

  @doc """
  Returns `:greater`, `:less`, or `:equal` for two term IDs under a total
  extension of NCPO-LNF parameterized by `params`. Never returns
  `:incomparable`.
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
  Returns `true` iff `s_id` is strictly greater than `t_id` in the total
  (heuristic) extension. See the module docs for when to prefer
  `strict_gt?/3` instead.
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
