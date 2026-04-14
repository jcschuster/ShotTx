defmodule ShotTx.Generation.TypeUniverse do
  @moduledoc ~S"""
  Collects and maintains the set of types relevant to a proof.

  The type universe determines which polymorphic constants ($=_\tau$,
  $\Pi_\tau$, $\Sigma_\tau$) are available as heads in general bindings for
  primitive substitution. It contains every type and sub-type occurring in the
  problem signature as well as every type introduced at runtime by
  skolemization or renaming.

  A type $\alpha_1\to\cdots\to\alpha_n\to\gamma$ decomposes into:

    * the type itself,
    * every proper suffix $\alpha_k\to\cdots\to\alpha_n\to\gamma$,
    * the base type $\gamma$, and
    * recursively, the sub-types of each $\alpha_i$.
  """

  alias ShotDs.Data.{Type, Term}
  alias ShotDs.Stt.TermFactory, as: TF

  @doc """
  Computes the initial type universe from a list of problem formula IDs.
  """
  @spec from_formulas([Term.term_id()]) :: MapSet.t(Type.t())
  def from_formulas(formula_ids) do
    formula_ids
    |> Enum.flat_map(&collect_from_term/1)
    |> MapSet.new()
  end

  @doc """
  Extends an existing universe with all sub-types of `type`. Returns the
  universe unchanged when nothing new is introduced.
  """
  @spec extend(MapSet.t(Type.t()), Type.t()) :: MapSet.t(Type.t())
  def extend(universe, %Type{} = type) do
    new = type |> decompose() |> MapSet.new() |> MapSet.difference(universe)
    MapSet.union(universe, new)
  end

  @doc """
  Decomposes a type into itself, every proper suffix and recursively all
  sub-types of its arguments.
  """
  @spec decompose(Type.t()) :: [Type.t()]
  def decompose(%Type{args: []} = type), do: [type]

  def decompose(%Type{goal: goal, args: args} = type) do
    suffixes = for n <- 1..length(args), do: %Type{goal: goal, args: Enum.drop(args, n)}
    arg_subtypes = Enum.flat_map(args, &decompose/1)

    Enum.uniq([type | suffixes] ++ arg_subtypes)
  end

  ##############################################################################
  # PRIVATE
  ##############################################################################

  @spec collect_from_term(Term.term_id()) :: [Type.t()]
  defp collect_from_term(term_id) do
    %Term{head: head, bvars: bvars, fvars: fvars, args: args} = TF.get_term!(term_id)

    decompose(head.type) ++
      Enum.flat_map(bvars, &decompose(&1.type)) ++
      Enum.flat_map(fvars, &decompose(&1.type)) ++
      Enum.flat_map(args, &collect_from_term/1)
  end
end
