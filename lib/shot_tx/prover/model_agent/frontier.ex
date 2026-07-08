defmodule ShotTx.Prover.ModelAgent.Frontier do
  @moduledoc """
  Projects a `ShotTx.Prover.Branch` onto a `ShotDs.Data.Problem` for external
  model-finding.

  The projection ships the branch's `:frontier` as axioms and its `:defs` as
  TPTP `definition` entries. Types are auto-derived from constants referenced
  by the axioms via `ShotDs.Data.Problem.new/1`; constants that only appear in
  `:defs` are added afterwards so their type declarations are not lost.

  The resulting `%Problem{}` has **no conjecture** — the intended TPTP payload
  is "here are some axioms, find me a model," which is exactly what
  `nitpick[satisfy]` consumes.
  """

  alias ShotDs.Data.{Declaration, Problem, TypeScheme}
  alias ShotTx.Prover.Branch

  @doc """
  Builds a `ShotDs.Data.Problem` from a branch. Sorted axiom order gives
  deterministic TPTP output for golden testing.
  """
  @spec to_problem(Branch.t()) :: Problem.t()
  def to_problem(%Branch{} = branch) do
    axioms =
      branch.frontier
      |> MapSet.to_list()
      |> Enum.sort()
      |> Enum.with_index(1)
      |> Enum.map(fn {tid, idx} -> {"a_#{idx}", tid} end)

    %Problem{} = base = Problem.new!(axioms: axioms, path: "shot_tx_frontier_probe_#{branch.id}")

    def_types = build_def_types(branch.defs)

    %{base | definitions: branch.defs, types: Map.merge(def_types, base.types)}
  end

  defp build_def_types(defs) do
    Map.new(defs, fn {%Declaration{name: name, type: type}, _rhs} ->
      {name_key(name), TypeScheme.generalize(type, MapSet.new())}
    end)
  end

  defp name_key(name) when is_binary(name), do: name

  defp name_key(ref) when is_reference(ref),
    do: "c#{:erlang.phash2(ref) |> Integer.to_string(36)}"
end
