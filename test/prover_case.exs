defmodule ShotTx.Test.ProverCase do
  @moduledoc """
  Shared helpers for end-to-end prover tests. The application is started by
  ExUnit, so we just provide convenience wrappers that keep the test default
  timeout short and surface readable failure messages.
  """

  defmacro __using__(_opts) do
    quote do
      use ExUnit.Case, async: false

      import ShotDs.Hol.Sigils
      import ShotTx.Test.ProverCase

      alias ShotTx.Prover
    end
  end

  @default_opts [timeout: 5_000]

  @doc """
  Asserts that a TPTP-THF problem is a theorem.
  """
  def assert_thm(problem, opts \\ []) do
    case ShotTx.Prover.prove(problem, Keyword.merge(@default_opts, opts)) do
      {:thm, proof} ->
        proof

      other ->
        ExUnit.Assertions.flunk(
          "expected :thm, got #{inspect(elem(other, 0))} for problem:\n#{inspect(problem)}"
        )
    end
  end

  @doc """
  Asserts that a TPTP-THF problem has a countermodel (counter-satisfiable).
  """
  def assert_csa(problem, opts \\ []) do
    case ShotTx.Prover.prove(problem, Keyword.merge(@default_opts, opts)) do
      {:csa, model, proof} ->
        {model, proof}

      other ->
        ExUnit.Assertions.flunk(
          "expected :csa, got #{inspect(elem(other, 0))} for problem:\n#{inspect(problem)}"
        )
    end
  end

  @doc """
  Proves a problem and returns whichever result the prover gives, including
  `:unknown` or `:timeout`. Useful for soft regression checks.
  """
  def prove(problem, opts \\ []) do
    ShotTx.Prover.prove(problem, Keyword.merge(@default_opts, opts))
  end
end
