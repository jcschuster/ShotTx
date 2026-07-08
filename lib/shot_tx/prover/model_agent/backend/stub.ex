defmodule ShotTx.Prover.ModelAgent.Backend.Stub do
  @moduledoc """
  Trivial `Backend` implementation that returns `:unknown` for every probe.
  Used when `model_agent_backend` is `:none`, `:stub`, or when Isabelle is
  unavailable at runtime. Keeps the agent's plumbing exercised in tests
  without any external dependency.
  """
  @behaviour ShotTx.Prover.ModelAgent.Backend

  @impl true
  def probe(_problem, _opts), do: {:ok, make_ref()}

  @impl true
  def await(_ref, _timeout_ms), do: :unknown
end
