defmodule ShotTx.Prover.ModelAgent.Backend do
  @moduledoc """
  Behaviour implemented by external model-finding backends.

  A backend answers the question *"is this `%ShotDs.Data.Problem{}`
  satisfiable, and if so, produce a witness."* The default implementation
  (`ShotTx.Prover.ModelAgent.Backend.Nitpick`, layer 3) sends the problem to
  a warm Isabelle server and runs `nitpick[satisfy]`. `Backend.Stub` returns
  `:unknown` unconditionally and is the safe default for tests / CI.

  The API is deliberately async: `probe/2` returns immediately with a
  reference; the caller later drains the verdict via `await/2`. This lets
  `ShotTx.Prover.ModelAgent` fan out multiple probes without blocking its
  GenServer mailbox.
  """

  alias ShotDs.Data.Problem

  @typedoc "Opaque handle identifying an in-flight probe."
  @type ref :: reference()

  @typedoc "A model witness — backend-specific payload attached to a `:sat` verdict."
  @type witness :: map()

  @typedoc "Terminal verdicts a backend can return."
  @type verdict :: {:sat, witness()} | :unsat | :unknown | {:error, term()}

  @doc """
  Dispatches a probe. Returns an opaque reference the agent will later hand
  to `await/2`, or `{:error, reason}` if the backend refused to accept the
  probe (e.g. queue full, service unavailable).
  """
  @callback probe(Problem.t(), keyword()) :: {:ok, ref()} | {:error, term()}

  @doc """
  Waits up to `timeout_ms` for the probe to finish. Returns a verdict or
  `{:error, :timeout}` when the budget elapses without a reply.
  """
  @callback await(ref(), timeout_ms :: pos_integer()) :: verdict()
end
