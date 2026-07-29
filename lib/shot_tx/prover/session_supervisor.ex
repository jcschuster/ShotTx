defmodule ShotTx.Prover.SessionSupervisor do
  @moduledoc """
  OTP supervisor owning the per-session proof-search tree.

  Started once per `ShotTx.Prover.prove/*` call and torn down when the caller
  returns. Uses `:rest_for_one` so that if the `Manager` or an agent crashes,
  its dependents restart in the correct order — the ETS keeper stays alive
  and preserves stats/traces for post-mortem inspection.

  Children (in start order):

    * `EtsKeeper` — owns the per-session tables (`:stats`, `:tombs`,
      `:work_queue`, `:idle_queue`, `:traces`).
    * `Task.Supervisor` — supervises async CSP dispatches from
      `ContradictionAgent`.
    * `Manager` — orchestrates workers and iterative deepening.
    * `ContradictionAgent`, `SuggestionAgent`, `ModelAgent` — peer agents on
      the shared `branch_evidence_<session>` PubSub topic.
    * A `DynamicSupervisor` for the worker pool.
  """

  use Supervisor

  @doc """
  Starts a per-session supervision tree.

  `init_arg` is `{session_id, formulas, defs, params}` where `session_id` is
  the unique reference for this proof, `formulas` are the initial branch
  formulas (assumptions plus the negated conclusion), `defs` a definition
  map, and `params` a `ShotTx.Data.Parameters` struct.
  """
  def start_link(init_arg) do
    Supervisor.start_link(__MODULE__, init_arg)
  end

  @impl true
  def init({session_id, formulas, defs, params}) do
    children = [
      {ShotTx.Prover.EtsKeeper, {session_id, params}},
      {Task.Supervisor, name: via(session_id, :task_supervisor)},
      {ShotTx.Prover.Manager, {session_id, formulas, defs, params}},
      {ShotTx.Prover.ContradictionAgent, {session_id, params}},
      {ShotTx.Prover.SuggestionAgent, {session_id, params}},
      {ShotTx.Prover.ModelAgent, {session_id, params}},
      %{
        id: :branch_supervisor,
        start:
          {DynamicSupervisor, :start_link,
           [[name: via(session_id, :branch_supervisor), strategy: :one_for_one]]},
        type: :supervisor,
        shutdown: :brutal_kill
      }
    ]

    Supervisor.init(children, strategy: :rest_for_one)
  end

  defp via(session_id, name) do
    {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, name}}}
  end
end
