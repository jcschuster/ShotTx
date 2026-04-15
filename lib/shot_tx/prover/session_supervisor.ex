defmodule ShotTx.Prover.SessionSupervisor do
  use Supervisor

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
      # {DynamicSupervisor, name: via(session_id, :branch_supervisor), strategy: :one_for_one},
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
