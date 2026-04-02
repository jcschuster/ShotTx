defmodule ShotMain.Prover.SessionSupervisor do
  use Supervisor

  def start_link(init_arg) do
    Supervisor.start_link(__MODULE__, init_arg)
  end

  @impl true
  def init({session_id, formulas, defs, params}) do
    children = [
      {Task.Supervisor, name: via(session_id, :task_supervisor)},
      {DynamicSupervisor, name: via(session_id, :branch_supervisor), strategy: :one_for_one},
      {ShotMain.Prover.ContradictionAgent, session_id},
      {ShotMain.Prover.Manager, {session_id, formulas, defs, params}}
    ]

    Supervisor.init(children, strategy: :rest_for_one)
  end

  defp via(session_id, name) do
    {:via, Registry, {ShotMain.Prover.ProcessRegistry, {session_id, name}}}
  end
end
