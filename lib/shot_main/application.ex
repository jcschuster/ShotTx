defmodule ShotMain.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    children = [
      # Communication channel
      {Registry, keys: :duplicate, name: ShotMain.Prover.PubSub},

      # Pool for branch expanders
      {DynamicSupervisor, name: ShotMain.Prover.BranchSupervisor, strategy: :one_for_one},

      # Watcher
      ShotMain.Prover.ContradictionAgent,

      # Orchestrator
      ShotMain.Prover.Manager
    ]

    opts = [strategy: :rest_for_one, name: ShotMain.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
