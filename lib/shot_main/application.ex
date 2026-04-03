defmodule ShotMain.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    # cache simplifications
    :ets.new(:term_cache, [:set, :public, :named_table, read_concurrency: true])

    children = [
      {Registry, keys: :duplicate, name: ShotMain.Prover.PubSub},
      {Registry, keys: :unique, name: ShotMain.Prover.ProcessRegistry},
      {DynamicSupervisor, name: ShotMain.SessionSpawner, strategy: :one_for_one}
    ]

    # children = [
    #   {Registry, keys: :duplicate, name: ShotMain.Prover.PubSub},
    #   {Task.Supervisor, name: ShotMain.TaskSupervisor},
    #   {DynamicSupervisor, name: ShotMain.BranchSupervisor, strategy: :one_for_one},
    #   ShotMain.Prover.ContradictionAgent,
    #   ShotMain.Prover.Manager
    # ]

    opts = [strategy: :rest_for_one, name: ShotMain.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
