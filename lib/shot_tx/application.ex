defmodule ShotTx.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    # cache simplifications
    :ets.new(:term_cache, [:set, :public, :named_table, read_concurrency: true])

    children = [
      {Registry, keys: :duplicate, name: ShotTx.Prover.PubSub},
      {Registry, keys: :unique, name: ShotTx.Prover.ProcessRegistry},
      {DynamicSupervisor, name: ShotTx.SessionSpawner, strategy: :one_for_one}
    ]

    opts = [strategy: :rest_for_one, name: ShotTx.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
