defmodule ShotTx.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    children =
      [
        {Registry, keys: :duplicate, name: ShotTx.Prover.PubSub},
        {Registry, keys: :unique, name: ShotTx.Prover.ProcessRegistry},
        {DynamicSupervisor, name: ShotTx.SessionSpawner, strategy: :one_for_one}
      ] ++ maybe_isabelle_bridge()

    opts = [strategy: :rest_for_one, name: ShotTx.Supervisor]
    Supervisor.start_link(children, opts)
  end

  # Start the Isabelle server owner only when configured
  # (`config :shot_tx, isabelle_backend: :nitpick`).
  defp maybe_isabelle_bridge do
    case Application.get_env(:shot_tx, :isabelle_backend, :none) do
      :none -> []
      _other -> [ShotTx.IsabelleBridge]
    end
  end
end
