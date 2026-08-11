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

  # Add the app-level Isabelle server owner when the user opts in via config
  # (`config :shot_tx, isabelle_backend: :nitpick`). Absent config leaves the
  # supervision tree untouched so users who don't need model finding pay
  # nothing at boot.
  defp maybe_isabelle_bridge do
    case Application.get_env(:shot_tx, :isabelle_backend, :none) do
      :none -> []
      _other -> [ShotTx.IsabelleBridge]
    end
  end
end
