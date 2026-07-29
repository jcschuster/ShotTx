defmodule ShotTx.IsabelleBridgeTest do
  @moduledoc """
  Verifies the bridge's :inactive path. Real Isabelle integration is out of
  scope for this suite — the bridge only spawns a server when the
  `:isabelle_backend` config asks for it (which never happens in test env).
  """
  use ExUnit.Case, async: false

  alias ShotTx.IsabelleBridge

  setup do
    # Sanity: test env leaves Isabelle off. If a future config change breaks
    # this assumption we want to know before we start diagnosing spurious
    # verdicts.
    assert Application.get_env(:shot_tx, :isabelle_backend, :none) == :none
    :ok
  end

  test "start_link with default config yields an :inactive bridge" do
    if Process.whereis(IsabelleBridge) do
      assert IsabelleBridge.status() == :inactive
    else
      {:ok, pid} = IsabelleBridge.start_link([])

      on_exit(fn ->
        if Process.alive?(pid) do
          try do
            GenServer.stop(pid, :normal, 1_000)
          catch
            :exit, _ -> :ok
          end
        end
      end)

      assert IsabelleBridge.status() == :inactive
    end
  end

  test "probe/await returns :unknown while the bridge is inactive" do
    unless Process.whereis(IsabelleBridge) do
      {:ok, pid} = IsabelleBridge.start_link([])

      on_exit(fn ->
        if Process.alive?(pid) do
          try do
            GenServer.stop(pid, :normal, 1_000)
          catch
            :exit, _ -> :ok
          end
        end
      end)
    end

    {:ok, ref} = IsabelleBridge.probe("theory Dummy imports Main begin end")
    assert IsabelleBridge.await(ref, 1_000) == :unknown
  end
end
