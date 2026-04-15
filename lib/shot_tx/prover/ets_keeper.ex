defmodule ShotTx.Prover.EtsKeeper do
  use GenServer

  def start_link({session_id, _params}) do
    name = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :ets_keeper}}}
    GenServer.start_link(__MODULE__, [], name: name)
  end

  @impl true
  def init(_args) do
    tables = %{
      stats: :ets.new(:tableau_stats, [:set, :public, write_concurrency: true]),
      tombs: :ets.new(:tableau_tombstones, [:set, :public, read_concurrency: true])
    }

    {:ok, tables}
  end

  def get_tables(session_id) do
    name = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :ets_keeper}}}
    GenServer.call(name, :get_tables)
  end

  @impl true
  def handle_call(:get_tables, _from, tables) do
    {:reply, tables, tables}
  end
end
