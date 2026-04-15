defmodule ShotTx.Prover.EtsKeeper do
  use GenServer

  def start_link({session_id, _params}) do
    GenServer.start_link(__MODULE__, session_id, name: via(session_id))
  end

  def get_tables(session_id) do
    GenServer.call(via(session_id), :get_tables)
  end

  @impl true
  def init(_session_id) do
    tables = %{
      stats: :ets.new(:stats, [:set, :public, read_concurrency: true, write_concurrency: true]),
      tombs: :ets.new(:tombs, [:set, :public, read_concurrency: true, write_concurrency: true]),
      # New lock-free queues for work stealing
      work_queue:
        :ets.new(:work_queue, [
          :ordered_set,
          :public,
          read_concurrency: true,
          write_concurrency: true
        ]),
      idle_queue:
        :ets.new(:idle_queue, [:set, :public, read_concurrency: true, write_concurrency: true])
    }

    {:ok, tables}
  end

  @impl true
  def handle_call(:get_tables, _from, tables) do
    {:reply, tables, tables}
  end

  defp via(session_id) do
    {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :ets_keeper}}}
  end
end
