defmodule ShotTx.Prover.EtsKeeper do
  @moduledoc """
  GenServer that owns the ETS tables for a single proof session.

  Creates five shared, public tables on startup and keeps them alive for the
  duration of the session tree. All other processes obtain the table references
  via `get_tables/1`.

  Tables created:
  - `:stats` — proof-search counters and timing metadata.
  - `:tombs` — branch IDs that have been closed; used to poison descendants.
  - `:work_queue` — ordered set of `{priority_key, Branch.t()}` entries.
  - `:idle_queue` — branches parked waiting for iterative deepening.
  - `:traces` — per-branch rule application history for proof reconstruction.
  """

  use GenServer

  @doc "Starts the ETS keeper for the given `session_id`."
  @spec start_link({String.t(), term()}) :: GenServer.on_start()
  def start_link({session_id, _params}) do
    GenServer.start_link(__MODULE__, session_id, name: via(session_id))
  end

  @doc "Returns the ETS table map for the given `session_id`."
  @spec get_tables(String.t()) :: map()
  def get_tables(session_id) do
    GenServer.call(via(session_id), :get_tables)
  end

  @impl true
  def init(_session_id) do
    tables = %{
      stats: :ets.new(:stats, [:set, :public, read_concurrency: true, write_concurrency: true]),
      tombs: :ets.new(:tombs, [:set, :public, read_concurrency: true, write_concurrency: true]),
      work_queue:
        :ets.new(:work_queue, [
          :ordered_set,
          :public,
          read_concurrency: true,
          write_concurrency: true
        ]),
      idle_queue:
        :ets.new(:idle_queue, [:set, :public, read_concurrency: true, write_concurrency: true]),
      traces:
        :ets.new(:traces, [:set, :public, read_concurrency: true, write_concurrency: true])
    }

    :ets.insert(tables.stats, {:proof_started_at_us, System.monotonic_time(:microsecond)})

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
