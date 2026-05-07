defmodule ShotTx.Prover.Stats do
  @moduledoc """
  Lightweight ETS-backed counters/samplers for proof-session debugging.

  Operates on the `:stats` table created by `EtsKeeper`. All ops are
  concurrency-safe and lock-free; samplers and max-trackers use CAS via
  `:ets.select_replace/2`.

  Schema:
    {key, integer}                          # counters & max trackers
    {key, count, sum, min, max}             # samplers
    {key, term}                             # one-off set/get (e.g. timestamps)
  """

  @type tables :: %{stats: :ets.table()} | :ets.table()

  defp tab(%{stats: t}), do: t
  defp tab(t), do: t

  @doc "Atomic increment-or-create."
  @spec incr(tables(), atom(), integer()) :: integer()
  def incr(tables, key, by \\ 1) do
    :ets.update_counter(tab(tables), key, by, {key, 0})
  end

  @doc "Best-effort max tracker. Retries on contention up to `retries` times."
  @spec record_max(tables(), atom(), integer(), non_neg_integer()) :: :ok
  def record_max(tables, key, value, retries \\ 3)
  def record_max(_tables, _key, _value, 0), do: :ok

  def record_max(tables, key, value, retries) do
    table = tab(tables)

    case :ets.lookup(table, key) do
      [] ->
        if :ets.insert_new(table, {key, value}),
          do: :ok,
          else: record_max(tables, key, value, retries - 1)

      [{^key, current}] when value > current ->
        ms = [{{key, current}, [], [{:const, {key, value}}]}]

        case :ets.select_replace(table, ms) do
          1 -> :ok
          0 -> record_max(tables, key, value, retries - 1)
        end

      _ ->
        :ok
    end
  end

  @doc "Records a sample. Maintains {count, sum, min, max} for the key."
  @spec record_sample(tables(), atom(), number(), non_neg_integer()) :: :ok
  def record_sample(tables, key, value, retries \\ 3)
  def record_sample(_tables, _key, _value, 0), do: :ok

  def record_sample(tables, key, value, retries) do
    table = tab(tables)

    case :ets.lookup(table, key) do
      [] ->
        if :ets.insert_new(table, {key, 1, value, value, value}),
          do: :ok,
          else: record_sample(tables, key, value, retries - 1)

      [{^key, c, s, mn, mx} = old] ->
        new = {key, c + 1, s + value, min(mn, value), max(mx, value)}
        ms = [{old, [], [{:const, new}]}]

        case :ets.select_replace(table, ms) do
          1 -> :ok
          0 -> record_sample(tables, key, value, retries - 1)
        end
    end
  end

  @doc "One-shot set (non-atomic, used for timestamps / metadata)."
  @spec set(tables(), atom(), term()) :: :ok
  def set(tables, key, value) do
    :ets.insert(tab(tables), {key, value})
    :ok
  end

  @doc "Snapshot the entire table as a map. Samplers expand to a stats map."
  @spec snapshot(tables()) :: map()
  def snapshot(tables) do
    tab(tables)
    |> :ets.tab2list()
    |> Map.new(&decode_row/1)
  end

  defp decode_row({key, count, sum, mn, mx}) do
    avg = if count > 0, do: sum / count, else: 0
    {key, %{count: count, sum: sum, min: mn, max: mx, avg: avg}}
  end

  defp decode_row({key, value}), do: {key, value}

  @doc "Pretty-prints a snapshot, sorted with samplers grouped at the bottom."
  @spec format(map()) :: String.t()
  def format(snapshot) do
    {samplers, scalars} =
      Enum.split_with(snapshot, fn {_, v} -> is_map(v) end)

    scalar_lines =
      scalars
      |> Enum.sort()
      |> Enum.map_join("\n", fn {k, v} -> "  #{k}: #{inspect(v)}" end)

    sampler_lines =
      samplers
      |> Enum.sort()
      |> Enum.map_join("\n", fn {k, %{count: c, min: mn, max: mx, avg: a, sum: s}} ->
        "  #{k}: count=#{c} min=#{mn} max=#{mx} avg=#{Float.round(a / 1, 2)} sum=#{s}"
      end)

    "Proof Stats:\n#{scalar_lines}\n#{sampler_lines}\n"
  end
end
