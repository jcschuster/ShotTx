defmodule ShotTx.Prover.Stats do
  @moduledoc """
  Lightweight ETS-backed counters/samplers for proof-session debugging,
  plus user-facing helpers to compile and pretty-print a snapshot.

  Operates on the `:stats` table created by `EtsKeeper`. All ops are
  concurrency-safe and lock-free; samplers and max-trackers use CAS via
  `:ets.select_replace/2`.

  Schema:
    {key, integer}                          # counters & max trackers
    {key, count, sum, min, max}             # samplers
    {key, term}                             # one-off set/get (e.g. timestamps)
  """

  @type tables :: %{stats: :ets.table()} | :ets.table()
  @type sampler :: %{
          count: non_neg_integer(),
          sum: number(),
          min: number(),
          max: number(),
          avg: number()
        }
  @type snapshot :: %{atom() => integer() | sampler() | term()}
  @type report :: %{
          timing: map(),
          search: map(),
          rules: map(),
          branches: map(),
          csp: map()
        }

  defp tab(%{stats: t}), do: t
  defp tab(t), do: t

  ##############################################################################
  # RAW COUNTER API (used by the prover internals)
  ##############################################################################

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
  @spec snapshot(tables()) :: snapshot()
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

  ##############################################################################
  # USER-FACING COMPILATION & FORMATTING
  ##############################################################################

  @rule_keys ~w(
    rule_alpha rule_beta rule_gamma rule_gamma_finite rule_delta
    rule_rename rule_atomic rule_instantiate rule_prim_subst
    rule_contradiction rule_tautology rule_other
  )a

  @branch_counter_keys ~w(
    branches_activated_total branches_split branches_instantiate_children
    branches_closed_locally branches_saturated
  )a

  @doc """
  Compiles a raw snapshot into a structured report grouped by category:
  `:timing`, `:search`, `:rules`, `:branches`, `:csp`.

  Derived metrics included:

    * `timing.duration_us` / `duration_ms` from the start/finish timestamps.
    * `search.steps_per_sec` from `steps_total` and `duration_us`.
    * `csp.success_rate` from `csp_calls_succeeded / csp_calls`.

  Idempotent: a compiled report passed in is returned unchanged.
  """
  @spec compile(snapshot() | report()) :: report()
  def compile(%{timing: _, search: _, rules: _, branches: _, csp: _} = report), do: report

  def compile(snapshot) when is_map(snapshot) do
    duration_us = duration_us(snapshot)

    %{
      timing: timing_section(snapshot, duration_us),
      search: search_section(snapshot, duration_us),
      rules: rules_section(snapshot),
      branches: branches_section(snapshot),
      csp: csp_section(snapshot)
    }
  end

  @doc "Total proof duration in microseconds, or `nil` if timing data is missing."
  @spec duration_us(snapshot()) :: non_neg_integer() | nil
  def duration_us(snapshot) do
    case {Map.get(snapshot, :proof_started_at_us), Map.get(snapshot, :proof_finished_at_us)} do
      {start, finish} when is_integer(start) and is_integer(finish) -> finish - start
      _ -> nil
    end
  end

  defp timing_section(snapshot, duration_us) do
    %{
      duration_us: duration_us,
      duration_ms: duration_us && duration_us / 1_000,
      aborted: Map.get(snapshot, :aborted, false)
    }
  end

  defp search_section(snapshot, duration_us) do
    steps = Map.get(snapshot, :steps_total, 0)

    steps_per_sec =
      case duration_us do
        nil -> nil
        0 -> nil
        us -> steps * 1_000_000 / us
      end

    %{
      steps_total: steps,
      steps_per_sec: steps_per_sec,
      worker_yields: Map.get(snapshot, :worker_yields, 0)
    }
  end

  defp rules_section(snapshot) do
    counts =
      Map.new(@rule_keys, fn key ->
        short = key |> Atom.to_string() |> String.replace_prefix("rule_", "") |> String.to_atom()
        {short, Map.get(snapshot, key, 0)}
      end)

    Map.put(counts, :total, counts |> Map.values() |> Enum.sum())
  end

  defp branches_section(snapshot) do
    base =
      Map.new(@branch_counter_keys, fn key ->
        short =
          key |> Atom.to_string() |> String.replace_prefix("branches_", "") |> String.to_atom()

        {short, Map.get(snapshot, key, 0)}
      end)

    Map.put(base, :active_max, Map.get(snapshot, :active_branches_max, 0))
  end

  defp csp_section(snapshot) do
    calls = Map.get(snapshot, :csp_calls, 0)
    succeeded = Map.get(snapshot, :csp_calls_succeeded, 0)

    %{
      calls: calls,
      succeeded: succeeded,
      failed: Map.get(snapshot, :csp_calls_failed, 0),
      skipped: Map.get(snapshot, :csp_calls_skipped, 0),
      success_rate: if(calls > 0, do: succeeded / calls, else: nil),
      duration_us: Map.get(snapshot, :csp_duration_us),
      branches_count: Map.get(snapshot, :csp_branches_count),
      max_domain_size: Map.get(snapshot, :csp_max_domain_size),
      total_candidates: Map.get(snapshot, :csp_total_candidates)
    }
  end

  ##############################################################################
  # FORMATTING
  ##############################################################################

  @doc """
  Pretty-prints stats as a human-readable string. Accepts either a raw
  snapshot or a compiled report.

  Options:

    * `:verbose` (default `false`) — include rule/branch counters whose value
      is zero. By default they are hidden to reduce noise.
    * `:sections` (default `:all`) — subset of `[:timing, :search, :rules,
      :branches, :csp]` to render, in the given order.
  """
  @spec format(snapshot() | report(), keyword()) :: String.t()
  def format(stats, opts \\ []) do
    report = compile(stats)
    verbose? = Keyword.get(opts, :verbose, false)
    sections = Keyword.get(opts, :sections, [:timing, :search, :rules, :branches, :csp])

    blocks =
      sections
      |> Enum.map(&section_block(&1, report, verbose?))
      |> Enum.reject(&(&1 == ""))

    header = "Proof Stats\n" <> String.duplicate("=", 50)
    header <> "\n\n" <> Enum.join(blocks, "\n\n") <> "\n"
  end

  defp section_block(:timing, %{timing: t}, _verbose) do
    rows =
      [
        {"duration", format_duration(t.duration_us)},
        {"status", if(t.aborted, do: "aborted", else: "completed")}
      ]

    render_section("Timing", rows)
  end

  defp section_block(:search, %{search: s}, _verbose) do
    rows =
      [
        {"steps", format_int(s.steps_total)},
        {"steps/sec", format_rate(s.steps_per_sec)},
        {"worker yields", format_int(s.worker_yields)}
      ]

    render_section("Search", rows)
  end

  defp section_block(:rules, %{rules: rules}, verbose) do
    {total, per_rule} = Map.pop(rules, :total, 0)

    entries =
      per_rule
      |> Enum.sort_by(fn {_k, v} -> -v end)
      |> Enum.reject(fn {_k, v} -> not verbose and v == 0 end)

    if entries == [] and total == 0 do
      ""
    else
      rule_rows =
        Enum.map(entries, fn {name, count} ->
          {Atom.to_string(name), "#{format_int(count)}  #{format_pct(count, total)}"}
        end)

      render_section("Rules", rule_rows ++ [{"total", format_int(total)}])
    end
  end

  defp section_block(:branches, %{branches: b}, verbose) do
    rows =
      [
        {"activated", b.activated_total},
        {"active (max)", b.active_max},
        {"split", b.split},
        {"instantiate children", b.instantiate_children},
        {"closed locally", b.closed_locally},
        {"saturated", b.saturated}
      ]
      |> Enum.reject(fn {_label, v} -> not verbose and v == 0 end)
      |> Enum.map(fn {label, v} -> {label, format_int(v)} end)

    if rows == [], do: "", else: render_section("Branches", rows)
  end

  defp section_block(:csp, %{csp: csp}, verbose) do
    rate =
      case csp.success_rate do
        nil -> "—"
        r -> "#{Float.round(r * 100, 1)}% (#{csp.succeeded}/#{csp.calls})"
      end

    scalar_rows =
      [
        {"calls", csp.calls},
        {"success rate", nil},
        {"failed", csp.failed},
        {"skipped", csp.skipped}
      ]

    base_rows =
      scalar_rows
      |> Enum.reject(fn
        {"success rate", _} -> false
        {_label, 0} -> not verbose
        _ -> false
      end)
      |> Enum.map(fn
        {"success rate", _} -> {"success rate", rate}
        {label, v} -> {label, format_int(v)}
      end)

    sampler_rows =
      [
        {"duration μs", csp.duration_us},
        {"branches/call", csp.branches_count},
        {"max domain size", csp.max_domain_size},
        {"total candidates", csp.total_candidates}
      ]
      |> Enum.reject(fn {_label, sampler} -> is_nil(sampler) end)
      |> Enum.map(fn {label, sampler} -> {label, format_sampler(sampler)} end)

    rows = base_rows ++ sampler_rows

    if rows == [], do: "", else: render_section("CSP", rows)
  end

  defp render_section(title, rows) do
    label_width =
      rows
      |> Enum.map(fn {label, _} -> String.length(label) end)
      |> Enum.max(fn -> 0 end)

    body =
      Enum.map_join(rows, "\n", fn {label, value} ->
        "  " <> String.pad_trailing(label, label_width) <> "  " <> value
      end)

    "#{title}\n#{body}"
  end

  defp format_duration(nil), do: "—"
  defp format_duration(us) when us < 1_000, do: "#{us} μs"
  defp format_duration(us) when us < 1_000_000, do: "#{Float.round(us / 1_000, 2)} ms"
  defp format_duration(us), do: "#{Float.round(us / 1_000_000, 3)} s"

  defp format_int(n) when is_integer(n) do
    n
    |> Integer.to_string()
    |> String.reverse()
    |> String.replace(~r/(\d{3})(?=\d)/, "\\1,")
    |> String.reverse()
  end

  defp format_int(n), do: inspect(n)

  defp format_rate(nil), do: "—"
  defp format_rate(r) when r >= 1000, do: format_int(round(r))
  defp format_rate(r), do: "#{Float.round(r, 2)}"

  defp format_pct(_count, 0), do: ""
  defp format_pct(count, total), do: "(#{Float.round(count * 100 / total, 1)}%)"

  defp format_sampler(%{count: c, min: mn, max: mx, avg: a}) do
    "avg=#{format_number(a)} min=#{format_number(mn)} max=#{format_number(mx)} (n=#{c})"
  end

  defp format_number(n) when is_integer(n), do: format_int(n)

  defp format_number(n) when is_float(n) do
    if n == trunc(n) and abs(n) < 1.0e15,
      do: format_int(trunc(n)),
      else: :erlang.float_to_binary(n, decimals: 2)
  end
end
