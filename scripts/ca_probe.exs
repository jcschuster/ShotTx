# scripts/ca_probe.exs
#
# Targeted follow-up to the 2026-08-15 ablation sweep: measures what the
# ContradictionAgent actually does under a full worker pool and under a serial
# pool, on the subset of problems where it does anything at all.
#
# The sweep CSV carries `csp_calls` and `csp_succeeded` only. `Stats` also
# records `csp_calls_skipped`, `csp_duration_us`, `csp_branches_count`,
# `csp_max_domain_size` and `csp_total_candidates`, and `TptpRunner` exports
# none of them. This script reads them straight off the stats snapshot that
# `Prover.prove/3` returns, so nothing under `lib/` has to change.
#
# ## The question it answers
#
# Adding workers multiplies inference by about three and leaves the number of
# global closure searches unchanged. Two explanations are consistent with the
# sweep data:
#
#   (a) time-saturated: the agent spends most of the budget inside
#       `find_global_closure/3`, and a wider frontier makes each search
#       exponentially more expensive.
#   (b) trigger-starved: searches are cheap but rarely dispatched, because
#       `insufficient_options?/1` is true as soon as one open branch has no
#       clash candidate, and because at most one search runs at a time.
#
# `csp_duration_sum_us` against `time_ms` separates them. Under (a) the ratio
# is large and grows with the pool; under (b) it stays small while
# `csp_skipped` grows.
#
# ## One counter this cannot reach without a code change
#
# Checks suppressed because a search was already in flight are not recorded:
# the first clause of `check_global_closure/1` (contradiction_agent.ex:428)
# returns without incrementing anything. To measure that path, add one line:
#
#     defp check_global_closure(%__MODULE__{pending_search: %Task{}} = state) do
#       Stats.incr(state.ets_tables, :csp_calls_inflight_suppressed)
#       {:noreply, state}
#     end
#
# The script reads that key if it is present and records 0 if it is not, so it
# runs either way. Without the line, `csp_skipped` still covers the
# insufficient-options path, which is the larger of the two.
#
# ## Usage
#
#     export TPTP_ROOT=/opt/TPTP
#     mix run scripts/ca_probe.exs             # run the probe
#     mix run scripts/ca_probe.exs --summarise # print the comparison
#
# Environment:
#
#   TPTP_ROOT           required, the TPTP directory containing Problems/
#   CA_PROBE_SWEEP      sweep dir to take the problem set from
#                       (default ablation_results/2026-08-15)
#   CA_PROBE_OUT        output dir (default ablation_results/ca_probe)
#   CA_PROBE_TIMEOUT    prover budget in ms (default 2000, matching the sweep)
#   CA_PROBE_REPEATS    runs per (problem, configuration) pair (default 1).
#                       Set to 3 to also get a run-to-run variance estimate,
#                       which is what the chapter's noise floor currently
#                       lacks. Cost scales linearly.
#   CA_PROBE_LIMIT      cap the problem count, for a smoke test
#
# Resumable: an interrupted run re-invoked with the same CA_PROBE_OUT skips
# every (label, problem, rep) row already written. Pause with
# `touch <CA_PROBE_OUT>/STOP` and resume by deleting the file.
#
# Cost: the problem set is the 1677 problems on which either the baseline or
# the serial configuration dispatched at least one search. Summing the sweep's
# own wall clock over that set gives about 1.5 hours per repeat for the two
# configurations together, plus parsing, which is paid once per problem here
# rather than once per configuration.

defmodule CaProbe do
  @moduledoc false

  alias ShotDs.Tptp
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover

  @stop_sentinel "STOP"
  @parse_timeout 60_000
  @prove_grace 10_000

  @columns ~w(
    label problem rep order result time_ms
    steps active_branches_max branches_split branches_closed
    csp_calls csp_succeeded csp_failed csp_skipped csp_inflight_suppressed
    csp_duration_sum_us csp_duration_max_us
    csp_branches_avg csp_max_domain_avg csp_candidates_avg
    details
  )

  # Column offsets in the sweep CSV written by TptpRunner.
  @sweep_problem_col 1
  @sweep_csp_calls_col 13

  ############################################################################
  # ENTRY POINT
  ############################################################################

  def main([mode | _]) when mode in ~w(--summarise --summarize summarise summarize),
    do: summarise()

  def main(_argv), do: run()

  ############################################################################
  # RUN
  ############################################################################

  defp run do
    Logger.configure(level: :none)

    tptp_root =
      System.get_env("TPTP_ROOT") ||
        raise "TPTP_ROOT is missing. Set it to your TPTP directory."

    sweep_dir = env("CA_PROBE_SWEEP", "ablation_results/2026-08-15")
    out_dir = env("CA_PROBE_OUT", "ablation_results/ca_probe")
    budget = env_int("CA_PROBE_TIMEOUT", 2_000)
    repeats = env_int("CA_PROBE_REPEATS", 1)
    limit = env_int("CA_PROBE_LIMIT", 0)

    File.mkdir_p!(out_dir)
    csv_path = Path.join(out_dir, "ca_probe.csv")
    ensure_header(csv_path)
    write_meta(Path.join(out_dir, "ca_probe.meta"), budget, repeats, sweep_dir)

    problems = probe_set(sweep_dir)
    problems = if limit > 0, do: Enum.take(problems, limit), else: problems
    done = load_done(csv_path)

    configs = configs(budget)
    planned = length(problems) * length(configs) * repeats
    remaining = planned - MapSet.size(done)

    notice(
      "ca_probe: #{length(problems)} problem(s) x #{length(configs)} config(s) x " <>
        "#{repeats} rep(s) = #{planned} run(s); #{MapSet.size(done)} already recorded, " <>
        "#{remaining} to go."
    )

    {:ok, sup} = Task.Supervisor.start_link()

    ctx = %{
      tptp_root: tptp_root,
      csv_path: csv_path,
      stop_path: Path.join(out_dir, @stop_sentinel),
      task_sup: sup,
      configs: configs,
      repeats: repeats,
      done: done,
      prove_timeout: budget + @prove_grace,
      completed: 0,
      total: remaining,
      started_at_ms: System.monotonic_time(:millisecond)
    }

    problems
    |> Enum.with_index()
    |> Enum.reduce_while(ctx, fn {rel_path, index}, acc ->
      if File.exists?(acc.stop_path) do
        notice("ca_probe: STOP sentinel present, halting.")
        {:halt, acc}
      else
        {:cont, process_problem(rel_path, index, acc)}
      end
    end)

    notice("ca_probe: done.")
    :ok
  end

  # Both configurations run on one parse of the problem. The parser never sees
  # `%Parameters{}`, so a second parse would produce the same terms at the same
  # cost, and holding the pair together keeps machine state comparable across
  # the two runs being compared.
  defp process_problem(rel_path, index, ctx) do
    pending =
      for rep <- 1..ctx.repeats,
          {label, _params} <- ctx.configs,
          not MapSet.member?(ctx.done, {label, rel_path, rep}),
          do: {label, rep}

    if pending == [] do
      ctx
    else
      abs_path = Path.join([ctx.tptp_root, "Problems", rel_path])

      case parse(abs_path, ctx) do
        {:ok, problem} ->
          ctx = run_pairs(problem, rel_path, index, ctx)
          Prover.release_term_pool()
          ctx

        {:error, tag, message} ->
          notice("[skip] #{rel_path} #{tag}: #{message}")
          ctx
      end
    end
  end

  defp run_pairs(problem, rel_path, index, ctx) do
    Enum.reduce(1..ctx.repeats, ctx, fn rep, acc ->
      # Alternating the order within each problem keeps a warm-up effect from
      # loading onto whichever configuration always runs first. `order` records
      # the position so the effect can be checked rather than assumed.
      ordered =
        if rem(index + rep, 2) == 0,
          do: acc.configs,
          else: Enum.reverse(acc.configs)

      ordered
      |> Enum.with_index(1)
      |> Enum.reduce(acc, fn {{label, params}, order}, inner ->
        if MapSet.member?(inner.done, {label, rel_path, rep}) do
          inner
        else
          run_one(problem, rel_path, label, params, rep, order, inner)
        end
      end)
    end)
  end

  defp run_one(problem, rel_path, label, params, rep, order, ctx) do
    {micro, {result, details, stats}} =
      :timer.tc(fn -> prove_isolated(problem, params, ctx) end)

    time_ms = div(micro, 1000)

    append_row(
      ctx.csv_path,
      [label, rel_path, rep, order, result, time_ms] ++
        stats_cells(stats) ++ [sanitise(details)]
    )

    ctx = %{ctx | completed: ctx.completed + 1}

    notice(
      "[#{label}] #{ctx.completed}/#{ctx.total} | #{rel_path} rep#{rep} -> " <>
        "#{result} #{time_ms}ms csp=#{Map.get(stats, :csp_calls, 0)}" <>
        "/#{Map.get(stats, :csp_skipped, 0)}skip " <>
        "#{div(Map.get(stats, :csp_duration_sum_us, 0), 1000)}ms-in-csp | " <>
        "elapsed #{elapsed(ctx)} eta #{eta(ctx)}"
    )

    ctx
  end

  ############################################################################
  # PROVING
  ############################################################################

  defp prove_isolated(%{conjecture: nil}, _params, _ctx), do: {:no_conjecture, "", %{}}

  defp prove_isolated(problem, params, ctx) do
    case isolated(ctx.task_sup, ctx.prove_timeout, fn -> prove(problem, params) end) do
      {:ok, outcome} -> outcome
      {:exit, reason} -> {:prover_error, inspect(reason), %{}}
      :timeout -> {:hard_timeout, "killed after #{ctx.prove_timeout}ms", %{}}
    end
  end

  # Mirrors `TptpRunner.prove_problem/2`, keeping the option construction
  # identical so the numbers stay comparable with the sweep CSVs.
  defp prove(problem, params) do
    {_name, conclusion} = problem.conjecture
    axioms = Enum.map(problem.axioms, fn {_name, term} -> term end)

    opts =
      params
      |> Map.from_struct()
      |> Enum.into([])
      |> Keyword.put(:defs, problem.definitions)
      |> Keyword.put(:stats, true)

    {result, raw} = Prover.prove(conclusion, axioms, opts)
    stats = extract_stats(raw)

    case result do
      {:thm, _} -> {:thm, "", stats}
      {:csa, model, _} -> {:csa, String.slice(model, 0, 120), stats}
      :unknown -> {:unk, "", stats}
      {:timeout, _} -> {:timeout, "", stats}
      {:error, reason} -> {:prover_error, inspect(reason), stats}
    end
  rescue
    e -> {:prover_error, Exception.message(e), %{}}
  catch
    :exit, reason -> {:prover_error, inspect(reason), %{}}
  end

  # `csp_duration_us` and the three domain-size keys are recorded through
  # `Stats.record_sample/4`, so the snapshot holds
  # `%{count:, sum:, min:, max:, avg:}` rather than a scalar, and the key is
  # absent when no search ever ran.
  defp extract_stats(raw) do
    report = Prover.compile_stats(raw)
    csp = report.csp

    %{
      steps: report.search.steps_total,
      active_branches_max: report.branches.active_max,
      branches_split: report.branches.split,
      branches_closed: report.branches.closed_locally,
      csp_calls: csp.calls,
      csp_succeeded: csp.succeeded,
      csp_failed: csp.failed,
      csp_skipped: csp.skipped,
      csp_inflight_suppressed: Map.get(raw, :csp_calls_inflight_suppressed, 0),
      csp_duration_sum_us: sample(csp.duration_us, :sum),
      csp_duration_max_us: sample(csp.duration_us, :max),
      csp_branches_avg: sample(csp.branches_count, :avg),
      csp_max_domain_avg: sample(csp.max_domain_size, :avg),
      csp_candidates_avg: sample(csp.total_candidates, :avg)
    }
  end

  defp sample(nil, _key), do: 0
  defp sample(map, key) when is_map(map), do: Map.get(map, key, 0)
  defp sample(_other, _key), do: 0

  defp parse(abs_path, ctx) do
    parse_fun = fn ->
      try do
        Tptp.parse_tptp_file(abs_path, :custom)
      rescue
        e -> {:error, Exception.message(e)}
      end
    end

    case isolated(ctx.task_sup, @parse_timeout, parse_fun) do
      {:ok, {:ok, problem}} -> {:ok, problem}
      {:ok, {:error, reason}} -> {:error, :parser_error, to_string(reason)}
      {:exit, reason} -> {:error, :parser_error, inspect(reason)}
      :timeout -> {:error, :parse_timeout, "parse exceeded #{@parse_timeout}ms"}
    end
  end

  # The prover's own timeout is cooperative, so a separate process the caller
  # can kill is the only hard wall-clock bound available.
  defp isolated(task_sup, timeout, fun) do
    task = Task.Supervisor.async_nolink(task_sup, fun)

    case Task.yield(task, timeout) || Task.shutdown(task, :brutal_kill) do
      {:ok, value} -> {:ok, value}
      {:exit, reason} -> {:exit, reason}
      nil -> :timeout
    end
  end

  ############################################################################
  # CONFIGURATIONS
  ############################################################################

  # Only `worker_pool_size` differs. Everything else is the sweep baseline, so
  # the rows here can be read against `ablation_results/2026-08-15/*.csv`.
  defp configs(budget) do
    [
      {"probe_auto", %Parameters{timeout: budget}},
      {"probe_serial", %Parameters{timeout: budget, worker_pool_size: 1}}
    ]
  end

  ############################################################################
  # PROBLEM SET
  ############################################################################

  # Every problem on which either sweep configuration dispatched at least one
  # global closure search. Problems the agent never engaged carry no signal for
  # the question and would only spend budget.
  defp probe_set(sweep_dir) do
    ["baseline.csv", "serial.csv"]
    |> Enum.map(&Path.join(sweep_dir, &1))
    |> Enum.flat_map(&problems_with_csp/1)
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp problems_with_csp(path) do
    unless File.exists?(path), do: raise("sweep CSV not found: #{path}")

    path
    |> File.stream!()
    |> Stream.drop(1)
    |> Stream.map(&(&1 |> String.trim() |> String.split(",")))
    |> Stream.filter(fn cells ->
      length(cells) > @sweep_csp_calls_col and
        to_int(Enum.at(cells, @sweep_csp_calls_col)) > 0
    end)
    |> Stream.map(&Enum.at(&1, @sweep_problem_col))
    |> Enum.to_list()
  end

  ############################################################################
  # SUMMARY
  ############################################################################

  defp summarise do
    out_dir = env("CA_PROBE_OUT", "ablation_results/ca_probe")
    path = Path.join(out_dir, "ca_probe.csv")
    rows = read_rows(path)

    if rows == [] do
      notice("ca_probe: no rows in #{path}.")
    else
      by_label = Enum.group_by(rows, & &1["label"])

      IO.puts("")
      IO.puts("ca_probe summary over #{length(rows)} run(s) from #{path}")
      IO.puts(String.duplicate("=", 78))

      Enum.each(by_label, fn {label, rs} ->
        n = length(rs)
        steps = sum(rs, "steps")
        calls = sum(rs, "csp_calls")
        skipped = sum(rs, "csp_skipped")
        suppressed = sum(rs, "csp_inflight_suppressed")
        csp_us = sum(rs, "csp_duration_sum_us")
        wall_us = sum(rs, "time_ms") * 1000

        IO.puts("")
        IO.puts("#{label}  (#{n} runs)")
        IO.puts("  steps total                  #{steps}")
        IO.puts("  peak open branches, median   #{median(rs, "active_branches_max")}")
        IO.puts("  global closure searches      #{calls}")
        IO.puts("  ... per 1000 steps           #{ratio(calls * 1000, steps)}")
        IO.puts("  skipped, no options          #{skipped}")
        IO.puts("  suppressed, search in flight #{suppressed} #{suppressed_note(suppressed)}")
        IO.puts("  time inside closure search   #{div(csp_us, 1000)} ms")
        IO.puts("  ... as share of wall clock   #{percent(csp_us, wall_us)}")
        IO.puts("  longest single search        #{div(max_of(rs, "csp_duration_max_us"), 1000)} ms")
        IO.puts("  branches per search, mean    #{mean(rs, "csp_branches_avg")}")
        IO.puts("  candidates per search, mean  #{mean(rs, "csp_candidates_avg")}")
        IO.puts("  solved                       #{count_where(rs, "result", ["thm", "csa"])}")
      end)

      IO.puts("")
      IO.puts(String.duplicate("-", 78))
      IO.puts("Reading: a large and pool-sensitive 'share of wall clock' means the")
      IO.puts("agent is time-saturated. A small share with 'skipped' or 'suppressed'")
      IO.puts("rising against a flat search count means it is trigger-starved.")

      report_variance(rows)
    end
  end

  # With CA_PROBE_REPEATS > 1 the same (label, problem) pair appears more than
  # once, which gives the run-to-run stability the sweep could not measure.
  defp report_variance(rows) do
    groups =
      rows
      |> Enum.group_by(&{&1["label"], &1["problem"]})
      |> Enum.filter(fn {_key, rs} -> length(rs) > 1 end)

    if groups != [] do
      unstable =
        Enum.filter(groups, fn {_key, rs} ->
          rs |> Enum.map(& &1["result"]) |> Enum.uniq() |> length() > 1
        end)

      IO.puts("")
      IO.puts("Repeated pairs: #{length(groups)}; answering differently across repeats: " <>
                "#{length(unstable)}")

      unstable
      |> Enum.take(20)
      |> Enum.each(fn {{label, problem}, rs} ->
        IO.puts("  #{label} #{problem}: #{Enum.map_join(rs, ", ", & &1["result"])}")
      end)
    end
  end

  ############################################################################
  # CSV
  ############################################################################

  defp ensure_header(path) do
    unless File.exists?(path) do
      File.write!(path, Enum.join(@columns, ",") <> "\n")
    end
  end

  defp write_meta(path, budget, repeats, sweep_dir) do
    unless File.exists?(path) do
      sha =
        case System.cmd("git", ["rev-parse", "HEAD"], stderr_to_stdout: true) do
          {out, 0} -> String.trim(out)
          _ -> "unknown"
        end

      File.write!(path, """
      started_at: #{DateTime.utc_now() |> DateTime.to_iso8601()}
      git_sha: #{sha}
      schedulers_online: #{System.schedulers_online()}
      timeout_ms: #{budget}
      repeats: #{repeats}
      problem_set: csp_calls > 0 in baseline or serial of #{sweep_dir}
      """)
    end
  end

  defp append_row(path, cells) do
    File.write!(path, Enum.map_join(cells, ",", &to_cell/1) <> "\n", [:append])
  end

  defp stats_cells(stats) do
    ~w(steps active_branches_max branches_split branches_closed
       csp_calls csp_succeeded csp_failed csp_skipped csp_inflight_suppressed
       csp_duration_sum_us csp_duration_max_us
       csp_branches_avg csp_max_domain_avg csp_candidates_avg)a
    |> Enum.map(&Map.get(stats, &1, 0))
  end

  defp load_done(path) do
    path
    |> read_rows()
    |> Enum.map(&{&1["label"], &1["problem"], to_int(&1["rep"])})
    |> MapSet.new()
  end

  defp read_rows(path) do
    if File.exists?(path) do
      path
      |> File.stream!()
      |> Enum.map(&(&1 |> String.trim() |> String.split(",")))
      |> Enum.reject(&(&1 == [""]))
      |> case do
        [] -> []
        [header | lines] -> Enum.map(lines, &Map.new(Enum.zip(header, &1)))
      end
    else
      []
    end
  end

  ############################################################################
  # HELPERS
  ############################################################################

  defp env(key, default), do: System.get_env(key) || default
  defp env_int(key, default), do: key |> System.get_env() |> to_int(default)

  defp to_int(value, default \\ 0)
  defp to_int(nil, default), do: default
  defp to_int(value, default) when is_binary(value) do
    case Integer.parse(String.trim(value)) do
      {n, _rest} -> n
      :error -> default
    end
  end

  defp to_cell(value) when is_float(value), do: :erlang.float_to_binary(value, decimals: 2)
  defp to_cell(value) when is_atom(value), do: Atom.to_string(value)
  defp to_cell(value), do: to_string(value)

  defp sanitise(nil), do: ""
  defp sanitise(text), do: String.replace(to_string(text), ~r/[,;\r\n]/, " ")

  defp num(row, key) do
    case Float.parse(Map.get(row, key, "0") || "0") do
      {f, _rest} -> f
      :error -> 0.0
    end
  end

  defp sum(rows, key), do: rows |> Enum.map(&num(&1, key)) |> Enum.sum() |> round()
  defp max_of(rows, key), do: rows |> Enum.map(&num(&1, key)) |> Enum.max(fn -> 0 end) |> round()

  defp mean([], _key), do: "0.00"

  defp mean(rows, key) do
    values = Enum.map(rows, &num(&1, key))
    fmt(Enum.sum(values) / length(values))
  end

  defp median(rows, key) do
    values = rows |> Enum.map(&num(&1, key)) |> Enum.sort()
    n = length(values)

    case n do
      0 -> "0"
      _ when rem(n, 2) == 1 -> fmt(Enum.at(values, div(n, 2)))
      _ -> fmt((Enum.at(values, div(n, 2) - 1) + Enum.at(values, div(n, 2))) / 2)
    end
  end

  defp count_where(rows, key, values) do
    Enum.count(rows, &(Map.get(&1, key) in values))
  end

  defp ratio(_num, 0), do: "n/a"
  defp ratio(numerator, denominator), do: fmt(numerator / denominator)

  defp percent(_num, 0), do: "n/a"
  defp percent(numerator, denominator), do: fmt(100 * numerator / denominator) <> " %"

  defp fmt(value) when is_float(value), do: :erlang.float_to_binary(value, decimals: 2)
  defp fmt(value), do: to_string(value)

  defp suppressed_note(0),
    do: "(counter absent: see the one-line patch in the header comment)"

  defp suppressed_note(_), do: ""

  defp elapsed(ctx), do: hms(System.monotonic_time(:millisecond) - ctx.started_at_ms)

  defp eta(%{completed: 0}), do: "--:--:--"

  defp eta(ctx) do
    spent = System.monotonic_time(:millisecond) - ctx.started_at_ms
    hms(round(spent / ctx.completed * max(ctx.total - ctx.completed, 0)))
  end

  defp hms(ms) do
    total = div(ms, 1000)

    [div(total, 3600), rem(div(total, 60), 60), rem(total, 60)]
    |> Enum.map_join(":", &String.pad_leading(Integer.to_string(&1), 2, "0"))
  end

  defp notice(message) do
    stamp = Calendar.strftime(DateTime.utc_now(), "%m-%d %H:%M:%S")
    IO.puts("[#{stamp}] #{message}")
  end
end

CaProbe.main(System.argv())
