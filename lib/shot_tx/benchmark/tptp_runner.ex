defmodule ShotTx.Benchmark.TptpRunner do
  @moduledoc """
  Runs the prover across the TPTP TH0/TH1 problem library and records one CSV
  row per problem. Designed for long unattended benchmark sweeps on a laptop:

    * **Parameterised.** Accepts a `ShotTx.Data.Parameters` struct so an
      ablation sweep can invoke the same runner once per configuration.
    * **Resumable.** Each call reads the destination CSV and skips any
      `(run_label, problem)` row that is already recorded. Interrupting the
      runner (Ctrl-C, kill, laptop lid) and re-invoking with the same
      arguments picks up where it left off; at worst the in-flight problem is
      re-run.
    * **Pausable.** Between problems, the runner checks for a `STOP`
      sentinel file in the output directory and exits cleanly if it exists.
      Delete the file to resume.
    * **Wall-clock bounded.** Parsing and proving each run in a throwaway
      process the runner kills when its budget expires, so no single problem
      can stall a sweep. A killed phase is still recorded as a CSV row
      (`parse_timeout` / `hard_timeout`), so the data set stays complete.
    * **SZS-scored.** The TPTP problem header (`% Status : ...`) is parsed
      from each file so the CSV records whether the prover's answer matched
      the expected TPTP status.
    * **Snapshotted.** A `<label>.meta` sidecar file is written on the first
      run of each config, capturing the start timestamp, `git rev-parse HEAD`,
      and the full `%Parameters{}` value. On resume, if the current call's
      parameters disagree with the recorded ones, the runner logs a warning
      and continues — so a mid-sweep code change never silently mixes
      configurations into one CSV without a trail.

  ### CSV columns

      run_label, problem, language, expected_szs, result, correct, time_ms,
      steps, worker_yields, rules_total, active_branches_max,
      branches_closed, branches_saturated, csp_calls, csp_succeeded, details

    * `run_label` — the label of the parameter configuration.
    * `problem` — path relative to `TPTP/Problems`, e.g. `SYO/SYO001^1.p`.
    * `language` — `TH0` | `TH1` | `unknown` (from the file `SPC` header).
    * `expected_szs` — TPTP-declared status: `Theorem`, `CounterSatisfiable`,
      `Unknown`, `Open`, … (or `unknown` if the header is missing).
    * `result` — `thm` | `csa` | `unk` | `timeout` | `parse_timeout` |
      `hard_timeout` | `parser_error` | `prover_error` | `no_conjecture`.
      `timeout` is the prover reporting its own budget exhausted;
      `hard_timeout` is the runner killing a prover that overran it anyway;
      `parse_timeout` is the parser killed before the prover ever started.
    * `correct` — `yes` | `no` | `n/a`. Only decidable when both the expected
      status is one of `Theorem` / `CounterSatisfiable` and the prover
      terminated with a definite answer.
    * `time_ms` — wall-clock milliseconds for parse + prove.
    * `steps`, `worker_yields` — proof-search counters (see
      `ShotTx.Prover.Stats`).
    * `rules_total` — total rule firings across all workers.
    * `active_branches_max` — peak open-branch count.
    * `branches_closed`, `branches_saturated` — branches closed locally vs.
      saturated (SAT witnesses).
    * `csp_calls`, `csp_succeeded` — CSP solver calls and successes.
    * `details` — free-form detail string, commas/semicolons replaced with
      spaces for CSV safety. Empty for cases that produced no stats
      (`parser_error`, `no_conjecture`, catastrophic `prover_error`).

  ### Options

    * `label` (default `"default"`) — configuration label written into every
      row. Also determines the CSV filename (`<output_dir>/<label>.csv`).
    * `output_dir` (default `"bench_results"`) — directory that holds all CSV
      files and the `STOP` sentinel for this run. Persist a stable name
      across resumes.
    * `language` (default `:both`) — `:th0`, `:th1`, or `:both`. Filters
      problems by the `SPC` header line.
    * `problem_limit` (default `nil`) — max number of problems to process in
      this invocation (after already-completed rows are skipped). Handy for
      smoke tests.
    * `problem_filter` (default `nil`) — a function `(relative_path -> boolean)`.
    * `log_level` (default `:none`) — level applied to the *prover's* Logger for
      the duration of the run. The runner's own progress and result lines go
      straight to standard output and are unaffected. Raising it costs search
      time as well as screen space: Logger skips argument evaluation for
      suppressed calls, and several hot sites build their message eagerly.
    * `parse_timeout` (default `60_000` ms) — wall-clock budget for parsing
      one problem. A handful of TPTP problems pull in enough `include`s to
      keep the parser busy for many minutes; those are killed at the budget
      and recorded as `parse_timeout`.
    * `prove_grace` (default `10_000` ms) — slack added to
      `params.timeout` to obtain the wall-clock budget for the proof attempt.
      The prover's own timeout is cooperative (workers have to come back
      around to notice it); this is the hard backstop, recorded as
      `hard_timeout`.

  ### Parse cache

  The parser never sees `%Parameters{}`, so a problem that times out or fails to
  parse under one configuration does the same under all of them. The first
  configuration to hit one appends the outcome to `<output_dir>/parse_cache`;
  later configurations replay it from there instead of paying the parse again —
  which is the difference between one 60-second stall and one per configuration.
  Successful parses are not cached: the parsed problem is what the prover needs.
  Delete the file to force a re-attempt (e.g. after a parser fix).

  ### Progress output

  One line per problem on standard output, prefixed with the local wall-clock
  time and carrying an ETA extrapolated from the problems completed so far *in
  this invocation*:

      [07-28 14:03:22] [baseline] 142/5138 2.8% | SYO/SYO001^1.p → thm 152ms correct=yes | elapsed 00:04:11 eta 02:27:03

  """

  require Logger
  alias ShotDs.Tptp
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover

  @stop_sentinel "STOP"
  @parse_cache "parse_cache"
  @default_parse_timeout 60_000
  @default_prove_grace 10_000

  @typedoc "Runner options."
  @type opt ::
          {:label, String.t()}
          | {:output_dir, String.t()}
          | {:language, :th0 | :th1 | :both}
          | {:problem_limit, pos_integer() | nil}
          | {:problem_filter, (String.t() -> boolean()) | nil}
          | {:log_level, Logger.level() | :none}
          | {:parse_timeout, pos_integer()}
          | {:prove_grace, non_neg_integer()}

  @spec run_tptp(Parameters.t(), [opt()]) :: :ok | :stopped
  def run_tptp(params \\ %Parameters{}, opts \\ []) do
    Logger.configure(level: Keyword.get(opts, :log_level, :none))

    label = Keyword.get(opts, :label, "default")
    output_dir = Keyword.get(opts, :output_dir, "bench_results")
    language = Keyword.get(opts, :language, :both)
    problem_limit = Keyword.get(opts, :problem_limit)
    problem_filter = Keyword.get(opts, :problem_filter)
    parse_timeout = Keyword.get(opts, :parse_timeout, @default_parse_timeout)
    prove_grace = Keyword.get(opts, :prove_grace, @default_prove_grace)

    tptp_root =
      System.get_env("TPTP_ROOT") ||
        raise "TPTP_ROOT environment variable is missing. Set it to your TPTP directory."

    File.mkdir_p!(output_dir)

    csv_path = Path.join(output_dir, label <> ".csv")
    meta_path = Path.join(output_dir, label <> ".meta")
    ensure_header(csv_path)
    write_or_check_meta(meta_path, label, params)
    completed = load_completed(csv_path, label)

    stop_path = Path.join(output_dir, @stop_sentinel)
    parse_cache_path = Path.join(output_dir, @parse_cache)
    parse_cache = load_parse_cache(parse_cache_path)

    # Linked to the runner, so an abandoned sweep takes its phase processes
    # with it. `async_nolink` below keeps the traffic one-way: a phase that
    # crashes is reported back as a value, never as an exit signal.
    {:ok, task_sup} = Task.Supervisor.start_link()

    problems =
      tptp_root
      |> discover_problems(problem_filter)
      |> Enum.reject(&MapSet.member?(completed, relative_path(&1, tptp_root)))

    total = min(length(problems), problem_limit || length(problems))

    notice(
      "TptpRunner[#{label}]: #{total} problem(s) to process; " <>
        "#{MapSet.size(completed)} already completed, " <>
        "#{map_size(parse_cache)} known-unparsable."
    )

    process_all(problems, tptp_root, %{
      params: params,
      label: label,
      language: language,
      csv_path: csv_path,
      stop_path: stop_path,
      parse_cache_path: parse_cache_path,
      parse_cache: parse_cache,
      task_sup: task_sup,
      parse_timeout: parse_timeout,
      prove_timeout: params.timeout + prove_grace,
      remaining_budget: problem_limit,
      done: 0,
      total: total,
      started_at_ms: System.monotonic_time(:millisecond)
    })
  end

  ##############################################################################
  # SWEEP DRIVER
  ##############################################################################

  @doc """
  Runs a list of `{label, %Parameters{}}` configurations sequentially, calling
  `run_tptp/2` once per config. Shared `opts` (e.g. `output_dir`, `language`)
  are merged into every call; the per-config `label` overrides.

  Stops at the first config that reports `:stopped` (STOP sentinel encountered).
  Delete the sentinel and re-invoke to resume; earlier configs will short-circuit
  via the resume mechanism.
  """
  @spec run_sweep([{String.t(), Parameters.t()}], [opt()]) :: :ok | :stopped
  def run_sweep(configs, opts \\ []) when is_list(configs) do
    Enum.reduce_while(configs, :ok, fn {label, params}, _acc ->
      config_opts = Keyword.put(opts, :label, label)

      case run_tptp(params, config_opts) do
        :stopped -> {:halt, :stopped}
        :ok -> {:cont, :ok}
      end
    end)
  end

  ##############################################################################
  # MAIN LOOP
  ##############################################################################

  defp process_all([], _tptp_root, ctx) do
    notice("TptpRunner[#{ctx.label}]: done. #{ctx.done} problem(s) in #{elapsed(ctx)}.")
    :ok
  end

  defp process_all(_problems, _tptp_root, %{remaining_budget: 0} = ctx) do
    notice("TptpRunner[#{ctx.label}]: hit problem_limit after #{elapsed(ctx)}.")
    :ok
  end

  defp process_all([path | rest], tptp_root, %{stop_path: stop_path, label: label} = ctx) do
    if File.exists?(stop_path) do
      notice("TptpRunner[#{label}]: STOP sentinel present, halting.")
      :stopped
    else
      advanced = %{ctx | done: ctx.done + 1}

      process_one(path, tptp_root, advanced)

      # The row is written, so nothing downstream can still read this problem's
      # terms. Without this the pool carries every problem in the sweep.
      ShotTx.Prover.release_term_pool()

      new_budget =
        case ctx.remaining_budget do
          nil -> nil
          n when is_integer(n) -> n - 1
        end

      process_all(rest, tptp_root, %{advanced | remaining_budget: new_budget})
    end
  end

  defp process_one(abs_path, tptp_root, ctx) do
    rel_path = relative_path(abs_path, tptp_root)
    {expected, language} = read_headers(abs_path)

    if match_language?(language, ctx.language) do
      {time_micro, {result_tag, details, stats}} =
        :timer.tc(fn -> run_one(abs_path, rel_path, ctx) end)

      time_ms = div(time_micro, 1000)
      correct = score(expected, result_tag)

      notice(
        "[#{ctx.label}] #{ctx.done}/#{ctx.total} #{percent(ctx)} | " <>
          "#{rel_path} → #{result_tag} #{time_ms}ms correct=#{correct} | " <>
          "elapsed #{elapsed(ctx)} eta #{eta(ctx)}"
      )

      append_row(
        ctx.csv_path,
        [
          ctx.label,
          rel_path,
          language,
          expected,
          Atom.to_string(result_tag),
          Atom.to_string(correct),
          Integer.to_string(time_ms)
        ] ++ stats_cells(stats) ++ [details]
      )
    else
      Logger.debug("[#{ctx.label}] skipping #{rel_path} (language filter)")
    end
  end

  # Parsing and proving are rescued separately so the CSV attributes a failure
  # to the phase it happened in. The previous single `try` wrapped both, so an
  # exception raised inside `Prover.prove/3` was recorded as `parser_error`.
  defp run_one(abs_path, rel_path, ctx) do
    case parse_phase(abs_path, rel_path, ctx) do
      {:ok, problem} -> prove_phase(problem, ctx)
      {:error, tag, message} -> {tag, message, %{}}
    end
  end

  # A parse that timed out or failed once does the same again: the parser never
  # sees `%Parameters{}`, so its outcome is identical under every configuration
  # of the sweep. Replaying it from the cache turns "one stalled parse per
  # configuration" into "one stalled parse".
  defp parse_phase(abs_path, rel_path, ctx) do
    case Map.fetch(ctx.parse_cache, rel_path) do
      {:ok, {tag, message}} -> {:error, tag, "cached: " <> message}
      :error -> parse_problem(abs_path, rel_path, ctx)
    end
  end

  defp parse_problem(abs_path, rel_path, ctx) do
    parse = fn ->
      try do
        Tptp.parse_tptp_file(abs_path, :custom)
      rescue
        e -> {:error, Exception.message(e)}
      end
    end

    case isolated(ctx.task_sup, ctx.parse_timeout, parse) do
      {:ok, {:ok, problem}} ->
        {:ok, problem}

      {:ok, {:error, reason}} ->
        cache_parse_failure(ctx, rel_path, :parser_error, to_string(reason))

      {:exit, reason} ->
        cache_parse_failure(ctx, rel_path, :parser_error, inspect(reason))

      :timeout ->
        cache_parse_failure(
          ctx,
          rel_path,
          :parse_timeout,
          "parse exceeded #{ctx.parse_timeout}ms"
        )
    end
  end

  defp cache_parse_failure(ctx, rel_path, tag, message) do
    record_parse_failure(ctx.parse_cache_path, rel_path, tag, message)
    {:error, tag, message}
  end

  defp prove_phase(%{conjecture: nil}, _ctx), do: {:no_conjecture, "", %{}}

  defp prove_phase(problem, ctx) do
    case isolated(ctx.task_sup, ctx.prove_timeout, fn -> prove_problem(problem, ctx.params) end) do
      {:ok, outcome} -> outcome
      {:exit, reason} -> {:prover_error, inspect(reason), %{}}
      :timeout -> {:hard_timeout, "killed after #{ctx.prove_timeout}ms", %{}}
    end
  end

  defp prove_problem(problem, params) do
    {_name, conclusion} = problem.conjecture
    axioms = Enum.map(problem.axioms, fn {_name, term} -> term end)

    opts =
      params
      |> Map.from_struct()
      |> Enum.into([])
      |> Keyword.put(:defs, problem.definitions)
      |> Keyword.put(:stats, true)

    {result, stats} = Prover.prove(conclusion, axioms, opts)
    stats_map = extract_stats(stats)

    case result do
      {:thm, _} -> {:thm, "", stats_map}
      {:csa, model, _} -> {:csa, String.slice(model, 0, 200), stats_map}
      :unknown -> {:unk, "", stats_map}
      {:timeout, _} -> {:timeout, "", stats_map}
      {:error, reason} -> {:prover_error, inspect(reason), stats_map}
    end
  rescue
    e -> {:prover_error, Exception.message(e), %{}}
  catch
    :exit, reason -> {:prover_error, inspect(reason), %{}}
  end

  ##############################################################################
  # WALL-CLOCK ISOLATION
  ##############################################################################

  # `try/after` cannot bound a runaway computation — `after` runs once the body
  # returns, however long that takes. The only hard wall-clock guarantee on the
  # BEAM is a separate process the caller can kill, which is what this is.
  #
  # `async_nolink` keeps a crashing phase from taking the runner down with it,
  # and a killed proof attempt is cleaned up by `Prover`'s session reaper, which
  # monitors its caller — here, the task.
  @spec isolated(pid(), pos_integer(), (-> result)) :: {:ok, result} | {:exit, term()} | :timeout
        when result: term()
  defp isolated(task_sup, timeout, fun) do
    task = Task.Supervisor.async_nolink(task_sup, fun)

    case Task.yield(task, timeout) || Task.shutdown(task, :brutal_kill) do
      {:ok, value} -> {:ok, value}
      {:exit, reason} -> {:exit, reason}
      nil -> :timeout
    end
  end

  @stats_columns [
    :steps,
    :worker_yields,
    :rules_total,
    :active_branches_max,
    :branches_closed,
    :branches_saturated,
    :csp_calls,
    :csp_succeeded
  ]

  defp extract_stats(stats) do
    report = Prover.compile_stats(stats)

    %{
      steps: report.search.steps_total,
      worker_yields: report.search.worker_yields,
      rules_total: report.rules.total,
      active_branches_max: report.branches.active_max,
      branches_closed: report.branches.closed_locally,
      branches_saturated: report.branches.saturated,
      csp_calls: report.csp.calls,
      csp_succeeded: report.csp.succeeded
    }
  end

  defp stats_cells(stats), do: Enum.map(@stats_columns, &to_string(Map.get(stats, &1, "")))

  ##############################################################################
  # PROGRESS REPORTING
  ##############################################################################

  # The runner's own output goes straight to standard output rather than
  # through Logger, so that silencing the prover (`log_level: :none`, the
  # default) never takes the progress report with it. Every line carries the
  # local wall-clock time: a sweep runs for days, and `elapsed`/`eta` alone
  # cannot say when a line was printed or whether the run is still moving.
  defp notice(message), do: IO.puts(stamp() <> " " <> message)

  defp stamp, do: "[" <> Calendar.strftime(NaiveDateTime.local_now(), "%m-%d %H:%M:%S") <> "]"

  defp percent(%{done: done, total: total}) when total > 0,
    do: "#{Float.round(done / total * 100, 1)}%"

  defp percent(_ctx), do: "--%"

  defp elapsed(ctx), do: format_duration(System.monotonic_time(:millisecond) - ctx.started_at_ms)

  # Extrapolates from the mean cost of the problems finished so far. That mean
  # is a poor predictor over the first handful of problems and a decent one by
  # a few hundred in, which is the regime the estimate is actually read in.
  defp eta(%{done: done}) when done <= 0, do: "--:--:--"

  defp eta(%{done: done, total: total} = ctx) do
    (System.monotonic_time(:millisecond) - ctx.started_at_ms)
    |> div(done)
    |> Kernel.*(max(total - done, 0))
    |> format_duration()
  end

  defp format_duration(milliseconds) do
    total_seconds = div(milliseconds, 1000)

    [div(total_seconds, 3600), rem(div(total_seconds, 60), 60), rem(total_seconds, 60)]
    |> Enum.map_join(":", &(&1 |> Integer.to_string() |> String.pad_leading(2, "0")))
  end

  ##############################################################################
  # CSV HELPERS
  ##############################################################################

  @csv_header "run_label,problem,language,expected_szs,result,correct,time_ms," <>
                "steps,worker_yields,rules_total,active_branches_max," <>
                "branches_closed,branches_saturated,csp_calls,csp_succeeded,details\n"

  defp ensure_header(csv_path) do
    unless File.exists?(csv_path) and File.stat!(csv_path).size > 0 do
      File.write!(csv_path, @csv_header)
    end
  end

  # A `<label>.meta` file captures the exact parameters and code revision a
  # run started under, so a later resume against the same directory can tell
  # whether the CSV rows still describe the current configuration.
  defp write_or_check_meta(meta_path, label, params) do
    current = meta_snapshot(label, params)

    case File.read(meta_path) do
      {:ok, existing} ->
        if params_line(existing) != params_line(current) do
          notice(
            "WARNING TptpRunner[#{label}]: parameters differ from previous run recorded in " <>
              meta_path <> ". Resumed CSV may mix configurations."
          )
        end

      {:error, :enoent} ->
        File.write!(meta_path, current)
    end
  end

  defp meta_snapshot(label, params) do
    """
    label: #{label}
    started_at: #{DateTime.utc_now() |> DateTime.to_iso8601()}
    git_sha: #{git_sha()}
    params: #{inspect(params, limit: :infinity, printable_limit: :infinity)}
    """
  end

  defp params_line(text) do
    text
    |> String.split("\n", trim: true)
    |> Enum.find(fn line -> String.starts_with?(line, "params:") end)
  end

  defp git_sha do
    case System.cmd("git", ["rev-parse", "HEAD"], stderr_to_stdout: true) do
      {sha, 0} -> String.trim(sha)
      _ -> "unknown"
    end
  rescue
    ErlangError -> "unknown"
  end

  defp load_completed(csv_path, label) do
    if File.exists?(csv_path) do
      csv_path
      |> File.stream!()
      |> Stream.drop(1)
      |> Stream.map(&String.split(&1, ",", parts: 3))
      |> Stream.filter(fn [row_label | _] -> row_label == label end)
      |> Stream.map(fn [_label, problem | _] -> problem end)
      |> Enum.into(MapSet.new())
    else
      MapSet.new()
    end
  end

  # Shared across every configuration of a sweep, unlike the per-label CSVs:
  # one tab-separated `path <TAB> tag <TAB> message` line per problem that
  # could not be parsed. A malformed line is dropped rather than fatal — the
  # cache is an optimisation, and re-parsing is always a correct fallback.
  defp load_parse_cache(parse_cache_path) do
    case File.read(parse_cache_path) do
      {:ok, contents} ->
        contents
        |> String.split("\n", trim: true)
        |> Enum.flat_map(&parse_cache_entry/1)
        |> Map.new()

      {:error, :enoent} ->
        %{}
    end
  end

  defp parse_cache_entry(line) do
    case String.split(line, "\t") do
      [rel_path, "parse_timeout", message] -> [{rel_path, {:parse_timeout, message}}]
      [rel_path, "parser_error", message] -> [{rel_path, {:parser_error, message}}]
      _malformed -> []
    end
  end

  defp record_parse_failure(parse_cache_path, rel_path, tag, message) do
    entry =
      [rel_path, Atom.to_string(tag), message |> single_line() |> String.slice(0, 200)]
      |> Enum.join("\t")

    File.write!(parse_cache_path, entry <> "\n", [:append])
  end

  defp single_line(text), do: String.replace(text, ~r/\s+/, " ")

  defp append_row(csv_path, cells) do
    line = Enum.map_join(cells, ",", &sanitize/1) <> "\n"
    File.write!(csv_path, line, [:append])
  end

  defp sanitize(cell) when is_binary(cell), do: String.replace(cell, ~r/[,;\n\r]/, " ")

  ##############################################################################
  # HEADER PARSING & DISCOVERY
  ##############################################################################

  # Parses `% Status : Theorem` and `% SPC : TH0_THM_EQU_NAR` from a TPTP file
  # header. The language lives in the `SPC` field: `Syntax` carries formula
  # statistics, not a language tag, in every problem of the current corpus.
  #
  # 50 lines rather than 40: the header is longer in some problems and the SPC
  # line sits as deep as line 42. Reading past it would cost a full scan of
  # every file in the ~5000 problem TH0/TH1 corpus for nothing.
  defp read_headers(abs_path) do
    lines =
      abs_path
      |> File.stream!()
      |> Stream.take(50)
      |> Enum.to_list()

    {parse_status(lines), parse_spc(lines)}
  end

  defp parse_status(lines), do: parse_header_field(lines, "Status", "unknown")
  defp parse_spc(lines), do: syntax_language(parse_header_field(lines, "SPC", ""))

  defp parse_header_field(lines, field, default) do
    Enum.find_value(lines, default, fn line ->
      case Regex.run(~r/^%\s*#{field}\s*:\s*([^\s]+)/, line) do
        [_, value] -> value
        _ -> nil
      end
    end)
  end

  defp syntax_language("TH0" <> _), do: "TH0"
  defp syntax_language("TH1" <> _), do: "TH1"
  defp syntax_language(_), do: "unknown"

  defp match_language?(_language, :both), do: true
  defp match_language?("TH0", :th0), do: true
  defp match_language?("TH1", :th1), do: true
  defp match_language?(_language, _), do: false

  defp discover_problems(tptp_root, problem_filter) do
    tptp_root
    |> Path.join("Problems/**/*.p")
    |> Path.wildcard()
    |> Enum.filter(&String.match?(&1, ~r/\^\d+\.p$/))
    |> maybe_filter(tptp_root, problem_filter)
    |> Enum.sort()
  end

  defp maybe_filter(paths, _tptp_root, nil), do: paths

  defp maybe_filter(paths, tptp_root, filter) when is_function(filter, 1) do
    Enum.filter(paths, fn abs -> filter.(relative_path(abs, tptp_root)) end)
  end

  defp relative_path(abs_path, tptp_root) do
    problems_root = Path.join(tptp_root, "Problems") |> Path.expand()
    abs_expanded = Path.expand(abs_path)

    case Path.relative_to(abs_expanded, problems_root) do
      ^abs_expanded -> Path.basename(abs_path)
      rel -> rel
    end
  end

  ##############################################################################
  # SCORING
  ##############################################################################

  # Maps (expected TPTP status, prover result tag) → correctness verdict.
  # The truth table is intentionally narrow: SZS "Theorem" and
  # "CounterSatisfiable" are the only expected statuses that give a definite
  # ground truth against a `:thm` / `:csa` prover answer. Anything else — an
  # unknown/open expected status, a timeout, or a parser failure — is `n/a`.
  defp score("Theorem", :thm), do: :yes
  defp score("Theorem", :csa), do: :no
  defp score("CounterSatisfiable", :csa), do: :yes
  defp score("CounterSatisfiable", :thm), do: :no
  defp score(_expected, _result), do: :na
end
