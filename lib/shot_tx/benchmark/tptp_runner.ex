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
    * `language` — `TH0` | `TH1` | `unknown` (from the file `Syntax` header).
    * `expected_szs` — TPTP-declared status: `Theorem`, `CounterSatisfiable`,
      `Unknown`, `Open`, … (or `unknown` if the header is missing).
    * `result` — `thm` | `csa` | `unk` | `timeout` | `parser_error` |
      `prover_error` | `unexpected` | `no_conjecture`.
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
      problems by the `Syntax` header line.
    * `problem_limit` (default `nil`) — max number of problems to process in
      this invocation (after already-completed rows are skipped). Handy for
      smoke tests.
    * `problem_filter` (default `nil`) — a function `(relative_path -> boolean)`.
  """

  require Logger
  alias ShotDs.Tptp
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover

  @stop_sentinel "STOP"

  @typedoc "Runner options."
  @type opt ::
          {:label, String.t()}
          | {:output_dir, String.t()}
          | {:language, :th0 | :th1 | :both}
          | {:problem_limit, pos_integer() | nil}
          | {:problem_filter, (String.t() -> boolean()) | nil}

  @spec run_tptp(Parameters.t(), [opt()]) :: :ok | :stopped
  def run_tptp(params \\ %Parameters{}, opts \\ []) do
    label = Keyword.get(opts, :label, "default")
    output_dir = Keyword.get(opts, :output_dir, "bench_results")
    language = Keyword.get(opts, :language, :both)
    problem_limit = Keyword.get(opts, :problem_limit)
    problem_filter = Keyword.get(opts, :problem_filter)

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

    problems =
      tptp_root
      |> discover_problems(problem_filter)
      |> Enum.reject(&MapSet.member?(completed, relative_path(&1, tptp_root)))

    Logger.info(
      "TptpRunner[#{label}]: #{length(problems)} problem(s) to process; " <>
        "#{MapSet.size(completed)} already completed."
    )

    process_all(problems, tptp_root, %{
      params: params,
      label: label,
      language: language,
      csv_path: csv_path,
      stop_path: stop_path,
      remaining_budget: problem_limit
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

  defp process_all([], _tptp_root, %{label: label}) do
    Logger.info("TptpRunner[#{label}]: done.")
    :ok
  end

  defp process_all(_problems, _tptp_root, %{remaining_budget: 0, label: label}) do
    Logger.info("TptpRunner[#{label}]: hit problem_limit.")
    :ok
  end

  defp process_all([path | rest], tptp_root, %{stop_path: stop_path, label: label} = ctx) do
    if File.exists?(stop_path) do
      Logger.warning("TptpRunner[#{label}]: STOP sentinel present, halting.")
      :stopped
    else
      process_one(path, tptp_root, ctx)

      new_budget =
        case ctx.remaining_budget do
          nil -> nil
          n when is_integer(n) -> n - 1
        end

      process_all(rest, tptp_root, %{ctx | remaining_budget: new_budget})
    end
  end

  defp process_one(abs_path, tptp_root, ctx) do
    rel_path = relative_path(abs_path, tptp_root)
    {expected, language} = read_headers(abs_path)

    if match_language?(language, ctx.language) do
      {time_micro, {result_tag, details, stats}} =
        :timer.tc(fn -> run_one(abs_path, ctx.params) end)

      time_ms = div(time_micro, 1000)
      correct = score(expected, result_tag)

      Logger.info(
        "[#{ctx.label}] #{rel_path} → #{result_tag} " <>
          "(expected #{expected}, #{time_ms}ms, correct=#{correct})"
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

  defp run_one(abs_path, params) do
    try do
      case Tptp.parse_tptp_file(abs_path, :custom) do
        {:ok, problem} -> prove_problem(problem, params)
        {:error, reason} -> {:parser_error, to_string(reason), %{}}
      end
    rescue
      e -> {:parser_error, Exception.message(e), %{}}
    catch
      :exit, reason -> {:prover_error, inspect(reason), %{}}
    end
  end

  defp prove_problem(%{conjecture: nil}, _params), do: {:no_conjecture, "", %{}}

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
          Logger.warning(
            "TptpRunner[#{label}]: parameters differ from previous run recorded in " <>
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

  defp append_row(csv_path, cells) do
    line = Enum.map_join(cells, ",", &sanitize/1) <> "\n"
    File.write!(csv_path, line, [:append])
  end

  defp sanitize(cell) when is_binary(cell), do: String.replace(cell, ~r/[,;\n\r]/, " ")

  ##############################################################################
  # HEADER PARSING & DISCOVERY
  ##############################################################################

  # Parses `% Status : Theorem` and `% Syntax : TH0_...` from a TPTP file
  # header. Reads at most the first 40 lines to keep this cheap on the ~4000
  # problem TH0/TH1 corpus.
  defp read_headers(abs_path) do
    lines =
      abs_path
      |> File.stream!()
      |> Stream.take(40)
      |> Enum.to_list()

    {parse_status(lines), parse_syntax(lines)}
  end

  defp parse_status(lines), do: parse_header_field(lines, "Status", "unknown")
  defp parse_syntax(lines), do: syntax_language(parse_header_field(lines, "Syntax", ""))

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
