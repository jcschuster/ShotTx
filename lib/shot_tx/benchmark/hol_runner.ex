defmodule ShotTx.Benchmark.HolRunner do
  @moduledoc """
  Evaluates ShotTx on one `ShotTx.Benchmark.HolSuite` problem and renders the
  outcome as a CSV row.

  The configuration evaluated is the `@params` module attribute below. It is
  `%Parameters{}` — the shipped defaults — so the numbers this produces are
  what a user gets from a bare `ShotTx.Prover.prove/1`. Edit the attribute, or
  pass a `%Parameters{}` to `evaluate/2`, to evaluate a different one.

  > #### One problem per BEAM {: .warning}
  >
  > This module deliberately evaluates a *single* problem per invocation.
  > ShotTx keeps shared state across proof sessions (the global `:term_cache`,
  > the session registries), and a session that crashes or is killed leaves
  > enough of it behind to change the answer for later problems in the same
  > node — during development of this suite, one problem returned `thm`,
  > `csa` and `prover_error` depending on what ran before it. Sweeping the
  > suite inside one node therefore does not measure the prover; it measures
  > the prover plus its history. `scripts/run_hol_benchmark.sh` drives the
  > sweep with a fresh node per problem for that reason.
  >
  > Independent of ordering, a handful of problems are genuinely
  > nondeterministic run-to-run — the search is parallel, and which worker
  > reaches a verdict first is a race. Repeat a surprising row before
  > believing it.

  ### CSV columns

      id, section, variant, livebook_note, result, time_ms, steps,
      rules_total, active_branches_max, branches_closed, branches_saturated,
      csp_calls, csp_succeeded, details

    * `result` — `thm` | `csa` | `unk` | `timeout` | `parser_error` |
      `prover_error` | `hard_timeout`.
    * `livebook_note` — what `structured_hol_problems.livemd` claims for this
      problem (`THM`, `Timeout`, or empty). Recorded for reference only; it is
      the author's observation, not ground truth.
    * `time_ms` — wall-clock milliseconds for parse plus proof search, measured
      after `warm_up/1` so it excludes module loading.
  """

  alias ShotTx.Benchmark.HolSuite
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover

  # Evaluation configuration. Defaults as shipped; change here to re-evaluate.
  @params %Parameters{}

  # Safety net for an unattended run: if the prover's own timeout fails to
  # fire, abandon the problem rather than hanging the sweep. Set well above
  # `timeout` on purpose — ShotTx routinely overshoots its own deadline by
  # several multiples, and a tight wall here would silently truncate problems
  # it was about to solve.
  @hard_timeout_factor 12
  @hard_timeout_grace_ms 10_000

  # Free-form detail text is truncated before it reaches the CSV; a crash dump
  # can otherwise run to several kilobytes.
  @detail_limit 200

  @stat_columns [
    :steps,
    :rules_total,
    :active_branches_max,
    :branches_closed,
    :branches_saturated,
    :csp_calls,
    :csp_succeeded
  ]

  @doc """
  The parameter configuration this runner evaluates.
  """
  @spec params() :: Parameters.t()
  def params, do: @params

  @doc """
  The CSV header line, newline included.
  """
  @spec csv_header() :: String.t()
  def csv_header do
    (~w(id section variant livebook_note result time_ms) ++
       Enum.map(@stat_columns, &Atom.to_string/1) ++ ["details"])
    |> Enum.join(",")
    |> Kernel.<>("\n")
  end

  @doc """
  Runs one proof attempt so the measured attempt does not pay for loading the
  prover's modules and warming the JIT — on the order of a third of a second,
  which would otherwise be charged to every problem.
  """
  @spec warm_up(Parameters.t()) :: :ok
  def warm_up(params \\ @params) do
    prove("thf(warm_up, conjecture, ![X:$i]: (X = X)).\n", params)
    :ok
  end

  @doc """
  Proves one problem and returns its row as a map.
  """
  @spec evaluate(HolSuite.problem(), Parameters.t()) :: map()
  def evaluate(problem, params \\ @params) do
    {time_micro, {result, details, stats}} = :timer.tc(fn -> prove(problem.thf, params) end)

    %{
      id: problem.id,
      section: problem.section,
      variant: problem.variant,
      livebook_note: problem.note,
      result: Atom.to_string(result),
      time_ms: div(time_micro, 1000),
      details: String.slice(details, 0, @detail_limit)
    }
    |> Map.merge(stats)
  end

  @doc """
  Renders a row from `evaluate/2` as a CSV line, newline included.
  """
  @spec csv_row(map()) :: String.t()
  def csv_row(row) do
    cells =
      [row.id, row.section, row.variant, row.livebook_note, row.result, row.time_ms] ++
        Enum.map(@stat_columns, &Map.get(row, &1, "")) ++
        [row.details]

    Enum.map_join(cells, ",", &sanitize/1) <> "\n"
  end

  ##############################################################################
  # PROOF ATTEMPT
  ##############################################################################

  defp prove(thf, params) do
    task = Task.async(fn -> parse_and_prove(thf, params) end)
    wall = params.timeout * @hard_timeout_factor + @hard_timeout_grace_ms

    case Task.yield(task, wall) || Task.shutdown(task, :brutal_kill) do
      {:ok, outcome} -> outcome
      nil -> {:hard_timeout, "exceeded #{wall}ms wall clock", %{}}
    end
  end

  defp parse_and_prove(thf, params) do
    case parse(thf) do
      {:ok, problem} -> run_prover(problem, params)
      {:error, message} -> {:parser_error, message, %{}}
    end
  end

  defp parse(thf) do
    {:ok, ShotDs.Tptp.parse_tptp_string!(thf)}
  rescue
    e -> {:error, Exception.message(e)}
  end

  defp run_prover(problem, params) do
    opts =
      params
      |> Map.from_struct()
      |> Enum.into([])
      |> Keyword.put(:stats, true)

    {result, stats} = Prover.prove(problem, opts)
    classify(result, extract_stats(stats))
  rescue
    e -> {:prover_error, Exception.message(e), %{}}
  catch
    :exit, reason -> {:prover_error, inspect(reason), %{}}
  end

  defp classify({:thm, _proof}, stats), do: {:thm, "", stats}
  defp classify({:csa, model, _proof}, stats), do: {:csa, model, stats}
  defp classify(:unknown, stats), do: {:unk, "", stats}
  defp classify({:timeout, _partial}, stats), do: {:timeout, "", stats}
  defp classify({:error, reason}, stats), do: {:prover_error, inspect(reason), stats}

  defp extract_stats(stats) do
    report = Prover.compile_stats(stats)

    %{
      steps: report.search.steps_total,
      rules_total: report.rules.total,
      active_branches_max: report.branches.active_max,
      branches_closed: report.branches.closed_locally,
      branches_saturated: report.branches.saturated,
      csp_calls: report.csp.calls,
      csp_succeeded: report.csp.succeeded
    }
  end

  defp sanitize(cell) when is_integer(cell), do: Integer.to_string(cell)
  defp sanitize(cell) when is_binary(cell), do: String.replace(cell, ~r/[,;\n\r]/, " ")
end
