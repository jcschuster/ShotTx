defmodule ShotTx.Cli do
  @moduledoc """
  Command-line entry point for the **Shot** prover, packaged as an escript.

  `ShotTx` is the tableau component of the Shot ecosystem; the `shot_tx`
  binary is Shot's CLI.

  ## Building

      $ mix escript.build
      Generated escript shot_tx

  ## Usage

      $ ./shot_tx [OPTIONS] <INPUT>

  `<INPUT>` is either the path to a TPTP `.p` problem file or an inline
  problem string. An inline string may be a full TPTP problem (`thf(...).`
  declarations, optionally with `include/1` directives — set `$TPTP`)
  or a single THF formula (in which case the conjecture-only fragment is
  proved with no axioms).

  A leading dash reads the problem from standard input.

  ## Output modes

  By default, the CLI prints a short human-readable line:

      $ ./shot_tx problem.p
      THM

  With `--szs`, the output follows the SZS ontology (Sutcliffe 2008):

      $ ./shot_tx --szs problem.p
      % SZS status Theorem for problem.p

  With `--szs --proof`, the proof follows in a `Proof` output block; a model
  (the model, then the open branch) in a `Model` block:

      % SZS status Theorem for problem.p
      % SZS output start Proof for problem.p
      1. ...
      % SZS output end Proof for problem.p

  The block holds Shot's textual derivation tree, not a TSTP derivation. Its
  lines are not `%`-prefixed; everything outside an output block is.

  ### Status map

  | Outcome                                       | SZS status           | Exit |
  |-----------------------------------------------|----------------------|------|
  | Conjecture, tableau closed                    | `Theorem`            | 0    |
  | Conjecture, model found (pure-`o` only)       | `CounterSatisfiable` | 0    |
  | No conjecture (or `--sat`), tableau closed    | `Unsatisfiable`      | 0    |
  | No conjecture (or `--sat`), model found       | `Satisfiable`        | 0    |
  | Search space exhausted without a model        | `Incomplete`         | 1    |
  | Saturated but not pure-`o`, other give-ups    | `GaveUp`             | 1    |
  | Wall-clock limit reached (`-t`)               | `WCTimeout`          | 1    |
  | CPU-time limit reached (`--cpu-timeout`)      | `Timeout`            | 1    |
  | Stopped by SIGTERM                            | `Forced`             | 1    |
  | Input not parseable as THF                    | `Inappropriate`      | 2    |
  | Missing file, unreadable include, empty input | `InputError`         | 2    |
  | Bad command-line options                      | `UsageError`         | 2    |

  An internal error is reported as `GaveUp` with the reason after ` : `.
  Models are reported only for problems whose types are all pure-`o` (see
  `:pure_o_models_only` in `ShotTx.Data.Parameters`). Problems using `$ite`
  are rejected as `Inappropriate`: Shot would treat it as an uninterpreted
  constant, which is sound for proofs but not for models.

  ## Time limits

  `-t MS` bounds the whole run in wall-clock time — parsing, search and proof
  reconstruction. The search itself gets a slightly smaller budget so a result
  can still be printed; if the hard limit is reached anyway, the CLI prints
  `WCTimeout`.

  `--cpu-timeout MS` bounds the CPU time of the whole VM, summed over all
  threads, as a CPU-second limit does (SystemOnTPTP). The run is stopped with
  `Timeout` once the budget is used up. Both limits count from VM start and may
  be combined; without `-t`, the wall-clock limit equals the CPU limit.

  ## Options

  All prover knobs described in `ShotTx.Data.Parameters` are exposed as
  long flags in kebab-case; e.g. `--initial-gamma-limit 3` sets
  `:initial_gamma_limit`. Booleans support the `--flag` / `--no-flag` form.
  Run `shot_tx --help` for the common ones.

  ## TPTP directory

  `$TPTP` (or, if unset, `$TPTP_ROOT`) names the TPTP directory. Includes are
  resolved against the problem file's own directory when all of them exist
  there, else against the TPTP directory. It is also a fallback for the input path:
  if the argument looks like a path and no such file exists locally, it is
  looked up relative to the TPTP directory.

      $ TPTP=/opt/TPTP shot_tx --szs Problems/SYO/SYO001^1.p

  `-V` prints `Shot---<version>`.
  """

  alias ShotDs.Data.{Context, Problem}
  alias ShotDs.Parser
  alias ShotDs.Stt.TermFactory
  alias ShotDs.Tptp
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover

  @typedoc "Everything an escript main entry point ever receives."
  @type argv :: [String.t()]

  @typep status ::
           :theorem
           | :counter_satisfiable
           | :satisfiable
           | :unsatisfiable
           | :gave_up
           | :incomplete
           | :forced
           | :timeout
           | :cpu_timeout
           | :inappropriate
           | :input_error
           | :usage_error

  # Long flags with their OptionParser types. Kept explicit rather than
  # generated from `%Parameters{}` so the CLI surface stays intentional.
  @flag_types [
    # Output / mode
    szs: :boolean,
    sat: :boolean,
    proof: :boolean,
    stats: :boolean,
    verbose: :boolean,
    help: :boolean,
    version: :boolean,
    # Time limits (ms)
    timeout: :integer,
    cpu_timeout: :integer,
    # Numeric prover parameters
    initial_gamma_limit: :integer,
    initial_prim_limit: :integer,
    prim_subst_after: :integer,
    prim_subst_batch_size: :integer,
    unification_depth: :integer,
    suggestion_cascade_ceiling: :integer,
    worker_pool_size: :integer,
    progress_interval_ms: :integer,
    # Enum-valued (parsed as string, converted to atom below)
    unfold_defs: :string,
    simplification: :string,
    orient: :string,
    equivalence_processing: :string,
    formula_cost_strategy: :string,
    instance_based_gamma_limit: :string,
    # Booleans
    beta_variant: :boolean,
    finite_o_quantification: :boolean,
    instance_based_gamma: :boolean,
    demodulation: :boolean,
    atom_decomposition: :boolean,
    suggestions_enabled: :boolean,
    contradiction_agent: :boolean,
    primitive_substitution: :boolean,
    iterative_deepening: :boolean,
    pure_o_models_only: :boolean
  ]

  @aliases [h: :help, t: :timeout, s: :szs, v: :verbose, V: :version]

  @cli_only_keys [:szs, :sat, :proof, :stats, :help, :verbose, :version, :cpu_timeout]

  # Granularity of the limit checks while the search runs.
  @poll_ms 100

  @enum_keys [
    :unfold_defs,
    :simplification,
    :orient,
    :equivalence_processing,
    :formula_cost_strategy
  ]

  # ShotDs reports these input failures as plain strings (`InputError`).
  # Everything else it returns is a parser complaint (`Inappropriate`).
  @io_error_prefixes ["Could not read", "TPTP_ROOT environment variable"]

  @doc """
  Escript entry point. Parses `argv`, runs the prover, prints the result,
  and calls `System.halt/1` with the appropriate exit code.
  """
  @spec main(argv()) :: no_return()
  def main(argv) do
    {opts, args, invalid} = OptionParser.parse(argv, strict: @flag_types, aliases: @aliases)

    configure_logging(opts)
    ShotTx.Config.tptp_root()
    # Started already in the escript, but not under `bin/shot_tx eval`.
    {:ok, _} = Application.ensure_all_started(:shot_tx)

    cond do
      opts[:help] ->
        IO.puts(help_text())
        System.halt(0)

      opts[:version] ->
        IO.puts("Shot---#{version()}")
        System.halt(0)

      invalid != [] ->
        usage_error("unrecognised option(s): #{format_invalid(invalid)}", argv, opts)

      args == [] ->
        usage_error("no problem given", argv, opts)

      true ->
        run(args, opts)
    end
  end

  @spec usage_error(String.t(), argv(), keyword()) :: no_return()
  defp usage_error(message, argv, opts) do
    label = argv |> List.last("shot") |> label_for()
    report = %{status: :usage_error, detail: message, solution: nil, stats: nil}
    if opts[:szs], do: emit(report, label, opts)
    IO.puts(:stderr, "shot_tx: #{message}\nRun `shot_tx --help` for usage.")
    System.halt(exit_code(:usage_error))
  end

  defp version do
    case :application.get_key(:shot_tx, :vsn) do
      {:ok, vsn} -> List.to_string(vsn)
      _ -> "unknown"
    end
  end

  # The prover's internal Logger chatter is noise for a CLI. Silence it by
  # default and send whatever remains to stderr, so stdout carries only the
  # result; users opt into the log stream with `--verbose`.
  defp configure_logging(opts) do
    level = if opts[:verbose], do: :debug, else: :error
    Logger.configure(level: level)
    _ = :logger.update_handler_config(:default, :config, %{type: :standard_error})
    :ok
  end

  ## ---------------------------------------------------------------------------
  ## Dispatch
  ## ---------------------------------------------------------------------------

  @spec run(argv(), keyword()) :: no_return()
  defp run([input | _], opts) do
    wall_limit = wall_limit(opts)
    cpu_limit = cpu_budget(opts[:cpu_timeout])
    budgeted_opts = Keyword.put(opts, :timeout, search_budget(remaining_wall(wall_limit)))
    task = Task.async(fn -> attempt(input, budgeted_opts) end)

    report = await(task, wall_limit, cpu_limit)
    emit(report, label_for(input), opts)
    System.halt(exit_code(report.status))
  end

  # Both limits count from VM start, so booting the escript is charged to them.
  # Without `-t`, the CPU limit doubles as the wall-clock limit.
  defp wall_limit(opts) do
    opts[:timeout] || opts[:cpu_timeout] ||
      Keyword.get(ShotTx.Config.get(), :timeout, %Parameters{}.timeout)
  end

  defp remaining_wall(limit), do: max(limit - wall_used(), 1)

  defp wall_used, do: :erlang.statistics(:wall_clock) |> elem(0)

  # CPU time of the whole VM, all threads summed, as a CPU-second limit sees it.
  defp cpu_used, do: :erlang.statistics(:runtime) |> elem(0)

  # Between two polls every scheduler may burn another `@poll_ms` of CPU, and
  # shutting down costs a little more, so the check fires early enough for the
  # run to end inside an external CPU limit.
  defp cpu_budget(nil), do: :infinity

  defp cpu_budget(limit) do
    margin = max(div(limit, 10), 500 + @poll_ms * System.schedulers_online())
    max(limit - margin, div(limit, 2))
  end

  # Polls the search so that either budget can end the run.
  defp await(task, wall_limit, cpu_limit) do
    case Task.yield(task, min(@poll_ms, remaining_wall(wall_limit))) do
      {:ok, report} -> report
      {:exit, reason} -> gave_up(inspect(reason))
      nil -> check_budgets(task, wall_limit, cpu_limit)
    end
  end

  defp check_budgets(task, wall_limit, cpu_limit) do
    cond do
      cpu_used() >= cpu_limit -> stop(task, :cpu_timeout)
      wall_used() >= wall_limit -> stop(task, :timeout)
      true -> await(task, wall_limit, cpu_limit)
    end
  end

  defp stop(task, status) do
    Task.shutdown(task, :brutal_kill)
    %{status: status, detail: nil, solution: nil, stats: nil}
  end

  # Leave room to reconstruct and print the proof inside the hard limit.
  defp search_budget(limit) do
    margin = max(div(limit, 10), 500)
    max(limit - margin, div(limit, 2))
  end

  # Runs in its own process under the deadline. Never raises: a crash is
  # reported as `GaveUp` rather than as a stack trace on stdout.
  defp attempt(input, opts) do
    with {:ok, loaded} <- load_problem(input),
         :ok <- reject_ite(loaded) do
      solve(loaded, opts)
    else
      {:error, status, reason} -> %{status: status, detail: reason, solution: nil, stats: nil}
    end
  rescue
    e -> gave_up(Exception.message(e))
  catch
    # SIGTERM shuts the VM down under us.
    :exit, {:shutdown, _} -> %{status: :forced, detail: nil, solution: nil, stats: nil}
    :exit, reason -> gave_up(inspect(reason))
  end

  defp gave_up(reason), do: %{status: :gave_up, detail: reason, solution: nil, stats: nil}

  # `$ite` parses as an uninterpreted constant. A proof stays sound, a model
  # may not respect the intended semantics, so the problem is turned away.
  defp reject_ite(loaded) do
    if Enum.any?(loaded_formulas(loaded), &uses_ite?/1),
      do: {:error, :inappropriate, "$ite is not supported"},
      else: :ok
  end

  defp loaded_formulas({:formula, id}), do: [id]

  defp loaded_formulas({:problem, %Problem{definitions: defs} = problem}),
    do: problem_formulas(problem) ++ Map.values(defs)

  defp uses_ite?(term_id) do
    term_id
    |> TermFactory.get_term!()
    |> Map.fetch!(:consts)
    |> Enum.any?(&match?(%{name: "$ite"}, &1))
  end

  defp solve(loaded, opts) do
    mode = mode(loaded, opts)
    params = stats_option(opts) ++ param_keywords(opts)
    {result, stats} = loaded |> call_prover(mode, params) |> split_stats(opts[:stats])
    {status, detail} = classify(result, mode)

    %{status: status, detail: detail, solution: solution(result, opts), stats: stats}
  end

  # Without a conjecture there is nothing to prove, only a set to refute.
  defp mode({:problem, %Problem{conjecture: nil}}, _opts), do: :sat
  defp mode(_loaded, opts), do: if(opts[:sat], do: :sat, else: :prove)

  defp call_prover({:problem, problem}, :prove, params), do: Prover.prove(problem, params)

  defp call_prover({:problem, problem}, :sat, params),
    do: Prover.refute(problem_formulas(problem), [{:defs, problem.definitions} | params])

  defp call_prover({:formula, id}, :prove, params), do: Prover.prove(id, [], params)
  defp call_prover({:formula, id}, :sat, params), do: Prover.refute([id], params)

  defp stats_option(opts), do: if(opts[:stats], do: [stats: true], else: [])

  defp split_stats({result, stats}, true), do: {result, stats}
  defp split_stats(result, _), do: {result, nil}

  defp problem_formulas(%Problem{axioms: axioms, conjecture: conjecture}) do
    axiom_ids = Enum.map(axioms, fn {_name, id} -> id end)

    case conjecture do
      nil -> axiom_ids
      {_name, id} -> [id | axiom_ids]
    end
  end

  ## ---------------------------------------------------------------------------
  ## Input loading
  ## ---------------------------------------------------------------------------

  # Returns `{:ok, {:problem, Problem.t()}}`, `{:ok, {:formula, term_id()}}`,
  # or `{:error, :inappropriate | :input_error, message}`.
  defp load_problem("-") do
    IO.read(:stdio, :eof) |> parse_source("stdin")
  end

  defp load_problem(input) do
    cond do
      regular_file?(input) ->
        parse_file(input)

      looks_like_path?(input) ->
        case resolve_in_tptp_root(input) do
          {:ok, path} -> parse_file(path)
          :error -> {:error, :input_error, "no such file: #{input}"}
        end

      true ->
        parse_source(input, "argument")
    end
  end

  defp regular_file?(path) do
    match?({:ok, %File.Stat{type: :regular}}, File.stat(path))
  end

  # A leading slash, a slash anywhere, or a TPTP/THF extension is a strong
  # enough signal that the user meant "file" rather than an inline formula.
  defp looks_like_path?(input) do
    String.contains?(input, "/") or
      Path.extname(input) in [".p", ".thf", ".tptp", ".ax"]
  end

  defp resolve_in_tptp_root(rel) do
    case ShotTx.Config.tptp_root() do
      nil -> :error
      root -> root |> Path.join(rel) |> existing_file()
    end
  end

  defp existing_file(path), do: if(regular_file?(path), do: {:ok, path}, else: :error)

  defp parse_file(path) do
    use_include_root(path)

    case Tptp.parse_tptp_file(path, :custom) do
      {:ok, problem} -> {:ok, {:problem, problem}}
      {:error, reason} -> {:error, input_error_status(reason), reason}
    end
  rescue
    e -> {:error, :inappropriate, Exception.message(e)}
  end

  # ShotDs resolves includes only under `$TPTP_ROOT`. TPTP convention is to try
  # the including file's directory first, so point `$TPTP_ROOT` there when all
  # of the file's includes exist in it.
  defp use_include_root(path) do
    includes =
      ~r/^\s*include\(\s*'([^']+)'/m
      |> Regex.scan(File.read!(path), capture: :all_but_first)
      |> List.flatten()

    local = Path.dirname(path)

    if includes != [] and Enum.all?(includes, &regular_file?(Path.join(local, &1))) do
      System.put_env("TPTP_ROOT", local)
    end
  end

  defp input_error_status(reason) do
    if String.starts_with?(reason, @io_error_prefixes), do: :input_error, else: :inappropriate
  end

  defp parse_source(:eof, source), do: {:error, :input_error, "empty input from #{source}"}

  defp parse_source(content, source) when is_binary(content) do
    case Tptp.parse_tptp_string(content, source) do
      {:ok, %Problem{axioms: [], conjecture: nil}} -> try_parse_formula(content, source)
      {:ok, problem} -> {:ok, {:problem, problem}}
      {:error, _reason} -> try_parse_formula(content, source)
    end
  end

  defp try_parse_formula(content, source) do
    formula_id = Parser.parse!(content, force_o: true, ctx: Context.new())
    {:ok, {:formula, formula_id}}
  rescue
    e -> {:error, :inappropriate, "failed to parse #{source}: #{Exception.message(e)}"}
  end

  ## ---------------------------------------------------------------------------
  ## Result classification
  ## ---------------------------------------------------------------------------

  # In prove mode the negated conjecture is on the branch, so a closed tableau
  # is a theorem and a model is a countermodel. In sat mode the formulas are
  # taken as they are.
  @spec classify(Prover.proof_result(), :prove | :sat) :: {status(), String.t() | nil}
  defp classify({:thm, _proof}, :prove), do: {:theorem, nil}
  defp classify({:thm, _proof}, :sat), do: {:unsatisfiable, nil}
  defp classify({:csa, model, _proof}, :prove), do: {:counter_satisfiable, model}
  defp classify({:csa, model, _proof}, :sat), do: {:satisfiable, model}
  defp classify({:unknown, :exhausted_without_model}, _mode), do: {:incomplete, nil}
  defp classify({:unknown, _reason}, _mode), do: {:gave_up, nil}
  defp classify({:timeout, _partial}, _mode), do: {:timeout, nil}
  defp classify({:error, reason}, _mode), do: {:gave_up, inspect(reason)}

  @spec exit_code(status()) :: 0 | 1 | 2
  defp exit_code(status) when status in [:gave_up, :incomplete, :timeout, :cpu_timeout, :forced],
    do: 1

  defp exit_code(status) when status in [:inappropriate, :input_error, :usage_error], do: 2

  defp exit_code(_definite), do: 0

  # The text of the output block, built under the deadline: the proof tree,
  # preceded by the model for a countermodel.
  defp solution(result, opts), do: if(opts[:proof], do: solution_text(result))

  defp solution_text({:thm, proof}) when is_map(proof), do: ShotTx.Proof.to_text(proof)

  defp solution_text({:csa, "", proof}) when is_map(proof), do: ShotTx.Proof.to_text(proof)

  defp solution_text({:csa, model, proof}) when is_map(proof),
    do: model <> "\n" <> ShotTx.Proof.to_text(proof)

  defp solution_text(_result), do: nil

  # SZS output form of the block: a refutation is a `Proof`, a saturated
  # branch with its model a `Model`.
  defp output_form(status) when status in [:theorem, :unsatisfiable], do: "Proof"
  defp output_form(_status), do: "Model"

  ## ---------------------------------------------------------------------------
  ## Output
  ## ---------------------------------------------------------------------------

  defp emit(report, label, opts) do
    if opts[:szs], do: emit_szs(report, label), else: emit_short(report)
  end

  defp emit_szs(%{status: status, detail: detail, solution: solution, stats: stats}, label) do
    IO.puts(szs_line(status, label, detail))

    if solution do
      form = output_form(status)
      IO.puts("% SZS output start #{form} for #{label}")
      IO.puts(String.trim_trailing(solution))
      IO.puts("% SZS output end #{form} for #{label}")
    end

    if stats, do: stats |> Prover.format_stats() |> as_tptp_comment() |> IO.puts()
  end

  defp emit_short(%{status: status, detail: detail, solution: solution, stats: stats}) do
    IO.puts(short_line(status, detail))
    if solution, do: IO.puts(solution)
    if stats, do: IO.puts(Prover.format_stats(stats))
  end

  defp as_tptp_comment(text) do
    text
    |> String.trim_trailing()
    |> String.split("\n")
    |> Enum.map_join("\n", &String.trim_trailing("% " <> &1))
  end

  @szs_names %{
    theorem: "Theorem",
    counter_satisfiable: "CounterSatisfiable",
    satisfiable: "Satisfiable",
    unsatisfiable: "Unsatisfiable",
    gave_up: "GaveUp",
    incomplete: "Incomplete",
    forced: "Forced",
    timeout: "WCTimeout",
    cpu_timeout: "Timeout",
    inappropriate: "Inappropriate",
    input_error: "InputError",
    usage_error: "UsageError"
  }

  @failures [:inappropriate, :input_error, :usage_error]

  # Failures carry a reason after ` : ` on one line; so does a `GaveUp` that
  # has one (an internal error).
  defp szs_line(status, label, detail) when status in @failures do
    "% SZS status #{@szs_names[status]} for #{label} : #{one_line(detail || "unknown error")}"
  end

  defp szs_line(:gave_up, label, detail) when is_binary(detail),
    do: "% SZS status GaveUp for #{label} : #{one_line(detail)}"

  defp szs_line(status, label, _detail), do: "% SZS status #{@szs_names[status]} for #{label}"

  defp one_line(text), do: text |> String.split() |> Enum.join(" ")

  defp short_line(:theorem, _), do: "THM"
  defp short_line(:counter_satisfiable, model), do: with_model("CSA", model)
  defp short_line(:satisfiable, model), do: with_model("SAT", model)
  defp short_line(:unsatisfiable, _), do: "UNSAT"
  defp short_line(:gave_up, nil), do: "UNK"
  defp short_line(:gave_up, reason), do: "UNK: #{reason}"
  defp short_line(:incomplete, _), do: "UNK"
  defp short_line(:forced, _), do: "Forced"
  defp short_line(:timeout, _), do: "Timeout"
  defp short_line(:cpu_timeout, _), do: "Timeout"
  defp short_line(status, detail), do: "#{@szs_names[status]}: #{detail || "unknown"}"

  defp with_model(verdict, model) when model in [nil, ""], do: verdict
  defp with_model(verdict, model), do: verdict <> "\n" <> model

  ## ---------------------------------------------------------------------------
  ## Option → Parameters keyword list
  ## ---------------------------------------------------------------------------

  defp param_keywords(opts) do
    opts
    |> Enum.reject(fn {k, _} -> k in @cli_only_keys end)
    |> Enum.map(&normalise_option/1)
  end

  defp normalise_option({:instance_based_gamma_limit, "infinity"}),
    do: {:instance_based_gamma_limit, :infinity}

  defp normalise_option({:instance_based_gamma_limit, val}) when is_binary(val),
    do: {:instance_based_gamma_limit, String.to_integer(val)}

  defp normalise_option({key, val}) when key in @enum_keys and is_binary(val),
    do: {key, String.to_atom(val)}

  defp normalise_option({key, val}), do: {key, val}

  ## ---------------------------------------------------------------------------
  ## Misc helpers
  ## ---------------------------------------------------------------------------

  defp label_for("-"), do: "stdin"
  defp label_for(input), do: Path.basename(input)

  defp format_invalid(invalid) do
    invalid
    |> Enum.map_join(", ", fn
      {flag, nil} -> flag
      {flag, val} -> "#{flag}=#{val}"
    end)
  end

  defp help_text do
    """
    Shot -- Church STT tableau prover.

    Usage:
      shot_tx [OPTIONS] <FILE | "STRING" | ->

    Input:
      A .p / .thf file path, an inline TPTP or THF problem string,
      or `-` to read from standard input. `include/1` directives and
      relative problem paths are resolved against $TPTP (or $TPTP_ROOT).

    Output:
      --szs                 Emit `% SZS status <verdict> for <problem>`
                            in the SZS ontology.
      --proof               Print the reconstructed proof / model (inside
                            a `Comment` output block with --szs).
      --stats               Print search statistics.
      -v, --verbose         Enable prover debug logging on stderr.
      -V, --version         Print the version (Shot---x.y.z) and exit.

    Mode:
      --sat                 Check the input for satisfiability instead
                            of proving it (do not negate the conjecture).
                            Implied for problems without a conjecture.

    Common knobs (see `ShotTx.Data.Parameters` for the full list):
      -t, --timeout MS                        default 5000 (whole run, wall clock)
          --cpu-timeout MS                    CPU time of the whole VM; also the
                                              wall-clock limit unless -t is given
          --initial-gamma-limit N             default 1
          --initial-prim-limit N              default 1
          --unfold-defs lazy|eager            default eager
          --[no-]beta-variant                 default false
          --[no-]demodulation                 default true
          --[no-]atom-decomposition           default true
          --[no-]contradiction-agent          default true
          --[no-]primitive-substitution       default true
          --[no-]iterative-deepening          default true
          --[no-]pure-o-models-only           default true
          --formula-cost-strategy default|uniform|depth_first
                                              default default
          --worker-pool-size N                default :auto

    Exit codes:
      0  Theorem, CounterSatisfiable, Satisfiable, Unsatisfiable
      1  GaveUp, Incomplete, WCTimeout, Timeout, Forced
      2  Inappropriate, InputError, UsageError
    """
  end
end
