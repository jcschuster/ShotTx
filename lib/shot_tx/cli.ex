defmodule ShotTx.CLI do
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
  declarations, optionally with `include/1` directives — set `$TPTP_ROOT`)
  or a single THF formula (in which case the conjecture-only fragment is
  proved with no axioms).

  A leading dash reads the problem from standard input.

  ## Output modes

  By default, the CLI prints a short human-readable line:

      $ ./shot_tx problem.p
      THM

  With `--szs`, the output follows the SZS ontology (Sutcliffe 2008) that
  every mainstream automated theorem prover emits:

      $ ./shot_tx --szs problem.p
      % SZS status Theorem for problem.p

  ### Status map

  | Prover result        | SZS status         |
  |----------------------|--------------------|
  | `{:thm, _}`          | `Theorem`          |
  | `{:csa, _, _}`       | `CounterSatisfiable` |
  | `:unknown`           | `GaveUp`           |
  | `{:timeout, _}`      | `Timeout`          |
  | `{:error, _}`        | `Error`            |

  ## Options

  All prover knobs described in `ShotTx.Data.Parameters` are exposed as
  long flags in kebab-case; e.g. `--initial-gamma-limit 3` sets
  `:initial_gamma_limit`. Booleans support the `--flag` / `--no-flag` form.

  Common flags:

    * `--szs`                — emit SZS-ontology status line.
    * `--sat`                — treat the input as a satisfiability check
                                (do not negate a conclusion).
    * `-t`, `--timeout MS`   — wall-clock limit in milliseconds.
    * `--proof`              — print the reconstructed proof tree.
    * `--stats`              — print search statistics after the result.
    * `-v`, `--verbose`      — enable prover debug logging on stderr.
    * `-V`, `--version`      — print the version and exit.
    * `-h`, `--help`         — show a compact help message.

  ## TPTP_ROOT fallback

  If the positional argument looks like a file path (contains `/` or ends
  in `.p`, `.thf`, `.tptp`, or `.ax`) and no such file exists locally, the
  CLI retries the lookup relative to the `TPTP_ROOT` environment variable.
  This lets you invoke problems by their canonical TPTP name — e.g.

      $ TPTP_ROOT=/opt/TPTP shot_tx --szs Problems/PUZ/PUZ001+1.p

  ## Exit codes

  The escript returns `0` when the prover produces a definite verdict
  (theorem or countermodel), `1` for `unknown`/`timeout`, and `2` for any
  input or parsing error.
  """

  alias ShotDs.Data.{Context, Problem}
  alias ShotDs.Parser
  alias ShotDs.Tptp
  alias ShotTx.Prover

  @typedoc "Everything an escript main entry point ever receives."
  @type argv :: [String.t()]

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
    # Numeric prover parameters
    timeout: :integer,
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
    iterative_deepening: :boolean
  ]

  @aliases [h: :help, t: :timeout, s: :szs, v: :verbose, V: :version]

  @enum_keys [
    :unfold_defs,
    :simplification,
    :orient,
    :equivalence_processing,
    :formula_cost_strategy
  ]

  @doc """
  Escript entry point. Parses `argv`, runs the prover, prints the result,
  and calls `System.halt/1` with the appropriate exit code.
  """
  @spec main(argv()) :: no_return()
  def main(argv) do
    {opts, args, invalid} = OptionParser.parse(argv, strict: @flag_types, aliases: @aliases)

    configure_logging(opts)

    cond do
      opts[:help] ->
        IO.puts(help_text())
        System.halt(0)

      opts[:version] ->
        IO.puts("shot_tx #{version()}")
        System.halt(0)

      invalid != [] ->
        IO.puts(:stderr, "shot_tx: unrecognised option(s): #{format_invalid(invalid)}")
        IO.puts(:stderr, "Run `shot_tx --help` for usage.")
        System.halt(2)

      args == [] ->
        IO.puts(:stderr, "shot_tx: no problem given")
        IO.puts(:stderr, "Run `shot_tx --help` for usage.")
        System.halt(2)

      true ->
        run(args, opts)
    end
  end

  defp version do
    case :application.get_key(:shot_tx, :vsn) do
      {:ok, vsn} -> List.to_string(vsn)
      _ -> "unknown"
    end
  end

  # The prover's internal Logger chatter is noise for a CLI. Silence it by
  # default so `--szs` output stays clean; users opt into the log stream
  # with `--verbose`.
  defp configure_logging(opts) do
    level = if opts[:verbose], do: :debug, else: :error
    Logger.configure(level: level)
  end

  ## ---------------------------------------------------------------------------
  ## Dispatch
  ## ---------------------------------------------------------------------------

  @spec run(argv(), keyword()) :: no_return()
  defp run([input | _], opts) do
    problem_label = label_for(input)

    case load_problem(input) do
      {:ok, {:problem, %Problem{} = problem}} ->
        run_problem(problem, problem_label, opts)

      {:ok, {:formula, formula_id}} ->
        run_formula(formula_id, problem_label, opts)

      {:error, reason} ->
        emit_status(problem_label, :error, opts, "input: " <> reason)
        System.halt(2)
    end
  end

  @spec run_problem(Problem.t(), String.t(), keyword()) :: no_return()
  defp run_problem(%Problem{} = problem, label, opts) do
    param_kws = param_keywords(opts)

    {result, stats} =
      case {opts[:sat], opts[:stats]} do
        {true, true} ->
          Prover.sat(problem_formulas(problem), problem.definitions, [{:stats, true} | param_kws])

        {true, _} ->
          {Prover.sat(problem_formulas(problem), problem.definitions, param_kws), nil}

        {_, true} ->
          Prover.prove(problem, [{:stats, true} | param_kws])

        _ ->
          {Prover.prove(problem, param_kws), nil}
      end

    finish(result, stats, label, opts)
  end

  @spec run_formula(term(), String.t(), keyword()) :: no_return()
  defp run_formula(formula_id, label, opts) do
    param_kws = param_keywords(opts)

    {result, stats} =
      case {opts[:sat], opts[:stats]} do
        {true, true} ->
          Prover.sat([formula_id], %{}, [{:stats, true} | param_kws])

        {true, _} ->
          {Prover.sat([formula_id], %{}, param_kws), nil}

        {_, true} ->
          Prover.prove(formula_id, [], [{:stats, true} | param_kws])

        _ ->
          {Prover.prove(formula_id, [], param_kws), nil}
      end

    finish(result, stats, label, opts)
  end

  @spec finish(term(), map() | nil, String.t(), keyword()) :: no_return()
  defp finish(result, stats, label, opts) do
    mode = if opts[:sat], do: :sat, else: :prove
    exit_code = emit_result(result, label, mode, opts)
    maybe_emit_stats(stats)
    System.halt(exit_code)
  end

  defp maybe_emit_stats(nil), do: :ok
  defp maybe_emit_stats(stats), do: IO.puts(Prover.format_stats(stats))

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
  # or `{:error, message}`.
  defp load_problem("-") do
    IO.read(:stdio, :eof) |> parse_source("stdin")
  end

  defp load_problem(input) do
    cond do
      regular_file?(input) ->
        parse_file(input)

      looks_like_path?(input) ->
        case resolve_tptp_root(input) do
          {:ok, path} -> parse_file(path)
          :error -> {:error, "no such file: #{input}"}
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

  defp resolve_tptp_root(rel) do
    case System.get_env("TPTP_ROOT") do
      nil ->
        :error

      root ->
        candidate = Path.join(root, rel)
        if regular_file?(candidate), do: {:ok, candidate}, else: :error
    end
  end

  defp parse_file(path) do
    case Tptp.parse_tptp_file(path, :custom) do
      {:ok, problem} -> {:ok, {:problem, problem}}
      {:error, reason} -> {:error, reason}
    end
  end

  defp parse_source(:eof, source), do: {:error, "empty input from #{source}"}

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
    e ->
      {:error, "failed to parse #{source}: #{Exception.message(e)}"}
  end

  ## ---------------------------------------------------------------------------
  ## Result emission
  ## ---------------------------------------------------------------------------

  defp emit_result(result, label, mode, opts) do
    {status, detail, exit_code} = classify(result, mode)
    emit_status(label, status, opts, detail)
    maybe_emit_proof(result, label, opts)
    exit_code
  end

  # SZS status normalization. In `--sat` mode the input is treated as an
  # unadorned formula set, so a model means `Satisfiable`; in prove mode
  # the negated conjecture is on the branch, so a model means
  # `CounterSatisfiable`.
  defp classify({:thm, _proof}, _mode), do: {:theorem, nil, 0}
  defp classify({:csa, model, _proof}, _mode), do: {:counter_satisfiable, model, 0}
  defp classify(:unknown, _mode), do: {:gave_up, nil, 1}
  defp classify({:timeout, _partial}, _mode), do: {:timeout, nil, 1}
  defp classify({:error, reason}, _mode), do: {:error, inspect(reason), 2}
  defp classify({:sat, _}, :sat), do: {:satisfiable, nil, 0}
  defp classify({:sat, _}, _), do: {:counter_satisfiable, nil, 0}
  defp classify({:unsat, _, _, _}, :sat), do: {:unsatisfiable, nil, 0}
  defp classify({:unsat, _, _, _}, _), do: {:theorem, nil, 0}
  defp classify({:unknown, _}, _mode), do: {:gave_up, nil, 1}

  defp emit_status(label, status, opts, detail) do
    if opts[:szs] do
      IO.puts(szs_line(status, label, detail))
    else
      IO.puts(short_line(status, detail))
    end
  end

  defp szs_line(:theorem, label, _detail), do: "% SZS status Theorem for #{label}"

  defp szs_line(:counter_satisfiable, label, _detail),
    do: "% SZS status CounterSatisfiable for #{label}"

  defp szs_line(:satisfiable, label, _detail), do: "% SZS status Satisfiable for #{label}"

  defp szs_line(:unsatisfiable, label, _detail), do: "% SZS status Unsatisfiable for #{label}"

  defp szs_line(:gave_up, label, _detail), do: "% SZS status GaveUp for #{label}"
  defp szs_line(:timeout, label, _detail), do: "% SZS status Timeout for #{label}"

  defp szs_line(:error, label, detail),
    do: "% SZS status Error for #{label} : #{detail || "unknown error"}"

  defp short_line(:theorem, _), do: "THM"
  defp short_line(:counter_satisfiable, nil), do: "CSA"
  defp short_line(:counter_satisfiable, model), do: "CSA\n" <> model
  defp short_line(:satisfiable, _), do: "SAT"
  defp short_line(:unsatisfiable, _), do: "UNSAT"
  defp short_line(:gave_up, _), do: "UNK"
  defp short_line(:timeout, _), do: "Timeout"
  defp short_line(:error, detail), do: "Error: " <> (detail || "unknown")

  defp maybe_emit_proof({:thm, proof}, label, opts) when is_map(proof) do
    maybe_render_proof(proof, label, opts, "Refutation")
  end

  defp maybe_emit_proof({:csa, _model, proof}, label, opts) when is_map(proof) do
    maybe_render_proof(proof, label, opts, "CounterModel")
  end

  defp maybe_emit_proof(_result, _label, _opts), do: :ok

  defp maybe_render_proof(proof, label, opts, kind) do
    if opts[:proof] do
      text = ShotTx.Proof.to_text(proof)

      if opts[:szs] do
        IO.puts("% SZS output start #{kind} for #{label}")
        IO.puts(text)
        IO.puts("% SZS output end #{kind} for #{label}")
      else
        IO.puts(text)
      end
    end
  end

  ## ---------------------------------------------------------------------------
  ## Option → Parameters keyword list
  ## ---------------------------------------------------------------------------

  defp param_keywords(opts) do
    opts
    |> Enum.reject(fn {k, _} -> k in [:szs, :sat, :proof, :stats, :help, :verbose] end)
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
      or `-` to read from standard input.

    Output:
      --szs                 Emit `% SZS status <verdict> for <problem>`
                            in the SZS ontology.
      --proof               Print the reconstructed proof / countermodel.
      --stats               Print search statistics.
      -v, --verbose         Enable prover debug logging on stderr.
      -V, --version         Print the shot_tx version and exit.

    Mode:
      --sat                 Check the input for satisfiability instead
                            of proving it (do not negate the conjecture).

    Common knobs (see `ShotTx.Data.Parameters` for the full list):
      -t, --timeout MS                        default 5000
          --initial-gamma-limit N             default 1
          --initial-prim-limit N              default 1
          --unfold-defs lazy|eager            default lazy
          --[no-]beta-variant                 default true
          --[no-]demodulation                 default true
          --[no-]atom-decomposition           default true
          --[no-]contradiction-agent          default true
          --[no-]primitive-substitution       default true
          --[no-]iterative-deepening          default true
          --formula-cost-strategy default|uniform|depth_first
                                              default default
          --worker-pool-size N                default :auto

    Exit codes:
      0  Theorem or CounterSatisfiable
      1  GaveUp / Timeout
      2  Bad input / parse error / unknown option
    """
  end
end
