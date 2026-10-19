defmodule ShotTx.Prover do
  @moduledoc """
  Public entry point for the ShotTx tableau prover.

  Three related APIs live here:

    * `prove/1`, `prove/2`, `prove/3` — attempt to prove `conclusion` from
      `assumptions` (or a `ShotDs.Data.Problem`). Returns a `t:proof_result/0`.
    * `refute/2` — run the tableau on a formula set without negating a
      conclusion. Returns a `t:proof_result/0`, like `prove/3`.
    * `sat/1`, `sat/2`, `sat/3` — check a list of formulas for satisfiability
      without negating a conclusion. Returns the raw `Manager` result.
    * `prove_string/1`, `prove_string/2`, `prove_string/3` — thin convenience
      wrapper that formats the outcome via `format_result/1`.

  `release_term_pool/0` sits alongside them for callers that run many proofs in
  one node.

  Every call spins up a fresh `ShotTx.Prover.SessionSupervisor` and blocks
  synchronously on the `Manager` until the search terminates (theorem,
  countermodel, timeout, or exhausted iterative deepening). The session tree is
  torn down on every exit path, including a caller that is killed outright.
  Configuration
  is threaded through as a keyword list that is merged into a
  `ShotTx.Data.Parameters` struct — see that module for the full list of
  knobs, and `ShotTx.Config` for session-wide defaults.
  """

  import ShotDs.Hol.Dsl
  alias ShotTx.Data.Parameters
  alias ShotTx.Generation.TypeUniverse
  alias ShotTx.Prover.Rules
  use ShotDs.Hol.Patterns
  import ShotDs.Util.Formatter
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Data.{Declaration, Term, Problem}
  import ShotDs.Hol.{Definitions, Dsl}

  require Logger

  @type proof_result ::
          {:thm, ShotTx.Proof.t()}
          | {:csa, String.t(), ShotTx.Proof.t()}
          | {:unknown, term()}
          | {:timeout, ShotTx.Proof.t()}
          | {:error, term()}

  @doc """
  Shorthand delegating to the three-argument form.

  Accepts either a `ShotDs.Data.Problem` (`prove(problem)` — no options), a
  single `t:ShotDs.Data.Term.term_id/0` conclusion (`prove(conclusion)`), or a
  conclusion plus either an assumption list or options list.

  See `prove/3` for the primary interface and return type.
  """
  @spec prove(Problem.t() | Term.term_id()) :: proof_result()
  def prove(problem) when is_struct(problem, Problem), do: prove(problem, [])

  def prove(conclusion) when is_integer(conclusion), do: prove(conclusion, [], [])

  @spec prove(Problem.t(), keyword()) :: proof_result() | {proof_result(), map()}
  @spec prove(Term.term_id(), [Term.term_id()] | keyword()) ::
          proof_result() | {proof_result(), map()}
  def prove(conclusion, [{key, _} | _] = opts) when is_integer(conclusion) and is_atom(key),
    do: prove(conclusion, [], opts)

  def prove(conclusion, assumptions) when is_integer(conclusion) and is_list(assumptions),
    do: prove(conclusion, assumptions, defs: %{})

  def prove(%Problem{} = problem, opts) when is_struct(problem, Problem) do
    if is_nil(problem.conjecture) do
      {:error, :no_conjecture}
    else
      {_name, conclusion} = problem.conjecture
      assumptions = Enum.map(problem.axioms, fn {_name, axiom} -> axiom end)
      prove(conclusion, assumptions, [{:defs, problem.definitions} | opts])
    end
  end

  @doc """
  Attempts to prove `conclusion` from `assumptions`.

  Accepts three call shapes:
  - `prove(problem)` — a `Problem` struct with a conjecture and axioms.
  - `prove(conclusion)` / `prove(conclusion, assumptions)` — term IDs.
  - `prove(conclusion, assumptions, opts)` — full form; `opts` are forwarded to
    `Parameters` except for the `:defs` key (a definition map).

  Returns a `proof_result()`.
  """
  @spec prove(Term.term_id(), [Term.term_id()], keyword()) ::
          proof_result() | {proof_result(), map()}
  def prove(conclusion, assumptions, opts)
      when is_integer(conclusion) and is_list(assumptions) and is_list(opts) do
    # Thunked: `format!/2` runs over every assumption, so a problem with
    # thousands of axioms would render all of them even when nothing logs.
    Logger.info(fn ->
      "Attempting to prove:\n" <>
        Enum.map_join(assumptions, ", ", &format!(&1, _hide_types = true)) <>
        " ⊢ " <>
        format!(conclusion)
    end)

    closed_conclusion = close_formula(conclusion)
    closed_assms = Enum.map(assumptions, &close_formula/1)

    refute([neg(closed_conclusion) | closed_assms], opts)
  end

  @doc """
  Runs the tableau on `formulas` exactly as given — no conclusion is negated —
  and reconstructs the proof or model like `prove/3` does.

  `{:thm, proof}` means the set is unsatisfiable; `{:csa, model, proof}` means
  a model was found. Accepts the same options as `prove/3`, including `:defs`
  and `:stats`.
  """
  @spec refute([Term.term_id()], keyword()) :: proof_result() | {proof_result(), map()}
  def refute(formulas, opts) when is_list(formulas) and is_list(opts) do
    {defs, params} = Keyword.pop(opts, :defs, %{})

    if opts[:stats] do
      {raw, stats} = sat(formulas, defs, params)
      {to_result(raw, formulas), stats}
    else
      formulas |> sat(defs, params) |> to_result(formulas)
    end
  end

  defp to_result(
         {:sat,
          %{
            model_branch_id: bid,
            model_atoms: atoms,
            model_defs: ds,
            model_trace: mt,
            closed_traces: ct
          }},
         formulas
       ) do
    proof = ShotTx.Proof.from_countermodel(ct, formulas, bid, mt, {atoms, ds})
    {:csa, format_model(atoms, ds), proof}
  end

  defp to_result(
         {:sat,
          %{
            model_branch_id: bid,
            model_source: :model_agent,
            model_witness: witness,
            closed_traces: ct
          }},
         formulas
       ) do
    proof = ShotTx.Proof.from_countermodel(ct, formulas, bid, [], {[], %{}})
    {:csa, format_agent_witness(witness), proof}
  end

  defp to_result({:unsat, global_subst, flex_pairs, traces}, formulas) do
    {:thm, ShotTx.Proof.from_refutation(traces, formulas, global_subst, flex_pairs)}
  end

  defp to_result({:unknown, reason}, _formulas), do: {:unknown, reason}
  defp to_result({:timeout, partial_proof}, _formulas), do: {:timeout, partial_proof}
  defp to_result({:error, reason}, _formulas), do: {:error, reason}

  @doc """
  Convenience wrapper that returns a human-readable string result,
  preserving the original `prove` interface for quick testing.
  """
  @spec prove_string(Problem.t() | Term.term_id(), [Term.term_id()], keyword()) :: String.t()
  def prove_string(target, assumptions \\ [], opts \\ [])

  def prove_string(%Problem{} = problem, _assumptions, opts) do
    format_result(prove(problem, opts))
  end

  def prove_string(conclusion, assumptions, opts) do
    format_result(prove(conclusion, assumptions, opts))
  end

  @doc "Formats a `proof_result()` as a short human-readable string for quick inspection."
  @spec format_result(proof_result()) :: String.t()
  def format_result({:thm, _proof}), do: "THM"
  def format_result({:csa, model, _proof}), do: "CSA\n" <> model
  def format_result({:unknown, _reason}), do: "UNK"
  def format_result({:timeout, _partial_proof}), do: "Timeout"
  def format_result({:error, reason}), do: "Error: #{inspect(reason)}"

  @doc """
  Checks the satisfiability of a list of formulas. Delegates the execution to
  the Manager GenServer.
  """
  @spec sat([Term.term_id()] | Term.term_id(), map(), keyword()) ::
          {:sat, map()}
          | {:unsat, map(), list(), map()}
          | {:unknown, term()}
          | {:timeout, ShotTx.Proof.t()}
          | {sat_result :: term(), stats :: map()}
  def sat(formulas, defs \\ %{}, opts \\ [])

  def sat(formulas, defs, opts) when is_list(formulas) do
    {return_stats?, param_kws} = Keyword.pop(opts, :stats, false)
    merged_kws = Keyword.merge(ShotTx.Config.get(), param_kws)
    raw_params = struct!(Parameters, merged_kws)
    params = resolve_formula_cost(raw_params)
    :ok = validate_term_order!(formulas, params)
    session_id = make_ref() |> inspect()

    {session_pid, reaper} = start_session({session_id, formulas, defs, params})
    manager_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :manager}}}

    {result, stats} =
      try do
        GenServer.call(manager_via, :start_proof, :infinity)
      after
        send(reaper, :caller_done)
        terminate_session(session_pid)
      end

    unwrapped =
      case result do
        {:sat, results} ->
          {:sat, results}

        {:unsat, global_substitution, remaining_flex, traces} ->
          {:unsat, global_substitution, remaining_flex, traces}

        {:unknown, reason} ->
          {:unknown, reason}

        {:timeout, partial_proof} ->
          {:timeout, partial_proof}

        other ->
          other
      end

    gated = gate_model(unwrapped, formulas, defs, params)

    if return_stats?, do: {gated, stats}, else: gated
  end

  def sat(formula, defs, opts), do: sat([formula], defs, opts)

  # A saturated branch is only a model if bounded γ-instantiation could not
  # have missed anything — guaranteed when every type is pure-`o`, since those
  # domains are finite and enumerated. See `Parameters.pure_o_models_only`.
  defp gate_model({:sat, _} = result, formulas, defs, %Parameters{pure_o_models_only: true}) do
    if pure_o_problem?(formulas, defs), do: result, else: {:unknown, :saturation_not_pure_o}
  end

  defp gate_model(result, _formulas, _defs, _params), do: result

  defp pure_o_problem?(formulas, defs) do
    (formulas ++ Map.values(defs))
    |> TypeUniverse.from_formulas()
    |> Enum.all?(&Rules.pure_o_type?/1)
  end

  # The session hangs off a node-wide supervisor; the reaper ties it to the
  # caller. `after` covers normal exits, the reaper covers `:kill`. The reaper
  # starts the session itself, after its monitor is set, so no window exists
  # in which a killed caller orphans a running session.
  defp start_session(session_spec) do
    caller = self()
    ref = make_ref()

    {reaper, monitor_ref} =
      spawn_monitor(fn ->
        caller_ref = Process.monitor(caller)

        outcome =
          DynamicSupervisor.start_child(ShotTx.SessionSpawner, session_child(session_spec))

        send(caller, {ref, outcome})
        await_caller(outcome, caller, caller_ref)
      end)

    receive do
      {^ref, {:ok, session_pid}} ->
        Process.demonitor(monitor_ref, [:flush])
        {session_pid, reaper}

      {^ref, other} ->
        Process.demonitor(monitor_ref, [:flush])
        raise "ShotTx could not start a proof session: #{inspect(other)}"

      {:DOWN, ^monitor_ref, :process, ^reaper, reason} ->
        raise "ShotTx session reaper died before starting the session: #{inspect(reason)}"
    end
  end

  defp session_child(session_spec), do: {ShotTx.Prover.SessionSupervisor, session_spec}

  defp await_caller({:ok, session_pid}, caller, caller_ref) do
    receive do
      {:DOWN, ^caller_ref, :process, ^caller, _reason} -> terminate_session(session_pid)
      :caller_done -> :ok
    end
  end

  defp await_caller(_failed_start, _caller, _caller_ref), do: :ok

  # Drops the `EtsKeeper` and with it the session's tables. The reaper may race
  # the `after` block; the loser gets `{:error, :not_found}`.
  defp terminate_session(session_pid) do
    DynamicSupervisor.terminate_child(ShotTx.SessionSpawner, session_pid)
  end

  @doc """
  Drops every term memoized in the node-wide `:term_pool`.

  Sessions release their own ETS tables when they terminate, but the term pool
  is shared and only ever grows: a sweep accumulates every term of every problem
  it has seen, and the hash-consing lookups on the hot path pay for it.

  Term IDs do not survive a release. Any `ShotTx.Proof`, `ShotDs.Data.Problem`
  or bare term ID still held becomes unreadable, so call this only between
  problems, once the previous result has been consumed.
  """
  @spec release_term_pool() :: :ok
  def release_term_pool do
    :ets.delete_all_objects(:term_pool)
    :ok
  end

  @doc """
  Compiles a raw stats snapshot (as returned by `prove/3` with `stats: true`)
  into a structured report grouped by `:timing`, `:search`, `:rules`,
  `:branches`, and `:csp`. Idempotent on already-compiled reports.
  """
  @spec compile_stats(map()) :: map()
  defdelegate compile_stats(stats), to: ShotTx.Prover.Stats, as: :compile

  @doc """
  Pretty-prints a stats snapshot or compiled report. Pass `verbose: true` to
  include zero-valued rule/branch counters, or `sections: [:timing, :csp]` to
  render a subset.
  """
  @spec format_stats(map(), keyword()) :: String.t()
  defdelegate format_stats(stats, opts \\ []), to: ShotTx.Prover.Stats, as: :format

  # NCPO-LNF soundness: a user-restricted `accessible` / `basic_sorts` must meet
  # Definitions 5–6 of Niederhauser & Middeldorp (2025) for the input's
  # constants. The `:all` defaults hold vacuously. Violations abort the proof
  # rather than reduce under an unsound order.
  defp validate_term_order!(formulas, %Parameters{term_order: %ShotTo.Parameters{} = to_params}) do
    if to_params.accessible == :all and to_params.basic_sorts == :all do
      :ok
    else
      const_types = collect_constant_types(formulas)

      case ShotTo.Parameters.validate(to_params, const_types) do
        :ok ->
          :ok

        {:error, violations} ->
          raise ArgumentError,
                "NCPO-LNF parameters violate accessibility/basicness compatibility " <>
                  "(Definitions 5–6 of Niederhauser & Middeldorp 2025); paramodulation " <>
                  "would derive rewrites outside the reduction order. Violations:\n" <>
                  Enum.map_join(violations, "\n", &("  - " <> &1))
      end
    end
  end

  defp collect_constant_types(formulas) do
    formulas
    |> Enum.flat_map(fn tid -> TF.get_term!(tid).consts end)
    |> Enum.into(%{}, fn %Declaration{name: name, type: type} -> {name, type} end)
  end

  # A `formula_cost_strategy` other than the historical `:default` overrides the
  # `formula_cost` field. This keeps the raw function field as an escape hatch
  # (Livebook users can still hand it a lambda) but ensures ablation sweeps get
  # a self-describing enum in the CSV.
  defp resolve_formula_cost(%Parameters{formula_cost_strategy: :default} = params), do: params

  defp resolve_formula_cost(%Parameters{formula_cost_strategy: strategy} = params) do
    %{params | formula_cost: ShotTx.Prover.Rules.resolve_cost_strategy(strategy)}
  end

  defp close_formula(term_id) do
    %Term{fvars: fvars} = TF.get_term!(term_id)

    Enum.reduce(fvars, term_id, fn %Declaration{type: t} = fv, acc_term ->
      TF.make_abstr_term!(acc_term, fv)
      |> then(&app(forall_term(t), &1))
    end)
  end

  defp format_agent_witness(witness) when is_map(witness) do
    case Map.get(witness, :nitpick_output) do
      nil -> "external model finder"
      output when is_binary(output) -> "external model finder\n" <> output
    end
  end

  defp format_agent_witness(_), do: "external model finder"

  defp format_model(model_atoms, model_defs) do
    defs_string =
      model_defs
      |> Enum.map_join(", ", fn {head, term_id} ->
        "#{format!(head)} <- #{format!(term_id)}"
      end)

    atoms_string =
      Enum.reject(model_atoms, &(&1 in [true_term(), neg(false_term())]))
      |> Enum.map_join(", ", &format!(&1))

    case {defs_string, atoms_string} do
      {"", ""} -> ""
      {"", _} -> atoms_string
      {_, ""} -> "[#{defs_string}]"
      {_, _} -> "[#{defs_string}] \nModel: #{atoms_string}"
    end
  end
end
