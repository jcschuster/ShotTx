defmodule ShotTx.Prover do
  import ShotDs.Hol.Dsl
  alias ShotTx.Data.Parameters
  use ShotDs.Hol.Patterns
  import ShotDs.Util.Formatter
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Data.{Declaration, Term, Problem}
  import ShotDs.Hol.{Definitions, Dsl}

  require Logger

  def prove(problem) when is_struct(problem, Problem), do: prove(problem, [])

  def prove(conclusion) when is_integer(conclusion), do: prove(conclusion, [], [])

  def prove(conclusion, [{key, _} | _] = opts) when is_integer(conclusion) and is_atom(key),
    do: prove(conclusion, [], opts)

  def prove(conclusion, assumptions) when is_integer(conclusion) and is_list(assumptions),
    do: prove(conclusion, assumptions, [defs: %{}])

  def prove(%Problem{} = problem, opts) when is_struct(problem, Problem) do
    if is_nil(problem.conjecture) do
      "Error: no conjecture found"
    else
      {_name, conclusion} = problem.conjecture
      assumptions = Enum.map(problem.axioms, fn {_name, axiom} -> axiom end)
      prove(conclusion, assumptions, [{:defs, problem.definitions} | opts])
    end
  end

  def prove(conclusion, assumptions, opts) when is_integer(conclusion) and is_list(assumptions) and is_list(opts) do
    {defs, params} = Keyword.pop(opts, :defs, %{})

    Logger.info(
      "Attempting to prove:\n" <>
      Enum.map_join(assumptions, ", ", &format!(&1, false)) <>
      " ⊢ " <>
      format!(conclusion, false)
      )

    closed_conclusion = close_formula(conclusion)
    closed_assms = Enum.map(assumptions, &close_formula/1)

    formulas = [neg(closed_conclusion) | closed_assms]

    case sat(formulas, defs, params) do
      {:sat, model} ->
        "CSA: #{model}"

      :unsat ->
        "THM"

      {:cond_unsat, _subst, flex_pairs} ->
        "THM (Conditional on #{length(flex_pairs)} Flex-Flex constraints)"

      {:unknown, _partial_model} ->
        "UNK"

      :timeout ->
        "Timeout"

      {:error, reason} ->
        "Error: #{inspect(reason)}"
    end
  end

  @doc """
  Checks the satisfiability of a list of formulas. Delegates the execution to
  the Manager GenServer.
  """
  def sat(formulas, defs \\ %{}, opts \\ [])

  def sat(formulas, defs, opts) when is_list(formulas) do
    params = struct!(Parameters, opts)
    session_id = make_ref() |> inspect()

    {:ok, session_pid} =
      DynamicSupervisor.start_child(
        ShotTx.SessionSpawner,
        {ShotTx.Prover.SessionSupervisor, {session_id, formulas, defs, params}}
      )

    manager_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :manager}}}
    result = GenServer.call(manager_via, :start_proof, :infinity)

    DynamicSupervisor.terminate_child(ShotTx.SessionSpawner, session_pid)

    case result do
      {:sat, {model_atoms, model_defs}} ->
        {:sat, format_model(model_atoms, model_defs)}

      {:unsat, _global_substitution} ->
        :unsat

      {:cond_unsat, global_substitutions, flex_pairs} ->
        {:cond_unsat, global_substitutions, flex_pairs}

      {:unknown, :max_branches_reached} ->
        {:unknown, "Branch limit (#{params.max_branches}) reached."}

      {:unknown, _} ->
        {:unknown, []}

      :timeout ->
        :timeout

      other ->
        other
    end
  end

  def sat(formula, defs, opts), do: sat([formula], defs, opts)

  defp close_formula(term_id) do
    case TF.get_term!(term_id) do
      %Term{fvars: []} ->
        term_id

      %Term{fvars: fvars} ->
        Enum.reduce(fvars, term_id, fn %Declaration{type: t} = fv, acc_term ->
          TF.make_abstr_term!(acc_term, fv)
          |> then(&app(pi_term(t), &1))
        end)
    end
  end

  defp format_model(model_atoms, model_defs) do
    defs_string =
      model_defs
      |> Enum.map_join(", ", fn {head, term_id} ->
        "#{format!(head)} <- #{format!(term_id)}"
      end)

    atoms_string =
      Enum.reject(model_atoms, & &1 in [true_term(), neg(false_term())])
      |> Enum.map_join(", ", &format!(&1))

    case {defs_string, atoms_string} do
      {"", ""} -> ""
      {"", _} -> atoms_string
      {_, ""} -> "[#{defs_string}]"
      {_, _} -> "[#{defs_string}] \nModel: #{atoms_string}"
    end
  end
end
