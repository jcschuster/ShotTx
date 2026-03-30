defmodule ShotMain.Prover do
  import ShotDs.Hol.Dsl
  alias ShotMain.Data.Parameters
  use ShotDs.Hol.Patterns
  import ShotDs.Util.Formatter
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Data.{Declaration, Term}
  import ShotDs.Hol.{Definitions, Dsl}

  def prove(conclusion, assumptions \\ [], defs \\ %{}, opts \\ [])
      when is_list(assumptions) do
    closed_conclusion = close_formula(conclusion)
    closed_assms = Enum.map(assumptions, &close_formula/1)

    formulas = [neg(closed_conclusion) | closed_assms]

    case sat(formulas, defs, opts) do
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
  Checks the satisfiability of a list of formulas.
  Delegates the execution to the global Manager GenServer.
  """
  def sat(formulas, defs \\ %{}, opts \\ [])

  def sat(formulas, defs, opts) when is_list(formulas) do
    params = struct!(Parameters, opts)

    case ShotMain.Prover.Manager.prove(formulas, defs, params) do
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

      {:error, reason} ->
        {:error, reason}
    end
  end

  def sat(formula, defs, opts), do: sat([formula], defs, opts)

  defp close_formula(term_id) do
    case TF.get_term(term_id) do
      %Term{fvars: []} ->
        term_id

      %Term{fvars: fvars} ->
        Enum.reduce(fvars, term_id, fn %Declaration{type: t} = fv, acc_term ->
          TF.make_abstr_term(acc_term, fv)
          |> then(&app(pi_term(t), &1))
        end)
    end
  end

  defp format_model(model_atoms, model_defs) do
    defs_string =
      model_defs
      |> Enum.map_join(", ", fn {head, term_id} ->
        "#{format(head, true)} <- #{format(term_id, true)}"
      end)

    atoms_string = Enum.map_join(model_atoms, ", ", &format(&1, true))

    if defs_string == "" do
      atoms_string
    else
      "[#{defs_string}] \nModel: #{atoms_string}"
    end
  end
end
