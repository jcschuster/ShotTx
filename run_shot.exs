# run_shot.exs — CLI for the ShotTx prover
#
# Usage:
#   mix run run_shot.exs [OPTIONS]
#
# Run with --help for the full option listing.

alias ShotDs.{Tptp, Parser, Data.Context}
alias ShotTx.Prover

help = """
Usage: mix run run_shot.exs [OPTIONS]

Input (one required):
  -f, --formula FORMULA        THF formula string
      --file PATH              TPTP problem file (.p)

Mode:
  -m, --mode prove|sat         prove: tautology check (default)
                               sat:   satisfiability check

Prover parameters (all optional, defaults shown):
  -t, --timeout MS                        5000
      --initial-gamma-limit N             1
      --initial-prim-limit N              1
      --prim-subst-after N                0
      --prim-subst-batch-size N           8
      --unification-depth N               8
      --unfold-defs lazy|eager            lazy
      --[no-]beta-variant                 true
      --simplification none|shallow|deep  deep
      --orient none|shallow|deep          none
      --[no-]finite-o-quantification      true
      --paramodulation-mode unification|pattern|matching
                                          unification
      --equivalence-processing same_polarity|bidirectional_imp|dual
                                          bidirectional_imp
      --[no-]instance-based-gamma         true
      --instance-based-gamma-limit N|infinity
                                          0
      --[no-]paramodulation               true
      --[no-]atom-decomposition           true

Other:
  -h, --help                   Show this help

Results (prove mode):  THM | CSA + countermodel | UNK | Timeout
Results (sat mode):    SAT + model | UNSAT | UNK | Timeout
"""

{opts, args, _invalid} =
  OptionParser.parse(System.argv(),
    strict: [
      # script flags
      mode: :string,
      formula: :string,
      file: :string,
      help: :boolean,
      # integer params
      timeout: :integer,
      initial_gamma_limit: :integer,
      initial_prim_limit: :integer,
      prim_subst_after: :integer,
      prim_subst_batch_size: :integer,
      unification_depth: :integer,
      # atom-enum params (parsed as string, converted below)
      unfold_defs: :string,
      simplification: :string,
      orient: :string,
      paramodulation_mode: :string,
      equivalence_processing: :string,
      # special: integer or "infinity"
      instance_based_gamma_limit: :string,
      # boolean params
      beta_variant: :boolean,
      finite_o_quantification: :boolean,
      instance_based_gamma: :boolean,
      paramodulation: :boolean,
      atom_decomposition: :boolean
    ],
    aliases: [m: :mode, f: :formula, t: :timeout, h: :help]
  )

if opts[:help] do
  IO.puts(help)
  System.halt(0)
end

mode =
  case opts[:mode] do
    nil -> :prove
    "prove" -> :prove
    "sat" -> :sat
    other ->
      IO.puts(:stderr, "Error: unknown mode #{inspect(other)}. Use 'prove' or 'sat'.")
      System.halt(1)
  end

# All keys that map directly to Parameters fields (integers and booleans pass through as-is)
passthrough_keys = [
  :timeout, :initial_gamma_limit, :initial_prim_limit, :prim_subst_after,
  :prim_subst_batch_size, :unification_depth,
  :beta_variant, :finite_o_quantification, :instance_based_gamma,
  :paramodulation, :atom_decomposition
]

atom_enum_keys = [:unfold_defs, :simplification, :orient, :paramodulation_mode, :equivalence_processing]

param_kws =
  (passthrough_keys ++ atom_enum_keys ++ [:instance_based_gamma_limit])
  |> Enum.flat_map(fn key ->
    case {key, opts[key]} do
      {_, nil} -> []
      {k, val} when k in [:unfold_defs, :simplification, :orient, :paramodulation_mode, :equivalence_processing] ->
        [{k, String.to_atom(val)}]
      {:instance_based_gamma_limit, "infinity"} -> [{key, :infinity}]
      {:instance_based_gamma_limit, val} -> [{key, String.to_integer(val)}]
      {k, val} -> [{k, val}]
    end
  end)

input =
  cond do
    file = opts[:file] -> {:file, file}
    formula = opts[:formula] || List.first(args) -> {:formula, formula}
    true ->
      IO.puts(:stderr, "Error: provide --formula or --file.\n\n#{help}")
      System.halt(1)
  end

parse_formula = fn str ->
  Parser.parse!(str, force_o: true, ctx: Context.new())
end

result =
  case {mode, input} do
    {:prove, {:file, path}} ->
      path |> Tptp.parse_tptp_file!() |> Prover.prove(param_kws)

    {:prove, {:formula, str}} ->
      str |> parse_formula.() |> Prover.prove([], param_kws)

    {:sat, {:file, path}} ->
      problem = Tptp.parse_tptp_file!(path)
      axiom_ids = Enum.map(problem.axioms, fn {_name, id} -> id end)

      formulas =
        case problem.conjecture do
          {_name, conj_id} -> [conj_id | axiom_ids]
          nil -> axiom_ids
        end

      Prover.sat(formulas, problem.definitions, param_kws)

    {:sat, {:formula, str}} ->
      str |> parse_formula.() |> then(&Prover.sat([&1], %{}, param_kws))
  end

format_sat_model = fn atoms, defs ->
  defs_str =
    defs
    |> Enum.map_join(", ", fn {head, id} ->
      "#{ShotDs.Util.Formatter.format!(head)} <- #{ShotDs.Util.Formatter.format!(id)}"
    end)
    |> then(fn
      "" -> ""
      s -> "[#{s}] "
    end)

  atoms_str =
    atoms
    |> Enum.reject(&(&1 in [ShotDs.Hol.Definitions.true_term()]))
    |> Enum.map_join(", ", &ShotDs.Util.Formatter.format!/1)

  "SAT\n#{defs_str}#{atoms_str}"
end

output =
  case {mode, result} do
    {:prove, res} -> Prover.format_result(res)
    {:sat, {:sat, %{model_atoms: atoms, model_defs: defs}}} -> format_sat_model.(atoms, defs)
    {:sat, {:unsat, _subst, _flex, _traces}} -> "UNSAT"
    {:sat, {:unknown, _}} -> "UNK"
    {:sat, {:timeout, _}} -> "Timeout"
    {:sat, {:error, reason}} -> "Error: #{inspect(reason)}"
  end

IO.puts(output)
