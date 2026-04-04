defmodule ShotTx.Benchmark.TptpRunner do
  require Logger
  alias ShotDs.Tptp
  alias ShotTx.Prover

  @doc """
  Runs the prover against all TH0 files in the TPTP library.
  Ensure the `TPTP_ROOT` environment variable is set before running.
  """
  def run_tptp(output_file \\ "tptp_results.csv") do
    tptp_root = System.get_env("TPTP_ROOT")

    if is_nil(tptp_root) do
      raise "TPTP_ROOT environment variable is missing. Please set it to your TPTP directory."
    end

    File.write!(output_file, "Problem,Result,Time(ms),Details\n")

    problems_dir = Path.join(tptp_root, "Problems")

    problems_dir
    |> Path.join("**/*")
    |> Path.wildcard()
    |> Enum.filter(&String.match?(&1, ~r/\^\d+\.p$/))
    |> Enum.map(fn path ->
      Path.split(path) |> Enum.drop_while(fn name -> name != "Problems" end) |> Path.join()
    end)
    |> Enum.each(&process_problem(&1, output_file))

    Logger.info("Benchmarking complete. Results saved to #{output_file}")
  end

  defp process_problem(file_path, output_file) do
    problem_name = Path.basename(file_path)

    {time_micro, result_data} =
      :timer.tc(fn ->
        try do
          case Tptp.parse_tptp_file(file_path) do
            {:ok, problem} -> run_proof(problem)
            {:error, reason} -> {:parser_error, reason}
          end
        rescue
          e -> {:parser_crash, Exception.message(e)}
        catch
          :exit, reason -> {:exit, inspect(reason)}
        end
      end)

    if result_data != :ignore do
      Logger.info("Evaluated: #{problem_name} -> #{elem(result_data, 0)}")

      time_ms = div(time_micro, 1000)
      write_result(output_file, problem_name, result_data, time_ms)
    end
  end

  defp run_proof(problem) do
    case problem.conjecture do
      {_name, conclusion_term} ->
        axioms = Enum.map(problem.axioms, fn {_name, term} -> term end)

        case Prover.prove(conclusion_term, axioms, problem.definitions) do
          "THM" -> {:thm, "Theorem"}
          "CSA: " <> _model -> {:csa, "Counter-Satisfiable"}
          "UNK" -> {:unk, "Unknown"}
          "Timeout" -> {:timeout, "Timeout"}
          "Error: " <> reason -> {:prover_error, reason}
          other -> {:unexpected, inspect(other)}
        end

      nil ->
        {:no_conjecture, "Problem file contains no conjecture."}
    end
  end

  defp write_result(file, name, {status, details}, time_ms) do
    safe_details = String.replace(details, ~r/[,;\n\r]/, " ")
    line = "#{name},#{status},#{time_ms},#{safe_details}\n"

    File.write!(file, line, [:append])
  end
end
