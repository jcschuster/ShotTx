# Evaluates ONE problem from ShotTx.Benchmark.HolSuite and prints its CSV row.
#
# Usage:
#   mix run scripts/hol_problem.exs <problem-id> [timeout-ms]
#   mix run scripts/hol_problem.exs --list       # print every problem id
#   mix run scripts/hol_problem.exs --header     # print the CSV header
#
# Driven by scripts/run_hol_benchmark.sh, which invokes it once per problem so
# each measurement gets a fresh BEAM. See ShotTx.Benchmark.HolRunner for why
# that isolation is not optional.

alias ShotTx.Benchmark.{HolRunner, HolSuite}

# stdout carries exactly one thing: the CSV row. The prover narrates its
# search at :info, announces closures at :warning, and emits multi-line crash
# reports at :error — all on stdout, all of which would otherwise be captured
# as part of the row. Nothing is lost by silencing it: a failed attempt is
# recorded in the row's `details` column either way.
Logger.configure(level: :none)

case System.argv() do
  ["--list"] ->
    Enum.each(HolSuite.problems(), &IO.puts(&1.id))

  ["--header"] ->
    IO.write(HolRunner.csv_header())

  [id | rest] ->
    params =
      case rest do
        [timeout] -> %{HolRunner.params() | timeout: String.to_integer(timeout)}
        [] -> HolRunner.params()
      end

    case HolSuite.fetch(id) do
      {:ok, problem} ->
        HolRunner.warm_up(params)
        IO.write(HolRunner.csv_row(HolRunner.evaluate(problem, params)))

      :error ->
        IO.puts(:stderr, "unknown problem id: #{id}")
        System.halt(1)
    end

  [] ->
    IO.puts(:stderr, "usage: mix run scripts/hol_problem.exs <problem-id> [timeout-ms]")
    System.halt(1)
end
