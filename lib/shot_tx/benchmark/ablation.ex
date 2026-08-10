defmodule ShotTx.Benchmark.Ablation do
  @moduledoc """
  Declarative ablation matrix for the ShotTx prover.

  The matrix has three parts:

    * **`baseline/1`** — one row, all components enabled, at whatever `timeout`
      the caller specifies.
    * **`oat/1`** — one row per component switched off relative to the
      baseline (one-at-a-time ablation). Answers "how much does component X
      contribute to what the prover can solve?"
    * **`sweeps/1`** — two numeric sweeps at three values each:
      `initial_gamma_limit` and `prim_subst_batch_size`. Answers "how
      sensitive is performance to the main tuning knobs?"

  `matrix/1` concatenates the three, deduplicated on the label.

  The timeout is deliberately *not* a swept dimension: every configuration in
  the matrix runs at the same `base_timeout` (default 2s) so that solved-count
  differences between rows are attributable to the component under ablation
  and not to a differing time budget. Raise it with `base_timeout: 5_000` to
  give every row more room — uniformly.

  Each entry is a `{label, %Parameters{}}` pair, fed straight to
  `ShotTx.Benchmark.TptpRunner.run_sweep/2`.

  ## Typical invocation

      # From iex or `mix run -e`
      configs = ShotTx.Benchmark.Ablation.matrix(base_timeout: 5_000)
      ShotTx.Benchmark.TptpRunner.run_sweep(configs,
        output_dir: "bench_results/2026-07-28",
        language: :both
      )

  Resume after Ctrl-C simply by re-invoking with the same `output_dir` — each
  per-config CSV is loaded to skip already-completed problems. Pause a live
  sweep with `touch bench_results/2026-07-28/STOP`.
  """

  alias ShotTx.Data.Parameters

  @type entry :: {String.t(), Parameters.t()}

  @doc """
  Full ablation matrix: baseline + OAT + numeric sweeps.

  Deduplicated on the `%Parameters{}` value so that sweep rows equal to
  the baseline (typically the middle point of each numeric sweep) drop
  out and are not run twice. The first occurrence's label wins.
  """
  @spec matrix(keyword()) :: [entry()]
  def matrix(opts \\ []) do
    base_timeout = Keyword.get(opts, :base_timeout, 2_000)

    (baseline(base_timeout) ++ oat(base_timeout) ++ sweeps(base_timeout))
    |> Enum.uniq_by(fn {_label, params} -> params end)
  end

  @doc "Baseline: all components on, default parameters."
  @spec baseline(pos_integer()) :: [entry()]
  def baseline(base_timeout) do
    [{"baseline", base_params(base_timeout)}]
  end

  @doc """
  One-at-a-time ablations. Each entry differs from the baseline by a single
  component turned off (or a single enum flipped to its most neutral variant).

  Every row must differ from the baseline in the resulting `%Parameters{}`,
  or `matrix/1`'s deduplication drops it and the component goes unmeasured.
  For a component that is off by default, express the row as an `<name>_on`
  entry that flips it on.
  """
  @spec oat(pos_integer()) :: [entry()]
  def oat(base_timeout) do
    base = base_params(base_timeout)

    [
      {"no_demodulation", %{base | demodulation: false}},
      {"no_beta_variant", %{base | beta_variant: false}},
      {"no_prim_subst", %{base | primitive_substitution: false}},
      {"no_contradiction_agent", %{base | contradiction_agent: false}},
      {"no_instance_based_gamma", %{base | instance_based_gamma: false}},
      {"no_atom_decomposition", %{base | atom_decomposition: false}},
      {"no_finite_o_quantification", %{base | finite_o_quantification: false}},
      {"eager_unfold_defs", %{base | unfold_defs: :eager}},
      {"no_iterative_deepening", %{base | iterative_deepening: false}},
      {"serial", %{base | worker_pool_size: 1}},
      {"no_suggestions", %{base | suggestions_enabled: false}}
    ]
  end

  @doc """
  Numeric parameter sweeps at three values each.

  `timeout` is not among them, by design — see the module doc. Every row here
  inherits `base_timeout` unchanged.
  """
  @spec sweeps(pos_integer()) :: [entry()]
  def sweeps(base_timeout) do
    base = base_params(base_timeout)

    gamma_sweep =
      for g <- [1, 3, 5] do
        {"gamma_limit_#{g}", %{base | initial_gamma_limit: g}}
      end

    prim_batch_sweep =
      for b <- [4, 8, 16] do
        {"prim_batch_#{b}", %{base | prim_subst_batch_size: b}}
      end

    gamma_sweep ++ prim_batch_sweep
  end

  @doc """
  Convenience wrapper: build the matrix and run it against TPTP, writing to
  `output_dir`. Extra options are forwarded to `TptpRunner.run_sweep/2`.
  """
  @spec run(keyword()) :: :ok | :stopped
  def run(opts \\ []) do
    {matrix_opts, runner_opts} = Keyword.split(opts, [:base_timeout])
    configs = matrix(matrix_opts)
    ShotTx.Benchmark.TptpRunner.run_sweep(configs, runner_opts)
  end

  defp base_params(base_timeout), do: %Parameters{timeout: base_timeout}
end
