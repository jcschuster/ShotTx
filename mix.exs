defmodule ShotTx.MixProject do
  use Mix.Project

  @version "0.0.4"
  @source_url "https://github.com/jcschuster/ShotTx"

  def project do
    [
      app: :shot_tx,
      version: @version,
      elixir: "~> 1.20",
      start_permanent: Mix.env() == :prod,
      test_ignore_filters: ["test/prover_case.exs"],
      deps: deps(),
      escript: escript(),
      docs: docs(),
      package: package(),
      name: "ShotTx",
      description:
        "Tableau component of Shot, a parallel Church Simple Type Theory theorem prover.",
      source_url: @source_url
    ]
  end

  defp package do
    [
      licenses: ["MIT"],
      links: %{"GitHub" => @source_url},
      maintainers: ["Johannes Schuster"],
      files: ~w(lib mix.exs README.md LICENSE CHANGELOG.md)
    ]
  end

  defp escript do
    [
      main_module: ShotTx.Cli,
      name: "shot_tx",
      app: :shot_tx,
      # Force UTF-8 filename encoding so the script runs cleanly regardless
      # of the caller's locale — otherwise the BEAM prints a runtime warning
      # about latin1 encoding on every invocation.
      emu_args: "+fnu"
    ]
  end

  defp docs do
    [
      main: "ShotTx",
      extras: ["README.md"],
      groups_for_modules: [
        "Public API": [
          ShotTx,
          ShotTx.Cli,
          ShotTx.Prover,
          ShotTx.Config,
          ShotTx.Data.Parameters,
          ShotTx.Proof
        ],
        "Proof search core": [
          ShotTx.Prover.Branch,
          ShotTx.Prover.Rules,
          ShotTx.Prover.Paramodulation,
          ShotTx.Prover.Demodulation,
          ShotTx.Prover.TermOrder,
          ShotTx.Prover.LambdaLift,
          ShotTx.Prover.FormulaPqueue,
          ShotTx.Util.PropSimplify
        ],
        "OTP / concurrency": [
          ShotTx.Prover.SessionSupervisor,
          ShotTx.Prover.Manager,
          ShotTx.Prover.Worker,
          ShotTx.Prover.EtsKeeper,
          ShotTx.Prover.Stats
        ],
        Agents: [
          ShotTx.Prover.ContradictionAgent,
          ShotTx.Prover.SuggestionAgent,
          ShotTx.Prover.Suggestion,
          ShotTx.Prover.ModelAgent,
          ShotTx.Prover.ModelAgent.Backend,
          ShotTx.Prover.ModelAgent.Backend.Nitpick,
          ShotTx.Prover.ModelAgent.Backend.Stub,
          ShotTx.Prover.ModelAgent.Frontier,
          ShotTx.IsabelleBridge
        ],
        Generation: [
          ShotTx.Generation,
          ShotTx.Generation.GeneralBindings,
          ShotTx.Generation.TypeUniverse,
          ShotTx.Prover.Provenance
        ],
        Benchmarking: [
          ShotTx.Benchmark.Ablation,
          ShotTx.Benchmark.TptpRunner,
          ShotTx.Benchmark.HolSuite,
          ShotTx.Benchmark.HolRunner
        ]
      ]
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger],
      mod: {ShotTx.Application, []}
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      # Data structures and semantics for HOL objects
      {:shot_ds, "~> 1.3"},
      # Unification algorithm
      {:shot_un, "~> 0.2"},
      # NCPO Term Ordering
      {:shot_to, "~> 0.2"},
      # Isabelle client — powers `ShotTx.Prover.ModelAgent.Backend.Nitpick`.
      # Optional: absence leaves the ModelAgent stubbed. Enable with
      # `config :shot_tx, isabelle_backend: :nitpick` after installing.
      {:isabelle_elixir, "~> 0.4", optional: true},
      # Standard observability events for ModelAgent + IsabelleBridge.
      {:telemetry, "~> 1.2"},
      # Code analyzer, duplication checker and security analyzer
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      # Code analyzer and type checker
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      # Documentation generation
      {:ex_doc, "~> 0.40.1", only: :dev, runtime: false}
    ]
  end
end
