defmodule ShotTx.MixProject do
  use Mix.Project

  def project do
    [
      app: :shot_tx,
      version: "0.1.0",
      elixir: "~> 1.19",
      start_permanent: Mix.env() == :prod,
      deps: deps()
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
      {:shot_ds, "~> 1.0"},
      # Unification algorithm
      {:shot_un, "~> 0.1"},
      # Code analyzer, duplication checker and security analyzer
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      # Code analyzer and type checker
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      # Documentation generation
      {:ex_doc, "~> 0.40.1", only: :dev, runtime: false}
    ]
  end
end
