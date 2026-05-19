Logger.configure(level: :warning)

Code.require_file("prover_case.exs", __DIR__)

ExUnit.start(capture_log: true)
