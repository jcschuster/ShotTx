defmodule ShotTx.Prover.ModelAgent.Backend.Nitpick do
  @moduledoc """
  `Backend` that ships the branch's frontier to a warm Isabelle server and
  runs `nitpick[satisfy]` against it.

  Pipeline:

    1. `Frontier.to_problem/1` turns the branch into a `%ShotDs.Data.Problem{}`.
    2. `ShotDs.Tptp.unparse_problem/1` renders it as THF text with all
       constants declared and every axiom universally-closed over its free
       variables.
    3. `IsabelleClient.TPTP.isabellize_theory/1` (from `isabelle_elixir`)
       converts the THF into Isabelle theory commands.
    4. A `theorem "True" nitpick[satisfy, user_axioms=true, …]` is appended so
       Nitpick searches for a model of the axioms rather than a countermodel of
       a specific goal. `user_axioms=true` is critical — without it Nitpick
       ignores the axioms and trivially satisfies the `True` goal.
    5. `ShotTx.IsabelleBridge.probe/2` submits the theory body and returns an
       async reference. `await/2` blocks for the verdict.

  ## Nitpick options

  Per-probe options via `opts[:nitpick_opts]` — merged into the invocation.
  Common knobs:

    * `card: n` — cap on cardinality search
    * `mono: true|false` — assume monotonicity for polymorphic types
    * `iter: n` — iteration count for coinductive datatypes
    * `sat_solver: "…"` — override the SAT backend

  Timeout is derived from `opts[:budget_ms]` (converted to seconds). If
  `nitpick_opts` explicitly sets `timeout`, that value wins.

  The result of parsing Nitpick's messages is coarse — `:sat` when Nitpick
  reports a model, `:unknown` otherwise. Structured countermodel extraction
  is left for a follow-up; the model string is stashed in the witness payload
  as `:nitpick_output` for display.
  """
  @behaviour ShotTx.Prover.ModelAgent.Backend

  alias ShotDs.Data.Problem
  alias ShotDs.Tptp
  alias ShotTx.IsabelleBridge

  @isabelle_tptp IsabelleClient.TPTP

  @default_nitpick_opts [satisfy: true, user_axioms: true]

  @impl true
  def probe(%Problem{} = problem, opts) do
    case build_theory_body(problem, opts) do
      {:ok, body} -> IsabelleBridge.probe(body, opts)
      {:error, _} = err -> err
    end
  end

  @impl true
  def await(ref, timeout_ms), do: IsabelleBridge.await(ref, timeout_ms)

  ##############################################################################
  # THEORY BUILDING
  ##############################################################################

  defp build_theory_body(%Problem{} = problem, opts) do
    with {:ok, thf} <- Tptp.unparse_problem(problem),
         {:ok, isar} <- to_isar(thf) do
      body =
        [
          "unbundle from_TPTP",
          isar,
          "unbundle no from_TPTP",
          "theorem sat_probe: \"True\"",
          "  nitpick[#{format_opts(opts)}]",
          "  oops"
        ]
        |> Enum.join("\n")

      {:ok, body}
    end
  end

  defp to_isar(thf) do
    if Code.ensure_loaded?(@isabelle_tptp) do
      {:ok, apply(@isabelle_tptp, :isabellize_theory, [thf])}
    else
      {:error, :isabelle_elixir_not_loaded}
    end
  rescue
    e -> {:error, Exception.message(e)}
  end

  # Merges defaults + user overrides + a computed timeout. User `nitpick_opts`
  # override the defaults, and an explicit `timeout` in `nitpick_opts` wins over
  # the budget-derived one so callers can dial Nitpick independently.
  defp format_opts(opts) do
    user = Keyword.get(opts, :nitpick_opts, [])
    budget_ms = Keyword.get(opts, :budget_ms, 5_000)

    computed_timeout =
      if Keyword.has_key?(user, :timeout), do: [], else: [timeout: max(1, div(budget_ms, 1_000))]

    (@default_nitpick_opts ++ user ++ computed_timeout)
    |> Enum.uniq_by(&elem(&1, 0))
    |> Enum.map_join(", ", &format_opt/1)
  end

  defp format_opt({key, true}), do: "#{key}"
  defp format_opt({key, false}), do: "~#{key}"

  defp format_opt({key, value}) when is_integer(value) or is_atom(value),
    do: "#{key}=#{value}"

  defp format_opt({key, value}) when is_binary(value), do: "#{key}=\"#{value}\""
end
