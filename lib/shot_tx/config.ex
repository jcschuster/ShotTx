defmodule ShotTx.Config do
  @moduledoc """
  Session-global defaults for `ShotTx.Prover` calls.

  Values set here are used as the base parameters for every `prove/*` and
  `sat/*` call; per-call options still override them. Intended for Livebook
  sessions where you want to fix a few flags once (e.g. `timeout`,
  `unfold_defs`, `suggestions_enabled`) instead of threading them through
  every invocation.

      ShotTx.Config.configure(timeout: 30_000, suggestions_enabled: true)
      ShotTx.Prover.prove(problem)                     # uses the globals
      ShotTx.Prover.prove(problem, [], timeout: 1_000) # per-call wins

  Storage is `Application.put_env(:shot_tx, :prover_defaults, ...)`, so the
  scope is the whole OTP node — two Livebooks sharing a runtime share
  config.
  """

  alias ShotTx.Data.Parameters

  @env_key :prover_defaults

  @valid_keys Parameters.__struct__() |> Map.keys() |> List.delete(:__struct__)

  @doc """
  Merges `opts` into the current global defaults. Unknown keys (not fields of
  `ShotTx.Data.Parameters`) raise `ArgumentError`.
  """
  @spec configure(keyword()) :: keyword()
  def configure(opts) when is_list(opts) do
    :ok = validate_keys!(opts)
    merged = Keyword.merge(get(), opts)
    Application.put_env(:shot_tx, @env_key, merged)
    merged
  end

  @doc "Returns the current global defaults as a keyword list."
  @spec get() :: keyword()
  def get, do: Application.get_env(:shot_tx, @env_key, [])

  @doc "Clears all global defaults."
  @spec reset() :: :ok
  def reset, do: Application.delete_env(:shot_tx, @env_key)

  defp validate_keys!(opts) do
    case Enum.reject(Keyword.keys(opts), &(&1 in @valid_keys)) do
      [] ->
        :ok

      bad ->
        raise ArgumentError,
              "unknown ShotTx.Prover option(s): #{inspect(bad)}. " <>
                "Valid keys: #{inspect(@valid_keys)}"
    end
  end
end
