defmodule ShotTx.IsabelleBridge do
  @moduledoc """
  Application-level singleton that owns a warm Isabelle connection.

  Isabelle's cold start (server + `HOL-Main` load) is 30–60 s on modest
  hardware — the single heaviest cost in the ShotTx pipeline. Paying it once
  per session would dominate proof time, so this bridge holds one long-lived
  `IsabelleClient.Shared` GenServer and lets every
  `ShotTx.Prover.ModelAgent.Backend.Nitpick` probe borrow it through
  `probe/2` / `await/2`.

  Activation is opt-in via application config:

      config :shot_tx, isabelle_backend: :nitpick

  When unset (or `:none`), the bridge starts and stays in `:inactive` state —
  no server is spawned, no dependency is loaded, and every probe returns
  `:unknown`. That is the default in test and dev.

  ## Concurrency

  `IsabelleClient.Shared` demultiplexes many concurrent callers over one TCP
  socket, routing async task replies back by task id. Each probe runs in a
  short-lived Task that blocks on `Shared.check_text/5`, so N callers get N
  concurrent Isabelle tasks. Nitpick execution itself is bounded by
  Isabelle's own thread pool.

  ## Lifecycle

  The bridge traps exits. On termination it stops the `Shared` client, which
  in turn closes the TCP socket and kills the Isabelle server process —
  preventing the orphan JVM + polyml processes that would otherwise survive
  a bridge crash.
  """
  use GenServer
  require Logger

  alias ShotTx.Prover.ModelAgent.Backend

  @isabelle_client_module IsabelleClient
  @isabelle_shared_module IsabelleClient.Shared

  defstruct status: :inactive,
            shared_pid: nil,
            warmup_pid: nil,
            scratch_dir: nil

  @type status :: :inactive | :starting | :ready | :failed

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc "Reports the current bridge status."
  @spec status() :: status()
  def status, do: GenServer.call(__MODULE__, :status)

  @doc """
  Submits an Isar theory body plus a nitpick invocation. Returns an opaque
  reference the caller later hands to `await/2`. When the bridge is
  `:inactive`, this delivers `:unknown` immediately.
  """
  @spec probe(String.t(), keyword()) :: {:ok, Backend.ref()} | {:error, term()}
  def probe(theory_body, opts \\ []) do
    GenServer.call(__MODULE__, {:probe, theory_body, opts})
  end

  @doc "Blocks up to `timeout_ms` for a verdict."
  @spec await(Backend.ref(), pos_integer()) :: Backend.verdict()
  def await(ref, timeout_ms) do
    receive do
      {:isabelle_verdict, ^ref, verdict} -> verdict
    after
      timeout_ms -> {:error, :timeout}
    end
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init(_opts) do
    Process.flag(:trap_exit, true)

    case Application.get_env(:shot_tx, :isabelle_backend, :none) do
      :none ->
        {:ok, %__MODULE__{status: :inactive}}

      :nitpick ->
        if Code.ensure_loaded?(@isabelle_client_module) do
          me = self()
          warmup_pid = spawn_link(fn -> warmup_worker(me) end)
          {:ok, %__MODULE__{status: :starting, warmup_pid: warmup_pid}}
        else
          Logger.warning(
            "ShotTx.IsabelleBridge: isabelle_backend=:nitpick requested but " <>
              "isabelle_elixir dep not loaded; staying :inactive"
          )

          {:ok, %__MODULE__{status: :inactive}}
        end
    end
  end

  @impl true
  def handle_call(:status, _from, state), do: {:reply, state.status, state}

  @impl true
  def handle_call({:probe, _theory, _opts}, {caller, _tag}, %{status: :inactive} = state) do
    ref = make_ref()
    send(caller, {:isabelle_verdict, ref, :unknown})
    {:reply, {:ok, ref}, state}
  end

  @impl true
  def handle_call({:probe, _theory, _opts}, _from, %{status: :failed} = state) do
    {:reply, {:error, :bridge_failed}, state}
  end

  @impl true
  def handle_call({:probe, _theory, _opts}, _from, %{status: :starting} = state) do
    {:reply, {:error, :bridge_starting}, state}
  end

  @impl true
  def handle_call({:probe, theory_body, opts}, {caller, _tag}, %{status: :ready} = state) do
    ref = make_ref()
    shared = state.shared_pid
    master_dir = state.scratch_dir

    :telemetry.execute(
      [:shot_tx, :isabelle_bridge, :probe, :start],
      %{system_time: System.system_time()},
      %{ref: ref, budget_ms: Keyword.get(opts, :budget_ms, 5_000)}
    )

    Task.start(fn ->
      t0 = System.monotonic_time(:millisecond)
      verdict = do_probe(shared, master_dir, theory_body, opts)
      duration_ms = System.monotonic_time(:millisecond) - t0

      :telemetry.execute(
        [:shot_tx, :isabelle_bridge, :probe, :stop],
        %{duration_ms: duration_ms},
        %{ref: ref, verdict_tag: verdict_tag(verdict)}
      )

      send(caller, {:isabelle_verdict, ref, verdict})
    end)

    {:reply, {:ok, ref}, state}
  end

  @impl true
  def handle_info({:shared_ready, shared, scratch_dir}, state) do
    Process.link(shared)

    :telemetry.execute(
      [:shot_tx, :isabelle_bridge, :status_change],
      %{system_time: System.system_time()},
      %{from: state.status, to: :ready}
    )

    Logger.info("ShotTx.IsabelleBridge: warm, ready to probe")

    {:noreply,
     %{state | status: :ready, shared_pid: shared, warmup_pid: nil, scratch_dir: scratch_dir}}
  end

  @impl true
  def handle_info({:shared_failed, reason}, state) do
    :telemetry.execute(
      [:shot_tx, :isabelle_bridge, :status_change],
      %{system_time: System.system_time()},
      %{from: state.status, to: :failed, reason: inspect(reason)}
    )

    Logger.warning("ShotTx.IsabelleBridge warmup failed: #{inspect(reason)}")
    {:noreply, %{state | status: :failed, warmup_pid: nil}}
  end

  @impl true
  def handle_info({:EXIT, pid, reason}, %{shared_pid: pid} = state) do
    Logger.warning("ShotTx.IsabelleBridge: Shared client died: #{inspect(reason)}")
    {:noreply, %{state | status: :failed, shared_pid: nil}}
  end

  @impl true
  def handle_info({:EXIT, pid, _reason}, %{warmup_pid: pid} = state) do
    # Warmup process exits normally after handing off; nothing to do.
    {:noreply, %{state | warmup_pid: nil}}
  end

  @impl true
  def handle_info({:EXIT, _pid, _reason}, state), do: {:noreply, state}

  @impl true
  def handle_info(_msg, state), do: {:noreply, state}

  @impl true
  def terminate(_reason, %{shared_pid: nil} = state) do
    cleanup_scratch(state.scratch_dir)
    :ok
  end

  def terminate(_reason, %{shared_pid: shared} = state) do
    # Shared.terminate closes the socket AND kills the underlying Isabelle
    # server process, which prevents an orphan JVM+polyml from surviving a
    # bridge crash.
    try do
      GenServer.stop(shared, :normal, 5_000)
    catch
      :exit, _ -> :ok
    end

    cleanup_scratch(state.scratch_dir)
    :ok
  end

  defp cleanup_scratch(nil), do: :ok
  defp cleanup_scratch(dir), do: File.rm_rf(dir)

  ##############################################################################
  # WARMUP
  ##############################################################################

  # Runs in a spawn_linked worker so the bridge process stays responsive to
  # `:status` calls while Isabelle loads its HOL image. On success the shared
  # client is unlinked from the worker (so worker's normal exit doesn't take
  # it down) and re-linked to the bridge on the receiving side.
  defp warmup_worker(bridge_pid) do
    case start_shared() do
      {:ok, shared, scratch_dir} ->
        Process.unlink(shared)
        send(bridge_pid, {:shared_ready, shared, scratch_dir})

      {:error, reason} ->
        send(bridge_pid, {:shared_failed, reason})
    end
  end

  defp start_shared do
    if Code.ensure_loaded?(@isabelle_shared_module) do
      do_start_shared()
    else
      {:error, :isabelle_elixir_not_loaded}
    end
  rescue
    e -> {:error, Exception.message(e)}
  end

  defp do_start_shared do
    with {:ok, shared} <- apply(@isabelle_shared_module, :start_link, [[session: "HOL"]]),
         {:ok, scratch_dir} <- setup_scratch_dir() do
      {:ok, shared, scratch_dir}
    end
  end

  # Creates a per-bridge scratch dir, copies isabelle_elixir's TPTP.thy into
  # it, and returns the path. All probes reuse this dir as their `master_dir`
  # so Isabelle finds TPTP alongside their probe theory. The dir is cleaned up
  # in `terminate/2`.
  defp setup_scratch_dir do
    tptp_mod = Module.concat(@isabelle_client_module, TPTP)

    scratch_dir =
      Path.join([
        System.tmp_dir!(),
        "shot_tx_isabelle_bridge_#{:erlang.unique_integer([:positive])}"
      ])

    File.mkdir_p!(scratch_dir)

    if Code.ensure_loaded?(tptp_mod) do
      source = apply(tptp_mod, :source_path, [])
      File.cp!(source, Path.join(scratch_dir, "TPTP.thy"))
    end

    {:ok, scratch_dir}
  rescue
    e -> {:error, Exception.message(e)}
  end

  ##############################################################################
  # PROBE
  ##############################################################################

  defp do_probe(shared, master_dir, theory_body, opts) do
    timeout_ms = Keyword.get(opts, :budget_ms, 5_000)

    result =
      apply(@isabelle_shared_module, :check_text, [
        shared,
        "ShotTxNitpickProbe",
        theory_body,
        [imports: "TPTP", unicode_symbols: false, master_dir: master_dir],
        timeout_ms
      ])

    case result do
      {:ok, task} ->
        messages = apply(@isabelle_client_module, :messages, [task])
        classify(messages)

      {:error, reason} ->
        {:error, reason}
    end
  rescue
    e -> {:error, Exception.message(e)}
  end

  ##############################################################################
  # VERDICT CLASSIFICATION
  ##############################################################################

  # The false-friend to watch is `"Nitpick found no model"` which means Nitpick
  # exhausted bounded search without finding one, NOT that it found a model.
  # Match on the specific SAT phrases so `"found no model"` never matches.
  @sat_phrases [
    "Nitpick found a model",
    "Nitpick found a genuine model",
    "Nitpick found a quasi genuine model"
  ]

  defp classify(messages) when is_list(messages) do
    blob = Enum.join(messages, "\n")

    if Enum.any?(@sat_phrases, &String.contains?(blob, &1)) do
      {:sat, %{nitpick_output: blob}}
    else
      :unknown
    end
  end

  defp verdict_tag({:sat, _}), do: :sat
  defp verdict_tag(:unknown), do: :unknown
  defp verdict_tag({:error, _}), do: :error
end
