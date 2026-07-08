defmodule ShotTx.Prover.ModelAgent do
  @moduledoc """
  GenServer that plays the dual of `ContradictionAgent`: probes live branches
  for satisfiability via an external model finder. A `:sat` verdict on any
  branch terminates the session with a confirmed countermodel.

  Ticks on `params.model_agent_min_delta_ms`. On each tick it enumerates
  branches present in the session's `work_queue` and `idle_queue` ETS tables,
  filters out those whose ancestor is tombstoned, and dispatches a backend
  probe for each branch whose `frontier_version` has advanced since we last
  looked. Verdicts are collected asynchronously and reported to the Manager
  through the same `send_proof_result/2` idiom `ContradictionAgent` uses.

  When `params.model_agent_backend` is `:none` the GenServer starts, logs
  once, and stays passive — no ticks, no probes. This is the historical
  default and keeps every existing test path untouched.

  ## Failure isolation

  Probe Tasks are spawned via `Task.Supervisor.async_nolink/2` and monitored.
  If a Task crashes (or the backend blows up), the monitor `:DOWN` message
  cleans the branch out of `in_flight` so it's eligible for a later re-probe.
  Without this the branch would stay stuck as "in flight forever."

  ## Telemetry

  Emits three event families under `[:shot_tx, :model_agent, ...]`:

    * `:tick` — every scan pass. Meta includes counts of live / eligible /
      in-flight / skipped-too-small / skipped-too-big.
    * `:probe, :start | :stop` — per-probe span with `branch_id`,
      `frontier_size`, and terminal `verdict_tag`.
    * `:verdict_conflict` — when MA and CA fire simultaneously with
      disagreeing verdicts (indicates a soundness bug — frontier or
      decomposition).
  """
  use GenServer
  require Logger

  alias ShotDs.Data.Problem
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.{Branch, EtsKeeper}
  alias ShotTx.Prover.ModelAgent.{Backend, Frontier}

  defstruct session_id: nil,
            ets_tables: %{},
            params: %Parameters{},
            backend: nil,
            last_probed_version: %{},
            in_flight: %{},
            tick_ref: nil

  # in_flight :: %{branch_id => %{task_ref: reference, version: non_neg_integer}}

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  @doc "Starts the ModelAgent for the given session."
  @spec start_link({String.t(), Parameters.t()}) :: GenServer.on_start()
  def start_link({session_id, params}) do
    name = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :model_agent}}}
    GenServer.start_link(__MODULE__, {session_id, params}, name: name)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init({session_id, params}) do
    ets_tables = EtsKeeper.get_tables(session_id)

    state = %__MODULE__{
      session_id: session_id,
      params: params,
      ets_tables: ets_tables,
      backend: backend_for(params.model_agent_backend)
    }

    case state.backend do
      nil ->
        {:ok, state}

      _module ->
        Logger.debug(
          "ModelAgent started for #{session_id} with backend #{inspect(state.backend)}"
        )

        {:ok, schedule_tick(state)}
    end
  end

  @impl true
  def handle_info(:tick, state) do
    if aborted?(state) do
      {:noreply, %{state | tick_ref: nil}}
    else
      {:noreply, state |> scan_and_dispatch() |> schedule_tick()}
    end
  end

  @impl true
  def handle_info({:probe_done, branch_id, verdict}, state) do
    do_handle_verdict(branch_id, verdict, state)
  end

  # A monitored probe Task terminated. Clean the branch out of in_flight so
  # it's eligible for a future re-probe. Normal exits fire here too (Task
  # completed successfully) — those are silent. Abnormal exits log a warning.
  @impl true
  def handle_info({:DOWN, ref, :process, _pid, reason}, state) do
    case pop_by_task_ref(state.in_flight, ref) do
      {nil, in_flight} ->
        {:noreply, %{state | in_flight: in_flight}}

      {branch_id, in_flight} ->
        if reason not in [:normal, :shutdown] do
          Logger.warning(
            "ModelAgent probe crashed for branch #{branch_id}: #{inspect(reason)}"
          )
        end

        {:noreply, %{state | in_flight: in_flight}}
    end
  end

  @impl true
  def handle_info(_msg, state), do: {:noreply, state}

  ##############################################################################
  # SCAN + DISPATCH
  ##############################################################################

  defp scan_and_dispatch(state) do
    live = live_branches(state)

    {new_state, counts} =
      Enum.reduce(live, {state, %{eligible: 0, dispatched: 0, skipped: 0}}, fn branch, {s, c} ->
        cond do
          eligible?(branch, s) and map_size(s.in_flight) < s.params.model_agent_max_in_flight ->
            {dispatch_probe(branch, s),
             %{c | eligible: c.eligible + 1, dispatched: c.dispatched + 1}}

          eligible?(branch, s) ->
            {s, %{c | eligible: c.eligible + 1, skipped: c.skipped + 1}}

          true ->
            {s, %{c | skipped: c.skipped + 1}}
        end
      end)

    :telemetry.execute(
      [:shot_tx, :model_agent, :tick],
      Map.merge(counts, %{live: length(live), in_flight: map_size(new_state.in_flight)}),
      %{session_id: state.session_id}
    )

    new_state
  end

  defp live_branches(state) do
    from_work =
      state.ets_tables.work_queue
      |> :ets.tab2list()
      |> Enum.map(fn {_priority_key, branch} -> branch end)

    from_idle =
      state.ets_tables.idle_queue
      |> :ets.tab2list()
      |> Enum.map(fn {_id, branch} -> branch end)

    (from_work ++ from_idle)
    |> Enum.uniq_by(& &1.id)
    |> Enum.reject(&poisoned?(&1.id, state.ets_tables))
  end

  defp eligible?(%Branch{id: id, frontier: frontier, frontier_version: v}, state) do
    size = MapSet.size(frontier)

    size >= state.params.model_agent_min_frontier and
      size <= state.params.model_agent_max_frontier and
      v > Map.get(state.last_probed_version, id, -1) and
      not Map.has_key?(state.in_flight, id)
  end

  defp dispatch_probe(%Branch{} = branch, state) do
    problem = Frontier.to_problem(branch)
    parent = self()
    branch_id = branch.id

    :telemetry.execute(
      [:shot_tx, :model_agent, :probe, :start],
      %{system_time: System.system_time()},
      %{branch_id: branch_id, frontier_size: MapSet.size(branch.frontier)}
    )

    task =
      Task.Supervisor.async_nolink(
        task_sup_via(state.session_id),
        fn ->
          verdict = run_probe(problem, state)
          send(parent, {:probe_done, branch_id, verdict})
          verdict
        end
      )

    %{
      state
      | in_flight:
          Map.put(state.in_flight, branch_id, %{
            task_ref: task.ref,
            version: branch.frontier_version
          }),
        last_probed_version:
          Map.put(state.last_probed_version, branch_id, branch.frontier_version)
    }
  end

  defp run_probe(%Problem{} = problem, state) do
    case state.backend.probe(problem, budget_ms: state.params.model_agent_budget_ms) do
      {:ok, ref} -> state.backend.await(ref, state.params.model_agent_budget_ms)
      {:error, reason} -> {:error, reason}
    end
  end

  ##############################################################################
  # VERDICT HANDLING
  ##############################################################################

  defp do_handle_verdict(branch_id, verdict, state) do
    cleared = %{state | in_flight: Map.delete(state.in_flight, branch_id)}

    :telemetry.execute(
      [:shot_tx, :model_agent, :probe, :stop],
      %{system_time: System.system_time()},
      %{branch_id: branch_id, verdict_tag: verdict_tag(verdict)}
    )

    case verdict do
      {:sat, witness} ->
        maybe_flag_conflict(cleared)
        broadcast_sat(branch_id, witness, cleared)
        {:noreply, cleared}

      {:error, _reason} ->
        # Transient backend errors (bridge starting, temporarily unavailable,
        # timeout) shouldn't burn the branch's probe slot. Clear the
        # last_probed_version so the next tick retries. If the backend is
        # permanently broken this will retry on every tick — the backend
        # itself is responsible for its own backoff behavior.
        retryable = %{
          cleared
          | last_probed_version: Map.delete(cleared.last_probed_version, branch_id)
        }

        {:noreply, retryable}

      _other ->
        {:noreply, cleared}
    end
  end

  defp broadcast_sat(branch_id, witness, state) do
    Logger.warning("ModelAgent confirmed SAT on branch #{branch_id}")

    results = %{
      model_branch_id: branch_id,
      model_witness: witness,
      model_source: :model_agent,
      closed_traces: read_traces(state)
    }

    send_proof_result({:sat, results}, state)
  end

  defp send_proof_result(result, state) do
    case Map.get(state.ets_tables, :stats) do
      nil -> :ok
      stats -> :ets.insert(stats, {:aborted, true})
    end

    manager_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :manager}}}

    GenServer.cast(manager_via, {:proof_result, result})
  end

  # Called when MA is about to declare :sat. If `:aborted` is already true, CA
  # (or something else) beat us to the punch — that's a soundness alarm because
  # Fitting's theorem forbids simultaneous :sat and :unsat verdicts on a
  # consistent problem. Log at :error so it's noticeable in dev; kept out of
  # the terminal flow so we don't disrupt existing behavior.
  defp maybe_flag_conflict(state) do
    case Map.get(state.ets_tables, :stats) do
      nil ->
        :ok

      stats ->
        case :ets.lookup(stats, :aborted) do
          [{:aborted, true}] ->
            :telemetry.execute(
              [:shot_tx, :model_agent, :verdict_conflict],
              %{system_time: System.system_time()},
              %{session_id: state.session_id}
            )

            Logger.error(
              "ModelAgent :sat conflicts with an already-decided verdict on session " <>
                "#{state.session_id}. This should be impossible under Fitting soundness; " <>
                "investigate frontier maintenance or rule decomposition."
            )

          _ ->
            :ok
        end
    end
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp backend_for(:none), do: nil
  defp backend_for(:stub), do: Backend.Stub
  defp backend_for(:nitpick), do: Backend.Nitpick
  defp backend_for({:custom, module}) when is_atom(module), do: module

  defp schedule_tick(%__MODULE__{backend: nil} = state), do: state

  defp schedule_tick(%__MODULE__{} = state) do
    ref = Process.send_after(self(), :tick, state.params.model_agent_min_delta_ms)
    %{state | tick_ref: ref}
  end

  defp aborted?(state) do
    case Map.get(state.ets_tables, :stats) do
      nil -> true
      t -> :ets.lookup(t, :aborted) == [{:aborted, true}]
    end
  end

  defp poisoned?(branch_id, ets_tables) do
    segments = String.split(branch_id, "_")
    prefixes = Enum.scan(segments, fn seg, acc -> acc <> "_" <> seg end)

    try do
      Enum.any?(prefixes, &:ets.member(ets_tables.tombs, &1))
    rescue
      ArgumentError -> true
    end
  end

  defp task_sup_via(session_id),
    do: {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :task_supervisor}}}

  defp read_traces(%__MODULE__{ets_tables: %{traces: table}}) do
    Map.new(:ets.tab2list(table))
  end

  defp read_traces(_), do: %{}

  defp verdict_tag({:sat, _}), do: :sat
  defp verdict_tag(:unknown), do: :unknown
  defp verdict_tag(:unsat), do: :unsat
  defp verdict_tag({:error, _}), do: :error

  # Finds the branch_id whose task_ref matches. Returns {branch_id | nil,
  # updated_in_flight}.
  defp pop_by_task_ref(in_flight, ref) do
    case Enum.find(in_flight, fn {_id, %{task_ref: r}} -> r == ref end) do
      nil -> {nil, in_flight}
      {branch_id, _} -> {branch_id, Map.delete(in_flight, branch_id)}
    end
  end
end
