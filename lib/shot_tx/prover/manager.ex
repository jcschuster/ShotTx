defmodule ShotTx.Prover.Manager do
  @moduledoc """
  GenServer that orchestrates the proof search for a single session.

  On `start_proof`, seeds the root branch into the ETS work queue, spawns `N`
  worker processes, and sets a timeout timer. Workers report back as idle when
  their queue empties; once all workers stall the Manager triggers iterative
  deepening by incrementing the gamma and prim-subst limits and waking the parked
  branches. The final proof result is returned synchronously to the caller of
  `start_proof`.
  """

  use GenServer
  require Logger

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Branch

  defstruct session_id: nil,
            ets_tables: %{},
            formulas: [],
            defs: %{},
            params: %Parameters{},
            active_caller: nil,
            timer_ref: nil,
            current_gamma_limit: 1,
            current_prim_depth_limit: 1,
            worker_count: 0,
            idle_workers: MapSet.new(),
            saturated_branches: %{},
            parked_count: 0

  @root_name "root"
  @progress_interval_ms 2_000

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  @doc "Starts the Manager for the given session."
  @spec start_link({String.t(), [term()], map(), Parameters.t()}) :: GenServer.on_start()
  def start_link({session_id, formulas, defs, params}) do
    name = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :manager}}}
    GenServer.start_link(__MODULE__, {session_id, formulas, defs, params}, name: name)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init({session_id, formulas, defs, params}) do
    ets_tables = ShotTx.Prover.EtsKeeper.get_tables(session_id)
    worker_count = Map.get(params, :worker_pool_size, System.schedulers_online())

    state = %__MODULE__{
      session_id: session_id,
      ets_tables: ets_tables,
      formulas: formulas,
      defs: defs,
      params: params,
      worker_count: worker_count
    }

    {:ok, state}
  end

  @impl true
  def handle_call(:start_proof, from, state) do
    if state.active_caller do
      {:reply, {:error, :prover_busy}, state}
    else
      Logger.info(
        "Manager starting proof with #{state.worker_count} workers. Timeout: #{state.params.timeout}ms"
      )

      :ets.insert(state.ets_tables.stats, {:aborted, false})

      root_branch = Branch.new(@root_name, state.formulas, state.params, defs: state.defs)
      priority_key = {byte_size(root_branch.id), root_branch.id}
      :ets.insert(state.ets_tables.work_queue, {priority_key, root_branch})

      spawn_workers(state)

      Process.send_after(self(), :log_progress, @progress_interval_ms)
      timer = Process.send_after(self(), :timeout, state.params.timeout)

      {:noreply,
       %{
         state
         | active_caller: from,
           timer_ref: timer,
           current_gamma_limit: state.params.initial_gamma_limit,
           current_prim_depth_limit: state.params.initial_prim_limit,
           idle_workers: MapSet.new()
       }}
    end
  end

  # --- Kill Switches & Results ------------------------------------------------

  @impl true
  def handle_info(:timeout, state) do
    if state.active_caller do
      Logger.warning("Proof timed out!")

      stats = ShotTx.Prover.Stats.snapshot(state.ets_tables)
      :ets.insert(state.ets_tables.stats, {:aborted, true})

      log_timeout_traces(state)

      partial_proof = ShotTx.Proof.from_partial(gather_traces(state), state.formulas)

      GenServer.reply(state.active_caller, {{:timeout, partial_proof}, stats})
      {:noreply, %{state | active_caller: nil}}
    else
      {:noreply, state}
    end
  end

  @impl true
  def handle_info(:log_progress, %{active_caller: nil} = state), do: {:noreply, state}

  @impl true
  def handle_info(:log_progress, state) do
    stats = ShotTx.Prover.Stats.snapshot(state.ets_tables)
    queue_size = :ets.info(state.ets_tables.work_queue, :size)
    parked_size = :ets.info(state.ets_tables.idle_queue, :size)

    Logger.info(
      "Progress | gamma=#{state.current_gamma_limit} prim=#{state.current_prim_depth_limit}" <>
        " | idle #{MapSet.size(state.idle_workers)}/#{state.worker_count} workers" <>
        " | queue=#{queue_size} parked=#{parked_size}" <>
        " | steps=#{Map.get(stats, :steps_total, 0)}" <>
        " γ=#{Map.get(stats, :rule_gamma, 0)}" <>
        " prim=#{Map.get(stats, :rule_prim_subst, 0)}" <>
        " closed=#{Map.get(stats, :branches_closed_locally, 0)}" <>
        " sat=#{Map.get(stats, :branches_saturated, 0)}"
    )

    Process.send_after(self(), :log_progress, @progress_interval_ms)
    {:noreply, state}
  end

  @impl true
  def handle_info(_, state) do
    {:noreply, state}
  end

  # --- Worker Tracking & Deepening --------------------------------------------

  @impl true
  def handle_cast({:worker_active, worker_id}, state) do
    new_idle = MapSet.delete(state.idle_workers, worker_id)
    {:noreply, %{state | idle_workers: new_idle}}
  end

  @impl true
  def handle_cast({:worker_idle, worker_id}, state) do
    case :ets.lookup(state.ets_tables.stats, :aborted) do
      [{:aborted, true}] ->
        {:noreply, state}

      _ ->
        Logger.debug(
          "worker_idle from #{worker_id}; idle_workers size now #{MapSet.size(MapSet.put(state.idle_workers, worker_id))}"
        )

        new_idle = MapSet.put(state.idle_workers, worker_id)
        check_and_trigger_deepening(%{state | idle_workers: new_idle})
    end
  end

  @impl true
  def handle_cast({:branch_saturated, branch_id, data}, state) do
    new_sat = Map.put(state.saturated_branches, branch_id, data)
    {:noreply, %{state | saturated_branches: new_sat}}
  end

  @impl true
  def handle_cast({:proof_result, result}, state) do
    if state.active_caller do
      Logger.info("Manager received final result: #{inspect(result)}")
      if state.timer_ref, do: Process.cancel_timer(state.timer_ref)

      ShotTx.Prover.Stats.set(
        state.ets_tables,
        :proof_finished_at_us,
        System.monotonic_time(:microsecond)
      )

      stats = ShotTx.Prover.Stats.snapshot(state.ets_tables)
      :ets.insert(state.ets_tables.stats, {:aborted, true})

      GenServer.reply(state.active_caller, {result, stats})
      {:noreply, %{state | active_caller: nil}}
    else
      {:noreply, state}
    end
  end

  @impl true
  def handle_cast({:branch_parked, _branch_id}, state) do
    {:noreply, %{state | parked_count: state.parked_count + 1}}
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp spawn_workers(state) do
    supervisor_via =
      {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :branch_supervisor}}}

    for i <- 1..state.worker_count do
      DynamicSupervisor.start_child(
        supervisor_via,
        {ShotTx.Prover.Worker,
         [
           worker_id: "worker_#{i}",
           session_id: state.session_id,
           ets_tables: state.ets_tables,
           params: state.params,
           initial_gamma_limit: state.params.initial_gamma_limit,
           initial_prim_limit: state.params.initial_prim_limit
         ]}
      )
    end
  end

  defp check_and_trigger_deepening(state) do
    all_idle? = MapSet.size(state.idle_workers) == state.worker_count

    if all_idle? and not is_nil(state.active_caller) do
      has_saturated? = map_size(state.saturated_branches) > 0
      idle_queue_empty? = state.parked_count == 0

      cond do
        has_saturated? ->
          Logger.debug(
            "All workers idle. Saturated branches found. Asking Agent to investigate CSA..."
          )

          GenServer.cast(ca_via(state), {:verify_csa, state.saturated_branches})
          {:noreply, state}

        idle_queue_empty? ->
          Logger.debug(
            "All workers idle and queue exhausted. Asking Agent to verify global unification..."
          )

          GenServer.cast(ca_via(state), :verify_all_closed)
          {:noreply, state}

        true ->
          send_wake_up_if_open(state)
      end
    else
      {:noreply, state}
    end
  end

  defp send_wake_up_if_open(state) do
    case GenServer.call(ca_via(state), :settle, :infinity) do
      :closed ->
        {:noreply, state}

      :open ->
        new_state =
          transfer_idle_to_work_queue(state, state.ets_tables, state.params.formula_cost)

        new_gamma = state.current_gamma_limit + 1
        new_prim = state.current_prim_depth_limit + 1

        Logger.debug(
          "Iterative deepening triggered. Gamma: #{new_gamma}, Prim depth: #{new_prim}"
        )

        Registry.dispatch(
          ShotTx.Prover.PubSub,
          "branch_control_#{state.session_id}",
          fn entries ->
            for {pid, _} <- entries, do: send(pid, {:wake_up, new_gamma, new_prim})
          end
        )

        {:noreply,
         %{
           new_state
           | current_gamma_limit: new_gamma,
             current_prim_depth_limit: new_prim,
             idle_workers: MapSet.new()
         }}
    end
  end

  defp transfer_idle_to_work_queue(state, ets_tables, cost_fn) do
    parked_branches = :ets.tab2list(ets_tables.idle_queue)

    Enum.each(parked_branches, fn {id, branch} ->
      awakened_branch = Branch.wake_up(branch, cost_fn)
      priority_key = {byte_size(id), id}
      :ets.insert(ets_tables.work_queue, {priority_key, awakened_branch})
    end)

    :ets.delete_all_objects(ets_tables.idle_queue)
    %{state | parked_count: 0}
  end

  defp gather_traces(state) do
    ets_traces = Map.new(:ets.tab2list(state.ets_tables.traces))

    queue_branches =
      state.ets_tables.work_queue
      |> :ets.tab2list()
      |> Enum.map(fn {_key, branch} -> branch end)

    idle_branches =
      state.ets_tables.idle_queue
      |> :ets.tab2list()
      |> Enum.map(fn {_id, branch} -> branch end)

    Enum.reduce(queue_branches ++ idle_branches, ets_traces, fn branch, acc ->
      Map.put(acc, branch.id, Enum.reverse(branch.history))
    end)
  end

  defp log_timeout_traces(state) do
    queued =
      state.ets_tables.work_queue
      |> :ets.tab2list()
      |> Enum.map(fn {_key, branch} -> branch end)

    parked =
      state.ets_tables.idle_queue
      |> :ets.tab2list()
      |> Enum.map(fn {_id, branch} -> branch end)

    queued_str = Enum.map_join(queued, "\n", &format_branch_for_log/1)
    parked_str = Enum.map_join(parked, "\n", &format_branch_for_log/1)

    Logger.warning("""
    Timeout trace — gamma_limit=#{state.current_gamma_limit} prim_limit=#{state.current_prim_depth_limit} idle_workers=#{MapSet.size(state.idle_workers)}/#{state.worker_count}
    work_queue (#{length(queued)} branch(es)):
    #{if queued == [], do: "  (empty)", else: queued_str}
    idle_queue (#{length(parked)} branch(es)):
    #{if parked == [], do: "  (empty)", else: parked_str}
    """)
  end

  defp format_branch_for_log(branch) do
    total = length(branch.history)
    recent = branch.history |> Enum.take(20) |> Enum.reverse()

    sleeping_str =
      case branch.sleeping_gamma_rules do
        [] -> ""
        rules -> " [#{length(rules)} sleeping gamma]"
      end

    rule_lines =
      Enum.map_join(recent, "\n", fn {_src, rule, _produced} -> "    #{inspect(rule)}" end)

    "  [#{branch.id}] #{total} step(s)#{sleeping_str}:\n#{rule_lines}"
  end

  defp ca_via(state),
    do: {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
end
