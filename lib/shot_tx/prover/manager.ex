defmodule ShotTx.Prover.Manager do
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

            # Worker Pool Tracking
            worker_count: 0,
            idle_workers: MapSet.new(),
            saturated_branches: %{}

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  def start_link({session_id, formulas, defs, params}) do
    name = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :manager}}}
    GenServer.start_link(__MODULE__, {session_id, formulas, defs, params}, name: name)
  end

  def prove(formulas, defs, %Parameters{} = params) do
    GenServer.call(__MODULE__, {:start_proof, formulas, defs, params}, :infinity)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init({session_id, formulas, defs, params}) do
    Registry.register(ShotTx.Prover.PubSub, "proof_results_#{session_id}", [])

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

      ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
      GenServer.cast(ca_via, {:set_ets_tables, state.ets_tables})

      root_branch = Branch.new("root", state.formulas, state.defs, state.params)
      priority_key = {byte_size(root_branch.id), root_branch.id}
      :ets.insert(state.ets_tables.work_queue, {priority_key, root_branch})

      spawn_workers(state)

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
  def handle_info({:proof_result, result}, state) do
    if state.active_caller do
      Logger.info("Manager received final result: #{inspect(result)}")
      if state.timer_ref, do: Process.cancel_timer(state.timer_ref)
      :ets.insert(state.ets_tables.stats, {:aborted, true})
      GenServer.reply(state.active_caller, result)
      {:noreply, %{state | active_caller: nil}}
    else
      {:noreply, state}
    end
  end

  @impl true
  def handle_info(:timeout, state) do
    if state.active_caller do
      Logger.warning("Proof timed out!")
      :ets.insert(state.ets_tables.stats, {:aborted, true})
      GenServer.reply(state.active_caller, :timeout)
      {:noreply, %{state | active_caller: nil}}
    else
      {:noreply, state}
    end
  end

  # --- Worker Tracking & Deepening --------------------------------------------

  @impl true
  def handle_cast({:worker_active, worker_id}, state) do
    new_idle = MapSet.delete(state.idle_workers, worker_id)
    {:noreply, %{state | idle_workers: new_idle}}
  end

  @impl true
  def handle_cast({:worker_idle, worker_id}, state) do
    new_idle = MapSet.put(state.idle_workers, worker_id)
    check_and_trigger_deepening(%{state | idle_workers: new_idle})
  end

  @impl true
  def handle_cast({:branch_saturated, branch_id, data}, state) do
    new_sat = Map.put(state.saturated_branches, branch_id, data)
    {:noreply, %{state | saturated_branches: new_sat}}
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
      idle_queue_empty? = :ets.info(state.ets_tables.idle_queue, :size) == 0

      cond do
        has_saturated? ->
          Logger.debug(
            "All workers idle. Saturated branches found. Asking Agent to investigate CSA..."
          )

          ca_cast(state, {:verify_csa, state.saturated_branches})
          {:noreply, state}

        idle_queue_empty? ->
          Logger.debug(
            "All workers idle and queue exhausted. Asking Agent to verify global unification..."
          )

          ca_cast(state, :verify_all_closed)
          {:noreply, state}

        true ->
          transfer_idle_to_work_queue(state.ets_tables, state.params.formula_cost)

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
             state
             | current_gamma_limit: new_gamma,
               current_prim_depth_limit: new_prim,
               idle_workers: MapSet.new()
           }}
      end
    else
      {:noreply, state}
    end
  end

  defp transfer_idle_to_work_queue(ets_tables, cost_fn) do
    parked_branches = :ets.tab2list(ets_tables.idle_queue)

    Enum.each(parked_branches, fn {id, branch} ->
      awakened_branch = Branch.wake_up(branch, cost_fn)
      priority_key = {byte_size(id), id}
      :ets.insert(ets_tables.work_queue, {priority_key, awakened_branch})
    end)

    :ets.delete_all_objects(ets_tables.idle_queue)
  end

  defp ca_cast(state, msg) do
    ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
    GenServer.cast(ca_via, msg)
  end
end
