defmodule ShotTx.Prover.Manager do
  # GenServer, orchestrator and public API
  use GenServer
  require Logger

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.BranchWorker

  # State tracking
  defstruct session_id: nil,
            ets_tables: %{},
            formulas: [],
            defs: %{},
            params: %Parameters{},
            active_caller: nil,
            timer_ref: nil,
            current_gamma_limit: 1,
            active_branches: MapSet.new(),
            idle_branches: MapSet.new(),
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
    Registry.register(ShotTx.Prover.PubSub, "branch_events_#{session_id}", [])

    board_ref =
      :ets.new(:tableau_board, [:bag, :public, read_concurrency: true, write_concurrency: true])

    stats_ref = :ets.new(:tableau_stats, [:set, :public, write_concurrency: true])
    tomb_ref = :ets.new(:tableau_tombstones, [:set, :public, read_concurrency: true])

    ets_tables = %{board: board_ref, stats: stats_ref, tombs: tomb_ref}

    state = %__MODULE__{
      session_id: session_id,
      ets_tables: ets_tables,
      formulas: formulas,
      defs: defs,
      params: params
    }

    {:ok, state}
  end

  @impl true
  def handle_call(:start_proof, from, state) do
    if state.active_caller do
      {:reply, {:error, :prover_busy}, state}
    else
      Logger.info("Manager starting proof with timeout: #{state.params.timeout}ms")

      :ets.insert(state.ets_tables.stats, {:aborted, false})
      :ets.insert(state.ets_tables.stats, {:branch_count, 1})

      ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
      GenServer.cast(ca_via, {:set_ets_tables, state.ets_tables})

      BranchWorker.start_branch(
        "root",
        state.formulas,
        state.defs,
        state.params,
        state.session_id,
        state.ets_tables
      )

      timer = Process.send_after(self(), :timeout, state.params.timeout)

      new_state = %{
        state
        | active_caller: from,
          timer_ref: timer,
          current_gamma_limit: 1,
          active_branches: MapSet.new(["root"]),
          idle_branches: MapSet.new()
      }

      {:noreply, new_state}
    end
  end

  ##### Kill Switches #####

  @impl true
  def handle_info({:proof_result, final_result}, state) do
    if state.active_caller do
      Logger.info("Manager received final result: #{inspect(final_result)}")
      if state.timer_ref, do: Process.cancel_timer(state.timer_ref)
      GenServer.reply(state.active_caller, final_result)
      {:noreply, %{state | active_caller: nil}}
    else
      {:noreply, state}
    end
  end

  @impl true
  def handle_info(:timeout, state) do
    if state.active_caller do
      Logger.warning("Proof timed out!")
      GenServer.reply(state.active_caller, :timeout)
      {:noreply, %{state | active_caller: nil}}
    else
      {:noreply, state}
    end
  end

  ##### Iterative Deepening and Branch Tracking #####

  @impl true
  def handle_info({:branch_status, branch_id, :active}, state) do
    new_active = MapSet.put(state.active_branches, branch_id)
    new_idle = MapSet.delete(state.idle_branches, branch_id)
    new_sat = Map.delete(state.saturated_branches, branch_id)

    new_state = %{
      state
      | active_branches: new_active,
        idle_branches: new_idle,
        saturated_branches: new_sat
    }

    {:noreply, new_state}
  end

  @impl true
  def handle_info({:branch_status, branch_id, {:saturated, {branch_defs, local_atoms}}}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)
    new_idle = MapSet.delete(state.idle_branches, branch_id)
    new_sat = Map.put(state.saturated_branches, branch_id, {branch_defs, local_atoms})

    new_state = %{
      state
      | active_branches: new_active,
        idle_branches: new_idle,
        saturated_branches: new_sat
    }

    check_and_trigger_deepening(new_state)
  end

  @impl true
  def handle_info({:branch_status, branch_id, :closed}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)
    new_idle = MapSet.delete(state.idle_branches, branch_id)
    new_sat = Map.delete(state.saturated_branches, branch_id)

    new_state = %{
      state
      | active_branches: new_active,
        idle_branches: new_idle,
        saturated_branches: new_sat
    }

    check_and_trigger_deepening(new_state)
  end

  @impl true
  def handle_info({:branch_status, branch_id, :idle}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)
    new_idle = MapSet.put(state.idle_branches, branch_id)
    new_sat = Map.delete(state.saturated_branches, branch_id)

    new_state = %{
      state
      | active_branches: new_active,
        idle_branches: new_idle,
        saturated_branches: new_sat
    }

    check_and_trigger_deepening(new_state)
  end

  @impl true
  def handle_info({:branch_status, branch_id, :split}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)
    new_idle = MapSet.delete(state.idle_branches, branch_id)
    new_sat = Map.delete(state.saturated_branches, branch_id)

    new_state = %{
      state
      | active_branches: new_active,
        idle_branches: new_idle,
        saturated_branches: new_sat
    }

    check_and_trigger_deepening(new_state)
  end

  @impl true
  def handle_info(_msg, state), do: {:noreply, state}

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp check_and_trigger_deepening(state) do
    cond do
      is_nil(state.active_caller) ->
        {:noreply, state}

      MapSet.size(state.active_branches) == 0 and
        MapSet.size(state.idle_branches) == 0 and
          Kernel.map_size(state.saturated_branches) > 0 ->
        Logger.debug("All workers finished. Asking Agent to investigate CSA...")

        ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
        GenServer.cast(ca_via, {:verify_csa, state.saturated_branches})

        {:noreply, state}

      MapSet.size(state.active_branches) == 0 and
        MapSet.size(state.idle_branches) == 0 and
          Kernel.map_size(state.saturated_branches) == 0 ->
        Logger.debug(
          "All branches closed explicitly. Asking Agent to verify global unification..."
        )

        ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
        GenServer.cast(ca_via, :verify_all_closed)

        {:noreply, state}

      MapSet.size(state.active_branches) == 0 and MapSet.size(state.idle_branches) > 0 ->
        new_limit = state.current_gamma_limit + 1
        Logger.debug("All branches idle. Increasing Gamma Limit to #{new_limit}...")

        Registry.dispatch(
          ShotTx.Prover.PubSub,
          "branch_events_#{state.session_id}",
          fn entries ->
            for {pid, _} <- entries, do: send(pid, {:wake_up, new_limit})
          end
        )

        new_state = %{
          state
          | current_gamma_limit: new_limit,
            active_branches: state.idle_branches,
            idle_branches: MapSet.new()
        }

        {:noreply, new_state}

      true ->
        {:noreply, state}
    end
  end
end
