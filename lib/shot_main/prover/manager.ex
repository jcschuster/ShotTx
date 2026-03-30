defmodule ShotMain.Prover.Manager do
  # GenServer, orchestrator and public API
  use GenServer
  require Logger

  alias ShotMain.Data.Parameters
  alias ShotMain.Prover.BranchWorker

  # State tracking
  defstruct active_caller: nil,
            timer_ref: nil,
            current_gamma_limit: 1,
            active_branches: MapSet.new(),
            idle_branches: MapSet.new(),
            saturated_branches: %{}

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  def start_link(_opts \\ []) do
    GenServer.start_link(__MODULE__, %__MODULE__{}, name: __MODULE__)
  end

  def prove(formulas, defs, %Parameters{} = params) do
    GenServer.call(__MODULE__, {:start_proof, formulas, defs, params}, :infinity)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init(state) do
    Registry.register(ShotMain.Prover.PubSub, "proof_results", [])
    Registry.register(ShotMain.Prover.PubSub, "branch_events", [])

    :ets.new(:tableau_board, [
      :bag,
      :public,
      :named_table,
      read_concurrency: true,
      write_concurrency: true
    ])

    :ets.new(:tableau_lineage, [:set, :public, :named_table, read_concurrency: true])

    :ets.new(:tableau_stats, [:set, :public, :named_table, write_concurrency: true])

    {:ok, state}
  end

  @impl true
  def handle_call({:start_proof, formulas, defs, params}, from, state) do
    if state.active_caller do
      {:reply, {:error, :prover_busy}, state}
    else
      Logger.info("Manager starting proof with timeout: #{params.timeout}ms")

      cleanup_environment()

      :ets.insert(:tableau_stats, {:aborted, false})
      :ets.insert(:tableau_stats, {:branch_count, 1})

      timer = Process.send_after(self(), :timeout, params.timeout)

      BranchWorker.start_branch("root", formulas, defs, params)

      new_state = %__MODULE__{
        active_caller: from,
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
      cleanup_environment()
      {:noreply, %__MODULE__{}}
    else
      {:noreply, state}
    end
  end

  @impl true
  def handle_info(:timeout, state) do
    if state.active_caller do
      Logger.warning("Proof timed out!")
      GenServer.reply(state.active_caller, :timeout)
      cleanup_environment()
      {:noreply, %__MODULE__{}}
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
  def handle_info({:branch_status, branch_id, {:saturated, branch_defs}}, state) do
    new_active = MapSet.delete(state.active_branches, branch_id)
    new_idle = MapSet.delete(state.idle_branches, branch_id)
    new_sat = Map.put(state.saturated_branches, branch_id, branch_defs)

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
        Logger.debug("All workers finished. Asking Agent to flush mailbox and investigate CSA...")
        send(ShotMain.Prover.ContradictionAgent, {:verify_csa, state.saturated_branches})
        {:noreply, state}

      MapSet.size(state.active_branches) == 0 and MapSet.size(state.idle_branches) > 0 ->
        new_limit = state.current_gamma_limit + 1
        Logger.debug("All branches idle. Increasing Gamma Limit to #{new_limit}...")

        Registry.dispatch(ShotMain.Prover.PubSub, "branch_events", fn entries ->
          for {pid, _} <- entries, do: send(pid, {:wake_up, new_limit})
        end)

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

  defp cleanup_environment do
    :ets.insert(:tableau_stats, {:aborted, true})

    terminate_all_branches()

    :ets.delete_all_objects(:tableau_board)
    :ets.delete_all_objects(:tableau_lineage)

    send(ShotMain.Prover.ContradictionAgent, :reset_state)
  end

  defp terminate_all_branches do
    case DynamicSupervisor.which_children(ShotMain.Prover.BranchSupervisor) do
      [] ->
        :ok

      children ->
        Enum.each(children, fn {_, pid, _, _} ->
          # Process.exit(pid, :kill)
          DynamicSupervisor.terminate_child(ShotMain.Prover.BranchSupervisor, pid)
        end)

        Process.sleep(1)

        terminate_all_branches()
    end
  end
end
