defmodule ShotTx.Prover.Manager do
  use GenServer
  require Logger

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.BranchWorker

  defstruct session_id: nil,
            ets_tables: %{},
            formulas: [],
            defs: %{},
            params: %Parameters{},
            active_caller: nil,
            timer_ref: nil,
            current_gamma_limit: 1,
            current_prim_depth_limit: 1,
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

    ets_tables = %{
      board:
        :ets.new(:tableau_board, [:bag, :public, read_concurrency: true, write_concurrency: true]),
      stats: :ets.new(:tableau_stats, [:set, :public, write_concurrency: true]),
      tombs: :ets.new(:tableau_tombstones, [:set, :public, read_concurrency: true])
    }

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

      {:noreply,
       %{
         state
         | active_caller: from,
           timer_ref: timer,
           current_gamma_limit: state.params.initial_gamma_limit,
           current_prim_depth_limit: state.params.initial_prim_limit,
           active_branches: MapSet.new(["root"]),
           idle_branches: MapSet.new()
       }}
    end
  end

  ##### Kill Switches #####

  @impl true
  def handle_info({:proof_result, result}, state) do
    if state.active_caller do
      Logger.info("Manager received final result: #{inspect(result)}")
      if state.timer_ref, do: Process.cancel_timer(state.timer_ref)
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
      GenServer.reply(state.active_caller, :timeout)
      {:noreply, %{state | active_caller: nil}}
    else
      {:noreply, state}
    end
  end

  ##### Branch Tracking #####

  @impl true
  def handle_info({:branch_status, id, :active}, state) do
    {:noreply, track(state, add: id, to: :active)}
  end

  @impl true
  def handle_info({:branch_status, id, {:saturated, data}}, state) do
    new = track(state, remove: id)
    new = %{new | saturated_branches: Map.put(new.saturated_branches, id, data)}
    check_and_trigger_deepening(new)
  end

  @impl true
  def handle_info({:branch_status, id, :closed}, state) do
    check_and_trigger_deepening(track(state, remove: id))
  end

  @impl true
  def handle_info({:branch_status, id, :idle}, state) do
    check_and_trigger_deepening(track(state, add: id, to: :idle))
  end

  @impl true
  def handle_info({:branch_status, id, :split}, state) do
    check_and_trigger_deepening(track(state, remove: id))
  end

  @impl true
  def handle_info(_msg, state), do: {:noreply, state}

  ##############################################################################
  # HELPERS
  ##############################################################################

  # Moves a branch id between tracking sets.
  defp track(state, opts) do
    id = opts[:add] || opts[:remove]

    base = %{
      state
      | active_branches: MapSet.delete(state.active_branches, id),
        idle_branches: MapSet.delete(state.idle_branches, id),
        saturated_branches: Map.delete(state.saturated_branches, id)
    }

    case opts[:to] do
      :active -> %{base | active_branches: MapSet.put(base.active_branches, id)}
      :idle -> %{base | idle_branches: MapSet.put(base.idle_branches, id)}
      nil -> base
    end
  end

  defp check_and_trigger_deepening(state) do
    active = MapSet.size(state.active_branches)
    idle = MapSet.size(state.idle_branches)
    sat = map_size(state.saturated_branches)

    cond do
      is_nil(state.active_caller) ->
        {:noreply, state}

      active == 0 and idle == 0 and sat > 0 ->
        Logger.debug("All workers finished. Asking Agent to investigate CSA...")
        ca_cast(state, {:verify_csa, state.saturated_branches})
        {:noreply, state}

      active == 0 and idle == 0 and sat == 0 ->
        Logger.debug("All branches closed. Asking Agent to verify global unification...")
        ca_cast(state, :verify_all_closed)
        {:noreply, state}

      active == 0 and idle > 0 ->
        new_gamma = state.current_gamma_limit + 1
        new_prim = state.current_prim_depth_limit + 1

        Logger.debug("All branches idle. Gamma: #{new_gamma}, Prim depth: #{new_prim}")

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
             active_branches: state.idle_branches,
             idle_branches: MapSet.new()
         }}

      true ->
        {:noreply, state}
    end
  end

  defp ca_cast(state, msg) do
    ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
    GenServer.cast(ca_via, msg)
  end
end
