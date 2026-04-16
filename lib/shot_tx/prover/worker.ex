defmodule ShotTx.Prover.Worker do
  @moduledoc """
  Long-lived worker process that steals branch data from an ETS queue,
  processes it using the pure Branch module, and applies resulting side effects.
  """
  use GenServer
  require Logger

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Branch

  defstruct id: nil,
            session_id: nil,
            ets_tables: %{},
            params: %Parameters{},
            current_gamma_limit: 1,
            current_prim_depth_limit: 1,
            current_branch: nil,
            steps_since_yield: 0

  @yield_limit 10

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  def start_link(opts) do
    GenServer.start_link(__MODULE__, opts)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init(opts) do
    session_id = Keyword.fetch!(opts, :session_id)

    Registry.register(ShotTx.Prover.PubSub, "branch_control_#{session_id}", [])

    state = %__MODULE__{
      id: Keyword.fetch!(opts, :worker_id),
      session_id: session_id,
      ets_tables: Keyword.fetch!(opts, :ets_tables),
      params: Keyword.fetch!(opts, :params),
      current_gamma_limit: Keyword.get(opts, :initial_gamma_limit, 1),
      current_prim_depth_limit: Keyword.get(opts, :initial_prim_limit, 1)
    }

    {:ok, state, {:continue, :process_next}}
  end

  # --- External Control Messages ---

  @impl true
  def handle_info({:wake_up, new_gamma, new_prim_depth}, state) do
    Logger.debug(
      "Worker #{state.id} waking up. Gamma: #{new_gamma}, Prim depth: #{new_prim_depth}"
    )

    new_state = %{
      state
      | current_gamma_limit: new_gamma,
        current_prim_depth_limit: new_prim_depth
    }

    {:noreply, new_state, {:continue, :process_next}}
  end

  @impl true
  def handle_info(_msg, state), do: {:noreply, state}

  # --- Main Execution Loop ---

  @impl true
  def handle_continue(:process_next, %{current_branch: nil} = state) do
    case checkout_work(state.ets_tables.work_queue) do
      {:ok, branch} ->
        if poisoned?(branch.id, state.ets_tables) do
          {:noreply, state, {:continue, :process_next}}
        else
          {:noreply, %{state | current_branch: branch}, {:continue, :process_next}}
        end

      :empty ->
        notify_manager(state, {:worker_idle, state.id})
        {:noreply, state}
    end
  end

  def handle_continue(:process_next, %{current_branch: branch, steps_since_yield: steps} = state) do
    cond do
      poisoned?(branch.id, state.ets_tables) ->
        {:noreply, %{state | current_branch: nil}, {:continue, :process_next}}

      steps >= @yield_limit ->
        push_work(state.ets_tables.work_queue, branch)

        {:noreply, %{state | current_branch: nil, steps_since_yield: 0},
         {:continue, :process_next}}

      true ->
        step_result =
          Branch.step(
            branch,
            state.params,
            state.current_gamma_limit,
            state.current_prim_depth_limit
          )

        handle_step_result(step_result, %{state | steps_since_yield: steps + 1})
    end
  end

  ##############################################################################
  # RESULT HANDLING & SIDE EFFECTS
  ##############################################################################

  defp handle_step_result({:continue, updated_branch, effect}, state) do
    apply_effect(effect, updated_branch, state)
    {:noreply, %{state | current_branch: updated_branch}, {:continue, :process_next}}
  end

  defp handle_step_result({:split, a, b}, state) do
    parent_id = state.current_branch.id

    broadcast_status(a.id, :active, state.session_id)
    broadcast_status(b.id, :active, state.session_id)
    broadcast_status(parent_id, :split, state.session_id)

    push_work(state.ets_tables.work_queue, a)
    push_work(state.ets_tables.work_queue, b)
    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:instantiate, branches}, state) do
    parent_id = state.current_branch.id

    Enum.each(branches, fn b ->
      broadcast_status(b.id, :active, state.session_id)
      push_work(state.ets_tables.work_queue, b)
    end)

    broadcast_status(parent_id, :split, state.session_id)
    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:closed, closed_branch}, state) do
    branch_id = closed_branch.id
    trace = Enum.reverse(closed_branch.history)

    Logger.debug(
      "Worker #{state.id} found local ground closure on #{branch_id}. Initiating tombstone."
    )

    :ets.insert(state.ets_tables.tombs, {branch_id, true})

    broadcast_status(branch_id, {:closed, trace}, state.session_id)
    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:idle, branch}, state) do
    :ets.insert(state.ets_tables.idle_queue, {branch.id, branch})
    {:noreply, %{state | current_branch: nil}, {:continue, :process_next}}
  end

  defp handle_step_result({:saturated, {defs, literals}}, state) do
    Logger.info(
      "Worker #{state.id} fully saturated branch #{state.current_branch.id}. Found a counter-model!"
    )

    notify_manager(state, {:branch_saturated, state.current_branch.id, {defs, literals}})
    {:noreply, %{state | current_branch: nil}, {:continue, :process_next}}
  end

  # --- Effect Application ---

  defp apply_effect({:notify_ca, clashes, trace}, branch, state) do
    ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
    GenServer.cast(ca_via, {:local_clashes, branch.id, clashes, trace})
  end

  defp apply_effect(:no_effects, _branch, _state), do: :ok

  ##############################################################################
  # Helpers (ETS Queues & Poisoning)
  ##############################################################################

  defp broadcast_status(branch_id, status, session_id) do
    Registry.dispatch(ShotTx.Prover.PubSub, "branch_events_#{session_id}", fn entries ->
      for {pid, _} <- entries, do: send(pid, {:branch_status, branch_id, status})
    end)
  end

  defp checkout_work(table) do
    case :ets.first(table) do
      :"$end_of_table" ->
        :empty

      key ->
        case :ets.take(table, key) do
          [{^key, branch}] -> {:ok, branch}
          [] -> checkout_work(table)
        end
    end
  end

  defp push_work(table, branch) do
    priority_key = {byte_size(branch.id), branch.id}
    :ets.insert(table, {priority_key, branch})
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

  defp notify_manager(state, message) do
    manager_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :manager}}}
    GenServer.cast(manager_via, message)
  end
end
