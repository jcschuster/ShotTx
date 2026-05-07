defmodule ShotTx.Prover.Worker do
  @moduledoc """
  Long-lived worker process that steals branch data from an ETS queue,
  processes it using the pure Branch module, and applies resulting side effects.
  """
  use GenServer
  require Logger

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Branch
  alias ShotTx.Prover.Stats

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

  @impl true
  def terminate(reason, state) when reason not in [:normal, :shutdown] do
    Logger.error(
      "Worker #{inspect(Map.get(state, :id))} terminating abnormally:\n" <>
        "  branch: #{inspect(Map.get(state, :current_branch) && state.current_branch.id)}\n" <>
        "  reason: #{inspect(reason, pretty: true, limit: :infinity)}"
    )

    :ok
  end

  def terminate(_reason, _state), do: :ok

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
  def handle_info(:work_available, %{current_branch: nil} = state) do
    {:noreply, state, {:continue, :process_next}}
  end

  @impl true
  def handle_info(:work_available, state), do: {:noreply, state}

  @impl true
  def handle_info(_msg, state), do: {:noreply, state}

  # --- Main Execution Loop ----------------------------------------------------

  defp aborted?(state) do
    case Map.get(state.ets_tables, :stats) do
      nil -> false
      t -> :ets.lookup(t, :aborted) == [{:aborted, true}]
    end
  end

  @impl true
  def handle_continue(:process_next, state) do
    if aborted?(state) do
      {:noreply, state}
    else
      do_process_next(state)
    end
  end

  defp do_process_next(%{current_branch: nil} = state) do
    case checkout_work(state.ets_tables.work_queue) do
      {:ok, branch} ->
        if poisoned?(branch.id, state.ets_tables) do
          {:noreply, state, {:continue, :process_next}}
        else
          {:noreply, %{state | current_branch: branch}, {:continue, :process_next}}
        end

      :empty ->
        notify_manager(state.session_id, {:worker_idle, state.id})
        {:noreply, state}
    end
  end

  defp do_process_next(%{current_branch: branch, steps_since_yield: steps} = state) do
    cond do
      poisoned?(branch.id, state.ets_tables) ->
        {:noreply, %{state | current_branch: nil}, {:continue, :process_next}}

      steps >= @yield_limit ->
        Stats.incr(state.ets_tables, :worker_yields)
        push_work(state.ets_tables.work_queue, branch, state.session_id)

        {:noreply, %{state | current_branch: nil, steps_since_yield: 0},
         {:continue, :process_next}}

      true ->
        try do
          step_result =
            Branch.step(
              branch,
              state.params,
              state.current_gamma_limit,
              state.current_prim_depth_limit
            )

          handle_step_result(step_result, %{state | steps_since_yield: steps + 1})
        rescue
          e ->
            Logger.error(
              "Worker #{state.id} crashed on branch #{branch.id}: #{Exception.format(:error, e, __STACKTRACE__)}"
            )

            reraise e, __STACKTRACE__
        end
    end
  end

  ##############################################################################
  # RESULT HANDLING & SIDE EFFECTS
  ##############################################################################

  defp handle_step_result({:continue, updated_branch, effect}, state) do
    Stats.incr(state.ets_tables, :steps_total)
    bump_rule(state.ets_tables, updated_branch)
    apply_effect(effect, updated_branch, state)
    {:noreply, %{state | current_branch: updated_branch}, {:continue, :process_next}}
  end

  defp handle_step_result({:split, a, b}, state) do
    Stats.incr(state.ets_tables, :steps_total)
    Stats.incr(state.ets_tables, :branches_split, 2)
    bump_rule(state.ets_tables, a)

    parent_id = state.current_branch.id

    notify_ca_sync(state.session_id, {:branch_active, a.id})
    notify_ca_sync(state.session_id, {:branch_active, b.id})
    notify_ca_sync(state.session_id, {:branch_split, parent_id})

    push_work(state.ets_tables.work_queue, a, state.session_id)
    push_work(state.ets_tables.work_queue, b, state.session_id)
    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:instantiate, branches}, state) do
    Stats.incr(state.ets_tables, :steps_total)
    Stats.incr(state.ets_tables, :branches_instantiate_children, length(branches))

    parent_id = state.current_branch.id

    Enum.each(branches, fn b ->
      notify_ca_sync(state.session_id, {:branch_active, b.id})
      push_work(state.ets_tables.work_queue, b, state.session_id)
    end)

    notify_ca_sync(state.session_id, {:branch_split, parent_id})
    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:closed, closed_branch}, state) do
    Stats.incr(state.ets_tables, :steps_total)
    Stats.incr(state.ets_tables, :branches_closed_locally)
    bump_rule(state.ets_tables, closed_branch)

    branch_id = closed_branch.id
    trace = Enum.reverse(closed_branch.history)

    Logger.debug(
      "Worker #{state.id} found local ground closure on #{branch_id}. Initiating tombstone."
    )

    :ets.insert(state.ets_tables.tombs, {branch_id, true})

    ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :ca}}}
    GenServer.call(ca_via, {:closed, branch_id, trace}, :infinity)

    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:idle, branch}, state) do
    :ets.insert(state.ets_tables.idle_queue, {branch.id, branch})
    notify_manager(state.session_id, {:branch_parked, branch.id})
    {:noreply, %{state | current_branch: nil}, {:continue, :process_next}}
  end

  defp handle_step_result({:saturated, {defs, literals}}, state) do
    Stats.incr(state.ets_tables, :branches_saturated)

    trace = Enum.reverse(state.current_branch.history)

    Logger.info(
      "Worker #{state.id} fully saturated branch #{state.current_branch.id}. Found a counter-model!"
    )

    msg = {:branch_saturated, state.current_branch.id, {defs, literals, trace}}

    notify_manager(state.session_id, msg)
    notify_ca_sync(state.session_id, msg)
    {:noreply, %{state | current_branch: nil}, {:continue, :process_next}}
  end

  # --- Effect Application ---

  defp apply_effect({:notify_ca, clashes, trace}, branch, state) do
    notify_ca_sync(state.session_id, {:local_clashes_sync, branch.id, clashes, trace})
  end

  defp apply_effect(:no_effects, _branch, _state), do: :ok

  ##############################################################################
  # Helpers (ETS Queues & Poisoning)
  ##############################################################################

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

  defp push_work(table, branch, session_id) do
    priority_key = {byte_size(branch.id), branch.id}
    :ets.insert(table, {priority_key, branch})

    Registry.dispatch(ShotTx.Prover.PubSub, "branch_control_#{session_id}", fn entries ->
      for {pid, _} <- entries, do: send(pid, :work_available)
    end)
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

  defp notify_manager(session_id, message) do
    manager_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :manager}}}
    GenServer.cast(manager_via, message)
  end

  defp notify_ca_sync(session_id, message) do
    ca_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :ca}}}
    GenServer.call(ca_via, message, :infinity)
  end

  defp bump_rule(tables, %{history: [{_src, rule, _} | _]}) do
    Stats.incr(tables, rule_key(rule))
  end

  defp bump_rule(_tables, _branch), do: :ok

  defp rule_key(:contradiction), do: :rule_contradiction
  defp rule_key(:tautology), do: :rule_tautology
  defp rule_key({:alpha, _}), do: :rule_alpha
  defp rule_key({:beta, _}), do: :rule_beta
  defp rule_key({:delta, _}), do: :rule_delta
  defp rule_key({:rename, _}), do: :rule_rename
  defp rule_key({:atomic, _}), do: :rule_atomic
  defp rule_key({:gamma, _, _, _}), do: :rule_gamma
  defp rule_key({:prim_subst, _, _, _, _}), do: :rule_prim_subst
  defp rule_key({:instantiate, _, _}), do: :rule_instantiate
  defp rule_key(_), do: :rule_other
end
