defmodule ShotTx.Prover.Worker do
  @moduledoc """
  Long-lived worker process that steals branch data from an ETS queue,
  processes it using the pure Branch module, and applies resulting side effects.
  """
  use GenServer
  require Logger

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.Branch
  alias ShotTx.Prover.Provenance
  alias ShotTx.Prover.Stats
  alias ShotTx.Prover.Suggestion

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

  @doc """
  Starts a worker process.

  `opts` must contain `:session_id` and `:worker_id`. Additional keys are
  written straight into the `%__MODULE__{}` state; see `init/1` and the
  struct default values above for the accepted fields.
  """
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
          spliced = splice_suggestions(branch, state)
          {:noreply, %{state | current_branch: spliced}, {:continue, :process_next}}
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
        spliced = splice_suggestions(branch, state)
        push_work(state.ets_tables.work_queue, spliced, state.session_id)

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
    :ets.delete(state.ets_tables.traces, parent_id)
    publish_trace(state.ets_tables, a)
    publish_trace(state.ets_tables, b)

    broadcast_evidence(state.session_id, {:branch_split, parent_id, [a.id, b.id]})

    push_work(state.ets_tables.work_queue, a, state.session_id)
    push_work(state.ets_tables.work_queue, b, state.session_id)
    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:instantiate, branches}, state) do
    Stats.incr(state.ets_tables, :steps_total)
    Stats.incr(state.ets_tables, :branches_instantiate_children, length(branches))

    parent_id = state.current_branch.id
    :ets.delete(state.ets_tables.traces, parent_id)
    Enum.each(branches, &publish_trace(state.ets_tables, &1))
    child_ids = Enum.map(branches, & &1.id)

    broadcast_evidence(state.session_id, {:branch_split, parent_id, child_ids})

    Enum.each(branches, fn b -> push_work(state.ets_tables.work_queue, b, state.session_id) end)
    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:closed, closed_branch}, state) do
    Stats.incr(state.ets_tables, :steps_total)
    Stats.incr(state.ets_tables, :branches_closed_locally)
    bump_rule(state.ets_tables, closed_branch)

    branch_id = closed_branch.id
    publish_trace(state.ets_tables, closed_branch)

    Logger.debug(
      "Worker #{state.id} found local ground closure on #{branch_id}. Initiating tombstone."
    )

    :ets.insert(state.ets_tables.tombs, {branch_id, true})

    broadcast_evidence(state.session_id, {:branch_closed, branch_id})

    {:noreply, %{state | current_branch: nil, steps_since_yield: 0}, {:continue, :process_next}}
  end

  defp handle_step_result({:idle, branch}, state) do
    publish_trace(state.ets_tables, branch)
    :ets.insert(state.ets_tables.idle_queue, {branch.id, branch})
    notify_manager(state.session_id, {:branch_parked, branch.id})
    {:noreply, %{state | current_branch: nil}, {:continue, :process_next}}
  end

  defp handle_step_result({:saturated, {defs, literals}}, state) do
    Stats.incr(state.ets_tables, :branches_saturated)

    publish_trace(state.ets_tables, state.current_branch)

    Logger.info(
      "Worker #{state.id} fully saturated branch #{state.current_branch.id}. Found a counter-model!"
    )

    msg = {:branch_saturated, state.current_branch.id, {defs, literals}}

    notify_manager(state.session_id, msg)
    broadcast_evidence(state.session_id, msg)
    {:noreply, %{state | current_branch: nil}, {:continue, :process_next}}
  end

  # --- Effect Application ---

  defp apply_effect({:notify_ca, clashes}, branch, state) do
    publish_trace(state.ets_tables, branch)
    broadcast_evidence(state.session_id, {:local_clashes, branch.id, clashes})
  end

  defp apply_effect({:record_provenance, records}, _branch, state) do
    table = state.ets_tables.provenance

    Enum.each(records, fn {var_id, prov} ->
      Provenance.record(table, var_id, prov)
    end)
  end

  defp apply_effect(:no_effects, _branch, _state), do: :ok

  defp publish_trace(ets_tables, branch) do
    base = Enum.reverse(branch.history)

    trace =
      cond do
        ends_in_hard_closure?(base) -> base
        is_nil(branch.last_clash) -> base
        true -> base ++ [clash_marker(branch.last_clash)]
      end

    :ets.insert(ets_tables.traces, {branch.id, trace})
  end

  defp ends_in_hard_closure?([]), do: false

  defp ends_in_hard_closure?(base) do
    case List.last(base) do
      {_, :contradiction, _} -> true
      _ -> false
    end
  end

  defp clash_marker({:ground, term_id, matchings}),
    do: {nil, {:close_pair, term_id, matchings}, []}

  defp clash_marker({:unification, term_id, matchings}),
    do: {nil, {:clash_candidates, term_id, matchings}, []}

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
    branch_id
    |> ancestor_prefixes()
    |> then(fn prefixes ->
      try do
        Enum.any?(prefixes, &:ets.member(ets_tables.tombs, &1))
      rescue
        ArgumentError -> true
      end
    end)
  end

  defp ancestor_prefixes(branch_id) do
    segments = String.split(branch_id, "_")
    Enum.scan(segments, fn seg, acc -> acc <> "_" <> seg end)
  end

  # Reads suggestions inherited from `branch.id`'s ancestor prefixes and
  # splices each as a synthetic `:suggested_instantiate` rule. The
  # `:ets.update_counter/3` guard enforces the cascade cap atomically —
  # the racing worker that sees `applied_count > ceiling` skips the splice.
  defp splice_suggestions(branch, %{params: %Parameters{suggestions_enabled: false}} = _state),
    do: branch

  defp splice_suggestions(branch, state) do
    sug_table = state.ets_tables.suggestions
    ceiling = state.params.suggestion_cascade_ceiling

    branch.id
    |> ancestor_prefixes()
    |> Enum.flat_map(&:ets.match_object(sug_table, {{&1, :_, :_}, :_, :_}))
    |> Enum.reduce(branch, fn {{_, recipe, _} = key, _count, %Suggestion{} = suggestion}, b ->
      case :ets.update_counter(sug_table, key, {2, 1}) do
        n when n > ceiling ->
          b

        _ ->
          Stats.incr(state.ets_tables, :suggestions_spliced)

          Branch.splice_suggested_instantiate(
            b,
            recipe,
            suggestion.term,
            suggestion.source,
            state.params
          )
      end
    end)
  end

  defp notify_manager(session_id, message) do
    manager_via = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :manager}}}
    GenServer.cast(manager_via, message)
  end

  # Every branch-lifecycle event is delivered as an asynchronous fanout on
  # `branch_evidence_<session>`. Both CA and SA subscribe; neither knows
  # about the other. Cross-sender ordering is handled by CA's defensive
  # split/closed logic — see the "Out-of-order tolerance" note on
  # `ContradictionAgent`.
  defp broadcast_evidence(session_id, msg) do
    Registry.dispatch(ShotTx.Prover.PubSub, "branch_evidence_#{session_id}", fn entries ->
      for {pid, _} <- entries, do: send(pid, msg)
    end)
  end

  defp bump_rule(tables, %{history: [{_src, {:gamma, _, _, prev, _} = rule, _} | _]}) do
    Stats.incr(tables, rule_key(rule))
    Stats.incr(tables, :"rule_gamma_c#{prev}")
    Stats.record_max(tables, :rule_gamma_max_c, prev)
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
  defp rule_key({:gamma, _, _, _, _}), do: :rule_gamma
  defp rule_key({:prim_subst, _, _, _, _}), do: :rule_prim_subst
  defp rule_key({:instantiate, _, _}), do: :rule_instantiate
  defp rule_key({:suggested_instantiate, _, _}), do: :rule_suggested_instantiate
  defp rule_key({:equality_expansion, _, _}), do: :rule_equality_expansion
  defp rule_key(_), do: :rule_other
end
