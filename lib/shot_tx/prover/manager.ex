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
            exhausted_branches: MapSet.new(),
            parked_count: 0

  @root_name "root"

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
    worker_count = resolve_worker_count(params.worker_pool_size)

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

      schedule_progress_log(state.params.progress_interval_ms)
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

    schedule_progress_log(state.params.progress_interval_ms)
    {:noreply, state}
  end

  @impl true
  def handle_info(_, state) do
    {:noreply, state}
  end

  defp schedule_progress_log(interval) when is_integer(interval) and interval > 0 do
    Process.send_after(self(), :log_progress, interval)
  end

  defp schedule_progress_log(_), do: :ok

  defp resolve_worker_count(:auto), do: System.schedulers_online()
  defp resolve_worker_count(n) when is_integer(n) and n > 0, do: n

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
  def handle_cast({:branch_exhausted, branch_id}, state) do
    {:noreply, %{state | exhausted_branches: MapSet.put(state.exhausted_branches, branch_id)}}
  end

  # The agent could neither close the tableau nor certify any saturated branch
  # as a countermodel. Forget the saturated set before re-deciding: it is never
  # emptied on its own, so leaving it in place sends `check_and_trigger_deepening/1`
  # straight back into the same dead end and deepening never resumes.
  @impl true
  def handle_cast(:csa_undecided, state) do
    check_and_trigger_deepening(%{state | saturated_branches: %{}})
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
      cond do
        map_size(state.saturated_branches) > 0 ->
          Logger.debug(
            "All workers idle. Saturated branches found. Asking Agent to investigate CSA..."
          )

          GenServer.cast(ca_via(state), {:verify_csa, state.saturated_branches})
          {:noreply, state}

        # Parked branches still have sleeping rules, so another deepening round
        # can still make progress. This is checked before the exhausted case:
        # an exhausted branch is a dead end for itself, not for the tableau.
        state.parked_count > 0 ->
          send_wake_up_if_open(state)

        MapSet.size(state.exhausted_branches) > 0 ->
          Logger.debug(
            "All workers idle, #{MapSet.size(state.exhausted_branches)} branch(es) exhausted " <>
              "without deciding satisfiability. Asking Agent for a final closure check..."
          )

          GenServer.cast(ca_via(state), :verify_exhausted)
          {:noreply, state}

        true ->
          Logger.debug(
            "All workers idle and queue exhausted. Asking Agent to verify global unification..."
          )

          GenServer.cast(ca_via(state), :verify_all_closed)
          {:noreply, state}
      end
    else
      {:noreply, state}
    end
  end

  defp send_wake_up_if_open(state) do
    case settle(state) do
      :closed ->
        {:noreply, state}

      :open ->
        deepen_or_report_unknown(state)
    end
  end

  # Settling is bounded by whatever is left of the proof's own deadline, never
  # `:infinity`. The agent answers this call only once its global-closure task
  # finishes, and that task is an exponential cartesian product over every open
  # branch's clash candidates — on a wide tableau it runs for minutes. While
  # the manager blocks here it cannot process its own `:timeout` message, so
  # the deadline it is supposed to enforce silently stops applying: a 3 s proof
  # was observed returning after 197 s.
  #
  # Giving up on the settle is safe. `:open` is what the agent reports when it
  # finds no closure, so treating a late answer as `:open` merely deepens or
  # falls through to the timeout — the timeout message is already queued and is
  # handled as soon as this returns. A reply that lands afterwards goes to a
  # caller that has stopped listening, which `GenServer.reply/2` tolerates.
  defp settle(state) do
    GenServer.call(ca_via(state), :settle, settle_budget(state))
  catch
    :exit, {:timeout, _call} ->
      Logger.warning("Settle exceeded the remaining proof budget; treating branches as open.")
      :open
  end

  defp settle_budget(%{timer_ref: ref}) when is_reference(ref) do
    case Process.read_timer(ref) do
      remaining when is_integer(remaining) and remaining > 0 -> remaining
      # Already fired or cancelled — the timeout is in the mailbox behind us.
      _ -> 1
    end
  end

  defp settle_budget(_state), do: :infinity

  defp deepen_or_report_unknown(%{params: %{iterative_deepening: false}} = state) do
    Logger.debug(
      "Iterative deepening disabled. Reporting :unknown at gamma=#{state.current_gamma_limit} prim=#{state.current_prim_depth_limit}."
    )

    GenServer.cast(self(), {:proof_result, {:unknown, :deepening_disabled}})
    {:noreply, state}
  end

  defp deepen_or_report_unknown(state) do
    new_state =
      transfer_idle_to_work_queue(state, state.ets_tables, state.params.formula_cost)

    new_gamma = state.current_gamma_limit + 1
    new_prim = state.current_prim_depth_limit + 1

    Logger.debug("Iterative deepening triggered. Gamma: #{new_gamma}, Prim depth: #{new_prim}")

    Registry.dispatch(
      ShotTx.Prover.PubSub,
      "branch_control_#{state.session_id}",
      fn entries ->
        for {pid, _} <- entries, do: send(pid, {:wake_up, new_gamma, new_prim})
      end
    )

    # A new round re-derives branches under the higher limits, so last round's
    # per-branch verdicts are stale: branch ids are positional, and `root_A` at
    # gamma+1 carries more formulas than the `root_A` that ran out of rules at
    # gamma. Carrying either set forward lets a dead end from an earlier round
    # answer for a branch that has not been explored yet.
    {:noreply,
     %{
       new_state
       | current_gamma_limit: new_gamma,
         current_prim_depth_limit: new_prim,
         idle_workers: MapSet.new(),
         saturated_branches: %{},
         exhausted_branches: MapSet.new()
     }}
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
