defmodule ShotTx.Prover.Manager do
  @moduledoc """
  GenServer that orchestrates the proof search for a single session.

  On `start_proof`, arms the deadline, then builds the root branch in a
  supervised task and spawns `N` workers once it lands. Workers report back as
  idle when their queue empties; once all workers stall the Manager triggers
  iterative deepening by incrementing the gamma and prim-subst limits and waking
  the parked branches. The final proof result is returned synchronously to the
  caller of `start_proof`.

  The deadline is enforced against the wall clock at the head of every callback,
  not by the `:timeout` message alone — see `on_deadline/3`. Every step this
  process runs on a proof's behalf must therefore stay bounded, or it defers the
  deadline it is meant to enforce.
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
            deadline_us: nil,
            seeding: nil,
            current_gamma_limit: 1,
            current_prim_depth_limit: 1,
            worker_count: 0,
            idle_workers: MapSet.new(),
            saturated_branches: %{},
            exhausted_branches: MapSet.new(),
            parked_count: 0

  @root_name "root"

  # How many parked branches are woken between deadline checks during a
  # deepening round. Checking every branch would put a clock read on the hot
  # path; checking never is what let a round run for 70s past the deadline.
  @wake_check_interval 256

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

      # Armed before any proof work: arming it after the root branch was built
      # left that build outside the deadline entirely — 68s of it, on a
      # 279-formula TH1 problem given a 2s budget.
      schedule_progress_log(state.params.progress_interval_ms)
      timer = Process.send_after(self(), :timeout, state.params.timeout)

      {:noreply,
       %{
         state
         | active_caller: from,
           timer_ref: timer,
           deadline_us: System.monotonic_time(:microsecond) + state.params.timeout * 1000,
           seeding: seed_root_branch(state),
           current_gamma_limit: state.params.initial_gamma_limit,
           current_prim_depth_limit: state.params.initial_prim_limit,
           idle_workers: MapSet.new()
       }}
    end
  end

  # Lambda-lifts, ingests and indexes every input formula, which on a large
  # problem outlasts the whole proof budget. Run inline it would block this
  # process throughout, leaving the deadline unenforceable however early the
  # timer was armed.
  defp seed_root_branch(%__MODULE__{} = state) do
    %{formulas: formulas, params: params, defs: defs} = state

    Task.Supervisor.async_nolink(task_sup_via(state), fn ->
      {:root_branch, Branch.new(@root_name, formulas, params, defs: defs)}
    end)
  end

  defp task_sup_via(state),
    do: {:via, Registry, {ShotTx.Prover.ProcessRegistry, {state.session_id, :task_supervisor}}}

  # --- Deadline ---------------------------------------------------------------

  # `:timeout` is only as punctual as the mailbox in front of it: worker casts
  # fan into this one process, and a backlog that outgrows the drain rate defers
  # the deadline indefinitely. Reading the clock at the head of every callback
  # keeps the deadline enforceable whatever is queued; the timer remains the
  # ordinary trigger.
  @impl true
  def handle_info(message, state), do: on_deadline(&do_handle_info/2, message, state)

  @impl true
  def handle_cast(message, state), do: on_deadline(&do_handle_cast/2, message, state)

  defp on_deadline(handler, message, state) do
    if overdue?(state) do
      {:noreply, finish_with_timeout(state)}
    else
      handler.(message, state)
    end
  end

  defp overdue?(%__MODULE__{active_caller: nil}), do: false
  defp overdue?(%__MODULE__{deadline_us: nil}), do: false

  defp overdue?(%__MODULE__{deadline_us: deadline_us}),
    do: System.monotonic_time(:microsecond) >= deadline_us

  # --- Kill Switches & Results ------------------------------------------------

  defp do_handle_info(:timeout, %{active_caller: nil} = state), do: {:noreply, state}

  defp do_handle_info(:timeout, state), do: {:noreply, finish_with_timeout(state)}

  defp do_handle_info(:log_progress, %{active_caller: nil} = state), do: {:noreply, state}

  defp do_handle_info(:log_progress, state) do
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

  defp do_handle_info({ref, {:root_branch, root_branch}}, %{seeding: %Task{ref: ref}} = state) do
    Process.demonitor(ref, [:flush])

    priority_key = {byte_size(root_branch.id), root_branch.id}
    :ets.insert(state.ets_tables.work_queue, {priority_key, root_branch})

    # Workers start only now: one that finds an empty queue reports itself idle,
    # and an all-idle pool is what triggers a deepening round — starting them
    # before the root exists would deepen against nothing.
    spawn_workers(state)

    {:noreply, %{state | seeding: nil}}
  end

  defp do_handle_info({:DOWN, ref, :process, _pid, reason}, %{seeding: %Task{ref: ref}} = state) do
    {:noreply, finish_with_error(state, {:root_branch_failed, reason})}
  end

  defp do_handle_info(_, state) do
    {:noreply, state}
  end

  defp finish_with_timeout(state) do
    Logger.warning("Proof timed out!")

    # Park the workers first: everything below competes with them for schedulers
    # and lands on the caller as overshoot past its deadline.
    :ets.insert(state.ets_tables.stats, {:aborted, true})
    cancel_seeding(state.seeding)

    ShotTx.Prover.Stats.set(
      state.ets_tables,
      :proof_finished_at_us,
      System.monotonic_time(:microsecond)
    )

    stats = ShotTx.Prover.Stats.snapshot(state.ets_tables)

    log_timeout_traces(state)

    partial_proof = ShotTx.Proof.from_partial(gather_traces(state), state.formulas)

    GenServer.reply(state.active_caller, {{:timeout, partial_proof}, stats})
    %{state | active_caller: nil, seeding: nil}
  end

  # The root branch could not be built. There is no tableau to time out on, so
  # the caller gets an error rather than a partial proof.
  defp finish_with_error(%{active_caller: nil} = state, _reason), do: state

  defp finish_with_error(state, reason) do
    if state.timer_ref, do: Process.cancel_timer(state.timer_ref)
    :ets.insert(state.ets_tables.stats, {:aborted, true})

    stats = ShotTx.Prover.Stats.snapshot(state.ets_tables)
    GenServer.reply(state.active_caller, {{:error, reason}, stats})
    %{state | active_caller: nil, seeding: nil}
  end

  defp cancel_seeding(nil), do: :ok
  defp cancel_seeding(%Task{} = task), do: Task.shutdown(task, :brutal_kill)

  defp schedule_progress_log(interval) when is_integer(interval) and interval > 0 do
    Process.send_after(self(), :log_progress, interval)
  end

  defp schedule_progress_log(_), do: :ok

  defp resolve_worker_count(:auto), do: System.schedulers_online()
  defp resolve_worker_count(n) when is_integer(n) and n > 0, do: n

  # --- Worker Tracking & Deepening --------------------------------------------

  defp do_handle_cast({:worker_idle, worker_id}, state) do
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

  defp do_handle_cast({:branch_saturated, branch_id, data}, state) do
    new_sat = Map.put(state.saturated_branches, branch_id, data)
    {:noreply, %{state | saturated_branches: new_sat}}
  end

  defp do_handle_cast({:branch_exhausted, branch_id}, state) do
    {:noreply, %{state | exhausted_branches: MapSet.put(state.exhausted_branches, branch_id)}}
  end

  # The agent could neither close the tableau nor certify any saturated branch
  # as a countermodel. Forget the saturated set before re-deciding: it is never
  # emptied on its own, so leaving it in place sends `check_and_trigger_deepening/1`
  # straight back into the same dead end and deepening never resumes.
  defp do_handle_cast(:csa_undecided, state) do
    check_and_trigger_deepening(%{state | saturated_branches: %{}})
  end

  defp do_handle_cast({:proof_result, result}, state) do
    if state.active_caller do
      # Thunked: a `:unsat` result carries the whole trace store, so inspecting
      # it eagerly renders the entire proof on every successful search.
      Logger.info(fn -> "Manager received final result: #{inspect(result)}" end)
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

  defp do_handle_cast({:branch_parked, _branch_id}, state) do
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

  # Bounded by whatever is left of the proof's own deadline, never `:infinity`:
  # the agent replies only once its global-closure search finishes, and blocking
  # here would defer the manager's own `:timeout` (a 3s proof was observed
  # returning after 197s). Giving up is safe — `:open` is what the agent reports
  # when it finds no closure, and a late reply goes to a caller that has stopped
  # listening, which `GenServer.reply/2` tolerates.
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

  # Unbounded work in the process that must stay responsive to its own deadline.
  # Draining a key at a time, rather than snapshotting the table, bounds both the
  # heap this copies into and how far a deepening round runs past the deadline.
  # Branches left parked stay in the idle queue, where a timeout would have found
  # them anyway.
  defp transfer_idle_to_work_queue(state, ets_tables, cost_fn) do
    woken = drain_idle_queue(state, ets_tables, cost_fn, 0)
    %{state | parked_count: max(state.parked_count - woken, 0)}
  end

  defp drain_idle_queue(state, ets_tables, cost_fn, woken) do
    case :ets.first(ets_tables.idle_queue) do
      :"$end_of_table" ->
        woken

      id ->
        wake_parked(ets_tables, id, cost_fn)

        if rem(woken + 1, @wake_check_interval) == 0 and overdue?(state) do
          woken + 1
        else
          drain_idle_queue(state, ets_tables, cost_fn, woken + 1)
        end
    end
  end

  defp wake_parked(ets_tables, id, cost_fn) do
    case :ets.take(ets_tables.idle_queue, id) do
      [{^id, branch}] ->
        priority_key = {byte_size(id), id}
        :ets.insert(ets_tables.work_queue, {priority_key, Branch.wake_up(branch, cost_fn)})

      [] ->
        :ok
    end
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

  # Thunked on purpose: rendering walks every queued and parked branch, and an
  # interpolated string would be built here before Logger could discard it.
  defp log_timeout_traces(state) do
    Logger.debug(fn ->
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

      """
      Timeout trace — gamma_limit=#{state.current_gamma_limit} prim_limit=#{state.current_prim_depth_limit} idle_workers=#{MapSet.size(state.idle_workers)}/#{state.worker_count}
      work_queue (#{length(queued)} branch(es)):
      #{if queued == [], do: "  (empty)", else: queued_str}
      idle_queue (#{length(parked)} branch(es)):
      #{if parked == [], do: "  (empty)", else: parked_str}
      """
    end)
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
