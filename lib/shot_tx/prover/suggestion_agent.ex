defmodule ShotTx.Prover.SuggestionAgent do
  @moduledoc """
  A *peer* of `ContradictionAgent`. Subscribes to the same raw evidence
  stream (`branch_evidence_<session>`) and runs strictly weaker unification
  than CA — pair-level only — turning σs into per-recipe instantiation
  hints spliced into descendant branches of the recipe's `birth_branch`.

  Gated behind `params.suggestions_enabled` (default `false`). When
  disabled, `init/1` returns immediately without subscribing to the topic
  and no message handling runs, so the prover's behaviour is unchanged.

  ## Pipeline

    * **Ingest.** `{:local_clashes, branch_id, MapSet<{a,b}>}` arrives
      from `branch_evidence_<session>` and accumulates in
      `clashing_local_pairs`.
    * **Search.** Each freshly-added pair is unified with
      `ShotUn.unify/2 |> Enum.take(1)`. Any multi-pair regime is CA's
      job by construction.
    * **Derive.** For every `X ↦ t` in the returned σ, `Provenance.fetch/2`
      recovers `(recipe, source, birth_branch, origin)`; suggestions
      whose composed term is not closed over `birth_branch` are dropped.
    * **Publish.** `publish_suggestions/2` writes rows into the
      `:suggestions` ETS table with `:ets.insert_new/2`. Keys are
      `{branch_prefix, recipe, term}`; the `applied_count` counter at
      tuple position 2 is incremented atomically at the splice site so
      the cascade cap (`suggestion_cascade_ceiling`, default `3`) is
      lock-free.
    * **Splice.** `Worker.splice_suggestions/2` walks ancestor prefixes
      of the checked-out branch, calls `:ets.update_counter/3` to reserve
      a slot, and injects the synthetic
      `{:suggested_instantiate, recipe, term}` rule via
      `Branch.splice_suggested_instantiate/5`. The rule has cost `2`,
      cheaper than γ (≥ 3) and prim-subst (≥ 20) but not free — atomic
      (1) still preempts closure detection.

  SA never declares closure. Pair-level search cannot witness a
  multi-branch closure by construction, so `:unsat` remains CA's
  responsibility.
  """

  use GenServer
  require Logger

  alias ShotDs.Data.Substitution
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.{EtsKeeper, Provenance, Suggestion}
  alias ShotUn.UnifSolution

  defstruct session_id: nil,
            ets_tables: %{},
            active_branches: MapSet.new(["root"]),
            clashing_local_pairs: %{},
            params: %Parameters{}

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  @doc "Starts the SuggestionAgent for the given session."
  @spec start_link({String.t(), Parameters.t()}) :: GenServer.on_start()
  def start_link({session_id, params}) do
    name = {:via, Registry, {ShotTx.Prover.ProcessRegistry, {session_id, :sa}}}
    GenServer.start_link(__MODULE__, {session_id, params}, name: name)
  end

  ##############################################################################
  # CALLBACKS
  ##############################################################################

  @impl true
  def init({session_id, %Parameters{suggestions_enabled: false} = params}) do
    # Passive mode: never subscribe, never process. Keep the state so a
    # future hot-reload could flip the flag without a restart, but the
    # message handlers all early-return.
    {:ok, %__MODULE__{session_id: session_id, params: params}}
  end

  @impl true
  def init({session_id, params}) do
    Registry.register(ShotTx.Prover.PubSub, "branch_evidence_#{session_id}", [])
    ets_tables = EtsKeeper.get_tables(session_id)

    {:ok,
     %__MODULE__{
       session_id: session_id,
       ets_tables: ets_tables,
       params: params
     }}
  end

  @impl true
  def handle_info(msg, %{params: %Parameters{suggestions_enabled: false}} = state) do
    _ = msg
    {:noreply, state}
  end

  @impl true
  def handle_info({:branch_split, parent_id, child_ids}, state) do
    new_active =
      state.active_branches
      |> MapSet.delete(parent_id)
      |> MapSet.union(MapSet.new(child_ids))

    {:noreply, %{state | active_branches: new_active}}
  end

  @impl true
  def handle_info({:branch_closed, branch_id}, state) do
    {:noreply, drop_branch(state, branch_id)}
  end

  @impl true
  def handle_info({:branch_saturated, branch_id, _model}, state) do
    {:noreply, drop_branch(state, branch_id)}
  end

  @impl true
  def handle_info({:local_clashes, branch_id, new_pairs}, state) do
    process_new_clashes(branch_id, new_pairs, state)

    updated =
      Map.update(
        state.clashing_local_pairs,
        branch_id,
        new_pairs,
        &MapSet.union(&1, new_pairs)
      )

    {:noreply, %{state | clashing_local_pairs: updated}}
  end

  @impl true
  def handle_info(_msg, state), do: {:noreply, state}

  ##############################################################################
  # PIPELINE
  ##############################################################################

  defp drop_branch(state, branch_id) do
    %{
      state
      | active_branches: MapSet.delete(state.active_branches, branch_id),
        clashing_local_pairs: Map.delete(state.clashing_local_pairs, branch_id)
    }
  end

  # Runs pair-level unification on every clash pair reported for `branch_id`
  # and publishes the derivable `{recipe, term}` suggestions into the
  # `:suggestions` ETS table, then dispatches `:work_available` so idle
  # workers pick them up. Scoring and TopK come later — Step 5.
  defp process_new_clashes(_branch_id, new_pairs, state) do
    depth = state.params.unification_depth

    Enum.each(new_pairs, fn {a, b} ->
      [{a, b}]
      |> ShotUn.unify(depth)
      |> Enum.take(1)
      |> case do
        [%UnifSolution{substitutions: substs}] -> publish_suggestions(substs, state)
        _ -> :ok
      end
    end)
  end

  defp publish_suggestions(substs, state) do
    prov_table = state.ets_tables.provenance
    sug_table = state.ets_tables.suggestions

    inserted? =
      Enum.reduce(substs, false, fn subst, acc ->
        case try_publish_one(subst, prov_table, sug_table) do
          :inserted -> true
          :skipped -> acc
        end
      end)

    if inserted?, do: broadcast_work_available(state.session_id)
    :ok
  end

  defp try_publish_one(%Substitution{fvar: fvar, term_id: term_id}, prov_table, sug_table) do
    var_id = TF.make_term(fvar)

    with %Provenance{recipe: recipe, birth_branch: birth, source: source} <-
           Provenance.fetch(prov_table, var_id),
         suggestion = build_suggestion(term_id, source),
         row = {{birth, recipe, term_id}, 0, suggestion},
         true <- :ets.insert_new(sug_table, row) do
      Logger.debug("SA published hint: recipe=#{recipe} ↦ term=#{term_id} (birth=#{birth})")
      :inserted
    else
      _ -> :skipped
    end
  end

  defp build_suggestion(term_id, source) do
    %Suggestion{
      term: term_id,
      source: source,
      score: 1,
      published_at_us: System.monotonic_time(:microsecond)
    }
  end

  defp broadcast_work_available(session_id) do
    Registry.dispatch(ShotTx.Prover.PubSub, "branch_control_#{session_id}", fn entries ->
      for {pid, _} <- entries, do: send(pid, :work_available)
    end)
  end
end
