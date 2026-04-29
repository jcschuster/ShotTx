defmodule ShotTx.Proof do
  @moduledoc """
  A tableau derivation reconstructed from the closed-branch traces returned
  by the prover.

  The proof is a tree of `Step` nodes. Each step carries a unique integer
  `label` — the line number you would write in a textbook derivation —
  and a `sources` field listing the labels of the steps it was derived
  from. Branching rules (β, `instantiate`) produce **multiple sibling
  steps** that all cite the same source; they are not represented as a
  separate node above their alternatives.

  ## Step kinds

    * `:given`   — an initial formula (an assumption or the negated
                   conclusion). No rule, no sources.
    * `:rule`    — a formula derived by applying a rule to one earlier
                   step. `sources` is the singleton list of that premise's
                   label, `rule` the symbol of the applied rule
                   (`:alpha`, `:beta`, `:gamma`, …).
    * `:closure` — the ⊥ leaf that closes a branch. `sources` cites the
                   contradictory pair (or the `false` / `¬true` literal
                   for trivial closures).

  ## Construction

  `from_refutation/4` linearises each closed branch's trace into a flat
  list of "events" — one event per produced formula — and groups branches
  whose first events agree under a single `Step`, recursing into the
  divergent tails. Branches share `Step`s as long as they share prefixes;
  the moment they pop different rules from their queues, two sibling
  `Step`s emit and the tree forks. This is why a β-step ends up with two
  siblings (one per disjunct) and pure-trunk α/γ chains stay linear.

  Branch ids encode the path through every β/`instantiate` split as
  `_A` / `_B` / `_I{idx}` segments; the linearisation consumes one
  segment per branching event to pick the correct side.

  Renders to Mermaid via `to_mermaid/1` and to a plain-text tableau
  layout via `to_text/1`.
  """

  alias ShotDs.Data.Term
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.Dsl, only: [neg: 1]
  import ShotDs.Util.Formatter
  use ShotDs.Hol.Patterns

  defmodule Step do
    @moduledoc false
    defstruct label: nil,
              formula: nil,
              rule: nil,
              sources: [],
              kind: :rule,
              children: []

    @type kind :: :given | :rule | :closure

    @type t :: %__MODULE__{
            label: pos_integer(),
            formula: Term.term_id() | nil,
            rule: atom() | nil,
            sources: [pos_integer()],
            kind: kind(),
            children: [t()]
          }
  end

  @type t :: %__MODULE__{
          root: Step.t() | nil,
          substitution: map(),
          flex_pairs: list()
        }

  defstruct root: nil, substitution: %{}, flex_pairs: []

  ##############################################################################
  # CONSTRUCTION
  ##############################################################################

  @doc """
  Build a `Proof` from the per-branch traces returned by the prover.

    * `branch_traces`    — `%{branch_id => trace}`, oldest entry first per trace.
      Each trace entry is `{source, classified_rule, [produced]}`.
    * `initial_formulas` — the seeds of the root branch (assumptions plus
      the negated conclusion); they become the `:given` steps.
    * `substitution`, `flex_pairs` — refutation metadata, threaded through
      for use by callers that want to display the global witness.
  """
  @spec from_refutation(map(), [Term.term_id()], map(), list()) :: t()
  def from_refutation(branch_traces, initial_formulas, substitution, flex_pairs) do
    {given_steps, t2l, next_label} = build_givens(initial_formulas)

    branches_events =
      branch_traces
      |> Enum.map(fn {branch_id, trace} -> linearize(trace, branch_id) end)
      |> Enum.reject(&Enum.empty?/1)

    {derivation_children, _final} = build_subtree(branches_events, t2l, next_label)

    root = chain_steps(given_steps, derivation_children)

    %__MODULE__{root: root, substitution: substitution, flex_pairs: flex_pairs}
  end

  ##############################################################################
  # GIVEN STEPS
  ##############################################################################

  defp build_givens(formulas) do
    {steps_rev, t2l, next} =
      Enum.reduce(formulas, {[], %{}, 1}, fn formula, {steps, t2l, label} ->
        step = %Step{
          label: label,
          formula: formula,
          rule: nil,
          sources: [],
          kind: :given,
          children: []
        }

        {[step | steps], Map.put_new(t2l, formula, label), label + 1}
      end)

    {Enum.reverse(steps_rev), t2l, next}
  end

  defp chain_steps([], _children), do: nil

  defp chain_steps(givens, derivation_children) do
    [last | rest_rev] = Enum.reverse(givens)
    last_with_children = %{last | children: derivation_children}

    Enum.reduce(rest_rev, last_with_children, fn step, child ->
      %{step | children: [child]}
    end)
  end

  ##############################################################################
  # LINEARIZING INTO EVENTS
  ##############################################################################

  defp linearize([], _branch_id), do: []

  defp linearize(trace, branch_id) do
    segments = branch_id |> String.split("_") |> Enum.drop(1)

    {interior_entries, [last_entry]} = Enum.split(trace, length(trace) - 1)

    {events_rev, _segs} =
      Enum.reduce(interior_entries, {[], segments}, &interior_event/2)

    case closure_event(last_entry) do
      nil -> Enum.reverse(events_rev)
      ev -> Enum.reverse([ev | events_rev])
    end
  end

  defp interior_event({_src, :tautology, _}, state), do: state
  defp interior_event({_src, :contradiction, _}, state), do: state

  defp interior_event({src, {:alpha, _}, produced}, {evs, segs}) do
    {fold_rule_events(:alpha, src, produced, evs), segs}
  end

  defp interior_event({src, {:delta, _}, [sk]}, {evs, segs}) do
    {[{:rule, src, :delta, sk} | evs], segs}
  end

  defp interior_event({src, {:rename, _}, produced}, {evs, segs}) do
    {fold_rule_events(:rename, src, produced, evs), segs}
  end

  defp interior_event({src, {:beta, {b1, _b2}}, _produced}, {evs, ["A" | rest]}) do
    {[{:branch, src, :beta, b1} | evs], rest}
  end

  defp interior_event({src, {:beta, {_b1, b2}}, _produced}, {evs, ["B" | rest]}) do
    {[{:branch, src, :beta, b2} | evs], rest}
  end

  defp interior_event({_src, {:instantiate, _, 0}, _}, state), do: state

  defp interior_event(
         {src, {:instantiate, _, _}, produced},
         {evs, ["I" <> idx_str | rest]}
       ) do
    chosen = Enum.at(produced, String.to_integer(idx_str))
    {[{:branch, src, :instantiate, chosen} | evs], rest}
  end

  defp interior_event({src, {:gamma, _, _, _}, [inst]}, {evs, segs}) do
    {[{:rule, src, :gamma, inst} | evs], segs}
  end

  defp interior_event({_src, {:gamma, _, _, _}, []}, state), do: state

  defp interior_event({src, {:gamma_finite, _, _}, [_ | _] = instances}, {evs, segs}) do
    {fold_rule_events(:gamma_finite, src, instances, evs), segs}
  end

  defp interior_event({_src, {:gamma_finite, _, _}, []}, state), do: state

  defp interior_event({src, {:prim_subst, _, _, _, _}, [_ | _] = instances}, {evs, segs}) do
    {fold_rule_events(:prim_subst, src, instances, evs), segs}
  end

  defp interior_event({_src, {:prim_subst, _, _, _, _}, []}, state), do: state

  defp interior_event({src, {:atomic, _}, [unfolded]}, {evs, segs}) do
    {[{:rule, src, :unfold, unfolded} | evs], segs}
  end

  defp interior_event({_src, {:atomic, _}, []}, state), do: state

  defp interior_event(_unhandled, state), do: state

  defp fold_rule_events(rule_atom, src, produced, evs) do
    Enum.reduce(produced, evs, fn p, acc -> [{:rule, src, rule_atom, p} | acc] end)
  end

  defp closure_event({src, :contradiction, _}), do: {:closure, src, :contradiction}
  defp closure_event({src, {:atomic, _}, []}), do: {:closure, src, :atomic}
  defp closure_event(_), do: nil

  ##############################################################################
  # TREE BUILDING
  ##############################################################################

  defp build_subtree(branches_events, t2l, counter) do
    case Enum.reject(branches_events, &Enum.empty?/1) do
      [] ->
        {[], counter}

      live ->
        groups = live |> Enum.group_by(&hd/1, &tl/1) |> Enum.to_list()

        {steps_rev, final_counter} =
          Enum.reduce(groups, {[], counter}, fn {first_event, tails}, {acc, c} ->
            {step, c2} = make_step(first_event, tails, t2l, c)
            {[step | acc], c2}
          end)

        {Enum.reverse(steps_rev), final_counter}
    end
  end

  defp make_step({:rule, src, rule_atom, formula}, tails, t2l, counter) do
    build_formula_step(src, rule_atom, formula, tails, t2l, counter)
  end

  defp make_step({:branch, src, rule_atom, formula}, tails, t2l, counter) do
    build_formula_step(src, rule_atom, formula, tails, t2l, counter)
  end

  defp make_step({:closure, src, rule_atom}, _tails, t2l, counter) do
    step = %Step{
      label: counter,
      formula: nil,
      rule: rule_atom,
      sources: closure_sources(rule_atom, src, t2l),
      kind: :closure,
      children: []
    }

    {step, counter + 1}
  end

  defp build_formula_step(src, rule_atom, formula, tails, t2l, counter) do
    label = counter
    src_label = lookup_label(t2l, src)
    t2l_with_self = Map.put_new(t2l, formula, label)
    {children, next_counter} = build_subtree(tails, t2l_with_self, label + 1)

    step = %Step{
      label: label,
      formula: formula,
      rule: rule_atom,
      sources: List.wrap(src_label),
      kind: :rule,
      children: children
    }

    {step, next_counter}
  end

  defp lookup_label(t2l, src), do: Map.get(t2l, src)

  defp closure_sources(:atomic, src, t2l) do
    [Map.get(t2l, src), Map.get(t2l, lit_neg(src))]
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq()
  end

  defp closure_sources(:contradiction, src, t2l) do
    case Map.get(t2l, src) do
      nil -> []
      label -> [label]
    end
  end

  defp lit_neg(term_id) do
    case TF.get_term!(term_id) do
      negated(inner) -> inner
      _ -> neg(term_id)
    end
  end

  ##############################################################################
  # MERMAID RENDERING
  ##############################################################################

  @doc """
  Render the proof tree as a Mermaid `graph TD` diagram.

  Branch points (β / `instantiate`) emit solid arrows; linear derivations
  emit dotted arrows. Each rule node carries its label, the derived formula
  and a justification footer naming the rule symbol and the cited line(s).
  """
  @spec to_mermaid(t()) :: String.t()
  def to_mermaid(%__MODULE__{root: nil}), do: ""

  def to_mermaid(%__MODULE__{root: root, substitution: sub, flex_pairs: flex}) do
    {nodes, edges, _} = collect(root, 0)

    header = """
    %%{init: {'theme': 'base', 'themeVariables': { 'lineColor': '#999999', 'edgeLabelBackground': '#ffffff', 'fontFamily': 'sans-serif'}}}%%
    graph TD;
      classDef given fill:#e3f2fd,stroke:#1565c0,stroke-width:2px,color:#0d47a1,rx:8px,ry:8px;
      classDef rule fill:#eeeeee,stroke:#999999,stroke-width:2px,color:#333333,rx:8px,ry:8px;
      classDef closure fill:#fff3e0,stroke:#cc5500,stroke-width:2px,color:#000000,rx:8px,ry:8px;
      classDef subst fill:#f9fbe7,stroke:#827717,stroke-width:2px,color:#000000,rx:8px,ry:8px,stroke-dasharray: 5 5;
    """

    node_lines =
      Enum.map_join(nodes, "\n", fn {id, label, class} ->
        "  N#{id}[\"#{escape(label)}\"]:::#{class};"
      end)

    edge_lines =
      Enum.map_join(edges, "\n", fn
        {from, to, :branch} -> "  N#{from} ==> N#{to};"
        {from, to, :linear} -> "  N#{from} -.-> N#{to};"
      end)

    subst_node =
      if map_size(sub) > 0 do
        mappings = Enum.map_join(sub, "<br/>", fn {k, v} -> "● #{format!(v)} / #{format!(k)}" end)
        "\n  Sub[\"<b>Global Substitution:</b><br/>#{escape(mappings)}\"]:::subst;"
      else
        ""
      end

    flex_node =
      if not Enum.empty?(flex) do
        constrs =
          Enum.map_join(flex, "<br/>", fn {t1, t2} -> "● #{format!(t1)} = #{format!(t2)}" end)

        "\n Constraints[\"<b>Global Flex-Flex Constraints:</b><br/>#{escape(constrs)}\"]"
      else
        ""
      end

    header <> node_lines <> "\n" <> edge_lines <> subst_node <> flex_node <> "\n"
  end

  defp collect(%Step{} = step, counter) do
    my_id = counter
    self_entry = {my_id, mermaid_label(step), node_class(step)}
    edge_kind = if length(step.children) > 1, do: :branch, else: :linear

    {child_nodes, child_edges, next_counter} =
      Enum.reduce(step.children, {[], [], counter + 1}, fn child, {ns, es, c} ->
        {cn, ce, c2} = collect(child, c)
        edge = {my_id, c, edge_kind}
        {ns ++ cn, es ++ [edge | ce], c2}
      end)

    {[self_entry | child_nodes], child_edges, next_counter}
  end

  defp mermaid_label(%Step{kind: :given, label: l, formula: f}) do
    "(#{l})  #{format!(f)}"
  end

  defp mermaid_label(%Step{kind: :rule, label: l, formula: f, rule: r, sources: srcs}) do
    "(#{l})  #{format!(f)}<br/><small>(#{rule_symbol(r)} on #{Enum.join(srcs, ", ")})</small>"
  end

  defp mermaid_label(%Step{kind: :closure, sources: []}), do: "⊥"

  defp mermaid_label(%Step{kind: :closure, sources: srcs}) do
    "⊥<br/><small>(#{Enum.join(srcs, ", ")})</small>"
  end

  defp node_class(%Step{kind: :given}), do: "given"
  defp node_class(%Step{kind: :rule}), do: "rule"
  defp node_class(%Step{kind: :closure}), do: "closure"

  ##############################################################################
  # PLAIN-TEXT RENDERING
  ##############################################################################

  @doc """
  Render the proof tree as a plain-text tableau derivation.

  Linear chains print one step per line at the current indentation level.
  At a branch point the children expand under tree connectors `├──` and
  `└──`; descendant lines carry `│   ` continuation markers as long as
  there are siblings still to be rendered.

  Example output:

      1. (p ∨ q)            [given]
      2. ¬p                 [given]
      3. ¬q                 [given]
      ├── 4. p              [β on 1]
      │   5. ⊥              [2, 4]
      └── 6. q              [β on 1]
          7. ⊥              [3, 6]
  """
  @spec to_text(t()) :: String.t()
  def to_text(%__MODULE__{root: nil}), do: "(no proof)\n"

  def to_text(%__MODULE__{root: root, substitution: sub}) do
    proof_text =
      root
      |> render_root("")
      |> IO.iodata_to_binary()

    subst_text = format_subst(sub)
    proof_text <> "\n" <> subst_text
  end

  defp format_subst(sub) when map_size(sub) == 0, do: ""

  defp format_subst(sub) do
    mappings = Enum.map_join(sub, ", ", fn {k, v} -> "#{format!(v)} / #{format!(k)}" end)
    "Global Substitution: { #{mappings} }\n"
  end

  defp render_root(%Step{} = step, prefix) do
    line = [prefix, text_label(step), "\n"]

    case step.children do
      [] ->
        line

      [only] ->
        [line, render_root(only, prefix)]

      many ->
        [line, render_branch(many, prefix)]
    end
  end

  defp render_with_connector(%Step{} = step, lead, connector, descendants_prefix) do
    line = [lead, connector, text_label(step), "\n"]

    case step.children do
      [] ->
        line

      [only] ->
        [line, render_root(only, descendants_prefix)]

      many ->
        [line, render_branch(many, descendants_prefix)]
    end
  end

  # Render a list of sibling steps with tree connectors.
  defp render_branch(siblings, prefix) do
    n = length(siblings)

    siblings
    |> Enum.with_index()
    |> Enum.map(fn {child, idx} ->
      is_last = idx == n - 1
      connector = if is_last, do: "└── ", else: "├── "
      continuation = if is_last, do: "    ", else: "│   "
      render_with_connector(child, prefix, connector, prefix <> continuation)
    end)
  end

  # ---- Per-step formatting --------------------------------------------------

  defp text_label(%Step{kind: :given, label: l, formula: f}) do
    pad("#{l}. #{format!(f)}") <> "[given]"
  end

  defp text_label(%Step{kind: :rule, label: l, formula: f, rule: r, sources: []}) do
    pad("#{l}. #{format!(f)}") <> "[#{rule_symbol(r)}]"
  end

  defp text_label(%Step{kind: :rule, label: l, formula: f, rule: r, sources: srcs}) do
    pad("#{l}. #{format!(f)}") <> "[#{rule_symbol(r)} on #{Enum.join(srcs, ", ")}]"
  end

  defp text_label(%Step{kind: :closure, label: l, sources: []}) do
    pad("#{l}. ⊥") <> "[⊥]"
  end

  defp text_label(%Step{kind: :closure, label: l, sources: srcs}) do
    pad("#{l}. ⊥") <> "[#{Enum.join(srcs, ", ")}]"
  end

  @label_column_width 36
  defp pad(text) do
    text = to_string(text)
    needed = @label_column_width - String.length(text)
    if needed > 0, do: text <> String.duplicate(" ", needed), else: text <> " "
  end

  ##############################################################################
  # SHARED RULE SYMBOL TABLE
  ##############################################################################

  defp rule_symbol(:alpha), do: "α"
  defp rule_symbol(:beta), do: "β"
  defp rule_symbol(:gamma), do: "γ"
  defp rule_symbol(:gamma_finite), do: "γ_fin"
  defp rule_symbol(:delta), do: "δ"
  defp rule_symbol(:prim_subst), do: "π"
  defp rule_symbol(:rename), do: "ren"
  defp rule_symbol(:instantiate), do: "inst"
  defp rule_symbol(:unfold), do: "unfold"
  defp rule_symbol(:atomic), do: "atomic"
  defp rule_symbol(:contradiction), do: "⊥"
  defp rule_symbol(other), do: to_string(other)

  defp escape(text) do
    text
    |> to_string()
    |> String.replace("\"", "\\\"")
  end
end
