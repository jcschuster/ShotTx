defmodule ShotTx.Proof do
  @moduledoc """
  A structured proof object reconstructed from closed branch traces. Each
  source formula that was processed in any trace becomes a node; the formulas
  spawned by that source's rule become its children. Produced formulas that
  were never processed themselves (e.g. siblings of a formula that closed the
  branch first) appear as leaves.

  It behaves as an And-Or tree where beta branches are :and nodes, and linear
  branch progressions (alpha rules) are :or nodes.

  Renders to Mermaid via `to_rich_mermaid/1`.
  """

  alias ShotDs.Data.Term
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Util.Formatter
  use ShotDs.Hol.Patterns

  defmodule Node do
    @moduledoc false
    defstruct formula: nil, rule: nil, node_type: :or, children: [], closed: false

    @type t :: %__MODULE__{
            formula: Term.term_id() | nil,
            rule: any(),
            node_type: :and | :or,
            children: [t()],
            closed: boolean()
          }
  end

  @type t :: %__MODULE__{
          tree: Node.t() | nil,
          substitution: map(),
          flex_pairs: list()
        }

  defstruct tree: nil, substitution: %{}, flex_pairs: []

  ##############################################################################
  # CONSTRUCTION
  ##############################################################################

  @doc """
  Build a `Proof` from the refutation data returned by the prover.

  Expects each trace entry to have the shape
  `{source_term_id | nil, classified_rule, [produced_term_id]}`.
  """
  @spec from_refutation(map(), map(), list()) :: t()
  def from_refutation(branch_traces, substitution, flex_pairs) do
    traces = Map.values(branch_traces)

    # γ / gamma_finite / prim_subst reinsertions carry `nil` as their source.
    # Map each such rule back to the formula that originally triggered it.
    recipe_origin = collect_recipe_origins(traces)

    source_info = collect_source_info(traces, recipe_origin)
    closed_sources = collect_closed_sources(traces)
    parent_of = compute_parents(source_info)

    roots =
      source_info
      |> Map.keys()
      |> Enum.reject(&Map.has_key?(parent_of, &1))

    tree =
      case roots do
        [r] ->
          build_node(r, source_info, closed_sources)

        [] ->
          nil

        many ->
          %Node{
            formula: nil,
            rule: nil,
            # Multiple roots exist on the initial single branch
            node_type: :or,
            children: Enum.map(many, &build_node(&1, source_info, closed_sources))
          }
      end

    %__MODULE__{tree: tree, substitution: substitution, flex_pairs: flex_pairs}
  end

  ##############################################################################
  # TREE CONSTRUCTION HELPERS
  ##############################################################################

  # Find the first-occurring source for each {recipe-bearing rule kind, recipe}
  # pair. Used to attribute nil-source reinsertion entries back to the original
  # source formula.
  defp collect_recipe_origins(traces) do
    traces
    |> List.flatten()
    |> Enum.reduce(%{}, fn entry, acc ->
      case entry do
        {src, {:gamma, recipe, _, _}, _} when is_integer(src) ->
          Map.put_new(acc, {:gamma, recipe}, src)

        {src, {:gamma_finite, recipe, _}, _} when is_integer(src) ->
          Map.put_new(acc, {:gamma_finite, recipe}, src)

        {src, {:prim_subst, recipe, _, _, _}, _} when is_integer(src) ->
          Map.put_new(acc, {:prim_subst, recipe}, src)

        _ ->
          acc
      end
    end)
  end

  # Aggregate {source => {rule, produced}} across all traces. Entries for the
  # same source in different branches (e.g. everything before a β-split) are
  # merged by union-ing the produced lists.
  defp collect_source_info(traces, recipe_origin) do
    Enum.reduce(traces, %{}, fn trace, acc ->
      Enum.reduce(trace, acc, fn {source, rule, produced}, a ->
        effective = effective_source(source, rule, recipe_origin)

        if is_nil(effective) do
          a
        else
          Map.update(a, effective, {rule, produced}, fn {existing_rule, existing_produced} ->
            merged = Enum.uniq(existing_produced ++ produced)
            # Prefer the earliest rule seen (shouldn't differ for identical sources,
            # but for γ reinsertions we want the original rule, not the reinsert).
            {existing_rule, merged}
          end)
        end
      end)
    end)
  end

  defp effective_source(source, _rule, _origin) when is_integer(source), do: source

  defp effective_source(nil, rule, recipe_origin) do
    case recipe_key(rule) do
      nil -> nil
      key -> Map.get(recipe_origin, key)
    end
  end

  defp recipe_key({:gamma, recipe, _, _}), do: {:gamma, recipe}
  defp recipe_key({:gamma_finite, recipe, _}), do: {:gamma_finite, recipe}
  defp recipe_key({:prim_subst, recipe, _, _, _}), do: {:prim_subst, recipe}
  defp recipe_key(_), do: nil

  # The last entry in a trace is the step that caused the branch to close
  # (either ground closure or a clash-notification that succeeded globally).
  defp collect_closed_sources(traces) do
    traces
    |> Enum.flat_map(fn
      [] ->
        []

      trace ->
        case List.last(trace) do
          {src, _, _} when is_integer(src) -> [src]
          _ -> []
        end
    end)
    |> MapSet.new()
  end

  # A formula's parent is the source whose rule produced it. Earliest wins.
  defp compute_parents(source_info) do
    Enum.reduce(source_info, %{}, fn {source, {_rule, produced}}, acc ->
      Enum.reduce(produced, acc, fn p, a ->
        if Map.has_key?(a, p), do: a, else: Map.put(a, p, source)
      end)
    end)
  end

  # Recursively materialise an And-Or Node for the given source, pulling children from
  # its produced list.
  defp build_node(source, source_info, closed_sources) do
    {rule, produced} = Map.get(source_info, source, {nil, []})

    node_type =
      case rule do
        # Beta rules split the tableau (all branches must close)
        {:beta, _} -> :and
        # Alpha, Gamma, etc. add to the current branch
        _ -> :or
      end

    children =
      Enum.map(produced, fn child_id ->
        if Map.has_key?(source_info, child_id) do
          build_node(child_id, source_info, closed_sources)
        else
          %Node{
            formula: child_id,
            rule: nil,
            node_type: :or,
            children: [],
            closed: MapSet.member?(closed_sources, child_id)
          }
        end
      end)

    %Node{
      formula: source,
      rule: rule,
      node_type: node_type,
      children: children,
      closed: MapSet.member?(closed_sources, source) and children == []
    }
  end

  ##############################################################################
  # MERMAID RENDERING
  ##############################################################################

  @doc """
  Render the proof tree as a Mermaid `graph TD` diagram.

  Beta splits (:and nodes) render as solid branching lines.
  Alpha extensions (:or nodes) render as dotted lines to indicate same-branch propagation.
  """
  @spec to_rich_mermaid(t()) :: String.t()
  def to_rich_mermaid(%__MODULE__{tree: nil}), do: ""

  def to_rich_mermaid(%__MODULE__{tree: tree}) do
    {nodes, edges, _} = collect(tree, 0)

    header = """
    %%{init: {'theme': 'base', 'themeVariables': { 'lineColor': '#999999', 'edgeLabelBackground': '#ffffff', 'fontFamily': 'sans-serif'}}}%%
    graph TD;
      classDef formula fill:#eeeeee,stroke:#999999,stroke-width:2px,color:#333333,rx:8px,ry:8px;
      classDef closed fill:#eeeeee,stroke:#cc5500,stroke-width:2px,color:#000000,rx:8px,ry:8px;
      classDef conclusion fill:#e3f2fd,stroke:#1565c0,stroke-width:2px,color:#0d47a1,rx:8px,ry:8px;
    """

    node_lines =
      Enum.map_join(nodes, "\n", fn {id, label, class} ->
        "  N#{id}[\"#{escape(label)}\"]:::#{class};"
      end)

    edge_lines =
      Enum.map_join(edges, "\n", fn
        {from, to, nil, :and} ->
          "  N#{from} --> N#{to};"

        {from, to, label, :and} ->
          "  N#{from} -->|\"#{escape(label)}\"| N#{to};"

        {from, to, nil, :or} ->
          "  N#{from} -.-> N#{to};"

        {from, to, label, :or} ->
          "  N#{from} -.->|\"#{escape(label)}\"| N#{to};"
      end)

    header <> node_lines <> "\n" <> edge_lines <> "\n"
  end

  # Depth-first walk: assign a numeric id to each node, collect node labels
  # and edges. Returns {nodes, edges, next_id}.
  defp collect(%Node{} = node, counter) do
    my_id = counter
    self_entry = {my_id, node_label(node), node_class(node)}

    {child_nodes, child_edges, next_counter} =
      node.children
      |> Enum.with_index()
      |> Enum.reduce({[], [], counter + 1}, fn {child, idx}, {ns, es, c} ->
        {cn, ce, c2} = collect(child, c)

        # We append the node_type to the edge so we know how to render the branch
        edge = {my_id, c, edge_label_for(node, idx), node.node_type}

        {ns ++ cn, es ++ [edge | ce], c2}
      end)

    {[self_entry | child_nodes], child_edges, next_counter}
  end

  defp node_label(%Node{formula: nil}), do: "⊥"

  defp node_label(%Node{formula: term_id}) when is_integer(term_id) do
    format!(term_id)
  end

  defp node_class(%Node{closed: true}), do: "closed"
  defp node_class(_), do: "formula"

  # Edge from `parent` to its idx-th child: labelled by parent's rule,
  # enriched with the connective of parent's source formula.
  defp edge_label_for(%Node{rule: nil}, _idx), do: nil

  defp edge_label_for(%Node{formula: src, rule: rule, children: children}, idx) do
    base = enriched_rule_label(src, rule)

    case rule do
      {:beta, _} when length(children) == 2 ->
        suffix = if idx == 0, do: "_a", else: "_b"
        "#{base}#{suffix}"

      {:instantiate, _, _} when length(children) > 1 ->
        "#{base}_#{idx + 1}"

      _ ->
        base
    end
  end

  # Inspect the source formula to enrich the rule's label with the principal
  # connective — e.g. an α applied to `¬(p ⊃ q)` becomes `¬⊃`.
  defp enriched_rule_label(source, rule) when is_integer(source) do
    case safe_get_term(source) do
      nil -> rule_name(rule)
      term -> do_enriched_label(term, rule)
    end
  end

  defp enriched_rule_label(_, rule), do: rule_name(rule)

  defp do_enriched_label(term, rule) do
    case term do
      negated(inner) ->
        inner_term = safe_get_term(inner)
        suffix = if inner_term, do: connective_symbol(inner_term), else: nil
        "¬" <> (suffix || fallback_suffix(rule))

      _ ->
        connective_symbol(term) || rule_name(rule)
    end
  end

  # The suffix we reach for when we can't resolve the inner formula of a
  # negation — mostly just the bare rule name.
  defp fallback_suffix(rule), do: rule_name(rule) || ""

  # Map a term's principal connective to its display symbol.
  defp connective_symbol(term) do
    case term do
      negated(_inner) -> "¬"
      conjunction(_p, _q) -> "∧"
      disjunction(_p, _q) -> "∨"
      implication(_p, _q) -> "⊃"
      equivalence(_p, _q) -> "≡"
      equality(_a, _b) -> "="
      universal_quantification(_pred) -> "Π"
      existential_quantification(_pred) -> "Σ"
      _ -> nil
    end
  end

  # Plain rule name for rules we can't enrich (or as a fallback).
  defp rule_name(:tautology), do: "⊤"
  defp rule_name(:contradiction), do: "⊥"
  defp rule_name({:alpha, _}), do: "α"
  defp rule_name({:beta, _}), do: "β"
  defp rule_name({:gamma, _, _, _}), do: "γ"
  defp rule_name({:gamma_finite, _, _}), do: "γfin"
  defp rule_name({:delta, _}), do: "δ"
  defp rule_name({:prim_subst, _, _, _, _}), do: "π"
  defp rule_name({:rename, _}), do: "ren"
  defp rule_name({:instantiate, _, _}), do: "inst"
  # Atomic steps don't decompose, so they're never the "parent rule" on an
  # edge unless the atom was unfolded via a definition.
  defp rule_name({:atomic, _}), do: "unfold"
  defp rule_name(_), do: nil

  defp safe_get_term(term_id) do
    try do
      TF.get_term!(term_id)
    rescue
      _ -> nil
    end
  end

  defp escape(text) do
    text
    |> to_string()
    |> String.replace("\"", "\\\"")
  end
end
