defmodule ShotTx.Prover.FormulaPqueue do
  alias ShotTx.Prover.Rules

  @type t :: :gb_trees.tree(non_neg_integer(), Rules.rule_t())

  def new() do
    :gb_trees.empty()
  end

  def empty?(pqueue), do: :gb_trees.is_empty(pqueue)

  def insert(pqueue, element, cost) do
    case :gb_trees.lookup(cost, pqueue) do
      {:value, others} -> :gb_trees.update(cost, [element | others], pqueue)
      :none -> :gb_trees.insert(cost, [element], pqueue)
    end
  end

  def take_smallest(pqueue) do
    {cost, elements, new_tree} = :gb_trees.take_smallest(pqueue)

    case elements do
      [e] -> {e, new_tree}
      [e | es] -> {e, :gb_trees.insert(cost, es, new_tree)}
    end
  end
end
