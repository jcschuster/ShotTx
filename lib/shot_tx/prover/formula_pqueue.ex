defmodule ShotTx.Prover.FormulaPqueue do
  @moduledoc """
  Min-priority queue for tableau formulas, backed by `:gb_trees`.

  Elements are bucketed by integer cost; within the same cost bucket they are
  served FIFO. The cost is supplied by the caller (see `Rules.rule_cost/1`).
  """

  alias ShotTx.Prover.Rules

  @type t :: :gb_trees.tree(non_neg_integer(), :queue.queue(Rules.rule_t()))

  @doc "Returns an empty priority queue."
  @spec new() :: t()
  def new() do
    :gb_trees.empty()
  end

  @doc "Returns `true` if the queue contains no elements."
  @spec empty?(t()) :: boolean()
  def empty?(pqueue), do: :gb_trees.is_empty(pqueue)

  @doc "Inserts `element` at the given `cost`. Equal-cost elements are served FIFO."
  @spec insert(t(), element :: term(), cost :: non_neg_integer()) :: t()
  def insert(pqueue, element, cost) do
    case :gb_trees.lookup(cost, pqueue) do
      {:value, others} -> :gb_trees.update(cost, :queue.in(element, others), pqueue)
      :none -> :gb_trees.insert(cost, :queue.in(element, :queue.new()), pqueue)
    end
  end

  @doc "Removes and returns the lowest-cost element together with the updated queue."
  @spec take_smallest(t()) :: {element :: term(), t()}
  def take_smallest(pqueue) do
    {cost, elements, new_tree} = :gb_trees.take_smallest(pqueue)
    {{:value, e}, rest_queue} = :queue.out(elements)

    if :queue.is_empty(rest_queue) do
      {e, new_tree}
    else
      {e, :gb_trees.insert(cost, rest_queue, new_tree)}
    end
  end
end
