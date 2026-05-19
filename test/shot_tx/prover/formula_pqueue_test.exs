defmodule ShotTx.Prover.FormulaPqueueTest do
  use ExUnit.Case, async: true

  alias ShotTx.Prover.FormulaPqueue, as: FPQ

  test "new/0 returns an empty queue" do
    q = FPQ.new()
    assert FPQ.empty?(q)
  end

  test "insert/3 makes the queue non-empty" do
    q = FPQ.new() |> FPQ.insert(:a, 5)
    refute FPQ.empty?(q)
  end

  test "take_smallest returns the lowest-cost element first" do
    q =
      FPQ.new()
      |> FPQ.insert(:mid, 5)
      |> FPQ.insert(:low, 1)
      |> FPQ.insert(:high, 10)

    {e1, q1} = FPQ.take_smallest(q)
    {e2, q2} = FPQ.take_smallest(q1)
    {e3, q3} = FPQ.take_smallest(q2)

    assert e1 == :low
    assert e2 == :mid
    assert e3 == :high
    assert FPQ.empty?(q3)
  end

  test "equal-cost elements come out in FIFO order" do
    q =
      FPQ.new()
      |> FPQ.insert(:first, 3)
      |> FPQ.insert(:second, 3)
      |> FPQ.insert(:third, 3)

    {e1, q1} = FPQ.take_smallest(q)
    {e2, q2} = FPQ.take_smallest(q1)
    {e3, _} = FPQ.take_smallest(q2)

    assert [e1, e2, e3] == [:first, :second, :third]
  end

  test "alternating costs interleave correctly" do
    q =
      FPQ.new()
      |> FPQ.insert(:a, 2)
      |> FPQ.insert(:b, 1)
      |> FPQ.insert(:c, 2)
      |> FPQ.insert(:d, 1)

    {e1, q1} = FPQ.take_smallest(q)
    {e2, q2} = FPQ.take_smallest(q1)
    {e3, q3} = FPQ.take_smallest(q2)
    {e4, _} = FPQ.take_smallest(q3)

    assert [e1, e2, e3, e4] == [:b, :d, :a, :c]
  end
end
