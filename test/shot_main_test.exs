defmodule ShotMainTest do
  use ExUnit.Case
  doctest ShotMain

  test "greets the world" do
    assert ShotMain.hello() == :world
  end
end
