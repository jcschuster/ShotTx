defmodule ShotTx.Prover.StatsTest do
  use ExUnit.Case, async: true

  alias ShotTx.Prover.Stats

  describe "compile/1" do
    test "groups raw counters into the expected sections" do
      snapshot = %{
        proof_started_at_us: 1_000,
        proof_finished_at_us: 3_500_000,
        aborted: false,
        steps_total: 50,
        worker_yields: 2,
        rule_alpha: 30,
        rule_beta: 10,
        rule_gamma: 10,
        branches_split: 5,
        branches_closed_locally: 2,
        active_branches_max: 3,
        csp_calls: 4,
        csp_calls_succeeded: 1,
        csp_calls_failed: 3,
        csp_calls_skipped: 7
      }

      report = Stats.compile(snapshot)

      assert report.timing.duration_us == 3_499_000
      assert report.timing.duration_ms == 3499.0
      assert report.timing.aborted == false

      assert report.search.steps_total == 50
      assert_in_delta report.search.steps_per_sec, 14.29, 0.1

      assert report.rules.alpha == 30
      assert report.rules.beta == 10
      assert report.rules.gamma == 10
      assert report.rules.total == 50

      assert report.branches.split == 5
      assert report.branches.closed_locally == 2
      assert report.branches.active_max == 3

      assert report.csp.calls == 4
      assert report.csp.skipped == 7
      assert report.csp.success_rate == 0.25
    end

    test "handles a snapshot missing timing data" do
      report = Stats.compile(%{steps_total: 10})

      assert report.timing.duration_us == nil
      assert report.timing.duration_ms == nil
      assert report.search.steps_per_sec == nil
    end

    test "is idempotent on an already-compiled report" do
      snapshot = %{steps_total: 5}
      compiled = Stats.compile(snapshot)
      assert Stats.compile(compiled) == compiled
    end
  end

  describe "format/2" do
    setup do
      snapshot = %{
        proof_started_at_us: 0,
        proof_finished_at_us: 2_500_000,
        aborted: false,
        steps_total: 100,
        rule_alpha: 60,
        rule_beta: 40,
        branches_split: 20,
        branches_closed_locally: 10,
        csp_calls: 5,
        csp_calls_succeeded: 1,
        csp_duration_us: %{count: 5, sum: 1000, min: 100, max: 400, avg: 200.0}
      }

      {:ok, snapshot: snapshot}
    end

    test "renders all sections by default", %{snapshot: snapshot} do
      out = Stats.format(snapshot)

      assert out =~ "Proof Stats"
      assert out =~ "Timing"
      assert out =~ "Search"
      assert out =~ "Rules"
      assert out =~ "Branches"
      assert out =~ "CSP"
    end

    test "hides zero-valued rule counters by default", %{snapshot: snapshot} do
      out = Stats.format(snapshot)

      assert out =~ "alpha"
      assert out =~ "beta"
      refute out =~ "delta"
      refute out =~ "rename"
    end

    test "verbose: true keeps zero counters", %{snapshot: snapshot} do
      out = Stats.format(snapshot, verbose: true)

      assert out =~ "delta"
      assert out =~ "rename"
    end

    test "sections opt selects which blocks to render", %{snapshot: snapshot} do
      out = Stats.format(snapshot, sections: [:timing, :csp])

      assert out =~ "Timing"
      assert out =~ "CSP"
      refute out =~ "\nRules\n"
      refute out =~ "\nBranches\n"
    end

    test "renders sampler stats for CSP", %{snapshot: snapshot} do
      out = Stats.format(snapshot)

      assert out =~ "duration μs"
      assert out =~ "avg=200"
      assert out =~ "n=5"
    end

    test "accepts an already-compiled report", %{snapshot: snapshot} do
      compiled = Stats.compile(snapshot)
      assert Stats.format(compiled) == Stats.format(snapshot)
    end

    test "renders a duration of 2.5s" do
      out = Stats.format(%{proof_started_at_us: 0, proof_finished_at_us: 2_500_000})
      assert out =~ "2.5 s"
    end
  end
end
