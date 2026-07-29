defmodule ShotTx.Prover.ProvenanceTest do
  @moduledoc """
  Verifies the load-bearing bookkeeping for `SuggestionAgent` / future
  evidence-driven agents: every fresh variable minted by a γ- or prim-subst
  rule is emitted as a `{:record_provenance, ...}` effect from
  `Branch.step/4`, tagged with the originating `recipe`, `source`,
  `birth_branch`, and origin kind.
  """
  use ExUnit.Case, async: false

  import ShotDs.Hol.Sigils

  alias ShotTx.Data.Parameters
  alias ShotTx.Prover.{Branch, Provenance}

  @minimal %Parameters{
    simplification: :none,
    beta_variant: false,
    demodulation: false,
    orient: :none,
    instance_based_gamma: false
  }

  describe "γ site" do
    test "one fresh var per firing, tagged with :gamma origin and iteration 0" do
      ctx = ~e"p: $i > $o"

      with_context(ctx, fn ->
        all = ~f"![X: $i]: (p @ X)"

        branch = Branch.new("root", [all], @minimal)

        assert {:continue, _next, {:record_provenance, records}} =
                 Branch.step(branch, @minimal, 2, 1)

        assert [{fresh_var, %Provenance{} = prov}] = records
        assert is_integer(fresh_var)
        assert prov.origin == :gamma
        assert prov.birth_branch == "root"
        assert prov.gamma_iteration == 0
        assert is_integer(prov.recipe)
        assert is_integer(prov.source)
      end)
    end

    test "second γ-firing bumps gamma_iteration to 1" do
      ctx = ~e"p: $i > $o"

      with_context(ctx, fn ->
        all = ~f"![X: $i]: (p @ X)"

        # Step budget: γ (0) → atomic → γ (1). We loop until we see a
        # second :gamma record.
        branch = Branch.new("root", [all], @minimal)
        records = step_until_gamma(branch, @minimal, 2, 1, iteration: 1)

        assert [{_fresh, %Provenance{origin: :gamma, gamma_iteration: 1}}] = records
      end)
    end
  end

  describe "prim-subst site" do
    # `prim_subst_after: 0` combined with a γ-bound variable whose type has
    # `goal == :o` forces prim-subst to schedule on the first γ-fire. We then
    # step past the interleaved atomic/γ pops until the prim-subst rule fires.
    @primsubst %Parameters{
      simplification: :none,
      beta_variant: false,
      demodulation: false,
      orient: :none,
      instance_based_gamma: false,
      prim_subst_after: 0,
      prim_subst_batch_size: 4
    }

    test "each general-binding hole is emitted with :prim_subst origin" do
      ctx = ~e"p: ($i > $o) > $o"

      with_context(ctx, fn ->
        # ∀P: $i>$o. p @ P — γ binds a function-typed var (type.goal == :o),
        # scheduling prim-subst. `p` is a rigid constant so the atomic
        # instance p @ P cannot close the branch, giving prim-subst room to
        # actually fire.
        all = ~f"![P: $i > $o]: (p @ P)"

        branch = Branch.new("root", [all], @primsubst)
        ps_records = step_until_prim_subst(branch, @primsubst, 1, 1)

        assert ps_records != []

        for {h_id, %Provenance{} = prov} <- ps_records do
          assert is_integer(h_id)
          assert prov.origin == :prim_subst
          assert prov.birth_branch == "root"
          assert prov.gamma_iteration == 1
          assert is_integer(prov.recipe)
        end
      end)
    end
  end

  describe "record/3 + fetch/2" do
    test "round-trips a provenance struct through ETS" do
      table = :ets.new(:test_provenance, [:set, :public])

      prov = %Provenance{
        recipe: 42,
        source: 7,
        birth_branch: "root_A",
        gamma_iteration: 3,
        origin: :gamma
      }

      assert Provenance.record(table, 99, prov) == true
      assert Provenance.fetch(table, 99) == prov
      # insert_new — second write is silently rejected
      assert Provenance.record(table, 99, %{prov | gamma_iteration: 999}) == false
      assert Provenance.fetch(table, 99) == prov
      assert Provenance.fetch(table, 12_345) == nil
    end
  end

  # --- helpers ---------------------------------------------------------------

  defp step_until_gamma(branch, params, g, p, iteration: target) do
    case Branch.step(branch, params, g, p) do
      {:continue, _next,
       {:record_provenance, [{_, %Provenance{origin: :gamma, gamma_iteration: ^target}}] = recs}} ->
        recs

      {:continue, next, _} ->
        step_until_gamma(next, params, g, p, iteration: target)

      other ->
        flunk("unexpected step result: #{inspect(other, limit: 5)}")
    end
  end

  defp step_until_prim_subst(branch, params, g, p) do
    case Branch.step(branch, params, g, p) do
      {:continue, _next, {:record_provenance, [{_, %Provenance{origin: :prim_subst}} | _] = recs}} ->
        recs

      {:continue, next, _} ->
        step_until_prim_subst(next, params, g, p)

      other ->
        flunk("unexpected step result: #{inspect(other, limit: 5)}")
    end
  end
end
