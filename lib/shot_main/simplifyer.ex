defmodule ShotMain.Simplifyer do
  import ShotDs.Hol.{Definitions, Patterns, Dsl}
  alias ShotDs.Stt.TermFactory, as: TF

  def o_simplify(term_id) do
    case :ets.lookup(:term_cache, {:simp, term_id}) do
      [{{:simp, ^term_id}, cached_result}] ->
        cached_result

      [] ->
        simplified = do_o_simplify(term_id)
        :ets.insert(:term_cache, {{:simp, term_id}, simplified})
        simplified
    end
  end

  defp do_o_simplify(term_id) do
    case TF.get_term(term_id) do
      negated(inner) ->
        inner_s = o_simplify(inner)

        case TF.get_term(inner_s) do
          truth() -> false_term()
          falsity() -> true_term()
          negated(inner_inner) -> inner_inner
          _ -> neg(inner_s)
        end

      conjunction(p, q) ->
        p_s = o_simplify(p)
        q_s = o_simplify(q)

        case {TF.get_term(p_s), TF.get_term(q_s)} do
          {truth(), _} -> q_s
          {_, truth()} -> p_s
          {falsity(), _} -> false_term()
          {_, falsity()} -> false_term()
          _ when p_s == q_s -> p_s
          _ -> p_s &&& q_s
        end

      disjunction(p, q) ->
        p_s = o_simplify(p)
        q_s = o_simplify(q)

        case {TF.get_term(p_s), TF.get_term(q_s)} do
          {truth(), _} -> true_term()
          {_, truth()} -> true_term()
          {falsity(), _} -> q_s
          {_, falsity()} -> p_s
          _ when p_s == q_s -> p_s
          _ -> p_s ||| q_s
        end

      implication(p, q) ->
        p_s = o_simplify(p)
        q_s = o_simplify(q)

        case {TF.get_term(p_s), TF.get_term(q_s)} do
          {truth(), _} -> q_s
          {falsity(), _} -> true_term()
          {_, truth()} -> true_term()
          _ when p_s == q_s -> true_term()
          _ -> p_s ~> q_s
        end

      equivalence(p, q) ->
        p_s = o_simplify(p)
        q_s = o_simplify(q)

        case {TF.get_term(p_s), TF.get_term(q_s)} do
          {truth(), _} -> q_s
          {_, truth()} -> p_s
          {falsity(), _} -> o_simplify(neg(q_s))
          {_, falsity()} -> o_simplify(neg(p_s))
          _ when p_s == q_s -> true_term()
          _ -> p_s <~> q_s
        end

      _ ->
        term_id
    end
  end
end
