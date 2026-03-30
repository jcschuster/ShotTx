defmodule ShotMain.Generation do
  alias ShotDs.Data.{Type, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.{Definitions, Dsl, Patterns}
  import ShotMain.Simplifyer

  @o %Type{goal: :o, args: []}
  @oo %Type{goal: :o, args: [@o]}
  @ooo %Type{goal: :o, args: [@o, @o]}

  @typep o_type :: %Type{goal: :o, args: [o_type()]}

  @spec gen_o(o_type()) :: Enumerable.t(Term.term_id())
  def gen_o(type) do
    cache_key = {:gen_o_cache, type}

    case Process.get(cache_key) do
      nil ->
        result = do_gen_o(type)
        Process.put(cache_key, result)
        result

      cached_result ->
        cached_result
    end
  end

  defp do_gen_o(@o), do: [true_term(), false_term()]

  defp do_gen_o(@oo) do
    [
      neg_term(),
      lambda([type_o()], fn x -> x end),
      lambda([type_o()], fn _x -> true_term() end),
      lambda([type_o()], fn _x -> false_term() end)
    ]
  end

  defp do_gen_o(@ooo) do
    [
      and_term(),
      or_term(),
      implies_term(),
      equivalent_term(),
      nand_term(),
      nor_term(),
      implied_by_term(),
      xor_term(),
      lambda([type_o(), type_o()], fn p, q -> p &&& neg(q) end),
      lambda([type_o(), type_o()], fn p, q -> neg(p) &&& q end),
      lambda([type_o(), type_o()], fn _p, _q -> true_term() end),
      lambda([type_o(), type_o()], fn _p, _q -> false_term() end),
      lambda([type_o(), type_o()], fn p, _q -> p end),
      lambda([type_o(), type_o()], fn _p, q -> q end),
      lambda([type_o(), type_o()], fn p, _q -> neg(p) end),
      lambda([type_o(), type_o()], fn _p, q -> neg(q) end)
    ]
  end

  defp do_gen_o(%Type{goal: :o, args: [alpha | rest]}) do
    beta = %Type{goal: :o, args: rest}
    xs = gen_o(alpha) |> Enum.to_list()
    ys = gen_o(beta)

    cartesian_power(ys, length(xs))
    |> Stream.map(fn combo ->
      pairs = Enum.zip(xs, combo)
      [{_x_last, y_last} | rest_pairs] = Enum.reverse(pairs)

      lambda(alpha, fn var_x ->
        body =
          Enum.reduce(rest_pairs, y_last, fn {x_i, y_i}, prev_body ->
            c = equiv(alpha, var_x, x_i)
            ite(beta, c, y_i, prev_body)
          end)

        o_simplify(body)
      end)
    end)
  end

  defp cartesian_power(_ys, 0), do: [[]]

  defp cartesian_power(ys, n) do
    ys_list = Enum.to_list(ys)

    Enum.reduce(1..n, [[]], fn _, acc ->
      Stream.flat_map(acc, fn rest ->
        Stream.map(ys_list, fn y -> [y | rest] end)
      end)
    end)
  end

  defp ite(@o, c, u, v) do
    c_s = o_simplify(c)
    u_s = o_simplify(u)
    v_s = o_simplify(v)

    if u_s == v_s do
      u_s
    else
      case TF.get_term(c_s) do
        truth() -> u_s
        falsity() -> v_s
        _ -> o_simplify((c_s &&& u_s) ||| (neg(c_s) &&& v_s))
      end
    end
  end

  defp ite(%Type{goal: :o, args: [alpha | rest]}, c, u, v) do
    beta = %Type{goal: :o, args: rest}
    lambda(alpha, fn x -> ite(beta, c, app(u, x), app(v, x)) end)
  end

  defp equiv(@o, p, q), do: o_simplify(p <~> q)

  defp equiv(%Type{goal: :o, args: [alpha | rest]}, f, g) do
    beta = %Type{goal: :o, args: rest}

    gen_o(alpha)
    |> Stream.map(fn x -> equiv(beta, app(f, x), app(g, x)) end)
    |> Enum.reduce(fn eq_i, acc -> o_simplify(eq_i &&& acc) end)
  end
end
