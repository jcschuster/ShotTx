defmodule ShotTx.Prover.Paramodulation do
  @moduledoc """
  Lazy paramodulation, including rewriting at head positions.

  Given a literal and a map of equations, generates *paramodulants* — variants
  of the literal where some subterm `s` has been replaced by an equal term `t`,
  using equations from the map.

  Two rewrite sites are considered:

    * **DAG subterms** of the literal, found by `subterms/1` (anything in the
      argument-spine of the literal's term DAG).
    * **Head positions** — the prefix of any applied subterm `h(t̄)`, exposed
      as the η-expansion `λv̄. h(t̄, v̄)` of a partial application of the head
      `h`. This makes the head of an application a first-class rewrite site
      even though it lives in the term's `:head` field rather than in `:args`.

  Two complementary matching strategies are run together at each site:

    * **Structural** matching (`paramodulants/2`): identity of memoised
      term-ids, plus a special-case check for equations whose LHS is a
      primitive η-expansion `λv̄. h(v̄)` of a head `h`.
    * **Higher-order unification** (`unifying_paramodulants/4`): calls
      `ShotUn.unify/3` against subterms and against η-expanded head prefixes,
      then applies the resulting substitution before rewriting. The fourth
      argument selects the alignment fragment:

        * `:unification` — full higher-order pre-unification (Huet 1975);
        * `:pattern`     — Miller pattern unification (decidable, unitary);
        * `:matching`    — Huet second-order matching (decidable,
          terminating; requires the literal position to be ground).

      For `:pattern` and `:matching` the precondition is checked locally
      via `ShotUn.Fragment`; positions outside the fragment are silently
      skipped so the strategy stays terminating.

  Triggering is lazy (no preprocessing): paramodulants are generated on
  demand when a new literal enters the branch (against all known equations)
  or when a new equation enters the branch (against all existing literals,
  using only the new equation). Both call sites live in
  `ShotTx.Prover.Branch`.

  Rewriting is by **DAG occurrence**, not tree occurrence: replacing `s` with
  `t` rewrites all shared occurrences of `s` simultaneously, consistent with
  the term factory's structure-sharing semantics. The `:equality_expansion`
  rule (Leibniz / extensional / o-type iff) remains a sound and complete
  fallback for higher-order equality reasoning; paramodulation supplements
  it with cheap direct rewrites. The expansion rule is priced separately
  per kind so Leibniz can be held back behind paramodulation on first-order
  problems — see `ShotTx.Prover.Rules.rule_cost/2`.

  ## Limitations

    * Head-position rewriting is enumerated only for applied subterms whose
      outermost form is *not* an abstraction (i.e. `bvars == []`).
      Rewriting at a head position inside a λ-abstraction would require
      rebuilding the abstraction over substituted prefix args; the
      α-decomposition path covers those cases.
    * `unifying_paramodulants/4` enumerates partial-application prefixes for
      every arity `0 ≤ k < arity(s)`; full-spine matching (`k = arity(s)`) is
      already covered by direct subterm unification.
  """

  alias ShotDs.Data.Term
  alias ShotDs.Stt.Semantics
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TermTraversal
  alias ShotUn.Fragment

  @typedoc "Map from a term-id to the set of all its known-equal term-ids."
  @type equation_map :: %{Term.term_id() => MapSet.t(Term.term_id())}

  @typedoc """
  Strategy used when aligning an equation LHS with a literal position.

    * `:unification` — full higher-order pre-unification (Huet 1975).
    * `:pattern`     — Miller pattern unification: decidable and unitary,
      restricted to the higher-order pattern fragment.
    * `:matching`    — Huet second-order matching: decidable and
      terminating, requires the literal-side term to be ground and every
      type to be at most second-order.

  For `:pattern` and `:matching` the fragment precondition is checked at
  each site; pairs that fall outside the fragment are skipped.
  """
  @type mode :: :unification | :pattern | :matching

  @doc """
  Returns the paramodulants of `term_id` using `equations`.

  Combines two structural rewrite paths:

    * Subterm rewrites: for every subterm `s` of `term_id` that is a key in
      `equations`, every replacement `t ∈ equations[s]` produces the variant
      where every occurrence of `s` (by id) in `term_id` is replaced by `t`.
    * Head rewrites: for every equation whose LHS is recognisable as a
      primitive η-expansion `λv̄. h(v̄)` of a head `h`, every applied subterm
      with head `h` and matching arity is rewritten by β-applying the RHS to
      its existing arguments.

  Variants identical to the original and duplicates are dropped.
  """
  @spec paramodulants(Term.term_id(), equation_map()) :: [Term.term_id()]
  def paramodulants(_term_id, equations) when map_size(equations) == 0, do: []

  def paramodulants(term_id, equations) do
    (subterm_paramodulants(term_id, equations) ++
       head_paramodulants(term_id, equations))
    |> Enum.uniq()
  end

  @spec subterm_paramodulants(Term.term_id(), equation_map()) :: [Term.term_id()]
  defp subterm_paramodulants(term_id, equations) do
    term_id
    |> subterms()
    |> Enum.flat_map(fn s ->
      case Map.get(equations, s) do
        nil ->
          []

        replacements ->
          Enum.flat_map(replacements, fn t ->
            case replace_subterm(term_id, s, t) do
              ^term_id -> []
              result -> [result]
            end
          end)
      end
    end)
  end

  @spec head_paramodulants(Term.term_id(), equation_map()) :: [Term.term_id()]
  defp head_paramodulants(term_id, equations) do
    eta_heads = collect_eta_heads(equations)

    if eta_heads == [] do
      []
    else
      term_id
      |> applied_subterms()
      |> Enum.flat_map(fn s_id ->
        rewrite_head_position(term_id, s_id, eta_heads)
      end)
    end
  end

  defp rewrite_head_position(term_id, s_id, eta_heads) do
    s = TF.get_term!(s_id)
    arity = length(s.args)

    Enum.flat_map(eta_heads, fn {head_decl, n, rhs_ids} ->
      if s.head == head_decl and n <= arity do
        Enum.flat_map(MapSet.to_list(rhs_ids), fn rhs_id ->
          rewritten_subterm = TF.fold_apply!(rhs_id, s.args)

          case replace_subterm(term_id, s_id, rewritten_subterm) do
            ^term_id -> []
            result -> [result]
          end
        end)
      else
        []
      end
    end)
  end

  @doc """
  Returns paramodulants using higher-order pre-unification.

  Complements `paramodulants/2` by trying to unify each equation LHS against
  two kinds of positions in `term_id`:

    * Every DAG subterm `s` of `term_id` (whole-subterm unification).
    * Every η-expanded partial-application prefix of every applied subterm
      `s = h(a₁,…,aₘ)`, i.e. `λv̄. h(a₁,…,aₖ, v̄)` for each `0 ≤ k < m`.
      This exposes head positions to unification even though heads have no
      term-id node of their own.

  For each pre-unification solution the substitution is applied to the
  literal and the rewrite is computed by applying the substituted RHS to the
  remaining (substituted) arguments. Results are committed to the global
  term factory and de-duplicated.

  The `mode` argument selects the unification fragment used at each site
  (`:unification`, `:pattern`, or `:matching`). For `:pattern` and
  `:matching` the precondition of the fragment is checked per pair; pairs
  that fall outside the fragment are silently skipped.
  """
  @spec unifying_paramodulants(Term.term_id(), equation_map(), non_neg_integer(), mode()) ::
          [Term.term_id()]
  def unifying_paramodulants(term_id, equations, depth, mode \\ :unification)

  def unifying_paramodulants(_term_id, equations, _depth, _mode) when map_size(equations) == 0,
    do: []

  def unifying_paramodulants(term_id, equations, depth, mode) do
    (subterm_unifying(term_id, equations, depth, mode) ++
       prefix_unifying(term_id, equations, depth, mode))
    |> Enum.uniq()
  end

  defp subterm_unifying(term_id, equations, depth, mode) do
    subs = subterms(term_id)

    Enum.flat_map(equations, fn {lhs_id, rhs_ids} ->
      Enum.flat_map(subs, fn sub_id ->
        if sub_id == lhs_id do
          []
        else
          unify_and_rewrite(term_id, sub_id, lhs_id, rhs_ids, depth, mode, fn _ -> [] end)
        end
      end)
    end)
  end

  defp prefix_unifying(term_id, equations, depth, mode) do
    term_id
    |> applied_subterms()
    |> Enum.flat_map(fn s_id ->
      s = TF.get_term!(s_id)
      head_id = TF.make_term(s.head)

      0..(length(s.args) - 1)
      |> Enum.flat_map(fn k ->
        prefix_id = TF.fold_apply!(head_id, Enum.take(s.args, k))
        trailing = Enum.drop(s.args, k)

        Enum.flat_map(equations, fn {lhs_id, rhs_ids} ->
          unify_and_rewrite(term_id, prefix_id, lhs_id, rhs_ids, depth, mode, fn substs ->
            applied_trailing = Enum.map(trailing, &Semantics.subst!(substs, &1))
            applied_s = Semantics.subst!(substs, s_id)
            {:rebuild, applied_s, applied_trailing}
          end)
        end)
      end)
    end)
  end

  defp unify_and_rewrite(term_id, position_id, lhs_id, rhs_ids, depth, mode, post_unify) do
    case unify_stream({lhs_id, position_id}, depth, mode) do
      :skip ->
        []

      stream ->
        Enum.flat_map(stream, fn %{substitutions: substs} ->
          applied_literal = Semantics.subst!(substs, term_id)
          applied_lhs = Semantics.subst!(substs, lhs_id)
          rebuild = post_unify.(substs)

          Enum.flat_map(MapSet.to_list(rhs_ids), fn rhs_id ->
            applied_rhs = Semantics.subst!(substs, rhs_id)

            candidate =
              case rebuild do
                [] ->
                  replace_subterm(applied_literal, applied_lhs, applied_rhs)

                {:rebuild, target_id, trailing} ->
                  rewritten = TF.fold_apply!(applied_rhs, trailing)
                  replace_subterm(applied_literal, target_id, rewritten)
              end

            if candidate == applied_literal do
              []
            else
              [TF.commit_to_global!(candidate)]
            end
          end)
        end)
    end
  end

  # Returns the unifier stream for the chosen strategy, or `:skip` when the
  # pair falls outside the precondition of a restricted fragment.
  defp unify_stream(pair, depth, :unification),
    do: ShotUn.unify(pair, depth)

  defp unify_stream(pair, _depth, :pattern) do
    if Fragment.pattern_problem?([pair]),
      do: ShotUn.unify(pair, 0, strategy: :pattern),
      else: :skip
  end

  defp unify_stream(pair, _depth, :matching) do
    if Fragment.matching_problem?([pair]),
      do: ShotUn.unify(pair, 0, strategy: :matching),
      else: :skip
  end

  @doc """
  Returns the set of all subterm ids that appear inside `term_id`, including
  `term_id` itself.

  Heads are not separately represented as term-id nodes; they only count as
  subterms when they appear as zero-arity terms. To rewrite at head positions
  see `paramodulants/2` and `unifying_paramodulants/4`.
  """
  @spec subterms(Term.term_id()) :: MapSet.t(Term.term_id())
  def subterms(term_id) do
    {result, _cache} =
      TermTraversal.fold_term!(term_id, fn term, arg_results ->
        arg_results
        |> Enum.reduce(MapSet.new(), &MapSet.union/2)
        |> MapSet.put(term.id)
      end)

    result
  end

  @doc """
  Returns `term_id` with every occurrence of the subterm `target` replaced by
  `replacement`.
  """
  @spec replace_subterm(Term.term_id(), Term.term_id(), Term.term_id()) ::
          Term.term_id()
  def replace_subterm(term_id, target, replacement) when term_id == target,
    do: replacement

  def replace_subterm(term_id, target, replacement) do
    transform = fn current_term, new_args, _env, acc_cache ->
      if current_term.id == target do
        {replacement, acc_cache}
      else
        {rebuild_term(current_term, new_args), acc_cache}
      end
    end

    {result_id, _cache} =
      TermTraversal.map_term!(term_id, nil, fn _, env -> env end, transform)

    result_id
  end

  # Rebuild a term from its head and new args, recomputing all metadata fields.
  # Avoids the stale consts/fvars/max_num/tvars left by %{term | args: new_args}.
  defp rebuild_term(%Term{head: head, bvars: bvars}, new_args) do
    head_id = TF.make_term(head)
    body_id = TF.fold_apply!(head_id, new_args)
    List.foldr(bvars, body_id, &TF.make_abstr_term!(&2, &1))
  end

  # ----------------------------------------------------------------------------
  # Internal helpers
  # ----------------------------------------------------------------------------

  # Returns `[{head_decl, arity, rhs_ids}]` for every equation whose LHS is a
  # primitive η-expansion `λv̄. h(v̄)`.
  defp collect_eta_heads(equations) do
    Enum.flat_map(equations, fn {lhs_id, rhs_ids} ->
      case eta_head_pattern(lhs_id) do
        nil -> []
        {head_decl, arity} -> [{head_decl, arity, rhs_ids}]
      end
    end)
  end

  defp eta_head_pattern(term_id) do
    case TF.primitive_term?(term_id) do
      {:ok, true} ->
        %Term{head: head_decl, bvars: bvars} = TF.get_term!(term_id)

        case bvars do
          [] -> nil
          _ -> {head_decl, length(bvars)}
        end

      _ ->
        nil
    end
  end

  # All subterms of `term_id` that are applied terms whose outermost form is
  # not an abstraction (i.e. `bvars == []` and `args != []`).
  defp applied_subterms(term_id) do
    {result, _cache} =
      TermTraversal.fold_term!(term_id, fn term, arg_results ->
        children = Enum.reduce(arg_results, MapSet.new(), &MapSet.union/2)

        if term.bvars == [] and term.args != [] do
          MapSet.put(children, term.id)
        else
          children
        end
      end)

    result
  end
end
