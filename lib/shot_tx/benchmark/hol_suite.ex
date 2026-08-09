defmodule ShotTx.Benchmark.HolSuite do
  @moduledoc """
  The structured set of higher-order problems from
  `examples/structured_hol_problems.livemd`, expressed as self-contained TPTP
  THF problem strings.

  The livebook states its problems in a mixture of `~f` (bare formula, types
  inferred), `~e`/`with_context` (formula plus an ambient type environment) and
  `~p` (TPTP problem). To compare ShotTx against external provers, every
  problem here is normalised to *one* representation: a complete THF problem
  that both `ShotDs.Tptp.parse_tptp_string!/1` and SystemOnTPTP accept
  verbatim. Nobody gets a different input.

  Two deliberate deviations from the livebook text:

    * **Monomorphisation.** The livebook declares `l: A > A > $o` and friends
      with implicit type variables. Rank-1 polymorphism is TH1, which Satallax
      and E do not accept, so every equality-like relation is declared at a
      concrete type. Where the livebook applies one polymorphic constant at two
      different types (e.g. `l @ F @ G` and `l @ (F @ X) @ (G @ X)` in
      Example 9a), this suite declares two monomorphic copies (`l_f`, `l_i`).

    * **Set-theory typo fix.** `set_theory_defs` in the livebook defines
      `set_l1` three times and never defines `set_l2`, `set_l3`,
      `set_set_l2` or `set_set_l3` — a copy-paste slip that leaves the
      Example 22 Leibniz variants referring to undefined constants (hence not
      theorems at all). Each definition here binds its own head.

  Free set constants in Example 22 are named `sa`/`sb`/`sc` throughout so the
  Andrews variant, which needs the constant `a` for its own relation, does not
  collide.

  Each problem carries the livebook's own annotation in `:note` (`"THM"`,
  `"Timeout"`, or `""` where the livebook made no claim). That is the author's
  recorded observation, *not* ground truth — the reference provers supply that.
  """

  @typedoc "One benchmark problem."
  @type problem :: %{
          id: String.t(),
          section: String.t(),
          variant: String.t(),
          note: String.t(),
          thf: String.t()
        }

  # The equality-like relations the livebook varies each example over.
  @leibniz [{"leibniz_imp", "=>"}, {"leibniz_rev_imp", "<="}, {"leibniz_iff", "<=>"}]

  @doc """
  Every problem in the suite, in livebook order.
  """
  @spec problems() :: [problem()]
  def problems do
    Enum.concat([
      warm_up(),
      non_theorems(),
      choice(),
      reflexivity(),
      commutativity(),
      transitivity(),
      congruence_endomorphisms(),
      congruence_predicates(),
      leibniz_vs_primitive(),
      functional_extensionality(),
      boolean_extensionality(),
      boolean_extensionality_hard(),
      eta_expansion(),
      extension_with_identity(),
      extension_of_identity(),
      commutativity_extension(),
      conjunction_extension(),
      self_negation(),
      nested_boolean_argument(),
      lambda_normalisation(),
      de_morgan(),
      finite_domain(),
      set_theory(),
      propositional_witnesses(),
      cantor()
    ])
  end

  @doc """
  Looks a problem up by `:id`.
  """
  @spec fetch(String.t()) :: {:ok, problem()} | :error
  def fetch(id) do
    case Enum.find(problems(), &(&1.id == id)) do
      nil -> :error
      problem -> {:ok, problem}
    end
  end

  ##############################################################################
  # DEFINITION BLOCKS
  #
  # `tau` is a type string already parenthesised where compound, so it can be
  # dropped into both an atomic slot (`l: tau > tau > $o`) and a binder
  # (`^[X:tau]`).
  ##############################################################################

  # Leo-III and Satallax reject a bare lambda on the right of `=`, so every
  # definition body is parenthesised. Compound binder types are parenthesised
  # for the same reason.
  defp leibniz_def(name, tau, connective) do
    """
    thf(#{name}_t, type, #{name}: #{tau} > #{tau} > $o).
    thf(#{name}_def, definition,
      #{name} = (^[X:#{tau}, Y:#{tau}]: (![P:(#{tau}>$o)]: ((P @ X) #{connective} (P @ Y))))
    ).
    """
  end

  defp andrews_def(name, tau) do
    """
    thf(#{name}_t, type, #{name}: #{tau} > #{tau} > $o).
    thf(#{name}_def, definition,
      #{name} = (^[X:#{tau}, Y:#{tau}]:
        (![Q:(#{tau}>#{tau}>$o)]: ((![Z:#{tau}]: (Q @ Z @ Z)) => (Q @ X @ Y))))
    ).
    """
  end

  # Pointwise-equality relation on the function type `sigma > tau`.
  defp extensional_def(name, sigma, tau) do
    fun = "(#{sigma}>#{tau})"

    """
    thf(#{name}_t, type, #{name}: #{fun} > #{fun} > $o).
    thf(#{name}_def, definition,
      #{name} = (^[X:#{fun}, Y:#{fun}]: (![Z:#{sigma}]: ((X @ Z) = (Y @ Z))))
    ).
    """
  end

  defp conjecture(text), do: "thf(conj, conjecture,\n  #{text}\n).\n"

  defp problem(id, section, variant, note, preamble, conj) do
    %{
      id: id,
      section: section,
      variant: variant,
      note: note,
      thf: preamble <> conjecture(conj)
    }
  end

  ##############################################################################
  # WARM-UP
  ##############################################################################

  defp warm_up do
    preamble = """
    thf(a_t, type, a: $o).
    thf(b_t, type, b: $o).
    thf(p_t, type, p: $o>$o).
    """

    [
      problem(
        "warmup_negated_forall",
        "Warm-up",
        "primitive",
        "",
        preamble,
        "~ (![Y:($o>$o)]: (((~a) & (Y @ a)) | ((~ (p @ b)) & (p @ (Y @ b)))))"
      )
    ]
  end

  ##############################################################################
  # NON-THEOREMS
  ##############################################################################

  defp non_theorems do
    section = "Non-Theorems"
    q = "thf(q_t, type, q: $i>$i>$o).\n"

    fixpoint =
      [
        {"prim", "", "![F:($i>$i)]: (?[X:$i]: ((F @ X) = X))"}
      ] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$i", conn), "![F:($i>$i)]: (?[X:$i]: (l @ (F @ X) @ X))"}
        end ++
        [
          {"andrews", andrews_def("a", "$i"), "![F:($i>$i)]: (?[X:$i]: (a @ (F @ X) @ X))"},
          {"extensional", extensional_def("e", "$i", "$i"),
           "![F:(($i>$i)>$i>$i)]: (?[X:($i>$i)]: (e @ (F @ X) @ X))"}
        ]

    [
      problem(
        "nt_quantifier_swap_1",
        section,
        "primitive",
        "Timeout",
        q,
        "(?[X:$i]: (![Y:$i]: (q @ X @ Y))) | (?[U:$i]: (![V:$i]: (~ (q @ V @ U))))"
      ),
      problem(
        "nt_quantifier_swap_2",
        section,
        "primitive",
        "Timeout",
        q,
        "?[Y:$i]: (![X:$i]: ((![Z:$i]: (q @ X @ Z)) | (~ (q @ X @ Y))))"
      )
    ] ++
      for {variant, defs, conj} <- fixpoint do
        problem("nt_fixpoint_#{variant}", section, variant, "Timeout", defs, conj)
      end
  end

  ##############################################################################
  # EXAMPLES 4 & 5 (CHOICE)
  ##############################################################################

  defp choice do
    section = "Examples 4 & 5 (Choice)"

    [
      problem(
        "choice_skolem",
        section,
        "primitive",
        "THM",
        "thf(r_t, type, r: $i>$i>$o).\n",
        "(![X:$i]: (?[Y:$i]: (r @ X @ Y))) => (?[F:($i>$i)]: (![X:$i]: (r @ X @ (F @ X))))"
      ),
      problem(
        "choice_epsilon",
        section,
        "primitive",
        "THM",
        "",
        "?[E:(($i>$o)>$i)]: (![P:($i>$o)]: ((![Y:$i]: (P @ Y)) => (P @ (E @ P))))"
      )
    ]
  end

  ##############################################################################
  # EXAMPLE 6 (REFLEXIVITY, COMMUTATIVITY, TRANSITIVITY)
  ##############################################################################

  defp reflexivity do
    section = "Example 6a (Reflexivity)"

    specs =
      [{"prim", "", "![X:$i]: (X = X)"}] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$i", conn), "![X:$i]: (l @ X @ X)"}
        end ++
        [
          {"andrews", andrews_def("a", "$i"), "![X:$i]: (a @ X @ X)"},
          {"extensional", extensional_def("e", "$i", "$i"), "![X:($i>$i)]: (e @ X @ X)"}
        ]

    for {variant, defs, conj} <- specs do
      problem("refl_#{variant}", section, variant, "THM", defs, conj)
    end
  end

  defp commutativity do
    section = "Example 6b (Commutativity)"

    specs =
      [{"prim", "", "![X:$i, Y:$i]: ((X = Y) => (Y = X))", "THM"}] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$i", conn), "![X:$i, Y:$i]: ((l @ X @ Y) => (l @ Y @ X))",
           "THM"}
        end ++
        [
          {"andrews", andrews_def("a", "$i"), "![X:$i, Y:$i]: ((a @ X @ Y) => (a @ Y @ X))",
           "THM"},
          {"extensional", extensional_def("e", "$i", "$i"),
           "![X:($i>$i), Y:($i>$i)]: ((e @ X @ Y) => (e @ Y @ X))", "THM"}
        ]

    for {variant, defs, conj, note} <- specs do
      problem("comm_#{variant}", section, variant, note, defs, conj)
    end
  end

  defp transitivity do
    section = "Example 6c (Transitivity)"

    specs =
      [{"prim", "", "![X:$i, Y:$i, Z:$i]: (((X = Y) & (Y = Z)) => (X = Z))", "THM"}] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$i", conn),
           "![X:$i, Y:$i, Z:$i]: (((l @ X @ Y) & (l @ Y @ Z)) => (l @ X @ Z))", "THM"}
        end ++
        [
          {"andrews", andrews_def("a", "$i"),
           "![X:$i, Y:$i, Z:$i]: (((a @ X @ Y) & (a @ Y @ Z)) => (a @ X @ Z))", "Timeout"},
          {"extensional", extensional_def("e", "$i", "$i"),
           "![X:($i>$i), Y:($i>$i), Z:($i>$i)]: (((e @ X @ Y) & (e @ Y @ Z)) => (e @ X @ Z))",
           "THM"}
        ]

    for {variant, defs, conj, note} <- specs do
      problem("trans_#{variant}", section, variant, note, defs, conj)
    end
  end

  ##############################################################################
  # EXAMPLE 7 (CONGRUENCE)
  ##############################################################################

  defp congruence_endomorphisms do
    section = "Example 7a (Congruence under endomorphisms)"

    specs =
      [
        {"prim", "", "![X:$i, Y:$i, F:($i>$i)]: ((X = Y) => ((F @ X) = (F @ Y)))", "THM"}
      ] ++
        for {variant, conn} <- @leibniz do
          note = if variant == "leibniz_iff", do: "Timeout", else: "THM"

          {variant, leibniz_def("l", "$i", conn),
           "![X:$i, Y:$i, F:($i>$i)]: ((l @ X @ Y) => (l @ (F @ X) @ (F @ Y)))", note}
        end ++
        [
          {"andrews", andrews_def("a", "$i"),
           "![X:$i, Y:$i, F:($i>$i)]: ((a @ X @ Y) => (a @ (F @ X) @ (F @ Y)))", "Timeout"},
          {"extensional", extensional_def("e", "$i", "$i"),
           "![X:($i>$i), Y:($i>$i), F:(($i>$i)>$i>$i)]: " <>
             "((e @ X @ Y) => (e @ (F @ X) @ (F @ Y)))", "Timeout"}
        ]

    for {variant, defs, conj, note} <- specs do
      problem("cong_endo_#{variant}", section, variant, note, defs, conj)
    end
  end

  defp congruence_predicates do
    section = "Example 7b (Congruence under predicates)"

    specs =
      [
        {"prim", "", "![X:$i, Y:$i, P:($i>$o)]: ((X = Y) => ((P @ X) => (P @ Y)))", "THM"}
      ] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$i", conn),
           "![X:$i, Y:$i, P:($i>$o)]: ((l @ X @ Y) => ((P @ X) => (P @ Y)))", "THM"}
        end ++
        [
          {"andrews", andrews_def("a", "$i"),
           "![X:$i, Y:$i, P:($i>$o)]: ((a @ X @ Y) => ((P @ X) => (P @ Y)))", "Timeout"},
          {"extensional", extensional_def("e", "$i", "$i"),
           "![X:($i>$i), Y:($i>$i), P:(($i>$i)>$o)]: " <>
             "((e @ X @ Y) => ((P @ X) => (P @ Y)))", "Timeout"}
        ]

    for {variant, defs, conj, note} <- specs do
      problem("cong_pred_#{variant}", section, variant, note, defs, conj)
    end
  end

  ##############################################################################
  # EXAMPLE 8 (LEIBNIZ AND PRIMITIVE EQUALITY)
  ##############################################################################

  defp leibniz_vs_primitive do
    section = "Example 8 (Leibniz and primitive equality)"
    consts = "thf(a_t, type, a: $i).\nthf(b_t, type, b: $i).\n"

    for {variant, conn} <- @leibniz do
      note = if variant == "leibniz_iff", do: "THM", else: "Timeout"

      problem(
        "leibniz_implies_eq_#{variant}",
        section,
        variant,
        note,
        leibniz_def("l", "$i", conn) <> consts,
        "(l @ a @ b) => (a = b)"
      )
    end
  end

  ##############################################################################
  # EXAMPLE 9 (TRIVIAL DIRECTIONS OF EXTENSIONALITY)
  ##############################################################################

  defp functional_extensionality do
    section = "Example 9a (Functional extensionality, trivial direction)"

    specs =
      [
        {"prim", "", "![F:($i>$i), G:($i>$i)]: ((F = G) => (![X:$i]: ((F @ X) = (G @ X))))"}
      ] ++
        for {variant, conn} <- @leibniz do
          # `l` is used at both $i>$i and $i, so it needs two monomorphic copies.
          {variant, leibniz_def("l_f", "($i>$i)", conn) <> leibniz_def("l_i", "$i", conn),
           "![F:($i>$i), G:($i>$i)]: ((l_f @ F @ G) => (![X:$i]: (l_i @ (F @ X) @ (G @ X))))"}
        end ++
        [
          {"andrews", andrews_def("a_f", "($i>$i)") <> andrews_def("a_i", "$i"),
           "![F:($i>$i), G:($i>$i)]: ((a_f @ F @ G) => (![X:$i]: (a_i @ (F @ X) @ (G @ X))))"},
          {"extensional",
           extensional_def("e_f", "$i", "($i>$i)") <> extensional_def("e_i", "$i", "$i"),
           "![F:($i>($i>$i)), G:($i>($i>$i))]: " <>
             "((e_f @ F @ G) => (![X:$i]: (e_i @ (F @ X) @ (G @ X))))"}
        ]

    for {variant, defs, conj} <- specs do
      problem("fun_ext_trivial_#{variant}", section, variant, "THM", defs, conj)
    end
  end

  defp boolean_extensionality do
    section = "Example 9b (Boolean extensionality, trivial direction)"

    specs =
      [{"prim", "", "![A:$o, B:$o]: ((A = B) => (A <=> B))"}] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$o", conn), "![A:$o, B:$o]: ((l @ A @ B) => (A <=> B))"}
        end ++
        [
          {"andrews", andrews_def("a", "$o"), "![A:$o, B:$o]: ((a @ A @ B) => (A <=> B))"},
          {"extensional", extensional_def("e", "$o", "$o"),
           "![A:($o>$o), B:($o>$o)]: ((e @ A @ B) => " <>
             "(((A @ $true) <=> (B @ $true)) & ((A @ $false) <=> (B @ $false))))"}
        ]

    for {variant, defs, conj} <- specs do
      problem("bool_ext_trivial_#{variant}", section, variant, "THM", defs, conj)
    end
  end

  defp boolean_extensionality_hard do
    section = "Example 10 (Boolean extensionality, non-trivial direction)"

    specs =
      [{"prim", "", "![A:$o, B:$o]: ((A <=> B) => (A = B))"}] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$o", conn), "![A:$o, B:$o]: ((A <=> B) => (l @ A @ B))"}
        end ++
        [
          {"andrews", andrews_def("a", "$o"), "![A:$o, B:$o]: ((A <=> B) => (a @ A @ B))"},
          {"extensional", extensional_def("e", "$o", "$o"),
           "![A:($o>$o), B:($o>$o)]: " <>
             "((((A @ $true) <=> (B @ $true)) & ((A @ $false) <=> (B @ $false))) => " <>
             "(e @ A @ B))"}
        ]

    for {variant, defs, conj} <- specs do
      problem("bool_ext_hard_#{variant}", section, variant, "THM", defs, conj)
    end
  end

  ##############################################################################
  # EXAMPLES 12-14 (ETA / IDENTITY EXTENSIONS)
  ##############################################################################

  defp eta_expansion do
    [
      problem(
        "eta_expanded_extension",
        "Example 12 (Eta-expanded extension)",
        "primitive",
        "THM",
        "thf(f_t, type, f: $i>$i).\nthf(p_t, type, p: ($i>$i)>$o).\n",
        "(p @ (^[X:$i]: (f @ X))) => (p @ f)"
      )
    ]
  end

  # Examples 13 and 14 share their hypothesis and differ only in the
  # conclusion: eta-expanded `p @ (^[X]: f @ X)` vs. bare `p @ f`.
  defp identity_extension_specs do
    base = "thf(f_t, type, f: $i>$i).\nthf(p_t, type, p: ($i>$i)>$o).\n"
    ext = "thf(f_t, type, f: ($i>$i)>$i>$i).\nthf(p_t, type, p: (($i>$i)>$i>$i)>$o).\n"

    [
      {"prim", base, "![X:$i]: ((f @ X) = X)", "^[X:$i]: X", "^[X:$i]: (f @ X)", "$i"}
    ] ++
      for {variant, conn} <- @leibniz do
        {variant, leibniz_def("l", "$i", conn) <> base, "![X:$i]: (l @ (f @ X) @ X)",
         "^[X:$i]: X", "^[X:$i]: (f @ X)", "$i"}
      end ++
      [
        {"andrews", andrews_def("a", "$i") <> base, "![X:$i]: (a @ (f @ X) @ X)", "^[X:$i]: X",
         "^[X:$i]: (f @ X)", "$i"},
        {"extensional", extensional_def("e", "$i", "$i") <> ext,
         "![X:($i>$i)]: (e @ (f @ X) @ X)", "^[X:($i>$i)]: X", "^[X:($i>$i)]: (f @ X)", "($i>$i)"}
      ]
  end

  defp extension_with_identity do
    section = "Example 13 (Extension with identity)"

    for {variant, defs, hyp, id_lambda, eta_lambda, _tau} <- identity_extension_specs() do
      problem(
        "ext_with_identity_#{variant}",
        section,
        variant,
        "Timeout",
        defs,
        "((#{hyp}) & (p @ (#{id_lambda}))) => (p @ (#{eta_lambda}))"
      )
    end
  end

  defp extension_of_identity do
    section = "Example 14 (Extension of identity)"

    for {variant, defs, hyp, id_lambda, _eta_lambda, _tau} <- identity_extension_specs() do
      problem(
        "ext_of_identity_#{variant}",
        section,
        variant,
        "Timeout",
        defs,
        "((#{hyp}) & (p @ (#{id_lambda}))) => (p @ f)"
      )
    end
  end

  ##############################################################################
  # EXAMPLES 15-19
  ##############################################################################

  defp commutativity_extension do
    section = "Example 15 (Extensionality under commutativity)"
    preamble = "thf(a_t, type, a: $o).\nthf(b_t, type, b: $o).\nthf(p_t, type, p: $o>$o).\n"

    [
      problem(
        "comm_ext_argument",
        section,
        "primitive",
        "THM",
        preamble,
        "(p @ (a & b)) => (p @ (b & a))"
      ),
      problem(
        "comm_ext_hypothesis",
        section,
        "primitive",
        "THM",
        preamble,
        "((a & b) & (p @ a)) => (p @ b)"
      )
    ]
  end

  defp conjunction_extension do
    [
      problem(
        "conj_ext",
        "Example 16 (Extensionality for conjunctions)",
        "primitive",
        "THM",
        "thf(a_t, type, a: $o).\nthf(b_t, type, b: $o).\nthf(p_t, type, p: $o>$o).\n",
        "((p @ a) & (p @ b)) => (p @ (a & b))"
      )
    ]
  end

  defp self_negation do
    [
      problem(
        "self_negation_unequal",
        "Example 17 (Unequality of self-negation)",
        "primitive",
        "THM",
        "thf(a_t, type, a: $o).\n",
        "~ (a = (~ a))"
      )
    ]
  end

  defp nested_boolean_argument do
    section = "Example 18 (Nested boolean argument)"
    h_i = "thf(h_t, type, h: $o>$i).\n"
    h_f = "thf(h_t, type, h: $o>($i>$i)).\n"

    specs =
      [
        {"prim", h_i, "(h @ ((h @ $true) = (h @ $false))) = (h @ $false)", "THM"}
      ] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$i", conn) <> h_i,
           "l @ (h @ (l @ (h @ $true) @ (h @ $false))) @ (h @ $false)", "THM"}
        end ++
        [
          {"andrews", andrews_def("a", "$i") <> h_i,
           "a @ (h @ (a @ (h @ $true) @ (h @ $false))) @ (h @ $false)", "Timeout"},
          {"extensional", extensional_def("e", "$i", "$i") <> h_f,
           "e @ (h @ (e @ (h @ $true) @ (h @ $false))) @ (h @ $false)", "THM"}
        ]

    for {variant, defs, conj, note} <- specs do
      problem("nested_bool_#{variant}", section, variant, note, defs, conj)
    end
  end

  defp lambda_normalisation do
    preamble = """
    thf(p_t, type, p: ($i>$i)>$o).
    thf(f_t, type, f: $o>$i>$i).
    thf(a_t, type, a: ($i>$i)>$o).
    thf(b_t, type, b: $o).
    """

    [
      problem(
        "lambda_normalisation",
        "Example 19 (Normalisation under lambda)",
        "primitive",
        "THM",
        preamble,
        "(p @ (^[X:$i]: (f @ ((a @ (^[Y:$i]: (f @ b @ Y))) & b) @ X))) => " <>
          "(p @ (f @ (b & (a @ (f @ b)))))"
      )
    ]
  end

  ##############################################################################
  # EXAMPLE 20 (DE MORGAN)
  ##############################################################################

  defp de_morgan do
    de_morgan_a() ++ de_morgan_b() ++ de_morgan_c() ++ de_morgan_d()
  end

  defp de_morgan_a do
    [
      problem(
        "de_morgan_iff",
        "Example 20a (De Morgan, equivalence)",
        "primitive",
        "THM",
        "",
        "![X:$o, Y:$o]: ((X & Y) <=> (~ ((~ X) | (~ Y))))"
      )
    ]
  end

  defp de_morgan_b do
    section = "Example 20b (De Morgan, boolean equality)"

    specs =
      [{"prim", "", "![X:$o, Y:$o]: ((X & Y) = (~ ((~ X) | (~ Y))))"}] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", "$o", conn),
           "![X:$o, Y:$o]: (l @ (X & Y) @ (~ ((~ X) | (~ Y))))"}
        end ++
        [
          {"andrews", andrews_def("a", "$o"),
           "![X:$o, Y:$o]: (a @ (X & Y) @ (~ ((~ X) | (~ Y))))"}
        ]

    for {variant, defs, conj} <- specs do
      problem("de_morgan_bool_#{variant}", section, variant, "THM", defs, conj)
    end
  end

  @de_morgan_lambda "^[X:$o, Y:$o]: (~ ((~ X) | (~ Y)))"
  @conj_lambda "^[U:$o, V:$o]: (U & V)"
  @bool_bin "($o>$o>$o)"

  defp de_morgan_c do
    section = "Example 20c (De Morgan, lambda equality)"

    specs =
      [{"prim", "", "(#{@conj_lambda}) = (#{@de_morgan_lambda})", "THM"}] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", @bool_bin, conn),
           "l @ (#{@conj_lambda}) @ (#{@de_morgan_lambda})", "Timeout"}
        end ++
        [
          {"andrews", andrews_def("a", @bool_bin),
           "a @ (#{@conj_lambda}) @ (#{@de_morgan_lambda})", "Timeout"},
          {"extensional", extensional_def("e", "$o", "($o>$o)"),
           "e @ (#{@conj_lambda}) @ (#{@de_morgan_lambda})", "Timeout"}
        ]

    for {variant, defs, conj, note} <- specs do
      problem("de_morgan_lambda_#{variant}", section, variant, note, defs, conj)
    end
  end

  defp de_morgan_d do
    section = "Example 20d (De Morgan, connective equality)"

    specs =
      [{"prim", "", "(&) = (#{@de_morgan_lambda})", "THM"}] ++
        for {variant, conn} <- @leibniz do
          {variant, leibniz_def("l", @bool_bin, conn), "l @ (&) @ (#{@de_morgan_lambda})",
           "Timeout"}
        end ++
        [
          {"andrews", andrews_def("a", @bool_bin), "a @ (&) @ (#{@de_morgan_lambda})", "Timeout"},
          {"extensional", extensional_def("e", "$o", "($o>$o)"),
           "e @ (&) @ (#{@de_morgan_lambda})", "Timeout"}
        ]

    for {variant, defs, conj, note} <- specs do
      problem("de_morgan_conn_#{variant}", section, variant, note, defs, conj)
    end
  end

  ##############################################################################
  # EXAMPLE 21 (FINITE DOMAIN)
  ##############################################################################

  defp finite_domain do
    [
      problem(
        "finite_domain_oo",
        "Example 21 (Finite domain of $o>$o)",
        "primitive",
        "THM",
        "thf(p_t, type, p: ($o>$o)>$o).\n",
        "((p @ (^[X:$o]: X)) & (p @ (^[X:$o]: (~ X))) & " <>
          "(p @ (^[X:$o]: $false)) & (p @ (^[X:$o]: $true))) => (![Y:($o>$o)]: (p @ Y))"
      )
    ]
  end

  ##############################################################################
  # EXAMPLE 22 (SET THEORY)
  ##############################################################################

  # Types and definitions from the livebook's `set_theory` block, with each
  # definition bound to its own head (the livebook defines `set_l1` and
  # `set_set_l1` three times each).
  defp set_theory_preamble do
    """
    thf(elem_t, type, elem: $i>($i>$o)>$o).
    thf(set_t, type, set: $i>$i>$o).
    thf(set_l1_t, type, set_l1: $i>$i>$o).
    thf(set_l2_t, type, set_l2: $i>$i>$o).
    thf(set_l3_t, type, set_l3: $i>$i>$o).
    thf(set_a_t, type, set_a: $i>$i>$o).
    thf(set_set_t, type, set_set: ($i>$o)>($i>$o)>$o).
    thf(set_set_l1_t, type, set_set_l1: ($i>$o)>($i>$o)>$o).
    thf(set_set_l2_t, type, set_set_l2: ($i>$o)>($i>$o)>$o).
    thf(set_set_l3_t, type, set_set_l3: ($i>$o)>($i>$o)>$o).
    thf(set_set_a_t, type, set_set_a: ($i>$o)>($i>$o)>$o).
    thf(set_set_e_t, type, set_set_e: ($i>$o)>($i>$o)>$o).
    thf(null_t, type, null: $i>$o).
    thf(inter_t, type, inter: ($i>$o)>($i>$o)>$i>$o).
    thf(union_t, type, union: ($i>$o)>($i>$o)>$i>$o).
    thf(subset_t, type, subset: ($i>$o)>($i>$o)>$o).
    thf(powerset_t, type, powerset: ($i>$o)>($i>$o)>$o).
    thf(elem_def, definition, elem = (^[X:$i, S:($i>$o)]: (S @ X))).
    thf(set_def, definition, set = (^[X:$i, Y:$i]: (X = Y))).
    thf(set_l1_def, definition,
      set_l1 = (^[X:$i, Y:$i]: (![P:($i>$o)]: ((P @ X) => (P @ Y))))).
    thf(set_l2_def, definition,
      set_l2 = (^[X:$i, Y:$i]: (![P:($i>$o)]: ((P @ X) <= (P @ Y))))).
    thf(set_l3_def, definition,
      set_l3 = (^[X:$i, Y:$i]: (![P:($i>$o)]: ((P @ X) <=> (P @ Y))))).
    thf(set_a_def, definition,
      set_a = (^[X:$i, Y:$i]:
        (![Q:($i>$i>$o)]: ((![Z:$i]: (Q @ Z @ Z)) => (Q @ X @ Y))))).
    thf(set_set_def, definition, set_set = (^[X:($i>$o), Y:($i>$o)]: (X = Y))).
    thf(set_set_l1_def, definition,
      set_set_l1 = (^[X:($i>$o), Y:($i>$o)]:
        (![P:(($i>$o)>$o)]: ((P @ X) => (P @ Y))))).
    thf(set_set_l2_def, definition,
      set_set_l2 = (^[X:($i>$o), Y:($i>$o)]:
        (![P:(($i>$o)>$o)]: ((P @ X) <= (P @ Y))))).
    thf(set_set_l3_def, definition,
      set_set_l3 = (^[X:($i>$o), Y:($i>$o)]:
        (![P:(($i>$o)>$o)]: ((P @ X) <=> (P @ Y))))).
    thf(set_set_a_def, definition,
      set_set_a = (^[X:($i>$o), Y:($i>$o)]:
        (![Q:(($i>$o)>($i>$o)>$o)]: ((![Z:($i>$o)]: (Q @ Z @ Z)) => (Q @ X @ Y))))).
    thf(set_set_e_def, definition,
      set_set_e = (^[X:($i>$o), Y:($i>$o)]: (![Z:$i]: ((X @ Z) = (Y @ Z))))).
    thf(null_def, definition, null = (^[Z:$i]: $false)).
    thf(inter_def, definition,
      inter = (^[X:($i>$o), Y:($i>$o), Z:$i]: ((elem @ Z @ X) & (elem @ Z @ Y)))).
    thf(union_def, definition,
      union = (^[X:($i>$o), Y:($i>$o), Z:$i]: ((elem @ Z @ X) | (elem @ Z @ Y)))).
    thf(subset_def, definition,
      subset = (^[X:($i>$o), Y:($i>$o)]: (![Z:$i]: ((elem @ Z @ X) => (elem @ Z @ Y))))).
    thf(powerset_def, definition,
      powerset = (^[X:($i>$o), Y:($i>$o)]: (subset @ Y @ X))).
    """
  end

  defp set_theory do
    set_distributivity() ++ set_powerset_of_empty()
  end

  defp set_distributivity do
    section = "Example 22a (Set theory, distributivity)"

    sets =
      "thf(sa_t, type, sa: $i>$o).\nthf(sb_t, type, sb: $i>$o).\nthf(sc_t, type, sc: $i>$o).\n"

    preamble = set_theory_preamble() <> sets
    lhs = "(union @ sa @ (inter @ sb @ sc))"
    rhs = "(inter @ (union @ sa @ sb) @ (union @ sa @ sc))"

    specs =
      [{"prim", preamble, "#{lhs} = #{rhs}"}] ++
        for {variant, conn} <- @leibniz do
          {variant, preamble <> leibniz_def("l", "($i>$o)", conn), "l @ #{lhs} @ #{rhs}"}
        end ++
        [
          {"andrews", preamble <> andrews_def("a", "($i>$o)"), "a @ #{lhs} @ #{rhs}"},
          {"extensional", preamble <> extensional_def("e", "$i", "$o"), "e @ #{lhs} @ #{rhs}"}
        ]

    for {variant, defs, conj} <- specs do
      problem("set_distributivity_#{variant}", section, variant, "Timeout", defs, conj)
    end
  end

  defp set_powerset_of_empty do
    section = "Example 22b (Set theory, powerset of the empty set)"
    preamble = set_theory_preamble()
    pow = "(powerset @ null)"
    set_of_sets = "(($i>$o)>$o)"

    specs =
      [{"prim", preamble, "#{pow} = (set_set @ null)", "THM"}] ++
        for {{variant, conn}, head} <- Enum.zip(@leibniz, ~w(set_set_l1 set_set_l2 set_set_l3)) do
          {variant, preamble <> leibniz_def("l", set_of_sets, conn),
           "l @ #{pow} @ (#{head} @ null)", "Timeout"}
        end ++
        [
          {"andrews", preamble <> andrews_def("a", set_of_sets),
           "a @ #{pow} @ (set_set_a @ null)", "Timeout"},
          {"extensional", preamble <> extensional_def("e", "($i>$o)", "$o"),
           "e @ #{pow} @ (set_set_e @ null)", "Timeout"}
        ]

    for {variant, defs, conj, note} <- specs do
      problem("set_powerset_empty_#{variant}", section, variant, note, defs, conj)
    end
  end

  ##############################################################################
  # EXAMPLES 23-29 (PROPOSITIONAL WITNESSES)
  ##############################################################################

  defp propositional_witnesses do
    example_26 =
      ([{"prim", "", "~ (![F:($o>$o)]: (?[X:$o]: ((F @ X) = X)))"}] ++
         for {variant, conn} <- @leibniz do
           {variant, leibniz_def("l", "$o", conn),
            "~ (![F:($o>$o)]: (?[X:$o]: (l @ (F @ X) @ X)))"}
         end ++
         [{"andrews", andrews_def("a", "$o"), "~ (![F:($o>$o)]: (?[X:$o]: (a @ (F @ X) @ X)))"}])
      |> Enum.map(fn {variant, defs, conj} ->
        note = if variant == "andrews", do: "Timeout", else: "THM"

        problem(
          "no_bool_fixpoint_#{variant}",
          "Example 26 (No boolean fixed point)",
          variant,
          note,
          defs,
          conj
        )
      end)

    [
      problem("exists_true_prop", "Example 23", "primitive", "THM", "", "?[P:$o]: P"),
      problem("not_all_props", "Example 24", "primitive", "THM", "", "~ (![P:$o]: P)"),
      problem(
        "negation_exists",
        "Example 25",
        "primitive",
        "THM",
        "",
        "?[N:($o>$o)]: (![P:$o]: ((N @ P) <=> (~ P)))"
      )
    ] ++
      example_26 ++
      [
        problem(
          "disjunction_exists",
          "Example 27",
          "primitive",
          "THM",
          "",
          "?[D:($o>$o>$o)]: (![P:$o, Q:$o]: ((D @ P @ Q) <=> (P | Q)))"
        ),
        problem(
          "universal_quantifier_exists",
          "Example 28",
          "primitive",
          "Timeout",
          "",
          "?[Q:(($i>$o)>$o)]: (![P:($i>$o)]: ((Q @ P) <=> (![X:$i]: (P @ X))))"
        ),
        problem(
          "identity_predicate_exists",
          "Example 29",
          "primitive",
          "THM",
          "",
          "?[N:($o>$o)]: (![P:$o]: ((N @ P) <=> P))"
        )
      ]
  end

  ##############################################################################
  # CANTOR
  ##############################################################################

  defp cantor do
    [
      problem(
        "cantor_surjective",
        "Cantor (surjective)",
        "primitive",
        "THM",
        "",
        "~ (?[G:($i>$i>$o)]: (![F:($i>$o)]: (?[J:$i]: ((G @ J) = F))))"
      ),
      problem(
        "cantor_injective",
        "Cantor (injective)",
        "primitive",
        "Timeout",
        "",
        "~ (?[H:(($i>$o)>$i)]: " <>
          "(![P:($i>$o), Q:($i>$o)]: (((H @ P) = (H @ Q)) => (P = Q))))"
      )
    ]
  end
end
