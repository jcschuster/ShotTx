# Evaluation on the Structured Set of Higher-order Problems

**Date:** 2026-08-09 · **Prover:** ShotTx 0.0.3 · **Configuration:** `%ShotTx.Data.Parameters{}` (shipped defaults, `timeout: 5_000`)

ShotTx was evaluated on the 130 higher-order problems in
`examples/structured_hol_problems.livemd` and contrasted with Vampire, E,
Zipperposition, Leo-III and Satallax via SystemOnTPTP.

ShotTx proves **76 of 130 problems on every run and 79 on the measured run**,
produces no unsound answers, and **every verdict agrees with the reference
provers** — 79 agreements, zero disagreements, over all 130 problems submitted.

Reference consensus rates 122 of the 130 problems `Theorem`, so ShotTx decides
roughly two thirds of what the reference set can decide. The remaining eight
are decided by nobody, ShotTx and reference provers alike.

---

## 1. Method

### The suite

`ShotTx.Benchmark.HolSuite` normalises the livebook's problems — stated
variously as `~f` formulas, `~e`/`with_context` pairs and `~p` TPTP problems —
into 130 self-contained THF problems. Both ShotTx and SystemOnTPTP receive
byte-identical text.

Two deliberate deviations from the livebook source:

| Deviation | Reason |
| --- | --- |
| Equality-like relations declared at concrete types | The livebook writes `l: A > A > $o`. Rank-1 polymorphism is TH1, which Satallax and E reject. Where one polymorphic constant is applied at two types, the suite declares two monomorphic copies (`l_f`, `l_i`). |
| `set_theory_defs` typo corrected | The livebook binds `set_l1` three times and never defines `set_l2`, `set_l3`, `set_set_l2` or `set_set_l3`, leaving the Example 22 Leibniz variants referring to undefined constants. Each definition now binds its own head. |

Definition bodies are parenthesised throughout: Leo-III and Satallax reject a
bare lambda on the right of `=`.

### Isolation

Each problem runs in a **fresh BEAM**. This is not timing hygiene alone:
ShotTx carries state across proof sessions, so a problem's verdict in a shared
node can depend on what ran before it. A single-node sweep does not measure the
prover; it measures the prover plus its history. Timings are taken after a
warm-up proof so no problem is charged for module loading.

### Repetition

The suite was run three times at identical settings. This is not a refinement
of the timing — it changes what the headline number means, so §2 reports the
stable core and the single-run figure separately.

### Reference provers

All five systems run on the same SystemOnTPTP machine with a 10 s limit each,
reached through the ATP MCP tooling (`compare_provers`). All 130 problems were
submitted, so the ones ShotTx does not solve carry reference ground truth too.

| System | Version |
| --- | --- |
| Vampire | 5.0.1 |
| E | 3.5.1 |
| Zipperposition | Zipperpin 2.1 |
| Leo-III | 1.8.0 |
| Satallax | 3.5 |

Two runtimes are recorded per prover. `wc_s` is SystemOnTPTP's own measurement
of the prover process and **includes process launch** — around 60 ms for
Vampire and E, over a second of JVM start for Leo-III. `self_s` is the time
the prover reports for the solve itself. ShotTx's figure is measured inside an
already-running BEAM, so `self_s` is the like-for-like comparison and the
stricter test; both are reported.

---

## 2. Results

### ShotTx over all 130 problems

| Verdict | run 1 | run 2 | run 3 | Meaning |
| --- | ---: | ---: | ---: | --- |
| `thm` | **79** | 81 | 78 | Proved. Every one confirmed by the reference provers. |
| `timeout` | 48 | 46 | 49 | 5 s deadline reached. |
| `unk` | 3 | 3 | 3 | Rules exhausted without deciding satisfiability. |
| `hard_timeout` | 0 | 0 | 0 | Harness safety net at 70 s — not reached. |
| `csa` | **0** | 0 | 0 | — |

Aggregated over the three runs:

| | Count |
| --- | ---: |
| Proved on **every** run | **76** |
| Proved on some run but not all | 6 |
| Never proved | 48 (45 `timeout`, 3 `unk`) |

Solve times over the stable 76 (run 1): min 2 ms, **median 34 ms**, p90 133 ms,
max 4657 ms.

No branch raised during any run: a sweep over all 130 problems reading the
`branches_errored` counter reports zero, so no verdict above is a crash in
disguise.

### The six that flip are bimodal, not borderline

The obvious reading of a ±3 spread is that some proofs land either side of the
5 s deadline. That is not what the data shows:

| Problem | run 1 | run 2 | run 3 |
| --- | ---: | ---: | ---: |
| `nested_bool_leibniz_iff` | **40 ms** | **33 ms** | timeout |
| `de_morgan_conn_leibniz_rev_imp` | timeout | timeout | **147 ms** |
| `de_morgan_conn_leibniz_imp` | **4905 ms** | **138 ms** | timeout |
| `de_morgan_lambda_leibniz_imp` | timeout | **160 ms** | timeout |
| `de_morgan_conn_extensional` | **970 ms** | **732 ms** | timeout |
| `trans_leibniz_rev_imp` | timeout | **4548 ms** | **4663 ms** |

A problem that closes in 33 ms on one run and exhausts 5 s on the next is not
losing a race against the clock. Proof search is distributed over a worker pool
reading a shared queue, so which worker picks up which branch decides whether
the productive prim-subst instance is tried early or after a long detour. The
distribution is bimodal — tens of milliseconds, or never.

Only `trans_leibniz_rev_imp` (4.5–6.1 s) is genuinely deadline-bound. Raising
`timeout` would recover that one and none of the other five; those need a
better branch-selection heuristic, not more time.

### Where the remaining failures sit

Counts are *stable* solves — proved on all three runs; a parenthesised figure
is the best single run.

| Section | Solved |
| --- | --- |
| Reflexivity, commutativity, Boolean extensionality (both directions), De Morgan (equivalence/boolean), no-boolean-fixpoint, Choice, Cantor (surjective) | all |
| Congruence under endomorphisms / predicates (Examples 7a, 7b) | 5 of 6 · 4 of 6 |
| Functional extensionality, trivial direction (Example 9a) | 4 of 6 |
| De Morgan, lambda equality (Example 20c) | 2 of 6 (3) |
| De Morgan, connective equality (Example 20d) | 1 of 6 (4) |
| Set theory (Examples 22a, 22b) | 2 of 6 each |
| Leibniz and primitive equality (Example 8) | 1 of 3 |
| Transitivity (Example 6c) | 1 of 6 (2) |
| Extension with/of identity (Examples 13, 14) | 0 of 12 |
| Normalisation under lambda (19), Cantor (injective), Example 28 | 0 of 1 each |
| Non-theorems | 0 of 8 — all time out rather than producing a countermodel |

---

## 3. Comparison with the reference provers

| ShotTx | Reference consensus | Agrees | Count |
| --- | --- | --- | ---: |
| `thm` | Theorem | **yes** | 79 |
| `timeout` | Theorem | n/a | 40 |
| `unk` | Theorem | n/a | 3 |
| `timeout` | Unknown | n/a | 8 |

**Zero disagreements.** Every problem ShotTx proves, the reference set proves.

The 8 `Unknown` rows are exactly the designated non-theorems — and **no
reference prover returns `CounterSatisfiable` on any of them either**. Nobody
on the panel refutes them, so ShotTx's timeout is the same non-answer every
other system gives rather than a shortfall against the field.

That leaves 122 problems with a confirmed `Theorem` consensus, of which ShotTx
proves 79 (65%).

### Coverage over all 130

| Prover | Definite | Theorem | GaveUp | Timeout | Unknown |
| --- | ---: | ---: | ---: | ---: | ---: |
| Vampire | 121 | 121 | — | 9 | — |
| Leo-III | 120 | 120 | 6 | 4 | — |
| Satallax | 118 | 118 | — | — | 12 |
| E | 116 | 116 | 12 | 2 | — |
| Zipperposition | 112 | 112 | — | 6 | 12 |
| **ShotTx** | **79** | 79 | — | 48 | 3 |

### Coverage over the 79 ShotTx proved

| Prover | Theorem | Timeout | Unknown |
| --- | ---: | ---: | ---: |
| Vampire | 79 | — | — |
| Leo-III | 79 | — | — |
| E | 78 | 1 | — |
| Satallax | 77 | — | 2 |
| Zipperposition | 76 | 3 | — |

Vampire and Leo-III each prove every one. ShotTx solves nothing here that the
reference set does not.

### Median self-reported solve time, over those 79

| Prover | Median | Max |
| --- | ---: | ---: |
| E | 0.012 s | 4.197 s |
| Zipperposition | 0.013 s | 1.411 s |
| Vampire | 0.024 s | 0.116 s |
| **ShotTx** | **0.035 s** | 4.905 s |
| Leo-III | 1.374 s | 2.486 s |
| Satallax | reports no time | — |

---

## 4. Is ShotTx faster on anything?

**Yes — on 14 of the 79, measured startup-free.**

Against the best reference prover's own reported solve time:

| Problem | ShotTx | Best reference |
| --- | ---: | --- |
| `refl_prim` | 0.002 s | Zipperposition 0.007 s |
| `de_morgan_conn_prim` | 0.003 s | Zipperposition 0.008 s |
| `exists_true_prop` | 0.003 s | Zipperposition 0.005 s |
| `not_all_props` | 0.003 s | Zipperposition 0.005 s |
| `refl_leibniz_rev_imp` | 0.004 s | Zipperposition 0.006 s |
| `eta_expanded_extension` | 0.004 s | E 0.010 s |
| `comm_ext_argument` | 0.004 s | E 0.011 s |
| `de_morgan_iff` | 0.004 s | Zipperposition 0.008 s |
| `de_morgan_bool_prim` | 0.004 s | E 0.008 s |
| `de_morgan_lambda_prim` | 0.004 s | Zipperposition 0.008 s |
| `refl_leibniz_imp` | 0.005 s | Zipperposition 0.006 s |
| `refl_leibniz_iff` | 0.005 s | Zipperposition 0.006 s |
| `negation_exists` | 0.007 s | E 0.016 s |
| `identity_predicate_exists` | 0.007 s | E 0.016 s |

Against wall clock including process launch, ShotTx wins 37 of 79 — but 24 of
those wins are against Satallax's startup, which says more about process launch
than about search. The startup-free number is the honest one.

Overall ShotTx is **2.7× slower than the best reference prover at the median**
(p90 43×, worst 388×). The wins share a shape: small, purely propositional or
reflexivity-style goals that close in a handful of rule applications, where the
tableau reaches a contradiction directly and a saturation-based prover pays for
clausification it does not need.

**Caveat.** Different hardware, and ShotTx's figure excludes BEAM startup while
the reference `wc_s` includes process launch. Treat differences under roughly
2× as noise; the signal is order of magnitude and which problems each side
solves at all.

---

## 5. Known limitations

### The `timeout` parameter is a soft deadline

Median wall clock on a 5 s timeout is 5.6 s, with a tail to 6.8 s. Nothing
reaches the 70 s harness safety net.

### No countermodels on this suite

All eight designated non-theorems time out. `Branch.model_certain?/2` requires
every same-head, opposite-polarity literal pair to be separated at some
argument position by two distinct rigid base-type terms — what a free term
model can interpret as distinct elements — and otherwise reports the branch
*exhausted* rather than satisfiable. That deliberately trades countermodel
coverage for soundness. Recovering it needs an extensionality decision
procedure, not a looser saturation test. Genuine countermodels are still
available: `p a` against `¬(p b)` for distinct base constants qualifies.

### Extensionality is not applied inside atoms

The three `unk` results — `set_powerset_empty_leibniz_imp`, `..._rev_imp`,
`..._iff` — are stable across runs, crash-free, and confirmed theorems by the
reference set. All three halt on a branch holding

```
   C (λT. ∀x. ¬(T x))          ≡    C (powerset ∅)
  ¬(C (λT. ∀P. P ∅ ⊃ P T))     ≡   ¬(C {∅})
```

with `C` the δ-Skolem of the Leibniz `∀P`. Same rigid head, opposite polarity,
and arguments that denote the same set but do not unify — `ShotUn.unify`
returns no solution.

The calculus expands extensionality only for formulas that *already are*
equalities, so nothing turns a rigid-head atom pair into the goal
`⋁ᵢ sᵢ ≠ tᵢ`. The `prim` (56 ms) and `extensional` (58 ms) siblings of the same
theorem succeed precisely because they state the equality in the conjecture.
Relaxing the `:rename` rule's type gate does not close them — the verdict moves
from `unk` to `timeout`, because renaming both sides mints two *distinct* fresh
constants and the atoms still fail to clash. What is missing is a rule, not a
looser guard.

### Branch selection is unordered

Six problems (§2) are proved on some runs and not others, in tens of
milliseconds or not at all. The shared work queue imposes no preference over
which open branch a free worker picks up.

### A restarted worker resumes with the round's *initial* limits

Gamma and prim-subst limits are re-read at round start rather than from the
current round. This can only cost convergence speed, never correctness.

---

## 6. Reproducing

### ShotTx

```bash
# Over the suite — one fresh BEAM per problem, resumable
scripts/run_hol_benchmark.sh [bench_results/hol_suite.csv]

# One problem, for debugging
mix run scripts/hol_problem.exs bool_ext_trivial_prim
mix run scripts/hol_problem.exs --list
```

`TIMEOUT_MS` overrides the per-problem timeout. The sweep resumes: rows already
present are skipped, and a `STOP` sentinel in the output directory halts it at
the next problem boundary.

Three runs produced §2; `bench_results/hol_suite.csv` is run 1. §2's stable-solve
and bimodality figures need all three, so write each run to its own path.

### Reference provers

The repository carries no SystemOnTPTP client. Problem text comes from
`ShotTx.Benchmark.HolSuite.fetch/1` (the `:thf` field) and goes to the ATP MCP
tooling — `compare_provers`, with `time_limit_sec: 10` and

`Vampire---5.0.1` · `E---3.5.1` · `Zipperpin---2.1` · `Leo-III---1.8.0` ·
`Satallax---3.5`

which returns the five SZS verdicts side by side. §3 aggregates one such
submission per problem over all 130.

### Outputs

`bench_results/` is git-ignored: it is local measurement output, and the
figures worth keeping are recorded in this report. Nothing in the repository
reproduces a past run's numbers — a fresh sweep re-measures, and §2 is the
reason to expect it to differ by a few problems.

### Code

| Module | Role |
| --- | --- |
| `ShotTx.Benchmark.HolSuite` | The 130 problems as canonical THF |
| `ShotTx.Benchmark.HolRunner` | Evaluates one problem, renders a CSV row |
