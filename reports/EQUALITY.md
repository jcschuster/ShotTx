# Equality in Shot: A Roadmap Toward Superposition

This document tracks ideas — beyond the first cost-splitting step that just
landed — for making Shot's equality handling more competitive on the
first-order fragment, drawing inspiration from superposition calculi.

It is a research/design note, not an implementation specification. Each
section sketches a direction, the cost/benefit, and the dependencies on
earlier work.

## 0. Where things stand

Equality decomposition used to be a single `{:alpha, [...]}` rule with
cost 2. As of the change accompanying this report it splits into

    {:equality_expansion, kind, [formula]}
    kind ∈ {:iff_o, :extensional, :leibniz}

with per-kind defaults of `2 / 10 / 15` resolved by
`ShotTx.Prover.Rules.rule_cost/1` and overridable through
`rule_cost/2`:

    formula_cost: &ShotTx.Prover.Rules.rule_cost(&1, %{leibniz: 100})

The Leibniz expansion is now substantially deferred behind γ and β so
**paramodulation** — which already runs eagerly at ingestion time, before
any expansion fires — has first crack at closing equational goals on the
FO fragment.

### The trade-off this exposes

Lifting Leibniz from cost 2 to cost 15 cleanly defers it behind cheaper
machinery, but it does *not* eliminate the cases where Leibniz is the
only way forward. The motivating example is

    ∀X Y F. X = Y → F(X) = F(Y)         (congruence under endomorphisms)

After γ + δ we have the positive equation `x = y` and the negated
equation `¬(f(x) = f(y))`. Paramodulation indexes `x = y` as a rewrite
rule, but it has nothing to apply it to: the only candidate, `f(x) =
f(y)`, lives *inside a negated equality*, which is not in `branch.literals`.
The atomic literals that paramodulation can rewrite only appear after
Leibniz expands `¬(f(x) = f(y))` into `P(f(x)) ∧ ¬P(f(y))` (modulo δ on
the existential `P`). Pushing the Leibniz cost much past ~20 starts to
time this kind of problem out within a 5 s budget.

That observation is what motivates the rest of this document. Most of
the suggestions below either give paramodulation a direct hook on
negative equalities (so Leibniz really *can* be set aside) or tighten
the equational machinery so the saved budget pays off.

## 1. Iterative-deepening on the Leibniz cost

**Idea.** Re-use the γ iterative-deepening counter (or carry a separate
`equality_limit`) to make the Leibniz cost grow per round: cheap on the
first sweep, prohibitive on later sweeps unless explicitly raised.

**Why.** Iterative deepening already gates γ instantiation and prim-subst
depth. Tying Leibniz cost to the same dial preserves the user's intuition
that "deeper" rounds search a wider space, and gives paramodulation an
inner loop in which to close before Leibniz is unleashed.

**Sketch.** Either store the current iteration counter in the rule tuple
(analogous to `{:gamma, _, _, c}` carrying its `prev` field) or thread
`gamma_limit` into `formula_cost` callsites and let the cost function
read it. The first is cleaner.

**Size.** Small. The plumbing for iterative deepening already exists.
**Dependencies.** None.

## 2. Negative equations as paramodulation participants

**Idea.** Treat `¬(s = t)` as a first-class branch literal: store it
alongside `branch.literals` (or in a sibling map) so paramodulation can
rewrite either side. When rewriting reduces it to `¬(u = u)`, close the
branch by `:contradiction` via the existing reflexivity path.

**Why.** This is the conceptual core of why superposition is effective on
FO equality. It also unblocks pushing Leibniz cost much higher (50+ or
disabled-by-default) without sacrificing problems like congruence under
endomorphisms. Without (2), high Leibniz cost is a footgun on FO.

**Sketch.** Add a new branch field `negative_equations: MapSet.t()` (or
generalize `literals`). In `Rules`, classify `¬(s = t)` as a new
`{:negative_equation, ...}` rule that, when popped, registers the literal
without expanding. In `Branch.ingest_formula`, paramodulate every known
positive equation against the negative equation's two sides; when a
paramodulant yields `¬(u = u)` set `pending_closure` and fire
`:contradiction`. Mirror the existing eager paramodulation pathway.

**Care points.**
- Soundness: positive paramodulation against a negative equation is
  sound but completeness requires both directions (the standard
  superposition restriction on selected literals).
- Completeness on higher types still needs Leibniz as a fallback. Keep
  the existing expansion rule alive; just make it genuinely the last
  resort.
- The `ContradictionAgent` already handles cross-branch closure via the
  `shot_un` CSP; surface the negative equation in the same way so
  unification-based closure works.

**Size.** Medium. Touches `Rules`, `Branch`, possibly `Proof` for the new
closure variety.
**Dependencies.** None strictly, but pairs naturally with (1) (a strong
deferral on Leibniz is most useful once (2) exists to cover for it).

## 3. Ordered superposition restrictions

**Idea.** Restrict where paramodulation can fire. Two pieces:

1. **Maximal-side rewriting.** Only rewrite an equation `s = t` at
   subterm positions whose containing literal is maximal w.r.t.
   `TermOrder`. Standard superposition restriction.
2. **Literal selection.** Select a negative literal per clause/branch
   and only paramodulate into it. Drastically prunes the search.

**Why.** Today every paramodulation triggers at every DAG subterm; on
problems with many equations the cross-product blows up. Selection plus
maximal-side restrictions are how Vampire / E / Zipperposition stay fast
on FO equality.

**Sketch.** Half the infrastructure exists: `TermOrder` already wraps
NCPO-LNF with a tiebreaker and `Branch.orient_pair` directs equations.
What's missing is

- A `maximal?/3` predicate ranking literals on a branch.
- A selection-function callback in `Parameters`.
- Calls in `Paramodulation` that respect both restrictions.

**Care points.** This is real superposition machinery; the soundness and
completeness arguments shift to standard refutation completeness for
selection-based superposition. NCPO-LNF is not a reduction order, so the
literal ordering needs to be made well-founded before claiming
completeness (or the order must only restrict, not eliminate, in the
absence of well-foundedness).

**Size.** Large. Best done after (2) so we have the negative-equation
infrastructure to select against.
**Dependencies.** (2), and a well-foundedness story for `TermOrder`.

## 4. Redundancy and subsumption on equations

**Idea.** Drop equations subsumed by others; don't keep paramodulating
with equations whose RHS has already been normalised away.

**Why.** In superposition, redundancy elimination is essential — without
it, the search space grows linearly with every derived equation,
including derivatives that are immediately reducible. We already have
oriented `lhs → {rhs, …}` storage; we don't yet have any pruning.

**Sketch.** Two passes:

- **Demodulation.** When inserting an equation, normalise its RHS using
  every previously oriented equation. If the result is `s = s`, drop it
  as a tautology; otherwise store the normal form.
- **Subsumption.** Periodically scan `branch.equations` for entries
  whose LHS rewrites to another entry's LHS — the rewritten one
  subsumes the rewriting one. Remove the redundant entry.

**Care points.** Demodulation can be unsound under non-confluent rewrite
systems; ordering on equations must be respected. Bookkeeping needs to
invalidate any cached paramodulants of removed equations.

**Size.** Medium-to-large. Mostly contained in `Paramodulation` and
`Branch.ingest_formula`.
**Dependencies.** Benefits enormously from (3) (a stable ordering helps
demodulation termination) but can be staged in independently if
restricted to ground equations.

## 5. Skip Leibniz when paramodulation has reached fixpoint

**Idea.** Inspect a sleeping branch: if no further paramodulants are
producible from the current equation/literal sets, *and* no closure has
fired, then Leibniz expansion really is the only way forward — let it
fire at its normal cost. Otherwise keep deferring.

**Why.** This is the principled version of "high Leibniz cost". The
fixpoint check makes the deferral observable instead of just a heuristic.

**Care points.** Fragile without (4): without redundancy elimination
"fixpoint" is hard to recognise because the equation set keeps growing
non-monotonically.

**Size.** Small to medium once (4) is in place; fragile before then.
**Dependencies.** (4).

## Suggested ordering

A sensible path through the list:

1. Land the cost-split (done).
2. **(2) Negative-equation paramodulation.** Highest leverage; lifts the
   ceiling on Leibniz cost.
3. **(1) Iterative-deepening on Leibniz cost.** Cheap, pairs with (2).
4. **(4) Demodulation.** Independent infrastructure win, makes the
   numbers in proof traces stop ballooning.
5. **(3) Ordered superposition restrictions.** Tackle when (2) and (4)
   are stable.
6. **(5) Fixpoint-aware Leibniz.** Only once redundancy is in place.

After (2)+(1), the default `equality_cost` for `:leibniz` can probably
be lifted from 15 back to 50+ without regression on the existing test
suite.
