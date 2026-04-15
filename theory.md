# General Bindings and Primitive Substitution: Theory and Completeness

## 1. Setting

We work in Church's Simple Type Theory (STT) over the type base
$\{\iota, o\}$ with the standard logical signature:

$$
\Sigma = \{\top_o,\;\bot_o,\;\lnot_{o \to o},\;\land_{ooo},\;\lor_{ooo},\;
\supset_{ooo},\;\equiv_{ooo},\;=_{\tau\tau o},\;
\Pi_{(\tau o)o},\;\Sigma_{(\tau o)o}\}
$$

where we write $ooo$ for $o \to o \to o$, $\tau\tau o$ for
$\tau \to \tau \to o$, etc. Types are built by the grammar
$\tau ::= \iota \mid o \mid \tau_1 \to \tau_2$; in the uncurried
representation used in the implementation a type
$\alpha_1 \to \cdots \to \alpha_n \to \gamma$ is stored as
$(\gamma;\;[\alpha_1,\ldots,\alpha_n])$.

**Henkin semantics.** A _frame_ $\mathcal{D}$ assigns to each type $\tau$
a non-empty set $\mathcal{D}_\tau$ such that $\mathcal{D}_o = \{T, F\}$.
A frame is _Henkin_ if every $\mathcal{D}_{\alpha \to \beta}$ is a subset
of all functions $\mathcal{D}_\alpha \to \mathcal{D}_\beta$ that is
_closed under the operations definable in $\Sigma$_. A Henkin model is a
frame together with an interpretation of the non-logical constants that
respects the signature.

## 2. The Tableau Calculus

A branch $\mathcal{B}$ is a set of signed formulas (term IDs of type $o$)
maintained in a priority queue. The calculus applies rules that either
decompose formulas, introduce new branches, instantiate quantifiers, or
detect contradictions.

### 2.1 Propositional Rules

**$\alpha$-rules** (linear decomposition):

$$
\frac{A \land B}{\{A,\; B\}} \qquad
  \frac{\lnot(A \lor B)}{\{\lnot A,\; \lnot B\}} \qquad
  \frac{\lnot(A \supset B)}{\{A,\; \lnot B\}} \qquad \ldots
$$

**$\beta$-rules** (branching):

$$
\frac{A \lor B}{\mathcal{B} \cup \{A\} \mid \mathcal{B} \cup \{B\}}
  \qquad
  \frac{A \supset B}{\mathcal{B} \cup \{\lnot A\} \mid \mathcal{B} \cup \{B\}}
  \qquad \ldots
$$

### 2.2 Quantifier Rules

**$\delta$-rule** (Skolemization). For $\exists x_\tau.\;\Phi(x)$ with
free variables $\overline{z}$:

$$\frac{\exists x_\tau.\;\Phi(x)}{\Phi\bigl(\mathsf{sk}(\overline{z})\bigr)}$$

where $\mathsf{sk}$ is a fresh constant of type
$\tau_1 \to \cdots \to \tau_k \to \tau$ applied to $\overline{z}$.
Dually, $\lnot\forall x.\;\Phi(x)$ yields
$\lnot\Phi(\mathsf{sk}(\overline{z}))$.

**$\gamma$-rule** (universal instantiation with fresh variable). For
$\forall x_\tau.\;\Phi(x)$:

$$\frac{\forall x_\tau.\;\Phi(x)}{\Phi(Y_\tau)}$$

where $Y_\tau$ is a fresh free variable. The formula is _not consumed_;
it is re-enqueued with an incremented instantiation counter. An iterative
deepening mechanism on the $\gamma$-limit ensures that each
$\gamma$-formula is eventually instantiated unboundedly many times.

**$\gamma_{\text{finite}}$-rule.** When $\tau$ is a _finite_ type (i.e.,
a pure $o$-type such as $o$, $o \to o$, $o \to o \to o$, etc.), the
quantifier is consumed by exhaustive instantiation with every element of
the domain, which is enumerated by `gen_o`.

### 2.3 Equality and Extensionality

**Boolean extensionality.** Equality at type $o$ reduces to equivalence:

$$
\frac{a =_o b}{a \equiv b} \qquad
  \frac{\lnot(a =_o b)}{\lnot(a \equiv b)}
$$

**Functional extensionality.** Equality at a function type
$\alpha \to \beta$ reduces via the extensional equality axiom:

$$
\frac{f =_{\alpha \to \beta} g}
      {\forall z_\alpha.\; f\;z =_\beta g\;z}
$$

**Leibniz equality.** Equality at a base type $\tau$ (neither $o$ nor a
function type) reduces to the Leibniz schema:

$$
\frac{a =_\tau b}
      {\forall P_{\tau \to o}.\; (P\;a \odot P\;b)}
$$

where $\odot \in \{\equiv, \supset, \subset\}$ (the implementation
defaults to $\equiv$).

### 2.4 Rename and Instantiate (Primitive Boolean Extensionality)

When an atom $c(s_1,\ldots,s_n)$ has an argument $s_i$ of a pure
$o$-type that is not a member of the finite domain $\text{gen}_o(\tau_i)$:

- **Rename**: if $s_i$ is a non-primitive term, introduce a fresh constant
  $d$ of the appropriate type and add both $c(\ldots, d, \ldots)$ and
  $d = s_i$ to the branch. This reduces a complex argument to a name.

- **Instantiate**: if $s_i$ is a primitive term (eta-expanded constant or
  variable) that is not in the signature, branch over every element of
  $\text{gen}_o(\tau_i)$, defining $s_i$ to be each element in turn.
  This exhaustively enumerates the finite Boolean domain.

### 2.5 Branch Closure

A branch $\mathcal{B}$ is **closed** if it contains complementary
literals $\ell$ and $\lnot\ell$. More generally, a branch is closed if
there exist literals $\ell \in \mathcal{B}$ and $\lnot\ell' \in \mathcal{B}$
such that the higher-order pre-unification problem $\ell \doteq \ell'$
has a solution $\sigma$. The unifier $\sigma$ is applied globally across
branches (via the contradiction agent).

## 3. The Primitive Substitution Rule

### 3.1 Motivation

The $\gamma$-rule introduces a fresh variable $Y_\tau$ and relies on
pre-unification to determine its value. However, pre-unification is
incomplete for higher-order unification: flex-flex pairs are postponed
indefinitely, and certain bindings (especially those with logical
structure) may never be discovered.

**Example.** Suppose a proof requires instantiating $\forall P_{(\iota \to o)}.\;\Phi(P)$
with $\lambda x_\iota.\;Q(x) \land R(x)$. The $\gamma$-rule introduces
a fresh $Y_{(\iota \to o)}$, but the unification problem that would force
$Y = \lambda x.\;Q(x) \land R(x)$ may never arise—the relevant flex-rigid
pair might not appear, or the pair might be flex-flex and therefore
deferred.

### 3.2 General Bindings

A **general binding** at depth $d$ for a type
$\alpha_1 \to \cdots \to \alpha_n \to o$ (written $\overline{\alpha} \to o$)
is a $\lambda$-term:

$$
\mathcal{B}^d_{Q} \;=\;
  \lambda y_1^{\alpha_1}\cdots y_n^{\alpha_n}.\;
  Q\bigl(H_1\;\overline{y},\;\ldots,\;H_m\;\overline{y}\bigr)
$$

where:

- $Q$ is a **head symbol** drawn from the signature,
- $H_1,\ldots,H_m$ are **fresh free variables** (holes) of types
  determined by the head's argument types and the binder types,
- $m$ is the arity of $Q$.

Each $H_i$ has type $\alpha_1 \to \cdots \to \alpha_n \to \beta_i$
where $\beta_i$ is the $i$-th argument type of $Q$. The application
$H_i\;\overline{y}$ ensures that the holes have access to all bound
variables.

### 3.3 Head Catalogue

The heads are partitioned into **base** (propositional) and
**polymorphic** (type-dependent):

**Base heads** (independent of the type universe):

| Head $Q$  | Arity $m$ | Binding matrix                                                          |
| --------- | --------- | ----------------------------------------------------------------------- |
| $\top$    | 0         | $\lambda\overline{y}.\;\top$                                            |
| $\bot$    | 0         | $\lambda\overline{y}.\;\bot$                                            |
| $\lnot$   | 1         | $\lambda\overline{y}.\;\lnot(H_1\;\overline{y})$                        |
| $\land$   | 2         | $\lambda\overline{y}.\;(H_1\;\overline{y}) \land (H_2\;\overline{y})$   |
| $\lor$    | 2         | $\lambda\overline{y}.\;(H_1\;\overline{y}) \lor (H_2\;\overline{y})$    |
| $\supset$ | 2         | $\lambda\overline{y}.\;(H_1\;\overline{y}) \supset (H_2\;\overline{y})$ |
| $\equiv$  | 2         | $\lambda\overline{y}.\;(H_1\;\overline{y}) \equiv (H_2\;\overline{y})$  |

**Polymorphic heads** (for each type $\tau$ in the universe $\mathcal{U}$):

| Head $Q$       | Hole type(s)                            | Binding matrix                                                         |
| -------------- | --------------------------------------- | ---------------------------------------------------------------------- |
| $=_\tau$       | $H_1, H_2 : \overline{\alpha} \to \tau$ | $\lambda\overline{y}.\;(H_1\;\overline{y}) =_\tau (H_2\;\overline{y})$ |
| $\Pi_\beta$    | $H : \overline{\alpha} \to \beta \to o$ | $\lambda\overline{y}.\;\Pi_\beta(H\;\overline{y})$                     |
| $\Sigma_\beta$ | $H : \overline{\alpha} \to \beta \to o$ | $\lambda\overline{y}.\;\Sigma_\beta(H\;\overline{y})$                  |

Note that $\Pi_\beta(H\;\overline{y})$ abbreviates
$\forall z_\beta.\;(H\;\overline{y})\;z$, i.e., the quantifier is
applied to the predicate $H\;\overline{y} : \beta \to o$.

### 3.4 Depth-2 Composed Heads

At depth $d \geq 2$, additional **composed heads** are generated by
nesting a head (polymorphic or propositional) inside a propositional
connective. These cover structures that require two levels of logical
nesting. Representative examples:

**Propositional compositions:**

$$
\lambda\overline{y}.\;\lnot((H_1\;\overline{y}) \land (H_2\;\overline{y}))
\qquad
\lambda\overline{y}.\;\lnot(H_1\;\overline{y}) \land (H_2\;\overline{y})
\qquad \ldots
$$

**Polymorphic compositions** (for each $\tau \in \mathcal{U}$):

$$
\lambda\overline{y}.\;\lnot((H_1\;\overline{y}) =_\tau (H_2\;\overline{y}))
\qquad
\lambda\overline{y}.\;((H_1\;\overline{y}) =_\tau (H_2\;\overline{y})) \land (H_3\;\overline{y})
\qquad \ldots
$$

$$
\lambda\overline{y}.\;\lnot\Pi_\beta(H\;\overline{y})
\qquad
\lambda\overline{y}.\;\Pi_\beta(H_1\;\overline{y}) \land (H_2\;\overline{y})
\qquad \ldots
$$

### 3.5 The Inference Rule

$$
\frac{\forall X_{\overline{\alpha} \to o}.\;\Phi(X)}
      {\Phi(\mathcal{B}^d_1),\;\ldots,\;\Phi(\mathcal{B}^d_k)}
\;\;\text{(prim\_subst)}
$$

where $\mathcal{B}^d_1,\ldots,\mathcal{B}^d_k$ are the general bindings
at depth $d$ for type $\overline{\alpha} \to o$, processed in batches of
size $k$ (the `prim_subst_batch_size` parameter).

**Key properties:**

- The rule does **not** consume the quantified formula—it remains on the
  branch for further instantiation.
- The fresh holes $H_i$ in each binding are globally visible free
  variables, available for subsequent pre-unification.
- The rule is seeded as a companion to the $\gamma$-rule on the first
  $\gamma$-instantiation, but with much higher cost, ensuring it fires
  only when cheaper rules are exhausted.
- The rule is only applicable when $\text{goal}(\tau) = o$.

### 3.6 Interaction with the $\gamma$-Rule

The two rules are complementary:

|                       | $\gamma$                | prim_subst                                   |
| --------------------- | ----------------------- | -------------------------------------------- |
| **Instantiates with** | Fresh variable $Y_\tau$ | Structured term $\mathcal{B}^d_Q$ with holes |
| **Binding discovery** | Pre-unification         | Fixed head; holes via unification            |
| **Cost**              | $5 + 2c$                | $20 + 10d + 2c$                              |
| **Applies to**        | All types $\tau$        | Only $\overline{\alpha} \to o$               |

They cooperate: $\gamma$ introduces a flexible variable that unification
_may_ bind to a structured term. When unification cannot discover the
needed structure (flex-flex postponement, missing equations), prim_subst
provides it directly. The holes left by prim_subst can in turn be
refined by unification or by subsequent prim_subst applications.

## 4. The Type Universe

### 4.1 Definition

The **type universe** $\mathcal{U}$ is the set of all types $\tau$ for
which the polymorphic constants $=_\tau$, $\Pi_\tau$, $\Sigma_\tau$ are
available as general binding heads. It must contain every type and
sub-type occurring in the proof.

A type $\alpha_1 \to \cdots \to \alpha_n \to \gamma$ decomposes into:

$$
\mathcal{U}(\tau) \;=\; \{\tau\}
  \;\cup\; \bigcup_{k=1}^{n} \{\alpha_k \to \cdots \to \alpha_n \to \gamma\}
  \;\cup\; \bigcup_{i=1}^{n} \mathcal{U}(\alpha_i)
$$

### 4.2 Dynamic Extension

The initial universe $\mathcal{U}_0$ is computed from the problem
signature. During the proof, two rules introduce fresh constants whose
types may be new:

- **$\delta$-rule**: a Skolem constant $\mathsf{sk} : \sigma_1 \to \cdots \to \sigma_k \to \tau$
  may assemble argument types into a function type not in $\mathcal{U}$.

- **Rename rule**: a fresh naming constant $d : \tau$ is introduced for
  the same reason.

After each such rule fires, the universe is extended:
$\mathcal{U} \leftarrow \mathcal{U} \cup \mathcal{U}(\tau_{\text{new}})$.

### 4.3 Per-Depth Coverage

Because polymorphic heads at depth $d$ produce **different**
specifications than at depth $d-1$ (the composed forms are depth-dependent),
the set of types already covered by polymorphic binding generation is
tracked **per depth** and reset when advancing. This ensures that when
depth increases, all types—including those introduced earlier—get their
composed polymorphic bindings generated at the new depth.

Within a single depth, incremental coverage tracking (the
`covered_types` set) ensures that types introduced mid-depth by
skolemization are picked up in the next prim_subst firing without
replaying previously covered types.

### 4.4 Monotonicity

$\mathcal{U}$ grows monotonically: every type in $\mathcal{U}$ at step
$t$ is in $\mathcal{U}$ at step $t' > t$. Since each extension adds
finitely many sub-types and the proof generates finitely many fresh
constants per step, $\mathcal{U}$ remains finite at every finite proof
step.

## 5. Iterative Deepening

Two limits are maintained globally and incremented in lockstep when all
branches are idle:

- **$\gamma$-limit** $L_\gamma$: bounds how many times each
  $\gamma$-formula may be instantiated before sleeping.

- **prim_subst depth limit** $L_d$: bounds the maximum binding depth
  for prim_subst rules before sleeping.

When all branches are idle (no active processing, some branches sleeping
on exhausted $\gamma$ or prim_subst rules), the manager increments both
limits and wakes all sleeping branches.

This constitutes a **fair** search strategy: every $\gamma$-formula
is eventually instantiated an arbitrary number of times, and every
prim_subst rule is eventually allowed to generate bindings at arbitrary
depth.

## 6. Henkin Completeness

**Theorem.** _The tableau calculus described above is complete for Henkin
semantics: if $\Phi$ is valid in every Henkin model, then the tableau for
$\lnot\Phi$ closes._

### 6.1 Proof Strategy

We argue by contraposition. Assume the tableau for $\lnot\Phi$ does not
close under a fair search. Then by fairness, there exists a _saturated_
branch $\mathcal{B}$ — a branch on which every applicable rule has been
applied to saturation. We construct a Henkin model
$\mathcal{M} \models \lnot\Phi$ from $\mathcal{B}$, contradicting the
validity of $\Phi$.

### 6.2 Saturation Properties

A branch $\mathcal{B}$ produced by a fair search that does not close has
the following properties:

**(S1) Propositional saturation.** If $A \land B \in \mathcal{B}$ then
$A \in \mathcal{B}$ and $B \in \mathcal{B}$. If $A \lor B \in \mathcal{B}$
then $A \in \mathcal{B}$ or $B \in \mathcal{B}$. Similarly for all
$\alpha$- and $\beta$-rules.

**(S2) $\delta$-saturation.** If
$\exists x_\tau.\;\Phi(x) \in \mathcal{B}$ then
$\Phi(\mathsf{sk}(\overline{z})) \in \mathcal{B}$ for some Skolem term.

**(S3) $\gamma$-saturation.** If
$\forall x_\tau.\;\Phi(x) \in \mathcal{B}$ then for every closed term
$t$ of type $\tau$ constructible from the signature and the Skolem
constants introduced on $\mathcal{B}$, $\Phi(t) \in \mathcal{B}$.

This follows from the fact that the $\gamma$-rule introduces fresh
variables that are universally quantified over the term universe: as the
$\gamma$-limit grows without bound, every term is eventually represented.

**(S4) prim_subst saturation.** If
$\forall X_{\overline{\alpha} \to o}.\;\Phi(X) \in \mathcal{B}$ then for
every depth $d$ and every general binding
$\mathcal{B}^d_Q$ at depth $d$ (over the final type universe),
$\Phi(\mathcal{B}^d_Q) \in \mathcal{B}$.

This follows from the unbounded prim_subst depth limit and the per-depth
coverage mechanism.

**(S5) Extensionality saturation.** If $a =_{\alpha \to \beta} b \in \mathcal{B}$,
then $\forall z_\alpha.\;a\;z =_\beta b\;z \in \mathcal{B}$. If
$a =_o b \in \mathcal{B}$, then $a \equiv b \in \mathcal{B}$.

**(S6) Boolean saturation.** For every atom $c(\ldots,s_i,\ldots)$ on
$\mathcal{B}$ where $s_i$ is of a finite (pure $o$-) type, $s_i$ has
been instantiated with every element of $\text{gen}_o(\tau_i)$ (via
$\gamma_{\text{finite}}$, instantiate, or rename).

**(S7) Consistency.** $\mathcal{B}$ does not contain both $\ell$ and
$\lnot\ell$ for any literal $\ell$, nor does it contain
$\ell, \lnot\ell'$ with a pre-unification solution $\ell \doteq \ell'$.

### 6.3 Model Construction

From the saturated branch $\mathcal{B}$, we construct a Henkin model
$\mathcal{M}$:

**Term universe.** For each type $\tau$, let $\mathcal{T}_\tau$ be the
set of closed terms of type $\tau$ built from the signature constants
and the Skolem constants introduced on $\mathcal{B}$.

**Domains.** $\mathcal{D}_o = \{T, F\}$. For other types,
$\mathcal{D}_\tau = \mathcal{T}_\tau / {\sim_\tau}$ where $\sim_\tau$
is the congruence induced by the equalities on $\mathcal{B}$. (Two terms
are equivalent if the branch forces them equal.)

**Interpretation.** Constants are interpreted by their equivalence class.
Truth is determined by: a closed formula $\varphi$ of type $o$ is true
in $\mathcal{M}$ iff $\varphi \in \mathcal{B}$, and false iff
$\lnot\varphi \in \mathcal{B}$.

### 6.4 The Critical Step: Domain Completeness for $o$-Goal Types

The domains $\mathcal{D}_\tau$ must form a valid Henkin frame: for each
function type $\alpha \to \beta$, $\mathcal{D}_{\alpha \to \beta}$ must
be closed under the operations definable in the language. The critical
case is when $\beta = o$ (propositional function types), because the
denotations of such terms are essentially sets/predicates defined by
logical formulas.

For types $\tau$ with $\text{goal}(\tau) \neq o$, the $\gamma$-rule
with fresh variables ensures that $\mathcal{D}_\tau$ contains enough
elements. Unification between these fresh variables and existing terms
discovers the needed equalities.

For types $\tau = \overline{\alpha} \to o$ with $\text{goal}(\tau) = o$,
we need $\mathcal{D}_\tau$ to contain the denotation of every
$\lambda$-term $\lambda\overline{y}.\;\psi(\overline{y})$ where $\psi$
is built from connectives, quantifiers, and equality. This is precisely
what prim_subst provides:

**Lemma (Term Approximation).** _For every closed term
$t : \overline{\alpha} \to o$ built from the signature and from constants
on branch $\mathcal{B}$, and for every $\varepsilon > 0$, there exists a
depth $d$ and a general binding $\mathcal{B}^d_Q$ together with a
substitution $\sigma$ for its holes such that
$\sigma(\mathcal{B}^d_Q) = t$._

_Proof._ By structural induction on $t$. The outermost connective of the
body of $t$ determines the head $Q$. The sub-formulas are assigned to
the holes $H_1,\ldots,H_m$. If these sub-formulas are themselves
complex, they in turn have outermost connectives that determine the next
level of heads—either discovered by unification of the holes, or by
increasing the depth $d$ so that the next level of connective is fixed
directly.

At depth $d$, every term with at most $d$ levels of connective nesting
is directly generated (with trivial hole substitutions). For terms with
deeper nesting, depth $d$ produces an approximation with holes at level
$d$, and those holes can be filled by:

1. Pre-unification, if the right equations arise from branch closure
   attempts, or
2. Subsequent prim_subst applications at depth $d+1, d+2, \ldots$

Since the depth limit grows without bound, every finite term is
eventually covered exactly. $\square$

**Corollary.** By (S3), (S4), and the Term Approximation Lemma, the
saturated branch $\mathcal{B}$ contains $\Phi(t)$ for every closed term
$t$ of every type—including propositional types. Therefore the domains
$\mathcal{D}_\tau$ contain all definable elements, forming a valid Henkin
frame.

### 6.5 Verifying the Model

We verify that $\mathcal{M} \models \lnot\Phi$:

1. $\lnot\Phi \in \mathcal{B}$ by construction (the root formula).
2. By the saturation properties and the inductive structure of the rules,
   every formula on $\mathcal{B}$ is true in $\mathcal{M}$.
3. By (S7), $\mathcal{B}$ is consistent, so $\mathcal{M}$ is
   well-defined.
4. By the equality and extensionality saturation (S5, S6),
   $\mathcal{M}$ satisfies the extensionality axioms.

Therefore $\mathcal{M}$ is a Henkin model of $\lnot\Phi$, contradicting
the assumption that $\Phi$ is valid. $\square$

### 6.6 Why Each Component Is Necessary

| Component                  | Role in completeness                                                                                                         |
| -------------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| $\gamma$-rule              | Introduces witnesses for universal quantifiers over all types                                                                |
| $\gamma$-limit deepening   | Ensures fairness: every $\gamma$-formula instantiated unboundedly                                                            |
| prim_subst                 | Provides logical structure for $o$-goal types that unification alone cannot discover                                         |
| prim_subst depth deepening | Ensures every finite logical structure is eventually generated                                                               |
| Type universe extension    | Ensures polymorphic heads ($=_\tau$, $\Pi_\tau$, $\Sigma_\tau$) cover all types, including those introduced by skolemization |
| Per-depth coverage reset   | Ensures composed polymorphic heads are generated at each new depth for every type                                            |
| Boolean extensionality     | Ensures the model satisfies $a =_o b \;\Leftrightarrow\; (a \Leftrightarrow b)$                                              |
| Functional extensionality  | Ensures the model satisfies $f =_{\alpha \to \beta} g \;\Leftrightarrow\; \forall x.\;f\;x =_\beta g\;x$                     |
| Leibniz equality           | Ensures the model satisfies indiscernibility of identicals at base types                                                     |
| Pre-unification closure    | Detects complementary pairs modulo $\beta\eta$-equivalence                                                                   |
| Rename + Instantiate       | Handles primitive Boolean extensionality for atomic formulas with $o$-typed arguments                                        |

### 6.7 Remark: Why prim_subst Is Not Needed for Non-$o$ Goals

For a quantified variable $X_\tau$ where $\text{goal}(\tau) \neq o$
(e.g., $X_{\iota \to \iota}$), the elements of $\mathcal{D}_\tau$ in a
Henkin model are functions whose structure is _opaque_ from the logical
perspective. The $\gamma$-rule introduces a fresh $Y_\tau$ that stands
for an arbitrary element; pre-unification can bind $Y$ to any term
of the right type when forced by rigid-flex or rigid-rigid
decomposition. No logical head enumeration is needed because the
"structure" of elements of type $\iota$ is not expressible in the logic.

For $o$-goal types, the situation is fundamentally different: the
elements of $\mathcal{D}_{\overline{\alpha} \to o}$ _are_ truth-valued
functions—predicates—whose structure is expressible and relevant.
Pre-unification alone cannot always discover this structure because it
may involve flex-flex pairs that are deferred indefinitely. Primitive
substitution bridges this gap by directly proposing logical structures.
