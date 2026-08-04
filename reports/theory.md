# General Bindings and Primitive Substitution: Theory

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
