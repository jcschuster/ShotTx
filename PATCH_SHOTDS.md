# Patch proposal: ShotDs THF parser

Three defects in `ShotDs.Parser` account for the great majority of
`parser_error` rows in the ShotTx TPTP ablation sweep. Two are diagnosed with a
verified patch below; the third is diagnosed with a proposed fix that has not
been implemented.

| # | Defect | Domains affected | Status |
| - | ------ | ---------------- | ------ |
| 1 | Binder body in argument position swallows the enclosing `@`-chain | ITP, SCT, SET`^3`, DAT, SEV, SWW, COM, SYO, PRO, NUM | Patch written and measured |
| 2 | TH1 type arguments are not recognised when single-quoted | RAL (all 70) | Patch written and measured |
| 3 | TPTP arithmetic constants are monomorphic per problem | RAL | Diagnosed, fix proposed only |

Measured against **shot_ds 1.2.10** and **TPTP v9.3.0**, on a 338-problem
sample: **113 problems fixed, 0 regressions.**

---

## 1. A binder body in argument position swallows the application chain

### Symptom

```
Type Error: Cannot unify strict function types of different arities.
```

raised from `ShotDs.Util.TypeInference` (`util/type_inference.ex:160`), and —
when the stolen argument clashes on a base type instead of an arity —

```
Type Error: Cannot unify concrete goals b and c.
```

from `util/type_inference.ex:123`. The second message is the one that
identifies the defect: nothing in a well-formed problem should ever compare
those two types.

### Root cause

`parse_lambda/3` (`parser.ex:1063`) parses an unparenthesised body with
`parse_formula/3` (`parser.ex:1075`), which keeps consuming `@ arg` tokens:

```elixir
{:ok, {body_pre_term, rest_tokens, _body_ctx, subst2}} <-
  (case body_tokens do
     [{:lparen, _, _} | _] -> parse_atomic(body_tokens, inner_ctx, subst)
     _ -> parse_formula(body_tokens, inner_ctx, subst)   # <- greedy
   end)
```

`parse_lambda/3` is reached from two places: `parse_unitary/3`
(`parser.ex:835`, top level of a formula) and `parse_atomic/3`
(`parser.ex:1337`, the right operand of an `@`). In the second case the greedy
body provably steals the arguments of the application the lambda is an argument
*of*.

Per the THF grammar a binder's body is a `<thf_unitary_formula>`; an
application is a `<thf_apply_formula>`, so the chain continues **outside** the
binder:

```
<thf_quantified_formula> ::= <thf_quantification> <thf_unitary_formula>
<thf_apply_formula>      ::= <thf_unitary_formula> @ <thf_unitary_formula>
                           | <thf_apply_formula> @ <thf_unitary_formula>
```

### Minimal reproduction

`SET640^3`'s conjecture is the clearest instance:

```tptp
thf(thm,conjecture,
    ! [R: $i > $i > $o,Q: $i > $i > $o] :
      ( ( sub_rel @ R @ Q )
     => ( sub_rel @ R
        @ ( cartesian_product
          @ ^ [X: $i] : $true
          @ ^ [X: $i] : $true ) ) ) ).
```

`cartesian_product @ (^[X]: ($true @ ^[X]: $true))` is built instead of
`cartesian_product @ (^[X]:$true) @ (^[X]:$true)`, so `$true` — type `$o`,
arity 0 — is applied to an argument. Parenthesising both lambdas makes the file
parse unchanged in every other respect.

A self-contained 8-line case:

```tptp
thf(t1,type, a: $tType ).
thf(t2,type, b: $tType ).
thf(t3,type, g: b > $o ).
thf(t4,type, prof: ( a > b > $o ) > $o ).
thf(t5,type, m2: ( a > b > $o ) > ( ( a > b > $o ) > $o ) > $o ).
thf(bug,axiom, m2 @ ^ [P: a] : g @ prof ).          % fails
thf(ok, axiom, m2 @ ( ^ [P: a] : g ) @ prof ).      % parses
```

### Fix

Give `parse_lambda` a body-scope parameter. Argument position parses the body
at unitary level; the top level keeps today's behaviour.

```diff
@@ parser.ex:1063
-  defp parse_lambda([{:lbracket, _, _} | rest], ctx, subst) do
+  defp parse_lambda(tokens, ctx, subst), do: parse_lambda(tokens, ctx, subst, :formula)
+
+  defp parse_lambda([{:lbracket, _, _} | rest], ctx, subst, body_scope) do
     with {:ok, {vars, updated_tvar_env, rest_after_vars}} <-
            parse_typed_vars_with_inference(rest, ctx.type_vars),
          inner_ctx =
@@
          [{:rbracket, _, _}, {:colon, _, _} | body_tokens] <- rest_after_vars,
          {:ok, {body_pre_term, rest_tokens, _body_ctx, subst2}} <-
-           (case body_tokens do
-              [{:lparen, _, _} | _] -> parse_atomic(body_tokens, inner_ctx, subst)
-              _ -> parse_formula(body_tokens, inner_ctx, subst)
-            end) do
+           parse_lambda_body(body_tokens, inner_ctx, subst, body_scope) do

@@ after parse_lambda/4
+  # A binder's body is a `<thf_unitary_formula>`; an application chain continues
+  # *outside* it. In argument position (`f @ ^[X]: b @ y`) a body parsed at
+  # formula level swallows the enclosing chain's remaining arguments, turning
+  # `f @ (^[X]: b) @ y` into `f @ (^[X]: (b @ y))`. Hence `:unitary` there.
+  defp parse_lambda_body([{:lparen, _, _} | _] = tokens, ctx, subst, _scope),
+    do: parse_atomic(tokens, ctx, subst)
+
+  defp parse_lambda_body(tokens, ctx, subst, :formula), do: parse_formula(tokens, ctx, subst)
+
+  # `~` applied to a unitary formula stays part of the body; `~` as a bare term
+  # (`~ @ x`, or `~` before `)`) is left to `parse_atomic`, matching the
+  # corresponding clauses of `parse_unitary/3`.
+  defp parse_lambda_body([{:not, _, off} | [next | _] = rest], ctx, subst, :unitary)
+       when not (elem(next, 0) in [:app, :rparen]) do
+    with {:ok, {term, rest2, ctx2, s1}} <- parse_lambda_body(rest, ctx, subst, :unitary),
+         {:ok, s2} <- unify_at(get_pre_type(term), Definitions.type_o(), s1, off) do
+      {:ok,
+       {{:pre_app, {:pre_const, "~", Definitions.type_oo()}, term, Definitions.type_o()}, rest2,
+        ctx2, s2}}
+    end
+  end
+
+  defp parse_lambda_body(tokens, ctx, subst, :unitary), do: parse_atomic(tokens, ctx, subst)

@@ parser.ex:1337
-  defp parse_atomic([{:lambda, _, _} | rest], ctx, subst), do: parse_lambda(rest, ctx, subst)
+  defp parse_atomic([{:lambda, _, _} | rest], ctx, subst),
+    do: parse_lambda(rest, ctx, subst, :unitary)
```

### Notes on the fix

* **The `~` clause is required, not decorative.** `parse_atomic/3` returns `~`
  as a bare constant for the `@`-chain to apply (`parser.ex:1339`), so without
  it the body of `q @ ^[X:$i]: ~ ( p @ X )` would end at `~`. Both the
  parenthesised and unparenthesised spellings were tested.

* **The top-level binder is deliberately left greedy.** The grammar says its
  body is unitary there too, but tightening it changes the reading of every
  `! [X] : p @ X` that parses today, and every failure observed is in argument
  position. The residual limitation is visible as

  ```tptp
  thf(n3,axiom, ^ [X: $i] : ~ ( p @ X ) = ^ [Y: $i] : ~ ( p @ Y ) ).
  ```

  which still fails. Confirmed on the unpatched build that this failure is
  pre-existing and not introduced by the patch.

* **Quantifiers have the same latent defect.** `parse_quantifier/4` is reached
  from `parse_atomic/3` at `parser.ex:1307` and `1310` and parses its body the
  same way. No problem in the sample failed on it, so it is left alone; if it
  surfaces, the same body-scope treatment applies.

---

## 2. TH1 type arguments are not recognised when single-quoted

### Symptom

```
Type Error: Cannot unify strict function types of different arities.
```

on every problem including `Axioms/MAT001^0.ax` — all 70 RAL problems.

### Root cause

`parse_type_arg/2` (`parser.ex:960`) accepts `:atom` and `:system` tokens but
not `:distinct`, which is what the lexer tags single-quoted words with
(`util/lexer.ex:154`). The three other type-parsing sites all guard
`atom_like in [:atom, :distinct, :distinct_object]` (`parser.ex:248`, `481`,
`1197`); this one does not.

`MAT001^0.ax` single-quotes every type name, so in

```tptp
thf('nil/0_type',type, 'nil/0': !>[Tv0: $tType] : ( 'ListOf' @ Tv0 ) ).
thf('.def_polynomial-sum_nil_axiom',axiom,
    ( ( 'polynomial-sum/1' @ ( 'nil/0' @ 'Polynomial' ) ) = ... ) ).
```

`'nil/0' @ 'Polynomial'` is not recognised as a *type* application. Control
falls through to the `{:error, _}` branch at `parser.ex:904` ("Not an explicit
type argument; fall through to regular term application"), and `'nil/0'` —
whose erased type `'ListOf' @ Tv0` is nullary — is applied to a term argument.

### Confirmation

The same file with unquoted type names parses; the quoted version does not.
Only the quoting differs:

```tptp
thf(t1,type, listof: $tType > $tType).          % parses
thf(t1,type, 'ListOf': $tType > $tType).        % fails
```

### Fix

```diff
@@ parser.ex:960
-  defp parse_type_arg([{:atom, name, _} | rest], ctx) do
+  defp parse_type_arg([{atom_like, name, _} | rest], ctx)
+       when atom_like in [:atom, :distinct, :distinct_object] do
     if Context.get_const_scheme(ctx, name) != nil do
       {:error, "TH1: '#{name}' is a known constant, not a type argument"}
     else
```

---

## 3. TPTP arithmetic constants are monomorphic per problem

**Diagnosed; no patch written.**

### Symptom

With patches 1 and 2 applied, `RAL001^1.p` advances from byte 80938 to byte
310118 and fails with

```
Type Error: Cannot unify concrete goals real and int.
```

on `2d.def_converge_point_axiom` in `Axioms/MAT001^0.ax`:

```tptp
! [V_f: $int > '2d.Point',V_p0: '2d.Point'] :
  ( ( '2d.converge-point/2' @ V_f @ V_p0 )
<=> ! [V_x: $real] : ? [V_l: $int] : ! [V_n: $int] :
      ( ( $less @ V_l @ V_n )                                   % $int
     => ( $less @ ( '2d.distance/2' @ V_p0 @ ( V_f @ V_n ) ) @ V_x ) ) ) % $real
```

### Root cause

`$less` has no special handling anywhere in the parser. It reaches
`parse_constant/4` (`parser.ex:1359`) via `parse_atomic/3` (`parser.ex:1243`),
misses the `%TypeScheme{vars: [_ | _]}` branch, and lands in the "not declared
yet" branch, which mints **one** fresh type variable and stores it in the
context:

```elixir
nil ->
  new_type = Type.fresh_type_var()
  ctx2 = Context.put_const(ctx, name, new_type)
```

That single variable is bound by the first occurrence to `$int > $int > $o`, so
the `$real` occurrence in the same formula clashes. TPTP's arithmetic
predicates and functions are ad-hoc polymorphic over `$int`, `$rat` and
`$real`.

### Proposed fix

Register the TPTP arithmetic constants as `TypeScheme`s in the initial context
so `parse_constant/4` takes its existing polymorphic branch and
`TypeScheme.instantiate_with_refs/1` gives every occurrence a fresh
instantiation — the same machinery TH1 constants already use.

* comparisons — `$less`, `$lesseq`, `$greater`, `$greatereq`: `α > α > $o`
* arithmetic — `$sum`, `$difference`, `$product`, `$quotient`,
  `$quotient_e/_t/_f`, `$remainder_e/_t/_f`: `α > α > α`
* unary — `$uminus`, `$floor`, `$ceiling`, `$truncate`, `$round`: `α > α`
* predicates — `$is_int`, `$is_rat`: `α > $o`
* conversions — `$to_int`, `$to_rat`, `$to_real`: `α > $int` / `$rat` / `$real`

TPTP restricts `α` to the three numeric sorts; an unconstrained type variable
is sufficient to parse the corpus and keeps the change to a table plus a
context seed.

---

## Validation

### Method

338 problems from TPTP v9.3.0, parsed with `ShotDs.Tptp.parse_tptp_file/2`
before and after patches 1 and 2, each under a 25-second wall-clock cap in a
throwaway process:

* **138 pattern hits** — every problem whose text matches a lambda in argument
  position with an unparenthesised body,
  `rg -lU --pcre2 '@\s*\^\s*\[[^\]]*\]\s*:\s*[^\s()]+\s*@'`.
* **200 control problems** — the largest problems *not* matching that pattern,
  chosen to make regressions maximally likely to surface.

### Results

| Group | Before → after |
| ----- | -------------- |
| Pattern hits, non-ITP (113) | **96 fixed**, 17 still failing |
| Pattern hits, ITP (25) | **17 fixed**, 8 still failing |
| Control (200) | 193 OK → OK, 7 already failing → unchanged |

**113 fixed, 0 regressions.** All 138 pattern-matched problems were failing
beforehand, so the textual pattern was a perfect predictor of failure on this
sample. `SET640^3` and `SCT170^1` parse; `RAL001^1` advances as described in §3.

### Corpus-wide exposure

Problems matching the §1 pattern, by domain: ITP 417, DAT 26, SEV 17, SWW 16,
COM 15, SYO 11, SCT 7, SEU 6, PRO 6, SET 4, NUM 4, SWV 1 — **530 problems**,
plus 24 axiom files under `Axioms/` (including `MAT001^0.ax`, which every RAL
problem includes, and 23 `ITP001/*.ax`).

---

## Known failures not addressed

From the 32 sample problems still failing after patches 1 and 2:

| Count | Failure | Note |
| ----- | ------- | ---- |
| 12 | `Syntax Error: Expected atomic term, but found token '@'` on Isabelle's `split_paired_All` / `ex_nat` | 9 failed this way before the patch too; 3 reach it only after clearing their earlier error |
| 8 | `Cannot unify strict function types of different arities` on `thm_2Eoption_2Eoption__REP__ABS__DEF` (ITP`^7`) | Distinct defect, undiagnosed |
| 5 | Occurs check / arity errors in COM | Undiagnosed |
| 7 | Tuples, sequents (`-->`) and modal operators in SYO | No counterpart in simple type theory; out of scope |

---

## Reproducing

```bash
export TPTP_ROOT=/path/to/TPTP

# Single problem
mix run -e '
  IO.inspect(ShotDs.Tptp.parse_tptp_file(System.get_env("TPTP_ROOT") <> "/Problems/SET/SET640^3.p", :custom))'

# Every problem exposed to defect 1
cd $TPTP_ROOT/Problems && rg -lU --pcre2 '@\s*\^\s*\[[^\]]*\]\s*:\s*[^\s()]+\s*@' --glob '*^*.p'
```

## Downstream note for ShotTx

`ShotTx.Benchmark.TptpRunner` caches unparsable problems in
`<output_dir>/parse_cache` and replays the verdict across configurations.
Delete that file after upgrading `shot_ds`, or the stale `parser_error` rows
will be replayed instead of re-attempted.
