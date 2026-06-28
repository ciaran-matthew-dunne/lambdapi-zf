# lambdapi-zf

A [Lambdapi](https://github.com/Deducteam/lambdapi) translation of the
**Isabelle/ZF** object logic — Zermelo–Fraenkel set theory formalized in
first-order logic, ported theory-for-theory into the λΠ-calculus modulo
rewriting.

The modules mirror the structure (and largely the lemma names) of the upstream
Isabelle/ZF theories in `src/ZF/`, so a reader familiar with Isabelle/ZF will
recognize the API. The original `.thy` sources each module was translated from
are kept under [`isabelle-src/`](isabelle-src/) for provenance and auditing.

All proofs are complete: **0 `admitted`**.

## Using it

This is a Lambdapi package:

```
package_name = zf
root_path    = ZF
```

so modules are imported under the logical root `ZF`, regardless of where the
repository is checked out:

```lambdapi
require open ZF.ZF_Base ZF.upair ZF.pair ZF.Ordinal;
```

### As a git submodule

The package was extracted from the [`hyperset`](https://github.com/ciaran-matthew-dunne/hyperset)
project and is consumed there as a submodule. To use it the same way:

```bash
git submodule add https://github.com/ciaran-matthew-dunne/lambdapi-zf.git path/to/ZF
```

Because resolution is by `root_path` (not directory name), the checkout
directory can be named anything — `path/to/ZF`, `vendor/lambdapi-zf`, etc. When
type-checking files in a *different* package that `require ZF.*`, point Lambdapi
at the checkout with `--map-dir=ZF:path/to/checkout`.

## Requirements

- **Lambdapi** ≥ `dev-3.0.0` (developed against `dev-3.0.0-89-g402c35e1`).
- The **`Stdlib`** package, available in Lambdapi's global library root (it
  ships with a standard `lambdapi` install). The modules use
  `Stdlib.Set`, `Stdlib.Prop`, `Stdlib.FOL`, `Stdlib.Eq`.

## Checking

```bash
./check.sh            # type-check every module
./check.sh Ordinal.lp # or specific files (dependencies are built automatically)
```

## Modules

| Module        | Contents                                                              |
|---------------|----------------------------------------------------------------------|
| `ZF_Base`     | Core ZF axioms: `∈`, `empty`, `Pow`, `Union`, `Collect`, `RepFun`, infinity, replacement |
| `upair`       | Unordered pairs, `cons`, `succ`, `∪`, `∩`                             |
| `pair`        | Ordered pairs (**abstract `Pair`**, see below), `fst`/`snd`, `split`, `Sigma` |
| `equalities`  | Boolean-algebra-style equalities and inclusions on sets              |
| `func`        | Functions as relations: `lam`, `apply`, `Pi`, `domain`, `range`      |
| `Bool_ZF`     | Booleans in ZF (`1`, `0`, `cond`, and/or/not)                        |
| `Fixedpt`     | Knaster–Tarski least/greatest fixed points (`lfp`, `gfp`)           |
| `Trancl`      | Transitive and reflexive-transitive closure (`trancl`, `rtrancl`)   |
| `WF`          | Well-founded relations, well-founded recursion (`wfrec`) and induction |
| `Ordinal`     | Ordinals, `Ord`, `Limit`, `Transset`, transfinite induction         |
| `Nat_ZF`      | Natural numbers (`nat`/`omega`), induction, recursion               |
| `Epsilon`     | `∈`-recursion (`transrec`), rank, `Vset`                            |
| `EquivClass`  | Equivalence relations and quotients                                 |
| `Perm`        | Injections, surjections, bijections, composition (partial wrt Isabelle's `Perm`) |
| `AC`          | Axiom of choice                                                     |
| `Univ`        | The cumulative universe / `univ` construction                       |
| `ZF_extra`    | Extra lemmas used downstream, not part of upstream Isabelle/ZF      |

## Design note: `Pair` is abstract

Unlike Isabelle/ZF (and unlike the concrete Kuratowski encoding
`Pair a b = {{a}, {a, b}}`), `Pair` here is an **abstract constructor**:

```lambdapi
symbol Pair : τ ι → τ ι → τ ι;
symbol fst  : τ ι → τ ι;
symbol snd  : τ ι → τ ι;
rule fst (Pair $a $b) ↪ $a;
rule snd (Pair $a $b) ↪ $b;
rule Pair (fst $p) (snd $p) ↪ $p;
```

with injectivity (`Pair_inject1`, `Pair_inject2`) and `Pair_neq_0` taken as
axioms (they are theorems under the Kuratowski encoding). This makes `fst`/`snd`
reduce **definitionally** on pairs, which is convenient for developments that
compute heavily with ordered pairs — e.g. the cumulative non-well-founded set
model in `hyperset`, where graph edges are pairs. A Kuratowski-based variant
(everything proved, no extra axioms, `fst`/`snd` via definite description)
exists upstream; the two are not interchangeable.

## Provenance

Translated by hand from Isabelle2025 `src/ZF/`. The source `.thy` files for the
translated modules are in [`isabelle-src/`](isabelle-src/). Isabelle/ZF is
distributed under the Isabelle BSD-style license.

## Status & roadmap

- All listed modules type-check with **0 admitted** proofs.
- `Perm` is a partial translation relative to Isabelle's full `Perm.thy`.
- Not yet ported (candidates): `Order`, `Sum`, `QPair`, `OrdQuant`, `Cardinal`,
  `Arith`, `List`, … A fuller (Kuratowski-pair) translation with a translation
  harness lives in the author's `lp-slop` workspace and can be folded in.
- **TODO:** add a `LICENSE`.
