# lambdapi-zf

A [Lambdapi](https://github.com/Deducteam/lambdapi) translation of the
**Isabelle/ZF** object logic — Zermelo–Fraenkel set theory formalized in
first-order logic, ported theory-for-theory into the λΠ-calculus modulo
rewriting.

The modules mirror the structure (and largely the lemma names) of the upstream
Isabelle/ZF theories in `src/ZF/`, so a reader familiar with Isabelle/ZF will
recognize the API. The original `.thy` sources each module was translated from
are kept under [`isabelle-src/`](isabelle-src/) for provenance and auditing.

## Status at a glance

Every module in the package **type-checks** (`./check.sh` ends `OK`). The
foundational layer up through ordinals, recursion, orderings and equivalence
classes is **fully proved**; the frontier toward cardinals is present as
**faithful skeletons** (every definition and every lemma/theorem *statement* is
there, with the harder proofs left as `admit`). The remaining `admit`s are
concentrated in the last few modules on the road to `Cardinal`:

| Module | `admit`s | | Module | `admit`s |
|---|--:|---|---|--:|
| `Cardinal` | 153 | | `OrderArith` | 18 |
| `OrderType` | 116 | | `Perm` | 2 |
| `Finite` | 24 | | `Order` | 1 |

All **21 other modules have 0 `admit`s.** (`admit` is the tactic that leaves a
hole + axiom; it is *not* a faked proof — statements stay faithful and the
kernel still checks everything else. Count with
`grep -cnE '^\s*admit\b' *.lp`.)

## Theories

Legend: **✅ proved** (0 `admit`s) · **🔨 in progress** (some hard proofs
`admit`ted) · **🧩 skeleton** (all statements present, proofs `admit`ted).

### Foundations — fully proved

| Module (`.lp`) | Isabelle `.thy` | | Contents |
|---|---|:--:|---|
| `ZF_Base`    | `ZF_Base`    | ✅ | Core ZF axioms: `∈`, `empty`, `Pow`, `Union`, `Collect`, `RepFun`, infinity, replacement |
| `upair`      | `upair`      | ✅ | Unordered pairs, `cons`, `succ`, `∪`, `∩`, `The` |
| `pair`       | `pair`       | ✅ | Ordered pairs (**concrete Kuratowski**, see below), `fst`/`snd`, `split`, `Sigma`, `converse`, `domain`/`range` |
| `equalities` | `equalities` | ✅ | Boolean-algebra-style equalities and inclusions on sets |
| `func`       | `func`       | ✅ | Functions as relations: `Lambda`, `apply`, `Pi`, `restrict`, `Image` |
| `Bool_ZF`    | `Bool`       | ✅ | Booleans in ZF (`1`, `0`, `cond`, and/or/not) |
| `Sum`        | `Sum`        | ✅ | Disjoint sums `A+B`, `Inl`/`Inr`, `case` |
| `QPair`      | `QPair`      | ✅ | Quine ordered pairs and disjoint sums (`<a;b>`, `QSigma`, `qsplit`) |
| `Fixedpt`    | `Fixedpt`    | ✅ | Knaster–Tarski least/greatest fixed points (`lfp`, `gfp`) |
| `Trancl`     | `Trancl`     | ✅ | Transitive & reflexive-transitive closure; `rcomp`, `sym`, `trans` |
| `WF`         | `WF`         | ✅ | Well-founded relations, well-founded recursion (`wfrec`) and induction |
| `Ordinal`    | `Ordinal`    | ✅ | Ordinals, `Ord`, `Limit`, `Transset`; `lt`/`le` **carry `Ord`** (as in Isabelle) |
| `OrdQuant`   | `OrdQuant`   | ✅ | Bounded ordinal quantifiers `∀x<a`, `∃x<a`, `OUnion` |
| `Nat_ZF`     | `Nat`        | ✅ | Natural numbers (`nat`/`omega`), induction, recursion |
| `Epsilon`    | `Epsilon`    | ✅ | `∈`-recursion (`transrec`), `rank`, `Vset` |
| `Inductive`  | `Inductive`  | ✅ | Glue lemmas for the inductive-definition package |
| `EquivClass` | `EquivClass` | ✅ | Equivalence relations, quotients, congruences |
| `AC`         | `AC`         | ✅ | Axiom of choice |
| `Univ`       | `Univ`       | ✅ | The cumulative universe / `univ` construction |
| `ZF_extra`   | *(none)*     | ✅ | Extra lemmas used downstream, not part of upstream Isabelle/ZF |

### Frontier toward `Cardinal`

| Module (`.lp`) | Isabelle `.thy` | | `admit`s | Notes |
|---|---|:--:|--:|---|
| `Perm`       | `Perm`       | 🔨 | 2   | Injections/surjections/bijections. Remaining: `fun_is_surj`, `bij_inverse_exists` |
| `Order`      | `Order`      | 🔨 | 1   | Orderings, order isomorphisms. Remaining: `well_ord_trichotomy` capstone |
| `OrderArith` | `OrderArith` | 🔨 | 18  | Combining orderings (`radd`, `rmult`, `rvimage`, `measure`, `wfrank`). wf-rank→ordinal & measure layers proved; remaining: `case_sum` bijections, converse-inverse `ord_iso`s, nested `wf_on` inductions |
| `Finite`     | `Finite`     | 🔨 | 24  | `Fin`/`FiniteFun`. `Fin`-side derived lemmas proved from the abstract `Fin` axioms; `FiniteFun` side still skeleton |
| `OrderType`  | `OrderType`  | 🧩 | 116 | Order types, ordinal `+`, `·`, `−` (`ordermap`, `ordertype`, `omult`, `oadd`) |
| `Cardinal`   | `Cardinal`   | 🧩 | 153 | Cardinals, `≈`/`≼` (equipollence/lepoll), `|A|`, `Card`, Schröder–Bernstein |

### Not yet ported

The dependency chain continues past `Cardinal` into arithmetic and the datatype
package. Base first-order logic (`FOL`, `IFOL`) is supplied by Lambdapi's
`Stdlib`, and `ZF.thy` is only an umbrella import, so those are not separate
modules here.

| Isabelle `.thy` | Depends on | Notes |
|---|---|---|
| `Arith`, `ArithSimp` | `Nat` | Arithmetic on `nat` (next up) |
| `Bin`, `Int`, `IntDiv` | `Arith` | Binary integers |
| `List` | `Datatype` | Lists |
| `CardinalArith` | `ArithSimp`, `Cardinal` | Cardinal arithmetic |
| `Zorn` | `OrderType`, `AC` | Zorn's lemma / well-ordering theorem |
| `Cardinal_AC` | `Zorn` | Cardinal arithmetic assuming AC |
| `Datatype`, `InfDatatype` | `Univ`, `Nat` | Datatype package |
| `QUniv` | `Univ`, `QPair` | Quine (non-well-founded) universe |
| `ZFC` | `Cardinal` | AC as an axiom (off the critical path) |

Run `python3 tools/audit.py --status` for the live dashboard (per-module `admit`
counts and statement completeness vs the Isabelle source), or
`python3 tools/audit.py <Module>` for a detailed per-module diff.

## Design note: `Pair` is concrete Kuratowski

Ordered pairs use Isabelle/ZF's concrete Kuratowski encoding — they are **not**
an abstract constructor:

```lambdapi
Pair a b ≔ Upair (singleton a) (Upair a b)   // {{a}, {a,b}}
fst p    ≔ The (λ a, ∃ b, p = Pair a b)
snd p    ≔ The (λ b, ∃ a, p = Pair a b)
```

Consequently `Pair_inject1/2`, `Pair_neq_0`, `fst_conv`, `snd_conv` are
**proved theorems**, not axioms. Note that `fst (Pair a b)` does **not** reduce
to `a` definitionally — you rewrite with `fst_conv a b : fst (Pair a b) = a`
(and `snd_conv`). Likewise ordinal `lt`/`le` carry an `Ord` witness exactly as
in Isabelle (`lt i j ≔ i ∈ j ∧ Ord j`), so ported ordinal lemmas need no extra
`Ord` hypotheses. These are deliberate faithfulness choices; see `CLAUDE.md §3`.

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

The package is consumed by the [`hyperset`](https://github.com/ciaran-matthew-dunne/hyperset)
project as a submodule. To use it the same way:

```bash
git submodule add https://github.com/ciaran-matthew-dunne/lambdapi-zf.git path/to/ZF
```

Because resolution is by `root_path` (not directory name), the checkout
directory can be named anything. When type-checking files in a *different*
package that `require ZF.*`, point Lambdapi at the checkout with
`--map-dir=ZF:path/to/checkout`.

## Requirements

- **Lambdapi** ≥ `dev-3.0.0`.
- The **`Stdlib`** package, in Lambdapi's global library root (ships with a
  standard `lambdapi` install). The modules use `Stdlib.Set`, `Stdlib.Prop`,
  `Stdlib.FOL`, `Stdlib.Eq`, `Stdlib.Classic`, `Stdlib.Impred`, `Stdlib.HOL`,
  `Stdlib.PropExt`, `Stdlib.Epsilon`.

## Checking

```bash
./check.sh                       # type-check every module (writes .lpo caches)
./check.sh Ordinal.lp            # or specific files (dependencies built automatically)
lambdapi check Order.lp          # read-only check (no cache), fastest feedback
python3 tools/audit.py --status  # admits + completeness dashboard vs Isabelle source
```

## Provenance

Translated by hand from Isabelle2025 `src/ZF/`. The source `.thy` files for the
translated modules are in [`isabelle-src/`](isabelle-src/). Isabelle/ZF is
distributed under the Isabelle BSD-style license.

**TODO:** add a `LICENSE`.
