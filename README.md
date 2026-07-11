# lambdapi-zf

A [Lambdapi](https://github.com/Deducteam/lambdapi) port of **Isabelle/ZF** —
Zermelo–Fraenkel set theory with the Axiom of Choice, in first-order logic.
Each module translates the corresponding theory from Isabelle's `src/ZF/`; the
`.thy` sources are under [`isabelle-src/`](isabelle-src/).

**Status: complete.** All 40 modules type-check on a cold build (~5 s) with
**zero `admit`s**. The port asserts *only* the axioms of ZFC —
extensionality, the empty set, union, power set, foundation and replacement
([`ZF_Base`](ZF_Base.lp)), infinity ([`upair`](upair.lp)) and choice
([`AC`](AC.lp)) — and **proves every other definition, lemma and theorem** from
them. Build, admit worklist and anti-cheat gates are all driven by one tool:

```bash
./check.py          # cold build of the whole port + admit count + gates (~5 s)
./check.py --gate   # exit non-zero iff the build is red or a gate fails
```

The **coverage** column below is the number of Isabelle source statements that
have a port, over the total in the source `.thy`, as reported by
`./check.py --json`. It is *not* a measure of how much is proved — **every
ported statement is proved**. Foundation modules deliberately port only the
subset the development uses, so their coverage reads low even though every
downstream dependency is present (the untracked remainder is Isabelle
simp/rewrite-lemma noise the development never cites). The mathematical target
modules — the ordinal/cardinal chain up to [`Cardinal`](Cardinal.lp) and the
arithmetic chain through [`IntDiv`](IntDiv.lp)/[`List`](List.lp)/
[`CardinalArith`](CardinalArith.lp) — sit at or near 100 %. The **Notes**
column records faithfulness caveats: deliberate encoding choices and the few
statement-level divergences from the Isabelle source.

| Theory | coverage | Notes |
|---|--:|---|
| [`ZF_Base`](ZF_Base.lp) | 32/110 | the six ZF axioms are declared here as constants; `empty_ax` is axiomatized though Isabelle derives it (conservative); theory content is split across `upair`/`pair`/`func`/`equalities`; low coverage is simp-lemma noise |
| [`upair`](upair.lp) | 32/101 | `The` (definite description) is ε-free — encoded via guarded replacement, so no choice leaks in (`theI`/`the_0` proved); the axiom of infinity is declared here |
| [`pair`](pair.lp) | 12/33 | ordered pairs are concrete Kuratowski `{{a},{a,b}}`; projections need `fst_conv`/`snd_conv` (no definitional reduction) |
| [`equalities`](equalities.lp) | 15/263 | the Boolean-algebra-of-sets simp corpus; ports the downstream-used subset — every ported lemma faithful |
| [`func`](func.lp) | 17/122 | `Image` is the **function** image (`f` applied across `C ∩ domain f`), agreeing with Isabelle's relational image only when `function f` holds — genuine relations use `rel_image_sing`; `restrict_apply`/`apply_iff` carry extra well-formedness hypotheses |
| [`Bool`](Bool_ZF.lp) | 6/44 | deliberate `cond`-focused subset of Isabelle's `Bool` |
| [`Sum`](Sum.lp) | 39/47 | disjoint sums, `case`, `Part`; ported subset faithful |
| [`QPair`](QPair.lp) | 70/71 | quasi-pairs / quasi-sums; faithful and complete |
| [`Fixedpt`](Fixedpt.lp) | 13/41 | Knaster–Tarski least/greatest fixed points (`lfp`/`gfp`) |
| [`Trancl`](Trancl.lp) | 19/60 | reflexive/transitive closure |
| [`WF`](WF.lp) | 18/47 | well-founded relations and recursion |
| [`Perm`](Perm.lp) | 27/88 | injections, surjections, bijections, inverses, composition |
| [`EquivClass`](EquivClass.lp) | 30/32 | quotients; faithful and complete (only `respects`/`respects2` sugar unported) |
| [`Ordinal`](Ordinal.lp) | 89/154 | `lt`/`le` carry `Ord` exactly as Isabelle; `Ord_linear`, transfinite induction |
| [`OrdLeast`](OrdLeast.lp) | — | port-internal split of Isabelle's least-ordinal `Least` (μ) operator, ε-free; homed separately so downstream need not import `Cardinal` |
| [`OrdQuant`](OrdQuant.lp) | 52/63 | bounded ordinal quantifiers `oall`/`oex`, `OUN` |
| [`Nat`](Nat_ZF.lp) | 40/52 | naturals; `omega` uses a provably-equal non-`lfp` body |
| [`Epsilon`](Epsilon.lp) | 40/62 | ε-recursion, `rank`, transitive closure `eclose` |
| [`Order`](Order.lp) | 95/95 | partial/total/well-orders, order isomorphisms; `well_ord_trichotomy` now proved |
| [`OrderArith`](OrderArith.lp) | 76/76 | order sums/products `radd`/`rmult`/`rvimage` and their bijections — complete (was 7 admits) |
| [`Inductive`](Inductive.lp) | 3/3 | `inductive`-package glue; faithful and complete |
| [`Finite`](Finite.lp) | 25/25 | `Fin`/`FiniteFun` from Knaster–Tarski; faithful and complete |
| [`OrderType`](OrderType.lp) | 124/124 | order types, `ordermap`/`ordertype`, ordinal `oadd`/`omult` with associativity & distributivity — complete (was ~78 admits) |
| [`Cardinal`](Cardinal.lp) | 160/160 | **the north star** — cardinality (`cardinal`), `Card`, Cantor, Schröder–Bernstein; complete (was a skeleton) |
| [`Univ`](Univ.lp) | 27/114 | `Vfrom`/`Vset`/`univ`, `Vrec`; fully proved *without* importing `Cardinal` (Isabelle's `Univ` imports it, but the ported lemmas do not need it) |
| [`Arith`](Arith.lp) | 95/101 | natural-number arithmetic `+`/`×`/`−`/`div`/`mod` |
| [`ArithSimp`](ArithSimp.lp) | 78/79 | arithmetic simplification lemmas |
| [`Bin`](Bin.lp) | 94/99 | binary integer numerals |
| [`Int`](Int.lp) | 182/186 | integers as equivalence classes of nat pairs |
| [`IntDiv`](IntDiv.lp) | 202/202 | integer division/modulo via `posDivAlg`/`negDivAlg`; complete |
| [`List`](List.lp) | 171/171 | finite lists, `map`/`app`/`rev`/`length`; complete |
| [`CardinalArith`](CardinalArith.lp) | 94/94 | cardinal `+`/`×`, `csucc`, `InfCard`; complete |
| [`Zorn`](Zorn.lp) | 41/41 | Zorn's lemma, Hausdorff maximal principle; complete |
| [`Cardinal_AC`](Cardinal_AC.lp) | 22/22 | cardinal arithmetic with choice; complete |
| [`QUniv`](QUniv.lp) | 39/39 | quasi-universe for codatatypes; complete |
| [`InfDatatype`](InfDatatype.lp) | 17/19 | infinite-branching datatypes |
| [`Datatype`](Datatype.lp) | — | `datatype`/`codatatype` package glue — no object-level statements (concrete datatypes are built at the `lfp`/`Vset` level in their own modules) |
| [`AC`](AC.lp) | 8/8 | the Axiom of Choice (functional form) as the sole axiom, plus its consequences — all proved |
| [`ZF`](ZF.lp) | 5/10 | transfinite-recursion section of `ZF.thy` (`transrec3`) + the ordinal predecessor `pred` |
| [`ZFC`](ZFC.lp) | — | marker bundling `ZF` + `InfDatatype`; empty theory body |

## Dependency tree

Each theory is followed by the theories it imports, read from the Isabelle
`imports` declarations — the mathematical dependency DAG. It reads top-down:
every import sits above the theory that needs it, foundations first. The port
builds on Lambdapi's `Stdlib.*` wherever Isabelle uses `FOL`. **Every node
below is ported and fully proved.**

```text
Foundations
  ZF_Base       ← FOL
  upair         ← ZF_Base
  pair          ← upair
  equalities    ← pair
  Bool          ← pair

Functions · sums · fixed points
  Sum           ← Bool, equalities
  Fixedpt       ← equalities
  func          ← equalities, Sum
  QPair         ← Sum, func
  Perm          ← func

Relations · well-foundedness
  Trancl        ← Fixedpt, Perm
  WF            ← Trancl
  EquivClass    ← Trancl, Perm

Ordinals · naturals
  Ordinal       ← WF, Bool, equalities
  OrdQuant      ← Ordinal
  Nat           ← OrdQuant, Bool
  Epsilon       ← Nat

Orders · inductive definitions
  Order         ← WF, Perm
  OrderArith    ← Order, Sum, Ordinal
  Inductive     ← Fixedpt, QPair, Nat
  Finite        ← Inductive, Epsilon, Nat

Toward Cardinal  (north star)
  OrderType     ← OrderArith, OrdQuant, Nat
  Cardinal      ← OrderType, Finite, Nat, Sum
  Univ          ← Epsilon, Cardinal          · port proves Univ without the Cardinal import (used lemmas don't need it)

Arithmetic · integers · datatypes
  Arith         ← Univ
  ArithSimp     ← Arith
  QUniv         ← Univ, QPair
  Datatype      ← Inductive, Univ, QUniv
  Int           ← EquivClass, ArithSimp
  List          ← Datatype, ArithSimp
  Bin           ← Int, Datatype
  IntDiv        ← Bin, OrderArith
  CardinalArith ← Cardinal, OrderArith, ArithSimp, Finite

Umbrella · choice
  ZF            ← List, IntDiv, CardinalArith
  AC            ← ZF                            · port depends only on ZF_Base
  Zorn          ← OrderArith, AC, Inductive
  Cardinal_AC   ← CardinalArith, Zorn
  InfDatatype   ← Datatype, Univ, Finite, Cardinal_AC
  ZFC           ← ZF, InfDatatype
```
