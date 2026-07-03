# lambdapi-zf

A [Lambdapi](https://github.com/Deducteam/lambdapi) port of **Isabelle/ZF** —
Zermelo–Fraenkel set theory in first-order logic. Each module translates the
corresponding theory from Isabelle's `src/ZF/`; the `.thy` sources are under
[`isabelle-src/`](isabelle-src/).

Status: **●** proved · **◐** in progress (admits or axiom-asserted lemmas) ·
**○** not ported. The *def* and *lemma* columns are Isabelle definitions /
lemmas covered over the total in the source; a lemma counts only once proved.
Counts are approximate — the port renames and reorganizes results — and
foundation modules port only the subset used downstream, so their coverage reads
low though every proof is complete.

|  | Theory | defs | lemmas | Notes |
|:-:|---|--:|--:|---|
| ● | [`ZF_Base`](ZF_Base.lp) | 28/36 | 36/68 | |
| ● | [`upair`](upair.lp) | — | 45/83 | |
| ● | [`pair`](pair.lp) | — | 24/27 | |
| ● | [`equalities`](equalities.lp) | — | 20/260 | |
| ● | [`func`](func.lp) | 0/1 | 27/116 | |
| ● | [`Bool`](Bool_ZF.lp) | 1/9 | 7/31 | |
| ● | [`Sum`](Sum.lp) | 4/5 | 35/35 | |
| ● | [`QPair`](QPair.lp) | 11/11 | 55/55 | |
| ● | [`Fixedpt`](Fixedpt.lp) | 3/3 | 6/38 | |
| ● | [`Trancl`](Trancl.lp) | 8/10 | 25/45 | |
| ● | [`WF`](WF.lp) | 5/7 | 23/38 | |
| ● | [`Ordinal`](Ordinal.lp) | 6/6 | 94/141 | |
| ● | [`OrdQuant`](OrdQuant.lp) | 6/6 | 50/59 | |
| ● | [`Nat`](Nat_ZF.lp) | 3/9 | 18/39 | |
| ● | [`Epsilon`](Epsilon.lp) | 3/6 | 31/49 | |
| ● | [`Inductive`](Inductive.lp) | — | 3/3 | |
| ● | [`EquivClass`](EquivClass.lp) | 3/5 | 27/27 | |
| ◐ | [`AC`](AC.lp) | — | 0/8 | axiom of choice asserted |
| ◐ | [`Univ`](Univ.lp) | 2/5 | 0/96 | lemmas asserted as axioms |
| ◐ | [`Order`](Order.lp) | 9/13 | 84/85 | |
| ◐ | [`Perm`](Perm.lp) | 3/5 | 22/81 | |
| ◐ | [`OrderArith`](OrderArith.lp) | 6/6 | 53/68 | |
| ◐ | [`Finite`](Finite.lp) | 1/1 | 4/22 | `FiniteFun` unproved |
| ◐ | [`OrderType`](OrderType.lp) | 8/8 | 0/112 | skeleton |
| ◐ | [`Cardinal`](Cardinal.lp) | 7/7 | 0/143 | skeleton |
| ○ | [`Arith`](isabelle-src/Arith.thy) | 0/9 | 0/88 | |
| ○ | [`ArithSimp`](isabelle-src/ArithSimp.thy) | — | 0/114 | |
| ○ | [`Bin`](isabelle-src/Bin.thy) | 0/1 | 0/130 | |
| ○ | [`Int`](isabelle-src/Int.thy) | 0/18 | 0/166 | |
| ○ | [`IntDiv`](isabelle-src/IntDiv.thy) | 0/8 | 0/197 | |
| ○ | [`List`](isabelle-src/List.thy) | 0/7 | 0/162 | |
| ○ | [`CardinalArith`](isabelle-src/CardinalArith.thy) | 0/6 | 0/85 | |
| ○ | [`Zorn`](isabelle-src/Zorn.thy) | 0/6 | 0/32 | |
| ○ | [`Cardinal_AC`](isabelle-src/Cardinal_AC.thy) | — | 0/21 | |
| ○ | [`Datatype`](isabelle-src/Datatype.thy) | — | — | package |
| ○ | [`InfDatatype`](isabelle-src/InfDatatype.thy) | — | 0/7 | |
| ○ | [`QUniv`](isabelle-src/QUniv.thy) | 0/1 | 0/21 | |
| ○ | [`ZFC`](isabelle-src/ZFC.thy) | — | — | AC axiom |

## Dependency tree

Each theory is followed by the theories it imports, read from the Isabelle
`imports` declarations — the mathematical dependency DAG. It reads top-down:
every import sits above the theory that needs it, foundations first. The port
builds on Lambdapi's `Stdlib.*` wherever Isabelle uses `FOL`.

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
  Univ          ← Epsilon, Cardinal          · port cuts the Cardinal edge (lemmas axiomatized)

Arithmetic · datatypes  (off the Cardinal route — not yet ported)
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
  ZF            ← List, IntDiv, CardinalArith   · re-exports all of core ZF
  AC            ← ZF                            · port depends only on ZF_Base
  Zorn          ← OrderArith, AC, Inductive
  Cardinal_AC   ← CardinalArith, Zorn
  InfDatatype   ← Datatype, Univ, Finite, Cardinal_AC
  ZFC           ← ZF, InfDatatype
```
