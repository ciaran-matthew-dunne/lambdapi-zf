# lambdapi-zf

A [Lambdapi](https://github.com/Deducteam/lambdapi) port of **Isabelle/ZF** —
Zermelo–Fraenkel set theory in first-order logic. Each module translates the
corresponding theory from Isabelle's `src/ZF/` and keeps its lemma names; the
`.thy` sources are under [`isabelle-src/`](isabelle-src/).

Every module type-checks. The `admits` column counts the proof goals left open
(`0` = fully proved, `—` = not yet ported); run `python3 tools/audit.py --status`
for the live version.

| Theory | admits |
|---|---:|
| `ZF_Base`       |  0 |
| `upair`         |  0 |
| `pair`          |  0 |
| `equalities`    |  0 |
| `func`          |  0 |
| `Bool`          |  0 |
| `Sum`           |  0 |
| `QPair`         |  0 |
| `Fixedpt`       |  0 |
| `Trancl`        |  0 |
| `WF`            |  0 |
| `Ordinal`       |  0 |
| `OrdQuant`      |  0 |
| `Nat`           |  0 |
| `Epsilon`       |  0 |
| `Inductive`     |  0 |
| `EquivClass`    |  0 |
| `AC`            |  0 |
| `Univ`          |  0 |
| `Order`         |  1 |
| `Perm`          |  2 |
| `OrderArith`    | 18 |
| `Finite`        | 24 |
| `OrderType`     | 116 |
| `Cardinal`      | 153 |
| `Arith`         |  — |
| `ArithSimp`     |  — |
| `Bin`           |  — |
| `Int`           |  — |
| `IntDiv`        |  — |
| `List`          |  — |
| `CardinalArith` |  — |
| `Zorn`          |  — |
| `Cardinal_AC`   |  — |
| `Datatype`      |  — |
| `InfDatatype`   |  — |
| `QUniv`         |  — |
| `ZFC`           |  — |
