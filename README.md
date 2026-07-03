# lambdapi-zf

A [Lambdapi](https://github.com/Deducteam/lambdapi) port of **Isabelle/ZF** —
Zermelo–Fraenkel set theory in first-order logic. Each module translates the
corresponding theory from Isabelle's `src/ZF/` and keeps its lemma names; the
`.thy` sources are under [`isabelle-src/`](isabelle-src/).

Status: **●** proved (no `admit`s) · **◐** proofs in progress · **○** not yet
ported. The *def & lemma* column is Isabelle statements present over the total in
the source `.thy` (`python3 tools/audit.py --status`); foundation modules port
only the subset used downstream, so they read below their total though every
proof is complete.

| | Theory | def & lemma | admits | Notes |
|:-:|---|--:|--:|---|
| ● | `ZF_Base`       |  41/110 | 0 | |
| ● | `upair`         |  64/101 | 0 | |
| ● | `pair`          |   32/33 | 0 | |
| ● | `equalities`    |  21/263 | 0 | |
| ● | `func`          |  53/122 | 0 | |
| ● | `Bool`          |    9/44 | 0 | |
| ● | `Sum`           |   43/47 | 0 | |
| ● | `QPair`         |   71/71 | 0 | |
| ● | `Fixedpt`       |   33/41 | 0 | |
| ● | `Trancl`        |   59/60 | 0 | |
| ● | `WF`            |   44/47 | 0 | |
| ● | `Ordinal`       | 152/154 | 0 | |
| ● | `OrdQuant`      |   60/63 | 0 | |
| ● | `Nat`           |   16/52 | 0 | |
| ● | `Epsilon`       |   50/62 | 0 | |
| ● | `Inductive`     |     3/3 | 0 | |
| ● | `EquivClass`    |   30/32 | 0 | |
| ● | `AC`            |     7/8 | 0 | |
| ● | `Univ`          |  49/114 | 0 | |
| ◐ | `Order`         |   89/95 | 1 | well-ordering trichotomy |
| ◐ | `Perm`          |   55/88 | 2 | |
| ◐ | `OrderArith`    |   76/76 | 18 | |
| ◐ | `Finite`        |   25/25 | 24 | `FiniteFun` side unproved |
| ◐ | `OrderType`     | 124/124 | 116 | skeleton |
| ◐ | `Cardinal`      | 160/160 | 153 | skeleton |
| ○ | `Arith`         |   0/101 | — | |
| ○ | `ArithSimp`     |    0/79 | — | |
| ○ | `Bin`           |    0/99 | — | |
| ○ | `Int`           |   0/186 | — | |
| ○ | `IntDiv`        |   0/209 | — | |
| ○ | `List`          |   0/171 | — | |
| ○ | `CardinalArith` |    0/94 | — | |
| ○ | `Zorn`          |    0/41 | — | |
| ○ | `Cardinal_AC`   |    0/22 | — | |
| ○ | `Datatype`      |       — | — | package, no object lemmas |
| ○ | `InfDatatype`   |    0/19 | — | |
| ○ | `QUniv`         |    0/39 | — | |
| ○ | `ZFC`           |       — | — | AC as an axiom |
