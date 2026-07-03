# lambdapi-zf

A [Lambdapi](https://github.com/Deducteam/lambdapi) translation of the
**Isabelle/ZF** object logic — Zermelo–Fraenkel set theory in first-order logic,
ported theory-for-theory into the λΠ-calculus modulo rewriting. The modules
mirror the structure and lemma names of upstream Isabelle/ZF (`src/ZF/`); the
original `.thy` sources are kept under [`isabelle-src/`](isabelle-src/).

Every module type-checks. The foundational layer is fully proved; the frontier
toward `Cardinal` is present as faithful skeletons — every definition and
statement is there, with the harder proofs left as `admit`. Legend: **✅**
proved · **🔨** proofs in progress · **🧩** skeleton · **—** not yet ported.
Run `python3 tools/audit.py --status` for the live version of this table.

| Theory | Status |
|---|---|
| `ZF_Base`      | ✅ |
| `upair`        | ✅ |
| `pair`         | ✅ |
| `equalities`   | ✅ |
| `func`         | ✅ |
| `Bool`         | ✅ |
| `Sum`          | ✅ |
| `QPair`        | ✅ |
| `Fixedpt`      | ✅ |
| `Trancl`       | ✅ |
| `WF`           | ✅ |
| `Ordinal`      | ✅ |
| `OrdQuant`     | ✅ |
| `Nat`          | ✅ |
| `Epsilon`      | ✅ |
| `Inductive`    | ✅ |
| `EquivClass`   | ✅ |
| `AC`           | ✅ |
| `Univ`         | ✅ |
| `Perm`         | 🔨 2 admits |
| `Order`        | 🔨 1 admit |
| `OrderArith`   | 🔨 18 admits |
| `Finite`       | 🔨 24 admits |
| `OrderType`    | 🧩 116 admits |
| `Cardinal`     | 🧩 153 admits |
| `Arith`        | — |
| `ArithSimp`    | — |
| `Bin`          | — |
| `Int`          | — |
| `IntDiv`       | — |
| `List`         | — |
| `CardinalArith`| — |
| `Zorn`         | — |
| `Cardinal_AC`  | — |
| `Datatype`     | — |
| `InfDatatype`  | — |
| `QUniv`        | — |
| `ZFC`          | — |
