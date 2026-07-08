// ZF.Datatype — Datatype and CoDatatype Definitions
//
// Isabelle source: Datatype.thy (Paulson).  The entire theory is the ML
// implementation of the `datatype`/`codatatype` definition PACKAGE
// (Tools/datatype_package.ML) plus a `simproc_setup` for constructor
// freeness reasoning — there is no object-level `definition`, `lemma`, or
// `theorem` in it to port.  (Compare Inductive.lp, which is the analogous
// glue file for the `inductive` package and DOES carry three tiny
// object-level lemmas; Datatype.thy carries none.)
//
// Concrete datatypes built with this package (e.g. `list`, `Bin`'s binary
// integers) are ported directly at the lfp/Vset level in their own modules,
// the same way Finite.lp hand-built `Fin`/`FiniteFun` from the package's
// generated operator.  This file exists only so `require open ZF.Datatype`
// resolves for those downstream modules.

require open ZF.Inductive ZF.Univ ZF.QUniv;
