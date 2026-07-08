// ZF.ZFC — marker theory
//
// Isabelle source: ZFC.thy — `theory ZFC imports ZF InfDatatype begin end`.
// The theory body is empty: it exists only to bundle "plain ZF" together
// with the infinite-branching-datatype machinery under one import name.
// No object-level `definition`/`lemma`/`theorem` to port.  This file exists
// only so `require open ZF.ZFC` resolves for anything that names it.

require open ZF.ZF ZF.InfDatatype;
