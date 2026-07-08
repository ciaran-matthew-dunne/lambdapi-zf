// ZF.ZFC — marker theory
//
// Isabelle source: ZFC.thy — `theory ZFC imports ZF InfDatatype begin end`.
// The theory body is empty: it exists only to bundle "plain ZF" together
// with the infinite-branching-datatype machinery under one import name.
// No object-level `definition`/`lemma`/`theorem` to port.  This file exists
// only so `require open ZF.ZFC` resolves for anything that names it.

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func ZF.Fixedpt
             ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum ZF.Ordinal ZF.OrdQuant
             ZF.Nat_ZF ZF.QPair ZF.Epsilon ZF.Inductive ZF.Univ ZF.QUniv
             ZF.Datatype ZF.Order ZF.OrderArith ZF.OrderType ZF.Finite
             ZF.Cardinal ZF.Arith ZF.ArithSimp ZF.CardinalArith
             ZF.Cardinal_AC ZF.InfDatatype;
