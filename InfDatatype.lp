// ZF.InfDatatype — Infinite-Branching Datatype Definitions
// Faithful SKELETON port of isabelle-src/InfDatatype.thy.
// Every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/InfDatatype.thy.)
//
// Most facts here are Isabelle `lemmas foo = bar [THEN baz, OF qux]` derived
// aliases built from VLimit-family facts in Univ.thy (`Limit_VfromE`,
// `Pair_in_VLimit`, `Inl_in_VLimit`, `Inr_in_VLimit`, `zero_in_VLimit`,
// `nat_into_VLimit`) — NONE of which are ported yet in this repo's Univ.lp
// (a "base file" with known simp-noise-heavy gaps per CLAUDE.md §4).  Rather
// than add those intermediate names to Univ.lp, each alias below is rendered
// directly as the final COMPOSED fact (per CLAUDE.md's standard treatment of
// this idiom — see Int.lp's eq_intrelD/zless_asym for the precedent), using
// only already-existing primitives (Vfrom, Limit, csucc, InfCard, Pair, Inl,
// Inr, cardinal).  The exact source statements of the Univ.thy lemmas being
// composed were read directly from isabelle-src/Univ.thy to keep the
// derivations exact, not guessed.
//
// `Data_Arg_intros`/`inf_datatype_intros` are named hint BUNDLES (bags of
// pre-existing facts for the ML datatype package's type-checking tactic),
// not single Prop-typed statements — skipped, same precedent as `div_rls`.

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func ZF.Fixedpt
             ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum ZF.Ordinal ZF.OrdQuant
             ZF.Nat_ZF ZF.QPair ZF.Epsilon ZF.Inductive ZF.Univ ZF.QUniv
             ZF.Datatype ZF.Order ZF.OrderArith ZF.OrderType ZF.Finite
             ZF.Cardinal ZF.Arith ZF.ArithSimp ZF.CardinalArith ZF.Cardinal_AC;

// fun_Limit_VfromE = Limit_VfromE [OF apply_funtype InfCard_csucc [THEN InfCard_is_Limit]]
opaque symbol fun_Limit_VfromE (f D A K d : τ ι) (Q : Prop) :
  π (f ∈ Pi D (λ _, Vfrom A (csucc K))) → π (d ∈ D) → π (InfCard K) →
  (Π (x : τ ι), π (lt x (csucc K)) → π (fapply f d ∈ Vfrom A x) → π Q) → π Q ≔
begin admit end;

opaque symbol fun_Vcsucc_lemma (f D A K : τ ι) :
  π (f ∈ Pi D (λ _, Vfrom A (csucc K))) → π (le (cardinal D) K) → π (InfCard K) →
  π (`∃ (j : τ ι), f ∈ Pi D (λ _, Vfrom A j) ∧ lt j (csucc K)) ≔
begin admit end;

opaque symbol subset_Vcsucc (D A K : τ ι) :
  π (D ⊆ Vfrom A (csucc K)) → π (le (cardinal D) K) → π (InfCard K) →
  π (`∃ (j : τ ι), D ⊆ Vfrom A j ∧ lt j (csucc K)) ≔
begin admit end;

// Version for arbitrary index sets
opaque symbol fun_Vcsucc (D A K : τ ι) :
  π (le (cardinal D) K) → π (InfCard K) → π (D ⊆ Vfrom A (csucc K)) →
  π (Pi D (λ _, Vfrom A (csucc K)) ⊆ Vfrom A (csucc K)) ≔
begin admit end;

opaque symbol fun_in_Vcsucc (f D A K : τ ι) :
  π (f ∈ Pi D (λ _, Vfrom A (csucc K))) → π (le (cardinal D) K) → π (InfCard K) →
  π (D ⊆ Vfrom A (csucc K)) → π (f ∈ Vfrom A (csucc K)) ≔
begin admit end;

// Remove ⊆ from the rule above
// fun_in_Vcsucc' = fun_in_Vcsucc [OF _ _ _ subsetI]
opaque symbol fun_in_Vcsucc' (f D A K : τ ι) :
  π (f ∈ Pi D (λ _, Vfrom A (csucc K))) → π (le (cardinal D) K) → π (InfCard K) →
  (Π (x : τ ι), π (x ∈ D) → π (x ∈ Vfrom A (csucc K))) →
  π (f ∈ Vfrom A (csucc K)) ≔
begin admit end;

// ** Version where K itself is the index set **

opaque symbol Card_fun_Vcsucc (K A : τ ι) :
  π (InfCard K) → π (Pi K (λ _, Vfrom A (csucc K)) ⊆ Vfrom A (csucc K)) ≔
begin admit end;

opaque symbol Card_fun_in_Vcsucc (f K A : τ ι) :
  π (f ∈ Pi K (λ _, Vfrom A (csucc K))) → π (InfCard K) → π (f ∈ Vfrom A (csucc K)) ≔
begin admit end;

opaque symbol Limit_csucc (K : τ ι) : π (InfCard K) → π (Limit (csucc K)) ≔
begin admit end;

// Pair_in_Vcsucc = Pair_in_VLimit [OF _ _ Limit_csucc]
opaque symbol Pair_in_Vcsucc (a b A K : τ ι) :
  π (a ∈ Vfrom A (csucc K)) → π (b ∈ Vfrom A (csucc K)) → π (InfCard K) →
  π (Pair a b ∈ Vfrom A (csucc K)) ≔
begin admit end;

// Inl_in_Vcsucc = Inl_in_VLimit [OF _ Limit_csucc]
opaque symbol Inl_in_Vcsucc (a A K : τ ι) :
  π (a ∈ Vfrom A (csucc K)) → π (InfCard K) → π (Inl a ∈ Vfrom A (csucc K)) ≔
begin admit end;

// Inr_in_Vcsucc = Inr_in_VLimit [OF _ Limit_csucc]
opaque symbol Inr_in_Vcsucc (b A K : τ ι) :
  π (b ∈ Vfrom A (csucc K)) → π (InfCard K) → π (Inr b ∈ Vfrom A (csucc K)) ≔
begin admit end;

// zero_in_Vcsucc = Limit_csucc [THEN zero_in_VLimit]
opaque symbol zero_in_Vcsucc (A K : τ ι) :
  π (InfCard K) → π (empty ∈ Vfrom A (csucc K)) ≔
begin admit end;

// nat_into_Vcsucc = nat_into_VLimit [OF _ Limit_csucc]
opaque symbol nat_into_Vcsucc (n A K : τ ι) :
  π (n ∈ omega) → π (InfCard K) → π (n ∈ Vfrom A (csucc K)) ≔
begin admit end;

// For handling Cardinals of the form  nat ∪ |X|

// InfCard_nat_Un_cardinal = InfCard_Un [OF InfCard_nat Card_cardinal]
opaque symbol InfCard_nat_Un_cardinal (A : τ ι) : π (InfCard (Un omega (cardinal A))) ≔
begin admit end;

// le_nat_Un_cardinal = Un_upper2_le [OF Ord_nat Card_cardinal [THEN Card_is_Ord]]
opaque symbol le_nat_Un_cardinal (A : τ ι) :
  π (le (cardinal A) (Un omega (cardinal A))) ≔
begin admit end;

// UN_upper_cardinal = UN_upper [THEN subset_imp_lepoll, THEN lepoll_imp_cardinal_le]
opaque symbol UN_upper_cardinal (a A : τ ι) (B : τ ι → τ ι) :
  π (a ∈ A) → π (le (cardinal (B a)) (cardinal (Union (RepFun A B)))) ≔
begin admit end;
