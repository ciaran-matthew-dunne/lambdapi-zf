// ZF.Cardinal_AC — Cardinal Arithmetic Using AC
// Faithful SKELETON port of isabelle-src/Cardinal_AC.thy.
// Every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/Cardinal_AC.thy — "these results help justify
// infinite-branching datatypes".)
//
// Several lemmas here (cardinal_UN_le, cardinal_UN_lt_csucc,
// cardinal_UN_Ord_lt_csucc, inj_UN_subset, le_UN_Ord_lt_csucc) are stated in
// Isabelle with SCHEMATIC FUNCTION VARIABLES (`X`, `j`, `C` : i⇒i, e.g.
// "⋀i. i∈K ⟹ |X(i)| ≤ K"); these become Π-bound `τ ι → τ ι` parameters here,
// exactly as CardinalArith.lp's own function-valued lemmas already do.
// Isar `assumes ... shows ...` blocks are flattened to ordinary curried
// hypotheses in declaration order, per CLAUDE.md's standard treatment.

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func ZF.Fixedpt
             ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum ZF.Ordinal ZF.OrdQuant
             ZF.Nat_ZF ZF.QPair ZF.Epsilon ZF.Inductive ZF.Order ZF.OrderArith
             ZF.OrderType ZF.Finite ZF.Cardinal ZF.Arith ZF.ArithSimp
             ZF.CardinalArith ZF.AC ZF.Inductive ZF.Zorn;

// ===========================================================================
// Strengthened Forms of Existing Theorems on Cardinals
// ===========================================================================

opaque symbol cardinal_eqpoll (A : τ ι) : π (eqpoll (cardinal A) A) ≔
begin admit end;

// The theorem ||A|| = |A|
opaque symbol cardinal_idem (A : τ ι) : π (cardinal (cardinal A) = cardinal A) ≔
begin admit end;

opaque symbol cardinal_eqE (X Y : τ ι) :
  π (cardinal X = cardinal Y) → π (eqpoll X Y) ≔
begin admit end;

opaque symbol cardinal_eqpoll_iff (X Y : τ ι) :
  π (cardinal X = cardinal Y ⇔ eqpoll X Y) ≔
begin admit end;

opaque symbol cardinal_disjoint_Un (A B C D : τ ι) :
  π (cardinal A = cardinal B) → π (cardinal C = cardinal D) →
  π (Int A C = empty) → π (Int B D = empty) →
  π (cardinal (Un A C) = cardinal (Un B D)) ≔
begin admit end;

opaque symbol lepoll_imp_cardinal_le (A B : τ ι) :
  π (lepoll A B) → π (le (cardinal A) (cardinal B)) ≔
begin admit end;

opaque symbol cadd_assoc (i j k : τ ι) :
  π (cadd (cadd i j) k = cadd i (cadd j k)) ≔
begin admit end;

opaque symbol cmult_assoc (i j k : τ ι) :
  π (cmult (cmult i j) k = cmult i (cmult j k)) ≔
begin admit end;

opaque symbol cadd_cmult_distrib (i j k : τ ι) :
  π (cmult (cadd i j) k = cadd (cmult i k) (cmult j k)) ≔
begin admit end;

opaque symbol InfCard_square_eq (A : τ ι) :
  π (InfCard (cardinal A)) → π (eqpoll (Sigma A (λ _, A)) A) ≔
begin admit end;

// ===========================================================================
// The relationship between cardinality and le-pollence
// ===========================================================================

opaque symbol Card_le_imp_lepoll (A B : τ ι) :
  π (le (cardinal A) (cardinal B)) → π (lepoll A B) ≔
begin admit end;

opaque symbol le_Card_iff (K A : τ ι) :
  π (Card K) → π (le (cardinal A) K ⇔ lepoll A K) ≔
begin admit end;

opaque symbol cardinal_0_iff_0 (A : τ ι) : π (cardinal A = empty ⇔ A = empty) ≔
begin admit end;

opaque symbol cardinal_lt_iff_lesspoll (i A : τ ι) :
  π (Ord i) → π (lt i (cardinal A) ⇔ lesspoll i A) ≔
begin admit end;

opaque symbol cardinal_le_imp_lepoll (i A : τ ι) :
  π (le i (cardinal A)) → π (lesspoll i A ∨ eqpoll i A) ≔
begin admit end;

// ===========================================================================
// Other Applications of AC
// ===========================================================================

opaque symbol surj_implies_inj (f X Y : τ ι) :
  π (f ∈ surj X Y) → π (`∃ (g : τ ι), g ∈ inj Y X) ≔
begin admit end;

// Kunen's Lemma 10.20
opaque symbol surj_implies_cardinal_le (f X Y : τ ι) :
  π (f ∈ surj X Y) → π (le (cardinal Y) (cardinal X)) ≔
begin admit end;

// Kunen's Lemma 10.21
opaque symbol cardinal_UN_le (K : τ ι) (X : τ ι → τ ι) :
  π (InfCard K) → (Π (i : τ ι), π (i ∈ K) → π (le (cardinal (X i)) K)) →
  π (le (cardinal (Union (RepFun K X))) K) ≔
begin admit end;

// The same again, using csucc
opaque symbol cardinal_UN_lt_csucc (K : τ ι) (X : τ ι → τ ι) :
  π (InfCard K) → (Π (i : τ ι), π (i ∈ K) → π (lt (cardinal (X i)) (csucc K))) →
  π (lt (cardinal (Union (RepFun K X))) (csucc K)) ≔
begin admit end;

// The same again, for a union of ordinals. In use, j(i) is a bit like
// rank(i), the least ordinal j such that i:Vfrom(A,j).
opaque symbol cardinal_UN_Ord_lt_csucc (K : τ ι) (j : τ ι → τ ι) :
  π (InfCard K) → (Π (i : τ ι), π (i ∈ K) → π (lt (j i) (csucc K))) →
  π (lt (Union (RepFun K j)) (csucc K)) ≔
begin admit end;

// ===========================================================================
// The Main Result for Infinite-Branching Datatypes
// ===========================================================================

// As above, but the index set need not be a cardinal. Work backwards along
// the injection from W into K, given that W≠0.
opaque symbol inj_UN_subset (f A B a : τ ι) (C : τ ι → τ ι) :
  π (f ∈ inj A B) → π (a ∈ A) →
  π (Union (RepFun A C) ⊆
     Union (RepFun B (λ y, C (If (y ∈ range f) (fapply (converse f) y) a)))) ≔
begin admit end;

opaque symbol le_UN_Ord_lt_csucc (K W : τ ι) (j : τ ι → τ ι) :
  π (InfCard K) → π (le (cardinal W) K) →
  (Π (w : τ ι), π (w ∈ W) → π (lt (j w) (csucc K))) →
  π (lt (Union (RepFun W j)) (csucc K)) ≔
begin admit end;
