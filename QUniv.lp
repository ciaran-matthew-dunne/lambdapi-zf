// ZF.QUniv — A Small Universe for Lazy Recursive Types
// Faithful SKELETON port of isabelle-src/QUniv.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/QUniv.thy.)
//
// The two `rep_datatype` blocks at the top of the .thy re-register the
// already-existing `sum`/`qsum` as datatypes (elimination = sumE/qsumE,
// already ported in Sum.lp/QPair.lp) — no new object-level content.

require open ZF.Univ ZF.QPair;

// ===========================================================================
// Definitions
// ===========================================================================

// quniv(A) ≡ Pow(univ(eclose(A)))
constant symbol quniv (A : τ ι) : τ ι;
constant symbol quniv_def (A : τ ι) :
  π (quniv A = Pow (univ (eclose A)));

// ===========================================================================
// Properties involving Transset and Sum
// ===========================================================================

opaque symbol Transset_includes_summands (C A B : τ ι) :
  π (Transset C) → π (sum A B ⊆ C) → π (A ⊆ C ∧ B ⊆ C) ≔
begin admit end;

opaque symbol Transset_sum_Int_subset (C A B : τ ι) :
  π (Transset C) → π (Int (sum A B) C ⊆ sum (Int A C) (Int B C)) ≔
begin admit end;

// ===========================================================================
// Introduction and Elimination Rules
// ===========================================================================

opaque symbol qunivI (X A : τ ι) : π (X ⊆ univ (eclose A)) → π (X ∈ quniv A) ≔
begin
  assume X A h;
  rewrite quniv_def;
  refine PowI X (univ (eclose A)) h
end;

opaque symbol qunivD (X A : τ ι) : π (X ∈ quniv A) → π (X ⊆ univ (eclose A)) ≔
begin
  assume X A h;
  have h' : π (X ∈ Pow (univ (eclose A)))
    { refine ind_eq (eq_sym (quniv_def A)) (λ w, X ∈ w) h };
  refine PowD X (univ (eclose A)) h'
end;

opaque symbol quniv_mono (A B : τ ι) : π (A ⊆ B) → π (quniv A ⊆ quniv B) ≔
begin admit end;

// ===========================================================================
// Closure Properties
// ===========================================================================

opaque symbol univ_eclose_subset_quniv (A : τ ι) : π (univ (eclose A) ⊆ quniv A) ≔
begin admit end;

// Key property for proving A_subset_quniv; requires eclose in definition of quniv
opaque symbol univ_subset_quniv (A : τ ι) : π (univ A ⊆ quniv A) ≔
begin admit end;

opaque symbol univ_into_quniv (a A : τ ι) : π (a ∈ univ A) → π (a ∈ quniv A) ≔
begin admit end;

opaque symbol Pow_univ_subset_quniv (A : τ ι) : π (Pow (univ A) ⊆ quniv A) ≔
begin admit end;

opaque symbol univ_subset_into_quniv (A B : τ ι) : π (A ⊆ univ B) → π (A ∈ quniv B) ≔
begin admit end;

opaque symbol zero_in_quniv (A : τ ι) : π (empty ∈ quniv A) ≔
begin admit end;

opaque symbol one_in_quniv (A : τ ι) : π (one ∈ quniv A) ≔
begin admit end;

opaque symbol two_in_quniv (A : τ ι) : π (succ one ∈ quniv A) ≔
begin admit end;

opaque symbol A_subset_quniv (A : τ ι) : π (A ⊆ quniv A) ≔
begin admit end;

opaque symbol A_into_quniv (a A : τ ι) : π (a ∈ A) → π (a ∈ quniv A) ≔
begin admit end;

// *** univ(A) closure for Quine-inspired pairs and injections ***

// Quine ordered pairs
opaque symbol QPair_subset_univ (a b A : τ ι) :
  π (a ⊆ univ A) → π (b ⊆ univ A) → π (QPair a b ⊆ univ A) ≔
begin admit end;

// ===========================================================================
// Quine Disjoint Sum
// ===========================================================================

opaque symbol QInl_subset_univ (a A : τ ι) : π (a ⊆ univ A) → π (QInl a ⊆ univ A) ≔
begin admit end;

opaque symbol naturals_subset_nat (n : τ ι) : π (n ∈ omega) → π (n ⊆ omega) ≔
begin admit end;

opaque symbol naturals_subset_univ (n A : τ ι) : π (n ∈ omega) → π (n ⊆ univ A) ≔
begin admit end;

opaque symbol QInr_subset_univ (a A : τ ι) : π (a ⊆ univ A) → π (QInr a ⊆ univ A) ≔
begin admit end;

// ===========================================================================
// Closure for Quine-Inspired Products and Sums
// ===========================================================================

// Quine ordered pairs
opaque symbol QPair_in_quniv (a b A : τ ι) :
  π (a ∈ quniv A) → π (b ∈ quniv A) → π (QPair a b ∈ quniv A) ≔
begin admit end;

opaque symbol QSigma_quniv (A : τ ι) : π (qprod (quniv A) (quniv A) ⊆ quniv A) ≔
begin admit end;

opaque symbol QSigma_subset_quniv (A Z : τ ι) (B : τ ι → τ ι) :
  π (A ⊆ quniv Z) → π (Ball A (λ x, B x ⊆ quniv Z)) → π (QSigma A B ⊆ quniv Z) ≔
begin admit end;

// The opposite inclusion
opaque symbol quniv_QPair_D (a b A : τ ι) :
  π (QPair a b ∈ quniv A) → π (a ∈ quniv A ∧ b ∈ quniv A) ≔
begin admit end;

opaque symbol quniv_QPair_E (a b A : τ ι) (P : Prop) :
  π (QPair a b ∈ quniv A) → (π (a ∈ quniv A) → π (b ∈ quniv A) → π P) → π P ≔
begin admit end;

opaque symbol quniv_QPair_iff (a b A : τ ι) :
  π (QPair a b ∈ quniv A ⇔ (a ∈ quniv A ∧ b ∈ quniv A)) ≔
begin admit end;

// ===========================================================================
// Quine Disjoint Sum
// ===========================================================================

opaque symbol QInl_in_quniv (a A : τ ι) : π (a ∈ quniv A) → π (QInl a ∈ quniv A) ≔
begin admit end;

opaque symbol QInr_in_quniv (b A : τ ι) : π (b ∈ quniv A) → π (QInr b ∈ quniv A) ≔
begin admit end;

opaque symbol qsum_quniv (C : τ ι) : π (qsum (quniv C) (quniv C) ⊆ quniv C) ≔
begin admit end;

opaque symbol qsum_subset_quniv (A B Z : τ ι) :
  π (A ⊆ quniv Z) → π (B ⊆ quniv Z) → π (qsum A B ⊆ quniv Z) ≔
begin admit end;

// ===========================================================================
// The Natural Numbers
// ===========================================================================

opaque symbol nat_subset_quniv (A : τ ι) : π (omega ⊆ quniv A) ≔
begin admit end;

opaque symbol nat_into_quniv (n A : τ ι) : π (n ∈ omega) → π (n ∈ quniv A) ≔
begin admit end;

opaque symbol bool_subset_quniv (A : τ ι) : π (bool_set ⊆ quniv A) ≔
begin admit end;

opaque symbol bool_into_quniv (b A : τ ι) : π (b ∈ bool_set) → π (b ∈ quniv A) ≔
begin admit end;

// ===========================================================================
// Intersecting <a;b> with Vfrom...
// ===========================================================================

opaque symbol QPair_Int_Vfrom_succ_subset (X a b i : τ ι) :
  π (Transset X) →
  π (Int (QPair a b) (Vfrom X (succ i)) ⊆ QPair (Int a (Vfrom X i)) (Int b (Vfrom X i))) ≔
begin admit end;

// ===========================================================================
// "Take-Lemma" Rules
// ===========================================================================

// for proving a=b by coinduction and c: quniv(A)

// Rule for level i -- preserving the level, not decreasing it
opaque symbol QPair_Int_Vfrom_subset (X a b i : τ ι) :
  π (Transset X) →
  π (Int (QPair a b) (Vfrom X i) ⊆ QPair (Int a (Vfrom X i)) (Int b (Vfrom X i))) ≔
begin admit end;

// a ∩ Vset(i) ⊆ c → b ∩ Vset(i) ⊆ d → <a;b> ∩ Vset(i) ⊆ <c;d>
opaque symbol QPair_Int_Vset_subset_trans (a b i c d : τ ι) :
  π (Int a (Vset i) ⊆ c) → π (Int b (Vset i) ⊆ d) →
  π (Int (QPair a b) (Vset i) ⊆ QPair c d) ≔
begin admit end;

opaque symbol QPair_Int_Vset_subset_UN (i a b : τ ι) :
  π (Ord i) →
  π (Int (QPair a b) (Vset i) ⊆
     Union (RepFun i (λ j, QPair (Int a (Vset j)) (Int b (Vset j))))) ≔
begin admit end;
