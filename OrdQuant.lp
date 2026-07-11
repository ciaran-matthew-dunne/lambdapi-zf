// OrdQuant: Special quantifiers for ordinals and classes
//
// Isabelle source: OrdQuant.thy
// Authors: Krzysztof Grabczewski and L C Paulson
//
// Defines: oall, oex (ordinal quantifiers), OUnion (ordinal union),
//          rall, rex (class quantifiers), setclass

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.Ordinal;

// ===========================================================================
// Section: Quantifiers and union operator for ordinals
// ===========================================================================

// ---------------------------------------------------------------------------
// oall: ordinal universal quantifier — ∀x<A. P(x) ≡ ∀x. x<A → P(x)
// ---------------------------------------------------------------------------

// oall(A, P) ≡ ∀x. lt(x, A) → P(x)
symbol oall (A : τ ι) (P : τ ι → Prop) : Prop ≔
  `∀ (x : τ ι), lt x A ⇒ P x;

// ---------------------------------------------------------------------------
// oex: ordinal existential quantifier — ∃x<A. P(x) ≡ ∃x. x<A ∧ P(x)
// ---------------------------------------------------------------------------

// oex(A, P) ≡ ∃x. lt(x, A) ∧ P(x)
symbol oex (A : τ ι) (P : τ ι → Prop) : Prop ≔
  `∃ (x : τ ι), lt x A ∧ P x;

// ---------------------------------------------------------------------------
// OUnion: ordinal-indexed union — ⋃x<i. B(x) = {z ∈ ⋃x∈i.B(x) | Ord(i)}
// ---------------------------------------------------------------------------

// OUnion(i, B) ≡ Collect(Union(RepFun(i, B)), λ z. Ord(i))
// This is the Isabelle definition: {z: ⋃x∈i. B(x). Ord(i)}
constant symbol OUnion (i : τ ι) (B : τ ι → τ ι) : τ ι;
constant symbol OUnion_def (i : τ ι) (B : τ ι → τ ι) :
  π (OUnion i B = Collect (Union (RepFun i B)) (λ _, Ord i));

// oall/oex (and rall/rex/setclass below) are binder plumbing exactly like
// Ball/Bex — Isabelle definitions kept transparent (≔) by the documented
// π-computing exception, so proofs can eliminate them with bare assume/∃ᵢ.

// ===========================================================================
// Simplification of ordinal quantifiers
// ===========================================================================

// oall_0: ∀x<0. P(x) (vacuously true — nothing is less than 0)
opaque symbol oall_0 (P : τ ι → Prop) : π (oall empty P) ≔
begin
  assume P x hlt;
  refine ⊥ₑ (not_lt0 x hlt)
end;

// not_oex_0: ¬(∃x<0. P(x))
opaque symbol not_oex_0 (P : τ ι → Prop) : π (¬ (oex empty P)) ≔
begin
  assume P hex;
  refine ∃ₑ hex _;
  assume x hx;
  have hlt : π (lt x empty) { refine ∧ₑ₁ hx };
  refine not_lt0 x hlt
end;

// oall_succ: (∀x<succ(i). P(x)) ⟷ (Ord(i) → P(i) ∧ (∀x<i. P(x)))
// Isabelle: (\<forall>x<succ(i). P(x)) <-> (Ord(i) \<longrightarrow> P(i) \<and> (\<forall>x<i. P(x)))
opaque symbol oall_succ (i : τ ι) (P : τ ι → Prop) :
  π (oall (succ i) P ⇔ (Ord i ⇒ P i ∧ oall i P)) ≔
begin
  assume i P;
  apply ∧ᵢ
  { assume hall hOi;
    apply ∧ᵢ
    { refine hall i (ltI i (succ i) (succI1 i) (Ord_succ i hOi)) }
    { assume x hx;
      refine hall x (ltI x (succ i) (succI2 x i (ltD x i hx)) (Ord_succ i hOi)) } }
  { assume h x hx;
    have hOsi : π (Ord (succ i)) { refine lt_Ord2 x (succ i) hx };
    have hOi : π (Ord i) { refine Ord_in_Ord (succ i) i hOsi (succI1 i) };
    have hdisj : π (x = i ∨ x ∈ i) { refine ∧ₑ₁ (succ_iff x i) (ltD x (succ i) hx) };
    have hconj : π (P i ∧ oall i P) { refine h hOi };
    refine ∨ₑ hdisj _ _
    { assume heq; refine ind_eq heq (λ w, P w) (∧ₑ₁ hconj) }
    { assume hxi; refine (∧ₑ₂ hconj) x (ltI x i hxi hOi) } }
end;

// oex_succ: (∃x<succ(i). P(x)) ⟷ (Ord(i) ∧ (P(i) ∨ (∃x<i. P(x))))
opaque symbol oex_succ (i : τ ι) (P : τ ι → Prop) :
  π (oex (succ i) P ⇔ (Ord i ∧ (P i ∨ oex i P))) ≔
begin
  assume i P;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hxsi : π (lt x (succ i)) { refine ∧ₑ₁ hx };
    have hPx : π (P x) { refine ∧ₑ₂ hx };
    have hOi : π (Ord i) { refine Ord_in_Ord (succ i) i (lt_Ord2 x (succ i) hxsi) (succI1 i) };
    have hdisj : π (x = i ∨ x ∈ i) { refine ∧ₑ₁ (succ_iff x i) (ltD x (succ i) hxsi) };
    refine ∧ᵢ hOi _;
    refine ∨ₑ hdisj _ _
    { assume heq; refine ∨ᵢ₁ (ind_eq (eq_sym heq) (λ w, P w) hPx) }
    { assume hxi; refine ∨ᵢ₂ (∃ᵢ x (∧ᵢ (ltI x i hxi hOi) hPx)) } }
  { assume h;
    have hOi : π (Ord i) { refine ∧ₑ₁ h };
    have hdisj : π (P i ∨ oex i P) { refine ∧ₑ₂ h };
    refine ∨ₑ hdisj _ _
    { assume hPi;
      refine ∃ᵢ i (∧ᵢ (ltI i (succ i) (succI1 i) (Ord_succ i hOi)) hPi) }
    { assume hex;
      refine ∃ₑ hex _;
      assume x hx;
      have hxi : π (lt x i) { refine ∧ₑ₁ hx };
      have hPx : π (P x) { refine ∧ₑ₂ hx };
      refine ∃ᵢ x (∧ᵢ (ltI x (succ i) (succI2 x i (ltD x i hxi)) (Ord_succ i hOi)) hPx) } }
end;

// ===========================================================================
// Section: Ordinal union
// ===========================================================================

// Ord_OUN: if B(x) is ordinal for all x < A, then OUnion(A, B) is ordinal
// Isabelle: ⟦⋀x. x<A ⟹ Ord(B(x))⟧ ⟹ Ord(⋃x<A. B(x))
opaque symbol Ord_OUN (A : τ ι) (B : τ ι → τ ι) :
  π (oall A (λ x, Ord (B x))) → π (Ord (OUnion A B)) ≔
begin
  assume A B hAll;
  // OUnion(A,B) = Collect(Union(RepFun(A, B)), λ _. Ord(A))
  // OUnion(A,B) ⊆ Union(RepFun(A, B))
  // If Ord(A) doesn't hold, OUnion is empty, hence Ord (since Ord(empty)).
  // If Ord(A) holds, OUnion = Union(RepFun(A, B)) and each B(x) is Ord, so Union is Ord.
  refine ∨ₑ (em (Ord A)) _ _
  { assume hOA;
    // OUnion(A,B) = Collect(Union(RepFun(A,B)), λ _. Ord(A))
    // Since Ord(A), any z ∈ Union(RepFun(A,B)) is also in OUnion(A,B)
    // and vice versa. So OUnion(A,B) = Union(RepFun(A,B)).
    // Union(RepFun(A,B)) is ordinal if all B(x) for x ∈ A are ordinal.
    // Ball(RepFun(A,B), Ord) holds: for S ∈ RepFun(A,B), ∃x∈A. S = B(x), so Ord(S).
    have hBall : π (Ball (RepFun A B) (λ x, Ord x)) {
      assume S hS;
      have hrep : π (Bex A (λ x, S = B x))
        { refine ∧ₑ₁ (RepFun_iff S A B) hS };
      refine ∃ₑ hrep _;
      assume x hx;
      have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
      have hSeq : π (S = B x) { refine ∧ₑ₂ hx };
      have hOBx : π (Ord (B x)) { refine hAll x (ltI x A hxA hOA) };
      refine ind_eq hSeq (λ w, Ord w) hOBx
    };
    have hOrd_union : π (Ord (Union (RepFun A B)))
      { refine Ord_Union (RepFun A B) hBall };
    // Now show Ord(OUnion(A,B)). OUnion = Collect(Union(RepFun(A,B)), λ _. Ord(A))
    // Since Ord(A) holds, this equals Union(RepFun(A,B)).
    // Formally: OUnion(A,B) = Collect(Union(RepFun(A,B)), λ _. Ord(A))
    // For z: z ∈ OUnion iff z ∈ Union(RepFun(A,B)) ∧ Ord(A) iff z ∈ Union(RepFun(A,B))
    // So Ord(OUnion) follows from Ord(Union(RepFun(A,B))) and the equality.
    // We need subset_antisym to show equality, then rewrite.
    have heq : π (OUnion A B = Union (RepFun A B)) {
      refine subset_antisym (OUnion A B) (Union (RepFun A B)) _ _
      { assume z hz;
        have hz' : π (z ∈ Collect (Union (RepFun A B)) (λ _, Ord A))
          { refine ind_eq (eq_sym (OUnion_def A B)) (λ w, z ∈ w) hz };
        refine CollectD1 z (Union (RepFun A B)) (λ _, Ord A) hz' }
      { assume z hz;
        refine ind_eq (OUnion_def A B) (λ w, z ∈ w)
          (CollectI z (Union (RepFun A B)) (λ _, Ord A) hz hOA) }
    };
    refine ind_eq heq (λ w, Ord w) hOrd_union }
  { assume hnOA;
    // ¬Ord(A): OUnion(A,B) = Collect(Union(RepFun(A,B)), λ _. Ord(A))
    // Since ¬Ord(A), no z satisfies the predicate, so OUnion = empty.
    have heq : π (OUnion A B = empty) {
      refine equals0I (OUnion A B) _;
      assume z hz;
      have hz' : π (z ∈ Collect (Union (RepFun A B)) (λ _, Ord A))
        { refine ind_eq (eq_sym (OUnion_def A B)) (λ w, z ∈ w) hz };
      have hOA2 : π (Ord A) { refine CollectD2 z (Union (RepFun A B)) (λ _, Ord A) hz' };
      refine hnOA hOA2
    };
    refine ind_eq heq (λ w, Ord w) Ord_0 }
end;

// OUN_upper_lt: a<A → i < b(a) → Ord(⋃x<A. b(x)) → i < (⋃x<A. b(x))
opaque symbol OUN_upper_lt (a A i : τ ι) (b : τ ι → τ ι) :
  π (lt a A) → π (lt i (b a)) → π (Ord (OUnion A b)) →
  π (lt i (OUnion A b)) ≔
begin
  assume a A i b haA hiba hOrd;
  have hOA : π (Ord A) { refine lt_Ord2 a A haA };
  have hba_in : π (b a ∈ RepFun A b) { refine RepFunI a A b (ltD a A haA) };
  have hi_union : π (i ∈ Union (RepFun A b)) { refine UnionI i (b a) (RepFun A b) (ltD i (b a) hiba) hba_in };
  refine ltI i (OUnion A b)
    (ind_eq (OUnion_def A b) (λ w, i ∈ w)
      (CollectI i (Union (RepFun A b)) (λ _, Ord A) hi_union hOA)) hOrd
end;

// OUN_upper_le: a<A → le(i, b(a)) → Ord(⋃x<A. b(x)) → le(i, ⋃x<A. b(x))
opaque symbol OUN_upper_le (a A i : τ ι) (b : τ ι → τ ι) :
  π (lt a A) → π (le i (b a)) → π (Ord (OUnion A b)) →
  π (le i (OUnion A b)) ≔
begin
  assume a A i b haA hle hOrd;
  have hOA : π (Ord A) { refine lt_Ord2 a A haA };
  refine ∨ₑ (leE i (b a) hle) _ _
  { assume hlt;
    refine leI i (OUnion A b) _ hOrd;
    have hba_in : π (b a ∈ RepFun A b) { refine RepFunI a A b (ltD a A haA) };
    have hi_union : π (i ∈ Union (RepFun A b)) { refine UnionI i (b a) (RepFun A b) hlt hba_in };
    refine ind_eq (OUnion_def A b) (λ w, i ∈ w)
      (CollectI i (Union (RepFun A b)) (λ _, Ord A) hi_union hOA) }
  { assume heq;
    have hOba : π (Ord (b a)) { refine le_Ord2 i (b a) hle };
    have hsub : π (i ⊆ OUnion A b) {
      assume z hz;
      have hzba : π (z ∈ b a) { refine ind_eq (eq_sym heq) (λ w, z ∈ w) hz };
      have hba_in : π (b a ∈ RepFun A b) { refine RepFunI a A b (ltD a A haA) };
      have hzU : π (z ∈ Union (RepFun A b)) { refine UnionI z (b a) (RepFun A b) hzba hba_in };
      refine ind_eq (OUnion_def A b) (λ w, z ∈ w)
        (CollectI z (Union (RepFun A b)) (λ _, Ord A) hzU hOA) };
    have hOi : π (Ord i) { refine ind_eq heq (λ w, Ord w) hOba };
    refine subset_imp_le (OUnion A b) i hsub hOrd hOi }
end;

// Limit_OUN_eq: Limit(i) → (⋃x<i. x) = i
opaque symbol Limit_OUN_eq (i : τ ι) :
  π (Limit i) → π (OUnion i (λ x, x) = i) ≔
begin
  assume i hL;
  have hOi : π (Ord i) { refine Limit_is_Ord i hL };
  // OUnion(i, λx.x) = Collect(Union(RepFun(i, λx.x)), λ_. Ord(i))
  // RepFun(i, λx.x) = i (identity). Union(i) = i (Limit).
  // So OUnion(i, λx.x) = Collect(i, λ_. Ord(i)) = i (since Ord(i) holds).
  // First show RepFun(i, id) = i
  have hRF_eq : π (RepFun i (λ x, x) = i) {
    refine subset_antisym (RepFun i (λ x, x)) i _ _
    { assume z hz;
      have hrep : π (Bex i (λ x, z = x))
        { refine ∧ₑ₁ (RepFun_iff z i (λ x, x)) hz };
      refine ∃ₑ hrep _;
      assume x hx;
      have hxi : π (x ∈ i) { refine ∧ₑ₁ hx };
      have hzeq : π (z = x) { refine ∧ₑ₂ hx };
      refine ind_eq hzeq (λ w, w ∈ i) hxi }
    { assume z hz;
      refine RepFunI z i (λ x, x) hz }
  };
  // Union(RepFun(i, id)) = Union(i) = i
  have hU_eq : π (Union (RepFun i (λ x, x)) = i) {
    have h2 : π (Union i = i) { refine Limit_Union_eq i hL };
    refine ind_eq hRF_eq (λ w, Union w = i) h2
  };
  // OUnion(i, id) = Collect(Union(RepFun(i,id)), λ_. Ord(i))
  //              = Collect(i, λ_. Ord(i)) = i
  refine subset_antisym (OUnion i (λ x, x)) i _ _
  { assume z hz;
    have hz' : π (z ∈ Collect (Union (RepFun i (λ x, x))) (λ _, Ord i))
      { refine ind_eq (eq_sym (OUnion_def i (λ x, x))) (λ w, z ∈ w) hz };
    have hz1 : π (z ∈ Union (RepFun i (λ x, x)))
      { refine CollectD1 z (Union (RepFun i (λ x, x))) (λ _, Ord i) hz' };
    refine ind_eq (eq_sym hU_eq) (λ w, z ∈ w) hz1 }
  { assume z hz;
    have hz1 : π (z ∈ Union (RepFun i (λ x, x)))
      { refine ind_eq hU_eq (λ w, z ∈ w) hz };
    refine ind_eq (OUnion_def i (λ x, x)) (λ w, z ∈ w)
      (CollectI z (Union (RepFun i (λ x, x))) (λ _, Ord i) hz1 hOi) }
end;

// OUN_least: (∀x. x<A → B(x) ⊆ C) → (⋃x<A. B(x)) ⊆ C
opaque symbol OUN_least (A C : τ ι) (B : τ ι → τ ι) :
  (Π (x : τ ι), π (lt x A) → π (B x ⊆ C)) →
  π (OUnion A B ⊆ C) ≔
begin
  assume A C B hAll z hz;
  // z ∈ OUnion(A,B) = Collect(Union(RepFun(A,B)), λ_. Ord(A))
  have hz' : π (z ∈ Collect (Union (RepFun A B)) (λ _, Ord A))
    { refine ind_eq (eq_sym (OUnion_def A B)) (λ w, z ∈ w) hz };
  have hOA : π (Ord A) { refine CollectD2 z (Union (RepFun A B)) (λ _, Ord A) hz' };
  have hzU : π (z ∈ Union (RepFun A B))
    { refine CollectD1 z (Union (RepFun A B)) (λ _, Ord A) hz' };
  // z ∈ Union(RepFun(A,B)) → ∃S ∈ RepFun(A,B). z ∈ S
  have hbex : π (Bex (RepFun A B) (λ S, z ∈ S))
    { refine UnionE z (RepFun A B) hzU };
  refine ∃ₑ hbex _;
  assume S hS;
  have hSin : π (S ∈ RepFun A B) { refine ∧ₑ₁ hS };
  have hzS : π (z ∈ S) { refine ∧ₑ₂ hS };
  // S ∈ RepFun(A,B) → ∃x∈A. S = B(x)
  have hrep : π (Bex A (λ x, S = B x))
    { refine ∧ₑ₁ (RepFun_iff S A B) hSin };
  refine ∃ₑ hrep _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hSeq : π (S = B x) { refine ∧ₑ₂ hx };
  have hzBx : π (z ∈ B x) { refine ind_eq (eq_sym hSeq) (λ w, z ∈ w) hzS };
  refine hAll x (ltI x A hxA hOA) z hzBx
end;

// OUN_least_le: Ord(i) → (∀x. x<A → le(b(x), i)) → le(⋃x<A. b(x), i)
opaque symbol OUN_least_le (A i : τ ι) (b : τ ι → τ ι) :
  π (Ord i) →
  (Π (x : τ ι), π (lt x A) → π (le (b x) i)) →
  π (le (OUnion A b) i) ≔
begin
  assume A i b hOi hAll;
  // OUnion(A,b) ⊆ i → le(OUnion(A,b), i)
  // Need: Ord(OUnion(A,b)) for subset_imp_le
  refine ∨ₑ (em (Ord A)) _ _
  { assume hOA;
    // OUnion subset: every element of OUnion(A,b) is in i
    have hsub : π (OUnion A b ⊆ i) {
      assume z hz;
      have hz' : π (z ∈ Collect (Union (RepFun A b)) (λ _, Ord A))
        { refine ind_eq (eq_sym (OUnion_def A b)) (λ w, z ∈ w) hz };
      have hzU : π (z ∈ Union (RepFun A b))
        { refine CollectD1 z (Union (RepFun A b)) (λ _, Ord A) hz' };
      have hbex : π (Bex (RepFun A b) (λ S, z ∈ S))
        { refine UnionE z (RepFun A b) hzU };
      refine ∃ₑ hbex _;
      assume S hS;
      have hSin : π (S ∈ RepFun A b) { refine ∧ₑ₁ hS };
      have hzS : π (z ∈ S) { refine ∧ₑ₂ hS };
      have hrep : π (Bex A (λ x, S = b x))
        { refine ∧ₑ₁ (RepFun_iff S A b) hSin };
      refine ∃ₑ hrep _;
      assume x hx;
      have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
      have hSeq : π (S = b x) { refine ∧ₑ₂ hx };
      have hzBx : π (z ∈ b x) { refine ind_eq (eq_sym hSeq) (λ w, z ∈ w) hzS };
      // le(b(x), i) means b(x) ∈ i ∨ b(x) = i
      have hle : π (le (b x) i) { refine hAll x (ltI x A hxA hOA) };
      refine ∨ₑ (leE (b x) i hle) _ _
      { assume hbxi;
        // b(x) ∈ i and Ord(i) → b(x) ⊆ i
        have hbxsub : π (b x ⊆ i) { refine OrdmemD i (b x) hbxi hOi };
        refine hbxsub z hzBx }
      { assume hbxeq;
        refine ind_eq (eq_sym hbxeq) (λ w, z ∈ w) hzBx }
    };
    // Ord(OUnion(A,b)): need oall premise for Ord_OUN
    have hOOUN : π (Ord (OUnion A b)) {
      refine Ord_OUN A b _;
      assume x hxA;
      // le(b(x), i) and Ord(i) → Ord(b(x))
      have hle : π (le (b x) i) { refine hAll x hxA };
      refine ∨ₑ (leE (b x) i hle) _ _
      { assume hbxi; refine Ord_in_Ord i (b x) hOi hbxi }
      { assume hbxeq; refine ind_eq hbxeq (λ w, Ord w) hOi }
    };
    refine subset_imp_le i (OUnion A b) hsub hOi hOOUN }
  { assume hnOA;
    // ¬Ord(A) → OUnion(A,b) = empty
    have heq : π (OUnion A b = empty) {
      refine equals0I (OUnion A b) _;
      assume z hz;
      have hz' : π (z ∈ Collect (Union (RepFun A b)) (λ _, Ord A))
        { refine ind_eq (eq_sym (OUnion_def A b)) (λ w, z ∈ w) hz };
      have hOA2 : π (Ord A) { refine CollectD2 z (Union (RepFun A b)) (λ _, Ord A) hz' };
      refine hnOA hOA2
    };
    // le(OUnion(A,b), i) via rewriting to le(empty, i)
    refine ind_eq heq (λ w, le w i) (Ord_0_le i hOi) }
end;

// le_implies_OUN_le_OUN: (∀x. x<A → le(c(x), d(x))) → le(⋃x<A. c(x), ⋃x<A. d(x))
opaque symbol le_implies_OUN_le_OUN (A : τ ι) (c d : τ ι → τ ι) :
  (Π (x : τ ι), π (lt x A) → π (le (c x) (d x))) →
  π (le (OUnion A c) (OUnion A d)) ≔
begin
  assume A c d hle;
  have hOOUNd : π (Ord (OUnion A d)) {
    refine Ord_OUN A d _;
    assume x hxA;
    refine le_Ord2 (c x) (d x) (hle x hxA) };
  refine OUN_least_le A (OUnion A d) c hOOUNd _;
  assume x hxA;
  have hOdx : π (Ord (d x)) { refine le_Ord2 (c x) (d x) (hle x hxA) };
  have hle_dU : π (le (d x) (OUnion A d)) {
    refine OUN_upper_le x A (d x) d hxA (le_refl (d x) hOdx) hOOUNd };
  refine le_trans (c x) (d x) (OUnion A d) (hle x hxA) hle_dU
end;

// ===========================================================================
// Section: Universal quantifier for ordinals
// ===========================================================================

// oallI: (∀x. x<A → P(x)) → oall(A, P)
opaque symbol oallI (A : τ ι) (P : τ ι → Prop) :
  (Π (x : τ ι), π (lt x A) → π (P x)) → π (oall A P) ≔
begin
  assume A P h x hlt;
  refine h x hlt
end;

// ospec: oall(A, P) → x<A → P(x)
opaque symbol ospec (A : τ ι) (P : τ ι → Prop) (x : τ ι) :
  π (oall A P) → π (lt x A) → π (P x) ≔
begin
  assume A P x hall hlt;
  refine hall x hlt
end;

// oallE: oall(A, P) → (P(x) → Q) → (¬(x<A) → Q) → Q
opaque symbol oallE (A : τ ι) (P : τ ι → Prop) (x : τ ι) (Q : Prop) :
  π (oall A P) → (π (P x) → π Q) → (π (¬ (lt x A)) → π Q) → π Q ≔
begin
  assume A P x Q hall hpq hnlt;
  refine ∨ₑ (em (lt x A)) _ _
  { assume hlt; refine hpq (hall x hlt) }
  { assume hn; refine hnlt hn }
end;

// rev_oallE: oall(A, P) → (¬(x<A) → Q) → (P(x) → Q) → Q
opaque symbol rev_oallE (A : τ ι) (P : τ ι → Prop) (x : τ ι) (Q : Prop) :
  π (oall A P) → (π (¬ (lt x A)) → π Q) → (π (P x) → π Q) → π Q ≔
begin
  assume A P x Q hall hnlt hpq;
  refine ∨ₑ (em (lt x A)) _ _
  { assume hlt; refine hpq (hall x hlt) }
  { assume hn; refine hnlt hn }
end;

// oall_simp: oall(a, λx. ⊤) ⟷ ⊤
opaque symbol oall_simp (a : τ ι) : π (oall a (λ _, ⊤) ⇔ ⊤) ≔
begin
  assume a;
  apply ∧ᵢ
  { assume h; apply ⊤ᵢ }
  { assume h x hlt; apply ⊤ᵢ }
end;

// oall_cong: a = a' → (∀x. x<a' → P(x) ⟷ P'(x)) → oall(a, P) ⟷ oall(a', P')
opaque symbol oall_cong (a a' : τ ι) (P P' : τ ι → Prop) :
  π (a = a') →
  (Π (x : τ ι), π (lt x a') → π (P x ⇔ P' x)) →
  π (oall a P ⇔ oall a' P') ≔
begin
  assume a a' P P' heq hiff;
  apply ∧ᵢ
  { assume hall x hlt;
    have hlt2 : π (lt x a) { refine ind_eq heq (λ w, lt x w) hlt };
    have hPx : π (P x) { refine hall x hlt2 };
    refine ∧ₑ₁ (hiff x hlt) hPx }
  { assume hall x hlt;
    have hlt2 : π (lt x a') { refine ind_eq (eq_sym heq) (λ w, lt x w) hlt };
    have hP'x : π (P' x) { refine hall x hlt2 };
    refine ∧ₑ₂ (hiff x hlt2) hP'x }
end;

// ===========================================================================
// Section: Existential quantifier for ordinals
// ===========================================================================

// oexI: P(x) → x<A → oex(A, P)
opaque symbol oexI (A : τ ι) (P : τ ι → Prop) (x : τ ι) :
  π (P x) → π (lt x A) → π (oex A P) ≔
begin
  assume A P x hPx hlt;
  refine ∃ᵢ x (∧ᵢ hlt hPx)
end;

// oexCI: (oall(A, λx. ¬P(x)) → P(a)) → a<A → oex(A, P)
opaque symbol oexCI (A : τ ι) (P : τ ι → Prop) (a : τ ι) :
  (π (oall A (λ x, ¬ (P x))) → π (P a)) → π (lt a A) → π (oex A P) ≔
begin
  assume A P a hcase haA;
  refine ∨ₑ (em (oex A P)) _ _
  { assume h; apply h }
  { assume hn;
    // ¬oex(A,P) → oall(A, λx. ¬P(x))
    have hall : π (oall A (λ x, ¬ (P x))) {
      assume x hlt hPx;
      refine hn (∃ᵢ x (∧ᵢ hlt hPx))
    };
    refine ∃ᵢ a (∧ᵢ haA (hcase hall)) }
end;

// oexE: oex(A, P) → (∀x. x<A → P(x) → Q) → Q
opaque symbol oexE (A : τ ι) (P : τ ι → Prop) (Q : Prop) :
  π (oex A P) → (Π (x : τ ι), π (lt x A) → π (P x) → π Q) → π Q ≔
begin
  assume A P Q hex hk;
  refine ∃ₑ hex _;
  assume x hx;
  have hlt : π (lt x A) { refine ∧ₑ₁ hx };
  have hPx : π (P x) { refine ∧ₑ₂ hx };
  refine hk x hlt hPx
end;

// oex_cong: a = a' → (∀x. x<a' → P(x) ⟷ P'(x)) → oex(a, P) ⟷ oex(a', P')
opaque symbol oex_cong (a a' : τ ι) (P P' : τ ι → Prop) :
  π (a = a') →
  (Π (x : τ ι), π (lt x a') → π (P x ⇔ P' x)) →
  π (oex a P ⇔ oex a' P') ≔
begin
  assume a a' P P' heq hiff;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hlt : π (lt x a) { refine ∧ₑ₁ hx };
    have hPx : π (P x) { refine ∧ₑ₂ hx };
    have hlt2 : π (lt x a') { refine ind_eq (eq_sym heq) (λ w, lt x w) hlt };
    have hP'x : π (P' x) { refine ∧ₑ₁ (hiff x hlt2) hPx };
    refine ∃ᵢ x (∧ᵢ hlt2 hP'x) }
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hlt : π (lt x a') { refine ∧ₑ₁ hx };
    have hP'x : π (P' x) { refine ∧ₑ₂ hx };
    have hlt2 : π (lt x a) { refine ind_eq heq (λ w, lt x w) hlt };
    have hPx : π (P x) { refine ∧ₑ₂ (hiff x hlt) hP'x };
    refine ∃ᵢ x (∧ᵢ hlt2 hPx) }
end;

// ===========================================================================
// Section: Rules for Ordinal-Indexed Unions
// ===========================================================================

// OUN_I: a<i → b ∈ B(a) → b ∈ OUnion(i, B)
opaque symbol OUN_I (a b i : τ ι) (B : τ ι → τ ι) :
  π (lt a i) → π (b ∈ B a) → π (b ∈ OUnion i B) ≔
begin
  assume a b i B hai hbBa;
  have hOi : π (Ord i) { refine lt_Ord2 a i hai };
  have hBa_in : π (B a ∈ RepFun i B) { refine RepFunI a i B (ltD a i hai) };
  have hbU : π (b ∈ Union (RepFun i B)) { refine UnionI b (B a) (RepFun i B) hbBa hBa_in };
  refine ind_eq (OUnion_def i B) (λ w, b ∈ w)
    (CollectI b (Union (RepFun i B)) (λ _, Ord i) hbU hOi)
end;

// OUN_E: b ∈ OUnion(i, B) → (∀a. b ∈ B(a) → a<i → R) → R
opaque symbol OUN_E (b i : τ ι) (B : τ ι → τ ι) (R : Prop) :
  π (b ∈ OUnion i B) → (Π (a : τ ι), π (b ∈ B a) → π (lt a i) → π R) → π R ≔
begin
  assume b i B R hb hk;
  // b ∈ OUnion(i,B) = Collect(Union(RepFun(i,B)), λ_. Ord(i))
  have hb' : π (b ∈ Collect (Union (RepFun i B)) (λ _, Ord i))
    { refine ind_eq (eq_sym (OUnion_def i B)) (λ w, b ∈ w) hb };
  have hOi : π (Ord i) { refine CollectD2 b (Union (RepFun i B)) (λ _, Ord i) hb' };
  have hbU : π (b ∈ Union (RepFun i B))
    { refine CollectD1 b (Union (RepFun i B)) (λ _, Ord i) hb' };
  // b ∈ Union(RepFun(i,B)) → ∃S ∈ RepFun(i,B). b ∈ S
  have hbex : π (Bex (RepFun i B) (λ S, b ∈ S))
    { refine UnionE b (RepFun i B) hbU };
  refine ∃ₑ hbex _;
  assume S hS;
  have hSin : π (S ∈ RepFun i B) { refine ∧ₑ₁ hS };
  have hbS : π (b ∈ S) { refine ∧ₑ₂ hS };
  have hrep : π (Bex i (λ x, S = B x))
    { refine ∧ₑ₁ (RepFun_iff S i B) hSin };
  refine ∃ₑ hrep _;
  assume a ha;
  have haI : π (a ∈ i) { refine ∧ₑ₁ ha };
  have hSeq : π (S = B a) { refine ∧ₑ₂ ha };
  have hbBa : π (b ∈ B a) { refine ind_eq (eq_sym hSeq) (λ w, b ∈ w) hbS };
  refine hk a hbBa (ltI a i haI hOi)
end;

// OUN_iff: b ∈ OUnion(i, B) ⟷ oex(i, λx. b ∈ B(x))
opaque symbol OUN_iff (b i : τ ι) (B : τ ι → τ ι) :
  π (b ∈ OUnion i B ⇔ oex i (λ x, b ∈ B x)) ≔
begin
  assume b i B;
  apply ∧ᵢ
  { assume hb;
    refine OUN_E b i B (oex i (λ x, b ∈ B x)) hb _;
    assume a hbBa haI;
    refine ∃ᵢ a (∧ᵢ haI hbBa) }
  { assume hex;
    refine ∃ₑ hex _;
    assume a ha;
    have haI : π (lt a i) { refine ∧ₑ₁ ha };
    have hbBa : π (b ∈ B a) { refine ∧ₑ₂ ha };
    refine OUN_I a b i B haI hbBa }
end;

// lt_induct: i<k → (∀x. x<k → oall(x, P) → P(x)) → P(i)
opaque symbol lt_induct (i k : τ ι) (P : τ ι → Prop) :
  π (lt i k) → (Π (x : τ ι), π (lt x k) → π (oall x P) → π (P x)) →
  π (P i) ≔
begin
  assume i k P hik hstep;
  have hik_mem : π (i ∈ k) { refine ltD i k hik };
  have hOk : π (Ord k) { refine lt_Ord2 i k hik };
  have hOi : π (Ord i) { refine Ord_in_Ord k i hOk hik_mem };
  have hTk : π (Transset k) { refine Ord_is_Transset k hOk };
  have hR : π (i ∈ k ⇒ P i) {
    refine trans_induct i (λ x, x ∈ k ⇒ P x) hOi _;
    assume x hOx hIH hxk;
    have hxsub : π (x ⊆ k) { refine TranssetD k x hTk hxk };
    have hballP : π (oall x P) {
      assume y hy;
      have hyx : π (y ∈ x) { refine ltD y x hy };
      have hyk : π (y ∈ k) { refine hxsub y hyx };
      refine hIH y hyx hyk };
    refine hstep x (ltI x k hxk hOk) hballP };
  refine hR hik_mem
end;

// ===========================================================================
// Section: Quantification over a class
// ===========================================================================

// rall(M, P) ≡ ∀x. M(x) → P(x)
symbol rall (M : τ ι → Prop) (P : τ ι → Prop) : Prop ≔
  `∀ (x : τ ι), M x ⇒ P x;

// rex(M, P) ≡ ∃x. M(x) ∧ P(x)
symbol rex (M : τ ι → Prop) (P : τ ι → Prop) : Prop ≔
  `∃ (x : τ ι), M x ∧ P x;

// ---------------------------------------------------------------------------
// Relativized universal quantifier
// ---------------------------------------------------------------------------

// rallI: (∀x. M(x) → P(x)) → rall(M, P)
opaque symbol rallI (M P : τ ι → Prop) :
  (Π (x : τ ι), π (M x) → π (P x)) → π (rall M P) ≔
begin
  assume M P h x hMx;
  refine h x hMx
end;

// rspec: rall(M, P) → M(x) → P(x)
opaque symbol rspec (M P : τ ι → Prop) (x : τ ι) :
  π (rall M P) → π (M x) → π (P x) ≔
begin
  assume M P x hall hMx;
  refine hall x hMx
end;

// rev_rallE: rall(M, P) → (¬M(x) → Q) → (P(x) → Q) → Q
opaque symbol rev_rallE (M P : τ ι → Prop) (x : τ ι) (Q : Prop) :
  π (rall M P) → (π (¬ (M x)) → π Q) → (π (P x) → π Q) → π Q ≔
begin
  assume M P x Q hall hnM hP;
  refine ∨ₑ (em (M x)) _ _
  { assume hMx; refine hP (hall x hMx) }
  { assume hnMx; refine hnM hnMx }
end;

// rallE: rall(M, P) → (P(x) → Q) → (¬M(x) → Q) → Q
opaque symbol rallE (M P : τ ι → Prop) (x : τ ι) (Q : Prop) :
  π (rall M P) → (π (P x) → π Q) → (π (¬ (M x)) → π Q) → π Q ≔
begin
  assume M P x Q hall hP hnM;
  refine ∨ₑ (em (M x)) _ _
  { assume hMx; refine hP (hall x hMx) }
  { assume hnMx; refine hnM hnMx }
end;

// rall_triv: rall(M, λ_. P) ⟷ ((∃x. M(x)) ⇒ P)
opaque symbol rall_triv (M : τ ι → Prop) (P : Prop) :
  π (rall M (λ _, P) ⇔ ((`∃ (x : τ ι), M x) ⇒ P)) ≔
begin
  assume M P;
  apply ∧ᵢ
  { assume hall hex;
    refine ∃ₑ hex _;
    assume x hMx;
    refine hall x hMx }
  { assume h x hMx;
    refine h (∃ᵢ x hMx) }
end;

// rall_cong: (∀x. M(x) → P(x) ⟷ P'(x)) → rall(M,P) ⟷ rall(M,P')
opaque symbol rall_cong (M : τ ι → Prop) (P P' : τ ι → Prop) :
  (Π (x : τ ι), π (M x) → π (P x ⇔ P' x)) → π (rall M P ⇔ rall M P') ≔
begin
  assume M P P' hiff;
  apply ∧ᵢ
  { assume hall x hMx;
    refine ∧ₑ₁ (hiff x hMx) (hall x hMx) }
  { assume hall x hMx;
    refine ∧ₑ₂ (hiff x hMx) (hall x hMx) }
end;

// ---------------------------------------------------------------------------
// Relativized existential quantifier
// ---------------------------------------------------------------------------

// rexI: P(x) → M(x) → rex(M, P)
opaque symbol rexI (M P : τ ι → Prop) (x : τ ι) :
  π (P x) → π (M x) → π (rex M P) ≔
begin
  assume M P x hPx hMx;
  refine ∃ᵢ x (∧ᵢ hMx hPx)
end;

// rev_rexI: M(x) → P(x) → rex(M, P)
opaque symbol rev_rexI (M P : τ ι → Prop) (x : τ ι) :
  π (M x) → π (P x) → π (rex M P) ≔
begin
  assume M P x hMx hPx;
  refine ∃ᵢ x (∧ᵢ hMx hPx)
end;

// rexCI: (rall(M, λx. ¬P(x)) → P(a)) → M(a) → rex(M, P)
opaque symbol rexCI (M P : τ ι → Prop) (a : τ ι) :
  (π (rall M (λ x, ¬ (P x))) → π (P a)) → π (M a) → π (rex M P) ≔
begin
  assume M P a hcase hMa;
  refine ∨ₑ (em (rex M P)) _ _
  { assume h; apply h }
  { assume hn;
    have hall : π (rall M (λ x, ¬ (P x))) {
      assume x hMx hPx;
      refine hn (∃ᵢ x (∧ᵢ hMx hPx))
    };
    refine ∃ᵢ a (∧ᵢ hMa (hcase hall)) }
end;

// rexE: rex(M, P) → (∀x. M(x) → P(x) → Q) → Q
opaque symbol rexE (M P : τ ι → Prop) (Q : Prop) :
  π (rex M P) → (Π (x : τ ι), π (M x) → π (P x) → π Q) → π Q ≔
begin
  assume M P Q hex hk;
  refine ∃ₑ hex _;
  assume x hx;
  have hMx : π (M x) { refine ∧ₑ₁ hx };
  have hPx : π (P x) { refine ∧ₑ₂ hx };
  refine hk x hMx hPx
end;

// rex_triv: rex(M, λ_. P) ⟷ ((∃x. M(x)) ∧ P)
opaque symbol rex_triv (M : τ ι → Prop) (P : Prop) :
  π (rex M (λ _, P) ⇔ ((`∃ (x : τ ι), M x) ∧ P)) ≔
begin
  assume M P;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hMx : π (M x) { refine ∧ₑ₁ hx };
    have hP : π P { refine ∧ₑ₂ hx };
    apply ∧ᵢ (∃ᵢ x hMx) hP }
  { assume h;
    have hex : π (`∃ (x : τ ι), M x) { refine ∧ₑ₁ h };
    have hP : π P { refine ∧ₑ₂ h };
    refine ∃ₑ hex _;
    assume x hMx;
    refine ∃ᵢ x (∧ᵢ hMx hP) }
end;

// rex_cong: (∀x. M(x) → P(x) ⟷ P'(x)) → rex(M,P) ⟷ rex(M,P')
opaque symbol rex_cong (M : τ ι → Prop) (P P' : τ ι → Prop) :
  (Π (x : τ ι), π (M x) → π (P x ⇔ P' x)) → π (rex M P ⇔ rex M P') ≔
begin
  assume M P P' hiff;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hMx : π (M x) { refine ∧ₑ₁ hx };
    have hPx : π (P x) { refine ∧ₑ₂ hx };
    refine ∃ᵢ x (∧ᵢ hMx (∧ₑ₁ (hiff x hMx) hPx)) }
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hMx : π (M x) { refine ∧ₑ₁ hx };
    have hP'x : π (P' x) { refine ∧ₑ₂ hx };
    refine ∃ᵢ x (∧ᵢ hMx (∧ₑ₂ (hiff x hMx) hP'x)) }
end;

// rall_is_ball: rall(λz. z∈A, P) ⟷ Ball(A, P)
opaque symbol rall_is_ball (A : τ ι) (P : τ ι → Prop) :
  π (rall (λ z, z ∈ A) P ⇔ Ball A P) ≔
begin
  assume A P;
  apply ∧ᵢ
  { assume h x hxA; refine h x hxA }
  { assume h x hxA; refine h x hxA }
end;

// rex_is_bex: rex(λz. z∈A, P) ⟷ Bex(A, P)
opaque symbol rex_is_bex (A : τ ι) (P : τ ι → Prop) :
  π (rex (λ z, z ∈ A) P ⇔ Bex A P) ≔
begin
  assume A P;
  apply ∧ᵢ
  { assume h;
    refine ∃ₑ h _;
    assume x hx;
    refine ∃ᵢ x hx }
  { assume h;
    refine ∃ₑ h _;
    assume x hx;
    refine ∃ᵢ x hx }
end;

// rall_conj_distrib: rall(M, λx. P(x) ∧ Q(x)) ⟷ rall(M,P) ∧ rall(M,Q)
opaque symbol rall_conj_distrib (M : τ ι → Prop) (P Q : τ ι → Prop) :
  π (rall M (λ x, P x ∧ Q x) ⇔ (rall M P ∧ rall M Q)) ≔
begin
  assume M P Q;
  apply ∧ᵢ
  { assume h;
    apply ∧ᵢ
    { assume x hMx; refine ∧ₑ₁ (h x hMx) }
    { assume x hMx; refine ∧ₑ₂ (h x hMx) } }
  { assume h x hMx;
    have hP : π (P x) { refine ∧ₑ₁ h x hMx };
    have hQ : π (Q x) { refine ∧ₑ₂ h x hMx };
    apply ∧ᵢ hP hQ }
end;

// rex_disj_distrib: rex(M, λx. P(x) ∨ Q(x)) ⟷ rex(M,P) ∨ rex(M,Q)
opaque symbol rex_disj_distrib (M : τ ι → Prop) (P Q : τ ι → Prop) :
  π (rex M (λ x, P x ∨ Q x) ⇔ (rex M P ∨ rex M Q)) ≔
begin
  assume M P Q;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hMx : π (M x) { refine ∧ₑ₁ hx };
    have hdisj : π (P x ∨ Q x) { refine ∧ₑ₂ hx };
    refine ∨ₑ hdisj _ _
    { assume hPx; refine ∨ᵢ₁ (∃ᵢ x (∧ᵢ hMx hPx)) }
    { assume hQx; refine ∨ᵢ₂ (∃ᵢ x (∧ᵢ hMx hQx)) } }
  { assume hdisj;
    refine ∨ₑ hdisj _ _
    { assume hex;
      refine ∃ₑ hex _;
      assume x hx;
      have hMx : π (M x) { refine ∧ₑ₁ hx };
      have hPx : π (P x) { refine ∧ₑ₂ hx };
      refine ∃ᵢ x (∧ᵢ hMx (∨ᵢ₁ hPx)) }
    { assume hex;
      refine ∃ₑ hex _;
      assume x hx;
      have hMx : π (M x) { refine ∧ₑ₁ hx };
      have hQx : π (Q x) { refine ∧ₑ₂ hx };
      refine ∃ᵢ x (∧ᵢ hMx (∨ᵢ₂ hQx)) } }
end;

// ===========================================================================
// Section: One-point rules for class quantifiers
// ===========================================================================

// rex_triv_one_point1: rex(M, λx. x = a) ⟷ M(a)
opaque symbol rex_triv_one_point1 (M : τ ι → Prop) (a : τ ι) :
  π (rex M (λ x, x = a) ⇔ M a) ≔
begin
  assume M a;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hMx : π (M x) { refine ∧ₑ₁ hx };
    have hxa : π (x = a) { refine ∧ₑ₂ hx };
    refine ind_eq (eq_sym hxa) (λ w, M w) hMx }
  { assume hMa;
    refine ∃ᵢ a (∧ᵢ hMa (eq_refl a)) }
end;

// rex_triv_one_point2: rex(M, λx. a = x) ⟷ M(a)
opaque symbol rex_triv_one_point2 (M : τ ι → Prop) (a : τ ι) :
  π (rex M (λ x, a = x) ⇔ M a) ≔
begin
  assume M a;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hMx : π (M x) { refine ∧ₑ₁ hx };
    have hax : π (a = x) { refine ∧ₑ₂ hx };
    refine ind_eq hax (λ w, M w) hMx }
  { assume hMa;
    refine ∃ᵢ a (∧ᵢ hMa (eq_refl a)) }
end;

// rex_one_point1: rex(M, λx. x = a ∧ P(x)) ⟷ M(a) ∧ P(a)
opaque symbol rex_one_point1 (M : τ ι → Prop) (P : τ ι → Prop) (a : τ ι) :
  π (rex M (λ x, x = a ∧ P x) ⇔ (M a ∧ P a)) ≔
begin
  assume M P a;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hMx : π (M x) { refine ∧ₑ₁ hx };
    have hconj : π (x = a ∧ P x) { refine ∧ₑ₂ hx };
    have hxa : π (x = a) { refine ∧ₑ₁ hconj };
    have hPx : π (P x) { refine ∧ₑ₂ hconj };
    apply ∧ᵢ
    { refine ind_eq (eq_sym hxa) (λ w, M w) hMx }
    { refine ind_eq (eq_sym hxa) (λ w, P w) hPx } }
  { assume h;
    have hMa : π (M a) { refine ∧ₑ₁ h };
    have hPa : π (P a) { refine ∧ₑ₂ h };
    refine ∃ᵢ a (∧ᵢ hMa (∧ᵢ (eq_refl a) hPa)) }
end;

// rex_one_point2: rex(M, λx. a = x ∧ P(x)) ⟷ M(a) ∧ P(a)
opaque symbol rex_one_point2 (M : τ ι → Prop) (P : τ ι → Prop) (a : τ ι) :
  π (rex M (λ x, a = x ∧ P x) ⇔ (M a ∧ P a)) ≔
begin
  assume M P a;
  apply ∧ᵢ
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hMx : π (M x) { refine ∧ₑ₁ hx };
    have hconj : π (a = x ∧ P x) { refine ∧ₑ₂ hx };
    have hax : π (a = x) { refine ∧ₑ₁ hconj };
    have hPx : π (P x) { refine ∧ₑ₂ hconj };
    apply ∧ᵢ
    { refine ind_eq hax (λ w, M w) hMx }
    { refine ind_eq hax (λ w, P w) hPx } }
  { assume h;
    have hMa : π (M a) { refine ∧ₑ₁ h };
    have hPa : π (P a) { refine ∧ₑ₂ h };
    refine ∃ᵢ a (∧ᵢ hMa (∧ᵢ (eq_refl a) hPa)) }
end;

// rall_one_point1: rall(M, λx. x = a ⇒ P(x)) ⟷ (M(a) ⇒ P(a))
opaque symbol rall_one_point1 (M : τ ι → Prop) (P : τ ι → Prop) (a : τ ι) :
  π (rall M (λ x, x = a ⇒ P x) ⇔ (M a ⇒ P a)) ≔
begin
  assume M P a;
  apply ∧ᵢ
  { assume hall hMa;
    refine hall a hMa (eq_refl a) }
  { assume h x hMx hxa;
    have hMa : π (M a) { refine ind_eq (eq_sym hxa) (λ w, M w) hMx };
    have hPa : π (P a) { refine h hMa };
    refine ind_eq hxa (λ w, P w) hPa }
end;

// rall_one_point2: rall(M, λx. a = x ⇒ P(x)) ⟷ (M(a) ⇒ P(a))
opaque symbol rall_one_point2 (M : τ ι → Prop) (P : τ ι → Prop) (a : τ ι) :
  π (rall M (λ x, a = x ⇒ P x) ⇔ (M a ⇒ P a)) ≔
begin
  assume M P a;
  apply ∧ᵢ
  { assume hall hMa;
    refine hall a hMa (eq_refl a) }
  { assume h x hMx hax;
    have hMa : π (M a) { refine ind_eq hax (λ w, M w) hMx };
    have hPa : π (P a) { refine h hMa };
    refine ind_eq (eq_sym hax) (λ w, P w) hPa }
end;

// ===========================================================================
// Section: Sets as classes
// ===========================================================================

// setclass(A) ≡ λx. x ∈ A
symbol setclass (A : τ ι) : τ ι → Prop ≔ λ x, x ∈ A;

// setclass_iff: setclass(A, x) ⟷ x ∈ A
opaque symbol setclass_iff (A x : τ ι) :
  π (setclass A x ⇔ x ∈ A) ≔
begin
  assume A x;
  apply ∧ᵢ
  { assume h; apply h }
  { assume h; apply h }
end;

// rall_setclass_is_ball: rall(setclass(A), P) ⟷ Ball(A, P)
opaque symbol rall_setclass_is_ball (A : τ ι) (P : τ ι → Prop) :
  π (rall (setclass A) P ⇔ Ball A P) ≔
begin
  assume A P;
  apply ∧ᵢ
  { assume h x hxA; refine h x hxA }
  { assume h x hxA; refine h x hxA }
end;

// rex_setclass_is_bex: rex(setclass(A), P) ⟷ Bex(A, P)
opaque symbol rex_setclass_is_bex (A : τ ι) (P : τ ι → Prop) :
  π (rex (setclass A) P ⇔ Bex A P) ≔
begin
  assume A P;
  apply ∧ᵢ
  { assume h;
    refine ∃ₑ h _;
    assume x hx;
    refine ∃ᵢ x hx }
  { assume h;
    refine ∃ₑ h _;
    assume x hx;
    refine ∃ᵢ x hx }
end;
