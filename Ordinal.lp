// Ordinal: Ordinal numbers in ZF
//
// Isabelle source: Ordinal.thy
// Defines: Transset, Ord, lt, Limit, succ_ord
// Key: ordinals are transitive sets well-ordered by ∈

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.Trancl ZF.WF ZF.equalities;

// ===========================================================================
// Transitive sets
// ===========================================================================

// Transset(A): A is a transitive set (every member is a subset)
symbol Transset (A : τ ι) : Prop ≔
  Ball A (λ x, x ⊆ A);

// ===========================================================================
// Ordinal numbers
// ===========================================================================

// Ord(i): i is an ordinal iff i is transitive and ∈ is well-founded on i
// (In Isabelle: Transset(i) ∧ ∀x∈i. Transset(x))
// Equivalent: transitive set whose members are all transitive sets
symbol Ord (i : τ ι) : Prop ≔
  Transset i ∧ Ball i (λ x, Transset x);

// ===========================================================================
// Ordinal ordering: i < j iff i ∈ j (for ordinals)
// ===========================================================================

// lt: i < j  ≡  i ∈ j ∧ Ord(j)   (Isabelle/ZF definition)
symbol lt (i j : τ ι) : Prop ≔ i ∈ j ∧ Ord j;

// le: i ≤ j  ≡  i < succ(j)        (Isabelle/ZF definition)
symbol le (i j : τ ι) : Prop ≔ lt i (succ j);

// ===========================================================================
// Basic ordinal properties
// ===========================================================================

// 0 is an ordinal
opaque symbol Ord_0 : π (Ord empty) ≔
begin
  apply ∧ᵢ
  { // Transset(empty): vacuously true
    assume x hx;
    refine ⊥ₑ (emptyE x hx) }
  { // Ball empty (λ x, Transset x): vacuously true
    assume x hx;
    refine ⊥ₑ (emptyE x hx) }
end;

// Members of ordinals are ordinals
opaque symbol Ord_in_Ord (i j : τ ι) :
  π (Ord i) → π (j ∈ i) → π (Ord j) ≔
begin
  assume i j hOi hji;
  // Ord(i) = Transset(i) ∧ Ball(i, Transset)
  have hTi : π (Transset i) { refine ∧ₑ₁ hOi };
  have hBi : π (Ball i (λ x, Transset x)) { refine ∧ₑ₂ hOi };
  // Transset(j): from Ball(i, Transset) and j ∈ i
  have hTj : π (Transset j) { refine hBi j hji };
  // Ball(j, Transset): for any x ∈ j, show Transset(x)
  // Since Transset(i) and j ∈ i, j ⊆ i. So x ∈ j → x ∈ i → Transset(x).
  have hBj : π (Ball j (λ x, Transset x)) {
    assume x hxj;
    // j ⊆ i from Transset(i): Transset(i) = Ball(i, λ x, x ⊆ i), so j ∈ i gives j ⊆ i
    have hjsub : π (j ⊆ i) { refine hTi j hji };
    have hxi : π (x ∈ i) { refine hjsub x hxj };
    refine hBi x hxi
  };
  apply ∧ᵢ hTj hBj
end;

// succ of an ordinal is an ordinal
opaque symbol Ord_succ (i : τ ι) :
  π (Ord i) → π (Ord (succ i)) ≔
begin
  assume i hOi;
  have hTi : π (Transset i) { refine ∧ₑ₁ hOi };
  have hBi : π (Ball i (λ x, Transset x)) { refine ∧ₑ₂ hOi };
  // Need: Transset(succ(i)) ∧ Ball(succ(i), Transset)
  apply ∧ᵢ
  { // Transset(succ(i)): ∀x ∈ succ(i). x ⊆ succ(i)
    assume x hxs;
    // x ∈ succ(i) means x = i ∨ x ∈ i
    have hdisj : π (x = i ∨ x ∈ i) { refine ∧ₑ₁ (succ_iff x i) hxs };
    // Need: x ⊆ succ(i), i.e., ∀z ∈ x. z ∈ succ(i)
    assume z hzx;
    refine ∨ₑ hdisj _ _
    { // x = i: z ∈ x = i, so z ∈ i, so z ∈ succ(i) by succI2
      assume hxi;
      have hzi : π (z ∈ i) { refine ind_eq (eq_sym hxi) (λ w, z ∈ w) hzx };
      refine succI2 z i hzi }
    { // x ∈ i: Transset(i) gives x ⊆ i (wait, we need x ⊆ i)
      // Actually Transset(i) = Ball(i, λ x, x ⊆ i), so x ∈ i gives x ⊆ i
      assume hxi;
      have hxsub : π (x ⊆ i) { refine hTi x hxi };
      have hzi : π (z ∈ i) { refine hxsub z hzx };
      refine succI2 z i hzi } }
  { // Ball(succ(i), Transset): ∀x ∈ succ(i). Transset(x)
    assume x hxs;
    have hdisj : π (x = i ∨ x ∈ i) { refine ∧ₑ₁ (succ_iff x i) hxs };
    refine ∨ₑ hdisj _ _
    { // x = i: Transset(i)
      assume hxi;
      refine ind_eq hxi (λ w, Transset w) hTi }
    { // x ∈ i: Ball(i, Transset) gives Transset(x)
      assume hxi;
      refine hBi x hxi } }
end;

// Ord_linear is defined after trans_induct (below)

// ===========================================================================
// Limit ordinals
// ===========================================================================

// A limit ordinal is a nonzero ordinal that is not a successor
symbol Limit (i : τ ι) : Prop ≔
  Ord i ∧ i ≠ empty ∧ (`∀ (y : τ ι), y ∈ i ⇒ succ y ∈ i);

// ===========================================================================
// Ordinal arithmetic (basic)
// ===========================================================================

// Union of a set of ordinals is an ordinal
opaque symbol Ord_Union (A : τ ι) :
  π (Ball A (λ x, Ord x)) → π (Ord (Union A)) ≔
begin
  assume A hAll;
  apply ∧ᵢ
  { // Transset(Union A): ∀x ∈ Union(A). x ⊆ Union(A)
    assume x hxU;
    // x ∈ Union(A) means ∃B ∈ A. x ∈ B
    have hbex : π (Bex A (λ B, x ∈ B)) { refine UnionE x A hxU };
    // Need: x ⊆ Union(A), i.e., ∀z ∈ x. z ∈ Union(A)
    assume z hzx;
    refine ∃ₑ hbex _;
    assume B hB;
    have hBA : π (B ∈ A) { refine ∧ₑ₁ hB };
    have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
    // Ord(B), so Transset(B), so x ∈ B gives x ⊆ B
    have hOB : π (Ord B) { refine hAll B hBA };
    have hTB : π (Transset B) { refine ∧ₑ₁ hOB };
    have hxsubB : π (x ⊆ B) { refine hTB x hxB };
    have hzB : π (z ∈ B) { refine hxsubB z hzx };
    // z ∈ B and B ∈ A, so z ∈ Union(A)
    refine UnionI z B A hzB hBA }
  { // Ball(Union A, Transset): ∀x ∈ Union(A). Transset(x)
    assume x hxU;
    have hbex : π (Bex A (λ B, x ∈ B)) { refine UnionE x A hxU };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBA : π (B ∈ A) { refine ∧ₑ₁ hB };
    have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
    // Ord(B) and x ∈ B gives Transset(x) via Ball(B, Transset)
    have hOB : π (Ord B) { refine hAll B hBA };
    have hBallB : π (Ball B (λ y, Transset y)) { refine ∧ₑ₂ hOB };
    refine hBallB x hxB }
end;

// Intersection of a set of ordinals is an ordinal.
// (Faithful to Isabelle Ord_Inter, which needs no A≠0 premise: Inter(empty)=empty
//  and Ord(empty) holds, so the proof is uniform in A.)
opaque symbol Ord_Inter (A : τ ι) :
  π (Ball A (λ x, Ord x)) → π (Ord (Inter A)) ≔
begin
  assume A hAll;
  // Inter(A) = Collect(Union A)(λ x, Ball A (λ y, x ∈ y))
  // x ∈ Inter(A) iff x ∈ Union(A) ∧ ∀y∈A. x∈y
  apply ∧ᵢ
  { // Transset(Inter A): ∀x ∈ Inter(A). x ⊆ Inter(A)
    assume x hxI;
    // x ∈ Inter(A) means x ∈ Union(A) ∧ Ball(A, λ y, x ∈ y)
    have hxU : π (x ∈ Union A) { refine CollectD1 x (Union A) (λ w, Ball A (λ y, w ∈ y)) hxI };
    have hball : π (Ball A (λ y, x ∈ y)) { refine CollectD2 x (Union A) (λ w, Ball A (λ y, w ∈ y)) hxI };
    // Need: x ⊆ Inter(A), i.e., ∀z ∈ x. z ∈ Inter(A)
    assume z hzx;
    // z ∈ Inter(A) means z ∈ Union(A) ∧ ∀y∈A. z∈y
    refine CollectI z (Union A) (λ w, Ball A (λ y, w ∈ y)) _ _
    { // z ∈ Union(A): pick any B ∈ A, x ∈ B, Transset(B) gives x ⊆ B, so z ∈ B
      have hbex : π (Bex A (λ B, x ∈ B)) { refine UnionE x A hxU };
      refine ∃ₑ hbex _;
      assume B hB;
      have hBA : π (B ∈ A) { refine ∧ₑ₁ hB };
      have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
      have hOB : π (Ord B) { refine hAll B hBA };
      have hTB : π (Transset B) { refine ∧ₑ₁ hOB };
      have hxsubB : π (x ⊆ B) { refine hTB x hxB };
      have hzB : π (z ∈ B) { refine hxsubB z hzx };
      refine UnionI z B A hzB hBA }
    { // ∀y∈A. z∈y: for y ∈ A, x ∈ y (from hball), Transset(y) gives x ⊆ y, so z ∈ y
      assume y hyA;
      have hxy : π (x ∈ y) { refine hball y hyA };
      have hOy : π (Ord y) { refine hAll y hyA };
      have hTy : π (Transset y) { refine ∧ₑ₁ hOy };
      have hxsuby : π (x ⊆ y) { refine hTy x hxy };
      refine hxsuby z hzx } }
  { // Ball(Inter A, Transset): ∀x ∈ Inter(A). Transset(x)
    assume x hxI;
    have hxU : π (x ∈ Union A) { refine CollectD1 x (Union A) (λ w, Ball A (λ y, w ∈ y)) hxI };
    // x ∈ Union(A) means ∃B∈A. x∈B. Pick B. Ord(B) gives Transset(x).
    have hbex : π (Bex A (λ B, x ∈ B)) { refine UnionE x A hxU };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBA : π (B ∈ A) { refine ∧ₑ₁ hB };
    have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
    have hOB : π (Ord B) { refine hAll B hBA };
    have hBallB : π (Ball B (λ y, Transset y)) { refine ∧ₑ₂ hOB };
    refine hBallB x hxB }
end;

// ===========================================================================
// Transfinite induction
// ===========================================================================

opaque symbol trans_induct (i : τ ι) (P : τ ι → Prop) :
  π (Ord i) →
  π (`∀ (x : τ ι), Ord x ⇒ Ball x (λ y, P y) ⇒ P x) →
  π (P i) ≔
begin
  assume i P hOi hstep;
  // By contradiction using classical logic
  refine ¬¬ₑ _ _;
  assume hnPi;
  // Ord(succ(i))
  have hOsi : π (Ord (succ i)) { refine Ord_succ i hOi };
  // S = Collect(succ(i), λ x, Ord(x) ∧ ¬P(x))
  // S is nonempty: i ∈ succ(i), Ord(i), ¬P(i)
  have hiS : π (i ∈ Collect (succ i) (λ x, Ord x ∧ ¬ (P x))) {
    refine CollectI i (succ i) (λ x, Ord x ∧ ¬ (P x)) (succI1 i) (∧ᵢ hOi hnPi)
  };
  have hSne : π (Collect (succ i) (λ x, Ord x ∧ ¬ (P x)) ≠ empty) {
    refine ne_empty (Collect (succ i) (λ x, Ord x ∧ ¬ (P x))) i hiS
  };
  // By foundation, S = empty ∨ ∃x₀∈S. ∀y∈x₀. y∉S
  have hfound : π (Collect (succ i) (λ x, Ord x ∧ ¬ (P x)) = empty
    ∨ Bex (Collect (succ i) (λ x, Ord x ∧ ¬ (P x)))
        (λ x, Ball x (λ y, y ∉ Collect (succ i) (λ x, Ord x ∧ ¬ (P x)))))
    { refine foundation (Collect (succ i) (λ x, Ord x ∧ ¬ (P x))) };
  refine ∨ₑ hfound _ _
  { // S = empty: contradiction since i ∈ S
    assume heq;
    refine emptyE i _;
    rewrite left heq;
    apply hiS }
  { // ∃x₀∈S. ∀y∈x₀. y∉S
    assume hbex;
    refine ∃ₑ hbex _;
    assume x0 hx0;
    have hx0S : π (x0 ∈ Collect (succ i) (λ x, Ord x ∧ ¬ (P x))) { refine ∧ₑ₁ hx0 };
    have hx0min : π (Ball x0 (λ y, y ∉ Collect (succ i) (λ x, Ord x ∧ ¬ (P x)))) { refine ∧ₑ₂ hx0 };
    // x0 ∈ succ(i), Ord(x0), ¬P(x0)
    have hx0si : π (x0 ∈ succ i) { refine CollectD1 x0 (succ i) (λ x, Ord x ∧ ¬ (P x)) hx0S };
    have hx0prop : π (Ord x0 ∧ ¬ (P x0)) { refine CollectD2 x0 (succ i) (λ x, Ord x ∧ ¬ (P x)) hx0S };
    have hOx0 : π (Ord x0) { refine ∧ₑ₁ hx0prop };
    have hnPx0 : π (¬ (P x0)) { refine ∧ₑ₂ hx0prop };
    // Transset(succ(i)) gives x0 ⊆ succ(i)
    have hTsi : π (Transset (succ i)) { refine ∧ₑ₁ hOsi };
    have hx0sub : π (x0 ⊆ succ i) { refine hTsi x0 hx0si };
    // Ball(x0, P): for y ∈ x0, show P(y)
    have hBallP : π (Ball x0 (λ y, P y)) {
      assume y hyx0;
      // y ∈ x0 and Ord(x0), so Ord(y)
      have hOy : π (Ord y) { refine Ord_in_Ord x0 y hOx0 hyx0 };
      // y ∈ succ(i) since x0 ⊆ succ(i)
      have hysi : π (y ∈ succ i) { refine hx0sub y hyx0 };
      // y ∉ S (from minimality: hx0min)
      have hynotS : π (y ∉ Collect (succ i) (λ x, Ord x ∧ ¬ (P x))) { refine hx0min y hyx0 };
      // y ∉ S means ¬(y ∈ succ(i) ∧ Ord(y) ∧ ¬P(y))
      // We know y ∈ succ(i) and Ord(y), so ¬¬P(y), hence P(y)
      refine ¬¬ₑ _ _;
      assume hnPy;
      have hyS : π (y ∈ Collect (succ i) (λ x, Ord x ∧ ¬ (P x))) {
        refine CollectI y (succ i) (λ x, Ord x ∧ ¬ (P x)) hysi (∧ᵢ hOy hnPy)
      };
      refine hynotS hyS
    };
    // By hstep: Ord(x0) → Ball(x0, P) → P(x0)
    have hPx0 : π (P x0) { refine hstep x0 hOx0 hBallP };
    refine hnPx0 hPx0 }
end;

// ===========================================================================
// Ordinal linearity (requires trans_induct)
// ===========================================================================

// Helper: Ord_trans — if i ∈ j, j ∈ k, Ord(k), then i ∈ k
opaque symbol Ord_trans (i j k : τ ι) :
  π (i ∈ j) → π (j ∈ k) → π (Ord k) → π (i ∈ k) ≔
begin
  assume i j k hij hjk hOk;
  have hTk : π (Transset k) { refine ∧ₑ₁ hOk };
  have hjsub : π (j ⊆ k) { refine hTk j hjk };
  refine hjsub i hij
end;

// Ordinals are linearly ordered
opaque symbol Ord_linear (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (i ∈ j ∨ i = j ∨ j ∈ i) ≔
begin
  assume i j hOi hOj;
  // By trans_induct on i: P(i) = ∀j. Ord(j) → i ∈ j ∨ i = j ∨ j ∈ i
  refine trans_induct i (λ i, `∀ (j : τ ι), Ord j ⇒ (i ∈ j ∨ i = j ∨ j ∈ i)) hOi _ j hOj;
  // Step: assume Ord(x), Ball(x, λ k, ∀j. Ord(j) → k ∈ j ∨ k = j ∨ j ∈ k)
  assume x hOx hIH_outer;
  // For j1: inner trans_induct
  assume j1 hOj1;
  refine trans_induct j1 (λ j, x ∈ j ∨ x = j ∨ j ∈ x) hOj1 _;
  assume y hOy hIH_inner;
  // By excluded middle on x ∈ y
  have hem_xy : π (x ∈ y ∨ ¬ (x ∈ y)) { refine em (x ∈ y) };
  refine ∨ₑ hem_xy _ _
  { assume hxy; refine ∨ᵢ₁ hxy }
  { assume hnxy;
    have hem_yx : π (y ∈ x ∨ ¬ (y ∈ x)) { refine em (y ∈ x) };
    refine ∨ₑ hem_yx _ _
    { assume hyx; refine ∨ᵢ₂ (∨ᵢ₂ hyx) }
    { assume hnyx;
      // y ⊆ x: for k ∈ y, inner IH gives x ∈ k ∨ x = k ∨ k ∈ x
      have hysub : π (y ⊆ x) {
        assume k hky;
        have hd : π (x ∈ k ∨ x = k ∨ k ∈ x) { refine hIH_inner k hky };
        refine ∨ₑ hd _ _
        { assume hxk;
          refine ⊥ₑ _;
          refine hnxy (Ord_trans x k y hxk hky hOy) }
        { assume hd2;
          refine ∨ₑ hd2 _ _
          { assume hxk;
            refine ⊥ₑ _;
            refine hnxy (ind_eq hxk (λ w, w ∈ y) hky) }
          { assume hkx; apply hkx } }
      };
      // x ⊆ y: for k ∈ x, outer IH gives k ∈ y ∨ k = y ∨ y ∈ k
      have hxsub : π (x ⊆ y) {
        assume k hkx;
        have hOk : π (Ord k) { refine Ord_in_Ord x k hOx hkx };
        have hd : π (k ∈ y ∨ k = y ∨ y ∈ k) { refine hIH_outer k hkx y hOy };
        refine ∨ₑ hd _ _
        { assume hky; apply hky }
        { assume hd2;
          refine ∨ₑ hd2 _ _
          { assume hky;
            refine ⊥ₑ _;
            refine hnyx (ind_eq (eq_sym hky) (λ w, w ∈ x) hkx) }
          { assume hyk;
            refine ⊥ₑ _;
            refine hnyx (Ord_trans y k x hyk hkx hOx) } }
      };
      refine ∨ᵢ₂ (∨ᵢ₁ (subset_antisym x y hxsub hysub)) } }
end;

// ===========================================================================
// Phase 2c: Transset lemmas
// ===========================================================================

// Transset(0): empty is transitive (vacuously)
opaque symbol Transset_0 : π (Transset empty) ≔
begin
  assume x hx;
  refine ⊥ₑ (emptyE x hx)
end;

// Transset(i) → Transset(succ(i))
opaque symbol Transset_succ (i : τ ι) :
  π (Transset i) → π (Transset (succ i)) ≔
begin
  assume i hTi;
  // Transset(succ(i)): ∀x ∈ succ(i). x ⊆ succ(i)
  assume x hxs;
  have hdisj : π (x = i ∨ x ∈ i) { refine ∧ₑ₁ (succ_iff x i) hxs };
  assume z hzx;
  refine ∨ₑ hdisj _ _
  { assume hxi;
    have hzi : π (z ∈ i) { refine ind_eq (eq_sym hxi) (λ w, z ∈ w) hzx };
    refine succI2 z i hzi }
  { assume hxi;
    have hxsub : π (x ⊆ i) { refine hTi x hxi };
    have hzi : π (z ∈ i) { refine hxsub z hzx };
    refine succI2 z i hzi }
end;

// Transset(A) → Transset(B) → Transset(A ∪ B)
opaque symbol Transset_Un (A B : τ ι) :
  π (Transset A) → π (Transset B) → π (Transset (Un A B)) ≔
begin
  assume A B hTA hTB;
  assume x hxU;
  have hdisj : π (x ∈ A ∨ x ∈ B) { refine ∧ₑ₁ (Un_iff x A B) hxU };
  assume z hzx;
  refine ∨ₑ hdisj _ _
  { assume hxA;
    have hxsub : π (x ⊆ A) { refine hTA x hxA };
    have hzA : π (z ∈ A) { refine hxsub z hzx };
    refine UnI1 z A B hzA }
  { assume hxB;
    have hxsub : π (x ⊆ B) { refine hTB x hxB };
    have hzB : π (z ∈ B) { refine hxsub z hzx };
    refine UnI2 z A B hzB }
end;

// Transset(A) → Transset(B) → Transset(A ∩ B)
opaque symbol Transset_Int (A B : τ ι) :
  π (Transset A) → π (Transset B) → π (Transset (Int A B)) ≔
begin
  assume A B hTA hTB;
  assume x hxI;
  have hxA : π (x ∈ A) { refine IntD1 x A B hxI };
  have hxB : π (x ∈ B) { refine IntD2 x A B hxI };
  assume z hzx;
  have hxsubA : π (x ⊆ A) { refine hTA x hxA };
  have hxsubB : π (x ⊆ B) { refine hTB x hxB };
  have hzA : π (z ∈ A) { refine hxsubA z hzx };
  have hzB : π (z ∈ B) { refine hxsubB z hzx };
  refine IntI z A B hzA hzB
end;

// ∀x∈A. Transset(x) → Transset(⋃A)
opaque symbol Transset_Union_family (A : τ ι) :
  π (Ball A (λ x, Transset x)) → π (Transset (Union A)) ≔
begin
  assume A hAll;
  assume x hxU;
  have hbex : π (Bex A (λ B, x ∈ B)) { refine UnionE x A hxU };
  assume z hzx;
  refine ∃ₑ hbex _;
  assume B hB;
  have hBA : π (B ∈ A) { refine ∧ₑ₁ hB };
  have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
  have hTB : π (Transset B) { refine hAll B hBA };
  have hxsubB : π (x ⊆ B) { refine hTB x hxB };
  have hzB : π (z ∈ B) { refine hxsubB z hzx };
  refine UnionI z B A hzB hBA
end;

// Transset(A) → ⋃A ⊆ A
opaque symbol Transset_iff_Union_subset_fwd (A : τ ι) :
  π (Transset A) → π (Union A ⊆ A) ≔
begin
  assume A hTA;
  assume x hxU;
  have hbex : π (Bex A (λ B, x ∈ B)) { refine UnionE x A hxU };
  refine ∃ₑ hbex _;
  assume B hB;
  have hBA : π (B ∈ A) { refine ∧ₑ₁ hB };
  have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
  have hBsub : π (B ⊆ A) { refine hTA B hBA };
  refine hBsub x hxB
end;

// ⋃A ⊆ A → Transset(A)
opaque symbol Transset_iff_Union_subset_bwd (A : τ ι) :
  π (Union A ⊆ A) → π (Transset A) ≔
begin
  assume A hUsub;
  assume x hxA;
  assume z hzx;
  have hzU : π (z ∈ Union A) { refine UnionI z x A hzx hxA };
  refine hUsub z hzU
end;

// Transset(A) → A ⊆ Pow(A)
opaque symbol Transset_iff_Pow_fwd (A : τ ι) :
  π (Transset A) → π (A ⊆ Pow A) ≔
begin
  assume A hTA;
  assume x hxA;
  have hxsub : π (x ⊆ A) { refine hTA x hxA };
  refine PowI x A hxsub
end;

// A ⊆ Pow(A) → Transset(A)
opaque symbol Transset_iff_Pow_bwd (A : τ ι) :
  π (A ⊆ Pow A) → π (Transset A) ≔
begin
  assume A hAsub;
  assume x hxA;
  have hxP : π (x ∈ Pow A) { refine hAsub x hxA };
  refine PowD x A hxP
end;

// ===========================================================================
// Phase 2d: Ord lemmas
// ===========================================================================

// OrdI: Transset(i) → Ball(i, Transset) → Ord(i)
opaque symbol OrdI (i : τ ι) :
  π (Transset i) → π (Ball i (λ x, Transset x)) → π (Ord i) ≔
begin
  assume i hTi hBi;
  apply ∧ᵢ hTi hBi
end;

// Ord_is_Transset: Ord(i) → Transset(i)
opaque symbol Ord_is_Transset (i : τ ι) :
  π (Ord i) → π (Transset i) ≔
begin
  assume i hOi;
  refine ∧ₑ₁ hOi
end;

// Ord_contains_Transset: Ord(i) → j ∈ i → Transset(j)
opaque symbol Ord_contains_Transset (i j : τ ι) :
  π (Ord i) → π (j ∈ i) → π (Transset j) ≔
begin
  assume i j hOi hji;
  have hBi : π (Ball i (λ x, Transset x)) { refine ∧ₑ₂ hOi };
  refine hBi j hji
end;

// OrdmemD: j ∈ i → Ord(i) → j ⊆ i
opaque symbol OrdmemD (i j : τ ι) :
  π (j ∈ i) → π (Ord i) → π (j ⊆ i) ≔
begin
  assume i j hji hOi;
  have hTi : π (Transset i) { refine ∧ₑ₁ hOi };
  refine hTi j hji
end;

// Ord_succ_subsetI: i ∈ j → Ord(j) → succ(i) ⊆ j
opaque symbol Ord_succ_subsetI (i j : τ ι) :
  π (i ∈ j) → π (Ord j) → π (succ i ⊆ j) ≔
begin
  assume i j hij hOj;
  have hisub : π (i ⊆ j) { refine OrdmemD j i hij hOj };
  assume x hxs;
  have hdisj : π (x = i ∨ x ∈ i) { refine ∧ₑ₁ (succ_iff x i) hxs };
  refine ∨ₑ hdisj _ _
  { assume hxi;
    refine ind_eq hxi (λ w, w ∈ j) hij }
  { assume hxi;
    refine hisub x hxi }
end;

// Ord_succD: Ord(j) → i ∈ succ(j) → i ∈ j ∨ i = j
opaque symbol Ord_succD (i j : τ ι) :
  π (Ord j) → π (i ∈ succ j) → π (i ∈ j ∨ i = j) ≔
begin
  assume i j hOj his;
  have hdisj : π (i = j ∨ i ∈ j) { refine ∧ₑ₁ (succ_iff i j) his };
  refine ∨ₑ hdisj _ _
  { assume hij; refine ∨ᵢ₂ hij }
  { assume hij; refine ∨ᵢ₁ hij }
end;

// succ(i) ∈ succ(j) → i ∈ j   (Isabelle Ord_succ_mem_iff needs only Ord j)
opaque symbol Ord_succ_mem_iff_fwd (i j : τ ι) :
  π (Ord j) → π (succ i ∈ succ j) → π (i ∈ j) ≔
begin
  assume i j hOj hsis;
  have hdisj : π (succ i = j ∨ succ i ∈ j) { refine ∧ₑ₁ (succ_iff (succ i) j) hsis };
  refine ∨ₑ hdisj _ _
  { assume hsi_eq_j;
    have hi_in_si : π (i ∈ succ i) { refine succI1 i };
    refine ind_eq (eq_sym hsi_eq_j) (λ w, i ∈ w) hi_in_si }
  { assume hsi_in_j;
    have hsi_sub : π (succ i ⊆ j) { refine OrdmemD j (succ i) hsi_in_j hOj };
    refine hsi_sub i (succI1 i) }
end;

// i ∈ j → succ(i) ∈ succ(j)   (needs only Ord j; Ord i derived from i∈j)
opaque symbol Ord_succ_mem_iff_bwd (i j : τ ι) :
  π (Ord j) → π (i ∈ j) → π (succ i ∈ succ j) ≔
begin
  assume i j hOj hij;
  have hOi : π (Ord i) { refine Ord_in_Ord j i hOj hij };
  have hOsi : π (Ord (succ i)) { refine Ord_succ i hOi };
  have hlin : π (succ i ∈ j ∨ succ i = j ∨ j ∈ succ i)
    { refine Ord_linear (succ i) j hOsi hOj };
  refine ∨ₑ hlin _ _
  { assume h; refine succI2 (succ i) j h }
  { assume hd;
    refine ∨ₑ hd _ _
    { assume heq;
      refine ∧ₑ₂ (succ_iff (succ i) j) (∨ᵢ₁ heq) }
    { assume hjsi;
      have hd2 : π (j = i ∨ j ∈ i) { refine ∧ₑ₁ (succ_iff j i) hjsi };
      refine ∨ₑ hd2 _ _
      { assume hji;
        refine ⊥ₑ _;
        have hii : π (i ∈ i) { refine ind_eq (eq_sym hji) (λ w, i ∈ w) hij };
        refine mem_irrefl i hii }
      { assume hji;
        refine ⊥ₑ _;
        refine mem_asym i j hij hji } } }
end;

// ===========================================================================
// Phase 2e: lt/le lemmas
// ===========================================================================

// ltI: i ∈ j → lt(i, j) (trivial from definition: lt ≔ ∈)
opaque symbol ltI (i j : τ ι) :
  π (i ∈ j) → π (Ord j) → π (lt i j) ≔
begin
  assume i j h hOj; refine ∧ᵢ h hOj
end;

// ltD: lt(i, j) → i ∈ j
opaque symbol ltD (i j : τ ι) :
  π (lt i j) → π (i ∈ j) ≔
begin
  assume i j h; refine ∧ₑ₁ h
end;

// ltE: lt(i, j) → (i ∈ j → P) → P
opaque symbol ltE (i j : τ ι) (P : Prop) :
  π (lt i j) → (π (i ∈ j) → π (Ord i) → π (Ord j) → π P) → π P ≔
begin
  assume i j P h f; refine f (∧ₑ₁ h) (Ord_in_Ord j i (∧ₑ₂ h) (∧ₑ₁ h)) (∧ₑ₂ h)
end;

// not_lt0: ¬ lt(i, 0) (nothing in empty)
opaque symbol not_lt0 (i : τ ι) : π (¬ (lt i empty)) ≔
begin
  assume i h;
  refine emptyE i (ltD i empty h)
end;

// lt_Ord: lt(i, j) → Ord(i)   (Ord j is derivable from lt i j, not a premise)
opaque symbol lt_Ord (i j : τ ι) :
  π (lt i j) → π (Ord i) ≔
begin
  assume i j hij;
  refine Ord_in_Ord j i (∧ₑ₂ hij) (ltD i j hij)
end;

// lt_trans: lt(i,j) → lt(j,k) → lt(i,k)   (Ord k derived from lt j k)
opaque symbol lt_trans (i j k : τ ι) :
  π (lt i j) → π (lt j k) → π (lt i k) ≔
begin
  assume i j k hij hjk;
  have hOk : π (Ord k) { refine ∧ₑ₂ hjk };
  refine ltI i k (Ord_trans i j k (ltD i j hij) (ltD j k hjk) hOk) hOk
end;

// lt_not_sym: lt(i,j) → ¬ lt(j,i)
opaque symbol lt_not_sym (i j : τ ι) :
  π (lt i j) → π (¬ (lt j i)) ≔
begin
  assume i j hij;
  assume hji;
  refine mem_asym i j (ltD i j hij) (ltD j i hji)
end;

// lt_irrefl: ¬ lt(i,i)   (no Ord premise, matching lt_not_refl)
opaque symbol lt_irrefl (i : τ ι) :
  π (¬ (lt i i)) ≔
begin
  assume i hii;
  refine mem_irrefl i (ltD i i hii)
end;

// leI: i ∈ j → le(i, j)
opaque symbol leI (i j : τ ι) :
  π (i ∈ j) → π (Ord j) → π (le i j) ≔
begin
  assume i j h hOj; refine ∧ᵢ (succI2 i j h) (Ord_succ j hOj)
end;

// le_eqI: i = j → le(i, j)
opaque symbol le_eqI (i j : τ ι) :
  π (i = j) → π (Ord j) → π (le i j) ≔
begin
  assume i j h hOj;
  refine ∧ᵢ (ind_eq h (λ w, w ∈ succ j) (succI1 j)) (Ord_succ j hOj)
end;

// le_refl: Ord(i) → le(i, i)
opaque symbol le_refl (i : τ ι) : π (Ord i) → π (le i i) ≔
begin
  assume i hOi; refine ∧ᵢ (succI1 i) (Ord_succ i hOi)
end;

// leE: le(i, j) → i ∈ j ∨ i = j  (recover the disjunction)
opaque symbol leE (i j : τ ι) : π (le i j) → π (i ∈ j ∨ i = j) ≔
begin
  assume i j h;
  have hd : π (i = j ∨ i ∈ j) { refine ∧ₑ₁ (succ_iff i j) (∧ₑ₁ h) };
  refine ∨ₑ hd _ _
  { assume he; refine ∨ᵢ₂ he }
  { assume hm; refine ∨ᵢ₁ hm }
end;

// le_Ord2: le(i, j) → Ord(j)
opaque symbol le_Ord2 (i j : τ ι) : π (le i j) → π (Ord j) ≔
begin
  assume i j h;
  refine Ord_in_Ord (succ j) j (∧ₑ₂ h) (succI1 j)
end;

// le_anti_sym: le(i,j) → le(j,i) → i = j
opaque symbol le_anti_sym (i j : τ ι) :
  π (le i j) → π (le j i) → π (i = j) ≔
begin
  assume i j hij hji;
  // le(i,j) gives i ∈ j ∨ i = j
  refine ∨ₑ (leE i j hij) _ _
  { assume h_ij;
    refine ∨ₑ (leE j i hji) _ _
    { assume h_ji;
      refine ⊥ₑ _;
      refine mem_asym i j h_ij h_ji }
    { assume h_eq;
      refine eq_sym h_eq } }
  { assume h_eq;
    apply h_eq }
end;

// not_lt_iff_le forward: Ord(i) → Ord(j) → ¬lt(i,j) → le(j,i)
opaque symbol not_lt_imp_le (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (¬ (lt i j)) → π (le j i) ≔
begin
  assume i j hOi hOj hnij;
  // By Ord_linear: i ∈ j ∨ i = j ∨ j ∈ i
  have hlin : π (i ∈ j ∨ i = j ∨ j ∈ i) { refine Ord_linear i j hOi hOj };
  refine ∨ₑ hlin _ _
  { assume hij;
    refine ⊥ₑ (hnij (ltI i j hij hOj)) }
  { assume hd;
    refine ∨ₑ hd _ _
    { assume heq; refine le_eqI j i (eq_sym heq) hOi }
    { assume hji; refine leI j i hji hOi } }
end;

// le_imp_not_lt: le(j,i) → ¬lt(i,j)
opaque symbol le_imp_not_lt (i j : τ ι) :
  π (le j i) → π (¬ (lt i j)) ≔
begin
  assume i j hji;
  assume hij;
  refine ∨ₑ (leE j i hji) _ _
  { assume h; refine mem_asym i j (ltD i j hij) h }
  { assume h;
    have hii : π (i ∈ i) { refine ind_eq (eq_sym h) (λ w, i ∈ w) (ltD i j hij) };
    refine mem_irrefl i hii }
end;

// Ord_0_le: Ord(i) → le(0, i)
opaque symbol Ord_0_le (i : τ ι) :
  π (Ord i) → π (le empty i) ≔
begin
  assume i hOi;
  // not_lt_imp_le: ¬(i ∈ 0) → le(0, i)
  // But simpler: either i = 0 or i ≠ 0
  have hem : π (i = empty ∨ ¬ (i = empty)) { refine em (i = empty) };
  refine ∨ₑ hem _ _
  { assume heq;
    refine le_eqI empty i (eq_sym heq) hOi }
  { assume hne;
    // Ord_linear: empty ∈ i ∨ empty = i ∨ i ∈ empty
    have hlin : π (empty ∈ i ∨ empty = i ∨ i ∈ empty) { refine Ord_linear empty i Ord_0 hOi };
    refine ∨ₑ hlin _ _
    { assume h; refine leI empty i h hOi }
    { assume hd;
      refine ∨ₑ hd _ _
      { assume heq; refine le_eqI empty i heq hOi }
      { assume h; refine ⊥ₑ (emptyE i h) } } }
end;

// Ord_0_lt: Ord(i) → i ≠ 0 → lt(0, i)
opaque symbol Ord_0_lt (i : τ ι) :
  π (Ord i) → π (i ≠ empty) → π (lt empty i) ≔
begin
  assume i hOi hne;
  have hle : π (le empty i) { refine Ord_0_le i hOi };
  refine ∨ₑ (leE empty i hle) _ _
  { assume h; refine ltI empty i h hOi }
  { assume heq;
    refine ⊥ₑ _;
    refine hne (eq_sym heq) }
end;

// succ_leI: Ord(j) → i ∈ j → le(succ(i), j)
// i.e., succ(i) ∈ j ∨ succ(i) = j
opaque symbol succ_leI (i j : τ ι) :
  π (Ord j) → π (i ∈ j) → π (le (succ i) j) ≔
begin
  assume i j hOj hij;
  // By Ord_linear on succ(i) and j
  have hOi : π (Ord i) { refine Ord_in_Ord j i hOj hij };
  have hOsi : π (Ord (succ i)) { refine Ord_succ i hOi };
  have hlin : π (succ i ∈ j ∨ succ i = j ∨ j ∈ succ i)
    { refine Ord_linear (succ i) j hOsi hOj };
  refine ∨ₑ hlin _ _
  { assume h; refine leI (succ i) j h hOj }
  { assume hd;
    refine ∨ₑ hd _ _
    { assume heq; refine le_eqI (succ i) j heq hOj }
    { assume hjsi;
      // j ∈ succ(i) means j = i ∨ j ∈ i
      have hd2 : π (j = i ∨ j ∈ i) { refine ∧ₑ₁ (succ_iff j i) hjsi };
      refine ∨ₑ hd2 _ _
      { assume hji;
        // j = i but i ∈ j, contradiction
        refine ⊥ₑ _;
        have hii : π (i ∈ i) { refine ind_eq (eq_sym hji) (λ w, i ∈ w) hij };
        refine mem_irrefl i hii }
      { assume hji;
        // j ∈ i and i ∈ j, contradiction
        refine ⊥ₑ _;
        refine mem_asym i j hij hji } } }
end;

// lt_succ: Ord(i) → lt(i, succ(i))
opaque symbol lt_succ (i : τ ι) :
  π (Ord i) → π (lt i (succ i)) ≔
begin
  assume i hOi;
  refine ltI i (succ i) (succI1 i) (Ord_succ i hOi)
end;

// le_imp_subset: le(i, j) → i ⊆ j   (Ord j derived from le i j)
opaque symbol le_imp_subset (i j : τ ι) :
  π (le i j) → π (i ⊆ j) ≔
begin
  assume i j hle;
  have hOj : π (Ord j) { refine le_Ord2 i j hle };
  refine ∨ₑ (leE i j hle) _ _
  { assume hij;
    // i ∈ j and Ord(j) → i ⊆ j
    refine OrdmemD j i hij hOj }
  { assume heq;
    // i = j → i ⊆ j
    assume x hx;
    refine ind_eq (eq_sym heq) (λ w, x ∈ w) hx }
end;

// subset_imp_le: j ⊆ i → Ord(i) → Ord(j) → le(j, i)
opaque symbol subset_imp_le (i j : τ ι) :
  π (j ⊆ i) → π (Ord i) → π (Ord j) → π (le j i) ≔
begin
  assume i j hjsub hOi hOj;
  // ¬(i ∈ j), because i ∈ j → i ∈ i (via hjsub) → ⊥
  have hnij : π (¬ (lt i j)) {
    assume hij;
    have hii : π (i ∈ i) { refine hjsub i (ltD i j hij) };
    refine mem_irrefl i hii };
  refine not_lt_imp_le i j hOi hOj hnij
end;

// ===========================================================================
// Phase 2f: Memrel
// ===========================================================================

// Memrel(A) = {z ∈ A×A | ∃x y. z = ⟨x,y⟩ ∧ x ∈ y}
symbol Memrel (A : τ ι) : τ ι ≔
  Collect (Sigma A (λ _, A)) (λ z, fst z ∈ snd z);

// MemrelI: a ∈ b → a ∈ A → b ∈ A → Pair(a,b) ∈ Memrel(A)
opaque symbol MemrelI (a b A : τ ι) :
  π (a ∈ b) → π (a ∈ A) → π (b ∈ A) → π (Pair a b ∈ Memrel A) ≔
begin
  assume a b A hab haA hbA;
  refine CollectI (Pair a b) (Sigma A (λ _, A)) (λ z, fst z ∈ snd z) _ _
  { // Pair(a,b) ∈ Sigma(A, λ _. A) = A × A
    refine SigmaI a b A (λ _, A) haA hbA }
  { // fst(Pair(a,b)) ∈ snd(Pair(a,b)), i.e., a ∈ b
    have hfst : π (fst (Pair a b) = a) { refine fst_conv a b };
    have hsnd : π (snd (Pair a b) = b) { refine snd_conv a b };
    refine ind_eq hfst (λ w, w ∈ snd (Pair a b)) _;
    refine ind_eq hsnd (λ w, a ∈ w) _;
    apply hab }
end;

// MemrelE: Pair(a,b) ∈ Memrel(A) → a ∈ A ∧ b ∈ A ∧ a ∈ b
opaque symbol MemrelE (a b A : τ ι) :
  π (Pair a b ∈ Memrel A) →
  π (a ∈ A ∧ b ∈ A ∧ a ∈ b) ≔
begin
  assume a b A hm;
  have h1 : π (Pair a b ∈ Sigma A (λ _, A))
    { refine CollectD1 (Pair a b) (Sigma A (λ _, A)) (λ z, fst z ∈ snd z) hm };
  have h2 : π (fst (Pair a b) ∈ snd (Pair a b))
    { refine CollectD2 (Pair a b) (Sigma A (λ _, A)) (λ z, fst z ∈ snd z) hm };
  // From h1: Pair(a,b) ∈ A × A, extract a ∈ A and b ∈ A
  have hbex : π (Bex A (λ x, Bex A (λ y, Pair a b = Pair x y)))
    { refine SigmaE (Pair a b) A (λ _, A) h1 };
  have hfst : π (fst (Pair a b) = a) { refine fst_conv a b };
  have hsnd : π (snd (Pair a b) = b) { refine snd_conv a b };
  // fst(Pair(a,b)) ∈ snd(Pair(a,b)) means a ∈ b
  have hab : π (a ∈ b) {
    have h3 : π (a ∈ snd (Pair a b))
      { refine ind_eq (eq_sym hfst) (λ w, w ∈ snd (Pair a b)) h2 };
    refine ind_eq (eq_sym hsnd) (λ w, a ∈ w) h3
  };
  // Extract a ∈ A and b ∈ A from SigmaE
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hbex2 : π (Bex A (λ y, Pair a b = Pair x y)) { refine ∧ₑ₂ hx };
  refine ∃ₑ hbex2 _;
  assume y hy;
  have hyA : π (y ∈ A) { refine ∧ₑ₁ hy };
  have hpeq : π (Pair a b = Pair x y) { refine ∧ₑ₂ hy };
  have hax : π (a = x) { refine Pair_inject1 a b x y hpeq };
  have hby : π (b = y) { refine Pair_inject2 a b x y hpeq };
  have haA : π (a ∈ A) { refine ind_eq hax (λ w, w ∈ A) hxA };
  have hbA : π (b ∈ A) { refine ind_eq hby (λ w, w ∈ A) hyA };
  refine ∧ᵢ haA (∧ᵢ hbA hab)
end;

// Memrel_type: Memrel(A) ⊆ A × A
opaque symbol Memrel_type (A : τ ι) :
  π (Memrel A ⊆ Sigma A (λ _, A)) ≔
begin
  assume A;
  assume z hz;
  refine CollectD1 z (Sigma A (λ _, A)) (λ w, fst w ∈ snd w) hz
end;

// wf_Memrel: the membership relation Memrel(A) is well-founded (globally).
// This is just the foundation axiom: a nonempty set Z has an ∈-minimal
// element x; that same x is Memrel(A)-minimal, since Pair y x ∈ Memrel A
// entails y ∈ x.
opaque symbol wf_Memrel (A : τ ι) : π (wf_global (Memrel A)) ≔
begin
  assume A Z;
  have hf : π (Z = empty ∨ Bex Z (λ x, Ball x (λ y, y ∉ Z)))
    { refine foundation Z };
  refine ∨ₑ hf _ _
  { assume heq; refine ∨ᵢ₁ heq }
  { assume hbex;
    refine ∨ᵢ₂ _;
    refine ∃ₑ hbex _;
    assume x hx;
    have hxZ : π (x ∈ Z) { refine ∧ₑ₁ hx };
    have hmin : π (Ball x (λ y, y ∉ Z)) { refine ∧ₑ₂ hx };
    refine ∃ᵢ x (∧ᵢ hxZ _);
    assume y hyx;
    have hmem : π (y ∈ A ∧ x ∈ A ∧ y ∈ x) { refine MemrelE y x A hyx };
    refine hmin y (∧ₑ₂ (∧ₑ₂ hmem)) }
end;

// ===========================================================================
// Phase 2g: Limit lemmas
// ===========================================================================

// Limit_is_Ord: Limit(i) → Ord(i)
opaque symbol Limit_is_Ord (i : τ ι) :
  π (Limit i) → π (Ord i) ≔
begin
  assume i hL;
  refine ∧ₑ₁ hL
end;

// Limit_has_0: Limit(i) → 0 ∈ i (i.e., lt(0, i))
opaque symbol Limit_has_0 (i : τ ι) :
  π (Limit i) → π (lt empty i) ≔
begin
  assume i hL;
  have hOi : π (Ord i) { refine ∧ₑ₁ hL };
  have hne : π (i ≠ empty) { refine ∧ₑ₁ (∧ₑ₂ hL) };
  refine Ord_0_lt i hOi hne
end;

// Limit_nonzero: Limit(i) → i ≠ 0
opaque symbol Limit_nonzero (i : τ ι) :
  π (Limit i) → π (i ≠ empty) ≔
begin
  assume i hL;
  have h0i : π (empty ∈ i) { refine ltD empty i (Limit_has_0 i hL) };
  assume heq;
  have h0_in_0 : π (empty ∈ empty) { refine ind_eq (eq_sym heq) (λ w, empty ∈ w) h0i };
  refine emptyE empty h0_in_0
end;

// Limit_has_succ: Limit(i) → j ∈ i → succ(j) ∈ i
opaque symbol Limit_has_succ (i j : τ ι) :
  π (Limit i) → π (j ∈ i) → π (succ j ∈ i) ≔
begin
  assume i j hL hji;
  have hsucc_closed : π (`∀ (y : τ ι), y ∈ i ⇒ succ y ∈ i) { refine ∧ₑ₂ (∧ₑ₂ hL) };
  refine hsucc_closed j hji
end;

// Limit_Union_eq: Limit(i) → ⋃i = i
opaque symbol Limit_Union_eq (i : τ ι) :
  π (Limit i) → π (Union i = i) ≔
begin
  assume i hL;
  have hOi : π (Ord i) { refine Limit_is_Ord i hL };
  refine subset_antisym (Union i) i _ _
  { // ⋃i ⊆ i: from Transset(i) via Transset_iff_Union_subset_fwd
    refine Transset_iff_Union_subset_fwd i (Ord_is_Transset i hOi) }
  { // i ⊆ ⋃i: for x ∈ i, succ(x) ∈ i (Limit), and x ∈ succ(x), so x ∈ ⋃i
    assume x hxi;
    have hsx : π (succ x ∈ i) { refine Limit_has_succ i x hL hxi };
    have hx_in_sx : π (x ∈ succ x) { refine succI1 x };
    refine UnionI x (succ x) i hx_in_sx hsx }
end;

// Ord_cases: Ord(i) → (i = 0 → P) → (∃j. Ord(j) ∧ i = succ(j) → P) → (Limit(i) → P) → P
opaque symbol Ord_cases (i : τ ι) (P : Prop) :
  π (Ord i) →
  (π (i = empty) → π P) →
  (π (Bex i (λ j, Ord j ∧ i = succ j)) → π P) →
  (π (Limit i) → π P) →
  π P ≔
begin
  assume i P hOi hcase0 hcaseS hcaseL;
  // Case split: i = 0 or i ≠ 0
  have hem : π (i = empty ∨ ¬ (i = empty)) { refine em (i = empty) };
  refine ∨ₑ hem _ _
  { assume h; refine hcase0 h }
  { assume hne;
    // i ≠ 0. Is i a successor or a limit?
    // By excluded middle: ∃j ∈ i. i = succ(j), or not
    have hem2 : π (Bex i (λ j, Ord j ∧ i = succ j) ∨ ¬ (Bex i (λ j, Ord j ∧ i = succ j)))
      { refine em (Bex i (λ j, Ord j ∧ i = succ j)) };
    refine ∨ₑ hem2 _ _
    { assume h; refine hcaseS h }
    { assume hnsucc;
      // Not a successor → Limit
      refine hcaseL _;
      // Need: Ord(i) ∧ i ≠ 0 ∧ ∀y ∈ i. succ(y) ∈ i
      refine ∧ᵢ hOi (∧ᵢ hne _);
      assume y hyi;
      // y ∈ i, Ord(i) → Ord(y)
      have hOy : π (Ord y) { refine Ord_in_Ord i y hOi hyi };
      // succ(y) ≤ i: succ(y) ∈ i ∨ succ(y) = i
      have hle : π (le (succ y) i) { refine succ_leI y i hOi hyi };
      refine ∨ₑ (leE (succ y) i hle) _ _
      { assume h; apply h }
      { assume heq;
        // succ(y) = i → i is a successor of y, contradiction
        refine ⊥ₑ _;
        refine hnsucc _;
        refine ∃ᵢ y (∧ᵢ hyi (∧ᵢ hOy (eq_sym heq))) } } }
end;

// ===========================================================================
// Phase 3: Additional theorems from Ordinal.thy
// ===========================================================================

// Transset_doubleton_D: Transset(C) → {a,b} ∈ C → a ∈ C ∧ b ∈ C
opaque symbol Transset_doubleton_D (C a b : τ ι) :
  π (Transset C) → π (Upair a b ∈ C) → π (a ∈ C ∧ b ∈ C) ≔
begin
  assume C a b hTC hU;
  // Transset(C) means ∀x∈C. x ⊆ C
  // Upair(a,b) ∈ C, so Upair(a,b) ⊆ C
  have hUsub : π (Upair a b ⊆ C) { refine hTC (Upair a b) hU };
  apply ∧ᵢ
  { refine hUsub a (UpairI1 a b) }
  { refine hUsub b (UpairI2 a b) }
end;

// Transset_Pair_D: Transset(C) → ⟨a,b⟩ ∈ C → a ∈ C ∧ b ∈ C
// Pair a b = {{a},{a,b}} (concrete Kuratowski), so apply Transset_doubleton_D
// twice: ⟨a,b⟩∈C gives {a,b}∈C, which gives a∈C ∧ b∈C.
opaque symbol Transset_Pair_D (C a b : τ ι) :
  π (Transset C) → π (Pair a b ∈ C) → π (a ∈ C ∧ b ∈ C) ≔
begin
  assume C a b hTC hP;
  have h1 : π (singleton a ∈ C ∧ Upair a b ∈ C)
    { refine Transset_doubleton_D C (singleton a) (Upair a b) hTC hP };
  refine Transset_doubleton_D C a b hTC (∧ₑ₂ h1)
end;

// Transset_Pow: Transset(i) → Transset(Pow(i))
opaque symbol Transset_Pow (i : τ ι) :
  π (Transset i) → π (Transset (Pow i)) ≔
begin
  assume i hTi;
  // Transset(Pow(i)): ∀x ∈ Pow(i). x ⊆ Pow(i)
  assume x hxP;
  // x ∈ Pow(i) means x ⊆ i
  have hxi : π (x ⊆ i) { refine PowD x i hxP };
  // Need: x ⊆ Pow(i), i.e., ∀z ∈ x. z ∈ Pow(i)
  assume z hzx;
  // z ∈ x ⊆ i, so z ∈ i. Transset(i) gives z ⊆ i. So z ∈ Pow(i).
  have hzi : π (z ∈ i) { refine hxi z hzx };
  have hzsub : π (z ⊆ i) { refine hTi z hzi };
  refine PowI z i hzsub
end;

// Transset_Union: Transset(A) → Transset(⋃A)
opaque symbol Transset_Union (A : τ ι) :
  π (Transset A) → π (Transset (Union A)) ≔
begin
  assume A hTA;
  // ∀x ∈ A, since A is transitive and x ∈ A, x ⊆ A, so x is a set of subsets
  // Actually: Transset_Union_family with the fact that members of A are subsets of A
  // But that's wrong — we need each member of A to be transitive, not A itself.
  // Transset(A) means ∀x∈A. x ⊆ A.
  // Transset(⋃A): ∀y ∈ ⋃A. y ⊆ ⋃A.
  // y ∈ ⋃A means ∃B∈A. y∈B. Then for z ∈ y, need z ∈ ⋃A.
  // z ∈ y, y ∈ B, B ∈ A, and B ⊆ A (from Transset(A)). So y ∈ A.
  // Then z ∈ y and y ∈ A, so z ∈ ⋃A.
  assume y hyU;
  have hbex : π (Bex A (λ B, y ∈ B)) { refine UnionE y A hyU };
  assume z hzy;
  refine ∃ₑ hbex _;
  assume B hB;
  have hBA : π (B ∈ A) { refine ∧ₑ₁ hB };
  have hyB : π (y ∈ B) { refine ∧ₑ₂ hB };
  // B ∈ A and Transset(A) → B ⊆ A → y ∈ A
  have hBsub : π (B ⊆ A) { refine hTA B hBA };
  have hyA : π (y ∈ A) { refine hBsub y hyB };
  // z ∈ y and y ∈ A → z ∈ ⋃A
  refine UnionI z y A hzy hyA
end;

// Transset_Inter_family: (∀i∈A. Transset(i)) → Transset(⋂A)
opaque symbol Transset_Inter_family (A : τ ι) :
  π (Ball A (λ x, Transset x)) → π (Transset (Inter A)) ≔
begin
  assume A hAll;
  // Inter(A) = {x ∈ ⋃A | ∀B∈A. x∈B}
  assume x hxI;
  // x ∈ Inter(A) = Collect(Union A)(λ x, Ball A (λ y, x ∈ y))
  have hball : π (Ball A (λ y, x ∈ y))
    { refine CollectD2 x (Union A) (λ w, Ball A (λ y, w ∈ y)) hxI };
  assume z hzx;
  // Need: z ∈ Inter(A), i.e., z ∈ Union(A) ∧ ∀B∈A. z∈B
  refine CollectI z (Union A) (λ w, Ball A (λ y, w ∈ y)) _ _
  { // z ∈ Union(A): take any B ∈ A. x ∈ B, Transset(B) → x ⊆ B → z ∈ B. B ∈ A → z ∈ ⋃A.
    have hxU : π (x ∈ Union A)
      { refine CollectD1 x (Union A) (λ w, Ball A (λ y, w ∈ y)) hxI };
    have hbex : π (Bex A (λ B, x ∈ B)) { refine UnionE x A hxU };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBA : π (B ∈ A) { refine ∧ₑ₁ hB };
    have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
    have hTB : π (Transset B) { refine hAll B hBA };
    have hxsubB : π (x ⊆ B) { refine hTB x hxB };
    have hzB : π (z ∈ B) { refine hxsubB z hzx };
    refine UnionI z B A hzB hBA }
  { // ∀B∈A. z∈B
    assume B hBA;
    have hxB : π (x ∈ B) { refine hball B hBA };
    have hTB : π (Transset B) { refine hAll B hBA };
    have hxsubB : π (x ⊆ B) { refine hTB x hxB };
    refine hxsubB z hzx }
end;

// Ord_subset_Ord: Ord(i) → Transset(j) → j ⊆ i → Ord(j)
opaque symbol Ord_subset_Ord (i j : τ ι) :
  π (Ord i) → π (Transset j) → π (j ⊆ i) → π (Ord j) ≔
begin
  assume i j hOi hTj hjsub;
  have hBi : π (Ball i (λ x, Transset x)) { refine ∧ₑ₂ hOi };
  apply ∧ᵢ hTj _;
  assume x hxj;
  have hxi : π (x ∈ i) { refine hjsub x hxj };
  refine hBi x hxi
end;

// Ord_succ_iff: Ord(succ(i)) ↔ Ord(i)
// Forward: Ord(succ(i)) → Ord(i) (i ∈ succ(i), so Ord_in_Ord)
opaque symbol Ord_succD2 (i : τ ι) :
  π (Ord (succ i)) → π (Ord i) ≔
begin
  assume i hOsi;
  refine Ord_in_Ord (succ i) i hOsi (succI1 i)
end;

// lt_not_refl: ¬ lt(i,i)
opaque symbol lt_not_refl (i : τ ι) : π (¬ (lt i i)) ≔
begin
  assume i hii;
  refine mem_irrefl i (ltD i i hii)
end;

// Ord_Un: Ord(i) → Ord(j) → Ord(i ∪ j)
opaque symbol Ord_Un (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (Un i j)) ≔
begin
  assume i j hOi hOj;
  have hTi : π (Transset i) { refine ∧ₑ₁ hOi };
  have hTj : π (Transset j) { refine ∧ₑ₁ hOj };
  have hBi : π (Ball i (λ x, Transset x)) { refine ∧ₑ₂ hOi };
  have hBj : π (Ball j (λ x, Transset x)) { refine ∧ₑ₂ hOj };
  apply ∧ᵢ
  { refine Transset_Un i j hTi hTj }
  { assume x hxU;
    have hdisj : π (x ∈ i ∨ x ∈ j) { refine ∧ₑ₁ (Un_iff x i j) hxU };
    refine ∨ₑ hdisj _ _
    { assume hxi; refine hBi x hxi }
    { assume hxj; refine hBj x hxj } }
end;

// Ord_Int: Ord(i) → Ord(j) → Ord(i ∩ j)
opaque symbol Ord_Int (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (Int i j)) ≔
begin
  assume i j hOi hOj;
  have hTi : π (Transset i) { refine ∧ₑ₁ hOi };
  have hTj : π (Transset j) { refine ∧ₑ₁ hOj };
  have hBi : π (Ball i (λ x, Transset x)) { refine ∧ₑ₂ hOi };
  apply ∧ᵢ
  { refine Transset_Int i j hTi hTj }
  { assume x hxI;
    have hxi : π (x ∈ i) { refine IntD1 x i j hxI };
    refine hBi x hxi }
end;

// lt_trans1: le(i,j) → lt(j,k) → lt(i,k)   (Ord k derived from lt j k)
opaque symbol lt_trans1 (i j k : τ ι) :
  π (le i j) → π (lt j k) → π (lt i k) ≔
begin
  assume i j k hij hjk;
  have hOk : π (Ord k) { refine ∧ₑ₂ hjk };
  refine ∨ₑ (leE i j hij) _ _
  { assume h; refine ltI i k (Ord_trans i j k h (ltD j k hjk) hOk) hOk }
  { assume heq;
    rewrite heq; apply hjk }
end;

// lt_trans2: lt(i,j) → le(j,k) → lt(i,k)   (Ord k derived from le j k)
opaque symbol lt_trans2 (i j k : τ ι) :
  π (lt i j) → π (le j k) → π (lt i k) ≔
begin
  assume i j k hij hjk;
  have hOk : π (Ord k) { refine le_Ord2 j k hjk };
  refine ∨ₑ (leE j k hjk) _ _
  { assume h; refine lt_trans i j k hij (ltI j k h hOk) }
  { assume heq;
    refine ind_eq (eq_sym heq) (λ w, lt i w) hij }
end;

// le_trans: le(i,j) → le(j,k) → le(i,k)   (Ord k derived from le j k)
opaque symbol le_trans (i j k : τ ι) :
  π (le i j) → π (le j k) → π (le i k) ≔
begin
  assume i j k hij hjk;
  have hOk : π (Ord k) { refine le_Ord2 j k hjk };
  refine ∨ₑ (leE i j hij) _ _
  { assume h;
    refine ∨ₑ (leE j k hjk) _ _
    { assume h2; refine leI i k (Ord_trans i j k h h2 hOk) hOk }
    { assume heq; refine leI i k (ind_eq (eq_sym heq) (λ w, i ∈ w) h) hOk } }
  { assume heq;
    refine ∨ₑ (leE j k hjk) _ _
    { assume h2; refine leI i k (ind_eq heq (λ w, w ∈ k) h2) hOk }
    { assume heq2;
      have h : π (i = k) { rewrite heq; apply heq2 };
      refine le_eqI i k h hOk } }
end;

// succ_leE: le(succ(i), j) → lt(i, j)
// le(succ(i), j) = succ(i) ∈ j ∨ succ(i) = j
opaque symbol succ_leE (i j : τ ι) :
  π (le (succ i) j) → π (lt i j) ≔
begin
  assume i j hle;
  have hOj : π (Ord j) { refine le_Ord2 (succ i) j hle };
  refine ∨ₑ (leE (succ i) j hle) _ _
  { assume h;
    // succ(i) ∈ j and Ord(j), so succ(i) ⊆ j, so i ∈ j (since i ∈ succ(i))
    have hsub : π (succ i ⊆ j) { refine OrdmemD j (succ i) h hOj };
    refine ltI i j (hsub i (succI1 i)) hOj }
  { assume heq;
    // succ(i) = j, so i ∈ succ(i) = j
    refine ltI i j (ind_eq (eq_sym heq) (λ w, i ∈ w) (succI1 i)) hOj }
end;

// Ord_0_lt_iff: Ord(i) → (i ≠ 0 ↔ lt(0, i))
// Forward already proved as Ord_0_lt. Backward:
opaque symbol Ord_0_lt_iff_bwd (i : τ ι) :
  π (lt empty i) → π (i ≠ empty) ≔
begin
  assume i h0i heq;
  have h0i2 : π (empty ∈ i) { refine ltD empty i h0i };
  have hsym : π (empty = i) { refine eq_sym heq };
  have h : π (empty ∈ empty) { refine ind_eq hsym (λ w, empty ∈ w) h0i2 };
  refine emptyE empty h
end;

// all_lt_imp_le: If every x < j satisfies x < i, then j ≤ i (because j ⊆ i)
opaque symbol all_lt_imp_le (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (Ball j (λ x, x ∈ i)) →
  π (le j i) ≔
begin
  assume i j hOi hOj hall;
  // j ⊆ i
  have hsub : π (j ⊆ i) { assume x hxj; refine hall x hxj };
  refine subset_imp_le i j hsub hOi hOj
end;

// lt_imp_0_lt: lt(j, i) → lt(0, i)   (Ord i derived from lt j i)
opaque symbol lt_imp_0_lt (i j : τ ι) :
  π (lt j i) → π (lt empty i) ≔
begin
  assume i j hji;
  have hOi : π (Ord i) { refine ∧ₑ₂ hji };
  have hle : π (le empty j) {
    have hOj : π (Ord j) { refine Ord_in_Ord i j hOi (ltD j i hji) };
    refine Ord_0_le j hOj };
  refine lt_trans1 empty j i hle hji
end;

// Ord_Union_succ_eq: Ord(i) → ⋃(succ(i)) = i
opaque symbol Ord_Union_succ_eq (i : τ ι) :
  π (Ord i) → π (Union (succ i) = i) ≔
begin
  assume i hOi;
  refine subset_antisym (Union (succ i)) i _ _
  { // ⋃(succ(i)) ⊆ i
    assume x hxU;
    have hbex : π (Bex (succ i) (λ B, x ∈ B)) { refine UnionE x (succ i) hxU };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBsi : π (B ∈ succ i) { refine ∧ₑ₁ hB };
    have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
    // B ∈ succ(i) means B = i ∨ B ∈ i
    have hdisj : π (B = i ∨ B ∈ i) { refine ∧ₑ₁ (succ_iff B i) hBsi };
    refine ∨ₑ hdisj _ _
    { assume heq; rewrite left heq; apply hxB }
    { assume hBi;
      // B ∈ i and Ord(i) → B ⊆ i
      have hBsub : π (B ⊆ i) { refine OrdmemD i B hBi hOi };
      refine hBsub x hxB } }
  { // i ⊆ ⋃(succ(i))
    assume x hxi;
    // x ∈ i and i ∈ succ(i), so x ∈ ⋃(succ(i))
    refine UnionI x i (succ i) hxi (succI1 i) }
end;

// Ord_Union_subset: Ord(i) → ⋃i ⊆ i
opaque symbol Ord_Union_subset (i : τ ι) :
  π (Ord i) → π (Union i ⊆ i) ≔
begin
  assume i hOi;
  refine Transset_iff_Union_subset_fwd i (Ord_is_Transset i hOi)
end;

// Ord_equality: Ord(i) → ⋃{succ(y) | y ∈ i} = i
// In Isabelle: (⋃y∈i. succ(y)) = i
// ⋃{succ(y) | y ∈ i} = Union(RepFun(i, succ))
opaque symbol Ord_equality (i : τ ι) :
  π (Ord i) → π (Union (RepFun i (λ y, succ y)) = i) ≔
begin
  assume i hOi;
  refine subset_antisym (Union (RepFun i (λ y, succ y))) i _ _
  { // (⋃y∈i. succ(y)) ⊆ i
    assume x hxU;
    have hbex : π (Bex (RepFun i (λ y, succ y)) (λ B, x ∈ B))
      { refine UnionE x (RepFun i (λ y, succ y)) hxU };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBR : π (B ∈ RepFun i (λ y, succ y)) { refine ∧ₑ₁ hB };
    have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
    // B ∈ RepFun(i, succ) means ∃a∈i. B = succ(a)
    have hbex2 : π (Bex i (λ a, B = succ a))
      { refine ∧ₑ₁ (RepFun_iff B i (λ y, succ y)) hBR };
    refine ∃ₑ hbex2 _;
    assume a ha;
    have haI : π (a ∈ i) { refine ∧ₑ₁ ha };
    have hBeq : π (B = succ a) { refine ∧ₑ₂ ha };
    // x ∈ B = succ(a), so x = a ∨ x ∈ a
    have hxsa : π (x ∈ succ a) { rewrite left hBeq; apply hxB };
    have hdisj : π (x = a ∨ x ∈ a) { refine ∧ₑ₁ (succ_iff x a) hxsa };
    refine ∨ₑ hdisj _ _
    { assume heq; rewrite heq; apply haI }
    { assume hxa;
      // x ∈ a, a ∈ i, Ord(i) → x ∈ i
      refine Ord_trans x a i hxa haI hOi } }
  { // i ⊆ (⋃y∈i. succ(y))
    assume x hxi;
    // x ∈ i, succ(x) ∈ RepFun(i, succ), x ∈ succ(x)
    have hsx : π (succ x ∈ RepFun i (λ y, succ y))
      { refine RepFunI x i (λ y, succ y) hxi };
    refine UnionI x (succ x) (RepFun i (λ y, succ y)) (succI1 x) hsx }
end;

// Memrel_mono: A ⊆ B → Memrel(A) ⊆ Memrel(B)
opaque symbol Memrel_mono (A B : τ ι) :
  π (A ⊆ B) → π (Memrel A ⊆ Memrel B) ≔
begin
  assume A B hAB;
  assume z hz;
  // z ∈ Memrel(A) = Collect(A×A, λ z, fst z ∈ snd z)
  have h1 : π (z ∈ Sigma A (λ _, A))
    { refine CollectD1 z (Sigma A (λ _, A)) (λ w, fst w ∈ snd w) hz };
  have h2 : π (fst z ∈ snd z)
    { refine CollectD2 z (Sigma A (λ _, A)) (λ w, fst w ∈ snd w) hz };
  // z ∈ A×A, need z ∈ B×B
  // Extract components from SigmaE
  have hbex : π (Bex A (λ x, Bex A (λ y, z = Pair x y)))
    { refine SigmaE z A (λ _, A) h1 };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hbex2 : π (Bex A (λ y, z = Pair x y)) { refine ∧ₑ₂ hx };
  refine ∃ₑ hbex2 _;
  assume y hy;
  have hyA : π (y ∈ A) { refine ∧ₑ₁ hy };
  have hzeq : π (z = Pair x y) { refine ∧ₑ₂ hy };
  have hxB : π (x ∈ B) { refine hAB x hxA };
  have hyB : π (y ∈ B) { refine hAB y hyA };
  // z = Pair(x,y), fst(z) ∈ snd(z), i.e., x ∈ y
  have hfst : π (fst (Pair x y) = x) { refine fst_conv x y };
  have hsnd : π (snd (Pair x y) = y) { refine snd_conv x y };
  have hxy : π (x ∈ y) {
    have h3 : π (fst z ∈ snd z) { apply h2 };
    have h4 : π (fst (Pair x y) ∈ snd (Pair x y))
      { rewrite left hzeq; apply h3 };
    have h5 : π (x ∈ snd (Pair x y))
      { refine ind_eq (eq_sym hfst) (λ w, w ∈ snd (Pair x y)) h4 };
    refine ind_eq (eq_sym hsnd) (λ w, x ∈ w) h5 };
  // Now Pair(x,y) ∈ Memrel(B)
  have hm : π (Pair x y ∈ Memrel B)
    { refine MemrelI x y B hxy hxB hyB };
  rewrite hzeq; apply hm
end;

// zero_not_Limit: ¬ Limit(0)
opaque symbol zero_not_Limit : π (¬ (Limit empty)) ≔
begin
  assume hL;
  have h0 : π (empty ∈ empty) { refine ltD empty empty (Limit_has_0 empty hL) };
  refine emptyE empty h0
end;

// Limit_has_1: Limit(i) → lt(succ(empty), i)
opaque symbol Limit_has_1 (i : τ ι) :
  π (Limit i) → π (lt (succ empty) i) ≔
begin
  assume i hL;
  have hOi : π (Ord i) { refine Limit_is_Ord i hL };
  have h0 : π (empty ∈ i) { refine ltD empty i (Limit_has_0 i hL) };
  refine ltI (succ empty) i (Limit_has_succ i empty hL h0) hOi
end;

// succ_LimitE: Limit(succ(i)) → ⊥ (succ is never a limit)
opaque symbol succ_LimitE (i : τ ι) :
  π (Limit (succ i)) → π ⊥ ≔
begin
  assume i hL;
  // Limit(succ(i)): succ(i) ∈ succ(i) eventually (since i ∈ succ(i), succ(i) ∈ succ(i) by Limit_has_succ)
  // Actually: i < succ(i) (= i ∈ succ(i)), so succ(i) < succ(i) by Limit_has_succ
  have hOsi : π (Ord (succ i)) { refine Limit_is_Ord (succ i) hL };
  have hOi : π (Ord i) { refine Ord_succD2 i hOsi };
  have hi_in_si : π (i ∈ succ i) { refine succI1 i };
  have hsi_in_si : π (succ i ∈ succ i) { refine Limit_has_succ (succ i) i hL hi_in_si };
  refine mem_irrefl (succ i) hsi_in_si
end;

// not_succ_Limit: ¬ Limit(succ(i))
opaque symbol not_succ_Limit (i : τ ι) :
  π (¬ (Limit (succ i))) ≔
begin
  assume i hL;
  refine succ_LimitE i hL
end;

// Limit_le_succD: Limit(i) → le(i, succ(j)) → le(i, j)
opaque symbol Limit_le_succD (i j : τ ι) :
  π (Limit i) → π (le i (succ j)) → π (le i j) ≔
begin
  assume i j hL hle;
  have hOj : π (Ord j) { refine Ord_succD2 j (le_Ord2 i (succ j) hle) };
  refine ∨ₑ (leE i (succ j) hle) _ _
  { assume h;
    // i ∈ succ(j) means i = j ∨ i ∈ j
    have hdisj : π (i = j ∨ i ∈ j) { refine ∧ₑ₁ (succ_iff i j) h };
    refine ∨ₑ hdisj _ _
    { assume heq; refine le_eqI i j heq hOj }
    { assume hij; refine leI i j hij hOj } }
  { assume heq;
    // i = succ(j) → Limit(succ(j)) → ⊥
    // heq : π (i = succ j)
    have hLsj : π (Limit (succ j)) { refine ind_eq (eq_sym heq) (λ w, Limit w) hL };
    refine ⊥ₑ (succ_LimitE j hLsj) }
end;

// le0_iff: le(i, empty) ↔ i = empty
// Forward: le(i, 0) → i = 0
opaque symbol le0D (i : τ ι) :
  π (le i empty) → π (i = empty) ≔
begin
  assume i hle;
  refine ∨ₑ (leE i empty hle) _ _
  { assume h; refine ⊥ₑ (emptyE i h) }
  { assume heq; apply heq }
end;

// Backward: i = 0 → le(i, 0)
opaque symbol le0I (i : τ ι) :
  π (i = empty) → π (le i empty) ≔
begin
  assume i heq;
  refine le_eqI i empty heq Ord_0
end;

// Un_upper1_le: Ord(i) → Ord(j) → le(i, i ∪ j)
opaque symbol Un_upper1_le (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (le i (Un i j)) ≔
begin
  assume i j hOi hOj;
  have hOij : π (Ord (Un i j)) { refine Ord_Un i j hOi hOj };
  refine subset_imp_le (Un i j) i (Un_upper1 i j) hOij hOi
end;

// Un_upper2_le: Ord(i) → Ord(j) → le(j, i ∪ j)
opaque symbol Un_upper2_le (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (le j (Un i j)) ≔
begin
  assume i j hOi hOj;
  have hOij : π (Ord (Un i j)) { refine Ord_Un i j hOi hOj };
  refine subset_imp_le (Un i j) j (Un_upper2 i j) hOij hOj
end;

// Transset_includes_domain: Transset(C) → A×B ⊆ C → b ∈ B → A ⊆ C
opaque symbol Transset_includes_domain (C A B : τ ι) (b : τ ι) :
  π (Transset C) → π (Sigma A (λ _, B) ⊆ C) → π (b ∈ B) → π (A ⊆ C) ≔
begin
  assume C A B b hTC hABC hbB;
  assume a haA;
  // Pair(a,b) ∈ A×B ⊆ C
  have hpAB : π (Pair a b ∈ Sigma A (λ _, B)) { refine SigmaI a b A (λ _, B) haA hbB };
  have hpC : π (Pair a b ∈ C) { refine hABC (Pair a b) hpAB };
  // Transset_Pair_D gives a ∈ C
  have hd : π (a ∈ C ∧ b ∈ C) { refine Transset_Pair_D C a b hTC hpC };
  refine ∧ₑ₁ hd
end;

// Transset_includes_range: Transset(C) → A×B ⊆ C → a ∈ A → B ⊆ C
opaque symbol Transset_includes_range (C A B : τ ι) (a : τ ι) :
  π (Transset C) → π (Sigma A (λ _, B) ⊆ C) → π (a ∈ A) → π (B ⊆ C) ≔
begin
  assume C A B a hTC hABC haA;
  assume b hbB;
  have hpAB : π (Pair a b ∈ Sigma A (λ _, B)) { refine SigmaI a b A (λ _, B) haA hbB };
  have hpC : π (Pair a b ∈ C) { refine hABC (Pair a b) hpAB };
  have hd : π (a ∈ C ∧ b ∈ C) { refine Transset_Pair_D C a b hTC hpC };
  refine ∧ₑ₂ hd
end;

// Transset_iff_Union_succ: Transset(A) ↔ ⋃(succ(A)) = A
// Forward: Transset(A) → ⋃(succ(A)) = A
opaque symbol Transset_iff_Union_succ_fwd (A : τ ι) :
  π (Transset A) → π (Union (succ A) = A) ≔
begin
  assume A hTA;
  refine subset_antisym (Union (succ A)) A _ _
  { // ⋃(succ(A)) ⊆ A
    assume x hxU;
    have hbex : π (Bex (succ A) (λ B, x ∈ B)) { refine UnionE x (succ A) hxU };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBsA : π (B ∈ succ A) { refine ∧ₑ₁ hB };
    have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
    have hdisj : π (B = A ∨ B ∈ A) { refine ∧ₑ₁ (succ_iff B A) hBsA };
    refine ∨ₑ hdisj _ _
    { assume heq;
      refine ind_eq (eq_sym heq) (λ w, x ∈ w) hxB }
    { assume hBA;
      have hBsub : π (B ⊆ A) { refine hTA B hBA };
      refine hBsub x hxB } }
  { // A ⊆ ⋃(succ(A))
    assume x hxA;
    // x ∈ A and A ∈ succ(A)
    refine UnionI x A (succ A) hxA (succI1 A) }
end;

// Backward: ⋃(succ(A)) = A → Transset(A)
opaque symbol Transset_iff_Union_succ_bwd (A : τ ι) :
  π (Union (succ A) = A) → π (Transset A) ≔
begin
  assume A heq;
  // Transset(A): ∀x∈A. x ⊆ A
  assume x hxA;
  assume z hzx;
  // z ∈ x, x ∈ A, so x ∈ succ(A) (by succI2). Also z ∈ x ∈ succ(A).
  // So z ∈ ⋃(succ(A)) = A.
  have hxsA : π (x ∈ succ A) { refine succI2 x A hxA };
  have hzU : π (z ∈ Union (succ A)) { refine UnionI z x (succ A) hzx hxsA };
  // ⋃(succ(A)) = A, so z ∈ A
  refine ind_eq (eq_sym heq) (λ w, z ∈ w) hzU
end;

// Transset_Memrel_iff: Transset(A) → Pair(a,b) ∈ Memrel(A) ↔ a ∈ b ∧ b ∈ A
opaque symbol Transset_Memrel_iff_fwd (A a b : τ ι) :
  π (Transset A) → π (Pair a b ∈ Memrel A) → π (a ∈ b ∧ b ∈ A) ≔
begin
  assume A a b hTA hm;
  have h : π (a ∈ A ∧ b ∈ A ∧ a ∈ b) { refine MemrelE a b A hm };
  have hab : π (a ∈ b) { refine ∧ₑ₂ (∧ₑ₂ h) };
  have hbA : π (b ∈ A) { refine ∧ₑ₁ (∧ₑ₂ h) };
  apply ∧ᵢ hab hbA
end;

opaque symbol Transset_Memrel_iff_bwd (A a b : τ ι) :
  π (Transset A) → π (a ∈ b) → π (b ∈ A) → π (Pair a b ∈ Memrel A) ≔
begin
  assume A a b hTA hab hbA;
  // a ∈ b ∈ A, Transset(A) → b ⊆ A → a ∈ A
  have hbsub : π (b ⊆ A) { refine hTA b hbA };
  have haA : π (a ∈ A) { refine hbsub a hab };
  refine MemrelI a b A hab haA hbA
end;

// trans_Memrel: Ord(i) → trans(Memrel(i))
opaque symbol trans_Memrel (i : τ ι) :
  π (Ord i) → π (trans (Memrel i)) ≔
begin
  assume i hOi a b c hab hbc;
  // Decompose Pair(a,b) ∈ Memrel(i): gives a ∈ i ∧ b ∈ i ∧ a ∈ b
  have heab : π (a ∈ i ∧ b ∈ i ∧ a ∈ b) { refine MemrelE a b i hab };
  have haai : π (a ∈ i) { refine ∧ₑ₁ heab };
  have habi : π (b ∈ i) { refine ∧ₑ₁ (∧ₑ₂ heab) };
  have habm : π (a ∈ b) { refine ∧ₑ₂ (∧ₑ₂ heab) };
  // Decompose Pair(b,c) ∈ Memrel(i): gives b ∈ i ∧ c ∈ i ∧ b ∈ c
  have hebc : π (b ∈ i ∧ c ∈ i ∧ b ∈ c) { refine MemrelE b c i hbc };
  have hci : π (c ∈ i) { refine ∧ₑ₁ (∧ₑ₂ hebc) };
  have hbcm : π (b ∈ c) { refine ∧ₑ₂ (∧ₑ₂ hebc) };
  // Ord(i) → c ∈ i → Transset(c)
  have hTc : π (Transset c) { refine Ord_contains_Transset i c hOi hci };
  // Transset(c) → b ∈ c → b ⊆ c → a ∈ b → a ∈ c
  have hbsc : π (b ⊆ c) { refine hTc b hbcm };
  have hac : π (a ∈ c) { refine hbsc a habm };
  // Build Pair(a,c) ∈ Memrel(i)
  refine MemrelI a c i hac haai hci
end;

// ===========================================================================
// trans_induct3: Three-way transfinite induction (0 / succ / limit)
// ===========================================================================

// trans_induct3: Ord(i) → P(0) → (∀x. Ord(x) → P(x) → P(succ(x)))
//   → (∀x. Limit(x) → Ball(x,P) → P(x)) → P(i)
opaque symbol trans_induct3 (i : τ ι) (P : τ ι → Prop) :
  π (Ord i) →
  π (P empty) →
  (Π (x : τ ι), π (Ord x) → π (P x) → π (P (succ x))) →
  (Π (x : τ ι), π (Limit x) → (Π (y : τ ι), π (y ∈ x) → π (P y)) → π (P x)) →
  π (P i) ≔
begin
  assume i P hOi hP0 hPsucc hPlim;
  // Use trans_induct: Ord(i) → (∀x. Ord(x) → Ball(x,P) → P(x)) → P(i)
  refine trans_induct i P hOi _;
  // Need: ∀x. Ord(x) → Ball(x,P) → P(x)
  assume x hOx hBall;
  // Case split on x using Ord_cases
  refine Ord_cases x (P x) hOx _ _ _
  { // Case x = 0
    assume heq;
    refine ind_eq heq (λ w, P w) hP0 }
  { // Case x = succ(j) for some j ∈ x with Ord(j)
    assume hbex;
    // hbex : Bex x (λ j, Ord j ∧ x = succ j)
    refine ∃ₑ hbex _;
    assume j hj;
    have hjx : π (j ∈ x) { refine ∧ₑ₁ hj };
    have hOj : π (Ord j) { refine ∧ₑ₁ (∧ₑ₂ hj) };
    have hxeq : π (x = succ j) { refine ∧ₑ₂ (∧ₑ₂ hj) };
    // P(j) from Ball(x, P) since j ∈ x
    have hPj : π (P j) { refine hBall j hjx };
    // P(succ(j)) from the successor case
    have hPsj : π (P (succ j)) { refine hPsucc j hOj hPj };
    // x = succ(j), so P(x) = P(succ(j))
    refine ind_eq hxeq (λ w, P w) hPsj }
  { // Case Limit(x)
    assume hLx;
    // Ball(x, P) gives us P(y) for all y ∈ x
    refine hPlim x hLx (λ y hy, hBall y hy) }
end;
