// equalities: Basic set algebra identities for ZF set theory
//
// Isabelle source: equalities.thy
// Proves: commutativity, associativity, absorption, identity, distributivity
//         for union and intersection; difference identities; subset relationships

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt;
require open ZF.ZF_Base ZF.upair;

// ===========================================================================
// Union identities
// ===========================================================================

// A ∪ B = B ∪ A
opaque symbol Un_commute (A B : τ ι) : π (Un A B = Un B A) ≔
begin
  assume A B;
  refine extension (Un A B) (Un B A) _;
  assume x;
  apply ∧ᵢ
  { assume h;
    have hdisj : π (x ∈ A ∨ x ∈ B) { refine UnE x A B h };
    refine ∨ₑ hdisj _ _
    { assume hA; refine UnI2 x B A hA }
    { assume hB; refine UnI1 x B A hB } }
  { assume h;
    have hdisj : π (x ∈ B ∨ x ∈ A) { refine UnE x B A h };
    refine ∨ₑ hdisj _ _
    { assume hB; refine UnI2 x A B hB }
    { assume hA; refine UnI1 x A B hA } }
end;

// (A ∪ B) ∪ C = A ∪ (B ∪ C)
opaque symbol Un_assoc (A B C : τ ι) : π (Un (Un A B) C = Un A (Un B C)) ≔
begin
  assume A B C;
  refine extension (Un (Un A B) C) (Un A (Un B C)) _;
  assume x;
  apply ∧ᵢ
  { assume h;
    have h1 : π (x ∈ Un A B ∨ x ∈ C) { refine UnE x (Un A B) C h };
    refine ∨ₑ h1 _ _
    { assume hAB;
      have h2 : π (x ∈ A ∨ x ∈ B) { refine UnE x A B hAB };
      refine ∨ₑ h2 _ _
      { assume hA; refine UnI1 x A (Un B C) hA }
      { assume hB; refine UnI2 x A (Un B C) (UnI1 x B C hB) } }
    { assume hC; refine UnI2 x A (Un B C) (UnI2 x B C hC) } }
  { assume h;
    have h1 : π (x ∈ A ∨ x ∈ Un B C) { refine UnE x A (Un B C) h };
    refine ∨ₑ h1 _ _
    { assume hA; refine UnI1 x (Un A B) C (UnI1 x A B hA) }
    { assume hBC;
      have h2 : π (x ∈ B ∨ x ∈ C) { refine UnE x B C hBC };
      refine ∨ₑ h2 _ _
      { assume hB; refine UnI1 x (Un A B) C (UnI2 x A B hB) }
      { assume hC; refine UnI2 x (Un A B) C hC } } }
end;

// A ∪ A = A
opaque symbol Un_absorb (A : τ ι) : π (Un A A = A) ≔
begin
  assume A;
  refine extension (Un A A) A _;
  assume x;
  apply ∧ᵢ
  { assume h;
    have hdisj : π (x ∈ A ∨ x ∈ A) { refine UnE x A A h };
    refine ∨ₑ hdisj _ _
    { assume hA; apply hA }
    { assume hA; apply hA } }
  { assume h; refine UnI1 x A A h }
end;

// empty ∪ A = A
opaque symbol Un_empty_left (A : τ ι) : π (Un empty A = A) ≔
begin
  assume A;
  refine extension (Un empty A) A _;
  assume x;
  apply ∧ᵢ
  { assume h;
    have hdisj : π (x ∈ empty ∨ x ∈ A) { refine UnE x empty A h };
    refine ∨ₑ hdisj _ _
    { assume he; refine ⊥ₑ (emptyE x he) }
    { assume hA; apply hA } }
  { assume h; refine UnI2 x empty A h }
end;

// A ∪ empty = A
opaque symbol Un_empty_right (A : τ ι) : π (Un A empty = A) ≔
begin
  assume A;
  refine extension (Un A empty) A _;
  assume x;
  apply ∧ᵢ
  { assume h;
    have hdisj : π (x ∈ A ∨ x ∈ empty) { refine UnE x A empty h };
    refine ∨ₑ hdisj _ _
    { assume hA; apply hA }
    { assume he; refine ⊥ₑ (emptyE x he) } }
  { assume h; refine UnI1 x A empty h }
end;

// ===========================================================================
// Intersection identities
// ===========================================================================

// A ∩ B = B ∩ A
opaque symbol Int_commute (A B : τ ι) : π (Int A B = Int B A) ≔
begin
  assume A B;
  refine extension (Int A B) (Int B A) _;
  assume x;
  apply ∧ᵢ
  { assume h;
    have hA : π (x ∈ A) { refine IntD1 x A B h };
    have hB : π (x ∈ B) { refine IntD2 x A B h };
    refine IntI x B A hB hA }
  { assume h;
    have hB : π (x ∈ B) { refine IntD1 x B A h };
    have hA : π (x ∈ A) { refine IntD2 x B A h };
    refine IntI x A B hA hB }
end;

// (A ∩ B) ∩ C = A ∩ (B ∩ C)
opaque symbol Int_assoc (A B C : τ ι) : π (Int (Int A B) C = Int A (Int B C)) ≔
begin
  assume A B C;
  refine extension (Int (Int A B) C) (Int A (Int B C)) _;
  assume x;
  apply ∧ᵢ
  { assume h;
    have hAB : π (x ∈ Int A B) { refine IntD1 x (Int A B) C h };
    have hC : π (x ∈ C) { refine IntD2 x (Int A B) C h };
    have hA : π (x ∈ A) { refine IntD1 x A B hAB };
    have hB : π (x ∈ B) { refine IntD2 x A B hAB };
    refine IntI x A (Int B C) hA (IntI x B C hB hC) }
  { assume h;
    have hA : π (x ∈ A) { refine IntD1 x A (Int B C) h };
    have hBC : π (x ∈ Int B C) { refine IntD2 x A (Int B C) h };
    have hB : π (x ∈ B) { refine IntD1 x B C hBC };
    have hC : π (x ∈ C) { refine IntD2 x B C hBC };
    refine IntI x (Int A B) C (IntI x A B hA hB) hC }
end;

// A ∩ A = A
opaque symbol Int_absorb (A : τ ι) : π (Int A A = A) ≔
begin
  assume A;
  refine extension (Int A A) A _;
  assume x;
  apply ∧ᵢ
  { assume h; refine IntD1 x A A h }
  { assume h; refine IntI x A A h h }
end;

// A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
opaque symbol Int_Un_distrib (A B C : τ ι) :
  π (Int A (Un B C) = Un (Int A B) (Int A C)) ≔
begin
  assume A B C;
  refine extension (Int A (Un B C)) (Un (Int A B) (Int A C)) _;
  assume x;
  apply ∧ᵢ
  { assume h;
    have hA : π (x ∈ A) { refine IntD1 x A (Un B C) h };
    have hBC : π (x ∈ Un B C) { refine IntD2 x A (Un B C) h };
    have hdisj : π (x ∈ B ∨ x ∈ C) { refine UnE x B C hBC };
    refine ∨ₑ hdisj _ _
    { assume hB; refine UnI1 x (Int A B) (Int A C) (IntI x A B hA hB) }
    { assume hC; refine UnI2 x (Int A B) (Int A C) (IntI x A C hA hC) } }
  { assume h;
    have hdisj : π (x ∈ Int A B ∨ x ∈ Int A C) { refine UnE x (Int A B) (Int A C) h };
    refine ∨ₑ hdisj _ _
    { assume hAB;
      have hA : π (x ∈ A) { refine IntD1 x A B hAB };
      have hB : π (x ∈ B) { refine IntD2 x A B hAB };
      refine IntI x A (Un B C) hA (UnI1 x B C hB) }
    { assume hAC;
      have hA : π (x ∈ A) { refine IntD1 x A C hAC };
      have hC : π (x ∈ C) { refine IntD2 x A C hAC };
      refine IntI x A (Un B C) hA (UnI2 x B C hC) } }
end;

// ===========================================================================
// Difference identities
// ===========================================================================

// A \ A = empty
opaque symbol Diff_cancel (A : τ ι) : π (Diff A A = empty) ≔
begin
  assume A;
  refine subset_antisym (Diff A A) empty _ (empty_subset (Diff A A));
  assume x hx;
  have hA : π (x ∈ A) { refine DiffD1 x A A hx };
  have hnA : π (x ∉ A) { refine DiffD2 x A A hx };
  refine ⊥ₑ (hnA hA)
end;

// A \ empty = A
opaque symbol Diff_empty (A : τ ι) : π (Diff A empty = A) ≔
begin
  assume A;
  refine extension (Diff A empty) A _;
  assume x;
  apply ∧ᵢ
  { assume h; refine DiffD1 x A empty h }
  { assume h; refine DiffI x A empty h (emptyE x) }
end;

// ===========================================================================
// Subset and union/intersection
// ===========================================================================

// A ⊆ A ∪ B
opaque symbol Un_upper1 (A B : τ ι) : π (A ⊆ Un A B) ≔
begin
  assume A B x hx;
  refine UnI1 x A B hx
end;

// B ⊆ A ∪ B
opaque symbol Un_upper2 (A B : τ ι) : π (B ⊆ Un A B) ≔
begin
  assume A B x hx;
  refine UnI2 x A B hx
end;

// A ∩ B ⊆ A
opaque symbol Int_lower1 (A B : τ ι) : π (Int A B ⊆ A) ≔
begin
  assume A B x hx;
  refine IntD1 x A B hx
end;

// A ∩ B ⊆ B
opaque symbol Int_lower2 (A B : τ ι) : π (Int A B ⊆ B) ≔
begin
  assume A B x hx;
  refine IntD2 x A B hx
end;

// A ⊆ C → B ⊆ C → A ∪ B ⊆ C
opaque symbol Un_least (A B C : τ ι) :
  π (A ⊆ C) → π (B ⊆ C) → π (Un A B ⊆ C) ≔
begin
  assume A B C hAC hBC x hx;
  have hdisj : π (x ∈ A ∨ x ∈ B) { refine UnE x A B hx };
  refine ∨ₑ hdisj _ _
  { assume hA; refine hAC x hA }
  { assume hB; refine hBC x hB }
end;

// C ⊆ A → C ⊆ B → C ⊆ A ∩ B
opaque symbol Int_greatest (A B C : τ ι) :
  π (C ⊆ A) → π (C ⊆ B) → π (C ⊆ Int A B) ≔
begin
  assume A B C hCA hCB x hx;
  refine IntI x A B (hCA x hx) (hCB x hx)
end;
