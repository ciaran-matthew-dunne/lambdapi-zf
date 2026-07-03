// Bool_ZF: Boolean values as ZF sets
//
// Isabelle source: Bool.thy
// ZF booleans: 1 = {0} = succ(0), bool = {0, 1}
// cond(b, c, d) = if b=1 then c else d

require open ZF.ZF_Base ZF.upair;

// ---------------------------------------------------------------------------
// ZF Boolean values (not to be confused with Stdlib 𝔹)
// ---------------------------------------------------------------------------

// 1 = succ(0) = {0}
symbol one : τ ι ≔ succ empty;

// bool = {0, 1}
symbol bool_set : τ ι ≔ Upair empty one;

// bool membership: x ∈ bool ⟷ x = 0 ∨ x = 1
opaque symbol bool_iff (x : τ ι) :
  π ((x ∈ bool_set) ⇔ (x = empty ∨ x = one)) ≔
begin
  assume x;
  apply Upair_iff x empty one
end;

// 0 ∈ bool
opaque symbol zero_in_bool : π (empty ∈ bool_set) ≔
begin
  refine UpairI1 empty one
end;

// 1 ∈ bool
opaque symbol one_in_bool : π (one ∈ bool_set) ≔
begin
  refine UpairI2 empty one
end;

// 0 ≠ 1
opaque symbol zero_ne_one : π (empty ≠ one) ≔
begin
  assume heq;
  // one = succ(empty) = cons(empty, empty) = Upair(empty,empty) ∪ empty
  // If empty = one, then empty ∈ one = empty, contradiction
  // one = succ(empty), so empty ∈ succ(empty) by succI1
  have h : π (empty ∈ one) { refine succI1 empty };
  // If empty = one, then empty ∈ empty
  have h2 : π (empty ∈ empty)
    { refine ind_eq heq (λ z, empty ∈ z) h };
  refine emptyE empty h2
end;

// ---------------------------------------------------------------------------
// Conditional: cond(b, c, d) = if b = 1 then c else d
// ---------------------------------------------------------------------------

// In Isabelle: cond(P, c, d) = if(P, c, d) where P is 1 or 0
// Here we define it for set-level booleans: b ∈ bool
symbol cond (b c d : τ ι) : τ ι ≔
  If (b = one) c d;

// cond(1, c, d) = c   (Isabelle: cond_1)
opaque symbol cond_1 (c d : τ ι) : π (cond one c d = c) ≔
begin
  assume c d;
  refine If_P (one = one) c d (eq_refl one)
end;

// cond(0, c, d) = d   (Isabelle: cond_0)
opaque symbol cond_0 (c d : τ ι) : π (cond empty c d = d) ≔
begin
  assume c d;
  refine If_not_P (empty = one) c d zero_ne_one
end;

// ---------------------------------------------------------------------------
// bool is not empty
// ---------------------------------------------------------------------------

opaque symbol bool_not_empty : π (bool_set ≠ empty) ≔
begin
  refine ne_empty bool_set empty zero_in_bool
end;
