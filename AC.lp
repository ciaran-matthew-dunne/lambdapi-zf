// AC: The Axiom of Choice
//
// Isabelle source: AC.thy (Paulson; the definition comes from Halmos 1960,
// p. 59). The axiom is the FUNCTIONAL form: every family of nonempty sets
// has a dependent choice function (an element of the Pi-set). The previously
// stated relational form (∃f. ∀x∈A. ∃y. y∈x ∧ ⟨x,y⟩∈f) was a ZF THEOREM
// (witness Sigma A (λx,x)) and carried no choice strength — replaced
// 2026-07-11 with the faithful statement.

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func;

// ===========================================================================
// The axiom
// ===========================================================================

// AC: ⟦a ∈ A; ⋀x. x ∈ A ⟹ ∃y. y ∈ B(x)⟧ ⟹ ∃z. z ∈ Pi(A,B)
constant symbol AC (a A : τ ι) (B : τ ι → τ ι) :
  π (a ∈ A) →
  (Π x : τ ι, π (x ∈ A) → π (`∃ (y : τ ι), y ∈ B x)) →
  π (`∃ (z : τ ι), z ∈ Pi A B);

// ===========================================================================
// Consequences (AC.thy)
// ===========================================================================

// AC_Pi: the same, with no a ∈ A premise (A = 0 gives the empty function).
opaque symbol AC_Pi (A : τ ι) (B : τ ι → τ ι) :
  (Π x : τ ι, π (x ∈ A) → π (`∃ (y : τ ι), y ∈ B x)) →
  π (`∃ (z : τ ι), z ∈ Pi A B) ≔
begin
  assume A B hB;
  refine ∨ₑ (em (A = empty)) _ _
  { assume he;
    refine ∃ᵢ empty _;
    refine ∧ₑ₂ (Pi_iff empty A B) _;
    refine ∧ᵢ _ (∧ᵢ _ _)
    { rewrite function_def;
      assume x y yp hxy hxyp;
      refine ⊥ₑ (emptyE (Pair x y) hxy) }
    { assume p hp; refine ⊥ₑ (emptyE p hp) }
    { assume x hx;
      have hx0 : π (x ∈ empty) { refine ind_eq (eq_sym he) (λ w, x ∈ w) hx };
      refine ⊥ₑ (emptyE x hx0) } }
  { assume hne;
    refine not_emptyE A (`∃ (z : τ ι), z ∈ Pi A B) hne _;
    assume a ha;
    refine AC a A B ha hB }
end;

// AC_ball_Pi: the Ball form of the premise.
opaque symbol AC_ball_Pi (A : τ ι) (B : τ ι → τ ι) :
  π (Ball A (λ x, `∃ (y : τ ι), y ∈ B x)) →
  π (`∃ (y : τ ι), y ∈ Pi A B) ≔
begin
  assume A B hB;
  refine AC_Pi A B _;
  assume x hx;
  refine hB x hx
end;

// AC_Pi_Pow: a choice function on the nonempty subsets of C.
opaque symbol AC_Pi_Pow (C : τ ι) :
  π (`∃ (f : τ ι), f ∈ Pi (Diff (Pow C) (singleton empty)) (λ X, X)) ≔
begin
  assume C;
  refine AC_Pi (Diff (Pow C) (singleton empty)) (λ X, X) _;
  assume x hx;
  have hne : π (x ≠ empty)
    { assume he;
      refine DiffD2 x (Pow C) (singleton empty) hx _;
      rewrite he;
      refine singletonI empty };
  refine not_emptyE x (`∃ (y : τ ι), y ∈ x) hne _;
  assume y hy;
  refine ∃ᵢ y hy
end;

// AC_func: a choice function A → ⋃A for a family of nonempty sets.
opaque symbol AC_func (A : τ ι) :
  (Π x : τ ι, π (x ∈ A) → π (`∃ (y : τ ι), y ∈ x)) →
  π (`∃ (f : τ ι), f ∈ Pi A (λ _, Union A)
       ∧ Ball A (λ x, fapply f x ∈ x)) ≔
begin
  assume A hne;
  refine ∃ₑ (AC_Pi A (λ x, x) hne) _;
  assume z hz;
  refine ∃ᵢ z _;
  apply ∧ᵢ
  { refine Pi_type z A (λ x, x) (λ _, Union A) hz _;
    assume x hx w hw;
    refine UnionI w x A hw hx }
  { assume x hx;
    refine fapply_type z x A (λ w, w) hz hx }
end;

// non_empty_family: if 0 ∉ A then every member of A is nonempty.
opaque symbol non_empty_family (A x : τ ι) :
  π (empty ∉ A) → π (x ∈ A) → π (`∃ (y : τ ι), y ∈ x) ≔
begin
  assume A x h0 hx;
  have hne : π (x ≠ empty)
    { assume he;
      refine h0 (ind_eq (eq_sym he) (λ w, w ∈ A) hx) };
  refine not_emptyE x (`∃ (y : τ ι), y ∈ x) hne _;
  assume y hy;
  refine ∃ᵢ y hy
end;

// AC_func0: the same with the 0 ∉ A premise.
opaque symbol AC_func0 (A : τ ι) :
  π (empty ∉ A) →
  π (`∃ (f : τ ι), f ∈ Pi A (λ _, Union A)
       ∧ Ball A (λ x, fapply f x ∈ x)) ≔
begin
  assume A h0;
  refine AC_func A _;
  assume x hx;
  refine non_empty_family A x h0 hx
end;

// AC_func_Pow: a choice function on the nonempty subsets of C, valued in C.
opaque symbol AC_func_Pow (C : τ ι) :
  π (`∃ (f : τ ι), f ∈ Pi (Diff (Pow C) (singleton empty)) (λ _, C)
       ∧ Ball (Diff (Pow C) (singleton empty)) (λ x, fapply f x ∈ x)) ≔
begin
  assume C;
  have h0 : π (empty ∉ Diff (Pow C) (singleton empty))
    { assume h;
      refine DiffD2 empty (Pow C) (singleton empty) h (singletonI empty) };
  refine ∃ₑ (AC_func0 (Diff (Pow C) (singleton empty)) h0) _;
  assume f hf;
  refine ∃ᵢ f _;
  apply ∧ᵢ _ (∧ₑ₂ hf);
  refine fun_weaken_type f (Diff (Pow C) (singleton empty))
    (Union (Diff (Pow C) (singleton empty))) C (∧ₑ₁ hf) _;
  assume w hw;
  refine ∃ₑ (UnionE w (Diff (Pow C) (singleton empty)) hw) _;
  assume S hS;
  refine PowD S C (DiffD1 S (Pow C) (singleton empty) (∧ₑ₁ hS)) w (∧ₑ₂ hS)
end;

// AC_Pi0: a dependent choice function on any family avoiding 0.
opaque symbol AC_Pi0 (A : τ ι) :
  π (empty ∉ A) →
  π (`∃ (f : τ ι), f ∈ Pi A (λ x, x)) ≔
begin
  assume A h0;
  refine AC_Pi A (λ x, x) _;
  assume x hx;
  refine non_empty_family A x h0 hx
end;
