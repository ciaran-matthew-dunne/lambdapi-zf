// ZF_Base: Core Zermelo-Fraenkel Set Theory Axioms
//
// Isabelle source: ZF_Base.thy
// Types: i (sets) → ι from Stdlib.Set, o (propositions) → o from Stdlib.Impred
// Arrow: ⇒ → ⤳ from Stdlib.HOL

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt;

// ---------------------------------------------------------------------------
// Primitive symbols (axiomatic)
// ---------------------------------------------------------------------------

// Membership relation: x ∈ A
constant symbol ∈ : τ ι → τ ι → Prop;
notation ∈ infix 10;

// Not-a-member: x ∉ A
symbol ∉ (x A : τ ι) ≔ ¬ (x ∈ A);
notation ∉ infix 10;

// Empty set
constant symbol empty : τ ι;

// Power set: Pow(A) = {x | x ⊆ A}
constant symbol Pow : τ ι → τ ι;

// General union: ⋃(C) = {x | ∃B∈C. x∈B}
constant symbol Union : τ ι → τ ι;

// Infinite set (axiom of infinity witness)
constant symbol Inf : τ ι;

// Primitive replacement: PrimReplace(A, P) = {b | ∃x∈A. P(x,b)} when P is functional
constant symbol PrimReplace : τ ι → (τ ι → τ ι → Prop) → τ ι;

// ---------------------------------------------------------------------------
// Subset (defined)
// ---------------------------------------------------------------------------

// A ⊆ B iff every member of A is a member of B
symbol ⊆ (A B : τ ι) : Prop ≔ `∀ (x : τ ι), x ∈ A ⇒ x ∈ B;
notation ⊆ infix 8;

// ---------------------------------------------------------------------------
// Bounded quantifiers (defined)
// ---------------------------------------------------------------------------

// Ball A P ≡ ∀x∈A. P(x)
symbol Ball (A : τ ι) (P : τ ι → Prop) : Prop ≔
  `∀ (x : τ ι), x ∈ A ⇒ P x;

// Bex A P ≡ ∃x∈A. P(x)
symbol Bex (A : τ ι) (P : τ ι → Prop) : Prop ≔
  `∃ (x : τ ι), x ∈ A ∧ P x;

// ---------------------------------------------------------------------------
// ZF Axioms
// ---------------------------------------------------------------------------

// Extensionality: sets with the same members are equal
constant symbol extension (A B : τ ι) :
  π ((`∀ (x : τ ι), (x ∈ A ⇔ x ∈ B)) ⇒ A = B);

// Empty set: nothing is a member of empty
constant symbol empty_ax :
  π (`∀ (x : τ ι), x ∉ empty);

// Union: A ∈ ⋃(C) iff there is a B in C containing A
constant symbol Union_iff (A C : τ ι) :
  π (A ∈ Union C ⇔ Bex C (λ B, A ∈ B));

// Power set: A ∈ Pow(B) iff A ⊆ B
constant symbol Pow_iff (A B : τ ι) :
  π (A ∈ Pow B ⇔ A ⊆ B);

// Foundation (regularity): every nonempty set has an ∈-minimal element
constant symbol foundation (A : τ ι) :
  π (A = empty ∨ Bex A (λ x, Ball x (λ y, y ∉ A)));

// Replacement: if P is functional on A, then PrimReplace(A,P) is the image
// Functional: ∀x∈A. ∀y z. P(x,y) ∧ P(x,z) → y = z
// Then: b ∈ PrimReplace(A,P) ⇔ ∃x∈A. P(x,b)
constant symbol replacement (A : τ ι) (P : τ ι → τ ι → Prop) :
  π (Ball A (λ x, `∀ (y : τ ι), `∀ (z : τ ι), P x y ⇒ P x z ⇒ y = z))
  → π (`∀ (b : τ ι),
       (b ∈ PrimReplace A P ⇔ Bex A (λ x, P x b)));

// ---------------------------------------------------------------------------
// Early derived lemmas
// ---------------------------------------------------------------------------

// Nothing is a member of the empty set (direct use)
opaque symbol emptyE (x : τ ι) : π (x ∉ empty) ≔
begin
  assume x h;
  refine empty_ax x h;
end;

// If something is in A, then A is nonempty (A ≠ empty)
opaque symbol ne_empty (A : τ ι) (x : τ ι) :
  π (x ∈ A) → π (A ≠ empty) ≔
begin
  assume A x hx heq;
  refine empty_ax x _;
  rewrite left heq;
  apply hx
end;

// Subset is reflexive
opaque symbol subset_refl (A : τ ι) : π (A ⊆ A) ≔
begin
  assume A x hx; apply hx
end;

// Subset is transitive
opaque symbol subset_trans (A B C : τ ι) :
  π (A ⊆ B) → π (B ⊆ C) → π (A ⊆ C) ≔
begin
  assume A B C hab hbc x hx;
  refine hbc x (hab x hx)
end;

// Equal sets are subsets of each other
opaque symbol eq_subset (A B : τ ι) :
  π (A = B) → π (A ⊆ B) ≔
begin
  assume A B heq x hx;
  rewrite left heq;
  apply hx
end;

// Extensionality (biconditional form): A = B iff same members
opaque symbol extension_iff (A B : τ ι) :
  π (A = B ⇔ (`∀ (x : τ ι), (x ∈ A ⇔ x ∈ B))) ≔
begin
  assume A B;
  apply ∧ᵢ
  { assume heq x;
    rewrite heq;
    apply ⇔_refl }
  { assume h; refine extension A B h }
end;

// Subset antisymmetry: if A ⊆ B and B ⊆ A then A = B
opaque symbol subset_antisym (A B : τ ι) :
  π (A ⊆ B) → π (B ⊆ A) → π (A = B) ≔
begin
  assume A B hab hba;
  refine extension A B _;
  assume x;
  apply ∧ᵢ
  { assume hx; refine hab x hx }
  { assume hx; refine hba x hx }
end;

// Empty set is a subset of everything
opaque symbol empty_subset (A : τ ι) : π (empty ⊆ A) ≔
begin
  assume A x hx;
  refine ⊥ₑ _;
  refine empty_ax x hx
end;

// If A ⊆ empty then A = empty
opaque symbol subset_empty (A : τ ι) :
  π (A ⊆ empty) → π (A = empty) ≔
begin
  assume A h;
  refine subset_antisym A empty h (empty_subset A)
end;

// Power set intro and elim
opaque symbol PowI (A B : τ ι) : π (A ⊆ B) → π (A ∈ Pow B) ≔
begin
  assume A B h;
  refine ∧ₑ₂ (Pow_iff A B) h
end;

opaque symbol PowD (A B : τ ι) : π (A ∈ Pow B) → π (A ⊆ B) ≔
begin
  assume A B h;
  refine ∧ₑ₁ (Pow_iff A B) h
end;

// Union intro: if x ∈ B and B ∈ C then x ∈ ⋃C
opaque symbol UnionI (x B C : τ ι) :
  π (x ∈ B) → π (B ∈ C) → π (x ∈ Union C) ≔
begin
  assume x B C hxB hBC;
  refine ∧ₑ₂ (Union_iff x C) _;
  refine ∃ᵢ B _;
  apply ∧ᵢ hBC hxB
end;

// Union elim: if x ∈ ⋃C then there exists B ∈ C with x ∈ B
opaque symbol UnionE (x C : τ ι) :
  π (x ∈ Union C) → π (Bex C (λ B, x ∈ B)) ≔
begin
  assume x C h;
  refine ∧ₑ₁ (Union_iff x C) h
end;

// ---------------------------------------------------------------------------
// Bounded quantifier lemmas
// ---------------------------------------------------------------------------

// Ball introduction: if P(x) for all x ∈ A, then Ball A P
opaque symbol ballI (A : τ ι) (P : τ ι → Prop) :
  (Π (x : τ ι), π (x ∈ A) → π (P x)) → π (Ball A P) ≔
begin
  assume A P h x hx;
  refine h x hx
end;

// Ball specialization: if Ball A P and x ∈ A, then P(x)
opaque symbol bspec (A : τ ι) (P : τ ι → Prop) (x : τ ι) :
  π (Ball A P) → π (x ∈ A) → π (P x) ≔
begin
  assume A P x hball hx;
  refine hball x hx
end;

// Ball elimination (classical): if Ball A P, then either x ∉ A or P(x) → Q
opaque symbol ballE (A : τ ι) (P : τ ι → Prop) (x : τ ι) (Q : Prop) :
  π (Ball A P) → (π (P x) → π Q) → (π (x ∉ A) → π Q) → π Q ≔
begin
  assume A P x Q hball hpq hna;
  refine ∨ₑ (em (x ∈ A)) _ _
  { assume hx; refine hpq (hball x hx) }
  { assume hnx; refine hna hnx }
end;

// Bex introduction: if x ∈ A and P(x), then Bex A P
opaque symbol bexI (A : τ ι) (P : τ ι → Prop) (x : τ ι) :
  π (P x) → π (x ∈ A) → π (Bex A P) ≔
begin
  assume A P x hp hx;
  refine ∃ᵢ x _;
  apply ∧ᵢ hx hp
end;

// Bex elimination: if Bex A P, then for some x ∈ A we have P(x)
opaque symbol bexE (A : τ ι) (P : τ ι → Prop) (Q : Prop) :
  π (Bex A P) → (Π (x : τ ι), π (x ∈ A) → π (P x) → π Q) → π Q ≔
begin
  assume A P Q hbex hpq;
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hPx : π (P x) { refine ∧ₑ₂ hx };
  refine hpq x hxA hPx
end;

// Reversed Bex introduction
opaque symbol rev_bexI (A : τ ι) (P : τ ι → Prop) (x : τ ι) :
  π (x ∈ A) → π (P x) → π (Bex A P) ≔
begin
  assume A P x hx hp;
  refine bexI A P x hp hx
end;

// ---------------------------------------------------------------------------
// More subset lemmas
// ---------------------------------------------------------------------------

// subsetD: A ⊆ B and c ∈ A implies c ∈ B
opaque symbol subsetD (A B : τ ι) (c : τ ι) :
  π (A ⊆ B) → π (c ∈ A) → π (c ∈ B) ≔
begin
  assume A B c hsub hc;
  refine hsub c hc
end;

// rev_subsetD: c ∈ A and A ⊆ B implies c ∈ B
opaque symbol rev_subsetD (A B : τ ι) (c : τ ι) :
  π (c ∈ A) → π (A ⊆ B) → π (c ∈ B) ≔
begin
  assume A B c hc hsub;
  refine hsub c hc
end;

// contra_subsetD: A ⊆ B and c ∉ B implies c ∉ A
opaque symbol contra_subsetD (A B : τ ι) (c : τ ι) :
  π (A ⊆ B) → π (c ∉ B) → π (c ∉ A) ≔
begin
  assume A B c hsub hnb hca;
  refine hnb (hsub c hca)
end;

// subsetCE: classical elimination for subsets
opaque symbol subsetCE (A B : τ ι) (c : τ ι) (P : Prop) :
  π (A ⊆ B) → (π (c ∉ A) → π P) → (π (c ∈ B) → π P) → π P ≔
begin
  assume A B c P hsub hna hb;
  refine ∨ₑ (em (c ∈ A)) _ _
  { assume hca; refine hb (hsub c hca) }
  { assume hnca; refine hna hnca }
end;

// subset_iff: A ⊆ B iff forall x, x ∈ A → x ∈ B
opaque symbol subset_iff (A B : τ ι) :
  π (A ⊆ B ⇔ (`∀ (x : τ ι), x ∈ A ⇒ x ∈ B)) ≔
begin
  assume A B;
  apply ∧ᵢ
  { assume h x hx; refine h x hx }
  { assume h x hx; refine h x hx }
end;

// ---------------------------------------------------------------------------
// More equality lemmas
// ---------------------------------------------------------------------------

// equality_iffI: if membership is equivalent for all x, then A = B
opaque symbol equality_iffI (A B : τ ι) :
  (Π (x : τ ι), π (x ∈ A ⇔ x ∈ B)) → π (A = B) ≔
begin
  assume A B h;
  refine extension A B _;
  assume x;
  refine h x
end;

// equalityD1: A = B implies A ⊆ B
opaque symbol equalityD1 (A B : τ ι) :
  π (A = B) → π (A ⊆ B) ≔
begin
  assume A B heq;
  refine eq_subset A B heq
end;

// equalityD2: A = B implies B ⊆ A
opaque symbol equalityD2 (A B : τ ι) :
  π (A = B) → π (B ⊆ A) ≔
begin
  assume A B heq;
  refine eq_subset B A (eq_sym heq)
end;

// equalityE: A = B gives both A ⊆ B and B ⊆ A
opaque symbol equalityE (A B : τ ι) (P : Prop) :
  π (A = B) → (π (A ⊆ B) → π (B ⊆ A) → π P) → π P ≔
begin
  assume A B P heq hk;
  refine hk (equalityD1 A B heq) (equalityD2 A B heq)
end;

// equalityCE: classical equality elimination
opaque symbol equalityCE (A B : τ ι) (c : τ ι) (P : Prop) :
  π (A = B) → (π (c ∈ A) → π (c ∈ B) → π P) →
  (π (c ∉ A) → π (c ∉ B) → π P) → π P ≔
begin
  assume A B c P heq hin hout;
  refine ∨ₑ (em (c ∈ A)) _ _
  { assume hca;
    have hcb : π (c ∈ B) { refine subsetD A B c (equalityD1 A B heq) hca };
    refine hin hca hcb }
  { assume hnca;
    have hncb : π (c ∉ B) { refine contra_subsetD B A c (equalityD2 A B heq) hnca };
    refine hout hnca hncb }
end;

// equality_iffD: A = B implies x ∈ A ⇔ x ∈ B
opaque symbol equality_iffD (A B : τ ι) (x : τ ι) :
  π (A = B) → π (x ∈ A ⇔ x ∈ B) ≔
begin
  assume A B x heq;
  refine ∧ₑ₁ (extension_iff A B) heq x
end;

// ---------------------------------------------------------------------------
// More empty set lemmas
// ---------------------------------------------------------------------------

// equals0I: if nothing is in A, then A = empty
opaque symbol equals0I (A : τ ι) :
  (Π (y : τ ι), π (y ∈ A) → π ⊥) → π (A = empty) ≔
begin
  assume A h;
  refine subset_empty A _;
  assume x hx;
  refine ⊥ₑ (h x hx)
end;

// equals0D: A = empty implies a ∉ A
opaque symbol equals0D (A : τ ι) (a : τ ι) :
  π (A = empty) → π (a ∉ A) ≔
begin
  assume A a heq ha;
  refine empty_ax a _;
  rewrite left heq;
  apply ha
end;

// not_emptyE: if A ≠ empty, then there exists some x ∈ A
opaque symbol not_emptyE (A : τ ι) (R : Prop) :
  π (A ≠ empty) → (Π (x : τ ι), π (x ∈ A) → π R) → π R ≔
begin
  assume A R hne hk;
  // Use foundation: A = empty ∨ Bex A (λ x, Ball x (λ y, y ∉ A))
  refine ∨ₑ (foundation A) _ _
  { // A = empty — contradicts hne
    assume heq;
    refine ⊥ₑ (hne heq) }
  { // ∃ x ∈ A. Ball x (λ y, y ∉ A)
    assume hbex;
    refine ∃ₑ hbex _;
    assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    refine hk x hxA
  }
end;

// subst_elem: b ∈ A and a = b implies a ∈ A
opaque symbol subst_elem (a b A : τ ι) :
  π (b ∈ A) → π (a = b) → π (a ∈ A) ≔
begin
  assume a b A hb heq;
  rewrite heq;
  apply hb
end;

// ---------------------------------------------------------------------------
// Pow derived lemmas
// ---------------------------------------------------------------------------

// Pow_bottom: empty ∈ Pow(B)
opaque symbol Pow_bottom (B : τ ι) : π (empty ∈ Pow B) ≔
begin
  assume B;
  refine PowI empty B (empty_subset B)
end;

// Pow_top: A ∈ Pow(A)
opaque symbol Pow_top (A : τ ι) : π (A ∈ Pow A) ≔
begin
  assume A;
  refine PowI A A (subset_refl A)
end;

// Note: mem_irrefl and mem_asym are proved in upair.lp (after singleton/Upair are defined)
