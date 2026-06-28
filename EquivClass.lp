// EquivClass: Equivalence Relations and Quotient Constructions
//
// Isabelle source: EquivClass.thy
// Defines: refl_on, equiv, quotient, congruent, congruent2
// Proves: equivalence class lemmas, quotient properties

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.Trancl ZF.Perm;

// ===========================================================================
// Relational image of singleton — r``{a} = {y | Pair(a,y) ∈ r}
// In Isabelle ZF: r``{a} is Image(r, {a})
// ===========================================================================

// rel_image_sing(r, a) = {y ∈ range(r) | Pair(a,y) ∈ r}
symbol rel_image_sing (r a : τ ι) : τ ι ≔
  Collect (range r) (λ y, Pair a y ∈ r);

// rel_image_singI: Pair(a,b) ∈ r → b ∈ rel_image_sing(r, a)
opaque symbol rel_image_singI (a b r : τ ι) :
  π (Pair a b ∈ r) → π (b ∈ rel_image_sing r a) ≔
begin
  assume a b r hab;
  refine CollectI b (range r) (λ y, Pair a y ∈ r) (rangeI a b r hab) hab
end;

// rel_image_singD: b ∈ rel_image_sing(r, a) → Pair(a,b) ∈ r
opaque symbol rel_image_singD (a b r : τ ι) :
  π (b ∈ rel_image_sing r a) → π (Pair a b ∈ r) ≔
begin
  assume a b r h;
  refine CollectD2 b (range r) (λ y, Pair a y ∈ r) h
end;

// ===========================================================================
// Reflexive relation — refl(A,r) ≡ ∀x∈A. Pair(x,x) ∈ r
// ===========================================================================

symbol refl_on (A r : τ ι) : Prop ≔
  Ball A (λ x, Pair x x ∈ r);

// ===========================================================================
// Equivalence relation — equiv(A,r) ≡ r ⊆ A×A ∧ refl(A,r) ∧ sym(r) ∧ trans(r)
// ===========================================================================

symbol equiv (A r : τ ι) : Prop ≔
  r ⊆ Sigma A (λ _, A) ∧ refl_on A r ∧ sym r ∧ trans r;

// equiv projections
opaque symbol equiv_type (A r : τ ι) :
  π (equiv A r) → π (r ⊆ Sigma A (λ _, A)) ≔
begin
  assume A r h;
  refine ∧ₑ₁ h
end;

opaque symbol equiv_refl (A r : τ ι) :
  π (equiv A r) → π (refl_on A r) ≔
begin
  assume A r h;
  refine ∧ₑ₁ (∧ₑ₂ h)
end;

opaque symbol equiv_sym (A r : τ ι) :
  π (equiv A r) → π (sym r) ≔
begin
  assume A r h;
  refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ h))
end;

opaque symbol equiv_trans (A r : τ ι) :
  π (equiv A r) → π (trans r) ≔
begin
  assume A r h;
  refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h))
end;

// ===========================================================================
// Quotient — A//r = {r``{x} | x ∈ A}
// ===========================================================================

symbol quotient (A r : τ ι) : τ ι ≔
  RepFun A (λ x, rel_image_sing r x);

// ===========================================================================
// Congruent — congruent(r,b) ≡ ∀y z. Pair(y,z) ∈ r → b(y) = b(z)
// ===========================================================================

symbol congruent (r : τ ι) (b : τ ι → τ ι) : Prop ≔
  `∀ (y : τ ι), `∀ (z : τ ι), Pair y z ∈ r ⇒ b y = b z;

// ===========================================================================
// Congruent2 — congruent2(r1,r2,b) ≡ ∀y1 z1 y2 z2. ...
// ===========================================================================

symbol congruent2 (r1 r2 : τ ι) (b : τ ι → τ ι → τ ι) : Prop ≔
  `∀ (y1 : τ ι), `∀ (z1 : τ ι), `∀ (y2 : τ ι), `∀ (z2 : τ ι),
    Pair y1 z1 ∈ r1 ⇒ Pair y2 z2 ∈ r2 ⇒ b y1 y2 = b z1 z2;

// ===========================================================================
// Section: Suppes Theorem 70
// equiv(A,r) iff converse(r) O r = r
// ===========================================================================

// sym_trans_comp_subset: sym(r) → trans(r) → converse(r) O r ⊆ r
opaque symbol sym_trans_comp_subset (r : τ ι) :
  π (sym r) → π (trans r) → π (rcomp (converse r) r ⊆ r) ≔
begin
  assume r hsym htrans p hp;
  // p ∈ rcomp(converse(r), r)
  // rcomp is Collect(Sigma(domain(r), λ_. range(converse(r))), ...)
  // p must be in Sigma, so it's a pair
  have hSig : π (p ∈ Sigma (domain r) (λ _, range (converse r)))
    { refine CollectD1 p (Sigma (domain r) (λ _, range (converse r)))
        (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ r ∧ Pair y (snd q) ∈ converse r) hp };
  have hbex : π (Bex (domain r) (λ x, Bex (range (converse r)) (λ y, p = Pair x y)))
    { refine SigmaE p (domain r) (λ _, range (converse r)) hSig };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxdom : π (x ∈ domain r) { refine ∧ₑ₁ hx };
  have hbex2 : π (Bex (range (converse r)) (λ y, p = Pair x y)) { refine ∧ₑ₂ hx };
  refine ∃ₑ hbex2 _;
  assume z hz;
  have hzrng : π (z ∈ range (converse r)) { refine ∧ₑ₁ hz };
  have hpeq : π (p = Pair x z) { refine ∧ₑ₂ hz };
  // Now get the witness from rcomp
  have hfst_eq : π (fst (Pair x z) = x) { refine fst_conv x z };
  have hsnd_eq : π (snd (Pair x z) = z) { refine snd_conv x z };
  have hex : π (`∃ (y : τ ι), Pair (fst p) y ∈ r ∧ Pair y (snd p) ∈ converse r)
    { refine CollectD2 p (Sigma (domain r) (λ _, range (converse r)))
        (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ r ∧ Pair y (snd q) ∈ converse r) hp };
  // Substitute p = Pair(x,z) to get fst p = x, snd p = z
  refine ∃ₑ hex _;
  assume y hy;
  // Pair(fst p, y) ∈ r and Pair(y, snd p) ∈ converse(r)
  have h1 : π (Pair (fst p) y ∈ r) { refine ∧ₑ₁ hy };
  have h2 : π (Pair y (snd p) ∈ converse r) { refine ∧ₑ₂ hy };
  // fst p = x, snd p = z (via hpeq)
  have hfst_p : π (fst p = x)
    { refine ind_eq hpeq (λ q, fst q = x) hfst_eq };
  have hsnd_p : π (snd p = z)
    { refine ind_eq hpeq (λ q, snd q = z) hsnd_eq };
  // Pair(x,y) ∈ r
  have hxy : π (Pair x y ∈ r)
    { refine ind_eq (eq_sym hfst_p) (λ w, Pair w y ∈ r) h1 };
  // Pair(y,z) ∈ converse(r), so Pair(z,y) ∈ r
  have hyz_conv : π (Pair y z ∈ converse r)
    { refine ind_eq (eq_sym hsnd_p) (λ w, Pair y w ∈ converse r) h2 };
  have hzy : π (Pair z y ∈ r) { refine converseD y z r hyz_conv };
  // By sym: Pair(y,z) ∈ r
  have hyz : π (Pair y z ∈ r) { refine hsym z y hzy };
  // By trans: Pair(x,y) ∈ r ∧ Pair(y,z) ∈ r → Pair(x,z) ∈ r
  have hxz : π (Pair x z ∈ r) { refine htrans x y z hxy hyz };
  rewrite hpeq;
  apply hxz
end;

// refl_comp_subset: refl(A,r) → r ⊆ A×A → r ⊆ converse(r) O r
opaque symbol refl_comp_subset (A r : τ ι) :
  π (refl_on A r) → π (r ⊆ Sigma A (λ _, A)) → π (r ⊆ rcomp (converse r) r) ≔
begin
  assume A r hrefl hsub p hp;
  // p ∈ r, and r ⊆ A×A, so p = Pair(x,y) for some x ∈ A, y ∈ A
  have hpSig : π (p ∈ Sigma A (λ _, A)) { refine hsub p hp };
  have hbex : π (Bex A (λ x, Bex A (λ y, p = Pair x y)))
    { refine SigmaE p A (λ _, A) hpSig };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hbex2 : π (Bex A (λ y, p = Pair x y)) { refine ∧ₑ₂ hx };
  refine ∃ₑ hbex2 _;
  assume y hy;
  have hyA : π (y ∈ A) { refine ∧ₑ₁ hy };
  have hpeq : π (p = Pair x y) { refine ∧ₑ₂ hy };
  // Pair(x,y) ∈ r
  have hxy : π (Pair x y ∈ r) { refine ind_eq (eq_sym hpeq) (λ q, q ∈ r) hp };
  // refl(A,r) → Pair(x,x) ∈ r
  have hxx : π (Pair x x ∈ r) { refine hrefl x hxA };
  // converse(r): Pair(x,x) ∈ r → Pair(x,x) ∈ converse(r)
  have hxx_conv : π (Pair x x ∈ converse r) { refine converseI x x r hxx };
  // rcomp(converse(r), r): Pair(x,y) ∈ r ∧ Pair(x,x) ∈ converse(r) → Pair(x,y) ∈ rcomp
  // rcompI: Pair(a,b) ∈ s → Pair(b,c) ∈ r → Pair(a,c) ∈ rcomp(r,s)
  // We need Pair(x,x) ∈ r (first arg to rcomp is 2nd relation)
  // rcomp(converse(r), r) means: ∃m. Pair(x,m) ∈ r ∧ Pair(m,y) ∈ converse(r)
  // Take m = x: Pair(x,x) ∈ r ✓ and Pair(x,y) ∈ converse(r)
  // Wait: we need Pair(x,y) ∈ converse(r), i.e., Pair(y,x) ∈ r
  // Actually let's use m = y: Pair(x,y) ∈ r ✓ and Pair(y,y) ∈ converse(r)
  // Pair(y,y) ∈ r since y ∈ A and refl
  have hyy : π (Pair y y ∈ r) { refine hrefl y hyA };
  have hyy_conv : π (Pair y y ∈ converse r) { refine converseI y y r hyy };
  // rcompI a b c r s: Pair(a,b) ∈ s → Pair(b,c) ∈ r → Pair(a,c) ∈ rcomp(r,s)
  // rcomp(converse(r), r): s=r, r=converse(r)
  // Need: Pair(x,y) ∈ r and Pair(y,y) ∈ converse(r) → Pair(x,y) ∈ rcomp(converse(r), r)
  have hres : π (Pair x y ∈ rcomp (converse r) r)
    { refine rcompI x y y (converse r) r hxy hyy_conv };
  rewrite hpeq;
  apply hres
end;

// equiv_comp_eq: equiv(A,r) → converse(r) O r = r
opaque symbol equiv_comp_eq (A r : τ ι) :
  π (equiv A r) → π (rcomp (converse r) r = r) ≔
begin
  assume A r heq;
  refine subset_antisym (rcomp (converse r) r) r _ _
  { refine sym_trans_comp_subset r (equiv_sym A r heq) (equiv_trans A r heq) }
  { refine refl_comp_subset A r (equiv_refl A r heq) (equiv_type A r heq) }
end;

// comp_equivI: converse(r) O r = r → domain(r) = A → equiv(A,r)
// TODO: prove — complex proof involving unfolding all definitions
opaque symbol comp_equivI (A r : τ ι) :
  π (rcomp (converse r) r = r) → π (domain r = A) → π (equiv A r) ≔
begin
  assume A r hcomp hdom;
  admit
end;

// ===========================================================================
// Equivalence classes
// ===========================================================================

// equiv_class_subset: sym(r) → trans(r) → Pair(a,b) ∈ r → r``{a} ⊆ r``{b}
opaque symbol equiv_class_subset (a b r : τ ι) :
  π (sym r) → π (trans r) → π (Pair a b ∈ r) →
  π (rel_image_sing r a ⊆ rel_image_sing r b) ≔
begin
  assume a b r hsym htrans hab x hx;
  // x ∈ r``{a} means Pair(a,x) ∈ r
  have hax : π (Pair a x ∈ r) { refine rel_image_singD a x r hx };
  // sym: Pair(a,b) ∈ r → Pair(b,a) ∈ r
  have hba : π (Pair b a ∈ r) { refine hsym a b hab };
  // trans: Pair(b,a) ∈ r → Pair(a,x) ∈ r → Pair(b,x) ∈ r
  have hbx : π (Pair b x ∈ r) { refine htrans b a x hba hax };
  refine rel_image_singI b x r hbx
end;

// equiv_class_eq: equiv(A,r) → Pair(a,b) ∈ r → r``{a} = r``{b}
opaque symbol equiv_class_eq (A a b r : τ ι) :
  π (equiv A r) → π (Pair a b ∈ r) →
  π (rel_image_sing r a = rel_image_sing r b) ≔
begin
  assume A a b r heq hab;
  have hsym0 : π (sym r) { refine equiv_sym A r heq };
  have htrans0 : π (trans r) { refine equiv_trans A r heq };
  refine subset_antisym (rel_image_sing r a) (rel_image_sing r b) _ _
  { refine equiv_class_subset a b r hsym0 htrans0 hab }
  { // Pair(b,a) ∈ r by sym
    have hba : π (Pair b a ∈ r) { refine hsym0 a b hab };
    refine equiv_class_subset b a r hsym0 htrans0 hba }
end;

// equiv_class_self: equiv(A,r) → a ∈ A → a ∈ r``{a}
opaque symbol equiv_class_self (A a r : τ ι) :
  π (equiv A r) → π (a ∈ A) → π (a ∈ rel_image_sing r a) ≔
begin
  assume A a r heq haA;
  have hrefl0 : π (refl_on A r) { refine equiv_refl A r heq };
  have haa : π (Pair a a ∈ r) { refine hrefl0 a haA };
  refine rel_image_singI a a r haa
end;

// subset_equiv_class: equiv(A,r) → r``{b} ⊆ r``{a} → b ∈ A → Pair(a,b) ∈ r
opaque symbol subset_equiv_class (A a b r : τ ι) :
  π (equiv A r) → π (rel_image_sing r b ⊆ rel_image_sing r a) → π (b ∈ A) →
  π (Pair a b ∈ r) ≔
begin
  assume A a b r heq hsub hbA;
  // b ∈ r``{b} by refl
  have hb_self : π (b ∈ rel_image_sing r b) { refine equiv_class_self A b r heq hbA };
  // b ∈ r``{a} by subset
  have hb_a : π (b ∈ rel_image_sing r a) { refine hsub b hb_self };
  // Pair(a,b) ∈ r
  refine rel_image_singD a b r hb_a
end;

// eq_equiv_class: r``{a} = r``{b} → equiv(A,r) → b ∈ A → Pair(a,b) ∈ r
opaque symbol eq_equiv_class (A a b r : τ ι) :
  π (rel_image_sing r a = rel_image_sing r b) → π (equiv A r) → π (b ∈ A) →
  π (Pair a b ∈ r) ≔
begin
  assume A a b r heqc heq hbA;
  refine subset_equiv_class A a b r heq
    (equalityD2 (rel_image_sing r a) (rel_image_sing r b) heqc) hbA
end;

// equiv_class_nondisjoint: equiv(A,r) → x ∈ r``{a} ∩ r``{b} → Pair(a,b) ∈ r
opaque symbol equiv_class_nondisjoint (A a b x r : τ ι) :
  π (equiv A r) → π (x ∈ Int (rel_image_sing r a) (rel_image_sing r b)) →
  π (Pair a b ∈ r) ≔
begin
  assume A a b x r heq hx;
  have hsym0 : π (sym r) { refine equiv_sym A r heq };
  have htrans0 : π (trans r) { refine equiv_trans A r heq };
  have hxa : π (x ∈ rel_image_sing r a)
    { refine ∧ₑ₁ (∧ₑ₁ (Int_iff x (rel_image_sing r a) (rel_image_sing r b)) hx) };
  have hxb : π (x ∈ rel_image_sing r b)
    { refine ∧ₑ₂ (∧ₑ₁ (Int_iff x (rel_image_sing r a) (rel_image_sing r b)) hx) };
  // Pair(a,x) ∈ r and Pair(b,x) ∈ r
  have hax : π (Pair a x ∈ r) { refine rel_image_singD a x r hxa };
  have hbx : π (Pair b x ∈ r) { refine rel_image_singD b x r hxb };
  // sym: Pair(x,b) ∈ r
  have hxb2 : π (Pair x b ∈ r) { refine hsym0 b x hbx };
  // trans: Pair(a,x) ∈ r → Pair(x,b) ∈ r → Pair(a,b) ∈ r
  refine htrans0 a x b hax hxb2
end;

// equiv_class_eq_iff: equiv(A,r) → (Pair(x,y) ∈ r ⇔ r``{x} = r``{y} ∧ x ∈ A ∧ y ∈ A)
opaque symbol equiv_class_eq_iff (A x y r : τ ι) :
  π (equiv A r) →
  π (Pair x y ∈ r ⇔ (rel_image_sing r x = rel_image_sing r y ∧ x ∈ A ∧ y ∈ A)) ≔
begin
  assume A x y r heq;
  apply ∧ᵢ
  { assume hxy;
    have htype : π (r ⊆ Sigma A (λ _, A)) { refine equiv_type A r heq };
    have hpSig : π (Pair x y ∈ Sigma A (λ _, A)) { refine htype (Pair x y) hxy };
    have hbex : π (Bex A (λ a, Bex A (λ b, Pair x y = Pair a b)))
      { refine SigmaE (Pair x y) A (λ _, A) hpSig };
    // From Pair(x,y) ∈ Sigma(A, λ_. A), get x ∈ A and y ∈ A
    have hxA : π (x ∈ A)
    { refine ∃ₑ hbex _;
      assume a ha;
      have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
      have hbex2 : π (Bex A (λ b, Pair x y = Pair a b)) { refine ∧ₑ₂ ha };
      refine ∃ₑ hbex2 _;
      assume b hb;
      have hpeq : π (Pair x y = Pair a b) { refine ∧ₑ₂ hb };
      have hxa : π (x = a) { refine Pair_inject1 x y a b hpeq };
      rewrite hxa; apply haA };
    have hyA : π (y ∈ A)
    { refine ∃ₑ hbex _;
      assume a ha;
      have hbex2 : π (Bex A (λ b, Pair x y = Pair a b)) { refine ∧ₑ₂ ha };
      refine ∃ₑ hbex2 _;
      assume b hb;
      have hbA : π (b ∈ A) { refine ∧ₑ₁ hb };
      have hpeq : π (Pair x y = Pair a b) { refine ∧ₑ₂ hb };
      have hyb : π (y = b) { refine Pair_inject2 x y a b hpeq };
      rewrite hyb; apply hbA };
    apply ∧ᵢ
    { refine equiv_class_eq A x y r heq hxy }
    { apply ∧ᵢ hxA hyA } }
  { assume h;
    have heqc : π (rel_image_sing r x = rel_image_sing r y) { refine ∧ₑ₁ h };
    have hyA : π (y ∈ A) { refine ∧ₑ₂ (∧ₑ₂ h) };
    refine eq_equiv_class A x y r heqc heq hyA }
end;

// eq_equiv_class_iff: equiv(A,r) → x ∈ A → y ∈ A → (r``{x} = r``{y} ⇔ Pair(x,y) ∈ r)
opaque symbol eq_equiv_class_iff (A x y r : τ ι) :
  π (equiv A r) → π (x ∈ A) → π (y ∈ A) →
  π (rel_image_sing r x = rel_image_sing r y ⇔ Pair x y ∈ r) ≔
begin
  assume A x y r heq hxA hyA;
  apply ∧ᵢ
  { assume heqc; refine eq_equiv_class A x y r heqc heq hyA }
  { assume hxy; refine equiv_class_eq A x y r heq hxy }
end;

// ===========================================================================
// Quotients
// ===========================================================================

// quotientI: x ∈ A → r``{x} ∈ A//r
opaque symbol quotientI (x A r : τ ι) :
  π (x ∈ A) → π (rel_image_sing r x ∈ quotient A r) ≔
begin
  assume x A r hxA;
  refine RepFunI x A (λ w, rel_image_sing r w) hxA
end;

// quotientE: X ∈ A//r → ∃x∈A. X = r``{x}
opaque symbol quotientE (X A r : τ ι) :
  π (X ∈ quotient A r) →
  π (Bex A (λ x, X = rel_image_sing r x)) ≔
begin
  assume X A r hX;
  refine ∧ₑ₁ (RepFun_iff X A (λ w, rel_image_sing r w)) hX
end;

// Union_quotient: equiv(A,r) → ⋃(A//r) = A
// TODO: prove
opaque symbol Union_quotient (A r : τ ι) :
  π (equiv A r) → π (Union (quotient A r) = A) ≔
begin
  assume A r heq;
  admit
end;

// quotient_disj: equiv(A,r) → X ∈ A//r → Y ∈ A//r → X = Y ∨ X ∩ Y ⊆ empty
// TODO: prove
opaque symbol quotient_disj (A r X Y : τ ι) :
  π (equiv A r) → π (X ∈ quotient A r) → π (Y ∈ quotient A r) →
  π (X = Y ∨ Int X Y ⊆ empty) ≔
begin
  assume A r X Y heq hX hY;
  admit
end;

// ===========================================================================
// Section: Defining Unary Operations upon Equivalence Classes
// ===========================================================================

// UN_equiv_class: equiv(A,r) → congruent(r,b) → a ∈ A →
//   ⋃{b(x) | x ∈ r``{a}} = b(a)
// Note: ⋃{b(x) | x ∈ S} is Union(RepFun(S, b))
// TODO: prove
opaque symbol UN_equiv_class (A r : τ ι) (b : τ ι → τ ι) (a : τ ι) :
  π (equiv A r) → π (congruent r b) → π (a ∈ A) →
  π (Union (RepFun (rel_image_sing r a) b) = b a) ≔
begin
  assume A r b a heq hcong haA;
  admit
end;

// UN_equiv_class_type: equiv(A,r) → congruent(r,b) → X ∈ A//r →
//   (∀x∈A. b(x) ∈ B) → ⋃{b(x) | x ∈ X} ∈ B
// TODO: prove
opaque symbol UN_equiv_class_type (A r B : τ ι) (b : τ ι → τ ι) (X : τ ι) :
  π (equiv A r) → π (congruent r b) → π (X ∈ quotient A r) →
  (Π (x : τ ι), π (x ∈ A) → π (b x ∈ B)) →
  π (Union (RepFun X b) ∈ B) ≔
begin
  assume A r B b X heq hcong hX hbB;
  admit
end;

// UN_equiv_class_inject: equiv(A,r) → congruent(r,b) →
//   ⋃{b(x)|x∈X} = ⋃{b(y)|y∈Y} → X ∈ A//r → Y ∈ A//r →
//   (∀x y. x∈A → y∈A → b(x)=b(y) → Pair(x,y)∈r) → X = Y
// TODO: prove
opaque symbol UN_equiv_class_inject (A r : τ ι) (b : τ ι → τ ι) (X Y : τ ι) :
  π (equiv A r) → π (congruent r b) →
  π (Union (RepFun X b) = Union (RepFun Y b)) →
  π (X ∈ quotient A r) → π (Y ∈ quotient A r) →
  (Π (x : τ ι), Π (y : τ ι), π (x ∈ A) → π (y ∈ A) → π (b x = b y) → π (Pair x y ∈ r)) →
  π (X = Y) ≔
begin
  assume A r b X Y heq hcong hunion hXq hYq hinj;
  admit
end;

// ===========================================================================
// Section: Defining Binary Operations upon Equivalence Classes
// ===========================================================================

// congruent2_implies_congruent: equiv(A,r1) → congruent2(r1,r2,b) → a ∈ A →
//   congruent(r2, b(a))
opaque symbol congruent2_implies_congruent (A r1 r2 : τ ι) (b : τ ι → τ ι → τ ι) (a : τ ι) :
  π (equiv A r1) → π (congruent2 r1 r2 b) → π (a ∈ A) →
  π (congruent r2 (b a)) ≔
begin
  assume A r1 r2 b a heq hcong2 haA y z hyz;
  // congruent2: ∀y1 z1 y2 z2. Pair(y1,z1)∈r1 → Pair(y2,z2)∈r2 → b(y1,y2) = b(z1,z2)
  // Take y1=z1=a, y2=y, z2=z: need Pair(a,a) ∈ r1
  have haa : π (Pair a a ∈ r1) { refine (equiv_refl A r1 heq) a haA };
  refine hcong2 a a y z haa hyz
end;

// congruent2_implies_congruent_UN: equiv(A1,r1) → equiv(A2,r2) →
//   congruent2(r1,r2,b) → a ∈ A2 →
//   congruent(r1, λx1. ⋃{b(x1,x2) | x2 ∈ r2``{a}})
// TODO: prove
opaque symbol congruent2_implies_congruent_UN (A1 A2 r1 r2 : τ ι)
  (b : τ ι → τ ι → τ ι) (a : τ ι) :
  π (equiv A1 r1) → π (equiv A2 r2) → π (congruent2 r1 r2 b) → π (a ∈ A2) →
  π (congruent r1 (λ x1, Union (RepFun (rel_image_sing r2 a) (λ x2, b x1 x2)))) ≔
begin
  assume A1 A2 r1 r2 b a heq1 heq2 hcong2 haA2;
  admit
end;

// UN_equiv_class2: equiv(A1,r1) → equiv(A2,r2) → congruent2(r1,r2,b) →
//   a1 ∈ A1 → a2 ∈ A2 →
//   ⋃{⋃{b(x1,x2) | x2 ∈ r2``{a2}} | x1 ∈ r1``{a1}} = b(a1,a2)
// TODO: prove
opaque symbol UN_equiv_class2 (A1 A2 r1 r2 : τ ι)
  (b : τ ι → τ ι → τ ι) (a1 a2 : τ ι) :
  π (equiv A1 r1) → π (equiv A2 r2) → π (congruent2 r1 r2 b) →
  π (a1 ∈ A1) → π (a2 ∈ A2) →
  π (Union (RepFun (rel_image_sing r1 a1) (λ x1,
    Union (RepFun (rel_image_sing r2 a2) (λ x2, b x1 x2)))) = b a1 a2) ≔
begin
  assume A1 A2 r1 r2 b a1 a2 heq1 heq2 hcong2 ha1A1 ha2A2;
  admit
end;

// UN_equiv_class_type2: equiv(A,r) → congruent2(r,r,b) →
//   X1 ∈ A//r → X2 ∈ A//r →
//   (∀x1∈A. ∀x2∈A. b(x1,x2) ∈ B) →
//   ⋃{⋃{b(x1,x2)|x2∈X2}|x1∈X1} ∈ B
// TODO: prove
opaque symbol UN_equiv_class_type2 (A r B X1 X2 : τ ι)
  (b : τ ι → τ ι → τ ι) :
  π (equiv A r) → π (congruent2 r r b) →
  π (X1 ∈ quotient A r) → π (X2 ∈ quotient A r) →
  (Π (x1 : τ ι), Π (x2 : τ ι), π (x1 ∈ A) → π (x2 ∈ A) → π (b x1 x2 ∈ B)) →
  π (Union (RepFun X1 (λ x1, Union (RepFun X2 (λ x2, b x1 x2)))) ∈ B) ≔
begin
  assume A r B X1 X2 b heq hcong2 hX1 hX2 hbB;
  admit
end;

// congruent2I: equiv(A1,r1) → equiv(A2,r2) →
//   (∀w∈A2. ∀y z. Pair(y,z) ∈ r1 → b(y,w) = b(z,w)) →
//   (∀w∈A1. ∀y z. Pair(y,z) ∈ r2 → b(w,y) = b(w,z)) →
//   congruent2(r1,r2,b)
// TODO: prove
opaque symbol congruent2I (A1 A2 r1 r2 : τ ι) (b : τ ι → τ ι → τ ι) :
  π (equiv A1 r1) → π (equiv A2 r2) →
  (Π (w : τ ι), π (w ∈ A2) → Π (y : τ ι), Π (z : τ ι), π (Pair y z ∈ r1) → π (b y w = b z w)) →
  (Π (w : τ ι), π (w ∈ A1) → Π (y : τ ι), Π (z : τ ι), π (Pair y z ∈ r2) → π (b w y = b w z)) →
  π (congruent2 r1 r2 b) ≔
begin
  assume A1 A2 r1 r2 b heq1 heq2 hleft hright;
  admit
end;

// congruent2_commuteI: equiv(A,r) →
//   (∀y z. y∈A → z∈A → b(y,z) = b(z,y)) →
//   (∀w y z. w∈A → Pair(y,z)∈r → b(w,y) = b(w,z)) →
//   congruent2(r,r,b)
// TODO: prove
opaque symbol congruent2_commuteI (A r : τ ι) (b : τ ι → τ ι → τ ι) :
  π (equiv A r) →
  (Π (y : τ ι), Π (z : τ ι), π (y ∈ A) → π (z ∈ A) → π (b y z = b z y)) →
  (Π (w : τ ι), Π (y : τ ι), Π (z : τ ι), π (w ∈ A) → π (Pair y z ∈ r) → π (b w y = b w z)) →
  π (congruent2 r r b) ≔
begin
  assume A r b heq hcomm hcong;
  admit
end;

// congruent_commuteI: equiv(A,r) → Z ∈ A//r →
//   (∀w∈A. congruent(r, λz. b(w,z))) →
//   (∀x y. x∈A → y∈A → b(y,x) = b(x,y)) →
//   congruent(r, λw. ⋃{b(w,z) | z ∈ Z})
// TODO: prove
opaque symbol congruent_commuteI (A r Z : τ ι) (b : τ ι → τ ι → τ ι) :
  π (equiv A r) → π (Z ∈ quotient A r) →
  (Π (w : τ ι), π (w ∈ A) → π (congruent r (λ z, b w z))) →
  (Π (x : τ ι), Π (y : τ ι), π (x ∈ A) → π (y ∈ A) → π (b y x = b x y)) →
  π (congruent r (λ w, Union (RepFun Z (λ z, b w z)))) ≔
begin
  assume A r Z b heq hZ hcongw hcomm;
  admit
end;
