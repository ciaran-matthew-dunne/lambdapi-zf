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
opaque symbol comp_equivI (A r : τ ι) :
  π (rcomp (converse r) r = r) → π (domain r = A) → π (equiv A r) ≔
begin
  assume A r hcomp hdom;
  // Symmetry: converse(r)∘r is inherently symmetric, and it equals r.
  have hsym : π (sym r) {
    assume a b hab;
    have hin : π (Pair a b ∈ rcomp (converse r) r)
      { refine ind_eq hcomp (λ w, Pair a b ∈ w) hab };
    refine ∃ₑ (rcompE_pair a b (converse r) r hin) _; assume y hy;
    have hby : π (Pair b y ∈ r) { refine converseD y b r (∧ₑ₂ hy) };
    have hya : π (Pair y a ∈ converse r) { refine converseI a y r (∧ₑ₁ hy) };
    refine ind_eq (eq_sym hcomp) (λ w, Pair b a ∈ w)
      (rcompI b y a (converse r) r hby hya) };
  // Transitivity, using symmetry.
  have htrans : π (trans r) {
    assume a b c hab hbc;
    have hbc_conv : π (Pair b c ∈ converse r) { refine converseI c b r (hsym b c hbc) };
    refine ind_eq (eq_sym hcomp) (λ w, Pair a c ∈ w)
      (rcompI a b c (converse r) r hab hbc_conv) };
  // Reflexivity on A = domain(r): each x has some ⟨x,y⟩∈r, so ⟨x,x⟩∈r by sym+trans.
  have hrefl : π (refl_on A r) {
    assume x hxA;
    have hxdom : π (x ∈ domain r) { refine ind_eq hdom (λ w, x ∈ w) hxA };
    refine ∃ₑ (domainE x r hxdom) _; assume y hxy;
    refine htrans x y x hxy (hsym x y hxy) };
  // r ⊆ A×A: elements of r = converse(r)∘r are pairs; both projections lie in domain(r)=A.
  have hsub : π (r ⊆ Sigma A (λ _, A)) {
    assume z hz;
    have hzc : π (z ∈ rcomp (converse r) r) { refine ind_eq hcomp (λ w, z ∈ w) hz };
    have hzS : π (z ∈ Sigma (domain r) (λ _, range (converse r)))
      { refine CollectD1 z (Sigma (domain r) (λ _, range (converse r)))
          (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ r ∧ Pair y (snd p) ∈ converse r) hzc };
    refine ∃ₑ (SigmaE z (domain r) (λ _, range (converse r)) hzS) _; assume a haz;
    refine ∃ₑ (∧ₑ₂ haz) _; assume b hbz;
    have hzeq : π (z = Pair a b) { refine ∧ₑ₂ hbz };
    have hab_r : π (Pair a b ∈ r) { refine ind_eq (eq_sym hzeq) (λ w, w ∈ r) hz };
    have haA : π (a ∈ A) { refine ind_eq (eq_sym hdom) (λ w, a ∈ w) (domainI a b r hab_r) };
    have hbA : π (b ∈ A)
      { refine ind_eq (eq_sym hdom) (λ w, b ∈ w) (domainI b a r (hsym a b hab_r)) };
    refine ind_eq hzeq (λ w, w ∈ Sigma A (λ _, A)) (SigmaI a b A (λ _, A) haA hbA) };
  refine ∧ᵢ hsub (∧ᵢ hrefl (∧ᵢ hsym htrans))
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
opaque symbol Union_quotient (A r : τ ι) :
  π (equiv A r) → π (Union (quotient A r) = A) ≔
begin
  assume A r heq;
  have htype : π (r ⊆ Sigma A (λ _, A)) { refine equiv_type A r heq };
  refine subset_antisym (Union (quotient A r)) A _ _
  { // ⋃(A//r) ⊆ A: each class element is related to a class rep, hence in A.
    assume y hy;
    refine ∃ₑ (UnionE y (quotient A r) hy) _; assume X hX;
    refine ∃ₑ (quotientE X A r (∧ₑ₁ hX)) _; assume x hxX;
    have hXeq : π (X = rel_image_sing r x) { refine ∧ₑ₂ hxX };
    have hyRel : π (y ∈ rel_image_sing r x)
      { refine ind_eq (eq_sym hXeq) (λ w, y ∈ w) (∧ₑ₂ hX) };
    have hSig : π (Pair x y ∈ Sigma A (λ _, A))
      { refine htype (Pair x y) (rel_image_singD x y r hyRel) };
    refine ind_eq (eq_sym (snd_conv x y)) (λ w, w ∈ A) (SigmaD2 (Pair x y) A (λ _, A) hSig) }
  { // A ⊆ ⋃(A//r): x is in its own class, which is in the quotient.
    assume x hxA;
    refine UnionI x (rel_image_sing r x) (quotient A r)
      (equiv_class_self A x r heq hxA) (quotientI x A r hxA) }
end;

// quotient_disj: equiv(A,r) → X ∈ A//r → Y ∈ A//r → X = Y ∨ X ∩ Y ⊆ empty
opaque symbol quotient_disj (A r X Y : τ ι) :
  π (equiv A r) → π (X ∈ quotient A r) → π (Y ∈ quotient A r) →
  π (X = Y ∨ Int X Y ⊆ empty) ≔
begin
  assume A r X Y heq hX hY;
  refine ∃ₑ (quotientE X A r hX) _; assume a haX;
  have hXeq : π (X = rel_image_sing r a) { refine ∧ₑ₂ haX };
  refine ∃ₑ (quotientE Y A r hY) _; assume b hbY;
  have hYeq : π (Y = rel_image_sing r b) { refine ∧ₑ₂ hbY };
  refine ∨ₑ (em (Int X Y = empty)) _ _
  { // disjoint
    assume hempty; refine ∨ᵢ₂ _; rewrite hempty; refine subset_refl empty }
  { // a common element forces the two classes (hence X, Y) to coincide.
    assume hne; refine ∨ᵢ₁ _;
    refine not_emptyE (Int X Y) (X = Y) hne _;
    assume z hz;
    have hz2 : π (z ∈ Int (rel_image_sing r a) (rel_image_sing r b))
      { rewrite left hXeq; rewrite left hYeq; refine hz };
    have hcleq : π (rel_image_sing r a = rel_image_sing r b)
      { refine equiv_class_eq A a b r heq (equiv_class_nondisjoint A a b z r heq hz2) };
    rewrite hXeq; rewrite hYeq; refine hcleq }
end;

// ===========================================================================
// Section: Defining Unary Operations upon Equivalence Classes
// ===========================================================================

// UN_equiv_class: equiv(A,r) → congruent(r,b) → a ∈ A →
//   ⋃{b(x) | x ∈ r``{a}} = b(a)
// Note: ⋃{b(x) | x ∈ S} is Union(RepFun(S, b))
opaque symbol UN_equiv_class (A r : τ ι) (b : τ ι → τ ι) (a : τ ι) :
  π (equiv A r) → π (congruent r b) → π (a ∈ A) →
  π (Union (RepFun (rel_image_sing r a) b) = b a) ≔
begin
  assume A r b a heq hcong haA;
  refine subset_antisym (Union (RepFun (rel_image_sing r a) b)) (b a) _ _
  { // every b(x) for x in the class equals b(a) (congruence), so the union ⊆ b(a).
    assume y hy;
    refine ∃ₑ (UnionE y (RepFun (rel_image_sing r a) b) hy) _; assume S hS;
    refine ∃ₑ (∧ₑ₁ (RepFun_iff S (rel_image_sing r a) b) (∧ₑ₁ hS)) _; assume x hx;
    have hSeq : π (S = b x) { refine ∧ₑ₂ hx };
    have hbeq : π (b a = b x) { refine hcong a x (rel_image_singD a x r (∧ₑ₁ hx)) };
    have hy_bx : π (y ∈ b x) { refine ind_eq (eq_sym hSeq) (λ w, y ∈ w) (∧ₑ₂ hS) };
    refine ind_eq hbeq (λ w, y ∈ w) hy_bx }
  { // a is in its own class, so b(a) is one of the union'd sets.
    assume y hy;
    refine UnionI y (b a) (RepFun (rel_image_sing r a) b) hy
      (RepFunI a (rel_image_sing r a) b (equiv_class_self A a r heq haA)) }
end;

// UN_equiv_class_type: equiv(A,r) → congruent(r,b) → X ∈ A//r →
//   (∀x∈A. b(x) ∈ B) → ⋃{b(x) | x ∈ X} ∈ B
opaque symbol UN_equiv_class_type (A r B : τ ι) (b : τ ι → τ ι) (X : τ ι) :
  π (equiv A r) → π (congruent r b) → π (X ∈ quotient A r) →
  (Π (x : τ ι), π (x ∈ A) → π (b x ∈ B)) →
  π (Union (RepFun X b) ∈ B) ≔
begin
  assume A r B b X heq hcong hX hbB;
  refine ∃ₑ (quotientE X A r hX) _; assume a haX;
  have haA : π (a ∈ A) { refine ∧ₑ₁ haX };
  have hval : π (Union (RepFun X b) = b a)
    { rewrite (∧ₑ₂ haX); refine UN_equiv_class A r b a heq hcong haA };
  rewrite hval;
  refine hbB a haA
end;

// UN_equiv_class_inject: equiv(A,r) → congruent(r,b) →
//   ⋃{b(x)|x∈X} = ⋃{b(y)|y∈Y} → X ∈ A//r → Y ∈ A//r →
//   (∀x y. x∈A → y∈A → b(x)=b(y) → Pair(x,y)∈r) → X = Y
opaque symbol UN_equiv_class_inject (A r : τ ι) (b : τ ι → τ ι) (X Y : τ ι) :
  π (equiv A r) → π (congruent r b) →
  π (Union (RepFun X b) = Union (RepFun Y b)) →
  π (X ∈ quotient A r) → π (Y ∈ quotient A r) →
  (Π (x : τ ι), Π (y : τ ι), π (x ∈ A) → π (y ∈ A) → π (b x = b y) → π (Pair x y ∈ r)) →
  π (X = Y) ≔
begin
  assume A r b X Y heq hcong hunion hXq hYq hinj;
  refine ∃ₑ (quotientE X A r hXq) _; assume a haX;
  have haA : π (a ∈ A) { refine ∧ₑ₁ haX };
  have hXeq : π (X = rel_image_sing r a) { refine ∧ₑ₂ haX };
  refine ∃ₑ (quotientE Y A r hYq) _; assume c hcY;
  have hcA : π (c ∈ A) { refine ∧ₑ₁ hcY };
  have hYeq : π (Y = rel_image_sing r c) { refine ∧ₑ₂ hcY };
  have hXval : π (Union (RepFun X b) = b a)
    { rewrite hXeq; refine UN_equiv_class A r b a heq hcong haA };
  have hYval : π (Union (RepFun Y b) = b c)
    { rewrite hYeq; refine UN_equiv_class A r b c heq hcong hcA };
  // b a = ⋃(X.b) = ⋃(Y.b) = b c, so a and c are related, hence the classes coincide.
  have hbac : π (b a = b c)
    { have h1 : π (Union (RepFun X b) = b c) { rewrite hunion; refine hYval };
      rewrite left hXval; refine h1 };
  have hcleq : π (rel_image_sing r a = rel_image_sing r c)
    { refine equiv_class_eq A a c r heq (hinj a c haA hcA hbac) };
  rewrite hXeq; rewrite hYeq; refine hcleq
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
opaque symbol congruent2_implies_congruent_UN (A1 A2 r1 r2 : τ ι)
  (b : τ ι → τ ι → τ ι) (a : τ ι) :
  π (equiv A1 r1) → π (equiv A2 r2) → π (congruent2 r1 r2 b) → π (a ∈ A2) →
  π (congruent r1 (λ x1, Union (RepFun (rel_image_sing r2 a) (λ x2, b x1 x2)))) ≔
begin
  assume A1 A2 r1 r2 b a heq1 heq2 hcong2 haA2;
  assume y z hyz;
  // y, z ∈ A1.
  have hyzS : π (Pair y z ∈ Sigma A1 (λ _, A1)) { refine equiv_type A1 r1 heq1 (Pair y z) hyz };
  have hyA : π (y ∈ A1)
    { refine ind_eq (eq_sym (fst_conv y z)) (λ t, t ∈ A1)
        (SigmaD1 (Pair y z) A1 (λ _, A1) hyzS) };
  have hzA : π (z ∈ A1)
    { refine ind_eq (eq_sym (snd_conv y z)) (λ t, t ∈ A1)
        (SigmaD2 (Pair y z) A1 (λ _, A1) hyzS) };
  // Each inner union collapses (UN_equiv_class): ⋃x2∈r2``{a}. b(y,x2) = b(y,a).
  have hfy : π (Union (RepFun (rel_image_sing r2 a) (λ x2, b y x2)) = b y a)
    { refine UN_equiv_class A2 r2 (λ x2, b y x2) a heq2
        (congruent2_implies_congruent A1 r1 r2 b y heq1 hcong2 hyA) haA2 };
  have hfz : π (Union (RepFun (rel_image_sing r2 a) (λ x2, b z x2)) = b z a)
    { refine UN_equiv_class A2 r2 (λ x2, b z x2) a heq2
        (congruent2_implies_congruent A1 r1 r2 b z heq1 hcong2 hzA) haA2 };
  // b(y,a) = b(z,a) by congruent2 with ⟨a,a⟩∈r2 (reflexivity).
  have hbeq : π (b y a = b z a)
    { refine hcong2 y z a a hyz (equiv_refl A2 r2 heq2 a haA2) };
  rewrite hfy; rewrite hfz; refine hbeq
end;

// UN_equiv_class2: equiv(A1,r1) → equiv(A2,r2) → congruent2(r1,r2,b) →
//   a1 ∈ A1 → a2 ∈ A2 →
//   ⋃{⋃{b(x1,x2) | x2 ∈ r2``{a2}} | x1 ∈ r1``{a1}} = b(a1,a2)
opaque symbol UN_equiv_class2 (A1 A2 r1 r2 : τ ι)
  (b : τ ι → τ ι → τ ι) (a1 a2 : τ ι) :
  π (equiv A1 r1) → π (equiv A2 r2) → π (congruent2 r1 r2 b) →
  π (a1 ∈ A1) → π (a2 ∈ A2) →
  π (Union (RepFun (rel_image_sing r1 a1) (λ x1,
    Union (RepFun (rel_image_sing r2 a2) (λ x2, b x1 x2)))) = b a1 a2) ≔
begin
  assume A1 A2 r1 r2 b a1 a2 heq1 heq2 hcong2 ha1A1 ha2A2;
  // Collapse the outer union (function congruent on r1), then the inner one.
  have houter : π (Union (RepFun (rel_image_sing r1 a1)
                     (λ x1, Union (RepFun (rel_image_sing r2 a2) (λ x2, b x1 x2))))
                   = Union (RepFun (rel_image_sing r2 a2) (λ x2, b a1 x2)))
    { refine UN_equiv_class A1 r1
        (λ x1, Union (RepFun (rel_image_sing r2 a2) (λ x2, b x1 x2))) a1 heq1
        (congruent2_implies_congruent_UN A1 A2 r1 r2 b a2 heq1 heq2 hcong2 ha2A2) ha1A1 };
  rewrite houter;
  refine UN_equiv_class A2 r2 (λ x2, b a1 x2) a2 heq2
    (congruent2_implies_congruent A1 r1 r2 b a1 heq1 hcong2 ha1A1) ha2A2
end;

// UN_equiv_class_type2: equiv(A,r) → congruent2(r,r,b) →
//   X1 ∈ A//r → X2 ∈ A//r →
//   (∀x1∈A. ∀x2∈A. b(x1,x2) ∈ B) →
//   ⋃{⋃{b(x1,x2)|x2∈X2}|x1∈X1} ∈ B
opaque symbol UN_equiv_class_type2 (A r B X1 X2 : τ ι)
  (b : τ ι → τ ι → τ ι) :
  π (equiv A r) → π (congruent2 r r b) →
  π (X1 ∈ quotient A r) → π (X2 ∈ quotient A r) →
  (Π (x1 : τ ι), Π (x2 : τ ι), π (x1 ∈ A) → π (x2 ∈ A) → π (b x1 x2 ∈ B)) →
  π (Union (RepFun X1 (λ x1, Union (RepFun X2 (λ x2, b x1 x2)))) ∈ B) ≔
begin
  assume A r B X1 X2 b heq hcong2 hX1 hX2 hbB;
  refine ∃ₑ (quotientE X1 A r hX1) _; assume a1 ha1X;
  have ha1A : π (a1 ∈ A) { refine ∧ₑ₁ ha1X };
  refine ∃ₑ (quotientE X2 A r hX2) _; assume a2 ha2X;
  have ha2A : π (a2 ∈ A) { refine ∧ₑ₁ ha2X };
  have hval : π (Union (RepFun X1 (λ x1, Union (RepFun X2 (λ x2, b x1 x2)))) = b a1 a2)
    { rewrite (∧ₑ₂ ha1X); rewrite (∧ₑ₂ ha2X);
      refine UN_equiv_class2 A A r r b a1 a2 heq heq hcong2 ha1A ha2A };
  rewrite hval;
  refine hbB a1 a2 ha1A ha2A
end;

// congruent2I: equiv(A1,r1) → equiv(A2,r2) →
//   (∀w∈A2. ∀y z. Pair(y,z) ∈ r1 → b(y,w) = b(z,w)) →
//   (∀w∈A1. ∀y z. Pair(y,z) ∈ r2 → b(w,y) = b(w,z)) →
//   congruent2(r1,r2,b)
opaque symbol congruent2I (A1 A2 r1 r2 : τ ι) (b : τ ι → τ ι → τ ι) :
  π (equiv A1 r1) → π (equiv A2 r2) →
  (Π (w : τ ι), π (w ∈ A2) → Π (y : τ ι), Π (z : τ ι), π (Pair y z ∈ r1) → π (b y w = b z w)) →
  (Π (w : τ ι), π (w ∈ A1) → Π (y : τ ι), Π (z : τ ι), π (Pair y z ∈ r2) → π (b w y = b w z)) →
  π (congruent2 r1 r2 b) ≔
begin
  assume A1 A2 r1 r2 b heq1 heq2 hleft hright;
  assume y1 z1 y2 z2 h1 h2;
  // z1 ∈ A1 and y2 ∈ A2 (fields of the equivalence relations).
  have hz1A : π (z1 ∈ A1)
    { refine ind_eq (eq_sym (snd_conv y1 z1)) (λ w, w ∈ A1)
        (SigmaD2 (Pair y1 z1) A1 (λ _, A1) (equiv_type A1 r1 heq1 (Pair y1 z1) h1)) };
  have hy2A : π (y2 ∈ A2)
    { refine ind_eq (eq_sym (fst_conv y2 z2)) (λ w, w ∈ A2)
        (SigmaD1 (Pair y2 z2) A2 (λ _, A2) (equiv_type A2 r2 heq2 (Pair y2 z2) h2)) };
  // b y1 y2 = b z1 y2 (left congruence) = b z1 z2 (right congruence).
  have hstep1 : π (b y1 y2 = b z1 y2) { refine hleft y2 hy2A y1 z1 h1 };
  rewrite hstep1; refine hright z1 hz1A y2 z2 h2
end;

// congruent2_commuteI: equiv(A,r) →
//   (∀y z. y∈A → z∈A → b(y,z) = b(z,y)) →
//   (∀w y z. w∈A → Pair(y,z)∈r → b(w,y) = b(w,z)) →
//   congruent2(r,r,b)
opaque symbol congruent2_commuteI (A r : τ ι) (b : τ ι → τ ι → τ ι) :
  π (equiv A r) →
  (Π (y : τ ι), Π (z : τ ι), π (y ∈ A) → π (z ∈ A) → π (b y z = b z y)) →
  (Π (w : τ ι), Π (y : τ ι), Π (z : τ ι), π (w ∈ A) → π (Pair y z ∈ r) → π (b w y = b w z)) →
  π (congruent2 r r b) ≔
begin
  assume A r b heq hcomm hcong;
  refine congruent2I A A r r b heq heq _ _
  { // left congruence from commutativity + right congruence.
    assume w hwA y z hyz;
    have hyzS : π (Pair y z ∈ Sigma A (λ _, A)) { refine equiv_type A r heq (Pair y z) hyz };
    have hyA : π (y ∈ A)
      { refine ind_eq (eq_sym (fst_conv y z)) (λ t, t ∈ A)
          (SigmaD1 (Pair y z) A (λ _, A) hyzS) };
    have hzA : π (z ∈ A)
      { refine ind_eq (eq_sym (snd_conv y z)) (λ t, t ∈ A)
          (SigmaD2 (Pair y z) A (λ _, A) hyzS) };
    // b y w = b w y = b w z = b z w
    rewrite (hcomm y w hyA hwA);
    rewrite (hcong w y z hwA hyz);
    refine hcomm w z hwA hzA }
  { assume w hwA y z hyz; refine hcong w y z hwA hyz }
end;

// congruent_commuteI: equiv(A,r) → Z ∈ A//r →
//   (∀w∈A. congruent(r, λz. b(w,z))) →
//   (∀x y. x∈A → y∈A → b(y,x) = b(x,y)) →
//   congruent(r, λw. ⋃{b(w,z) | z ∈ Z})
opaque symbol congruent_commuteI (A r Z : τ ι) (b : τ ι → τ ι → τ ι) :
  π (equiv A r) → π (Z ∈ quotient A r) →
  (Π (w : τ ι), π (w ∈ A) → π (congruent r (λ z, b w z))) →
  (Π (x : τ ι), Π (y : τ ι), π (x ∈ A) → π (y ∈ A) → π (b y x = b x y)) →
  π (congruent r (λ w, Union (RepFun Z (λ z, b w z)))) ≔
begin
  assume A r Z b heq hZ hcongw hcomm;
  refine ∃ₑ (quotientE Z A r hZ) _; assume a haZ;
  have haA : π (a ∈ A) { refine ∧ₑ₁ haZ };
  have hZeq : π (Z = rel_image_sing r a) { refine ∧ₑ₂ haZ };
  assume y1 y2 h12;
  have h12S : π (Pair y1 y2 ∈ Sigma A (λ _, A)) { refine equiv_type A r heq (Pair y1 y2) h12 };
  have hy1A : π (y1 ∈ A)
    { refine ind_eq (eq_sym (fst_conv y1 y2)) (λ t, t ∈ A)
        (SigmaD1 (Pair y1 y2) A (λ _, A) h12S) };
  have hy2A : π (y2 ∈ A)
    { refine ind_eq (eq_sym (snd_conv y1 y2)) (λ t, t ∈ A)
        (SigmaD2 (Pair y1 y2) A (λ _, A) h12S) };
  // ⋃z∈Z. b(w,z) collapses to b(w,a); reduce both sides.
  have hf1 : π (Union (RepFun Z (λ z, b y1 z)) = b y1 a)
    { rewrite hZeq; refine UN_equiv_class A r (λ z, b y1 z) a heq (hcongw y1 hy1A) haA };
  have hf2 : π (Union (RepFun Z (λ z, b y2 z)) = b y2 a)
    { rewrite hZeq; refine UN_equiv_class A r (λ z, b y2 z) a heq (hcongw y2 hy2A) haA };
  // b(y1,a) = b(a,y1) = b(a,y2) = b(y2,a) via commutativity + congruence of b(a,·).
  have hb : π (b y1 a = b y2 a)
    { have e2 : π (b a y1 = b a y2) { refine hcongw a haA y1 y2 h12 };
      rewrite (hcomm a y1 haA hy1A);
      rewrite e2;
      refine hcomm y2 a hy2A haA };
  rewrite hf1; rewrite hf2; refine hb
end;
