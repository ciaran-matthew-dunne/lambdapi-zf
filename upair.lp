// upair: Unordered pairs, basic set operations, and membership lemmas
//
// Isabelle source: upair.thy (+ some definitions from ZF_Base.thy)
// Defines: Collect, RepFun, Upair, Un, Int, Inter, Diff, cons, succ,
//          singleton, The, If
// Proves: membership lemmas (iff, intro, elim rules)

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt
             Stdlib.Epsilon;
require open ZF.ZF_Base;

// ===========================================================================
// Separation (Collect) — {x ∈ A | P(x)}
// ===========================================================================

// Collect(A,P) = PrimReplace(A, λ x y. x = y ∧ P(x))
symbol Collect (A : τ ι) (P : τ ι → Prop) : τ ι ≔
  PrimReplace A (λ x y, x = y ∧ P x);

// Functionality of the Collect predicate
opaque symbol Collect_func (A : τ ι) (P : τ ι → Prop) :
  π (Ball A (λ x, `∀ (y : τ ι), `∀ (z : τ ι),
     (x = y ∧ P x) ⇒ ((x = z ∧ P x) ⇒ y = z))) ≔
begin
  assume A P x hxA y z hyz hxz;
  have hy : π (x = y) { refine ∧ₑ₁ hyz };
  have hz : π (x = z) { refine ∧ₑ₁ hxz };
  rewrite left hy; rewrite left hz; reflexivity
end;

// Collect membership: c ∈ Collect(A,P) ⟷ c ∈ A ∧ P(c)
opaque symbol Collect_iff (c A : τ ι) (P : τ ι → Prop) :
  π ((c ∈ Collect A P) ⇔ (c ∈ A ∧ P c)) ≔
begin
  assume c A P;
  have rep : π (`∀ (b : τ ι), (b ∈ PrimReplace A (λ x y, x = y ∧ P x))
               ⇔ Bex A (λ x, x = b ∧ P x))
    { refine replacement A (λ x y, x = y ∧ P x) (Collect_func A P) };
  apply ∧ᵢ
  { // forward: c ∈ Collect A P → c ∈ A ∧ P c
    assume hc;
    have hbex : π (Bex A (λ x, x = c ∧ P x)) { refine ∧ₑ₁ (rep c) hc };
    // hbex: ∃ x ∈ A. x = c ∧ P x
    refine ∃ₑ hbex _;
    assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    have hxc_Px : π (x = c ∧ P x) { refine ∧ₑ₂ hx };
    have hxc : π (x = c) { refine ∧ₑ₁ hxc_Px };
    have hPx : π (P x) { refine ∧ₑ₂ hxc_Px };
    apply ∧ᵢ
    { rewrite left hxc; apply hxA }
    { rewrite left hxc; apply hPx } }
  { // backward: c ∈ A ∧ P c → c ∈ Collect A P
    assume hcA;
    have hcInA : π (c ∈ A) { refine ∧ₑ₁ hcA };
    have hPc : π (P c) { refine ∧ₑ₂ hcA };
    refine ∧ₑ₂ (rep c) _;
    refine ∃ᵢ c _;
    apply ∧ᵢ hcInA (∧ᵢ (eq_refl c) hPc) }
end;

// Collect intro
opaque symbol CollectI (c A : τ ι) (P : τ ι → Prop) :
  π (c ∈ A) → π (P c) → π (c ∈ Collect A P) ≔
begin
  assume c A P hc hPc;
  refine ∧ₑ₂ (Collect_iff c A P) _;
  apply ∧ᵢ hc hPc
end;

// Collect elim: c ∈ A
opaque symbol CollectD1 (c A : τ ι) (P : τ ι → Prop) :
  π (c ∈ Collect A P) → π (c ∈ A) ≔
begin
  assume c A P h;
  refine ∧ₑ₁ (∧ₑ₁ (Collect_iff c A P) h)
end;

// Collect elim: P(c)
opaque symbol CollectD2 (c A : τ ι) (P : τ ι → Prop) :
  π (c ∈ Collect A P) → π (P c) ≔
begin
  assume c A P h;
  refine ∧ₑ₂ (∧ₑ₁ (Collect_iff c A P) h)
end;

// ===========================================================================
// Functional image (RepFun) — {f(x) | x ∈ A}
// ===========================================================================

// RepFun(A,f) = PrimReplace(A, λ x y. y = f(x))
symbol RepFun (A : τ ι) (f : τ ι → τ ι) : τ ι ≔
  PrimReplace A (λ x y, y = f x);

// Functionality of the RepFun predicate
opaque symbol RepFun_func (A : τ ι) (f : τ ι → τ ι) :
  π (Ball A (λ x, `∀ (y : τ ι), `∀ (z : τ ι),
     y = f x ⇒ (z = f x ⇒ y = z))) ≔
begin
  assume A f x hxA y z hy hz;
  rewrite hy; symmetry; apply hz
end;

// RepFun membership: c ∈ RepFun(A,f) ⟷ ∃x∈A. c = f(x)
opaque symbol RepFun_iff (c A : τ ι) (f : τ ι → τ ι) :
  π ((c ∈ RepFun A f) ⇔ Bex A (λ x, c = f x)) ≔
begin
  assume c A f;
  have rep : π (`∀ (b : τ ι), (b ∈ PrimReplace A (λ x y, y = f x))
               ⇔ Bex A (λ x, b = f x))
    { refine replacement A (λ x y, y = f x) (RepFun_func A f) };
  apply rep c
end;

// RepFun intro
opaque symbol RepFunI (a A : τ ι) (f : τ ι → τ ι) :
  π (a ∈ A) → π (f a ∈ RepFun A f) ≔
begin
  assume a A f ha;
  refine ∧ₑ₂ (RepFun_iff (f a) A f) _;
  refine ∃ᵢ a _;
  apply ∧ᵢ ha (eq_refl (f a))
end;

// ===========================================================================
// Upair — unordered pairs {a, b}
// ===========================================================================

// Upair(a,b) = RepFun(Pow(Pow(empty)), λ x. if x = empty then a else b)
// We need a conditional on sets. Since we don't have if-then-else at the
// set level yet, we use the Isabelle encoding directly:
// Upair(a,b) = {y | x ∈ Pow(Pow(empty)), (x = empty ∧ y = a) ∨ (x = Pow(empty) ∧ y = b)}
// This is PrimReplace(Pow(Pow(empty)), λ x y. (x = empty ∧ y = a) ∨ (x = Pow(empty) ∧ y = b))

symbol Upair (a b : τ ι) : τ ι ≔
  PrimReplace (Pow (Pow empty))
    (λ x y, (x = empty ∧ y = a) ∨ (x = Pow empty ∧ y = b));

// Key facts about Pow(Pow(empty)):
// - empty ∈ Pow(Pow(empty))         [since empty ⊆ Pow(empty)]
// - Pow(empty) ∈ Pow(Pow(empty))    [since Pow(empty) ⊆ Pow(empty)]
// - empty ≠ Pow(empty)              [since empty ∈ Pow(empty)]

// empty ⊆ anything (already proved as empty_subset)
// empty ∈ Pow(anything)
opaque symbol empty_in_Pow (A : τ ι) : π (empty ∈ Pow A) ≔
begin
  assume A;
  refine PowI empty A (empty_subset A)
end;

// Pow(empty) ⊆ Pow(empty) (reflexive)
// so Pow(empty) ∈ Pow(Pow(empty))
opaque symbol Pow_empty_in_PowPow : π (Pow empty ∈ Pow (Pow empty)) ≔
begin
  refine PowI (Pow empty) (Pow empty) (subset_refl (Pow empty))
end;

// empty ∈ Pow(Pow(empty))
opaque symbol empty_in_PowPow : π (empty ∈ Pow (Pow empty)) ≔
begin
  refine empty_in_Pow (Pow empty)
end;

// empty ∈ Pow(empty)
opaque symbol empty_in_Pow_empty : π (empty ∈ Pow empty) ≔
begin
  refine empty_in_Pow empty
end;

// empty ≠ Pow(empty)
opaque symbol empty_ne_Pow_empty : π (empty ≠ Pow empty) ≔
begin
  assume heq;
  // If empty = Pow(empty), then transport empty ∈ Pow(empty) along heq
  have h : π (empty ∈ empty)
    { refine ind_eq heq (λ A, empty ∈ A) empty_in_Pow_empty };
  refine emptyE empty h
end;

// Functionality of the Upair predicate
opaque symbol Upair_func (a b : τ ι) :
  π (Ball (Pow (Pow empty)) (λ x,
     `∀ (y : τ ι), `∀ (z : τ ι),
     ((x = empty ∧ y = a) ∨ (x = Pow empty ∧ y = b))
     ⇒ (((x = empty ∧ z = a) ∨ (x = Pow empty ∧ z = b))
     ⇒ y = z))) ≔
begin
  assume a b x hx y z hy hz;
  refine ∨ₑ hy _ _
  { assume hya;
    have hxe : π (x = empty) { refine ∧ₑ₁ hya };
    have hya2 : π (y = a) { refine ∧ₑ₂ hya };
    refine ∨ₑ hz _ _
    { assume hza;
      rewrite hya2; symmetry; refine ∧ₑ₂ hza }
    { assume hzb;
      // x = empty and x = Pow(empty) → contradiction
      have hxp : π (x = Pow empty) { refine ∧ₑ₁ hzb };
      have habs : π (empty = Pow empty)
        { refine ind_eq (eq_sym hxe) (λ z, z = Pow empty) hxp };
      refine ⊥ₑ (empty_ne_Pow_empty habs) } }
  { assume hyb;
    have hxp : π (x = Pow empty) { refine ∧ₑ₁ hyb };
    have hyb2 : π (y = b) { refine ∧ₑ₂ hyb };
    refine ∨ₑ hz _ _
    { assume hza;
      have hxe : π (x = empty) { refine ∧ₑ₁ hza };
      have habs : π (empty = Pow empty)
        { refine ind_eq (eq_sym hxp) (λ z, empty = z) (eq_sym hxe) };
      refine ⊥ₑ (empty_ne_Pow_empty habs) }
    { assume hzb;
      rewrite hyb2; symmetry; refine ∧ₑ₂ hzb } }
end;

// Upair membership: c ∈ Upair(a,b) ⟷ (c = a ∨ c = b)
opaque symbol Upair_iff (c a b : τ ι) :
  π ((c ∈ Upair a b) ⇔ (c = a ∨ c = b)) ≔
begin
  assume c a b;
  have rep : π (`∀ (d : τ ι),
    (d ∈ PrimReplace (Pow (Pow empty))
      (λ x y, (x = empty ∧ y = a) ∨ (x = Pow empty ∧ y = b)))
    ⇔ Bex (Pow (Pow empty))
      (λ x, (x = empty ∧ d = a) ∨ (x = Pow empty ∧ d = b)))
    { refine replacement (Pow (Pow empty))
        (λ x y, (x = empty ∧ y = a) ∨ (x = Pow empty ∧ y = b))
        (Upair_func a b) };
  apply ∧ᵢ
  { // forward: c ∈ Upair a b → c = a ∨ c = b
    assume hc;
    have hbex : π (Bex (Pow (Pow empty))
        (λ x, (x = empty ∧ c = a) ∨ (x = Pow empty ∧ c = b)))
      { refine ∧ₑ₁ (rep c) hc };
    refine ∃ₑ hbex _;
    assume x hx;
    have hxin : π (x ∈ Pow (Pow empty)) { refine ∧ₑ₁ hx };
    have hdisj : π ((x = empty ∧ c = a) ∨ (x = Pow empty ∧ c = b))
      { refine ∧ₑ₂ hx };
    refine ∨ₑ hdisj _ _
    { assume h; refine ∨ᵢ₁ (∧ₑ₂ h) }
    { assume h; refine ∨ᵢ₂ (∧ₑ₂ h) } }
  { // backward: c = a ∨ c = b → c ∈ Upair a b
    assume hdisj;
    refine ∧ₑ₂ (rep c) _;
    refine ∨ₑ hdisj _ _
    { assume hca;
      refine ∃ᵢ empty _;
      apply ∧ᵢ empty_in_PowPow (∨ᵢ₁ (∧ᵢ (eq_refl empty) hca)) }
    { assume hcb;
      refine ∃ᵢ (Pow empty) _;
      apply ∧ᵢ Pow_empty_in_PowPow (∨ᵢ₂ (∧ᵢ (eq_refl (Pow empty)) hcb)) } }
end;

// Upair intro/elim
opaque symbol UpairI1 (a b : τ ι) : π (a ∈ Upair a b) ≔
begin
  assume a b;
  refine ∧ₑ₂ (Upair_iff a a b) _;
  refine ∨ᵢ₁ (eq_refl a)
end;

opaque symbol UpairI2 (a b : τ ι) : π (b ∈ Upair a b) ≔
begin
  assume a b;
  refine ∧ₑ₂ (Upair_iff b a b) _;
  refine ∨ᵢ₂ (eq_refl b)
end;

opaque symbol UpairE (c a b : τ ι) :
  π (c ∈ Upair a b) → π (c = a ∨ c = b) ≔
begin
  assume c a b h;
  refine ∧ₑ₁ (Upair_iff c a b) h
end;

// ===========================================================================
// Binary union — A ∪ B = ⋃(Upair(A,B))
// ===========================================================================

symbol Un (A B : τ ι) : τ ι ≔ Union (Upair A B);
notation Un infix left 20;

// Un membership: c ∈ A ∪ B ⟷ c ∈ A ∨ c ∈ B
opaque symbol Un_iff (c A B : τ ι) :
  π ((c ∈ Un A B) ⇔ (c ∈ A ∨ c ∈ B)) ≔
begin
  assume c A B;
  apply ∧ᵢ
  { // forward
    assume hc;
    have hbex : π (Bex (Upair A B) (λ D, c ∈ D))
      { refine UnionE c (Upair A B) hc };
    refine ∃ₑ hbex _;
    assume D hD;
    have hDin : π (D ∈ Upair A B) { refine ∧ₑ₁ hD };
    have hcD : π (c ∈ D) { refine ∧ₑ₂ hD };
    have hdisj : π (D = A ∨ D = B) { refine UpairE D A B hDin };
    refine ∨ₑ hdisj _ _
    { assume hDA; rewrite left hDA; refine ∨ᵢ₁ hcD }
    { assume hDB; rewrite left hDB; refine ∨ᵢ₂ hcD } }
  { // backward
    assume hdisj;
    refine ∨ₑ hdisj _ _
    { assume hcA; refine UnionI c A (Upair A B) hcA (UpairI1 A B) }
    { assume hcB; refine UnionI c B (Upair A B) hcB (UpairI2 A B) } }
end;

// Un intro/elim
opaque symbol UnI1 (c A B : τ ι) : π (c ∈ A) → π (c ∈ Un A B) ≔
begin
  assume c A B h;
  refine ∧ₑ₂ (Un_iff c A B) (∨ᵢ₁ h)
end;

opaque symbol UnI2 (c A B : τ ι) : π (c ∈ B) → π (c ∈ Un A B) ≔
begin
  assume c A B h;
  refine ∧ₑ₂ (Un_iff c A B) (∨ᵢ₂ h)
end;

opaque symbol UnE (c A B : τ ι) :
  π (c ∈ Un A B) → π (c ∈ A ∨ c ∈ B) ≔
begin
  assume c A B h;
  refine ∧ₑ₁ (Un_iff c A B) h
end;

// ===========================================================================
// General intersection — ⋂(A) = {x ∈ ⋃A | ∀y∈A. x∈y}
// ===========================================================================

symbol Inter (A : τ ι) : τ ι ≔
  Collect (Union A) (λ x, Ball A (λ y, x ∈ y));

// ===========================================================================
// Binary intersection — A ∩ B
// ===========================================================================

symbol Int (A B : τ ι) : τ ι ≔ Inter (Upair A B);
notation Int infix left 20;

// Int membership: c ∈ A ∩ B ⟷ c ∈ A ∧ c ∈ B
opaque symbol Int_iff (c A B : τ ι) :
  π ((c ∈ Int A B) ⇔ (c ∈ A ∧ c ∈ B)) ≔
begin
  assume c A B;
  // Int A B = Collect (Union (Upair A B)) (λ x, Ball (Upair A B) (λ y, x ∈ y))
  apply ∧ᵢ
  { assume hc;
    // hc : c ∈ Collect (Union (Upair A B)) (λ x, Ball (Upair A B) (λ y, x ∈ y))
    have hball : π (Ball (Upair A B) (λ y, c ∈ y))
      { refine CollectD2 c (Union (Upair A B)) (λ x, Ball (Upair A B) (λ y, x ∈ y)) hc };
    // hball: ∀ y ∈ Upair A B. c ∈ y
    apply ∧ᵢ
    { refine hball A (UpairI1 A B) }
    { refine hball B (UpairI2 A B) } }
  { assume hcAB;
    have hcA : π (c ∈ A) { refine ∧ₑ₁ hcAB };
    have hcB : π (c ∈ B) { refine ∧ₑ₂ hcAB };
    // Need: c ∈ Collect (Union (Upair A B)) (λ x, Ball (Upair A B) (λ y, x ∈ y))
    refine CollectI c (Union (Upair A B)) (λ x, Ball (Upair A B) (λ y, x ∈ y)) _ _
    { // c ∈ Union (Upair A B)
      refine UnionI c A (Upair A B) hcA (UpairI1 A B) }
    { // Ball (Upair A B) (λ y, c ∈ y)
      assume y hy;
      have hdisj : π (y = A ∨ y = B) { refine UpairE y A B hy };
      refine ∨ₑ hdisj _ _
      { assume hyA; rewrite hyA; apply hcA }
      { assume hyB; rewrite hyB; apply hcB } } }
end;

// Int intro/elim
opaque symbol IntI (c A B : τ ι) :
  π (c ∈ A) → π (c ∈ B) → π (c ∈ Int A B) ≔
begin
  assume c A B hA hB;
  refine ∧ₑ₂ (Int_iff c A B) (∧ᵢ hA hB)
end;

opaque symbol IntD1 (c A B : τ ι) :
  π (c ∈ Int A B) → π (c ∈ A) ≔
begin
  assume c A B h;
  refine ∧ₑ₁ (∧ₑ₁ (Int_iff c A B) h)
end;

opaque symbol IntD2 (c A B : τ ι) :
  π (c ∈ Int A B) → π (c ∈ B) ≔
begin
  assume c A B h;
  refine ∧ₑ₂ (∧ₑ₁ (Int_iff c A B) h)
end;

// ===========================================================================
// Set difference — A \ B = {x ∈ A | x ∉ B}
// ===========================================================================

symbol Diff (A B : τ ι) : τ ι ≔ Collect A (λ x, x ∉ B);

// Diff membership: c ∈ Diff A B ⟷ c ∈ A ∧ c ∉ B
opaque symbol Diff_iff (c A B : τ ι) :
  π ((c ∈ Diff A B) ⇔ (c ∈ A ∧ c ∉ B)) ≔
begin
  assume c A B;
  apply Collect_iff c A (λ x, x ∉ B)
end;

opaque symbol DiffI (c A B : τ ι) :
  π (c ∈ A) → π (c ∉ B) → π (c ∈ Diff A B) ≔
begin
  assume c A B hA hnB;
  refine CollectI c A (λ x, x ∉ B) hA hnB
end;

opaque symbol DiffD1 (c A B : τ ι) :
  π (c ∈ Diff A B) → π (c ∈ A) ≔
begin
  assume c A B h;
  refine CollectD1 c A (λ x, x ∉ B) h
end;

opaque symbol DiffD2 (c A B : τ ι) :
  π (c ∈ Diff A B) → π (c ∉ B) ≔
begin
  assume c A B h;
  refine CollectD2 c A (λ x, x ∉ B) h
end;

// ===========================================================================
// cons — cons(a, A) = Upair(a,a) ∪ A  (adjoin element)
// ===========================================================================

symbol cons (a A : τ ι) : τ ι ≔ Un (Upair a a) A;

// cons membership: c ∈ cons(a, A) ⟷ c = a ∨ c ∈ A
opaque symbol cons_iff (c a A : τ ι) :
  π ((c ∈ cons a A) ⇔ (c = a ∨ c ∈ A)) ≔
begin
  assume c a A;
  apply ∧ᵢ
  { assume hc;
    have hdisj : π (c ∈ Upair a a ∨ c ∈ A) { refine UnE c (Upair a a) A hc };
    refine ∨ₑ hdisj _ _
    { assume hup;
      have hdisj2 : π (c = a ∨ c = a) { refine UpairE c a a hup };
      refine ∨ₑ hdisj2 _ _
      { assume h; refine ∨ᵢ₁ h }
      { assume h; refine ∨ᵢ₁ h } }
    { assume hA; refine ∨ᵢ₂ hA } }
  { assume hdisj;
    refine ∨ₑ hdisj _ _
    { assume hca;
      refine UnI1 c (Upair a a) A _;
      rewrite hca;
      refine UpairI1 a a }
    { assume hcA; refine UnI2 c (Upair a a) A hcA } }
end;

opaque symbol consI1 (a A : τ ι) : π (a ∈ cons a A) ≔
begin
  assume a A;
  refine ∧ₑ₂ (cons_iff a a A) (∨ᵢ₁ (eq_refl a))
end;

opaque symbol consI2 (c a A : τ ι) : π (c ∈ A) → π (c ∈ cons a A) ≔
begin
  assume c a A h;
  refine ∧ₑ₂ (cons_iff c a A) (∨ᵢ₂ h)
end;

// ===========================================================================
// Singleton — {a} = cons(a, empty)
// ===========================================================================

symbol singleton (a : τ ι) : τ ι ≔ cons a empty;

opaque symbol singleton_iff (c a : τ ι) :
  π ((c ∈ singleton a) ⇔ (c = a)) ≔
begin
  assume c a;
  apply ∧ᵢ
  { assume hc;
    have hdisj : π (c = a ∨ c ∈ empty)
      { refine ∧ₑ₁ (cons_iff c a empty) hc };
    refine ∨ₑ hdisj _ _
    { assume h; apply h }
    { assume h; refine ⊥ₑ (emptyE c h) } }
  { assume hca;
    refine ∧ₑ₂ (cons_iff c a empty) (∨ᵢ₁ hca) }
end;

opaque symbol singletonI (a : τ ι) : π (a ∈ singleton a) ≔
begin
  assume a;
  refine consI1 a empty
end;

// ===========================================================================
// Foundation consequences (proved here since they need singleton/Upair)
// ===========================================================================

// Foundation consequence: no set is a member of itself
opaque symbol mem_irrefl (A : τ ι) : π (A ∉ A) ≔
begin
  assume A hAA;
  // Apply foundation to singleton A = cons A empty
  have hfound : π (singleton A = empty ∨ Bex (singleton A) (λ x, Ball x (λ y, y ∉ singleton A)))
    { refine foundation (singleton A) };
  // Case split on foundation
  refine ∨ₑ hfound _ _
  { // Case 1: singleton A = empty → contradiction (A ∈ singleton A)
    assume heq;
    refine emptyE A _;
    rewrite left heq;
    refine singletonI A }
  { // Case 2: there exists x ∈ singleton A with Ball x (λ y, y ∉ singleton A)
    assume hbex;
    refine ∃ₑ hbex _;
    assume x hx;
    have hxsing : π (x ∈ singleton A) { refine ∧ₑ₁ hx };
    have hball : π (Ball x (λ y, y ∉ singleton A)) { refine ∧ₑ₂ hx };
    // x = A (since x ∈ singleton A)
    have hxA : π (x = A) { refine ∧ₑ₁ (singleton_iff x A) hxsing };
    // A ∈ A (hAA), so A ∈ x (since x = A via ind_eq), so hball gives A ∉ singleton A
    // But A ∈ singleton A — contradiction
    have hAxin : π (A ∈ x) { refine ind_eq hxA (λ z, A ∈ z) hAA };
    refine hball A hAxin (singletonI A) }
end;

// Foundation consequence: membership is asymmetric
opaque symbol mem_asym (A B : τ ι) : π (A ∈ B) → π (B ∉ A) ≔
begin
  assume A B hAB hBA;
  // Apply foundation to Upair A B
  have hfound : π (Upair A B = empty ∨ Bex (Upair A B) (λ x, Ball x (λ y, y ∉ Upair A B)))
    { refine foundation (Upair A B) };
  // Upair A B ≠ empty since A ∈ Upair A B
  refine ∨ₑ hfound _ _
  { // Case 1: Upair A B = empty → contradiction
    assume heq;
    refine emptyE A _;
    rewrite left heq;
    refine UpairI1 A B }
  { // Case 2: ∃ x ∈ Upair(A,B) with Ball x (λ y, y ∉ Upair A B)
    assume hbex;
    refine ∃ₑ hbex _;
    assume x hx;
    have hxup : π (x ∈ Upair A B) { refine ∧ₑ₁ hx };
    have hball : π (Ball x (λ y, y ∉ Upair A B)) { refine ∧ₑ₂ hx };
    // x = A or x = B
    have hdisj : π (x = A ∨ x = B) { refine UpairE x A B hxup };
    refine ∨ₑ hdisj _ _
    { // x = A: B ∈ A (hBA), so B ∈ x, so B ∉ Upair A B. But B ∈ Upair A B — contradiction.
      assume hxA;
      have hBxin : π (B ∈ x) { refine ind_eq hxA (λ z, B ∈ z) hBA };
      refine hball B hBxin (UpairI2 A B) }
    { // x = B: A ∈ B (hAB), so A ∈ x, so A ∉ Upair A B. But A ∈ Upair A B — contradiction.
      assume hxB;
      have hAxin : π (A ∈ x) { refine ind_eq hxB (λ z, A ∈ z) hAB };
      refine hball A hAxin (UpairI1 A B) } }
end;

// ===========================================================================
// Successor — succ(i) = cons(i, i)
// ===========================================================================

symbol succ (i : τ ι) : τ ι ≔ cons i i;

opaque symbol succ_iff (c i : τ ι) :
  π ((c ∈ succ i) ⇔ (c = i ∨ c ∈ i)) ≔
begin
  assume c i;
  apply cons_iff c i i
end;

opaque symbol succI1 (i : τ ι) : π (i ∈ succ i) ≔
begin
  assume i;
  refine consI1 i i
end;

opaque symbol succI2 (c i : τ ι) : π (c ∈ i) → π (c ∈ succ i) ≔
begin
  assume c i h;
  refine consI2 c i i h
end;

// ===========================================================================
// Infinity axiom (now that succ is defined)
// ===========================================================================

constant symbol infinity :
  π (empty ∈ Inf ∧ (`∀ (y : τ ι), y ∈ Inf ⇒ succ y ∈ Inf));

// ===========================================================================
// The (definite description) and If (conditional)
// ===========================================================================

// The(P) = ⋃{x ∈ ⋃(⋃(…)) | P(x)}  — In Isabelle, The uses Hilbert's epsilon
// We use the epsilon operator from Stdlib
// The x. P(x) returns the unique x such that P(x), if it exists

symbol The (P : τ ι → Prop) : τ ι ≔ ε P;

// If(P, a, b) = The(λ x. (P ∧ x = a) ∨ (¬P ∧ x = b))
symbol If (P : Prop) (a b : τ ι) : τ ι ≔
  The (λ x, (P ∧ x = a) ∨ (¬ P ∧ x = b));

// If_P: when P holds, If(P,a,b) = a.  (Isabelle: if_P)
// The defining predicate collapses to x = a; ε picks that witness.
opaque symbol If_P (P : Prop) (a b : τ ι) : π P → π (If P a b = a) ≔
begin
  assume P a b hP;
  have hex : π (`∃ x : τ ι, (P ∧ x = a) ∨ (¬ P ∧ x = b))
    { refine ∃ᵢ a (∨ᵢ₁ (∧ᵢ hP (eq_refl a))) };
  have heps : π ((P ∧ ε (λ x, (P ∧ x = a) ∨ (¬ P ∧ x = b)) = a)
              ∨ (¬ P ∧ ε (λ x, (P ∧ x = a) ∨ (¬ P ∧ x = b)) = b))
    { refine εᵢ _ hex };
  refine ∨ₑ heps _ _
  { assume h; refine ∧ₑ₂ h }
  { assume h; refine ⊥ₑ ((∧ₑ₁ h) hP) }
end;

// If_not_P: when P fails, If(P,a,b) = b.  (Isabelle: if_not_P)
opaque symbol If_not_P (P : Prop) (a b : τ ι) : π (¬ P) → π (If P a b = b) ≔
begin
  assume P a b hnP;
  have hex : π (`∃ x : τ ι, (P ∧ x = a) ∨ (¬ P ∧ x = b))
    { refine ∃ᵢ b (∨ᵢ₂ (∧ᵢ hnP (eq_refl b))) };
  have heps : π ((P ∧ ε (λ x, (P ∧ x = a) ∨ (¬ P ∧ x = b)) = a)
              ∨ (¬ P ∧ ε (λ x, (P ∧ x = a) ∨ (¬ P ∧ x = b)) = b))
    { refine εᵢ _ hex };
  refine ∨ₑ heps _ _
  { assume h; refine ⊥ₑ (hnP (∧ₑ₁ h)) }
  { assume h; refine ∧ₑ₂ h }
end;

// succ_neq_self: succ(b) ≠ b  (proved, via mem_irrefl / foundation)
opaque symbol succ_neq_self (b : τ ι) : π (succ b ≠ b) ≔
begin
  assume b heq;
  // b ∈ succ b by succI1
  have hbsucc : π (b ∈ succ b) { refine succI1 b };
  // rewrite succ b = b to get b ∈ b
  have hbb : π (b ∈ b) { refine ind_eq (eq_sym heq) (λ z, b ∈ z) hbsucc };
  // contradiction with mem_irrefl
  refine mem_irrefl b hbb
end;

// cons is not empty
opaque symbol cons_not_empty (a A : τ ι) : π (cons a A ≠ empty) ≔
begin
  assume a A heq;
  have h : π (a ∈ cons a A) { refine consI1 a A };
  refine emptyE a _;
  rewrite left heq;
  apply h
end;

// ===========================================================================
// Collect_subset: {x ∈ A | P x} ⊆ A   (from upair.thy / subset.thy)
// ===========================================================================
opaque symbol Collect_subset (A : τ ι) (P : τ ι → Prop) :
  π (Collect A P ⊆ A) ≔
begin
  assume A P x hx;
  refine CollectD1 x A P hx
end;
