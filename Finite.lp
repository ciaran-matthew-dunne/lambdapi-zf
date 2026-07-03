// Finite: Finite Powerset Operator and Finite Function Space
//
// Isabelle source: Finite.thy (Lawrence C Paulson).
//   theory Finite imports Inductive Epsilon Nat
//
// SKELETON: every definition + every lemma/theorem statement is present;
// every proof is `admit`.  Statements are faithful to the Isabelle source.
//
// Fin(A) and FiniteFun(A,B) are package-generated INDUCTIVE sets.  They are
// declared here as ABSTRACT symbols; their inductive content is supplied by the
// admitted rules Fin_0I / Fin_consI / Fin_induct / FinD (and the FiniteFun
// analogues + type rules) below.

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum ZF.Ordinal ZF.OrdQuant ZF.Nat_ZF ZF.QPair ZF.Epsilon ZF.Inductive;

// ===========================================================================
// Definitions  (consts Fin, FiniteFun + definition contents)
// ===========================================================================

// Fin(A): finite-powerset inductive set (⊆ Pow A).  ABSTRACT; content via the
// admitted rules Fin_0I / Fin_consI / Fin_induct / FinD below.
symbol Fin (A : τ ι) : τ ι;

// FiniteFun(A,B) — Isabelle infix `A -||> B` — finite partial functions.
// ABSTRACT; content via FiniteFun_0I / FiniteFun_consI / its induction & type rules.
symbol FiniteFun (A B : τ ι) : τ ι;

// contents(X) ≡ THE x. X = {x}
symbol contents (X : τ ι) : τ ι ≔ The (λ x, X = singleton x);

// ===========================================================================
// Inductive intro rules (package-generated; not explicit `lemma` lines).
// Added so the abstract Fin / FiniteFun are usable.
// ===========================================================================

// Fin.emptyI : 0 ∈ Fin(A)
opaque symbol Fin_0I (A : τ ι) :
  π (empty ∈ Fin A) ≔
begin
  admit
end;

// Fin.consI : ⟦a ∈ A; b ∈ Fin(A)⟧ ⟹ cons(a,b) ∈ Fin(A)
opaque symbol Fin_consI (A a b : τ ι) :
  π (a ∈ A) → π (b ∈ Fin A) → π (cons a b ∈ Fin A) ≔
begin
  admit
end;

// FiniteFun.emptyI : 0 ∈ A -||> B
opaque symbol FiniteFun_0I (A B : τ ι) :
  π (empty ∈ FiniteFun A B) ≔
begin
  admit
end;

// FiniteFun.consI : ⟦a ∈ A; b ∈ B; h ∈ A -||> B; a ∉ domain(h)⟧
//                   ⟹ cons(⟨a,b⟩, h) ∈ A -||> B
opaque symbol FiniteFun_consI (A B a b h : τ ι) :
  π (a ∈ A) → π (b ∈ B) → π (h ∈ FiniteFun A B) → π (a ∉ domain h) →
  π (cons (Pair a b) h ∈ FiniteFun A B) ≔
begin
  admit
end;

// ===========================================================================
// Finite Powerset Operator
// ===========================================================================

// FinD : A ∈ Fin(B) ⟹ A ⊆ B   [lemmas FinD = Fin.dom_subset [THEN subsetD, THEN PowD]]
opaque symbol FinD (A B : τ ι) :
  π (A ∈ Fin B) → π (A ⊆ B) ≔
begin
  admit
end;

// Fin_induct : induction on finite sets  (the abstract inductive characterization)
opaque symbol Fin_induct (A b : τ ι) (P : τ ι → Prop) :
  π (b ∈ Fin A) →
  π (P empty) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ Fin A) → π (x ∉ y) → π (P y) → π (P (cons x y))) →
  π (P b) ≔
begin
  admit
end;

// Fin_mono : A ⊆ B ⟹ Fin(A) ⊆ Fin(B)
opaque symbol Fin_mono (A B : τ ι) :
  π (A ⊆ B) → π (Fin A ⊆ Fin B) ≔
begin
  assume A B hAB C hC;
  refine Fin_induct A C (λ w, w ∈ Fin B) hC _ _
  { refine Fin_0I B }
  { assume x y hxA hyFinA hxny hyFinB;
    refine Fin_consI B x y (hAB x hxA) hyFinB }
end;

// Fin_0 : Fin(0) = {0}
opaque symbol Fin_0 :
  π (Fin empty = singleton empty) ≔
begin
  refine equality_iffI (Fin empty) (singleton empty) _;
  assume C;
  apply ∧ᵢ
  { assume hC;
    // C ∈ Fin(0) → C ⊆ 0 → C = 0.
    refine ∧ₑ₂ (singleton_iff C empty) (subset_empty C (FinD C empty hC)) }
  { assume hC;
    // C ∈ {0} → C = 0 → C ∈ Fin(0).
    refine ind_eq (∧ₑ₁ (singleton_iff C empty) hC) (λ w, w ∈ Fin empty) (Fin_0I empty) }
end;

// Fin_UnI : ⟦b ∈ Fin(A); c ∈ Fin(A)⟧ ⟹ b ∪ c ∈ Fin(A)
opaque symbol Fin_UnI (A b c : τ ι) :
  π (b ∈ Fin A) → π (c ∈ Fin A) → π (Un b c ∈ Fin A) ≔
begin
  assume A b c hb hc;
  refine Fin_induct A b (λ w, Un w c ∈ Fin A) hb _ _
  { refine ind_eq (Un_empty_left c) (λ w, w ∈ Fin A) hc }
  { assume x y hxA hyFinA hxny hyUn;
    refine ind_eq (cons_Un_distrib x y c) (λ w, w ∈ Fin A)
      (Fin_consI A x (Un y c) hxA hyUn) }
end;

// Fin_UnionI : C ∈ Fin(Fin(A)) ⟹ ⋃(C) ∈ Fin(A)
opaque symbol Fin_UnionI (A C : τ ι) :
  π (C ∈ Fin (Fin A)) → π (Union C ∈ Fin A) ≔
begin
  admit
end;

// Fin_subset_lemma [rule_format] : b ∈ Fin(A) ⟹ ∀z. z ⊆ b ⟶ z ∈ Fin(A)
opaque symbol Fin_subset_lemma (A b : τ ι) :
  π (b ∈ Fin A) → π (`∀ (z : τ ι), z ⊆ b ⇒ z ∈ Fin A) ≔
begin
  admit
end;

// Fin_subset : ⟦c ⊆ b; b ∈ Fin(A)⟧ ⟹ c ∈ Fin(A)
opaque symbol Fin_subset (A b c : τ ι) :
  π (c ⊆ b) → π (b ∈ Fin A) → π (c ∈ Fin A) ≔
begin
  admit
end;

// Fin_IntI1 : b ∈ Fin(A) ⟹ b ∩ c ∈ Fin(A)
opaque symbol Fin_IntI1 (A b c : τ ι) :
  π (b ∈ Fin A) → π (Int b c ∈ Fin A) ≔
begin
  admit
end;

// Fin_IntI2 : c ∈ Fin(A) ⟹ b ∩ c ∈ Fin(A)
opaque symbol Fin_IntI2 (A b c : τ ι) :
  π (c ∈ Fin A) → π (Int b c ∈ Fin A) ≔
begin
  admit
end;

// Fin_0_induct_lemma [rule_format] :
//   ⟦c ∈ Fin(A); b ∈ Fin(A); P(b);
//      ⋀x y. ⟦x ∈ A; y ∈ Fin(A); x ∈ y; P(y)⟧ ⟹ P(y-{x})⟧
//   ⟹ c ⊆ b ⟶ P(b-c)
opaque symbol Fin_0_induct_lemma (A b c : τ ι) (P : τ ι → Prop) :
  π (c ∈ Fin A) →
  π (b ∈ Fin A) →
  π (P b) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ Fin A) → π (x ∈ y) → π (P y) → π (P (Diff y (singleton x)))) →
  π (c ⊆ b ⇒ P (Diff b c)) ≔
begin
  admit
end;

// Fin_0_induct :
//   ⟦b ∈ Fin(A); P(b);
//      ⋀x y. ⟦x ∈ A; y ∈ Fin(A); x ∈ y; P(y)⟧ ⟹ P(y-{x})⟧ ⟹ P(0)
opaque symbol Fin_0_induct (A b : τ ι) (P : τ ι → Prop) :
  π (b ∈ Fin A) →
  π (P b) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ Fin A) → π (x ∈ y) → π (P y) → π (P (Diff y (singleton x)))) →
  π (P empty) ≔
begin
  admit
end;

// nat_fun_subset_Fin : n ∈ nat ⟹ n->A ⊆ Fin(nat*A)
opaque symbol nat_fun_subset_Fin (n A : τ ι) :
  π (n ∈ omega) → π (Pi n (λ _, A) ⊆ Fin (Sigma omega (λ _, A))) ≔
begin
  admit
end;

// ===========================================================================
// Finite Function Space
// ===========================================================================

// FiniteFun_mono : ⟦A ⊆ C; B ⊆ D⟧ ⟹ A -||> B ⊆ C -||> D
opaque symbol FiniteFun_mono (A B C D : τ ι) :
  π (A ⊆ C) → π (B ⊆ D) → π (FiniteFun A B ⊆ FiniteFun C D) ≔
begin
  admit
end;

// FiniteFun_mono1 : A ⊆ B ⟹ A -||> A ⊆ B -||> B
opaque symbol FiniteFun_mono1 (A B : τ ι) :
  π (A ⊆ B) → π (FiniteFun A A ⊆ FiniteFun B B) ≔
begin
  admit
end;

// FiniteFun_is_fun : h ∈ A -||> B ⟹ h ∈ domain(h) -> B
opaque symbol FiniteFun_is_fun (A B h : τ ι) :
  π (h ∈ FiniteFun A B) → π (h ∈ Pi (domain h) (λ _, B)) ≔
begin
  admit
end;

// FiniteFun_domain_Fin : h ∈ A -||> B ⟹ domain(h) ∈ Fin(A)
opaque symbol FiniteFun_domain_Fin (A B h : τ ι) :
  π (h ∈ FiniteFun A B) → π (domain h ∈ Fin A) ≔
begin
  admit
end;

// FiniteFun_apply_type : ⟦h ∈ A -||> B; a ∈ domain(h)⟧ ⟹ h`a ∈ B
//   [lemmas FiniteFun_apply_type = FiniteFun_is_fun [THEN apply_type]]
opaque symbol FiniteFun_apply_type (A B h a : τ ι) :
  π (h ∈ FiniteFun A B) → π (a ∈ domain h) → π (fapply h a ∈ B) ≔
begin
  admit
end;

// FiniteFun_subset_lemma [rule_format] : b ∈ A -||> B ⟹ ∀z. z ⊆ b ⟶ z ∈ A -||> B
opaque symbol FiniteFun_subset_lemma (A B b : τ ι) :
  π (b ∈ FiniteFun A B) → π (`∀ (z : τ ι), z ⊆ b ⇒ z ∈ FiniteFun A B) ≔
begin
  admit
end;

// FiniteFun_subset : ⟦c ⊆ b; b ∈ A -||> B⟧ ⟹ c ∈ A -||> B
opaque symbol FiniteFun_subset (A B b c : τ ι) :
  π (c ⊆ b) → π (b ∈ FiniteFun A B) → π (c ∈ FiniteFun A B) ≔
begin
  admit
end;

// fun_FiniteFunI [rule_format] : A ∈ Fin(X) ⟹ ∀f. f ∈ A->B ⟶ f ∈ A -||> B
opaque symbol fun_FiniteFunI (A B X : τ ι) :
  π (A ∈ Fin X) → π (`∀ (f : τ ι), f ∈ Pi A (λ _, B) ⇒ f ∈ FiniteFun A B) ≔
begin
  admit
end;

// lam_FiniteFun : A ∈ Fin(X) ⟹ (λx∈A. b(x)) ∈ A -||> {b(x). x ∈ A}
opaque symbol lam_FiniteFun (A X : τ ι) (b : τ ι → τ ι) :
  π (A ∈ Fin X) → π (Lambda A (λ x, b x) ∈ FiniteFun A (RepFun A (λ x, b x))) ≔
begin
  admit
end;

// FiniteFun_Collect_iff :
//   f ∈ FiniteFun(A, {y ∈ B. P(y)})
//     ⟷ f ∈ FiniteFun(A,B) ∧ (∀x∈domain(f). P(f`x))
opaque symbol FiniteFun_Collect_iff (A B f : τ ι) (P : τ ι → Prop) :
  π (f ∈ FiniteFun A (Collect B (λ y, P y)) ⇔
     (f ∈ FiniteFun A B ∧ Ball (domain f) (λ x, P (fapply f x)))) ≔
begin
  admit
end;

// ===========================================================================
// The Contents of a Singleton Set
// ===========================================================================

// contents_eq : contents({x}) = x
opaque symbol contents_eq (x : τ ι) :
  π (contents (singleton x) = x) ≔
begin
  assume x;
  refine the_equality (λ y, singleton x = singleton y) x (eq_refl (singleton x)) _;
  assume y hy;
  refine eq_sym (singleton_inject x y hy)
end;
