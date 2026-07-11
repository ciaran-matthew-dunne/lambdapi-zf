// ZF.List — Lists in Zermelo-Fraenkel Set Theory
// Faithful SKELETON port of isabelle-src/List.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/List.thy.)
//
// BOOTSTRAP (hand-built, no proofs — analogous to Finite.lp's Fin/FiniteFun
// and Zorn.lp's TFin, which likewise reconstruct what Isabelle's `datatype`/
// `inductive` package generates):
//
//   list(A) is the package-generated datatype "list(A) = Nil | Cons(a∈A,l∈list(A))".
//   Its ACTUAL Isabelle encoding (Datatype.thy's Standard_Sum instantiation) is
//   the least fixed point, domain univ(A), of X ↦ {0} + (A*X):
//     Nil      = Inl(0)
//     Cons a l = Inr(⟨a,l⟩)
//   freeness (Nil≠Cons(..), Cons injective) follows from Inl/Inr already being
//   proved disjoint+injective in Sum.lp — this is exactly why the package
//   itself picks a disjoint-sum encoding, and why we do too.
//
//   list_case/list_rec are the package-generated case-analysis/recursor.
//   list_case is a direct (non-recursive) combinator, `≔`-defined.  list_rec
//   is recursive (built on Vrec, i.e. Vset-rank recursion) — per Arith.lp's
//   established precedent (see that file's header) recursive definitions here
//   are ABSTRACT symbols with a defining *_def AXIOM rather than a `≔` body,
//   to keep the kernel from eagerly unfolding Vrec/transrec/rank during
//   conversion checking.  `list_rec_def` IS the Isabelle definition, faithfully.
//
//   Every other primrec'd function in List.thy (length, hd, tl, map, app,
//   rev, flat, list_add, drop, filter, upt, zip_aux, repeat) is a direct
//   instance of list_rec — e.g. length ≔ list_rec(0, λx xs r. succ(r)).
//   `take`/`nth`/`list_update` are defined via list_rec directly in the .thy
//   too (not `primrec`), same treatment.

require open ZF.Datatype ZF.ArithSimp;

// ===========================================================================
// The datatype list(A), its constructors, case analysis and recursor
// ===========================================================================

symbol list (A : τ ι) : τ ι ≔
  lfp (univ A) (λ X, sum (singleton empty) (Sigma A (λ _, X)));

symbol Nil : τ ι ≔ Inl empty;
symbol Cons (a l : τ ι) : τ ι ≔ Inr (Pair a l);

symbol list_case (c : τ ι) (h : τ ι → τ ι → τ ι) (l : τ ι) : τ ι ≔
  case_sum (λ _, c) (split h) l;

// list_rec(c,h,l) ≡ Vrec(l, λl2 g. list_case(c, λx xs. h(x,xs,g`xs), l2))
symbol list_rec : τ ι → (τ ι → τ ι → τ ι → τ ι) → τ ι → τ ι;
// list_rec is an abstract symbol with no body, so this equation IS its
// definition (Isabelle's list_rec_def) — a declared `_def` axiom per Arith.lp's
// precedent for Vrec-based recursors, not a provable lemma.
symbol list_rec_def (c : τ ι) (h : τ ι → τ ι → τ ι → τ ι) (l : τ ι) :
  π (list_rec c h l =
     Vrec l (λ l2 g, list_case c (λ x xs, h x xs (fapply g xs)) l2));

// ===========================================================================
// Private bootstrap infrastructure (port-internal helpers): what Isabelle's
// datatype package proves behind the scenes — univ-closure of the list
// operator, bounded monotonicity, and structural induction.  All private;
// the public statements below match the .thy.
// ===========================================================================

// port-internal helper — Univ.thy's Pair_in_VLimit at i := ω (Univ.lp does
// not port it; same inline derivation as QUniv.lp's QPair_subset_univ).
private opaque symbol Pair_in_univ (x y A : τ ι) :
  π (x ∈ univ A) → π (y ∈ univ A) → π (Pair x y ∈ univ A) ≔
begin
  assume x y A hxu hyu;
  have hx : π (x ∈ Vfrom A omega)
    { refine ind_eq (eq_sym (univ_def A)) (λ w, x ∈ w) hxu };
  have hy : π (y ∈ Vfrom A omega)
    { refine ind_eq (eq_sym (univ_def A)) (λ w, y ∈ w) hyu };
  have hTom : π (Transset omega) { refine Ord_is_Transset omega Ord_omega };
  have heq : π (Vfrom A omega = Union (RepFun omega (λ j, Vfrom A j)))
    { refine Limit_Vfrom_eq A omega Limit_omega };
  have hxU : π (x ∈ Union (RepFun omega (λ j, Vfrom A j)))
    { refine ind_eq (eq_sym heq) (λ w, x ∈ w) hx };
  have hyU : π (y ∈ Union (RepFun omega (λ j, Vfrom A j)))
    { refine ind_eq (eq_sym heq) (λ w, y ∈ w) hy };
  have hxbex : π (Bex (RepFun omega (λ j, Vfrom A j)) (λ S, x ∈ S))
    { refine UnionE x (RepFun omega (λ j, Vfrom A j)) hxU };
  refine ∃ₑ hxbex _; assume S hS;
  have hSbex : π (Bex omega (λ j, S = Vfrom A j))
    { refine ∧ₑ₁ (RepFun_iff S omega (λ j, Vfrom A j)) (∧ₑ₁ hS) };
  refine ∃ₑ hSbex _; assume i hi;
  have hxi : π (x ∈ Vfrom A i)
    { refine ind_eq (eq_sym (∧ₑ₂ hi)) (λ w, x ∈ w) (∧ₑ₂ hS) };
  have hybex : π (Bex (RepFun omega (λ j, Vfrom A j)) (λ S2, y ∈ S2))
    { refine UnionE y (RepFun omega (λ j, Vfrom A j)) hyU };
  refine ∃ₑ hybex _; assume T hT;
  have hTbex : π (Bex omega (λ j, T = Vfrom A j))
    { refine ∧ₑ₁ (RepFun_iff T omega (λ j, Vfrom A j)) (∧ₑ₁ hT) };
  refine ∃ₑ hTbex _; assume j hj;
  have hyj : π (y ∈ Vfrom A j)
    { refine ind_eq (eq_sym (∧ₑ₂ hj)) (λ w, y ∈ w) (∧ₑ₂ hT) };
  have hk : π (Un i j ∈ omega) { refine Un_nat_type i j (∧ₑ₁ hi) (∧ₑ₁ hj) };
  have hxk : π (x ∈ Vfrom A (Un i j))
    { refine Vfrom_mono A A i (Un i j) (subset_refl A) (Un_upper1 i j) x hxi };
  have hyk : π (y ∈ Vfrom A (Un i j))
    { refine Vfrom_mono A A j (Un i j) (subset_refl A) (Un_upper2 i j) y hyj };
  have hsing : π (singleton x ∈ Pow (Vfrom A (Un i j)))
    { refine PowI (singleton x) (Vfrom A (Un i j)) _;
      assume z hz;
      refine ind_eq (singletonE z x hz) (λ w, w ∈ Vfrom A (Un i j)) hxk };
  have hup : π (Upair x y ∈ Pow (Vfrom A (Un i j)))
    { refine PowI (Upair x y) (Vfrom A (Un i j)) _;
      assume z hz;
      refine ∨ₑ (UpairE z x y hz) _ _
      { assume hzx; refine ind_eq hzx (λ w, w ∈ Vfrom A (Un i j)) hxk }
      { assume hzy; refine ind_eq hzy (λ w, w ∈ Vfrom A (Un i j)) hyk } };
  have hVs1 : π (Vfrom A (succ (Un i j)) = Un A (Pow (Vfrom A (Un i j))))
    { refine Vfrom_succ A (Un i j) };
  have hsing1 : π (singleton x ∈ Vfrom A (succ (Un i j)))
    { refine ind_eq hVs1 (λ w, singleton x ∈ w)
        (UnI2 (singleton x) A (Pow (Vfrom A (Un i j))) hsing) };
  have hup1 : π (Upair x y ∈ Vfrom A (succ (Un i j)))
    { refine ind_eq hVs1 (λ w, Upair x y ∈ w)
        (UnI2 (Upair x y) A (Pow (Vfrom A (Un i j))) hup) };
  have hpair_sub : π (Pair x y ⊆ Vfrom A (succ (Un i j)))
    { refine ind_eq (Pair_def x y) (λ w, w ⊆ Vfrom A (succ (Un i j))) _;
      assume z hz;
      refine ∨ₑ (UpairE z (singleton x) (Upair x y) hz) _ _
      { assume h1; refine ind_eq h1 (λ w, w ∈ Vfrom A (succ (Un i j))) hsing1 }
      { assume h2; refine ind_eq h2 (λ w, w ∈ Vfrom A (succ (Un i j))) hup1 } };
  have hVs2 : π (Vfrom A (succ (succ (Un i j))) =
                 Un A (Pow (Vfrom A (succ (Un i j)))))
    { refine Vfrom_succ A (succ (Un i j)) };
  have hpair_mem : π (Pair x y ∈ Vfrom A (succ (succ (Un i j))))
    { refine ind_eq hVs2 (λ w, Pair x y ∈ w)
        (UnI2 (Pair x y) A (Pow (Vfrom A (succ (Un i j))))
          (PowI (Pair x y) (Vfrom A (succ (Un i j))) hpair_sub)) };
  have hss : π (succ (succ (Un i j)) ∈ omega)
    { refine succ_in_omega (succ (Un i j)) (succ_in_omega (Un i j) hk) };
  have hVsub : π (Vfrom A (succ (succ (Un i j))) ⊆ Vfrom A omega)
    { refine Vfrom_mono A A (succ (succ (Un i j))) omega (subset_refl A)
        (TranssetD omega (succ (succ (Un i j))) hTom hss) };
  refine ind_eq (univ_def A) (λ w, Pair x y ∈ w) (hVsub (Pair x y) hpair_mem)
end;

// port-internal helper (Univ.thy zero_in_univ)
private opaque symbol zero_in_univ (A : τ ι) : π (empty ∈ univ A) ≔
begin
  assume A;
  refine ind_eq (univ_def A) (λ w, empty ∈ w)
    (i_subset_Vfrom A omega empty zero_in_omega)
end;

// port-internal helper (Univ.thy one_in_univ)
private opaque symbol one_in_univ (A : τ ι) : π (one ∈ univ A) ≔
begin
  assume A;
  refine ind_eq (univ_def A) (λ w, one ∈ w)
    (i_subset_Vfrom A omega one nat_1I)
end;

// port-internal helper (Univ.thy A_subset_univ)
private opaque symbol A_subset_univ (A : τ ι) : π (A ⊆ univ A) ≔
begin
  assume A x hx;
  refine ind_eq (univ_def A) (λ w, x ∈ w) (A_subset_Vfrom A omega x hx)
end;

// port-internal helper: the list operator's image lands in univ(A)
private opaque symbol list_op_subset_univ (B X A : τ ι) :
  π (B ⊆ univ A) → π (X ⊆ univ A) →
  π (sum (singleton empty) (Sigma B (λ _, X)) ⊆ univ A) ≔
begin
  assume B X A hB hX u hu;
  refine sumE u (singleton empty) (Sigma B (λ _, X)) (u ∈ univ A) hu _ _
  { assume x hx hueq;
    have hxu : π (x ∈ univ A)
      { refine ind_eq (singletonE x empty hx) (λ w, w ∈ univ A) (zero_in_univ A) };
    have hu2 : π (u = Pair empty x) { rewrite hueq; refine Inl_def x };
    refine ind_eq hu2 (λ w, w ∈ univ A)
      (Pair_in_univ empty x A (zero_in_univ A) hxu) }
  { assume p hp hueq;
    have hbex : π (Bex B (λ a, Bex X (λ l, p = Pair a l)))
      { refine SigmaE p B (λ _, X) hp };
    refine ∃ₑ hbex _; assume a ha;
    refine ∃ₑ (∧ₑ₂ ha) _; assume l hl;
    have hpu : π (p ∈ univ A)
      { refine ind_eq (∧ₑ₂ hl) (λ w, w ∈ univ A)
          (Pair_in_univ a l A (hB a (∧ₑ₁ ha)) (hX l (∧ₑ₁ hl))) };
    have hu2 : π (u = Pair one p) { rewrite hueq; refine Inr_def p };
    refine ind_eq hu2 (λ w, w ∈ univ A)
      (Pair_in_univ one p A (one_in_univ A) hpu) }
end;

// port-internal helper: monotonicity of the list operator
private opaque symbol list_op_mono (A W X : τ ι) :
  π (W ⊆ X) →
  π (sum (singleton empty) (Sigma A (λ _, W)) ⊆
     sum (singleton empty) (Sigma A (λ _, X))) ≔
begin
  assume A W X hWX u hu;
  refine sumE u (singleton empty) (Sigma A (λ _, W))
    (u ∈ sum (singleton empty) (Sigma A (λ _, X))) hu _ _
  { assume x hx hueq;
    refine ind_eq hueq (λ w, w ∈ sum (singleton empty) (Sigma A (λ _, X)))
      (InlI x (singleton empty) (Sigma A (λ _, X)) hx) }
  { assume p hp hueq;
    have hbex : π (Bex A (λ a, Bex W (λ l, p = Pair a l)))
      { refine SigmaE p A (λ _, W) hp };
    refine ∃ₑ hbex _; assume a ha;
    refine ∃ₑ (∧ₑ₂ ha) _; assume l hl;
    have hpX : π (p ∈ Sigma A (λ _, X))
      { refine ind_eq (∧ₑ₂ hl) (λ w, w ∈ Sigma A (λ _, X))
          (SigmaI a l A (λ _, X) (∧ₑ₁ ha) (hWX l (∧ₑ₁ hl))) };
    refine ind_eq hueq (λ w, w ∈ sum (singleton empty) (Sigma A (λ _, X)))
      (InrI p (singleton empty) (Sigma A (λ _, X)) hpX) }
end;

// port-internal helper: list.bnd_mono
private opaque symbol list_bnd_mono (A : τ ι) :
  π (bnd_mono (univ A) (λ X, sum (singleton empty) (Sigma A (λ _, X)))) ≔
begin
  assume A;
  rewrite bnd_mono_def;
  apply ∧ᵢ
  { refine list_op_subset_univ A (univ A) A (A_subset_univ A)
      (subset_refl (univ A)) }
  { assume W X hWX hXD; refine list_op_mono A W X hWX }
end;

// port-internal helper: list_unfold, available before its public position
private opaque symbol list_unfold_h (A : τ ι) :
  π (list A = sum (singleton empty) (Sigma A (λ _, list A))) ≔
begin
  assume A;
  refine lfp_unfold (univ A) (λ X, sum (singleton empty) (Sigma A (λ _, X)))
    (list_bnd_mono A)
end;

// ===========================================================================
// Basic freeness / typing (`declare list.intros [simp,TC]`,
// `inductive_cases ConsE`, and the immediate freeness lemmas)
// ===========================================================================

opaque symbol list_0I (A : τ ι) : π (Nil ∈ list A) ≔
begin
  assume A;
  refine ind_eq (list_unfold_h A) (λ w, Nil ∈ w)
    (InlI empty (singleton empty) (Sigma A (λ _, list A)) (singletonI empty))
end;

opaque symbol list_consI (a l A : τ ι) :
  π (a ∈ A) → π (l ∈ list A) → π (Cons a l ∈ list A) ≔
begin
  assume a l A ha hl;
  refine ind_eq (list_unfold_h A) (λ w, Cons a l ∈ w)
    (InrI (Pair a l) (singleton empty) (Sigma A (λ _, list A))
      (SigmaI a l A (λ _, list A) ha hl))
end;

// inductive_cases ConsE: elimination rule for Cons(a,l) ∈ list(A)
opaque symbol ConsE (a l A : τ ι) (P : Prop) :
  π (Cons a l ∈ list A) → (π (a ∈ A) → π (l ∈ list A) → π P) → π P ≔
begin
  assume a l A P hmem hstep;
  have hsum : π (Cons a l ∈ sum (singleton empty) (Sigma A (λ _, list A)))
    { refine ind_eq (eq_sym (list_unfold_h A)) (λ w, Cons a l ∈ w) hmem };
  have hp : π (Pair a l ∈ Sigma A (λ _, list A))
    { refine InrD (Pair a l) (singleton empty) (Sigma A (λ _, list A)) hsum };
  have hbex : π (Bex A (λ x, Bex (list A) (λ y, Pair a l = Pair x y)))
    { refine SigmaE (Pair a l) A (λ _, list A) hp };
  refine ∃ₑ hbex _; assume x hx;
  refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
  have hax : π (a = x) { refine Pair_inject1 a l x y (∧ₑ₂ hy) };
  have hly : π (l = y) { refine Pair_inject2 a l x y (∧ₑ₂ hy) };
  refine hstep (ind_eq hax (λ w, w ∈ A) (∧ₑ₁ hx))
    (ind_eq hly (λ w, w ∈ list A) (∧ₑ₁ hy))
end;

opaque symbol Cons_type_iff (a l A : τ ι) :
  π (Cons a l ∈ list A ⇔ (a ∈ A ∧ l ∈ list A)) ≔
begin
  assume a l A;
  apply ∧ᵢ
  { assume h;
    refine ConsE a l A (a ∈ A ∧ l ∈ list A) h _;
    assume ha hl; refine ∧ᵢ ha hl }
  { assume h; refine list_consI a l A (∧ₑ₁ h) (∧ₑ₂ h) }
end;

// Proving freeness results
opaque symbol Cons_iff (a l a' l' : τ ι) :
  π (Cons a l = Cons a' l' ⇔ (a = a' ∧ l = l')) ≔
begin
  assume a l a' l';
  apply ∧ᵢ
  { assume h;
    have hp : π (Pair a l = Pair a' l')
      { refine Inr_inject (Pair a l) (Pair a' l') h };
    refine ∧ᵢ (Pair_inject1 a l a' l' hp) (Pair_inject2 a l a' l' hp) }
  { assume h; rewrite (∧ₑ₁ h); rewrite (∧ₑ₂ h); reflexivity }
end;

opaque symbol Nil_Cons_iff (a l : τ ι) : π (¬ (Nil = Cons a l)) ≔
begin
  assume a l h;
  refine Inl_neq_Inr empty (Pair a l) ⊥ h
end;

opaque symbol list_unfold (A : τ ι) :
  π (list A = sum (singleton empty) (Sigma A (λ _, list A))) ≔
begin
  assume A;
  refine list_unfold_h A
end;

// port-internal helper — the structural induction principle list.induct that
// Isabelle's datatype package generates (derived from Fixedpt.induct).
private opaque symbol list_induct (l A : τ ι) (P : τ ι → Prop) :
  π (l ∈ list A) → π (P Nil) →
  (Π (a y : τ ι), π (a ∈ A) → π (y ∈ list A) → π (P y) → π (P (Cons a y))) →
  π (P l) ≔
begin
  assume l A P hl hNil hCons;
  refine induct (univ A) l (λ X, sum (singleton empty) (Sigma A (λ _, X))) P
    hl (list_bnd_mono A) _;
  assume x hx;
  refine sumE x (singleton empty) (Sigma A (λ _, Collect (list A) P)) (P x) hx _ _
  { assume y hy hxeq;
    have hxNil : π (x = Nil)
      { rewrite hxeq; rewrite (singletonE y empty hy); reflexivity };
    refine ind_eq hxNil P hNil }
  { assume p hp hxeq;
    have hbex : π (Bex A (λ a, Bex (Collect (list A) P) (λ y, p = Pair a y)))
      { refine SigmaE p A (λ _, Collect (list A) P) hp };
    refine ∃ₑ hbex _; assume a ha;
    refine ∃ₑ (∧ₑ₂ ha) _; assume y hy;
    have hyl : π (y ∈ list A) { refine CollectD1 y (list A) P (∧ₑ₁ hy) };
    have hyP : π (P y) { refine CollectD2 y (list A) P (∧ₑ₁ hy) };
    have hxCons : π (x = Cons a y)
      { rewrite hxeq; rewrite (∧ₑ₂ hy); reflexivity };
    refine ind_eq hxCons P (hCons a y (∧ₑ₁ ha) hyl hyP) }
end;

// port-internal helper — the exhaustion lemma list.cases the package generates
private opaque symbol list_cases (l A : τ ι) :
  π (l ∈ list A) →
  π (l = Nil ∨ (`∃ (a : τ ι), `∃ (y : τ ι), l = Cons a y ∧ a ∈ A ∧ y ∈ list A)) ≔
begin
  assume l A hl;
  refine list_induct l A
    (λ w, w = Nil ∨ (`∃ (a : τ ι), `∃ (y : τ ι), w = Cons a y ∧ a ∈ A ∧ y ∈ list A))
    hl _ _
  { refine ∨ᵢ₁ (eq_refl Nil) }
  { assume x y hx hy hIH;
    refine ∨ᵢ₂ (∃ᵢ x (∃ᵢ y (∧ᵢ (eq_refl (Cons x y)) (∧ᵢ hx hy)))) }
end;

// port-internal helpers — the case-analysis equations the package generates
private opaque symbol list_case_Nil (c : τ ι) (h : τ ι → τ ι → τ ι) :
  π (list_case c h Nil = c) ≔
begin
  assume c h;
  refine case_Inl (λ _, c) (split h) empty
end;

private opaque symbol list_case_Cons (c : τ ι) (h : τ ι → τ ι → τ ι) (a l : τ ι) :
  π (list_case c h (Cons a l) = h a l) ≔
begin
  assume c h a l;
  have hg : π (case_sum (λ _, c) (split h) (Inr (Pair a l)) = h a l)
    { rewrite case_Inr;
      rewrite split_def;
      rewrite fst_conv; rewrite snd_conv; reflexivity };
  refine hg
end;

// ===========================================================================
// Lemmas to justify using "list" in other recursive type definitions
// ===========================================================================

opaque symbol list_mono (A B : τ ι) : π (A ⊆ B) → π (list A ⊆ list B) ≔
begin
  assume A B hAB l hl;
  refine list_induct l A (λ w, w ∈ list B) hl (list_0I B) _;
  assume a y ha hy hyB;
  refine list_consI a y B (hAB a ha) hyB
end;

// There is a similar proof by list induction.
opaque symbol list_univ (A : τ ι) : π (list (univ A) ⊆ univ A) ≔
begin
  assume A;
  refine lfp_lowerbound (univ (univ A)) (univ A)
    (λ X, sum (singleton empty) (Sigma (univ A) (λ _, X))) _
    (A_subset_univ (univ A));
  refine list_op_subset_univ (univ A) (univ A) A (subset_refl (univ A))
    (subset_refl (univ A))
end;

// These two theorems justify datatypes involving list(nat), list(A), ...
opaque symbol list_subset_univ (A B : τ ι) : π (A ⊆ univ B) → π (list A ⊆ univ B) ≔
begin
  assume A B h;
  refine subset_trans (list A) (list (univ B)) (univ B)
    (list_mono A (univ B) h) (list_univ B)
end;

opaque symbol list_into_univ (l A B : τ ι) :
  π (l ∈ list A) → π (A ⊆ univ B) → π (l ∈ univ B) ≔
begin
  assume l A B hl hAB;
  refine list_subset_univ A B hAB l hl
end;

opaque symbol list_case_type (l A c : τ ι) (h : τ ι → τ ι → τ ι) (C : τ ι → τ ι) :
  π (l ∈ list A) → π (c ∈ C Nil) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ list A) → π (h x y ∈ C (Cons x y))) →
  π (list_case c h l ∈ C l) ≔
begin
  assume l A c h C hl hc hstep;
  refine list_induct l A (λ w, list_case c h w ∈ C w) hl _ _
  { refine ind_eq (list_case_Nil c h) (λ w, w ∈ C Nil) hc }
  { assume x y hx hy hIH;
    refine ind_eq (list_case_Cons c h x y) (λ w, w ∈ C (Cons x y))
      (hstep x y hx hy) }
end;

opaque symbol list_0_triv : π (list empty = singleton Nil) ≔
begin
  refine subset_antisym (list empty) (singleton Nil) _ _
  { assume l hl;
    refine list_induct l empty (λ w, w ∈ singleton Nil) hl (singletonI Nil) _;
    assume x y hx hy hIH;
    refine ⊥ₑ (emptyE x hx) }
  { assume l hl;
    refine ind_eq (singletonE l Nil hl) (λ w, w ∈ list empty) (list_0I empty) }
end;

// port-internal helper — Epsilon.thy's rank_pair2 lifted to Cons:
// rank(l) < rank(Cons(a,l)), since Cons(a,l) = Inr(⟨a,l⟩) = ⟨1,⟨a,l⟩⟩ and
// rank climbs strictly along ∈ (l ∈ {a,l} ∈ ⟨a,l⟩, then two more levels).
private opaque symbol rank_Cons2 (a l : τ ι) :
  π (lt (rank l) (rank (Cons a l))) ≔
begin
  assume a l;
  have h1 : π (lt (rank l) (rank (Upair a l)))
    { refine rank_lt l (Upair a l) (UpairI2 a l) };
  have h2 : π (Upair a l ∈ Pair a l)
    { refine ind_eq (Pair_def a l) (λ w, Upair a l ∈ w)
        (UpairI2 (singleton a) (Upair a l)) };
  have h7 : π (lt (rank l) (rank (Pair a l)))
    { refine lt_trans (rank l) (rank (Upair a l)) (rank (Pair a l)) h1
        (rank_lt (Upair a l) (Pair a l) h2) };
  have h4 : π (Upair one (Pair a l) ∈ Pair one (Pair a l))
    { refine ind_eq (Pair_def one (Pair a l)) (λ w, Upair one (Pair a l) ∈ w)
        (UpairI2 (singleton one) (Upair one (Pair a l))) };
  have h6 : π (lt (rank (Pair a l)) (rank (Pair one (Pair a l))))
    { refine lt_trans (rank (Pair a l)) (rank (Upair one (Pair a l)))
        (rank (Pair one (Pair a l)))
        (rank_lt (Pair a l) (Upair one (Pair a l)) (UpairI2 one (Pair a l)))
        (rank_lt (Upair one (Pair a l)) (Pair one (Pair a l)) h4) };
  have h8 : π (lt (rank l) (rank (Pair one (Pair a l))))
    { refine lt_trans (rank l) (rank (Pair a l)) (rank (Pair one (Pair a l)))
        h7 h6 };
  refine ind_eq (Inr_def (Pair a l)) (λ w, lt (rank l) (rank w)) h8
end;

// port-internal helpers — the recursion equations that Isabelle's package
// generates for list_rec (List.thy's list_rec_Nil / list_rec_Cons, proved
// there by `list_rec_def [THEN def_Vrec, THEN trans]`).
private opaque symbol list_rec_Nil (c : τ ι) (h : τ ι → τ ι → τ ι → τ ι) :
  π (list_rec c h Nil = c) ≔
begin
  assume c h;
  have hunf : π (list_rec c h Nil =
      list_case c
        (λ x xs, h x xs (fapply (Lambda (Vset (rank Nil)) (λ w, list_rec c h w)) xs))
        Nil)
    { refine def_Vrec (λ w, list_rec c h w)
        (λ l2 g, list_case c (λ x xs, h x xs (fapply g xs)) l2)
        (λ w, list_rec_def c h w) Nil };
  rewrite hunf;
  refine list_case_Nil c
    (λ x xs, h x xs (fapply (Lambda (Vset (rank Nil)) (λ w, list_rec c h w)) xs))
end;

private opaque symbol list_rec_Cons (c : τ ι) (h : τ ι → τ ι → τ ι → τ ι) (a l : τ ι) :
  π (list_rec c h (Cons a l) = h a l (list_rec c h l)) ≔
begin
  assume c h a l;
  have hunf : π (list_rec c h (Cons a l) =
      list_case c
        (λ x xs, h x xs
          (fapply (Lambda (Vset (rank (Cons a l))) (λ w, list_rec c h w)) xs))
        (Cons a l))
    { refine def_Vrec (λ w, list_rec c h w)
        (λ l2 g, list_case c (λ x xs, h x xs (fapply g xs)) l2)
        (λ w, list_rec_def c h w) (Cons a l) };
  rewrite hunf;
  have hcase : π (list_case c
        (λ x xs, h x xs
          (fapply (Lambda (Vset (rank (Cons a l))) (λ w, list_rec c h w)) xs))
        (Cons a l)
      = h a l (fapply (Lambda (Vset (rank (Cons a l))) (λ w, list_rec c h w)) l))
    { refine list_case_Cons c
        (λ x xs, h x xs
          (fapply (Lambda (Vset (rank (Cons a l))) (λ w, list_rec c h w)) xs))
        a l };
  rewrite hcase;
  have hbeta : π (fapply (Lambda (Vset (rank (Cons a l))) (λ w, list_rec c h w)) l
      = list_rec c h l)
    { refine beta (Vset (rank (Cons a l))) (λ w, list_rec c h w) l
        (VsetI l (rank (Cons a l)) (rank_Cons2 a l)) };
  rewrite hbeta;
  reflexivity
end;

// ===========================================================================
// List functions
// ===========================================================================

symbol length (l : τ ι) : τ ι ≔ list_rec empty (λ a l2 r, succ r) l;
symbol hd (l : τ ι) : τ ι ≔ list_rec empty (λ a l2 r, a) l;
symbol tl (l : τ ι) : τ ι ≔ list_rec Nil (λ a l2 r, l2) l;

// port-internal helpers — the primrec equations for length/hd/tl (definitional
// instances of list_rec_Nil/list_rec_Cons; in the .thy they are the primrec
// clauses themselves).
private opaque symbol length_Nil : π (length Nil = empty) ≔
  list_rec_Nil empty (λ a l2 r, succ r);
private opaque symbol length_Cons (a l : τ ι) :
  π (length (Cons a l) = succ (length l)) ≔
  list_rec_Cons empty (λ a2 l2 r, succ r) a l;
private opaque symbol hd_Cons (a l : τ ι) : π (hd (Cons a l) = a) ≔
  list_rec_Cons empty (λ a2 l2 r, a2) a l;
private opaque symbol tl_Nil : π (tl Nil = Nil) ≔
  list_rec_Nil Nil (λ a l2 r, l2);
private opaque symbol tl_Cons (a l : τ ι) : π (tl (Cons a l) = l) ≔
  list_rec_Cons Nil (λ a2 l2 r, l2) a l;

opaque symbol tl_type (l A : τ ι) : π (l ∈ list A) → π (tl l ∈ list A) ≔
begin
  assume l A hl;
  refine list_induct l A (λ w, tl w ∈ list A) hl _ _
  { refine ind_eq tl_Nil (λ w, w ∈ list A) (list_0I A) }
  { assume x y hx hy hIH;
    refine ind_eq (tl_Cons x y) (λ w, w ∈ list A) hy }
end;

// ===========================================================================
// map, set_of_list, app
// ===========================================================================

symbol map (f : τ ι → τ ι) (l : τ ι) : τ ι ≔
  list_rec Nil (λ a l2 r, Cons (f a) r) l;

symbol set_of_list (l : τ ι) : τ ι ≔ list_rec empty (λ a l2 r, cons a r) l;

symbol app (xs ys : τ ι) : τ ι ≔ list_rec ys (λ a l2 r, Cons a r) xs;
notation app infix right 60;

symbol rev (l : τ ι) : τ ι ≔ list_rec Nil (λ a l2 r, app r (Cons a Nil)) l;

symbol flat (l : τ ι) : τ ι ≔ list_rec Nil (λ a l2 r, app a r) l;

symbol list_add (l : τ ι) : τ ι ≔ list_rec empty (λ a l2 r, add a r) l;

symbol drop (i l : τ ι) : τ ι ≔ nat_rec i l (λ i2 r, tl r);

// port-internal helpers — the primrec equations for the functions above
// (definitional instances of list_rec_Nil/list_rec_Cons resp. nat_rec_0/succ).
private opaque symbol map_Nil (f : τ ι → τ ι) : π (map f Nil = Nil) ≔
  list_rec_Nil Nil (λ a l2 r, Cons (f a) r);
private opaque symbol map_Cons (f : τ ι → τ ι) (a l : τ ι) :
  π (map f (Cons a l) = Cons (f a) (map f l)) ≔
  list_rec_Cons Nil (λ a2 l2 r, Cons (f a2) r) a l;
private opaque symbol set_of_list_Nil : π (set_of_list Nil = empty) ≔
  list_rec_Nil empty (λ a l2 r, cons a r);
private opaque symbol set_of_list_Cons (a l : τ ι) :
  π (set_of_list (Cons a l) = cons a (set_of_list l)) ≔
  list_rec_Cons empty (λ a2 l2 r, cons a2 r) a l;
private opaque symbol app_Nil (ys : τ ι) : π (app Nil ys = ys) ≔
  list_rec_Nil ys (λ a l2 r, Cons a r);
private opaque symbol app_Cons (a l ys : τ ι) :
  π (app (Cons a l) ys = Cons a (app l ys)) ≔
  list_rec_Cons ys (λ a2 l2 r, Cons a2 r) a l;
private opaque symbol rev_Nil : π (rev Nil = Nil) ≔
  list_rec_Nil Nil (λ a l2 r, app r (Cons a Nil));
private opaque symbol rev_Cons (a l : τ ι) :
  π (rev (Cons a l) = app (rev l) (Cons a Nil)) ≔
  list_rec_Cons Nil (λ a2 l2 r, app r (Cons a2 Nil)) a l;
private opaque symbol flat_Nil : π (flat Nil = Nil) ≔
  list_rec_Nil Nil (λ a l2 r, app a r);
private opaque symbol flat_Cons (a l : τ ι) :
  π (flat (Cons a l) = app a (flat l)) ≔
  list_rec_Cons Nil (λ a2 l2 r, app a2 r) a l;
private opaque symbol list_add_Nil : π (list_add Nil = empty) ≔
  list_rec_Nil empty (λ a l2 r, add a r);
private opaque symbol list_add_Cons (a l : τ ι) :
  π (list_add (Cons a l) = add a (list_add l)) ≔
  list_rec_Cons empty (λ a2 l2 r, add a2 r) a l;
private opaque symbol drop_0 (l : τ ι) : π (drop empty l = l) ≔
  nat_rec_0 l (λ i2 r, tl r);
private opaque symbol drop_succ (i l : τ ι) :
  π (i ∈ omega) → π (drop (succ i) l = tl (drop i l)) ≔
  λ hi, nat_rec_succ i l (λ i2 r, tl r) hi;

// ===========================================================================
// (** Type checking -- proved by induction, as usual **))
// ===========================================================================

opaque symbol list_rec_type (l A c : τ ι) (h : τ ι → τ ι → τ ι → τ ι) (C : τ ι → τ ι) :
  π (l ∈ list A) → π (c ∈ C Nil) →
  (Π (x y r : τ ι), π (x ∈ A) → π (y ∈ list A) → π (r ∈ C y) →
    π (h x y r ∈ C (Cons x y))) →
  π (list_rec c h l ∈ C l) ≔
begin
  assume l A c h C hl hc hstep;
  refine list_induct l A (λ w, list_rec c h w ∈ C w) hl _ _
  { refine ind_eq (list_rec_Nil c h) (λ w, w ∈ C Nil) hc }
  { assume x y hx hy hIH;
    refine ind_eq (list_rec_Cons c h x y) (λ w, w ∈ C (Cons x y))
      (hstep x y (list_rec c h y) hx hy hIH) }
end;

// ===========================================================================
// map
// ===========================================================================

opaque symbol map_type (l A B : τ ι) (h : τ ι → τ ι) :
  π (l ∈ list A) → (Π (x : τ ι), π (x ∈ A) → π (h x ∈ B)) →
  π (map h l ∈ list B) ≔
begin
  assume l A B h hl hstep;
  refine list_induct l A (λ w, map h w ∈ list B) hl _ _
  { refine ind_eq (map_Nil h) (λ w, w ∈ list B) (list_0I B) }
  { assume x y hx hy hIH;
    refine ind_eq (map_Cons h x y) (λ w, w ∈ list B)
      (list_consI (h x) (map h y) B (hstep x hx) hIH) }
end;

opaque symbol map_type2 (l A : τ ι) (h : τ ι → τ ι) :
  π (l ∈ list A) → π (map h l ∈ list (RepFun A h)) ≔
begin
  assume l A h hl;
  refine map_type l A (RepFun A h) h hl _;
  assume x hx;
  refine RepFunI x A h hx
end;

// ===========================================================================
// length
// ===========================================================================

opaque symbol length_type (l A : τ ι) : π (l ∈ list A) → π (length l ∈ omega) ≔
begin
  assume l A hl;
  refine list_induct l A (λ w, length w ∈ omega) hl _ _
  { refine ind_eq length_Nil (λ w, w ∈ omega) zero_in_omega }
  { assume x y hx hy hIH;
    refine ind_eq (length_Cons x y) (λ w, w ∈ omega)
      (succ_in_omega (length y) hIH) }
end;

opaque symbol lt_length_in_nat (x l A : τ ι) :
  π (lt x (length l)) → π (l ∈ list A) → π (x ∈ omega) ≔
begin
  assume x l A hlt hl;
  refine lt_nat_in_nat x (length l) hlt (length_type l A hl)
end;

// ===========================================================================
// app
// ===========================================================================

opaque symbol app_type (xs ys A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (app xs ys ∈ list A) ≔
begin
  assume xs ys A hxs hys;
  refine list_induct xs A (λ w, app w ys ∈ list A) hxs _ _
  { refine ind_eq (app_Nil ys) (λ w, w ∈ list A) hys }
  { assume x y hx hy hIH;
    refine ind_eq (app_Cons x y ys) (λ w, w ∈ list A)
      (list_consI x (app y ys) A hx hIH) }
end;

// ===========================================================================
// rev
// ===========================================================================

opaque symbol rev_type (xs A : τ ι) : π (xs ∈ list A) → π (rev xs ∈ list A) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, rev w ∈ list A) hxs _ _
  { refine ind_eq rev_Nil (λ w, w ∈ list A) (list_0I A) }
  { assume x y hx hy hIH;
    refine ind_eq (rev_Cons x y) (λ w, w ∈ list A)
      (app_type (rev y) (Cons x Nil) A hIH (list_consI x Nil A hx (list_0I A))) }
end;

// ===========================================================================
// flat
// ===========================================================================

opaque symbol flat_type (ls A : τ ι) : π (ls ∈ list (list A)) → π (flat ls ∈ list A) ≔
begin
  assume ls A hls;
  refine list_induct ls (list A) (λ w, flat w ∈ list A) hls _ _
  { refine ind_eq flat_Nil (λ w, w ∈ list A) (list_0I A) }
  { assume x y hx hy hIH;
    refine ind_eq (flat_Cons x y) (λ w, w ∈ list A)
      (app_type x (flat y) A hx hIH) }
end;

// ===========================================================================
// set_of_list
// ===========================================================================

opaque symbol set_of_list_type (l A : τ ι) :
  π (l ∈ list A) → π (set_of_list l ∈ Pow A) ≔
begin
  assume l A hl;
  refine list_induct l A (λ w, set_of_list w ∈ Pow A) hl _ _
  { refine ind_eq set_of_list_Nil (λ w, w ∈ Pow A)
      (PowI empty A (empty_subset A)) }
  { assume x y hx hy hIH;
    refine ind_eq (set_of_list_Cons x y) (λ w, w ∈ Pow A) _;
    refine PowI (cons x (set_of_list y)) A _;
    assume z hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z x (set_of_list y)) hz) _ _
    { assume hzx; refine ind_eq hzx (λ w, w ∈ A) hx }
    { assume hzy; refine PowD (set_of_list y) A hIH z hzy } }
end;

opaque symbol set_of_list_append (xs ys A : τ ι) :
  π (xs ∈ list A) →
  π (set_of_list (app xs ys) = Un (set_of_list xs) (set_of_list ys)) ≔
begin
  assume xs ys A hxs;
  refine list_induct xs A
    (λ w, set_of_list (app w ys) = Un (set_of_list w) (set_of_list ys)) hxs _ _
  { simplify rule off;
    rewrite app_Nil; rewrite set_of_list_Nil;
    rewrite Un_empty_left; reflexivity }
  { assume x y hx hy hIH;
    rewrite app_Cons; rewrite set_of_list_Cons; rewrite set_of_list_Cons;
    rewrite hIH;
    rewrite cons_Un_distrib; reflexivity }
end;

// ===========================================================================
// list_add
// ===========================================================================

opaque symbol list_add_type (xs : τ ι) : π (xs ∈ list omega) → π (list_add xs ∈ omega) ≔
begin
  assume xs hxs;
  refine list_induct xs omega (λ w, list_add w ∈ omega) hxs _ _
  { refine ind_eq list_add_Nil (λ w, w ∈ omega) zero_in_omega }
  { assume x y hx hy hIH;
    refine ind_eq (list_add_Cons x y) (λ w, w ∈ omega) (add_type x (list_add y)) }
end;

// ===========================================================================
// More list functions: take, nth, list_update, filter, upt, min, max,
// zip_aux, zip, sublist, repeat
// (Grouped here, right after the base list functions/typing lemmas above,
//  because Lambdapi requires define-before-use.  The .thy itself scatters
//  these definitions earlier, interleaved with "drop" near the top of the
//  file (isabelle-src/List.thy lines 90-127), well before the "Aspects of
//  the datatype definition" section that the bootstrap already ported.)
// ===========================================================================

constant symbol take (n xs : τ ι) : τ ι;
constant symbol take_def (n xs : τ ι) :
  π (take n xs =
     fapply (list_rec (Lambda omega (λ _, Nil))
       (λ a l r, Lambda omega (λ n2, nat_case Nil (λ m, Cons a (fapply r m)) n2)) xs) n);

constant symbol nth (n xs : τ ι) : τ ι;
constant symbol nth_def (n xs : τ ι) :
  π (nth n xs =
     fapply (list_rec (Lambda omega (λ _, empty))
       (λ a l r, Lambda omega (λ n2, nat_case a (λ m, fapply r m) n2)) xs) n);

constant symbol list_update (xs i v : τ ι) : τ ι;
constant symbol list_update_def (xs i v : τ ι) :
  π (list_update xs i v =
     fapply (list_rec (Lambda omega (λ _, Nil))
       (λ u us vs, Lambda omega
         (λ n2, nat_case (Cons v us) (λ m, Cons u (fapply vs m)) n2)) xs) i);

symbol filter (P : τ ι → Prop) (l : τ ι) : τ ι ≔
  list_rec Nil (λ x xs r, If (P x) (Cons x r) r) l;

symbol upt (i j : τ ι) : τ ι ≔
  nat_rec j Nil (λ j2 r, If (le i j2) (app r (Cons j2 Nil)) Nil);

constant symbol min (x y : τ ι) : τ ι;
constant symbol min_def (x y : τ ι) : π (min x y = If (le x y) x y);
constant symbol max (x y : τ ι) : τ ι;
constant symbol max_def (x y : τ ι) : π (max x y = If (le x y) y x);

// zip_aux(B,l) recurses on l, closing over B; used to give zip(xs,ys) its
// type without needing ys's element type as an extra explicit argument.
symbol zip_aux (B l : τ ι) : τ ι ≔
  list_rec
    (Lambda (list B) (λ ys, list_case Nil (λ y l2, Nil) ys))
    (λ x l2 r,
       Lambda (list B) (λ ys, list_case Nil (λ y zs, Cons (Pair x y) (fapply r zs)) ys))
    l;

constant symbol zip (xs ys : τ ι) : τ ι;
constant symbol zip_def (xs ys : τ ι) :
  π (zip xs ys = fapply (zip_aux (set_of_list ys) xs) ys);

constant symbol sublist (xs A : τ ι) : τ ι;
constant symbol sublist_def (xs A : τ ι) :
  π (sublist xs A =
     map fst (filter (λ p, snd p ∈ A) (zip xs (upt empty (length xs)))));

// Named `list_repeat`, not `repeat` (Isabelle's name): `repeat` is a
// reserved tactical keyword in Lambdapi (the `repeat` tactic combinator).
symbol list_repeat (a n : τ ι) : τ ι ≔ nat_rec n Nil (λ n2 r, Cons a r);

// ===========================================================================
// (** drop **)
// ===========================================================================

opaque symbol drop_Nil (i : τ ι) : π (i ∈ omega) → π (drop i Nil = Nil) ≔
begin
  assume i hi;
  refine nat_induct (λ w, drop w Nil = Nil) _ _ i hi
  { refine drop_0 Nil }
  { assume n hn hIH;
    rewrite (drop_succ n Nil hn);
    rewrite hIH;
    refine tl_Nil }
end;

opaque symbol drop_succ_Cons (i a l : τ ι) :
  π (i ∈ omega) → π (drop (succ i) (Cons a l) = drop i l) ≔
begin
  assume i a l hi;
  refine nat_induct (λ w, drop (succ w) (Cons a l) = drop w l) _ _ i hi
  { simplify rule off;
    rewrite (drop_succ empty (Cons a l) zero_in_omega);
    rewrite drop_0; rewrite drop_0;
    refine tl_Cons a l }
  { assume n hn hIH;
    rewrite (drop_succ (succ n) (Cons a l) (succ_in_omega n hn));
    rewrite hIH;
    refine eq_sym (drop_succ n l hn) }
end;

opaque symbol drop_type (i l A : τ ι) :
  π (i ∈ omega) → π (l ∈ list A) → π (drop i l ∈ list A) ≔
begin
  assume i l A hi hl;
  refine nat_induct (λ w, drop w l ∈ list A) _ _ i hi
  { refine ind_eq (drop_0 l) (λ w, w ∈ list A) hl }
  { assume n hn hIH;
    refine ind_eq (drop_succ n l hn) (λ w, w ∈ list A)
      (tl_type (drop n l) A hIH) }
end;

// declare drop_succ [simp del]: an attribute toggle on the primrec equation
// already captured by `drop`'s definition above — no new content.

// ===========================================================================
// theorems about map
// ===========================================================================

opaque symbol map_ident (l A : τ ι) : π (l ∈ list A) → π (map (λ u, u) l = l) ≔
begin
  assume l A hl;
  refine list_induct l A (λ w, map (λ u, u) w = w) hl _ _
  { refine map_Nil (λ u, u) }
  { assume x y hx hy hIH;
    rewrite map_Cons;
    simplify rule off;
    rewrite hIH;
    reflexivity }
end;

opaque symbol map_compose (l A : τ ι) (h j : τ ι → τ ι) :
  π (l ∈ list A) → π (map h (map j l) = map (λ u, h (j u)) l) ≔
begin
  assume l A h j hl;
  refine list_induct l A (λ w, map h (map j w) = map (λ u, h (j u)) w) hl _ _
  { simplify rule off;
    rewrite (map_Nil j); rewrite (map_Nil h);
    rewrite (map_Nil (λ u, h (j u))); reflexivity }
  { assume x y hx hy hIH;
    rewrite (map_Cons j x y);
    rewrite (map_Cons h (j x) (map j y));
    rewrite (map_Cons (λ u, h (j u)) x y);
    simplify rule off;
    rewrite hIH;
    reflexivity }
end;

opaque symbol map_app_distrib (xs A ys : τ ι) (h : τ ι → τ ι) :
  π (xs ∈ list A) → π (map h (app xs ys) = app (map h xs) (map h ys)) ≔
begin
  assume xs A ys h hxs;
  refine list_induct xs A (λ w, map h (app w ys) = app (map h w) (map h ys)) hxs _ _
  { simplify rule off;
    rewrite (app_Nil ys); rewrite (map_Nil h);
    rewrite (app_Nil (map h ys)); reflexivity }
  { assume x y hx hy hIH;
    rewrite (app_Cons x y ys);
    rewrite (map_Cons h x (app y ys));
    rewrite (map_Cons h x y);
    rewrite (app_Cons (h x) (map h y) (map h ys));
    rewrite hIH;
    reflexivity }
end;

opaque symbol map_flat (ls A : τ ι) (h : τ ι → τ ι) :
  π (ls ∈ list (list A)) → π (map h (flat ls) = flat (map (map h) ls)) ≔
begin
  assume ls A h hls;
  refine list_induct ls (list A) (λ w, map h (flat w) = flat (map (map h) w)) hls _ _
  { simplify rule off;
    rewrite flat_Nil; rewrite (map_Nil h);
    rewrite (map_Nil (map h)); rewrite flat_Nil; reflexivity }
  { assume x y hx hy hIH;
    rewrite (flat_Cons x y);
    rewrite (map_app_distrib x A (flat y) h hx);
    rewrite (map_Cons (map h) x y);
    rewrite (flat_Cons (map h x) (map (map h) y));
    rewrite hIH;
    reflexivity }
end;

opaque symbol list_rec_map (l A c : τ ι) (d : τ ι → τ ι → τ ι → τ ι) (h : τ ι → τ ι) :
  π (l ∈ list A) →
  π (list_rec c d (map h l) = list_rec c (λ x xs r, d (h x) (map h xs) r) l) ≔
begin
  assume l A c d h hl;
  refine list_induct l A
    (λ w, list_rec c d (map h w) = list_rec c (λ x xs r, d (h x) (map h xs) r) w)
    hl _ _
  { simplify rule off;
    rewrite (map_Nil h);
    rewrite (list_rec_Nil c d);
    rewrite (list_rec_Nil c (λ x xs r, d (h x) (map h xs) r));
    reflexivity }
  { assume x y hx hy hIH;
    rewrite (map_Cons h x y);
    rewrite (list_rec_Cons c d (h x) (map h y));
    rewrite (list_rec_Cons c (λ x2 xs r, d (h x2) (map h xs) r) x y);
    simplify rule off;
    rewrite hIH;
    reflexivity }
end;

// list_CollectD = Collect_subset [THEN list_mono, THEN subsetD]
opaque symbol list_CollectD (A : τ ι) (P : τ ι → Prop) (c : τ ι) :
  π (c ∈ list (Collect A P)) → π (c ∈ list A) ≔
begin
  assume A P c h;
  refine list_mono (Collect A P) A (Collect_subset A P) c h
end;

opaque symbol map_list_Collect (l A : τ ι) (h j : τ ι → τ ι) :
  π (l ∈ list (Collect A (λ x, h x = j x))) → π (map h l = map j l) ≔
begin
  assume l A h j hl;
  refine list_induct l (Collect A (λ x, h x = j x)) (λ w, map h w = map j w) hl _ _
  { simplify rule off;
    rewrite (map_Nil h); rewrite (map_Nil j); reflexivity }
  { assume x y hx hy hIH;
    rewrite (map_Cons h x y);
    rewrite (map_Cons j x y);
    rewrite (CollectD2 x A (λ x2, h x2 = j x2) hx);
    rewrite hIH;
    reflexivity }
end;

// ===========================================================================
// theorems about length
// ===========================================================================

opaque symbol length_map (xs A : τ ι) (h : τ ι → τ ι) :
  π (xs ∈ list A) → π (length (map h xs) = length xs) ≔
begin
  assume xs A h hxs;
  refine list_induct xs A (λ w, length (map h w) = length w) hxs _ _
  { simplify rule off;
    rewrite (map_Nil h); reflexivity }
  { assume x y hx hy hIH;
    rewrite (map_Cons h x y);
    rewrite (length_Cons (h x) (map h y));
    rewrite (length_Cons x y);
    rewrite hIH;
    reflexivity }
end;

opaque symbol length_app (xs ys A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) →
  π (length (app xs ys) = add (length xs) (length ys)) ≔
begin
  assume xs ys A hxs hys;
  refine list_induct xs A (λ w, length (app w ys) = add (length w) (length ys)) hxs _ _
  { simplify rule off;
    rewrite (app_Nil ys); rewrite length_Nil;
    refine eq_sym (add_0 (length ys) (length_type ys A hys)) }
  { assume x y hx hy hIH;
    rewrite (app_Cons x y ys);
    rewrite (length_Cons x (app y ys));
    rewrite (length_Cons x y);
    rewrite hIH;
    refine eq_sym (add_succ (length y) (length ys)) }
end;

opaque symbol length_rev (xs A : τ ι) : π (xs ∈ list A) → π (length (rev xs) = length xs) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, length (rev w) = length w) hxs _ _
  { simplify rule off;
    rewrite rev_Nil; reflexivity }
  { assume x y hx hy hIH;
    rewrite (rev_Cons x y);
    rewrite (length_app (rev y) (Cons x Nil) A (rev_type y A hy)
      (list_consI x Nil A hx (list_0I A)));
    rewrite hIH;
    rewrite (length_Cons x Nil); rewrite length_Nil;
    rewrite (length_Cons x y);
    rewrite add_succ_right;
    rewrite (add_0_right (length y) (length_type y A hy));
    reflexivity }
end;

opaque symbol length_flat (ls A : τ ι) :
  π (ls ∈ list (list A)) → π (length (flat ls) = list_add (map length ls)) ≔
begin
  assume ls A hls;
  refine list_induct ls (list A) (λ w, length (flat w) = list_add (map length w)) hls _ _
  { simplify rule off;
    rewrite flat_Nil; rewrite length_Nil;
    rewrite (map_Nil length); rewrite list_add_Nil; reflexivity }
  { assume x y hx hy hIH;
    rewrite (flat_Cons x y);
    rewrite (length_app x (flat y) A hx (flat_type y A hy));
    rewrite hIH;
    rewrite (map_Cons length x y);
    rewrite (list_add_Cons (length x) (map length y));
    reflexivity }
end;

// ===========================================================================
// Length and drop
// ===========================================================================

// Lemma for the inductive step of drop_length
opaque symbol drop_length_Cons (xs A x : τ ι) :
  π (xs ∈ list A) →
  π (`∃ (z : τ ι), `∃ (zs : τ ι), drop (length xs) (Cons x xs) = Cons z zs) ≔
begin
  assume xs A x hxs;
  have hgen : π (`∀ (x2 : τ ι), `∃ (z : τ ι), `∃ (zs : τ ι),
      drop (length xs) (Cons x2 xs) = Cons z zs)
    { refine list_induct xs A
        (λ w, `∀ (x2 : τ ι), `∃ (z : τ ι), `∃ (zs : τ ι),
           drop (length w) (Cons x2 w) = Cons z zs) hxs _ _
      { assume x2;
        refine ∃ᵢ x2 (∃ᵢ Nil _);
        rewrite length_Nil;
        refine drop_0 (Cons x2 Nil) }
      { assume a y ha hy hIH x2;
        refine ∃ₑ (hIH a) _; assume z hz;
        refine ∃ₑ hz _; assume zs hzs;
        refine ∃ᵢ z (∃ᵢ zs _);
        rewrite (length_Cons a y);
        rewrite (drop_succ_Cons (length y) x2 (Cons a y) (length_type y A hy));
        refine hzs } };
  refine hgen x
end;

opaque symbol drop_length (l A i : τ ι) :
  π (l ∈ list A) → π (i ∈ length l) →
  π (`∃ (z : τ ι), `∃ (zs : τ ι), drop i l = Cons z zs) ≔
begin
  assume l A i hl hi;
  have hgen : π (`∀ (i2 : τ ι), (i2 ∈ length l) ⇒
      (`∃ (z : τ ι), `∃ (zs : τ ι), drop i2 l = Cons z zs))
    { refine list_induct l A
        (λ w, `∀ (i2 : τ ι), (i2 ∈ length w) ⇒
           (`∃ (z : τ ι), `∃ (zs : τ ι), drop i2 w = Cons z zs)) hl _ _
      { assume i2 hi2;
        have hie : π (i2 ∈ empty)
          { refine ind_eq (eq_sym length_Nil) (λ w, i2 ∈ w) hi2 };
        refine ⊥ₑ (emptyE i2 hie) }
      { assume a y ha hy hIH i2 hi2;
        have hly : π (length y ∈ omega) { refine length_type y A hy };
        have hi2s : π (i2 ∈ succ (length y))
          { refine ind_eq (eq_sym (length_Cons a y)) (λ w, i2 ∈ w) hi2 };
        have hdisj : π (i2 = length y ∨ i2 ∈ length y)
          { refine ∧ₑ₁ (succ_iff i2 (length y)) hi2s };
        refine ∨ₑ hdisj _ _
        { assume heq;
          refine ∃ₑ (drop_length_Cons y A a hy) _; assume z hz;
          refine ∃ₑ hz _; assume zs hzs;
          refine ∃ᵢ z (∃ᵢ zs _);
          rewrite heq;
          refine hzs }
        { assume hmem;
          have hi2n : π (i2 ∈ omega)
            { refine lt_nat_in_nat i2 (length y)
                (ltI i2 (length y) hmem (nat_into_Ord (length y) hly)) hly };
          refine natE i2
            (`∃ (z : τ ι), `∃ (zs : τ ι), drop i2 (Cons a y) = Cons z zs) hi2n _ _
          { assume h0;
            refine ∃ᵢ a (∃ᵢ y _);
            rewrite h0;
            refine drop_0 (Cons a y) }
          { assume x hx0 heq;
            have hxly : π (x ∈ length y)
              { refine Ord_trans x (succ x) (length y) (succI1 x)
                  (ind_eq (eq_sym heq) (λ w, w ∈ length y) hmem)
                  (nat_into_Ord (length y) hly) };
            refine ∃ₑ (hIH x hxly) _; assume z hz;
            refine ∃ₑ hz _; assume zs hzs;
            refine ∃ᵢ z (∃ᵢ zs _);
            rewrite heq;
            rewrite (drop_succ_Cons x a y hx0);
            refine hzs } } } };
  refine hgen i hi
end;

// ===========================================================================
// theorems about app
// ===========================================================================

opaque symbol app_right_Nil (xs A : τ ι) : π (xs ∈ list A) → π (app xs Nil = xs) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, app w Nil = w) hxs _ _
  { refine app_Nil Nil }
  { assume x y hx hy hIH;
    rewrite (app_Cons x y Nil);
    rewrite hIH;
    reflexivity }
end;

opaque symbol app_assoc (xs A ys zs : τ ι) :
  π (xs ∈ list A) → π (app (app xs ys) zs = app xs (app ys zs)) ≔
begin
  assume xs A ys zs hxs;
  refine list_induct xs A (λ w, app (app w ys) zs = app w (app ys zs)) hxs _ _
  { simplify rule off;
    rewrite (app_Nil ys); rewrite (app_Nil (app ys zs)); reflexivity }
  { assume x y hx hy hIH;
    rewrite (app_Cons x y ys);
    rewrite (app_Cons x (app y ys) zs);
    rewrite (app_Cons x y (app ys zs));
    rewrite hIH;
    reflexivity }
end;

opaque symbol flat_app_distrib (ls A ms : τ ι) :
  π (ls ∈ list (list A)) → π (flat (app ls ms) = app (flat ls) (flat ms)) ≔
begin
  assume ls A ms hls;
  refine list_induct ls (list A) (λ w, flat (app w ms) = app (flat w) (flat ms)) hls _ _
  { simplify rule off;
    rewrite (app_Nil ms); rewrite flat_Nil;
    rewrite (app_Nil (flat ms)); reflexivity }
  { assume x y hx hy hIH;
    rewrite (app_Cons x y ms);
    rewrite (flat_Cons x (app y ms));
    rewrite (flat_Cons x y);
    rewrite hIH;
    refine eq_sym (app_assoc x A (flat y) (flat ms) hx) }
end;

// ===========================================================================
// theorems about rev
// ===========================================================================

opaque symbol rev_map_distrib (l A : τ ι) (h : τ ι → τ ι) :
  π (l ∈ list A) → π (rev (map h l) = map h (rev l)) ≔
begin
  assume l A h hl;
  refine list_induct l A (λ w, rev (map h w) = map h (rev w)) hl _ _
  { simplify rule off;
    rewrite (map_Nil h); rewrite rev_Nil; rewrite (map_Nil h); reflexivity }
  { assume x y hx hy hIH;
    rewrite (map_Cons h x y);
    rewrite (rev_Cons (h x) (map h y));
    rewrite (rev_Cons x y);
    rewrite (map_app_distrib (rev y) A (Cons x Nil) h (rev_type y A hy));
    rewrite hIH;
    rewrite (map_Cons h x Nil);
    rewrite (map_Nil h);
    reflexivity }
end;

// Simplifier needs the premises as assumptions because rewriting will not
// instantiate the variable ?A in the rules' typing conditions; note that
// rev_type does not instantiate ?A.  Only the premises do.
opaque symbol rev_app_distrib (xs ys A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (rev (app xs ys) = app (rev ys) (rev xs)) ≔
begin
  assume xs ys A hxs hys;
  refine list_induct xs A (λ w, rev (app w ys) = app (rev ys) (rev w)) hxs _ _
  { simplify rule off;
    rewrite (app_Nil ys); rewrite rev_Nil;
    refine eq_sym (app_right_Nil (rev ys) A (rev_type ys A hys)) }
  { assume x y hx hy hIH;
    rewrite (app_Cons x y ys);
    rewrite (rev_Cons x (app y ys));
    rewrite (rev_Cons x y);
    rewrite hIH;
    refine app_assoc (rev ys) A (rev y) (Cons x Nil) (rev_type ys A hys) }
end;

opaque symbol rev_rev_ident (l A : τ ι) : π (l ∈ list A) → π (rev (rev l) = l) ≔
begin
  assume l A hl;
  refine list_induct l A (λ w, rev (rev w) = w) hl _ _
  { simplify rule off;
    rewrite rev_Nil; rewrite rev_Nil; reflexivity }
  { assume x y hx hy hIH;
    rewrite (rev_Cons x y);
    rewrite (rev_app_distrib (rev y) (Cons x Nil) A (rev_type y A hy)
      (list_consI x Nil A hx (list_0I A)));
    rewrite hIH;
    rewrite (rev_Cons x Nil);
    rewrite rev_Nil;
    rewrite (app_Nil (Cons x Nil));
    rewrite (app_Cons x Nil y);
    rewrite (app_Nil y);
    reflexivity }
end;

opaque symbol rev_flat (ls A : τ ι) :
  π (ls ∈ list (list A)) → π (rev (flat ls) = flat (map rev (rev ls))) ≔
begin
  assume ls A hls;
  refine list_induct ls (list A) (λ w, rev (flat w) = flat (map rev (rev w))) hls _ _
  { simplify rule off;
    rewrite flat_Nil; rewrite rev_Nil;
    rewrite (map_Nil rev); rewrite flat_Nil; reflexivity }
  { assume x y hx hy hIH;
    rewrite (flat_Cons x y);
    rewrite (rev_app_distrib x (flat y) A hx (flat_type y A hy));
    rewrite hIH;
    rewrite (rev_Cons x y);
    rewrite (map_app_distrib (rev y) (list A) (Cons x Nil) rev (rev_type y (list A) hy));
    rewrite (flat_app_distrib (map rev (rev y)) A (map rev (Cons x Nil))
      (map_type (rev y) (list A) (list A) rev (rev_type y (list A) hy)
        (λ u hu, rev_type u A hu)));
    rewrite (map_Cons rev x Nil);
    rewrite (map_Nil rev);
    rewrite (flat_Cons (rev x) Nil);
    rewrite flat_Nil;
    rewrite (app_right_Nil (rev x) A (rev_type x A hx));
    reflexivity }
end;

// ===========================================================================
// theorems about list_add
// ===========================================================================

opaque symbol list_add_app (xs ys : τ ι) :
  π (xs ∈ list omega) → π (ys ∈ list omega) →
  π (list_add (app xs ys) = add (list_add ys) (list_add xs)) ≔
begin
  assume xs ys hxs hys;
  refine list_induct xs omega
    (λ w, list_add (app w ys) = add (list_add ys) (list_add w)) hxs _ _
  { simplify rule off;
    rewrite (app_Nil ys); rewrite list_add_Nil;
    refine eq_sym (add_0_right (list_add ys) (list_add_type ys hys)) }
  { assume x y hx hy hIH;
    rewrite (app_Cons x y ys);
    rewrite (list_add_Cons x (app y ys));
    rewrite (list_add_Cons x y);
    rewrite hIH;
    refine add_left_commute x (list_add ys) (list_add y) }
end;

opaque symbol list_add_rev (l : τ ι) :
  π (l ∈ list omega) → π (list_add (rev l) = list_add l) ≔
begin
  assume l hl;
  refine list_induct l omega (λ w, list_add (rev w) = list_add w) hl _ _
  { simplify rule off;
    rewrite rev_Nil; reflexivity }
  { assume x y hx hy hIH;
    rewrite (rev_Cons x y);
    rewrite (list_add_app (rev y) (Cons x Nil) (rev_type y omega hy)
      (list_consI x Nil omega hx (list_0I omega)));
    rewrite hIH;
    rewrite (list_add_Cons x Nil);
    rewrite list_add_Nil;
    rewrite (list_add_Cons x y);
    rewrite (add_0_right x hx);
    reflexivity }
end;

opaque symbol list_add_flat (ls : τ ι) :
  π (ls ∈ list (list omega)) → π (list_add (flat ls) = list_add (map list_add ls)) ≔
begin
  assume ls hls;
  refine list_induct ls (list omega)
    (λ w, list_add (flat w) = list_add (map list_add w)) hls _ _
  { simplify rule off;
    rewrite flat_Nil; rewrite (map_Nil list_add); reflexivity }
  { assume x y hx hy hIH;
    rewrite (flat_Cons x y);
    rewrite (list_add_app x (flat y) hx (flat_type y omega hy));
    rewrite hIH;
    rewrite (map_Cons list_add x y);
    rewrite (list_add_Cons (list_add x) (map list_add y));
    refine add_commute (list_add (map list_add y)) (list_add x) }
end;

// ===========================================================================
// New induction rules
// ===========================================================================

opaque symbol list_append_induct (l A : τ ι) (P : τ ι → Prop) :
  π (l ∈ list A) → π (P Nil) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ list A) → π (P y) → π (P (app y (Cons x Nil)))) →
  π (P l) ≔
begin
  assume l A P hl hNil hstep;
  have hrev : π (P (rev (rev l)))
    { refine list_induct (rev l) A (λ w, P (rev w)) (rev_type l A hl) _ _
      { refine ind_eq rev_Nil P hNil }
      { assume x y hx hy hIH;
        refine ind_eq (rev_Cons x y) P
          (hstep x (rev y) hx (rev_type y A hy) hIH) } };
  refine ind_eq (eq_sym (rev_rev_ident l A hl)) P hrev
end;

opaque symbol list_complete_induct_lemma (A : τ ι) (P : τ ι → Prop)
  (ih : Π (l : τ ι), π (l ∈ list A) →
        π (Ball (list A) (λ l', lt (length l') (length l) ⇒ P l')) → π (P l))
  (n l : τ ι) :
  π (n ∈ omega) → π (l ∈ list A) → π (lt (length l) n) → π (P l) ≔
begin
  assume A P ih n l hn hl hlt;
  have hmain : π (Ball omega (λ w, Ball (list A) (λ l2, lt (length l2) w ⇒ P l2)))
    { refine nat_induct (λ w, Ball (list A) (λ l2, lt (length l2) w ⇒ P l2)) _ _
      { assume l2 hl2 hlt2;
        refine ⊥ₑ (not_lt0 (length l2) hlt2) }
      { assume n2 hn2 hIH l2 hl2 hlt2;
        refine ih l2 hl2 _;
        assume l' hl' hlt';
        refine hIH l' hl' (lt_trans2 (length l') (length l2) n2 hlt' hlt2) } };
  refine hmain n hn l hl hlt
end;

opaque symbol list_complete_induct (l A : τ ι) (P : τ ι → Prop) :
  π (l ∈ list A) →
  (Π (l2 : τ ι), π (l2 ∈ list A) →
    π (Ball (list A) (λ l', lt (length l') (length l2) ⇒ P l')) → π (P l2)) →
  π (P l) ≔
begin
  assume l A P hl ih;
  refine list_complete_induct_lemma A P ih (succ (length l)) l
    (succ_in_omega (length l) (length_type l A hl)) hl _;
  refine le_refl (length l) (nat_into_Ord (length l) (length_type l A hl))
end;

// ===========================================================================
// (** min FIXME: replace by Int! **)
// Min theorems are also true for i, j ordinals
// ===========================================================================

opaque symbol min_sym (i j : τ ι) : π (i ∈ omega) → π (j ∈ omega) → π (min i j = min j i) ≔
begin
  assume i j hi hj;
  have hOi : π (Ord i) { refine nat_into_Ord i hi };
  have hOj : π (Ord j) { refine nat_into_Ord j hj };
  rewrite (min_def i j); rewrite (min_def j i);
  refine ∨ₑ (Ord_linear i j hOi hOj) _ _
  { assume hij;
    have hle : π (le i j) { refine leI i j hij hOj };
    have hnle : π (¬ (le j i))
      { assume hle2; refine le_imp_not_lt i j hle2 (ltI i j hij hOj) };
    rewrite (If_P (le i j) i j hle);
    rewrite (If_not_P (le j i) j i hnle);
    reflexivity }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume heq; rewrite heq; reflexivity }
    { assume hji;
      have hle : π (le j i) { refine leI j i hji hOi };
      have hnle : π (¬ (le i j))
        { assume hle2; refine le_imp_not_lt j i hle2 (ltI j i hji hOi) };
      rewrite (If_not_P (le i j) i j hnle);
      rewrite (If_P (le j i) j i hle);
      reflexivity } }
end;

opaque symbol min_type (i j : τ ι) : π (i ∈ omega) → π (j ∈ omega) → π (min i j ∈ omega) ≔
begin
  assume i j hi hj;
  rewrite min_def;
  refine ∨ₑ (em (le i j)) _ _
  { assume h; rewrite (If_P (le i j) i j h); refine hi }
  { assume h; rewrite (If_not_P (le i j) i j h); refine hj }
end;

opaque symbol min_0 (i : τ ι) : π (i ∈ omega) → π (min empty i = empty) ≔
begin
  assume i hi;
  rewrite min_def;
  rewrite (If_P (le empty i) empty i (Ord_0_le i (nat_into_Ord i hi)));
  reflexivity
end;

opaque symbol min_02 (i : τ ι) : π (i ∈ omega) → π (min i empty = empty) ≔
begin
  assume i hi;
  rewrite min_def;
  refine ∨ₑ (em (le i empty)) _ _
  { assume h; rewrite (If_P (le i empty) i empty h); refine le0D i h }
  { assume h; rewrite (If_not_P (le i empty) i empty h); reflexivity }
end;

opaque symbol lt_min_iff (i j k : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (k ∈ omega) →
  π (lt i (min j k) ⇔ (lt i j ∧ lt i k)) ≔
begin
  assume i j k hi hj hk;
  have hOj : π (Ord j) { refine nat_into_Ord j hj };
  have hOk : π (Ord k) { refine nat_into_Ord k hk };
  rewrite min_def;
  refine ∨ₑ (em (le j k)) _ _
  { assume h;
    rewrite (If_P (le j k) j k h);
    apply ∧ᵢ
    { assume hlt;
      refine ∧ᵢ hlt (lt_trans2 i j k hlt h) }
    { assume hconj; refine ∧ₑ₁ hconj } }
  { assume h;
    rewrite (If_not_P (le j k) j k h);
    have hkj : π (lt k j)
      { refine succ_leE k j (not_lt_imp_le j (succ k) hOj (Ord_succ k hOk) h) };
    apply ∧ᵢ
    { assume hlt;
      refine ∧ᵢ (lt_trans i k j hlt hkj) hlt }
    { assume hconj; refine ∧ₑ₂ hconj } }
end;

opaque symbol min_succ_succ (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (min (succ i) (succ j) = succ (min i j)) ≔
begin
  assume i j hi hj;
  have hOj : π (Ord j) { refine nat_into_Ord j hj };
  rewrite (min_def (succ i) (succ j)); rewrite (min_def i j);
  refine ∨ₑ (em (le i j)) _ _
  { assume h;
    have hles : π (le (succ i) (succ j))
      { refine succ_leI i (succ j) (Ord_succ j hOj) (ltD i (succ j) h) };
    rewrite (If_P (le (succ i) (succ j)) (succ i) (succ j) hles);
    rewrite (If_P (le i j) i j h);
    reflexivity }
  { assume h;
    have hnles : π (¬ (le (succ i) (succ j)))
      { assume h2; refine h (succ_leE i (succ j) h2) };
    rewrite (If_not_P (le (succ i) (succ j)) (succ i) (succ j) hnles);
    rewrite (If_not_P (le i j) i j h);
    reflexivity }
end;

// ===========================================================================
// more theorems about lists
// ===========================================================================

// (** filter **)

// port-internal helpers — filter's primrec equations
private opaque symbol filter_Nil (P : τ ι → Prop) : π (filter P Nil = Nil) ≔
  list_rec_Nil Nil (λ x xs r, If (P x) (Cons x r) r);
private opaque symbol filter_Cons (P : τ ι → Prop) (x xs : τ ι) :
  π (filter P (Cons x xs) = If (P x) (Cons x (filter P xs)) (filter P xs)) ≔
  list_rec_Cons Nil (λ x2 xs2 r, If (P x2) (Cons x2 r) r) x xs;

opaque symbol filter_append (xs A ys : τ ι) (P : τ ι → Prop) :
  π (xs ∈ list A) → π (filter P (app xs ys) = app (filter P xs) (filter P ys)) ≔
begin
  assume xs A ys P hxs;
  refine list_induct xs A
    (λ w, filter P (app w ys) = app (filter P w) (filter P ys)) hxs _ _
  { simplify rule off;
    rewrite (app_Nil ys); rewrite (filter_Nil P);
    rewrite (app_Nil (filter P ys)); reflexivity }
  { assume x y hx hy hIH;
    rewrite (app_Cons x y ys);
    rewrite (filter_Cons P x (app y ys));
    rewrite (filter_Cons P x y);
    rewrite hIH;
    refine ∨ₑ (em (P x)) _ _
    { assume hP;
      rewrite (If_P (P x) (Cons x (app (filter P y) (filter P ys))) (app (filter P y) (filter P ys)) hP);
      rewrite (If_P (P x) (Cons x (filter P y)) (filter P y) hP);
      rewrite (app_Cons x (filter P y) (filter P ys));
      reflexivity }
    { assume hnP;
      rewrite (If_not_P (P x) (Cons x (app (filter P y) (filter P ys))) (app (filter P y) (filter P ys)) hnP);
      rewrite (If_not_P (P x) (Cons x (filter P y)) (filter P y) hnP);
      reflexivity } }
end;

opaque symbol filter_type (xs A : τ ι) (P : τ ι → Prop) :
  π (xs ∈ list A) → π (filter P xs ∈ list A) ≔
begin
  assume xs A P hxs;
  refine list_induct xs A (λ w, filter P w ∈ list A) hxs _ _
  { refine ind_eq (filter_Nil P) (λ w, w ∈ list A) (list_0I A) }
  { assume x y hx hy hIH;
    refine ind_eq (filter_Cons P x y) (λ w, w ∈ list A) _;
    refine ∨ₑ (em (P x)) _ _
    { assume hP;
      refine ind_eq (If_P (P x) (Cons x (filter P y)) (filter P y) hP)
        (λ w, w ∈ list A) (list_consI x (filter P y) A hx hIH) }
    { assume hnP;
      refine ind_eq (If_not_P (P x) (Cons x (filter P y)) (filter P y) hnP)
        (λ w, w ∈ list A) hIH } }
end;

opaque symbol length_filter (xs A : τ ι) (P : τ ι → Prop) :
  π (xs ∈ list A) → π (le (length (filter P xs)) (length xs)) ≔
begin
  assume xs A P hxs;
  refine list_induct xs A (λ w, le (length (filter P w)) (length w)) hxs _ _
  { simplify rule off;
    rewrite (filter_Nil P); rewrite length_Nil;
    refine le_refl empty Ord_0 }
  { assume x y hx hy hIH;
    have hOly : π (Ord (length y))
      { refine nat_into_Ord (length y) (length_type y A hy) };
    rewrite (filter_Cons P x y);
    rewrite (length_Cons x y);
    refine ∨ₑ (em (P x)) _ _
    { assume hP;
      rewrite (If_P (P x) (Cons x (filter P y)) (filter P y) hP);
      rewrite (length_Cons x (filter P y));
      refine succ_leI (length (filter P y)) (succ (length y))
        (Ord_succ (length y) hOly) (ltD (length (filter P y)) (succ (length y)) hIH) }
    { assume hnP;
      rewrite (If_not_P (P x) (Cons x (filter P y)) (filter P y) hnP);
      refine lt_trans (length (filter P y)) (succ (length y)) (succ (succ (length y)))
        hIH (le_refl (succ (length y)) (Ord_succ (length y) hOly)) } }
end;

opaque symbol filter_is_subset (xs A : τ ι) (P : τ ι → Prop) :
  π (xs ∈ list A) → π (set_of_list (filter P xs) ⊆ set_of_list xs) ≔
begin
  assume xs A P hxs;
  refine list_induct xs A (λ w, set_of_list (filter P w) ⊆ set_of_list w) hxs _ _
  { refine ind_eq (filter_Nil P) (λ w, set_of_list w ⊆ set_of_list Nil)
      (subset_refl (set_of_list Nil)) }
  { assume x y hx hy hIH;
    assume z hz;
    have hz2 : π (z ∈ set_of_list (If (P x) (Cons x (filter P y)) (filter P y)))
      { refine ind_eq (eq_sym (filter_Cons P x y)) (λ w, z ∈ set_of_list w) hz };
    have hgoal : π (z ∈ cons x (set_of_list y))
      { refine ∨ₑ (em (P x)) _ _
        { assume hP;
          have hz3 : π (z ∈ set_of_list (Cons x (filter P y)))
            { refine ind_eq (eq_sym (If_P (P x) (Cons x (filter P y)) (filter P y) hP))
                (λ w, z ∈ set_of_list w) hz2 };
          have hz4 : π (z ∈ cons x (set_of_list (filter P y)))
            { refine ind_eq (eq_sym (set_of_list_Cons x (filter P y)))
                (λ w, z ∈ w) hz3 };
          refine ∨ₑ (∧ₑ₁ (cons_iff z x (set_of_list (filter P y))) hz4) _ _
          { assume hzx;
            refine ind_eq hzx (λ w, w ∈ cons x (set_of_list y))
              (consI1 x (set_of_list y)) }
          { assume hzin;
            refine consI2 z x (set_of_list y) (hIH z hzin) } }
        { assume hnP;
          have hz3 : π (z ∈ set_of_list (filter P y))
            { refine ind_eq (eq_sym (If_not_P (P x) (Cons x (filter P y)) (filter P y) hnP))
                (λ w, z ∈ set_of_list w) hz2 };
          refine consI2 z x (set_of_list y) (hIH z hz3) } };
    refine ind_eq (set_of_list_Cons x y) (λ w, z ∈ w) hgoal }
end;

opaque symbol filter_False (xs A : τ ι) : π (xs ∈ list A) → π (filter (λ p, ⊥) xs = Nil) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, filter (λ p, ⊥) w = Nil) hxs _ _
  { refine filter_Nil (λ p, ⊥) }
  { assume x y hx hy hIH;
    rewrite (filter_Cons (λ p, ⊥) x y);
    simplify rule off;
    have hnP : π (¬ ⊥) { assume h; refine h };
    rewrite (If_not_P ⊥ (Cons x (filter (λ p, ⊥) y)) (filter (λ p, ⊥) y) hnP);
    refine hIH }
end;

opaque symbol filter_True (xs A : τ ι) : π (xs ∈ list A) → π (filter (λ p, ⊤) xs = xs) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, filter (λ p, ⊤) w = w) hxs _ _
  { refine filter_Nil (λ p, ⊤) }
  { assume x y hx hy hIH;
    rewrite (filter_Cons (λ p, ⊤) x y);
    simplify rule off;
    rewrite (If_P ⊤ (Cons x (filter (λ p, ⊤) y)) (filter (λ p, ⊤) y) ⊤ᵢ);
    rewrite hIH;
    reflexivity }
end;

// (** length **)

opaque symbol length_is_0_iff (xs A : τ ι) :
  π (xs ∈ list A) → π (length xs = empty ⇔ xs = Nil) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, length w = empty ⇔ w = Nil) hxs _ _
  { apply ∧ᵢ
    { assume h; reflexivity }
    { assume h; refine length_Nil } }
  { assume x y hx hy hIH;
    apply ∧ᵢ
    { assume h;
      have h2 : π (succ (length y) = empty)
        { refine ind_eq (eq_sym (length_Cons x y)) (λ w, w = empty) h };
      refine ⊥ₑ (succ_neq_0 (length y) h2) }
    { assume h; refine ⊥ₑ (Nil_Cons_iff x y (eq_sym h)) } }
end;

opaque symbol length_is_0_iff2 (xs A : τ ι) :
  π (xs ∈ list A) → π (empty = length xs ⇔ xs = Nil) ≔
begin
  assume xs A hxs;
  apply ∧ᵢ
  { assume h; refine ∧ₑ₁ (length_is_0_iff xs A hxs) (eq_sym h) }
  { assume h; refine eq_sym (∧ₑ₂ (length_is_0_iff xs A hxs) h) }
end;

opaque symbol length_tl (xs A : τ ι) :
  π (xs ∈ list A) → π (length (tl xs) = diff (length xs) (succ empty)) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, length (tl w) = diff (length w) (succ empty)) hxs _ _
  { simplify rule off;
    rewrite tl_Nil; rewrite length_Nil;
    refine eq_sym (diff_0_eq_0 (succ empty)) }
  { assume x y hx hy hIH;
    rewrite (tl_Cons x y);
    rewrite (length_Cons x y);
    rewrite diff_succ_succ;
    rewrite (diff_0 (length y));
    refine eq_sym (natify_ident (length y) (length_type y A hy)) }
end;

opaque symbol length_greater_0_iff (xs A : τ ι) :
  π (xs ∈ list A) → π (lt empty (length xs) ⇔ xs ≠ Nil) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, lt empty (length w) ⇔ w ≠ Nil) hxs _ _
  { apply ∧ᵢ
    { assume h heq;
      refine not_lt0 empty (ind_eq (eq_sym length_Nil) (λ w, lt empty w) h) }
    { assume h; refine ⊥ₑ (h (eq_refl Nil)) } }
  { assume x y hx hy hIH;
    apply ∧ᵢ
    { assume h heq;
      refine Nil_Cons_iff x y (eq_sym heq) }
    { assume h;
      refine ind_eq (length_Cons x y) (λ w, lt empty w)
        (Ord_0_le (length y) (nat_into_Ord (length y) (length_type y A hy))) } }
end;

opaque symbol length_succ_iff (xs A n : τ ι) :
  π (xs ∈ list A) →
  π (length xs = succ n ⇔ (`∃ (y : τ ι), `∃ (ys : τ ι), xs = Cons y ys ∧ length ys = n)) ≔
begin
  assume xs A n hxs;
  refine list_induct xs A
    (λ w, length w = succ n ⇔ (`∃ (y : τ ι), `∃ (ys : τ ι), w = Cons y ys ∧ length ys = n))
    hxs _ _
  { apply ∧ᵢ
    { assume h;
      have h2 : π (succ n = empty)
        { refine eq_sym (ind_eq (eq_sym length_Nil) (λ w, w = succ n) h) };
      refine ⊥ₑ (succ_neq_0 n h2) }
    { assume hex;
      refine ∃ₑ hex _; assume z hz;
      refine ∃ₑ hz _; assume zs hzs;
      refine ⊥ₑ (Nil_Cons_iff z zs (∧ₑ₁ hzs)) } }
  { assume x y hx hy hIH;
    apply ∧ᵢ
    { assume h;
      have h2 : π (succ (length y) = succ n)
        { refine ind_eq (eq_sym (length_Cons x y)) (λ w, w = succ n) h };
      refine ∃ᵢ x (∃ᵢ y (∧ᵢ (eq_refl (Cons x y)) (succ_inject (length y) n h2))) }
    { assume hex;
      refine ∃ₑ hex _; assume z hz;
      refine ∃ₑ hz _; assume zs hzs;
      have hxy : π (x = z ∧ y = zs)
        { refine ∧ₑ₁ (Cons_iff x y z zs) (∧ₑ₁ hzs) };
      rewrite (length_Cons x y);
      rewrite (∧ₑ₂ hxy);
      rewrite (∧ₑ₂ hzs);
      reflexivity } }
end;

// (** more theorems about append **)

opaque symbol append_is_Nil_iff (xs A ys : τ ι) :
  π (xs ∈ list A) → π (app xs ys = Nil ⇔ (xs = Nil ∧ ys = Nil)) ≔
begin
  assume xs A ys hxs;
  refine list_induct xs A (λ w, app w ys = Nil ⇔ (w = Nil ∧ ys = Nil)) hxs _ _
  { apply ∧ᵢ
    { assume h;
      refine ∧ᵢ (eq_refl Nil) (ind_eq (eq_sym (app_Nil ys)) (λ w, w = Nil) h) }
    { assume h;
      rewrite (∧ₑ₂ h);
      refine app_Nil Nil } }
  { assume x y hx hy hIH;
    apply ∧ᵢ
    { assume h;
      have h2 : π (Cons x (app y ys) = Nil)
        { refine ind_eq (eq_sym (app_Cons x y ys)) (λ w, w = Nil) h };
      refine ⊥ₑ (Nil_Cons_iff x (app y ys) (eq_sym h2)) }
    { assume h;
      refine ⊥ₑ (Nil_Cons_iff x y (eq_sym (∧ₑ₁ h))) } }
end;

opaque symbol append_is_Nil_iff2 (xs A ys : τ ι) :
  π (xs ∈ list A) → π (Nil = app xs ys ⇔ (xs = Nil ∧ ys = Nil)) ≔
begin
  assume xs A ys hxs;
  apply ∧ᵢ
  { assume h; refine ∧ₑ₁ (append_is_Nil_iff xs A ys hxs) (eq_sym h) }
  { assume h; refine eq_sym (∧ₑ₂ (append_is_Nil_iff xs A ys hxs) h) }
end;

opaque symbol append_left_is_self_iff (xs A ys : τ ι) :
  π (xs ∈ list A) → π (app xs ys = xs ⇔ ys = Nil) ≔
begin
  assume xs A ys hxs;
  refine list_induct xs A (λ w, app w ys = w ⇔ ys = Nil) hxs _ _
  { apply ∧ᵢ
    { assume h; refine ind_eq (eq_sym (app_Nil ys)) (λ w, w = Nil) h }
    { assume h; rewrite h; refine app_Nil Nil } }
  { assume x y hx hy hIH;
    apply ∧ᵢ
    { assume h;
      have h2 : π (Cons x (app y ys) = Cons x y)
        { refine ind_eq (eq_sym (app_Cons x y ys)) (λ w, w = Cons x y) h };
      refine ∧ₑ₁ hIH (∧ₑ₂ (∧ₑ₁ (Cons_iff x (app y ys) x y) h2)) }
    { assume h;
      rewrite h;
      refine app_right_Nil (Cons x y) A (list_consI x y A hx hy) } }
end;

opaque symbol append_left_is_self_iff2 (xs A ys : τ ι) :
  π (xs ∈ list A) → π (xs = app xs ys ⇔ ys = Nil) ≔
begin
  assume xs A ys hxs;
  apply ∧ᵢ
  { assume h; refine ∧ₑ₁ (append_left_is_self_iff xs A ys hxs) (eq_sym h) }
  { assume h; refine eq_sym (∧ₑ₂ (append_left_is_self_iff xs A ys hxs) h) }
end;

// TOO SLOW as a default simprule!
opaque symbol append_left_is_Nil_iff (xs ys zs A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (zs ∈ list A) →
  π (length ys = length zs) →
  π (app xs ys = zs ⇔ (xs = Nil ∧ ys = zs)) ≔
begin
  assume xs ys zs A hxs hys hzs hlen;
  apply ∧ᵢ
  { assume h;
    // lengths: |zs| = |xs| + |ys| = |xs| + |zs|, so |xs| = 0, so xs = Nil
    have hlzs : π (length zs = add (length xs) (length ys))
      { rewrite left h; refine length_app xs ys A hxs hys };
    have h3 : π (length zs = add (length xs) (length zs))
      { refine ind_eq (eq_sym hlen) (λ w, length zs = add (length xs) w) hlzs };
    have h4 : π (natify (length xs) = empty)
      { rewrite left (diff_add_inverse2 (length xs) (length zs));
        rewrite left h3;
        refine diff_self_eq_0 (length zs) };
    have h5 : π (length xs = empty)
      { rewrite left (natify_ident (length xs) (length_type xs A hxs));
        refine h4 };
    have hxsNil : π (xs = Nil) { refine ∧ₑ₁ (length_is_0_iff xs A hxs) h5 };
    refine ∧ᵢ hxsNil _;
    have h6 : π (app Nil ys = zs)
      { refine ind_eq (eq_sym hxsNil) (λ w, app w ys = zs) h };
    refine ind_eq (eq_sym (app_Nil ys)) (λ w, w = zs) h6 }
  { assume h;
    rewrite (∧ₑ₁ h);
    rewrite (app_Nil ys);
    refine ∧ₑ₂ h }
end;

// TOO SLOW as a default simprule!
opaque symbol append_left_is_Nil_iff2 (xs ys zs A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (zs ∈ list A) →
  π (length ys = length zs) →
  π (zs = app ys xs ⇔ (xs = Nil ∧ ys = zs)) ≔
begin
  assume xs ys zs A hxs hys hzs hlen;
  apply ∧ᵢ
  { assume h;
    have hlzs : π (length zs = add (length ys) (length xs))
      { rewrite h; refine length_app ys xs A hys hxs };
    have h3 : π (length zs = add (length zs) (length xs))
      { refine ind_eq (eq_sym hlen) (λ w, length zs = add w (length xs)) hlzs };
    have h4 : π (natify (length xs) = empty)
      { rewrite left (diff_add_inverse (length zs) (length xs));
        rewrite left h3;
        refine diff_self_eq_0 (length zs) };
    have h5 : π (length xs = empty)
      { rewrite left (natify_ident (length xs) (length_type xs A hxs));
        refine h4 };
    have hxsNil : π (xs = Nil) { refine ∧ₑ₁ (length_is_0_iff xs A hxs) h5 };
    refine ∧ᵢ hxsNil _;
    rewrite h; rewrite hxsNil;
    refine eq_sym (app_right_Nil ys A hys) }
  { assume h;
    rewrite (∧ₑ₁ h);
    rewrite (app_right_Nil ys A hys);
    refine eq_sym (∧ₑ₂ h) }
end;

opaque symbol append_eq_append_iff (xs A ys us vs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (length xs = length ys) →
  π (app xs us = app ys vs ⇔ (xs = ys ∧ us = vs)) ≔
begin
  assume xs A ys us vs hxs hys hlen;
  have hgen : π (`∀ (ys2 : τ ι), (ys2 ∈ list A) ⇒ (length xs = length ys2) ⇒
      (app xs us = app ys2 vs ⇔ (xs = ys2 ∧ us = vs)))
    { refine list_induct xs A
        (λ w, `∀ (ys2 : τ ι), (ys2 ∈ list A) ⇒ (length w = length ys2) ⇒
           (app w us = app ys2 vs ⇔ (w = ys2 ∧ us = vs))) hxs _ _
      { assume ys2 hys2 hlen2;
        have h0 : π (empty = length ys2)
          { refine ind_eq (eq_sym length_Nil) (λ w, w = length ys2) hlen2 };
        have hys2Nil : π (ys2 = Nil)
          { refine ∧ₑ₁ (length_is_0_iff2 ys2 A hys2) h0 };
        apply ∧ᵢ
        { assume h;
          have h2 : π (app Nil us = app Nil vs)
            { refine ind_eq (eq_sym hys2Nil) (λ w, app Nil us = app w vs) h };
          have h3 : π (us = vs)
            { rewrite left (app_Nil us); rewrite left (app_Nil vs); refine h2 };
          refine ∧ᵢ (eq_sym hys2Nil) h3 }
        { assume hc;
          rewrite (∧ₑ₂ hc);
          rewrite left (∧ₑ₁ hc);
          reflexivity } }
      { assume x y hx hy hIH ys2 hys2 hlen2;
        refine ∨ₑ (list_cases ys2 A hys2) _ _
        { assume hys2Nil;
          have h0 : π (succ (length y) = empty)
            { have h1 : π (length (Cons x y) = length Nil)
                { refine ind_eq (eq_sym hys2Nil) (λ w, length (Cons x y) = length w) hlen2 };
              have h2 : π (length (Cons x y) = empty)
                { rewrite left length_Nil; refine h1 };
              refine ind_eq (eq_sym (length_Cons x y)) (λ w, w = empty) h2 };
          refine ⊥ₑ (succ_neq_0 (length y) h0) }
        { assume hex;
          refine ∃ₑ hex _; assume b hb;
          refine ∃ₑ hb _; assume z hz;
          have hbz : π (ys2 = Cons b z) { refine ∧ₑ₁ hz };
          have hbA : π (b ∈ A) { refine ∧ₑ₁ (∧ₑ₂ hz) };
          have hzl : π (z ∈ list A) { refine ∧ₑ₂ (∧ₑ₂ hz) };
          rewrite hbz;
          have hlen3 : π (length y = length z)
            { have h1 : π (length (Cons x y) = length (Cons b z))
                { refine ind_eq (eq_sym hbz) (λ w, length (Cons x y) = length w) hlen2 };
              have h2 : π (succ (length y) = succ (length z))
                { rewrite left (length_Cons x y); rewrite left (length_Cons b z);
                  refine h1 };
              refine succ_inject (length y) (length z) h2 };
          have hrec : π (app y us = app z vs ⇔ (y = z ∧ us = vs))
            { refine hIH z hzl hlen3 };
          apply ∧ᵢ
          { assume h;
            have h2 : π (Cons x (app y us) = Cons b (app z vs))
              { rewrite left (app_Cons x y us); rewrite left (app_Cons b z vs);
                refine h };
            have hxb : π (x = b ∧ app y us = app z vs)
              { refine ∧ₑ₁ (Cons_iff x (app y us) b (app z vs)) h2 };
            have hyz : π (y = z ∧ us = vs) { refine ∧ₑ₁ hrec (∧ₑ₂ hxb) };
            have hcons : π (Cons x y = Cons b z)
              { rewrite (∧ₑ₁ hxb); rewrite (∧ₑ₁ hyz); reflexivity };
            refine ∧ᵢ hcons (∧ₑ₂ hyz) }
          { assume hc;
            have hxb : π (x = b ∧ y = z)
              { refine ∧ₑ₁ (Cons_iff x y b z) (∧ₑ₁ hc) };
            rewrite (app_Cons x y us);
            rewrite (app_Cons b z vs);
            rewrite (∧ₑ₁ hxb);
            rewrite (∧ₑ₂ hxb);
            rewrite (∧ₑ₂ hc);
            reflexivity } } } };
  refine hgen ys hys hlen
end;

opaque symbol append_eq_append (xs A ys us vs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (us ∈ list A) → π (vs ∈ list A) →
  π (length us = length vs) → π (app xs us = app ys vs) →
  π (xs = ys ∧ us = vs) ≔
begin
  assume xs A ys us vs hxs hys hus hvs hlen h;
  have hl : π (add (length xs) (length us) = add (length ys) (length vs))
    { rewrite left (length_app xs us A hxs hus);
      rewrite left (length_app ys vs A hys hvs);
      rewrite h; reflexivity };
  have hl2 : π (add (length xs) (length vs) = add (length ys) (length vs))
    { refine ind_eq (eq_sym hlen)
        (λ w, add (length xs) w = add (length ys) (length vs)) hl };
  have hl3 : π (add (length vs) (length xs) = add (length vs) (length ys))
    { rewrite (add_commute (length vs) (length xs));
      rewrite (add_commute (length vs) (length ys));
      refine hl2 };
  have hlenxy : π (length xs = length ys)
    { refine add_left_cancel (length vs) (length vs) (length xs) (length ys)
        (eq_refl (length vs)) hl3 (length_type xs A hxs) (length_type ys A hys) };
  refine ∧ₑ₁ (append_eq_append_iff xs A ys us vs hxs hys hlenxy) h
end;

opaque symbol append_eq_append_iff2 (xs A ys us vs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (us ∈ list A) → π (vs ∈ list A) →
  π (length us = length vs) →
  π (app xs us = app ys vs ⇔ (xs = ys ∧ us = vs)) ≔
begin
  assume xs A ys us vs hxs hys hus hvs hlen;
  apply ∧ᵢ
  { assume h; refine append_eq_append xs A ys us vs hxs hys hus hvs hlen h }
  { assume hc;
    rewrite (∧ₑ₁ hc); rewrite (∧ₑ₂ hc); reflexivity }
end;

opaque symbol append_self_iff (xs A ys zs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (zs ∈ list A) →
  π (app xs ys = app xs zs ⇔ ys = zs) ≔
begin
  assume xs A ys zs hxs hys hzs;
  have hiff : π (app xs ys = app xs zs ⇔ (xs = xs ∧ ys = zs))
    { refine append_eq_append_iff xs A xs ys zs hxs hxs (eq_refl (length xs)) };
  apply ∧ᵢ
  { assume h; refine ∧ₑ₂ (∧ₑ₁ hiff h) }
  { assume h; refine ∧ₑ₂ hiff (∧ᵢ (eq_refl xs) h) }
end;

opaque symbol append_self_iff2 (xs A ys zs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (zs ∈ list A) →
  π (app ys xs = app zs xs ⇔ ys = zs) ≔
begin
  assume xs A ys zs hxs hys hzs;
  have hiff : π (app ys xs = app zs xs ⇔ (ys = zs ∧ xs = xs))
    { refine append_eq_append_iff2 ys A zs xs xs hys hzs hxs hxs
        (eq_refl (length xs)) };
  apply ∧ᵢ
  { assume h; refine ∧ₑ₁ (∧ₑ₁ hiff h) }
  { assume h; refine ∧ₑ₂ hiff (∧ᵢ h (eq_refl xs)) }
end;

// Can also be proved from append_eq_append_iff2, but the proof requires two
// more hypotheses: x \<in> A and y \<in> A
opaque symbol append1_eq_iff (xs A ys x y : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) →
  π (app xs (Cons x Nil) = app ys (Cons y Nil) ⇔ (xs = ys ∧ x = y)) ≔
begin
  assume xs A ys x y hxs hys;
  have hgen : π (`∀ (ys2 : τ ι), (ys2 ∈ list A) ⇒
      (app xs (Cons x Nil) = app ys2 (Cons y Nil) ⇔ (xs = ys2 ∧ x = y)))
    { refine list_induct xs A
        (λ w, `∀ (ys2 : τ ι), (ys2 ∈ list A) ⇒
           (app w (Cons x Nil) = app ys2 (Cons y Nil) ⇔ (w = ys2 ∧ x = y)))
        hxs _ _
      { assume ys2 hys2;
        refine ∨ₑ (list_cases ys2 A hys2) _ _
        { assume hys2Nil;
          rewrite hys2Nil;
          apply ∧ᵢ
          { assume h;
            have h2 : π (Cons x Nil = Cons y Nil)
              { rewrite left (app_Nil (Cons x Nil));
                rewrite left (app_Nil (Cons y Nil));
                refine h };
            refine ∧ᵢ (eq_refl Nil) (∧ₑ₁ (∧ₑ₁ (Cons_iff x Nil y Nil) h2)) }
          { assume hc; rewrite (∧ₑ₂ hc); reflexivity } }
        { assume hex;
          refine ∃ₑ hex _; assume b hb;
          refine ∃ₑ hb _; assume z hz;
          rewrite (∧ₑ₁ hz);
          apply ∧ᵢ
          { assume h;
            have h2 : π (Cons x Nil = Cons b (app z (Cons y Nil)))
              { rewrite left (app_Nil (Cons x Nil));
                rewrite left (app_Cons b z (Cons y Nil));
                refine h };
            have h3 : π (Nil = app z (Cons y Nil))
              { refine ∧ₑ₂ (∧ₑ₁ (Cons_iff x Nil b (app z (Cons y Nil))) h2) };
            have h4 : π (z = Nil ∧ Cons y Nil = Nil)
              { refine ∧ₑ₁ (append_is_Nil_iff2 z A (Cons y Nil) (∧ₑ₂ (∧ₑ₂ hz))) h3 };
            refine ⊥ₑ (Nil_Cons_iff y Nil (eq_sym (∧ₑ₂ h4))) }
          { assume hc;
            refine ⊥ₑ (Nil_Cons_iff b z (∧ₑ₁ hc)) } } }
      { assume a l ha hl hIH ys2 hys2;
        refine ∨ₑ (list_cases ys2 A hys2) _ _
        { assume hys2Nil;
          rewrite hys2Nil;
          apply ∧ᵢ
          { assume h;
            have h2 : π (Cons a (app l (Cons x Nil)) = Cons y Nil)
              { rewrite left (app_Cons a l (Cons x Nil));
                rewrite left (app_Nil (Cons y Nil));
                refine h };
            have h3 : π (app l (Cons x Nil) = Nil)
              { refine ∧ₑ₂ (∧ₑ₁ (Cons_iff a (app l (Cons x Nil)) y Nil) h2) };
            have h4 : π (l = Nil ∧ Cons x Nil = Nil)
              { refine ∧ₑ₁ (append_is_Nil_iff l A (Cons x Nil) hl) h3 };
            refine ⊥ₑ (Nil_Cons_iff x Nil (eq_sym (∧ₑ₂ h4))) }
          { assume hc;
            refine ⊥ₑ (Nil_Cons_iff a l (eq_sym (∧ₑ₁ hc))) } }
        { assume hex;
          refine ∃ₑ hex _; assume b hb;
          refine ∃ₑ hb _; assume z hz;
          rewrite (∧ₑ₁ hz);
          have hrec : π (app l (Cons x Nil) = app z (Cons y Nil) ⇔ (l = z ∧ x = y))
            { refine hIH z (∧ₑ₂ (∧ₑ₂ hz)) };
          apply ∧ᵢ
          { assume h;
            have h2 : π (Cons a (app l (Cons x Nil)) = Cons b (app z (Cons y Nil)))
              { rewrite left (app_Cons a l (Cons x Nil));
                rewrite left (app_Cons b z (Cons y Nil));
                refine h };
            have hab : π (a = b ∧ app l (Cons x Nil) = app z (Cons y Nil))
              { refine ∧ₑ₁ (Cons_iff a (app l (Cons x Nil)) b (app z (Cons y Nil))) h2 };
            have hlz : π (l = z ∧ x = y) { refine ∧ₑ₁ hrec (∧ₑ₂ hab) };
            have hcons : π (Cons a l = Cons b z)
              { rewrite (∧ₑ₁ hab); rewrite (∧ₑ₁ hlz); reflexivity };
            refine ∧ᵢ hcons (∧ₑ₂ hlz) }
          { assume hc;
            have hab : π (a = b ∧ l = z)
              { refine ∧ₑ₁ (Cons_iff a l b z) (∧ₑ₁ hc) };
            rewrite (app_Cons a l (Cons x Nil));
            rewrite (app_Cons b z (Cons y Nil));
            rewrite (∧ₑ₁ hab);
            rewrite (∧ₑ₂ hab);
            rewrite (∧ₑ₂ hc);
            reflexivity } } } };
  refine hgen ys hys
end;

opaque symbol append_right_is_self_iff (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (app xs ys = ys ⇔ xs = Nil) ≔
begin
  assume xs A ys hxs hys;
  have hiff : π (app xs ys = ys ⇔ (xs = Nil ∧ ys = ys))
    { refine append_left_is_Nil_iff xs ys ys A hxs hys hys (eq_refl (length ys)) };
  apply ∧ᵢ
  { assume h; refine ∧ₑ₁ (∧ₑ₁ hiff h) }
  { assume h; refine ∧ₑ₂ hiff (∧ᵢ h (eq_refl ys)) }
end;

opaque symbol append_right_is_self_iff2 (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (ys = app xs ys ⇔ xs = Nil) ≔
begin
  assume xs A ys hxs hys;
  apply ∧ᵢ
  { assume h; refine ∧ₑ₁ (append_right_is_self_iff xs A ys hxs hys) (eq_sym h) }
  { assume h; refine eq_sym (∧ₑ₂ (append_right_is_self_iff xs A ys hxs hys) h) }
end;

opaque symbol hd_append (xs A ys : τ ι) :
  π (xs ∈ list A) → π (xs ≠ Nil) → π (hd (app xs ys) = hd xs) ≔
begin
  assume xs A ys hxs hne;
  refine ∨ₑ (list_cases xs A hxs) _ _
  { assume h; refine ⊥ₑ (hne h) }
  { assume hex;
    refine ∃ₑ hex _; assume a ha;
    refine ∃ₑ ha _; assume l hl;
    rewrite (∧ₑ₁ hl);
    rewrite (app_Cons a l ys);
    rewrite (hd_Cons a (app l ys));
    rewrite (hd_Cons a l);
    reflexivity }
end;

opaque symbol tl_append (xs A ys : τ ι) :
  π (xs ∈ list A) → π (xs ≠ Nil) → π (tl (app xs ys) = app (tl xs) ys) ≔
begin
  assume xs A ys hxs hne;
  refine ∨ₑ (list_cases xs A hxs) _ _
  { assume h; refine ⊥ₑ (hne h) }
  { assume hex;
    refine ∃ₑ hex _; assume a ha;
    refine ∃ₑ ha _; assume l hl;
    rewrite (∧ₑ₁ hl);
    rewrite (app_Cons a l ys);
    rewrite (tl_Cons a (app l ys));
    rewrite (tl_Cons a l);
    reflexivity }
end;

// (** rev **)

opaque symbol rev_is_Nil_iff (xs A : τ ι) : π (xs ∈ list A) → π (rev xs = Nil ⇔ xs = Nil) ≔
begin
  assume xs A hxs;
  refine ∨ₑ (list_cases xs A hxs) _ _
  { assume h;
    rewrite h;
    apply ∧ᵢ
    { assume h2; reflexivity }
    { assume h2; refine rev_Nil } }
  { assume hex;
    refine ∃ₑ hex _; assume a ha;
    refine ∃ₑ ha _; assume l hl;
    rewrite (∧ₑ₁ hl);
    apply ∧ᵢ
    { assume h;
      have h2 : π (app (rev l) (Cons a Nil) = Nil)
        { rewrite left (rev_Cons a l); refine h };
      have h3 : π (rev l = Nil ∧ Cons a Nil = Nil)
        { refine ∧ₑ₁ (append_is_Nil_iff (rev l) A (Cons a Nil)
            (rev_type l A (∧ₑ₂ (∧ₑ₂ hl)))) h2 };
      refine ⊥ₑ (Nil_Cons_iff a Nil (eq_sym (∧ₑ₂ h3))) }
    { assume h; refine ⊥ₑ (Nil_Cons_iff a l (eq_sym h)) } }
end;

opaque symbol Nil_is_rev_iff (xs A : τ ι) : π (xs ∈ list A) → π (Nil = rev xs ⇔ xs = Nil) ≔
begin
  assume xs A hxs;
  apply ∧ᵢ
  { assume h; refine ∧ₑ₁ (rev_is_Nil_iff xs A hxs) (eq_sym h) }
  { assume h; refine eq_sym (∧ₑ₂ (rev_is_Nil_iff xs A hxs) h) }
end;

opaque symbol rev_is_rev_iff (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (rev xs = rev ys ⇔ xs = ys) ≔
begin
  assume xs A ys hxs hys;
  apply ∧ᵢ
  { assume h;
    rewrite left (rev_rev_ident xs A hxs);
    rewrite h;
    refine rev_rev_ident ys A hys }
  { assume h; rewrite h; reflexivity }
end;

opaque symbol rev_list_elim (xs A : τ ι) (P : Prop) :
  π (xs ∈ list A) →
  π (xs = Nil ⇒ P) →
  π (Ball (list A) (λ ys, Ball A (λ y, (xs = app ys (Cons y Nil)) ⇒ P))) →
  π P ≔
begin
  assume xs A P hxs h0 hstep;
  have hq : π ((xs = xs) ⇒ P)
    { refine list_append_induct xs A (λ w, (xs = w) ⇒ P) hxs _ _
      { refine h0 }
      { assume x y hx hy hIH heq;
        refine hstep y hy x hx heq } };
  refine hq (eq_refl xs)
end;

// (** more theorems about drop **)

opaque symbol length_drop (n A xs : τ ι) :
  π (n ∈ omega) → π (xs ∈ list A) → π (length (drop n xs) = diff (length xs) n) ≔
begin
  assume n A xs hn hxs;
  have hmain : π (Ball omega (λ w, Ball (list A)
      (λ xs2, length (drop w xs2) = diff (length xs2) w)))
    { refine nat_induct (λ w, Ball (list A)
        (λ xs2, length (drop w xs2) = diff (length xs2) w)) _ _
      { assume xs2 hxs2;
        rewrite (drop_0 xs2);
        rewrite (diff_0 (length xs2));
        refine eq_sym (natify_ident (length xs2) (length_type xs2 A hxs2)) }
      { assume n2 hn2 hIH xs2 hxs2;
        refine ∨ₑ (list_cases xs2 A hxs2) _ _
        { assume hNil;
          rewrite hNil;
          rewrite (drop_Nil (succ n2) (succ_in_omega n2 hn2));
          rewrite length_Nil;
          refine eq_sym (diff_0_eq_0 (succ n2)) }
        { assume hex;
          refine ∃ₑ hex _; assume a ha;
          refine ∃ₑ ha _; assume l hl;
          rewrite (∧ₑ₁ hl);
          rewrite (drop_succ_Cons n2 a l hn2);
          rewrite (hIH l (∧ₑ₂ (∧ₑ₂ hl)));
          rewrite (length_Cons a l);
          rewrite diff_succ_succ;
          reflexivity } } };
  refine hmain n hn xs hxs
end;

opaque symbol drop_all (n A xs : τ ι) :
  π (n ∈ omega) → π (xs ∈ list A) → π (le (length xs) n) → π (drop n xs = Nil) ≔
begin
  assume n A xs hn hxs hle;
  have hmain : π (Ball omega (λ w, Ball (list A)
      (λ xs2, le (length xs2) w ⇒ drop w xs2 = Nil)))
    { refine nat_induct (λ w, Ball (list A)
        (λ xs2, le (length xs2) w ⇒ drop w xs2 = Nil)) _ _
      { assume xs2 hxs2 hle2;
        rewrite (drop_0 xs2);
        refine ∧ₑ₁ (length_is_0_iff xs2 A hxs2) (le0D (length xs2) hle2) }
      { assume n2 hn2 hIH xs2 hxs2 hle2;
        refine ∨ₑ (list_cases xs2 A hxs2) _ _
        { assume hNil;
          rewrite hNil;
          refine drop_Nil (succ n2) (succ_in_omega n2 hn2) }
        { assume hex;
          refine ∃ₑ hex _; assume a ha;
          refine ∃ₑ ha _; assume l hl;
          rewrite (∧ₑ₁ hl);
          rewrite (drop_succ_Cons n2 a l hn2);
          have hle3 : π (le (length (Cons a l)) (succ n2))
            { refine ind_eq (eq_sym (∧ₑ₁ hl)) (λ w, le (length w) (succ n2)) hle2 };
          have hle4 : π (le (succ (length l)) (succ n2))
            { refine ind_eq (eq_sym (length_Cons a l)) (λ w, le w (succ n2)) hle3 };
          refine hIH l (∧ₑ₂ (∧ₑ₂ hl)) (succ_leE (length l) (succ n2) hle4) } } };
  refine hmain n hn xs hxs hle
end;

opaque symbol drop_append (n A xs ys : τ ι) :
  π (n ∈ omega) → π (xs ∈ list A) →
  π (drop n (app xs ys) = app (drop n xs) (drop (diff n (length xs)) ys)) ≔
begin
  assume n A xs ys hn hxs;
  have hmain : π (Ball omega (λ w, Ball (list A)
      (λ xs2, drop w (app xs2 ys) = app (drop w xs2) (drop (diff w (length xs2)) ys))))
    { refine nat_induct (λ w, Ball (list A)
        (λ xs2, drop w (app xs2 ys) = app (drop w xs2) (drop (diff w (length xs2)) ys))) _ _
      { assume xs2 hxs2;
        rewrite (drop_0 (app xs2 ys));
        rewrite (drop_0 xs2);
        rewrite (diff_0_eq_0 (length xs2));
        rewrite (drop_0 ys);
        reflexivity }
      { assume n2 hn2 hIH xs2 hxs2;
        refine ∨ₑ (list_cases xs2 A hxs2) _ _
        { assume hNil;
          rewrite hNil;
          rewrite (app_Nil ys);
          rewrite (drop_Nil (succ n2) (succ_in_omega n2 hn2));
          rewrite (app_Nil (drop (diff (succ n2) (length Nil)) ys));
          rewrite length_Nil;
          rewrite (diff_0 (succ n2));
          rewrite (natify_ident (succ n2) (succ_in_omega n2 hn2));
          reflexivity }
        { assume hex;
          refine ∃ₑ hex _; assume a ha;
          refine ∃ₑ ha _; assume l hl;
          rewrite (∧ₑ₁ hl);
          rewrite (app_Cons a l ys);
          rewrite (drop_succ_Cons n2 a (app l ys) hn2);
          rewrite (drop_succ_Cons n2 a l hn2);
          rewrite (length_Cons a l);
          rewrite diff_succ_succ;
          refine hIH l (∧ₑ₂ (∧ₑ₂ hl)) } } };
  refine hmain n hn xs hxs
end;

opaque symbol drop_drop (m A : τ ι) :
  π (m ∈ omega) →
  π (Ball (list A) (λ xs, Ball omega (λ n, drop n (drop m xs) = drop (add n m) xs))) ≔
begin
  assume m A hm;
  have hmain : π (Ball omega (λ w, Ball (list A)
      (λ xs, Ball omega (λ n, drop n (drop w xs) = drop (add n w) xs))))
    { refine nat_induct (λ w, Ball (list A)
        (λ xs, Ball omega (λ n, drop n (drop w xs) = drop (add n w) xs))) _ _
      { assume xs hxs n hn;
        rewrite (drop_0 xs);
        rewrite (add_0_right n hn);
        reflexivity }
      { assume m2 hm2 hIH xs hxs n hn;
        refine ∨ₑ (list_cases xs A hxs) _ _
        { assume hNil;
          rewrite hNil;
          rewrite (drop_Nil (succ m2) (succ_in_omega m2 hm2));
          rewrite (drop_Nil n hn);
          rewrite (drop_Nil (add n (succ m2)) (add_type n (succ m2)));
          reflexivity }
        { assume hex;
          refine ∃ₑ hex _; assume a ha;
          refine ∃ₑ ha _; assume l hl;
          rewrite (∧ₑ₁ hl);
          rewrite (drop_succ_Cons m2 a l hm2);
          rewrite (add_succ_right n m2);
          rewrite (drop_succ_Cons (add n m2) a l (add_type n m2));
          refine hIH l (∧ₑ₂ (∧ₑ₂ hl)) n hn } } };
  assume xs hxs n hn;
  refine hmain m hm xs hxs n hn
end;

// ===========================================================================
// (** take **)
// ===========================================================================

// port-internal helpers — take's defining equations, unfolded from take_def
// via the list_rec equations + beta + nat_case equations.
private opaque symbol take_Nil_h (n : τ ι) : π (n ∈ omega) → π (take n Nil = Nil) ≔
begin
  assume n hn;
  rewrite (take_def n Nil);
  rewrite (list_rec_Nil (Lambda omega (λ _, Nil))
    (λ a l r, Lambda omega (λ n2, nat_case Nil (λ m, Cons a (fapply r m)) n2)));
  refine beta omega (λ _, Nil) n hn
end;

private opaque symbol take_Cons_h (n a l : τ ι) :
  π (n ∈ omega) →
  π (take n (Cons a l) =
     nat_case Nil
       (λ m, Cons a (fapply (list_rec (Lambda omega (λ _, Nil))
         (λ a2 l2 r, Lambda omega (λ n2, nat_case Nil (λ m2, Cons a2 (fapply r m2)) n2))
         l) m)) n) ≔
begin
  assume n a l hn;
  rewrite (take_def n (Cons a l));
  rewrite (list_rec_Cons (Lambda omega (λ _, Nil))
    (λ a2 l2 r, Lambda omega (λ n2, nat_case Nil (λ m2, Cons a2 (fapply r m2)) n2)) a l);
  simplify rule off;
  refine beta omega
    (λ n2, nat_case Nil
      (λ m2, Cons a (fapply (list_rec (Lambda omega (λ _, Nil))
        (λ a3 l3 r, Lambda omega (λ n3, nat_case Nil (λ m3, Cons a3 (fapply r m3)) n3))
        l) m2)) n2) n hn
end;

opaque symbol take_0 (xs A : τ ι) : π (xs ∈ list A) → π (take empty xs = Nil) ≔
begin
  assume xs A hxs;
  refine ∨ₑ (list_cases xs A hxs) _ _
  { assume hNil;
    rewrite hNil;
    refine take_Nil_h empty zero_in_omega }
  { assume hex;
    refine ∃ₑ hex _; assume a ha;
    refine ∃ₑ ha _; assume l hl;
    rewrite (∧ₑ₁ hl);
    rewrite (take_Cons_h empty a l zero_in_omega);
    refine nat_case_0 Nil
      (λ m, Cons a (fapply (list_rec (Lambda omega (λ _, Nil))
        (λ a2 l2 r, Lambda omega (λ n2, nat_case Nil (λ m2, Cons a2 (fapply r m2)) n2))
        l) m)) }
end;

opaque symbol take_succ_Cons (n a xs : τ ι) :
  π (n ∈ omega) → π (take (succ n) (Cons a xs) = Cons a (take n xs)) ≔
begin
  assume n a xs hn;
  rewrite (take_Cons_h (succ n) a xs (succ_in_omega n hn));
  rewrite (nat_case_succ Nil
    (λ m, Cons a (fapply (list_rec (Lambda omega (λ _, Nil))
      (λ a2 l2 r, Lambda omega (λ n2, nat_case Nil (λ m2, Cons a2 (fapply r m2)) n2))
      xs) m)) n);
  simplify rule off;
  rewrite left (take_def n xs);
  reflexivity
end;

// Needed for proving take_all
opaque symbol take_Nil (n : τ ι) : π (n ∈ omega) → π (take n Nil = Nil) ≔
begin
  assume n hn;
  refine take_Nil_h n hn
end;

opaque symbol take_all (n A xs : τ ι) :
  π (n ∈ omega) → π (xs ∈ list A) → π (le (length xs) n) → π (take n xs = xs) ≔
begin
  assume n A xs hn hxs hle;
  have hmain : π (Ball omega (λ w, Ball (list A)
      (λ xs2, le (length xs2) w ⇒ take w xs2 = xs2)))
    { refine nat_induct (λ w, Ball (list A)
        (λ xs2, le (length xs2) w ⇒ take w xs2 = xs2)) _ _
      { assume xs2 hxs2 hle2;
        rewrite (take_0 xs2 A hxs2);
        refine eq_sym (∧ₑ₁ (length_is_0_iff xs2 A hxs2)
          (le0D (length xs2) hle2)) }
      { assume n2 hn2 hIH xs2 hxs2 hle2;
        refine ∨ₑ (list_cases xs2 A hxs2) _ _
        { assume hNil;
          rewrite hNil;
          refine take_Nil_h (succ n2) (succ_in_omega n2 hn2) }
        { assume hex;
          refine ∃ₑ hex _; assume a ha;
          refine ∃ₑ ha _; assume l hl;
          rewrite (∧ₑ₁ hl);
          rewrite (take_succ_Cons n2 a l hn2);
          have hle3 : π (le (length (Cons a l)) (succ n2))
            { refine ind_eq (eq_sym (∧ₑ₁ hl)) (λ w, le (length w) (succ n2)) hle2 };
          have hle4 : π (le (succ (length l)) (succ n2))
            { refine ind_eq (eq_sym (length_Cons a l)) (λ w, le w (succ n2)) hle3 };
          rewrite (hIH l (∧ₑ₂ (∧ₑ₂ hl)) (succ_leE (length l) (succ n2) hle4));
          reflexivity } } };
  refine hmain n hn xs hxs hle
end;

opaque symbol take_type (xs A n : τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) → π (take n xs ∈ list A) ≔
begin
  assume xs A n hxs hn;
  have hmain : π (Ball omega (λ n2, take n2 xs ∈ list A))
    { refine list_induct xs A (λ w, Ball omega (λ n2, take n2 w ∈ list A)) hxs _ _
      { assume n2 hn2;
        refine ind_eq (take_Nil_h n2 hn2) (λ w, w ∈ list A) (list_0I A) }
      { assume x y hx hy hIH n2 hn2;
        refine natE n2 (take n2 (Cons x y) ∈ list A) hn2 _ _
        { assume h0;
          rewrite h0;
          refine ind_eq (take_0 (Cons x y) A (list_consI x y A hx hy))
            (λ w, w ∈ list A) (list_0I A) }
        { assume m hm heq;
          rewrite heq;
          refine ind_eq (take_succ_Cons m x y hm) (λ w, w ∈ list A)
            (list_consI x (take m y) A hx (hIH m hm)) } } };
  refine hmain n hn
end;

opaque symbol take_append (xs A ys n : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (n ∈ omega) →
  π (take n (app xs ys) = app (take n xs) (take (diff n (length xs)) ys)) ≔
begin
  assume xs A ys n hxs hys hn;
  have hmain : π (Ball omega
      (λ n2, take n2 (app xs ys) = app (take n2 xs) (take (diff n2 (length xs)) ys)))
    { refine list_induct xs A (λ w, Ball omega
        (λ n2, take n2 (app w ys) = app (take n2 w) (take (diff n2 (length w)) ys)))
        hxs _ _
      { assume n2 hn2;
        rewrite (app_Nil ys);
        rewrite (take_Nil_h n2 hn2);
        rewrite (app_Nil (take (diff n2 (length Nil)) ys));
        rewrite length_Nil;
        rewrite (diff_0 n2);
        rewrite (natify_ident n2 hn2);
        reflexivity }
      { assume x y hx hy hIH n2 hn2;
        refine natE n2
          (take n2 (app (Cons x y) ys)
           = app (take n2 (Cons x y)) (take (diff n2 (length (Cons x y))) ys))
          hn2 _ _
        { assume h0;
          rewrite h0;
          rewrite (take_0 (app (Cons x y) ys) A
            (app_type (Cons x y) ys A (list_consI x y A hx hy) hys));
          rewrite (take_0 (Cons x y) A (list_consI x y A hx hy));
          rewrite (app_Nil (take (diff empty (length (Cons x y))) ys));
          rewrite (diff_0_eq_0 (length (Cons x y)));
          refine eq_sym (take_0 ys A hys) }
        { assume m hm heq;
          rewrite heq;
          rewrite (app_Cons x y ys);
          rewrite (take_succ_Cons m x (app y ys) hm);
          rewrite (take_succ_Cons m x y hm);
          rewrite (app_Cons x (take m y) (take (diff (succ m) (length (Cons x y))) ys));
          rewrite (length_Cons x y);
          rewrite diff_succ_succ;
          rewrite (hIH m hm);
          reflexivity } } };
  refine hmain n hn
end;

opaque symbol take_take (m A xs n : τ ι) :
  π (m ∈ omega) → π (xs ∈ list A) → π (n ∈ omega) →
  π (take n (take m xs) = take (min n m) xs) ≔
begin
  assume m A xs n hm hxs hn;
  have hmain : π (Ball omega (λ w, Ball (list A) (λ xs2, Ball omega
      (λ n2, take n2 (take w xs2) = take (min n2 w) xs2))))
    { refine nat_induct (λ w, Ball (list A) (λ xs2, Ball omega
        (λ n2, take n2 (take w xs2) = take (min n2 w) xs2))) _ _
      { assume xs2 hxs2 n2 hn2;
        rewrite (take_0 xs2 A hxs2);
        rewrite (take_Nil_h n2 hn2);
        rewrite (min_02 n2 hn2);
        refine eq_sym (take_0 xs2 A hxs2) }
      { assume m2 hm2 hIH xs2 hxs2 n2 hn2;
        refine ∨ₑ (list_cases xs2 A hxs2) _ _
        { assume hNil;
          rewrite hNil;
          rewrite (take_Nil_h (succ m2) (succ_in_omega m2 hm2));
          rewrite (take_Nil_h n2 hn2);
          refine eq_sym (take_Nil_h (min n2 (succ m2))
            (min_type n2 (succ m2) hn2 (succ_in_omega m2 hm2))) }
        { assume hex;
          refine ∃ₑ hex _; assume a ha;
          refine ∃ₑ ha _; assume l hl;
          rewrite (∧ₑ₁ hl);
          refine natE n2
            (take n2 (take (succ m2) (Cons a l)) = take (min n2 (succ m2)) (Cons a l))
            hn2 _ _
          { assume h0;
            rewrite h0;
            rewrite (take_0 (take (succ m2) (Cons a l)) A
              (take_type (Cons a l) A (succ m2)
                (list_consI a l A (∧ₑ₁ (∧ₑ₂ hl)) (∧ₑ₂ (∧ₑ₂ hl)))
                (succ_in_omega m2 hm2)));
            rewrite (min_0 (succ m2) (succ_in_omega m2 hm2));
            refine eq_sym (take_0 (Cons a l) A
              (list_consI a l A (∧ₑ₁ (∧ₑ₂ hl)) (∧ₑ₂ (∧ₑ₂ hl)))) }
          { assume k hk heq;
            rewrite heq;
            rewrite (take_succ_Cons m2 a l hm2);
            rewrite (take_succ_Cons k a (take m2 l) hk);
            rewrite (hIH l (∧ₑ₂ (∧ₑ₂ hl)) k hk);
            rewrite (min_succ_succ k m2 hk hm2);
            rewrite (take_succ_Cons (min k m2) a l (min_type k m2 hk hm2));
            reflexivity } } } };
  refine hmain m hm xs hxs n hn
end;

// ===========================================================================
// (** nth **)
// ===========================================================================

// port-internal helper — a Lambda applied outside its domain gives 0 (the
// THE-based fapply has no witness); func.lp does not port Isabelle's
// apply_0/apply_equality machinery for this case.
private opaque symbol fapply_Lambda_out (A : τ ι) (b : τ ι → τ ι) (x : τ ι) :
  π (x ∉ A) → π (fapply (Lambda A b) x = empty) ≔
begin
  assume A b x hnx;
  rewrite (fapply_def (Lambda A b) x);
  refine the_0 (λ y, Pair x y ∈ Lambda A b) _;
  assume hex;
  refine ∃ₑ hex _; assume y hy;
  have hmem : π (Pair x y ∈ RepFun A (λ x2, Pair x2 (b x2)))
    { refine ind_eq (eq_sym (Lambda_def A b)) (λ w, Pair x y ∈ w) (∧ₑ₁ hy) };
  have hbex : π (Bex A (λ x2, Pair x y = Pair x2 (b x2)))
    { refine ∧ₑ₁ (RepFun_iff (Pair x y) A (λ x2, Pair x2 (b x2))) hmem };
  refine ∃ₑ hbex _; assume x2 hx2;
  have hxx2 : π (x = x2) { refine Pair_inject1 x y x2 (b x2) (∧ₑ₂ hx2) };
  refine hnx (ind_eq hxx2 (λ w, w ∈ A) (∧ₑ₁ hx2))
end;

// port-internal helper — nth's Cons equation, unfolded from nth_def
private opaque symbol nth_Cons_h (n a l : τ ι) :
  π (n ∈ omega) →
  π (nth n (Cons a l) =
     nat_case a
       (λ m, fapply (list_rec (Lambda omega (λ _, empty))
         (λ a2 l2 r, Lambda omega (λ n2, nat_case a2 (λ m2, fapply r m2) n2))
         l) m) n) ≔
begin
  assume n a l hn;
  rewrite (nth_def n (Cons a l));
  rewrite (list_rec_Cons (Lambda omega (λ _, empty))
    (λ a2 l2 r, Lambda omega (λ n2, nat_case a2 (λ m2, fapply r m2) n2)) a l);
  simplify rule off;
  refine beta omega
    (λ n2, nat_case a
      (λ m2, fapply (list_rec (Lambda omega (λ _, empty))
        (λ a3 l3 r, Lambda omega (λ n3, nat_case a3 (λ m3, fapply r m3) n3))
        l) m2) n2) n hn
end;

opaque symbol nth_0 (a l : τ ι) : π (nth empty (Cons a l) = a) ≔
begin
  assume a l;
  rewrite (nth_Cons_h empty a l zero_in_omega);
  refine nat_case_0 a
    (λ m, fapply (list_rec (Lambda omega (λ _, empty))
      (λ a2 l2 r, Lambda omega (λ n2, nat_case a2 (λ m2, fapply r m2) n2))
      l) m)
end;

opaque symbol nth_Cons (n a l : τ ι) :
  π (n ∈ omega) → π (nth (succ n) (Cons a l) = nth n l) ≔
begin
  assume n a l hn;
  rewrite (nth_Cons_h (succ n) a l (succ_in_omega n hn));
  rewrite (nat_case_succ a
    (λ m, fapply (list_rec (Lambda omega (λ _, empty))
      (λ a2 l2 r, Lambda omega (λ n2, nat_case a2 (λ m2, fapply r m2) n2))
      l) m) n);
  simplify rule off;
  rewrite left (nth_def n l);
  reflexivity
end;

opaque symbol nth_empty (n : τ ι) : π (nth n Nil = empty) ≔
begin
  assume n;
  rewrite (nth_def n Nil);
  rewrite (list_rec_Nil (Lambda omega (λ _, empty))
    (λ a2 l2 r, Lambda omega (λ n2, nat_case a2 (λ m2, fapply r m2) n2)));
  refine ∨ₑ (em (n ∈ omega)) _ _
  { assume hn; refine beta omega (λ _, empty) n hn }
  { assume hn; refine fapply_Lambda_out omega (λ _, empty) n hn }
end;

opaque symbol nth_type (xs A n : τ ι) :
  π (xs ∈ list A) → π (lt n (length xs)) → π (nth n xs ∈ A) ≔
begin
  assume xs A n hxs hlt;
  have hmain : π (`∀ (n2 : τ ι), lt n2 (length xs) ⇒ nth n2 xs ∈ A)
    { refine list_induct xs A
        (λ w, `∀ (n2 : τ ι), lt n2 (length w) ⇒ nth n2 w ∈ A) hxs _ _
      { assume n2 hlt2;
        refine ⊥ₑ (not_lt0 n2
          (ind_eq (eq_sym length_Nil) (λ w, lt n2 w) hlt2)) }
      { assume x y hx hy hIH n2 hlt2;
        have hn2 : π (n2 ∈ omega)
          { refine lt_nat_in_nat n2 (length (Cons x y)) hlt2
              (length_type (Cons x y) A (list_consI x y A hx hy)) };
        refine natE n2 (nth n2 (Cons x y) ∈ A) hn2 _ _
        { assume h0;
          rewrite h0;
          refine ind_eq (nth_0 x y) (λ w, w ∈ A) hx }
        { assume m hm heq;
          rewrite heq;
          have hlt3 : π (lt (succ m) (succ (length y)))
            { refine ind_eq (eq_sym (length_Cons x y)) (λ w, lt (succ m) w)
                (ind_eq (eq_sym heq) (λ w, lt w (length (Cons x y))) hlt2) };
          refine ind_eq (nth_Cons m x y hm) (λ w, w ∈ A)
            (hIH m (succ_leE m (length y) hlt3)) } } };
  refine hmain n hlt
end;

opaque symbol nth_eq_0 (xs A n : τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) → π (le (length xs) n) → π (nth n xs = empty) ≔
begin
  assume xs A n hxs hn hle;
  have hmain : π (Ball omega (λ n2, le (length xs) n2 ⇒ nth n2 xs = empty))
    { refine list_induct xs A
        (λ w, Ball omega (λ n2, le (length w) n2 ⇒ nth n2 w = empty)) hxs _ _
      { assume n2 hn2 hle2;
        refine nth_empty n2 }
      { assume x y hx hy hIH n2 hn2 hle2;
        refine natE n2 (nth n2 (Cons x y) = empty) hn2 _ _
        { assume h0;
          have hle3 : π (le (length (Cons x y)) empty)
            { refine ind_eq (eq_sym h0) (λ w, le (length (Cons x y)) w) hle2 };
          have h02 : π (succ (length y) = empty)
            { refine ind_eq (eq_sym (length_Cons x y)) (λ w, w = empty)
                (le0D (length (Cons x y)) hle3) };
          refine ⊥ₑ (succ_neq_0 (length y) h02) }
        { assume m hm heq;
          rewrite heq;
          rewrite (nth_Cons m x y hm);
          have hle3 : π (le (succ (length y)) (succ m))
            { refine ind_eq (eq_sym (length_Cons x y)) (λ w, le w (succ m))
                (ind_eq (eq_sym heq) (λ w, le (length (Cons x y)) w) hle2) };
          refine hIH m hm (succ_leE (length y) (succ m) hle3) } } };
  refine hmain n hn hle
end;

opaque symbol nth_append (xs A ys n : τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) →
  π (nth n (app xs ys) = If (lt n (length xs)) (nth n xs) (nth (diff n (length xs)) ys)) ≔
begin
  assume xs A ys n hxs hn;
  have hmain : π (Ball omega (λ n2,
      nth n2 (app xs ys)
      = If (lt n2 (length xs)) (nth n2 xs) (nth (diff n2 (length xs)) ys)))
    { refine list_induct xs A (λ w, Ball omega (λ n2,
        nth n2 (app w ys)
        = If (lt n2 (length w)) (nth n2 w) (nth (diff n2 (length w)) ys))) hxs _ _
      { assume n2 hn2;
        rewrite (app_Nil ys);
        rewrite length_Nil;
        rewrite (If_not_P (lt n2 empty) (nth n2 Nil) (nth (diff n2 empty) ys)
          (not_lt0 n2));
        rewrite (diff_0 n2);
        rewrite (natify_ident n2 hn2);
        reflexivity }
      { assume x y hx hy hIH n2 hn2;
        have hOly : π (Ord (length y))
          { refine nat_into_Ord (length y) (length_type y A hy) };
        refine natE n2
          (nth n2 (app (Cons x y) ys)
           = If (lt n2 (length (Cons x y))) (nth n2 (Cons x y))
               (nth (diff n2 (length (Cons x y))) ys)) hn2 _ _
        { assume h0;
          rewrite h0;
          rewrite (app_Cons x y ys);
          rewrite (nth_0 x (app y ys));
          rewrite (length_Cons x y);
          rewrite (If_P (lt empty (succ (length y))) (nth empty (Cons x y))
            (nth (diff empty (succ (length y))) ys) (Ord_0_le (length y) hOly));
          refine eq_sym (nth_0 x y) }
        { assume m hm heq;
          rewrite heq;
          rewrite (app_Cons x y ys);
          rewrite (nth_Cons m x (app y ys) hm);
          rewrite (hIH m hm);
          rewrite (length_Cons x y);
          rewrite (nth_Cons m x y hm);
          rewrite diff_succ_succ;
          refine ∨ₑ (em (lt m (length y))) _ _
          { assume hp;
            rewrite (If_P (lt m (length y)) (nth m y) (nth (diff m (length y)) ys) hp);
            rewrite (If_P (lt (succ m) (succ (length y))) (nth m y)
              (nth (diff m (length y)) ys) (succ_lt_mono m (length y) hp));
            reflexivity }
          { assume hnp;
            have hnp2 : π (¬ (lt (succ m) (succ (length y))))
              { assume h2; refine hnp (succ_leE m (length y) h2) };
            rewrite (If_not_P (lt m (length y)) (nth m y)
              (nth (diff m (length y)) ys) hnp);
            rewrite (If_not_P (lt (succ m) (succ (length y))) (nth m y)
              (nth (diff m (length y)) ys) hnp2);
            reflexivity } } } };
  refine hmain n hn
end;

opaque symbol set_of_list_conv_nth (xs A : τ ι) :
  π (xs ∈ list A) →
  π (set_of_list xs = Collect A (λ x, Bex omega (λ i, lt i (length xs) ∧ x = nth i xs))) ≔
begin admit end;

// ===========================================================================
// Other theorems about lists
// ===========================================================================

opaque symbol nth_take_lemma (k A xs ys : τ ι) :
  π (k ∈ omega) → π (xs ∈ list A) → π (ys ∈ list A) →
  π (le k (length xs)) → π (le k (length ys)) →
  π (Ball omega (λ i, lt i k ⇒ nth i xs = nth i ys)) →
  π (take k xs = take k ys) ≔
begin admit end;

opaque symbol nth_equalityI (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (length xs = length ys) →
  π (Ball omega (λ i, lt i (length xs) ⇒ nth i xs = nth i ys)) →
  π (xs = ys) ≔
begin admit end;

// The famous take-lemma
opaque symbol take_equalityI (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) →
  π (Ball omega (λ i, take i xs = take i ys)) →
  π (xs = ys) ≔
begin admit end;

opaque symbol nth_drop (n i A xs : τ ι) :
  π (n ∈ omega) → π (i ∈ omega) → π (xs ∈ list A) →
  π (nth i (drop n xs) = nth (add n i) xs) ≔
begin
  assume n i A xs hn hi hxs;
  have hmain : π (Ball omega (λ w, Ball (list A)
      (λ xs2, nth i (drop w xs2) = nth (add w i) xs2)))
    { refine nat_induct (λ w, Ball (list A)
        (λ xs2, nth i (drop w xs2) = nth (add w i) xs2)) _ _
      { assume xs2 hxs2;
        rewrite (drop_0 xs2);
        rewrite (add_0 i hi);
        reflexivity }
      { assume n2 hn2 hIH xs2 hxs2;
        refine ∨ₑ (list_cases xs2 A hxs2) _ _
        { assume hNil;
          rewrite hNil;
          rewrite (drop_Nil (succ n2) (succ_in_omega n2 hn2));
          rewrite (nth_empty i);
          refine eq_sym (nth_empty (add (succ n2) i)) }
        { assume hex;
          refine ∃ₑ hex _; assume a ha;
          refine ∃ₑ ha _; assume l hl;
          rewrite (∧ₑ₁ hl);
          rewrite (drop_succ_Cons n2 a l hn2);
          rewrite (hIH l (∧ₑ₂ (∧ₑ₂ hl)));
          rewrite (add_succ n2 i);
          refine eq_sym (nth_Cons (add n2 i) a l (add_type n2 i)) } } };
  refine hmain n hn xs hxs
end;

opaque symbol take_succ (xs A i : τ ι) :
  π (xs ∈ list A) → π (lt i (length xs)) →
  π (take (succ i) xs = app (take i xs) (Cons (nth i xs) Nil)) ≔
begin
  assume xs A i hxs hlt;
  have hmain : π (`∀ (i2 : τ ι), lt i2 (length xs) ⇒
      take (succ i2) xs = app (take i2 xs) (Cons (nth i2 xs) Nil))
    { refine list_induct xs A (λ w, `∀ (i2 : τ ι), lt i2 (length w) ⇒
        take (succ i2) w = app (take i2 w) (Cons (nth i2 w) Nil)) hxs _ _
      { assume i2 hlt2;
        refine ⊥ₑ (not_lt0 i2 (ind_eq (eq_sym length_Nil) (λ w, lt i2 w) hlt2)) }
      { assume x y hx hy hIH i2 hlt2;
        have hi2 : π (i2 ∈ omega)
          { refine lt_nat_in_nat i2 (length (Cons x y)) hlt2
              (length_type (Cons x y) A (list_consI x y A hx hy)) };
        refine natE i2
          (take (succ i2) (Cons x y)
           = app (take i2 (Cons x y)) (Cons (nth i2 (Cons x y)) Nil)) hi2 _ _
        { assume h0;
          rewrite h0;
          rewrite (take_succ_Cons empty x y zero_in_omega);
          rewrite (take_0 y A hy);
          rewrite (take_0 (Cons x y) A (list_consI x y A hx hy));
          rewrite (nth_0 x y);
          rewrite (app_Nil (Cons x Nil));
          reflexivity }
        { assume m hm heq;
          rewrite heq;
          have hlt3 : π (lt (succ m) (succ (length y)))
            { refine ind_eq (eq_sym (length_Cons x y)) (λ w, lt (succ m) w)
                (ind_eq (eq_sym heq) (λ w, lt w (length (Cons x y))) hlt2) };
          rewrite (take_succ_Cons (succ m) x y (succ_in_omega m hm));
          rewrite (hIH m (succ_leE m (length y) hlt3));
          rewrite (take_succ_Cons m x y hm);
          rewrite (nth_Cons m x y hm);
          rewrite (app_Cons x (take m y) (Cons (nth m y) Nil));
          reflexivity } } };
  refine hmain i hlt
end;

opaque symbol take_add (xs A j i : τ ι) :
  π (xs ∈ list A) → π (j ∈ omega) → π (i ∈ omega) →
  π (take (add i j) xs = app (take i xs) (take j (drop i xs))) ≔
begin
  assume xs A j i hxs hj hi;
  have hmain : π (Ball omega (λ i2,
      take (add i2 j) xs = app (take i2 xs) (take j (drop i2 xs))))
    { refine list_induct xs A (λ w, Ball omega (λ i2,
        take (add i2 j) w = app (take i2 w) (take j (drop i2 w)))) hxs _ _
      { assume i2 hi2;
        rewrite (take_Nil_h (add i2 j) (add_type i2 j));
        rewrite (take_Nil_h i2 hi2);
        rewrite (drop_Nil i2 hi2);
        rewrite (take_Nil_h j hj);
        rewrite (app_Nil Nil);
        reflexivity }
      { assume x y hx hy hIH i2 hi2;
        refine natE i2
          (take (add i2 j) (Cons x y)
           = app (take i2 (Cons x y)) (take j (drop i2 (Cons x y)))) hi2 _ _
        { assume h0;
          rewrite h0;
          rewrite (add_0 j hj);
          rewrite (take_0 (Cons x y) A (list_consI x y A hx hy));
          rewrite (drop_0 (Cons x y));
          rewrite (app_Nil (take j (Cons x y)));
          reflexivity }
        { assume m hm heq;
          rewrite heq;
          rewrite (add_succ m j);
          rewrite (take_succ_Cons (add m j) x y (add_type m j));
          rewrite (hIH m hm);
          rewrite (take_succ_Cons m x y hm);
          rewrite (drop_succ_Cons m x y hm);
          rewrite (app_Cons x (take m y) (take j (drop m y)));
          reflexivity } } };
  refine hmain i hi
end;

opaque symbol length_take (l A : τ ι) :
  π (l ∈ list A) → π (Ball omega (λ n, length (take n l) = min n (length l))) ≔
begin
  assume l A hl;
  refine list_induct l A
    (λ w, Ball omega (λ n, length (take n w) = min n (length w))) hl _ _
  { assume n hn;
    rewrite (take_Nil_h n hn);
    rewrite length_Nil;
    refine eq_sym (min_02 n hn) }
  { assume x y hx hy hIH n hn;
    refine natE n (length (take n (Cons x y)) = min n (length (Cons x y))) hn _ _
    { assume h0;
      rewrite h0;
      rewrite (take_0 (Cons x y) A (list_consI x y A hx hy));
      rewrite length_Nil;
      refine eq_sym (min_0 (length (Cons x y))
        (length_type (Cons x y) A (list_consI x y A hx hy))) }
    { assume m hm heq;
      rewrite heq;
      rewrite (take_succ_Cons m x y hm);
      rewrite (length_Cons x (take m y));
      rewrite (hIH m hm);
      rewrite (length_Cons x y);
      refine eq_sym (min_succ_succ m (length y) hm (length_type y A hy)) } }
end;

// ===========================================================================
// The function zip
// ===========================================================================

opaque symbol list_on_set_of_list (xs A : τ ι) :
  π (xs ∈ list A) → π (xs ∈ list (set_of_list xs)) ≔
begin
  assume xs A hxs;
  refine list_induct xs A (λ w, w ∈ list (set_of_list w)) hxs _ _
  { refine list_0I (set_of_list Nil) }
  { assume x y hx hy hIH;
    refine ind_eq (set_of_list_Cons x y) (λ w, Cons x y ∈ list w) _;
    refine list_consI x y (cons x (set_of_list y)) (consI1 x (set_of_list y)) _;
    refine list_mono (set_of_list y) (cons x (set_of_list y)) _ y hIH;
    assume z hz;
    refine consI2 z x (set_of_list y) hz }
end;

opaque symbol zip_Nil (ys A : τ ι) : π (ys ∈ list A) → π (zip Nil ys = Nil) ≔
begin admit end;

opaque symbol zip_Nil2 (xs A : τ ι) : π (xs ∈ list A) → π (zip xs Nil = Nil) ≔
begin admit end;

opaque symbol zip_aux_unique (B C xs A ys : τ ι) :
  π (B ⊆ C) → π (xs ∈ list A) → π (ys ∈ list B) →
  π (fapply (zip_aux C xs) ys = fapply (zip_aux B xs) ys) ≔
begin admit end;

opaque symbol zip_Cons_Cons (xs A ys B x y : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list B) → π (x ∈ A) → π (y ∈ B) →
  π (zip (Cons x xs) (Cons y ys) = Cons (Pair x y) (zip xs ys)) ≔
begin admit end;

opaque symbol zip_type (xs A ys B : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list B) → π (zip xs ys ∈ list (Sigma A (λ _, B))) ≔
begin admit end;

// zip length
opaque symbol length_zip (xs A ys B : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list B) →
  π (length (zip xs ys) = min (length xs) (length ys)) ≔
begin admit end;

opaque symbol zip_append1 (ys A zs B xs : τ ι) :
  π (ys ∈ list A) → π (zs ∈ list B) → π (xs ∈ list A) →
  π (zip (app xs ys) zs
     = app (zip xs (take (length xs) zs)) (zip ys (drop (length xs) zs))) ≔
begin admit end;

opaque symbol zip_append2 (xs A zs B ys : τ ι) :
  π (xs ∈ list A) → π (zs ∈ list B) → π (ys ∈ list B) →
  π (zip xs (app ys zs)
     = app (zip (take (length ys) xs) ys) (zip (drop (length ys) xs) zs)) ≔
begin admit end;

opaque symbol zip_append (xs us ys vs A B : τ ι) :
  π (length xs = length us) → π (length ys = length vs) →
  π (xs ∈ list A) → π (us ∈ list B) → π (ys ∈ list A) → π (vs ∈ list B) →
  π (zip (app xs ys) (app us vs) = app (zip xs us) (zip ys vs)) ≔
begin admit end;

opaque symbol zip_rev (ys B xs A : τ ι) :
  π (ys ∈ list B) → π (xs ∈ list A) → π (length xs = length ys) →
  π (zip (rev xs) (rev ys) = rev (zip xs ys)) ≔
begin admit end;

opaque symbol nth_zip (ys B i A xs : τ ι) :
  π (ys ∈ list B) → π (i ∈ omega) → π (xs ∈ list A) →
  π (lt i (length xs)) → π (lt i (length ys)) →
  π (nth i (zip xs ys) = Pair (nth i xs) (nth i ys)) ≔
begin admit end;

// NOTE: the .thy's hypothesis list literally includes `i \<in> nat` even
// though the `i` bound inside the ∃ in the conclusion shadows it (so the
// hypothesis is, as stated, unused) — ported literally per CLAUDE.md's
// faithfulness requirement, not "fixed".
opaque symbol set_of_list_zip (xs A ys B i : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list B) → π (i ∈ omega) →
  π (set_of_list (zip xs ys)
     = Collect (Sigma A (λ _, B))
         (λ p, Bex omega (λ i2, lt i2 (min (length xs) (length ys))
                ∧ fst p = nth i2 xs ∧ snd p = nth i2 ys))) ≔
begin admit end;

// ===========================================================================
// (** list_update **)
// ===========================================================================

// port-internal helper — list_update's Cons equation, unfolded from
// list_update_def via list_rec_Cons + beta.
private opaque symbol list_update_Cons_h (i x xs v : τ ι) :
  π (i ∈ omega) →
  π (list_update (Cons x xs) i v =
     nat_case (Cons v xs)
       (λ m, Cons x (fapply (list_rec (Lambda omega (λ _, Nil))
         (λ u us vs, Lambda omega
           (λ n2, nat_case (Cons v us) (λ m2, Cons u (fapply vs m2)) n2))
         xs) m)) i) ≔
begin
  assume i x xs v hi;
  rewrite (list_update_def (Cons x xs) i v);
  rewrite (list_rec_Cons (Lambda omega (λ _, Nil))
    (λ u us vs, Lambda omega
      (λ n2, nat_case (Cons v us) (λ m2, Cons u (fapply vs m2)) n2)) x xs);
  simplify rule off;
  refine beta omega
    (λ n2, nat_case (Cons v xs)
      (λ m2, Cons x (fapply (list_rec (Lambda omega (λ _, Nil))
        (λ u us vs, Lambda omega
          (λ n3, nat_case (Cons v us) (λ m3, Cons u (fapply vs m3)) n3))
        xs) m2)) n2) i hi
end;

opaque symbol list_update_Nil (i v : τ ι) :
  π (i ∈ omega) → π (list_update Nil i v = Nil) ≔
begin
  assume i v hi;
  rewrite (list_update_def Nil i v);
  rewrite (list_rec_Nil (Lambda omega (λ _, Nil))
    (λ u us vs, Lambda omega
      (λ n2, nat_case (Cons v us) (λ m2, Cons u (fapply vs m2)) n2)));
  refine beta omega (λ _, Nil) i hi
end;

opaque symbol list_update_Cons_0 (x xs v : τ ι) :
  π (list_update (Cons x xs) empty v = Cons v xs) ≔
begin
  assume x xs v;
  rewrite (list_update_Cons_h empty x xs v zero_in_omega);
  refine nat_case_0 (Cons v xs)
    (λ m, Cons x (fapply (list_rec (Lambda omega (λ _, Nil))
      (λ u us vs, Lambda omega
        (λ n2, nat_case (Cons v us) (λ m2, Cons u (fapply vs m2)) n2))
      xs) m))
end;

opaque symbol list_update_Cons_succ (n x xs v : τ ι) :
  π (n ∈ omega) →
  π (list_update (Cons x xs) (succ n) v = Cons x (list_update xs n v)) ≔
begin
  assume n x xs v hn;
  rewrite (list_update_Cons_h (succ n) x xs v (succ_in_omega n hn));
  rewrite (nat_case_succ (Cons v xs)
    (λ m, Cons x (fapply (list_rec (Lambda omega (λ _, Nil))
      (λ u us vs, Lambda omega
        (λ n2, nat_case (Cons v us) (λ m2, Cons u (fapply vs m2)) n2))
      xs) m)) n);
  simplify rule off;
  rewrite left (list_update_def xs n v);
  reflexivity
end;

opaque symbol list_update_type (xs A v n : τ ι) :
  π (xs ∈ list A) → π (v ∈ A) → π (n ∈ omega) →
  π (list_update xs n v ∈ list A) ≔
begin
  assume xs A v n hxs hv hn;
  have hmain : π (Ball omega (λ n2, list_update xs n2 v ∈ list A))
    { refine list_induct xs A
        (λ w, Ball omega (λ n2, list_update w n2 v ∈ list A)) hxs _ _
      { assume n2 hn2;
        refine ind_eq (list_update_Nil n2 v hn2) (λ w, w ∈ list A) (list_0I A) }
      { assume x y hx hy hIH n2 hn2;
        refine natE n2 (list_update (Cons x y) n2 v ∈ list A) hn2 _ _
        { assume h0;
          rewrite h0;
          refine ind_eq (list_update_Cons_0 x y v) (λ w, w ∈ list A)
            (list_consI v y A hv hy) }
        { assume m hm heq;
          rewrite heq;
          refine ind_eq (list_update_Cons_succ m x y v hm) (λ w, w ∈ list A)
            (list_consI x (list_update y m v) A hx (hIH m hm)) } } };
  refine hmain n hn
end;

opaque symbol length_list_update (xs A i v : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (length (list_update xs i v) = length xs) ≔
begin
  assume xs A i v hxs hi;
  have hmain : π (Ball omega (λ i2, length (list_update xs i2 v) = length xs))
    { refine list_induct xs A
        (λ w, Ball omega (λ i2, length (list_update w i2 v) = length w)) hxs _ _
      { assume i2 hi2;
        rewrite (list_update_Nil i2 v hi2);
        reflexivity }
      { assume x y hx hy hIH i2 hi2;
        refine natE i2
          (length (list_update (Cons x y) i2 v) = length (Cons x y)) hi2 _ _
        { assume h0;
          rewrite h0;
          rewrite (list_update_Cons_0 x y v);
          rewrite (length_Cons v y);
          rewrite (length_Cons x y);
          reflexivity }
        { assume m hm heq;
          rewrite heq;
          rewrite (list_update_Cons_succ m x y v hm);
          rewrite (length_Cons x (list_update y m v));
          rewrite (length_Cons x y);
          rewrite (hIH m hm);
          reflexivity } } };
  refine hmain i hi
end;

opaque symbol nth_list_update (xs A i j x : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (j ∈ omega) → π (lt i (length xs)) →
  π (nth j (list_update xs i x) = If (i = j) x (nth j xs)) ≔
begin
  assume xs A i j x hxs hi hj hlt;
  have hmain : π (Ball omega (λ i2, Ball omega (λ j2, lt i2 (length xs) ⇒
      nth j2 (list_update xs i2 x) = If (i2 = j2) x (nth j2 xs))))
    { refine list_induct xs A
        (λ w, Ball omega (λ i2, Ball omega (λ j2, lt i2 (length w) ⇒
           nth j2 (list_update w i2 x) = If (i2 = j2) x (nth j2 w)))) hxs _ _
      { assume i2 hi2 j2 hj2 hlt2;
        refine ⊥ₑ (not_lt0 i2 (ind_eq (eq_sym length_Nil) (λ w, lt i2 w) hlt2)) }
      { assume a l ha hl hIH i2 hi2 j2 hj2 hlt2;
        refine natE i2
          (nth j2 (list_update (Cons a l) i2 x) = If (i2 = j2) x (nth j2 (Cons a l)))
          hi2 _ _
        { assume h0i;
          rewrite h0i;
          rewrite (list_update_Cons_0 a l x);
          refine natE j2
            (nth j2 (Cons x l) = If (empty = j2) x (nth j2 (Cons a l))) hj2 _ _
          { assume h0j;
            rewrite h0j;
            rewrite (nth_0 x l);
            rewrite (If_P (empty = empty) x (nth empty (Cons a l)) (eq_refl empty));
            reflexivity }
          { assume k hk heqj;
            rewrite heqj;
            rewrite (nth_Cons k x l hk);
            have hne : π (¬ (empty = succ k))
              { assume h2; refine succ_neq_0 k (eq_sym h2) };
            rewrite (If_not_P (empty = succ k) x (nth (succ k) (Cons a l)) hne);
            refine eq_sym (nth_Cons k a l hk) } }
        { assume m hm heqi;
          rewrite heqi;
          rewrite (list_update_Cons_succ m a l x hm);
          have hlt3 : π (lt m (length l))
            { refine succ_leE m (length l)
                (ind_eq (eq_sym (length_Cons a l)) (λ w, lt (succ m) w)
                  (ind_eq (eq_sym heqi) (λ w, lt w (length (Cons a l))) hlt2)) };
          refine natE j2
            (nth j2 (Cons a (list_update l m x))
             = If (succ m = j2) x (nth j2 (Cons a l))) hj2 _ _
          { assume h0j;
            rewrite h0j;
            rewrite (nth_0 a (list_update l m x));
            have hne : π (¬ (succ m = empty)) { refine succ_neq_0 m };
            rewrite (If_not_P (succ m = empty) x (nth empty (Cons a l)) hne);
            refine eq_sym (nth_0 a l) }
          { assume k hk heqj;
            rewrite heqj;
            rewrite (nth_Cons k a (list_update l m x) hk);
            rewrite (hIH m hm k hk hlt3);
            rewrite (nth_Cons k a l hk);
            refine ∨ₑ (em (m = k)) _ _
            { assume heqmk;
              rewrite (If_P (m = k) x (nth k l) heqmk);
              have heqs : π (succ m = succ k) { rewrite heqmk; reflexivity };
              rewrite (If_P (succ m = succ k) x (nth k l) heqs);
              reflexivity }
            { assume hnemk;
              rewrite (If_not_P (m = k) x (nth k l) hnemk);
              have hnes : π (¬ (succ m = succ k))
                { assume h2; refine hnemk (succ_inject m k h2) };
              rewrite (If_not_P (succ m = succ k) x (nth k l) hnes);
              reflexivity } } } } };
  refine hmain i hi j hj hlt
end;

opaque symbol nth_list_update_eq (i xs A x : τ ι) :
  π (lt i (length xs)) → π (xs ∈ list A) → π (nth i (list_update xs i x) = x) ≔
begin
  assume i xs A x hlt hxs;
  have hi : π (i ∈ omega)
    { refine lt_nat_in_nat i (length xs) hlt (length_type xs A hxs) };
  rewrite (nth_list_update xs A i i x hxs hi hi hlt);
  refine If_P (i = i) x (nth i xs) (eq_refl i)
end;

opaque symbol nth_list_update_neq (xs A i j x : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (j ∈ omega) → π (i ≠ j) →
  π (nth j (list_update xs i x) = nth j xs) ≔
begin
  assume xs A i j x hxs hi hj hne;
  have hmain : π (Ball omega (λ i2, Ball omega (λ j2, (¬ (i2 = j2)) ⇒
      nth j2 (list_update xs i2 x) = nth j2 xs)))
    { refine list_induct xs A
        (λ w, Ball omega (λ i2, Ball omega (λ j2, (¬ (i2 = j2)) ⇒
           nth j2 (list_update w i2 x) = nth j2 w))) hxs _ _
      { assume i2 hi2 j2 hj2 hne2;
        rewrite (list_update_Nil i2 x hi2);
        reflexivity }
      { assume a l ha hl hIH i2 hi2 j2 hj2 hne2;
        refine natE i2
          (nth j2 (list_update (Cons a l) i2 x) = nth j2 (Cons a l)) hi2 _ _
        { assume h0i;
          rewrite h0i;
          rewrite (list_update_Cons_0 a l x);
          refine natE j2 (nth j2 (Cons x l) = nth j2 (Cons a l)) hj2 _ _
          { assume h0j;
            have heq : π (i2 = j2) { rewrite h0i; rewrite h0j; reflexivity };
            refine ⊥ₑ (hne2 heq) }
          { assume k hk heqj;
            rewrite heqj;
            rewrite (nth_Cons k x l hk);
            refine eq_sym (nth_Cons k a l hk) } }
        { assume m hm heqi;
          rewrite heqi;
          rewrite (list_update_Cons_succ m a l x hm);
          refine natE j2
            (nth j2 (Cons a (list_update l m x)) = nth j2 (Cons a l)) hj2 _ _
          { assume h0j;
            rewrite h0j;
            rewrite (nth_0 a (list_update l m x));
            refine eq_sym (nth_0 a l) }
          { assume k hk heqj;
            rewrite heqj;
            rewrite (nth_Cons k a (list_update l m x) hk);
            rewrite (nth_Cons k a l hk);
            refine hIH m hm k hk _;
            assume hmk;
            have heq : π (i2 = j2)
              { rewrite heqi; rewrite heqj; rewrite hmk; reflexivity };
            refine hne2 heq } } } };
  refine hmain i hi j hj hne
end;

opaque symbol list_update_overwrite (xs A i x y : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (lt i (length xs)) →
  π (list_update (list_update xs i x) i y = list_update xs i y) ≔
begin
  assume xs A i x y hxs hi hlt;
  have hmain : π (Ball omega (λ i2, lt i2 (length xs) ⇒
      list_update (list_update xs i2 x) i2 y = list_update xs i2 y))
    { refine list_induct xs A (λ w, Ball omega (λ i2, lt i2 (length w) ⇒
        list_update (list_update w i2 x) i2 y = list_update w i2 y)) hxs _ _
      { assume i2 hi2 hlt2;
        refine ⊥ₑ (not_lt0 i2 (ind_eq (eq_sym length_Nil) (λ w, lt i2 w) hlt2)) }
      { assume a l ha hl hIH i2 hi2 hlt2;
        refine natE i2
          (list_update (list_update (Cons a l) i2 x) i2 y
           = list_update (Cons a l) i2 y) hi2 _ _
        { assume h0;
          rewrite h0;
          rewrite (list_update_Cons_0 a l x);
          rewrite (list_update_Cons_0 x l y);
          refine eq_sym (list_update_Cons_0 a l y) }
        { assume m hm heq;
          rewrite heq;
          have hlt3 : π (lt m (length l))
            { refine succ_leE m (length l)
                (ind_eq (eq_sym (length_Cons a l)) (λ w, lt (succ m) w)
                  (ind_eq (eq_sym heq) (λ w, lt w (length (Cons a l))) hlt2)) };
          rewrite (list_update_Cons_succ m a l x hm);
          rewrite (list_update_Cons_succ m a (list_update l m x) y hm);
          rewrite (list_update_Cons_succ m a l y hm);
          rewrite (hIH m hm hlt3);
          reflexivity } } };
  refine hmain i hi hlt
end;

opaque symbol list_update_same_conv (xs A i x : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (lt i (length xs)) →
  π (list_update xs i x = xs ⇔ nth i xs = x) ≔
begin
  assume xs A i x hxs hi hlt;
  have hmain : π (Ball omega (λ i2, lt i2 (length xs) ⇒
      (list_update xs i2 x = xs ⇔ nth i2 xs = x)))
    { refine list_induct xs A (λ w, Ball omega (λ i2, lt i2 (length w) ⇒
        (list_update w i2 x = w ⇔ nth i2 w = x))) hxs _ _
      { assume i2 hi2 hlt2;
        refine ⊥ₑ (not_lt0 i2 (ind_eq (eq_sym length_Nil) (λ w, lt i2 w) hlt2)) }
      { assume a l ha hl hIH i2 hi2 hlt2;
        refine natE i2
          (list_update (Cons a l) i2 x = Cons a l ⇔ nth i2 (Cons a l) = x) hi2 _ _
        { assume h0;
          rewrite h0;
          rewrite (list_update_Cons_0 a l x);
          rewrite (nth_0 a l);
          apply ∧ᵢ
          { assume h;
            refine eq_sym (∧ₑ₁ (∧ₑ₁ (Cons_iff x l a l) h)) }
          { assume h; rewrite h; reflexivity } }
        { assume m hm heq;
          rewrite heq;
          have hlt3 : π (lt m (length l))
            { refine succ_leE m (length l)
                (ind_eq (eq_sym (length_Cons a l)) (λ w, lt (succ m) w)
                  (ind_eq (eq_sym heq) (λ w, lt w (length (Cons a l))) hlt2)) };
          rewrite (list_update_Cons_succ m a l x hm);
          rewrite (nth_Cons m a l hm);
          apply ∧ᵢ
          { assume h;
            refine ∧ₑ₁ (hIH m hm hlt3)
              (∧ₑ₂ (∧ₑ₁ (Cons_iff a (list_update l m x) a l) h)) }
          { assume h;
            rewrite (∧ₑ₂ (hIH m hm hlt3) h);
            reflexivity } } } };
  refine hmain i hi hlt
end;

opaque symbol update_zip (ys B i A xy xs : τ ι) :
  π (ys ∈ list B) → π (i ∈ omega) → π (xy ∈ Sigma A (λ _, B)) →
  π (xs ∈ list A) → π (length xs = length ys) →
  π (list_update (zip xs ys) i xy
     = zip (list_update xs i (fst xy)) (list_update ys i (snd xy))) ≔
begin admit end;

opaque symbol set_update_subset_cons (xs A i x : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) →
  π (set_of_list (list_update xs i x) ⊆ cons x (set_of_list xs)) ≔
begin admit end;

opaque symbol set_of_list_update_subsetI (xs A x i : τ ι) :
  π (set_of_list xs ⊆ A) → π (xs ∈ list A) → π (x ∈ A) → π (i ∈ omega) →
  π (set_of_list (list_update xs i x) ⊆ A) ≔
begin admit end;

// ===========================================================================
// (** upt **)
// ===========================================================================

// port-internal helpers — upt's primrec equations
private opaque symbol upt_0_h (i : τ ι) : π (upt i empty = Nil) ≔
  nat_rec_0 Nil (λ j2 r, If (le i j2) (app r (Cons j2 Nil)) Nil);
private opaque symbol upt_succ_h (i j : τ ι) :
  π (j ∈ omega) →
  π (upt i (succ j) = If (le i j) (app (upt i j) (Cons j Nil)) Nil) ≔
  λ hj, nat_rec_succ j Nil (λ j2 r, If (le i j2) (app r (Cons j2 Nil)) Nil) hj;

opaque symbol upt_rec (i j : τ ι) :
  π (j ∈ omega) → π (upt i j = If (lt i j) (Cons i (upt (succ i) j)) Nil) ≔
begin
  assume i j hj;
  refine nat_induct (λ w, upt i w = If (lt i w) (Cons i (upt (succ i) w)) Nil) _ _ j hj
  { simplify rule off;
    rewrite (upt_0_h i);
    rewrite (If_not_P (lt i empty) (Cons i (upt (succ i) empty)) Nil (not_lt0 i));
    reflexivity }
  { assume j2 hj2 hIH;
    have hOj2 : π (Ord j2) { refine nat_into_Ord j2 hj2 };
    rewrite (upt_succ_h i j2 hj2);
    refine ∨ₑ (em (le i j2)) _ _
    { assume hle;
      rewrite (If_P (le i j2) (app (upt i j2) (Cons j2 Nil)) Nil hle);
      rewrite (If_P (lt i (succ j2)) (Cons i (upt (succ i) (succ j2))) Nil hle);
      rewrite (upt_succ_h (succ i) j2 hj2);
      refine ∨ₑ (leE i j2 hle) _ _
      { assume hmem;
        have hlt : π (lt i j2) { refine ltI i j2 hmem hOj2 };
        have hIH2 : π (upt i j2 = Cons i (upt (succ i) j2))
          { rewrite hIH;
            refine If_P (lt i j2) (Cons i (upt (succ i) j2)) Nil hlt };
        have hles : π (le (succ i) j2) { refine succ_leI i j2 hOj2 hmem };
        rewrite hIH2;
        rewrite (app_Cons i (upt (succ i) j2) (Cons j2 Nil));
        rewrite (If_P (le (succ i) j2) (app (upt (succ i) j2) (Cons j2 Nil)) Nil hles);
        reflexivity }
      { assume heq;
        have hIH2 : π (upt i j2 = Nil)
          { rewrite hIH;
            refine If_not_P (lt i j2) (Cons i (upt (succ i) j2)) Nil _;
            assume hlt;
            refine lt_irrefl j2 (ind_eq (eq_sym heq) (λ w, lt w j2) hlt) };
        have hnles : π (¬ (le (succ i) j2))
          { assume h2;
            refine lt_irrefl j2
              (ind_eq (eq_sym heq) (λ w, lt w j2) (succ_leE i j2 h2)) };
        rewrite hIH2;
        rewrite (app_Nil (Cons j2 Nil));
        rewrite (If_not_P (le (succ i) j2)
          (app (upt (succ i) j2) (Cons j2 Nil)) Nil hnles);
        rewrite heq;
        reflexivity } }
    { assume hnle;
      rewrite (If_not_P (le i j2) (app (upt i j2) (Cons j2 Nil)) Nil hnle);
      rewrite (If_not_P (lt i (succ j2)) (Cons i (upt (succ i) (succ j2))) Nil hnle);
      reflexivity } }
end;

opaque symbol upt_conv_Nil (i j : τ ι) :
  π (le j i) → π (j ∈ omega) → π (upt i j = Nil) ≔
begin
  assume i j hle hj;
  refine natE j (upt i j = Nil) hj _ _
  { assume h0; rewrite h0; refine upt_0_h i }
  { assume m hm heq;
    rewrite heq;
    rewrite (upt_succ_h i m hm);
    refine If_not_P (le i m) (app (upt i m) (Cons m Nil)) Nil _;
    assume h2;
    have hle2 : π (le (succ m) i) { refine ind_eq (eq_sym heq) (λ w, le w i) hle };
    refine lt_irrefl m (succ_leE m m (le_trans (succ m) i m hle2 h2)) }
end;

// Only needed if upt_Suc is deleted from the simpset
opaque symbol upt_succ_append (i j : τ ι) :
  π (le i j) → π (j ∈ omega) → π (upt i (succ j) = app (upt i j) (Cons j Nil)) ≔
begin
  assume i j hle hj;
  rewrite (upt_succ_h i j hj);
  refine If_P (le i j) (app (upt i j) (Cons j Nil)) Nil hle
end;

opaque symbol upt_conv_Cons (i j : τ ι) :
  π (lt i j) → π (j ∈ omega) → π (upt i j = Cons i (upt (succ i) j)) ≔
begin
  assume i j hlt hj;
  rewrite (upt_rec i j hj);
  refine If_P (lt i j) (Cons i (upt (succ i) j)) Nil hlt
end;

opaque symbol upt_type (i j : τ ι) : π (j ∈ omega) → π (upt i j ∈ list omega) ≔
begin
  assume i j hj;
  refine nat_induct (λ w, upt i w ∈ list omega) _ _ j hj
  { refine ind_eq (upt_0_h i) (λ w, w ∈ list omega) (list_0I omega) }
  { assume j2 hj2 hIH;
    refine ind_eq (upt_succ_h i j2 hj2) (λ w, w ∈ list omega) _;
    refine ∨ₑ (em (le i j2)) _ _
    { assume h;
      refine ind_eq (If_P (le i j2) (app (upt i j2) (Cons j2 Nil)) Nil h)
        (λ w, w ∈ list omega)
        (app_type (upt i j2) (Cons j2 Nil) omega hIH
          (list_consI j2 Nil omega hj2 (list_0I omega))) }
    { assume h;
      refine ind_eq (If_not_P (le i j2) (app (upt i j2) (Cons j2 Nil)) Nil h)
        (λ w, w ∈ list omega) (list_0I omega) } }
end;

// LOOPS as a simprule, since j<=j
opaque symbol upt_add_eq_append (i j k : τ ι) :
  π (le i j) → π (j ∈ omega) → π (k ∈ omega) →
  π (upt i (add j k) = app (upt i j) (upt j (add j k))) ≔
begin
  assume i j k hle hj hk;
  refine nat_induct (λ w, upt i (add j w) = app (upt i j) (upt j (add j w))) _ _ k hk
  { simplify rule off;
    rewrite (add_0_right j hj);
    rewrite (upt_conv_Nil j j (le_refl j (nat_into_Ord j hj)) hj);
    refine eq_sym (app_right_Nil (upt i j) omega (upt_type i j hj)) }
  { assume k2 hk2 hIH;
    rewrite (add_succ_right j k2);
    have hijk : π (le i (add j k2))
      { refine le_trans i j (add j k2) hle (add_le_self j k2 hj) };
    rewrite (upt_succ_append i (add j k2) hijk (add_type j k2));
    rewrite (upt_succ_append j (add j k2) (add_le_self j k2 hj) (add_type j k2));
    rewrite hIH;
    refine app_assoc (upt i j) omega (upt j (add j k2)) (Cons (add j k2) Nil)
      (upt_type i j hj) }
end;

opaque symbol length_upt (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (length (upt i j) = diff j i) ≔
begin
  assume i j hi hj;
  refine nat_induct (λ w, length (upt i w) = diff w i) _ _ j hj
  { simplify rule off;
    rewrite (upt_0_h i);
    rewrite length_Nil;
    refine eq_sym (diff_0_eq_0 i) }
  { assume j2 hj2 hIH;
    rewrite (upt_succ_h i j2 hj2);
    refine ∨ₑ (em (le i j2)) _ _
    { assume h;
      rewrite (If_P (le i j2) (app (upt i j2) (Cons j2 Nil)) Nil h);
      rewrite (length_app (upt i j2) (Cons j2 Nil) omega (upt_type i j2 hj2)
        (list_consI j2 Nil omega hj2 (list_0I omega)));
      rewrite hIH;
      rewrite (length_Cons j2 Nil);
      rewrite length_Nil;
      rewrite (add_succ_right (diff j2 i) empty);
      rewrite (add_0_right (diff j2 i) (diff_type j2 i));
      refine eq_sym (diff_succ i j2 h hj2) }
    { assume h;
      rewrite (If_not_P (le i j2) (app (upt i j2) (Cons j2 Nil)) Nil h);
      rewrite length_Nil;
      have hle2 : π (le (succ j2) i)
        { refine not_lt_imp_le i (succ j2) (nat_into_Ord i hi)
            (Ord_succ j2 (nat_into_Ord j2 hj2)) h };
      have hn2 : π (le (natify (succ j2)) (natify i))
        { rewrite (natify_ident (succ j2) (succ_in_omega j2 hj2));
          rewrite (natify_ident i hi);
          refine hle2 };
      refine eq_sym (∧ₑ₂ (diff_is_0_iff (succ j2) i) hn2) } }
end;

opaque symbol nth_upt (i j k : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (k ∈ omega) → π (lt (add i k) j) →
  π (nth k (upt i j) = add i k) ≔
begin
  assume i j k hi hj hk hlt;
  have hmain : π (Ball omega (λ w, Ball omega
      (λ i2, lt (add i2 w) j ⇒ nth w (upt i2 j) = add i2 w)))
    { refine nat_induct (λ w, Ball omega
        (λ i2, lt (add i2 w) j ⇒ nth w (upt i2 j) = add i2 w)) _ _
      { assume i2 hi2 hlt2;
        have hlti : π (lt i2 j)
          { refine ind_eq (eq_sym (add_0_right i2 hi2)) (λ w, lt w j) hlt2 };
        rewrite (upt_conv_Cons i2 j hlti hj);
        rewrite (nth_0 i2 (upt (succ i2) j));
        refine eq_sym (add_0_right i2 hi2) }
      { assume m2 hm2 hIH i2 hi2 hlt2;
        have hlei : π (le i2 (add i2 (succ m2)))
          { refine add_le_self i2 (succ m2) hi2 };
        have hlti : π (lt i2 j)
          { refine lt_trans1 i2 (add i2 (succ m2)) j hlei hlt2 };
        rewrite (upt_conv_Cons i2 j hlti hj);
        rewrite (nth_Cons m2 i2 (upt (succ i2) j) hm2);
        have h1 : π (add (succ i2) m2 = add i2 (succ m2))
          { rewrite (add_succ i2 m2);
            refine eq_sym (add_succ_right i2 m2) };
        have hlt3 : π (lt (add (succ i2) m2) j)
          { refine ind_eq h1 (λ w, lt w j) hlt2 };
        rewrite (hIH (succ i2) (succ_in_omega i2 hi2) hlt3);
        refine h1 } };
  refine hmain k hk i hi hlt
end;

opaque symbol take_upt (m n i : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (i ∈ omega) → π (le (add i m) n) →
  π (take m (upt i n) = upt i (add i m)) ≔
begin
  assume m n i hm hn hi hle;
  have hmain : π (Ball omega (λ w, Ball omega
      (λ i2, le (add i2 w) n ⇒ take w (upt i2 n) = upt i2 (add i2 w))))
    { refine nat_induct (λ w, Ball omega
        (λ i2, le (add i2 w) n ⇒ take w (upt i2 n) = upt i2 (add i2 w))) _ _
      { assume i2 hi2 hle2;
        rewrite (take_0 (upt i2 n) omega (upt_type i2 n hn));
        rewrite (add_0_right i2 hi2);
        refine eq_sym (upt_conv_Nil i2 i2
          (le_refl i2 (nat_into_Ord i2 hi2)) hi2) }
      { assume m2 hm2 hIH i2 hi2 hle2;
        have h1 : π (add (succ i2) m2 = add i2 (succ m2))
          { rewrite (add_succ i2 m2);
            refine eq_sym (add_succ_right i2 m2) };
        have hle3 : π (le (add (succ i2) m2) n)
          { refine ind_eq h1 (λ w, le w n) hle2 };
        have hltsum : π (lt i2 (add i2 (succ m2)))
          { refine ind_eq (add_succ_right i2 m2) (λ w, lt i2 w)
              (add_le_self i2 m2 hi2) };
        have hltn : π (lt i2 n)
          { refine lt_trans2 i2 (add i2 (succ m2)) n hltsum hle2 };
        rewrite (upt_conv_Cons i2 n hltn hn);
        rewrite (take_succ_Cons m2 i2 (upt (succ i2) n) hm2);
        rewrite (hIH (succ i2) (succ_in_omega i2 hi2) hle3);
        rewrite h1;
        refine eq_sym (upt_conv_Cons i2 (add i2 (succ m2)) hltsum
          (add_type i2 (succ m2))) } };
  refine hmain m hm i hi hle
end;

opaque symbol map_succ_upt (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (map succ (upt m n) = upt (succ m) (succ n)) ≔
begin
  assume m n hm hn;
  refine nat_induct (λ w, map succ (upt m w) = upt (succ m) (succ w)) _ _ n hn
  { simplify rule off;
    rewrite (upt_0_h m);
    rewrite (map_Nil succ);
    rewrite (upt_succ_h (succ m) empty zero_in_omega);
    have hn0 : π (¬ (le (succ m) empty))
      { assume h2; refine succ_neq_0 m (le0D (succ m) h2) };
    rewrite (If_not_P (le (succ m) empty)
      (app (upt (succ m) empty) (Cons empty Nil)) Nil hn0);
    reflexivity }
  { assume n2 hn2 hIH;
    rewrite (upt_succ_h m n2 hn2);
    rewrite (upt_succ_h (succ m) (succ n2) (succ_in_omega n2 hn2));
    refine ∨ₑ (em (le m n2)) _ _
    { assume h;
      rewrite (If_P (le m n2) (app (upt m n2) (Cons n2 Nil)) Nil h);
      have hles : π (le (succ m) (succ n2))
        { refine succ_leI m (succ n2)
            (Ord_succ n2 (nat_into_Ord n2 hn2)) (ltD m (succ n2) h) };
      rewrite (If_P (le (succ m) (succ n2))
        (app (upt (succ m) (succ n2)) (Cons (succ n2) Nil)) Nil hles);
      rewrite (map_app_distrib (upt m n2) omega (Cons n2 Nil) succ
        (upt_type m n2 hn2));
      rewrite hIH;
      rewrite (map_Cons succ n2 Nil);
      rewrite (map_Nil succ);
      reflexivity }
    { assume h;
      rewrite (If_not_P (le m n2) (app (upt m n2) (Cons n2 Nil)) Nil h);
      have hnles : π (¬ (le (succ m) (succ n2)))
        { assume h2; refine h (succ_leE m (succ n2) h2) };
      rewrite (If_not_P (le (succ m) (succ n2))
        (app (upt (succ m) (succ n2)) (Cons (succ n2) Nil)) Nil hnles);
      refine map_Nil succ } }
end;

opaque symbol nth_map (xs A n : τ ι) (f : τ ι → τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) → π (lt n (length xs)) →
  π (nth n (map f xs) = f (nth n xs)) ≔
begin
  assume xs A n f hxs hn hlt;
  have hmain : π (Ball omega (λ n2, lt n2 (length xs) ⇒
      nth n2 (map f xs) = f (nth n2 xs)))
    { refine list_induct xs A (λ w, Ball omega (λ n2, lt n2 (length w) ⇒
        nth n2 (map f w) = f (nth n2 w))) hxs _ _
      { assume n2 hn2 hlt2;
        refine ⊥ₑ (not_lt0 n2 (ind_eq (eq_sym length_Nil) (λ w, lt n2 w) hlt2)) }
      { assume x y hx hy hIH n2 hn2 hlt2;
        refine natE n2 (nth n2 (map f (Cons x y)) = f (nth n2 (Cons x y))) hn2 _ _
        { assume h0;
          rewrite h0;
          rewrite (map_Cons f x y);
          rewrite (nth_0 (f x) (map f y));
          rewrite (nth_0 x y);
          reflexivity }
        { assume m hm heq;
          rewrite heq;
          rewrite (map_Cons f x y);
          rewrite (nth_Cons m (f x) (map f y) hm);
          rewrite (nth_Cons m x y hm);
          have hlt3 : π (lt (succ m) (succ (length y)))
            { refine ind_eq (eq_sym (length_Cons x y)) (λ w, lt (succ m) w)
                (ind_eq (eq_sym heq) (λ w, lt w (length (Cons x y))) hlt2) };
          refine hIH m hm (succ_leE m (length y) hlt3) } } };
  refine hmain n hn hlt
end;

opaque symbol nth_map_upt (m n i : τ ι) (f : τ ι → τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (i ∈ omega) → π (lt i (diff n m)) →
  π (nth i (map f (upt m n)) = f (add m i)) ≔
begin
  assume m n i f hm hn hi hlt;
  have hltadd : π (lt (add i m) n)
    { refine ∧ₑ₁ (less_diff_conv n m hn hm i hi) hlt };
  have hltadd2 : π (lt (add m i) n)
    { refine ind_eq (add_commute m i) (λ w, lt w n) hltadd };
  have hltlen : π (lt i (length (upt m n)))
    { refine ind_eq (length_upt m n hm hn) (λ w, lt i w) hlt };
  rewrite (nth_map (upt m n) omega i f (upt_type m n hn) hi hltlen);
  rewrite (nth_upt m n i hm hn hi hltadd2);
  reflexivity
end;

// ===========================================================================
// (** sublist (a generalization of nth to sets) **)
// ===========================================================================

opaque symbol sublist_0 (xs A : τ ι) : π (xs ∈ list A) → π (sublist xs empty = Nil) ≔
begin admit end;

opaque symbol sublist_Nil (A : τ ι) : π (sublist Nil A = Nil) ≔
begin admit end;

opaque symbol sublist_shift_lemma (xs B i A : τ ι) :
  π (xs ∈ list B) → π (i ∈ omega) →
  π (map fst (filter (λ p, snd p ∈ A) (zip xs (upt i (add i (length xs)))))
     = map fst (filter (λ p, snd p ∈ omega ∧ add (snd p) i ∈ A)
                        (zip xs (upt empty (length xs))))) ≔
begin admit end;

opaque symbol sublist_type (xs B A : τ ι) : π (xs ∈ list B) → π (sublist xs A ∈ list B) ≔
begin admit end;

opaque symbol upt_add_eq_append2 (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) →
  π (upt empty (add i j) = app (upt empty i) (upt i (add i j))) ≔
begin admit end;

opaque symbol sublist_append (xs B ys A : τ ι) :
  π (xs ∈ list B) → π (ys ∈ list B) →
  π (sublist (app xs ys) A
     = app (sublist xs A) (sublist ys (Collect omega (λ j, add j (length xs) ∈ A)))) ≔
begin admit end;

opaque symbol sublist_Cons (xs B x A : τ ι) :
  π (xs ∈ list B) → π (x ∈ B) →
  π (sublist (Cons x xs) A
     = app (If (empty ∈ A) (Cons x Nil) Nil) (sublist xs (Collect omega (λ j, succ j ∈ A)))) ≔
begin admit end;

opaque symbol sublist_singleton (x A : τ ι) :
  π (sublist (Cons x Nil) A = If (empty ∈ A) (Cons x Nil) Nil) ≔
begin admit end;

opaque symbol sublist_upt_eq_take (xs A n : τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) → π (sublist xs n = take n xs) ≔
begin admit end;

opaque symbol sublist_Int_eq (xs B A : τ ι) :
  π (xs ∈ list B) → π (sublist xs (Int A omega) = sublist xs A) ≔
begin admit end;

// ===========================================================================
// Repetition of a List Element
// ===========================================================================

// port-internal helpers — list_repeat's primrec equations
private opaque symbol repeat_0_h (a : τ ι) : π (list_repeat a empty = Nil) ≔
  nat_rec_0 Nil (λ n2 r, Cons a r);
private opaque symbol repeat_succ_h (a n : τ ι) :
  π (n ∈ omega) → π (list_repeat a (succ n) = Cons a (list_repeat a n)) ≔
  λ hn, nat_rec_succ n Nil (λ n2 r, Cons a r) hn;

opaque symbol length_repeat (a n : τ ι) : π (n ∈ omega) → π (length (list_repeat a n) = n) ≔
begin
  assume a n hn;
  refine nat_induct (λ w, length (list_repeat a w) = w) _ _ n hn
  { simplify rule off;
    rewrite (repeat_0_h a);
    refine length_Nil }
  { assume n2 hn2 hIH;
    rewrite (repeat_succ_h a n2 hn2);
    rewrite (length_Cons a (list_repeat a n2));
    rewrite hIH;
    reflexivity }
end;

opaque symbol repeat_succ_app (a n : τ ι) :
  π (n ∈ omega) → π (list_repeat a (succ n) = app (list_repeat a n) (Cons a Nil)) ≔
begin
  assume a n hn;
  have hcons : π (Ball omega
      (λ w, Cons a (list_repeat a w) = app (list_repeat a w) (Cons a Nil)))
    { refine nat_induct
        (λ w, Cons a (list_repeat a w) = app (list_repeat a w) (Cons a Nil)) _ _
      { simplify rule off;
        rewrite (repeat_0_h a);
        rewrite (app_Nil (Cons a Nil));
        reflexivity }
      { assume n2 hn2 hIH;
        rewrite (repeat_succ_h a n2 hn2);
        rewrite (app_Cons a (list_repeat a n2) (Cons a Nil));
        rewrite hIH;
        reflexivity } };
  rewrite (repeat_succ_h a n hn);
  refine hcons n hn
end;

opaque symbol repeat_type (a A n : τ ι) :
  π (a ∈ A) → π (n ∈ omega) → π (list_repeat a n ∈ list A) ≔
begin
  assume a A n ha hn;
  refine nat_induct (λ w, list_repeat a w ∈ list A) _ _ n hn
  { refine ind_eq (repeat_0_h a) (λ w, w ∈ list A) (list_0I A) }
  { assume n2 hn2 hIH;
    refine ind_eq (repeat_succ_h a n2 hn2) (λ w, w ∈ list A)
      (list_consI a (list_repeat a n2) A ha hIH) }
end;
