// ZF.QUniv — A Small Universe for Lazy Recursive Types
// Faithful port of isabelle-src/QUniv.thy: every definition is given and
// every lemma/theorem is proved (no admits).
// (Source: L. C. Paulson, ZF/QUniv.thy.)
//
// Note: Univ.lp does not yet port Pair_in_VLimit / sum_subset_univ /
// product_Int_Vfrom_subset, so the corresponding facts are derived inline
// here (see QPair_subset_univ and QPair_Int_Vfrom_succ_subset).
//
// The two `rep_datatype` blocks at the top of the .thy re-register the
// already-existing `sum`/`qsum` as datatypes (elimination = sumE/qsumE,
// already ported in Sum.lp/QPair.lp) — no new object-level content.

require open ZF.Univ ZF.QPair;

// ===========================================================================
// Definitions
// ===========================================================================

// quniv(A) ≡ Pow(univ(eclose(A)))
constant symbol quniv (A : τ ι) : τ ι;
constant symbol quniv_def (A : τ ι) :
  π (quniv A = Pow (univ (eclose A)));

// ===========================================================================
// Properties involving Transset and Sum
// ===========================================================================

opaque symbol Transset_includes_summands (C A B : τ ι) :
  π (Transset C) → π (sum A B ⊆ C) → π (A ⊆ C ∧ B ⊆ C) ≔
begin
  assume C A B hTC hsub;
  have hsub' : π (Un (Sigma (singleton empty) (λ _, A))
                     (Sigma (singleton one) (λ _, B)) ⊆ C)
    { refine ind_eq (eq_sym (sum_def A B)) (λ w, w ⊆ C) hsub };
  have hA : π (Sigma (singleton empty) (λ _, A) ⊆ C)
    { refine subset_trans (Sigma (singleton empty) (λ _, A))
        (Un (Sigma (singleton empty) (λ _, A)) (Sigma (singleton one) (λ _, B))) C
        (Un_upper1 (Sigma (singleton empty) (λ _, A)) (Sigma (singleton one) (λ _, B)))
        hsub' };
  have hB : π (Sigma (singleton one) (λ _, B) ⊆ C)
    { refine subset_trans (Sigma (singleton one) (λ _, B))
        (Un (Sigma (singleton empty) (λ _, A)) (Sigma (singleton one) (λ _, B))) C
        (Un_upper2 (Sigma (singleton empty) (λ _, A)) (Sigma (singleton one) (λ _, B)))
        hsub' };
  refine ∧ᵢ
    (Transset_includes_range C (singleton empty) A empty hTC hA (singletonI empty))
    (Transset_includes_range C (singleton one) B one hTC hB (singletonI one))
end;

opaque symbol Transset_sum_Int_subset (C A B : τ ι) :
  π (Transset C) → π (Int (sum A B) C ⊆ sum (Int A C) (Int B C)) ≔
begin
  assume C A B hTC z hz;
  have hzs : π (z ∈ sum A B) { refine IntD1 z (sum A B) C hz };
  have hzC : π (z ∈ C) { refine IntD2 z (sum A B) C hz };
  refine sumE z A B (z ∈ sum (Int A C) (Int B C)) hzs _ _
  { assume x hxA hzx;
    have hIC : π (Inl x ∈ C) { refine ind_eq (eq_sym hzx) (λ w, w ∈ C) hzC };
    have hPC : π (Pair empty x ∈ C)
      { refine ind_eq (eq_sym (Inl_def x)) (λ w, w ∈ C) hIC };
    have hxC : π (x ∈ C) { refine ∧ₑ₂ (Transset_Pair_D C empty x hTC hPC) };
    refine ind_eq hzx (λ w, w ∈ sum (Int A C) (Int B C))
      (InlI x (Int A C) (Int B C) (IntI x A C hxA hxC)) }
  { assume y hyB hzy;
    have hIC : π (Inr y ∈ C) { refine ind_eq (eq_sym hzy) (λ w, w ∈ C) hzC };
    have hPC : π (Pair one y ∈ C)
      { refine ind_eq (eq_sym (Inr_def y)) (λ w, w ∈ C) hIC };
    have hyC : π (y ∈ C) { refine ∧ₑ₂ (Transset_Pair_D C one y hTC hPC) };
    refine ind_eq hzy (λ w, w ∈ sum (Int A C) (Int B C))
      (InrI y (Int A C) (Int B C) (IntI y B C hyB hyC)) }
end;

// ===========================================================================
// Introduction and Elimination Rules
// ===========================================================================

opaque symbol qunivI (X A : τ ι) : π (X ⊆ univ (eclose A)) → π (X ∈ quniv A) ≔
begin
  assume X A h;
  rewrite quniv_def;
  refine PowI X (univ (eclose A)) h
end;

opaque symbol qunivD (X A : τ ι) : π (X ∈ quniv A) → π (X ⊆ univ (eclose A)) ≔
begin
  assume X A h;
  have h' : π (X ∈ Pow (univ (eclose A)))
    { refine ind_eq (eq_sym (quniv_def A)) (λ w, X ∈ w) h };
  refine PowD X (univ (eclose A)) h'
end;

opaque symbol quniv_mono (A B : τ ι) : π (A ⊆ B) → π (quniv A ⊆ quniv B) ≔
begin
  assume A B hAB;
  rewrite quniv_def; rewrite quniv_def;
  have hu : π (univ (eclose A) ⊆ univ (eclose B))
    { rewrite univ_def; rewrite univ_def;
      refine Vfrom_mono (eclose A) (eclose B) omega omega
        (eclose_mono A B hAB) (subset_refl omega) };
  refine Pow_mono (univ (eclose A)) (univ (eclose B)) hu
end;

// ===========================================================================
// Closure Properties
// ===========================================================================

opaque symbol univ_eclose_subset_quniv (A : τ ι) : π (univ (eclose A) ⊆ quniv A) ≔
begin
  assume A;
  rewrite quniv_def;
  have hT : π (Transset (univ (eclose A)))
    { rewrite univ_def;
      refine Transset_Vfrom (eclose A) omega (Transset_eclose A) };
  refine Transset_iff_Pow_fwd (univ (eclose A)) hT
end;

// Key property for proving A_subset_quniv; requires eclose in definition of quniv
opaque symbol univ_subset_quniv (A : τ ι) : π (univ A ⊆ quniv A) ≔
begin
  assume A;
  have hu : π (univ A ⊆ univ (eclose A))
    { rewrite univ_def; rewrite univ_def;
      refine Vfrom_mono A (eclose A) omega omega
        (arg_subset_eclose A) (subset_refl omega) };
  refine subset_trans (univ A) (univ (eclose A)) (quniv A) hu
    (univ_eclose_subset_quniv A)
end;

opaque symbol univ_into_quniv (a A : τ ι) : π (a ∈ univ A) → π (a ∈ quniv A) ≔
begin
  assume a A h;
  refine univ_subset_quniv A a h
end;

opaque symbol Pow_univ_subset_quniv (A : τ ι) : π (Pow (univ A) ⊆ quniv A) ≔
begin
  assume A;
  rewrite quniv_def;
  have hu : π (univ A ⊆ univ (eclose A))
    { rewrite univ_def; rewrite univ_def;
      refine Vfrom_mono A (eclose A) omega omega
        (arg_subset_eclose A) (subset_refl omega) };
  refine Pow_mono (univ A) (univ (eclose A)) hu
end;

opaque symbol univ_subset_into_quniv (A B : τ ι) : π (A ⊆ univ B) → π (A ∈ quniv B) ≔
begin
  assume A B h;
  refine Pow_univ_subset_quniv B A (PowI A (univ B) h)
end;

opaque symbol zero_in_quniv (A : τ ι) : π (empty ∈ quniv A) ≔
begin
  assume A;
  refine qunivI empty A (empty_subset (univ (eclose A)))
end;

opaque symbol one_in_quniv (A : τ ι) : π (one ∈ quniv A) ≔
begin
  assume A;
  have hno : π (omega ⊆ univ (eclose A))
    { rewrite univ_def; refine i_subset_Vfrom (eclose A) omega };
  have h1 : π (one ⊆ omega)
    { refine TranssetD omega one (Ord_is_Transset omega Ord_omega) nat_1I };
  refine qunivI one A (subset_trans one omega (univ (eclose A)) h1 hno)
end;

opaque symbol two_in_quniv (A : τ ι) : π (succ one ∈ quniv A) ≔
begin
  assume A;
  have hno : π (omega ⊆ univ (eclose A))
    { rewrite univ_def; refine i_subset_Vfrom (eclose A) omega };
  have h2 : π (succ one ⊆ omega)
    { refine TranssetD omega (succ one) (Ord_is_Transset omega Ord_omega) nat_2I };
  refine qunivI (succ one) A (subset_trans (succ one) omega (univ (eclose A)) h2 hno)
end;

opaque symbol A_subset_quniv (A : τ ι) : π (A ⊆ quniv A) ≔
begin
  assume A;
  have hAu : π (A ⊆ univ A)
    { rewrite univ_def; refine A_subset_Vfrom A omega };
  refine subset_trans A (univ A) (quniv A) hAu (univ_subset_quniv A)
end;

opaque symbol A_into_quniv (a A : τ ι) : π (a ∈ A) → π (a ∈ quniv A) ≔
begin
  assume a A h;
  refine A_subset_quniv A a h
end;

// *** univ(A) closure for Quine-inspired pairs and injections ***

// Quine ordered pairs
opaque symbol QPair_subset_univ (a b A : τ ι) :
  π (a ⊆ univ A) → π (b ⊆ univ A) → π (QPair a b ⊆ univ A) ≔
begin
  assume a b A ha hb;
  have ha' : π (a ⊆ Vfrom A omega)
    { refine ind_eq (eq_sym (univ_def A)) (λ w, a ⊆ w) ha };
  have hb' : π (b ⊆ Vfrom A omega)
    { refine ind_eq (eq_sym (univ_def A)) (λ w, b ⊆ w) hb };
  have hTom : π (Transset omega) { refine Ord_is_Transset omega Ord_omega };
  have homV : π (omega ⊆ Vfrom A omega) { refine i_subset_Vfrom A omega };
  // Local Pair_in_univ (Univ.thy's Pair_in_VLimit at i := ω):
  // members of Vfrom A ω live at finite levels; pairs climb two levels.
  have hPairV : Π (x y : τ ι), π (x ∈ Vfrom A omega) → π (y ∈ Vfrom A omega) →
                π (Pair x y ∈ Vfrom A omega)
    { assume x y hx hy;
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
      have hybex : π (Bex (RepFun omega (λ j, Vfrom A j)) (λ S, y ∈ S))
        { refine UnionE y (RepFun omega (λ j, Vfrom A j)) hyU };
      refine ∃ₑ hybex _; assume T hT;
      have hTbex : π (Bex omega (λ j, T = Vfrom A j))
        { refine ∧ₑ₁ (RepFun_iff T omega (λ j, Vfrom A j)) (∧ₑ₁ hT) };
      refine ∃ₑ hTbex _; assume j hj;
      have hyj : π (y ∈ Vfrom A j)
        { refine ind_eq (eq_sym (∧ₑ₂ hj)) (λ w, y ∈ w) (∧ₑ₂ hT) };
      // lift both to the common level i ∪ j ∈ ω
      have hk : π (Un i j ∈ omega) { refine Un_nat_type i j (∧ₑ₁ hi) (∧ₑ₁ hj) };
      have hxk : π (x ∈ Vfrom A (Un i j))
        { refine Vfrom_mono A A i (Un i j) (subset_refl A) (Un_upper1 i j) x hxi };
      have hyk : π (y ∈ Vfrom A (Un i j))
        { refine Vfrom_mono A A j (Un i j) (subset_refl A) (Un_upper2 i j) y hyj };
      // {x} and {x,y} ∈ Pow(Vfrom A (i∪j)) ⊆ Vfrom A (succ (i∪j))
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
      // Pair x y = {{x},{x,y}} ⊆ Vfrom A (succ (i∪j)), so it lands two up
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
      refine hVsub (Pair x y) hpair_mem };
  // main goal: <a;b> = a+b = Σ{0}a ∪ Σ{1}b ⊆ univ A
  rewrite QPair_def; rewrite sum_def; rewrite univ_def;
  have h0V : π (empty ∈ Vfrom A omega) { refine homV empty zero_in_omega };
  have h1V : π (one ∈ Vfrom A omega) { refine homV one nat_1I };
  refine Un_least (Sigma (singleton empty) (λ _, a))
    (Sigma (singleton one) (λ _, b)) (Vfrom A omega) _ _
  { assume p hp;
    have hbex : π (Bex (singleton empty) (λ x, Bex a (λ y, p = Pair x y)))
      { refine SigmaE p (singleton empty) (λ _, a) hp };
    refine ∃ₑ hbex _; assume x hx;
    refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
    have hxV : π (x ∈ Vfrom A omega)
      { refine ind_eq (singletonE x empty (∧ₑ₁ hx)) (λ w, w ∈ Vfrom A omega) h0V };
    refine ind_eq (∧ₑ₂ hy) (λ w, w ∈ Vfrom A omega)
      (hPairV x y hxV (ha' y (∧ₑ₁ hy))) }
  { assume p hp;
    have hbex : π (Bex (singleton one) (λ x, Bex b (λ y, p = Pair x y)))
      { refine SigmaE p (singleton one) (λ _, b) hp };
    refine ∃ₑ hbex _; assume x hx;
    refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
    have hxV : π (x ∈ Vfrom A omega)
      { refine ind_eq (singletonE x one (∧ₑ₁ hx)) (λ w, w ∈ Vfrom A omega) h1V };
    refine ind_eq (∧ₑ₂ hy) (λ w, w ∈ Vfrom A omega)
      (hPairV x y hxV (hb' y (∧ₑ₁ hy))) }
end;

// ===========================================================================
// Quine Disjoint Sum
// ===========================================================================

opaque symbol QInl_subset_univ (a A : τ ι) : π (a ⊆ univ A) → π (QInl a ⊆ univ A) ≔
begin
  assume a A h;
  rewrite QInl_def;
  refine QPair_subset_univ empty a A (empty_subset (univ A)) h
end;

opaque symbol naturals_subset_nat (n : τ ι) : π (n ∈ omega) → π (n ⊆ omega) ≔
begin
  assume n h;
  refine TranssetD omega n (Ord_is_Transset omega Ord_omega) h
end;

opaque symbol naturals_subset_univ (n A : τ ι) : π (n ∈ omega) → π (n ⊆ univ A) ≔
begin
  assume n A h;
  have hno : π (omega ⊆ univ A)
    { rewrite univ_def; refine i_subset_Vfrom A omega };
  refine subset_trans n omega (univ A) (naturals_subset_nat n h) hno
end;

opaque symbol QInr_subset_univ (a A : τ ι) : π (a ⊆ univ A) → π (QInr a ⊆ univ A) ≔
begin
  assume a A h;
  rewrite QInr_def;
  refine QPair_subset_univ one a A (naturals_subset_univ one A nat_1I) h
end;

// ===========================================================================
// Closure for Quine-Inspired Products and Sums
// ===========================================================================

// Quine ordered pairs
opaque symbol QPair_in_quniv (a b A : τ ι) :
  π (a ∈ quniv A) → π (b ∈ quniv A) → π (QPair a b ∈ quniv A) ≔
begin
  assume a b A ha hb;
  refine qunivI (QPair a b) A
    (QPair_subset_univ a b (eclose A) (qunivD a A ha) (qunivD b A hb))
end;

opaque symbol QSigma_quniv (A : τ ι) : π (qprod (quniv A) (quniv A) ⊆ quniv A) ≔
begin
  assume A p hp;
  refine QSigmaE p (quniv A) (λ _, quniv A) (p ∈ quniv A) hp _;
  assume x y hx hy hpeq;
  refine ind_eq hpeq (λ w, w ∈ quniv A) (QPair_in_quniv x y A hx hy)
end;

opaque symbol QSigma_subset_quniv (A Z : τ ι) (B : τ ι → τ ι) :
  π (A ⊆ quniv Z) → π (Ball A (λ x, B x ⊆ quniv Z)) → π (QSigma A B ⊆ quniv Z) ≔
begin
  assume A Z B hA hB;
  refine subset_trans (QSigma A B) (qprod (quniv Z) (quniv Z)) (quniv Z)
    (QSigma_mono A (quniv Z) B (λ _, quniv Z) hA hB) (QSigma_quniv Z)
end;

// The opposite inclusion
opaque symbol quniv_QPair_D (a b A : τ ι) :
  π (QPair a b ∈ quniv A) → π (a ∈ quniv A ∧ b ∈ quniv A) ≔
begin
  assume a b A h;
  have hsub : π (QPair a b ⊆ univ (eclose A)) { refine qunivD (QPair a b) A h };
  have hsum : π (sum a b ⊆ univ (eclose A))
    { refine ind_eq (eq_sym (QPair_def a b)) (λ w, w ⊆ univ (eclose A)) hsub };
  have hT : π (Transset (univ (eclose A)))
    { rewrite univ_def; refine Transset_Vfrom (eclose A) omega (Transset_eclose A) };
  have hab : π (a ⊆ univ (eclose A) ∧ b ⊆ univ (eclose A))
    { refine Transset_includes_summands (univ (eclose A)) a b hT hsum };
  refine ∧ᵢ (qunivI a A (∧ₑ₁ hab)) (qunivI b A (∧ₑ₂ hab))
end;

opaque symbol quniv_QPair_E (a b A : τ ι) (P : Prop) :
  π (QPair a b ∈ quniv A) → (π (a ∈ quniv A) → π (b ∈ quniv A) → π P) → π P ≔
begin
  assume a b A P h hk;
  have hD : π (a ∈ quniv A ∧ b ∈ quniv A) { refine quniv_QPair_D a b A h };
  refine hk (∧ₑ₁ hD) (∧ₑ₂ hD)
end;

opaque symbol quniv_QPair_iff (a b A : τ ι) :
  π (QPair a b ∈ quniv A ⇔ (a ∈ quniv A ∧ b ∈ quniv A)) ≔
begin
  assume a b A;
  refine ∧ᵢ _ _
  { assume h; refine quniv_QPair_D a b A h }
  { assume h; refine QPair_in_quniv a b A (∧ₑ₁ h) (∧ₑ₂ h) }
end;

// ===========================================================================
// Quine Disjoint Sum
// ===========================================================================

opaque symbol QInl_in_quniv (a A : τ ι) : π (a ∈ quniv A) → π (QInl a ∈ quniv A) ≔
begin
  assume a A h;
  rewrite QInl_def;
  refine QPair_in_quniv empty a A (zero_in_quniv A) h
end;

opaque symbol QInr_in_quniv (b A : τ ι) : π (b ∈ quniv A) → π (QInr b ∈ quniv A) ≔
begin
  assume b A h;
  rewrite QInr_def;
  refine QPair_in_quniv one b A (one_in_quniv A) h
end;

opaque symbol qsum_quniv (C : τ ι) : π (qsum (quniv C) (quniv C) ⊆ quniv C) ≔
begin
  assume C u hu;
  refine qsumE u (quniv C) (quniv C) (u ∈ quniv C) hu _ _
  { assume x hx hueq;
    refine ind_eq hueq (λ w, w ∈ quniv C) (QInl_in_quniv x C hx) }
  { assume y hy hueq;
    refine ind_eq hueq (λ w, w ∈ quniv C) (QInr_in_quniv y C hy) }
end;

opaque symbol qsum_subset_quniv (A B Z : τ ι) :
  π (A ⊆ quniv Z) → π (B ⊆ quniv Z) → π (qsum A B ⊆ quniv Z) ≔
begin
  assume A B Z hA hB;
  refine subset_trans (qsum A B) (qsum (quniv Z) (quniv Z)) (quniv Z)
    (qsum_mono A B (quniv Z) (quniv Z) hA hB) (qsum_quniv Z)
end;

// ===========================================================================
// The Natural Numbers
// ===========================================================================

opaque symbol nat_subset_quniv (A : τ ι) : π (omega ⊆ quniv A) ≔
begin
  assume A;
  have hno : π (omega ⊆ univ A)
    { rewrite univ_def; refine i_subset_Vfrom A omega };
  refine subset_trans omega (univ A) (quniv A) hno (univ_subset_quniv A)
end;

opaque symbol nat_into_quniv (n A : τ ι) : π (n ∈ omega) → π (n ∈ quniv A) ≔
begin
  assume n A h;
  refine nat_subset_quniv A n h
end;

opaque symbol bool_subset_quniv (A : τ ι) : π (bool_set ⊆ quniv A) ≔
begin
  assume A;
  refine subset_trans bool_set omega (quniv A) bool_subset_nat (nat_subset_quniv A)
end;

opaque symbol bool_into_quniv (b A : τ ι) : π (b ∈ bool_set) → π (b ∈ quniv A) ≔
begin
  assume b A h;
  refine bool_subset_quniv A b h
end;

// ===========================================================================
// Intersecting <a;b> with Vfrom...
// ===========================================================================

opaque symbol QPair_Int_Vfrom_succ_subset (X a b i : τ ι) :
  π (Transset X) →
  π (Int (QPair a b) (Vfrom X (succ i)) ⊆ QPair (Int a (Vfrom X i)) (Int b (Vfrom X i))) ≔
begin
  assume X a b i hTX;
  rewrite QPair_def; rewrite QPair_def;
  have hTV : π (Transset (Vfrom X i)) { refine Transset_Vfrom X i hTX };
  have hVs : π (Vfrom X (succ i) = Un X (Pow (Vfrom X i))) { refine Vfrom_succ X i };
  have hXV : π (X ⊆ Vfrom X i) { refine A_subset_Vfrom X i };
  // members of Vfrom X (succ i) are subsets of Vfrom X i (Transset X)
  have hlev : Π (z : τ ι), π (z ∈ Vfrom X (succ i)) → π (z ⊆ Vfrom X i)
    { assume z hz;
      have hz' : π (z ∈ Un X (Pow (Vfrom X i)))
        { refine ind_eq (eq_sym hVs) (λ w, z ∈ w) hz };
      refine ∨ₑ (UnE z X (Pow (Vfrom X i)) hz') _ _
      { assume hzX;
        refine subset_trans z X (Vfrom X i) (TranssetD X z hTX hzX) hXV }
      { assume hzP; refine PowD z (Vfrom X i) hzP } };
  // Pair u v ⊆ Vfrom X i forces u, v ∈ Vfrom X i (Transset (Vfrom X i))
  have hmem : Π (u v : τ ι), π (Pair u v ⊆ Vfrom X i) →
              π (u ∈ Vfrom X i ∧ v ∈ Vfrom X i)
    { assume u v hsub;
      have hupair : π (Upair (singleton u) (Upair u v) ⊆ Vfrom X i)
        { refine ind_eq (eq_sym (Pair_def u v)) (λ w, w ⊆ Vfrom X i) hsub };
      have huv : π (Upair u v ∈ Vfrom X i)
        { refine hupair (Upair u v) (UpairI2 (singleton u) (Upair u v)) };
      have huvsub : π (Upair u v ⊆ Vfrom X i)
        { refine TranssetD (Vfrom X i) (Upair u v) hTV huv };
      refine ∧ᵢ (huvsub u (UpairI1 u v)) (huvsub v (UpairI2 u v)) };
  assume z hz;
  have hzs : π (z ∈ sum a b) { refine IntD1 z (sum a b) (Vfrom X (succ i)) hz };
  have hzV : π (z ∈ Vfrom X (succ i)) { refine IntD2 z (sum a b) (Vfrom X (succ i)) hz };
  have hzsub : π (z ⊆ Vfrom X i) { refine hlev z hzV };
  refine sumE z a b (z ∈ sum (Int a (Vfrom X i)) (Int b (Vfrom X i))) hzs _ _
  { assume x hxa hzx;
    have hpsub : π (Pair empty x ⊆ Vfrom X i)
      { refine ind_eq (eq_sym (Inl_def x)) (λ w, w ⊆ Vfrom X i)
          (ind_eq (eq_sym hzx) (λ w, w ⊆ Vfrom X i) hzsub) };
    have hxV : π (x ∈ Vfrom X i) { refine ∧ₑ₂ (hmem empty x hpsub) };
    refine ind_eq hzx (λ w, w ∈ sum (Int a (Vfrom X i)) (Int b (Vfrom X i)))
      (InlI x (Int a (Vfrom X i)) (Int b (Vfrom X i)) (IntI x a (Vfrom X i) hxa hxV)) }
  { assume y hyb hzy;
    have hpsub : π (Pair one y ⊆ Vfrom X i)
      { refine ind_eq (eq_sym (Inr_def y)) (λ w, w ⊆ Vfrom X i)
          (ind_eq (eq_sym hzy) (λ w, w ⊆ Vfrom X i) hzsub) };
    have hyV : π (y ∈ Vfrom X i) { refine ∧ₑ₂ (hmem one y hpsub) };
    refine ind_eq hzy (λ w, w ∈ sum (Int a (Vfrom X i)) (Int b (Vfrom X i)))
      (InrI y (Int a (Vfrom X i)) (Int b (Vfrom X i)) (IntI y b (Vfrom X i) hyb hyV)) }
end;

// ===========================================================================
// "Take-Lemma" Rules
// ===========================================================================

// for proving a=b by coinduction and c: quniv(A)

// Rule for level i -- preserving the level, not decreasing it
opaque symbol QPair_Int_Vfrom_subset (X a b i : τ ι) :
  π (Transset X) →
  π (Int (QPair a b) (Vfrom X i) ⊆ QPair (Int a (Vfrom X i)) (Int b (Vfrom X i))) ≔
begin
  assume X a b i hTX;
  rewrite QPair_def; rewrite QPair_def;
  refine Transset_sum_Int_subset (Vfrom X i) a b (Transset_Vfrom X i hTX)
end;

// a ∩ Vset(i) ⊆ c → b ∩ Vset(i) ⊆ d → <a;b> ∩ Vset(i) ⊆ <c;d>
opaque symbol QPair_Int_Vset_subset_trans (a b i c d : τ ι) :
  π (Int a (Vset i) ⊆ c) → π (Int b (Vset i) ⊆ d) →
  π (Int (QPair a b) (Vset i) ⊆ QPair c d) ≔
begin
  assume a b i c d hac hbd;
  refine subset_trans (Int (QPair a b) (Vset i))
    (QPair (Int a (Vset i)) (Int b (Vset i))) (QPair c d)
    (QPair_Int_Vfrom_subset empty a b i Transset_0)
    (QPair_mono (Int a (Vset i)) (Int b (Vset i)) c d hac hbd)
end;

opaque symbol QPair_Int_Vset_subset_UN (i a b : τ ι) :
  π (Ord i) →
  π (Int (QPair a b) (Vset i) ⊆
     Union (RepFun i (λ j, QPair (Int a (Vset j)) (Int b (Vset j))))) ≔
begin
  assume i a b hOi;
  refine Ord_cases i (Int (QPair a b) (Vset i) ⊆
      Union (RepFun i (λ j, QPair (Int a (Vset j)) (Int b (Vset j))))) hOi _ _ _
  { // i = 0: Vset 0 = 0, so the intersection is empty
    assume h0 z hz;
    have hzV : π (z ∈ Vset i) { refine IntD2 z (QPair a b) (Vset i) hz };
    have hzV0 : π (z ∈ Vset empty)
      { refine ind_eq (eq_sym h0) (λ w, z ∈ Vset w) hzV };
    have hz0 : π (z ∈ empty) { refine ind_eq (eq_sym Vset_0) (λ w, z ∈ w) hzV0 };
    refine ⊥ₑ (emptyE z hz0) }
  { // i = succ j: decrease the level with QPair_Int_Vfrom_succ_subset
    assume hbex;
    refine ∃ₑ hbex _; assume j hj;
    have hji : π (j ∈ i) { refine ∧ₑ₁ hj };
    have hisucc : π (i = succ j) { refine ∧ₑ₂ (∧ₑ₂ hj) };
    have hmain : π (Int (QPair a b) (Vset (succ j)) ⊆
        Union (RepFun i (λ k, QPair (Int a (Vset k)) (Int b (Vset k)))))
      { refine subset_trans (Int (QPair a b) (Vset (succ j)))
          (QPair (Int a (Vset j)) (Int b (Vset j)))
          (Union (RepFun i (λ k, QPair (Int a (Vset k)) (Int b (Vset k)))))
          (QPair_Int_Vfrom_succ_subset empty a b j Transset_0)
          (UN_upper j i (λ k, QPair (Int a (Vset k)) (Int b (Vset k))) hji) };
    refine ind_eq hisucc (λ w, Int (QPair a b) (Vset w) ⊆
        Union (RepFun i (λ k, QPair (Int a (Vset k)) (Int b (Vset k))))) hmain }
  { // Limit i: every z ∈ Vset i already lives in some Vset j, j ∈ i
    assume hLim z hz;
    have hzQ : π (z ∈ QPair a b) { refine IntD1 z (QPair a b) (Vset i) hz };
    have hzV : π (z ∈ Vset i) { refine IntD2 z (QPair a b) (Vset i) hz };
    have hVeq : π (Vset i = Union (RepFun i (λ j, Vset j)))
      { refine Limit_Vset_eq i hLim };
    have hzU : π (z ∈ Union (RepFun i (λ j, Vset j)))
      { refine ind_eq (eq_sym hVeq) (λ w, z ∈ w) hzV };
    have hbexz : π (Bex (RepFun i (λ j, Vset j)) (λ S, z ∈ S))
      { refine UnionE z (RepFun i (λ j, Vset j)) hzU };
    refine ∃ₑ hbexz _; assume S hS;
    have hbexj : π (Bex i (λ j, S = Vset j))
      { refine ∧ₑ₁ (RepFun_iff S i (λ j, Vset j)) (∧ₑ₁ hS) };
    refine ∃ₑ hbexj _; assume j hj;
    have hzVj : π (z ∈ Vset j)
      { refine ind_eq (eq_sym (∧ₑ₂ hj)) (λ w, z ∈ w) (∧ₑ₂ hS) };
    have hsub : π (Int (QPair a b) (Vset j) ⊆ QPair (Int a (Vset j)) (Int b (Vset j)))
      { refine QPair_Int_Vfrom_subset empty a b j Transset_0 };
    refine UnionI z (QPair (Int a (Vset j)) (Int b (Vset j)))
      (RepFun i (λ k, QPair (Int a (Vset k)) (Int b (Vset k))))
      (hsub z (IntI z (QPair a b) (Vset j) hzQ hzVj))
      (RepFunI j i (λ k, QPair (Int a (Vset k)) (Int b (Vset k))) (∧ₑ₁ hj)) }
end;
