// ZF.OrderType — Order Types and Ordinal Arithmetic
// Faithful SKELETON port of isabelle-src/OrderType.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/OrderType.thy.)

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum ZF.Ordinal ZF.OrdQuant ZF.Nat_ZF ZF.Order ZF.OrderArith;

// ===========================================================================
// Lt — defined in Isabelle's Nat.thy (Lt ≡ {⟨x,y⟩ ∈ nat*nat. x<y}) but ABSENT
// from this port's Nat_ZF.lp.  Added here (faithfully, with nat = omega) so the
// *_Lt lemmas at the end of OrderType have a referent.
// ===========================================================================
symbol Lt : τ ι ≔ Collect (Sigma omega (λ _, omega)) (λ z, lt (fst z) (snd z));

// ===========================================================================
// Definitions
// ===========================================================================

constant symbol ordermap (A r : τ ι) : τ ι;
constant symbol ordermap_def (A r : τ ι) :
  π (ordermap A r =
     Lambda A (λ x, wfrec (Int r (Sigma A (λ _, A))) x (λ x2 f, Image f (pred A x2 r))));

constant symbol ordertype (A r : τ ι) : τ ι;
constant symbol ordertype_def (A r : τ ι) :
  π (ordertype A r = Image (ordermap A r) A);

constant symbol Ord_alt (X : τ ι) : Prop;
constant symbol Ord_alt_def (X : τ ι) :
  π (Ord_alt X =
     (well_ord X (Memrel X) ∧ Ball X (λ u, u = pred X u (Memrel X))));

constant symbol ordify (x : τ ι) : τ ι;
constant symbol ordify_def (x : τ ι) :
  π (ordify x = If (Ord x) x empty);

constant symbol omult (i j : τ ι) : τ ι;
constant symbol omult_def (i j : τ ι) :
  π (omult i j = ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)));

constant symbol raw_oadd (i j : τ ι) : τ ι;
constant symbol raw_oadd_def (i j : τ ι) :
  π (raw_oadd i j = ordertype (sum i j) (radd i (Memrel i) j (Memrel j)));

constant symbol oadd (i j : τ ι) : τ ι;
constant symbol oadd_def (i j : τ ι) :
  π (oadd i j = raw_oadd (ordify i) (ordify j));

constant symbol odiff (i j : τ ι) : τ ι;
constant symbol odiff_def (i j : τ ι) :
  π (odiff i j = ordertype (Diff i j) (Memrel i));

// ===========================================================================
// Proofs needing the combination of Ordinal.thy and Order.thy
// ===========================================================================

opaque symbol le_well_ord_Memrel (j i : τ ι) :
  π (le j i) → π (well_ord j (Memrel i)) ≔
begin
  assume j i hle;
  have hOj : π (Ord j) { refine lt_Ord j (succ i) hle };
  have hsub : π (j ⊆ i) { refine le_imp_subset j i hle };
  refine well_ordI j (Memrel i) _ _
  { refine wf_imp_wf_on j (Memrel i) (wf_Memrel i) }
  { refine linearI j (Memrel i) _;
    assume x hx y hy;
    have hOx : π (Ord x) { refine Ord_in_Ord j x hOj hx };
    have hOy : π (Ord y) { refine Ord_in_Ord j y hOj hy };
    refine ∨ₑ (Ord_linear x y hOx hOy) _ _
    { assume h; refine ∨ᵢ₁ (MemrelI x y i h (hsub x hx) (hsub y hy)) }
    { assume h; refine ∨ₑ h _ _
      { assume he; refine ∨ᵢ₂ (∨ᵢ₁ he) }
      { assume h2;
        refine ∨ᵢ₂ (∨ᵢ₂ (MemrelI y x i h2 (hsub y hy) (hsub x hx))) } } }
end;

// well_ord_Memrel = le_refl [THEN le_well_ord_Memrel] : Ord(i) ⟹ well_ord(i, Memrel(i))
opaque symbol well_ord_Memrel (i : τ ι) :
  π (Ord i) → π (well_ord i (Memrel i)) ≔
begin
  assume i hOi;
  refine le_well_ord_Memrel i i (le_refl i hOi)
end;

opaque symbol lt_pred_Memrel (j i : τ ι) :
  π (lt j i) → π (pred i j (Memrel i) = j) ≔
begin
  assume j i hlt;
  have hOi : π (Ord i) { refine lt_Ord2 j i hlt };
  have hji : π (j ∈ i) { refine ltD j i hlt };
  have hsub : π (j ⊆ i) { refine OrdmemD i j hji hOi };
  refine equality_iffI (pred i j (Memrel i)) j _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hmem : π (Pair x j ∈ Memrel i)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff x i j (Memrel i)) hx) };
    refine ∧ₑ₂ (∧ₑ₂ (MemrelE x j i hmem)) }
  { assume hx;
    refine predI x i j (Memrel i)
      (MemrelI x j i hx (hsub x hx) hji) (hsub x hx) }
end;

opaque symbol pred_Memrel (x A : τ ι) :
  π (x ∈ A) → π (pred A x (Memrel A) = Int A x) ≔
begin
  assume x A hxA;
  refine equality_iffI (pred A x (Memrel A)) (Int A x) _;
  assume y;
  apply ∧ᵢ
  { assume hy;
    have hmem : π (Pair y x ∈ Memrel A)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff y A x (Memrel A)) hy) };
    have h3 : π (y ∈ A ∧ x ∈ A ∧ y ∈ x) { refine MemrelE y x A hmem };
    refine IntI y A x (∧ₑ₁ h3) (∧ₑ₂ (∧ₑ₂ h3)) }
  { assume hy;
    have hyA : π (y ∈ A) { refine IntD1 y A x hy };
    have hyx : π (y ∈ x) { refine IntD2 y A x hy };
    refine predI y A x (Memrel A) (MemrelI y x A hyx hyA hxA) hyA }
end;

opaque symbol Ord_iso_implies_eq_lemma (j i f : τ ι) (R : Prop) :
  π (lt j i) → π (f ∈ ord_iso i (Memrel i) j (Memrel j)) → π R ≔
begin
  assume j i f R hlt hf;
  have hOi : π (Ord i) { refine lt_Ord2 j i hlt };
  have hji : π (j ∈ i) { refine ltD j i hlt };
  have hjsub : π (j ⊆ i) { refine OrdmemD i j hji hOi };
  have hpred : π (pred i j (Memrel i) = j) { refine lt_pred_Memrel j i hlt };
  have hbij : π (f ∈ bij i j)
    { refine ord_iso_is_bij f i (Memrel i) j (Memrel j) hf };
  have hfun : π (f ∈ Pi i (λ _, j)) { refine bij_is_fun f i j hbij };
  have hcond : π (Ball i (λ x, Ball i (λ y,
      (Pair x y ∈ Memrel i) ⇔ (Pair (fapply f x) (fapply f y) ∈ Memrel j))))
    { refine ord_iso_memD f i (Memrel i) j (Memrel j) hf };
  // Convert the target relation Memrel(j) to Memrel(i): on elements of j ⊆ i
  // the two membership relations agree.
  have hf2 : π (f ∈ ord_iso i (Memrel i) j (Memrel i))
    { rewrite ord_iso_def;
      refine CollectI f (bij i j) (λ g, Ball i (λ x, Ball i (λ y,
        (Pair x y ∈ Memrel i) ⇔ (Pair (fapply g x) (fapply g y) ∈ Memrel i)))) hbij _;
      assume x hx y hy;
      have hiff : π ((Pair x y ∈ Memrel i)
                     ⇔ (Pair (fapply f x) (fapply f y) ∈ Memrel j))
        { refine hcond x hx y hy };
      have hfx : π (fapply f x ∈ j) { refine fapply_type f x i (λ _, j) hfun hx };
      have hfy : π (fapply f y ∈ j) { refine fapply_type f y i (λ _, j) hfun hy };
      apply ∧ᵢ
      { assume hr;
        have h3 : π (fapply f x ∈ j ∧ fapply f y ∈ j ∧ fapply f x ∈ fapply f y)
          { refine MemrelE (fapply f x) (fapply f y) j (∧ₑ₁ hiff hr) };
        refine MemrelI (fapply f x) (fapply f y) i (∧ₑ₂ (∧ₑ₂ h3))
          (hjsub (fapply f x) hfx) (hjsub (fapply f y) hfy) }
      { assume hr;
        have h3 : π (fapply f x ∈ i ∧ fapply f y ∈ i ∧ fapply f x ∈ fapply f y)
          { refine MemrelE (fapply f x) (fapply f y) i hr };
        refine ∧ₑ₂ hiff
          (MemrelI (fapply f x) (fapply f y) j (∧ₑ₂ (∧ₑ₂ h3)) hfx hfy) } };
  have hf3 : π (f ∈ ord_iso i (Memrel i) (pred i j (Memrel i)) (Memrel i))
    { refine ind_eq hpred (λ w, f ∈ ord_iso i (Memrel i) w (Memrel i)) hf2 };
  refine ⊥ₑ (well_ord_iso_predE i (Memrel i) f j (well_ord_Memrel i hOi) hf3 hji)
end;

opaque symbol Ord_iso_implies_eq (i j f : τ ι) :
  π (Ord i) → π (Ord j) → π (f ∈ ord_iso i (Memrel i) j (Memrel j)) →
  π (i = j) ≔
begin
  assume i j f hOi hOj hf;
  refine ∨ₑ (Ord_linear i j hOi hOj) _ _
  { assume hij;
    refine Ord_iso_implies_eq_lemma i j (converse f) (i = j)
      (ltI i j hij hOj) (ord_iso_sym f i (Memrel i) j (Memrel j) hf) }
  { assume h;
    refine ∨ₑ h _ _
    { assume he; refine he }
    { assume hji;
      refine Ord_iso_implies_eq_lemma j i f (i = j) (ltI j i hji hOi) hf } }
end;

// ===========================================================================
// Ordermap and ordertype
// ===========================================================================

// Private abbreviation for the wfrec body of ordermap: ordermap A r is
// definitionally Lambda A (ombody A r).
private symbol ombody (A r y : τ ι) : τ ι ≔
  wfrec (Int r (Sigma A (λ _, A))) y (λ x2 f, Image f (pred A x2 r));

// The vimage of {x} under r ∩ A×A is exactly pred(A,x,r), for x ∈ A.
private opaque symbol pred_eq_vimage (A r x : τ ι) :
  π (x ∈ A) →
  π (vimage_singleton (Int r (Sigma A (λ _, A))) x = pred A x r) ≔
begin
  assume A r x hxA;
  refine equality_iffI (vimage_singleton (Int r (Sigma A (λ _, A))) x)
    (pred A x r) _;
  assume y;
  apply ∧ᵢ
  { assume hy;
    have hR : π (Pair y x ∈ Int r (Sigma A (λ _, A)))
      { refine vimage_singletonD y x (Int r (Sigma A (λ _, A))) hy };
    have hSig : π (Pair y x ∈ Sigma A (λ _, A))
      { refine IntD2 (Pair y x) r (Sigma A (λ _, A)) hR };
    have hyA : π (y ∈ A)
      { refine ind_eq (eq_sym (fst_conv y x)) (λ w, w ∈ A)
          (SigmaD1 (Pair y x) A (λ _, A) hSig) };
    refine predI y A x r      (IntD1 (Pair y x) r (Sigma A (λ _, A)) hR) hyA
 }
  { assume hy;
    have hyA : π (y ∈ A) { refine pred_subset A x r y hy };
    have hyr : π (Pair y x ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff y A x r) hy) };
    refine vimage_singletonI y x (Int r (Sigma A (λ _, A)))
      (IntI (Pair y x) r (Sigma A (λ _, A)) hyr
        (SigmaI y x A (λ _, A) hyA hxA)) }
end;

// Int (pred A x r) (domain (ordermap A r)) = pred A x r  (pred ⊆ A ⊆ domain).
private opaque symbol Int_pred_domain (A r x : τ ι) :
  π (Int (pred A x r) (domain (Lambda A (ombody A r))) = pred A x r) ≔
begin
  assume A r x;
  refine subset_antisym (Int (pred A x r) (domain (Lambda A (ombody A r))))
    (pred A x r) _ _
  { assume w hw;
    refine IntD1 w (pred A x r) (domain (Lambda A (ombody A r))) hw }
  { assume w hw;
    refine IntI w (pred A x r) (domain (Lambda A (ombody A r))) hw
      (Lambda_domain_subset A (ombody A r) w (pred_subset A x r w hw)) }
end;

opaque symbol ordermap_eq_image (A r x : τ ι) :
  π (wf A r) → π (x ∈ A) →
  π (fapply (ordermap A r) x = Image (ordermap A r) (pred A x r)) ≔
begin
  assume A r x hwf hx;
  have hbeta : π (fapply (ordermap A r) x = ombody A r x)
    { rewrite ordermap_def; refine beta A (ombody A r) x hx };
  have hunf : π (ombody A r x
      = Image (Lambda (vimage_singleton (Int r (Sigma A (λ _, A))) x)
               (ombody A r))
              (pred A x r))
    { refine wfrec_eq (Int r (Sigma A (λ _, A))) x
        (λ x2 f, Image f (pred A x2 r)) (wf_on_imp_wf_Int A r hwf) };
  have hdom : π (vimage_singleton (Int r (Sigma A (λ _, A))) x = pred A x r)
    { refine pred_eq_vimage A r x hx };
  have hunf2 : π (fapply (ordermap A r) x
      = Image (Lambda (pred A x r) (ombody A r)) (pred A x r))
    { refine ind_eq (eq_sym hdom)
        (λ w, fapply (ordermap A r) x
              = Image (Lambda w (ombody A r)) (pred A x r))
        (eq_trans hbeta hunf) };
  refine eq_trans hunf2 _;
  // Image over the restricted Lambda equals Image over ordermap itself:
  // both RepFun the same set with the same values.
  rewrite ordermap_def;
  refine equality_iffI
    (Image (Lambda (pred A x r) (ombody A r)) (pred A x r))
    (Image (Lambda A (ombody A r)) (pred A x r)) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    have hbex : π (Bex (Int (pred A x r)
                         (domain (Lambda (pred A x r) (ombody A r))))
                    (λ w, z = fapply (Lambda (pred A x r) (ombody A r)) w))
      { refine ∧ₑ₁ (Image_iff z (Lambda (pred A x r) (ombody A r)) (pred A x r)) hz };
    refine ∃ₑ hbex _; assume w hw;
    have hwp : π (w ∈ pred A x r)
      { refine IntD1 w (pred A x r)
          (domain (Lambda (pred A x r) (ombody A r))) (∧ₑ₁ hw) };
    have hwA : π (w ∈ A) { refine pred_subset A x r w hwp };
    have hzeq : π (z = fapply (Lambda A (ombody A r)) w)
      { refine eq_trans (∧ₑ₂ hw)
          (eq_trans (beta (pred A x r) (ombody A r) w hwp)
                    (eq_sym (beta A (ombody A r) w hwA))) };
    refine ∧ₑ₂ (Image_iff z (Lambda A (ombody A r)) (pred A x r)) _;
    refine ∃ᵢ w (∧ᵢ (IntI w (pred A x r) (domain (Lambda A (ombody A r))) hwp
      (Lambda_domain_subset A (ombody A r) w hwA)) hzeq) }
  { assume hz;
    have hbex : π (Bex (Int (pred A x r) (domain (Lambda A (ombody A r))))
                    (λ w, z = fapply (Lambda A (ombody A r)) w))
      { refine ∧ₑ₁ (Image_iff z (Lambda A (ombody A r)) (pred A x r)) hz };
    refine ∃ₑ hbex _; assume w hw;
    have hwp : π (w ∈ pred A x r)
      { refine IntD1 w (pred A x r) (domain (Lambda A (ombody A r))) (∧ₑ₁ hw) };
    have hwA : π (w ∈ A) { refine pred_subset A x r w hwp };
    have hzeq : π (z = fapply (Lambda (pred A x r) (ombody A r)) w)
      { refine eq_trans (∧ₑ₂ hw)
          (eq_trans (beta A (ombody A r) w hwA)
                    (eq_sym (beta (pred A x r) (ombody A r) w hwp))) };
    refine ∧ₑ₂ (Image_iff z (Lambda (pred A x r) (ombody A r)) (pred A x r)) _;
    refine ∃ᵢ w (∧ᵢ (IntI w (pred A x r)
      (domain (Lambda (pred A x r) (ombody A r))) hwp
      (Lambda_domain_subset (pred A x r) (ombody A r) w hwp)) hzeq) }
end;

opaque symbol ordermap_pred_unfold (A r x : τ ι) :
  π (wf A r) → π (x ∈ A) →
  π (fapply (ordermap A r) x
     = RepFun (pred A x r) (λ y, fapply (ordermap A r) y)) ≔
begin
  assume A r x hwf hx;
  refine eq_trans (ordermap_eq_image A r x hwf hx) _;
  rewrite Image_def;
  rewrite ordermap_def;
  refine ind_eq (Int_pred_domain A r x)
    (λ S, RepFun S (λ w, fapply (Lambda A (ombody A r)) w)
          = RepFun (pred A x r) (λ y, fapply (Lambda A (ombody A r)) y))
    (eq_refl (RepFun (pred A x r) (λ y, fapply (Lambda A (ombody A r)) y)))
end;

// ordermap_unfold = ordermap_pred_unfold [simplified pred_def] (pred unfolded to Collect)
opaque symbol ordermap_unfold (A r x : τ ι) :
  π (wf A r) → π (x ∈ A) →
  π (fapply (ordermap A r) x
     = RepFun (Collect A (λ y, Pair y x ∈ r)) (λ y, fapply (ordermap A r) y)) ≔
begin
  assume A r x hwf hx;
  rewrite left (pred_def A x r);
  refine ordermap_pred_unfold A r x hwf hx
end;

// Int A (domain (ordermap A r)) = A  (A ⊆ domain of the Lambda).
private opaque symbol Int_A_domain (A r : τ ι) :
  π (Int A (domain (Lambda A (ombody A r))) = A) ≔
begin
  assume A r;
  refine subset_antisym (Int A (domain (Lambda A (ombody A r)))) A _ _
  { assume w hw; refine IntD1 w A (domain (Lambda A (ombody A r))) hw }
  { assume w hw;
    refine IntI w A (domain (Lambda A (ombody A r))) hw
      (Lambda_domain_subset A (ombody A r) w hw) }
end;

opaque symbol ordermap_type (A r : τ ι) :
  π (ordermap A r ∈ Pi A (λ _, ordertype A r)) ≔
begin
  assume A r;
  rewrite ordermap_def;
  refine lam_type A (ombody A r) (λ _, ordertype A r) _;
  assume x hx;
  have hxdom : π (x ∈ domain (ordermap A r))
    { refine ind_eq (ordermap_def A r) (λ w, x ∈ domain w)
        (Lambda_domain_subset A (ombody A r) x hx) };
  have hmemI : π (fapply (ordermap A r) x ∈ Image (ordermap A r) A)
    { refine ∧ₑ₂ (Image_iff (fapply (ordermap A r) x) (ordermap A r) A) _;
      refine ∃ᵢ x (∧ᵢ (IntI x A (domain (ordermap A r)) hx hxdom)
        (eq_refl (fapply (ordermap A r) x))) };
  have hmem : π (fapply (ordermap A r) x ∈ ordertype A r)
    { refine ind_eq (ordertype_def A r) (λ w, fapply (ordermap A r) x ∈ w) hmemI };
  have happ : π (fapply (ordermap A r) x = ombody A r x)
    { rewrite ordermap_def; refine beta A (ombody A r) x hx };
  refine ind_eq (eq_sym happ) (λ w, w ∈ ordertype A r) hmem
end;

opaque symbol Ord_ordermap (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) → π (Ord (fapply (ordermap A r) x)) ≔
begin
  assume A r x hwo hx;
  have hwf : π (wf A r) { refine well_ord_is_wf A r hwo };
  have htrans : π (trans_on A r) { refine well_ord_is_trans_on A r hwo };
  refine wf_induct A r (λ w, Ord (fapply (ordermap A r) w)) hwf _ x hx;
  assume x2 hx2 ih;
  have hunf : π (fapply (ordermap A r) x2
      = RepFun (pred A x2 r) (λ y, fapply (ordermap A r) y))
    { refine ordermap_pred_unfold A r x2 hwf hx2 };
  refine OrdI (fapply (ordermap A r) x2) _ _
  { // Transset: u ∈ m(x2) → u ⊆ m(x2), via transitivity of r
    rewrite Transset_def;
    assume u hu;
    have huR : π (u ∈ RepFun (pred A x2 r) (λ y, fapply (ordermap A r) y))
      { refine ind_eq (eq_sym hunf) (λ w, u ∈ w) hu };
    have hbex : π (Bex (pred A x2 r) (λ y, u = fapply (ordermap A r) y))
      { refine ∧ₑ₁ (RepFun_iff u (pred A x2 r)
          (λ y, fapply (ordermap A r) y)) huR };
    refine ∃ₑ hbex _; assume y hy;
    have hyp : π (y ∈ pred A x2 r) { refine ∧ₑ₁ hy };
    have hueq : π (u = fapply (ordermap A r) y) { refine ∧ₑ₂ hy };
    have hyA : π (y ∈ A) { refine pred_subset A x2 r y hyp };
    have hyr : π (Pair y x2 ∈ r)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff y A x2 r) hyp) };
    assume v hv;
    have hvmy : π (v ∈ fapply (ordermap A r) y)
      { refine ind_eq (eq_sym hueq) (λ w, v ∈ w) hv };
    have hunfy : π (fapply (ordermap A r) y
        = RepFun (pred A y r) (λ w, fapply (ordermap A r) w))
      { refine ordermap_pred_unfold A r y hwf hyA };
    have hvR : π (v ∈ RepFun (pred A y r) (λ w, fapply (ordermap A r) w))
      { refine ind_eq (eq_sym hunfy) (λ w, v ∈ w) hvmy };
    have hbex2 : π (Bex (pred A y r) (λ w, v = fapply (ordermap A r) w))
      { refine ∧ₑ₁ (RepFun_iff v (pred A y r)
          (λ w, fapply (ordermap A r) w)) hvR };
    refine ∃ₑ hbex2 _; assume w hw;
    have hwp : π (w ∈ pred A y r) { refine ∧ₑ₁ hw };
    have hwA : π (w ∈ A) { refine pred_subset A y r w hwp };
    have hwy : π (Pair w y ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff w A y r) hwp) };
    have hwx : π (Pair w x2 ∈ r) { refine trans_onD A r w y x2 htrans hwA hyA hx2 hwy hyr };
    have hmw : π (fapply (ordermap A r) w
        ∈ RepFun (pred A x2 r) (λ z, fapply (ordermap A r) z))
      { refine RepFunI w (pred A x2 r) (λ z, fapply (ordermap A r) z)
          (predI w A x2 r hwx hwA) };
    have hvR2 : π (v ∈ RepFun (pred A x2 r) (λ z, fapply (ordermap A r) z))
      { refine ind_eq (∧ₑ₂ hw)
          (λ z, z ∈ RepFun (pred A x2 r) (λ z2, fapply (ordermap A r) z2)) hmw };
    refine ind_eq hunf (λ z, v ∈ z) hvR2 }
  { // every element of m(x2) is an ordinal (by IH), hence a Transset
    assume u hu;
    have huR : π (u ∈ RepFun (pred A x2 r) (λ y, fapply (ordermap A r) y))
      { refine ind_eq (eq_sym hunf) (λ w, u ∈ w) hu };
    have hbex : π (Bex (pred A x2 r) (λ y, u = fapply (ordermap A r) y))
      { refine ∧ₑ₁ (RepFun_iff u (pred A x2 r)
          (λ y, fapply (ordermap A r) y)) huR };
    refine ∃ₑ hbex _; assume y hy;
    have hyp : π (y ∈ pred A x2 r) { refine ∧ₑ₁ hy };
    have hOy : π (Ord (fapply (ordermap A r) y))
      { refine ih y (pred_subset A x2 r y hyp)
          (∧ₑ₁ (∧ₑ₁ (pred_iff y A x2 r) hyp)) };
    have hOu : π (Ord u) { refine ind_eq (∧ₑ₂ hy) (λ w, Ord w) hOy };
    refine ∧ₑ₁ (OrdD u hOu) }
end;

opaque symbol Ord_ordertype (A r : τ ι) :
  π (well_ord A r) → π (Ord (ordertype A r)) ≔
begin
  assume A r hwo;
  have hwf : π (wf A r) { refine well_ord_is_wf A r hwo };
  have hIA : π (Int A (domain (ordermap A r)) = A)
    { refine ind_eq (ordermap_def A r) (λ w, Int A (domain w) = A) (Int_A_domain A r) };
  // ordertype A r = RepFun A m  (up to the Int-domain collapse)
  have hunf0 : π (Image (ordermap A r) A = RepFun A (λ y, fapply (ordermap A r) y))
    { rewrite Image_def;
      refine ind_eq hIA
        (λ S, RepFun S (λ w, fapply (ordermap A r) w)
              = RepFun A (λ y, fapply (ordermap A r) y))
        (eq_refl (RepFun A (λ y, fapply (ordermap A r) y))) };
  have hunf : π (ordertype A r = RepFun A (λ y, fapply (ordermap A r) y))
    { rewrite ordertype_def; refine hunf0 };
  refine OrdI (ordertype A r) _ _
  { // Transset: u = m(y) ∈ ordertype, v ∈ u = RepFun(pred y)m → v = m(w), w ∈ A
    rewrite Transset_def;
    assume u hu;
    have huR : π (u ∈ RepFun A (λ y, fapply (ordermap A r) y))
      { refine ind_eq (eq_sym hunf) (λ w, u ∈ w) hu };
    have hbex : π (Bex A (λ y, u = fapply (ordermap A r) y))
      { refine ∧ₑ₁ (RepFun_iff u A (λ y, fapply (ordermap A r) y)) huR };
    refine ∃ₑ hbex _; assume y hy;
    have hyA : π (y ∈ A) { refine ∧ₑ₁ hy };
    assume v hv;
    have hvmy : π (v ∈ fapply (ordermap A r) y)
      { refine ind_eq (eq_sym (∧ₑ₂ hy)) (λ w, v ∈ w) hv };
    have hunfy : π (fapply (ordermap A r) y
        = RepFun (pred A y r) (λ w, fapply (ordermap A r) w))
      { refine ordermap_pred_unfold A r y hwf hyA };
    have hvR : π (v ∈ RepFun (pred A y r) (λ w, fapply (ordermap A r) w))
      { refine ind_eq (eq_sym hunfy) (λ w, v ∈ w) hvmy };
    have hbex2 : π (Bex (pred A y r) (λ w, v = fapply (ordermap A r) w))
      { refine ∧ₑ₁ (RepFun_iff v (pred A y r)
          (λ w, fapply (ordermap A r) w)) hvR };
    refine ∃ₑ hbex2 _; assume w hw;
    have hwA : π (w ∈ A) { refine pred_subset A y r w (∧ₑ₁ hw) };
    have hmw : π (fapply (ordermap A r) w
        ∈ RepFun A (λ z, fapply (ordermap A r) z))
      { refine RepFunI w A (λ z, fapply (ordermap A r) z) hwA };
    have hvR2 : π (v ∈ RepFun A (λ z, fapply (ordermap A r) z))
      { refine ind_eq (∧ₑ₂ hw)
          (λ z, z ∈ RepFun A (λ z2, fapply (ordermap A r) z2)) hmw };
    refine ind_eq hunf (λ z, v ∈ z) hvR2 }
  { // every element is Ord (Ord_ordermap), hence Transset
    assume u hu;
    have huR : π (u ∈ RepFun A (λ y, fapply (ordermap A r) y))
      { refine ind_eq (eq_sym hunf) (λ w, u ∈ w) hu };
    have hbex : π (Bex A (λ y, u = fapply (ordermap A r) y))
      { refine ∧ₑ₁ (RepFun_iff u A (λ y, fapply (ordermap A r) y)) huR };
    refine ∃ₑ hbex _; assume y hy;
    have hOy : π (Ord (fapply (ordermap A r) y))
      { refine Ord_ordermap A r y hwo (∧ₑ₁ hy) };
    have hOu : π (Ord u) { refine ind_eq (∧ₑ₂ hy) (λ w, Ord w) hOy };
    refine ∧ₑ₁ (OrdD u hOu) }
end;

opaque symbol ordermap_mono (w x A r : τ ι) :
  π (Pair w x ∈ r) → π (wf A r) → π (w ∈ A) → π (x ∈ A) →
  π (fapply (ordermap A r) w ∈ fapply (ordermap A r) x) ≔
begin
  assume w x A r hwx hwf hwA hxA;
  have hunf : π (fapply (ordermap A r) x
      = RepFun (pred A x r) (λ y, fapply (ordermap A r) y))
    { refine ordermap_pred_unfold A r x hwf hxA };
  have hmem : π (fapply (ordermap A r) w
      ∈ RepFun (pred A x r) (λ y, fapply (ordermap A r) y))
    { refine RepFunI w (pred A x r) (λ y, fapply (ordermap A r) y)
        (predI w A x r hwx hwA) };
  refine ind_eq hunf (λ z, fapply (ordermap A r) w ∈ z) hmem
end;

opaque symbol converse_ordermap_mono (w x A r : τ ι) :
  π (fapply (ordermap A r) w ∈ fapply (ordermap A r) x) →
  π (well_ord A r) → π (w ∈ A) → π (x ∈ A) → π (Pair w x ∈ r) ≔
begin
  assume w x A r hmm hwo hwA hxA;
  have hwf : π (wf A r) { refine well_ord_is_wf A r hwo };
  have hlin : π (linear A r) { refine well_ord_is_linear A r hwo };
  refine ∨ₑ (linearD A r w x hlin hwA hxA) _ _
  { assume h; refine h }
  { assume h;
    refine ∨ₑ h _ _
    { assume heq;
      refine ⊥ₑ (mem_irrefl (fapply (ordermap A r) w)
        (ind_eq heq (λ z, fapply (ordermap A r) w ∈ fapply (ordermap A r) z)
           hmm)) }
    { assume hxw;
      refine ⊥ₑ (mem_asym (fapply (ordermap A r) w) (fapply (ordermap A r) x)
        hmm (ordermap_mono x w A r hxw hwf hxA hwA)) } }
end;

opaque symbol ordermap_surj (A r : τ ι) :
  π (ordermap A r ∈ surj A (ordertype A r)) ≔
begin
  assume A r;
  rewrite surj_def;
  refine CollectI (ordermap A r) (Pi A (λ _, ordertype A r))
    (λ f, Ball (ordertype A r) (λ y, Bex A (λ x, fapply f x = y)))
    (ordermap_type A r) _;
  assume y hy;
  // y ∈ ordertype = RepFun (Int A dom) fapply
  have hy' : π (y ∈ Image (ordermap A r) A)
    { refine ind_eq (eq_sym (ordertype_def A r)) (λ w, y ∈ w) hy };
  have hbex : π (Bex (Int A (domain (ordermap A r)))
                  (λ x, y = fapply (ordermap A r) x))
    { refine ∧ₑ₁ (Image_iff y (ordermap A r) A) hy' };
  refine ∃ₑ hbex _; assume x hx;
  refine ∃ᵢ x (∧ᵢ (IntD1 x A (domain (ordermap A r)) (∧ₑ₁ hx))
    (eq_sym (∧ₑ₂ hx)))
end;

opaque symbol ordermap_bij (A r : τ ι) :
  π (well_ord A r) → π (ordermap A r ∈ bij A (ordertype A r)) ≔
begin
  assume A r hwo;
  have hlin : π (linear A r) { refine well_ord_is_linear A r hwo };
  have hwf : π (wf A r) { refine well_ord_is_wf A r hwo };
  rewrite bij_def;
  refine IntI (ordermap A r) (inj A (ordertype A r)) (surj A (ordertype A r))
    _ (ordermap_surj A r);
  rewrite inj_def;
  refine CollectI (ordermap A r) (Pi A (λ _, ordertype A r))
    (λ f, Ball A (λ w, Ball A (λ x, fapply f w = fapply f x ⇒ w = x)))
    (ordermap_type A r) _;
  assume w hw x hx heq;
  refine ∨ₑ (linearD A r w x hlin hw hx) _ _
  { assume hr;
    have hmono : π (fapply (ordermap A r) w ∈ fapply (ordermap A r) x)
      { refine ordermap_mono w x A r hr hwf hw hx };
    refine ⊥ₑ (mem_irrefl (fapply (ordermap A r) x)
      (ind_eq (eq_sym heq) (λ z, z ∈ fapply (ordermap A r) x) hmono)) }
  { assume h;
    refine ∨ₑ h _ _
    { assume he; refine he }
    { assume hr;
      have hmono : π (fapply (ordermap A r) x ∈ fapply (ordermap A r) w)
        { refine ordermap_mono x w A r hr hwf hx hw };
      refine ⊥ₑ (mem_irrefl (fapply (ordermap A r) x)
        (ind_eq (eq_sym heq) (λ z, fapply (ordermap A r) x ∈ z) hmono)) } }
end;

opaque symbol ordertype_ord_iso (A r : τ ι) :
  π (well_ord A r) →
  π (ordermap A r ∈ ord_iso A r (ordertype A r) (Memrel (ordertype A r))) ≔
begin
  assume A r hwo;
  have hwf : π (wf A r) { refine well_ord_is_wf A r hwo };
  have htype : π (ordermap A r ∈ Pi A (λ _, ordertype A r))
    { refine ordermap_type A r };
  rewrite ord_iso_def;
  refine CollectI (ordermap A r) (bij A (ordertype A r))
    (λ f, Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ Memrel (ordertype A r)))))
    (ordermap_bij A r hwo) _;
  assume x hx y hy;
  have hmx : π (fapply (ordermap A r) x ∈ ordertype A r)
    { refine fapply_type (ordermap A r) x A (λ _, ordertype A r) htype hx };
  have hmy : π (fapply (ordermap A r) y ∈ ordertype A r)
    { refine fapply_type (ordermap A r) y A (λ _, ordertype A r) htype hy };
  apply ∧ᵢ
  { assume hr;
    refine MemrelI (fapply (ordermap A r) x) (fapply (ordermap A r) y)
      (ordertype A r) (ordermap_mono x y A r hr hwf hx hy) hmx hmy }
  { assume hmem;
    have h3 : π (fapply (ordermap A r) x ∈ ordertype A r
                 ∧ fapply (ordermap A r) y ∈ ordertype A r
                 ∧ fapply (ordermap A r) x ∈ fapply (ordermap A r) y)
      { refine MemrelE (fapply (ordermap A r) x) (fapply (ordermap A r) y)
          (ordertype A r) hmem };
    refine converse_ordermap_mono x y A r (∧ₑ₂ (∧ₑ₂ h3)) hwo hx hy }
end;

opaque symbol ordertype_eq (f A r B s : τ ι) :
  π (f ∈ ord_iso A r B s) → π (well_ord B s) →
  π (ordertype A r = ordertype B s) ≔
begin
  assume f A r B s hf hwoB;
  have hwoA : π (well_ord A r) { refine well_ord_ord_iso A r B s f hwoB hf };
  // Compose ordertype(A,r) ≅ A ≅ B ≅ ordertype(B,s), then apply
  // Ord_iso_implies_eq to the two ordinals.
  have g1 : π (converse (ordermap A r)
      ∈ ord_iso (ordertype A r) (Memrel (ordertype A r)) A r)
    { refine ord_iso_sym (ordermap A r) A r (ordertype A r)
        (Memrel (ordertype A r)) (ordertype_ord_iso A r hwoA) };
  have g2 : π (rcomp f (converse (ordermap A r))
      ∈ ord_iso (ordertype A r) (Memrel (ordertype A r)) B s)
    { refine ord_iso_trans (converse (ordermap A r)) f (ordertype A r)
        (Memrel (ordertype A r)) A r B s g1 hf };
  have g3 : π (rcomp (ordermap B s) (rcomp f (converse (ordermap A r)))
      ∈ ord_iso (ordertype A r) (Memrel (ordertype A r))
                (ordertype B s) (Memrel (ordertype B s)))
    { refine ord_iso_trans (rcomp f (converse (ordermap A r))) (ordermap B s)
        (ordertype A r) (Memrel (ordertype A r)) B s
        (ordertype B s) (Memrel (ordertype B s)) g2
        (ordertype_ord_iso B s hwoB) };
  refine Ord_iso_implies_eq (ordertype A r) (ordertype B s)
    (rcomp (ordermap B s) (rcomp f (converse (ordermap A r))))
    (Ord_ordertype A r hwoA) (Ord_ordertype B s hwoB) g3
end;

opaque symbol ordertype_eq_imp_ord_iso (A r B s : τ ι) :
  π (ordertype A r = ordertype B s) → π (well_ord A r) → π (well_ord B s) →
  π (`∃ (f : τ ι), f ∈ ord_iso A r B s) ≔
begin
  assume A r B s heq hwoA hwoB;
  have h1 : π (ordermap A r
      ∈ ord_iso A r (ordertype A r) (Memrel (ordertype A r)))
    { refine ordertype_ord_iso A r hwoA };
  have h1b : π (ordermap A r
      ∈ ord_iso A r (ordertype B s) (Memrel (ordertype B s)))
    { refine ind_eq (eq_sym heq)
        (λ w, ordermap A r ∈ ord_iso A r w (Memrel w)) h1 };
  have h2 : π (converse (ordermap B s)
      ∈ ord_iso (ordertype B s) (Memrel (ordertype B s)) B s)
    { refine ord_iso_sym (ordermap B s) B s (ordertype B s)
        (Memrel (ordertype B s)) (ordertype_ord_iso B s hwoB) };
  refine ∃ᵢ (rcomp (converse (ordermap B s)) (ordermap A r))
    (ord_iso_trans (ordermap A r) (converse (ordermap B s)) A r
      (ordertype B s) (Memrel (ordertype B s)) B s h1b h2)
end;

// Replacing the source relation of an ord_iso by one that agrees on the
// source set gives another ord_iso.
private opaque symbol ord_iso_change_left (f A r r2 B s : τ ι) :
  π (f ∈ ord_iso A r B s) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ A) →
    π ((Pair x y ∈ r) ⇔ (Pair x y ∈ r2))) →
  π (f ∈ ord_iso A r2 B s) ≔
begin
  assume f A r r2 B s hf hagree;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hcond : π (Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ s))))
    { refine ord_iso_memD f A r B s hf };
  rewrite ord_iso_def;
  refine CollectI f (bij A B) (λ g, Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r2) ⇔ (Pair (fapply g x) (fapply g y) ∈ s)))) hbij _;
  assume x hx y hy;
  apply ∧ᵢ
  { assume h2;
    refine ∧ₑ₁ (hcond x hx y hy) (∧ₑ₂ (hagree x y hx hy) h2) }
  { assume hs;
    refine ∧ₑ₁ (hagree x y hx hy) (∧ₑ₂ (hcond x hx y hy) hs) }
end;

opaque symbol le_ordertype_Memrel (j i : τ ι) :
  π (le j i) → π (ordertype j (Memrel i) = j) ≔
begin
  assume j i hle;
  have hOj : π (Ord j) { refine lt_Ord j (succ i) hle };
  have hsub : π (j ⊆ i) { refine le_imp_subset j i hle };
  have hwo : π (well_ord j (Memrel i)) { refine le_well_ord_Memrel j i hle };
  have hm : π (ordermap j (Memrel i) ∈ ord_iso j (Memrel i)
      (ordertype j (Memrel i)) (Memrel (ordertype j (Memrel i))))
    { refine ordertype_ord_iso j (Memrel i) hwo };
  // On j the relations Memrel(i) and Memrel(j) agree.
  have hm2 : π (ordermap j (Memrel i) ∈ ord_iso j (Memrel j)
      (ordertype j (Memrel i)) (Memrel (ordertype j (Memrel i))))
    { refine ord_iso_change_left (ordermap j (Memrel i)) j (Memrel i)
        (Memrel j) (ordertype j (Memrel i))
        (Memrel (ordertype j (Memrel i))) hm _;
      assume x y hx hy;
      apply ∧ᵢ
      { assume h;
        have h3 : π (x ∈ i ∧ y ∈ i ∧ x ∈ y) { refine MemrelE x y i h };
        refine MemrelI x y j (∧ₑ₂ (∧ₑ₂ h3)) hx hy }
      { assume h;
        have h3 : π (x ∈ j ∧ y ∈ j ∧ x ∈ y) { refine MemrelE x y j h };
        refine MemrelI x y i (∧ₑ₂ (∧ₑ₂ h3)) (hsub x hx) (hsub y hy) } };
  refine eq_sym (Ord_iso_implies_eq j (ordertype j (Memrel i))
    (ordermap j (Memrel i)) hOj (Ord_ordertype j (Memrel i) hwo) hm2)
end;

// ordertype_Memrel = le_refl [THEN le_ordertype_Memrel] : Ord(i) ⟹ ordertype(i,Memrel(i)) = i
opaque symbol ordertype_Memrel (i : τ ι) :
  π (Ord i) → π (ordertype i (Memrel i) = i) ≔
begin
  assume i hOi;
  refine le_ordertype_Memrel i i (le_refl i hOi)
end;

opaque symbol ordertype_0 (r : τ ι) :
  π (ordertype empty r = empty) ≔
begin
  assume r;
  refine equals0I (ordertype empty r) _;
  assume z hz;
  have hz' : π (z ∈ Image (ordermap empty r) empty)
    { refine ind_eq (eq_sym (ordertype_def empty r)) (λ w, z ∈ w) hz };
  have hbex : π (Bex (Int empty (domain (ordermap empty r)))
                  (λ x, z = fapply (ordermap empty r) x))
    { refine ∧ₑ₁ (Image_iff z (ordermap empty r) empty) hz' };
  refine ∃ₑ hbex _; assume w hw;
  refine emptyE w (IntD1 w empty (domain (ordermap empty r))
    (∧ₑ₁ hw))
end;

// bij_ordertype_vimage = ord_iso_rvimage [THEN ordertype_eq]
opaque symbol bij_ordertype_vimage (f A B s : τ ι) :
  π (f ∈ bij A B) → π (well_ord B s) →
  π (ordertype A (rvimage A f s) = ordertype B s) ≔
begin
  assume f A B s hf hwo;
  refine ordertype_eq f A (rvimage A f s) B s (ord_iso_rvimage f A B s hf) hwo
end;

opaque symbol ordermap_pred_eq_ordermap (A r y z : τ ι) :
  π (well_ord A r) → π (y ∈ A) → π (z ∈ pred A y r) →
  π (fapply (ordermap (pred A y r) r) z = fapply (ordermap A r) z) ≔
begin
  assume A r y z hwo hyA hzP;
  have hwf : π (wf A r) { refine well_ord_is_wf A r hwo };
  have htrans : π (trans_on A r) { refine well_ord_is_trans_on A r hwo };
  have hPsub : π (pred A y r ⊆ A) { refine pred_subset A y r };
  have hwfP : π (wf (pred A y r) r) { refine wf_subset A (pred A y r) r hwf hPsub };
  refine wf_induct A r
    (λ w, w ∈ pred A y r
          ⇒ fapply (ordermap (pred A y r) r) w = fapply (ordermap A r) w)
    hwf _ z (hPsub z hzP) hzP;
  assume z2 hz2A ih hz2P;
  have hz2y : π (Pair z2 y ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z2 A y r) hz2P) };
  have hu1 : π (fapply (ordermap (pred A y r) r) z2
      = RepFun (pred (pred A y r) z2 r)
          (λ w, fapply (ordermap (pred A y r) r) w))
    { refine ordermap_pred_unfold (pred A y r) r z2 hwfP hz2P };
  // pred over the sub-order equals pred over A (r is transitive)
  have hset : π (pred (pred A y r) z2 r = pred A z2 r)
    { refine equality_iffI (pred (pred A y r) z2 r) (pred A z2 r) _;
      assume w;
      apply ∧ᵢ
      { assume hw;
        have hwP : π (w ∈ pred A y r)
          { refine pred_subset (pred A y r) z2 r w hw };
        refine predI w A z2 r
          (∧ₑ₁ (∧ₑ₁ (pred_iff w (pred A y r) z2 r) hw)) (hPsub w hwP) }
      { assume hw;
        have hwA : π (w ∈ A) { refine pred_subset A z2 r w hw };
        have hwz2 : π (Pair w z2 ∈ r)
          { refine ∧ₑ₁ (∧ₑ₁ (pred_iff w A z2 r) hw) };
        have hwy : π (Pair w y ∈ r)
          { refine trans_onD A r w z2 y htrans hwA hz2A hyA hwz2 hz2y };
        refine predI w (pred A y r) z2 r hwz2 (predI w A y r hwy hwA) } };
  have hu2 : π (fapply (ordermap (pred A y r) r) z2
      = RepFun (pred A z2 r) (λ w, fapply (ordermap (pred A y r) r) w))
    { refine ind_eq (eq_sym hset)
        (λ S, fapply (ordermap (pred A y r) r) z2
              = RepFun S (λ w, fapply (ordermap (pred A y r) r) w)) hu1 };
  have hcong : π (RepFun (pred A z2 r) (λ w, fapply (ordermap (pred A y r) r) w)
      = RepFun (pred A z2 r) (λ w, fapply (ordermap A r) w))
    { refine RepFun_cong (pred A z2 r)
        (λ w, fapply (ordermap (pred A y r) r) w)
        (λ w, fapply (ordermap A r) w) _;
      assume w hw;
      have hwA : π (w ∈ A) { refine pred_subset A z2 r w hw };
      have hwz2 : π (Pair w z2 ∈ r)
        { refine ∧ₑ₁ (∧ₑ₁ (pred_iff w A z2 r) hw) };
      have hwy : π (Pair w y ∈ r)
        { refine trans_onD A r w z2 y htrans hwA hz2A hyA hwz2 hz2y };
      refine ih w hwA hwz2 (predI w A y r hwy hwA) };
  have hu3 : π (fapply (ordermap A r) z2
      = RepFun (pred A z2 r) (λ w, fapply (ordermap A r) w))
    { refine ordermap_pred_unfold A r z2 hwf hz2A };
  refine eq_trans hu2 (eq_trans hcong (eq_sym hu3))
end;

opaque symbol ordertype_unfold (A r : τ ι) :
  π (ordertype A r = RepFun A (λ y, fapply (ordermap A r) y)) ≔
begin
  assume A r;
  have hIA : π (Int A (domain (ordermap A r)) = A)
    { refine ind_eq (ordermap_def A r) (λ w, Int A (domain w) = A) (Int_A_domain A r) };
  have h0 : π (Image (ordermap A r) A = RepFun A (λ y, fapply (ordermap A r) y))
    { rewrite Image_def;
      refine ind_eq hIA
        (λ S, RepFun S (λ w, fapply (ordermap A r) w)
              = RepFun A (λ y, fapply (ordermap A r) y))
        (eq_refl (RepFun A (λ y, fapply (ordermap A r) y))) };
  rewrite ordertype_def;
  refine h0
end;

// ordertype of an initial segment is the ordermap value at its bound.
private opaque symbol ordertype_pred_eq (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) →
  π (ordertype (pred A x r) r = fapply (ordermap A r) x) ≔
begin
  assume A r x hwo hx;
  have hwf : π (wf A r) { refine well_ord_is_wf A r hwo };
  have h1 : π (ordertype (pred A x r) r
      = RepFun (pred A x r) (λ w, fapply (ordermap (pred A x r) r) w))
    { refine ordertype_unfold (pred A x r) r };
  have h2 : π (RepFun (pred A x r) (λ w, fapply (ordermap (pred A x r) r) w)
      = RepFun (pred A x r) (λ w, fapply (ordermap A r) w))
    { refine RepFun_cong (pred A x r)
        (λ w, fapply (ordermap (pred A x r) r) w)
        (λ w, fapply (ordermap A r) w) _;
      assume w hw;
      refine ordermap_pred_eq_ordermap A r x w hwo hx hw };
  refine eq_trans h1
    (eq_trans h2 (eq_sym (ordermap_pred_unfold A r x hwf hx)))
end;

opaque symbol ordertype_pred_subset (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) →
  π (ordertype (pred A x r) r ⊆ ordertype A r) ≔
begin
  assume A r x hwo hx;
  have heq : π (ordertype (pred A x r) r = fapply (ordermap A r) x)
    { refine ordertype_pred_eq A r x hwo hx };
  have hmem : π (fapply (ordermap A r) x ∈ ordertype A r)
    { refine fapply_type (ordermap A r) x A (λ _, ordertype A r)
        (ordermap_type A r) hx };
  have hOot : π (Ord (ordertype A r)) { refine Ord_ordertype A r hwo };
  have hsub : π (fapply (ordermap A r) x ⊆ ordertype A r)
    { refine OrdmemD (ordertype A r) (fapply (ordermap A r) x) hmem hOot };
  refine ind_eq heq (λ w, w ⊆ ordertype A r) hsub
end;

opaque symbol ordertype_pred_lt (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) →
  π (lt (ordertype (pred A x r) r) (ordertype A r)) ≔
begin
  assume A r x hwo hx;
  have heq : π (ordertype (pred A x r) r = fapply (ordermap A r) x)
    { refine ordertype_pred_eq A r x hwo hx };
  have hmem : π (fapply (ordermap A r) x ∈ ordertype A r)
    { refine fapply_type (ordermap A r) x A (λ _, ordertype A r)
        (ordermap_type A r) hx };
  have hlt : π (lt (fapply (ordermap A r) x) (ordertype A r))
    { refine ltI (fapply (ordermap A r) x) (ordertype A r) hmem
        (Ord_ordertype A r hwo) };
  refine ind_eq heq (λ w, lt w (ordertype A r)) hlt
end;

opaque symbol ordertype_pred_unfold (A r : τ ι) :
  π (well_ord A r) →
  π (ordertype A r = RepFun A (λ x, ordertype (pred A x r) r)) ≔
begin
  assume A r hwo;
  refine eq_trans (ordertype_unfold A r) _;
  refine RepFun_cong A (λ y, fapply (ordermap A r) y)
    (λ x, ordertype (pred A x r) r) _;
  assume x hx;
  refine eq_sym (ordertype_pred_eq A r x hwo hx)
end;

// ===========================================================================
// Alternative definition of ordinal
// ===========================================================================

opaque symbol Ord_is_Ord_alt (i : τ ι) :
  π (Ord i) → π (Ord_alt i) ≔
begin
  assume i hOi;
  rewrite Ord_alt_def;
  apply ∧ᵢ
  { refine well_ord_Memrel i hOi }
  { assume u hu;
    have hpred : π (pred i u (Memrel i) = Int i u)
      { refine pred_Memrel u i hu };
    have hsub : π (u ⊆ i) { refine OrdmemD i u hu hOi };
    have hInt : π (Int i u = u)
      { refine equality_iffI (Int i u) u _;
        assume w;
        apply ∧ᵢ
        { assume hw; refine IntD2 w i u hw }
        { assume hw; refine IntI w i u (hsub w hw) hw } };
    refine eq_sym (eq_trans hpred hInt) }
end;

opaque symbol Ord_alt_is_Ord (i : τ ι) :
  π (Ord_alt i) → π (Ord i) ≔
begin
  assume i halt;
  have halt' : π (well_ord i (Memrel i) ∧ Ball i (λ u, u = pred i u (Memrel i)))
    { refine ind_eq (eq_sym (Ord_alt_def i)) (λ p, p) halt };
  have hwo : π (well_ord i (Memrel i)) { refine ∧ₑ₁ halt' };
  have hpr : π (Ball i (λ u, u = pred i u (Memrel i))) { refine ∧ₑ₂ halt' };
  have htrans : π (trans_on i (Memrel i)) { refine well_ord_is_trans_on i (Memrel i) hwo };
  // Transset(i): u ∈ i → u = pred(i,u,Memrel i) ⊆ i
  have hT : π (Transset i)
    { rewrite Transset_def;
      assume u hu;
      have heq : π (u = pred i u (Memrel i)) { refine hpr u hu };
      assume w hw;
      have hwpred : π (w ∈ pred i u (Memrel i))
        { refine ind_eq (eq_sym heq) (λ z, w ∈ z) hw };
      refine pred_subset i u (Memrel i) w hwpred };
  refine OrdI i hT _;
  // every u ∈ i is a Transset, via transitivity of Memrel(i) on i
  assume u hu;
  rewrite Transset_def;
  assume v hv w hw;
  have hvi : π (v ∈ i) { refine TranssetD i u hT hu v hv };
  have hui : π (u ∈ i) { refine hu };
  have hwi : π (w ∈ i) { refine TranssetD i v hT hvi w hw };
  have hwv : π (Pair w v ∈ Memrel i) { refine MemrelI w v i hw hwi hvi };
  have hvu : π (Pair v u ∈ Memrel i) { refine MemrelI v u i hv hvi hui };
  have hwu : π (Pair w u ∈ Memrel i)
    { refine trans_onD i (Memrel i) w v u htrans hwi hvi hui hwv hvu };
  refine ∧ₑ₂ (∧ₑ₂ (MemrelE w u i hwu))
end;

// ===========================================================================
// Ordinal Addition
// ===========================================================================

// The identity case-analysis function used by bij_sum_0 / bij_0_sum.
private symbol idcase (z : τ ι) : τ ι ≔ case_sum (λ x, x) (λ y, y) z;

opaque symbol bij_sum_0 (A : τ ι) :
  π (Lambda (sum A empty) (λ z, case_sum (λ x, x) (λ y, y) z)
     ∈ bij (sum A empty) A) ≔
begin
  assume A;
  refine lam_bijective (sum A empty) A idcase (λ x, Inl x) _ _ _ _
  { assume z hz;
    refine sumE z A empty _ hz _ _
    { assume x hx hze;
      rewrite hze;
      refine ind_eq (case_Inl (λ x2, x2) (λ y, y) x) (λ w, w ∈ A) hx }
    { assume y hy hze; refine ⊥ₑ (emptyE y hy) } }
  { assume x hx; refine InlI x A empty hx }
  { assume z hz;
    refine sumE z A empty _ hz _ _
    { assume x hx hze;
      rewrite hze;
      refine ind_eq (case_Inl (λ x2, x2) (λ y, y) x) (λ w, Inl w = Inl x)
        (eq_refl (Inl x)) }
    { assume y hy hze; refine ⊥ₑ (emptyE y hy) } }
  { assume x hx; refine case_Inl (λ x2, x2) (λ y, y) x }
end;

opaque symbol ordertype_sum_0_eq (A r s : τ ι) :
  π (well_ord A r) →
  π (ordertype (sum A empty) (radd A r empty s) = ordertype A r) ≔
begin
  assume A r s hwo;
  have hiso : π (Lambda (sum A empty) idcase
      ∈ ord_iso (sum A empty) (radd A r empty s) A r)
    { refine ord_isoI (Lambda (sum A empty) idcase)
        (sum A empty) (radd A r empty s) A r (bij_sum_0 A) _;
      assume z hz w hw;
      refine sumE z A empty _ hz _ _
      { assume x hx hze;
        refine sumE w A empty _ hw _ _
        { assume y hy hwe;
          rewrite hze; rewrite hwe;
          have hfx : π (fapply (Lambda (sum A empty) idcase) (Inl x) = x)
            { refine eq_trans
                (beta (sum A empty) idcase (Inl x) (InlI x A empty hx))
                (case_Inl (λ x2, x2) (λ y2, y2) x) };
          have hfy : π (fapply (Lambda (sum A empty) idcase) (Inl y) = y)
            { refine eq_trans
                (beta (sum A empty) idcase (Inl y) (InlI y A empty hy))
                (case_Inl (λ x2, x2) (λ y2, y2) y) };
          apply ∧ᵢ
          { assume hr;
            have h3 : π (x ∈ A ∧ y ∈ A ∧ Pair x y ∈ r)
              { refine ∧ₑ₁ (radd_Inl_iff x y A r empty s) hr };
            refine ind_eq hfx
              (λ u, Pair u (fapply (Lambda (sum A empty) idcase) (Inl y)) ∈ r)
              (ind_eq hfy (λ v, Pair x v ∈ r) (∧ₑ₂ (∧ₑ₂ h3))) }
          { assume hfr;
            have hxy : π (Pair x y ∈ r)
              { refine ind_eq (eq_sym hfy) (λ v, Pair x v ∈ r)
                  (ind_eq (eq_sym hfx)
                    (λ u, Pair u (fapply (Lambda (sum A empty) idcase) (Inl y)) ∈ r)
                    hfr) };
            refine ∧ₑ₂ (radd_Inl_iff x y A r empty s)
              (∧ᵢ hx (∧ᵢ hy hxy)) } }
        { assume y hy hwe; refine ⊥ₑ (emptyE y hy) } }
      { assume x hx hze; refine ⊥ₑ (emptyE x hx) } };
  refine ordertype_eq (Lambda (sum A empty) idcase)
    (sum A empty) (radd A r empty s) A r hiso hwo
end;

opaque symbol bij_0_sum (A : τ ι) :
  π (Lambda (sum empty A) (λ z, case_sum (λ x, x) (λ y, y) z)
     ∈ bij (sum empty A) A) ≔
begin
  assume A;
  refine lam_bijective (sum empty A) A idcase (λ y, Inr y) _ _ _ _
  { assume z hz;
    refine sumE z empty A _ hz _ _
    { assume x hx hze; refine ⊥ₑ (emptyE x hx) }
    { assume y hy hze;
      rewrite hze;
      refine ind_eq (case_Inr (λ x2, x2) (λ y2, y2) y) (λ w, w ∈ A) hy } }
  { assume y hy; refine InrI y empty A hy }
  { assume z hz;
    refine sumE z empty A _ hz _ _
    { assume x hx hze; refine ⊥ₑ (emptyE x hx) }
    { assume y hy hze;
      rewrite hze;
      refine ind_eq (case_Inr (λ x2, x2) (λ y2, y2) y) (λ w, Inr w = Inr y)
        (eq_refl (Inr y)) } }
  { assume y hy; refine case_Inr (λ x2, x2) (λ y2, y2) y }
end;

opaque symbol ordertype_0_sum_eq (A r s : τ ι) :
  π (well_ord A r) →
  π (ordertype (sum empty A) (radd empty s A r) = ordertype A r) ≔
begin
  assume A r s hwo;
  have hiso : π (Lambda (sum empty A) idcase
      ∈ ord_iso (sum empty A) (radd empty s A r) A r)
    { refine ord_isoI (Lambda (sum empty A) idcase)
        (sum empty A) (radd empty s A r) A r (bij_0_sum A) _;
      assume z hz w hw;
      refine sumE z empty A _ hz _ _
      { assume x hx hze; refine ⊥ₑ (emptyE x hx) }
      { assume x hx hze;
        refine sumE w empty A _ hw _ _
        { assume y hy hwe; refine ⊥ₑ (emptyE y hy) }
        { assume y hy hwe;
          rewrite hze; rewrite hwe;
          have hfx : π (fapply (Lambda (sum empty A) idcase) (Inr x) = x)
            { refine eq_trans
                (beta (sum empty A) idcase (Inr x) (InrI x empty A hx))
                (case_Inr (λ x2, x2) (λ y2, y2) x) };
          have hfy : π (fapply (Lambda (sum empty A) idcase) (Inr y) = y)
            { refine eq_trans
                (beta (sum empty A) idcase (Inr y) (InrI y empty A hy))
                (case_Inr (λ x2, x2) (λ y2, y2) y) };
          apply ∧ᵢ
          { assume hr;
            have h3 : π (x ∈ A ∧ y ∈ A ∧ Pair x y ∈ r)
              { refine ∧ₑ₁ (radd_Inr_iff x y empty s A r) hr };
            refine ind_eq hfx
              (λ u, Pair u (fapply (Lambda (sum empty A) idcase) (Inr y)) ∈ r)
              (ind_eq hfy (λ v, Pair x v ∈ r) (∧ₑ₂ (∧ₑ₂ h3))) }
          { assume hfr;
            have hxy : π (Pair x y ∈ r)
              { refine ind_eq (eq_sym hfy) (λ v, Pair x v ∈ r)
                  (ind_eq (eq_sym hfx)
                    (λ u, Pair u (fapply (Lambda (sum empty A) idcase) (Inr y)) ∈ r)
                    hfr) };
            refine ∧ₑ₂ (radd_Inr_iff x y empty s A r)
              (∧ᵢ hx (∧ᵢ hy hxy)) } } } };
  refine ordertype_eq (Lambda (sum empty A) idcase)
    (sum empty A) (radd empty s A r) A r hiso hwo
end;

opaque symbol pred_Inl_bij (a A r B s : τ ι) :
  π (a ∈ A) →
  π (Lambda (pred A a r) (λ x, Inl x)
     ∈ bij (pred A a r) (pred (sum A B) (Inl a) (radd A r B s))) ≔
begin
  assume a A r B s haA;
  refine lam_bijective (pred A a r) (pred (sum A B) (Inl a) (radd A r B s))
    (λ x, Inl x) idcase _ _ _ _
  { assume x hx;
    have hxA : π (x ∈ A) { refine pred_subset A a r x hx };
    have hxa : π (Pair x a ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff x A a r) hx) };
    refine predI (Inl x) (sum A B) (Inl a) (radd A r B s)
      (∧ₑ₂ (radd_Inl_iff x a A r B s) (∧ᵢ hxA (∧ᵢ haA hxa)))
      (InlI x A B hxA) }
  { assume z hz;
    have hzs : π (z ∈ sum A B)
      { refine pred_subset (sum A B) (Inl a) (radd A r B s) z hz };
    have hrel : π (Pair z (Inl a) ∈ radd A r B s)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z (sum A B) (Inl a) (radd A r B s)) hz) };
    refine sumE z A B _ hzs _ _
    { assume x hx hze;
      have hrel2 : π (Pair (Inl x) (Inl a) ∈ radd A r B s)
        { refine ind_eq (eq_sym hze) (λ w, Pair w (Inl a) ∈ radd A r B s) hrel };
      have h3 : π (x ∈ A ∧ a ∈ A ∧ Pair x a ∈ r)
        { refine ∧ₑ₁ (radd_Inl_iff x a A r B s) hrel2 };
      have hxp : π (x ∈ pred A a r)
        { refine predI x A a r (∧ₑ₂ (∧ₑ₂ h3)) (∧ₑ₁ h3) };
      rewrite hze;
      refine ind_eq (case_Inl (λ x2, x2) (λ y2, y2) x) (λ w, w ∈ pred A a r)
        hxp }
    { assume y hy hze;
      have hrel2 : π (Pair (Inr y) (Inl a) ∈ radd A r B s)
        { refine ind_eq (eq_sym hze) (λ w, Pair w (Inl a) ∈ radd A r B s) hrel };
      refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff y a A r B s) hrel2) } }
  { assume x hx; refine case_Inl (λ x2, x2) (λ y2, y2) x }
  { assume z hz;
    have hzs : π (z ∈ sum A B)
      { refine pred_subset (sum A B) (Inl a) (radd A r B s) z hz };
    have hrel : π (Pair z (Inl a) ∈ radd A r B s)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z (sum A B) (Inl a) (radd A r B s)) hz) };
    refine sumE z A B _ hzs _ _
    { assume x hx hze;
      rewrite hze;
      refine ind_eq (case_Inl (λ x2, x2) (λ y2, y2) x) (λ w, Inl w = Inl x)
        (eq_refl (Inl x)) }
    { assume y hy hze;
      have hrel2 : π (Pair (Inr y) (Inl a) ∈ radd A r B s)
        { refine ind_eq (eq_sym hze) (λ w, Pair w (Inl a) ∈ radd A r B s) hrel };
      refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff y a A r B s) hrel2) } }
end;

opaque symbol ordertype_pred_Inl_eq (a A r B s : τ ι) :
  π (a ∈ A) → π (well_ord A r) →
  π (ordertype (pred (sum A B) (Inl a) (radd A r B s)) (radd A r B s)
     = ordertype (pred A a r) r) ≔
begin
  assume a A r B s haA hwo;
  have hiso : π (Lambda (pred A a r) (λ x, Inl x)
      ∈ ord_iso (pred A a r) r
                (pred (sum A B) (Inl a) (radd A r B s)) (radd A r B s))
    { refine ord_isoI (Lambda (pred A a r) (λ x, Inl x)) (pred A a r) r
        (pred (sum A B) (Inl a) (radd A r B s)) (radd A r B s)
        (pred_Inl_bij a A r B s haA) _;
      assume x hx y hy;
      have hxA : π (x ∈ A) { refine pred_subset A a r x hx };
      have hyA : π (y ∈ A) { refine pred_subset A a r y hy };
      have hfx : π (fapply (Lambda (pred A a r) (λ w, Inl w)) x = Inl x)
        { refine beta (pred A a r) (λ w, Inl w) x hx };
      have hfy : π (fapply (Lambda (pred A a r) (λ w, Inl w)) y = Inl y)
        { refine beta (pred A a r) (λ w, Inl w) y hy };
      apply ∧ᵢ
      { assume hr;
        refine ind_eq hfx
          (λ u, Pair u (fapply (Lambda (pred A a r) (λ w, Inl w)) y)
                ∈ radd A r B s)
          (ind_eq hfy (λ v, Pair (Inl x) v ∈ radd A r B s)
            (∧ₑ₂ (radd_Inl_iff x y A r B s) (∧ᵢ hxA (∧ᵢ hyA hr)))) }
      { assume hfr;
        have hrel : π (Pair (Inl x) (Inl y) ∈ radd A r B s)
          { refine ind_eq (eq_sym hfy) (λ v, Pair (Inl x) v ∈ radd A r B s)
              (ind_eq (eq_sym hfx)
                (λ u, Pair u (fapply (Lambda (pred A a r) (λ w, Inl w)) y)
                      ∈ radd A r B s) hfr) };
        refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff x y A r B s) hrel)) } };
  // Follow Isabelle: sym the iso so ordertype_eq needs well_ord(pred A a r, r)
  // — derivable from hwo via pred_subset — not the unavailable well_ord(B,s).
  have hwoP : π (well_ord (pred A a r) r)
    { refine well_ord_subset A (pred A a r) r hwo (pred_subset A a r) };
  refine ordertype_eq
    (converse (Lambda (pred A a r) (λ x, Inl x)))
    (pred (sum A B) (Inl a) (radd A r B s)) (radd A r B s)
    (pred A a r) r
    (ord_iso_sym (Lambda (pred A a r) (λ x, Inl x)) (pred A a r) r
       (pred (sum A B) (Inl a) (radd A r B s)) (radd A r B s) hiso)
    hwoP
end;

// pred_Inr_bij (Isabelle OrderType.thy): the identity on A+pred(B,b,s) is a
// bijection onto pred(A+B, Inr b, radd) — every Inl precedes Inr b, and the
// Inr's below Inr b are exactly the Inr images of pred(B,b,s).
opaque symbol pred_Inr_bij (b A r B s : τ ι) :
  π (b ∈ B) →
  π (Lambda (sum A (pred B b s)) (λ z, z)
     ∈ bij (sum A (pred B b s)) (pred (sum A B) (Inr b) (radd A r B s))) ≔
begin
  assume b A r B s hbB;
  refine lam_bijective (sum A (pred B b s))
    (pred (sum A B) (Inr b) (radd A r B s)) (λ z, z) (λ z, z) _ _ _ _
  // (1) forward: z ∈ A+pred(B,b,s) → z ∈ pred(A+B, Inr b, radd)
  { assume z hz;
    refine sumE z A (pred B b s) (z ∈ pred (sum A B) (Inr b) (radd A r B s)) hz _ _
    { assume x hx hze;
      refine ind_eq hze (λ w, w ∈ pred (sum A B) (Inr b) (radd A r B s))
        (predI (Inl x) (sum A B) (Inr b) (radd A r B s)
          (∧ₑ₂ (radd_Inl_Inr_iff x b A r B s) (∧ᵢ hx hbB))
          (InlI x A B hx)) }
    { assume y hy hze;
      have hyB : π (y ∈ B) { refine pred_subset B b s y hy };
      have hyb : π (Pair y b ∈ s) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff y B b s) hy) };
      refine ind_eq hze (λ w, w ∈ pred (sum A B) (Inr b) (radd A r B s))
        (predI (Inr y) (sum A B) (Inr b) (radd A r B s)
          (∧ₑ₂ (radd_Inr_iff y b A r B s) (∧ᵢ hyB (∧ᵢ hbB hyb)))
          (InrI y A B hyB)) } }
  // (2) inverse: z ∈ pred(A+B, Inr b, radd) → z ∈ A+pred(B,b,s)
  { assume z hz;
    have hzs : π (z ∈ sum A B)
      { refine pred_subset (sum A B) (Inr b) (radd A r B s) z hz };
    have hrel : π (Pair z (Inr b) ∈ radd A r B s)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z (sum A B) (Inr b) (radd A r B s)) hz) };
    refine sumE z A B (z ∈ sum A (pred B b s)) hzs _ _
    { assume x hx hze;
      refine ind_eq hze (λ w, w ∈ sum A (pred B b s)) (InlI x A (pred B b s) hx) }
    { assume y hy hze;
      have hrel2 : π (Pair (Inr y) (Inr b) ∈ radd A r B s)
        { refine ind_eq (eq_sym hze) (λ w, Pair w (Inr b) ∈ radd A r B s) hrel };
      have h3 : π (y ∈ B ∧ b ∈ B ∧ Pair y b ∈ s)
        { refine ∧ₑ₁ (radd_Inr_iff y b A r B s) hrel2 };
      have hyp : π (y ∈ pred B b s)
        { refine predI y B b s (∧ₑ₂ (∧ₑ₂ h3)) (∧ₑ₁ h3) };
      refine ind_eq hze (λ w, w ∈ sum A (pred B b s)) (InrI y A (pred B b s) hyp) } }
  // (3) d(c z) = z   (4) c(d z) = z  — identity, reflexivity
  { assume z hz; reflexivity }
  { assume z hz; reflexivity }
end;

// ordertype_pred_Inr_eq (Isabelle OrderType.thy): the predecessors of Inr b
// in A+B under radd(A,r,B,s) have the same ordertype as A+pred(B,b,s) under
// radd(A,r,pred(B,b,s),s).
opaque symbol ordertype_pred_Inr_eq (b A r B s : τ ι) :
  π (b ∈ B) → π (well_ord A r) → π (well_ord B s) →
  π (ordertype (pred (sum A B) (Inr b) (radd A r B s)) (radd A r B s)
     = ordertype (sum A (pred B b s)) (radd A r (pred B b s) s)) ≔
begin
  assume b A r B s hbB hwoA hwoB;
  have hiso : π (Lambda (sum A (pred B b s)) (λ z, z)
      ∈ ord_iso (sum A (pred B b s)) (radd A r (pred B b s) s)
                (pred (sum A B) (Inr b) (radd A r B s)) (radd A r B s))
    { refine ord_isoI (Lambda (sum A (pred B b s)) (λ z, z))
        (sum A (pred B b s)) (radd A r (pred B b s) s)
        (pred (sum A B) (Inr b) (radd A r B s)) (radd A r B s)
        (pred_Inr_bij b A r B s hbB) _;
      assume x hx y hy;
      rewrite (beta (sum A (pred B b s)) (λ z, z) x hx);
      rewrite (beta (sum A (pred B b s)) (λ z, z) y hy);
      simplify rule off;
      // goal: Pair x y ∈ radd A r (pred B b s) s ⇔ Pair x y ∈ radd A r B s
      refine sumE x A (pred B b s)
        ((Pair x y ∈ radd A r (pred B b s) s) ⇔ (Pair x y ∈ radd A r B s))
        hx _ _
      { assume xa hxa hzex;
        rewrite hzex;
        refine sumE y A (pred B b s)
          ((Pair (Inl xa) y ∈ radd A r (pred B b s) s)
           ⇔ (Pair (Inl xa) y ∈ radd A r B s)) hy _ _
        { assume ya hya hzey;
          rewrite hzey;
          apply ∧ᵢ
          { assume h;
            refine ∧ₑ₂ (radd_Inl_iff xa ya A r B s)
              (∧ₑ₁ (radd_Inl_iff xa ya A r (pred B b s) s) h) }
          { assume h;
            refine ∧ₑ₂ (radd_Inl_iff xa ya A r (pred B b s) s)
              (∧ₑ₁ (radd_Inl_iff xa ya A r B s) h) } }
        { assume yb hyb hzey;
          rewrite hzey;
          have hybB : π (yb ∈ B) { refine pred_subset B b s yb hyb };
          apply ∧ᵢ
          { assume h;
            refine ∧ₑ₂ (radd_Inl_Inr_iff xa yb A r B s) (∧ᵢ hxa hybB) }
          { assume h;
            refine ∧ₑ₂ (radd_Inl_Inr_iff xa yb A r (pred B b s) s)
              (∧ᵢ hxa hyb) } } }
      { assume xb hxb hzex;
        rewrite hzex;
        have hxbB : π (xb ∈ B) { refine pred_subset B b s xb hxb };
        refine sumE y A (pred B b s)
          ((Pair (Inr xb) y ∈ radd A r (pred B b s) s)
           ⇔ (Pair (Inr xb) y ∈ radd A r B s)) hy _ _
        { assume ya hya hzey;
          rewrite hzey;
          apply ∧ᵢ
          { assume h;
            refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff xb ya A r (pred B b s) s) h) }
          { assume h;
            refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff xb ya A r B s) h) } }
        { assume yb hyb hzey;
          rewrite hzey;
          have hybB : π (yb ∈ B) { refine pred_subset B b s yb hyb };
          apply ∧ᵢ
          { assume h;
            have hc : π (xb ∈ pred B b s ∧ yb ∈ pred B b s ∧ Pair xb yb ∈ s)
              { refine ∧ₑ₁ (radd_Inr_iff xb yb A r (pred B b s) s) h };
            refine ∧ₑ₂ (radd_Inr_iff xb yb A r B s)
              (∧ᵢ hxbB (∧ᵢ hybB (∧ₑ₂ (∧ₑ₂ hc)))) }
          { assume h;
            have hc : π (xb ∈ B ∧ yb ∈ B ∧ Pair xb yb ∈ s)
              { refine ∧ₑ₁ (radd_Inr_iff xb yb A r B s) h };
            refine ∧ₑ₂ (radd_Inr_iff xb yb A r (pred B b s) s)
              (∧ᵢ hxb (∧ᵢ hyb (∧ₑ₂ (∧ₑ₂ hc)))) } } } };
  // Follow Isabelle: sym the iso so ordertype_eq needs well_ord of
  // A+pred(B,b,s) — from well_ord_radd + well_ord_subset via pred_subset.
  have hwoP : π (well_ord (pred B b s) s)
    { refine well_ord_subset B (pred B b s) s hwoB (pred_subset B b s) };
  have hwoSum : π (well_ord (sum A (pred B b s)) (radd A r (pred B b s) s))
    { refine well_ord_radd A r (pred B b s) s hwoA hwoP };
  refine ordertype_eq
    (converse (Lambda (sum A (pred B b s)) (λ z, z)))
    (pred (sum A B) (Inr b) (radd A r B s)) (radd A r B s)
    (sum A (pred B b s)) (radd A r (pred B b s) s)
    (ord_iso_sym (Lambda (sum A (pred B b s)) (λ z, z))
       (sum A (pred B b s)) (radd A r (pred B b s) s)
       (pred (sum A B) (Inr b) (radd A r B s)) (radd A r B s) hiso)
    hwoSum
end;

opaque symbol Ord_ordify (x : τ ι) :
  π (Ord (ordify x)) ≔
begin
  assume x;
  rewrite ordify_def;
  refine ∨ₑ (em (Ord x)) _ _
  { assume h; rewrite (If_P (Ord x) x empty h); refine h }
  { assume h; rewrite (If_not_P (Ord x) x empty h); refine Ord_0 }
end;

opaque symbol ordify_idem (x : τ ι) :
  π (ordify (ordify x) = ordify x) ≔
begin
  assume x;
  rewrite .[ordify (ordify x)] ordify_def;
  refine If_P (Ord (ordify x)) (ordify x) empty (Ord_ordify x)
end;

opaque symbol Ord_raw_oadd (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (raw_oadd i j)) ≔
begin
  assume i j hi hj;
  rewrite raw_oadd_def;
  refine Ord_ordertype (sum i j) (radd i (Memrel i) j (Memrel j))
    (well_ord_radd i (Memrel i) j (Memrel j)
      (well_ord_Memrel i hi) (well_ord_Memrel j hj))
end;

opaque symbol Ord_oadd (i j : τ ι) :
  π (Ord (oadd i j)) ≔
begin
  assume i j;
  rewrite oadd_def;
  refine Ord_raw_oadd (ordify i) (ordify j) (Ord_ordify i) (Ord_ordify j)
end;

opaque symbol raw_oadd_0 (i : τ ι) :
  π (Ord i) → π (raw_oadd i empty = i) ≔
begin
  assume i hi;
  rewrite raw_oadd_def;
  rewrite (ordertype_sum_0_eq i (Memrel i) (Memrel empty) (well_ord_Memrel i hi));
  refine ordertype_Memrel i hi
end;

opaque symbol oadd_0 (i : τ ι) :
  π (Ord i) → π (oadd i empty = i) ≔
begin
  assume i hi;
  rewrite oadd_def;
  rewrite ordify_def;
  rewrite ordify_def;
  rewrite (If_P (Ord i) i empty hi);
  rewrite (If_P (Ord empty) empty empty Ord_0);
  refine raw_oadd_0 i hi
end;

opaque symbol raw_oadd_0_left (i : τ ι) :
  π (Ord i) → π (raw_oadd empty i = i) ≔
begin
  assume i hi;
  rewrite raw_oadd_def;
  rewrite (ordertype_0_sum_eq i (Memrel i) (Memrel empty) (well_ord_Memrel i hi));
  refine ordertype_Memrel i hi
end;

opaque symbol oadd_0_left (i : τ ι) :
  π (Ord i) → π (oadd empty i = i) ≔
begin
  assume i hi;
  rewrite oadd_def;
  rewrite ordify_def;
  rewrite ordify_def;
  rewrite (If_P (Ord i) i empty hi);
  rewrite (If_P (Ord empty) empty empty Ord_0);
  refine raw_oadd_0_left i hi
end;

opaque symbol oadd_eq_if_raw_oadd (i j : τ ι) :
  π (oadd i j = If (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty)) ≔
begin
  assume i j;
  refine ∨ₑ (em (Ord i)) _ _
  { assume hi;
    rewrite (If_P (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty) hi);
    refine ∨ₑ (em (Ord j)) _ _
    { assume hj;
      rewrite (If_P (Ord j) (raw_oadd i j) i hj);
      rewrite oadd_def;
      rewrite ordify_def;
      rewrite ordify_def;
      rewrite (If_P (Ord i) i empty hi);
      rewrite (If_P (Ord j) j empty hj);
      reflexivity }
    { assume hj;
      rewrite (If_not_P (Ord j) (raw_oadd i j) i hj);
      rewrite oadd_def;
      rewrite ordify_def;
      rewrite ordify_def;
      rewrite (If_P (Ord i) i empty hi);
      rewrite (If_not_P (Ord j) j empty hj);
      refine raw_oadd_0 i hi } }
  { assume hi;
    rewrite (If_not_P (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty) hi);
    refine ∨ₑ (em (Ord j)) _ _
    { assume hj;
      rewrite (If_P (Ord j) j empty hj);
      rewrite oadd_def;
      rewrite ordify_def;
      rewrite ordify_def;
      rewrite (If_not_P (Ord i) i empty hi);
      rewrite (If_P (Ord j) j empty hj);
      refine raw_oadd_0_left j hj }
    { assume hj;
      rewrite (If_not_P (Ord j) j empty hj);
      rewrite oadd_def;
      rewrite ordify_def;
      rewrite ordify_def;
      rewrite (If_not_P (Ord i) i empty hi);
      rewrite (If_not_P (Ord j) j empty hj);
      refine raw_oadd_0 empty Ord_0 } }
end;

opaque symbol raw_oadd_eq_oadd (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (raw_oadd i j = oadd i j) ≔
begin
  assume i j hi hj;
  rewrite oadd_def;
  rewrite ordify_def;
  rewrite ordify_def;
  rewrite (If_P (Ord i) i empty hi);
  rewrite (If_P (Ord j) j empty hj);
  reflexivity
end;

// port-internal helper: trichotomy of ordinals expressed with lt.
private opaque symbol Ord_linear_lt3 (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (lt i j ∨ (i = j ∨ lt j i)) ≔
begin
  assume i j hOi hOj;
  refine ∨ₑ (Ord_linear i j hOi hOj) _ _
  { assume h; refine ∨ᵢ₁ (ltI i j h hOj) }
  { assume h;
    refine ∨ₑ h _ _
    { assume he; refine ∨ᵢ₂ (∨ᵢ₁ he) }
    { assume h2; refine ∨ᵢ₂ (∨ᵢ₂ (ltI j i h2 hOi)) } }
end;

opaque symbol lt_oadd1 (k i j : τ ι) :
  π (lt k i) → π (lt k (oadd i j)) ≔
begin
  assume k i j hlt;
  have hki : π (k ∈ i) { refine ltD k i hlt };
  have hOi : π (Ord i) { refine lt_Ord2 k i hlt };
  have hle : π (le k i) { refine leI k i hki hOi };
  have hOjj : π (Ord (ordify j)) { refine Ord_ordify j };
  have hwoi : π (well_ord i (Memrel i)) { refine well_ord_Memrel i hOi };
  have hwosum : π (well_ord (sum i (ordify j))
      (radd i (Memrel i) (ordify j) (Memrel (ordify j))))
    { refine well_ord_radd i (Memrel i) (ordify j) (Memrel (ordify j)) hwoi
        (well_ord_Memrel (ordify j) hOjj) };
  have hoadd : π (oadd i j
      = ordertype (sum i (ordify j)) (radd i (Memrel i) (ordify j) (Memrel (ordify j))))
    { rewrite oadd_def;
      rewrite .[ordify i] ordify_def;
      rewrite (If_P (Ord i) i empty hOi);
      refine raw_oadd_def i (ordify j) };
  have hprednlt : π (lt
      (ordertype (pred (sum i (ordify j)) (Inl k)
                   (radd i (Memrel i) (ordify j) (Memrel (ordify j))))
                 (radd i (Memrel i) (ordify j) (Memrel (ordify j))))
      (ordertype (sum i (ordify j)) (radd i (Memrel i) (ordify j) (Memrel (ordify j)))))
    { refine ordertype_pred_lt (sum i (ordify j))
        (radd i (Memrel i) (ordify j) (Memrel (ordify j))) (Inl k) hwosum
        (InlI k i (ordify j) hki) };
  have hV : π (ordertype (pred (sum i (ordify j)) (Inl k)
                   (radd i (Memrel i) (ordify j) (Memrel (ordify j))))
                 (radd i (Memrel i) (ordify j) (Memrel (ordify j))) = k)
    { have e1 : π (ordertype (pred (sum i (ordify j)) (Inl k)
                     (radd i (Memrel i) (ordify j) (Memrel (ordify j))))
                   (radd i (Memrel i) (ordify j) (Memrel (ordify j)))
                 = ordertype (pred i k (Memrel i)) (Memrel i))
        { refine ordertype_pred_Inl_eq k i (Memrel i) (ordify j) (Memrel (ordify j))
            hki hwoi };
      have e2 : π (ordertype (pred i k (Memrel i)) (Memrel i)
                   = ordertype k (Memrel i))
        { rewrite (lt_pred_Memrel k i hlt); reflexivity };
      have e3 : π (ordertype k (Memrel i) = k)
        { refine le_ordertype_Memrel k i hle };
      refine eq_trans e1 (eq_trans e2 e3) };
  have hlt2 : π (lt k
      (ordertype (sum i (ordify j)) (radd i (Memrel i) (ordify j) (Memrel (ordify j)))))
    { refine ind_eq (eq_sym hV)
        (λ w, lt w (ordertype (sum i (ordify j))
                     (radd i (Memrel i) (ordify j) (Memrel (ordify j))))) hprednlt };
  refine ind_eq hoadd (λ w, lt k w) hlt2
end;

opaque symbol oadd_le_self (i j : τ ι) :
  π (Ord i) → π (le i (oadd i j)) ≔
begin
  assume i j hOi;
  refine all_lt_imp_le (oadd i j) i (Ord_oadd i j) hOi _;
  assume x hx;
  refine ltD x (oadd i j) (lt_oadd1 x i j (ltI x i hx hOi))
end;

opaque symbol id_ord_iso_Memrel (A B : τ ι) :
  π (A ⊆ B) → π (id_fun A ∈ ord_iso A (Memrel A) A (Memrel B)) ≔
begin
  assume A B hAB;
  refine ord_isoI (id_fun A) A (Memrel A) A (Memrel B) (id_bij A) _;
  assume x hx y hy;
  have hix : π (fapply (id_fun A) x = x) { refine id_conv A x hx };
  have hiy : π (fapply (id_fun A) y = y) { refine id_conv A y hy };
  rewrite hix;
  rewrite hiy;
  apply ∧ᵢ
  { assume h;
    have hm : π (x ∈ A ∧ y ∈ A ∧ x ∈ y) { refine MemrelE x y A h };
    refine MemrelI x y B (∧ₑ₂ (∧ₑ₂ hm)) (hAB x hx) (hAB y hy) }
  { assume h;
    have hm : π (x ∈ B ∧ y ∈ B ∧ x ∈ y) { refine MemrelE x y B h };
    refine MemrelI x y A (∧ₑ₂ (∧ₑ₂ hm)) hx hy }
end;

opaque symbol subset_ord_iso_Memrel (f A B C r : τ ι) :
  π (f ∈ ord_iso A (Memrel B) C r) → π (A ⊆ B) →
  π (f ∈ ord_iso A (Memrel A) C r) ≔
begin
  assume f A B C r hf hAB;
  have hbij : π (f ∈ bij A C) { refine ord_iso_is_bij f A (Memrel B) C r hf };
  have hcond : π (Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ Memrel B) ⇔ (Pair (fapply f x) (fapply f y) ∈ r))))
    { refine ord_iso_memD f A (Memrel B) C r hf };
  refine ord_isoI f A (Memrel A) C r hbij _;
  assume x hx y hy;
  apply ∧ᵢ
  { assume h;
    have hm : π (x ∈ A ∧ y ∈ A ∧ x ∈ y) { refine MemrelE x y A h };
    refine ∧ₑ₁ (hcond x hx y hy)
      (MemrelI x y B (∧ₑ₂ (∧ₑ₂ hm)) (hAB x hx) (hAB y hy)) }
  { assume h;
    have hmB : π (Pair x y ∈ Memrel B) { refine ∧ₑ₂ (hcond x hx y hy) h };
    have hm : π (x ∈ B ∧ y ∈ B ∧ x ∈ y) { refine MemrelE x y B hmB };
    refine MemrelI x y A (∧ₑ₂ (∧ₑ₂ hm)) hx hy }
end;

opaque symbol restrict_ord_iso (f i A a r j : τ ι) :
  π (f ∈ ord_iso i (Memrel i) (pred A a r) r) → π (a ∈ A) → π (lt j i) →
  π (trans_on A r) →
  π (restrict f j ∈ ord_iso j (Memrel j) (pred A (fapply f j) r) r) ≔
begin
  assume f i A a r j hf haA hlt htrans;
  have hji : π (j ∈ i) { refine ltD j i hlt };
  have hbij : π (f ∈ bij i (pred A a r))
    { refine ord_iso_is_bij f i (Memrel i) (pred A a r) r hf };
  have hfun : π (f ∈ Pi i (λ _, pred A a r))
    { refine bij_is_fun f i (pred A a r) hbij };
  have hfj : π (fapply f j ∈ pred A a r)
    { refine fapply_type f j i (λ _, pred A a r) hfun hji };
  have hfjA : π (fapply f j ∈ A) { refine pred_subset A a r (fapply f j) hfj };
  have hfja_r : π (Pair (fapply f j) a ∈ r)
    { refine ∧ₑ₁ (∧ₑ₁ (pred_iff (fapply f j) A a r) hfj) };
  have hrp : π (restrict f (pred i j (Memrel i))
      ∈ ord_iso (pred i j (Memrel i)) (Memrel i)
                (pred (pred A a r) (fapply f j) r) r)
    { refine ord_iso_restrict_pred f i (Memrel i) (pred A a r) r j hf hji };
  have hpe : π (pred i j (Memrel i) = j) { refine lt_pred_Memrel j i hlt };
  have hpe2 : π (pred (pred A a r) (fapply f j) r = pred A (fapply f j) r)
    { refine trans_pred_pred_eq A r a (fapply f j) htrans hfja_r haA hfjA };
  have hint : π (restrict f j ∈ ord_iso j (Memrel i) (pred A (fapply f j) r) r)
    { refine ind_eq (eq_sym hpe2)
        (λ w, restrict f j ∈ ord_iso j (Memrel i) w r)
        (ind_eq (eq_sym hpe)
          (λ w, restrict f w ∈ ord_iso w (Memrel i)
                  (pred (pred A a r) (fapply f j) r) r)
          hrp) };
  refine subset_ord_iso_Memrel (restrict f j) j i (pred A (fapply f j) r) r hint
    (OrdmemD i j hji (lt_Ord2 j i hlt))
end;

opaque symbol restrict_ord_iso2 (f A a r i j : τ ι) :
  π (f ∈ ord_iso (pred A a r) r i (Memrel i)) → π (a ∈ A) → π (lt j i) →
  π (trans_on A r) →
  π (converse (restrict (converse f) j)
     ∈ ord_iso (pred A (fapply (converse f) j) r) r j (Memrel j)) ≔
begin
  assume f A a r i j hf haA hlt htrans;
  have hcf : π (converse f ∈ ord_iso i (Memrel i) (pred A a r) r)
    { refine ord_iso_sym f (pred A a r) r i (Memrel i) hf };
  have hrest : π (restrict (converse f) j
      ∈ ord_iso j (Memrel j) (pred A (fapply (converse f) j) r) r)
    { refine restrict_ord_iso (converse f) i A a r j hcf haA hlt htrans };
  refine ord_iso_sym (restrict (converse f) j) j (Memrel j)
    (pred A (fapply (converse f) j) r) r hrest
end;

opaque symbol ordertype_sum_Memrel (A r k j : τ ι) :
  π (well_ord A r) → π (lt k j) →
  π (ordertype (sum A k) (radd A r k (Memrel j))
     = ordertype (sum A k) (radd A r k (Memrel k))) ≔
begin
  assume A r k j hwoA hlt;
  have hkj : π (k ∈ j) { refine ltD k j hlt };
  have hOk : π (Ord k) { refine lt_Ord k j hlt };
  have hOj : π (Ord j) { refine lt_Ord2 k j hlt };
  have hksub : π (k ⊆ j) { refine OrdmemD j k hkj hOj };
  have hg : π (converse (id_fun k) ∈ ord_iso k (Memrel j) k (Memrel k))
    { refine ord_iso_sym (id_fun k) k (Memrel k) k (Memrel j)
        (id_ord_iso_Memrel k j hksub) };
  refine ordertype_eq _
    (sum A k) (radd A r k (Memrel j)) (sum A k) (radd A r k (Memrel k))
    (sum_ord_iso_cong (id_fun A) (converse (id_fun k))
       A r A r k (Memrel j) k (Memrel k) (ord_iso_refl A r) hg)
    (well_ord_radd A r k (Memrel k) hwoA (well_ord_Memrel k hOk))
end;

opaque symbol oadd_lt_mono2 (k j i : τ ι) :
  π (lt k j) → π (lt (oadd i k) (oadd i j)) ≔
begin
  assume k j i hlt;
  have hkj : π (k ∈ j) { refine ltD k j hlt };
  have hOk : π (Ord k) { refine lt_Ord k j hlt };
  have hOj : π (Ord j) { refine lt_Ord2 k j hlt };
  have hOii : π (Ord (ordify i)) { refine Ord_ordify i };
  have hwoii : π (well_ord (ordify i) (Memrel (ordify i)))
    { refine well_ord_Memrel (ordify i) hOii };
  have hwoj : π (well_ord j (Memrel j)) { refine well_ord_Memrel j hOj };
  have hwoSumj : π (well_ord (sum (ordify i) j)
      (radd (ordify i) (Memrel (ordify i)) j (Memrel j)))
    { refine well_ord_radd (ordify i) (Memrel (ordify i)) j (Memrel j) hwoii hwoj };
  have hoaddj : π (oadd i j
      = ordertype (sum (ordify i) j)
                  (radd (ordify i) (Memrel (ordify i)) j (Memrel j)))
    { rewrite oadd_def;
      rewrite .[ordify j] ordify_def;
      rewrite (If_P (Ord j) j empty hOj);
      refine raw_oadd_def (ordify i) j };
  have hoaddk : π (oadd i k
      = ordertype (sum (ordify i) k)
                  (radd (ordify i) (Memrel (ordify i)) k (Memrel k)))
    { rewrite oadd_def;
      rewrite .[ordify k] ordify_def;
      rewrite (If_P (Ord k) k empty hOk);
      refine raw_oadd_def (ordify i) k };
  have hprednlt : π (lt
      (ordertype (pred (sum (ordify i) j) (Inr k)
                   (radd (ordify i) (Memrel (ordify i)) j (Memrel j)))
                 (radd (ordify i) (Memrel (ordify i)) j (Memrel j)))
      (ordertype (sum (ordify i) j)
                 (radd (ordify i) (Memrel (ordify i)) j (Memrel j))))
    { refine ordertype_pred_lt (sum (ordify i) j)
        (radd (ordify i) (Memrel (ordify i)) j (Memrel j)) (Inr k) hwoSumj
        (InrI k (ordify i) j hkj) };
  have hVeq : π (ordertype (pred (sum (ordify i) j) (Inr k)
                   (radd (ordify i) (Memrel (ordify i)) j (Memrel j)))
                 (radd (ordify i) (Memrel (ordify i)) j (Memrel j))
               = oadd i k)
    { have e1 : π (ordertype (pred (sum (ordify i) j) (Inr k)
                     (radd (ordify i) (Memrel (ordify i)) j (Memrel j)))
                   (radd (ordify i) (Memrel (ordify i)) j (Memrel j))
                 = ordertype (sum (ordify i) (pred j k (Memrel j)))
                     (radd (ordify i) (Memrel (ordify i)) (pred j k (Memrel j)) (Memrel j)))
        { refine ordertype_pred_Inr_eq k (ordify i) (Memrel (ordify i)) j (Memrel j)
            hkj hwoii hwoj };
      have e2 : π (ordertype (sum (ordify i) (pred j k (Memrel j)))
                     (radd (ordify i) (Memrel (ordify i)) (pred j k (Memrel j)) (Memrel j))
                 = ordertype (sum (ordify i) k)
                     (radd (ordify i) (Memrel (ordify i)) k (Memrel j)))
        { rewrite (lt_pred_Memrel k j hlt); reflexivity };
      have e3 : π (ordertype (sum (ordify i) k)
                     (radd (ordify i) (Memrel (ordify i)) k (Memrel j))
                 = ordertype (sum (ordify i) k)
                     (radd (ordify i) (Memrel (ordify i)) k (Memrel k)))
        { refine ordertype_sum_Memrel (ordify i) (Memrel (ordify i)) k j hwoii hlt };
      refine eq_trans e1 (eq_trans e2 (eq_trans e3 (eq_sym hoaddk))) };
  have hlt2 : π (lt (oadd i k)
      (ordertype (sum (ordify i) j)
                 (radd (ordify i) (Memrel (ordify i)) j (Memrel j))))
    { refine ind_eq (eq_sym hVeq)
        (λ w, lt w (ordertype (sum (ordify i) j)
                     (radd (ordify i) (Memrel (ordify i)) j (Memrel j)))) hprednlt };
  refine ind_eq hoaddj (λ w, lt (oadd i k) w) hlt2
end;

opaque symbol oadd_lt_cancel2 (i j k : τ ι) :
  π (lt (oadd i j) (oadd i k)) → π (Ord j) → π (lt j k) ≔
begin
  assume i j k hlt hOj;
  refine ∨ₑ (em (Ord k)) _ _
  { assume hOk;
    refine ∨ₑ (Ord_linear_lt3 j k hOj hOk) _ _
    { assume hjk; refine hjk }
    { assume h;
      refine ∨ₑ h _ _
      { assume he;
        have hlt2 : π (lt (oadd i k) (oadd i k))
          { refine ind_eq (eq_sym he) (λ w, lt (oadd i w) (oadd i k)) hlt };
        refine ⊥ₑ (lt_irrefl (oadd i k) hlt2) }
      { assume hkj;
        have hlt2 : π (lt (oadd i k) (oadd i j)) { refine oadd_lt_mono2 k j i hkj };
        refine ⊥ₑ (lt_not_sym (oadd i j) (oadd i k) hlt hlt2) } } }
  { assume hnk;
    refine ∨ₑ (em (Ord i)) _ _
    { assume hOi;
      have hoik : π (oadd i k = i)
        { refine eq_trans (oadd_eq_if_raw_oadd i k) _;
          rewrite (If_P (Ord i) (If (Ord k) (raw_oadd i k) i) (If (Ord k) k empty) hOi);
          refine If_not_P (Ord k) (raw_oadd i k) i hnk };
      have hlti : π (lt (oadd i j) i)
        { refine ind_eq (eq_sym hoik) (λ w, lt (oadd i j) w) hlt };
      refine ⊥ₑ (lt_irrefl i
        (lt_trans1 i (oadd i j) i (oadd_le_self i j hOi) hlti)) }
    { assume hni;
      have hoik : π (oadd i k = empty)
        { refine eq_trans (oadd_eq_if_raw_oadd i k) _;
          rewrite (If_not_P (Ord i) (If (Ord k) (raw_oadd i k) i) (If (Ord k) k empty) hni);
          refine If_not_P (Ord k) k empty hnk };
      have hlt0 : π (lt (oadd i j) empty)
        { refine ind_eq (eq_sym hoik) (λ w, lt (oadd i j) w) hlt };
      refine ⊥ₑ (not_lt0 (oadd i j) hlt0) } }
end;

opaque symbol oadd_lt_iff2 (i j k : τ ι) :
  π (Ord j) → π (lt (oadd i j) (oadd i k) ⇔ lt j k) ≔
begin
  assume i j k hOj;
  apply ∧ᵢ
  { assume h; refine oadd_lt_cancel2 i j k h hOj }
  { assume h; refine oadd_lt_mono2 j k i h }
end;

opaque symbol oadd_inject (i j k : τ ι) :
  π (oadd i j = oadd i k) → π (Ord j) → π (Ord k) → π (j = k) ≔
begin
  assume i j k heq hOj hOk;
  refine ∨ₑ (em (Ord i)) _ _
  { assume hOi;
    refine ∨ₑ (Ord_linear_lt3 j k hOj hOk) _ _
    { assume hjk;
      have hlt : π (lt (oadd i j) (oadd i k)) { refine oadd_lt_mono2 j k i hjk };
      refine ⊥ₑ (lt_irrefl (oadd i k)
        (ind_eq (eq_sym heq) (λ w, lt w (oadd i k)) hlt)) }
    { assume h;
      refine ∨ₑ h _ _
      { assume he; refine he }
      { assume hkj;
        have hlt : π (lt (oadd i k) (oadd i j)) { refine oadd_lt_mono2 k j i hkj };
        refine ⊥ₑ (lt_irrefl (oadd i k)
          (ind_eq (eq_sym heq) (λ w, lt (oadd i k) w) hlt)) } } }
  { assume hni;
    have hoj : π (oadd i j = j)
      { refine eq_trans (oadd_eq_if_raw_oadd i j) _;
        rewrite (If_not_P (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty) hni);
        refine If_P (Ord j) j empty hOj };
    have hok : π (oadd i k = k)
      { refine eq_trans (oadd_eq_if_raw_oadd i k) _;
        rewrite (If_not_P (Ord i) (If (Ord k) (raw_oadd i k) i) (If (Ord k) k empty) hni);
        refine If_P (Ord k) k empty hOk };
    refine eq_trans (eq_sym hoj) (eq_trans heq hok) }
end;

opaque symbol lt_oadd_disj (k i j : τ ι) :
  π (lt k (oadd i j)) → π (lt k i ∨ Bex j (λ l, k = oadd i l)) ≔
begin
  assume k i j hlt;
  refine ∨ₑ (em (Ord i)) _ _
  { assume hOi;
    refine ∨ₑ (em (Ord j)) _ _
    { assume hOj;
      have hwoi : π (well_ord i (Memrel i)) { refine well_ord_Memrel i hOi };
      have hwoj : π (well_ord j (Memrel j)) { refine well_ord_Memrel j hOj };
      have hwosum : π (well_ord (sum i j) (radd i (Memrel i) j (Memrel j)))
        { refine well_ord_radd i (Memrel i) j (Memrel j) hwoi hwoj };
      have hoadd : π (oadd i j
          = ordertype (sum i j) (radd i (Memrel i) j (Memrel j)))
        { refine eq_trans (eq_sym (raw_oadd_eq_oadd i j hOi hOj)) (raw_oadd_def i j) };
      have hlt2 : π (lt k (ordertype (sum i j) (radd i (Memrel i) j (Memrel j))))
        { refine ind_eq (eq_sym hoadd) (λ w, lt k w) hlt };
      have hunf : π (ordertype (sum i j) (radd i (Memrel i) j (Memrel j))
          = RepFun (sum i j)
              (λ x, ordertype (pred (sum i j) x (radd i (Memrel i) j (Memrel j)))
                    (radd i (Memrel i) j (Memrel j))))
        { refine ordertype_pred_unfold (sum i j)
            (radd i (Memrel i) j (Memrel j)) hwosum };
      have hkR : π (k ∈ RepFun (sum i j)
              (λ x, ordertype (pred (sum i j) x (radd i (Memrel i) j (Memrel j)))
                    (radd i (Memrel i) j (Memrel j))))
        { refine ind_eq (eq_sym hunf) (λ w, k ∈ w)
            (ltD k (ordertype (sum i j) (radd i (Memrel i) j (Memrel j))) hlt2) };
      have hbex : π (Bex (sum i j)
              (λ x, k = ordertype (pred (sum i j) x (radd i (Memrel i) j (Memrel j)))
                    (radd i (Memrel i) j (Memrel j))))
        { refine ∧ₑ₁ (RepFun_iff k (sum i j)
            (λ x, ordertype (pred (sum i j) x (radd i (Memrel i) j (Memrel j)))
                  (radd i (Memrel i) j (Memrel j)))) hkR };
      refine ∃ₑ hbex _;
      assume x hx;
      have hxs : π (x ∈ sum i j) { refine ∧ₑ₁ hx };
      have heqx : π (k = ordertype (pred (sum i j) x (radd i (Memrel i) j (Memrel j)))
                    (radd i (Memrel i) j (Memrel j))) { refine ∧ₑ₂ hx };
      refine sumE x i j (lt k i ∨ Bex j (λ l, k = oadd i l)) hxs _ _
      { assume a haI hxe;
        have e1 : π (ordertype (pred (sum i j) (Inl a) (radd i (Memrel i) j (Memrel j)))
                       (radd i (Memrel i) j (Memrel j))
                     = ordertype (pred i a (Memrel i)) (Memrel i))
          { refine ordertype_pred_Inl_eq a i (Memrel i) j (Memrel j) haI hwoi };
        have hai_lt : π (lt a i) { refine ltI a i haI hOi };
        have e2 : π (ordertype (pred i a (Memrel i)) (Memrel i)
                     = ordertype a (Memrel i))
          { rewrite (lt_pred_Memrel a i hai_lt); reflexivity };
        have e3 : π (ordertype a (Memrel i) = a)
          { refine le_ordertype_Memrel a i (leI a i haI hOi) };
        have h0 : π (k = ordertype (pred (sum i j) (Inl a) (radd i (Memrel i) j (Memrel j)))
                      (radd i (Memrel i) j (Memrel j)))
          { refine ind_eq (eq_sym hxe)
              (λ w, k = ordertype (pred (sum i j) w (radd i (Memrel i) j (Memrel j)))
                    (radd i (Memrel i) j (Memrel j))) heqx };
        have hka : π (k = a)
          { refine eq_trans h0 (eq_trans e1 (eq_trans e2 e3)) };
        refine ∨ᵢ₁ (ind_eq hka (λ w, lt w i) hai_lt) }
      { assume b hbJ hxe;
        have hbj_lt : π (lt b j) { refine ltI b j hbJ hOj };
        have hOb : π (Ord b) { refine Ord_in_Ord j b hOj hbJ };
        have e1 : π (ordertype (pred (sum i j) (Inr b) (radd i (Memrel i) j (Memrel j)))
                       (radd i (Memrel i) j (Memrel j))
                     = ordertype (sum i (pred j b (Memrel j)))
                         (radd i (Memrel i) (pred j b (Memrel j)) (Memrel j)))
          { refine ordertype_pred_Inr_eq b i (Memrel i) j (Memrel j) hbJ hwoi hwoj };
        have e2 : π (ordertype (sum i (pred j b (Memrel j)))
                       (radd i (Memrel i) (pred j b (Memrel j)) (Memrel j))
                     = ordertype (sum i b) (radd i (Memrel i) b (Memrel j)))
          { rewrite (lt_pred_Memrel b j hbj_lt); reflexivity };
        have e3 : π (ordertype (sum i b) (radd i (Memrel i) b (Memrel j))
                     = ordertype (sum i b) (radd i (Memrel i) b (Memrel b)))
          { refine ordertype_sum_Memrel i (Memrel i) b j hwoi hbj_lt };
        have e4 : π (ordertype (sum i b) (radd i (Memrel i) b (Memrel b)) = raw_oadd i b)
          { refine eq_sym (raw_oadd_def i b) };
        have e5 : π (raw_oadd i b = oadd i b) { refine raw_oadd_eq_oadd i b hOi hOb };
        have h0 : π (k = ordertype (pred (sum i j) (Inr b) (radd i (Memrel i) j (Memrel j)))
                      (radd i (Memrel i) j (Memrel j)))
          { refine ind_eq (eq_sym hxe)
              (λ w, k = ordertype (pred (sum i j) w (radd i (Memrel i) j (Memrel j)))
                    (radd i (Memrel i) j (Memrel j))) heqx };
        have hkb : π (k = oadd i b)
          { refine eq_trans h0
              (eq_trans e1 (eq_trans e2 (eq_trans e3 (eq_trans e4 e5)))) };
        refine ∨ᵢ₂ (∃ᵢ b (∧ᵢ hbJ hkb)) } }
    { assume hnOj;
      have hoij : π (oadd i j = i)
        { refine eq_trans (oadd_eq_if_raw_oadd i j) _;
          rewrite (If_P (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty) hOi);
          refine If_not_P (Ord j) (raw_oadd i j) i hnOj };
      refine ∨ᵢ₁ (ind_eq (eq_sym hoij) (λ w, lt k w) hlt) } }
  { assume hnOi;
    refine ∨ₑ (em (Ord j)) _ _
    { assume hOj;
      have hoij : π (oadd i j = j)
        { refine eq_trans (oadd_eq_if_raw_oadd i j) _;
          rewrite (If_not_P (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty) hnOi);
          refine If_P (Ord j) j empty hOj };
      have hltj : π (lt k j) { refine ind_eq (eq_sym hoij) (λ w, lt k w) hlt };
      have hkj : π (k ∈ j) { refine ltD k j hltj };
      have hOk : π (Ord k) { refine Ord_in_Ord j k hOj hkj };
      have hoik : π (oadd i k = k)
        { refine eq_trans (oadd_eq_if_raw_oadd i k) _;
          rewrite (If_not_P (Ord i) (If (Ord k) (raw_oadd i k) i) (If (Ord k) k empty) hnOi);
          refine If_P (Ord k) k empty hOk };
      refine ∨ᵢ₂ (∃ᵢ k (∧ᵢ hkj (eq_sym hoik))) }
    { assume hnOj;
      have hoij : π (oadd i j = empty)
        { refine eq_trans (oadd_eq_if_raw_oadd i j) _;
          rewrite (If_not_P (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty) hnOi);
          refine If_not_P (Ord j) j empty hnOj };
      refine ⊥ₑ (not_lt0 k (ind_eq (eq_sym hoij) (λ w, lt k w) hlt)) } }
end;

// port-internal helper: ordify of an ordinal is itself.
private opaque symbol ordify_Ord_eq (x : τ ι) : π (Ord x) → π (ordify x = x) ≔
begin
  assume x hOx;
  rewrite ordify_def;
  refine If_P (Ord x) x empty hOx
end;

// port-internal helper: oadd depends only on the ordify of its arguments.
private opaque symbol oadd_ordify_eq (a b : τ ι) :
  π (oadd a b = oadd (ordify a) (ordify b)) ≔
begin
  assume a b;
  refine eq_trans (oadd_def a b) (eq_sym _);
  refine eq_trans (oadd_def (ordify a) (ordify b)) _;
  rewrite (ordify_idem a);
  rewrite (ordify_idem b);
  reflexivity
end;

// port-internal helper: oadd of two ordinals in ordertype form.
private opaque symbol oadd_ot_eq (a b : τ ι) :
  π (Ord a) → π (Ord b) →
  π (oadd a b = ordertype (sum a b) (radd a (Memrel a) b (Memrel b))) ≔
begin
  assume a b hOa hOb;
  refine eq_trans (eq_sym (raw_oadd_eq_oadd a b hOa hOb)) (raw_oadd_def a b)
end;

// port-internal helper: associativity of oadd for ordinals (the real content).
private opaque symbol oadd_assoc_Ord (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord k) →
  π (oadd (oadd i j) k = oadd i (oadd j k)) ≔
begin
  assume i j k hOi hOj hOk;
  have hOij : π (Ord (oadd i j)) { refine Ord_oadd i j };
  have hOjk : π (Ord (oadd j k)) { refine Ord_oadd j k };
  have woi : π (well_ord i (Memrel i)) { refine well_ord_Memrel i hOi };
  have woj : π (well_ord j (Memrel j)) { refine well_ord_Memrel j hOj };
  have wok : π (well_ord k (Memrel k)) { refine well_ord_Memrel k hOk };
  have woij : π (well_ord (sum i j) (radd i (Memrel i) j (Memrel j)))
    { refine well_ord_radd i (Memrel i) j (Memrel j) woi woj };
  have wojk : π (well_ord (sum j k) (radd j (Memrel j) k (Memrel k)))
    { refine well_ord_radd j (Memrel j) k (Memrel k) woj wok };
  have hOP : π (Ord (ordertype (sum i j) (radd i (Memrel i) j (Memrel j))))
    { refine Ord_ordertype (sum i j) (radd i (Memrel i) j (Memrel j)) woij };
  have hOQ : π (Ord (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))))
    { refine Ord_ordertype (sum j k) (radd j (Memrel j) k (Memrel k)) wojk };
  // unfold both sides to ordertype form
  rewrite (oadd_ot_eq (oadd i j) k hOij hOk);
  rewrite (oadd_ot_eq i (oadd j k) hOi hOjk);
  rewrite (oadd_ot_eq i j hOi hOj);
  rewrite (oadd_ot_eq j k hOj hOk);
  // Goal: ortype(sum P k, radd(P, Memrel P, k, Memrel k)) = ortype(sum i Q, radd(i, Memrel i, Q, Memrel Q))
  //   with P = ortype(sum i j, radd..), Q = ortype(sum j k, radd..)
  have step1 : π (ordertype (sum (sum i j) k)
                     (radd (sum i j) (radd i (Memrel i) j (Memrel j)) k (Memrel k))
      = ordertype (sum (ordertype (sum i j) (radd i (Memrel i) j (Memrel j))) k)
          (radd (ordertype (sum i j) (radd i (Memrel i) j (Memrel j)))
                (Memrel (ordertype (sum i j) (radd i (Memrel i) j (Memrel j)))) k (Memrel k)))
    { refine ordertype_eq _
        (sum (sum i j) k) (radd (sum i j) (radd i (Memrel i) j (Memrel j)) k (Memrel k))
        (sum (ordertype (sum i j) (radd i (Memrel i) j (Memrel j))) k)
        (radd (ordertype (sum i j) (radd i (Memrel i) j (Memrel j)))
              (Memrel (ordertype (sum i j) (radd i (Memrel i) j (Memrel j)))) k (Memrel k))
        (sum_ord_iso_cong (ordermap (sum i j) (radd i (Memrel i) j (Memrel j))) (id_fun k)
          (sum i j) (radd i (Memrel i) j (Memrel j))
          (ordertype (sum i j) (radd i (Memrel i) j (Memrel j)))
          (Memrel (ordertype (sum i j) (radd i (Memrel i) j (Memrel j))))
          k (Memrel k) k (Memrel k)
          (ordertype_ord_iso (sum i j) (radd i (Memrel i) j (Memrel j)) woij)
          (ord_iso_refl k (Memrel k)))
        (well_ord_radd (ordertype (sum i j) (radd i (Memrel i) j (Memrel j)))
          (Memrel (ordertype (sum i j) (radd i (Memrel i) j (Memrel j)))) k (Memrel k)
          (well_ord_Memrel (ordertype (sum i j) (radd i (Memrel i) j (Memrel j))) hOP) wok) };
  have step2 : π (ordertype (sum (sum i j) k)
                     (radd (sum i j) (radd i (Memrel i) j (Memrel j)) k (Memrel k))
      = ordertype (sum i (sum j k))
          (radd i (Memrel i) (sum j k) (radd j (Memrel j) k (Memrel k))))
    { refine ordertype_eq _
        (sum (sum i j) k) (radd (sum i j) (radd i (Memrel i) j (Memrel j)) k (Memrel k))
        (sum i (sum j k)) (radd i (Memrel i) (sum j k) (radd j (Memrel j) k (Memrel k)))
        (sum_assoc_ord_iso i (Memrel i) j (Memrel j) k (Memrel k))
        (well_ord_radd i (Memrel i) (sum j k) (radd j (Memrel j) k (Memrel k)) woi wojk) };
  have step3 : π (ordertype (sum i (sum j k))
                     (radd i (Memrel i) (sum j k) (radd j (Memrel j) k (Memrel k)))
      = ordertype (sum i (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))))
          (radd i (Memrel i) (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))
                (Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))))))
    { refine ordertype_eq _
        (sum i (sum j k)) (radd i (Memrel i) (sum j k) (radd j (Memrel j) k (Memrel k)))
        (sum i (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))))
        (radd i (Memrel i) (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))
              (Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))))
        (sum_ord_iso_cong (id_fun i) (ordermap (sum j k) (radd j (Memrel j) k (Memrel k)))
          i (Memrel i) i (Memrel i)
          (sum j k) (radd j (Memrel j) k (Memrel k))
          (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))
          (Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))))
          (ord_iso_refl i (Memrel i))
          (ordertype_ord_iso (sum j k) (radd j (Memrel j) k (Memrel k)) wojk))
        (well_ord_radd i (Memrel i) (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))
          (Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))) woi
          (well_ord_Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))) hOQ)) };
  refine eq_trans (eq_sym step1) (eq_trans step2 step3)
end;

opaque symbol oadd_assoc (i j k : τ ι) :
  π (oadd (oadd i j) k = oadd i (oadd j k)) ≔
begin
  assume i j k;
  have hOi : π (Ord (ordify i)) { refine Ord_ordify i };
  have hOj : π (Ord (ordify j)) { refine Ord_ordify j };
  have hOk : π (Ord (ordify k)) { refine Ord_ordify k };
  // reduce all to ordify'd (ordinal) arguments
  rewrite (oadd_ordify_eq (oadd i j) k);
  rewrite (oadd_ordify_eq i (oadd j k));
  rewrite (oadd_ordify_eq i j);
  rewrite (oadd_ordify_eq j k);
  rewrite (ordify_Ord_eq (oadd (ordify i) (ordify j)) (Ord_oadd (ordify i) (ordify j)));
  rewrite (ordify_Ord_eq (oadd (ordify j) (ordify k)) (Ord_oadd (ordify j) (ordify k)));
  refine oadd_assoc_Ord (ordify i) (ordify j) (ordify k) hOi hOj hOk
end;

opaque symbol oadd_unfold (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (oadd i j = Un i (Union (RepFun j (λ k, singleton (oadd i k))))) ≔
begin
  assume i j hOi hOj;
  refine equality_iffI (oadd i j)
    (Un i (Union (RepFun j (λ k, singleton (oadd i k))))) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hlt : π (lt x (oadd i j)) { refine ltI x (oadd i j) hx (Ord_oadd i j) };
    have hdisj : π (lt x i ∨ Bex j (λ l, x = oadd i l))
      { refine lt_oadd_disj x i j hlt };
    refine ∨ₑ hdisj _ _
    { assume hxi;
      refine UnI1 x i (Union (RepFun j (λ k, singleton (oadd i k)))) (ltD x i hxi) }
    { assume hbex;
      refine ∃ₑ hbex _;
      assume l hl;
      have hlj : π (l ∈ j) { refine ∧ₑ₁ hl };
      have hxeq : π (x = oadd i l) { refine ∧ₑ₂ hl };
      refine UnI2 x i (Union (RepFun j (λ k, singleton (oadd i k)))) _;
      refine UnionI x (singleton (oadd i l))
        (RepFun j (λ k, singleton (oadd i k))) _ _
      { refine ind_eq hxeq (λ w, w ∈ singleton (oadd i l)) (singletonI (oadd i l)) }
      { refine RepFunI l j (λ k, singleton (oadd i k)) hlj } } }
  { assume hx;
    have hdisj : π (x ∈ i ∨ x ∈ Union (RepFun j (λ k, singleton (oadd i k))))
      { refine UnE x i (Union (RepFun j (λ k, singleton (oadd i k)))) hx };
    refine ∨ₑ hdisj _ _
    { assume hxi;
      refine ltD x (oadd i j) (lt_oadd1 x i j (ltI x i hxi hOi)) }
    { assume hxU;
      have hbex : π (Bex (RepFun j (λ k, singleton (oadd i k))) (λ B, x ∈ B))
        { refine UnionE x (RepFun j (λ k, singleton (oadd i k))) hxU };
      refine ∃ₑ hbex _;
      assume B hB;
      have hBrep : π (B ∈ RepFun j (λ k, singleton (oadd i k))) { refine ∧ₑ₁ hB };
      have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
      have hbex2 : π (Bex j (λ k, B = singleton (oadd i k)))
        { refine ∧ₑ₁ (RepFun_iff B j (λ k, singleton (oadd i k))) hBrep };
      refine ∃ₑ hbex2 _;
      assume l hl;
      have hlj : π (l ∈ j) { refine ∧ₑ₁ hl };
      have hBeq : π (B = singleton (oadd i l)) { refine ∧ₑ₂ hl };
      have hxsing : π (x ∈ singleton (oadd i l))
        { refine ind_eq (eq_sym hBeq) (λ w, x ∈ w) hxB };
      have hxeq : π (x = oadd i l)
        { refine ∧ₑ₁ (singleton_iff x (oadd i l)) hxsing };
      have hlt : π (lt (oadd i l) (oadd i j))
        { refine oadd_lt_mono2 l j i (ltI l j hlj hOj) };
      refine ind_eq hxeq (λ w, w ∈ oadd i j) (ltD (oadd i l) (oadd i j) hlt) } }
end;

opaque symbol oadd_1 (i : τ ι) :
  π (Ord i) → π (oadd i (succ empty) = succ i) ≔
begin
  assume i hOi;
  refine equality_iffI (oadd i (succ empty)) (succ i) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hlt : π (lt x (oadd i (succ empty)))
      { refine ltI x (oadd i (succ empty)) hx (Ord_oadd i (succ empty)) };
    have hdisj : π (lt x i ∨ Bex (succ empty) (λ l, x = oadd i l))
      { refine lt_oadd_disj x i (succ empty) hlt };
    refine ∨ₑ hdisj _ _
    { assume hxi;
      refine ∧ₑ₂ (succ_iff x i) (∨ᵢ₂ (ltD x i hxi)) }
    { assume hbex;
      refine ∃ₑ hbex _;
      assume l hl;
      have hl1 : π (l ∈ succ empty) { refine ∧ₑ₁ hl };
      have hxeq : π (x = oadd i l) { refine ∧ₑ₂ hl };
      have hld : π (l = empty ∨ l ∈ empty) { refine ∧ₑ₁ (succ_iff l empty) hl1 };
      have hle : π (l = empty)
        { refine ∨ₑ hld _ _
          { assume h; refine h }
          { assume h; refine ⊥ₑ (emptyE l h) } };
      have hxi : π (x = i)
        { refine eq_trans hxeq
            (eq_trans (ind_eq hle (λ w, oadd i w = oadd i empty)
                        (eq_refl (oadd i empty))) (oadd_0 i hOi)) };
      refine ∧ₑ₂ (succ_iff x i) (∨ᵢ₁ hxi) } }
  { assume hx;
    have hdisj : π (x = i ∨ x ∈ i) { refine ∧ₑ₁ (succ_iff x i) hx };
    refine ∨ₑ hdisj _ _
    { assume hxeq;
      have hlt0 : π (lt empty (succ empty))
        { refine ltI empty (succ empty) (succI1 empty) (Ord_succ empty Ord_0) };
      have hltmono : π (lt (oadd i empty) (oadd i (succ empty)))
        { refine oadd_lt_mono2 empty (succ empty) i hlt0 };
      have hmem : π (oadd i empty ∈ oadd i (succ empty))
        { refine ltD (oadd i empty) (oadd i (succ empty)) hltmono };
      have hxoi : π (x = oadd i empty) { refine eq_trans hxeq (eq_sym (oadd_0 i hOi)) };
      refine ind_eq hxoi (λ w, w ∈ oadd i (succ empty)) hmem }
    { assume hxi;
      refine ltD x (oadd i (succ empty)) (lt_oadd1 x i (succ empty) (ltI x i hxi hOi)) } }
end;

opaque symbol oadd_succ (i j : τ ι) :
  π (Ord j) → π (oadd i (succ j) = succ (oadd i j)) ≔
begin
  assume i j hOj;
  refine equality_iffI (oadd i (succ j)) (succ (oadd i j)) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hlt : π (lt x (oadd i (succ j)))
      { refine ltI x (oadd i (succ j)) hx (Ord_oadd i (succ j)) };
    have hdisj : π (lt x i ∨ Bex (succ j) (λ l, x = oadd i l))
      { refine lt_oadd_disj x i (succ j) hlt };
    refine ∨ₑ hdisj _ _
    { assume hxi;
      have hmem : π (x ∈ oadd i j) { refine ltD x (oadd i j) (lt_oadd1 x i j hxi) };
      refine ∧ₑ₂ (succ_iff x (oadd i j)) (∨ᵢ₂ hmem) }
    { assume hbex;
      refine ∃ₑ hbex _;
      assume l hl;
      have hlsj : π (l ∈ succ j) { refine ∧ₑ₁ hl };
      have hxeq : π (x = oadd i l) { refine ∧ₑ₂ hl };
      have hld : π (l = j ∨ l ∈ j) { refine ∧ₑ₁ (succ_iff l j) hlsj };
      refine ∨ₑ hld _ _
      { assume hlj;
        have hxoj : π (x = oadd i j)
          { refine eq_trans hxeq
              (ind_eq hlj (λ w, oadd i w = oadd i j) (eq_refl (oadd i j))) };
        refine ∧ₑ₂ (succ_iff x (oadd i j)) (∨ᵢ₁ hxoj) }
      { assume hlj;
        have hltmono : π (lt (oadd i l) (oadd i j))
          { refine oadd_lt_mono2 l j i (ltI l j hlj hOj) };
        have hxmem : π (x ∈ oadd i j)
          { refine ind_eq hxeq (λ w, w ∈ oadd i j)
              (ltD (oadd i l) (oadd i j) hltmono) };
        refine ∧ₑ₂ (succ_iff x (oadd i j)) (∨ᵢ₂ hxmem) } } }
  { assume hx;
    have hltj : π (lt j (succ j)) { refine ltI j (succ j) (succI1 j) (Ord_succ j hOj) };
    have hltmono : π (lt (oadd i j) (oadd i (succ j)))
      { refine oadd_lt_mono2 j (succ j) i hltj };
    have hdisj : π (x = oadd i j ∨ x ∈ oadd i j)
      { refine ∧ₑ₁ (succ_iff x (oadd i j)) hx };
    refine ∨ₑ hdisj _ _
    { assume hxoj;
      refine ind_eq hxoj (λ w, w ∈ oadd i (succ j))
        (ltD (oadd i j) (oadd i (succ j)) hltmono) }
    { assume hxmem;
      have hltx : π (lt x (oadd i j)) { refine ltI x (oadd i j) hxmem (Ord_oadd i j) };
      refine ltD x (oadd i (succ j))
        (lt_trans x (oadd i j) (oadd i (succ j)) hltx hltmono) } }
end;

opaque symbol oadd_UN (A i a : τ ι) (jf : τ ι → τ ι) :
  π (Ball A (λ x, Ord (jf x))) → π (a ∈ A) →
  π (oadd i (Union (RepFun A (λ x, jf x)))
     = Union (RepFun A (λ x, oadd i (jf x)))) ≔
begin
  assume A i a jf hBord haA;
  have hOU : π (Ord (Union (RepFun A (λ x, jf x))))
    { refine Ord_Union (RepFun A (λ x, jf x))
        (ballI (RepFun A (λ x, jf x)) (λ z, Ord z) _);
      assume z hz;
      have hbz : π (Bex A (λ x, z = jf x))
        { refine ∧ₑ₁ (RepFun_iff z A (λ x, jf x)) hz };
      refine ∃ₑ hbz _;
      assume x hx;
      refine ind_eq (∧ₑ₂ hx) (λ w, Ord w) (hBord x (∧ₑ₁ hx)) };
  refine equality_iffI (oadd i (Union (RepFun A (λ x, jf x))))
    (Union (RepFun A (λ x, oadd i (jf x)))) _;
  assume y;
  apply ∧ᵢ
  { assume hy;
    have hlt : π (lt y (oadd i (Union (RepFun A (λ x, jf x)))))
      { refine ltI y (oadd i (Union (RepFun A (λ x, jf x)))) hy
          (Ord_oadd i (Union (RepFun A (λ x, jf x)))) };
    have hdisj : π (lt y i ∨ Bex (Union (RepFun A (λ x, jf x))) (λ l, y = oadd i l))
      { refine lt_oadd_disj y i (Union (RepFun A (λ x, jf x))) hlt };
    refine ∨ₑ hdisj _ _
    { assume hyi;
      have hymem : π (y ∈ oadd i (jf a))
        { refine ltD y (oadd i (jf a)) (lt_oadd1 y i (jf a) hyi) };
      refine UnionI y (oadd i (jf a)) (RepFun A (λ x, oadd i (jf x))) hymem
        (RepFunI a A (λ x, oadd i (jf x)) haA) }
    { assume hbex;
      refine ∃ₑ hbex _;
      assume l hl;
      have hlU : π (l ∈ Union (RepFun A (λ x, jf x))) { refine ∧ₑ₁ hl };
      have hyeq : π (y = oadd i l) { refine ∧ₑ₂ hl };
      have hb1 : π (Bex (RepFun A (λ x, jf x)) (λ C, l ∈ C))
        { refine UnionE l (RepFun A (λ x, jf x)) hlU };
      refine ∃ₑ hb1 _;
      assume C hC;
      have hCrep : π (C ∈ RepFun A (λ x, jf x)) { refine ∧ₑ₁ hC };
      have hlC : π (l ∈ C) { refine ∧ₑ₂ hC };
      have hb2 : π (Bex A (λ x, C = jf x))
        { refine ∧ₑ₁ (RepFun_iff C A (λ x, jf x)) hCrep };
      refine ∃ₑ hb2 _;
      assume x hx;
      have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
      have hCeq : π (C = jf x) { refine ∧ₑ₂ hx };
      have hljfx : π (l ∈ jf x) { refine ind_eq (eq_sym hCeq) (λ w, l ∈ w) hlC };
      have hOjfx : π (Ord (jf x)) { refine hBord x hxA };
      have hltmono : π (lt (oadd i l) (oadd i (jf x)))
        { refine oadd_lt_mono2 l (jf x) i (ltI l (jf x) hljfx hOjfx) };
      have hymem : π (y ∈ oadd i (jf x))
        { refine ind_eq hyeq (λ w, w ∈ oadd i (jf x))
            (ltD (oadd i l) (oadd i (jf x)) hltmono) };
      refine UnionI y (oadd i (jf x)) (RepFun A (λ x2, oadd i (jf x2))) hymem
        (RepFunI x A (λ x2, oadd i (jf x2)) hxA) } }
  { assume hy;
    have hbex : π (Bex (RepFun A (λ x, oadd i (jf x))) (λ B, y ∈ B))
      { refine UnionE y (RepFun A (λ x, oadd i (jf x))) hy };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBrep : π (B ∈ RepFun A (λ x, oadd i (jf x))) { refine ∧ₑ₁ hB };
    have hyB : π (y ∈ B) { refine ∧ₑ₂ hB };
    have hb2 : π (Bex A (λ x, B = oadd i (jf x)))
      { refine ∧ₑ₁ (RepFun_iff B A (λ x, oadd i (jf x))) hBrep };
    refine ∃ₑ hb2 _;
    assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    have hBeq : π (B = oadd i (jf x)) { refine ∧ₑ₂ hx };
    have hyk : π (y ∈ oadd i (jf x)) { refine ind_eq (eq_sym hBeq) (λ w, y ∈ w) hyB };
    have hlty : π (lt y (oadd i (jf x)))
      { refine ltI y (oadd i (jf x)) hyk (Ord_oadd i (jf x)) };
    have hdisj : π (lt y i ∨ Bex (jf x) (λ l, y = oadd i l))
      { refine lt_oadd_disj y i (jf x) hlty };
    refine ∨ₑ hdisj _ _
    { assume hyi;
      refine ltD y (oadd i (Union (RepFun A (λ x2, jf x2))))
        (lt_oadd1 y i (Union (RepFun A (λ x2, jf x2))) hyi) }
    { assume hbex3;
      refine ∃ₑ hbex3 _;
      assume l hl;
      have hljfx : π (l ∈ jf x) { refine ∧ₑ₁ hl };
      have hyeq : π (y = oadd i l) { refine ∧ₑ₂ hl };
      have hjfxrep : π (jf x ∈ RepFun A (λ x2, jf x2))
        { refine RepFunI x A (λ x2, jf x2) hxA };
      have hlU : π (l ∈ Union (RepFun A (λ x2, jf x2)))
        { refine UnionI l (jf x) (RepFun A (λ x2, jf x2)) hljfx hjfxrep };
      have hltmono : π (lt (oadd i l) (oadd i (Union (RepFun A (λ x2, jf x2)))))
        { refine oadd_lt_mono2 l (Union (RepFun A (λ x2, jf x2))) i
            (ltI l (Union (RepFun A (λ x2, jf x2))) hlU hOU) };
      refine ind_eq hyeq (λ w, w ∈ oadd i (Union (RepFun A (λ x2, jf x2))))
        (ltD (oadd i l) (oadd i (Union (RepFun A (λ x2, jf x2)))) hltmono) } }
end;

opaque symbol oadd_Limit (i j : τ ι) :
  π (Limit j) → π (oadd i j = Union (RepFun j (λ k, oadd i k))) ≔
begin
  assume i j hLj;
  have hOj : π (Ord j) { refine Limit_is_Ord j hLj };
  refine equality_iffI (oadd i j) (Union (RepFun j (λ k, oadd i k))) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hlt : π (lt x (oadd i j)) { refine ltI x (oadd i j) hx (Ord_oadd i j) };
    have hdisj : π (lt x i ∨ Bex j (λ l, x = oadd i l))
      { refine lt_oadd_disj x i j hlt };
    refine ∨ₑ hdisj _ _
    { assume hxi;
      have hOi : π (Ord i) { refine lt_Ord2 x i hxi };
      have hxmem : π (x ∈ i) { refine ltD x i hxi };
      have hx0 : π (x ∈ oadd i empty)
        { refine ind_eq (oadd_0 i hOi) (λ w, x ∈ w) hxmem };
      have h0j : π (empty ∈ j) { refine ltD empty j (Limit_has_0 j hLj) };
      refine UnionI x (oadd i empty) (RepFun j (λ k, oadd i k)) hx0
        (RepFunI empty j (λ k, oadd i k) h0j) }
    { assume hbex;
      refine ∃ₑ hbex _;
      assume l hl;
      have hlj : π (l ∈ j) { refine ∧ₑ₁ hl };
      have hxeq : π (x = oadd i l) { refine ∧ₑ₂ hl };
      have hOl : π (Ord l) { refine Ord_in_Ord j l hOj hlj };
      have hsl : π (succ l ∈ j) { refine Limit_has_succ j l hLj hlj };
      have hltl : π (lt l (succ l))
        { refine ltI l (succ l) (succI1 l) (Ord_succ l hOl) };
      have hltmono : π (lt (oadd i l) (oadd i (succ l)))
        { refine oadd_lt_mono2 l (succ l) i hltl };
      have hxmem : π (x ∈ oadd i (succ l))
        { refine ind_eq hxeq (λ w, w ∈ oadd i (succ l))
            (ltD (oadd i l) (oadd i (succ l)) hltmono) };
      refine UnionI x (oadd i (succ l)) (RepFun j (λ k, oadd i k)) hxmem
        (RepFunI (succ l) j (λ k, oadd i k) hsl) } }
  { assume hx;
    have hbex : π (Bex (RepFun j (λ k, oadd i k)) (λ B, x ∈ B))
      { refine UnionE x (RepFun j (λ k, oadd i k)) hx };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBrep : π (B ∈ RepFun j (λ k, oadd i k)) { refine ∧ₑ₁ hB };
    have hxB : π (x ∈ B) { refine ∧ₑ₂ hB };
    have hbex2 : π (Bex j (λ k, B = oadd i k))
      { refine ∧ₑ₁ (RepFun_iff B j (λ k, oadd i k)) hBrep };
    refine ∃ₑ hbex2 _;
    assume k hk;
    have hkj : π (k ∈ j) { refine ∧ₑ₁ hk };
    have hBeq : π (B = oadd i k) { refine ∧ₑ₂ hk };
    have hxk : π (x ∈ oadd i k) { refine ind_eq (eq_sym hBeq) (λ w, x ∈ w) hxB };
    have hltx : π (lt x (oadd i k)) { refine ltI x (oadd i k) hxk (Ord_oadd i k) };
    have hdisj : π (lt x i ∨ Bex k (λ l, x = oadd i l))
      { refine lt_oadd_disj x i k hltx };
    refine ∨ₑ hdisj _ _
    { assume hxi;
      refine ltD x (oadd i j) (lt_oadd1 x i j hxi) }
    { assume hbex3;
      refine ∃ₑ hbex3 _;
      assume l hl;
      have hlk : π (l ∈ k) { refine ∧ₑ₁ hl };
      have hxeq : π (x = oadd i l) { refine ∧ₑ₂ hl };
      have hksub : π (k ⊆ j) { refine OrdmemD j k hkj hOj };
      have hlj : π (l ∈ j) { refine hksub l hlk };
      have hltlj : π (lt l j) { refine ltI l j hlj hOj };
      have hltmono : π (lt (oadd i l) (oadd i j))
        { refine oadd_lt_mono2 l j i hltlj };
      refine ind_eq hxeq (λ w, w ∈ oadd i j)
        (ltD (oadd i l) (oadd i j) hltmono) } }
end;

opaque symbol oadd_eq_0_iff (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π ((oadd i j = empty) ⇔ (i = empty ∧ j = empty)) ≔
begin
  assume i j hOi hOj;
  refine trans_induct3 j
    (λ w, (oadd i w = empty) ⇔ (i = empty ∧ w = empty)) hOj _ _ _
  { apply ∧ᵢ
    { assume h;
      refine ∧ᵢ (eq_trans (eq_sym (oadd_0 i hOi)) h) (eq_refl empty) }
    { assume h; refine eq_trans (oadd_0 i hOi) (∧ₑ₁ h) } }
  { assume x hOx ih;
    apply ∧ᵢ
    { assume h;
      have h2 : π (succ (oadd i x) = empty)
        { refine ind_eq (eq_sym (oadd_succ i x hOx)) (λ w, w = empty) h };
      refine ⊥ₑ (emptyE (oadd i x)
        (ind_eq (eq_sym h2) (λ w, oadd i x ∈ w) (succI1 (oadd i x)))) }
    { assume h;
      refine ⊥ₑ (emptyE x
        (ind_eq (eq_sym (∧ₑ₂ h)) (λ w, x ∈ w) (succI1 x))) } }
  { assume x hLx ih;
    apply ∧ᵢ
    { assume h;
      have hmem : π (oadd i empty ∈ oadd i x)
        { refine ltD (oadd i empty) (oadd i x)
            (oadd_lt_mono2 empty x i (Limit_has_0 x hLx)) };
      refine ⊥ₑ (emptyE (oadd i empty)
        (ind_eq (eq_sym h) (λ w, oadd i empty ∈ w) hmem)) }
    { assume h; refine ⊥ₑ (Limit_nonzero x hLx (∧ₑ₂ h)) } }
end;

opaque symbol oadd_eq_lt_iff (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (lt empty (oadd i j) ⇔ (lt empty i ∨ lt empty j)) ≔
begin
  assume i j hOi hOj;
  have hOij : π (Ord (oadd i j)) { refine Ord_oadd i j };
  apply ∧ᵢ
  { assume h;
    have hne : π (oadd i j ≠ empty)
      { assume he;
        refine emptyE empty
          (ind_eq (eq_sym he) (λ w, empty ∈ w) (ltD empty (oadd i j) h)) };
    have hnand : π (¬ (i = empty ∧ j = empty))
      { assume hand; refine hne (∧ₑ₂ (oadd_eq_0_iff i j hOi hOj) hand) };
    refine ∨ₑ (em (i = empty)) _ _
    { assume hie;
      refine ∨ᵢ₂ (Ord_0_lt j hOj (λ hje, hnand (∧ᵢ hie hje))) }
    { assume hine; refine ∨ᵢ₁ (Ord_0_lt i hOi hine) } }
  { assume h;
    have hne : π (oadd i j ≠ empty)
      { assume he;
        refine ∨ₑ h _ _
        { assume hi;
          have hie : π (i = empty)
            { refine ∧ₑ₁ (∧ₑ₁ (oadd_eq_0_iff i j hOi hOj) he) };
          refine emptyE empty
            (ind_eq (eq_sym hie) (λ w, empty ∈ w) (ltD empty i hi)) }
        { assume hj;
          have hje : π (j = empty)
            { refine ∧ₑ₂ (∧ₑ₁ (oadd_eq_0_iff i j hOi hOj) he) };
          refine emptyE empty
            (ind_eq (eq_sym hje) (λ w, empty ∈ w) (ltD empty j hj)) } };
    refine Ord_0_lt (oadd i j) hOij hne }
end;

opaque symbol oadd_LimitI (i j : τ ι) :
  π (Ord i) → π (Limit j) → π (Limit (oadd i j)) ≔
begin
  assume i j hOi hLj;
  have hOj : π (Ord j) { refine Limit_is_Ord j hLj };
  have hne : π (oadd i j ≠ empty)
    { assume he;
      refine Limit_nonzero j hLj (∧ₑ₂ (∧ₑ₁ (oadd_eq_0_iff i j hOi hOj) he)) };
  have hlt_i_oij : π (lt i (oadd i j))
    { refine ind_eq (eq_sym (oadd_0 i hOi)) (λ w, lt w (oadd i j))
        (oadd_lt_mono2 empty j i (Limit_has_0 j hLj)) };
  refine LimitI (oadd i j) (Ord_oadd i j) hne _;
  assume y hy;
  have hlt : π (lt y (oadd i j)) { refine ltI y (oadd i j) hy (Ord_oadd i j) };
  have hdisj : π (lt y i ∨ Bex j (λ l, y = oadd i l))
    { refine lt_oadd_disj y i j hlt };
  refine ∨ₑ hdisj _ _
  { assume hyi;
    have hle : π (le (succ y) i) { refine succ_leI y i hOi (ltD y i hyi) };
    refine ltD (succ y) (oadd i j)
      (lt_trans1 (succ y) i (oadd i j) hle hlt_i_oij) }
  { assume hbex;
    refine ∃ₑ hbex _;
    assume l hl;
    have hlj : π (l ∈ j) { refine ∧ₑ₁ hl };
    have hyeq : π (y = oadd i l) { refine ∧ₑ₂ hl };
    have hOl : π (Ord l) { refine Ord_in_Ord j l hOj hlj };
    have hsy : π (succ y = oadd i (succ l))
      { refine eq_trans
          (ind_eq (eq_sym hyeq) (λ w, succ y = succ w) (eq_refl (succ y)))
          (eq_sym (oadd_succ i l hOl)) };
    have hmono : π (lt (oadd i (succ l)) (oadd i j))
      { refine oadd_lt_mono2 (succ l) j i
          (ltI (succ l) j (Limit_has_succ j l hLj hlj) hOj) };
    refine ind_eq hsy (λ w, w ∈ oadd i j)
      (ltD (oadd i (succ l)) (oadd i j) hmono) }
end;

opaque symbol oadd_le_self2 (i j : τ ι) :
  π (Ord i) → π (le i (oadd j i)) ≔
begin
  assume i j hOi;
  refine trans_induct3 i (λ w, le w (oadd j w)) hOi _ _ _
  { refine Ord_0_le (oadd j empty) (Ord_oadd j empty) }
  { assume x hOx ih;
    have hxmem : π (x ∈ succ (oadd j x)) { refine ltD x (succ (oadd j x)) ih };
    have hle : π (le (succ x) (succ (oadd j x)))
      { refine succ_leI x (succ (oadd j x)) (Ord_succ (oadd j x) (Ord_oadd j x)) hxmem };
    refine ind_eq (oadd_succ j x hOx) (λ w, le (succ x) w) hle }
  { assume l hLl ih;
    have hOl : π (Ord l) { refine Limit_is_Ord l hLl };
    have hsub : π (l ⊆ oadd j l)
      { assume x hx;
        have hmono : π (lt (oadd j x) (oadd j l))
          { refine oadd_lt_mono2 x l j (ltI x l hx hOl) };
        refine ltD x (oadd j l)
          (lt_trans1 x (oadd j x) (oadd j l) (ih x hx) hmono) };
    refine subset_imp_le (oadd j l) l hsub (Ord_oadd j l) hOl }
end;

opaque symbol oadd_le_mono1 (k j i : τ ι) :
  π (le k j) → π (le (oadd k i) (oadd j i)) ≔
begin
  assume k j i hle;
  have hOk : π (Ord k) { refine lt_Ord k (succ j) hle };
  have hOj : π (Ord j) { refine le_Ord2 k j hle };
  refine ∨ₑ (em (Ord i)) _ _
  { assume hOi;
    refine trans_induct3 i (λ w, le (oadd k w) (oadd j w)) hOi _ _ _
    { refine ind_eq (oadd_0 k hOk) (λ w, le w (oadd j empty))
        (ind_eq (oadd_0 j hOj) (λ w, le k w) hle) }
    { assume x hOx ih;
      have hmem : π (oadd k x ∈ succ (oadd j x))
        { refine ltD (oadd k x) (succ (oadd j x)) ih };
      have hle2 : π (le (succ (oadd k x)) (succ (oadd j x)))
        { refine succ_leI (oadd k x) (succ (oadd j x))
            (Ord_succ (oadd j x) (Ord_oadd j x)) hmem };
      refine ind_eq (oadd_succ k x hOx) (λ w, le w (oadd j (succ x)))
        (ind_eq (oadd_succ j x hOx) (λ w, le (succ (oadd k x)) w) hle2) }
    { assume l hLl ih;
      have hOl : π (Ord l) { refine Limit_is_Ord l hLl };
      have hsub : π (oadd k l ⊆ oadd j l)
        { have hunf : π (oadd k l = Union (RepFun l (λ m, oadd k m)))
            { refine oadd_Limit k l hLl };
          assume x hx;
          have hxU : π (x ∈ Union (RepFun l (λ m, oadd k m)))
            { refine ind_eq (eq_sym hunf) (λ w, x ∈ w) hx };
          have hbex : π (Bex (RepFun l (λ m, oadd k m)) (λ B, x ∈ B))
            { refine UnionE x (RepFun l (λ m, oadd k m)) hxU };
          refine ∃ₑ hbex _;
          assume B hB;
          have hbex2 : π (Bex l (λ m, B = oadd k m))
            { refine ∧ₑ₁ (RepFun_iff B l (λ m, oadd k m)) (∧ₑ₁ hB) };
          refine ∃ₑ hbex2 _;
          assume m hm;
          have hml : π (m ∈ l) { refine ∧ₑ₁ hm };
          have hxkm : π (x ∈ oadd k m)
            { refine ind_eq (eq_sym (∧ₑ₂ hm)) (λ w, x ∈ w) (∧ₑ₂ hB) };
          have hxjm : π (x ∈ oadd j m)
            { refine le_imp_subset (oadd k m) (oadd j m) (ih m hml) x hxkm };
          have hjmsub : π (oadd j m ⊆ oadd j l)
            { refine OrdmemD (oadd j l) (oadd j m)
                (ltD (oadd j m) (oadd j l) (oadd_lt_mono2 m l j (ltI m l hml hOl)))
                (Ord_oadd j l) };
          refine hjmsub x hxjm };
      refine subset_imp_le (oadd j l) (oadd k l) hsub (Ord_oadd j l) (Ord_oadd k l) } }
  { assume hnOi;
    have e1 : π (oadd k i = k)
      { refine eq_trans (oadd_eq_if_raw_oadd k i) _;
        rewrite (If_P (Ord k) (If (Ord i) (raw_oadd k i) k) (If (Ord i) i empty) hOk);
        refine If_not_P (Ord i) (raw_oadd k i) k hnOi };
    have e2 : π (oadd j i = j)
      { refine eq_trans (oadd_eq_if_raw_oadd j i) _;
        rewrite (If_P (Ord j) (If (Ord i) (raw_oadd j i) j) (If (Ord i) i empty) hOj);
        refine If_not_P (Ord i) (raw_oadd j i) j hnOi };
    refine ind_eq e1 (λ w, le w (oadd j i)) (ind_eq e2 (λ w, le k w) hle) }
end;

opaque symbol oadd_lt_mono (ip i jp j : τ ι) :
  π (le ip i) → π (lt jp j) → π (lt (oadd ip jp) (oadd i j)) ≔
begin
  assume ip i jp j hle hlt;
  refine lt_trans1 (oadd ip jp) (oadd i jp) (oadd i j)
    (oadd_le_mono1 ip i jp hle)
    (oadd_lt_mono2 jp j i hlt)
end;

opaque symbol oadd_le_mono (ip i jp j : τ ι) :
  π (le ip i) → π (le jp j) → π (le (oadd ip jp) (oadd i j)) ≔
begin
  assume ip i jp j hlei hlej;
  have hOj : π (Ord j) { refine le_Ord2 jp j hlej };
  have hlt : π (lt (oadd ip jp) (oadd i (succ j)))
    { refine oadd_lt_mono ip i jp (succ j) hlei hlej };
  refine ind_eq (eq_sym (oadd_succ i j hOj)) (λ w, lt (oadd ip jp) w) hlt
end;

opaque symbol oadd_le_iff2 (i j k : τ ι) :
  π (Ord j) → π (Ord k) → π (le (oadd i j) (oadd i k) ⇔ le j k) ≔
begin
  assume i j k hOj hOk;
  have hiff : π (lt (oadd i j) (oadd i (succ k)) ⇔ lt j (succ k))
    { refine oadd_lt_iff2 i j (succ k) hOj };
  refine ind_eq (eq_sym (oadd_succ i k hOk))
    (λ w, lt (oadd i j) w ⇔ lt j (succ k)) hiff
end;

opaque symbol oadd_lt_self (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (lt i (oadd i j)) ≔
begin
  assume i j hOi hlt0;
  have hOj : π (Ord j) { refine lt_Ord2 empty j hlt0 };
  have h1j : π (le (succ empty) j) { refine succ_leI empty j hOj (ltD empty j hlt0) };
  have hmono : π (le (oadd i (succ empty)) (oadd i j))
    { refine oadd_le_mono i i (succ empty) j (le_refl i hOi) h1j };
  have hle : π (le (succ i) (oadd i j))
    { refine ind_eq (eq_sym (oadd_1 i hOi)) (λ w, le w (oadd i j)) hmono };
  refine lt_trans2 i (succ i) (oadd i j)
    (ltI i (succ i) (succI1 i) (Ord_succ i hOi)) hle
end;

opaque symbol Ord_imp_greater_Limit (i : τ ι) :
  π (Ord i) → π (`∃ (k : τ ι), lt i k ∧ Limit k) ≔
begin
  assume i hOi;
  have h0 : π (lt empty omega) { refine Limit_has_0 omega Limit_omega };
  refine ∃ᵢ (oadd i omega)
    (∧ᵢ (oadd_lt_self i omega hOi h0) (oadd_LimitI i omega hOi Limit_omega))
end;

opaque symbol Ord2_imp_greater_Limit (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (`∃ (k : τ ι), lt i k ∧ lt j k ∧ Limit k) ≔
begin
  assume i j hOi hOj;
  have hOij : π (Ord (Un i j)) { refine Ord_Un i j hOi hOj };
  have hgr : π (`∃ (k : τ ι), lt (Un i j) k ∧ Limit k)
    { refine Ord_imp_greater_Limit (Un i j) hOij };
  refine ∃ₑ hgr _;
  assume k hk;
  have hltUn : π (lt (Un i j) k) { refine ∧ₑ₁ hk };
  have hLk : π (Limit k) { refine ∧ₑ₂ hk };
  refine ∃ᵢ k (∧ᵢ (lt_trans1 i (Un i j) k (Un_upper1_le i j hOi hOj) hltUn)
    (∧ᵢ (lt_trans1 j (Un i j) k (Un_upper2_le i j hOi hOj) hltUn) hLk))
end;

// ===========================================================================
// Ordinal Subtraction
// ===========================================================================

opaque symbol bij_sum_Diff (A B : τ ι) :
  π (A ⊆ B) →
  π (Lambda B (λ y, If (y ∈ A) (Inl y) (Inr y)) ∈ bij B (sum A (Diff B A))) ≔
begin
  assume A B hAB;
  refine lam_bijective B (sum A (Diff B A))
    (λ y, If (y ∈ A) (Inl y) (Inr y)) idcase _ _ _ _
  // (1) forward type
  { assume y hy;
    refine ∨ₑ (em (y ∈ A)) _ _
    { assume hyA;
      refine ind_eq (If_P (y ∈ A) (Inl y) (Inr y) hyA)
        (λ w, w ∈ sum A (Diff B A)) (InlI y A (Diff B A) hyA) }
    { assume hynA;
      refine ind_eq (If_not_P (y ∈ A) (Inl y) (Inr y) hynA)
        (λ w, w ∈ sum A (Diff B A))
        (InrI y A (Diff B A) (DiffI y B A hy hynA)) } }
  // (2) inverse type
  { assume z hz;
    refine sumE z A (Diff B A) (idcase z ∈ B) hz _ _
    { assume x hx hze;
      refine ind_eq hze (λ w, idcase w ∈ B)
        (ind_eq (case_Inl (λ x2, x2) (λ y2, y2) x) (λ w, w ∈ B) (hAB x hx)) }
    { assume y hy hze;
      refine ind_eq hze (λ w, idcase w ∈ B)
        (ind_eq (case_Inr (λ x2, x2) (λ y2, y2) y) (λ w, w ∈ B)
          (DiffD1 y B A hy)) } }
  // (3) d (c y) = y
  { assume y hy;
    refine ∨ₑ (em (y ∈ A)) _ _
    { assume hyA;
      refine ind_eq (If_P (y ∈ A) (Inl y) (Inr y) hyA)
        (λ w, idcase w = y) (case_Inl (λ x2, x2) (λ y2, y2) y) }
    { assume hynA;
      refine ind_eq (If_not_P (y ∈ A) (Inl y) (Inr y) hynA)
        (λ w, idcase w = y) (case_Inr (λ x2, x2) (λ y2, y2) y) } }
  // (4) c (d z) = z
  { assume z hz;
    refine sumE z A (Diff B A)
      ((λ y0, If (y0 ∈ A) (Inl y0) (Inr y0)) (idcase z) = z) hz _ _
    { assume x hx hze;
      refine ind_eq hze
        (λ w, (λ y0, If (y0 ∈ A) (Inl y0) (Inr y0)) (idcase w) = w)
        (ind_eq (case_Inl (λ x2, x2) (λ y2, y2) x)
          (λ w, (λ y0, If (y0 ∈ A) (Inl y0) (Inr y0)) w = Inl x)
          (If_P (x ∈ A) (Inl x) (Inr x) hx)) }
    { assume y hy hze;
      refine ind_eq hze
        (λ w, (λ y0, If (y0 ∈ A) (Inl y0) (Inr y0)) (idcase w) = w)
        (ind_eq (case_Inr (λ x2, x2) (λ y2, y2) y)
          (λ w, (λ y0, If (y0 ∈ A) (Inl y0) (Inr y0)) w = Inr y)
          (If_not_P (y ∈ A) (Inl y) (Inr y) (DiffD2 y B A hy))) } }
end;

opaque symbol ordertype_sum_Diff (i j : τ ι) :
  π (le i j) →
  π (ordertype (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j))
     = ordertype j (Memrel j)) ≔
begin
  assume i j hle;
  have hOj : π (Ord j) { refine le_Ord2 i j hle };
  have hOi : π (Ord i) { refine lt_Ord i (succ j) hle };
  have hisub : π (i ⊆ j) { refine le_imp_subset i j hle };
  have hiso : π (Lambda j (λ y0, If (y0 ∈ i) (Inl y0) (Inr y0))
      ∈ ord_iso j (Memrel j) (sum i (Diff j i))
                (radd i (Memrel j) (Diff j i) (Memrel j)))
    { refine ord_isoI (Lambda j (λ y0, If (y0 ∈ i) (Inl y0) (Inr y0)))
        j (Memrel j) (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j))
        (bij_sum_Diff i j hisub) _;
      assume x hx y hy;
      have hOx : π (Ord x) { refine Ord_in_Ord j x hOj hx };
      have hOy : π (Ord y) { refine Ord_in_Ord j y hOj hy };
      have hfx : π (fapply (Lambda j (λ y0, If (y0 ∈ i) (Inl y0) (Inr y0))) x
                    = If (x ∈ i) (Inl x) (Inr x))
        { refine beta j (λ y0, If (y0 ∈ i) (Inl y0) (Inr y0)) x hx };
      have hfy : π (fapply (Lambda j (λ y0, If (y0 ∈ i) (Inl y0) (Inr y0))) y
                    = If (y ∈ i) (Inl y) (Inr y))
        { refine beta j (λ y0, If (y0 ∈ i) (Inl y0) (Inr y0)) y hy };
      rewrite hfx;
      rewrite hfy;
      refine ∨ₑ (em (x ∈ i)) _ _
      { assume hxi;
        rewrite (If_P (x ∈ i) (Inl x) (Inr x) hxi);
        refine ∨ₑ (em (y ∈ i)) _ _
        { assume hyi;
          rewrite (If_P (y ∈ i) (Inl y) (Inr y) hyi);
          apply ∧ᵢ
          { assume h;
            refine ∧ₑ₂ (radd_Inl_iff x y i (Memrel j) (Diff j i) (Memrel j))
              (∧ᵢ hxi (∧ᵢ hyi h)) }
          { assume h;
            refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff x y i (Memrel j) (Diff j i) (Memrel j)) h)) } }
        { assume hyni;
          rewrite (If_not_P (y ∈ i) (Inl y) (Inr y) hyni);
          apply ∧ᵢ
          { assume h;
            refine ∧ₑ₂ (radd_Inl_Inr_iff x y i (Memrel j) (Diff j i) (Memrel j))
              (∧ᵢ hxi (DiffI y j i hy hyni)) }
          { assume h;
            have hxy : π (lt x y)
              { refine lt_trans2 x i y (ltI x i hxi hOi)
                  (not_lt_imp_le y i hOy hOi (λ hh, hyni (ltD y i hh))) };
            refine MemrelI x y j (ltD x y hxy) hx hy } } }
      { assume hxni;
        rewrite (If_not_P (x ∈ i) (Inl x) (Inr x) hxni);
        refine ∨ₑ (em (y ∈ i)) _ _
        { assume hyi;
          rewrite (If_P (y ∈ i) (Inl y) (Inr y) hyi);
          apply ∧ᵢ
          { assume h;
            have hxy : π (x ∈ y) { refine ∧ₑ₂ (∧ₑ₂ (MemrelE x y j h)) };
            have hyx : π (lt y x)
              { refine lt_trans2 y i x (ltI y i hyi hOi)
                  (not_lt_imp_le x i hOx hOi (λ hh, hxni (ltD x i hh))) };
            refine ⊥ₑ (lt_not_sym x y (ltI x y hxy hOy) hyx) }
          { assume h;
            refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff x y i (Memrel j) (Diff j i) (Memrel j)) h) } }
        { assume hyni;
          rewrite (If_not_P (y ∈ i) (Inl y) (Inr y) hyni);
          apply ∧ᵢ
          { assume h;
            refine ∧ₑ₂ (radd_Inr_iff x y i (Memrel j) (Diff j i) (Memrel j))
              (∧ᵢ (DiffI x j i hx hxni) (∧ᵢ (DiffI y j i hy hyni) h)) }
          { assume h;
            refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff x y i (Memrel j) (Diff j i) (Memrel j)) h)) } } } };
  refine ordertype_eq (converse (Lambda j (λ y0, If (y0 ∈ i) (Inl y0) (Inr y0))))
    (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j)) j (Memrel j)
    (ord_iso_sym (Lambda j (λ y0, If (y0 ∈ i) (Inl y0) (Inr y0))) j (Memrel j)
       (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j)) hiso)
    (well_ord_Memrel j hOj)
end;

opaque symbol Ord_odiff (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (odiff i j)) ≔
begin
  assume i j hi hj;
  rewrite odiff_def;
  have hsub : π (Diff i j ⊆ i)
    { assume x hx; refine DiffD1 x i j hx };
  refine Ord_ordertype (Diff i j) (Memrel i)
    (well_ord_subset i (Diff i j) (Memrel i) (well_ord_Memrel i hi) hsub)
end;

opaque symbol raw_oadd_ordertype_Diff (i j : τ ι) :
  π (le i j) →
  π (raw_oadd i (odiff j i)
     = ordertype (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j))) ≔
begin
  assume i j hle;
  have hOj : π (Ord j) { refine le_Ord2 i j hle };
  have hisub : π (i ⊆ j) { refine le_imp_subset i j hle };
  have hDsub : π (Diff j i ⊆ j) { assume x hx; refine DiffD1 x j i hx };
  have hwoiMj : π (well_ord i (Memrel j)) { refine le_well_ord_Memrel i j hle };
  have hwoDiff : π (well_ord (Diff j i) (Memrel j))
    { refine well_ord_subset j (Diff j i) (Memrel j) (well_ord_Memrel j hOj) hDsub };
  have hwoCod : π (well_ord (sum i (Diff j i))
      (radd i (Memrel j) (Diff j i) (Memrel j)))
    { refine well_ord_radd i (Memrel j) (Diff j i) (Memrel j) hwoiMj hwoDiff };
  have hf : π (id_fun i ∈ ord_iso i (Memrel i) i (Memrel j))
    { refine id_ord_iso_Memrel i j hisub };
  have hg0 : π (ordermap (Diff j i) (Memrel j)
      ∈ ord_iso (Diff j i) (Memrel j)
                (ordertype (Diff j i) (Memrel j))
                (Memrel (ordertype (Diff j i) (Memrel j))))
    { refine ordertype_ord_iso (Diff j i) (Memrel j) hwoDiff };
  have hgsym : π (converse (ordermap (Diff j i) (Memrel j))
      ∈ ord_iso (ordertype (Diff j i) (Memrel j))
                (Memrel (ordertype (Diff j i) (Memrel j)))
                (Diff j i) (Memrel j))
    { refine ord_iso_sym (ordermap (Diff j i) (Memrel j)) (Diff j i) (Memrel j)
        (ordertype (Diff j i) (Memrel j))
        (Memrel (ordertype (Diff j i) (Memrel j))) hg0 };
  rewrite raw_oadd_def;
  rewrite odiff_def;
  refine ordertype_eq _ _ _ _ _
    (sum_ord_iso_cong _ _ _ _ _ _ _ _ _ _ hf hgsym)
    hwoCod
end;

opaque symbol oadd_odiff_inverse (i j : τ ι) :
  π (le i j) → π (oadd i (odiff j i) = j) ≔
begin
  assume i j hle;
  have hOi : π (Ord i) { refine lt_Ord i (succ j) hle };
  have hOj : π (Ord j) { refine le_Ord2 i j hle };
  have hOodiff : π (Ord (odiff j i)) { refine Ord_odiff j i hOj hOi };
  refine eq_trans (eq_sym (raw_oadd_eq_oadd i (odiff j i) hOi hOodiff))
    (eq_trans (raw_oadd_ordertype_Diff i j hle)
      (eq_trans (ordertype_sum_Diff i j hle)
        (ordertype_Memrel j hOj)))
end;

opaque symbol odiff_oadd_inverse (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (odiff (oadd i j) i = j) ≔
begin
  assume i j hOi hOj;
  refine oadd_inject i (odiff (oadd i j) i) j
    (oadd_odiff_inverse i (oadd i j) (oadd_le_self i j hOi))
    (Ord_odiff (oadd i j) i (Ord_oadd i j) hOi)
    hOj
end;

opaque symbol odiff_lt_mono2 (i j k : τ ι) :
  π (lt i j) → π (le k i) → π (lt (odiff i k) (odiff j k)) ≔
begin
  assume i j k hij hki;
  have hOi : π (Ord i) { refine lt_Ord i j hij };
  have hOk : π (Ord k) { refine lt_Ord k (succ i) hki };
  have hile : π (le i j) { refine leI i j (ltD i j hij) (lt_Ord2 i j hij) };
  have hkj : π (le k j) { refine le_trans k i j hki hile };
  have hoi : π (oadd k (odiff i k) = i) { refine oadd_odiff_inverse k i hki };
  have hoj : π (oadd k (odiff j k) = j) { refine oadd_odiff_inverse k j hkj };
  have hltoo : π (lt (oadd k (odiff i k)) (oadd k (odiff j k)))
    { refine ind_eq hoj (λ w, lt (oadd k (odiff i k)) w)
        (ind_eq hoi (λ w, lt w j) hij) };
  refine oadd_lt_cancel2 k (odiff i k) (odiff j k) hltoo
    (Ord_odiff i k hOi hOk)
end;

// ===========================================================================
// Ordinal Multiplication
// ===========================================================================

opaque symbol Ord_omult (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (omult i j)) ≔
begin
  assume i j hi hj;
  rewrite omult_def;
  refine Ord_ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))
    (well_ord_rmult j (Memrel j) i (Memrel i)
      (well_ord_Memrel j hj) (well_ord_Memrel i hi))
end;

opaque symbol pred_Pair_eq (a A b B r s : τ ι) :
  π (a ∈ A) → π (b ∈ B) →
  π (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)
     = Un (Sigma (pred A a r) (λ _, B)) (Sigma (singleton a) (λ _, pred B b s))) ≔
begin
  assume a A b B r s haA hbB;
  refine equality_iffI (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s))
    (Un (Sigma (pred A a r) (λ _, B)) (Sigma (singleton a) (λ _, pred B b s))) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    have hzSig : π (z ∈ Sigma A (λ _, B))
      { refine pred_subset (Sigma A (λ _, B)) (Pair a b) (rmult A r B s) z hz };
    have hzrmult : π (Pair z (Pair a b) ∈ rmult A r B s)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)) hz) };
    have hbex : π (Bex A (λ x, Bex B (λ y, z = Pair x y)))
      { refine SigmaE z A (λ _, B) hzSig };
    refine ∃ₑ hbex _; assume x hx0;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx0 };
    refine ∃ₑ (∧ₑ₂ hx0) _; assume y hy0;
    have hyB : π (y ∈ B) { refine ∧ₑ₁ hy0 };
    have hzeq : π (z = Pair x y) { refine ∧ₑ₂ hy0 };
    have hrm : π (Pair (Pair x y) (Pair a b) ∈ rmult A r B s)
      { refine ind_eq (eq_sym hzeq) (λ w, Pair w (Pair a b) ∈ rmult A r B s) hzrmult };
    have hdisj : π ((Pair x a ∈ r ∧ x ∈ A ∧ a ∈ A ∧ y ∈ B ∧ b ∈ B)
                    ∨ (Pair y b ∈ s ∧ x = a ∧ a ∈ A ∧ y ∈ B ∧ b ∈ B))
      { refine ∧ₑ₁ (rmult_iff x y a b A r B s) hrm };
    refine ∨ₑ hdisj _ _
    { assume h;
      have hzP : π (z ∈ Sigma (pred A a r) (λ _, B))
        { refine ind_eq hzeq (λ w, w ∈ Sigma (pred A a r) (λ _, B))
            (SigmaI x y (pred A a r) (λ _, B)
              (predI x A a r (∧ₑ₁ h) (∧ₑ₁ (∧ₑ₂ h))) hyB) };
      refine UnI1 z (Sigma (pred A a r) (λ _, B))
        (Sigma (singleton a) (λ _, pred B b s)) hzP }
    { assume h;
      have hzP : π (z ∈ Sigma (singleton a) (λ _, pred B b s))
        { refine ind_eq hzeq (λ w, w ∈ Sigma (singleton a) (λ _, pred B b s))
            (SigmaI x y (singleton a) (λ _, pred B b s)
              (∧ₑ₂ (singleton_iff x a) (∧ₑ₁ (∧ₑ₂ h)))
              (predI y B b s (∧ₑ₁ h) hyB)) };
      refine UnI2 z (Sigma (pred A a r) (λ _, B))
        (Sigma (singleton a) (λ _, pred B b s)) hzP } }
  { assume hz;
    have hdisj : π (z ∈ Sigma (pred A a r) (λ _, B)
                    ∨ z ∈ Sigma (singleton a) (λ _, pred B b s))
      { refine UnE z (Sigma (pred A a r) (λ _, B))
          (Sigma (singleton a) (λ _, pred B b s)) hz };
    refine ∨ₑ hdisj _ _
    { assume hzL;
      have hbex : π (Bex (pred A a r) (λ x, Bex B (λ y, z = Pair x y)))
        { refine SigmaE z (pred A a r) (λ _, B) hzL };
      refine ∃ₑ hbex _; assume x hx0;
      have hxpred : π (x ∈ pred A a r) { refine ∧ₑ₁ hx0 };
      refine ∃ₑ (∧ₑ₂ hx0) _; assume y hy0;
      have hyB : π (y ∈ B) { refine ∧ₑ₁ hy0 };
      have hzeq : π (z = Pair x y) { refine ∧ₑ₂ hy0 };
      have hxa : π (Pair x a ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff x A a r) hxpred) };
      have hxA : π (x ∈ A) { refine ∧ₑ₂ (∧ₑ₁ (pred_iff x A a r) hxpred) };
      have hrm : π (Pair (Pair x y) (Pair a b) ∈ rmult A r B s)
        { refine ∧ₑ₂ (rmult_iff x y a b A r B s)
            (∨ᵢ₁ (∧ᵢ hxa (∧ᵢ hxA (∧ᵢ haA (∧ᵢ hyB hbB))))) };
      have hSpair : π (Pair z (Pair a b) ∈ rmult A r B s)
        { refine ind_eq hzeq (λ w, Pair w (Pair a b) ∈ rmult A r B s) hrm };
      have hzSig : π (z ∈ Sigma A (λ _, B))
        { refine ind_eq hzeq (λ w, w ∈ Sigma A (λ _, B))
            (SigmaI x y A (λ _, B) hxA hyB) };
      refine predI z (Sigma A (λ _, B)) (Pair a b) (rmult A r B s) hSpair hzSig }
    { assume hzR;
      have hbex : π (Bex (singleton a) (λ x, Bex (pred B b s) (λ y, z = Pair x y)))
        { refine SigmaE z (singleton a) (λ _, pred B b s) hzR };
      refine ∃ₑ hbex _; assume x hx0;
      have hxsing : π (x ∈ singleton a) { refine ∧ₑ₁ hx0 };
      refine ∃ₑ (∧ₑ₂ hx0) _; assume y hy0;
      have hypred : π (y ∈ pred B b s) { refine ∧ₑ₁ hy0 };
      have hzeq : π (z = Pair x y) { refine ∧ₑ₂ hy0 };
      have hxa : π (x = a) { refine ∧ₑ₁ (singleton_iff x a) hxsing };
      have hyb : π (Pair y b ∈ s) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff y B b s) hypred) };
      have hyB : π (y ∈ B) { refine ∧ₑ₂ (∧ₑ₁ (pred_iff y B b s) hypred) };
      have hxA : π (x ∈ A) { refine ind_eq hxa (λ w, w ∈ A) haA };
      have hrm : π (Pair (Pair x y) (Pair a b) ∈ rmult A r B s)
        { refine ∧ₑ₂ (rmult_iff x y a b A r B s)
            (∨ᵢ₂ (∧ᵢ hyb (∧ᵢ hxa (∧ᵢ haA (∧ᵢ hyB hbB))))) };
      have hSpair : π (Pair z (Pair a b) ∈ rmult A r B s)
        { refine ind_eq hzeq (λ w, Pair w (Pair a b) ∈ rmult A r B s) hrm };
      have hzSig : π (z ∈ Sigma A (λ _, B))
        { refine ind_eq hzeq (λ w, w ∈ Sigma A (λ _, B))
            (SigmaI x y A (λ _, B) hxA hyB) };
      refine predI z (Sigma A (λ _, B)) (Pair a b) (rmult A r B s) hSpair hzSig } }
end;

opaque symbol ordertype_pred_Pair_eq (a A b B r s : τ ι) :
  π (a ∈ A) → π (b ∈ B) → π (well_ord A r) → π (well_ord B s) →
  π (ordertype (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)) (rmult A r B s)
     = ordertype (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
                 (radd (Sigma A (λ _, B)) (rmult A r B s) B s)) ≔
begin
  assume a A b B r s haA hbB hwoA hwoB;
  have hiso : π (Lambda (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
              (λ x, case_sum (λ x2, x2) (λ y, Pair a y) x)
       ∈ ord_iso (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
                 (radd (Sigma A (λ _, B)) (rmult A r B s) B s)
                 (Un (Sigma (pred A a r) (λ _, B))
                     (Sigma (singleton a) (λ _, pred B b s)))
                 (rmult A r B s))
    { refine prod_sum_singleton_ord_iso a A r b B s haA hwoA };
  have hwoSig : π (well_ord (Sigma A (λ _, B)) (rmult A r B s))
    { refine well_ord_rmult A r B s hwoA hwoB };
  have hpe : π (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)
                = Un (Sigma (pred A a r) (λ _, B))
                     (Sigma (singleton a) (λ _, pred B b s)))
    { refine pred_Pair_eq a A b B r s haA hbB };
  have hwoPred : π (well_ord (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s))
                     (rmult A r B s))
    { refine well_ord_subset (Sigma A (λ _, B))
        (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)) (rmult A r B s)
        hwoSig (pred_subset (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)) };
  have hwoUn : π (well_ord (Un (Sigma (pred A a r) (λ _, B))
                     (Sigma (singleton a) (λ _, pred B b s))) (rmult A r B s))
    { refine ind_eq (eq_sym hpe) (λ w, well_ord w (rmult A r B s)) hwoPred };
  have heq1 : π (ordertype (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
                   (radd (Sigma A (λ _, B)) (rmult A r B s) B s)
                 = ordertype (Un (Sigma (pred A a r) (λ _, B))
                       (Sigma (singleton a) (λ _, pred B b s))) (rmult A r B s))
    { refine ordertype_eq _
        (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
        (radd (Sigma A (λ _, B)) (rmult A r B s) B s)
        (Un (Sigma (pred A a r) (λ _, B)) (Sigma (singleton a) (λ _, pred B b s)))
        (rmult A r B s) hiso hwoUn };
  rewrite hpe;
  refine eq_sym heq1
end;

// port-internal helper: Memrel agrees on a subset (pointwise iff).
private opaque symbol Memrel_sub_iff (x y A B : τ ι) :
  π (A ⊆ B) → π (x ∈ A) → π (y ∈ A) →
  π (Pair x y ∈ Memrel A ⇔ Pair x y ∈ Memrel B) ≔
begin
  assume x y A B hAB hxA hyA;
  apply ∧ᵢ
  { assume h;
    refine MemrelI x y B (∧ₑ₂ (∧ₑ₂ (MemrelE x y A h))) (hAB x hxA) (hAB y hyA) }
  { assume h;
    refine MemrelI x y A (∧ₑ₂ (∧ₑ₂ (MemrelE x y B h))) hxA hyA }
end;

// port-internal helper: rmult with Memrel on the first component agrees when the
// first-component set shrinks along a subset (second component fixed).
private opaque symbol rmult_Memrel_sub_iff (ap aq bp bq A B j : τ ι) :
  π (A ⊆ B) → π (ap ∈ A) → π (bp ∈ A) → π (aq ∈ j) → π (bq ∈ j) →
  π (Pair (Pair ap aq) (Pair bp bq) ∈ rmult B (Memrel B) j (Memrel j)
     ⇔ Pair (Pair ap aq) (Pair bp bq) ∈ rmult A (Memrel A) j (Memrel j)) ≔
begin
  assume ap aq bp bq A B j hAB hap hbp haq hbq;
  have hapB : π (ap ∈ B) { refine hAB ap hap };
  have hbpB : π (bp ∈ B) { refine hAB bp hbp };
  apply ∧ᵢ
  { assume h;
    refine ∧ₑ₂ (rmult_iff ap aq bp bq A (Memrel A) j (Memrel j)) _;
    refine ∨ₑ (∧ₑ₁ (rmult_iff ap aq bp bq B (Memrel B) j (Memrel j)) h) _ _
    { assume hl;
      refine ∨ᵢ₁ (∧ᵢ (∧ₑ₂ (Memrel_sub_iff ap bp A B hAB hap hbp) (∧ₑ₁ hl))
        (∧ᵢ hap (∧ᵢ hbp (∧ᵢ haq hbq)))) }
    { assume hr;
      refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ hr) (∧ᵢ (∧ₑ₁ (∧ₑ₂ hr)) (∧ᵢ hbp (∧ᵢ haq hbq)))) } }
  { assume h;
    refine ∧ₑ₂ (rmult_iff ap aq bp bq B (Memrel B) j (Memrel j)) _;
    refine ∨ₑ (∧ₑ₁ (rmult_iff ap aq bp bq A (Memrel A) j (Memrel j)) h) _ _
    { assume hl;
      refine ∨ᵢ₁ (∧ᵢ (∧ₑ₁ (Memrel_sub_iff ap bp A B hAB hap hbp) (∧ₑ₁ hl))
        (∧ᵢ hapB (∧ᵢ hbpB (∧ᵢ haq hbq)))) }
    { assume hr;
      refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ hr) (∧ᵢ (∧ₑ₁ (∧ₑ₂ hr)) (∧ᵢ hbpB (∧ᵢ haq hbq)))) } }
end;

// port-internal helper: Sigma A (λ_,C) grows monotonically in its first factor.
private opaque symbol Sigma_left_sub (z A B C : τ ι) :
  π (A ⊆ B) → π (z ∈ Sigma A (λ _, C)) → π (z ∈ Sigma B (λ _, C)) ≔
begin
  assume z A B C hAB hz;
  refine ind_eq (eq_sym (Pair_fst_snd z A (λ _, C) hz)) (λ w, w ∈ Sigma B (λ _, C))
    (SigmaI (fst z) (snd z) B (λ _, C) (hAB (fst z) (SigmaD1 z A (λ _, C) hz))
      (SigmaD2 z A (λ _, C) hz))
end;

// port-internal helper: rmult (first component Memrel) agreement on undecomposed
// elements of Sigma A (λ_,j), when the first factor shrinks along a subset.
private opaque symbol rmult_sub_iff_pair (a b A B j : τ ι) :
  π (A ⊆ B) → π (a ∈ Sigma A (λ _, j)) → π (b ∈ Sigma A (λ _, j)) →
  π (Pair a b ∈ rmult B (Memrel B) j (Memrel j)
     ⇔ Pair a b ∈ rmult A (Memrel A) j (Memrel j)) ≔
begin
  assume a b A B j hAB ha hb;
  have hpa : π (Pair (fst a) (snd a) = a) { refine Pair_fst_snd a A (λ _, j) ha };
  have hpb : π (Pair (fst b) (snd b) = b) { refine Pair_fst_snd b A (λ _, j) hb };
  have hiff : π (Pair (Pair (fst a) (snd a)) (Pair (fst b) (snd b))
                  ∈ rmult B (Memrel B) j (Memrel j)
      ⇔ Pair (Pair (fst a) (snd a)) (Pair (fst b) (snd b))
                  ∈ rmult A (Memrel A) j (Memrel j))
    { refine rmult_Memrel_sub_iff (fst a) (snd a) (fst b) (snd b) A B j hAB
        (SigmaD1 a A (λ _, j) ha) (SigmaD1 b A (λ _, j) hb)
        (SigmaD2 a A (λ _, j) ha) (SigmaD2 b A (λ _, j) hb) };
  refine ind_eq (eq_sym hpa)
    (λ wa, (Pair wa b ∈ rmult B (Memrel B) j (Memrel j))
           ⇔ (Pair wa b ∈ rmult A (Memrel A) j (Memrel j)))
    (ind_eq (eq_sym hpb)
      (λ wb, (Pair (Pair (fst a) (snd a)) wb ∈ rmult B (Memrel B) j (Memrel j))
             ⇔ (Pair (Pair (fst a) (snd a)) wb ∈ rmult A (Memrel A) j (Memrel j)))
      hiff)
end;

opaque symbol ordertype_pred_Pair_lemma (ip i jp j : τ ι) :
  π (lt ip i) → π (lt jp j) →
  π (ordertype
       (pred (Sigma i (λ _, j)) (Pair ip jp) (rmult i (Memrel i) j (Memrel j)))
       (rmult i (Memrel i) j (Memrel j))
     = raw_oadd (omult j ip) jp) ≔
begin
  assume ip i jp j hlti hltj;
  have hOi : π (Ord i) { refine lt_Ord2 ip i hlti };
  have hOj : π (Ord j) { refine lt_Ord2 jp j hltj };
  have hOip : π (Ord ip) { refine lt_Ord ip i hlti };
  have hOjp : π (Ord jp) { refine lt_Ord jp j hltj };
  have hipi : π (ip ∈ i) { refine ltD ip i hlti };
  have hjpj : π (jp ∈ j) { refine ltD jp j hltj };
  have hipsub : π (ip ⊆ i) { refine OrdmemD i ip hipi hOi };
  have hjpsub : π (jp ⊆ j) { refine OrdmemD j jp hjpj hOj };
  have hwoi : π (well_ord i (Memrel i)) { refine well_ord_Memrel i hOi };
  have hwoj : π (well_ord j (Memrel j)) { refine well_ord_Memrel j hOj };
  have hwojp : π (well_ord jp (Memrel jp)) { refine well_ord_Memrel jp hOjp };
  have hOmult : π (Ord (omult j ip)) { refine Ord_omult j ip hOj hOip };
  have hwoSigIP : π (well_ord (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)))
    { refine well_ord_rmult ip (Memrel ip) j (Memrel j) (well_ord_Memrel ip hOip) hwoj };
  have hpe : π (ordertype (pred (Sigma i (λ _, j)) (Pair ip jp) (rmult i (Memrel i) j (Memrel j)))
                  (rmult i (Memrel i) j (Memrel j))
      = ordertype (sum (Sigma (pred i ip (Memrel i)) (λ _, j)) (pred j jp (Memrel j)))
                  (radd (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)) j (Memrel j)))
    { refine ordertype_pred_Pair_eq ip i jp j (Memrel i) (Memrel j) hipi hjpj hwoi hwoj };
  rewrite hpe;
  rewrite (lt_pred_Memrel ip i hlti);
  rewrite (lt_pred_Memrel jp j hltj);
  rewrite (raw_oadd_def (omult j ip) jp);
  // Step B ingredients: left iso ordermap → omult j ip
  have homd : π (omult j ip = ordertype (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)))
    { refine omult_def j ip };
  have hf : π (ordermap (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j))
      ∈ ord_iso (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j))
                (omult j ip) (Memrel (omult j ip)))
    { refine ind_eq homd
        (λ w, ordermap (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j))
          ∈ ord_iso (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)) w (Memrel w))
        (ordertype_ord_iso (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j))
          hwoSigIP) };
  have hStepB : π (ordertype (sum (Sigma ip (λ _, j)) jp)
                     (radd (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp))
      = ordertype (sum (omult j ip) jp)
                  (radd (omult j ip) (Memrel (omult j ip)) jp (Memrel jp)))
    { refine ordertype_eq _
        (sum (Sigma ip (λ _, j)) jp)
        (radd (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp))
        (sum (omult j ip) jp)
        (radd (omult j ip) (Memrel (omult j ip)) jp (Memrel jp))
        (sum_ord_iso_cong (ordermap (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)))
          (id_fun jp) (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j))
          (omult j ip) (Memrel (omult j ip)) jp (Memrel jp) jp (Memrel jp)
          hf (ord_iso_refl jp (Memrel jp)))
        (well_ord_radd (omult j ip) (Memrel (omult j ip)) jp (Memrel jp)
          (well_ord_Memrel (omult j ip) hOmult) hwojp) };
  // Step A: id ord_iso changing the radd relations on sum (Sigma ip (λ_,j)) jp
  have hisoA : π (id_fun (sum (Sigma ip (λ _, j)) jp)
      ∈ ord_iso (sum (Sigma ip (λ _, j)) jp)
                (radd (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)) j (Memrel j))
                (sum (Sigma ip (λ _, j)) jp)
                (radd (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)))
    { refine ord_isoI (id_fun (sum (Sigma ip (λ _, j)) jp)) (sum (Sigma ip (λ _, j)) jp)
        (radd (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)) j (Memrel j))
        (sum (Sigma ip (λ _, j)) jp)
        (radd (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp))
        (id_bij (sum (Sigma ip (λ _, j)) jp)) _;
      assume u hu v hv;
      rewrite (id_conv (sum (Sigma ip (λ _, j)) jp) u hu);
      rewrite (id_conv (sum (Sigma ip (λ _, j)) jp) v hv);
      refine sumE u (Sigma ip (λ _, j)) jp _ hu _ _
      { assume a ha hue;
        refine sumE v (Sigma ip (λ _, j)) jp _ hv _ _
        { assume b hb hve;
          rewrite hue; rewrite hve;
          apply ∧ᵢ
          { assume h;
            have hc : π (a ∈ Sigma i (λ _, j) ∧ b ∈ Sigma i (λ _, j)
                          ∧ Pair a b ∈ rmult i (Memrel i) j (Memrel j))
              { refine ∧ₑ₁ (radd_Inl_iff a b (Sigma i (λ _, j))
                  (rmult i (Memrel i) j (Memrel j)) j (Memrel j)) h };
            refine ∧ₑ₂ (radd_Inl_iff a b (Sigma ip (λ _, j))
              (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)) _;
            refine ∧ᵢ ha (∧ᵢ hb
              (∧ₑ₁ (rmult_sub_iff_pair a b ip i j hipsub ha hb) (∧ₑ₂ (∧ₑ₂ hc)))) }
          { assume h;
            have hc : π (a ∈ Sigma ip (λ _, j) ∧ b ∈ Sigma ip (λ _, j)
                          ∧ Pair a b ∈ rmult ip (Memrel ip) j (Memrel j))
              { refine ∧ₑ₁ (radd_Inl_iff a b (Sigma ip (λ _, j))
                  (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)) h };
            refine ∧ₑ₂ (radd_Inl_iff a b (Sigma i (λ _, j))
              (rmult i (Memrel i) j (Memrel j)) j (Memrel j)) _;
            refine ∧ᵢ (Sigma_left_sub a ip i j hipsub ha)
              (∧ᵢ (Sigma_left_sub b ip i j hipsub hb)
                (∧ₑ₂ (rmult_sub_iff_pair a b ip i j hipsub ha hb) (∧ₑ₂ (∧ₑ₂ hc)))) } }
        { assume b hb hve;
          rewrite hue; rewrite hve;
          apply ∧ᵢ
          { assume h;
            refine ∧ₑ₂ (radd_Inl_Inr_iff a b (Sigma ip (λ _, j))
              (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)) (∧ᵢ ha hb) }
          { assume h;
            refine ∧ₑ₂ (radd_Inl_Inr_iff a b (Sigma i (λ _, j))
              (rmult i (Memrel i) j (Memrel j)) j (Memrel j))
              (∧ᵢ (Sigma_left_sub a ip i j hipsub ha) (hjpsub b hb)) } } }
      { assume a ha hue;
        refine sumE v (Sigma ip (λ _, j)) jp _ hv _ _
        { assume b hb hve;
          rewrite hue; rewrite hve;
          apply ∧ᵢ
          { assume h;
            refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff a b (Sigma i (λ _, j))
              (rmult i (Memrel i) j (Memrel j)) j (Memrel j)) h) }
          { assume h;
            refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff a b (Sigma ip (λ _, j))
              (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)) h) } }
        { assume b hb hve;
          rewrite hue; rewrite hve;
          apply ∧ᵢ
          { assume h;
            have hc : π (a ∈ j ∧ b ∈ j ∧ Pair a b ∈ Memrel j)
              { refine ∧ₑ₁ (radd_Inr_iff a b (Sigma i (λ _, j))
                  (rmult i (Memrel i) j (Memrel j)) j (Memrel j)) h };
            refine ∧ₑ₂ (radd_Inr_iff a b (Sigma ip (λ _, j))
              (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)) _;
            refine ∧ᵢ ha (∧ᵢ hb
              (∧ₑ₂ (Memrel_sub_iff a b jp j hjpsub ha hb) (∧ₑ₂ (∧ₑ₂ hc)))) }
          { assume h;
            have hc : π (a ∈ jp ∧ b ∈ jp ∧ Pair a b ∈ Memrel jp)
              { refine ∧ₑ₁ (radd_Inr_iff a b (Sigma ip (λ _, j))
                  (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)) h };
            refine ∧ₑ₂ (radd_Inr_iff a b (Sigma i (λ _, j))
              (rmult i (Memrel i) j (Memrel j)) j (Memrel j)) _;
            refine ∧ᵢ (hjpsub a ha) (∧ᵢ (hjpsub b hb)
              (∧ₑ₁ (Memrel_sub_iff a b jp j hjpsub ha hb) (∧ₑ₂ (∧ₑ₂ hc)))) } } } };
  have hStepA : π (ordertype (sum (Sigma ip (λ _, j)) jp)
                     (radd (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)) j (Memrel j))
      = ordertype (sum (Sigma ip (λ _, j)) jp)
                  (radd (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)))
    { refine ordertype_eq (id_fun (sum (Sigma ip (λ _, j)) jp))
        (sum (Sigma ip (λ _, j)) jp)
        (radd (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)) j (Memrel j))
        (sum (Sigma ip (λ _, j)) jp)
        (radd (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp))
        hisoA
        (well_ord_radd (Sigma ip (λ _, j)) (rmult ip (Memrel ip) j (Memrel j)) jp (Memrel jp)
          hwoSigIP hwojp) };
  refine eq_trans hStepA hStepB
end;

opaque symbol lt_omult (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (lt k (omult j i)) →
  π (`∃ (jp : τ ι), `∃ (ip : τ ι),
       (k = oadd (omult j ip) jp) ∧ lt jp j ∧ lt ip i) ≔
begin
  assume i j k hOi hOj hlt;
  have hwoSig : π (well_ord (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)))
    { refine well_ord_rmult i (Memrel i) j (Memrel j)
        (well_ord_Memrel i hOi) (well_ord_Memrel j hOj) };
  have hkR : π (k ∈ RepFun (Sigma i (λ _, j))
      (λ z, ordertype (pred (Sigma i (λ _, j)) z (rmult i (Memrel i) j (Memrel j)))
            (rmult i (Memrel i) j (Memrel j))))
    { refine ind_eq (eq_sym (eq_trans (omult_def j i)
          (ordertype_pred_unfold (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)) hwoSig)))
        (λ w, k ∈ w) (ltD k (omult j i) hlt) };
  have hbex : π (Bex (Sigma i (λ _, j))
      (λ z, k = ordertype (pred (Sigma i (λ _, j)) z (rmult i (Memrel i) j (Memrel j)))
                (rmult i (Memrel i) j (Memrel j))))
    { refine ∧ₑ₁ (RepFun_iff k (Sigma i (λ _, j))
        (λ z, ordertype (pred (Sigma i (λ _, j)) z (rmult i (Memrel i) j (Memrel j)))
              (rmult i (Memrel i) j (Memrel j)))) hkR };
  refine ∃ₑ hbex _;
  assume z hz;
  have hzSig : π (z ∈ Sigma i (λ _, j)) { refine ∧ₑ₁ hz };
  have hkeq : π (k = ordertype (pred (Sigma i (λ _, j)) z (rmult i (Memrel i) j (Memrel j)))
                    (rmult i (Memrel i) j (Memrel j))) { refine ∧ₑ₂ hz };
  have hltfz : π (lt (fst z) i) { refine ltI (fst z) i (SigmaD1 z i (λ _, j) hzSig) hOi };
  have hltsz : π (lt (snd z) j) { refine ltI (snd z) j (SigmaD2 z i (λ _, j) hzSig) hOj };
  have hkeq2 : π (k = ordertype (pred (Sigma i (λ _, j)) (Pair (fst z) (snd z))
                     (rmult i (Memrel i) j (Memrel j))) (rmult i (Memrel i) j (Memrel j)))
    { refine ind_eq (Pair_fst_snd z i (λ _, j) hzSig)
        (λ w, k = ordertype (pred (Sigma i (λ _, j)) w (rmult i (Memrel i) j (Memrel j)))
              (rmult i (Memrel i) j (Memrel j))) hkeq };
  have hkfinal : π (k = oadd (omult j (fst z)) (snd z))
    { refine eq_trans hkeq2
        (eq_trans (ordertype_pred_Pair_lemma (fst z) i (snd z) j hltfz hltsz)
          (raw_oadd_eq_oadd (omult j (fst z)) (snd z)
            (Ord_omult j (fst z) hOj (lt_Ord (fst z) i hltfz))
            (lt_Ord (snd z) j hltsz))) };
  refine ∃ᵢ (snd z) (∃ᵢ (fst z) (∧ᵢ hkfinal (∧ᵢ hltsz hltfz)))
end;

opaque symbol omult_oadd_lt (jp j ip i : τ ι) :
  π (lt jp j) → π (lt ip i) →
  π (lt (oadd (omult j ip) jp) (omult j i)) ≔
begin
  assume jp j ip i hltj hlti;
  have hOi : π (Ord i) { refine lt_Ord2 ip i hlti };
  have hOj : π (Ord j) { refine lt_Ord2 jp j hltj };
  have hOip : π (Ord ip) { refine lt_Ord ip i hlti };
  have hOjp : π (Ord jp) { refine lt_Ord jp j hltj };
  have hipi : π (ip ∈ i) { refine ltD ip i hlti };
  have hjpj : π (jp ∈ j) { refine ltD jp j hltj };
  have hOmji : π (Ord (omult j i)) { refine Ord_omult j i hOj hOi };
  have hOmjip : π (Ord (omult j ip)) { refine Ord_omult j ip hOj hOip };
  have hwoSig : π (well_ord (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)))
    { refine well_ord_rmult i (Memrel i) j (Memrel j)
        (well_ord_Memrel i hOi) (well_ord_Memrel j hOj) };
  have hordeq : π (ordertype (pred (Sigma i (λ _, j)) (Pair ip jp)
                     (rmult i (Memrel i) j (Memrel j))) (rmult i (Memrel i) j (Memrel j))
                 = oadd (omult j ip) jp)
    { refine eq_trans (ordertype_pred_Pair_lemma ip i jp j hlti hltj)
        (raw_oadd_eq_oadd (omult j ip) jp hOmjip hOjp) };
  have hmemRep : π (ordertype (pred (Sigma i (λ _, j)) (Pair ip jp)
                     (rmult i (Memrel i) j (Memrel j))) (rmult i (Memrel i) j (Memrel j))
      ∈ RepFun (Sigma i (λ _, j))
          (λ z, ordertype (pred (Sigma i (λ _, j)) z (rmult i (Memrel i) j (Memrel j)))
                (rmult i (Memrel i) j (Memrel j))))
    { refine RepFunI (Pair ip jp) (Sigma i (λ _, j))
        (λ z, ordertype (pred (Sigma i (λ _, j)) z (rmult i (Memrel i) j (Memrel j)))
              (rmult i (Memrel i) j (Memrel j)))
        (SigmaI ip jp i (λ _, j) hipi hjpj) };
  have hmem : π (ordertype (pred (Sigma i (λ _, j)) (Pair ip jp)
                     (rmult i (Memrel i) j (Memrel j))) (rmult i (Memrel i) j (Memrel j))
      ∈ omult j i)
    { refine ind_eq (eq_trans (omult_def j i)
          (ordertype_pred_unfold (Sigma i (λ _, j)) (rmult i (Memrel i) j (Memrel j)) hwoSig))
        (λ w, ordertype (pred (Sigma i (λ _, j)) (Pair ip jp)
                (rmult i (Memrel i) j (Memrel j))) (rmult i (Memrel i) j (Memrel j)) ∈ w)
        hmemRep };
  refine ltI (oadd (omult j ip) jp) (omult j i)
    (ind_eq (eq_sym hordeq) (λ w, w ∈ omult j i) hmem) hOmji
end;

opaque symbol omult_unfold (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (omult j i
     = Union (RepFun j (λ jp,
         Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp)))))) ≔
begin
  assume i j hOi hOj;
  have hOmji : π (Ord (omult j i)) { refine Ord_omult j i hOj hOi };
  refine equality_iffI (omult j i)
    (Union (RepFun j (λ jp,
       Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp)))))) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hex : π (`∃ (jp : τ ι), `∃ (ip : τ ι),
                   (x = oadd (omult j ip) jp) ∧ lt jp j ∧ lt ip i)
      { refine lt_omult i j x hOi hOj (ltI x (omult j i) hx hOmji) };
    refine ∃ₑ hex _; assume jp hjp;
    refine ∃ₑ hjp _; assume ip hip;
    have hjpj : π (jp ∈ j) { refine ltD jp j (∧ₑ₁ (∧ₑ₂ hip)) };
    have hipi : π (ip ∈ i) { refine ltD ip i (∧ₑ₂ (∧ₑ₂ hip)) };
    have hxsing : π (x ∈ singleton (oadd (omult j ip) jp))
      { refine ind_eq (∧ₑ₁ hip) (λ w, w ∈ singleton (oadd (omult j ip) jp))
          (singletonI (oadd (omult j ip) jp)) };
    have hxUi : π (x ∈ Union (RepFun i (λ ip2, singleton (oadd (omult j ip2) jp))))
      { refine UnionI x (singleton (oadd (omult j ip) jp))
          (RepFun i (λ ip2, singleton (oadd (omult j ip2) jp))) hxsing
          (RepFunI ip i (λ ip2, singleton (oadd (omult j ip2) jp)) hipi) };
    refine UnionI x (Union (RepFun i (λ ip2, singleton (oadd (omult j ip2) jp))))
      (RepFun j (λ jp2, Union (RepFun i (λ ip2, singleton (oadd (omult j ip2) jp2)))))
      hxUi
      (RepFunI jp j
        (λ jp2, Union (RepFun i (λ ip2, singleton (oadd (omult j ip2) jp2)))) hjpj) }
  { assume hx;
    have hbex : π (Bex (RepFun j (λ jp,
                     Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp)))))
                   (λ B, x ∈ B))
      { refine UnionE x (RepFun j (λ jp,
          Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp))))) hx };
    refine ∃ₑ hbex _; assume B hB;
    have hbex2 : π (Bex j (λ jp,
                     B = Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp)))))
      { refine ∧ₑ₁ (RepFun_iff B j
          (λ jp, Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp))))) (∧ₑ₁ hB) };
    refine ∃ₑ hbex2 _; assume jp hjp;
    have hjpj : π (jp ∈ j) { refine ∧ₑ₁ hjp };
    have hxU2 : π (x ∈ Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp))))
      { refine ind_eq (eq_sym (∧ₑ₂ hjp)) (λ w, x ∈ w) (∧ₑ₂ hB) };
    have hbex3 : π (Bex (RepFun i (λ ip, singleton (oadd (omult j ip) jp)))
                     (λ C, x ∈ C))
      { refine UnionE x (RepFun i (λ ip, singleton (oadd (omult j ip) jp))) hxU2 };
    refine ∃ₑ hbex3 _; assume C hC;
    have hbex4 : π (Bex i (λ ip, C = singleton (oadd (omult j ip) jp)))
      { refine ∧ₑ₁ (RepFun_iff C i (λ ip, singleton (oadd (omult j ip) jp))) (∧ₑ₁ hC) };
    refine ∃ₑ hbex4 _; assume ip hip;
    have hipi : π (ip ∈ i) { refine ∧ₑ₁ hip };
    have hxsing : π (x ∈ singleton (oadd (omult j ip) jp))
      { refine ind_eq (eq_sym (∧ₑ₂ hip)) (λ w, x ∈ w) (∧ₑ₂ hC) };
    have hxeq : π (x = oadd (omult j ip) jp)
      { refine ∧ₑ₁ (singleton_iff x (oadd (omult j ip) jp)) hxsing };
    refine ind_eq hxeq (λ w, w ∈ omult j i)
      (ltD (oadd (omult j ip) jp) (omult j i)
        (omult_oadd_lt jp j ip i (ltI jp j hjpj hOj) (ltI ip i hipi hOi))) }
end;

opaque symbol omult_0 (i : τ ι) :
  π (omult i empty = empty) ≔
begin
  assume i;
  rewrite omult_def;
  have hSig : π (Sigma empty (λ _, i) = empty)
    { refine equals0I (Sigma empty (λ _, i)) _;
      assume p hp;
      refine emptyE (fst p) (SigmaD1 p empty (λ _, i) hp) };
  rewrite hSig;
  refine ordertype_0 (rmult empty (Memrel empty) i (Memrel i))
end;

opaque symbol omult_0_left (i : τ ι) :
  π (omult empty i = empty) ≔
begin
  assume i;
  rewrite omult_def;
  have hSig : π (Sigma i (λ _, empty) = empty)
    { refine equals0I (Sigma i (λ _, empty)) _;
      assume p hp;
      refine emptyE (snd p) (SigmaD2 p i (λ _, empty) hp) };
  rewrite hSig;
  refine ordertype_0 (rmult i (Memrel i) empty (Memrel empty))
end;

opaque symbol omult_1 (i : τ ι) :
  π (Ord i) → π (omult i (succ empty) = i) ≔
begin
  assume i hOi;
  have hbij : π (Lambda (Sigma (succ empty) (λ _, i)) (λ z, snd z)
      ∈ bij (Sigma (succ empty) (λ _, i)) i)
    { refine lam_bijective (Sigma (succ empty) (λ _, i)) i
        (λ z, snd z) (λ z, Pair empty z) _ _ _ _
      { assume z hz; refine SigmaD2 z (succ empty) (λ _, i) hz }
      { assume z hz; refine SigmaI empty z (succ empty) (λ _, i) (succI1 empty) hz }
      { assume z hz;
        have hfst : π (fst z ∈ succ empty) { refine SigmaD1 z (succ empty) (λ _, i) hz };
        have hfe : π (fst z = empty)
          { refine ∨ₑ (∧ₑ₁ (succ_iff (fst z) empty) hfst) _ _
            { assume h; refine h } { assume h; refine ⊥ₑ (emptyE (fst z) h) } };
        refine eq_trans
          (ind_eq hfe (λ w, Pair empty (snd z) = Pair w (snd z))
            (eq_refl (Pair empty (snd z))))
          (Pair_fst_snd z (succ empty) (λ _, i) hz) }
      { assume z hz; refine snd_conv empty z } };
  have hiso : π (Lambda (Sigma (succ empty) (λ _, i)) (λ z, snd z)
      ∈ ord_iso (Sigma (succ empty) (λ _, i))
                (rmult (succ empty) (Memrel (succ empty)) i (Memrel i))
                i (Memrel i))
    { refine ord_isoI (Lambda (Sigma (succ empty) (λ _, i)) (λ z, snd z))
        (Sigma (succ empty) (λ _, i))
        (rmult (succ empty) (Memrel (succ empty)) i (Memrel i)) i (Memrel i) hbij _;
      assume x1 hx1 x2 hx2;
      rewrite (beta (Sigma (succ empty) (λ _, i)) (λ z, snd z) x1 hx1);
      rewrite (beta (Sigma (succ empty) (λ _, i)) (λ z, snd z) x2 hx2);
      have hfst1 : π (fst x1 ∈ succ empty) { refine SigmaD1 x1 (succ empty) (λ _, i) hx1 };
      have hfst2 : π (fst x2 ∈ succ empty) { refine SigmaD1 x2 (succ empty) (λ _, i) hx2 };
      have hsnd1 : π (snd x1 ∈ i) { refine SigmaD2 x1 (succ empty) (λ _, i) hx1 };
      have hsnd2 : π (snd x2 ∈ i) { refine SigmaD2 x2 (succ empty) (λ _, i) hx2 };
      have hfe1 : π (fst x1 = empty)
        { refine ∨ₑ (∧ₑ₁ (succ_iff (fst x1) empty) hfst1) _ _
          { assume h; refine h } { assume h; refine ⊥ₑ (emptyE (fst x1) h) } };
      have hfe2 : π (fst x2 = empty)
        { refine ∨ₑ (∧ₑ₁ (succ_iff (fst x2) empty) hfst2) _ _
          { assume h; refine h } { assume h; refine ⊥ₑ (emptyE (fst x2) h) } };
      have hp1 : π (Pair (fst x1) (snd x1) = x1)
        { refine Pair_fst_snd x1 (succ empty) (λ _, i) hx1 };
      have hp2 : π (Pair (fst x2) (snd x2) = x2)
        { refine Pair_fst_snd x2 (succ empty) (λ _, i) hx2 };
      apply ∧ᵢ
      { assume hr;
        have hr2 : π (Pair (Pair (fst x1) (snd x1)) (Pair (fst x2) (snd x2))
                      ∈ rmult (succ empty) (Memrel (succ empty)) i (Memrel i))
          { refine ind_eq hp1
              (λ w, Pair w (Pair (fst x2) (snd x2))
                    ∈ rmult (succ empty) (Memrel (succ empty)) i (Memrel i))
              (ind_eq hp2
                (λ w, Pair x1 w ∈ rmult (succ empty) (Memrel (succ empty)) i (Memrel i))
                hr) };
        have hdisj : π ((Pair (fst x1) (fst x2) ∈ Memrel (succ empty)
                          ∧ fst x1 ∈ succ empty ∧ fst x2 ∈ succ empty
                          ∧ snd x1 ∈ i ∧ snd x2 ∈ i)
                        ∨ (Pair (snd x1) (snd x2) ∈ Memrel i
                          ∧ fst x1 = fst x2 ∧ fst x2 ∈ succ empty
                          ∧ snd x1 ∈ i ∧ snd x2 ∈ i))
          { refine ∧ₑ₁ (rmult_iff (fst x1) (snd x1) (fst x2) (snd x2)
              (succ empty) (Memrel (succ empty)) i (Memrel i)) hr2 };
        refine ∨ₑ hdisj _ _
        { assume hl;
          have hm : π (fst x1 ∈ succ empty ∧ fst x2 ∈ succ empty ∧ fst x1 ∈ fst x2)
            { refine MemrelE (fst x1) (fst x2) (succ empty) (∧ₑ₁ hl) };
          refine ⊥ₑ (emptyE (fst x1)
            (ind_eq (eq_sym hfe2) (λ w, fst x1 ∈ w) (∧ₑ₂ (∧ₑ₂ hm)))) }
        { assume hr3; refine ∧ₑ₁ hr3 } }
      { assume hm;
        have hr2 : π (Pair (Pair (fst x1) (snd x1)) (Pair (fst x2) (snd x2))
                      ∈ rmult (succ empty) (Memrel (succ empty)) i (Memrel i))
          { refine ∧ₑ₂ (rmult_iff (fst x1) (snd x1) (fst x2) (snd x2)
              (succ empty) (Memrel (succ empty)) i (Memrel i))
              (∨ᵢ₂ (∧ᵢ hm (∧ᵢ (eq_trans hfe1 (eq_sym hfe2))
                (∧ᵢ hfst2 (∧ᵢ hsnd1 hsnd2))))) };
        refine ind_eq (eq_sym hp1)
          (λ w, Pair w x2 ∈ rmult (succ empty) (Memrel (succ empty)) i (Memrel i))
          (ind_eq (eq_sym hp2)
            (λ w, Pair (Pair (fst x1) (snd x1)) w
                  ∈ rmult (succ empty) (Memrel (succ empty)) i (Memrel i)) hr2) } };
  rewrite (omult_def i (succ empty));
  refine eq_trans
    (ordertype_eq (Lambda (Sigma (succ empty) (λ _, i)) (λ z, snd z))
      (Sigma (succ empty) (λ _, i))
      (rmult (succ empty) (Memrel (succ empty)) i (Memrel i)) i (Memrel i)
      hiso (well_ord_Memrel i hOi))
    (ordertype_Memrel i hOi)
end;

opaque symbol omult_1_left (i : τ ι) :
  π (Ord i) → π (omult (succ empty) i = i) ≔
begin
  assume i hOi;
  have hbij : π (Lambda (Sigma i (λ _, succ empty)) (λ z, fst z)
      ∈ bij (Sigma i (λ _, succ empty)) i)
    { refine lam_bijective (Sigma i (λ _, succ empty)) i
        (λ z, fst z) (λ z, Pair z empty) _ _ _ _
      { assume z hz; refine SigmaD1 z i (λ _, succ empty) hz }
      { assume z hz; refine SigmaI z empty i (λ _, succ empty) hz (succI1 empty) }
      { assume z hz;
        have hsnd : π (snd z ∈ succ empty) { refine SigmaD2 z i (λ _, succ empty) hz };
        have hse : π (snd z = empty)
          { refine ∨ₑ (∧ₑ₁ (succ_iff (snd z) empty) hsnd) _ _
            { assume h; refine h } { assume h; refine ⊥ₑ (emptyE (snd z) h) } };
        refine eq_trans
          (ind_eq hse (λ w, Pair (fst z) empty = Pair (fst z) w)
            (eq_refl (Pair (fst z) empty)))
          (Pair_fst_snd z i (λ _, succ empty) hz) }
      { assume z hz; refine fst_conv z empty } };
  have hiso : π (Lambda (Sigma i (λ _, succ empty)) (λ z, fst z)
      ∈ ord_iso (Sigma i (λ _, succ empty))
                (rmult i (Memrel i) (succ empty) (Memrel (succ empty)))
                i (Memrel i))
    { refine ord_isoI (Lambda (Sigma i (λ _, succ empty)) (λ z, fst z))
        (Sigma i (λ _, succ empty))
        (rmult i (Memrel i) (succ empty) (Memrel (succ empty))) i (Memrel i) hbij _;
      assume x1 hx1 x2 hx2;
      rewrite (beta (Sigma i (λ _, succ empty)) (λ z, fst z) x1 hx1);
      rewrite (beta (Sigma i (λ _, succ empty)) (λ z, fst z) x2 hx2);
      have hfst1 : π (fst x1 ∈ i) { refine SigmaD1 x1 i (λ _, succ empty) hx1 };
      have hfst2 : π (fst x2 ∈ i) { refine SigmaD1 x2 i (λ _, succ empty) hx2 };
      have hsnd1 : π (snd x1 ∈ succ empty) { refine SigmaD2 x1 i (λ _, succ empty) hx1 };
      have hsnd2 : π (snd x2 ∈ succ empty) { refine SigmaD2 x2 i (λ _, succ empty) hx2 };
      have hse2 : π (snd x2 = empty)
        { refine ∨ₑ (∧ₑ₁ (succ_iff (snd x2) empty) hsnd2) _ _
          { assume h; refine h } { assume h; refine ⊥ₑ (emptyE (snd x2) h) } };
      have hp1 : π (Pair (fst x1) (snd x1) = x1)
        { refine Pair_fst_snd x1 i (λ _, succ empty) hx1 };
      have hp2 : π (Pair (fst x2) (snd x2) = x2)
        { refine Pair_fst_snd x2 i (λ _, succ empty) hx2 };
      apply ∧ᵢ
      { assume hr;
        have hr2 : π (Pair (Pair (fst x1) (snd x1)) (Pair (fst x2) (snd x2))
                      ∈ rmult i (Memrel i) (succ empty) (Memrel (succ empty)))
          { refine ind_eq hp1
              (λ w, Pair w (Pair (fst x2) (snd x2))
                    ∈ rmult i (Memrel i) (succ empty) (Memrel (succ empty)))
              (ind_eq hp2
                (λ w, Pair x1 w ∈ rmult i (Memrel i) (succ empty) (Memrel (succ empty)))
                hr) };
        have hdisj : π ((Pair (fst x1) (fst x2) ∈ Memrel i
                          ∧ fst x1 ∈ i ∧ fst x2 ∈ i
                          ∧ snd x1 ∈ succ empty ∧ snd x2 ∈ succ empty)
                        ∨ (Pair (snd x1) (snd x2) ∈ Memrel (succ empty)
                          ∧ fst x1 = fst x2 ∧ fst x2 ∈ i
                          ∧ snd x1 ∈ succ empty ∧ snd x2 ∈ succ empty))
          { refine ∧ₑ₁ (rmult_iff (fst x1) (snd x1) (fst x2) (snd x2)
              i (Memrel i) (succ empty) (Memrel (succ empty))) hr2 };
        refine ∨ₑ hdisj _ _
        { assume hl; refine ∧ₑ₁ hl }
        { assume hr3;
          have hm : π (snd x1 ∈ succ empty ∧ snd x2 ∈ succ empty ∧ snd x1 ∈ snd x2)
            { refine MemrelE (snd x1) (snd x2) (succ empty) (∧ₑ₁ hr3) };
          refine ⊥ₑ (emptyE (snd x1)
            (ind_eq (eq_sym hse2) (λ w, snd x1 ∈ w) (∧ₑ₂ (∧ₑ₂ hm)))) } }
      { assume hm;
        have hr2 : π (Pair (Pair (fst x1) (snd x1)) (Pair (fst x2) (snd x2))
                      ∈ rmult i (Memrel i) (succ empty) (Memrel (succ empty)))
          { refine ∧ₑ₂ (rmult_iff (fst x1) (snd x1) (fst x2) (snd x2)
              i (Memrel i) (succ empty) (Memrel (succ empty)))
              (∨ᵢ₁ (∧ᵢ hm (∧ᵢ hfst1 (∧ᵢ hfst2 (∧ᵢ hsnd1 hsnd2))))) };
        refine ind_eq (eq_sym hp1)
          (λ w, Pair w x2 ∈ rmult i (Memrel i) (succ empty) (Memrel (succ empty)))
          (ind_eq (eq_sym hp2)
            (λ w, Pair (Pair (fst x1) (snd x1)) w
                  ∈ rmult i (Memrel i) (succ empty) (Memrel (succ empty))) hr2) } };
  rewrite (omult_def (succ empty) i);
  refine eq_trans
    (ordertype_eq (Lambda (Sigma i (λ _, succ empty)) (λ z, fst z))
      (Sigma i (λ _, succ empty))
      (rmult i (Memrel i) (succ empty) (Memrel (succ empty))) i (Memrel i)
      hiso (well_ord_Memrel i hOi))
    (ordertype_Memrel i hOi)
end;

opaque symbol oadd_omult_distrib (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord k) →
  π (omult i (oadd j k) = oadd (omult i j) (omult i k)) ≔
begin
  assume i j k hOi hOj hOk;
  have woi : π (well_ord i (Memrel i)) { refine well_ord_Memrel i hOi };
  have woj : π (well_ord j (Memrel j)) { refine well_ord_Memrel j hOj };
  have wok : π (well_ord k (Memrel k)) { refine well_ord_Memrel k hOk };
  have wojk : π (well_ord (sum j k) (radd j (Memrel j) k (Memrel k)))
    { refine well_ord_radd j (Memrel j) k (Memrel k) woj wok };
  have woSj : π (well_ord (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
    { refine well_ord_rmult j (Memrel j) i (Memrel i) woj woi };
  have woSk : π (well_ord (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
    { refine well_ord_rmult k (Memrel k) i (Memrel i) wok woi };
  have hOojk : π (Ord (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))))
    { refine Ord_ordertype (sum j k) (radd j (Memrel j) k (Memrel k)) wojk };
  have hOP : π (Ord (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
    { refine Ord_ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)) woSj };
  have hOQ : π (Ord (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))))
    { refine Ord_ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)) woSk };
  rewrite (omult_def i (oadd j k));
  rewrite (oadd_ot_eq j k hOj hOk);
  rewrite (oadd_ot_eq (omult i j) (omult i k)
    (Ord_omult i j hOi hOj) (Ord_omult i k hOi hOk));
  rewrite (omult_def i j);
  rewrite (omult_def i k);
  have step1 : π (ordertype (Sigma (sum j k) (λ _, i))
                     (rmult (sum j k) (radd j (Memrel j) k (Memrel k)) i (Memrel i))
      = ordertype (Sigma (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))) (λ _, i))
          (rmult (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))
                 (Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))) i (Memrel i)))
    { refine ordertype_eq _
        (Sigma (sum j k) (λ _, i))
        (rmult (sum j k) (radd j (Memrel j) k (Memrel k)) i (Memrel i))
        (Sigma (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))) (λ _, i))
        (rmult (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))
               (Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))) i (Memrel i))
        (prod_ord_iso_cong (ordermap (sum j k) (radd j (Memrel j) k (Memrel k))) (id_fun i)
          (sum j k) (radd j (Memrel j) k (Memrel k))
          (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))
          (Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))))
          i (Memrel i) i (Memrel i)
          (ordertype_ord_iso (sum j k) (radd j (Memrel j) k (Memrel k)) wojk)
          (ord_iso_refl i (Memrel i)))
        (well_ord_rmult (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))
          (Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k)))) i (Memrel i)
          (well_ord_Memrel (ordertype (sum j k) (radd j (Memrel j) k (Memrel k))) hOojk) woi) };
  have step2 : π (ordertype (Sigma (sum j k) (λ _, i))
                     (rmult (sum j k) (radd j (Memrel j) k (Memrel k)) i (Memrel i))
      = ordertype (sum (Sigma j (λ _, i)) (Sigma k (λ _, i)))
          (radd (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))
                (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))))
    { refine ordertype_eq _
        (Sigma (sum j k) (λ _, i))
        (rmult (sum j k) (radd j (Memrel j) k (Memrel k)) i (Memrel i))
        (sum (Sigma j (λ _, i)) (Sigma k (λ _, i)))
        (radd (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))
              (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
        (sum_prod_distrib_ord_iso j (Memrel j) k (Memrel k) i (Memrel i))
        (well_ord_radd (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))
          (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)) woSj woSk) };
  have step3 : π (ordertype (sum (Sigma j (λ _, i)) (Sigma k (λ _, i)))
                     (radd (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))
                           (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
      = ordertype (sum (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
                       (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))))
          (radd (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
                (Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
                (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
                (Memrel (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))))))
    { refine ordertype_eq _
        (sum (Sigma j (λ _, i)) (Sigma k (λ _, i)))
        (radd (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))
              (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
        (sum (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
             (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))))
        (radd (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
              (Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
              (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
              (Memrel (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))))
        (sum_ord_iso_cong (ordermap (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
          (ordermap (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
          (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))
          (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
          (Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
          (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))
          (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
          (Memrel (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))))
          (ordertype_ord_iso (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)) woSj)
          (ordertype_ord_iso (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)) woSk))
        (well_ord_radd (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
          (Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
          (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i)))
          (Memrel (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))))
          (well_ord_Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))) hOP)
          (well_ord_Memrel (ordertype (Sigma k (λ _, i)) (rmult k (Memrel k) i (Memrel i))) hOQ)) };
  refine eq_trans (eq_sym step1) (eq_trans step2 step3)
end;

opaque symbol omult_succ (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (omult i (succ j) = oadd (omult i j) i) ≔
begin
  assume i j hOi hOj;
  have h1 : π (omult i (oadd j (succ empty)) = omult i (succ j))
    { rewrite (oadd_1 j hOj); reflexivity };
  refine eq_trans (eq_sym h1)
    (eq_trans (oadd_omult_distrib i j (succ empty) hOi hOj (Ord_succ empty Ord_0))
      (ind_eq (omult_1 i hOi) (λ w, oadd (omult i j) w = oadd (omult i j) i)
        (eq_refl (oadd (omult i j) i))))
end;

opaque symbol omult_assoc (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord k) →
  π (omult (omult i j) k = omult i (omult j k)) ≔
begin
  assume i j k hOi hOj hOk;
  have woi : π (well_ord i (Memrel i)) { refine well_ord_Memrel i hOi };
  have woj : π (well_ord j (Memrel j)) { refine well_ord_Memrel j hOj };
  have wok : π (well_ord k (Memrel k)) { refine well_ord_Memrel k hOk };
  have woSj : π (well_ord (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
    { refine well_ord_rmult j (Memrel j) i (Memrel i) woj woi };
  have woSkj : π (well_ord (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)))
    { refine well_ord_rmult k (Memrel k) j (Memrel j) wok woj };
  have hOP : π (Ord (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
    { refine Ord_ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)) woSj };
  have hOR : π (Ord (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))))
    { refine Ord_ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)) woSkj };
  rewrite (omult_def (omult i j) k);
  rewrite (omult_def i (omult j k));
  rewrite (omult_def i j);
  rewrite (omult_def j k);
  have step1 : π (ordertype (Sigma k (λ _, Sigma j (λ _, i)))
                     (rmult k (Memrel k) (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
      = ordertype (Sigma k (λ _, ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
          (rmult k (Memrel k)
                 (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
                 (Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))))
    { refine ordertype_eq _
        (Sigma k (λ _, Sigma j (λ _, i)))
        (rmult k (Memrel k) (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
        (Sigma k (λ _, ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
        (rmult k (Memrel k)
               (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
               (Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))))
        (prod_ord_iso_cong (id_fun k)
          (ordermap (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
          k (Memrel k) k (Memrel k)
          (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))
          (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
          (Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))))
          (ord_iso_refl k (Memrel k))
          (ordertype_ord_iso (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)) woSj))
        (well_ord_rmult k (Memrel k)
          (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
          (Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))) wok
          (well_ord_Memrel (ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i))) hOP)) };
  have step2 : π (ordertype (Sigma k (λ _, Sigma j (λ _, i)))
                     (rmult k (Memrel k) (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
      = ordertype (Sigma (Sigma k (λ _, j)) (λ _, i))
          (rmult (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)) i (Memrel i)))
    { refine ordertype_eq _
        (Sigma k (λ _, Sigma j (λ _, i)))
        (rmult k (Memrel k) (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
        (Sigma (Sigma k (λ _, j)) (λ _, i))
        (rmult (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)) i (Memrel i))
        (ord_iso_sym _
          (Sigma (Sigma k (λ _, j)) (λ _, i))
          (rmult (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)) i (Memrel i))
          (Sigma k (λ _, Sigma j (λ _, i)))
          (rmult k (Memrel k) (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i)))
          (prod_assoc_ord_iso k (Memrel k) j (Memrel j) i (Memrel i)))
        (well_ord_rmult (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)) i (Memrel i)
          woSkj woi) };
  have step3 : π (ordertype (Sigma (Sigma k (λ _, j)) (λ _, i))
                     (rmult (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)) i (Memrel i))
      = ordertype (Sigma (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))) (λ _, i))
          (rmult (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)))
                 (Memrel (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))))
                 i (Memrel i)))
    { refine ordertype_eq _
        (Sigma (Sigma k (λ _, j)) (λ _, i))
        (rmult (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)) i (Memrel i))
        (Sigma (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))) (λ _, i))
        (rmult (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)))
               (Memrel (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))))
               i (Memrel i))
        (prod_ord_iso_cong
          (ordermap (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))) (id_fun i)
          (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))
          (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)))
          (Memrel (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))))
          i (Memrel i) i (Memrel i)
          (ordertype_ord_iso (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)) woSkj)
          (ord_iso_refl i (Memrel i)))
        (well_ord_rmult (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)))
          (Memrel (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j)))) i (Memrel i)
          (well_ord_Memrel (ordertype (Sigma k (λ _, j)) (rmult k (Memrel k) j (Memrel j))) hOR)
          woi) };
  refine eq_trans (eq_sym step1) (eq_trans step2 step3)
end;

opaque symbol omult_UN (i A : τ ι) (jf : τ ι → τ ι) :
  π (Ord i) → π (Ball A (λ x, Ord (jf x))) →
  π (omult i (Union (RepFun A (λ x, jf x)))
     = Union (RepFun A (λ x, omult i (jf x)))) ≔
begin
  assume i A jf hOi hBord;
  have hOU : π (Ord (Union (RepFun A (λ x, jf x))))
    { refine Ord_Union (RepFun A (λ x, jf x))
        (ballI (RepFun A (λ x, jf x)) (λ z, Ord z) _);
      assume z hz;
      refine ∃ₑ (∧ₑ₁ (RepFun_iff z A (λ x, jf x)) hz) _;
      assume x hx;
      refine ind_eq (∧ₑ₂ hx) (λ w, Ord w) (hBord x (∧ₑ₁ hx)) };
  refine equality_iffI (omult i (Union (RepFun A (λ x, jf x))))
    (Union (RepFun A (λ x, omult i (jf x)))) _;
  assume y;
  apply ∧ᵢ
  { assume hy;
    have hex : π (`∃ (jp : τ ι), `∃ (ip : τ ι),
        (y = oadd (omult i ip) jp) ∧ lt jp i ∧ lt ip (Union (RepFun A (λ x, jf x))))
      { refine lt_omult (Union (RepFun A (λ x, jf x))) i y hOU hOi
          (ltI y (omult i (Union (RepFun A (λ x, jf x)))) hy
            (Ord_omult i (Union (RepFun A (λ x, jf x))) hOi hOU)) };
    refine ∃ₑ hex _; assume jp hjp;
    refine ∃ₑ hjp _; assume ip hip;
    have hltjp : π (lt jp i) { refine ∧ₑ₁ (∧ₑ₂ hip) };
    have hb1 : π (Bex (RepFun A (λ x, jf x)) (λ C, ip ∈ C))
      { refine UnionE ip (RepFun A (λ x, jf x))
          (ltD ip (Union (RepFun A (λ x, jf x))) (∧ₑ₂ (∧ₑ₂ hip))) };
    refine ∃ₑ hb1 _; assume C hC;
    have hb2 : π (Bex A (λ x, C = jf x))
      { refine ∧ₑ₁ (RepFun_iff C A (λ x, jf x)) (∧ₑ₁ hC) };
    refine ∃ₑ hb2 _; assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    have hipjfx : π (ip ∈ jf x)
      { refine ind_eq (eq_sym (∧ₑ₂ hx)) (λ w, ip ∈ w) (∧ₑ₂ hC) };
    have hltmem : π (lt (oadd (omult i ip) jp) (omult i (jf x)))
      { refine omult_oadd_lt jp i ip (jf x) hltjp
          (ltI ip (jf x) hipjfx (hBord x hxA)) };
    have hymem : π (y ∈ omult i (jf x))
      { refine ind_eq (∧ₑ₁ hip) (λ w, w ∈ omult i (jf x))
          (ltD (oadd (omult i ip) jp) (omult i (jf x)) hltmem) };
    refine UnionI y (omult i (jf x)) (RepFun A (λ x2, omult i (jf x2))) hymem
      (RepFunI x A (λ x2, omult i (jf x2)) hxA) }
  { assume hy;
    have hbex : π (Bex (RepFun A (λ x, omult i (jf x))) (λ B, y ∈ B))
      { refine UnionE y (RepFun A (λ x, omult i (jf x))) hy };
    refine ∃ₑ hbex _; assume B hB;
    have hb2 : π (Bex A (λ x, B = omult i (jf x)))
      { refine ∧ₑ₁ (RepFun_iff B A (λ x, omult i (jf x))) (∧ₑ₁ hB) };
    refine ∃ₑ hb2 _; assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    have hOjfx : π (Ord (jf x)) { refine hBord x hxA };
    have hymem : π (y ∈ omult i (jf x))
      { refine ind_eq (eq_sym (∧ₑ₂ hx)) (λ w, y ∈ w) (∧ₑ₂ hB) };
    have hex : π (`∃ (jp : τ ι), `∃ (ip : τ ι),
        (y = oadd (omult i ip) jp) ∧ lt jp i ∧ lt ip (jf x))
      { refine lt_omult (jf x) i y hOjfx hOi
          (ltI y (omult i (jf x)) hymem (Ord_omult i (jf x) hOi hOjfx)) };
    refine ∃ₑ hex _; assume jp hjp;
    refine ∃ₑ hjp _; assume ip hip;
    have hltjp : π (lt jp i) { refine ∧ₑ₁ (∧ₑ₂ hip) };
    have hipU : π (ip ∈ Union (RepFun A (λ x2, jf x2)))
      { refine UnionI ip (jf x) (RepFun A (λ x2, jf x2))
          (ltD ip (jf x) (∧ₑ₂ (∧ₑ₂ hip))) (RepFunI x A (λ x2, jf x2) hxA) };
    have hltmem : π (lt (oadd (omult i ip) jp)
                       (omult i (Union (RepFun A (λ x2, jf x2)))))
      { refine omult_oadd_lt jp i ip (Union (RepFun A (λ x2, jf x2))) hltjp
          (ltI ip (Union (RepFun A (λ x2, jf x2))) hipU hOU) };
    refine ind_eq (∧ₑ₁ hip) (λ w, w ∈ omult i (Union (RepFun A (λ x2, jf x2))))
      (ltD (oadd (omult i ip) jp) (omult i (Union (RepFun A (λ x2, jf x2)))) hltmem) }
end;

opaque symbol omult_Limit (i j : τ ι) :
  π (Ord i) → π (Limit j) →
  π (omult i j = Union (RepFun j (λ k, omult i k))) ≔
begin
  assume i j hOi hLj;
  have hOj : π (Ord j) { refine Limit_is_Ord j hLj };
  refine equality_iffI (omult i j) (Union (RepFun j (λ k, omult i k))) _;
  assume y;
  apply ∧ᵢ
  { assume hy;
    have hex : π (`∃ (jp : τ ι), `∃ (ip : τ ι),
        (y = oadd (omult i ip) jp) ∧ lt jp i ∧ lt ip j)
      { refine lt_omult j i y hOj hOi
          (ltI y (omult i j) hy (Ord_omult i j hOi hOj)) };
    refine ∃ₑ hex _; assume jp hjp;
    refine ∃ₑ hjp _; assume ip hip;
    have hltjp : π (lt jp i) { refine ∧ₑ₁ (∧ₑ₂ hip) };
    have hltip : π (lt ip j) { refine ∧ₑ₂ (∧ₑ₂ hip) };
    have hOip : π (Ord ip) { refine lt_Ord ip j hltip };
    have hsip : π (succ ip ∈ j) { refine Limit_has_succ j ip hLj (ltD ip j hltip) };
    have hltmem : π (lt (oadd (omult i ip) jp) (omult i (succ ip)))
      { refine omult_oadd_lt jp i ip (succ ip) hltjp
          (ltI ip (succ ip) (succI1 ip) (Ord_succ ip hOip)) };
    refine UnionI y (omult i (succ ip)) (RepFun j (λ k, omult i k))
      (ind_eq (∧ₑ₁ hip) (λ w, w ∈ omult i (succ ip))
        (ltD (oadd (omult i ip) jp) (omult i (succ ip)) hltmem))
      (RepFunI (succ ip) j (λ k, omult i k) hsip) }
  { assume hy;
    have hbex : π (Bex (RepFun j (λ k, omult i k)) (λ B, y ∈ B))
      { refine UnionE y (RepFun j (λ k, omult i k)) hy };
    refine ∃ₑ hbex _; assume B hB;
    have hb2 : π (Bex j (λ k, B = omult i k))
      { refine ∧ₑ₁ (RepFun_iff B j (λ k, omult i k)) (∧ₑ₁ hB) };
    refine ∃ₑ hb2 _; assume k hk;
    have hkj : π (k ∈ j) { refine ∧ₑ₁ hk };
    have hOk : π (Ord k) { refine Ord_in_Ord j k hOj hkj };
    have hymem : π (y ∈ omult i k)
      { refine ind_eq (eq_sym (∧ₑ₂ hk)) (λ w, y ∈ w) (∧ₑ₂ hB) };
    have hex : π (`∃ (jp : τ ι), `∃ (ip : τ ι),
        (y = oadd (omult i ip) jp) ∧ lt jp i ∧ lt ip k)
      { refine lt_omult k i y hOk hOi
          (ltI y (omult i k) hymem (Ord_omult i k hOi hOk)) };
    refine ∃ₑ hex _; assume jp hjp;
    refine ∃ₑ hjp _; assume ip hip;
    have hltjp : π (lt jp i) { refine ∧ₑ₁ (∧ₑ₂ hip) };
    have hipj : π (ip ∈ j)
      { refine (OrdmemD j k hkj hOj) ip (ltD ip k (∧ₑ₂ (∧ₑ₂ hip))) };
    have hltmem : π (lt (oadd (omult i ip) jp) (omult i j))
      { refine omult_oadd_lt jp i ip j hltjp (ltI ip j hipj hOj) };
    refine ind_eq (∧ₑ₁ hip) (λ w, w ∈ omult i j)
      (ltD (oadd (omult i ip) jp) (omult i j) hltmem) }
end;

opaque symbol lt_omult1 (k i j : τ ι) :
  π (lt k i) → π (lt empty j) → π (lt k (omult i j)) ≔
begin
  assume k i j hki h0j;
  have hOk : π (Ord k) { refine lt_Ord k i hki };
  have he : π (oadd (omult i empty) k = k)
    { refine ind_eq (omult_0 i) (λ w, oadd w k = k) (oadd_0_left k hOk) };
  refine ind_eq (eq_sym he) (λ w, lt w (omult i j))
    (omult_oadd_lt k i empty j hki h0j)
end;

opaque symbol omult_le_self (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (le i (omult i j)) ≔
begin
  assume i j hOi h0j;
  have hOj : π (Ord j) { refine lt_Ord2 empty j h0j };
  refine all_lt_imp_le (omult i j) i (Ord_omult i j hOi hOj) hOi
    (ballI i (λ x, x ∈ omult i j) _);
  assume x hx;
  refine ltD x (omult i j) (lt_omult1 x i j (ltI x i hx hOi) h0j)
end;

opaque symbol omult_le_mono1 (k j i : τ ι) :
  π (le k j) → π (Ord i) → π (le (omult k i) (omult j i)) ≔
begin
  assume k j i hkj hOi;
  have hOk : π (Ord k) { refine lt_Ord k (succ j) hkj };
  have hOj : π (Ord j) { refine le_Ord2 k j hkj };
  refine trans_induct i (λ w, le (omult k w) (omult j w)) hOi _;
  assume x hOx ih;
  have hsub : π (omult k x ⊆ omult j x)
    { assume y hy;
      have hex : π (`∃ (jp : τ ι), `∃ (ip : τ ι),
          (y = oadd (omult k ip) jp) ∧ lt jp k ∧ lt ip x)
        { refine lt_omult x k y hOx hOk
            (ltI y (omult k x) hy (Ord_omult k x hOk hOx)) };
      refine ∃ₑ hex _; assume jp hjp;
      refine ∃ₑ hjp _; assume ip hip;
      have hltjp : π (lt jp k) { refine ∧ₑ₁ (∧ₑ₂ hip) };
      have hltip : π (lt ip x) { refine ∧ₑ₂ (∧ₑ₂ hip) };
      have hih : π (le (omult k ip) (omult j ip)) { refine ih ip (ltD ip x hltip) };
      have hlt2 : π (lt (oadd (omult j ip) jp) (omult j x))
        { refine omult_oadd_lt jp j ip x (lt_trans2 jp k j hltjp hkj) hltip };
      have hlt4 : π (lt (oadd (omult k ip) jp) (omult j x))
        { refine lt_trans1 (oadd (omult k ip) jp) (oadd (omult j ip) jp) (omult j x)
            (oadd_le_mono1 (omult k ip) (omult j ip) jp hih) hlt2 };
      refine ind_eq (∧ₑ₁ hip) (λ w, w ∈ omult j x)
        (ltD (oadd (omult k ip) jp) (omult j x) hlt4) };
  refine subset_imp_le (omult j x) (omult k x) hsub
    (Ord_omult j x hOj hOx) (Ord_omult k x hOk hOx)
end;

opaque symbol omult_lt_mono2 (k j i : τ ι) :
  π (lt k j) → π (lt empty i) → π (lt (omult i k) (omult i j)) ≔
begin
  assume k j i hkj h0i;
  have hOi : π (Ord i) { refine lt_Ord2 empty i h0i };
  have hOk : π (Ord k) { refine lt_Ord k j hkj };
  have he : π (oadd (omult i k) empty = omult i k)
    { refine oadd_0 (omult i k) (Ord_omult i k hOi hOk) };
  refine ind_eq (eq_sym he) (λ w, lt w (omult i j))
    (omult_oadd_lt empty i k j h0i hkj)
end;

opaque symbol omult_le_mono2 (k j i : τ ι) :
  π (le k j) → π (Ord i) → π (le (omult i k) (omult i j)) ≔
begin
  assume k j i hkj hOi;
  have hOj : π (Ord j) { refine le_Ord2 k j hkj };
  have hOk : π (Ord k) { refine lt_Ord k (succ j) hkj };
  have hksub : π (k ⊆ j) { refine le_imp_subset k j hkj };
  have hsub : π (omult i k ⊆ omult i j)
    { have hunf : π (omult i k = Union (RepFun i (λ jp,
          Union (RepFun k (λ ip, singleton (oadd (omult i ip) jp))))))
        { refine omult_unfold k i hOk hOi };
      assume x hx;
      have hxU : π (x ∈ Union (RepFun i (λ jp,
          Union (RepFun k (λ ip, singleton (oadd (omult i ip) jp))))))
        { refine ind_eq (eq_sym hunf) (λ w, x ∈ w) hx };
      have hbex : π (Bex (RepFun i (λ jp,
          Union (RepFun k (λ ip, singleton (oadd (omult i ip) jp))))) (λ B, x ∈ B))
        { refine UnionE x (RepFun i (λ jp,
            Union (RepFun k (λ ip, singleton (oadd (omult i ip) jp))))) hxU };
      refine ∃ₑ hbex _; assume B hB;
      have hbex2 : π (Bex i (λ jp,
          B = Union (RepFun k (λ ip, singleton (oadd (omult i ip) jp)))))
        { refine ∧ₑ₁ (RepFun_iff B i (λ jp,
            Union (RepFun k (λ ip, singleton (oadd (omult i ip) jp))))) (∧ₑ₁ hB) };
      refine ∃ₑ hbex2 _; assume jp hjp;
      have hjpi : π (jp ∈ i) { refine ∧ₑ₁ hjp };
      have hxU2 : π (x ∈ Union (RepFun k (λ ip, singleton (oadd (omult i ip) jp))))
        { refine ind_eq (eq_sym (∧ₑ₂ hjp)) (λ w, x ∈ w) (∧ₑ₂ hB) };
      have hbex3 : π (Bex (RepFun k (λ ip, singleton (oadd (omult i ip) jp)))
                       (λ C, x ∈ C))
        { refine UnionE x (RepFun k (λ ip, singleton (oadd (omult i ip) jp))) hxU2 };
      refine ∃ₑ hbex3 _; assume C hC;
      have hbex4 : π (Bex k (λ ip, C = singleton (oadd (omult i ip) jp)))
        { refine ∧ₑ₁ (RepFun_iff C k (λ ip, singleton (oadd (omult i ip) jp))) (∧ₑ₁ hC) };
      refine ∃ₑ hbex4 _; assume ip hip;
      have hipk : π (ip ∈ k) { refine ∧ₑ₁ hip };
      have hxsing : π (x ∈ singleton (oadd (omult i ip) jp))
        { refine ind_eq (eq_sym (∧ₑ₂ hip)) (λ w, x ∈ w) (∧ₑ₂ hC) };
      have hxeq : π (x = oadd (omult i ip) jp)
        { refine ∧ₑ₁ (singleton_iff x (oadd (omult i ip) jp)) hxsing };
      refine ind_eq hxeq (λ w, w ∈ omult i j)
        (ltD (oadd (omult i ip) jp) (omult i j)
          (omult_oadd_lt jp i ip j (ltI jp i hjpi hOi)
            (ltI ip j (hksub ip hipk) hOj))) };
  refine subset_imp_le (omult i j) (omult i k) hsub
    (Ord_omult i j hOi hOj) (Ord_omult i k hOi hOk)
end;

opaque symbol omult_le_mono (ip i jp j : τ ι) :
  π (le ip i) → π (le jp j) → π (le (omult ip jp) (omult i j)) ≔
begin
  assume ip i jp j hlei hlej;
  have hOi : π (Ord i) { refine le_Ord2 ip i hlei };
  have hOjp : π (Ord jp) { refine lt_Ord jp (succ j) hlej };
  refine le_trans (omult ip jp) (omult i jp) (omult i j)
    (omult_le_mono1 ip i jp hlei hOjp)
    (omult_le_mono2 jp j i hlej hOi)
end;

opaque symbol omult_lt_mono (ip i jp j : τ ι) :
  π (le ip i) → π (lt jp j) → π (lt empty i) →
  π (lt (omult ip jp) (omult i j)) ≔
begin
  assume ip i jp j hlei hltj h0i;
  have hOjp : π (Ord jp) { refine lt_Ord jp j hltj };
  refine lt_trans1 (omult ip jp) (omult i jp) (omult i j)
    (omult_le_mono1 ip i jp hlei hOjp)
    (omult_lt_mono2 jp j i hltj h0i)
end;

opaque symbol omult_le_self2 (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (le i (omult j i)) ≔
begin
  assume i j hOi h0j;
  have hOj : π (Ord j) { refine lt_Ord2 empty j h0j };
  have hmono : π (le (omult (succ empty) i) (omult j i))
    { refine omult_le_mono1 (succ empty) j i
        (succ_leI empty j hOj (ltD empty j h0j)) hOi };
  refine ind_eq (eq_sym (omult_1_left i hOi)) (λ w, le w (omult j i)) hmono
end;

opaque symbol omult_inject (i j k : τ ι) :
  π (omult i j = omult i k) → π (lt empty i) → π (Ord j) → π (Ord k) →
  π (j = k) ≔
begin
  assume i j k heq h0i hOj hOk;
  refine ∨ₑ (Ord_linear_lt3 j k hOj hOk) _ _
  { assume hjk;
    have hlt : π (lt (omult i j) (omult i k)) { refine omult_lt_mono2 j k i hjk h0i };
    refine ⊥ₑ (lt_irrefl (omult i k)
      (ind_eq (eq_sym heq) (λ w, lt w (omult i k)) hlt)) }
  { assume h;
    refine ∨ₑ h _ _
    { assume he; refine he }
    { assume hkj;
      have hlt : π (lt (omult i k) (omult i j)) { refine omult_lt_mono2 k j i hkj h0i };
      refine ⊥ₑ (lt_irrefl (omult i k)
        (ind_eq (eq_sym heq) (λ w, lt (omult i k) w) hlt)) } }
end;

// ===========================================================================
// The Relation Lt
// ===========================================================================

// port-internal helper: introduction/elimination for the local relation Lt.
private opaque symbol LtI (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) → π (lt x y) → π (Pair x y ∈ Lt) ≔
begin
  assume x y hx hy hlt;
  refine CollectI (Pair x y) (Sigma omega (λ _, omega)) (λ z, lt (fst z) (snd z))
    (SigmaI x y omega (λ _, omega) hx hy)
    (ind_eq (fst_conv x y) (λ w, lt w (snd (Pair x y)))
      (ind_eq (snd_conv x y) (λ w, lt x w) hlt))
end;

// port-internal helper: the order component of Lt membership.
private opaque symbol LtD_lt (x y : τ ι) :
  π (Pair x y ∈ Lt) → π (lt x y) ≔
begin
  assume x y h;
  refine ind_eq (eq_sym (snd_conv x y)) (λ w, lt x w)
    (ind_eq (eq_sym (fst_conv x y)) (λ w, lt w (snd (Pair x y)))
      (CollectD2 (Pair x y) (Sigma omega (λ _, omega)) (λ z, lt (fst z) (snd z)) h))
end;

// port-internal helper: first domain component of Lt membership.
private opaque symbol LtD1 (x y : τ ι) :
  π (Pair x y ∈ Lt) → π (x ∈ omega) ≔
begin
  assume x y h;
  refine ind_eq (eq_sym (fst_conv x y)) (λ w, w ∈ omega)
    (SigmaD1 (Pair x y) omega (λ _, omega)
      (CollectD1 (Pair x y) (Sigma omega (λ _, omega)) (λ z, lt (fst z) (snd z)) h))
end;

// port-internal helper: second domain component of Lt membership.
private opaque symbol LtD2 (x y : τ ι) :
  π (Pair x y ∈ Lt) → π (y ∈ omega) ≔
begin
  assume x y h;
  refine ind_eq (eq_sym (snd_conv x y)) (λ w, w ∈ omega)
    (SigmaD2 (Pair x y) omega (λ _, omega)
      (CollectD1 (Pair x y) (Sigma omega (λ _, omega)) (λ z, lt (fst z) (snd z)) h))
end;

opaque symbol wf_Lt : π (wf_global Lt) ≔
begin
  refine wf_global_subset (Memrel omega) Lt (wf_Memrel omega) _;
  assume p hp;
  have hSig : π (p ∈ Sigma omega (λ _, omega))
    { refine CollectD1 p (Sigma omega (λ _, omega)) (λ z, lt (fst z) (snd z)) hp };
  have hltp : π (lt (fst p) (snd p))
    { refine CollectD2 p (Sigma omega (λ _, omega)) (λ z, lt (fst z) (snd z)) hp };
  have hbex : π (Bex omega (λ x, Bex ((λ _, omega) x) (λ y, p = Pair x y)))
    { refine SigmaE p omega (λ _, omega) hSig };
  refine ∃ₑ hbex _;
  assume a ha;
  have haom : π (a ∈ omega) { refine ∧ₑ₁ ha };
  refine ∃ₑ (∧ₑ₂ ha) _;
  assume b hb;
  have hbom : π (b ∈ omega) { refine ∧ₑ₁ hb };
  have hpeq : π (p = Pair a b) { refine ∧ₑ₂ hb };
  have hltab : π (lt a b)
    { refine ind_eq (eq_sym (snd_conv a b)) (λ w, lt a w)
        (ind_eq (eq_sym (fst_conv a b)) (λ w, lt w (snd (Pair a b)))
          (ind_eq (eq_sym hpeq) (λ w, lt (fst w) (snd w)) hltp)) };
  refine ind_eq hpeq (λ w, w ∈ Memrel omega)
    (MemrelI a b omega (ltD a b hltab) haom hbom)
end;

opaque symbol irrefl_Lt (A : τ ι) : π (irrefl_on A Lt) ≔
begin
  assume A;
  refine irrefl_onI A Lt _;
  assume x hx hmem;
  refine lt_irrefl x (LtD_lt x x hmem)
end;

opaque symbol trans_Lt (A : τ ι) : π (trans_on A Lt) ≔
begin
  assume A;
  refine trans_onI A Lt _;
  assume x hx y hy z hz hxy hyz;
  refine LtI x z (LtD1 x y hxy) (LtD2 y z hyz)
    (lt_trans x y z (LtD_lt x y hxy) (LtD_lt y z hyz))
end;

opaque symbol part_ord_Lt (A : τ ι) : π (part_ord A Lt) ≔
begin
  assume A;
  rewrite part_ord_def;
  refine ∧ᵢ (irrefl_Lt A) (trans_Lt A)
end;

opaque symbol linear_Lt : π (linear omega Lt) ≔
begin
  refine linearI omega Lt _;
  assume x hx y hy;
  have hOx : π (Ord x) { refine nat_into_Ord x hx };
  have hOy : π (Ord y) { refine nat_into_Ord y hy };
  refine ∨ₑ (Ord_linear x y hOx hOy) _ _
  { assume h; refine ∨ᵢ₁ (LtI x y hx hy (ltI x y h hOy)) }
  { assume h;
    refine ∨ₑ h _ _
    { assume he; refine ∨ᵢ₂ (∨ᵢ₁ he) }
    { assume h2; refine ∨ᵢ₂ (∨ᵢ₂ (LtI y x hy hx (ltI y x h2 hOx))) } }
end;

opaque symbol tot_ord_Lt : π (tot_ord omega Lt) ≔
begin
  rewrite tot_ord_def;
  refine ∧ᵢ (part_ord_Lt omega) linear_Lt
end;

opaque symbol well_ord_Lt : π (well_ord omega Lt) ≔
begin
  rewrite well_ord_def;
  refine ∧ᵢ tot_ord_Lt (wf_imp_wf_on omega Lt wf_Lt)
end;
