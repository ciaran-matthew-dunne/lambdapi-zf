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

symbol ordermap (A r : τ ι) : τ ι ≔
  Lambda A (λ x, wfrec (Int r (Sigma A (λ _, A))) x (λ x2 f, Image f (pred A x2 r)));

symbol ordertype (A r : τ ι) : τ ι ≔ Image (ordermap A r) A;

symbol Ord_alt (X : τ ι) : Prop ≔
  well_ord X (Memrel X) ∧ Ball X (λ u, u = pred X u (Memrel X));

symbol ordify (x : τ ι) : τ ι ≔ If (Ord x) x empty;

symbol omult (i j : τ ι) : τ ι ≔
  ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i));

symbol raw_oadd (i j : τ ι) : τ ι ≔
  ordertype (sum i j) (radd i (Memrel i) j (Memrel j));

symbol oadd (i j : τ ι) : τ ι ≔ raw_oadd (ordify i) (ordify j);

symbol odiff (i j : τ ι) : τ ι ≔ ordertype (Diff i j) (Memrel i);

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
  { assume x hx y hy;
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
  have hOi : π (Ord i) { refine ∧ₑ₂ hlt };
  have hji : π (j ∈ i) { refine ltD j i hlt };
  have hsub : π (j ⊆ i) { refine OrdmemD i j hji hOi };
  refine equality_iffI (pred i j (Memrel i)) j _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hmem : π (Pair x j ∈ Memrel i)
      { refine CollectD2 x i (λ y, Pair y j ∈ Memrel i) hx };
    refine ∧ₑ₂ (∧ₑ₂ (MemrelE x j i hmem)) }
  { assume hx;
    refine CollectI x i (λ y, Pair y j ∈ Memrel i) (hsub x hx)
      (MemrelI x j i hx (hsub x hx) hji) }
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
      { refine CollectD2 y A (λ w, Pair w x ∈ Memrel A) hy };
    have h3 : π (y ∈ A ∧ x ∈ A ∧ y ∈ x) { refine MemrelE y x A hmem };
    refine IntI y A x (∧ₑ₁ h3) (∧ₑ₂ (∧ₑ₂ h3)) }
  { assume hy;
    have hyA : π (y ∈ A) { refine IntD1 y A x hy };
    have hyx : π (y ∈ x) { refine IntD2 y A x hy };
    refine CollectI y A (λ w, Pair w x ∈ Memrel A) hyA
      (MemrelI y x A hyx hyA hxA) }
end;

opaque symbol Ord_iso_implies_eq_lemma (j i f : τ ι) (R : Prop) :
  π (lt j i) → π (f ∈ ord_iso i (Memrel i) j (Memrel j)) → π R ≔
begin
  assume j i f R hlt hf;
  have hOi : π (Ord i) { refine ∧ₑ₂ hlt };
  have hji : π (j ∈ i) { refine ltD j i hlt };
  have hjsub : π (j ⊆ i) { refine OrdmemD i j hji hOi };
  have hpred : π (pred i j (Memrel i) = j) { refine lt_pred_Memrel j i hlt };
  have hbij : π (f ∈ bij i j)
    { refine ord_iso_is_bij f i (Memrel i) j (Memrel j) hf };
  have hfun : π (f ∈ Pi i (λ _, j)) { refine bij_is_fun f i j hbij };
  have hcond : π (Ball i (λ x, Ball i (λ y,
      (Pair x y ∈ Memrel i) ⇔ (Pair (fapply f x) (fapply f y) ∈ Memrel j))))
    { refine CollectD2 f (bij i j) (λ g, Ball i (λ x, Ball i (λ y,
        (Pair x y ∈ Memrel i) ⇔ (Pair (fapply g x) (fapply g y) ∈ Memrel j)))) hf };
  // Convert the target relation Memrel(j) to Memrel(i): on elements of j ⊆ i
  // the two membership relations agree.
  have hf2 : π (f ∈ ord_iso i (Memrel i) j (Memrel i))
    { refine CollectI f (bij i j) (λ g, Ball i (λ x, Ball i (λ y,
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
    refine CollectI y A (λ w, Pair w x ∈ r) hyA
      (IntD1 (Pair y x) r (Sigma A (λ _, A)) hR) }
  { assume hy;
    have hyA : π (y ∈ A) { refine CollectD1 y A (λ w, Pair w x ∈ r) hy };
    have hyr : π (Pair y x ∈ r) { refine CollectD2 y A (λ w, Pair w x ∈ r) hy };
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
    { refine beta A (ombody A r) x hx };
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
  refine equality_iffI
    (Image (Lambda (pred A x r) (ombody A r)) (pred A x r))
    (Image (ordermap A r) (pred A x r)) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    have hbex : π (Bex (Int (pred A x r)
                         (domain (Lambda (pred A x r) (ombody A r))))
                    (λ w, z = fapply (Lambda (pred A x r) (ombody A r)) w))
      { refine ∧ₑ₁ (RepFun_iff z
          (Int (pred A x r) (domain (Lambda (pred A x r) (ombody A r))))
          (λ w, fapply (Lambda (pred A x r) (ombody A r)) w)) hz };
    refine ∃ₑ hbex _; assume w hw;
    have hwp : π (w ∈ pred A x r)
      { refine IntD1 w (pred A x r)
          (domain (Lambda (pred A x r) (ombody A r))) (∧ₑ₁ hw) };
    have hwA : π (w ∈ A) { refine pred_subset A x r w hwp };
    have hzeq : π (z = fapply (Lambda A (ombody A r)) w)
      { refine eq_trans (∧ₑ₂ hw)
          (eq_trans (beta (pred A x r) (ombody A r) w hwp)
                    (eq_sym (beta A (ombody A r) w hwA))) };
    refine ∧ₑ₂ (RepFun_iff z
        (Int (pred A x r) (domain (Lambda A (ombody A r))))
        (λ w, fapply (Lambda A (ombody A r)) w)) _;
    refine ∃ᵢ w (∧ᵢ (IntI w (pred A x r) (domain (Lambda A (ombody A r))) hwp
      (Lambda_domain_subset A (ombody A r) w hwA)) hzeq) }
  { assume hz;
    have hbex : π (Bex (Int (pred A x r) (domain (Lambda A (ombody A r))))
                    (λ w, z = fapply (Lambda A (ombody A r)) w))
      { refine ∧ₑ₁ (RepFun_iff z
          (Int (pred A x r) (domain (Lambda A (ombody A r))))
          (λ w, fapply (Lambda A (ombody A r)) w)) hz };
    refine ∃ₑ hbex _; assume w hw;
    have hwp : π (w ∈ pred A x r)
      { refine IntD1 w (pred A x r) (domain (Lambda A (ombody A r))) (∧ₑ₁ hw) };
    have hwA : π (w ∈ A) { refine pred_subset A x r w hwp };
    have hzeq : π (z = fapply (Lambda (pred A x r) (ombody A r)) w)
      { refine eq_trans (∧ₑ₂ hw)
          (eq_trans (beta A (ombody A r) w hwA)
                    (eq_sym (beta (pred A x r) (ombody A r) w hwp))) };
    refine ∧ₑ₂ (RepFun_iff z
        (Int (pred A x r) (domain (Lambda (pred A x r) (ombody A r))))
        (λ w, fapply (Lambda (pred A x r) (ombody A r)) w)) _;
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
  refine ind_eq (Int_pred_domain A r x)
    (λ S, RepFun S (λ w, fapply (ordermap A r) w)
          = RepFun (pred A x r) (λ y, fapply (ordermap A r) y))
    (eq_refl (RepFun (pred A x r) (λ y, fapply (ordermap A r) y)))
end;

// ordermap_unfold = ordermap_pred_unfold [simplified pred_def] (pred unfolded to Collect)
opaque symbol ordermap_unfold (A r x : τ ι) :
  π (wf A r) → π (x ∈ A) →
  π (fapply (ordermap A r) x
     = RepFun (Collect A (λ y, Pair y x ∈ r)) (λ y, fapply (ordermap A r) y)) ≔
begin
  assume A r x hwf hx;
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
  refine lam_type A (ombody A r) (λ _, ordertype A r) _;
  assume x hx;
  have hmem : π (fapply (ordermap A r) x ∈ ordertype A r)
    { refine RepFunI x (Int A (domain (Lambda A (ombody A r))))
        (λ w, fapply (ordermap A r) w)
        (IntI x A (domain (Lambda A (ombody A r))) hx
          (Lambda_domain_subset A (ombody A r) x hx)) };
  refine ind_eq (eq_sym (beta A (ombody A r) x hx)) (λ w, w ∈ ordertype A r)
    hmem
end;

opaque symbol Ord_ordermap (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) → π (Ord (fapply (ordermap A r) x)) ≔
begin
  assume A r x hwo hx;
  have hwf : π (wf A r) { refine ∧ₑ₂ hwo };
  have htrans : π (trans_on A r) { refine ∧ₑ₂ (∧ₑ₁ (∧ₑ₁ hwo)) };
  refine wf_induct A r (λ w, Ord (fapply (ordermap A r) w)) hwf _ x hx;
  assume x2 hx2 ih;
  have hunf : π (fapply (ordermap A r) x2
      = RepFun (pred A x2 r) (λ y, fapply (ordermap A r) y))
    { refine ordermap_pred_unfold A r x2 hwf hx2 };
  refine OrdI (fapply (ordermap A r) x2) _ _
  { // Transset: u ∈ m(x2) → u ⊆ m(x2), via transitivity of r
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
      { refine CollectD2 y A (λ w, Pair w x2 ∈ r) hyp };
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
    have hwy : π (Pair w y ∈ r) { refine CollectD2 w A (λ z, Pair z y ∈ r) hwp };
    have hwx : π (Pair w x2 ∈ r) { refine htrans w hwA y hyA x2 hx2 hwy hyr };
    have hmw : π (fapply (ordermap A r) w
        ∈ RepFun (pred A x2 r) (λ z, fapply (ordermap A r) z))
      { refine RepFunI w (pred A x2 r) (λ z, fapply (ordermap A r) z)
          (CollectI w A (λ z, Pair z x2 ∈ r) hwA hwx) };
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
          (CollectD2 y A (λ w, Pair w x2 ∈ r) hyp) };
    have hOu : π (Ord u) { refine ind_eq (∧ₑ₂ hy) (λ w, Ord w) hOy };
    refine ∧ₑ₁ hOu }
end;

opaque symbol Ord_ordertype (A r : τ ι) :
  π (well_ord A r) → π (Ord (ordertype A r)) ≔
begin
  assume A r hwo;
  have hwf : π (wf A r) { refine ∧ₑ₂ hwo };
  have hIA : π (Int A (domain (Lambda A (ombody A r))) = A)
    { refine Int_A_domain A r };
  // ordertype A r = RepFun A m  (up to the Int-domain collapse)
  have hunf : π (ordertype A r = RepFun A (λ y, fapply (ordermap A r) y))
    { refine ind_eq hIA
        (λ S, RepFun S (λ w, fapply (ordermap A r) w)
              = RepFun A (λ y, fapply (ordermap A r) y))
        (eq_refl (RepFun A (λ y, fapply (ordermap A r) y))) };
  refine OrdI (ordertype A r) _ _
  { // Transset: u = m(y) ∈ ordertype, v ∈ u = RepFun(pred y)m → v = m(w), w ∈ A
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
    refine ∧ₑ₁ hOu }
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
        (CollectI w A (λ z, Pair z x ∈ r) hwA hwx) };
  refine ind_eq hunf (λ z, fapply (ordermap A r) w ∈ z) hmem
end;

opaque symbol converse_ordermap_mono (w x A r : τ ι) :
  π (fapply (ordermap A r) w ∈ fapply (ordermap A r) x) →
  π (well_ord A r) → π (w ∈ A) → π (x ∈ A) → π (Pair w x ∈ r) ≔
begin
  assume w x A r hmm hwo hwA hxA;
  have hwf : π (wf A r) { refine ∧ₑ₂ hwo };
  have hlin : π (linear A r) { refine ∧ₑ₂ (∧ₑ₁ hwo) };
  refine ∨ₑ (hlin w hwA x hxA) _ _
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
  refine CollectI (ordermap A r) (Pi A (λ _, ordertype A r))
    (λ f, Ball (ordertype A r) (λ y, Bex A (λ x, fapply f x = y)))
    (ordermap_type A r) _;
  assume y hy;
  // y ∈ ordertype = RepFun (Int A dom) fapply
  have hbex : π (Bex (Int A (domain (Lambda A (ombody A r))))
                  (λ x, y = fapply (ordermap A r) x))
    { refine ∧ₑ₁ (RepFun_iff y (Int A (domain (Lambda A (ombody A r))))
        (λ x, fapply (ordermap A r) x)) hy };
  refine ∃ₑ hbex _; assume x hx;
  refine ∃ᵢ x (∧ᵢ (IntD1 x A (domain (Lambda A (ombody A r))) (∧ₑ₁ hx))
    (eq_sym (∧ₑ₂ hx)))
end;

opaque symbol ordermap_bij (A r : τ ι) :
  π (well_ord A r) → π (ordermap A r ∈ bij A (ordertype A r)) ≔
begin
  assume A r hwo;
  have hlin : π (linear A r) { refine ∧ₑ₂ (∧ₑ₁ hwo) };
  have hwf : π (wf A r) { refine ∧ₑ₂ hwo };
  refine IntI (ordermap A r) (inj A (ordertype A r)) (surj A (ordertype A r))
    _ (ordermap_surj A r);
  refine CollectI (ordermap A r) (Pi A (λ _, ordertype A r))
    (λ f, Ball A (λ w, Ball A (λ x, fapply f w = fapply f x ⇒ w = x)))
    (ordermap_type A r) _;
  assume w hw x hx heq;
  refine ∨ₑ (hlin w hw x hx) _ _
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
  have hwf : π (wf A r) { refine ∧ₑ₂ hwo };
  have htype : π (ordermap A r ∈ Pi A (λ _, ordertype A r))
    { refine ordermap_type A r };
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
    { refine CollectD2 f (bij A B) (λ g, Ball A (λ x, Ball A (λ y,
        (Pair x y ∈ r) ⇔ (Pair (fapply g x) (fapply g y) ∈ s)))) hf };
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
  have hbex : π (Bex (Int empty (domain (Lambda empty (ombody empty r))))
                  (λ x, z = fapply (ordermap empty r) x))
    { refine ∧ₑ₁ (RepFun_iff z
        (Int empty (domain (Lambda empty (ombody empty r))))
        (λ x, fapply (ordermap empty r) x)) hz };
  refine ∃ₑ hbex _; assume w hw;
  refine emptyE w (IntD1 w empty (domain (Lambda empty (ombody empty r)))
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
  have hwf : π (wf A r) { refine ∧ₑ₂ hwo };
  have htrans : π (trans_on A r) { refine ∧ₑ₂ (∧ₑ₁ (∧ₑ₁ hwo)) };
  have hPsub : π (pred A y r ⊆ A) { refine pred_subset A y r };
  have hwfP : π (wf (pred A y r) r) { refine wf_subset A (pred A y r) r hwf hPsub };
  refine wf_induct A r
    (λ w, w ∈ pred A y r
          ⇒ fapply (ordermap (pred A y r) r) w = fapply (ordermap A r) w)
    hwf _ z (hPsub z hzP) hzP;
  assume z2 hz2A ih hz2P;
  have hz2y : π (Pair z2 y ∈ r) { refine CollectD2 z2 A (λ w, Pair w y ∈ r) hz2P };
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
          { refine CollectD1 w (pred A y r) (λ v, Pair v z2 ∈ r) hw };
        refine CollectI w A (λ v, Pair v z2 ∈ r) (hPsub w hwP)
          (CollectD2 w (pred A y r) (λ v, Pair v z2 ∈ r) hw) }
      { assume hw;
        have hwA : π (w ∈ A) { refine CollectD1 w A (λ v, Pair v z2 ∈ r) hw };
        have hwz2 : π (Pair w z2 ∈ r)
          { refine CollectD2 w A (λ v, Pair v z2 ∈ r) hw };
        have hwy : π (Pair w y ∈ r)
          { refine htrans w hwA z2 hz2A y hyA hwz2 hz2y };
        refine CollectI w (pred A y r) (λ v, Pair v z2 ∈ r)
          (CollectI w A (λ v, Pair v y ∈ r) hwA hwy) hwz2 } };
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
        { refine CollectD2 w A (λ v, Pair v z2 ∈ r) hw };
      have hwy : π (Pair w y ∈ r)
        { refine htrans w hwA z2 hz2A y hyA hwz2 hz2y };
      refine ih w hwA hwz2 (CollectI w A (λ v, Pair v y ∈ r) hwA hwy) };
  have hu3 : π (fapply (ordermap A r) z2
      = RepFun (pred A z2 r) (λ w, fapply (ordermap A r) w))
    { refine ordermap_pred_unfold A r z2 hwf hz2A };
  refine eq_trans hu2 (eq_trans hcong (eq_sym hu3))
end;

opaque symbol ordertype_unfold (A r : τ ι) :
  π (ordertype A r = RepFun A (λ y, fapply (ordermap A r) y)) ≔
begin
  assume A r;
  refine ind_eq (Int_A_domain A r)
    (λ S, RepFun S (λ w, fapply (ordermap A r) w)
          = RepFun A (λ y, fapply (ordermap A r) y))
    (eq_refl (RepFun A (λ y, fapply (ordermap A r) y)))
end;

// ordertype of an initial segment is the ordermap value at its bound.
private opaque symbol ordertype_pred_eq (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) →
  π (ordertype (pred A x r) r = fapply (ordermap A r) x) ≔
begin
  assume A r x hwo hx;
  have hwf : π (wf A r) { refine ∧ₑ₂ hwo };
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
  have hwo : π (well_ord i (Memrel i)) { refine ∧ₑ₁ halt };
  have hpr : π (Ball i (λ u, u = pred i u (Memrel i))) { refine ∧ₑ₂ halt };
  have htrans : π (trans_on i (Memrel i)) { refine ∧ₑ₂ (∧ₑ₁ (∧ₑ₁ hwo)) };
  // Transset(i): u ∈ i → u = pred(i,u,Memrel i) ⊆ i
  have hT : π (Transset i)
    { assume u hu;
      have heq : π (u = pred i u (Memrel i)) { refine hpr u hu };
      assume w hw;
      have hwpred : π (w ∈ pred i u (Memrel i))
        { refine ind_eq (eq_sym heq) (λ z, w ∈ z) hw };
      refine CollectD1 w i (λ v, Pair v u ∈ Memrel i) hwpred };
  refine OrdI i hT _;
  // every u ∈ i is a Transset, via transitivity of Memrel(i) on i
  assume u hu;
  assume v hv w hw;
  have hvi : π (v ∈ i) { refine hT u hu v hv };
  have hui : π (u ∈ i) { refine hu };
  have hwi : π (w ∈ i) { refine hT v hvi w hw };
  have hwv : π (Pair w v ∈ Memrel i) { refine MemrelI w v i hw hwi hvi };
  have hvu : π (Pair v u ∈ Memrel i) { refine MemrelI v u i hv hvi hui };
  have hwu : π (Pair w u ∈ Memrel i)
    { refine htrans w hwi v hvi u hui hwv hvu };
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
    have hxA : π (x ∈ A) { refine CollectD1 x A (λ v, Pair v a ∈ r) hx };
    have hxa : π (Pair x a ∈ r) { refine CollectD2 x A (λ v, Pair v a ∈ r) hx };
    refine CollectI (Inl x) (sum A B) (λ z, Pair z (Inl a) ∈ radd A r B s)
      (InlI x A B hxA)
      (∧ₑ₂ (radd_Inl_iff x a A r B s) (∧ᵢ hxA (∧ᵢ haA hxa))) }
  { assume z hz;
    have hzs : π (z ∈ sum A B)
      { refine CollectD1 z (sum A B) (λ w, Pair w (Inl a) ∈ radd A r B s) hz };
    have hrel : π (Pair z (Inl a) ∈ radd A r B s)
      { refine CollectD2 z (sum A B) (λ w, Pair w (Inl a) ∈ radd A r B s) hz };
    refine sumE z A B _ hzs _ _
    { assume x hx hze;
      have hrel2 : π (Pair (Inl x) (Inl a) ∈ radd A r B s)
        { refine ind_eq (eq_sym hze) (λ w, Pair w (Inl a) ∈ radd A r B s) hrel };
      have h3 : π (x ∈ A ∧ a ∈ A ∧ Pair x a ∈ r)
        { refine ∧ₑ₁ (radd_Inl_iff x a A r B s) hrel2 };
      have hxp : π (x ∈ pred A a r)
        { refine CollectI x A (λ v, Pair v a ∈ r) (∧ₑ₁ h3) (∧ₑ₂ (∧ₑ₂ h3)) };
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
      { refine CollectD1 z (sum A B) (λ w, Pair w (Inl a) ∈ radd A r B s) hz };
    have hrel : π (Pair z (Inl a) ∈ radd A r B s)
      { refine CollectD2 z (sum A B) (λ w, Pair w (Inl a) ∈ radd A r B s) hz };
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

opaque symbol Ord_ordify (x : τ ι) :
  π (Ord (ordify x)) ≔
begin
  admit
end;

opaque symbol ordify_idem (x : τ ι) :
  π (ordify (ordify x) = ordify x) ≔
begin
  admit
end;

opaque symbol Ord_raw_oadd (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (raw_oadd i j)) ≔
begin
  admit
end;

opaque symbol Ord_oadd (i j : τ ι) :
  π (Ord (oadd i j)) ≔
begin
  admit
end;

opaque symbol raw_oadd_0 (i : τ ι) :
  π (Ord i) → π (raw_oadd i empty = i) ≔
begin
  admit
end;

opaque symbol oadd_0 (i : τ ι) :
  π (Ord i) → π (oadd i empty = i) ≔
begin
  admit
end;

opaque symbol raw_oadd_0_left (i : τ ι) :
  π (Ord i) → π (raw_oadd empty i = i) ≔
begin
  admit
end;

opaque symbol oadd_0_left (i : τ ι) :
  π (Ord i) → π (oadd empty i = i) ≔
begin
  admit
end;

opaque symbol oadd_eq_if_raw_oadd (i j : τ ι) :
  π (oadd i j = If (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty)) ≔
begin
  admit
end;

opaque symbol raw_oadd_eq_oadd (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (raw_oadd i j = oadd i j) ≔
begin
  admit
end;

opaque symbol lt_oadd1 (k i j : τ ι) :
  π (lt k i) → π (lt k (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_le_self (i j : τ ι) :
  π (Ord i) → π (le i (oadd i j)) ≔
begin
  admit
end;

opaque symbol id_ord_iso_Memrel (A B : τ ι) :
  π (A ⊆ B) → π (id_fun A ∈ ord_iso A (Memrel A) A (Memrel B)) ≔
begin
  admit
end;

opaque symbol subset_ord_iso_Memrel (f A B C r : τ ι) :
  π (f ∈ ord_iso A (Memrel B) C r) → π (A ⊆ B) →
  π (f ∈ ord_iso A (Memrel A) C r) ≔
begin
  admit
end;

opaque symbol restrict_ord_iso (f i A a r j : τ ι) :
  π (f ∈ ord_iso i (Memrel i) (pred A a r) r) → π (a ∈ A) → π (lt j i) →
  π (trans_on A r) →
  π (restrict f j ∈ ord_iso j (Memrel j) (pred A (fapply f j) r) r) ≔
begin
  admit
end;

opaque symbol restrict_ord_iso2 (f A a r i j : τ ι) :
  π (f ∈ ord_iso (pred A a r) r i (Memrel i)) → π (a ∈ A) → π (lt j i) →
  π (trans_on A r) →
  π (converse (restrict (converse f) j)
     ∈ ord_iso (pred A (fapply (converse f) j) r) r j (Memrel j)) ≔
begin
  admit
end;

opaque symbol ordertype_sum_Memrel (A r k j : τ ι) :
  π (well_ord A r) → π (lt k j) →
  π (ordertype (sum A k) (radd A r k (Memrel j))
     = ordertype (sum A k) (radd A r k (Memrel k))) ≔
begin
  admit
end;

opaque symbol oadd_lt_mono2 (k j i : τ ι) :
  π (lt k j) → π (lt (oadd i k) (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_lt_cancel2 (i j k : τ ι) :
  π (lt (oadd i j) (oadd i k)) → π (Ord j) → π (lt j k) ≔
begin
  admit
end;

opaque symbol oadd_lt_iff2 (i j k : τ ι) :
  π (Ord j) → π (lt (oadd i j) (oadd i k) ⇔ lt j k) ≔
begin
  admit
end;

opaque symbol oadd_inject (i j k : τ ι) :
  π (oadd i j = oadd i k) → π (Ord j) → π (Ord k) → π (j = k) ≔
begin
  admit
end;

opaque symbol lt_oadd_disj (k i j : τ ι) :
  π (lt k (oadd i j)) → π (lt k i ∨ Bex j (λ l, k = oadd i l)) ≔
begin
  admit
end;

opaque symbol oadd_assoc (i j k : τ ι) :
  π (oadd (oadd i j) k = oadd i (oadd j k)) ≔
begin
  admit
end;

opaque symbol oadd_unfold (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (oadd i j = Un i (Union (RepFun j (λ k, singleton (oadd i k))))) ≔
begin
  admit
end;

opaque symbol oadd_1 (i : τ ι) :
  π (Ord i) → π (oadd i (succ empty) = succ i) ≔
begin
  admit
end;

opaque symbol oadd_succ (i j : τ ι) :
  π (Ord j) → π (oadd i (succ j) = succ (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_UN (A i a : τ ι) (jf : τ ι → τ ι) :
  π (Ball A (λ x, Ord (jf x))) → π (a ∈ A) →
  π (oadd i (Union (RepFun A (λ x, jf x)))
     = Union (RepFun A (λ x, oadd i (jf x)))) ≔
begin
  admit
end;

opaque symbol oadd_Limit (i j : τ ι) :
  π (Limit j) → π (oadd i j = Union (RepFun j (λ k, oadd i k))) ≔
begin
  admit
end;

opaque symbol oadd_eq_0_iff (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π ((oadd i j = empty) ⇔ (i = empty ∧ j = empty)) ≔
begin
  admit
end;

opaque symbol oadd_eq_lt_iff (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (lt empty (oadd i j) ⇔ (lt empty i ∨ lt empty j)) ≔
begin
  admit
end;

opaque symbol oadd_LimitI (i j : τ ι) :
  π (Ord i) → π (Limit j) → π (Limit (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_le_self2 (i j : τ ι) :
  π (Ord i) → π (le i (oadd j i)) ≔
begin
  admit
end;

opaque symbol oadd_le_mono1 (k j i : τ ι) :
  π (le k j) → π (le (oadd k i) (oadd j i)) ≔
begin
  admit
end;

opaque symbol oadd_lt_mono (ip i jp j : τ ι) :
  π (le ip i) → π (lt jp j) → π (lt (oadd ip jp) (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_le_mono (ip i jp j : τ ι) :
  π (le ip i) → π (le jp j) → π (le (oadd ip jp) (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_le_iff2 (i j k : τ ι) :
  π (Ord j) → π (Ord k) → π (le (oadd i j) (oadd i k) ⇔ le j k) ≔
begin
  admit
end;

opaque symbol oadd_lt_self (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (lt i (oadd i j)) ≔
begin
  admit
end;

opaque symbol Ord_imp_greater_Limit (i : τ ι) :
  π (Ord i) → π (`∃ (k : τ ι), lt i k ∧ Limit k) ≔
begin
  admit
end;

opaque symbol Ord2_imp_greater_Limit (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (`∃ (k : τ ι), lt i k ∧ lt j k ∧ Limit k) ≔
begin
  admit
end;

// ===========================================================================
// Ordinal Subtraction
// ===========================================================================

opaque symbol bij_sum_Diff (A B : τ ι) :
  π (A ⊆ B) →
  π (Lambda B (λ y, If (y ∈ A) (Inl y) (Inr y)) ∈ bij B (sum A (Diff B A))) ≔
begin
  admit
end;

opaque symbol ordertype_sum_Diff (i j : τ ι) :
  π (le i j) →
  π (ordertype (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j))
     = ordertype j (Memrel j)) ≔
begin
  admit
end;

opaque symbol Ord_odiff (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (odiff i j)) ≔
begin
  admit
end;

opaque symbol raw_oadd_ordertype_Diff (i j : τ ι) :
  π (le i j) →
  π (raw_oadd i (odiff j i)
     = ordertype (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j))) ≔
begin
  admit
end;

opaque symbol oadd_odiff_inverse (i j : τ ι) :
  π (le i j) → π (oadd i (odiff j i) = j) ≔
begin
  admit
end;

opaque symbol odiff_oadd_inverse (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (odiff (oadd i j) i = j) ≔
begin
  admit
end;

opaque symbol odiff_lt_mono2 (i j k : τ ι) :
  π (lt i j) → π (le k i) → π (lt (odiff i k) (odiff j k)) ≔
begin
  admit
end;

// ===========================================================================
// Ordinal Multiplication
// ===========================================================================

opaque symbol Ord_omult (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (omult i j)) ≔
begin
  admit
end;

opaque symbol pred_Pair_eq (a A b B r s : τ ι) :
  π (a ∈ A) → π (b ∈ B) →
  π (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)
     = Un (Sigma (pred A a r) (λ _, B)) (Sigma (singleton a) (λ _, pred B b s))) ≔
begin
  admit
end;

opaque symbol ordertype_pred_Pair_eq (a A b B r s : τ ι) :
  π (a ∈ A) → π (b ∈ B) → π (well_ord A r) → π (well_ord B s) →
  π (ordertype (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)) (rmult A r B s)
     = ordertype (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
                 (radd (Sigma A (λ _, B)) (rmult A r B s) B s)) ≔
begin
  admit
end;

opaque symbol ordertype_pred_Pair_lemma (ip i jp j : τ ι) :
  π (lt ip i) → π (lt jp j) →
  π (ordertype
       (pred (Sigma i (λ _, j)) (Pair ip jp) (rmult i (Memrel i) j (Memrel j)))
       (rmult i (Memrel i) j (Memrel j))
     = raw_oadd (omult j ip) jp) ≔
begin
  admit
end;

opaque symbol lt_omult (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (lt k (omult j i)) →
  π (`∃ (jp : τ ι), `∃ (ip : τ ι),
       (k = oadd (omult j ip) jp) ∧ lt jp j ∧ lt ip i) ≔
begin
  admit
end;

opaque symbol omult_oadd_lt (jp j ip i : τ ι) :
  π (lt jp j) → π (lt ip i) →
  π (lt (oadd (omult j ip) jp) (omult j i)) ≔
begin
  admit
end;

opaque symbol omult_unfold (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (omult j i
     = Union (RepFun j (λ jp,
         Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp)))))) ≔
begin
  admit
end;

opaque symbol omult_0 (i : τ ι) :
  π (omult i empty = empty) ≔
begin
  admit
end;

opaque symbol omult_0_left (i : τ ι) :
  π (omult empty i = empty) ≔
begin
  admit
end;

opaque symbol omult_1 (i : τ ι) :
  π (Ord i) → π (omult i (succ empty) = i) ≔
begin
  admit
end;

opaque symbol omult_1_left (i : τ ι) :
  π (Ord i) → π (omult (succ empty) i = i) ≔
begin
  admit
end;

opaque symbol oadd_omult_distrib (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord k) →
  π (omult i (oadd j k) = oadd (omult i j) (omult i k)) ≔
begin
  admit
end;

opaque symbol omult_succ (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (omult i (succ j) = oadd (omult i j) i) ≔
begin
  admit
end;

opaque symbol omult_assoc (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord k) →
  π (omult (omult i j) k = omult i (omult j k)) ≔
begin
  admit
end;

opaque symbol omult_UN (i A : τ ι) (jf : τ ι → τ ι) :
  π (Ord i) → π (Ball A (λ x, Ord (jf x))) →
  π (omult i (Union (RepFun A (λ x, jf x)))
     = Union (RepFun A (λ x, omult i (jf x)))) ≔
begin
  admit
end;

opaque symbol omult_Limit (i j : τ ι) :
  π (Ord i) → π (Limit j) →
  π (omult i j = Union (RepFun j (λ k, omult i k))) ≔
begin
  admit
end;

opaque symbol lt_omult1 (k i j : τ ι) :
  π (lt k i) → π (lt empty j) → π (lt k (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_self (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (le i (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_mono1 (k j i : τ ι) :
  π (le k j) → π (Ord i) → π (le (omult k i) (omult j i)) ≔
begin
  admit
end;

opaque symbol omult_lt_mono2 (k j i : τ ι) :
  π (lt k j) → π (lt empty i) → π (lt (omult i k) (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_mono2 (k j i : τ ι) :
  π (le k j) → π (Ord i) → π (le (omult i k) (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_mono (ip i jp j : τ ι) :
  π (le ip i) → π (le jp j) → π (le (omult ip jp) (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_lt_mono (ip i jp j : τ ι) :
  π (le ip i) → π (lt jp j) → π (lt empty i) →
  π (lt (omult ip jp) (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_self2 (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (le i (omult j i)) ≔
begin
  admit
end;

opaque symbol omult_inject (i j k : τ ι) :
  π (omult i j = omult i k) → π (lt empty i) → π (Ord j) → π (Ord k) →
  π (j = k) ≔
begin
  admit
end;

// ===========================================================================
// The Relation Lt
// ===========================================================================

opaque symbol wf_Lt : π (wf_global Lt) ≔
begin
  admit
end;

opaque symbol irrefl_Lt (A : τ ι) : π (irrefl_on A Lt) ≔
begin
  admit
end;

opaque symbol trans_Lt (A : τ ι) : π (trans_on A Lt) ≔
begin
  admit
end;

opaque symbol part_ord_Lt (A : τ ι) : π (part_ord A Lt) ≔
begin
  admit
end;

opaque symbol linear_Lt : π (linear omega Lt) ≔
begin
  admit
end;

opaque symbol tot_ord_Lt : π (tot_ord omega Lt) ≔
begin
  admit
end;

opaque symbol well_ord_Lt : π (well_ord omega Lt) ≔
begin
  admit
end;
