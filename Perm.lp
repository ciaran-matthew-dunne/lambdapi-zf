// Perm: Injections, Surjections, Bijections, Composition
//
// Isabelle source: Perm.thy
// The theory underlying permutation groups:
//   -- Composition of relations, the identity relation
//   -- Injections, surjections, bijections
//   -- Lemmas for the Schroeder-Bernstein Theorem

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func;

// ===========================================================================
// Definitions
// ===========================================================================

// comp: composition of relations (Isabelle: r O s)
// Already defined as rcomp in pair.lp, but we re-export with Perm naming
// rcomp r s = {⟨x,z⟩ ∈ domain(s)×range(r) | ∃y. ⟨x,y⟩∈s ∧ ⟨y,z⟩∈r}

// id: identity function on A (Isabelle: id(A) = (λx∈A. x))
// id_rel is defined in pair.lp as RepFun A (λ x, Pair x x)
// Isabelle's id(A) = Lambda(A, λ x. x) which is the same as RepFun A (λ x, Pair x x)
// We define id_fun using Lambda for compatibility with fapply/Pi
symbol id_fun (A : τ ι) : τ ι ≔ Lambda A (λ x, x);

// inj: injective function space — {f ∈ A→B | ∀w∈A. ∀x∈A. f`w = f`x → w = x}
symbol inj (A B : τ ι) : τ ι ≔
  Collect (Pi A (λ _, B))
    (λ f, Ball A (λ w, Ball A (λ x, fapply f w = fapply f x ⇒ w = x)));

// surj: surjective function space — {f ∈ A→B | ∀y∈B. ∃x∈A. f`x = y}
symbol surj (A B : τ ι) : τ ι ≔
  Collect (Pi A (λ _, B))
    (λ f, Ball B (λ y, Bex A (λ x, fapply f x = y)));

// bij: bijective function space — inj(A,B) ∩ surj(A,B)
symbol bij (A B : τ ι) : τ ι ≔ Int (inj A B) (surj A B);

// ===========================================================================
// Section: Surjective Function Space
// ===========================================================================

// surj_is_fun: f ∈ surj(A,B) → f ∈ A→B
opaque symbol surj_is_fun (f A B : τ ι) :
  π (f ∈ surj A B) → π (f ∈ Pi A (λ _, B)) ≔
begin
  assume f A B hf;
  refine CollectD1 f (Pi A (λ _, B))
    (λ g, Ball B (λ y, Bex A (λ x, fapply g x = y))) hf
end;

// surj_memD: f ∈ surj(A,B) → Ball B (λ y, Bex A (λ x, fapply f x = y))
opaque symbol surj_memD (f A B : τ ι) :
  π (f ∈ surj A B) →
  π (Ball B (λ y, Bex A (λ x, fapply f x = y))) ≔
begin
  assume f A B hf;
  refine CollectD2 f (Pi A (λ _, B))
    (λ g, Ball B (λ y, Bex A (λ x, fapply g x = y))) hf
end;

// fun_is_surj: f ∈ Pi(A,B) → f ∈ surj(A, range(f))
opaque symbol fun_is_surj (f A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (f ∈ surj A (range f)) ≔
begin
  assume f A B hf;
  have hfun : π (function f) { refine Pi_function f A B hf };
  have hsub : π (f ⊆ Sigma A B) { refine Pi_subset_Sigma f A B hf };
  have hdomsub : π (A ⊆ domain f)
    { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (Pi_iff f A B) hf)) };
  refine CollectI f (Pi A (λ _, range f))
    (λ g, Ball (range f) (λ y, Bex A (λ x, fapply g x = y))) _ _
  { // f ∈ Pi(A, λ_. range f): every pair of f lands in A × range(f)
    refine ∧ₑ₂ (Pi_iff f A (λ _, range f)) _;
    refine ∧ᵢ hfun (∧ᵢ _ hdomsub);
    assume p hp;
    have hpS : π (p ∈ Sigma A B) { refine hsub p hp };
    have hbex : π (Bex A (λ x, Bex (B x) (λ y, p = Pair x y)))
      { refine SigmaE p A B hpS };
    refine ∃ₑ hbex _; assume x hx;
    refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
    have hpeq : π (p = Pair x y) { refine ∧ₑ₂ hy };
    have hPxy : π (Pair x y ∈ f) { refine ind_eq (eq_sym hpeq) (λ w, w ∈ f) hp };
    refine ind_eq hpeq (λ w, w ∈ Sigma A (λ _, range f))
      (SigmaI x y A (λ _, range f) (∧ₑ₁ hx) (rangeI x y f hPxy)) }
  { // every y ∈ range f is hit: rangeE gives the preimage
    assume y hyr;
    refine ∃ₑ (rangeE y f hyr) _; assume a ha;
    have haS : π (Pair a y ∈ Sigma A B) { refine hsub (Pair a y) ha };
    have haA : π (a ∈ A)
      { refine ind_eq (eq_sym (fst_conv a y)) (λ w, w ∈ A)
          (SigmaD1 (Pair a y) A B haS) };
    refine ∃ᵢ a (∧ᵢ haA (function_apply_equality a y f ha hfun)) }
end;

// surj_range: f ∈ surj(A,B) → range(f) = B
opaque symbol surj_range (f A B : τ ι) :
  π (f ∈ surj A B) → π (range f = B) ≔
begin
  assume f A B hf;
  have hfun : π (f ∈ Pi A (λ _, B)) { refine surj_is_fun f A B hf };
  have hmem : π (Ball B (λ y, Bex A (λ x, fapply f x = y))) { refine surj_memD f A B hf };
  have hsub : π (f ⊆ Sigma A (λ _, B))
    { refine Pi_subset_Sigma f A (λ _, B) hfun };
  refine subset_antisym (range f) B _ _
  { // range f ⊆ B
    assume y hy;
    refine ∃ₑ (rangeE y f hy) _; assume a hay;
    have hSig : π (Pair a y ∈ Sigma A (λ _, B))
      { refine subsetD f (Sigma A (λ _, B)) (Pair a y) hsub hay };
    refine ind_eq (eq_sym (snd_conv a y)) (λ w, w ∈ B) (SigmaD2 (Pair a y) A (λ _, B) hSig) }
  { // B ⊆ range f
    assume y hy;
    refine ∃ₑ (hmem y hy) _; assume x hx;
    have hfxy : π (fapply f x = y) { refine ∧ₑ₂ hx };
    have hpair : π (Pair x (fapply f x) ∈ f)
      { refine Pi_apply_Pair f x A (λ _, B) hfun (∧ₑ₁ hx) };
    refine rangeI x y f (ind_eq (eq_sym hfxy) (λ w, Pair x w ∈ f) hpair) }
end;

// f_imp_surjective: f ∈ A→B → (∀y∈B. d(y) ∈ A) → (∀y∈B. f`d(y) = y) → f ∈ surj(A,B)
opaque symbol f_imp_surjective (f A B : τ ι) (d : τ ι → τ ι) :
  π (f ∈ Pi A (λ _, B)) →
  π (Ball B (λ y, d y ∈ A)) →
  π (Ball B (λ y, fapply f (d y) = y)) →
  π (f ∈ surj A B) ≔
begin
  assume f A B d hfun hd hfd;
  refine CollectI f (Pi A (λ _, B))
    (λ g, Ball B (λ y, Bex A (λ x, fapply g x = y))) hfun _;
  assume y hyB;
  refine ∃ᵢ (d y) _;
  apply ∧ᵢ
  { refine hd y hyB }
  { refine hfd y hyB }
end;

// lam_surjective: (∀x∈A. c(x)∈B) → (∀y∈B. d(y)∈A) → (∀y∈B. c(d(y))=y) →
//   Lambda(A,c) ∈ surj(A,B)
opaque symbol lam_surjective (A B : τ ι) (c d : τ ι → τ ι) :
  π (Ball A (λ x, c x ∈ B)) →
  π (Ball B (λ y, d y ∈ A)) →
  π (Ball B (λ y, c (d y) = y)) →
  π (Lambda A c ∈ surj A B) ≔
begin
  assume A B c d hc hd hcd;
  refine f_imp_surjective (Lambda A c) A B d _ _ _
  { // Lambda(A,c) ∈ A→B
    refine lam_type A c (λ _, B) hc }
  { // ∀y∈B. d(y) ∈ A
    assume y hyB; refine hd y hyB }
  { // ∀y∈B. fapply(Lambda(A,c), d(y)) = y
    assume y hyB;
    have hdA : π (d y ∈ A) { refine hd y hyB };
    have hbeta : π (fapply (Lambda A c) (d y) = c (d y))
      { refine beta A c (d y) hdA };
    rewrite hbeta;
    refine hcd y hyB }
end;

// ===========================================================================
// Section: Injective Function Space
// ===========================================================================

// inj_is_fun: f ∈ inj(A,B) → f ∈ A→B
opaque symbol inj_is_fun (f A B : τ ι) :
  π (f ∈ inj A B) → π (f ∈ Pi A (λ _, B)) ≔
begin
  assume f A B hf;
  refine CollectD1 f (Pi A (λ _, B))
    (λ g, Ball A (λ w, Ball A (λ x, fapply g w = fapply g x ⇒ w = x))) hf
end;

// inj_memD: f ∈ inj(A,B) → ∀w∈A. ∀x∈A. f`w = f`x → w = x
opaque symbol inj_memD (f A B : τ ι) :
  π (f ∈ inj A B) →
  π (Ball A (λ w, Ball A (λ x, fapply f w = fapply f x ⇒ w = x))) ≔
begin
  assume f A B hf;
  refine CollectD2 f (Pi A (λ _, B))
    (λ g, Ball A (λ w, Ball A (λ x, fapply g w = fapply g x ⇒ w = x))) hf
end;

// inj_apply_equality: f ∈ inj(A,B) → f`a = f`b → a ∈ A → b ∈ A → a = b
opaque symbol inj_apply_equality (f A B : τ ι) (a b : τ ι) :
  π (f ∈ inj A B) → π (fapply f a = fapply f b) →
  π (a ∈ A) → π (b ∈ A) → π (a = b) ≔
begin
  assume f A B a b hinj heq haA hbA;
  have hcond : π (Ball A (λ w, Ball A (λ x, fapply f w = fapply f x ⇒ w = x)))
    { refine inj_memD f A B hinj };
  refine hcond a haA b hbA heq
end;

// f_imp_injective: f ∈ A→B → Ball A (λ x, d(fapply f x) = x) → f ∈ inj(A,B)
opaque symbol f_imp_injective (f A B : τ ι) (d : τ ι → τ ι) :
  π (f ∈ Pi A (λ _, B)) →
  π (Ball A (λ x, d (fapply f x) = x)) →
  π (f ∈ inj A B) ≔
begin
  assume f A B d hfun hd;
  refine CollectI f (Pi A (λ _, B))
    (λ g, Ball A (λ w, Ball A (λ x, fapply g w = fapply g x ⇒ w = x))) hfun _;
  assume w hwA x hxA heq;
  // d(f`w) = w and d(f`x) = x
  have hdw : π (d (fapply f w) = w) { refine hd w hwA };
  have hdx : π (d (fapply f x) = x) { refine hd x hxA };
  // f`w = f`x, so d(f`w) = d(f`x), so w = x
  rewrite left hdw;
  rewrite heq;
  apply hdx
end;

// lam_injective: (∀x∈A. c(x)∈B) → (∀x∈A. d(c(x)) = x) → Lambda(A,c) ∈ inj(A,B)
opaque symbol lam_injective (A B : τ ι) (c d : τ ι → τ ι) :
  π (Ball A (λ x, c x ∈ B)) →
  π (Ball A (λ x, d (c x) = x)) →
  π (Lambda A c ∈ inj A B) ≔
begin
  assume A B c d hc hdc;
  refine f_imp_injective (Lambda A c) A B d _ _
  { refine lam_type A c (λ _, B) hc }
  { assume x hxA;
    have hbeta : π (fapply (Lambda A c) x = c x)
      { refine beta A c x hxA };
    rewrite hbeta;
    refine hdc x hxA }
end;

// ===========================================================================
// Section: Bijections
// ===========================================================================

// bij_is_inj: f ∈ bij(A,B) → f ∈ inj(A,B)
opaque symbol bij_is_inj (f A B : τ ι) :
  π (f ∈ bij A B) → π (f ∈ inj A B) ≔
begin
  assume f A B hf;
  refine IntD1 f (inj A B) (surj A B) hf
end;

// bij_is_surj: f ∈ bij(A,B) → f ∈ surj(A,B)
opaque symbol bij_is_surj (f A B : τ ι) :
  π (f ∈ bij A B) → π (f ∈ surj A B) ≔
begin
  assume f A B hf;
  refine IntD2 f (inj A B) (surj A B) hf
end;

// bij_is_fun: f ∈ bij(A,B) → f ∈ A→B
opaque symbol bij_is_fun (f A B : τ ι) :
  π (f ∈ bij A B) → π (f ∈ Pi A (λ _, B)) ≔
begin
  assume f A B hf;
  have hinj : π (f ∈ inj A B) { refine bij_is_inj f A B hf };
  refine inj_is_fun f A B hinj
end;

// (bij_inverse_exists is proved at the end of this file, after the converse
// machinery it depends on.)

// ===========================================================================
// Section: Composition helper lemmas (selected)
// ===========================================================================

// comp_mono: r ⊆ r' → s ⊆ s' → comp(r,s) ⊆ comp(r',s')
opaque symbol comp_mono (r r' s s' : τ ι) :
  π (r ⊆ r') → π (s ⊆ s') → π (rcomp r s ⊆ rcomp r' s') ≔
begin
  assume r r' s s' hr hs p hp;
  have hp' : π (p ∈ Collect (Sigma (domain s) (λ _, range r))
      (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ s ∧ Pair y (snd q) ∈ r))
    { refine ind_eq (eq_sym (rcomp_def r s)) (λ z, p ∈ z) hp };
  have hpS : π (p ∈ Sigma (domain s) (λ _, range r))
    { refine CollectD1 p (Sigma (domain s) (λ _, range r))
        (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ s ∧ Pair y (snd q) ∈ r) hp' };
  have hpred : π (`∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r)
    { refine CollectD2 p (Sigma (domain s) (λ _, range r))
        (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ s ∧ Pair y (snd q) ∈ r) hp' };
  refine ∃ₑ hpred _; assume y hy;
  have hsy' : π (Pair (fst p) y ∈ s') { refine hs (Pair (fst p) y) (∧ₑ₁ hy) };
  have hry' : π (Pair y (snd p) ∈ r') { refine hr (Pair y (snd p)) (∧ₑ₂ hy) };
  have hpeq : π (Pair (fst p) (snd p) = p)
    { refine Pair_fst_snd p (domain s) (λ _, range r) hpS };
  have hpS' : π (p ∈ Sigma (domain s') (λ _, range r'))
    { refine ind_eq (eq_sym hpeq) (λ w, w ∈ Sigma (domain s') (λ _, range r'))
        (SigmaI (fst p) (snd p) (domain s') (λ _, range r')
          (domainI (fst p) y s' hsy') (rangeI y (snd p) r' hry')) };
  rewrite rcomp_def;
  refine CollectI p (Sigma (domain s') (λ _, range r'))
    (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ s' ∧ Pair y (snd q) ∈ r') hpS'
    (∃ᵢ y (∧ᵢ hsy' hry'))
end;

// rcomp_Int_subset: rcomp(r∩r', s∩s') ⊆ rcomp(r,s) ∩ rcomp(r',s')
opaque symbol rcomp_Int_subset (r r' s s' : τ ι) :
  π (rcomp (Int r r') (Int s s') ⊆ Int (rcomp r s) (rcomp r' s')) ≔
begin
  assume r r' s s' p hp;
  have hp' : π (p ∈ Collect (Sigma (domain (Int s s')) (λ _, range (Int r r')))
      (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ Int s s' ∧ Pair y (snd q) ∈ Int r r'))
    { refine ind_eq (eq_sym (rcomp_def (Int r r') (Int s s'))) (λ z, p ∈ z) hp };
  have hpS : π (p ∈ Sigma (domain (Int s s')) (λ _, range (Int r r')))
    { refine CollectD1 p (Sigma (domain (Int s s')) (λ _, range (Int r r')))
        (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ Int s s' ∧ Pair y (snd q) ∈ Int r r') hp' };
  have hpred : π (`∃ (y : τ ι), Pair (fst p) y ∈ Int s s' ∧ Pair y (snd p) ∈ Int r r')
    { refine CollectD2 p (Sigma (domain (Int s s')) (λ _, range (Int r r')))
        (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ Int s s' ∧ Pair y (snd q) ∈ Int r r') hp' };
  refine ∃ₑ hpred _; assume y hy;
  have hs1 : π (Pair (fst p) y ∈ s) { refine IntD1 (Pair (fst p) y) s s' (∧ₑ₁ hy) };
  have hs2 : π (Pair (fst p) y ∈ s') { refine IntD2 (Pair (fst p) y) s s' (∧ₑ₁ hy) };
  have hr1 : π (Pair y (snd p) ∈ r) { refine IntD1 (Pair y (snd p)) r r' (∧ₑ₂ hy) };
  have hr2 : π (Pair y (snd p) ∈ r') { refine IntD2 (Pair y (snd p)) r r' (∧ₑ₂ hy) };
  have hpeq : π (Pair (fst p) (snd p) = p)
    { refine Pair_fst_snd p (domain (Int s s')) (λ _, range (Int r r')) hpS };
  refine IntI p (rcomp r s) (rcomp r' s') _ _
  { have hpS1 : π (p ∈ Sigma (domain s) (λ _, range r))
      { refine ind_eq (eq_sym hpeq) (λ w, w ∈ Sigma (domain s) (λ _, range r))
          (SigmaI (fst p) (snd p) (domain s) (λ _, range r)
            (domainI (fst p) y s hs1) (rangeI y (snd p) r hr1)) };
    rewrite rcomp_def;
    refine CollectI p (Sigma (domain s) (λ _, range r))
      (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ s ∧ Pair y (snd q) ∈ r) hpS1
      (∃ᵢ y (∧ᵢ hs1 hr1)) }
  { have hpS2 : π (p ∈ Sigma (domain s') (λ _, range r'))
      { refine ind_eq (eq_sym hpeq) (λ w, w ∈ Sigma (domain s') (λ _, range r'))
          (SigmaI (fst p) (snd p) (domain s') (λ _, range r')
            (domainI (fst p) y s' hs2) (rangeI y (snd p) r' hr2)) };
    rewrite rcomp_def;
    refine CollectI p (Sigma (domain s') (λ _, range r'))
      (λ q, `∃ (y : τ ι), Pair (fst q) y ∈ s' ∧ Pair y (snd q) ∈ r') hpS2
      (∃ᵢ y (∧ᵢ hs2 hr2)) }
end;

// ===========================================================================
// Section: Basic converse and function utilities (used by EquivClass)
// ===========================================================================

opaque symbol converseI (a b r : τ ι) :
  π (Pair a b ∈ r) → π (Pair b a ∈ converse r) ≔
begin
  assume a b r hab;
  have hcoll : π (Pair a b ∈ Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    { refine CollectI (Pair a b) r
        (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y)
        hab (∃ᵢ a (∃ᵢ b (eq_refl (Pair a b)))) };
  // RepFunI gives Pair(snd(Pair a b), fst(Pair a b)) ∈ converse r; rewrite the projections.
  have hrep : π (Pair (snd (Pair a b)) (fst (Pair a b)) ∈ converse r)
    { rewrite converse_def;
      refine RepFunI (Pair a b)
        (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
        (λ p, Pair (snd p) (fst p)) hcoll };
  have h1 : π (Pair b (fst (Pair a b)) ∈ converse r)
    { refine ind_eq (eq_sym (snd_conv a b)) (λ w, Pair w (fst (Pair a b)) ∈ converse r) hrep };
  refine ind_eq (eq_sym (fst_conv a b)) (λ w, Pair b w ∈ converse r) h1
end;

// converseD: Pair(a,b) ∈ converse(r) → Pair(b,a) ∈ r
opaque symbol converseD (a b r : τ ι) :
  π (Pair a b ∈ converse r) → π (Pair b a ∈ r) ≔
begin
  assume a b r h;
  have h' : π (Pair a b ∈ RepFun (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
                  (λ p, Pair (snd p) (fst p)))
    { refine ind_eq (eq_sym (converse_def r)) (λ s, Pair a b ∈ s) h };
  have hbex : π (Bex (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
                     (λ q, Pair a b = Pair (snd q) (fst q)))
    { refine ∧ₑ₁ (RepFun_iff (Pair a b)
        (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
        (λ p, Pair (snd p) (fst p))) h' };
  refine ∃ₑ hbex _;
  assume q hq;
  have hqC : π (q ∈ Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    { refine ∧ₑ₁ hq };
  have heq : π (Pair a b = Pair (snd q) (fst q)) { refine ∧ₑ₂ hq };
  have hqr : π (q ∈ r)
    { refine CollectD1 q r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y) hqC };
  have hpair : π (`∃ x : τ ι, `∃ y : τ ι, q = Pair x y)
    { refine CollectD2 q r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y) hqC };
  refine ∃ₑ hpair _; assume x hx; refine ∃ₑ hx _; assume y hy;
  have hqeq : π (q = Pair x y) { refine hy };
  have hqr2 : π (Pair x y ∈ r) { refine ind_eq (eq_sym hqeq) (λ z, z ∈ r) hqr };
  have hsndq : π (snd q = y) { rewrite hqeq; refine snd_conv x y };
  have hfstq : π (fst q = x) { rewrite hqeq; refine fst_conv x y };
  have hay : π (a = snd q) { refine Pair_inject1 a b (snd q) (fst q) heq };
  have hbx : π (b = fst q) { refine Pair_inject2 a b (snd q) (fst q) heq };
  have hay2 : π (a = y) { rewrite hay; refine hsndq };
  have hbx2 : π (b = x) { rewrite hbx; refine hfstq };
  have step1 : π (Pair x a ∈ r) { refine ind_eq hay2 (λ w, Pair x w ∈ r) hqr2 };
  refine ind_eq hbx2 (λ w, Pair w a ∈ r) step1
end;

// converseE: a general element of converse(r) is a pair with the swapped pair in r.
//   z ∈ converse(r) → ∃x y. z = Pair(x,y) ∧ Pair(y,x) ∈ r
opaque symbol converseE (z r : τ ι) :
  π (z ∈ converse r) →
  π (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair x y ∧ Pair y x ∈ r) ≔
begin
  assume z r h;
  have h' : π (z ∈ RepFun (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
                  (λ p, Pair (snd p) (fst p)))
    { refine ind_eq (eq_sym (converse_def r)) (λ s, z ∈ s) h };
  have hbex : π (Bex (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
                     (λ q, z = Pair (snd q) (fst q)))
    { refine ∧ₑ₁ (RepFun_iff z
        (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
        (λ p, Pair (snd p) (fst p))) h' };
  refine ∃ₑ hbex _;
  assume q hq;
  have hqC : π (q ∈ Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    { refine ∧ₑ₁ hq };
  have hzeq : π (z = Pair (snd q) (fst q)) { refine ∧ₑ₂ hq };
  have hqr : π (q ∈ r)
    { refine CollectD1 q r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y) hqC };
  have hpair : π (`∃ x : τ ι, `∃ y : τ ι, q = Pair x y)
    { refine CollectD2 q r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y) hqC };
  refine ∃ₑ hpair _; assume a hx; refine ∃ₑ hx _; assume b hy;
  have hqeq : π (q = Pair a b) { refine hy };
  have hsndq : π (snd q = b) { rewrite hqeq; refine snd_conv a b };
  have hfstq : π (fst q = a) { rewrite hqeq; refine fst_conv a b };
  have hqr2 : π (Pair a b ∈ r) { refine ind_eq (eq_sym hqeq) (λ w, w ∈ r) hqr };
  // z = Pair(snd q, fst q) = Pair(b,a); witnesses x=b, y=a.
  refine ∃ᵢ b (∃ᵢ a (∧ᵢ _ hqr2));
  have h1 : π (z = Pair b (fst q))
    { refine ind_eq (eq_sym hsndq) (λ w, z = Pair w (fst q)) hzeq };
  refine ind_eq (eq_sym hfstq) (λ w, z = Pair b w) h1
end;

// apply_equality: Pair(a,b) ∈ f → f ∈ Pi(A,B) → fapply(f,a) = b
opaque symbol apply_equality (a b f A : τ ι) (B : τ ι → τ ι) :
  π (Pair a b ∈ f) → π (f ∈ Pi A B) → π (fapply f a = b) ≔
begin
  assume a b f A B hmem hfPi;
  refine function_apply_equality a b f hmem (Pi_function f A B hfPi)
end;

// domain_type: Pair(a,b) ∈ f → f ∈ Pi(A,B) → a ∈ A
opaque symbol domain_type (a b f A : τ ι) (B : τ ι → τ ι) :
  π (Pair a b ∈ f) → π (f ∈ Pi A B) → π (a ∈ A) ≔
begin
  assume a b f A B hmem hfPi;
  have hsub : π (f ⊆ Sigma A B) { refine Pi_subset_Sigma f A B hfPi };
  have hSig : π (Pair a b ∈ Sigma A B) { refine subsetD f (Sigma A B) (Pair a b) hsub hmem };
  refine ind_eq (eq_sym (fst_conv a b)) (λ w, w ∈ A) (SigmaD1 (Pair a b) A B hSig)
end;

// range_type: Pair(a,b) ∈ f → f ∈ Pi(A,B) → b ∈ B(a)
opaque symbol range_type (a b f A : τ ι) (B : τ ι → τ ι) :
  π (Pair a b ∈ f) → π (f ∈ Pi A B) → π (b ∈ B a) ≔
begin
  assume a b f A B hmem hfPi;
  have hsub : π (f ⊆ Sigma A B) { refine Pi_subset_Sigma f A B hfPi };
  have hSig : π (Pair a b ∈ Sigma A B) { refine subsetD f (Sigma A B) (Pair a b) hsub hmem };
  have h2 : π (snd (Pair a b) ∈ B (fst (Pair a b))) { refine SigmaD2 (Pair a b) A B hSig };
  have h3 : π (b ∈ B (fst (Pair a b)))
    { refine ind_eq (eq_sym (snd_conv a b)) (λ w, w ∈ B (fst (Pair a b))) h2 };
  refine ind_eq (eq_sym (fst_conv a b)) (λ w, b ∈ B w) h3
end;

// ===========================================================================
// lam_bijective: a Lambda with a two-sided inverse is a bijection.
//   (∀x∈A. c x ∈ B) → (∀y∈B. d y ∈ A) →
//   (∀x∈A. d(c x) = x) → (∀y∈B. c(d y) = y) → Lambda(A,c) ∈ bij(A,B)
//   bij = inj ∩ surj, so combine lam_injective and lam_surjective.
// ===========================================================================
opaque symbol lam_bijective (A B : τ ι) (c d : τ ι → τ ι) :
  π (Ball A (λ x, c x ∈ B)) →
  π (Ball B (λ y, d y ∈ A)) →
  π (Ball A (λ x, d (c x) = x)) →
  π (Ball B (λ y, c (d y) = y)) →
  π (Lambda A c ∈ bij A B) ≔
begin
  assume A B c d hcB hdA hdc hcd;
  refine IntI (Lambda A c) (inj A B) (surj A B) _ _
  { refine lam_injective A B c d hcB hdc }
  { refine lam_surjective A B c d hcB hdA hcd }
end;

// ===========================================================================
// Section: Converse of injections and bijections (Perm.thy)
// ===========================================================================

// The converse of an injection is a function (core of inj_converse_fun).
opaque symbol inj_converse_function (f A B : τ ι) :
  π (f ∈ inj A B) → π (function (converse f)) ≔
begin
  assume f A B hinj;
  rewrite function_def;
  assume y w wp hw hwp;
  have hfPi : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  have hwf : π (Pair w y ∈ f) { refine converseD y w f hw };
  have hwpf : π (Pair wp y ∈ f) { refine converseD y wp f hwp };
  have hwA : π (w ∈ A) { refine domain_type w y f A (λ _, B) hwf hfPi };
  have hwpA : π (wp ∈ A) { refine domain_type wp y f A (λ _, B) hwpf hfPi };
  have hfw : π (fapply f w = y) { refine apply_equality w y f A (λ _, B) hwf hfPi };
  have hfwp : π (fapply f wp = y) { refine apply_equality wp y f A (λ _, B) hwpf hfPi };
  refine inj_apply_equality f A B w wp hinj _ hwA hwpA;
  rewrite hfw; rewrite hfwp; reflexivity
end;

// left_inverse: f ∈ inj(A,B) → a ∈ A → converse(f)`(f`a) = a
opaque symbol left_inverse (f A B a : τ ι) :
  π (f ∈ inj A B) → π (a ∈ A) → π (fapply (converse f) (fapply f a) = a) ≔
begin
  assume f A B a hinj ha;
  have hfPi : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  have hPa : π (Pair a (fapply f a) ∈ f)
    { refine Pi_apply_Pair f a A (λ _, B) hfPi ha };
  refine function_apply_equality (fapply f a) a (converse f)
    (converseI a (fapply f a) f hPa) (inj_converse_function f A B hinj)
end;

// right_inverse: f ∈ inj(A,B) → b ∈ range(f) → f`(converse(f)`b) = b
opaque symbol right_inverse (f A B b : τ ι) :
  π (f ∈ inj A B) → π (b ∈ range f) → π (fapply f (fapply (converse f) b) = b) ≔
begin
  assume f A B b hinj hb;
  have hfPi : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  refine ∃ₑ (rangeE b f hb) _;
  assume x hx;
  have hcb : π (fapply (converse f) b = x)
    { refine function_apply_equality b x (converse f)
        (converseI x b f hx) (inj_converse_function f A B hinj) };
  rewrite hcb;
  refine apply_equality x b f A (λ _, B) hx hfPi
end;

// inj_converse_fun: f ∈ inj(A,B) → converse(f) ∈ range(f) → A
opaque symbol inj_converse_fun (f A B : τ ι) :
  π (f ∈ inj A B) → π (converse f ∈ Pi (range f) (λ _, A)) ≔
begin
  assume f A B hinj;
  have hfPi : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  rewrite Pi_def;
  refine CollectI (converse f) (Pow (Sigma (range f) (λ _, A)))
    (λ g, range f ⊆ domain g ∧ function g) _ _
  { refine PowI (converse f) (Sigma (range f) (λ _, A)) _;
    assume z hz;
    refine ∃ₑ (converseE z f hz) _; assume x hx;
    refine ∃ₑ hx _; assume y hy;
    have hyx : π (Pair y x ∈ f) { refine ∧ₑ₂ hy };
    have hxr : π (x ∈ range f) { refine rangeI y x f hyx };
    have hyA : π (y ∈ A) { refine domain_type y x f A (λ _, B) hyx hfPi };
    refine ind_eq (∧ₑ₁ hy) (λ w, w ∈ Sigma (range f) (λ _, A))
      (SigmaI x y (range f) (λ _, A) hxr hyA) }
  { apply ∧ᵢ
    { assume b hb;
      refine ∃ₑ (rangeE b f hb) _; assume x hx;
      refine domainI b x (converse f) (converseI x b f hx) }
    { refine inj_converse_function f A B hinj } }
end;

// bij_converse_bij: f ∈ bij(A,B) → converse(f) ∈ bij(B,A)
opaque symbol bij_converse_bij (f A B : τ ι) :
  π (f ∈ bij A B) → π (converse f ∈ bij B A) ≔
begin
  assume f A B hbij;
  have hinj : π (f ∈ inj A B) { refine bij_is_inj f A B hbij };
  have hfPi : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  have hrange : π (range f = B)
    { refine surj_range f A B (bij_is_surj f A B hbij) };
  have hconvPi : π (converse f ∈ Pi B (λ _, A))
    { refine ind_eq (eq_sym hrange) (λ w, converse f ∈ Pi w (λ _, A))
        (inj_converse_fun f A B hinj) };
  refine IntI (converse f) (inj B A) (surj B A) _ _
  { refine f_imp_injective (converse f) B A (λ b, fapply f b) hconvPi _;
    assume y hyB;
    have hyr : π (y ∈ range f) { refine ind_eq hrange (λ w, y ∈ w) hyB };
    refine right_inverse f A B y hinj hyr }
  { refine f_imp_surjective (converse f) B A (λ a, fapply f a) hconvPi _ _
    { assume a haA; refine fapply_type f a A (λ _, B) hfPi haA }
    { assume a haA; refine left_inverse f A B a hinj haA } }
end;

// left_inverse_bij: f ∈ bij(A,B) → a ∈ A → converse(f)`(f`a) = a
opaque symbol left_inverse_bij (f A B a : τ ι) :
  π (f ∈ bij A B) → π (a ∈ A) → π (fapply (converse f) (fapply f a) = a) ≔
begin
  assume f A B a hbij ha;
  refine left_inverse f A B a (bij_is_inj f A B hbij) ha
end;

// right_inverse_bij: f ∈ bij(A,B) → b ∈ B → f`(converse(f)`b) = b
opaque symbol right_inverse_bij (f A B b : τ ι) :
  π (f ∈ bij A B) → π (b ∈ B) → π (fapply f (fapply (converse f) b) = b) ≔
begin
  assume f A B b hbij hb;
  have hrange : π (range f = B)
    { refine surj_range f A B (bij_is_surj f A B hbij) };
  refine right_inverse f A B b (bij_is_inj f A B hbij)
    (ind_eq hrange (λ w, b ∈ w) hb)
end;

// converse_bij_apply_type: f ∈ bij(A,B) → b ∈ B → converse(f)`b ∈ A
// (bij_converse_bij + apply_type, packaged for downstream use)
opaque symbol converse_bij_apply_type (f A B b : τ ι) :
  π (f ∈ bij A B) → π (b ∈ B) → π (fapply (converse f) b ∈ A) ≔
begin
  assume f A B b hbij hb;
  have hcb : π (converse f ∈ bij B A) { refine bij_converse_bij f A B hbij };
  refine fapply_type (converse f) b B (λ _, A)
    (inj_is_fun (converse f) B A (bij_is_inj (converse f) B A hcb)) hb
end;

// bij_inverse_exists: f ∈ bij(A,B) → ∃g∈B→A. ∀a∈A. g`(f`a)=a ∧ f`(g`(f`a))=f`a
// Witness: converse(f), via left_inverse_bij.
opaque symbol bij_inverse_exists (f A B : τ ι) :
  π (f ∈ bij A B) →
  π (Bex (Pi B (λ _, A)) (λ g,
    Ball A (λ a, fapply g (fapply f a) = a ∧ fapply f (fapply g (fapply f a)) = fapply f a))) ≔
begin
  assume f A B hf;
  have hinj : π (f ∈ inj A B) { refine bij_is_inj f A B hf };
  have hrange : π (range f = B)
    { refine surj_range f A B (bij_is_surj f A B hf) };
  have hconvPi : π (converse f ∈ Pi B (λ _, A))
    { refine ind_eq (eq_sym hrange) (λ w, converse f ∈ Pi w (λ _, A))
        (inj_converse_fun f A B hinj) };
  refine ∃ᵢ (converse f) (∧ᵢ hconvPi _);
  assume a ha;
  have hli : π (fapply (converse f) (fapply f a) = a)
    { refine left_inverse f A B a hinj ha };
  apply ∧ᵢ hli _;
  rewrite hli;
  reflexivity
end;
