// Trancl: Transitive closure of relations
//
// Isabelle source: Trancl.thy
// Defines: rtrancl (r^*), trancl (r^+), trans, sym, antisym
// Uses lfp from Fixedpt

require open ZF.ZF_Base ZF.upair ZF.pair ZF.Fixedpt;

// ===========================================================================
// Relation properties
// ===========================================================================

// trans(r): r is transitive
symbol trans (r : τ ι) : Prop ≔
  `∀ (x : τ ι), `∀ (y : τ ι), `∀ (z : τ ι),
    Pair x y ∈ r ⇒ Pair y z ∈ r ⇒ Pair x z ∈ r;

// transD: elimination for trans — unfold the trans predicate
opaque symbol transD (r a b c : τ ι) :
  π (trans r) → π (Pair a b ∈ r) → π (Pair b c ∈ r) → π (Pair a c ∈ r) ≔
begin
  assume r a b c htr hab hbc;
  refine htr a b c hab hbc
end;

// sym(r): r is symmetric
symbol sym (r : τ ι) : Prop ≔
  `∀ (x : τ ι), `∀ (y : τ ι),
    Pair x y ∈ r ⇒ Pair y x ∈ r;

// antisym(r): r is antisymmetric
symbol antisym (r : τ ι) : Prop ≔
  `∀ (x : τ ι), `∀ (y : τ ι),
    Pair x y ∈ r ⇒ Pair y x ∈ r ⇒ x = y;

// irrefl(A,r): r is irreflexive on A   (faithful to Isabelle irrefl(A,r) ≡ ∀x∈A. ⟨x,x⟩∉r)
symbol irrefl (A r : τ ι) : Prop ≔
  Ball A (λ x, Pair x x ∉ r);

// ===========================================================================
// Reflexive-transitive closure: r^* = lfp(field(r) × field(r), λs. id(field(r)) ∪ (r O s))
// ===========================================================================

symbol rtrancl (r : τ ι) : τ ι ≔
  lfp (Sigma (field r) (λ _, field r))
      (λ s, Un (id_rel (field r)) (rcomp r s));

// ===========================================================================
// Transitive closure: r^+ = r O r^*
// ===========================================================================

symbol trancl (r : τ ι) : τ ι ≔ rcomp r (rtrancl r);

// ===========================================================================
// Helper: bnd_mono for the rtrancl operator
// ===========================================================================

// We need: bnd_mono(D, h) where D = Sigma(field(r), λ_. field(r))
// and h(s) = Un(id_rel(field(r)), rcomp(r,s))
// bnd_mono means: h(D) ⊆ D ∧ (∀W X. W ⊆ X → X ⊆ D → h(W) ⊆ h(X))

// Helper: fieldI1 — Pair(a,b) ∈ r → a ∈ field(r)
opaque symbol fieldI1 (a b r : τ ι) :
  π (Pair a b ∈ r) → π (a ∈ field r) ≔
begin
  assume a b r h;
  refine UnI1 a (domain r) (range r) (domainI a b r h)
end;

// Helper: fieldI2 — Pair(a,b) ∈ r → b ∈ field(r)
opaque symbol fieldI2 (a b r : τ ι) :
  π (Pair a b ∈ r) → π (b ∈ field r) ≔
begin
  assume a b r h;
  refine UnI2 b (domain r) (range r) (rangeI a b r h)
end;

// Helper: id_rel membership — p ∈ id_rel(A) ⟷ ∃x∈A. p = Pair(x,x)
opaque symbol id_relI (a A : τ ι) :
  π (a ∈ A) → π (Pair a a ∈ id_rel A) ≔
begin
  assume a A h;
  refine RepFunI a A (λ x, Pair x x) h
end;

opaque symbol id_relE (p A : τ ι) :
  π (p ∈ id_rel A) → π (Bex A (λ x, p = Pair x x)) ≔
begin
  assume p A h;
  refine ∧ₑ₁ (RepFun_iff p A (λ x, Pair x x)) h
end;

// Helper: rcomp membership intro
opaque symbol rcompI (a b c r s : τ ι) :
  π (Pair a b ∈ s) → π (Pair b c ∈ r) →
  π (Pair a c ∈ rcomp r s) ≔
begin
  assume a b c r s hs hr;
  // rcomp r s = Collect(Sigma(domain(s), λ_. range(r)), λp. ∃y. Pair(fst(p),y) ∈ s ∧ Pair(y,snd(p)) ∈ r)
  // Need: Pair(a,c) ∈ Collect(Sigma(domain(s), λ_. range(r)), ...)
  refine CollectI (Pair a c) (Sigma (domain s) (λ _, range r))
    (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r) _ _
  { // Pair(a,c) ∈ Sigma(domain(s), λ_. range(r))
    refine SigmaI a c (domain s) (λ _, range r)
      (domainI a b s hs) (rangeI b c r hr) }
  { // ∃y. Pair(fst(Pair(a,c)), y) ∈ s ∧ Pair(y, snd(Pair(a,c))) ∈ r
    // fst(Pair(a,c)) = a, snd(Pair(a,c)) = c
    refine ∃ᵢ b _;
    apply ∧ᵢ
    { // Pair(fst(Pair(a,c)), b) ∈ s, i.e., Pair(a, b) ∈ s
      have hfst : π (fst (Pair a c) = a) { refine fst_conv a c };
      refine ind_eq hfst (λ z, Pair z b ∈ s) hs }
    { // Pair(b, snd(Pair(a,c))) ∈ r, i.e., Pair(b, c) ∈ r
      have hsnd : π (snd (Pair a c) = c) { refine snd_conv a c };
      refine ind_eq hsnd (λ z, Pair b z ∈ r) hr } }
end;

// Helper: rcomp membership elim
opaque symbol rcompE (p r s : τ ι) :
  π (p ∈ rcomp r s) →
  π (`∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r) ≔
begin
  assume p r s h;
  refine CollectD2 p (Sigma (domain s) (λ _, range r))
    (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r) h
end;

// Helper: rcomp elim for Pair — avoids fst/snd
opaque symbol rcompE_pair (u v r s : τ ι) :
  π (Pair u v ∈ rcomp r s) →
  π (`∃ (y : τ ι), Pair u y ∈ s ∧ Pair y v ∈ r) ≔
begin
  assume u v r s h;
  have hex : π (`∃ (y : τ ι), Pair (fst (Pair u v)) y ∈ s ∧ Pair y (snd (Pair u v)) ∈ r)
    { refine rcompE (Pair u v) r s h };
  refine ∃ₑ hex _;
  assume y hy;
  have hfst : π (fst (Pair u v) = u) { refine fst_conv u v };
  have hsnd : π (snd (Pair u v) = v) { refine snd_conv u v };
  have huy : π (Pair u y ∈ s)
    { refine ind_eq (eq_sym hfst) (λ z, Pair z y ∈ s) (∧ₑ₁ hy) };
  have hyv : π (Pair y v ∈ r)
    { refine ind_eq (eq_sym hsnd) (λ z, Pair y z ∈ r) (∧ₑ₂ hy) };
  refine ∃ᵢ y (∧ᵢ huy hyv)
end;

// Helper: Un subset monotonicity
opaque symbol Un_mono (A B C D : τ ι) :
  π (A ⊆ C) → π (B ⊆ D) → π (Un A B ⊆ Un C D) ≔
begin
  assume A B C D hAC hBD x hx;
  have hdisj : π (x ∈ A ∨ x ∈ B) { refine UnE x A B hx };
  refine ∨ₑ hdisj _ _
  { assume hA; refine UnI1 x C D (hAC x hA) }
  { assume hB; refine UnI2 x C D (hBD x hB) }
end;

// Helper: id_rel(A) ⊆ Sigma(A, λ_. A)
opaque symbol id_rel_subset (A : τ ι) :
  π (id_rel A ⊆ Sigma A (λ _, A)) ≔
begin
  assume A p hp;
  // p ∈ RepFun(A, λx. Pair(x,x)), so ∃x∈A. p = Pair(x,x)
  have hbex : π (Bex A (λ x, p = Pair x x))
    { refine ∧ₑ₁ (RepFun_iff p A (λ x, Pair x x)) hp };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hpeq : π (p = Pair x x) { refine ∧ₑ₂ hx };
  rewrite hpeq;
  refine SigmaI x x A (λ _, A) hxA hxA
end;

// Helper: rcomp(r,s) ⊆ Sigma(domain(s), λ_. range(r))
opaque symbol rcomp_subset (r s : τ ι) :
  π (rcomp r s ⊆ Sigma (domain s) (λ _, range r)) ≔
begin
  assume r s p hp;
  refine CollectD1 p (Sigma (domain s) (λ _, range r))
    (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r) hp
end;

// Helper: domain and range monotonicity
opaque symbol domain_mono (r s : τ ι) :
  π (r ⊆ s) → π (domain r ⊆ domain s) ≔
begin
  assume r s hrs a ha;
  have hex : π (`∃ (y : τ ι), Pair a y ∈ r) { refine domainE a r ha };
  refine ∃ₑ hex _;
  assume y hy;
  refine domainI a y s (hrs (Pair a y) hy)
end;

opaque symbol range_mono (r s : τ ι) :
  π (r ⊆ s) → π (range r ⊆ range s) ≔
begin
  assume r s hrs b hb;
  have hex : π (`∃ (x : τ ι), Pair x b ∈ r) { refine rangeE b r hb };
  refine ∃ₑ hex _;
  assume x hx;
  refine rangeI x b s (hrs (Pair x b) hx)
end;

// Helper: Sigma monotonicity (in both components)
opaque symbol Sigma_mono (A C : τ ι) (B D : τ ι → τ ι) :
  π (A ⊆ C) → (Π (x : τ ι), π (x ∈ A) → π (B x ⊆ D x)) →
  π (Sigma A B ⊆ Sigma C D) ≔
begin
  assume A C B D hAC hBD p hp;
  have hbex : π (Bex A (λ x, Bex (B x) (λ y, p = Pair x y)))
    { refine SigmaE p A B hp };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hbex2 : π (Bex (B x) (λ y, p = Pair x y)) { refine ∧ₑ₂ hx };
  refine ∃ₑ hbex2 _;
  assume y hy;
  have hyB : π (y ∈ B x) { refine ∧ₑ₁ hy };
  have hpeq : π (p = Pair x y) { refine ∧ₑ₂ hy };
  rewrite hpeq;
  refine SigmaI x y C D (hAC x hxA) (hBD x hxA y hyB)
end;

// Helper: rcomp monotonicity in second argument
opaque symbol rcomp_mono_right (r s t : τ ι) :
  π (s ⊆ t) → π (rcomp r s ⊆ rcomp r t) ≔
begin
  assume r s t hst p hp;
  have hpSig : π (p ∈ Sigma (domain s) (λ _, range r))
    { refine CollectD1 p (Sigma (domain s) (λ _, range r))
        (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r) hp };
  have hex : π (`∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r)
    { refine CollectD2 p (Sigma (domain s) (λ _, range r))
        (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r) hp };
  refine ∃ₑ hex _;
  assume y hy;
  have hys : π (Pair (fst p) y ∈ s) { refine ∧ₑ₁ hy };
  have hyr : π (Pair y (snd p) ∈ r) { refine ∧ₑ₂ hy };
  have hyt : π (Pair (fst p) y ∈ t) { refine hst (Pair (fst p) y) hys };
  refine CollectI p (Sigma (domain t) (λ _, range r))
    (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ t ∧ Pair y (snd p) ∈ r) _ _
  { // p ∈ Sigma(domain(t), λ_. range(r))
    // p ∈ Sigma(domain(s), λ_. range(r)) and domain(s) ⊆ domain(t)
    refine Sigma_mono (domain s) (domain t) (λ _, range r) (λ _, range r)
      (domain_mono s t hst) (λ x hx, subset_refl (range r)) p hpSig }
  { refine ∃ᵢ y (∧ᵢ hyt hyr) }
end;

// Helper: if s ⊆ Sigma(A, λ_. A), then rcomp(r,s) ⊆ Sigma(A, λ_. A)
// when r ⊆ Sigma(A, λ_. A) too.
// Actually we need: h(s) ⊆ D when s ⊆ D
// h(s) = Un(id_rel(field(r)), rcomp(r,s))
// We need h(D) ⊆ D, i.e., Un(id_rel(field(r)), rcomp(r,D)) ⊆ Sigma(field(r), λ_. field(r))

// Helper: rcomp(r,s) ⊆ Sigma(field(r), λ_. field(r)) when s ⊆ Sigma(field(r), λ_. field(r))
opaque symbol rcomp_field_sub (r s : τ ι) :
  π (s ⊆ Sigma (field r) (λ _, field r)) →
  π (rcomp r s ⊆ Sigma (field r) (λ _, field r)) ≔
begin
  assume r s hsub p hp;
  have hex : π (`∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r)
    { refine rcompE p r s hp };
  refine ∃ₑ hex _;
  assume y hy;
  have hfs : π (Pair (fst p) y ∈ s) { refine ∧ₑ₁ hy };
  have hyr : π (Pair y (snd p) ∈ r) { refine ∧ₑ₂ hy };
  // fst(p) ∈ field(r): Pair(fst(p),y) ∈ s ⊆ Sigma(field(r),...), so fst(p) ∈ field(r)
  // Actually fst(p) is in domain(s) which is ⊆ field(r) via hsub
  // snd(p) ∈ field(r): Pair(y,snd(p)) ∈ r, so snd(p) ∈ field(r) by fieldI2
  // But we need p = Pair(fst(p),snd(p)) and p ∈ Sigma(domain(s), λ_. range(r))
  have hpSig : π (p ∈ Sigma (domain s) (λ _, range r))
    { refine CollectD1 p (Sigma (domain s) (λ _, range r))
        (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r) hp };
  // p ∈ Sigma(domain(s), λ_. range(r)), so ∃a∈domain(s). ∃b∈range(r). p = Pair(a,b)
  have hbex : π (Bex (domain s) (λ a, Bex (range r) (λ b, p = Pair a b)))
    { refine SigmaE p (domain s) (λ _, range r) hpSig };
  refine ∃ₑ hbex _;
  assume a ha;
  have hadom : π (a ∈ domain s) { refine ∧ₑ₁ ha };
  have hbex2 : π (Bex (range r) (λ b, p = Pair a b)) { refine ∧ₑ₂ ha };
  refine ∃ₑ hbex2 _;
  assume b hb;
  have hbran : π (b ∈ range r) { refine ∧ₑ₁ hb };
  have hpeq : π (p = Pair a b) { refine ∧ₑ₂ hb };
  rewrite hpeq;
  // a ∈ domain(s), so ∃w. Pair(a,w) ∈ s ⊆ Sigma(field(r),...), so a ∈ field(r)
  have haex : π (`∃ (w : τ ι), Pair a w ∈ s) { refine domainE a s hadom };
  refine ∃ₑ haex _;
  assume w hw;
  // Pair(a,w) ∈ s ⊆ Sigma(field(r),...), so via SigmaE we get a ∈ field(r)
  have hawS : π (Pair a w ∈ Sigma (field r) (λ _, field r)) { refine hsub (Pair a w) hw };
  have hbexS : π (Bex (field r) (λ x, Bex (field r) (λ y, Pair a w = Pair x y)))
    { refine SigmaE (Pair a w) (field r) (λ _, field r) hawS };
  refine ∃ₑ hbexS _;
  assume x hx;
  have hxf : π (x ∈ field r) { refine ∧ₑ₁ hx };
  have hrest : π (Bex (field r) (λ y, Pair a w = Pair x y)) { refine ∧ₑ₂ hx };
  refine ∃ₑ hrest _;
  assume x2 hx2;
  have hx2f : π (x2 ∈ field r) { refine ∧ₑ₁ hx2 };
  have hpeq2 : π (Pair a w = Pair x x2) { refine ∧ₑ₂ hx2 };
  have hax : π (a = x) { refine Pair_inject1 a w x x2 hpeq2 };
  have hafield : π (a ∈ field r)
    { refine ind_eq hax (λ z, z ∈ field r) hxf };
  // b ∈ range(r), so ∃v. Pair(v,b) ∈ r, so b ∈ field(r) by fieldI2
  have hbex3 : π (`∃ (v : τ ι), Pair v b ∈ r) { refine rangeE b r hbran };
  refine ∃ₑ hbex3 _;
  assume v hv;
  have hbfield : π (b ∈ field r) { refine fieldI2 v b r hv };
  refine SigmaI a b (field r) (λ _, field r) hafield hbfield
end;

// The bnd_mono property for our operator
opaque symbol rtrancl_bnd_mono (r : τ ι) :
  π (bnd_mono (Sigma (field r) (λ _, field r))
              (λ s, Un (id_rel (field r)) (rcomp r s))) ≔
begin
  assume r;
  rewrite bnd_mono_def;
  apply ∧ᵢ
  { // h(D) ⊆ D: Un(id_rel(field(r)), rcomp(r,D)) ⊆ Sigma(field(r), λ_. field(r))
    assume p hp;
    have hdisj : π (p ∈ id_rel (field r) ∨ p ∈ rcomp r (Sigma (field r) (λ _, field r)))
      { refine UnE p (id_rel (field r)) (rcomp r (Sigma (field r) (λ _, field r))) hp };
    refine ∨ₑ hdisj _ _
    { assume hid; refine id_rel_subset (field r) p hid }
    { assume hrc; refine rcomp_field_sub r (Sigma (field r) (λ _, field r))
        (subset_refl (Sigma (field r) (λ _, field r))) p hrc } }
  { // Monotonicity: W ⊆ X → X ⊆ D → h(W) ⊆ h(X)
    assume W X hWX hXD;
    refine Un_mono (id_rel (field r)) (rcomp r W) (id_rel (field r)) (rcomp r X)
      (subset_refl (id_rel (field r))) (rcomp_mono_right r W X hWX) }
end;

// ===========================================================================
// Key theorems
// ===========================================================================

// 1. rtrancl is a subset of field(r) × field(r)
opaque symbol rtrancl_type (r : τ ι) :
  π (rtrancl r ⊆ Sigma (field r) (λ _, field r)) ≔
begin
  assume r;
  refine lfp_subset (Sigma (field r) (λ _, field r))
    (λ s, Un (id_rel (field r)) (rcomp r s))
end;

// 3. Reflexivity: if a ∈ field(r) then Pair(a,a) ∈ r^*
opaque symbol rtrancl_refl (a : τ ι) (r : τ ι) :
  π (a ∈ field r) → π (Pair a a ∈ rtrancl r) ≔
begin
  assume a r haf;
  have hunfold : π (rtrancl r = Un (id_rel (field r)) (rcomp r (rtrancl r)))
    { refine lfp_unfold (Sigma (field r) (λ _, field r))
        (λ s, Un (id_rel (field r)) (rcomp r s)) (rtrancl_bnd_mono r) };
  have hid : π (Pair a a ∈ id_rel (field r))
    { refine id_relI a (field r) haf };
  have hun : π (Pair a a ∈ Un (id_rel (field r)) (rcomp r (rtrancl r)))
    { refine UnI1 (Pair a a) (id_rel (field r)) (rcomp r (rtrancl r)) hid };
  refine ind_eq hunfold (λ z, Pair a a ∈ z) hun
end;

// 2. r ⊆ r^*: the original relation is contained in its rtrancl
opaque symbol r_into_rtrancl (a b : τ ι) (r : τ ι) :
  π (Pair a b ∈ r) → π (Pair a b ∈ rtrancl r) ≔
begin
  assume a b r hab;
  // rtrancl(r) = h(rtrancl(r)) = Un(id_rel(field(r)), rcomp(r, rtrancl(r)))
  have hunfold : π (rtrancl r = Un (id_rel (field r)) (rcomp r (rtrancl r)))
    { refine lfp_unfold (Sigma (field r) (λ _, field r))
        (λ s, Un (id_rel (field r)) (rcomp r s)) (rtrancl_bnd_mono r) };
  // Pair(a,b) ∈ rcomp(r, rtrancl(r)) via y=a:
  // Pair(a,a) ∈ rtrancl(r) and Pair(a,b) ∈ r
  have haa : π (Pair a a ∈ rtrancl r)
    { refine rtrancl_refl a r (fieldI1 a b r hab) };
  have hrc : π (Pair a b ∈ rcomp r (rtrancl r))
    { refine rcompI a a b r (rtrancl r) haa hab };
  have hun : π (Pair a b ∈ Un (id_rel (field r)) (rcomp r (rtrancl r)))
    { refine UnI2 (Pair a b) (id_rel (field r)) (rcomp r (rtrancl r)) hrc };
  refine ind_eq hunfold (λ z, Pair a b ∈ z) hun
end;

// Helper: rtrancl_step — Pair(a,y) ∈ r^* and Pair(y,b) ∈ r implies Pair(a,b) ∈ r^*
// This follows from: Pair(a,b) ∈ rcomp(r, rtrancl(r)) ⊆ h(rtrancl(r)) = rtrancl(r)
opaque symbol rtrancl_step (a y b : τ ι) (r : τ ι) :
  π (Pair a y ∈ rtrancl r) → π (Pair y b ∈ r) → π (Pair a b ∈ rtrancl r) ≔
begin
  assume a y b r hay hyb;
  have hunfold : π (rtrancl r = Un (id_rel (field r)) (rcomp r (rtrancl r)))
    { refine lfp_unfold (Sigma (field r) (λ _, field r))
        (λ s, Un (id_rel (field r)) (rcomp r s)) (rtrancl_bnd_mono r) };
  have hrc : π (Pair a b ∈ rcomp r (rtrancl r))
    { refine rcompI a y b r (rtrancl r) hay hyb };
  have hun : π (Pair a b ∈ Un (id_rel (field r)) (rcomp r (rtrancl r)))
    { refine UnI2 (Pair a b) (id_rel (field r)) (rcomp r (rtrancl r)) hrc };
  refine ind_eq hunfold (λ z, Pair a b ∈ z) hun
end;

// 4. Transitivity of r^*
// Proof by lfp_lowerbound. Fix a. Define
// T = Collect(D, λp. ∀x y. p = Pair(x,y) → Pair(a,x) ∈ r^* → Pair(a,y) ∈ r^*)
// This avoids fst/snd which don't reduce computationally.
opaque symbol trans_rtrancl (r : τ ι) : π (trans (rtrancl r)) ≔
begin
  assume r a b c hab hbc;
  // Define the predicate P(p) ≡ ∀x y. p = Pair(x,y) → Pair(a,x) ∈ r^* → Pair(a,y) ∈ r^*
  // T = Collect(D, P) where D = Sigma(field(r), λ_. field(r))
  // T ⊆ D is clear.
  have hTD : π (Collect (Sigma (field r) (λ _, field r))
      (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)
    ⊆ Sigma (field r) (λ _, field r))
    { assume p hp;
      refine CollectD1 p (Sigma (field r) (λ _, field r))
        (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r) hp };
  // h(T) ⊆ T
  have hhT : π (Un (id_rel (field r)) (rcomp r
      (Collect (Sigma (field r) (λ _, field r))
        (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)))
    ⊆ Collect (Sigma (field r) (λ _, field r))
      (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r))
    { assume p hp;
      have hdisj : π (p ∈ id_rel (field r) ∨ p ∈ rcomp r
          (Collect (Sigma (field r) (λ _, field r))
            (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)))
        { refine UnE p (id_rel (field r)) (rcomp r
            (Collect (Sigma (field r) (λ _, field r))
              (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r))) hp };
      refine ∨ₑ hdisj _ _
      { // Case: p ∈ id_rel(field(r))
        assume hid;
        have hpD : π (p ∈ Sigma (field r) (λ _, field r))
          { refine id_rel_subset (field r) p hid };
        have hpred : π (`∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)
          { assume x y hpeq hax;
            // p ∈ id_rel(field(r)) means p = Pair(w,w) for some w
            have hbex : π (Bex (field r) (λ w, p = Pair w w)) { refine id_relE p (field r) hid };
            refine ∃ₑ hbex _;
            assume w hw;
            have hwf : π (w ∈ field r) { refine ∧ₑ₁ hw };
            have hpw : π (p = Pair w w) { refine ∧ₑ₂ hw };
            // p = Pair(w,w) and p = Pair(x,y), so x = w and y = w
            have hpxy : π (Pair w w = Pair x y)
              { refine ind_eq (eq_sym hpw) (λ z, z = Pair x y) hpeq };
            have hwx : π (w = x) { refine Pair_inject1 w w x y hpxy };
            have hwy : π (w = y) { refine Pair_inject2 w w x y hpxy };
            // x = w = y, so Pair(a,y) = Pair(a,x) ∈ r^*
            have hxy : π (x = y)
              { refine ind_eq (eq_sym hwx) (λ z, z = y) hwy };
            refine ind_eq (eq_sym hxy) (λ z, Pair a z ∈ rtrancl r) hax };
        refine CollectI p (Sigma (field r) (λ _, field r))
          (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)
          hpD hpred }
      { // Case: p ∈ rcomp(r, T)
        assume hrc;
        // p ∈ D via rcomp_field_sub
        have hpD : π (p ∈ Sigma (field r) (λ _, field r))
          { refine rcomp_field_sub r
              (Collect (Sigma (field r) (λ _, field r))
                (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r))
              hTD p hrc };
        // Decompose p via SigmaE to avoid fst/snd
        have hpbex : π (Bex (field r) (λ u, Bex (field r) (λ v, p = Pair u v)))
          { refine SigmaE p (field r) (λ _, field r) hpD };
        refine ∃ₑ hpbex _;
        assume u hu;
        have huf : π (u ∈ field r) { refine ∧ₑ₁ hu };
        have hvbex : π (Bex (field r) (λ v, p = Pair u v)) { refine ∧ₑ₂ hu };
        refine ∃ₑ hvbex _;
        assume v hv;
        have hvf : π (v ∈ field r) { refine ∧ₑ₁ hv };
        have hpuv : π (p = Pair u v) { refine ∧ₑ₂ hv };
        // Transport hrc: Pair(u,v) ∈ rcomp(r,T)
        have hrcuv : π (Pair u v ∈ rcomp r (Collect (Sigma (field r) (λ _, field r))
            (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)))
          { refine ind_eq (eq_sym hpuv) (λ z, z ∈ rcomp r (Collect (Sigma (field r) (λ _, field r))
              (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r))) hrc };
        // Use rcompE_pair to avoid fst/snd
        have hex : π (`∃ (m : τ ι), Pair u m ∈ Collect (Sigma (field r) (λ _, field r))
            (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)
          ∧ Pair m v ∈ r)
          { refine rcompE_pair u v r (Collect (Sigma (field r) (λ _, field r))
              (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)) hrcuv };
        // Build the predicate for p
        have hpred : π (`∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)
          { assume x y hpeq hax;
            refine ∃ₑ hex _;
            assume m hm;
            have humT : π (Pair u m ∈ Collect (Sigma (field r) (λ _, field r))
                (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r))
              { refine ∧ₑ₁ hm };
            have hmv : π (Pair m v ∈ r) { refine ∧ₑ₂ hm };
            // IH from humT: ∀x' y'. Pair(u,m) = Pair(x',y') → Pair(a,x') ∈ r^* → Pair(a,y') ∈ r^*
            have hih : π (`∀ (x1 : τ ι), `∀ (y1 : τ ι),
                Pair u m = Pair x1 y1 ⇒ Pair a x1 ∈ rtrancl r ⇒ Pair a y1 ∈ rtrancl r)
              { refine CollectD2 (Pair u m) (Sigma (field r) (λ _, field r))
                  (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)
                  humT };
            // Apply hih with u, m: Pair(u,m) = Pair(u,m) by refl
            // Gives: Pair(a,u) ∈ r^* → Pair(a,m) ∈ r^*
            // We need Pair(a,u) ∈ r^*:
            // p = Pair(u,v) and p = Pair(x,y), so u = x and v = y
            have hpuv_xy : π (Pair u v = Pair x y)
              { refine ind_eq (eq_sym hpuv) (λ z, z = Pair x y) hpeq };
            have hux : π (u = x) { refine Pair_inject1 u v x y hpuv_xy };
            have hvy : π (v = y) { refine Pair_inject2 u v x y hpuv_xy };
            // Pair(a,u) ∈ r^* since u = x and hax: Pair(a,x) ∈ r^*
            have hau : π (Pair a u ∈ rtrancl r)
              { refine ind_eq hux (λ z, Pair a z ∈ rtrancl r) hax };
            // Pair(a,m) ∈ r^* by IH
            have ham : π (Pair a m ∈ rtrancl r)
              { refine hih u m (eq_refl (Pair u m)) hau };
            // Pair(m,v) ∈ r, so Pair(a,v) ∈ r^* by rtrancl_step
            have hav : π (Pair a v ∈ rtrancl r)
              { refine rtrancl_step a m v r ham hmv };
            // v = y, so Pair(a,y) ∈ r^*
            refine ind_eq (eq_sym hvy) (λ z, Pair a z ∈ rtrancl r) hav };
        refine CollectI p (Sigma (field r) (λ _, field r))
          (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)
          hpD hpred } };
  // Now use lfp_lowerbound to get rtrancl(r) ⊆ T
  have hlb : π (rtrancl r ⊆ Collect (Sigma (field r) (λ _, field r))
      (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r))
    { refine lfp_lowerbound (Sigma (field r) (λ _, field r))
        (Collect (Sigma (field r) (λ _, field r))
          (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r))
        (λ s, Un (id_rel (field r)) (rcomp r s)) hhT hTD };
  // Pair(b,c) ∈ rtrancl(r) ⊆ T
  have hbcT : π (Pair b c ∈ Collect (Sigma (field r) (λ _, field r))
      (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r))
    { refine hlb (Pair b c) hbc };
  // Extract: Pair(b,c) = Pair(b,c) → Pair(a,b) ∈ r^* → Pair(a,c) ∈ r^*
  have hpred : π (`∀ (x : τ ι), `∀ (y : τ ι), Pair b c = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r)
    { refine CollectD2 (Pair b c) (Sigma (field r) (λ _, field r))
        (λ p, `∀ (x : τ ι), `∀ (y : τ ι), p = Pair x y ⇒ Pair a x ∈ rtrancl r ⇒ Pair a y ∈ rtrancl r) hbcT };
  refine hpred b c (eq_refl (Pair b c)) hab
end;

// 5. r ⊆ r^+
// trancl(r) = rcomp(r, rtrancl(r)) = {Pair(x,z) | ∃y. Pair(x,y) ∈ rtrancl(r) ∧ Pair(y,z) ∈ r}
// For Pair(a,b) ∈ r: take y=a, need Pair(a,a) ∈ rtrancl(r) and Pair(a,b) ∈ r
opaque symbol r_into_trancl (a b : τ ι) (r : τ ι) :
  π (Pair a b ∈ r) → π (Pair a b ∈ trancl r) ≔
begin
  assume a b r hab;
  // trancl(r) = rcomp(r, rtrancl(r))
  // Need: Pair(a,b) ∈ rcomp(r, rtrancl(r))
  // i.e., ∃y. Pair(a,y) ∈ rtrancl(r) ∧ Pair(y,b) ∈ r
  // Take y = a: Pair(a,a) ∈ rtrancl(r) [by rtrancl_refl] ∧ Pair(a,b) ∈ r ✓
  have haa : π (Pair a a ∈ rtrancl r)
    { refine rtrancl_refl a r (fieldI1 a b r hab) };
  refine rcompI a a b r (rtrancl r) haa hab
end;

// 6. Transitivity of r^+
// trans(trancl(r)): Pair(x,y) ∈ trancl(r) → Pair(y,z) ∈ trancl(r) → Pair(x,z) ∈ trancl(r)
// trancl(r) = rcomp(r, rtrancl(r))
// Pair(x,y) ∈ trancl(r): ∃u. Pair(x,u) ∈ rtrancl(r) ∧ Pair(u,y) ∈ r
// Pair(y,z) ∈ trancl(r): ∃v. Pair(y,v) ∈ rtrancl(r) ∧ Pair(v,z) ∈ r
// Need Pair(x,z) ∈ trancl(r), i.e., ∃w. Pair(x,w) ∈ rtrancl(r) ∧ Pair(w,z) ∈ r
// Take w = v. Need Pair(x,v) ∈ rtrancl(r) and Pair(v,z) ∈ r.
// Pair(v,z) ∈ r ✓
// Pair(x,v) ∈ rtrancl(r): by transitivity of rtrancl:
//   Pair(x,u) ∈ rtrancl(r), Pair(u,y) ∈ r → Pair(u,y) ∈ rtrancl(r),
//   Pair(y,v) ∈ rtrancl(r)
//   So Pair(x,y) ∈ rtrancl(r) (via trans) then Pair(x,v) ∈ rtrancl(r) (via trans)
opaque symbol trans_trancl (r : τ ι) : π (trans (trancl r)) ≔
begin
  assume r x y z hxy hyz;
  // hxy : Pair(x,y) ∈ trancl(r) = rcomp(r, rtrancl(r))
  // hyz : Pair(y,z) ∈ trancl(r) = rcomp(r, rtrancl(r))
  // Decompose: ∃u. Pair(x,u) ∈ rtrancl(r) ∧ Pair(u,y) ∈ r
  have hxu : π (`∃ (u : τ ι), Pair x u ∈ rtrancl r ∧ Pair u y ∈ r)
    { refine rcompE_pair x y r (rtrancl r) hxy };
  // ∃v. Pair(y,v) ∈ rtrancl(r) ∧ Pair(v,z) ∈ r
  have hyv : π (`∃ (v : τ ι), Pair y v ∈ rtrancl r ∧ Pair v z ∈ r)
    { refine rcompE_pair y z r (rtrancl r) hyz };
  refine ∃ₑ hxu _;
  assume u hu;
  have hxu_rt : π (Pair x u ∈ rtrancl r) { refine ∧ₑ₁ hu };
  have huy_r : π (Pair u y ∈ r) { refine ∧ₑ₂ hu };
  refine ∃ₑ hyv _;
  assume v hv;
  have hyv_rt : π (Pair y v ∈ rtrancl r) { refine ∧ₑ₁ hv };
  have hvz_r : π (Pair v z ∈ r) { refine ∧ₑ₂ hv };
  // Pair(x,y) ∈ rtrancl(r) by rtrancl_step(x,u,y): Pair(x,u) ∈ r^* ∧ Pair(u,y) ∈ r
  have hxy_rt : π (Pair x y ∈ rtrancl r)
    { refine rtrancl_step x u y r hxu_rt huy_r };
  // Pair(x,v) ∈ rtrancl(r) by trans_rtrancl: Pair(x,y) ∈ r^* ∧ Pair(y,v) ∈ r^*
  have hxv_rt : π (Pair x v ∈ rtrancl r)
    { refine trans_rtrancl r x y v hxy_rt hyv_rt };
  // Pair(x,z) ∈ trancl(r) = rcomp(r,rtrancl(r)) via witness v
  refine rcompI x v z r (rtrancl r) hxv_rt hvz_r
end;

// 7. r^+ ⊆ r^*
// trancl(r) = rcomp(r, rtrancl(r))
// Pair(a,b) ∈ rcomp(r, rtrancl(r)): ∃y. Pair(a,y) ∈ rtrancl(r) ∧ Pair(y,b) ∈ r
// Pair(y,b) ∈ r → Pair(y,b) ∈ rtrancl(r) (by r_into_rtrancl)
// Pair(a,y) ∈ rtrancl(r) and Pair(y,b) ∈ rtrancl(r) → Pair(a,b) ∈ rtrancl(r) (by trans_rtrancl)
opaque symbol trancl_into_rtrancl (a b : τ ι) (r : τ ι) :
  π (Pair a b ∈ trancl r) → π (Pair a b ∈ rtrancl r) ≔
begin
  assume a b r hab;
  // hab : Pair(a,b) ∈ rcomp(r, rtrancl(r))
  have hex : π (`∃ (y : τ ι), Pair a y ∈ rtrancl r ∧ Pair y b ∈ r)
    { refine rcompE_pair a b r (rtrancl r) hab };
  refine ∃ₑ hex _;
  assume y hy;
  have hay : π (Pair a y ∈ rtrancl r) { refine ∧ₑ₁ hy };
  have hyb : π (Pair y b ∈ r) { refine ∧ₑ₂ hy };
  // Pair(a,b) ∈ rtrancl(r) by rtrancl_step
  refine rtrancl_step a y b r hay hyb
end;
