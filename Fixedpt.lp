// Fixedpt: Knaster-Tarski fixed point theory
//
// Isabelle source: Fixedpt.thy
// Defines: bnd_mono, lfp, gfp
// Proves: lfp_unfold, gfp_unfold, induct (lfp induction), coinduct (gfp
// coinduction), lfp_greatest, bnd_monoI

require open ZF.ZF_Base ZF.upair ZF.equalities;

// ===========================================================================
// Bounded monotone operators
// ===========================================================================

// bnd_mono(D, h) ≡ h(D) ⊆ D ∧ ∀W X. W ⊆ X → X ⊆ D → h(W) ⊆ h(X)
symbol bnd_mono (D : τ ι) (h : τ ι → τ ι) : Prop ≔
  h D ⊆ D ∧ (`∀ (W : τ ι), `∀ (X : τ ι), W ⊆ X ⇒ X ⊆ D ⇒ h W ⊆ h X);

// ===========================================================================
// Least fixed point: lfp(D,h) = ⋂{X ∈ Pow(D) | h(X) ⊆ X}
// ===========================================================================

symbol lfp (D : τ ι) (h : τ ι → τ ι) : τ ι ≔
  Inter (Collect (Pow D) (λ X, h X ⊆ X));

// ===========================================================================
// Greatest fixed point: gfp(D,h) = ⋃{X ∈ Pow(D) | X ⊆ h(X)}
// ===========================================================================

symbol gfp (D : τ ι) (h : τ ι → τ ι) : τ ι ≔
  Union (Collect (Pow D) (λ X, X ⊆ h X));

// ===========================================================================
// lfp is contained in D
// ===========================================================================

// lfp(D,h) ⊆ D. Faithful to Isabelle lfp_subset: NO bnd_mono premise — unfolding
// Inter/Union shows any x ∈ lfp lies in some X ∈ Pow(D) (so X ⊆ D), hence x ∈ D.
opaque symbol lfp_subset (D : τ ι) (h : τ ι → τ ι) :
  π (lfp D h ⊆ D) ≔
begin
  assume D h x hx;
  // lfp D h = Inter (Coll); x ∈ Inter (Coll) → x ∈ Union (Coll), where
  // Coll = Collect (Pow D) (λ X, h X ⊆ X)   and   Inter A = Collect (Union A) (…)
  have hxU : π (x ∈ Union (Collect (Pow D) (λ X, h X ⊆ X)))
    { refine CollectD1 x (Union (Collect (Pow D) (λ X, h X ⊆ X)))
        (λ z, Ball (Collect (Pow D) (λ X, h X ⊆ X)) (λ Y, z ∈ Y)) hx };
  have hbex : π (Bex (Collect (Pow D) (λ X, h X ⊆ X)) (λ Y, x ∈ Y))
    { refine UnionE x (Collect (Pow D) (λ X, h X ⊆ X)) hxU };
  refine ∃ₑ hbex _;
  assume Y hY;
  have hYin : π (Y ∈ Collect (Pow D) (λ X, h X ⊆ X)) { refine ∧ₑ₁ hY };
  have hxY : π (x ∈ Y) { refine ∧ₑ₂ hY };
  have hYD : π (Y ⊆ D) { refine PowD Y D (CollectD1 Y (Pow D) (λ X, h X ⊆ X) hYin) };
  refine hYD x hxY
end;

// ===========================================================================
// lfp lower bound: if h(A) ⊆ A and A ⊆ D then lfp(D,h) ⊆ A
// ===========================================================================

opaque symbol lfp_lowerbound (D A : τ ι) (h : τ ι → τ ι) :
  π (h A ⊆ A) → π (A ⊆ D) → π (lfp D h ⊆ A) ≔
begin
  assume D A h hhA hAD x hx;
  have hball : π (Ball (Collect (Pow D) (λ X, h X ⊆ X)) (λ Y, x ∈ Y))
    { refine CollectD2 x (Union (Collect (Pow D) (λ X, h X ⊆ X)))
        (λ z, Ball (Collect (Pow D) (λ X, h X ⊆ X)) (λ Y, z ∈ Y)) hx };
  have hAin : π (A ∈ Collect (Pow D) (λ X, h X ⊆ X))
    { refine CollectI A (Pow D) (λ X, h X ⊆ X) (PowI A D hAD) hhA };
  refine hball A hAin
end;

// ===========================================================================
// lfp_unfold: bnd_mono(D,h) → lfp(D,h) = h(lfp(D,h))
// ===========================================================================

// This is the core Knaster-Tarski theorem
opaque symbol lfp_unfold (D : τ ι) (h : τ ι → τ ι) :
  π (bnd_mono D h) → π (lfp D h = h (lfp D h)) ≔
begin
  assume D h hm;
  // Extract parts of bnd_mono
  have hDpre : π (h D ⊆ D) { refine ∧ₑ₁ hm };
  have hmono : π (`∀ (W : τ ι), `∀ (X : τ ι), W ⊆ X ⇒ X ⊆ D ⇒ h W ⊆ h X)
    { refine ∧ₑ₂ hm };
  // Step 1: h(lfp) ⊆ lfp
  // For each x ∈ h(lfp), x must be in every X with h(X)⊆X and X⊆D
  have hh_sub_lfp : π (h (lfp D h) ⊆ lfp D h)
    { assume x hx;
      // x ∈ Inter(Collect(Pow D, λ X. h X ⊆ X)) iff x ∈ every such X
      // Need: x ∈ lfp D h = Inter(Collect(...))
      // Ball form: every Y in Collect(Pow D, λ X. h X ⊆ X) contains x
      refine CollectI x (Union (Collect (Pow D) (λ X, h X ⊆ X)))
              (λ z, Ball (Collect (Pow D) (λ X, h X ⊆ X)) (λ Y, z ∈ Y)) _ _
      { // x ∈ Union(Collect(...))
        // D is in Collect(Pow D, λ X. h X ⊆ X) and x ∈ h(lfp) ⊆ h(D) ⊆ D
        // lfp ⊆ D
        have hlfp_D : π (lfp D h ⊆ D) { refine lfp_subset D h};
        // h(lfp) ⊆ h(D) by mono (lfp ⊆ D, D ⊆ D)
        have hhlfp_hD : π (h (lfp D h) ⊆ h D)
          { refine hmono (lfp D h) D hlfp_D (subset_refl D) };
        // x ∈ h(D) ⊆ D
        have hxD : π (x ∈ D) { refine hDpre x (hhlfp_hD x hx) };
        // D is in Collect(Pow D, λ X. h X ⊆ X)
        have hDcoll : π (D ∈ Collect (Pow D) (λ X, h X ⊆ X))
          { refine CollectI D (Pow D) (λ X, h X ⊆ X)
              (PowI D D (subset_refl D)) hDpre };
        refine UnionI x D (Collect (Pow D) (λ X, h X ⊆ X)) hxD hDcoll }
      { // Ball: for all Y in Collect(Pow D, λ X. h X ⊆ X), x ∈ Y
        assume Y hYcoll;
        // Y ⊆ D and h(Y) ⊆ Y
        have hYD : π (Y ⊆ D)
          { refine PowD Y D (CollectD1 Y (Pow D) (λ X, h X ⊆ X) hYcoll) };
        have hhYY : π (h Y ⊆ Y)
          { refine CollectD2 Y (Pow D) (λ X, h X ⊆ X) hYcoll };
        // lfp ⊆ Y (Y is a pre-fixed point)
        have hlfp_Y : π (lfp D h ⊆ Y) { refine lfp_lowerbound D Y h hhYY hYD };
        // lfp ⊆ D
        have hlfp_D : π (lfp D h ⊆ D) { refine lfp_subset D h};
        // h(lfp) ⊆ h(Y) by mono
        have hhlfp_hY : π (h (lfp D h) ⊆ h Y)
          { refine hmono (lfp D h) Y hlfp_Y hYD };
        // x ∈ h(lfp) ⊆ h(Y) ⊆ Y
        refine hhYY x (hhlfp_hY x hx) } };
  // Step 2: lfp ⊆ h(lfp)
  // h(lfp) is itself a pre-fixed point (h(h(lfp)) ⊆ h(lfp)) contained in D
  have hlfp_D : π (lfp D h ⊆ D) { refine lfp_subset D h};
  // h(lfp) ⊆ D (since h(lfp) ⊆ lfp ⊆ D)
  have hhlfp_D : π (h (lfp D h) ⊆ D)
    { refine subset_trans (h (lfp D h)) (lfp D h) D hh_sub_lfp hlfp_D };
  // h(h(lfp)) ⊆ h(lfp) by mono (h(lfp) ⊆ lfp ⊆ D, h(lfp) ⊆ D)
  have hh2_sub : π (h (h (lfp D h)) ⊆ h (lfp D h))
    { refine hmono (h (lfp D h)) (lfp D h) hh_sub_lfp hlfp_D };
  // By lfp_lowerbound: lfp ⊆ h(lfp)
  have hlfp_sub_hlfp : π (lfp D h ⊆ h (lfp D h))
    { refine lfp_lowerbound D (h (lfp D h)) h hh2_sub hhlfp_D };
  // Conclude lfp = h(lfp)
  refine subset_antisym (lfp D h) (h (lfp D h)) hlfp_sub_hlfp hh_sub_lfp
end;

// ===========================================================================
// gfp_subset: gfp(D,h) ⊆ D
// ===========================================================================

// gfp(D,h) ⊆ D. Faithful to Isabelle gfp_subset: no bnd_mono premise.
opaque symbol gfp_subset (D : τ ι) (h : τ ι → τ ι) :
  π (gfp D h ⊆ D) ≔
begin
  assume D h x hx;
  // x ∈ gfp D h = Union (Collect (Pow D) (λ X, X ⊆ h X))
  have hbex : π (Bex (Collect (Pow D) (λ X, X ⊆ h X)) (λ Y, x ∈ Y))
    { refine UnionE x (Collect (Pow D) (λ X, X ⊆ h X)) hx };
  refine ∃ₑ hbex _;
  assume Y hY;
  have hYin : π (Y ∈ Collect (Pow D) (λ X, X ⊆ h X)) { refine ∧ₑ₁ hY };
  have hxY : π (x ∈ Y) { refine ∧ₑ₂ hY };
  have hYD : π (Y ⊆ D) { refine PowD Y D (CollectD1 Y (Pow D) (λ X, X ⊆ h X) hYin) };
  refine hYD x hxY
end;

// ===========================================================================
// gfp upper bound: if A ⊆ h(A) and A ⊆ D then A ⊆ gfp(D,h)
// ===========================================================================

opaque symbol gfp_upperbound (D A : τ ι) (h : τ ι → τ ι) :
  π (A ⊆ h A) → π (A ⊆ D) → π (A ⊆ gfp D h) ≔
begin
  assume D A h hAhA hAD x hx;
  // Need: x ∈ Union(Collect(Pow D, λ X. X ⊆ h X))
  // A ∈ Collect(Pow D, λ X. X ⊆ h X) since A ∈ Pow D and A ⊆ h A
  have hAin : π (A ∈ Collect (Pow D) (λ X, X ⊆ h X))
    { refine CollectI A (Pow D) (λ X, X ⊆ h X) (PowI A D hAD) hAhA };
  refine UnionI x A (Collect (Pow D) (λ X, X ⊆ h X)) hx hAin
end;

// ===========================================================================
// gfp_unfold: bnd_mono(D,h) → gfp(D,h) = h(gfp(D,h))
// ===========================================================================

opaque symbol gfp_unfold (D : τ ι) (h : τ ι → τ ι) :
  π (bnd_mono D h) → π (gfp D h = h (gfp D h)) ≔
begin
  assume D h hm;
  // Extract parts of bnd_mono
  have hDpre : π (h D ⊆ D) { refine ∧ₑ₁ hm };
  have hmono : π (`∀ (W : τ ι), `∀ (X : τ ι), W ⊆ X ⇒ X ⊆ D ⇒ h W ⊆ h X)
    { refine ∧ₑ₂ hm };
  // gfp ⊆ D
  have hgfp_D : π (gfp D h ⊆ D) { refine gfp_subset D h};
  // Step 1: gfp ⊆ h(gfp)
  // For each x ∈ gfp, find Y with Y ⊆ h(Y), Y ⊆ D, x ∈ Y
  // Then Y ⊆ gfp and h(Y) ⊆ h(gfp), so x ∈ h(gfp)
  have hgfp_sub_hgfp : π (gfp D h ⊆ h (gfp D h))
    { assume x hx;
      // x ∈ gfp = Union(Collect(Pow D, λ X. X ⊆ h X))
      have hbex : π (Bex (Collect (Pow D) (λ X, X ⊆ h X)) (λ Y, x ∈ Y))
        { refine UnionE x (Collect (Pow D) (λ X, X ⊆ h X)) hx };
      refine ∃ₑ hbex _;
      assume Y hY;
      have hYcoll : π (Y ∈ Collect (Pow D) (λ X, X ⊆ h X)) { refine ∧ₑ₁ hY };
      have hxY : π (x ∈ Y) { refine ∧ₑ₂ hY };
      // Y ⊆ D
      have hYD : π (Y ⊆ D)
        { refine PowD Y D (CollectD1 Y (Pow D) (λ X, X ⊆ h X) hYcoll) };
      // Y ⊆ h(Y)
      have hY_hY : π (Y ⊆ h Y)
        { refine CollectD2 Y (Pow D) (λ X, X ⊆ h X) hYcoll };
      // Y ⊆ gfp (Y is a post-fixed point in D)
      have hY_gfp : π (Y ⊆ gfp D h)
        { refine gfp_upperbound D Y h hY_hY hYD };
      // h(Y) ⊆ h(gfp) by mono (Y ⊆ gfp, gfp ⊆ D)
      have hhY_hgfp : π (h Y ⊆ h (gfp D h))
        { refine hmono Y (gfp D h) hY_gfp hgfp_D };
      // x ∈ Y ⊆ h(Y) ⊆ h(gfp)
      refine hhY_hgfp x (hY_hY x hxY) };
  // Step 2: h(gfp) ⊆ gfp
  // h(gfp) ⊆ h(h(gfp)) by mono (gfp ⊆ h(gfp), h(gfp) ⊆ D)
  // h(gfp) ⊆ D: h(D) ⊆ D by bnd_mono, gfp ⊆ D, so h(gfp) ⊆ h(D) ⊆ D
  have hhgfp_D : π (h (gfp D h) ⊆ D)
    { have hhgfp_hD : π (h (gfp D h) ⊆ h D)
        { refine hmono (gfp D h) D hgfp_D (subset_refl D) };
      refine subset_trans (h (gfp D h)) (h D) D hhgfp_hD hDpre };
  have hh2_gfp : π (h (gfp D h) ⊆ h (h (gfp D h)))
    { refine hmono (gfp D h) (h (gfp D h)) hgfp_sub_hgfp hhgfp_D };
  // By gfp_upperbound: h(gfp) ⊆ gfp
  have hhgfp_gfp : π (h (gfp D h) ⊆ gfp D h)
    { refine gfp_upperbound D (h (gfp D h)) h hh2_gfp hhgfp_D };
  // Conclude gfp = h(gfp)
  refine subset_antisym (gfp D h) (h (gfp D h)) hgfp_sub_hgfp hhgfp_gfp
end;

// ===========================================================================
// bnd_monoI  (Fixedpt.thy)
// ===========================================================================

opaque symbol bnd_monoI (D : τ ι) (h : τ ι → τ ι) :
  π (h D ⊆ D) →
  (Π (W X : τ ι), π (W ⊆ X) → π (X ⊆ D) → π (h W ⊆ h X)) →
  π (bnd_mono D h) ≔
begin
  assume D h h1 h2;
  refine ∧ᵢ h1 _;
  assume W X hWX hXD;
  refine h2 W X hWX hXD
end;

// ===========================================================================
// lfp_greatest  (Fixedpt.thy): lfp is above any set below all pre-fixed points
// ===========================================================================

opaque symbol lfp_greatest (D A : τ ι) (h : τ ι → τ ι) :
  π (bnd_mono D h) →
  (Π (X : τ ι), π (h X ⊆ X) → π (X ⊆ D) → π (A ⊆ X)) →
  π (A ⊆ lfp D h) ≔
begin
  assume D A h hm hstep;
  have hunf : π (lfp D h = h (lfp D h)) { refine lfp_unfold D h hm };
  refine hstep (lfp D h) _ (lfp_subset D h);
  assume x hx;
  refine ind_eq hunf (λ w, x ∈ w) hx
end;

// ===========================================================================
// induct  (Fixedpt.thy): the induction principle for lfp
//   b ∈ lfp(D,h) → bnd_mono(D,h) →
//   (∀x. x ∈ h(Collect(lfp(D,h),P)) → P(x)) → P(b)
// ===========================================================================

opaque symbol induct (D b : τ ι) (h : τ ι → τ ι) (P : τ ι → Prop) :
  π (b ∈ lfp D h) →
  π (bnd_mono D h) →
  (Π (x : τ ι), π (x ∈ h (Collect (lfp D h) P)) → π (P x)) →
  π (P b) ≔
begin
  assume D b h P hb hm hstep;
  have hmono : π (`∀ (W : τ ι), `∀ (X : τ ι), W ⊆ X ⇒ X ⊆ D ⇒ h W ⊆ h X)
    { refine ∧ₑ₂ hm };
  have hunf : π (lfp D h = h (lfp D h)) { refine lfp_unfold D h hm };
  have hCsub : π (Collect (lfp D h) P ⊆ lfp D h)
    { refine Collect_subset (lfp D h) P };
  have hCD : π (Collect (lfp D h) P ⊆ D)
    { refine subset_trans (Collect (lfp D h) P) (lfp D h) D hCsub (lfp_subset D h) };
  // h(Collect(lfp,P)) ⊆ Collect(lfp,P): membership in lfp via monotonicity +
  // unfold; the P-part is exactly the induction step.
  have hpre : π (h (Collect (lfp D h) P) ⊆ Collect (lfp D h) P)
    { assume x hx;
      have hhsub : π (h (Collect (lfp D h) P) ⊆ h (lfp D h))
        { refine hmono (Collect (lfp D h) P) (lfp D h) hCsub (lfp_subset D h) };
      have hxlfp : π (x ∈ lfp D h)
        { refine ind_eq hunf (λ w, x ∈ w) (hhsub x hx) };
      refine CollectI x (lfp D h) P hxlfp (hstep x hx) };
  have hlow : π (lfp D h ⊆ Collect (lfp D h) P)
    { refine lfp_lowerbound D (Collect (lfp D h) P) h hpre hCD };
  refine CollectD2 b (lfp D h) P (hlow b hb)
end;

// ===========================================================================
// coinduct  (Fixedpt.thy): the coinduction principle for gfp
//   bnd_mono(D,h) → a ∈ X → X ⊆ h(X ∪ gfp(D,h)) → X ⊆ D → a ∈ gfp(D,h)
// ===========================================================================

opaque symbol coinduct (D X a : τ ι) (h : τ ι → τ ι) :
  π (bnd_mono D h) →
  π (a ∈ X) →
  π (X ⊆ h (Un X (gfp D h))) →
  π (X ⊆ D) →
  π (a ∈ gfp D h) ≔
begin
  assume D X a h hm ha hXh hXD;
  have hmono : π (`∀ (W : τ ι), `∀ (Y : τ ι), W ⊆ Y ⇒ Y ⊆ D ⇒ h W ⊆ h Y)
    { refine ∧ₑ₂ hm };
  have hunf : π (gfp D h = h (gfp D h)) { refine gfp_unfold D h hm };
  have hUD : π (Un X (gfp D h) ⊆ D)
    { refine Un_least X (gfp D h) D hXD (gfp_subset D h) };
  // X ∪ gfp is a post-fixed point: X ⊆ h(X ∪ gfp) is given, and
  // gfp = h(gfp) ⊆ h(X ∪ gfp) by monotonicity.
  have hUsub : π (Un X (gfp D h) ⊆ h (Un X (gfp D h)))
    { refine Un_least X (gfp D h) (h (Un X (gfp D h))) hXh _;
      assume z hz;
      have hz2 : π (z ∈ h (gfp D h))
        { refine ind_eq (eq_sym hunf) (λ w, z ∈ w) hz };
      refine hmono (gfp D h) (Un X (gfp D h)) (Un_upper2 X (gfp D h)) hUD z hz2 };
  have hUgfp : π (Un X (gfp D h) ⊆ gfp D h)
    { refine gfp_upperbound D (Un X (gfp D h)) h hUsub hUD };
  refine hUgfp a (Un_upper1 X (gfp D h) a ha)
end;
