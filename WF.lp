// WF: Well-founded relations and well-founded induction
//
// Isabelle source: WF.thy
// Defines: wf (well-foundedness predicate)
// Proves: wf_induct, wf_trancl

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt
             Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.Fixedpt ZF.Trancl ZF.func;

// ===========================================================================
// Well-foundedness
// ===========================================================================

// wf(A, r): r is well-founded on A
// Every nonempty subset of A has an r-minimal element
symbol wf (A r : τ ι) : Prop ≔
  `∀ (Z : τ ι), Z ⊆ A ⇒ Z ≠ empty ⇒
    Bex Z (λ x, Ball Z (λ y, Pair y x ∉ r));

// ===========================================================================
// Well-founded induction
// ===========================================================================

// wf_induct: if r is well-founded on A, and P holds for a whenever
// P holds for all r-predecessors of a, then P holds for all of A
opaque symbol wf_induct (A r : τ ι) (P : τ ι → Prop) :
  π (wf A r) →
  π (Ball A (λ x, Ball A (λ y, Pair y x ∈ r ⇒ P y) ⇒ P x)) →
  π (Ball A (λ x, P x)) ≔
begin
  assume A r P hwf hind;
  // By double negation elimination: suffices to show ¬¬(Ball A (λ x, P x))
  refine ¬¬ₑ _ _;
  assume hnot;
  // hnot : ¬ Ball A (λ x, P x), i.e. ¬(∀x∈A. P x)
  // We need to derive ⊥. Consider bad = {x ∈ A | ¬P(x)}.
  // First show bad is nonempty.
  have hbad_nonempty : π (Collect A (λ x, ¬ P x) ≠ empty) {
    assume heq;
    // If bad = empty then ∀x∈A. P x
    apply hnot;
    assume x hxA;
    // x ∉ bad (since bad = empty)
    // So ¬¬P(x), hence P(x)
    apply (¬¬ₑ (P x) _);
    assume hnPx;
    have hxbad : π (x ∈ Collect A (λ x, ¬ P x)) {
      refine CollectI x A (λ x, ¬ P x) hxA hnPx
    };
    refine emptyE x _;
    rewrite left heq;
    apply hxbad
  };
  // bad ⊆ A
  have hbad_sub : π (Collect A (λ x, ¬ P x) ⊆ A) {
    assume x hx;
    refine CollectD1 x A (λ x, ¬ P x) hx
  };
  // By wf, bad has an r-minimal element x₀
  have hmin : π (Bex (Collect A (λ x, ¬ P x)) (λ x, Ball (Collect A (λ x, ¬ P x)) (λ y, Pair y x ∉ r))) {
    refine hwf (Collect A (λ x, ¬ P x)) hbad_sub hbad_nonempty
  };
  // Extract x₀
  refine ∃ₑ hmin _;
  assume x0 hx0;
  have hx0bad : π (x0 ∈ Collect A (λ x, ¬ P x)) { refine ∧ₑ₁ hx0 };
  have hx0min : π (Ball (Collect A (λ x, ¬ P x)) (λ y, Pair y x0 ∉ r)) { refine ∧ₑ₂ hx0 };
  have hx0A : π (x0 ∈ A) { refine CollectD1 x0 A (λ x, ¬ P x) hx0bad };
  have hnPx0 : π (¬ P x0) { refine CollectD2 x0 A (λ x, ¬ P x) hx0bad };
  // By hind, to get P(x0) we need: ∀y∈A. Pair(y,x0)∈r → P(y)
  // Show all r-predecessors of x0 in A satisfy P
  have hpred : π (Ball A (λ y, Pair y x0 ∈ r ⇒ P y)) {
    assume y hyA hyr;
    // y is an r-predecessor of x0. Show P(y) by contradiction.
    apply (¬¬ₑ (P y) _);
    assume hnPy;
    // y ∈ bad
    have hybad : π (y ∈ Collect A (λ x, ¬ P x)) {
      refine CollectI y A (λ x, ¬ P x) hyA hnPy
    };
    // But x0 is r-minimal in bad: Pair(y, x0) ∉ r
    have hcontra : π (Pair y x0 ∉ r) { refine hx0min y hybad };
    refine hcontra hyr
  };
  // Apply inductive hypothesis to get P(x0)
  have hPx0 : π (P x0) { refine hind x0 hx0A hpred };
  // Contradiction with ¬P(x0)
  refine hnPx0 hPx0
end;

// ===========================================================================
// Well-foundedness of ∈ (from foundation axiom)
// ===========================================================================

// ∈ is well-founded (every nonempty set has an ∈-minimal element)
// This follows directly from the foundation axiom
opaque symbol wf_mem (A : τ ι) :
  π (wf A (Collect (Sigma A (λ _, A)) (λ p, fst p ∈ snd p))) ≔
begin
  assume A Z hZA hZne;
  // Apply foundation to Z
  have hfound : π (Z = empty ∨ Bex Z (λ x, Ball x (λ y, y ∉ Z)))
    { refine foundation Z };
  refine ∨ₑ hfound _ _
  { // Case Z = empty: contradiction with Z ≠ empty
    assume heq;
    refine ⊥ₑ (hZne heq) }
  { // Case: ∃x∈Z. ∀y∈x. y ∉ Z
    assume hbex;
    refine ∃ₑ hbex _;
    assume x hx;
    have hxZ : π (x ∈ Z) { refine ∧ₑ₁ hx };
    have hxmin : π (Ball x (λ y, y ∉ Z)) { refine ∧ₑ₂ hx };
    // x is our witness: x ∈ Z and ∀y∈Z. Pair(y,x) ∉ Memrel
    refine ∃ᵢ x _;
    apply ∧ᵢ hxZ _;
    // Show: ∀y∈Z. Pair(y,x) ∉ Memrel
    assume y hyZ hmem;
    // hmem : Pair y x ∈ Collect (Sigma A (λ _, A)) (λ p, fst p ∈ snd p)
    // Extract: fst(Pair(y,x)) ∈ snd(Pair(y,x))
    have hfstsnd : π (fst (Pair y x) ∈ snd (Pair y x))
      { refine CollectD2 (Pair y x) (Sigma A (λ _, A)) (λ p, fst p ∈ snd p) hmem };
    // fst(Pair(y,x)) = y
    have hfst : π (fst (Pair y x) = y) { refine fst_conv y x };
    // snd(Pair(y,x)) = x
    have hsnd : π (snd (Pair y x) = x) { refine snd_conv y x };
    // Transport: y ∈ x
    have hyx : π (y ∈ x) {
      // From fst(Pair(y,x)) ∈ snd(Pair(y,x)), transport to y ∈ x
      // First transport fst to y: ind_eq (eq_sym hfst) (λ z, z ∈ snd(Pair y x))
      have h1 : π (y ∈ snd (Pair y x))
        { refine ind_eq (eq_sym hfst) (λ z, z ∈ snd (Pair y x)) hfstsnd };
      // Then transport snd to x: ind_eq (eq_sym hsnd) (λ z, y ∈ z)
      refine ind_eq (eq_sym hsnd) (λ z, y ∈ z) h1
    };
    // Foundation: y ∈ x → y ∉ Z. But y ∈ Z — contradiction.
    refine hxmin y hyx hyZ }
end;

// ===========================================================================
// Well-foundedness is preserved by transitive closure
// ===========================================================================

// Helper: decompose rtrancl membership into id_rel ∨ trancl
// rtrancl(r) = Un(id_rel(field(r)), rcomp(r, rtrancl(r))) = Un(id_rel(field(r)), trancl(r))
opaque symbol rtrancl_cases (p r : τ ι) :
  π (p ∈ rtrancl r) → π (p ∈ id_rel (field r) ∨ p ∈ trancl r) ≔
begin
  assume p r hp;
  have hunfold : π (rtrancl r = Un (id_rel (field r)) (rcomp r (rtrancl r)))
    { refine lfp_unfold (Sigma (field r) (λ _, field r))
        (λ s, Un (id_rel (field r)) (rcomp r s)) (rtrancl_bnd_mono r) };
  // Transport p ∈ rtrancl(r) to p ∈ Un(id_rel(field(r)), trancl(r))
  // rcomp(r, rtrancl(r)) = trancl(r) by definition
  have hp2 : π (p ∈ Un (id_rel (field r)) (rcomp r (rtrancl r)))
    { refine ind_eq (eq_sym hunfold) (λ z, p ∈ z) hp };
  refine UnE p (id_rel (field r)) (rcomp r (rtrancl r)) hp2
end;

// Downward closure: r-predecessors of elements of A are in A
// This is needed for wf_trancl (corresponds to Isabelle's r-``A ⊆ A)
// dc A r means: ∀y x. x ∈ A → Pair(y,x) ∈ r → y ∈ A
symbol dc (A r : τ ι) : Prop ≔
  `∀ (y : τ ι), `∀ (x : τ ι), x ∈ A ⇒ Pair y x ∈ r ⇒ y ∈ A;

opaque symbol wf_trancl (A r : τ ι) :
  π (wf A r) → π (dc A r) → π (wf A (trancl r)) ≔
begin
  assume A r hwf hdc;
  // Goal: wf A (trancl r)
  // i.e., ∀Z. Z ⊆ A → Z ≠ empty → Bex Z (λ x₀, Ball Z (λ y, Pair y x₀ ∉ trancl r))
  assume Z hZA hZne;
  // Step 1: By wf_induct, prove Ball A (λ x, Q x) where
  // Q(x) = ∀z∈A. Pair(z,x) ∈ trancl(r) → z ∈ Z → CONCL
  // where CONCL = Bex Z (λ x₀, Ball Z (λ y, Pair y x₀ ∉ trancl r))
  have hind_step : π (Ball A (λ x, Ball A (λ y, Pair y x ∈ r ⇒
      Ball A (λ z, Pair z y ∈ trancl r ⇒ z ∈ Z ⇒
        Bex Z (λ x0, Ball Z (λ w, Pair w x0 ∉ trancl r))))
    ⇒ Ball A (λ z, Pair z x ∈ trancl r ⇒ z ∈ Z ⇒
        Bex Z (λ x0, Ball Z (λ w, Pair w x0 ∉ trancl r)))))
  {
    assume x hxA ih z hzA hzt hzZ;
    // Pair(z,x) ∈ trancl(r) = rcomp(r, rtrancl(r))
    // Decompose: ∃w. Pair(z,w) ∈ rtrancl(r) ∧ Pair(w,x) ∈ r
    have hex : π (`∃ (m : τ ι), Pair z m ∈ rtrancl r ∧ Pair m x ∈ r)
      { refine rcompE_pair z x r (rtrancl r) hzt };
    refine ∃ₑ hex _;
    assume m hm;
    have hzm : π (Pair z m ∈ rtrancl r) { refine ∧ₑ₁ hm };
    have hmx : π (Pair m x ∈ r) { refine ∧ₑ₂ hm };
    // m ∈ A by downward closure (Pair(m,x) ∈ r, x ∈ A)
    have hmA : π (m ∈ A) { refine hdc m x hxA hmx };
    // By IH: Q(m), i.e., ∀z'∈A. Pair(z',m) ∈ trancl → z'∈Z → CONCL
    have hQm : π (Ball A (λ z2, Pair z2 m ∈ trancl r ⇒ z2 ∈ Z ⇒
        Bex Z (λ x0, Ball Z (λ w2, Pair w2 x0 ∉ trancl r))))
      { refine ih m hmA hmx };
    // Pair(z,m) ∈ rtrancl(r): either in id_rel or in trancl
    have hcases : π (Pair z m ∈ id_rel (field r) ∨ Pair z m ∈ trancl r)
      { refine rtrancl_cases (Pair z m) r hzm };
    refine ∨ₑ hcases _ _
    { // Case: Pair(z,m) ∈ id_rel(field(r)), so z = m
      assume hid;
      have hbex : π (Bex (field r) (λ v, Pair z m = Pair v v))
        { refine id_relE (Pair z m) (field r) hid };
      refine ∃ₑ hbex _;
      assume v hv;
      have hvf : π (v ∈ field r) { refine ∧ₑ₁ hv };
      have hpeq : π (Pair z m = Pair v v) { refine ∧ₑ₂ hv };
      have hzv : π (z = v) { refine Pair_inject1 z m v v hpeq };
      have hmv : π (m = v) { refine Pair_inject2 z m v v hpeq };
      // z = v = m, so z = m
      have hzm_eq : π (z = m)
        { refine ind_eq hmv (λ w2, z = w2) hzv };
      // z = m, z ∈ Z. Need CONCL.
      // By EM: either z is trancl-minimal in Z, or not
      refine ∨ₑ (em (Ball Z (λ y, Pair y z ∉ trancl r))) _ _
      { // z is trancl-minimal: z is the witness
        assume hmin;
        refine ∃ᵢ z (∧ᵢ hzZ hmin) }
      { // ∃y∈Z. Pair(y,z) ∈ trancl(r)
        assume hnmin;
        // ¬∀y∈Z. ... means ∃y∈Z. ¬(Pair(y,z) ∉ trancl(r)), i.e., ∃y∈Z. Pair(y,z) ∈ trancl(r)
        // By ¬¬ₑ on the conclusion
        refine ¬¬ₑ _ _;
        assume hnCONCL;
        // We'll derive ⊥ from hnmin
        apply hnmin;
        assume y hyZ;
        // Need: Pair(y,z) ∉ trancl(r)
        assume hyzt;
        // Pair(y,z) ∈ trancl(r), y ∈ Z ⊆ A, so y ∈ A
        have hyA : π (y ∈ A) { refine hZA y hyZ };
        // Q(m) = Q(z) (since z=m): apply with y
        have hCONCL2 : π (Bex Z (λ x0, Ball Z (λ w2, Pair w2 x0 ∉ trancl r)))
          { refine ind_eq hzm_eq
              (λ w2, Ball A (λ z2, Pair z2 w2 ∈ trancl r ⇒ z2 ∈ Z ⇒
                Bex Z (λ x0, Ball Z (λ w3, Pair w3 x0 ∉ trancl r)))) hQm
              y hyA hyzt hyZ };
        refine hnCONCL hCONCL2 } }
    { // Case: Pair(z,m) ∈ trancl(r)
      assume hzmtc;
      // Q(m) with z: z ∈ A, Pair(z,m) ∈ trancl, z ∈ Z → CONCL
      refine hQm z hzA hzmtc hzZ }
  };
  // Apply wf_induct to get Ball A Q
  have hQ : π (Ball A (λ x, Ball A (λ z, Pair z x ∈ trancl r ⇒ z ∈ Z ⇒
      Bex Z (λ x0, Ball Z (λ w, Pair w x0 ∉ trancl r)))))
    { refine wf_induct A r
        (λ x, Ball A (λ z, Pair z x ∈ trancl r ⇒ z ∈ Z ⇒
          Bex Z (λ x0, Ball Z (λ w, Pair w x0 ∉ trancl r))))
        hwf hind_step };
  // Step 2: Get the r-minimal element of Z using wf(A,r)
  have hmin : π (Bex Z (λ x0, Ball Z (λ y, Pair y x0 ∉ r)))
    { refine hwf Z hZA hZne };
  refine ∃ₑ hmin _;
  assume a0 ha0;
  have ha0Z : π (a0 ∈ Z) { refine ∧ₑ₁ ha0 };
  have ha0min : π (Ball Z (λ y, Pair y a0 ∉ r)) { refine ∧ₑ₂ ha0 };
  have ha0A : π (a0 ∈ A) { refine hZA a0 ha0Z };
  // Step 3: By EM, either a0 is trancl-minimal or not
  refine ∨ₑ (em (Ball Z (λ y, Pair y a0 ∉ trancl r))) _ _
  { // a0 is trancl-minimal
    assume htcmin;
    refine ∃ᵢ a0 (∧ᵢ ha0Z htcmin) }
  { // ∃y∈Z. Pair(y,a0) ∈ trancl(r)
    assume hntcmin;
    // Use ¬¬ₑ to derive CONCL
    refine ¬¬ₑ _ _;
    assume hnCONCL;
    apply hntcmin;
    assume y hyZ;
    assume hyatc;
    have hyA : π (y ∈ A) { refine hZA y hyZ };
    // Q(a0) with y: y ∈ A, Pair(y,a0) ∈ trancl, y ∈ Z → CONCL
    have hCONCL : π (Bex Z (λ x0, Ball Z (λ w, Pair w x0 ∉ trancl r)))
      { refine hQ a0 ha0A y hyA hyatc hyZ };
    refine hnCONCL hCONCL }
end;

// ===========================================================================
// Global well-foundedness (Isabelle's wf(r))
// ===========================================================================

// wf_global(r): every nonempty set has an r-minimal element
// This is the Isabelle definition: ∀Z. Z = 0 ∨ (∃x∈Z. ∀y. ⟨y,x⟩∈r → y ∉ Z)
symbol wf_global (r : τ ι) : Prop ≔
  `∀ (Z : τ ι), Z = empty ∨ Bex Z (λ x, `∀ (y : τ ι), Pair y x ∈ r ⇒ y ∉ Z);

// ---------------------------------------------------------------------------
// wf_global_induct: unrestricted well-founded induction
// wf_global(r) → (∀x. (∀y. Pair(y,x) ∈ r → P(y)) → P(x)) → P(a)
// ---------------------------------------------------------------------------

opaque symbol wf_global_induct (r : τ ι) (P : τ ι → Prop) (a : τ ι) :
  π (wf_global r) →
  π (`∀ (x : τ ι), (`∀ (y : τ ι), Pair y x ∈ r ⇒ P y) ⇒ P x) →
  π (P a) ≔
begin
  assume r P a hwf hind;
  // By contradiction: assume ¬P(a)
  refine ¬¬ₑ _ _;
  assume hnPa;
  // Use Z = Collect(cons(a, domain(r)), λ z. ¬P(z))
  // This contains a (if ¬P(a)) and all domain(r) elements without P.
  have hacons : π (a ∈ cons a (domain r)) { refine consI1 a (domain r) };
  have haZ : π (a ∈ Collect (cons a (domain r)) (λ z, ¬ P z))
    { refine CollectI a (cons a (domain r)) (λ z, ¬ P z) hacons hnPa };
  have hZne : π (Collect (cons a (domain r)) (λ z, ¬ P z) ≠ empty)
    { refine ne_empty (Collect (cons a (domain r)) (λ z, ¬ P z)) a haZ };
  have hwfZ : π (Collect (cons a (domain r)) (λ z, ¬ P z) = empty ∨
    Bex (Collect (cons a (domain r)) (λ z, ¬ P z))
      (λ x, `∀ (y : τ ι), Pair y x ∈ r ⇒ y ∉ Collect (cons a (domain r)) (λ z, ¬ P z)))
    { refine hwf (Collect (cons a (domain r)) (λ z, ¬ P z)) };
  refine ∨ₑ hwfZ _ _
  { assume heq; refine hZne heq }
  { assume hbex;
    refine ∃ₑ hbex _;
    assume x0 hx0;
    have hx0Z : π (x0 ∈ Collect (cons a (domain r)) (λ z, ¬ P z)) { refine ∧ₑ₁ hx0 };
    have hx0min : π (`∀ (y : τ ι), Pair y x0 ∈ r ⇒
      y ∉ Collect (cons a (domain r)) (λ z, ¬ P z))
      { refine ∧ₑ₂ hx0 };
    have hnPx0 : π (¬ P x0)
      { refine CollectD2 x0 (cons a (domain r)) (λ z, ¬ P z) hx0Z };
    // Show ∀y. Pair(y,x0)∈r → P(y)
    have hpred : π (`∀ (y : τ ι), Pair y x0 ∈ r ⇒ P y)
      { assume y hyr;
        have hynotZ : π (y ∉ Collect (cons a (domain r)) (λ z, ¬ P z))
          { refine hx0min y hyr };
        // y ∈ domain(r) since Pair(y,x0) ∈ r
        have hydom : π (y ∈ domain r) { refine domainI y x0 r hyr };
        have hycons : π (y ∈ cons a (domain r))
          { refine consI2 y a (domain r) hydom };
        // If ¬P(y) then y ∈ Z. Contradiction with hynotZ.
        refine ¬¬ₑ _ _;
        assume hnPy;
        have hyZ : π (y ∈ Collect (cons a (domain r)) (λ z, ¬ P z))
          { refine CollectI y (cons a (domain r)) (λ z, ¬ P z) hycons hnPy };
        refine hynotZ hyZ };
    have hPx0 : π (P x0) { refine hind x0 hpred };
    refine hnPx0 hPx0 }
end;

// ---------------------------------------------------------------------------
// wf_global_trancl: wf_global(r) → wf_global(trancl(r))
// ---------------------------------------------------------------------------
// Uses the same strategy as wf_trancl: strengthen the induction hypothesis.
// Q(x) = ∀z. Pair(z,x)∈r⁺ → z∈Z → CONCL

opaque symbol wf_global_trancl (r : τ ι) :
  π (wf_global r) → π (wf_global (trancl r)) ≔
begin
  assume r hwf Z;
  refine ∨ₑ (em (Z = empty)) _ _
  { assume heq; refine ∨ᵢ₁ heq }
  { assume hne;
    refine ∨ᵢ₂ _;
    // Strategy (same as wf_trancl): prove the stronger predicate
    // Q(x) = ∀z. Pair(z,x) ∈ trancl(r) → z ∈ Z → CONCL
    // where CONCL = Bex Z (λ x₀, ∀y. Pair(y,x₀) ∈ trancl(r) → y ∉ Z)
    // via wf_global_induct on r.

    // Step 1: Prove the inductive step for Q using wf_global_induct.
    // For each x, given IH: ∀m. Pair(m,x)∈r → Q(m), prove Q(x).
    // Q(x): given z with Pair(z,x) ∈ trancl(r) and z ∈ Z, prove CONCL.
    // Decompose Pair(z,x) ∈ trancl(r) = rcomp(r, rtrancl(r)):
    //   ∃m. Pair(z,m) ∈ rtrancl(r) ∧ Pair(m,x) ∈ r.
    // By IH with m: Q(m).
    // Case Pair(z,m) ∈ rtrancl(r):
    //   - id_rel: z = m. By EM either z is trancl-minimal or not.
    //   - trancl: Pair(z,m) ∈ trancl(r). Apply Q(m) with z directly.

    // First, prove Q for ALL x using wf_global_induct.
    // We'll instantiate it for specific x values later.
    have hind_step :
      π (`∀ (x : τ ι),
        (`∀ (m : τ ι), Pair m x ∈ r ⇒
          `∀ (z : τ ι), Pair z m ∈ trancl r ⇒ z ∈ Z ⇒
            Bex Z (λ x0, `∀ (w : τ ι), Pair w x0 ∈ trancl r ⇒ w ∉ Z))
        ⇒ `∀ (z : τ ι), Pair z x ∈ trancl r ⇒ z ∈ Z ⇒
            Bex Z (λ x0, `∀ (w : τ ι), Pair w x0 ∈ trancl r ⇒ w ∉ Z))
    {
      assume x ih z hzt hzZ;
      // Decompose Pair(z,x) ∈ trancl(r) = rcomp(r, rtrancl(r))
      have hex : π (`∃ (m : τ ι), Pair z m ∈ rtrancl r ∧ Pair m x ∈ r)
        { refine rcompE_pair z x r (rtrancl r) hzt };
      refine ∃ₑ hex _;
      assume m hm;
      have hzm : π (Pair z m ∈ rtrancl r) { refine ∧ₑ₁ hm };
      have hmx : π (Pair m x ∈ r) { refine ∧ₑ₂ hm };
      // IH gives Q(m)
      have hQm : π (`∀ (z2 : τ ι), Pair z2 m ∈ trancl r ⇒ z2 ∈ Z ⇒
          Bex Z (λ x0, `∀ (w : τ ι), Pair w x0 ∈ trancl r ⇒ w ∉ Z))
        { refine ih m hmx };
      // Case split on Pair(z,m) ∈ rtrancl(r): either id_rel or trancl
      have hcases : π (Pair z m ∈ id_rel (field r) ∨ Pair z m ∈ trancl r)
        { refine rtrancl_cases (Pair z m) r hzm };
      refine ∨ₑ hcases _ _
      { // Case: Pair(z,m) ∈ id_rel(field(r)), so z = m
        assume hid;
        have hbex : π (Bex (field r) (λ v, Pair z m = Pair v v))
          { refine id_relE (Pair z m) (field r) hid };
        refine ∃ₑ hbex _;
        assume v hv;
        have hpeq : π (Pair z m = Pair v v) { refine ∧ₑ₂ hv };
        have hzv : π (z = v) { refine Pair_inject1 z m v v hpeq };
        have hmv : π (m = v) { refine Pair_inject2 z m v v hpeq };
        have hzm_eq : π (z = m)
          { refine ind_eq hmv (λ w2, z = w2) hzv };
        // z = m, z ∈ Z. By EM: either z is trancl-minimal or not.
        refine ∨ₑ (em (`∀ (y : τ ι), Pair y z ∈ trancl r ⇒ y ∉ Z)) _ _
        { // z is trancl-minimal: z is the witness
          assume hmin;
          refine ∃ᵢ z (∧ᵢ hzZ hmin) }
        { // ¬(∀y. Pair(y,z)∈r⁺ → y∉Z)
          assume hnmin;
          // Use ¬¬ₑ to derive CONCL
          refine ¬¬ₑ _ _;
          assume hnCONCL;
          // Derive ⊥ from hnmin
          apply hnmin;
          assume y hyztc hyZ2;
          // hyztc : Pair(y,z) ∈ trancl(r), hyZ2 : y ∈ Z.
          // Since z=m, Pair(y,z) = Pair(y,m), so Pair(y,m) ∈ trancl(r).
          have hpair_eq : π (Pair y z = Pair y m)
            { refine feq (Pair y) hzm_eq };
          have hymt : π (Pair y m ∈ trancl r)
            { refine ind_eq (eq_sym hpair_eq) (λ p, p ∈ trancl r) hyztc };
          have hCONCL2 : π (Bex Z (λ x0, `∀ (w : τ ι), Pair w x0 ∈ trancl r ⇒ w ∉ Z))
            { refine hQm y hymt hyZ2 };
          refine hnCONCL hCONCL2 } }
      { // Case: Pair(z,m) ∈ trancl(r)
        assume hzmtc;
        // Q(m) with z: Pair(z,m)∈trancl(r), z∈Z → CONCL
        refine hQm z hzmtc hzZ }
    };

    // Step 2: Get Q(x) for all x via wf_global_induct
    // Q(x) = ∀z. Pair(z,x) ∈ trancl(r) → z ∈ Z → CONCL
    have hQ : π (`∀ (x : τ ι), `∀ (z : τ ι), Pair z x ∈ trancl r ⇒ z ∈ Z ⇒
        Bex Z (λ x0, `∀ (w : τ ι), Pair w x0 ∈ trancl r ⇒ w ∉ Z))
      { assume x;
        refine wf_global_induct r
          (λ x, `∀ (z : τ ι), Pair z x ∈ trancl r ⇒ z ∈ Z ⇒
            Bex Z (λ x0, `∀ (w : τ ι), Pair w x0 ∈ trancl r ⇒ w ∉ Z))
          x hwf hind_step };

    // Step 3: Get the r-minimal element of Z using wf_global(r)
    have hwfZr : π (Z = empty ∨ Bex Z (λ x, `∀ (y : τ ι), Pair y x ∈ r ⇒ y ∉ Z))
      { refine hwf Z };
    refine ∨ₑ hwfZr _ _
    { assume heq; apply ⊥ₑ; refine hne heq }
    { assume hrmin;
      refine ∃ₑ hrmin _;
      assume a0 ha0;
      have ha0Z : π (a0 ∈ Z) { refine ∧ₑ₁ ha0 };
      have ha0rmin : π (`∀ (y : τ ι), Pair y a0 ∈ r ⇒ y ∉ Z) { refine ∧ₑ₂ ha0 };
      // By EM: either a0 is trancl-minimal or not
      refine ∨ₑ (em (`∀ (y : τ ι), Pair y a0 ∈ trancl r ⇒ y ∉ Z)) _ _
      { // a0 is trancl-minimal
        assume htcmin;
        refine ∃ᵢ a0 (∧ᵢ ha0Z htcmin) }
      { // ∃y∈Z. Pair(y,a0) ∈ trancl(r) — use ¬¬ₑ
        assume hntcmin;
        refine ¬¬ₑ _ _;
        assume hnCONCL;
        apply hntcmin;
        assume y hyt;
        assume hyZ;
        // Pair(y,a0) ∈ trancl(r), y ∈ Z. Apply Q(a0) to get CONCL.
        have hCONCL : π (Bex Z (λ x0, `∀ (w : τ ι), Pair w x0 ∈ trancl r ⇒ w ∉ Z))
          { refine hQ a0 y hyt hyZ };
        refine hnCONCL hCONCL } } }
end;

// ===========================================================================
// Well-founded recursion definitions
// ===========================================================================

// is_recfun(r,a,H,f): f is the recursion function for element a
// f = Lambda(r⁻¹{a}, λ x. H(x, restrict(f, r⁻¹{x})))
symbol is_recfun (r a : τ ι) (H : τ ι → τ ι → τ ι) (f : τ ι) : Prop ≔
  f = Lambda (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x)));

// the_recfun(r,a,H): THE f such that is_recfun(r,a,H,f)
symbol the_recfun (r a : τ ι) (H : τ ι → τ ι → τ ι) : τ ι ≔
  The (λ f, is_recfun r a H f);

// wftrec(r,a,H): well-founded transitive recursion
// wftrec(r,a,H) = H(a, the_recfun(r,a,H))
symbol wftrec (r a : τ ι) (H : τ ι → τ ι → τ ι) : τ ι ≔
  H a (the_recfun r a H);

// wfrec(r,a,H): well-founded recursion (uses transitive closure)
// wfrec(r,a,H) = wftrec(r⁺, a, λ x f. H(x, restrict(f, r⁻¹{x})))
symbol wfrec (r a : τ ι) (H : τ ι → τ ι → τ ι) : τ ι ≔
  wftrec (trancl r) a (λ x f, H x (restrict f (vimage_singleton r x)));

// ===========================================================================
// is_recfun basic properties
// ===========================================================================

// is_recfun(r,a,H,f) → f is a function (Lambda is always a function)
opaque symbol is_recfun_imp_function (r a : τ ι) (H : τ ι → τ ι → τ ι) (f : τ ι) :
  π (is_recfun r a H f) → π (function f) ≔
begin
  assume r a H f hrf;
  // is_recfun means f = Lambda(vimage_singleton r a, ...)
  // Lambda is always a function
  have hfunc : π (function (Lambda (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x)))))
    { refine Lambda_function (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x))) };
  refine ind_eq hrf (λ z, function z) hfunc
end;

// is_recfun(r,a,H,f) → domain(f) = vimage_singleton r a
opaque symbol is_recfun_domain (r a : τ ι) (H : τ ι → τ ι → τ ι) (f : τ ι) :
  π (is_recfun r a H f) → π (domain f = vimage_singleton r a) ≔
begin
  assume r a H f hrf;
  have hlam_dom : π (domain (Lambda (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x)))) = vimage_singleton r a)
    { refine subset_antisym
        (domain (Lambda (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x)))))
        (vimage_singleton r a)
        (domain_Lambda_subset (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x))))
        (Lambda_domain_subset (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x)))) };
  refine ind_eq hrf (λ z, domain z = vimage_singleton r a) hlam_dom
end;

// apply_recfun: is_recfun(r,a,H,f) → Pair(x,a) ∈ r → fapply(f,x) = H(x, restrict(f, r⁻¹{x}))
opaque symbol apply_recfun (r a : τ ι) (H : τ ι → τ ι → τ ι) (f : τ ι) (x : τ ι) :
  π (is_recfun r a H f) →
  π (Pair x a ∈ r) →
  π (fapply f x = H x (restrict f (vimage_singleton r x))) ≔
begin
  assume r a H f x hrf hxa;
  // f = Lambda(vimage_singleton r a, λ y. H(y, restrict(f, r⁻¹{y})))
  // x ∈ vimage_singleton r a since Pair(x,a) ∈ r
  have hxdom : π (x ∈ vimage_singleton r a)
    { refine vimage_singletonI x a r hxa };
  // fapply(Lambda(...), x) = H(x, restrict(f, r⁻¹{x}))
  // But wait, f = Lambda(...), so we need to compute fapply(f, x)
  // Using is_recfun: f = Lambda(vimage_singleton r a, body)
  // So fapply(f, x) = fapply(Lambda(vimage_singleton r a, body), x) = body(x) by beta
  // But f and Lambda(...) are equal, so fapply(f,x) = fapply(Lambda(...),x) = body(x)
  have hbeta : π (fapply (Lambda (vimage_singleton r a) (λ y, H y (restrict f (vimage_singleton r y)))) x =
    H x (restrict f (vimage_singleton r x)))
    { refine beta (vimage_singleton r a) (λ y, H y (restrict f (vimage_singleton r y))) x hxdom };
  // Transport along f = Lambda(...)
  refine ind_eq hrf (λ z, fapply z x = H x (restrict f (vimage_singleton r x))) hbeta
end;

// ===========================================================================
// is_recfun_equal: the key uniqueness lemma
// ===========================================================================

// Helper: if f is a function and Pair(y,z) ∈ f, then z = fapply(f,y)
// (This is just function_apply_equality rephrased)

// is_recfun_equal: wf_global(r) → trans(r) → is_recfun(r,a,H,f) → is_recfun(r,b,H,g)
//   → Pair(x,a) ∈ r → Pair(x,b) ∈ r → fapply(f,x) = fapply(g,x)
opaque symbol is_recfun_equal (r : τ ι) (H : τ ι → τ ι → τ ι)
  (a b : τ ι) (f g : τ ι) :
  π (wf_global r) →
  π (trans r) →
  π (is_recfun r a H f) →
  π (is_recfun r b H g) →
  π (Ball (vimage_singleton r a) (λ x, Pair x b ∈ r ⇒ fapply f x = fapply g x)) ≔
begin
  assume r H a b f g hwf htr hrf hrg;
  // We prove this by wf_global_induct on x.
  // P(x) = x ∈ r⁻¹{a} → Pair(x,b) ∈ r → fapply(f,x) = fapply(g,x)
  // But wf_global_induct gives P for all x, so we apply it with the right predicate.

  // For each x ∈ vimage_singleton r a with Pair(x,b) ∈ r,
  // we use wf_global_induct to show fapply(f,x) = fapply(g,x).
  assume x hxa hxb;
  // hxa : x ∈ vimage_singleton r a, i.e., Pair(x,a) ∈ r
  have hxar : π (Pair x a ∈ r) { refine vimage_singletonD x a r hxa };
  // Apply wf_global_induct on x with predicate:
  // P(y) = Pair(y,a) ∈ r → Pair(y,b) ∈ r → fapply(f,y) = fapply(g,y)
  refine wf_global_induct r
    (λ y, Pair y a ∈ r ⇒ Pair y b ∈ r ⇒ fapply f y = fapply g y)
    x hwf _ hxar hxb;
  // Inductive step: assume IH for all r-predecessors of y
  assume y ih hya hyb;
  // fapply(f,y) = H(y, restrict(f, r⁻¹{y})) by apply_recfun
  have hfy : π (fapply f y = H y (restrict f (vimage_singleton r y)))
    { refine apply_recfun r a H f y hrf hya };
  // fapply(g,y) = H(y, restrict(g, r⁻¹{y})) by apply_recfun
  have hgy : π (fapply g y = H y (restrict g (vimage_singleton r y)))
    { refine apply_recfun r b H g y hrg hyb };
  // Need: restrict(f, r⁻¹{y}) = restrict(g, r⁻¹{y})
  have hrestr_eq : π (restrict f (vimage_singleton r y) = restrict g (vimage_singleton r y))
    { refine subset_antisym
        (restrict f (vimage_singleton r y))
        (restrict g (vimage_singleton r y)) _ _
      { // restrict(f, r⁻¹{y}) ⊆ restrict(g, r⁻¹{y})
        assume p hp;
        // p ∈ restrict(f, r⁻¹{y}): p ∈ f and ∃w∈r⁻¹{y}. ∃v. p = Pair(w,v)
        have hpf : π (p ∈ f) { refine restrictD1 p f (vimage_singleton r y) hp };
        have hbex : π (Bex (vimage_singleton r y) (λ w, `∃ (v : τ ι), p = Pair w v))
          { refine CollectD2 p f (λ q, Bex (vimage_singleton r y) (λ w, `∃ (v : τ ι), q = Pair w v)) hp };
        refine ∃ₑ hbex _;
        assume w hw;
        have hwdom : π (w ∈ vimage_singleton r y) { refine ∧ₑ₁ hw };
        have hexv : π (`∃ (v : τ ι), p = Pair w v) { refine ∧ₑ₂ hw };
        refine ∃ₑ hexv _;
        assume v hpwv;
        // Pair(w,y) ∈ r (from w ∈ r⁻¹{y})
        have hwy : π (Pair w y ∈ r) { refine vimage_singletonD w y r hwdom };
        // By trans: Pair(w,a) ∈ r and Pair(w,b) ∈ r
        have hwa : π (Pair w a ∈ r) { refine transD r w y a htr hwy hya };
        have hwb : π (Pair w b ∈ r) { refine transD r w y b htr hwy hyb };
        // By IH: fapply(f,w) = fapply(g,w)
        have hfgw : π (fapply f w = fapply g w) { refine ih w hwy hwa hwb };
        // v = fapply(f,w) since Pair(w,v) ∈ f and f is a function
        have hfunc_f : π (function f) { refine is_recfun_imp_function r a H f hrf };
        have hvfw : π (fapply f w = v)
          { have hpwvf : π (Pair w v ∈ f) { rewrite left hpwv; apply hpf };
            refine function_apply_equality w v f hpwvf hfunc_f };
        // fapply(g,w) = fapply(f,w) = v, so Pair(w,v) ∈ g
        have hvgw : π (fapply g w = v) { rewrite left hfgw; apply hvfw };
        // w ∈ domain(g): domain(g) = r⁻¹{b}, and Pair(w,b) ∈ r
        have hwdomg : π (w ∈ domain g) {
          have hdom_g : π (domain g = vimage_singleton r b) { refine is_recfun_domain r b H g hrg };
          have hwvsg : π (w ∈ vimage_singleton r b) { refine vimage_singletonI w b r hwb };
          refine ind_eq hdom_g (λ z, w ∈ z) hwvsg
        };
        have hfunc_g : π (function g) { refine is_recfun_imp_function r b H g hrg };
        // Pair(w, fapply(g,w)) ∈ g
        have hpg : π (Pair w (fapply g w) ∈ g) { refine apply_Pair g w hfunc_g hwdomg };
        // Pair(w, v) ∈ g since fapply(g,w) = v
        have hpwvg : π (Pair w v ∈ g)
          { refine ind_eq (eq_sym hvgw) (λ z, Pair w z ∈ g) hpg };
        // p = Pair(w,v) ∈ restrict(g, r⁻¹{y}) since w ∈ r⁻¹{y}
        rewrite hpwv;
        refine restrictI w v g (vimage_singleton r y) hpwvg hwdom }
      { // restrict(g, r⁻¹{y}) ⊆ restrict(f, r⁻¹{y}) — symmetric
        assume p hp;
        have hpg : π (p ∈ g) { refine restrictD1 p g (vimage_singleton r y) hp };
        have hbex : π (Bex (vimage_singleton r y) (λ w, `∃ (v : τ ι), p = Pair w v))
          { refine CollectD2 p g (λ q, Bex (vimage_singleton r y) (λ w, `∃ (v : τ ι), q = Pair w v)) hp };
        refine ∃ₑ hbex _;
        assume w hw;
        have hwdom : π (w ∈ vimage_singleton r y) { refine ∧ₑ₁ hw };
        have hexv : π (`∃ (v : τ ι), p = Pair w v) { refine ∧ₑ₂ hw };
        refine ∃ₑ hexv _;
        assume v hpwv;
        have hwy : π (Pair w y ∈ r) { refine vimage_singletonD w y r hwdom };
        have hwa : π (Pair w a ∈ r) { refine transD r w y a htr hwy hya };
        have hwb : π (Pair w b ∈ r) { refine transD r w y b htr hwy hyb };
        have hfgw : π (fapply f w = fapply g w) { refine ih w hwy hwa hwb };
        have hfunc_g : π (function g) { refine is_recfun_imp_function r b H g hrg };
        have hvgw : π (fapply g w = v)
          { have hpwvg : π (Pair w v ∈ g) { rewrite left hpwv; apply hpg };
            refine function_apply_equality w v g hpwvg hfunc_g };
        have hvfw : π (fapply f w = v) { rewrite hfgw; apply hvgw };
        have hwdomf : π (w ∈ domain f) {
          have hdom_f : π (domain f = vimage_singleton r a) { refine is_recfun_domain r a H f hrf };
          have hwvsa : π (w ∈ vimage_singleton r a) { refine vimage_singletonI w a r hwa };
          refine ind_eq hdom_f (λ z, w ∈ z) hwvsa
        };
        have hfunc_f : π (function f) { refine is_recfun_imp_function r a H f hrf };
        have hpf : π (Pair w (fapply f w) ∈ f) { refine apply_Pair f w hfunc_f hwdomf };
        have hpwvf : π (Pair w v ∈ f)
          { refine ind_eq (eq_sym hvfw) (λ z, Pair w z ∈ f) hpf };
        rewrite hpwv;
        refine restrictI w v f (vimage_singleton r y) hpwvf hwdom } };
  rewrite hfy; rewrite hgy; rewrite hrestr_eq; reflexivity
end;

// ===========================================================================
// is_recfun_cut: restrict(f, r⁻¹{b}) = g
// ===========================================================================

opaque symbol is_recfun_cut (r : τ ι) (H : τ ι → τ ι → τ ι)
  (a b : τ ι) (f g : τ ι) :
  π (wf_global r) →
  π (trans r) →
  π (is_recfun r a H f) →
  π (is_recfun r b H g) →
  π (Pair b a ∈ r) →
  π (restrict f (vimage_singleton r b) = g) ≔
begin
  assume r H a b f g hwf htr hrf hrg hba;
  refine subset_antisym (restrict f (vimage_singleton r b)) g _ _
  { // restrict(f, r⁻¹{b}) ⊆ g
    assume p hp;
    have hpf : π (p ∈ f) { refine restrictD1 p f (vimage_singleton r b) hp };
    have hbex : π (Bex (vimage_singleton r b) (λ w, `∃ (v : τ ι), p = Pair w v))
      { refine CollectD2 p f (λ q, Bex (vimage_singleton r b) (λ w, `∃ (v : τ ι), q = Pair w v)) hp };
    refine ∃ₑ hbex _;
    assume w hw;
    have hwvs : π (w ∈ vimage_singleton r b) { refine ∧ₑ₁ hw };
    have hexv : π (`∃ (v : τ ι), p = Pair w v) { refine ∧ₑ₂ hw };
    refine ∃ₑ hexv _;
    assume v hpwv;
    have hwb : π (Pair w b ∈ r) { refine vimage_singletonD w b r hwvs };
    have hwa : π (Pair w a ∈ r) { refine transD r w b a htr hwb hba };
    have hwvsa : π (w ∈ vimage_singleton r a) { refine vimage_singletonI w a r hwa };
    // v = fapply(f,w) since f is a function and Pair(w,v) ∈ f
    have hfunc_f : π (function f) { refine is_recfun_imp_function r a H f hrf };
    have hpwvf : π (Pair w v ∈ f) { rewrite left hpwv; apply hpf };
    have hvfw : π (fapply f w = v) { refine function_apply_equality w v f hpwvf hfunc_f };
    // fapply(f,w) = fapply(g,w) by is_recfun_equal
    have hfgw : π (fapply f w = fapply g w)
      { refine is_recfun_equal r H a b f g hwf htr hrf hrg w hwvsa hwb };
    // fapply(g,w) = v
    have hvgw : π (fapply g w = v) { rewrite left hfgw; apply hvfw };
    // Pair(w, fapply(g,w)) ∈ g
    have hfunc_g : π (function g) { refine is_recfun_imp_function r b H g hrg };
    have hwdomg : π (w ∈ domain g) {
      have hdom_g : π (domain g = vimage_singleton r b) { refine is_recfun_domain r b H g hrg };
      refine ind_eq hdom_g (λ z, w ∈ z) hwvs
    };
    have hpg : π (Pair w (fapply g w) ∈ g) { refine apply_Pair g w hfunc_g hwdomg };
    have hpwvg : π (Pair w v ∈ g)
      { refine ind_eq (eq_sym hvgw) (λ z, Pair w z ∈ g) hpg };
    rewrite hpwv; apply hpwvg }
  { // g ⊆ restrict(f, r⁻¹{b})
    assume p hp;
    // g = Lambda(r⁻¹{b}, body), so p ∈ g means ∃w∈r⁻¹{b}. p = Pair(w, body(w))
    // We need to extract w from the Lambda structure
    have hg_eq : π (g = Lambda (vimage_singleton r b) (λ x, H x (restrict g (vimage_singleton r x))))
      { apply hrg };
    // p ∈ Lambda(r⁻¹{b}, body)
    have hpL : π (p ∈ Lambda (vimage_singleton r b) (λ x, H x (restrict g (vimage_singleton r x))))
      { refine ind_eq (eq_sym hg_eq) (λ z, p ∈ z) hp };
    // RepFun_iff: p ∈ RepFun(A, f) ↔ Bex A (λ z, p = f(z))
    have hbex : π (Bex (vimage_singleton r b) (λ w, p = Pair w (H w (restrict g (vimage_singleton r w)))))
      { refine ∧ₑ₁ (RepFun_iff p (vimage_singleton r b)
          (λ w, Pair w (H w (restrict g (vimage_singleton r w))))) hpL };
    refine ∃ₑ hbex _;
    assume w hw;
    have hwvs : π (w ∈ vimage_singleton r b) { refine ∧ₑ₁ hw };
    have hpeq : π (p = Pair w (H w (restrict g (vimage_singleton r w)))) { refine ∧ₑ₂ hw };
    have hwb : π (Pair w b ∈ r) { refine vimage_singletonD w b r hwvs };
    have hwa : π (Pair w a ∈ r) { refine transD r w b a htr hwb hba };
    have hwvsa : π (w ∈ vimage_singleton r a) { refine vimage_singletonI w a r hwa };
    // fapply(g,w) = H(w, restrict(g, r⁻¹{w})) = the body value at w
    have hfgw : π (fapply f w = fapply g w)
      { refine is_recfun_equal r H a b f g hwf htr hrf hrg w hwvsa hwb };
    // fapply(g,w) = H(w, restrict(g, r⁻¹{w}))
    have hgw : π (fapply g w = H w (restrict g (vimage_singleton r w)))
      { refine apply_recfun r b H g w hrg hwb };
    // fapply(f,w) = H(w, restrict(g, r⁻¹{w})) (combining)
    have hfw_body : π (fapply f w = H w (restrict g (vimage_singleton r w)))
      { rewrite hfgw; apply hgw };
    // Pair(w, fapply(f,w)) ∈ f
    have hfunc_f : π (function f) { refine is_recfun_imp_function r a H f hrf };
    have hwdomf : π (w ∈ domain f) {
      have hdom_f : π (domain f = vimage_singleton r a) { refine is_recfun_domain r a H f hrf };
      refine ind_eq hdom_f (λ z, w ∈ z) hwvsa
    };
    have hpf : π (Pair w (fapply f w) ∈ f) { refine apply_Pair f w hfunc_f hwdomf };
    // Pair(w, body(w)) ∈ f since fapply(f,w) = body(w)
    have hpwbf : π (Pair w (H w (restrict g (vimage_singleton r w))) ∈ f)
      { refine ind_eq (eq_sym hfw_body) (λ z, Pair w z ∈ f) hpf };
    // p = Pair(w, body(w)) ∈ restrict(f, r⁻¹{b})
    rewrite hpeq;
    refine restrictI w (H w (restrict g (vimage_singleton r w))) f (vimage_singleton r b) hpwbf hwvs }
end;

// ===========================================================================
// is_recfun_functional: uniqueness of is_recfun
// ===========================================================================

opaque symbol is_recfun_functional (r : τ ι) (H : τ ι → τ ι → τ ι)
  (a : τ ι) (f g : τ ι) :
  π (wf_global r) →
  π (trans r) →
  π (is_recfun r a H f) →
  π (is_recfun r a H g) →
  π (f = g) ≔
begin
  assume r H a f g hwf htr hrf hrg;
  // Both f and g equal Lambda(r⁻¹{a}, ...)
  // f = Lambda(r⁻¹{a}, λ x. H(x, restrict(f, r⁻¹{x})))
  // g = Lambda(r⁻¹{a}, λ x. H(x, restrict(g, r⁻¹{x})))
  // By lam_cong, suffice to show ∀x∈r⁻¹{a}. H(x, restrict(f, r⁻¹{x})) = H(x, restrict(g, r⁻¹{x}))
  // This follows from restrict(f, r⁻¹{x}) = restrict(g, r⁻¹{x})
  // Which follows from is_recfun_equal (fapply(f,y) = fapply(g,y) for y ∈ r⁻¹{x})
  // Actually we can just use is_recfun_equal + subset_antisym on the restricts.

  // Actually, the simplest: f = Lambda(..._f) and g = Lambda(..._g).
  // By lam_cong (same domain r⁻¹{a}):
  have hf_eq : π (f = Lambda (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x))))
    { apply hrf };
  have hg_eq : π (g = Lambda (vimage_singleton r a) (λ x, H x (restrict g (vimage_singleton r x))))
    { apply hrg };
  // fapply(f,x) = fapply(g,x) for all x ∈ r⁻¹{a}
  // Using is_recfun_equal with a=a, b=a:
  have hfg : π (Ball (vimage_singleton r a) (λ x, fapply f x = fapply g x))
    { assume x hx;
      have hxa : π (Pair x a ∈ r) { refine vimage_singletonD x a r hx };
      refine is_recfun_equal r H a a f g hwf htr hrf hrg x hx hxa };
  // H(x, restrict(f, r⁻¹{x})) = fapply(f,x) = fapply(g,x) = H(x, restrict(g, r⁻¹{x}))
  have hlam_eq : π (Lambda (vimage_singleton r a) (λ x, H x (restrict f (vimage_singleton r x))) =
    Lambda (vimage_singleton r a) (λ x, H x (restrict g (vimage_singleton r x))))
    { refine lam_cong (vimage_singleton r a) (vimage_singleton r a)
        (λ x, H x (restrict f (vimage_singleton r x)))
        (λ x, H x (restrict g (vimage_singleton r x)))
        (eq_refl (vimage_singleton r a)) _;
      assume x hx;
      have hxa : π (Pair x a ∈ r) { refine vimage_singletonD x a r hx };
      // apply_recfun gives fapply(f,x) = H(x, restrict(f, r⁻¹{x}))
      have hfx : π (fapply f x = H x (restrict f (vimage_singleton r x)))
        { refine apply_recfun r a H f x hrf hxa };
      have hgx : π (fapply g x = H x (restrict g (vimage_singleton r x)))
        { refine apply_recfun r a H g x hrg hxa };
      have hfgx : π (fapply f x = fapply g x) { refine hfg x hx };
      rewrite left hfx; rewrite left hgx; apply hfgx };
  // f = Lambda(..._f) = Lambda(..._g) = g
  rewrite hf_eq; rewrite hg_eq; apply hlam_eq
end;

// ===========================================================================
// the_recfun_eq: is_recfun(r,a,H,f) → wf_global(r) → trans(r) → the_recfun(r,a,H) = f
// ===========================================================================

opaque symbol the_recfun_eq (r a : τ ι) (H : τ ι → τ ι → τ ι) (f : τ ι) :
  π (is_recfun r a H f) →
  π (wf_global r) →
  π (trans r) →
  π (the_recfun r a H = f) ≔
begin
  assume r a H f hrf hwf htr;
  // the_recfun(r,a,H) = The(is_recfun r a H) = ε(is_recfun r a H)
  // By εᵢ: if ∃f. is_recfun(r,a,H,f), then is_recfun(r,a,H,ε(is_recfun r a H))
  have hex : π (`∃ (g : τ ι), is_recfun r a H g) { refine ∃ᵢ f hrf };
  have hthe : π (is_recfun r a H (the_recfun r a H)) { refine εᵢ _ hex };
  refine is_recfun_functional r H a (the_recfun r a H) f hwf htr hthe hrf
end;

// ===========================================================================
// is_the_recfun: given a witness, the_recfun satisfies is_recfun
// ===========================================================================

opaque symbol is_the_recfun (r a : τ ι) (H : τ ι → τ ι → τ ι) (f : τ ι) :
  π (is_recfun r a H f) →
  π (wf_global r) →
  π (trans r) →
  π (is_recfun r a H (the_recfun r a H)) ≔
begin
  assume r a H f hrf hwf htr;
  have heq : π (the_recfun r a H = f) { refine the_recfun_eq r a H f hrf hwf htr };
  // is_recfun(r,a,H,f) and the_recfun = f, so is_recfun(r,a,H,the_recfun)
  refine ind_eq heq (λ z, is_recfun r a H z) hrf
end;

// ===========================================================================
// unfold_the_recfun: the main existence theorem
// wf_global(r) → trans(r) → is_recfun(r,a,H,the_recfun(r,a,H))
// ===========================================================================

opaque symbol unfold_the_recfun (r a : τ ι) (H : τ ι → τ ι → τ ι) :
  π (wf_global r) →
  π (trans r) →
  π (is_recfun r a H (the_recfun r a H)) ≔
begin
  assume r a H hwf htr;
  // By wf_global_induct on a with P(a) = is_recfun(r,a,H,the_recfun(r,a,H))
  refine wf_global_induct r
    (λ a, is_recfun r a H (the_recfun r a H))
    a hwf _;
  // Inductive step: for all x, (∀y. Pair(y,x)∈r → P(y)) → P(x)
  assume x ih;
  // ih : ∀y. Pair(y,x) ∈ r → is_recfun(r,y,H,the_recfun(r,y,H))
  // Construct f₀ = Lambda(r⁻¹{x}, λy. wftrec(r,y,H))
  // Show is_recfun(r,x,H,f₀), then use is_the_recfun.
  have hf0_is_recfun : π (is_recfun r x H (Lambda (vimage_singleton r x) (λ y, wftrec r y H))) {
    // Need: Lambda(r⁻¹{x}, λy. wftrec(r,y,H)) =
    //   Lambda(r⁻¹{x}, λy. H(y, restrict(Lambda(r⁻¹{x}, λz. wftrec(r,z,H)), r⁻¹{y})))
    // By lam_cong, for y ∈ r⁻¹{x}:
    //   wftrec(r,y,H) = H(y, restrict(Lambda(r⁻¹{x}, λz. wftrec(r,z,H)), r⁻¹{y}))
    refine lam_cong (vimage_singleton r x) (vimage_singleton r x)
      (λ y, wftrec r y H)
      (λ y, H y (restrict (Lambda (vimage_singleton r x) (λ z, wftrec r z H)) (vimage_singleton r y)))
      (eq_refl (vimage_singleton r x)) _;
    assume y hy;
    have hyx : π (Pair y x ∈ r) { refine vimage_singletonD y x r hy };
    // IH gives: is_recfun(r,y,H,the_recfun(r,y,H))
    have hrf_y : π (is_recfun r y H (the_recfun r y H)) { refine ih y hyx };
    // wftrec(r,y,H) = H(y, the_recfun(r,y,H)) by definition
    // Need: the_recfun(r,y,H) = restrict(Lambda(r⁻¹{x}, λz. wftrec(r,z,H)), r⁻¹{y})

    // Step 1: restrict(Lambda(r⁻¹{x}, λz. wftrec(r,z,H)), r⁻¹{y}) = Lambda(r⁻¹{y}, λz. wftrec(r,z,H))
    // by restrict_lam_eq, since r⁻¹{y} ⊆ r⁻¹{x} (by transitivity)
    have hvy_sub_vx : π (vimage_singleton r y ⊆ vimage_singleton r x) {
      assume z hz;
      have hzy : π (Pair z y ∈ r) { refine vimage_singletonD z y r hz };
      have hzx : π (Pair z x ∈ r) { refine transD r z y x htr hzy hyx };
      refine vimage_singletonI z x r hzx
    };
    have hrestr_eq : π (restrict (Lambda (vimage_singleton r x) (λ z, wftrec r z H)) (vimage_singleton r y) =
      Lambda (vimage_singleton r y) (λ z, wftrec r z H))
      { refine restrict_lam_eq (vimage_singleton r y) (vimage_singleton r x)
          (λ z, wftrec r z H) hvy_sub_vx };

    // Step 2: Show is_recfun(r,y,H,Lambda(r⁻¹{y}, λz. wftrec(r,z,H)))
    // by the same argument but for y. For z ∈ r⁻¹{y}:
    //   wftrec(r,z,H) = H(z, the_recfun(r,z,H)) [by def]
    //   need: the_recfun(r,z,H) = restrict(Lambda(r⁻¹{y}, λw. wftrec(r,w,H)), r⁻¹{z})
    //   restrict(Lambda(r⁻¹{y}, ...), r⁻¹{z}) = Lambda(r⁻¹{z}, λw. wftrec(r,w,H))
    //     by restrict_lam_eq (r⁻¹{z} ⊆ r⁻¹{y})
    //   is_recfun_cut on the_recfun(r,y,H) at z gives:
    //     restrict(the_recfun(r,y,H), r⁻¹{z}) = the_recfun(r,z,H)
    //   the_recfun(r,y,H) is the Lambda for y (from is_recfun), so its restrict at z =
    //     Lambda(r⁻¹{z}, ..wftrec..)
    //   Thus the_recfun(r,z,H) = Lambda(r⁻¹{z}, λw. wftrec(r,w,H))
    //   Done.
    //
    // Actually, more directly: use fun_extension / subset_antisym approach.
    // The key insight: we need the_recfun(r,y,H) = Lambda(r⁻¹{y}, λz. wftrec(r,z,H)).
    // From is_recfun(r,y,H,the_recfun(r,y,H)):
    //   the_recfun(r,y,H) = Lambda(r⁻¹{y}, λz. H(z, restrict(the_recfun(r,y,H), r⁻¹{z})))
    // Need: for z ∈ r⁻¹{y}, H(z, restrict(the_recfun(r,y,H), r⁻¹{z})) = wftrec(r,z,H) = H(z, the_recfun(r,z,H))
    // So need: restrict(the_recfun(r,y,H), r⁻¹{z}) = the_recfun(r,z,H)
    // This is exactly is_recfun_cut with:
    //   is_recfun(r,y,H,the_recfun(r,y,H)) [IH on y]
    //   is_recfun(r,z,H,the_recfun(r,z,H)) [IH on z, since Pair(z,x) ∈ r by trans]
    //   Pair(z,y) ∈ r

    // So: the_recfun(r,y,H) = Lambda(r⁻¹{y}, λz. wftrec(r,z,H))
    // Proof:
    have hthe_y_eq : π (the_recfun r y H = Lambda (vimage_singleton r y) (λ z, wftrec r z H)) {
      // the_recfun(r,y,H) = Lambda(r⁻¹{y}, λz. H(z, restrict(the_recfun(r,y,H), r⁻¹{z})))
      have hrf_unf : π (the_recfun r y H = Lambda (vimage_singleton r y)
        (λ z, H z (restrict (the_recfun r y H) (vimage_singleton r z))))
        { apply hrf_y };
      // For z ∈ r⁻¹{y}: H(z, restrict(the_recfun(r,y,H), r⁻¹{z})) = H(z, the_recfun(r,z,H)) = wftrec(r,z,H)
      have hbody_eq : π (Lambda (vimage_singleton r y)
        (λ z, H z (restrict (the_recfun r y H) (vimage_singleton r z))) =
        Lambda (vimage_singleton r y) (λ z, wftrec r z H))
        { refine lam_cong (vimage_singleton r y) (vimage_singleton r y)
            (λ z, H z (restrict (the_recfun r y H) (vimage_singleton r z)))
            (λ z, wftrec r z H)
            (eq_refl (vimage_singleton r y)) _;
          assume z hz;
          have hzy : π (Pair z y ∈ r) { refine vimage_singletonD z y r hz };
          have hzx : π (Pair z x ∈ r) { refine transD r z y x htr hzy hyx };
          // IH on z: is_recfun(r,z,H,the_recfun(r,z,H))
          have hrf_z : π (is_recfun r z H (the_recfun r z H)) { refine ih z hzx };
          // is_recfun_cut: restrict(the_recfun(r,y,H), r⁻¹{z}) = the_recfun(r,z,H)
          have hcut : π (restrict (the_recfun r y H) (vimage_singleton r z) = the_recfun r z H)
            { refine is_recfun_cut r H y z (the_recfun r y H) (the_recfun r z H) hwf htr hrf_y hrf_z hzy };
          // H(z, restrict(the_recfun(r,y,H), r⁻¹{z})) = H(z, the_recfun(r,z,H)) = wftrec(r,z,H)
          refine feq (H z) hcut };
      rewrite hrf_unf; apply hbody_eq
    };

    // Now: wftrec(r,y,H) = H(y, the_recfun(r,y,H)) [by def]
    //     = H(y, Lambda(r⁻¹{y}, λz. wftrec(r,z,H))) [by hthe_y_eq]
    //     = H(y, restrict(Lambda(r⁻¹{x}, λz. wftrec(r,z,H)), r⁻¹{y})) [by hrestr_eq, backwards]
    have hgoal : π (H y (the_recfun r y H) =
      H y (restrict (Lambda (vimage_singleton r x) (λ z, wftrec r z H)) (vimage_singleton r y)))
      { rewrite hthe_y_eq;
        rewrite hrestr_eq;
        reflexivity };
    apply hgoal
  };
  refine is_the_recfun r x H
    (Lambda (vimage_singleton r x) (λ y, wftrec r y H))
    hf0_is_recfun hwf htr
end;

// ===========================================================================
// the_recfun_cut2: restrict(the_recfun(r,a,H), r⁻¹{b}) = the_recfun(r,b,H)
// ===========================================================================

opaque symbol the_recfun_cut2 (r a b : τ ι) (H : τ ι → τ ι → τ ι) :
  π (wf_global r) →
  π (trans r) →
  π (Pair b a ∈ r) →
  π (restrict (the_recfun r a H) (vimage_singleton r b) = the_recfun r b H) ≔
begin
  assume r a b H hwf htr hba;
  refine is_recfun_cut r H a b (the_recfun r a H) (the_recfun r b H) hwf htr
    (unfold_the_recfun r a H hwf htr) (unfold_the_recfun r b H hwf htr) hba
end;

// ===========================================================================
// wftrec_eq: wftrec(r,a,H) = H(a, Lambda(r⁻¹{a}, λx. wftrec(r,x,H)))
// ===========================================================================

opaque symbol wftrec_eq (r a : τ ι) (H : τ ι → τ ι → τ ι) :
  π (wf_global r) →
  π (trans r) →
  π (wftrec r a H = H a (Lambda (vimage_singleton r a) (λ x, wftrec r x H))) ≔
begin
  assume r a H hwf htr;
  // wftrec(r,a,H) = H(a, the_recfun(r,a,H)) by definition
  // Need: the_recfun(r,a,H) = Lambda(r⁻¹{a}, λx. wftrec(r,x,H))
  have hunf : π (is_recfun r a H (the_recfun r a H))
    { refine unfold_the_recfun r a H hwf htr };
  // is_recfun gives: the_recfun(r,a,H) = Lambda(r⁻¹{a}, λx. H(x, restrict(the_recfun(r,a,H), r⁻¹{x})))
  have hthe_eq : π (the_recfun r a H = Lambda (vimage_singleton r a)
    (λ x, H x (restrict (the_recfun r a H) (vimage_singleton r x))))
    { apply hunf };
  // For x ∈ r⁻¹{a}: H(x, restrict(the_recfun(r,a,H), r⁻¹{x})) = H(x, the_recfun(r,x,H)) = wftrec(r,x,H)
  // by the_recfun_cut2
  have hlam_eq : π (Lambda (vimage_singleton r a)
    (λ x, H x (restrict (the_recfun r a H) (vimage_singleton r x))) =
    Lambda (vimage_singleton r a) (λ x, wftrec r x H))
    { refine lam_cong (vimage_singleton r a) (vimage_singleton r a)
        (λ x, H x (restrict (the_recfun r a H) (vimage_singleton r x)))
        (λ x, wftrec r x H)
        (eq_refl (vimage_singleton r a)) _;
      assume x hx;
      have hxa : π (Pair x a ∈ r) { refine vimage_singletonD x a r hx };
      have hcut : π (restrict (the_recfun r a H) (vimage_singleton r x) = the_recfun r x H)
        { refine the_recfun_cut2 r a x H hwf htr hxa };
      refine feq (H x) hcut };
  // the_recfun(r,a,H) = Lambda(r⁻¹{a}, λx. wftrec(r,x,H))
  have hthe_lam : π (the_recfun r a H = Lambda (vimage_singleton r a) (λ x, wftrec r x H))
    { rewrite hthe_eq; apply hlam_eq };
  // wftrec(r,a,H) = H(a, the_recfun(r,a,H)) = H(a, Lambda(r⁻¹{a}, λx. wftrec(r,x,H)))
  refine feq (H a) hthe_lam
end;

// ===========================================================================
// wfrec_eq: wfrec(r,a,H) = H(a, Lambda(r⁻¹{a}, λx. wfrec(r,x,H)))
// ===========================================================================

// Helper: r⁻¹{a} ⊆ trancl(r)⁻¹{a}
opaque symbol vimage_r_sub_trancl (r a : τ ι) :
  π (vimage_singleton r a ⊆ vimage_singleton (trancl r) a) ≔
begin
  assume r a x hx;
  have hxa : π (Pair x a ∈ r) { refine vimage_singletonD x a r hx };
  have hxatc : π (Pair x a ∈ trancl r) { refine r_into_trancl x a r hxa };
  refine vimage_singletonI x a (trancl r) hxatc
end;

opaque symbol wfrec_eq (r a : τ ι) (H : τ ι → τ ι → τ ι) :
  π (wf_global r) →
  π (wfrec r a H = H a (Lambda (vimage_singleton r a) (λ x, wfrec r x H))) ≔
begin
  assume r a H hwf;
  // wfrec(r,a,H) = wftrec(trancl(r), a, λ x f. H(x, restrict(f, r⁻¹{x})))
  // By wftrec_eq (with wf_global_trancl + trans_trancl):
  // = (λ x f. H(x, restrict(f, r⁻¹{x})))(a, Lambda(trancl(r)⁻¹{a}, λ x. wftrec(trancl(r), x, ...)))
  // = H(a, restrict(Lambda(trancl(r)⁻¹{a}, λ x. wftrec(trancl(r), x, ...)), r⁻¹{a}))
  have hwf_tc : π (wf_global (trancl r)) { refine wf_global_trancl r hwf };
  have htr_tc : π (trans (trancl r)) { refine trans_trancl r };
  have hstep : π (wftrec (trancl r) a (λ x f, H x (restrict f (vimage_singleton r x))) =
    (λ x f, H x (restrict f (vimage_singleton r x))) a
      (Lambda (vimage_singleton (trancl r) a)
        (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y))))))
    { refine wftrec_eq (trancl r) a (λ x f, H x (restrict f (vimage_singleton r x))) hwf_tc htr_tc };
  // This simplifies to:
  // wfrec(r,a,H) = H(a, restrict(Lambda(trancl(r)⁻¹{a}, λx. wfrec(r,x,H)), r⁻¹{a}))
  // By restrict_lam_eq (r⁻¹{a} ⊆ trancl(r)⁻¹{a}):
  // = H(a, Lambda(r⁻¹{a}, λx. wfrec(r,x,H)))
  have hrestr : π (restrict (Lambda (vimage_singleton (trancl r) a)
    (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y)))))
    (vimage_singleton r a) =
    Lambda (vimage_singleton r a)
      (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y)))))
    { refine restrict_lam_eq (vimage_singleton r a) (vimage_singleton (trancl r) a)
        (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y))))
        (vimage_r_sub_trancl r a) };
  // wfrec(r,a,H) = wftrec(trancl(r), a, ...)
  // hstep gives the unfolding, hrestr simplifies the restrict
  // The result of hstep is:
  // wftrec(...) = H(a, restrict(Lambda(trancl(r)⁻¹{a}, λx. wftrec(...,x,...)), r⁻¹{a}))
  // Rewriting with hrestr:
  // = H(a, Lambda(r⁻¹{a}, λx. wftrec(trancl(r), x, λy f. H(y, restrict(f, r⁻¹{y})))))
  // = H(a, Lambda(r⁻¹{a}, λx. wfrec(r,x,H)))  [by def of wfrec]
  // Goal: wfrec r a H = H a (Lambda(r⁻¹{a}, λx. wfrec(r,x,H)))
  // Change to wftrec form (wfrec is defined as wftrec on trancl)
  // hstep: wftrec(tc, a, F) = F a (Lambda(tc⁻¹{a}, λx. wftrec(tc, x, F)))
  //   where F = λ x f. H(x, restrict(f, r⁻¹{x}))
  // So wftrec(tc, a, F) = H(a, restrict(Lambda(tc⁻¹{a}, ...), r⁻¹{a}))
  // hrestr: restrict(Lambda(tc⁻¹{a}, ...), r⁻¹{a}) = Lambda(r⁻¹{a}, ...)
  // Combine: wftrec(tc, a, F) = H(a, Lambda(r⁻¹{a}, ...))
  have hcombined : π (wftrec (trancl r) a (λ x f, H x (restrict f (vimage_singleton r x))) =
    H a (Lambda (vimage_singleton r a)
      (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y))))))
  {
    // hstep says wftrec = F a (Lambda ...) where F = λ x f. H(x, restrict(f, r⁻¹{x}))
    // After beta: = H(a, restrict(Lambda(tc⁻¹{a}, body), r⁻¹{a}))
    // hrestr: restrict(Lambda(tc⁻¹{a}, body), r⁻¹{a}) = Lambda(r⁻¹{a}, body)
    // So: wftrec = H(a, Lambda(r⁻¹{a}, body))
    have h1 : π ((λ x f, H x (restrict f (vimage_singleton r x))) a
      (Lambda (vimage_singleton (trancl r) a)
        (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y))))) =
      H a (restrict (Lambda (vimage_singleton (trancl r) a)
        (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y)))))
        (vimage_singleton r a)))
    { reflexivity };
    have h2 : π ((λ x f, H x (restrict f (vimage_singleton r x))) a
      (Lambda (vimage_singleton (trancl r) a)
        (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y))))) =
      H a (Lambda (vimage_singleton r a)
        (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y))))))
    { rewrite h1; rewrite hrestr; reflexivity };
    rewrite hstep; apply h2
  };
  change π (wftrec (trancl r) a (λ x f, H x (restrict f (vimage_singleton r x))) =
    H a (Lambda (vimage_singleton r a)
      (λ x, wftrec (trancl r) x (λ y f, H y (restrict f (vimage_singleton r y))))));
  apply hcombined
end;
