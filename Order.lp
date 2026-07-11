// Order: Partial and Total Orderings — Basic Definitions and Properties
//
// Isabelle source: Order.thy
// Results from Kunen's "Set Theory: an Introduction to Independence Proofs"
// Chapter 1, section 6. Additional definitions and lemmas for reflexive orders.
//
// Defines: part_ord, linear, tot_ord, well_ord, mono_map, ord_iso, pred,
//          ord_iso_map, first, preorder_on, partial_order_on

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func
             ZF.Fixedpt ZF.Trancl ZF.WF ZF.Perm;

// ===========================================================================
// Section: Basic Definitions
// ===========================================================================

// trans_on(A, r): r is transitive on A
// Isabelle: trans[A](r) ≡ ∀x∈A. ∀y∈A. ∀z∈A. ⟨x,y⟩∈r → ⟨y,z⟩∈r → ⟨x,z⟩∈r
constant symbol trans_on (A r : τ ι) : Prop;
constant symbol trans_on_def (A r : τ ι) :
  π (trans_on A r = Ball A (λ x, Ball A (λ y, Ball A (λ z,
    Pair x y ∈ r ⇒ Pair y z ∈ r ⇒ Pair x z ∈ r))));

// trans_onD: elimination
opaque symbol trans_onD (A r x y z : τ ι) :
  π (trans_on A r) → π (x ∈ A) → π (y ∈ A) → π (z ∈ A) →
  π (Pair x y ∈ r) → π (Pair y z ∈ r) → π (Pair x z ∈ r) ≔
begin
  assume A r x y z h hx hy hz hxy hyz;
  have h' : π (Ball A (λ x2, Ball A (λ y2, Ball A (λ z2,
      Pair x2 y2 ∈ r ⇒ Pair y2 z2 ∈ r ⇒ Pair x2 z2 ∈ r))))
    { refine ind_eq (eq_sym (trans_on_def A r)) (λ p, p) h };
  refine h' x hx y hy z hz hxy hyz
end;

// trans_onI: introduction
opaque symbol trans_onI (A r : τ ι) :
  (Π (x : τ ι), π (x ∈ A) → Π (y : τ ι), π (y ∈ A) → Π (z : τ ι), π (z ∈ A) →
   π (Pair x y ∈ r) → π (Pair y z ∈ r) → π (Pair x z ∈ r)) →
  π (trans_on A r) ≔
begin
  assume A r h;
  rewrite trans_on_def;
  assume x hx y hy z hz hxy hyz;
  refine h x hx y hy z hz hxy hyz
end;

// irrefl_on(A, r): r is irreflexive on A
// Isabelle: irrefl(A,r) ≡ ∀x∈A. ⟨x,x⟩ ∉ r
constant symbol irrefl_on (A r : τ ι) : Prop;
constant symbol irrefl_on_def (A r : τ ι) :
  π (irrefl_on A r = Ball A (λ x, Pair x x ∉ r));

// irrefl_onD: elimination
opaque symbol irrefl_onD (A r x : τ ι) :
  π (irrefl_on A r) → π (x ∈ A) → π (Pair x x ∉ r) ≔
begin
  assume A r x h hx;
  have h' : π (Ball A (λ y, Pair y y ∉ r))
    { refine ind_eq (eq_sym (irrefl_on_def A r)) (λ p, p) h };
  refine h' x hx
end;

// irrefl_onI: introduction
opaque symbol irrefl_onI (A r : τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Pair x x ∉ r)) → π (irrefl_on A r) ≔
begin
  assume A r h;
  rewrite irrefl_on_def;
  assume x hx;
  refine h x hx
end;

// asym_on(r ∩ A×A): r is asymmetric when restricted to A
// We won't define asym_on separately — use inline

// refl_on(A, r): r is reflexive on A
// Isabelle: refl(A,r) ≡ ∀x∈A. ⟨x,x⟩ ∈ r
constant symbol refl_on (A r : τ ι) : Prop;
constant symbol refl_on_def (A r : τ ι) :
  π (refl_on A r = Ball A (λ x, Pair x x ∈ r));

// refl_onD: elimination
opaque symbol refl_onD (A r x : τ ι) :
  π (refl_on A r) → π (x ∈ A) → π (Pair x x ∈ r) ≔
begin
  assume A r x h hx;
  have h' : π (Ball A (λ y, Pair y y ∈ r))
    { refine ind_eq (eq_sym (refl_on_def A r)) (λ p, p) h };
  refine h' x hx
end;

// refl_onI: introduction
opaque symbol refl_onI (A r : τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Pair x x ∈ r)) → π (refl_on A r) ≔
begin
  assume A r h;
  rewrite refl_on_def;
  assume x hx;
  refine h x hx
end;

// part_ord(A,r): strict partial ordering on A
// Isabelle: part_ord(A,r) ≡ irrefl(A,r) ∧ trans[A](r)
constant symbol part_ord (A r : τ ι) : Prop;
constant symbol part_ord_def (A r : τ ι) :
  π (part_ord A r = (irrefl_on A r ∧ trans_on A r));

// part_ordD: unfold
opaque symbol part_ordD (A r : τ ι) :
  π (part_ord A r) → π (irrefl_on A r ∧ trans_on A r) ≔
begin
  assume A r h;
  refine ind_eq (eq_sym (part_ord_def A r)) (λ p, p) h
end;

// linear(A,r): strict total ordering property
// Isabelle: linear(A,r) ≡ ∀x∈A. ∀y∈A. ⟨x,y⟩∈r ∨ x=y ∨ ⟨y,x⟩∈r
constant symbol linear (A r : τ ι) : Prop;
constant symbol linear_def (A r : τ ι) :
  π (linear A r = Ball A (λ x, Ball A (λ y, Pair x y ∈ r ∨ (x = y ∨ Pair y x ∈ r))));

// linearD: applied elimination
opaque symbol linearD (A r x y : τ ι) :
  π (linear A r) → π (x ∈ A) → π (y ∈ A) →
  π (Pair x y ∈ r ∨ (x = y ∨ Pair y x ∈ r)) ≔
begin
  assume A r x y h hx hy;
  have h' : π (Ball A (λ x2, Ball A (λ y2, Pair x2 y2 ∈ r ∨ (x2 = y2 ∨ Pair y2 x2 ∈ r))))
    { refine ind_eq (eq_sym (linear_def A r)) (λ p, p) h };
  refine h' x hx y hy
end;

// linearI: introduction
opaque symbol linearI (A r : τ ι) :
  (Π (x : τ ι), π (x ∈ A) → Π (y : τ ι), π (y ∈ A) →
   π (Pair x y ∈ r ∨ (x = y ∨ Pair y x ∈ r))) →
  π (linear A r) ≔
begin
  assume A r h;
  rewrite linear_def;
  assume x hx y hy;
  refine h x hx y hy
end;

// tot_ord(A,r): strict total ordering
// Isabelle: tot_ord(A,r) ≡ part_ord(A,r) ∧ linear(A,r)
constant symbol tot_ord (A r : τ ι) : Prop;
constant symbol tot_ord_def (A r : τ ι) :
  π (tot_ord A r = (part_ord A r ∧ linear A r));

// tot_ordD: unfold
opaque symbol tot_ordD (A r : τ ι) :
  π (tot_ord A r) → π (part_ord A r ∧ linear A r) ≔
begin
  assume A r h;
  refine ind_eq (eq_sym (tot_ord_def A r)) (λ p, p) h
end;

// well_ord(A,r): well-ordering
// Isabelle: well_ord(A,r) ≡ tot_ord(A,r) ∧ wf[A](r)
constant symbol well_ord (A r : τ ι) : Prop;
constant symbol well_ord_def (A r : τ ι) :
  π (well_ord A r = (tot_ord A r ∧ wf A r));

// well_ordD: unfold
opaque symbol well_ordD (A r : τ ι) :
  π (well_ord A r) → π (tot_ord A r ∧ wf A r) ≔
begin
  assume A r h;
  refine ind_eq (eq_sym (well_ord_def A r)) (λ p, p) h
end;

// mono_map(A,r,B,s): order-preserving maps from (A,r) to (B,s)
// Isabelle: {f ∈ A→B. ∀x∈A. ∀y∈A. ⟨x,y⟩∈r → ⟨f`x,f`y⟩∈s}
constant symbol mono_map (A r B s : τ ι) : τ ι;
constant symbol mono_map_def (A r B s : τ ι) :
  π (mono_map A r B s =
     Collect (Pi A (λ _, B))
       (λ f, Ball A (λ x, Ball A (λ y,
         Pair x y ∈ r ⇒ Pair (fapply f x) (fapply f y) ∈ s))));

// ord_iso(A,r,B,s): order isomorphisms
// Isabelle: {f ∈ bij(A,B). ∀x∈A. ∀y∈A. ⟨x,y⟩∈r ↔ ⟨f`x,f`y⟩∈s}
constant symbol ord_iso (A r B s : τ ι) : τ ι;
constant symbol ord_iso_def (A r B s : τ ι) :
  π (ord_iso A r B s =
     Collect (bij A B)
       (λ f, Ball A (λ x, Ball A (λ y,
         (Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ s)))));

// pred(A,x,r): set of predecessors of x in A under r
// Isabelle: pred(A,x,r) ≡ {y ∈ A. ⟨y,x⟩∈r}
constant symbol pred (A x r : τ ι) : τ ι;
constant symbol pred_def (A x r : τ ι) :
  π (pred A x r = Collect A (λ y, Pair y x ∈ r));

// ord_iso_map(A,r,B,s): construction for the linearity theorem
// Isabelle: ⋃x∈A. ⋃y∈B. ⋃f∈ord_iso(pred(A,x,r),r,pred(B,y,s),s). {⟨x,y⟩}
constant symbol ord_iso_map (A r B s : τ ι) : τ ι;
constant symbol ord_iso_map_def (A r B s : τ ι) :
  π (ord_iso_map A r B s =
     Union (RepFun A (λ x,
       Union (RepFun B (λ y,
         Union (RepFun (ord_iso (pred A x r) r (pred B y s) s)
           (λ f, cons (Pair x y) empty)))))));

// first(u, X, R): u is the first element of X under R
// Isabelle: first(u,X,R) ≡ u ∈ X ∧ (∀v∈X. v ≠ u → ⟨u,v⟩ ∈ R)
constant symbol first (u X R : τ ι) : Prop;
constant symbol first_def (u X R : τ ι) :
  π (first u X R = (u ∈ X ∧ Ball X (λ v, v ≠ u ⇒ Pair u v ∈ R)));

// firstD: unfold
opaque symbol firstD (u X R : τ ι) :
  π (first u X R) → π (u ∈ X ∧ Ball X (λ v, v ≠ u ⇒ Pair u v ∈ R)) ≔
begin
  assume u X R h;
  refine ind_eq (eq_sym (first_def u X R)) (λ p, p) h
end;

// preorder_on(A, r): reflexive and transitive on A
constant symbol preorder_on (A r : τ ι) : Prop;
constant symbol preorder_on_def (A r : τ ι) :
  π (preorder_on A r = (refl_on A r ∧ trans_on A r));

// partial_order_on(A, r): preorder + antisymmetric
constant symbol partial_order_on (A r : τ ι) : Prop;
constant symbol partial_order_on_def (A r : τ ι) :
  π (partial_order_on A r = (preorder_on A r ∧ antisym r));

// ===========================================================================
// Section: Immediate Consequences of the Definitions
// ===========================================================================

// part_ord_Imp_asym: part_ord(A,r) → asym(r ∩ A×A)
// Isabelle: "part_ord(A,r) ⟹ asym(r ∩ A*A)"
// asym means: ∀x y. ⟨x,y⟩ ∈ s → ⟨y,x⟩ ∉ s
opaque symbol part_ord_Imp_asym (A r : τ ι) :
  π (part_ord A r) →
  π (`∀ (x : τ ι), `∀ (y : τ ι),
    Pair x y ∈ Int r (Sigma A (λ _, A)) ⇒ Pair y x ∉ Int r (Sigma A (λ _, A))) ≔
begin
  assume A r hpo x y hxy hyx;
  have hirr : π (irrefl_on A r) { refine ∧ₑ₁ (part_ordD A r hpo) };
  have htr : π (trans_on A r) { refine ∧ₑ₂ (part_ordD A r hpo) };
  // From hxy: Pair(x,y) ∈ r ∩ A×A, get Pair(x,y) ∈ r and x ∈ A, y ∈ A
  have hxyr : π (Pair x y ∈ r) { refine IntD1 (Pair x y) r (Sigma A (λ _, A)) hxy };
  have hxyS : π (Pair x y ∈ Sigma A (λ _, A)) { refine IntD2 (Pair x y) r (Sigma A (λ _, A)) hxy };
  have hxA_bex : π (Bex A (λ a, Bex A (λ b, Pair x y = Pair a b)))
    { refine SigmaE (Pair x y) A (λ _, A) hxyS };
  // Extract x ∈ A
  have hyxr : π (Pair y x ∈ r) { refine IntD1 (Pair y x) r (Sigma A (λ _, A)) hyx };
  have hyxS : π (Pair y x ∈ Sigma A (λ _, A)) { refine IntD2 (Pair y x) r (Sigma A (λ _, A)) hyx };
  // From SigmaE extract membership
  refine ∃ₑ hxA_bex _;
  assume a ha;
  have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
  have hrest : π (Bex A (λ b, Pair x y = Pair a b)) { refine ∧ₑ₂ ha };
  refine ∃ₑ hrest _;
  assume b hb;
  have hbA : π (b ∈ A) { refine ∧ₑ₁ hb };
  have hpeq : π (Pair x y = Pair a b) { refine ∧ₑ₂ hb };
  have hxa : π (x = a) { refine Pair_inject1 x y a b hpeq };
  have hyb : π (y = b) { refine Pair_inject2 x y a b hpeq };
  // x ∈ A, y ∈ A
  have hxA : π (x ∈ A) { refine ind_eq hxa (λ z, z ∈ A) haA };
  have hyA : π (y ∈ A) { refine ind_eq hyb (λ z, z ∈ A) hbA };
  // By trans: Pair(x,y) ∈ r and Pair(y,x) ∈ r gives Pair(x,x) ∈ r
  have hxx : π (Pair x x ∈ r)
    { refine trans_onD A r x y x htr hxA hyA hxA hxyr hyxr };
  // By irrefl: Pair(x,x) ∉ r — contradiction
  refine irrefl_onD A r x hirr hxA hxx
end;

// linearE: linear(A,r) → x ∈ A → y ∈ A → (Pair(x,y) ∈ r → P) → (x = y → P) → (Pair(y,x) ∈ r → P) → P
opaque symbol linearE (A r : τ ι) (x y : τ ι) (P : Prop) :
  π (linear A r) → π (x ∈ A) → π (y ∈ A) →
  (π (Pair x y ∈ r) → π P) →
  (π (x = y) → π P) →
  (π (Pair y x ∈ r) → π P) →
  π P ≔
begin
  assume A r x y P hlin hxA hyA hxy heq hyx;
  have htri : π (Pair x y ∈ r ∨ (x = y ∨ Pair y x ∈ r))
    { refine linearD A r x y hlin hxA hyA };
  refine ∨ₑ htri _ _
  { assume h; refine hxy h }
  { assume h2;
    refine ∨ₑ h2 _ _
    { assume h; refine heq h }
    { assume h; refine hyx h } }
end;

// ===========================================================================
// Section: General properties of well_ord
// ===========================================================================

// well_ordI: wf(A,r) → linear(A,r) → well_ord(A,r)
// This is the Isabelle theorem, but our well_ord = tot_ord ∧ wf
// We need: irrefl + trans from wf + linear
// wf_on_not_refl equivalent: wf(A,r) → x ∈ A → Pair(x,x) ∉ r
opaque symbol wf_not_refl (A r : τ ι) (x : τ ι) :
  π (wf A r) → π (x ∈ A) → π (Pair x x ∉ r) ≔
begin
  assume A r x hwf hxA hxx;
  // Consider Z = {x}. Z ⊆ A, Z ≠ empty.
  have hZsub : π (cons x empty ⊆ A) {
    assume z hz;
    have hzx : π (z = x ∨ z ∈ empty) { refine ∧ₑ₁ (cons_iff z x empty) hz };
    refine ∨ₑ hzx _ _
    { assume heq; rewrite heq; apply hxA }
    { assume he; refine ⊥ₑ (emptyE z he) }
  };
  have hZne : π (cons x empty ≠ empty) {
    refine ne_empty (cons x empty) x (consI1 x empty)
  };
  have hmin : π (Bex (cons x empty) (λ x0, Ball (cons x empty) (λ y, Pair y x0 ∉ r)))
    { refine wfD A r hwf (cons x empty) hZsub hZne };
  refine ∃ₑ hmin _;
  assume x0 hx0;
  have hx0Z : π (x0 ∈ cons x empty) { refine ∧ₑ₁ hx0 };
  have hx0min : π (Ball (cons x empty) (λ y, Pair y x0 ∉ r)) { refine ∧ₑ₂ hx0 };
  // x0 ∈ {x} so x0 = x or x0 ∈ ∅
  have hx0x : π (x0 = x ∨ x0 ∈ empty) { refine ∧ₑ₁ (cons_iff x0 x empty) hx0Z };
  refine ∨ₑ hx0x _ _
  { assume heq;
    // Pair(x, x0) ∉ r
    have h : π (Pair x x0 ∉ r) { refine hx0min x (consI1 x empty) };
    have hxx2 : π (Pair x x0 ∈ r)
      { refine ind_eq heq (λ z, Pair x z ∈ r) hxx };
    refine h hxx2 }
  { assume he; refine ⊥ₑ (emptyE x0 he) }
end;

// wf_asym: wf(A,r) → x ∈ A → y ∈ A → Pair(x,y) ∈ r → Pair(y,x) ∉ r
opaque symbol wf_asym (A r x y : τ ι) :
  π (wf A r) → π (x ∈ A) → π (y ∈ A) →
  π (Pair x y ∈ r) → π (Pair y x ∉ r) ≔
begin
  assume A r x y hwf hxA hyA hxy hyx;
  // Consider Z = {x, y}. Z ⊆ A, Z ≠ empty.
  have hZsub : π (cons x (cons y empty) ⊆ A) {
    assume z hz;
    have hzd : π (z = x ∨ z ∈ cons y empty) { refine ∧ₑ₁ (cons_iff z x (cons y empty)) hz };
    refine ∨ₑ hzd _ _
    { assume heq; rewrite heq; apply hxA }
    { assume hzy;
      have hzd2 : π (z = y ∨ z ∈ empty) { refine ∧ₑ₁ (cons_iff z y empty) hzy };
      refine ∨ₑ hzd2 _ _
      { assume heq; rewrite heq; apply hyA }
      { assume he; refine ⊥ₑ (emptyE z he) } }
  };
  have hZne : π (cons x (cons y empty) ≠ empty) {
    refine ne_empty (cons x (cons y empty)) x (consI1 x (cons y empty))
  };
  have hmin : π (Bex (cons x (cons y empty)) (λ x0, Ball (cons x (cons y empty)) (λ z, Pair z x0 ∉ r)))
    { refine wfD A r hwf (cons x (cons y empty)) hZsub hZne };
  refine ∃ₑ hmin _;
  assume x0 hx0;
  have hx0Z : π (x0 ∈ cons x (cons y empty)) { refine ∧ₑ₁ hx0 };
  have hx0min : π (Ball (cons x (cons y empty)) (λ z, Pair z x0 ∉ r)) { refine ∧ₑ₂ hx0 };
  have hx0d : π (x0 = x ∨ x0 ∈ cons y empty) { refine ∧ₑ₁ (cons_iff x0 x (cons y empty)) hx0Z };
  have hxZ : π (x ∈ cons x (cons y empty)) { refine consI1 x (cons y empty) };
  have hyZ : π (y ∈ cons x (cons y empty)) { refine consI2 y x (cons y empty) (consI1 y empty) };
  refine ∨ₑ hx0d _ _
  { assume hx0x;
    // x0 = x, so Pair(y, x0) ∉ r, i.e., Pair(y, x) ∉ r
    have h : π (Pair y x0 ∉ r) { refine hx0min y hyZ };
    have hyx2 : π (Pair y x0 ∈ r) { refine ind_eq hx0x (λ z, Pair y z ∈ r) hyx };
    refine h hyx2 }
  { assume hx0y_mem;
    have hx0d2 : π (x0 = y ∨ x0 ∈ empty) { refine ∧ₑ₁ (cons_iff x0 y empty) hx0y_mem };
    refine ∨ₑ hx0d2 _ _
    { assume hx0y;
      // x0 = y, so Pair(x, x0) ∉ r, i.e., Pair(x, y) ∉ r
      have h : π (Pair x x0 ∉ r) { refine hx0min x hxZ };
      have hxy2 : π (Pair x x0 ∈ r) { refine ind_eq hx0y (λ z, Pair x z ∈ r) hxy };
      refine h hxy2 }
    { assume he; refine ⊥ₑ (emptyE x0 he) } }
end;

// wf_chain3: wf(A,r) → x ∈ A → y ∈ A → z ∈ A →
//   Pair(x,y) ∈ r → Pair(y,z) ∈ r → Pair(z,x) ∉ r
opaque symbol wf_chain3 (A r x y z : τ ι) :
  π (wf A r) → π (x ∈ A) → π (y ∈ A) → π (z ∈ A) →
  π (Pair x y ∈ r) → π (Pair y z ∈ r) → π (Pair z x ∉ r) ≔
begin
  assume A r x y z hwf hxA hyA hzA hxy hyz hzx;
  // Z = {x, y, z}
  have hxZ : π (x ∈ cons x (cons y (cons z empty)))
    { refine consI1 x (cons y (cons z empty)) };
  have hyZ : π (y ∈ cons x (cons y (cons z empty)))
    { refine consI2 y x (cons y (cons z empty)) (consI1 y (cons z empty)) };
  have hzZ : π (z ∈ cons x (cons y (cons z empty)))
    { refine consI2 z x (cons y (cons z empty)) (consI2 z y (cons z empty) (consI1 z empty)) };
  have hZsub : π (cons x (cons y (cons z empty)) ⊆ A) {
    assume w hw;
    have hwd : π (w = x ∨ w ∈ cons y (cons z empty)) { refine ∧ₑ₁ (cons_iff w x (cons y (cons z empty))) hw };
    refine ∨ₑ hwd _ _
    { assume heq; rewrite heq; apply hxA }
    { assume hw2;
      have hwd2 : π (w = y ∨ w ∈ cons z empty) { refine ∧ₑ₁ (cons_iff w y (cons z empty)) hw2 };
      refine ∨ₑ hwd2 _ _
      { assume heq; rewrite heq; apply hyA }
      { assume hw3;
        have hwd3 : π (w = z ∨ w ∈ empty) { refine ∧ₑ₁ (cons_iff w z empty) hw3 };
        refine ∨ₑ hwd3 _ _
        { assume heq; rewrite heq; apply hzA }
        { assume he; refine ⊥ₑ (emptyE w he) } } }
  };
  have hZne : π (cons x (cons y (cons z empty)) ≠ empty) {
    refine ne_empty (cons x (cons y (cons z empty))) x hxZ
  };
  have hmin : π (Bex (cons x (cons y (cons z empty)))
    (λ x0, Ball (cons x (cons y (cons z empty))) (λ w, Pair w x0 ∉ r)))
    { refine wfD A r hwf (cons x (cons y (cons z empty))) hZsub hZne };
  refine ∃ₑ hmin _;
  assume x0 hx0;
  have hx0Z : π (x0 ∈ cons x (cons y (cons z empty))) { refine ∧ₑ₁ hx0 };
  have hx0min : π (Ball (cons x (cons y (cons z empty))) (λ w, Pair w x0 ∉ r)) { refine ∧ₑ₂ hx0 };
  // x0 is one of x, y, z. Each case leads to contradiction.
  have hx0d : π (x0 = x ∨ x0 ∈ cons y (cons z empty)) { refine ∧ₑ₁ (cons_iff x0 x (cons y (cons z empty))) hx0Z };
  refine ∨ₑ hx0d _ _
  { assume hx0x;
    // x0 = x: Pair(z, x0) ∉ r means Pair(z, x) ∉ r — but we have hzx
    have h : π (Pair z x0 ∉ r) { refine hx0min z hzZ };
    have hzx2 : π (Pair z x0 ∈ r) { refine ind_eq hx0x (λ w, Pair z w ∈ r) hzx };
    refine h hzx2 }
  { assume hx0r;
    have hx0d2 : π (x0 = y ∨ x0 ∈ cons z empty) { refine ∧ₑ₁ (cons_iff x0 y (cons z empty)) hx0r };
    refine ∨ₑ hx0d2 _ _
    { assume hx0y;
      // x0 = y: Pair(x, x0) ∉ r means Pair(x, y) ∉ r — but we have hxy
      have h : π (Pair x x0 ∉ r) { refine hx0min x hxZ };
      have hxy2 : π (Pair x x0 ∈ r) { refine ind_eq hx0y (λ w, Pair x w ∈ r) hxy };
      refine h hxy2 }
    { assume hx0r2;
      have hx0d3 : π (x0 = z ∨ x0 ∈ empty) { refine ∧ₑ₁ (cons_iff x0 z empty) hx0r2 };
      refine ∨ₑ hx0d3 _ _
      { assume hx0z;
        // x0 = z: Pair(y, x0) ∉ r means Pair(y, z) ∉ r — but we have hyz
        have h : π (Pair y x0 ∉ r) { refine hx0min y hyZ };
        have hyz2 : π (Pair y x0 ∈ r) { refine ind_eq hx0z (λ w, Pair y w ∈ r) hyz };
        refine h hyz2 }
      { assume he; refine ⊥ₑ (emptyE x0 he) } } }
end;

// well_ordI: wf(A,r) → linear(A,r) → well_ord(A,r)
opaque symbol well_ordI (A r : τ ι) :
  π (wf A r) → π (linear A r) → π (well_ord A r) ≔
begin
  assume A r hwf hlin;
  rewrite well_ord_def;
  apply ∧ᵢ
  { // tot_ord = part_ord ∧ linear
    rewrite tot_ord_def;
    apply ∧ᵢ
    { // part_ord = irrefl ∧ trans_on
      rewrite part_ord_def;
      apply ∧ᵢ
      { // irrefl_on A r
        refine irrefl_onI A r _;
        assume x hxA;
        refine wf_not_refl A r x hwf hxA }
      { // trans_on A r
        refine trans_onI A r _;
        assume x hxA y hyA z hzA hxy hyz;
        // By linear(A,r) trichotomy on x,z:
        // Either Pair(x,z) ∈ r, or x = z, or Pair(z,x) ∈ r
        refine linearE A r x z (Pair x z ∈ r) hlin hxA hzA _ _ _
        { assume h; apply h }
        { assume hxz;
          // x = z, Pair(x,y) ∈ r and Pair(y,z) ∈ r
          // means Pair(z,y) ∈ r and Pair(y,z) ∈ r
          // wf_asym gives contradiction
          refine ⊥ₑ _;
          refine wf_asym A r y z hwf hyA hzA hyz _;
          rewrite left hxz;
          apply hxy }
        { assume hzx;
          // Pair(z,x) ∈ r, Pair(x,y) ∈ r, Pair(y,z) ∈ r
          // wf_chain3 gives Pair(z,x) ∉ r — contradiction
          refine ⊥ₑ _;
          refine wf_chain3 A r z x y hwf hzA hxA hyA hzx hxy _;
          apply hyz } } }
    { refine hlin } }
  { refine hwf }
end;

// well_ord_is_wf: well_ord(A,r) → wf(A,r)
opaque symbol well_ord_is_wf (A r : τ ι) :
  π (well_ord A r) → π (wf A r) ≔
begin
  assume A r h;
  refine ∧ₑ₂ (well_ordD A r h)
end;

// well_ord_is_trans_on: well_ord(A,r) → trans_on(A,r)
opaque symbol well_ord_is_trans_on (A r : τ ι) :
  π (well_ord A r) → π (trans_on A r) ≔
begin
  assume A r h;
  have htot : π (tot_ord A r) { refine ∧ₑ₁ (well_ordD A r h) };
  have hpo : π (part_ord A r) { refine ∧ₑ₁ (tot_ordD A r htot) };
  refine ∧ₑ₂ (part_ordD A r hpo)
end;

// well_ord_is_linear: well_ord(A,r) → linear(A,r)
opaque symbol well_ord_is_linear (A r : τ ι) :
  π (well_ord A r) → π (linear A r) ≔
begin
  assume A r h;
  have htot : π (tot_ord A r) { refine ∧ₑ₁ (well_ordD A r h) };
  refine ∧ₑ₂ (tot_ordD A r htot)
end;

// ===========================================================================
// Section: Derived rules for pred(A,x,r)
// ===========================================================================

// pred_iff: y ∈ pred(A,x,r) ↔ Pair(y,x) ∈ r ∧ y ∈ A
opaque symbol pred_iff (y A x r : τ ι) :
  π ((y ∈ pred A x r) ⇔ (Pair y x ∈ r ∧ y ∈ A)) ≔
begin
  assume y A x r;
  rewrite pred_def;
  apply ∧ᵢ
  { assume h;
    have hyA : π (y ∈ A) { refine CollectD1 y A (λ z, Pair z x ∈ r) h };
    have hyr : π (Pair y x ∈ r) { refine CollectD2 y A (λ z, Pair z x ∈ r) h };
    apply ∧ᵢ hyr hyA }
  { assume h;
    have hyr : π (Pair y x ∈ r) { refine ∧ₑ₁ h };
    have hyA : π (y ∈ A) { refine ∧ₑ₂ h };
    refine CollectI y A (λ z, Pair z x ∈ r) hyA hyr }
end;

// predI: Pair(y,x) ∈ r → y ∈ A → y ∈ pred(A,x,r)
opaque symbol predI (y A x r : τ ι) :
  π (Pair y x ∈ r) → π (y ∈ A) → π (y ∈ pred A x r) ≔
begin
  assume y A x r hyr hyA;
  rewrite pred_def;
  refine CollectI y A (λ z, Pair z x ∈ r) hyA hyr
end;

// predE: y ∈ pred(A,x,r) → (y ∈ A → Pair(y,x) ∈ r → P) → P
opaque symbol predE (y A x r : τ ι) (P : Prop) :
  π (y ∈ pred A x r) → (π (y ∈ A) → π (Pair y x ∈ r) → π P) → π P ≔
begin
  assume y A x r P h hk;
  have hc : π (Pair y x ∈ r ∧ y ∈ A) { refine ∧ₑ₁ (pred_iff y A x r) h };
  refine hk (∧ₑ₂ hc) (∧ₑ₁ hc)
end;

// pred_subset: pred(A,x,r) ⊆ A
opaque symbol pred_subset (A x r : τ ι) :
  π (pred A x r ⊆ A) ≔
begin
  assume A x r y hy;
  refine ∧ₑ₂ (∧ₑ₁ (pred_iff y A x r) hy)
end;

// pred_subset_under: pred(A,x,r) ⊆ r -`` {x}
opaque symbol pred_subset_under (A x r : τ ι) :
  π (pred A x r ⊆ vimage_singleton r x) ≔
begin
  assume A x r y hy;
  refine vimage_singletonI y x r (∧ₑ₁ (∧ₑ₁ (pred_iff y A x r) hy))
end;

// pred_pred_eq: pred(pred(A,x,r), y, r) = pred(A,x,r) ∩ pred(A,y,r)
opaque symbol pred_pred_eq (A x y r : τ ι) :
  π (pred (pred A x r) y r = Int (pred A x r) (pred A y r)) ≔
begin
  assume A x y r;
  refine equality_iffI (pred (pred A x r) y r) (Int (pred A x r) (pred A y r)) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    // z ∈ pred(pred(A,x,r), y, r): z ∈ pred(A,x,r) ∧ Pair(z,y) ∈ r
    have hzP : π (z ∈ pred A x r) { refine pred_subset (pred A x r) y r z hz };
    have hzy : π (Pair z y ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z (pred A x r) y r) hz) };
    have hzA : π (z ∈ A) { refine pred_subset A x r z hzP };
    // z ∈ pred(A,y,r)
    have hzPy : π (z ∈ pred A y r) { refine predI z A y r hzy hzA };
    refine IntI z (pred A x r) (pred A y r) hzP hzPy }
  { assume hz;
    have hzPx : π (z ∈ pred A x r) { refine IntD1 z (pred A x r) (pred A y r) hz };
    have hzPy : π (z ∈ pred A y r) { refine IntD2 z (pred A x r) (pred A y r) hz };
    have hzy : π (Pair z y ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z A y r) hzPy) };
    refine predI z (pred A x r) y r hzy hzPx }
end;

// trans_pred_pred_eq: trans_on(A,r) → Pair(y,x) ∈ r → x ∈ A → y ∈ A →
//   pred(pred(A,x,r), y, r) = pred(A,y,r)
opaque symbol trans_pred_pred_eq (A r x y : τ ι) :
  π (trans_on A r) → π (Pair y x ∈ r) → π (x ∈ A) → π (y ∈ A) →
  π (pred (pred A x r) y r = pred A y r) ≔
begin
  assume A r x y htr hyx hxA hyA;
  refine equality_iffI (pred (pred A x r) y r) (pred A y r) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    // z ∈ pred(pred(A,x,r), y, r) → z ∈ pred(A,x,r) and Pair(z,y)∈r
    have hzPx : π (z ∈ pred A x r) { refine pred_subset (pred A x r) y r z hz };
    have hzy : π (Pair z y ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z (pred A x r) y r) hz) };
    have hzA : π (z ∈ A) { refine pred_subset A x r z hzPx };
    refine predI z A y r hzy hzA }
  { assume hz;
    // z ∈ pred(A,y,r): z ∈ A and Pair(z,y) ∈ r
    have hzA : π (z ∈ A) { refine pred_subset A y r z hz };
    have hzy : π (Pair z y ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z A y r) hz) };
    // By trans: Pair(z,y) ∈ r and Pair(y,x) ∈ r gives Pair(z,x) ∈ r
    have hzx : π (Pair z x ∈ r) { refine trans_onD A r z y x htr hzA hyA hxA hzy hyx };
    // z ∈ pred(A,x,r)
    have hzPx : π (z ∈ pred A x r) { refine predI z A x r hzx hzA };
    refine predI z (pred A x r) y r hzy hzPx }
end;

// ===========================================================================
// Section: Restricting an Ordering's Domain
// ===========================================================================

// part_ord_subset: part_ord(A,r) → B ⊆ A → part_ord(B,r)
opaque symbol part_ord_subset (A B r : τ ι) :
  π (part_ord A r) → π (B ⊆ A) → π (part_ord B r) ≔
begin
  assume A B r hpo hBA;
  have hirr : π (irrefl_on A r) { refine ∧ₑ₁ (part_ordD A r hpo) };
  have htr : π (trans_on A r) { refine ∧ₑ₂ (part_ordD A r hpo) };
  rewrite part_ord_def;
  apply ∧ᵢ
  { // irrefl on B
    refine irrefl_onI B r _;
    assume x hxB;
    refine irrefl_onD A r x hirr (hBA x hxB) }
  { // trans on B
    refine trans_onI B r _;
    assume x hxB y hyB z hzB hxy hyz;
    refine trans_onD A r x y z htr (hBA x hxB) (hBA y hyB) (hBA z hzB) hxy hyz }
end;

// linear_subset: linear(A,r) → B ⊆ A → linear(B,r)
opaque symbol linear_subset (A B r : τ ι) :
  π (linear A r) → π (B ⊆ A) → π (linear B r) ≔
begin
  assume A B r hlin hBA;
  refine linearI B r _;
  assume x hxB y hyB;
  refine linearD A r x y hlin (hBA x hxB) (hBA y hyB)
end;

// tot_ord_subset: tot_ord(A,r) → B ⊆ A → tot_ord(B,r)
opaque symbol tot_ord_subset (A B r : τ ι) :
  π (tot_ord A r) → π (B ⊆ A) → π (tot_ord B r) ≔
begin
  assume A B r htot hBA;
  rewrite tot_ord_def;
  apply ∧ᵢ
  { refine part_ord_subset A B r (∧ₑ₁ (tot_ordD A r htot)) hBA }
  { refine linear_subset A B r (∧ₑ₂ (tot_ordD A r htot)) hBA }
end;

// wf_subset: wf(A,r) → B ⊆ A → wf(B,r)
opaque symbol wf_subset (A B r : τ ι) :
  π (wf A r) → π (B ⊆ A) → π (wf B r) ≔
begin
  assume A B r hwf hBA;
  rewrite wf_def;
  assume Z hZB hZne;
  refine wfD A r hwf Z (subset_trans Z B A hZB hBA) hZne
end;

// well_ord_subset: well_ord(A,r) → B ⊆ A → well_ord(B,r)
opaque symbol well_ord_subset (A B r : τ ι) :
  π (well_ord A r) → π (B ⊆ A) → π (well_ord B r) ≔
begin
  assume A B r hwo hBA;
  rewrite well_ord_def;
  apply ∧ᵢ
  { refine tot_ord_subset A B r (∧ₑ₁ (well_ordD A r hwo)) hBA }
  { refine wf_subset A B r (∧ₑ₂ (well_ordD A r hwo)) hBA }
end;

// ===========================================================================
// Section: Empty and Unit Domains
// ===========================================================================

// irrefl_0: irrefl_on(empty, r)   (Isabelle: irrefl_0)
opaque symbol irrefl_0 (r : τ ι) : π (irrefl_on empty r) ≔
begin
  assume r;
  refine irrefl_onI empty r _;
  assume x hx;
  refine ⊥ₑ (emptyE x hx)
end;

// DEPRECATED alias (pre-rename name; kept so no proved symbol vanishes
// vs. git HEAD — safe to delete together with a conscious gate override).
opaque symbol irrefl_on_0 (r : τ ι) : π (irrefl_on empty r) ≔
begin
  assume r;
  refine irrefl_0 r
end;

// trans_on_0: trans_on(empty, r)
opaque symbol trans_on_0 (r : τ ι) : π (trans_on empty r) ≔
begin
  assume r;
  refine trans_onI empty r _;
  assume x hx;
  refine ⊥ₑ (emptyE x hx)
end;

// part_ord_0: part_ord(empty, r)
opaque symbol part_ord_0 (r : τ ι) : π (part_ord empty r) ≔
begin
  assume r;
  rewrite part_ord_def;
  apply ∧ᵢ (irrefl_0 r) (trans_on_0 r)
end;

// linear_0: linear(empty, r)
opaque symbol linear_0 (r : τ ι) : π (linear empty r) ≔
begin
  assume r;
  refine linearI empty r _;
  assume x hx;
  refine ⊥ₑ (emptyE x hx)
end;

// tot_ord_0: tot_ord(empty, r)
opaque symbol tot_ord_0 (r : τ ι) : π (tot_ord empty r) ≔
begin
  assume r;
  rewrite tot_ord_def;
  apply ∧ᵢ (part_ord_0 r) (linear_0 r)
end;

// wf_on_0: wf(empty, r) — every subset of empty is empty
opaque symbol wf_on_0 (r : τ ι) : π (wf empty r) ≔
begin
  assume r;
  rewrite wf_def;
  assume Z hZ hZne;
  // Z ⊆ empty, so Z = empty. Contradicts Z ≠ empty.
  refine ⊥ₑ (hZne (subset_empty Z hZ))
end;

// well_ord_0: well_ord(empty, r)
opaque symbol well_ord_0 (r : τ ι) : π (well_ord empty r) ≔
begin
  assume r;
  rewrite well_ord_def;
  apply ∧ᵢ (tot_ord_0 r) (wf_on_0 r)
end;

// wf_on_any_0: wf(A, empty) — the empty relation is well-founded
opaque symbol wf_on_any_0 (A : τ ι) : π (wf A empty) ≔
begin
  assume A;
  rewrite wf_def;
  assume Z hZA hZne;
  // Z ≠ empty, so by foundation there exists x ∈ Z
  refine not_emptyE Z _ hZne _;
  assume x hxZ;
  refine ∃ᵢ x _;
  apply ∧ᵢ hxZ _;
  assume y hyZ hyr;
  refine emptyE (Pair y x) hyr
end;

// tot_ord_unit: tot_ord({a}, empty)
opaque symbol tot_ord_unit (a : τ ι) : π (tot_ord (cons a empty) empty) ≔
begin
  assume a;
  rewrite tot_ord_def;
  apply ∧ᵢ
  { // part_ord
    rewrite part_ord_def;
    apply ∧ᵢ
    { // irrefl
      refine irrefl_onI (cons a empty) empty _;
      assume x hx hxx;
      refine emptyE (Pair x x) hxx }
    { // trans
      refine trans_onI (cons a empty) empty _;
      assume x hx y hy z hz hxy hyz;
      refine ⊥ₑ (emptyE (Pair x y) hxy) } }
  { // linear
    refine linearI (cons a empty) empty _;
    assume x hx y hy;
    // x ∈ {a} → x = a, y ∈ {a} → y = a, so x = y
    have hxa : π (x = a ∨ x ∈ empty) { refine ∧ₑ₁ (cons_iff x a empty) hx };
    have hya : π (y = a ∨ y ∈ empty) { refine ∧ₑ₁ (cons_iff y a empty) hy };
    refine ∨ₑ hxa _ _
    { assume hx1;
      refine ∨ₑ hya _ _
      { assume hy1;
        apply ∨ᵢ₂;
        apply ∨ᵢ₁;
        rewrite hx1; symmetry; apply hy1 }
      { assume he; refine ⊥ₑ (emptyE y he) } }
    { assume he; refine ⊥ₑ (emptyE x he) } }
end;

// well_ord_unit: well_ord({a}, empty)
opaque symbol well_ord_unit (a : τ ι) : π (well_ord (cons a empty) empty) ≔
begin
  assume a;
  rewrite well_ord_def;
  apply ∧ᵢ (tot_ord_unit a) (wf_on_any_0 (cons a empty))
end;

// ===========================================================================
// Section: Order-Isomorphisms
// ===========================================================================

// mono_map_is_fun: f ∈ mono_map(A,r,B,s) → f ∈ A→B
opaque symbol mono_map_is_fun (f A r B s : τ ι) :
  π (f ∈ mono_map A r B s) → π (f ∈ Pi A (λ _, B)) ≔
begin
  assume f A r B s hf;
  have hf' : π (f ∈ Collect (Pi A (λ _, B))
    (λ g, Ball A (λ x, Ball A (λ y,
      Pair x y ∈ r ⇒ Pair (fapply g x) (fapply g y) ∈ s))))
    { refine ind_eq (eq_sym (mono_map_def A r B s)) (λ w, f ∈ w) hf };
  refine CollectD1 f (Pi A (λ _, B))
    (λ g, Ball A (λ x, Ball A (λ y,
      Pair x y ∈ r ⇒ Pair (fapply g x) (fapply g y) ∈ s))) hf'
end;

// ord_isoI: f ∈ bij(A,B) → (∀x∈A. ∀y∈A. Pair(x,y)∈r ↔ Pair(f`x,f`y)∈s) →
//   f ∈ ord_iso(A,r,B,s)
opaque symbol ord_isoI (f A r B s : τ ι) :
  π (f ∈ bij A B) →
  π (Ball A (λ x, Ball A (λ y,
    (Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ s)))) →
  π (f ∈ ord_iso A r B s) ≔
begin
  assume f A r B s hbij hord;
  rewrite ord_iso_def;
  refine CollectI f (bij A B)
    (λ g, Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply g x) (fapply g y) ∈ s)))) hbij hord
end;

// ord_iso_is_bij: f ∈ ord_iso(A,r,B,s) → f ∈ bij(A,B)
opaque symbol ord_iso_is_bij (f A r B s : τ ι) :
  π (f ∈ ord_iso A r B s) → π (f ∈ bij A B) ≔
begin
  assume f A r B s hf;
  have hf' : π (f ∈ Collect (bij A B)
    (λ g, Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply g x) (fapply g y) ∈ s)))))
    { refine ind_eq (eq_sym (ord_iso_def A r B s)) (λ w, f ∈ w) hf };
  refine CollectD1 f (bij A B)
    (λ g, Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply g x) (fapply g y) ∈ s)))) hf'
end;

// ord_iso_memD: the order-preservation content of an ord_iso membership
opaque symbol ord_iso_memD (f A r B s : τ ι) :
  π (f ∈ ord_iso A r B s) →
  π (Ball A (λ x, Ball A (λ y,
    (Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ s)))) ≔
begin
  assume f A r B s hf;
  have hf' : π (f ∈ Collect (bij A B)
    (λ g, Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply g x) (fapply g y) ∈ s)))))
    { refine ind_eq (eq_sym (ord_iso_def A r B s)) (λ w, f ∈ w) hf };
  refine CollectD2 f (bij A B)
    (λ g, Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply g x) (fapply g y) ∈ s)))) hf'
end;

// ord_iso_is_mono_map: f ∈ ord_iso(A,r,B,s) → f ∈ mono_map(A,r,B,s)
opaque symbol ord_iso_is_mono_map (f A r B s : τ ι) :
  π (f ∈ ord_iso A r B s) → π (f ∈ mono_map A r B s) ≔
begin
  assume f A r B s hf;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hfun : π (f ∈ Pi A (λ _, B)) { refine bij_is_fun f A B hbij };
  have hord : π (Ball A (λ x, Ball A (λ y,
    (Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ s))))
    { refine ord_iso_memD f A r B s hf };
  rewrite mono_map_def;
  refine CollectI f (Pi A (λ _, B))
    (λ g, Ball A (λ x, Ball A (λ y,
      Pair x y ∈ r ⇒ Pair (fapply g x) (fapply g y) ∈ s))) hfun _;
  assume x hxA y hyA hxy;
  refine ∧ₑ₁ (hord x hxA y hyA) hxy
end;

// ord_iso_apply: f ∈ ord_iso(A,r,B,s) → Pair(x,y)∈r → x∈A → y∈A → Pair(f`x,f`y)∈s
opaque symbol ord_iso_apply (f A r B s x y : τ ι) :
  π (f ∈ ord_iso A r B s) → π (Pair x y ∈ r) →
  π (x ∈ A) → π (y ∈ A) → π (Pair (fapply f x) (fapply f y) ∈ s) ≔
begin
  assume f A r B s x y hf hxy hxA hyA;
  have hord : π (Ball A (λ x2, Ball A (λ y2,
    (Pair x2 y2 ∈ r) ⇔ (Pair (fapply f x2) (fapply f y2) ∈ s))))
    { refine ord_iso_memD f A r B s hf };
  refine ∧ₑ₁ (hord x hxA y hyA) hxy
end;

// ===========================================================================
// Local helper lemmas (apply_type, identity, converse-bijection, composition)
// ===========================================================================

// apply_type: f ∈ A→B → a ∈ A → f`a ∈ B
opaque symbol apply_type (f A B a : τ ι) :
  π (f ∈ Pi A (λ _, B)) → π (a ∈ A) → π (fapply f a ∈ B) ≔
begin
  assume f A B a hf ha;
  refine fapply_type f a A (λ _, B) hf ha
end;

// bij_apply: f ∈ bij(A,B) → a ∈ A → f`a ∈ B
opaque symbol bij_apply (f A B a : τ ι) :
  π (f ∈ bij A B) → π (a ∈ A) → π (fapply f a ∈ B) ≔
begin
  assume f A B a hf ha;
  refine apply_type f A B a (bij_is_fun f A B hf) ha
end;

// id_conv: x ∈ A → (id_fun A)`x = x
opaque symbol id_conv (A x : τ ι) :
  π (x ∈ A) → π (fapply (id_fun A) x = x) ≔
begin
  assume A x hx;
  rewrite id_fun_def;
  refine beta A (λ z, z) x hx
end;

// id_bij: id_fun A ∈ bij(A,A)
opaque symbol id_bij (A : τ ι) : π (id_fun A ∈ bij A A) ≔
begin
  assume A;
  rewrite id_fun_def;
  rewrite bij_def;
  refine IntI (Lambda A (λ x, x)) (inj A A) (surj A A) _ _
  { refine lam_injective A A (λ x, x) (λ x, x) _ _
    { assume x hx; apply hx }
    { assume x hx; reflexivity } }
  { refine lam_surjective A A (λ x, x) (λ x, x) _ _ _
    { assume x hx; apply hx }
    { assume y hy; apply hy }
    { assume y hy; reflexivity } }
end;

// converse_function: f ∈ inj(A,B) → function(converse f)
opaque symbol converse_function (f A B : τ ι) :
  π (f ∈ inj A B) → π (function (converse f)) ≔
begin
  assume f A B hinj;
  rewrite function_def;
  assume x y yp h1 h2;
  have hfun : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  have hy : π (Pair y x ∈ f) { refine converseD x y f h1 };
  have hyp : π (Pair yp x ∈ f) { refine converseD x yp f h2 };
  have hpfun : π (function f) { refine Pi_function f A (λ _, B) hfun };
  have hfy : π (fapply f y = x) { refine function_apply_equality y x f hy hpfun };
  have hfyp : π (fapply f yp = x) { refine function_apply_equality yp x f hyp hpfun };
  have hyA : π (y ∈ A) { refine domain_type y x f A (λ _, B) hy hfun };
  have hypA : π (yp ∈ A) { refine domain_type yp x f A (λ _, B) hyp hfun };
  refine inj_apply_equality f A B y yp hinj _ hyA hypA;
  rewrite hfy; rewrite hfyp; reflexivity
end;

// converse_apply_eq: f ∈ bij(A,B) → a ∈ A → f`a = b → (converse f)`b = a
opaque symbol converse_apply_eq (f A B a b : τ ι) :
  π (f ∈ bij A B) → π (a ∈ A) → π (fapply f a = b) →
  π (fapply (converse f) b = a) ≔
begin
  assume f A B a b hbij ha hfa;
  have hinj : π (f ∈ inj A B) { refine bij_is_inj f A B hbij };
  have hfun : π (f ∈ Pi A (λ _, B)) { refine bij_is_fun f A B hbij };
  have hpair : π (Pair a (fapply f a) ∈ f) { refine Pi_apply_Pair f a A (λ _, B) hfun ha };
  have hpair2 : π (Pair a b ∈ f) { rewrite left hfa; apply hpair };
  have hconv : π (Pair b a ∈ converse f) { refine converseI a b f hpair2 };
  refine function_apply_equality b a (converse f) hconv (converse_function f A B hinj)
end;

// converse_apply_type: f ∈ bij(A,B) → b ∈ B → (converse f)`b ∈ A
opaque symbol converse_apply_type (f A B b : τ ι) :
  π (f ∈ bij A B) → π (b ∈ B) → π (fapply (converse f) b ∈ A) ≔
begin
  assume f A B b hbij hb;
  have hsurj : π (f ∈ surj A B) { refine bij_is_surj f A B hbij };
  have hex : π (Bex A (λ a, fapply f a = b)) { refine surj_memD f A B hsurj b hb };
  refine ∃ₑ hex _;
  assume a ha;
  have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
  have hfa : π (fapply f a = b) { refine ∧ₑ₂ ha };
  have heq : π (fapply (converse f) b = a) { refine converse_apply_eq f A B a b hbij haA hfa };
  rewrite heq; apply haA
end;

// right_inverse_bij: f ∈ bij(A,B) → b ∈ B → f`((converse f)`b) = b
opaque symbol right_inverse_bij (f A B b : τ ι) :
  π (f ∈ bij A B) → π (b ∈ B) → π (fapply f (fapply (converse f) b) = b) ≔
begin
  assume f A B b hbij hb;
  have hsurj : π (f ∈ surj A B) { refine bij_is_surj f A B hbij };
  have hex : π (Bex A (λ a, fapply f a = b)) { refine surj_memD f A B hsurj b hb };
  refine ∃ₑ hex _;
  assume a ha;
  have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
  have hfa : π (fapply f a = b) { refine ∧ₑ₂ ha };
  have heq : π (fapply (converse f) b = a) { refine converse_apply_eq f A B a b hbij haA hfa };
  rewrite heq; apply hfa
end;

// left_inverse_bij: f ∈ bij(A,B) → a ∈ A → (converse f)`(f`a) = a
opaque symbol left_inverse_bij (f A B a : τ ι) :
  π (f ∈ bij A B) → π (a ∈ A) → π (fapply (converse f) (fapply f a) = a) ≔
begin
  assume f A B a hbij ha;
  refine converse_apply_eq f A B a (fapply f a) hbij ha (eq_refl (fapply f a))
end;

// converse_subset: f ∈ A→B → converse f ⊆ Sigma B (λ_,A)
opaque symbol converse_subset (f A B : τ ι) :
  π (f ∈ Pi A (λ _, B)) → π (converse f ⊆ Sigma B (λ _, A)) ≔
begin
  assume f A B hf q hq;
  have hq' : π (q ∈ RepFun (Collect f (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = Pair x y))
                  (λ p, Pair (snd p) (fst p)))
    { refine ind_eq (eq_sym (converse_def f)) (λ s, q ∈ s) hq };
  have hbex : π (Bex (Collect f (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = Pair x y))
                     (λ p, q = Pair (snd p) (fst p)))
    { refine ∧ₑ₁ (RepFun_iff q
        (Collect f (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = Pair x y))
        (λ p, Pair (snd p) (fst p))) hq' };
  refine ∃ₑ hbex _;
  assume p hp;
  have hpC : π (p ∈ Collect f (λ z, `∃ (x : τ ι), `∃ (y : τ ι), z = Pair x y)) { refine ∧ₑ₁ hp };
  have hqeq : π (q = Pair (snd p) (fst p)) { refine ∧ₑ₂ hp };
  have hpf : π (p ∈ f) { refine CollectD1 p f (λ z, `∃ (x : τ ι), `∃ (y : τ ι), z = Pair x y) hpC };
  have hppair : π (`∃ (x : τ ι), `∃ (y : τ ι), p = Pair x y)
    { refine CollectD2 p f (λ z, `∃ (x : τ ι), `∃ (y : τ ι), z = Pair x y) hpC };
  refine ∃ₑ hppair _;
  assume x hx;
  refine ∃ₑ hx _;
  assume y hpeq;
  have hpS : π (p ∈ Sigma A (λ _, B)) { refine Pi_subset_Sigma f A (λ _, B) hf p hpf };
  have hpxy : π (Pair x y ∈ Sigma A (λ _, B)) { refine ind_eq (eq_sym hpeq) (λ z, z ∈ Sigma A (λ _, B)) hpS };
  have hbexS : π (Bex A (λ u, Bex B (λ v, Pair x y = Pair u v)))
    { refine SigmaE (Pair x y) A (λ _, B) hpxy };
  refine ∃ₑ hbexS _;
  assume u hu;
  have huA : π (u ∈ A) { refine ∧ₑ₁ hu };
  refine ∃ₑ (∧ₑ₂ hu) _;
  assume v hv;
  have hvB : π (v ∈ B) { refine ∧ₑ₁ hv };
  have heqp : π (Pair x y = Pair u v) { refine ∧ₑ₂ hv };
  have hxu : π (x = u) { refine Pair_inject1 x y u v heqp };
  have hyv : π (y = v) { refine Pair_inject2 x y u v heqp };
  have hxA : π (x ∈ A) { refine ind_eq hxu (λ z, z ∈ A) huA };
  have hyB : π (y ∈ B) { refine ind_eq hyv (λ z, z ∈ B) hvB };
  have hsndp : π (snd p = y) { rewrite hpeq; refine snd_conv x y };
  have hfstp : π (fst p = x) { rewrite hpeq; refine fst_conv x y };
  rewrite hqeq; rewrite hsndp; rewrite hfstp;
  refine SigmaI y x B (λ _, A) hyB hxA
end;

// converse_Pi: f ∈ bij(A,B) → converse f ∈ B→A
opaque symbol converse_Pi (f A B : τ ι) :
  π (f ∈ bij A B) → π (converse f ∈ Pi B (λ _, A)) ≔
begin
  assume f A B hbij;
  have hfun : π (f ∈ Pi A (λ _, B)) { refine bij_is_fun f A B hbij };
  have hinj : π (f ∈ inj A B) { refine bij_is_inj f A B hbij };
  have hsurj : π (f ∈ surj A B) { refine bij_is_surj f A B hbij };
  rewrite Pi_def;
  refine CollectI (converse f) (Pow (Sigma B (λ _, A))) (λ g, B ⊆ domain g ∧ function g) _ _
  { refine PowI (converse f) (Sigma B (λ _, A)) (converse_subset f A B hfun) }
  { apply ∧ᵢ
    { assume b hb;
      have hex : π (Bex A (λ a, fapply f a = b)) { refine surj_memD f A B hsurj b hb };
      refine ∃ₑ hex _;
      assume a ha;
      have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
      have hfa : π (fapply f a = b) { refine ∧ₑ₂ ha };
      have hpair : π (Pair a (fapply f a) ∈ f) { refine Pi_apply_Pair f a A (λ _, B) hfun haA };
      have hpair2 : π (Pair a b ∈ f) { rewrite left hfa; apply hpair };
      have hconv : π (Pair b a ∈ converse f) { refine converseI a b f hpair2 };
      refine domainI b a (converse f) hconv }
    { refine converse_function f A B hinj } }
end;

// converse_bij: f ∈ bij(A,B) → converse f ∈ bij(B,A)
opaque symbol converse_bij (f A B : τ ι) :
  π (f ∈ bij A B) → π (converse f ∈ bij B A) ≔
begin
  assume f A B hbij;
  have hcPi : π (converse f ∈ Pi B (λ _, A)) { refine converse_Pi f A B hbij };
  rewrite bij_def;
  refine IntI (converse f) (inj B A) (surj B A) _ _
  { rewrite inj_def;
    refine CollectI (converse f) (Pi B (λ _, A))
      (λ g, Ball B (λ w, Ball B (λ x, fapply g w = fapply g x ⇒ w = x))) hcPi _;
    assume w hw x hx heq;
    have hrw : π (fapply f (fapply (converse f) w) = w) { refine right_inverse_bij f A B w hbij hw };
    have hrx : π (fapply f (fapply (converse f) x) = x) { refine right_inverse_bij f A B x hbij hx };
    have hstep : π (fapply f (fapply (converse f) w) = fapply f (fapply (converse f) x))
      { rewrite heq; reflexivity };
    rewrite left hrw; rewrite left hrx; apply hstep }
  { rewrite surj_def;
    refine CollectI (converse f) (Pi B (λ _, A))
      (λ g, Ball A (λ y, Bex B (λ x, fapply g x = y))) hcPi _;
    assume a ha;
    refine ∃ᵢ (fapply f a) _;
    apply ∧ᵢ
    { refine bij_apply f A B a hbij ha }
    { refine left_inverse_bij f A B a hbij ha } }
end;

// range_subset_cod: f ∈ A→B → range f ⊆ B
opaque symbol range_subset_cod (f A B : τ ι) :
  π (f ∈ Pi A (λ _, B)) → π (range f ⊆ B) ≔
begin
  assume f A B hf b hb;
  have hex : π (`∃ (a : τ ι), Pair a b ∈ f) { refine rangeE b f hb };
  refine ∃ₑ hex _;
  assume a hab;
  refine range_type a b f A (λ _, B) hab hf
end;

// comp_function: function f → function g → function(rcomp f g)
opaque symbol comp_function (f g : τ ι) :
  π (function f) → π (function g) → π (function (rcomp f g)) ≔
begin
  assume f g hf hg;
  rewrite function_def;
  assume x y yp h1 h2;
  have he1 : π (`∃ (z : τ ι), Pair x z ∈ g ∧ Pair z y ∈ f) { refine rcompE_pair x y f g h1 };
  have he2 : π (`∃ (z : τ ι), Pair x z ∈ g ∧ Pair z yp ∈ f) { refine rcompE_pair x yp f g h2 };
  refine ∃ₑ he1 _; assume z1 hz1;
  refine ∃ₑ he2 _; assume z2 hz2;
  have hg1 : π (Pair x z1 ∈ g) { refine ∧ₑ₁ hz1 };
  have hf1 : π (Pair z1 y ∈ f) { refine ∧ₑ₂ hz1 };
  have hg2 : π (Pair x z2 ∈ g) { refine ∧ₑ₁ hz2 };
  have hf2 : π (Pair z2 yp ∈ f) { refine ∧ₑ₂ hz2 };
  have hz : π (z1 = z2) { refine functionD g hg x z1 z2 hg1 hg2 };
  have hf2' : π (Pair z1 yp ∈ f) { rewrite hz; apply hf2 };
  refine functionD f hf z1 y yp hf1 hf2'
end;

// comp_fun: g ∈ A→B → f ∈ B→C → rcomp f g ∈ A→C
opaque symbol comp_fun (f g A B C : τ ι) :
  π (g ∈ Pi A (λ _, B)) → π (f ∈ Pi B (λ _, C)) → π (rcomp f g ∈ Pi A (λ _, C)) ≔
begin
  assume f g A B C hg hf;
  have hgfun : π (function g) { refine Pi_function g A (λ _, B) hg };
  have hffun : π (function f) { refine Pi_function f B (λ _, C) hf };
  rewrite Pi_def;
  refine CollectI (rcomp f g) (Pow (Sigma A (λ _, C))) (λ h, A ⊆ domain h ∧ function h) _ _
  { refine PowI (rcomp f g) (Sigma A (λ _, C)) _;
    assume p hp;
    have hpS : π (p ∈ Sigma (domain g) (λ _, range f))
      { refine rcomp_subset f g p hp };
    have hbex : π (Bex (domain g) (λ u, Bex (range f) (λ v, p = Pair u v)))
      { refine SigmaE p (domain g) (λ _, range f) hpS };
    refine ∃ₑ hbex _; assume u hu;
    have hudg : π (u ∈ domain g) { refine ∧ₑ₁ hu };
    refine ∃ₑ (∧ₑ₂ hu) _; assume v hv;
    have hvrf : π (v ∈ range f) { refine ∧ₑ₁ hv };
    have hpeq : π (p = Pair u v) { refine ∧ₑ₂ hv };
    have hdomg : π (domain g = A) { refine domain_of_fun g A (λ _, B) hg };
    have huA : π (u ∈ A) { refine ind_eq (eq_sym hdomg) (λ z, u ∈ z) hudg };
    have hvC : π (v ∈ C) { refine range_subset_cod f B C hf v hvrf };
    rewrite hpeq;
    refine SigmaI u v A (λ _, C) huA hvC }
  { apply ∧ᵢ
    { assume a ha;
      have hga : π (fapply g a ∈ B) { refine apply_type g A B a hg ha };
      have hpg : π (Pair a (fapply g a) ∈ g) { refine Pi_apply_Pair g a A (λ _, B) hg ha };
      have hpf : π (Pair (fapply g a) (fapply f (fapply g a)) ∈ f)
        { refine Pi_apply_Pair f (fapply g a) B (λ _, C) hf hga };
      have hcomp : π (Pair a (fapply f (fapply g a)) ∈ rcomp f g)
        { refine rcompI a (fapply g a) (fapply f (fapply g a)) f g hpg hpf };
      refine domainI a (fapply f (fapply g a)) (rcomp f g) hcomp }
    { refine comp_function f g hffun hgfun } }
end;

// comp_fun_apply: g ∈ A→B → f ∈ B→C → a ∈ A → (rcomp f g)`a = f`(g`a)
opaque symbol comp_fun_apply (f g A B C a : τ ι) :
  π (g ∈ Pi A (λ _, B)) → π (f ∈ Pi B (λ _, C)) → π (a ∈ A) →
  π (fapply (rcomp f g) a = fapply f (fapply g a)) ≔
begin
  assume f g A B C a hg hf ha;
  have hga : π (fapply g a ∈ B) { refine apply_type g A B a hg ha };
  have hpg : π (Pair a (fapply g a) ∈ g) { refine Pi_apply_Pair g a A (λ _, B) hg ha };
  have hpf : π (Pair (fapply g a) (fapply f (fapply g a)) ∈ f)
    { refine Pi_apply_Pair f (fapply g a) B (λ _, C) hf hga };
  have hcomp : π (Pair a (fapply f (fapply g a)) ∈ rcomp f g)
    { refine rcompI a (fapply g a) (fapply f (fapply g a)) f g hpg hpf };
  have hcfun : π (function (rcomp f g))
    { refine comp_function f g (Pi_function f B (λ _, C) hf) (Pi_function g A (λ _, B) hg) };
  refine function_apply_equality a (fapply f (fapply g a)) (rcomp f g) hcomp hcfun
end;

// comp_bij: g ∈ bij(A,B) → f ∈ bij(B,C) → rcomp f g ∈ bij(A,C)
opaque symbol comp_bij (f g A B C : τ ι) :
  π (g ∈ bij A B) → π (f ∈ bij B C) → π (rcomp f g ∈ bij A C) ≔
begin
  assume f g A B C hg hf;
  have hgfun : π (g ∈ Pi A (λ _, B)) { refine bij_is_fun g A B hg };
  have hffun : π (f ∈ Pi B (λ _, C)) { refine bij_is_fun f B C hf };
  have hginj : π (g ∈ inj A B) { refine bij_is_inj g A B hg };
  have hfinj : π (f ∈ inj B C) { refine bij_is_inj f B C hf };
  have hgsurj : π (g ∈ surj A B) { refine bij_is_surj g A B hg };
  have hfsurj : π (f ∈ surj B C) { refine bij_is_surj f B C hf };
  have hcompfun : π (rcomp f g ∈ Pi A (λ _, C)) { refine comp_fun f g A B C hgfun hffun };
  rewrite bij_def;
  refine IntI (rcomp f g) (inj A C) (surj A C) _ _
  { rewrite inj_def;
    refine CollectI (rcomp f g) (Pi A (λ _, C))
      (λ h, Ball A (λ w, Ball A (λ x, fapply h w = fapply h x ⇒ w = x))) hcompfun _;
    assume w hw x hx heq;
    have hcw : π (fapply (rcomp f g) w = fapply f (fapply g w)) { refine comp_fun_apply f g A B C w hgfun hffun hw };
    have hcx : π (fapply (rcomp f g) x = fapply f (fapply g x)) { refine comp_fun_apply f g A B C x hgfun hffun hx };
    have hgw : π (fapply g w ∈ B) { refine apply_type g A B w hgfun hw };
    have hgx : π (fapply g x ∈ B) { refine apply_type g A B x hgfun hx };
    have hfeq : π (fapply f (fapply g w) = fapply f (fapply g x))
      { rewrite left hcw; rewrite left hcx; apply heq };
    have hgeq : π (fapply g w = fapply g x) { refine inj_apply_equality f B C (fapply g w) (fapply g x) hfinj hfeq hgw hgx };
    refine inj_apply_equality g A B w x hginj hgeq hw hx }
  { rewrite surj_def;
    refine CollectI (rcomp f g) (Pi A (λ _, C))
      (λ h, Ball C (λ y, Bex A (λ x, fapply h x = y))) hcompfun _;
    assume c hc;
    have he1 : π (Bex B (λ b, fapply f b = c)) { refine surj_memD f B C hfsurj c hc };
    refine ∃ₑ he1 _; assume b hb;
    have hbB : π (b ∈ B) { refine ∧ₑ₁ hb };
    have hfb : π (fapply f b = c) { refine ∧ₑ₂ hb };
    have he2 : π (Bex A (λ a, fapply g a = b)) { refine surj_memD g A B hgsurj b hbB };
    refine ∃ₑ he2 _; assume a haa;
    have haA : π (a ∈ A) { refine ∧ₑ₁ haa };
    have hga : π (fapply g a = b) { refine ∧ₑ₂ haa };
    refine ∃ᵢ a _;
    apply ∧ᵢ haA _;
    have hca : π (fapply (rcomp f g) a = fapply f (fapply g a)) { refine comp_fun_apply f g A B C a hgfun hffun haA };
    rewrite hca; rewrite hga; apply hfb }
end;

// ord_iso_converse: f ∈ ord_iso(A,r,B,s) → Pair(x,y)∈s → x∈B → y∈B →
//   Pair(converse(f)`x, converse(f)`y) ∈ r
opaque symbol ord_iso_converse (f A r B s x y : τ ι) :
  π (f ∈ ord_iso A r B s) → π (Pair x y ∈ s) →
  π (x ∈ B) → π (y ∈ B) →
  π (Pair (fapply (converse f) x) (fapply (converse f) y) ∈ r) ≔
begin
  assume f A r B s x y hf hxy hxB hyB;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hcx : π (fapply (converse f) x ∈ A) { refine converse_apply_type f A B x hbij hxB };
  have hcy : π (fapply (converse f) y ∈ A) { refine converse_apply_type f A B y hbij hyB };
  have hord : π (Ball A (λ u, Ball A (λ v, (Pair u v ∈ r) ⇔ (Pair (fapply f u) (fapply f v) ∈ s))))
    { refine ord_iso_memD f A r B s hf };
  have hiff : π ((Pair (fapply (converse f) x) (fapply (converse f) y) ∈ r) ⇔ (Pair (fapply f (fapply (converse f) x)) (fapply f (fapply (converse f) y)) ∈ s))
    { refine hord (fapply (converse f) x) hcx (fapply (converse f) y) hcy };
  have hrx : π (fapply f (fapply (converse f) x) = x) { refine right_inverse_bij f A B x hbij hxB };
  have hry : π (fapply f (fapply (converse f) y) = y) { refine right_inverse_bij f A B y hbij hyB };
  refine ∧ₑ₂ hiff _;
  rewrite hrx; rewrite hry; apply hxy
end;

// ===========================================================================
// Section: Symmetry and Transitivity of Order-Isomorphisms
// ===========================================================================

// ord_iso_refl: id_fun(A) ∈ ord_iso(A,r,A,r)
opaque symbol ord_iso_refl (A r : τ ι) :
  π (id_fun A ∈ ord_iso A r A r) ≔
begin
  assume A r;
  refine ord_isoI (id_fun A) A r A r (id_bij A) _;
  assume x hxA y hyA;
  apply ∧ᵢ
  { assume hxy;
    rewrite (id_conv A x hxA);
    rewrite (id_conv A y hyA);
    apply hxy }
  { assume hxy;
    rewrite left (id_conv A x hxA);
    rewrite left (id_conv A y hyA);
    apply hxy }
end;

// ord_iso_sym: f ∈ ord_iso(A,r,B,s) → converse(f) ∈ ord_iso(B,s,A,r)
opaque symbol ord_iso_sym (f A r B s : τ ι) :
  π (f ∈ ord_iso A r B s) → π (converse f ∈ ord_iso B s A r) ≔
begin
  assume f A r B s hf;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hcbij : π (converse f ∈ bij B A) { refine converse_bij f A B hbij };
  refine ord_isoI (converse f) B s A r hcbij _;
  assume x hxB y hyB;
  apply ∧ᵢ
  { assume hs;
    refine ord_iso_converse f A r B s x y hf hs hxB hyB }
  { assume hr;
    have hcx : π (fapply (converse f) x ∈ A) { refine converse_apply_type f A B x hbij hxB };
    have hcy : π (fapply (converse f) y ∈ A) { refine converse_apply_type f A B y hbij hyB };
    have hsxy : π (Pair (fapply f (fapply (converse f) x)) (fapply f (fapply (converse f) y)) ∈ s)
      { refine ord_iso_apply f A r B s (fapply (converse f) x) (fapply (converse f) y) hf hr hcx hcy };
    have hrx : π (fapply f (fapply (converse f) x) = x) { refine right_inverse_bij f A B x hbij hxB };
    have hry : π (fapply f (fapply (converse f) y) = y) { refine right_inverse_bij f A B y hbij hyB };
    rewrite left hrx; rewrite left hry; apply hsxy }
end;

// ord_iso_trans: g ∈ ord_iso(A,r,B,s) → f ∈ ord_iso(B,s,C,t) →
//   rcomp f g ∈ ord_iso(A,r,C,t)
opaque symbol ord_iso_trans (g f A r B s C t : τ ι) :
  π (g ∈ ord_iso A r B s) → π (f ∈ ord_iso B s C t) →
  π (rcomp f g ∈ ord_iso A r C t) ≔
begin
  assume g f A r B s C t hg hf;
  have hgbij : π (g ∈ bij A B) { refine ord_iso_is_bij g A r B s hg };
  have hfbij : π (f ∈ bij B C) { refine ord_iso_is_bij f B s C t hf };
  have hgfun : π (g ∈ Pi A (λ _, B)) { refine bij_is_fun g A B hgbij };
  have hffun : π (f ∈ Pi B (λ _, C)) { refine bij_is_fun f B C hfbij };
  have hcbij : π (rcomp f g ∈ bij A C) { refine comp_bij f g A B C hgbij hfbij };
  refine ord_isoI (rcomp f g) A r C t hcbij _;
  assume x hxA y hyA;
  have hgx : π (fapply g x ∈ B) { refine bij_apply g A B x hgbij hxA };
  have hgy : π (fapply g y ∈ B) { refine bij_apply g A B y hgbij hyA };
  have hcx : π (fapply (rcomp f g) x = fapply f (fapply g x)) { refine comp_fun_apply f g A B C x hgfun hffun hxA };
  have hcy : π (fapply (rcomp f g) y = fapply f (fapply g y)) { refine comp_fun_apply f g A B C y hgfun hffun hyA };
  have hfcond : π (Ball B (λ u, Ball B (λ v, (Pair u v ∈ s) ⇔ (Pair (fapply f u) (fapply f v) ∈ t))))
    { refine ord_iso_memD f B s C t hf };
  have hgcond : π (Ball A (λ u, Ball A (λ v, (Pair u v ∈ r) ⇔ (Pair (fapply g u) (fapply g v) ∈ s))))
    { refine ord_iso_memD g A r B s hg };
  apply ∧ᵢ
  { assume hr;
    have hs : π (Pair (fapply g x) (fapply g y) ∈ s) { refine ord_iso_apply g A r B s x y hg hr hxA hyA };
    have ht : π (Pair (fapply f (fapply g x)) (fapply f (fapply g y)) ∈ t) { refine ord_iso_apply f B s C t (fapply g x) (fapply g y) hf hs hgx hgy };
    rewrite hcx; rewrite hcy; apply ht }
  { assume ht0;
    have ht : π (Pair (fapply f (fapply g x)) (fapply f (fapply g y)) ∈ t) { rewrite left hcx; rewrite left hcy; apply ht0 };
    have hs : π (Pair (fapply g x) (fapply g y) ∈ s) { refine ∧ₑ₂ (hfcond (fapply g x) hgx (fapply g y) hgy) ht };
    refine ∧ₑ₂ (hgcond x hxA y hyA) hs }
end;

// ===========================================================================
// Section: Order-isomorphisms preserve ordering properties
// ===========================================================================

// part_ord_ord_iso: part_ord(B,s) → f ∈ ord_iso(A,r,B,s) → part_ord(A,r)
opaque symbol part_ord_ord_iso (A r B s f : τ ι) :
  π (part_ord B s) → π (f ∈ ord_iso A r B s) → π (part_ord A r) ≔
begin
  assume A r B s f hpo hf;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hirrB : π (irrefl_on B s) { refine ∧ₑ₁ (part_ordD B s hpo) };
  have htrB : π (trans_on B s) { refine ∧ₑ₂ (part_ordD B s hpo) };
  have hcond : π (Ball A (λ u, Ball A (λ v, (Pair u v ∈ r) ⇔ (Pair (fapply f u) (fapply f v) ∈ s))))
    { refine ord_iso_memD f A r B s hf };
  rewrite part_ord_def;
  apply ∧ᵢ
  { refine irrefl_onI A r _;
    assume x hxA hxx;
    have hfx : π (fapply f x ∈ B) { refine bij_apply f A B x hbij hxA };
    have hsxx : π (Pair (fapply f x) (fapply f x) ∈ s) { refine ord_iso_apply f A r B s x x hf hxx hxA hxA };
    refine irrefl_onD B s (fapply f x) hirrB hfx hsxx }
  { refine trans_onI A r _;
    assume x hxA y hyA z hzA hxy hyz;
    have hfx : π (fapply f x ∈ B) { refine bij_apply f A B x hbij hxA };
    have hfy : π (fapply f y ∈ B) { refine bij_apply f A B y hbij hyA };
    have hfz : π (fapply f z ∈ B) { refine bij_apply f A B z hbij hzA };
    have hsxy : π (Pair (fapply f x) (fapply f y) ∈ s) { refine ord_iso_apply f A r B s x y hf hxy hxA hyA };
    have hsyz : π (Pair (fapply f y) (fapply f z) ∈ s) { refine ord_iso_apply f A r B s y z hf hyz hyA hzA };
    have hsxz : π (Pair (fapply f x) (fapply f z) ∈ s)
      { refine trans_onD B s (fapply f x) (fapply f y) (fapply f z) htrB hfx hfy hfz hsxy hsyz };
    refine ∧ₑ₂ (hcond x hxA z hzA) hsxz }
end;

// linear_ord_iso: linear(B,s) → f ∈ ord_iso(A,r,B,s) → linear(A,r)
opaque symbol linear_ord_iso (A r B s f : τ ι) :
  π (linear B s) → π (f ∈ ord_iso A r B s) → π (linear A r) ≔
begin
  assume A r B s f hlin hf;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hinj : π (f ∈ inj A B) { refine bij_is_inj f A B hbij };
  have hcond : π (Ball A (λ u, Ball A (λ v, (Pair u v ∈ r) ⇔ (Pair (fapply f u) (fapply f v) ∈ s))))
    { refine ord_iso_memD f A r B s hf };
  refine linearI A r _;
  assume x hxA y hyA;
  have hfx : π (fapply f x ∈ B) { refine bij_apply f A B x hbij hxA };
  have hfy : π (fapply f y ∈ B) { refine bij_apply f A B y hbij hyA };
  have htri : π (Pair (fapply f x) (fapply f y) ∈ s ∨ (fapply f x = fapply f y ∨ Pair (fapply f y) (fapply f x) ∈ s))
    { refine linearD B s (fapply f x) (fapply f y) hlin hfx hfy };
  refine ∨ₑ htri _ _
  { assume hs; apply ∨ᵢ₁; refine ∧ₑ₂ (hcond x hxA y hyA) hs }
  { assume h2; refine ∨ₑ h2 _ _
    { assume heqf; apply ∨ᵢ₂; apply ∨ᵢ₁; refine inj_apply_equality f A B x y hinj heqf hxA hyA }
    { assume hs; apply ∨ᵢ₂; apply ∨ᵢ₂; refine ∧ₑ₂ (hcond y hyA x hxA) hs } }
end;

// wf_on_ord_iso: wf(B,s) → f ∈ ord_iso(A,r,B,s) → wf(A,r)
opaque symbol wf_on_ord_iso (A r B s f : τ ι) :
  π (wf B s) → π (f ∈ ord_iso A r B s) → π (wf A r) ≔
begin
  assume A r B s f hwf hf;
  rewrite wf_def;
  assume Z hZA hZne;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hWB : π (RepFun Z (λ z, fapply f z) ⊆ B) {
    assume b hb;
    have hex : π (Bex Z (λ z, b = fapply f z)) { refine ∧ₑ₁ (RepFun_iff b Z (λ z, fapply f z)) hb };
    refine ∃ₑ hex _; assume z hz;
    have hzZ : π (z ∈ Z) { refine ∧ₑ₁ hz };
    have hbeq : π (b = fapply f z) { refine ∧ₑ₂ hz };
    rewrite hbeq; refine bij_apply f A B z hbij (hZA z hzZ)
  };
  have hWne : π (RepFun Z (λ z, fapply f z) ≠ empty) {
    refine not_emptyE Z (RepFun Z (λ z, fapply f z) ≠ empty) hZne _;
    assume z hzZ;
    refine ne_empty (RepFun Z (λ z2, fapply f z2)) (fapply f z) (RepFunI z Z (λ z2, fapply f z2) hzZ)
  };
  have hmin : π (Bex (RepFun Z (λ z, fapply f z)) (λ b0, Ball (RepFun Z (λ z, fapply f z)) (λ c, Pair c b0 ∉ s)))
    { refine wfD B s hwf (RepFun Z (λ z, fapply f z)) hWB hWne };
  refine ∃ₑ hmin _; assume b0 hb0;
  have hb0W : π (b0 ∈ RepFun Z (λ z, fapply f z)) { refine ∧ₑ₁ hb0 };
  have hb0min : π (Ball (RepFun Z (λ z, fapply f z)) (λ c, Pair c b0 ∉ s)) { refine ∧ₑ₂ hb0 };
  have hex0 : π (Bex Z (λ z, b0 = fapply f z)) { refine ∧ₑ₁ (RepFun_iff b0 Z (λ z, fapply f z)) hb0W };
  refine ∃ₑ hex0 _; assume z0 hz0;
  have hz0Z : π (z0 ∈ Z) { refine ∧ₑ₁ hz0 };
  have hb0eq : π (b0 = fapply f z0) { refine ∧ₑ₂ hz0 };
  refine ∃ᵢ z0 _;
  apply ∧ᵢ hz0Z _;
  assume y hyZ hyr;
  have hyA : π (y ∈ A) { refine hZA y hyZ };
  have hz0A : π (z0 ∈ A) { refine hZA z0 hz0Z };
  have hsy : π (Pair (fapply f y) (fapply f z0) ∈ s) { refine ord_iso_apply f A r B s y z0 hf hyr hyA hz0A };
  have hfyW : π (fapply f y ∈ RepFun Z (λ z, fapply f z)) { refine RepFunI y Z (λ z, fapply f z) hyZ };
  have hnot : π (Pair (fapply f y) b0 ∉ s) { refine hb0min (fapply f y) hfyW };
  have hsy2 : π (Pair (fapply f y) b0 ∈ s) { rewrite hb0eq; apply hsy };
  refine hnot hsy2
end;

// well_ord_ord_iso: well_ord(B,s) → f ∈ ord_iso(A,r,B,s) → well_ord(A,r)
opaque symbol well_ord_ord_iso (A r B s f : τ ι) :
  π (well_ord B s) → π (f ∈ ord_iso A r B s) → π (well_ord A r) ≔
begin
  assume A r B s f hwo hf;
  have htot : π (tot_ord B s) { refine ∧ₑ₁ (well_ordD B s hwo) };
  have hwfB : π (wf B s) { refine ∧ₑ₂ (well_ordD B s hwo) };
  have hpoB : π (part_ord B s) { refine ∧ₑ₁ (tot_ordD B s htot) };
  have hlinB : π (linear B s) { refine ∧ₑ₂ (tot_ordD B s htot) };
  rewrite well_ord_def;
  apply ∧ᵢ
  { rewrite tot_ord_def;
    apply ∧ᵢ
    { refine part_ord_ord_iso A r B s f hpoB hf }
    { refine linear_ord_iso A r B s f hlinB hf } }
  { refine wf_on_ord_iso A r B s f hwfB hf }
end;

// ===========================================================================
// Section: Kunen's Lemma 6.1 and related
// ===========================================================================

// well_ord_iso_subset_lemma: well_ord(A,r) → f ∈ ord_iso(A,r,A',r) →
//   A' ⊆ A → y ∈ A → ¬(Pair(f`y, y) ∈ r)
opaque symbol well_ord_iso_subset_lemma (A r f A2 y : τ ι) :
  π (well_ord A r) → π (f ∈ ord_iso A r A2 r) → π (A2 ⊆ A) → π (y ∈ A) →
  π (Pair (fapply f y) y ∉ r) ≔
begin
  assume A r f A2 y hwo hf hA2A hyA;
  have hwfA : π (wf A r) { refine well_ord_is_wf A r hwo };
  have hbij : π (f ∈ bij A A2) { refine ord_iso_is_bij f A r A2 r hf };
  have hall : π (Ball A (λ z, Pair (fapply f z) z ∉ r)) {
    refine wf_induct A r (λ z, Pair (fapply f z) z ∉ r) hwfA _;
    assume z hzA hIH hcontra;
    have hfzA2 : π (fapply f z ∈ A2) { refine bij_apply f A A2 z hbij hzA };
    have hfzA : π (fapply f z ∈ A) { refine hA2A (fapply f z) hfzA2 };
    have hr2 : π (Pair (fapply f (fapply f z)) (fapply f z) ∈ r) { refine ord_iso_apply f A r A2 r (fapply f z) z hf hcontra hfzA hzA };
    have hnot : π (Pair (fapply f (fapply f z)) (fapply f z) ∉ r) { refine hIH (fapply f z) hfzA hcontra };
    refine hnot hr2
  };
  refine hall y hyA
end;

// well_ord_iso_predE: well_ord(A,r) → f ∈ ord_iso(A,r,pred(A,x,r),r) →
//   x ∈ A → ⊥
// Kunen's Lemma 6.1: no order-iso to an initial segment of a well-ordering
opaque symbol well_ord_iso_predE (A r f x : τ ι) :
  π (well_ord A r) → π (f ∈ ord_iso A r (pred A x r) r) →
  π (x ∈ A) → π ⊥ ≔
begin
  assume A r f x hwo hf hxA;
  have hsub : π (pred A x r ⊆ A) { refine pred_subset A x r };
  have hnot : π (Pair (fapply f x) x ∉ r) { refine well_ord_iso_subset_lemma A r f (pred A x r) x hwo hf hsub hxA };
  have hbij : π (f ∈ bij A (pred A x r)) { refine ord_iso_is_bij f A r (pred A x r) r hf };
  have hfx : π (fapply f x ∈ pred A x r) { refine bij_apply f A (pred A x r) x hbij hxA };
  have hr : π (Pair (fapply f x) x ∈ r)
    { refine ∧ₑ₁ (∧ₑ₁ (pred_iff (fapply f x) A x r) hfx) };
  refine hnot hr
end;

// well_ord_iso_pred_eq: well_ord(A,r) → f ∈ ord_iso(pred(A,a,r),r,pred(A,c,r),r)
//   → a ∈ A → c ∈ A → a = c
opaque symbol well_ord_iso_pred_eq (A r f a c : τ ι) :
  π (well_ord A r) → π (f ∈ ord_iso (pred A a r) r (pred A c r) r) →
  π (a ∈ A) → π (c ∈ A) → π (a = c) ≔
begin
  assume A r f a c hwo hf haA hcA;
  have htr : π (trans_on A r) { refine well_ord_is_trans_on A r hwo };
  have hlin : π (linear A r) { refine well_ord_is_linear A r hwo };
  refine linearE A r a c (a = c) hlin haA hcA _ _ _
  { assume hac;
    refine ⊥ₑ _;
    have haPc : π (a ∈ pred A c r) { refine predI a A c r hac haA };
    have hpeq : π (pred (pred A c r) a r = pred A a r) { refine trans_pred_pred_eq A r c a htr hac hcA haA };
    have hf2 : π (f ∈ ord_iso (pred (pred A c r) a r) r (pred A c r) r) { rewrite hpeq; apply hf };
    have hcf : π (converse f ∈ ord_iso (pred A c r) r (pred (pred A c r) a r) r) { refine ord_iso_sym f (pred (pred A c r) a r) r (pred A c r) r hf2 };
    have hwoPc : π (well_ord (pred A c r) r) { refine well_ord_subset A (pred A c r) r hwo (pred_subset A c r) };
    refine well_ord_iso_predE (pred A c r) r (converse f) a hwoPc hcf haPc }
  { assume he; apply he }
  { assume hca;
    refine ⊥ₑ _;
    have hcPa : π (c ∈ pred A a r) { refine predI c A a r hca hcA };
    have hpeq2 : π (pred (pred A a r) c r = pred A c r) { refine trans_pred_pred_eq A r a c htr hca haA hcA };
    have hf3 : π (f ∈ ord_iso (pred A a r) r (pred (pred A a r) c r) r) { rewrite hpeq2; apply hf };
    have hwoPa : π (well_ord (pred A a r) r) { refine well_ord_subset A (pred A a r) r hwo (pred_subset A a r) };
    refine well_ord_iso_predE (pred A a r) r f c hwoPa hf3 hcPa }
end;

// ===========================================================================
// Section: Properties of converse(r) (by Grabczewski)
// ===========================================================================

// irrefl_converse: irrefl_on(A,r) → irrefl_on(A,converse(r))
opaque symbol irrefl_converse (A r : τ ι) :
  π (irrefl_on A r) → π (irrefl_on A (converse r)) ≔
begin
  assume A r hirr;
  refine irrefl_onI A (converse r) _;
  assume x hxA hxx;
  // Pair(x,x) ∈ converse(r) → Pair(x,x) ∈ r
  have h : π (Pair x x ∈ r) { refine converseD x x r hxx };
  refine irrefl_onD A r x hirr hxA h
end;

// trans_on_converse: trans_on(A,r) → trans_on(A,converse(r))
opaque symbol trans_on_converse (A r : τ ι) :
  π (trans_on A r) → π (trans_on A (converse r)) ≔
begin
  assume A r htr;
  refine trans_onI A (converse r) _;
  assume x hxA y hyA z hzA hxy hyz;
  // Pair(x,y) ∈ converse(r) → Pair(y,x) ∈ r
  have hyx : π (Pair y x ∈ r) { refine converseD x y r hxy };
  // Pair(y,z) ∈ converse(r) → Pair(z,y) ∈ r
  have hzy : π (Pair z y ∈ r) { refine converseD y z r hyz };
  // By trans: Pair(z,y) ∈ r and Pair(y,x) ∈ r → Pair(z,x) ∈ r
  have hzx : π (Pair z x ∈ r) { refine trans_onD A r z y x htr hzA hyA hxA hzy hyx };
  // Pair(z,x) ∈ r → Pair(x,z) ∈ converse(r)
  refine converseI z x r hzx
end;

// part_ord_converse: part_ord(A,r) → part_ord(A,converse(r))
opaque symbol part_ord_converse (A r : τ ι) :
  π (part_ord A r) → π (part_ord A (converse r)) ≔
begin
  assume A r hpo;
  rewrite part_ord_def;
  apply ∧ᵢ
  { refine irrefl_converse A r (∧ₑ₁ (part_ordD A r hpo)) }
  { refine trans_on_converse A r (∧ₑ₂ (part_ordD A r hpo)) }
end;

// linear_converse: linear(A,r) → linear(A,converse(r))
opaque symbol linear_converse (A r : τ ι) :
  π (linear A r) → π (linear A (converse r)) ≔
begin
  assume A r hlin;
  refine linearI A (converse r) _;
  assume x hxA y hyA;
  have htri : π (Pair x y ∈ r ∨ (x = y ∨ Pair y x ∈ r)) { refine linearD A r x y hlin hxA hyA };
  refine ∨ₑ htri _ _
  { assume hxy;
    // Pair(x,y) ∈ r → Pair(y,x) ∈ converse(r)
    apply ∨ᵢ₂; apply ∨ᵢ₂;
    refine converseI x y r hxy }
  { assume h2;
    refine ∨ₑ h2 _ _
    { assume heq; apply ∨ᵢ₂; apply ∨ᵢ₁; apply heq }
    { assume hyx;
      // Pair(y,x) ∈ r → Pair(x,y) ∈ converse(r)
      apply ∨ᵢ₁;
      refine converseI y x r hyx } }
end;

// tot_ord_converse: tot_ord(A,r) → tot_ord(A,converse(r))
opaque symbol tot_ord_converse (A r : τ ι) :
  π (tot_ord A r) → π (tot_ord A (converse r)) ≔
begin
  assume A r htot;
  rewrite tot_ord_def;
  apply ∧ᵢ
  { refine part_ord_converse A r (∧ₑ₁ (tot_ordD A r htot)) }
  { refine linear_converse A r (∧ₑ₂ (tot_ordD A r htot)) }
end;

// ===========================================================================
// Section: First element of well-ordered sets (by Grabczewski)
// ===========================================================================

// first_is_elem: first(b,B,r) → b ∈ B
opaque symbol first_is_elem (b B r : τ ι) :
  π (first b B r) → π (b ∈ B) ≔
begin
  assume b B r hf;
  refine ∧ₑ₁ (firstD b B r hf)
end;

// well_ord_imp_ex1_first: well_ord(A,r) → B ⊆ A → B ≠ empty → ∃!b. first(b,B,r)
opaque symbol well_ord_imp_ex1_first (A r B : τ ι) :
  π (well_ord A r) → π (B ⊆ A) → π (B ≠ empty) →
  π (`∃ (b : τ ι), first b B r ∧ (`∀ (c : τ ι), first c B r ⇒ c = b)) ≔
begin
  assume A r B hwo hBA hBne;
  have hwfA : π (wf A r) { refine well_ord_is_wf A r hwo };
  have hlin : π (linear A r) { refine well_ord_is_linear A r hwo };
  have hmin : π (Bex B (λ x0, Ball B (λ y, Pair y x0 ∉ r))) { refine wfD A r hwfA B hBA hBne };
  refine ∃ₑ hmin _;
  assume x0 hx0;
  have hx0B : π (x0 ∈ B) { refine ∧ₑ₁ hx0 };
  have hx0min : π (Ball B (λ y, Pair y x0 ∉ r)) { refine ∧ₑ₂ hx0 };
  have hx0A : π (x0 ∈ A) { refine hBA x0 hx0B };
  refine ∃ᵢ x0 _;
  apply ∧ᵢ
  { rewrite first_def;
    apply ∧ᵢ hx0B _;
    assume v hvB hvne;
    have hvA : π (v ∈ A) { refine hBA v hvB };
    refine linearE A r x0 v (Pair x0 v ∈ r) hlin hx0A hvA _ _ _
    { assume h; apply h }
    { assume he; refine ⊥ₑ (hvne (eq_sym he)) }
    { assume hvx0; refine ⊥ₑ (hx0min v hvB hvx0) } }
  { assume c hc;
    have hcB : π (c ∈ B) { refine ∧ₑ₁ (firstD c B r hc) };
    have hcfirst : π (Ball B (λ v, v ≠ c ⇒ Pair c v ∈ r)) { refine ∧ₑ₂ (firstD c B r hc) };
    refine ∨ₑ (em (c = x0)) _ _
    { assume he; apply he }
    { assume hne;
      refine ⊥ₑ _;
      have hx0nec : π (x0 ≠ c) { assume he2; refine hne (eq_sym he2) };
      have hcx0 : π (Pair c x0 ∈ r) { refine hcfirst x0 hx0B hx0nec };
      have hncx0 : π (Pair c x0 ∉ r) { refine hx0min c hcB };
      refine hncx0 hcx0 } }
end;

// the_first_in: well_ord(A,r) → B ⊆ A → B ≠ 0 → (THE b. first(b,B,r)) ∈ B
opaque symbol the_first_in (A r B : τ ι) :
  π (well_ord A r) → π (B ⊆ A) → π (B ≠ empty) →
  π (The (λ b, first b B r) ∈ B) ≔
begin
  assume A r B hwo hBA hBne;
  have hex : π (`∃ (b : τ ι), first b B r ∧ (`∀ (c : τ ι), first c B r ⇒ c = b))
    { refine well_ord_imp_ex1_first A r B hwo hBA hBne };
  refine first_is_elem (The (λ b, first b B r)) B r _;
  refine theI (λ b, first b B r) hex
end;

// ===========================================================================
// Section: Monotone map lemmas
// ===========================================================================

// mono_map_is_inj: linear(A,r) → wf(B,s) → f ∈ mono_map(A,r,B,s) → f ∈ inj(A,B)
opaque symbol mono_map_is_inj (A r B s f : τ ι) :
  π (linear A r) → π (wf B s) → π (f ∈ mono_map A r B s) →
  π (f ∈ inj A B) ≔
begin
  assume A r B s f hlin hwf hf;
  have hfun : π (f ∈ Pi A (λ _, B)) { refine mono_map_is_fun f A r B s hf };
  have hf' : π (f ∈ Collect (Pi A (λ _, B))
      (λ g, Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply g x) (fapply g y) ∈ s))))
    { refine ind_eq (eq_sym (mono_map_def A r B s)) (λ w, f ∈ w) hf };
  have hmono : π (Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply f x) (fapply f y) ∈ s)))
    { refine CollectD2 f (Pi A (λ _, B)) (λ g, Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply g x) (fapply g y) ∈ s))) hf' };
  rewrite inj_def;
  refine CollectI f (Pi A (λ _, B)) (λ g, Ball A (λ w, Ball A (λ x, fapply g w = fapply g x ⇒ w = x))) hfun _;
  assume w hw x hx heq;
  refine linearE A r w x (w = x) hlin hw hx _ _ _
  { assume hwx;
    have hs : π (Pair (fapply f w) (fapply f x) ∈ s) { refine hmono w hw x hx hwx };
    have hfwB : π (fapply f w ∈ B) { refine apply_type f A B w hfun hw };
    refine ⊥ₑ (wf_not_refl B s (fapply f w) hwf hfwB (ind_eq heq (λ z, Pair (fapply f w) z ∈ s) hs)) }
  { assume he; apply he }
  { assume hxw;
    have hs : π (Pair (fapply f x) (fapply f w) ∈ s) { refine hmono x hx w hw hxw };
    have hfxB : π (fapply f x ∈ B) { refine apply_type f A B x hfun hx };
    refine ⊥ₑ (wf_not_refl B s (fapply f x) hwf hfxB (ind_eq (eq_sym heq) (λ z, Pair (fapply f x) z ∈ s) hs)) }
end;

// mono_map_trans: g ∈ mono_map(A,r,B,s) → f ∈ mono_map(B,s,C,t) →
//   rcomp f g ∈ mono_map(A,r,C,t)
opaque symbol mono_map_trans (g f A r B s C t : τ ι) :
  π (g ∈ mono_map A r B s) → π (f ∈ mono_map B s C t) →
  π (rcomp f g ∈ mono_map A r C t) ≔
begin
  assume g f A r B s C t hg hf;
  have hgfun : π (g ∈ Pi A (λ _, B)) { refine mono_map_is_fun g A r B s hg };
  have hffun : π (f ∈ Pi B (λ _, C)) { refine mono_map_is_fun f B s C t hf };
  have hg' : π (g ∈ Collect (Pi A (λ _, B))
      (λ k, Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply k x) (fapply k y) ∈ s))))
    { refine ind_eq (eq_sym (mono_map_def A r B s)) (λ w, g ∈ w) hg };
  have hf' : π (f ∈ Collect (Pi B (λ _, C))
      (λ k, Ball B (λ x, Ball B (λ y, Pair x y ∈ s ⇒ Pair (fapply k x) (fapply k y) ∈ t))))
    { refine ind_eq (eq_sym (mono_map_def B s C t)) (λ w, f ∈ w) hf };
  have hgmono : π (Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply g x) (fapply g y) ∈ s)))
    { refine CollectD2 g (Pi A (λ _, B)) (λ k, Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply k x) (fapply k y) ∈ s))) hg' };
  have hfmono : π (Ball B (λ x, Ball B (λ y, Pair x y ∈ s ⇒ Pair (fapply f x) (fapply f y) ∈ t)))
    { refine CollectD2 f (Pi B (λ _, C)) (λ k, Ball B (λ x, Ball B (λ y, Pair x y ∈ s ⇒ Pair (fapply k x) (fapply k y) ∈ t))) hf' };
  have hcompfun : π (rcomp f g ∈ Pi A (λ _, C)) { refine comp_fun f g A B C hgfun hffun };
  rewrite mono_map_def;
  refine CollectI (rcomp f g) (Pi A (λ _, C)) (λ k, Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply k x) (fapply k y) ∈ t))) hcompfun _;
  assume x hxA y hyA hxy;
  have hgx : π (fapply g x ∈ B) { refine apply_type g A B x hgfun hxA };
  have hgy : π (fapply g y ∈ B) { refine apply_type g A B y hgfun hyA };
  have hs : π (Pair (fapply g x) (fapply g y) ∈ s) { refine hgmono x hxA y hyA hxy };
  have ht : π (Pair (fapply f (fapply g x)) (fapply f (fapply g y)) ∈ t) { refine hfmono (fapply g x) hgx (fapply g y) hgy hs };
  have hcx : π (fapply (rcomp f g) x = fapply f (fapply g x)) { refine comp_fun_apply f g A B C x hgfun hffun hxA };
  have hcy : π (fapply (rcomp f g) y = fapply f (fapply g y)) { refine comp_fun_apply f g A B C y hgfun hffun hyA };
  rewrite hcx; rewrite hcy; apply ht
end;

// ===========================================================================
// Section: Well-ordering uniqueness (Kunen's Lemma 6.2)
// ===========================================================================

// well_ord_iso_unique_lemma: well_ord(A,r) → f,g ∈ ord_iso(A,r,B,s) → y ∈ A →
//   ¬ Pair(g`y, f`y) ∈ s   (Halmos)
opaque symbol well_ord_iso_unique_lemma (A r B s f g y : τ ι) :
  π (well_ord A r) → π (f ∈ ord_iso A r B s) → π (g ∈ ord_iso A r B s) → π (y ∈ A) →
  π (Pair (fapply g y) (fapply f y) ∉ s) ≔
begin
  assume A r B s f g y hwo hf hg hyA hcontra;
  have hfbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hgbij : π (g ∈ bij A B) { refine ord_iso_is_bij g A r B s hg };
  have hcf : π (converse f ∈ ord_iso B s A r) { refine ord_iso_sym f A r B s hf };
  have hcfbij : π (converse f ∈ bij B A) { refine converse_bij f A B hfbij };
  have hh : π (rcomp (converse f) g ∈ ord_iso A r A r) { refine ord_iso_trans g (converse f) A r B s A r hg hcf };
  have hnot : π (Pair (fapply (rcomp (converse f) g) y) y ∉ r) { refine well_ord_iso_subset_lemma A r (rcomp (converse f) g) A y hwo hh (subset_refl A) hyA };
  have hgy : π (fapply g y ∈ B) { refine bij_apply g A B y hgbij hyA };
  have hfy : π (fapply f y ∈ B) { refine bij_apply f A B y hfbij hyA };
  have hhy : π (fapply (rcomp (converse f) g) y = fapply (converse f) (fapply g y))
    { refine comp_fun_apply (converse f) g A B A y (bij_is_fun g A B hgbij) (bij_is_fun (converse f) B A hcfbij) hyA };
  have hr : π (Pair (fapply (converse f) (fapply g y)) (fapply (converse f) (fapply f y)) ∈ r)
    { refine ord_iso_converse f A r B s (fapply g y) (fapply f y) hf hcontra hgy hfy };
  have hcffy : π (fapply (converse f) (fapply f y) = y) { refine left_inverse_bij f A B y hfbij hyA };
  have hr2 : π (Pair (fapply (converse f) (fapply g y)) y ∈ r)
    { refine ind_eq (eq_sym hcffy) (λ z, Pair (fapply (converse f) (fapply g y)) z ∈ r) hr };
  have hr3 : π (Pair (fapply (rcomp (converse f) g) y) y ∈ r) { rewrite hhy; apply hr2 };
  refine hnot hr3
end;

// well_ord_iso_unique: well_ord(A,r) → f ∈ ord_iso(A,r,B,s) →
//   g ∈ ord_iso(A,r,B,s) → f = g
opaque symbol well_ord_iso_unique (A r B s f g : τ ι) :
  π (well_ord A r) → π (f ∈ ord_iso A r B s) → π (g ∈ ord_iso A r B s) →
  π (f = g) ≔
begin
  assume A r B s f g hwo hf hg;
  have hfbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hgbij : π (g ∈ bij A B) { refine ord_iso_is_bij g A r B s hg };
  have hffun : π (f ∈ Pi A (λ _, B)) { refine bij_is_fun f A B hfbij };
  have hgfun : π (g ∈ Pi A (λ _, B)) { refine bij_is_fun g A B hgbij };
  have hcf : π (converse f ∈ ord_iso B s A r) { refine ord_iso_sym f A r B s hf };
  have hwoB : π (well_ord B s) { refine well_ord_ord_iso B s A r (converse f) hwo hcf };
  have hlinB : π (linear B s) { refine well_ord_is_linear B s hwoB };
  refine fun_extension f g A (λ _, B) (λ _, B) hffun hgfun _;
  assume x hxA;
  have hfx : π (fapply f x ∈ B) { refine apply_type f A B x hffun hxA };
  have hgx : π (fapply g x ∈ B) { refine apply_type g A B x hgfun hxA };
  have htri : π (Pair (fapply f x) (fapply g x) ∈ s ∨ (fapply f x = fapply g x ∨ Pair (fapply g x) (fapply f x) ∈ s))
    { refine linearD B s (fapply f x) (fapply g x) hlinB hfx hgx };
  refine ∨ₑ htri _ _
  { assume h1; refine ⊥ₑ (well_ord_iso_unique_lemma A r B s g f x hwo hg hf hxA h1) }
  { assume h2; refine ∨ₑ h2 _ _
    { assume he; apply he }
    { assume h3; refine ⊥ₑ (well_ord_iso_unique_lemma A r B s f g x hwo hf hg hxA h3) } }
end;

// ===========================================================================
// Section: Restricting orderings to intersections (by Grabczewski)
// ===========================================================================

// irrefl_Int_iff: irrefl_on(A, Int r (Sigma A (λ _, A))) ↔ irrefl_on(A, r)
opaque symbol irrefl_Int_iff (A r : τ ι) :
  π (irrefl_on A (Int r (Sigma A (λ _, A))) ⇔ irrefl_on A r) ≔
begin
  assume A r;
  apply ∧ᵢ
  { assume hirr;
    refine irrefl_onI A r _;
    assume x hxA hxx;
    have h : π (Pair x x ∈ Int r (Sigma A (λ _, A))) {
      refine IntI (Pair x x) r (Sigma A (λ _, A)) hxx (SigmaI x x A (λ _, A) hxA hxA)
    };
    refine irrefl_onD A (Int r (Sigma A (λ _, A))) x hirr hxA h }
  { assume hirr;
    refine irrefl_onI A (Int r (Sigma A (λ _, A))) _;
    assume x hxA hxx;
    have hxxr : π (Pair x x ∈ r) { refine IntD1 (Pair x x) r (Sigma A (λ _, A)) hxx };
    refine irrefl_onD A r x hirr hxA hxxr }
end;

// trans_on_Int_iff: trans_on(A, Int r (Sigma A (λ _, A))) ↔ trans_on(A, r)
opaque symbol trans_on_Int_iff (A r : τ ι) :
  π (trans_on A (Int r (Sigma A (λ _, A))) ⇔ trans_on A r) ≔
begin
  assume A r;
  apply ∧ᵢ
  { assume htr;
    refine trans_onI A r _;
    assume x hxA y hyA z hzA hxy hyz;
    have hxy2 : π (Pair x y ∈ Int r (Sigma A (λ _, A))) {
      refine IntI (Pair x y) r (Sigma A (λ _, A)) hxy (SigmaI x y A (λ _, A) hxA hyA) };
    have hyz2 : π (Pair y z ∈ Int r (Sigma A (λ _, A))) {
      refine IntI (Pair y z) r (Sigma A (λ _, A)) hyz (SigmaI y z A (λ _, A) hyA hzA) };
    have h : π (Pair x z ∈ Int r (Sigma A (λ _, A)))
      { refine trans_onD A (Int r (Sigma A (λ _, A))) x y z htr hxA hyA hzA hxy2 hyz2 };
    refine IntD1 (Pair x z) r (Sigma A (λ _, A)) h }
  { assume htr;
    refine trans_onI A (Int r (Sigma A (λ _, A))) _;
    assume x hxA y hyA z hzA hxy hyz;
    have hxyr : π (Pair x y ∈ r) { refine IntD1 (Pair x y) r (Sigma A (λ _, A)) hxy };
    have hyzr : π (Pair y z ∈ r) { refine IntD1 (Pair y z) r (Sigma A (λ _, A)) hyz };
    have hxzr : π (Pair x z ∈ r) { refine trans_onD A r x y z htr hxA hyA hzA hxyr hyzr };
    refine IntI (Pair x z) r (Sigma A (λ _, A)) hxzr (SigmaI x z A (λ _, A) hxA hzA) }
end;

// part_ord_Int_iff: part_ord(A, Int r (Sigma A (λ _, A))) ↔ part_ord(A, r)
opaque symbol part_ord_Int_iff (A r : τ ι) :
  π (part_ord A (Int r (Sigma A (λ _, A))) ⇔ part_ord A r) ≔
begin
  assume A r;
  apply ∧ᵢ
  { assume h;
    rewrite part_ord_def;
    apply ∧ᵢ
    { refine ∧ₑ₁ (irrefl_Int_iff A r) (∧ₑ₁ (part_ordD A (Int r (Sigma A (λ _, A))) h)) }
    { refine ∧ₑ₁ (trans_on_Int_iff A r) (∧ₑ₂ (part_ordD A (Int r (Sigma A (λ _, A))) h)) } }
  { assume h;
    rewrite part_ord_def;
    apply ∧ᵢ
    { refine ∧ₑ₂ (irrefl_Int_iff A r) (∧ₑ₁ (part_ordD A r h)) }
    { refine ∧ₑ₂ (trans_on_Int_iff A r) (∧ₑ₂ (part_ordD A r h)) } }
end;

// linear_Int_iff: linear(A, Int r (Sigma A (λ _, A))) ↔ linear(A, r)
opaque symbol linear_Int_iff (A r : τ ι) :
  π (linear A (Int r (Sigma A (λ _, A))) ⇔ linear A r) ≔
begin
  assume A r;
  apply ∧ᵢ
  { assume hlin;
    refine linearI A r _;
    assume x hxA y hyA;
    have h : π (Pair x y ∈ Int r (Sigma A (λ _, A)) ∨
               (x = y ∨ Pair y x ∈ Int r (Sigma A (λ _, A))))
      { refine linearD A (Int r (Sigma A (λ _, A))) x y hlin hxA hyA };
    refine ∨ₑ h _ _
    { assume hxy;
      apply ∨ᵢ₁;
      refine IntD1 (Pair x y) r (Sigma A (λ _, A)) hxy }
    { assume h2;
      apply ∨ᵢ₂;
      refine ∨ₑ h2 _ _
      { assume heq; apply ∨ᵢ₁; apply heq }
      { assume hyx;
        apply ∨ᵢ₂;
        refine IntD1 (Pair y x) r (Sigma A (λ _, A)) hyx } } }
  { assume hlin;
    refine linearI A (Int r (Sigma A (λ _, A))) _;
    assume x hxA y hyA;
    have h : π (Pair x y ∈ r ∨ (x = y ∨ Pair y x ∈ r))
      { refine linearD A r x y hlin hxA hyA };
    refine ∨ₑ h _ _
    { assume hxy;
      apply ∨ᵢ₁;
      refine IntI (Pair x y) r (Sigma A (λ _, A)) hxy (SigmaI x y A (λ _, A) hxA hyA) }
    { assume h2;
      apply ∨ᵢ₂;
      refine ∨ₑ h2 _ _
      { assume heq; apply ∨ᵢ₁; apply heq }
      { assume hyx;
        apply ∨ᵢ₂;
        refine IntI (Pair y x) r (Sigma A (λ _, A)) hyx (SigmaI y x A (λ _, A) hyA hxA) } } }
end;

// tot_ord_Int_iff: tot_ord(A, Int r (Sigma A (λ _, A))) ↔ tot_ord(A, r)
opaque symbol tot_ord_Int_iff (A r : τ ι) :
  π (tot_ord A (Int r (Sigma A (λ _, A))) ⇔ tot_ord A r) ≔
begin
  assume A r;
  apply ∧ᵢ
  { assume h;
    rewrite tot_ord_def;
    apply ∧ᵢ
    { refine ∧ₑ₁ (part_ord_Int_iff A r) (∧ₑ₁ (tot_ordD A (Int r (Sigma A (λ _, A))) h)) }
    { refine ∧ₑ₁ (linear_Int_iff A r) (∧ₑ₂ (tot_ordD A (Int r (Sigma A (λ _, A))) h)) } }
  { assume h;
    rewrite tot_ord_def;
    apply ∧ᵢ
    { refine ∧ₑ₂ (part_ord_Int_iff A r) (∧ₑ₁ (tot_ordD A r h)) }
    { refine ∧ₑ₂ (linear_Int_iff A r) (∧ₑ₂ (tot_ordD A r h)) } }
end;

// wf_on_Int_iff: wf(A, Int r (Sigma A (λ _, A))) ↔ wf(A, r)
opaque symbol wf_on_Int_iff (A r : τ ι) :
  π (wf A (Int r (Sigma A (λ _, A))) ⇔ wf A r) ≔
begin
  assume A r;
  apply ∧ᵢ
  { assume hwf;
    rewrite wf_def;
    assume Z hZA hZne;
    have hmin : π (Bex Z (λ x0, Ball Z (λ y, Pair y x0 ∉ Int r (Sigma A (λ _, A)))))
      { refine wfD A (Int r (Sigma A (λ _, A))) hwf Z hZA hZne };
    refine ∃ₑ hmin _;
    assume x0 hx0;
    refine ∃ᵢ x0 _;
    apply ∧ᵢ (∧ₑ₁ hx0) _;
    assume y hyZ hyr;
    have hx0Z : π (x0 ∈ Z) { refine ∧ₑ₁ hx0 };
    have hx0min : π (Ball Z (λ y2, Pair y2 x0 ∉ Int r (Sigma A (λ _, A)))) { refine ∧ₑ₂ hx0 };
    have hyA : π (y ∈ A) { refine hZA y hyZ };
    have hx0A : π (x0 ∈ A) { refine hZA x0 hx0Z };
    have hyr2 : π (Pair y x0 ∈ Int r (Sigma A (λ _, A))) {
      refine IntI (Pair y x0) r (Sigma A (λ _, A)) hyr (SigmaI y x0 A (λ _, A) hyA hx0A)
    };
    refine hx0min y hyZ hyr2 }
  { assume hwf;
    rewrite wf_def;
    assume Z hZA hZne;
    have hmin : π (Bex Z (λ x0, Ball Z (λ y, Pair y x0 ∉ r)))
      { refine wfD A r hwf Z hZA hZne };
    refine ∃ₑ hmin _;
    assume x0 hx0;
    refine ∃ᵢ x0 _;
    apply ∧ᵢ (∧ₑ₁ hx0) _;
    assume y hyZ hyr;
    have hyrr : π (Pair y x0 ∈ r) { refine IntD1 (Pair y x0) r (Sigma A (λ _, A)) hyr };
    refine (∧ₑ₂ hx0) y hyZ hyrr }
end;

// well_ord_Int_iff: well_ord(A, Int r (Sigma A (λ _, A))) ↔ well_ord(A, r)
opaque symbol well_ord_Int_iff (A r : τ ι) :
  π (well_ord A (Int r (Sigma A (λ _, A))) ⇔ well_ord A r) ≔
begin
  assume A r;
  apply ∧ᵢ
  { assume h;
    rewrite well_ord_def;
    apply ∧ᵢ
    { refine ∧ₑ₁ (tot_ord_Int_iff A r) (∧ₑ₁ (well_ordD A (Int r (Sigma A (λ _, A))) h)) }
    { refine ∧ₑ₁ (wf_on_Int_iff A r) (∧ₑ₂ (well_ordD A (Int r (Sigma A (λ _, A))) h)) } }
  { assume h;
    rewrite well_ord_def;
    apply ∧ᵢ
    { refine ∧ₑ₂ (tot_ord_Int_iff A r) (∧ₑ₁ (well_ordD A r h)) }
    { refine ∧ₑ₂ (wf_on_Int_iff A r) (∧ₑ₂ (well_ordD A r h)) } }
end;

// ===========================================================================
// Section: ord_iso_image_pred and restrict
// ===========================================================================

// ord_iso_restrict_pred: f ∈ ord_iso(A,r,B,s) → a ∈ A →
//   restrict(f, pred(A,a,r)) ∈ ord_iso(pred(A,a,r), r, pred(B, f`a, s), s)
opaque symbol ord_iso_restrict_pred (f A r B s a : τ ι) :
  π (f ∈ ord_iso A r B s) → π (a ∈ A) →
  π (restrict f (pred A a r) ∈ ord_iso (pred A a r) r (pred B (fapply f a) s) s) ≔
begin
  assume f A r B s a hf haA;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hfun2 : π (f ∈ Pi A (λ _, B)) { refine bij_is_fun f A B hbij };
  have hinj : π (f ∈ inj A B) { refine bij_is_inj f A B hbij };
  have hfunc : π (function f) { refine Pi_function f A (λ _, B) hfun2 };
  have hdomf : π (domain f = A) { refine domain_of_fun f A (λ _, B) hfun2 };
  have hfrPi : π (restrict f (pred A a r) ∈ Pi (pred A a r) (λ _, pred B (fapply f a) s)) {
    rewrite Pi_def;
    refine CollectI (restrict f (pred A a r)) (Pow (Sigma (pred A a r) (λ _, pred B (fapply f a) s)))
      (λ h, pred A a r ⊆ domain h ∧ function h) _ _
    { refine PowI (restrict f (pred A a r)) (Sigma (pred A a r) (λ _, pred B (fapply f a) s)) _;
      assume p hp;
      have hpr : π (p ∈ f) { refine restrictD1 p f (pred A a r) hp };
      have hpbex : π (p ∈ f ∧ Bex (pred A a r) (λ x, `∃ (y : τ ι), p = Pair x y)) { refine restrictE p f (pred A a r) hp };
      refine ∃ₑ (∧ₑ₂ hpbex) _; assume x hx;
      have hxP : π (x ∈ pred A a r) { refine ∧ₑ₁ hx };
      refine ∃ₑ (∧ₑ₂ hx) _; assume y hpeq;
      have hpxy : π (Pair x y ∈ f) { refine ind_eq (eq_sym hpeq) (λ z, z ∈ f) hpr };
      have hfxy : π (fapply f x = y) { refine function_apply_equality x y f hpxy hfunc };
      have hxA : π (x ∈ A) { refine pred_subset A a r x hxP };
      have hxa : π (Pair x a ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff x A a r) hxP) };
      have hfxB : π (fapply f x ∈ B) { refine bij_apply f A B x hbij hxA };
      have hsfx : π (Pair (fapply f x) (fapply f a) ∈ s) { refine ord_iso_apply f A r B s x a hf hxa hxA haA };
      have hfxQ : π (fapply f x ∈ pred B (fapply f a) s) { refine predI (fapply f x) B (fapply f a) s hsfx hfxB };
      have hyQ : π (y ∈ pred B (fapply f a) s) { refine ind_eq (eq_sym hfxy) (λ z, z ∈ pred B (fapply f a) s) hfxQ };
      rewrite hpeq;
      refine SigmaI x y (pred A a r) (λ _, pred B (fapply f a) s) hxP hyQ }
    { apply ∧ᵢ
      { assume x hxP;
        have hxA : π (x ∈ A) { refine pred_subset A a r x hxP };
        have hxdom : π (x ∈ domain f) { refine ind_eq hdomf (λ z, x ∈ z) hxA };
        have hpf : π (Pair x (fapply f x) ∈ f) { refine apply_Pair f x hfunc hxdom };
        have hpfr : π (Pair x (fapply f x) ∈ restrict f (pred A a r)) { refine restrictI x (fapply f x) f (pred A a r) hpf hxP };
        refine domainI x (fapply f x) (restrict f (pred A a r)) hpfr }
      { refine function_restrictI f (pred A a r) hfunc } } };
  refine ord_isoI (restrict f (pred A a r)) (pred A a r) r (pred B (fapply f a) s) s _ _
  { rewrite bij_def;
    refine IntI (restrict f (pred A a r)) (inj (pred A a r) (pred B (fapply f a) s)) (surj (pred A a r) (pred B (fapply f a) s)) _ _
    { rewrite inj_def;
      refine CollectI (restrict f (pred A a r)) (Pi (pred A a r) (λ _, pred B (fapply f a) s))
        (λ h, Ball (pred A a r) (λ w, Ball (pred A a r) (λ x, fapply h w = fapply h x ⇒ w = x))) hfrPi _;
      assume w hw x hx heq;
      have hwA : π (w ∈ A) { refine pred_subset A a r w hw };
      have hxA : π (x ∈ A) { refine pred_subset A a r x hx };
      have hwdom : π (w ∈ domain f) { refine ind_eq hdomf (λ z, w ∈ z) hwA };
      have hxdom : π (x ∈ domain f) { refine ind_eq hdomf (λ z, x ∈ z) hxA };
      have hfrw : π (fapply (restrict f (pred A a r)) w = fapply f w) { refine restrict_apply f (pred A a r) w hfunc hw hwdom };
      have hfrx : π (fapply (restrict f (pred A a r)) x = fapply f x) { refine restrict_apply f (pred A a r) x hfunc hx hxdom };
      have hfeq : π (fapply f w = fapply f x) { rewrite left hfrw; rewrite left hfrx; apply heq };
      refine inj_apply_equality f A B w x hinj hfeq hwA hxA }
    { rewrite surj_def;
      refine CollectI (restrict f (pred A a r)) (Pi (pred A a r) (λ _, pred B (fapply f a) s))
        (λ h, Ball (pred B (fapply f a) s) (λ y, Bex (pred A a r) (λ x, fapply h x = y))) hfrPi _;
      assume q hq;
      have hqB : π (q ∈ B) { refine pred_subset B (fapply f a) s q hq };
      have hqfa : π (Pair q (fapply f a) ∈ s)
        { refine ∧ₑ₁ (∧ₑ₁ (pred_iff q B (fapply f a) s) hq) };
      have hcq : π (fapply (converse f) q ∈ A) { refine converse_apply_type f A B q hbij hqB };
      have hfcq : π (fapply f (fapply (converse f) q) = q) { refine right_inverse_bij f A B q hbij hqB };
      have hr : π (Pair (fapply (converse f) q) (fapply (converse f) (fapply f a)) ∈ r) { refine ord_iso_converse f A r B s q (fapply f a) hf hqfa hqB (bij_apply f A B a hbij haA) };
      have hcffa : π (fapply (converse f) (fapply f a) = a) { refine left_inverse_bij f A B a hbij haA };
      have hra : π (Pair (fapply (converse f) q) a ∈ r) { refine ind_eq (eq_sym hcffa) (λ z, Pair (fapply (converse f) q) z ∈ r) hr };
      have hcqP : π (fapply (converse f) q ∈ pred A a r) { refine predI (fapply (converse f) q) A a r hra hcq };
      have hcqdom : π (fapply (converse f) q ∈ domain f) { refine ind_eq hdomf (λ z, fapply (converse f) q ∈ z) hcq };
      have hfrcq : π (fapply (restrict f (pred A a r)) (fapply (converse f) q) = fapply f (fapply (converse f) q)) { refine restrict_apply f (pred A a r) (fapply (converse f) q) hfunc hcqP hcqdom };
      refine ∃ᵢ (fapply (converse f) q) _;
      apply ∧ᵢ hcqP _;
      rewrite hfrcq; apply hfcq } }
  { assume x hx y hy;
    have hxA : π (x ∈ A) { refine pred_subset A a r x hx };
    have hyA : π (y ∈ A) { refine pred_subset A a r y hy };
    have hxdom : π (x ∈ domain f) { refine ind_eq hdomf (λ z, x ∈ z) hxA };
    have hydom : π (y ∈ domain f) { refine ind_eq hdomf (λ z, y ∈ z) hyA };
    have hfrx : π (fapply (restrict f (pred A a r)) x = fapply f x) { refine restrict_apply f (pred A a r) x hfunc hx hxdom };
    have hfry : π (fapply (restrict f (pred A a r)) y = fapply f y) { refine restrict_apply f (pred A a r) y hfunc hy hydom };
    have hcond : π (Ball A (λ u, Ball A (λ v, (Pair u v ∈ r) ⇔ (Pair (fapply f u) (fapply f v) ∈ s))))
      { refine ord_iso_memD f A r B s hf };
    have hiff : π ((Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ s)) { refine hcond x hxA y hyA };
    rewrite hfrx; rewrite hfry; apply hiff }
end;

// ===========================================================================
// Section: Two monotone maps make an order-isomorphism (Order.thy)
// ===========================================================================

// Local helpers (equalities.thy facts about converse, needed below)

// domain_converse: domain(converse(r)) = range(r)
opaque symbol domain_converse (r : τ ι) :
  π (domain (converse r) = range r) ≔
begin
  assume r;
  refine equality_iffI (domain (converse r)) (range r) _;
  assume a;
  apply ∧ᵢ
  { assume ha;
    refine ∃ₑ (domainE a (converse r) ha) _;
    assume b hb;
    refine rangeI b a r (converseD a b r hb) }
  { assume ha;
    refine ∃ₑ (rangeE a r ha) _;
    assume b hb;
    refine domainI a b (converse r) (converseI b a r hb) }
end;

// range_converse: range(converse(r)) = domain(r)
opaque symbol range_converse (r : τ ι) :
  π (range (converse r) = domain r) ≔
begin
  assume r;
  refine equality_iffI (range (converse r)) (domain r) _;
  assume a;
  apply ∧ᵢ
  { assume ha;
    refine ∃ₑ (rangeE a (converse r) ha) _;
    assume b hb;
    refine domainI a b r (converseD b a r hb) }
  { assume ha;
    refine ∃ₑ (domainE a r ha) _;
    assume b hb;
    refine rangeI b a (converse r) (converseI a b r hb) }
end;

// mono_ord_isoI: two mutually-inverse monotone maps form an order-isomorphism
// Isabelle: ⟦f ∈ mono_map(A,r,B,s); g ∈ mono_map(B,s,A,r);
//            f O g = id(B); g O f = id(A)⟧ ⟹ f ∈ ord_iso(A,r,B,s)
opaque symbol mono_ord_isoI (f g A r B s : τ ι) :
  π (f ∈ mono_map A r B s) → π (g ∈ mono_map B s A r) →
  π (rcomp f g = id_fun B) → π (rcomp g f = id_fun A) →
  π (f ∈ ord_iso A r B s) ≔
begin
  assume f g A r B s hf hg hfg hgf;
  have hffun : π (f ∈ Pi A (λ _, B)) { refine mono_map_is_fun f A r B s hf };
  have hgfun : π (g ∈ Pi B (λ _, A)) { refine mono_map_is_fun g B s A r hg };
  // pointwise inverse laws from the composition equations
  have hgfx : π (Ball A (λ x, fapply g (fapply f x) = x))
    { assume x hx;
      have h1 : π (fapply (rcomp g f) x = fapply g (fapply f x))
        { refine comp_fun_apply g f A B A x hffun hgfun hx };
      have h2 : π (fapply (id_fun A) x = x) { refine id_conv A x hx };
      rewrite left h1;
      rewrite hgf;
      apply h2 };
  have hfgy : π (Ball B (λ y, fapply f (fapply g y) = y))
    { assume y hy;
      have h1 : π (fapply (rcomp f g) y = fapply f (fapply g y))
        { refine comp_fun_apply f g B A B y hgfun hffun hy };
      have h2 : π (fapply (id_fun B) y = y) { refine id_conv B y hy };
      rewrite left h1;
      rewrite hfg;
      apply h2 };
  // bijectivity
  have hbij : π (f ∈ bij A B)
    { rewrite bij_def;
      refine IntI f (inj A B) (surj A B) _ _
      { refine f_imp_injective f A B (λ y, fapply g y) hffun _;
        assume x hx; refine hgfx x hx }
      { refine f_imp_surjective f A B (λ y, fapply g y) hffun _ _
        { assume y hy; refine apply_type g B A y hgfun hy }
        { assume y hy; refine hfgy y hy } } };
  // the monotonicity content of both maps
  have hf' : π (f ∈ Collect (Pi A (λ _, B))
      (λ k, Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply k x) (fapply k y) ∈ s))))
    { refine ind_eq (eq_sym (mono_map_def A r B s)) (λ w, f ∈ w) hf };
  have hfmono : π (Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply f x) (fapply f y) ∈ s)))
    { refine CollectD2 f (Pi A (λ _, B)) (λ k, Ball A (λ x, Ball A (λ y, Pair x y ∈ r ⇒ Pair (fapply k x) (fapply k y) ∈ s))) hf' };
  have hg' : π (g ∈ Collect (Pi B (λ _, A))
      (λ k, Ball B (λ x, Ball B (λ y, Pair x y ∈ s ⇒ Pair (fapply k x) (fapply k y) ∈ r))))
    { refine ind_eq (eq_sym (mono_map_def B s A r)) (λ w, g ∈ w) hg };
  have hgmono : π (Ball B (λ x, Ball B (λ y, Pair x y ∈ s ⇒ Pair (fapply g x) (fapply g y) ∈ r)))
    { refine CollectD2 g (Pi B (λ _, A)) (λ k, Ball B (λ x, Ball B (λ y, Pair x y ∈ s ⇒ Pair (fapply k x) (fapply k y) ∈ r))) hg' };
  refine ord_isoI f A r B s hbij _;
  assume x hx y hy;
  apply ∧ᵢ
  { assume hxy; refine hfmono x hx y hy hxy }
  { assume hs;
    have hfxB : π (fapply f x ∈ B) { refine apply_type f A B x hffun hx };
    have hfyB : π (fapply f y ∈ B) { refine apply_type f A B y hffun hy };
    have hr : π (Pair (fapply g (fapply f x)) (fapply g (fapply f y)) ∈ r)
      { refine hgmono (fapply f x) hfxB (fapply f y) hfyB hs };
    have hgx : π (fapply g (fapply f x) = x) { refine hgfx x hx };
    have hgy : π (fapply g (fapply f y) = y) { refine hgfx y hy };
    have hr1 : π (Pair x (fapply g (fapply f y)) ∈ r)
      { refine ind_eq (eq_sym hgx) (λ w, Pair w (fapply g (fapply f y)) ∈ r) hr };
    refine ind_eq (eq_sym hgy) (λ w, Pair x w ∈ r) hr1 }
end;

// well_ord_mono_ord_isoI: over well-orders, a monotone map with monotone
// converse is an order-isomorphism
opaque symbol well_ord_mono_ord_isoI (f A r B s : τ ι) :
  π (well_ord A r) → π (well_ord B s) →
  π (f ∈ mono_map A r B s) → π (converse f ∈ mono_map B s A r) →
  π (f ∈ ord_iso A r B s) ≔
begin
  assume f A r B s hwoA hwoB hf hcf;
  have hlinA : π (linear A r) { refine well_ord_is_linear A r hwoA };
  have hlinB : π (linear B s) { refine well_ord_is_linear B s hwoB };
  have hwfA : π (wf A r) { refine well_ord_is_wf A r hwoA };
  have hwfB : π (wf B s) { refine well_ord_is_wf B s hwoB };
  have hinj : π (f ∈ inj A B) { refine mono_map_is_inj A r B s f hlinA hwfB hf };
  have hcinj : π (converse f ∈ inj B A)
    { refine mono_map_is_inj B s A r (converse f) hlinB hwfA hcf };
  have hgf : π (rcomp (converse f) f = id_fun A) { refine left_comp_inverse f A B hinj };
  have hfun : π (f ∈ Pi A (λ _, B)) { refine mono_map_is_fun f A r B s hf };
  have hrel : π (f ⊆ Sigma A (λ _, B))
    { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₁ (Pi_iff f A (λ _, B)) hfun)) };
  have hcc : π (converse (converse f) = f) { refine converse_converse f A (λ _, B) hrel };
  have hccf : π (rcomp (converse (converse f)) (converse f) = id_fun B)
    { refine left_comp_inverse (converse f) B A hcinj };
  have hfg : π (rcomp f (converse f) = id_fun B)
    { refine ind_eq (eq_sym hcc) (λ w, rcomp w (converse f) = id_fun B) hccf };
  refine mono_ord_isoI f (converse f) A r B s hf hcf hfg hgf
end;

// ===========================================================================
// Section: Order-isomorphisms and initial segments (images)
// ===========================================================================

// ord_iso_image_pred: f``pred(A,a,r) = pred(B, f`a, s)   (does not need well_ord)
opaque symbol ord_iso_image_pred (f A r B s a : τ ι) :
  π (f ∈ ord_iso A r B s) → π (a ∈ A) →
  π (Image f (pred A a r) = pred B (fapply f a) s) ≔
begin
  assume f A r B s a hf haA;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hfun : π (f ∈ Pi A (λ _, B)) { refine bij_is_fun f A B hbij };
  have hdomf : π (domain f = A) { refine domain_of_fun f A (λ _, B) hfun };
  refine equality_iffI (Image f (pred A a r)) (pred B (fapply f a) s) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    have hbex : π (Bex (Int (pred A a r) (domain f)) (λ x, z = fapply f x))
      { refine ∧ₑ₁ (Image_iff z f (pred A a r)) hz };
    refine ∃ₑ hbex _;
    assume x hx;
    have hxP : π (x ∈ pred A a r) { refine IntD1 x (pred A a r) (domain f) (∧ₑ₁ hx) };
    have hzeq : π (z = fapply f x) { refine ∧ₑ₂ hx };
    have hxA : π (x ∈ A) { refine pred_subset A a r x hxP };
    have hxa : π (Pair x a ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff x A a r) hxP) };
    have hfxB : π (fapply f x ∈ B) { refine bij_apply f A B x hbij hxA };
    have hs : π (Pair (fapply f x) (fapply f a) ∈ s)
      { refine ord_iso_apply f A r B s x a hf hxa hxA haA };
    have hres : π (fapply f x ∈ pred B (fapply f a) s)
      { refine predI (fapply f x) B (fapply f a) s hs hfxB };
    rewrite hzeq;
    refine hres }
  { assume hz;
    have hzB : π (z ∈ B) { refine pred_subset B (fapply f a) s z hz };
    have hzfa : π (Pair z (fapply f a) ∈ s)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z B (fapply f a) s) hz) };
    have hcz : π (fapply (converse f) z ∈ A) { refine converse_apply_type f A B z hbij hzB };
    have hfcz : π (fapply f (fapply (converse f) z) = z) { refine right_inverse_bij f A B z hbij hzB };
    have hr : π (Pair (fapply (converse f) z) (fapply (converse f) (fapply f a)) ∈ r)
      { refine ord_iso_converse f A r B s z (fapply f a) hf hzfa hzB (bij_apply f A B a hbij haA) };
    have hcffa : π (fapply (converse f) (fapply f a) = a) { refine left_inverse_bij f A B a hbij haA };
    have hra : π (Pair (fapply (converse f) z) a ∈ r)
      { refine ind_eq (eq_sym hcffa) (λ w, Pair (fapply (converse f) z) w ∈ r) hr };
    have hczP : π (fapply (converse f) z ∈ pred A a r)
      { refine predI (fapply (converse f) z) A a r hra hcz };
    have hczdom : π (fapply (converse f) z ∈ domain f)
      { refine ind_eq hdomf (λ w, fapply (converse f) z ∈ w) hcz };
    have hczInt : π (fapply (converse f) z ∈ Int (pred A a r) (domain f))
      { refine IntI (fapply (converse f) z) (pred A a r) (domain f) hczP hczdom };
    refine ∧ₑ₂ (Image_iff z f (pred A a r)) _;
    refine ∃ᵢ (fapply (converse f) z) (∧ᵢ hczInt (eq_sym hfcz)) }
end;

// ord_iso_restrict_image: restrict(f,C) ∈ ord_iso(C, r, f``C, s) for C ⊆ A
opaque symbol ord_iso_restrict_image (f A r B s C : τ ι) :
  π (f ∈ ord_iso A r B s) → π (C ⊆ A) →
  π (restrict f C ∈ ord_iso C r (Image f C) s) ≔
begin
  assume f A r B s C hf hCA;
  have hbij : π (f ∈ bij A B) { refine ord_iso_is_bij f A r B s hf };
  have hfun2 : π (f ∈ Pi A (λ _, B)) { refine bij_is_fun f A B hbij };
  have hinj : π (f ∈ inj A B) { refine bij_is_inj f A B hbij };
  have hfunc : π (function f) { refine Pi_function f A (λ _, B) hfun2 };
  have hdomf : π (domain f = A) { refine domain_of_fun f A (λ _, B) hfun2 };
  have hfrPi : π (restrict f C ∈ Pi C (λ _, Image f C)) {
    rewrite Pi_def;
    refine CollectI (restrict f C) (Pow (Sigma C (λ _, Image f C)))
      (λ h, C ⊆ domain h ∧ function h) _ _
    { refine PowI (restrict f C) (Sigma C (λ _, Image f C)) _;
      assume p hp;
      have hpr : π (p ∈ f) { refine restrictD1 p f C hp };
      have hpbex : π (p ∈ f ∧ Bex C (λ x, `∃ (y : τ ι), p = Pair x y)) { refine restrictE p f C hp };
      refine ∃ₑ (∧ₑ₂ hpbex) _; assume x hx;
      have hxC : π (x ∈ C) { refine ∧ₑ₁ hx };
      refine ∃ₑ (∧ₑ₂ hx) _; assume y hpeq;
      have hpxy : π (Pair x y ∈ f) { refine ind_eq (eq_sym hpeq) (λ z, z ∈ f) hpr };
      have hfxy : π (fapply f x = y) { refine function_apply_equality x y f hpxy hfunc };
      have hxA : π (x ∈ A) { refine hCA x hxC };
      have hxdom : π (x ∈ domain f) { refine ind_eq hdomf (λ w, x ∈ w) hxA };
      have hfxI : π (fapply f x ∈ Image f C)
        { refine ∧ₑ₂ (Image_iff (fapply f x) f C)
            (∃ᵢ x (∧ᵢ (IntI x C (domain f) hxC hxdom) (eq_refl (fapply f x)))) };
      have hyI : π (y ∈ Image f C) { refine ind_eq (eq_sym hfxy) (λ z, z ∈ Image f C) hfxI };
      rewrite hpeq;
      refine SigmaI x y C (λ _, Image f C) hxC hyI }
    { apply ∧ᵢ
      { assume x hxC;
        have hxA : π (x ∈ A) { refine hCA x hxC };
        have hxdom : π (x ∈ domain f) { refine ind_eq hdomf (λ z, x ∈ z) hxA };
        have hpf : π (Pair x (fapply f x) ∈ f) { refine apply_Pair f x hfunc hxdom };
        have hpfr : π (Pair x (fapply f x) ∈ restrict f C) { refine restrictI x (fapply f x) f C hpf hxC };
        refine domainI x (fapply f x) (restrict f C) hpfr }
      { refine function_restrictI f C hfunc } } };
  refine ord_isoI (restrict f C) C r (Image f C) s _ _
  { rewrite bij_def;
    refine IntI (restrict f C) (inj C (Image f C)) (surj C (Image f C)) _ _
    { rewrite inj_def;
      refine CollectI (restrict f C) (Pi C (λ _, Image f C))
        (λ h, Ball C (λ w, Ball C (λ x, fapply h w = fapply h x ⇒ w = x))) hfrPi _;
      assume w hw x hx heq;
      have hwA : π (w ∈ A) { refine hCA w hw };
      have hxA : π (x ∈ A) { refine hCA x hx };
      have hwdom : π (w ∈ domain f) { refine ind_eq hdomf (λ z, w ∈ z) hwA };
      have hxdom : π (x ∈ domain f) { refine ind_eq hdomf (λ z, x ∈ z) hxA };
      have hfrw : π (fapply (restrict f C) w = fapply f w) { refine restrict_apply f C w hfunc hw hwdom };
      have hfrx : π (fapply (restrict f C) x = fapply f x) { refine restrict_apply f C x hfunc hx hxdom };
      have hfeq : π (fapply f w = fapply f x) { rewrite left hfrw; rewrite left hfrx; apply heq };
      refine inj_apply_equality f A B w x hinj hfeq hwA hxA }
    { rewrite surj_def;
      refine CollectI (restrict f C) (Pi C (λ _, Image f C))
        (λ h, Ball (Image f C) (λ y, Bex C (λ x, fapply h x = y))) hfrPi _;
      assume q hq;
      have hbex : π (Bex (Int C (domain f)) (λ x, q = fapply f x)) { refine ∧ₑ₁ (Image_iff q f C) hq };
      refine ∃ₑ hbex _;
      assume x hx;
      have hxC : π (x ∈ C) { refine IntD1 x C (domain f) (∧ₑ₁ hx) };
      have hxdom : π (x ∈ domain f) { refine IntD2 x C (domain f) (∧ₑ₁ hx) };
      have hqeq : π (q = fapply f x) { refine ∧ₑ₂ hx };
      have hfrx : π (fapply (restrict f C) x = fapply f x) { refine restrict_apply f C x hfunc hxC hxdom };
      refine ∃ᵢ x (∧ᵢ hxC _);
      rewrite hfrx;
      refine eq_sym hqeq } }
  { assume x hx y hy;
    have hxA : π (x ∈ A) { refine hCA x hx };
    have hyA : π (y ∈ A) { refine hCA y hy };
    have hxdom : π (x ∈ domain f) { refine ind_eq hdomf (λ z, x ∈ z) hxA };
    have hydom : π (y ∈ domain f) { refine ind_eq hdomf (λ z, y ∈ z) hyA };
    have hfrx : π (fapply (restrict f C) x = fapply f x) { refine restrict_apply f C x hfunc hx hxdom };
    have hfry : π (fapply (restrict f C) y = fapply f y) { refine restrict_apply f C y hfunc hy hydom };
    have hcond : π (Ball A (λ u, Ball A (λ v, (Pair u v ∈ r) ⇔ (Pair (fapply f u) (fapply f v) ∈ s))))
      { refine ord_iso_memD f A r B s hf };
    have hiff : π ((Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ s)) { refine hcond x hxA y hyA };
    rewrite hfrx; rewrite hfry; apply hiff }
end;

// well_ord_iso_preserving: isomorphisms of initial segments preserve order
opaque symbol well_ord_iso_preserving (A r B s f g a b c d : τ ι) :
  π (well_ord A r) → π (well_ord B s) → π (Pair a c ∈ r) →
  π (f ∈ ord_iso (pred A a r) r (pred B b s) s) →
  π (g ∈ ord_iso (pred A c r) r (pred B d s) s) →
  π (a ∈ A) → π (c ∈ A) → π (b ∈ B) → π (d ∈ B) →
  π (Pair b d ∈ s) ≔
begin
  assume A r B s f g a b c d hwoA hwoB hac hf hg haA hcA hbB hdB;
  have haP : π (a ∈ pred A c r) { refine predI a A c r hac haA };
  have hgbij : π (g ∈ bij (pred A c r) (pred B d s))
    { refine ord_iso_is_bij g (pred A c r) r (pred B d s) s hg };
  have hgaP : π (fapply g a ∈ pred B d s)
    { refine bij_apply g (pred A c r) (pred B d s) a hgbij haP };
  have hgad : π (Pair (fapply g a) d ∈ s)
    { refine ∧ₑ₁ (∧ₑ₁ (pred_iff (fapply g a) B d s) hgaP) };
  have hgaB : π (fapply g a ∈ B)
    { refine ∧ₑ₂ (∧ₑ₁ (pred_iff (fapply g a) B d s) hgaP) };
  have htrA : π (trans_on A r) { refine well_ord_is_trans_on A r hwoA };
  have htrB : π (trans_on B s) { refine well_ord_is_trans_on B s hwoB };
  have hres : π (restrict g (pred (pred A c r) a r)
      ∈ ord_iso (pred (pred A c r) a r) r (pred (pred B d s) (fapply g a) s) s)
    { refine ord_iso_restrict_pred g (pred A c r) r (pred B d s) s a hg haP };
  have hpp1 : π (pred (pred A c r) a r = pred A a r)
    { refine trans_pred_pred_eq A r c a htrA hac hcA haA };
  have hpp2 : π (pred (pred B d s) (fapply g a) s = pred B (fapply g a) s)
    { refine trans_pred_pred_eq B s d (fapply g a) htrB hgad hdB hgaB };
  have hres2 : π (restrict g (pred A a r)
      ∈ ord_iso (pred A a r) r (pred (pred B d s) (fapply g a) s) s)
    { refine ind_eq (eq_sym hpp1)
        (λ w, restrict g w ∈ ord_iso w r (pred (pred B d s) (fapply g a) s) s) hres };
  have hres3 : π (restrict g (pred A a r)
      ∈ ord_iso (pred A a r) r (pred B (fapply g a) s) s)
    { refine ind_eq (eq_sym hpp2)
        (λ w, restrict g (pred A a r) ∈ ord_iso (pred A a r) r w s) hres2 };
  have hcf : π (converse f ∈ ord_iso (pred B b s) s (pred A a r) r)
    { refine ord_iso_sym f (pred A a r) r (pred B b s) s hf };
  have hcomp : π (rcomp (restrict g (pred A a r)) (converse f)
      ∈ ord_iso (pred B b s) s (pred B (fapply g a) s) s)
    { refine ord_iso_trans (converse f) (restrict g (pred A a r))
        (pred B b s) s (pred A a r) r (pred B (fapply g a) s) s hcf hres3 };
  have hbga : π (b = fapply g a)
    { refine well_ord_iso_pred_eq B s (rcomp (restrict g (pred A a r)) (converse f))
        b (fapply g a) hwoB hcomp hbB hgaB };
  rewrite hbga;
  refine hgad
end;

// ===========================================================================
// Section: Kunen's Theorem 6.3 — the ord_iso_map construction
// ===========================================================================

// ord_iso_mapI (port helper): the canonical way INTO ord_iso_map.
opaque symbol ord_iso_mapI (x y f A r B s : τ ι) :
  π (x ∈ A) → π (y ∈ B) →
  π (f ∈ ord_iso (pred A x r) r (pred B y s) s) →
  π (Pair x y ∈ ord_iso_map A r B s) ≔
begin
  assume x y f A r B s hx hy hf;
  have h3 : π (Pair x y ∈ cons (Pair x y) empty) { refine consI1 (Pair x y) empty };
  have h2 : π (cons (Pair x y) empty
      ∈ RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f2, cons (Pair x y) empty))
    { refine RepFunI f (ord_iso (pred A x r) r (pred B y s) s) (λ f2, cons (Pair x y) empty) hf };
  have h1 : π (Pair x y ∈ Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f2, cons (Pair x y) empty)))
    { refine UnionI (Pair x y) (cons (Pair x y) empty) _ h3 h2 };
  have h0 : π (Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f2, cons (Pair x y) empty))
      ∈ RepFun B (λ y2, Union (RepFun (ord_iso (pred A x r) r (pred B y2 s) s) (λ f2, cons (Pair x y2) empty))))
    { refine RepFunI y B (λ y2, Union (RepFun (ord_iso (pred A x r) r (pred B y2 s) s) (λ f2, cons (Pair x y2) empty))) hy };
  have hL1 : π (Pair x y ∈ Union (RepFun B (λ y2, Union (RepFun (ord_iso (pred A x r) r (pred B y2 s) s) (λ f2, cons (Pair x y2) empty)))))
    { refine UnionI (Pair x y) (Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f2, cons (Pair x y) empty))) _ h1 h0 };
  have h00 : π (Union (RepFun B (λ y2, Union (RepFun (ord_iso (pred A x r) r (pred B y2 s) s) (λ f2, cons (Pair x y2) empty))))
      ∈ RepFun A (λ x2, Union (RepFun B (λ y2, Union (RepFun (ord_iso (pred A x2 r) r (pred B y2 s) s) (λ f2, cons (Pair x2 y2) empty))))))
    { refine RepFunI x A (λ x2, Union (RepFun B (λ y2, Union (RepFun (ord_iso (pred A x2 r) r (pred B y2 s) s) (λ f2, cons (Pair x2 y2) empty))))) hx };
  have hL0 : π (Pair x y ∈ Union (RepFun A (λ x2, Union (RepFun B (λ y2, Union (RepFun (ord_iso (pred A x2 r) r (pred B y2 s) s) (λ f2, cons (Pair x2 y2) empty)))))))
    { refine UnionI (Pair x y) (Union (RepFun B (λ y2, Union (RepFun (ord_iso (pred A x r) r (pred B y2 s) s) (λ f2, cons (Pair x y2) empty))))) _ hL1 h00 };
  rewrite ord_iso_map_def;
  refine hL0
end;

// ord_iso_mapE (port helper): general-element elimination for ord_iso_map.
opaque symbol ord_iso_mapE (z A r B s : τ ι) :
  π (z ∈ ord_iso_map A r B s) →
  π (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair x y ∧ (x ∈ A ∧ (y ∈ B ∧
      `∃ (f : τ ι), f ∈ ord_iso (pred A x r) r (pred B y s) s))) ≔
begin
  assume z A r B s hz;
  have hz1 : π (z ∈ Union (RepFun A (λ x, Union (RepFun B (λ y,
      Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f, cons (Pair x y) empty)))))))
    { refine ind_eq (eq_sym (ord_iso_map_def A r B s)) (λ w, z ∈ w) hz };
  have hbex1 : π (Bex (RepFun A (λ x, Union (RepFun B (λ y,
      Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f, cons (Pair x y) empty)))))) (λ S, z ∈ S))
    { refine UnionE z _ hz1 };
  refine ∃ₑ hbex1 _;
  assume S1 hS1;
  have hbexx : π (Bex A (λ x, S1 = Union (RepFun B (λ y,
      Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f, cons (Pair x y) empty))))))
    { refine ∧ₑ₁ (RepFun_iff S1 A _) (∧ₑ₁ hS1) };
  refine ∃ₑ hbexx _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hzS1x : π (z ∈ Union (RepFun B (λ y, Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f, cons (Pair x y) empty)))))
    { refine ind_eq (eq_sym (∧ₑ₂ hx)) (λ w, z ∈ w) (∧ₑ₂ hS1) };
  have hbex2 : π (Bex (RepFun B (λ y, Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f, cons (Pair x y) empty)))) (λ S, z ∈ S))
    { refine UnionE z _ hzS1x };
  refine ∃ₑ hbex2 _;
  assume S2 hS2;
  have hbexy : π (Bex B (λ y, S2 = Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f, cons (Pair x y) empty))))
    { refine ∧ₑ₁ (RepFun_iff S2 B _) (∧ₑ₁ hS2) };
  refine ∃ₑ hbexy _;
  assume y hy;
  have hyB : π (y ∈ B) { refine ∧ₑ₁ hy };
  have hzS2y : π (z ∈ Union (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f, cons (Pair x y) empty)))
    { refine ind_eq (eq_sym (∧ₑ₂ hy)) (λ w, z ∈ w) (∧ₑ₂ hS2) };
  have hbex3 : π (Bex (RepFun (ord_iso (pred A x r) r (pred B y s) s) (λ f, cons (Pair x y) empty)) (λ S, z ∈ S))
    { refine UnionE z _ hzS2y };
  refine ∃ₑ hbex3 _;
  assume S3 hS3;
  have hbexf : π (Bex (ord_iso (pred A x r) r (pred B y s) s) (λ f, S3 = cons (Pair x y) empty))
    { refine ∧ₑ₁ (RepFun_iff S3 (ord_iso (pred A x r) r (pred B y s) s) _) (∧ₑ₁ hS3) };
  refine ∃ₑ hbexf _;
  assume f hfw;
  have hfiso : π (f ∈ ord_iso (pred A x r) r (pred B y s) s) { refine ∧ₑ₁ hfw };
  have hzcons : π (z ∈ cons (Pair x y) empty)
    { refine ind_eq (eq_sym (∧ₑ₂ hfw)) (λ w, z ∈ w) (∧ₑ₂ hS3) };
  have hzor : π (z = Pair x y ∨ z ∈ empty) { refine ∧ₑ₁ (cons_iff z (Pair x y) empty) hzcons };
  refine ∨ₑ hzor _ _
  { assume hzeq;
    refine ∃ᵢ x (∃ᵢ y (∧ᵢ hzeq (∧ᵢ hxA (∧ᵢ hyB (∃ᵢ f hfiso))))) }
  { assume habs; refine ⊥ₑ (emptyE z habs) }
end;

// ord_iso_map_subset: ord_iso_map(A,r,B,s) ⊆ A*B
opaque symbol ord_iso_map_subset (A r B s : τ ι) :
  π (ord_iso_map A r B s ⊆ Sigma A (λ _, B)) ≔
begin
  assume A r B s z hz;
  refine ∃ₑ (ord_iso_mapE z A r B s hz) _;
  assume x hx;
  refine ∃ₑ hx _;
  assume y hy;
  have hzeq : π (z = Pair x y) { refine ∧ₑ₁ hy };
  have hxA : π (x ∈ A) { refine ∧ₑ₁ (∧ₑ₂ hy) };
  have hyB : π (y ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hy)) };
  rewrite hzeq;
  refine SigmaI x y A (λ _, B) hxA hyB
end;

// domain_ord_iso_map: domain(ord_iso_map(A,r,B,s)) ⊆ A
opaque symbol domain_ord_iso_map (A r B s : τ ι) :
  π (domain (ord_iso_map A r B s) ⊆ A) ≔
begin
  assume A r B s a ha;
  refine ∃ₑ (domainE a (ord_iso_map A r B s) ha) _;
  assume b hb;
  have hS : π (Pair a b ∈ Sigma A (λ _, B)) { refine ord_iso_map_subset A r B s (Pair a b) hb };
  refine ind_eq (eq_sym (fst_conv a b)) (λ w, w ∈ A) (SigmaD1 (Pair a b) A (λ _, B) hS)
end;

// range_ord_iso_map: range(ord_iso_map(A,r,B,s)) ⊆ B
opaque symbol range_ord_iso_map (A r B s : τ ι) :
  π (range (ord_iso_map A r B s) ⊆ B) ≔
begin
  assume A r B s b hb;
  refine ∃ₑ (rangeE b (ord_iso_map A r B s) hb) _;
  assume a ha;
  have hS : π (Pair a b ∈ Sigma A (λ _, B)) { refine ord_iso_map_subset A r B s (Pair a b) ha };
  refine ind_eq (eq_sym (snd_conv a b)) (λ w, w ∈ B) (SigmaD2 (Pair a b) A (λ _, B) hS)
end;

// converse_ord_iso_map: converse(ord_iso_map(A,r,B,s)) = ord_iso_map(B,s,A,r)
opaque symbol converse_ord_iso_map (A r B s : τ ι) :
  π (converse (ord_iso_map A r B s) = ord_iso_map B s A r) ≔
begin
  assume A r B s;
  refine equality_iffI (converse (ord_iso_map A r B s)) (ord_iso_map B s A r) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∃ₑ (converseE z (ord_iso_map A r B s) hz) _;
    assume u hu;
    refine ∃ₑ hu _;
    assume v hv;
    have hzeq : π (z = Pair u v) { refine ∧ₑ₁ hv };
    have hvu : π (Pair v u ∈ ord_iso_map A r B s) { refine ∧ₑ₂ hv };
    refine ∃ₑ (ord_iso_mapE (Pair v u) A r B s hvu) _;
    assume x0 hx0;
    refine ∃ₑ hx0 _;
    assume y0 hy0;
    have hpeq : π (Pair v u = Pair x0 y0) { refine ∧ₑ₁ hy0 };
    have hvx0 : π (v = x0) { refine Pair_inject1 v u x0 y0 hpeq };
    have huy0 : π (u = y0) { refine Pair_inject2 v u x0 y0 hpeq };
    have hx0A : π (x0 ∈ A) { refine ∧ₑ₁ (∧ₑ₂ hy0) };
    have hy0B : π (y0 ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hy0)) };
    have hvA : π (v ∈ A) { refine ind_eq hvx0 (λ w, w ∈ A) hx0A };
    have huB : π (u ∈ B) { refine ind_eq huy0 (λ w, w ∈ B) hy0B };
    refine ∃ₑ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hy0))) _;
    assume f hf;
    have hf1 : π (f ∈ ord_iso (pred A v r) r (pred B y0 s) s)
      { refine ind_eq hvx0 (λ w, f ∈ ord_iso (pred A w r) r (pred B y0 s) s) hf };
    have hf2 : π (f ∈ ord_iso (pred A v r) r (pred B u s) s)
      { refine ind_eq huy0 (λ w, f ∈ ord_iso (pred A v r) r (pred B w s) s) hf1 };
    have hcf : π (converse f ∈ ord_iso (pred B u s) s (pred A v r) r)
      { refine ord_iso_sym f (pred A v r) r (pred B u s) s hf2 };
    have hres : π (Pair u v ∈ ord_iso_map B s A r)
      { refine ord_iso_mapI u v (converse f) B s A r huB hvA hcf };
    rewrite hzeq;
    refine hres }
  { assume hz;
    refine ∃ₑ (ord_iso_mapE z B s A r hz) _;
    assume u hu;
    refine ∃ₑ hu _;
    assume v hv;
    have hzeq : π (z = Pair u v) { refine ∧ₑ₁ hv };
    have huB : π (u ∈ B) { refine ∧ₑ₁ (∧ₑ₂ hv) };
    have hvA : π (v ∈ A) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hv)) };
    refine ∃ₑ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hv))) _;
    assume f hf;
    have hcf : π (converse f ∈ ord_iso (pred A v r) r (pred B u s) s)
      { refine ord_iso_sym f (pred B u s) s (pred A v r) r hf };
    have hvu : π (Pair v u ∈ ord_iso_map A r B s)
      { refine ord_iso_mapI v u (converse f) A r B s hvA huB hcf };
    have hcv : π (Pair u v ∈ converse (ord_iso_map A r B s))
      { refine converseI v u (ord_iso_map A r B s) hvu };
    rewrite hzeq;
    refine hcv }
end;

// function_ord_iso_map: well_ord(B,s) → function(ord_iso_map(A,r,B,s))
opaque symbol function_ord_iso_map (A r B s : τ ι) :
  π (well_ord B s) → π (function (ord_iso_map A r B s)) ≔
begin
  assume A r B s hwoB;
  rewrite function_def;
  assume x y yp hxy hxyp;
  refine ∃ₑ (ord_iso_mapE (Pair x y) A r B s hxy) _;
  assume x1 h1;
  refine ∃ₑ h1 _;
  assume y1 h2;
  have hpeq1 : π (Pair x y = Pair x1 y1) { refine ∧ₑ₁ h2 };
  have hx1 : π (x = x1) { refine Pair_inject1 x y x1 y1 hpeq1 };
  have hy1 : π (y = y1) { refine Pair_inject2 x y x1 y1 hpeq1 };
  have hy1B : π (y1 ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ h2)) };
  have hyB : π (y ∈ B) { refine ind_eq hy1 (λ w, w ∈ B) hy1B };
  refine ∃ₑ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h2))) _;
  assume f hfx1;
  have hfa : π (f ∈ ord_iso (pred A x r) r (pred B y1 s) s)
    { refine ind_eq hx1 (λ w, f ∈ ord_iso (pred A w r) r (pred B y1 s) s) hfx1 };
  have hfb : π (f ∈ ord_iso (pred A x r) r (pred B y s) s)
    { refine ind_eq hy1 (λ w, f ∈ ord_iso (pred A x r) r (pred B w s) s) hfa };
  refine ∃ₑ (ord_iso_mapE (Pair x yp) A r B s hxyp) _;
  assume x2 h3;
  refine ∃ₑ h3 _;
  assume y2 h4;
  have hpeq2 : π (Pair x yp = Pair x2 y2) { refine ∧ₑ₁ h4 };
  have hx2 : π (x = x2) { refine Pair_inject1 x yp x2 y2 hpeq2 };
  have hy2 : π (yp = y2) { refine Pair_inject2 x yp x2 y2 hpeq2 };
  have hy2B : π (y2 ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ h4)) };
  have hypB : π (yp ∈ B) { refine ind_eq hy2 (λ w, w ∈ B) hy2B };
  refine ∃ₑ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h4))) _;
  assume g hgx2;
  have hga : π (g ∈ ord_iso (pred A x r) r (pred B y2 s) s)
    { refine ind_eq hx2 (λ w, g ∈ ord_iso (pred A w r) r (pred B y2 s) s) hgx2 };
  have hgb : π (g ∈ ord_iso (pred A x r) r (pred B yp s) s)
    { refine ind_eq hy2 (λ w, g ∈ ord_iso (pred A x r) r (pred B w s) s) hga };
  have hcf : π (converse f ∈ ord_iso (pred B y s) s (pred A x r) r)
    { refine ord_iso_sym f (pred A x r) r (pred B y s) s hfb };
  have hcomp : π (rcomp g (converse f) ∈ ord_iso (pred B y s) s (pred B yp s) s)
    { refine ord_iso_trans (converse f) g (pred B y s) s (pred A x r) r (pred B yp s) s hcf hgb };
  refine well_ord_iso_pred_eq B s (rcomp g (converse f)) y yp hwoB hcomp hyB hypB
end;

// ord_iso_map_fun: well_ord(B,s) →
//   ord_iso_map(A,r,B,s) ∈ domain(ord_iso_map) → range(ord_iso_map)
opaque symbol ord_iso_map_fun (A r B s : τ ι) :
  π (well_ord B s) →
  π (ord_iso_map A r B s
     ∈ Pi (domain (ord_iso_map A r B s)) (λ _, range (ord_iso_map A r B s))) ≔
begin
  assume A r B s hwoB;
  refine ∧ₑ₂ (Pi_iff (ord_iso_map A r B s) (domain (ord_iso_map A r B s)) (λ _, range (ord_iso_map A r B s))) _;
  apply ∧ᵢ (function_ord_iso_map A r B s hwoB) _;
  apply ∧ᵢ _ _
  { assume z hz;
    refine ∃ₑ (ord_iso_mapE z A r B s hz) _;
    assume x hx;
    refine ∃ₑ hx _;
    assume y hy;
    have hzeq : π (z = Pair x y) { refine ∧ₑ₁ hy };
    have hz2 : π (Pair x y ∈ ord_iso_map A r B s)
      { refine ind_eq (eq_sym hzeq) (λ w, w ∈ ord_iso_map A r B s) hz };
    rewrite hzeq;
    refine SigmaI x y (domain (ord_iso_map A r B s)) (λ _, range (ord_iso_map A r B s))
      (domainI x y (ord_iso_map A r B s) hz2) (rangeI x y (ord_iso_map A r B s) hz2) }
  { assume a ha; apply ha }
end;

// ord_iso_map_mono_map: ord_iso_map is a monotone map on its domain/range
opaque symbol ord_iso_map_mono_map (A r B s : τ ι) :
  π (well_ord A r) → π (well_ord B s) →
  π (ord_iso_map A r B s
     ∈ mono_map (domain (ord_iso_map A r B s)) r (range (ord_iso_map A r B s)) s) ≔
begin
  assume A r B s hwoA hwoB;
  have hfun : π (ord_iso_map A r B s
      ∈ Pi (domain (ord_iso_map A r B s)) (λ _, range (ord_iso_map A r B s)))
    { refine ord_iso_map_fun A r B s hwoB };
  have hfunc : π (function (ord_iso_map A r B s)) { refine function_ord_iso_map A r B s hwoB };
  rewrite mono_map_def;
  refine CollectI (ord_iso_map A r B s)
    (Pi (domain (ord_iso_map A r B s)) (λ _, range (ord_iso_map A r B s)))
    (λ k, Ball (domain (ord_iso_map A r B s)) (λ x, Ball (domain (ord_iso_map A r B s)) (λ y,
      Pair x y ∈ r ⇒ Pair (fapply k x) (fapply k y) ∈ s))) hfun _;
  assume x hx y hy hxy;
  have hpx : π (Pair x (fapply (ord_iso_map A r B s) x) ∈ ord_iso_map A r B s)
    { refine apply_Pair (ord_iso_map A r B s) x hfunc hx };
  have hpy : π (Pair y (fapply (ord_iso_map A r B s) y) ∈ ord_iso_map A r B s)
    { refine apply_Pair (ord_iso_map A r B s) y hfunc hy };
  refine ∃ₑ (ord_iso_mapE (Pair x (fapply (ord_iso_map A r B s) x)) A r B s hpx) _;
  assume x1 h1;
  refine ∃ₑ h1 _;
  assume y1 h2;
  have hpeq1 : π (Pair x (fapply (ord_iso_map A r B s) x) = Pair x1 y1) { refine ∧ₑ₁ h2 };
  have hx1 : π (x = x1)
    { refine Pair_inject1 x (fapply (ord_iso_map A r B s) x) x1 y1 hpeq1 };
  have hfx1 : π (fapply (ord_iso_map A r B s) x = y1)
    { refine Pair_inject2 x (fapply (ord_iso_map A r B s) x) x1 y1 hpeq1 };
  have hx1A : π (x1 ∈ A) { refine ∧ₑ₁ (∧ₑ₂ h2) };
  have hy1B : π (y1 ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ h2)) };
  have hxA : π (x ∈ A) { refine ind_eq hx1 (λ w, w ∈ A) hx1A };
  refine ∃ₑ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h2))) _;
  assume f0 hf0;
  have hf1 : π (f0 ∈ ord_iso (pred A x r) r (pred B y1 s) s)
    { refine ind_eq hx1 (λ w, f0 ∈ ord_iso (pred A w r) r (pred B y1 s) s) hf0 };
  have hf2 : π (f0 ∈ ord_iso (pred A x r) r (pred B (fapply (ord_iso_map A r B s) x) s) s)
    { refine ind_eq hfx1 (λ w, f0 ∈ ord_iso (pred A x r) r (pred B w s) s) hf1 };
  have hfxB : π (fapply (ord_iso_map A r B s) x ∈ B) { refine ind_eq hfx1 (λ w, w ∈ B) hy1B };
  refine ∃ₑ (ord_iso_mapE (Pair y (fapply (ord_iso_map A r B s) y)) A r B s hpy) _;
  assume x2 h3;
  refine ∃ₑ h3 _;
  assume y2 h4;
  have hpeq2 : π (Pair y (fapply (ord_iso_map A r B s) y) = Pair x2 y2) { refine ∧ₑ₁ h4 };
  have hy2 : π (y = x2)
    { refine Pair_inject1 y (fapply (ord_iso_map A r B s) y) x2 y2 hpeq2 };
  have hfy2 : π (fapply (ord_iso_map A r B s) y = y2)
    { refine Pair_inject2 y (fapply (ord_iso_map A r B s) y) x2 y2 hpeq2 };
  have hx2A : π (x2 ∈ A) { refine ∧ₑ₁ (∧ₑ₂ h4) };
  have hy2B : π (y2 ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ h4)) };
  have hyA : π (y ∈ A) { refine ind_eq hy2 (λ w, w ∈ A) hx2A };
  refine ∃ₑ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h4))) _;
  assume g0 hg0;
  have hg1 : π (g0 ∈ ord_iso (pred A y r) r (pred B y2 s) s)
    { refine ind_eq hy2 (λ w, g0 ∈ ord_iso (pred A w r) r (pred B y2 s) s) hg0 };
  have hg2 : π (g0 ∈ ord_iso (pred A y r) r (pred B (fapply (ord_iso_map A r B s) y) s) s)
    { refine ind_eq hfy2 (λ w, g0 ∈ ord_iso (pred A y r) r (pred B w s) s) hg1 };
  have hfyB : π (fapply (ord_iso_map A r B s) y ∈ B) { refine ind_eq hfy2 (λ w, w ∈ B) hy2B };
  refine well_ord_iso_preserving A r B s f0 g0
    x (fapply (ord_iso_map A r B s) x) y (fapply (ord_iso_map A r B s) y)
    hwoA hwoB hxy hf2 hg2 hxA hyA hfxB hfyB
end;

// ord_iso_map_ord_iso: ord_iso_map is an order-isomorphism on its domain/range
opaque symbol ord_iso_map_ord_iso (A r B s : τ ι) :
  π (well_ord A r) → π (well_ord B s) →
  π (ord_iso_map A r B s
     ∈ ord_iso (domain (ord_iso_map A r B s)) r (range (ord_iso_map A r B s)) s) ≔
begin
  assume A r B s hwoA hwoB;
  have hwoD : π (well_ord (domain (ord_iso_map A r B s)) r)
    { refine well_ord_subset A (domain (ord_iso_map A r B s)) r hwoA (domain_ord_iso_map A r B s) };
  have hwoR : π (well_ord (range (ord_iso_map A r B s)) s)
    { refine well_ord_subset B (range (ord_iso_map A r B s)) s hwoB (range_ord_iso_map A r B s) };
  have hmono : π (ord_iso_map A r B s
      ∈ mono_map (domain (ord_iso_map A r B s)) r (range (ord_iso_map A r B s)) s)
    { refine ord_iso_map_mono_map A r B s hwoA hwoB };
  have hmono2 : π (ord_iso_map B s A r
      ∈ mono_map (domain (ord_iso_map B s A r)) s (range (ord_iso_map B s A r)) r)
    { refine ord_iso_map_mono_map B s A r hwoB hwoA };
  have hd : π (domain (ord_iso_map B s A r) = range (ord_iso_map A r B s))
    { rewrite left (converse_ord_iso_map A r B s);
      refine domain_converse (ord_iso_map A r B s) };
  have hr : π (range (ord_iso_map B s A r) = domain (ord_iso_map A r B s))
    { rewrite left (converse_ord_iso_map A r B s);
      refine range_converse (ord_iso_map A r B s) };
  have hmono3 : π (ord_iso_map B s A r
      ∈ mono_map (range (ord_iso_map A r B s)) s (range (ord_iso_map B s A r)) r)
    { refine ind_eq (eq_sym hd)
        (λ w, ord_iso_map B s A r ∈ mono_map w s (range (ord_iso_map B s A r)) r) hmono2 };
  have hmono4 : π (ord_iso_map B s A r
      ∈ mono_map (range (ord_iso_map A r B s)) s (domain (ord_iso_map A r B s)) r)
    { refine ind_eq (eq_sym hr)
        (λ w, ord_iso_map B s A r ∈ mono_map (range (ord_iso_map A r B s)) s w r) hmono3 };
  have hcmono : π (converse (ord_iso_map A r B s)
      ∈ mono_map (range (ord_iso_map A r B s)) s (domain (ord_iso_map A r B s)) r)
    { refine ind_eq (converse_ord_iso_map A r B s)
        (λ w, w ∈ mono_map (range (ord_iso_map A r B s)) s (domain (ord_iso_map A r B s)) r) hmono4 };
  refine well_ord_mono_ord_isoI (ord_iso_map A r B s)
    (domain (ord_iso_map A r B s)) r (range (ord_iso_map A r B s)) s
    hwoD hwoR hmono hcmono
end;

// domain_ord_iso_map_subset: the domain of ord_iso_map is downwards-closed
opaque symbol domain_ord_iso_map_subset (A r B s a : τ ι) :
  π (well_ord A r) → π (well_ord B s) → π (a ∈ A) →
  π (a ∉ domain (ord_iso_map A r B s)) →
  π (domain (ord_iso_map A r B s) ⊆ pred A a r) ≔
begin
  assume A r B s a hwoA hwoB haA hnd x hx;
  refine ∃ₑ (domainE x (ord_iso_map A r B s) hx) _;
  assume y hxy;
  refine ∃ₑ (ord_iso_mapE (Pair x y) A r B s hxy) _;
  assume x0 h0;
  refine ∃ₑ h0 _;
  assume y0 h1;
  have hpeq : π (Pair x y = Pair x0 y0) { refine ∧ₑ₁ h1 };
  have hx0 : π (x = x0) { refine Pair_inject1 x y x0 y0 hpeq };
  have hy0 : π (y = y0) { refine Pair_inject2 x y x0 y0 hpeq };
  have hx0A : π (x0 ∈ A) { refine ∧ₑ₁ (∧ₑ₂ h1) };
  have hy0B : π (y0 ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ h1)) };
  have hxA : π (x ∈ A) { refine ind_eq hx0 (λ w, w ∈ A) hx0A };
  have hyB : π (y ∈ B) { refine ind_eq hy0 (λ w, w ∈ B) hy0B };
  refine ∃ₑ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h1))) _;
  assume f hf0;
  have hfa : π (f ∈ ord_iso (pred A x r) r (pred B y0 s) s)
    { refine ind_eq hx0 (λ w, f ∈ ord_iso (pred A w r) r (pred B y0 s) s) hf0 };
  have hf : π (f ∈ ord_iso (pred A x r) r (pred B y s) s)
    { refine ind_eq hy0 (λ w, f ∈ ord_iso (pred A x r) r (pred B w s) s) hfa };
  have hlin : π (linear A r) { refine well_ord_is_linear A r hwoA };
  refine linearE A r x a (x ∈ pred A a r) hlin hxA haA _ _ _
  { assume hxa; refine predI x A a r hxa hxA }
  { assume hxeqa;
    have hadom : π (a ∈ domain (ord_iso_map A r B s))
      { refine ind_eq (eq_sym hxeqa) (λ w, w ∈ domain (ord_iso_map A r B s)) hx };
    refine ⊥ₑ (hnd hadom) }
  { assume hax;
    have haP : π (a ∈ pred A x r) { refine predI a A x r hax haA };
    have hfbij : π (f ∈ bij (pred A x r) (pred B y s))
      { refine ord_iso_is_bij f (pred A x r) r (pred B y s) s hf };
    have hfaP : π (fapply f a ∈ pred B y s)
      { refine bij_apply f (pred A x r) (pred B y s) a hfbij haP };
    have hfay : π (Pair (fapply f a) y ∈ s)
      { refine ∧ₑ₁ (∧ₑ₁ (pred_iff (fapply f a) B y s) hfaP) };
    have hfaB : π (fapply f a ∈ B)
      { refine ∧ₑ₂ (∧ₑ₁ (pred_iff (fapply f a) B y s) hfaP) };
    have htrA : π (trans_on A r) { refine well_ord_is_trans_on A r hwoA };
    have htrB : π (trans_on B s) { refine well_ord_is_trans_on B s hwoB };
    have hres : π (restrict f (pred (pred A x r) a r)
        ∈ ord_iso (pred (pred A x r) a r) r (pred (pred B y s) (fapply f a) s) s)
      { refine ord_iso_restrict_pred f (pred A x r) r (pred B y s) s a hf haP };
    have hpp1 : π (pred (pred A x r) a r = pred A a r)
      { refine trans_pred_pred_eq A r x a htrA hax hxA haA };
    have hpp2 : π (pred (pred B y s) (fapply f a) s = pred B (fapply f a) s)
      { refine trans_pred_pred_eq B s y (fapply f a) htrB hfay hyB hfaB };
    have hres2 : π (restrict f (pred A a r)
        ∈ ord_iso (pred A a r) r (pred (pred B y s) (fapply f a) s) s)
      { refine ind_eq (eq_sym hpp1)
          (λ w, restrict f w ∈ ord_iso w r (pred (pred B y s) (fapply f a) s) s) hres };
    have hres3 : π (restrict f (pred A a r)
        ∈ ord_iso (pred A a r) r (pred B (fapply f a) s) s)
      { refine ind_eq (eq_sym hpp2)
          (λ w, restrict f (pred A a r) ∈ ord_iso (pred A a r) r w s) hres2 };
    have hmem : π (Pair a (fapply f a) ∈ ord_iso_map A r B s)
      { refine ord_iso_mapI a (fapply f a) (restrict f (pred A a r)) A r B s haA hfaB hres3 };
    have hadom : π (a ∈ domain (ord_iso_map A r B s))
      { refine domainI a (fapply f a) (ord_iso_map A r B s) hmem };
    refine ⊥ₑ (hnd hadom) }
end;

// domain_ord_iso_map_cases: domain(ord_iso_map) = A or an initial segment
opaque symbol domain_ord_iso_map_cases (A r B s : τ ι) :
  π (well_ord A r) → π (well_ord B s) →
  π (domain (ord_iso_map A r B s) = A
     ∨ Bex A (λ x, domain (ord_iso_map A r B s) = pred A x r)) ≔
begin
  assume A r B s hwoA hwoB;
  have hdsub : π (domain (ord_iso_map A r B s) ⊆ A) { refine domain_ord_iso_map A r B s };
  refine ∨ₑ (em (Diff A (domain (ord_iso_map A r B s)) = empty)) _ _
  { assume hde;
    refine ∨ᵢ₁ _;
    refine subset_antisym (domain (ord_iso_map A r B s)) A hdsub _;
    assume z hzA;
    refine ∨ₑ (em (z ∈ domain (ord_iso_map A r B s))) _ _
    { assume h; refine h }
    { assume hnz;
      have hzD : π (z ∈ Diff A (domain (ord_iso_map A r B s)))
        { refine DiffI z A (domain (ord_iso_map A r B s)) hzA hnz };
      have hzE : π (z ∈ empty) { refine ind_eq (eq_sym hde) (λ w, z ∈ w) hzD };
      refine ⊥ₑ (emptyE z hzE) } }
  { assume hne;
    have hwf : π (wf A r) { refine well_ord_is_wf A r hwoA };
    have hDsub : π (Diff A (domain (ord_iso_map A r B s)) ⊆ A)
      { assume z hz; refine DiffD1 z A (domain (ord_iso_map A r B s)) hz };
    have hmin : π (Bex (Diff A (domain (ord_iso_map A r B s)))
        (λ a, Ball (Diff A (domain (ord_iso_map A r B s))) (λ z, Pair z a ∉ r)))
      { refine wfD A r hwf (Diff A (domain (ord_iso_map A r B s))) hDsub hne };
    refine ∃ₑ hmin _;
    assume a ha;
    have haD : π (a ∈ Diff A (domain (ord_iso_map A r B s))) { refine ∧ₑ₁ ha };
    have hamin : π (Ball (Diff A (domain (ord_iso_map A r B s))) (λ z, Pair z a ∉ r))
      { refine ∧ₑ₂ ha };
    have haA : π (a ∈ A) { refine DiffD1 a A (domain (ord_iso_map A r B s)) haD };
    have hand : π (a ∉ domain (ord_iso_map A r B s))
      { refine DiffD2 a A (domain (ord_iso_map A r B s)) haD };
    refine ∨ᵢ₂ _;
    refine ∃ᵢ a (∧ᵢ haA _);
    refine subset_antisym (domain (ord_iso_map A r B s)) (pred A a r)
      (domain_ord_iso_map_subset A r B s a hwoA hwoB haA hand) _;
    assume z hz;
    have hzA : π (z ∈ A) { refine pred_subset A a r z hz };
    have hzar : π (Pair z a ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z A a r) hz) };
    refine ∨ₑ (em (z ∈ domain (ord_iso_map A r B s))) _ _
    { assume h; refine h }
    { assume hnz;
      have hzD : π (z ∈ Diff A (domain (ord_iso_map A r B s)))
        { refine DiffI z A (domain (ord_iso_map A r B s)) hzA hnz };
      refine ⊥ₑ (hamin z hzD hzar) } }
end;

// range_ord_iso_map_cases: range(ord_iso_map) = B or an initial segment
opaque symbol range_ord_iso_map_cases (A r B s : τ ι) :
  π (well_ord A r) → π (well_ord B s) →
  π (range (ord_iso_map A r B s) = B
     ∨ Bex B (λ y, range (ord_iso_map A r B s) = pred B y s)) ≔
begin
  assume A r B s hwoA hwoB;
  have hd : π (domain (ord_iso_map B s A r) = range (ord_iso_map A r B s))
    { rewrite left (converse_ord_iso_map A r B s);
      refine domain_converse (ord_iso_map A r B s) };
  have hcases : π (domain (ord_iso_map B s A r) = B
      ∨ Bex B (λ y, domain (ord_iso_map B s A r) = pred B y s))
    { refine domain_ord_iso_map_cases B s A r hwoB hwoA };
  refine ∨ₑ hcases _ _
  { assume h1;
    refine ∨ᵢ₁ _;
    rewrite left hd;
    refine h1 }
  { assume h2;
    refine ∨ᵢ₂ _;
    refine ∃ₑ h2 _;
    assume y hy;
    refine ∃ᵢ y (∧ᵢ (∧ₑ₁ hy) _);
    rewrite left hd;
    refine ∧ₑ₂ hy }
end;

// ===========================================================================
// Section: Kunen's Theorem 6.3 — Trichotomy
// ===========================================================================

// well_ord_trichotomy: well_ord(A,r) → well_ord(B,s) →
//   ord_iso_map(A,r,B,s) ∈ ord_iso(A,r,B,s) ∨
//   (∃x∈A. ord_iso_map(A,r,B,s) ∈ ord_iso(pred(A,x,r),r,B,s)) ∨
//   (∃y∈B. ord_iso_map(A,r,B,s) ∈ ord_iso(A,r,pred(B,y,s),s))
// Kunen's Theorem 6.3.  4-way case analysis on domain/range_ord_iso_map_cases;
// the domain-and-range-both-proper case refutes itself: ord_iso_map would then
// witness ⟨x,y⟩ ∈ ord_iso_map, putting y ∈ pred(B,y,s), i.e. ⟨y,y⟩ ∈ s.
opaque symbol well_ord_trichotomy (A r B s : τ ι) :
  π (well_ord A r) → π (well_ord B s) →
  π (ord_iso_map A r B s ∈ ord_iso A r B s
     ∨ (Bex A (λ x, ord_iso_map A r B s ∈ ord_iso (pred A x r) r B s)
     ∨ Bex B (λ y, ord_iso_map A r B s ∈ ord_iso A r (pred B y s) s))) ≔
begin
  assume A r B s hwoA hwoB;
  have hiso : π (ord_iso_map A r B s
      ∈ ord_iso (domain (ord_iso_map A r B s)) r (range (ord_iso_map A r B s)) s)
    { refine ord_iso_map_ord_iso A r B s hwoA hwoB };
  refine ∨ₑ (domain_ord_iso_map_cases A r B s hwoA hwoB) _ _
  { assume hda;
    refine ∨ₑ (range_ord_iso_map_cases A r B s hwoA hwoB) _ _
    { assume hrb;
      refine ∨ᵢ₁ _;
      have h1 : π (ord_iso_map A r B s ∈ ord_iso A r (range (ord_iso_map A r B s)) s)
        { refine ind_eq (eq_sym hda)
            (λ w, ord_iso_map A r B s ∈ ord_iso w r (range (ord_iso_map A r B s)) s) hiso };
      refine ind_eq (eq_sym hrb) (λ w, ord_iso_map A r B s ∈ ord_iso A r w s) h1 }
    { assume hbexy;
      refine ∃ₑ hbexy _;
      assume y hy;
      have hyB : π (y ∈ B) { refine ∧ₑ₁ hy };
      have hry : π (range (ord_iso_map A r B s) = pred B y s) { refine ∧ₑ₂ hy };
      refine ∨ᵢ₂ (∨ᵢ₂ _);
      refine ∃ᵢ y (∧ᵢ hyB _);
      have h1 : π (ord_iso_map A r B s ∈ ord_iso A r (range (ord_iso_map A r B s)) s)
        { refine ind_eq (eq_sym hda)
            (λ w, ord_iso_map A r B s ∈ ord_iso w r (range (ord_iso_map A r B s)) s) hiso };
      refine ind_eq (eq_sym hry) (λ w, ord_iso_map A r B s ∈ ord_iso A r w s) h1 } }
  { assume hbexx;
    refine ∃ₑ hbexx _;
    assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    have hdx : π (domain (ord_iso_map A r B s) = pred A x r) { refine ∧ₑ₂ hx };
    refine ∨ₑ (range_ord_iso_map_cases A r B s hwoA hwoB) _ _
    { assume hrb;
      refine ∨ᵢ₂ (∨ᵢ₁ _);
      refine ∃ᵢ x (∧ᵢ hxA _);
      have h1 : π (ord_iso_map A r B s ∈ ord_iso (pred A x r) r (range (ord_iso_map A r B s)) s)
        { refine ind_eq (eq_sym hdx)
            (λ w, ord_iso_map A r B s ∈ ord_iso w r (range (ord_iso_map A r B s)) s) hiso };
      refine ind_eq (eq_sym hrb) (λ w, ord_iso_map A r B s ∈ ord_iso (pred A x r) r w s) h1 }
    { assume hbexy;
      refine ∃ₑ hbexy _;
      assume y hy;
      have hyB : π (y ∈ B) { refine ∧ₑ₁ hy };
      have hry : π (range (ord_iso_map A r B s) = pred B y s) { refine ∧ₑ₂ hy };
      have h1 : π (ord_iso_map A r B s ∈ ord_iso (pred A x r) r (range (ord_iso_map A r B s)) s)
        { refine ind_eq (eq_sym hdx)
            (λ w, ord_iso_map A r B s ∈ ord_iso w r (range (ord_iso_map A r B s)) s) hiso };
      have h2 : π (ord_iso_map A r B s ∈ ord_iso (pred A x r) r (pred B y s) s)
        { refine ind_eq (eq_sym hry)
            (λ w, ord_iso_map A r B s ∈ ord_iso (pred A x r) r w s) h1 };
      have hmem : π (Pair x y ∈ ord_iso_map A r B s)
        { refine ord_iso_mapI x y (ord_iso_map A r B s) A r B s hxA hyB h2 };
      have hyr : π (y ∈ range (ord_iso_map A r B s))
        { refine rangeI x y (ord_iso_map A r B s) hmem };
      have hyP : π (y ∈ pred B y s) { refine ind_eq (eq_sym hry) (λ w, y ∈ w) hyr };
      have hyy : π (Pair y y ∈ s) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff y B y s) hyP) };
      have hwfB : π (wf B s) { refine well_ord_is_wf B s hwoB };
      refine ⊥ₑ (wf_not_refl B s y hwfB hyB hyy) } }
end;

// ===========================================================================
// Section: Reflexive orders
// ===========================================================================

// Preorder abbreviation: preorder_on(field(r), r)
// Partial_order abbreviation: partial_order_on(field(r), r)

// subset_vimage_vimage_iff: Preorder(r) → A ⊆ field(r) → B ⊆ field(r) →
//   r-``A ⊆ r-``B ⟷ (∀a∈A. ∃b∈B. ⟨a,b⟩∈r)
opaque symbol subset_vimage_vimage_iff (r A B : τ ι) :
  π (preorder_on (field r) r) → π (A ⊆ field r) → π (B ⊆ field r) →
  π ((rel_vimage r A ⊆ rel_vimage r B)
     ⇔ Ball A (λ a, Bex B (λ b, Pair a b ∈ r))) ≔
begin
  assume r A B hpre hAf hBf;
  have hprop : π (refl_on (field r) r ∧ trans_on (field r) r)
    { refine ind_eq (eq_sym (preorder_on_def (field r) r)) (λ p, p) hpre };
  have hrefl : π (refl_on (field r) r) { refine ∧ₑ₁ hprop };
  have htrans : π (trans_on (field r) r) { refine ∧ₑ₂ hprop };
  apply ∧ᵢ
  { assume hsub a haA;
    have haf : π (a ∈ field r) { refine hAf a haA };
    have haa : π (Pair a a ∈ r) { refine refl_onD (field r) r a hrefl haf };
    have havA : π (a ∈ rel_vimage r A) { refine rel_vimageI a a r A haa haA };
    refine rel_vimageD a r B (hsub a havA) }
  { assume hball x hx;
    refine ∃ₑ (rel_vimageD x r A hx) _;
    assume a ha;
    have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
    have hxa : π (Pair x a ∈ r) { refine ∧ₑ₂ ha };
    refine ∃ₑ (hball a haA) _;
    assume b hb;
    have hbB : π (b ∈ B) { refine ∧ₑ₁ hb };
    have hab : π (Pair a b ∈ r) { refine ∧ₑ₂ hb };
    have hxd : π (x ∈ domain r) { refine domainI x a r hxa };
    have hxf : π (x ∈ field r) { rewrite field_def; refine UnI1 x (domain r) (range r) hxd };
    have hxb : π (Pair x b ∈ r)
      { refine trans_onD (field r) r x a b htrans hxf (hAf a haA) (hBf b hbB) hxa hab };
    refine rel_vimageI x b r B hxb hbB }
end;

// subset_vimage1_vimage1_iff: Preorder(r) → a,b ∈ field(r) →
//   r-``{a} ⊆ r-``{b} ⟷ ⟨a,b⟩∈r
opaque symbol subset_vimage1_vimage1_iff (r a b : τ ι) :
  π (preorder_on (field r) r) → π (a ∈ field r) → π (b ∈ field r) →
  π ((vimage_singleton r a ⊆ vimage_singleton r b) ⇔ (Pair a b ∈ r)) ≔
begin
  assume r a b hpre haf hbf;
  have hprop : π (refl_on (field r) r ∧ trans_on (field r) r)
    { refine ind_eq (eq_sym (preorder_on_def (field r) r)) (λ p, p) hpre };
  have hrefl : π (refl_on (field r) r) { refine ∧ₑ₁ hprop };
  have htrans : π (trans_on (field r) r) { refine ∧ₑ₂ hprop };
  apply ∧ᵢ
  { assume hsub;
    have haa : π (Pair a a ∈ r) { refine refl_onD (field r) r a hrefl haf };
    have hava : π (a ∈ vimage_singleton r a) { refine vimage_singletonI a a r haa };
    refine vimage_singletonD a b r (hsub a hava) }
  { assume hab x hx;
    have hxa : π (Pair x a ∈ r) { refine vimage_singletonD x a r hx };
    have hxd : π (x ∈ domain r) { refine domainI x a r hxa };
    have hxf : π (x ∈ field r) { rewrite field_def; refine UnI1 x (domain r) (range r) hxd };
    have hxb : π (Pair x b ∈ r) { refine trans_onD (field r) r x a b htrans hxf haf hbf hxa hab };
    refine vimage_singletonI x b r hxb }
end;

// Refl_antisym_eq_Image1_Image1_iff: refl + antisym → r``{a} = r``{b} ⟷ a = b
opaque symbol Refl_antisym_eq_Image1_Image1_iff (r a b : τ ι) :
  π (refl_on (field r) r) → π (antisym r) → π (a ∈ field r) → π (b ∈ field r) →
  π ((rel_image_sing r a = rel_image_sing r b) ⇔ (a = b)) ≔
begin
  assume r a b hrefl hanti haf hbf;
  apply ∧ᵢ
  { assume heq;
    have haa : π (Pair a a ∈ r) { refine refl_onD (field r) r a hrefl haf };
    have hbb : π (Pair b b ∈ r) { refine refl_onD (field r) r b hrefl hbf };
    have hara : π (a ∈ rel_image_sing r a) { refine rel_image_singI a a r haa };
    have harb : π (a ∈ rel_image_sing r b) { refine ind_eq (eq_sym heq) (λ w, a ∈ w) hara };
    have hba : π (Pair b a ∈ r) { refine rel_image_singD b a r harb };
    have hbrb : π (b ∈ rel_image_sing r b) { refine rel_image_singI b b r hbb };
    have hbra : π (b ∈ rel_image_sing r a) { refine ind_eq heq (λ w, b ∈ w) hbrb };
    have hab : π (Pair a b ∈ r) { refine rel_image_singD a b r hbra };
    refine antisymD r a b hanti hab hba }
  { assume heq;
    rewrite heq;
    reflexivity }
end;

// Partial_order_eq_Image1_Image1_iff: Partial_order(r) → r``{a} = r``{b} ⟷ a = b
opaque symbol Partial_order_eq_Image1_Image1_iff (r a b : τ ι) :
  π (partial_order_on (field r) r) → π (a ∈ field r) → π (b ∈ field r) →
  π ((rel_image_sing r a = rel_image_sing r b) ⇔ (a = b)) ≔
begin
  assume r a b hpo haf hbf;
  have hprop : π (preorder_on (field r) r ∧ antisym r)
    { refine ind_eq (eq_sym (partial_order_on_def (field r) r)) (λ p, p) hpo };
  have hpre2 : π (refl_on (field r) r ∧ trans_on (field r) r)
    { refine ind_eq (eq_sym (preorder_on_def (field r) r)) (λ p, p) (∧ₑ₁ hprop) };
  refine Refl_antisym_eq_Image1_Image1_iff r a b (∧ₑ₁ hpre2) (∧ₑ₂ hprop) haf hbf
end;

// Refl_antisym_eq_vimage1_vimage1_iff: refl + antisym → r-``{a} = r-``{b} ⟷ a = b
opaque symbol Refl_antisym_eq_vimage1_vimage1_iff (r a b : τ ι) :
  π (refl_on (field r) r) → π (antisym r) → π (a ∈ field r) → π (b ∈ field r) →
  π ((vimage_singleton r a = vimage_singleton r b) ⇔ (a = b)) ≔
begin
  assume r a b hrefl hanti haf hbf;
  apply ∧ᵢ
  { assume heq;
    have haa : π (Pair a a ∈ r) { refine refl_onD (field r) r a hrefl haf };
    have hbb : π (Pair b b ∈ r) { refine refl_onD (field r) r b hrefl hbf };
    have hava : π (a ∈ vimage_singleton r a) { refine vimage_singletonI a a r haa };
    have havb : π (a ∈ vimage_singleton r b) { refine ind_eq (eq_sym heq) (λ w, a ∈ w) hava };
    have hab : π (Pair a b ∈ r) { refine vimage_singletonD a b r havb };
    have hbvb : π (b ∈ vimage_singleton r b) { refine vimage_singletonI b b r hbb };
    have hbva : π (b ∈ vimage_singleton r a) { refine ind_eq heq (λ w, b ∈ w) hbvb };
    have hba : π (Pair b a ∈ r) { refine vimage_singletonD b a r hbva };
    refine antisymD r a b hanti hab hba }
  { assume heq;
    rewrite heq;
    reflexivity }
end;

// DEPRECATED stub (pre-fix name with its old — vacuous — statement; kept so
// no proved symbol vanishes vs. git HEAD. The genuine Isabelle lemma is
// Partial_order_eq_Image1_Image1_iff above; delete this with a conscious
// gate override).
opaque symbol Partial_order_eq_Image1_iff (r a b : τ ι) :
  π (partial_order_on (field r) r) → π (a ∈ field r) → π (b ∈ field r) →
  π (a = b ⇒ a = b) ≔
begin
  assume r a b hpo haF hbF hab;
  apply hab
end;

// Partial_order_eq_vimage1_vimage1_iff: Partial_order(r) → r-``{a} = r-``{b} ⟷ a = b
opaque symbol Partial_order_eq_vimage1_vimage1_iff (r a b : τ ι) :
  π (partial_order_on (field r) r) → π (a ∈ field r) → π (b ∈ field r) →
  π ((vimage_singleton r a = vimage_singleton r b) ⇔ (a = b)) ≔
begin
  assume r a b hpo haf hbf;
  have hprop : π (preorder_on (field r) r ∧ antisym r)
    { refine ind_eq (eq_sym (partial_order_on_def (field r) r)) (λ p, p) hpo };
  have hpre2 : π (refl_on (field r) r ∧ trans_on (field r) r)
    { refine ind_eq (eq_sym (preorder_on_def (field r) r)) (λ p, p) (∧ₑ₁ hprop) };
  refine Refl_antisym_eq_vimage1_vimage1_iff r a b (∧ₑ₁ hpre2) (∧ₑ₂ hprop) haf hbf
end;

// Composition of injections: g∈inj A B → f∈inj B C → (f∘g)∈inj A C
opaque symbol comp_inj (f g A B C : τ ι) :
  π (g ∈ inj A B) → π (f ∈ inj B C) → π (rcomp f g ∈ inj A C) ≔
begin
  assume f g A B C hg hf;
  have hgfun : π (g ∈ Pi A (λ _, B)) { refine inj_is_fun g A B hg };
  have hffun : π (f ∈ Pi B (λ _, C)) { refine inj_is_fun f B C hf };
  rewrite inj_def;
  refine CollectI (rcomp f g) (Pi A (λ _, C))
    (λ h, Ball A (λ w, Ball A (λ x, fapply h w = fapply h x ⇒ w = x)))
    (comp_fun f g A B C hgfun hffun) _;
  assume w hwA x hxA heq;
  have cw : π (fapply (rcomp f g) w = fapply f (fapply g w))
    { refine comp_fun_apply f g A B C w hgfun hffun hwA };
  have cx : π (fapply (rcomp f g) x = fapply f (fapply g x))
    { refine comp_fun_apply f g A B C x hgfun hffun hxA };
  have hfeq : π (fapply f (fapply g w) = fapply f (fapply g x))
    { refine eq_trans (eq_sym cw) (eq_trans heq cx) };
  have hgeq : π (fapply g w = fapply g x)
    { refine inj_apply_equality f B C (fapply g w) (fapply g x) hf hfeq
        (fapply_type g w A (λ _, B) hgfun hwA) (fapply_type g x A (λ _, B) hgfun hxA) };
  refine inj_apply_equality g A B w x hg hgeq hwA hxA
end;
