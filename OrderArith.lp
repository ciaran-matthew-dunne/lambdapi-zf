// OrderArith: Combining Orderings — Foundations of Ordinal Arithmetic
//
// Isabelle source: OrderArith.thy
// Defines: radd (disjoint sum of relations; ordinal addition),
//          rmult (lexicographic product; ordinal multiplication),
//          rvimage (inverse image of a relation),
//          measure, wfrank, wftype.
//
// Encoding notes (faithful to this port's conventions):
//   * products  A*B          → Sigma A (λ _, B)
//   * sums       A+B          → sum A B          (Inl/Inr; case_sum)
//   * Isabelle wf(r)  (global) → wf_global r
//   * Isabelle wf[A](r)        → wf A r
//   * <x,y>                   → Pair x y    (concrete Kuratowski; fst/snd via
//                                            fst_conv/snd_conv, NOT reduction)
//   * case(c,d,z)             → case_sum c d z   (case_Inl/case_Inr, NOT reduction)
//   * i<j                     → lt i j  (carries Ord; see CLAUDE.md §3)
//
// Status: definitions + all statements faithful and complete.  The
// well-foundedness layer (wf_onI2-style inductions), the wfrec-based wfrank /
// wftype results, and the lam_bijective/ord_iso congruence/associativity layer
// are admitted with TODOs (they need wf_on introduction + heavy case_sum/split
// computation that this port does not yet have as reusable lemmas).

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func
             ZF.Fixedpt ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum
             ZF.Ordinal ZF.Order;

// ===========================================================================
// Definitions
// ===========================================================================

// radd(A,r,B,s): disjoint sum of relations on A+B.
//   {z ∈ (A+B)*(A+B). (∃x y. z=<Inl x,Inr y>)
//                   ∨ (∃x' x. z=<Inl x',Inl x> ∧ <x',x>∈r)
//                   ∨ (∃y' y. z=<Inr y',Inr y> ∧ <y',y>∈s)}
symbol radd (A r B s : τ ι) : τ ι ≔
  Collect (Sigma (sum A B) (λ _, sum A B))
    (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
        ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
        ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s));

// rmult(A,r,B,s): lexicographic product of relations on A*B.
//   {z ∈ (A*B)*(A*B). ∃x' y' x y. z=<<x',y'>,<x,y>>
//                       ∧ (<x',x>∈r ∨ (x'=x ∧ <y',y>∈s))}
symbol rmult (A r B s : τ ι) : τ ι ≔
  Collect (Sigma (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B)))
    (λ z, `∃ (xp : τ ι), `∃ (yp : τ ι), `∃ (x : τ ι), `∃ (y : τ ι),
       z = Pair (Pair xp yp) (Pair x y)
       ∧ (Pair xp x ∈ r ∨ (xp = x ∧ Pair yp y ∈ s)));

// rvimage(A,f,r): inverse image of r under f.
//   {z ∈ A*A. ∃x y. z=<x,y> ∧ <f`x,f`y>∈r}
symbol rvimage (A f r : τ ι) : τ ι ≔
  Collect (Sigma A (λ _, A))
    (λ z, `∃ (x : τ ι), `∃ (y : τ ι),
       z = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ r);

// measure(A,f) = {<x,y> ∈ A*A. f(x) < f(y)}
symbol measure (A : τ ι) (f : τ ι → τ ι) : τ ι ≔
  Collect (Sigma A (λ _, A)) (λ z, lt (f (fst z)) (f (snd z)));

// wfrank(r,a) = wfrec(r, a, λx f. ⋃y∈r-``{x}. succ(f`y))
symbol wfrank (r a : τ ι) : τ ι ≔
  wfrec r a (λ x f, Union (RepFun (vimage_singleton r x) (λ y, succ (fapply f y))));

// wftype(r) = ⋃y∈range(r). succ(wfrank(r,y))
symbol wftype (r : τ ι) : τ ι ≔
  Union (RepFun (range r) (λ y, succ (wfrank r y)));

// ===========================================================================
// Addition of Relations -- Disjoint Sum
// ===========================================================================

// --- Rewrite rules (can be used to obtain introduction rules) ---

// radd_Inl_Inr_iff: <Inl a, Inr b> ∈ radd(A,r,B,s) ⟷ a∈A ∧ b∈B
opaque symbol radd_Inl_Inr_iff (a b A r B s : τ ι) :
  π (Pair (Inl a) (Inr b) ∈ radd A r B s ⇔ a ∈ A ∧ b ∈ B) ≔
begin
  assume a b A r B s;
  apply ∧ᵢ
  { assume h;
    have hSig : π (Pair (Inl a) (Inr b) ∈ Sigma (sum A B) (λ _, sum A B))
      { refine CollectD1 (Pair (Inl a) (Inr b)) (Sigma (sum A B) (λ _, sum A B))
          (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
              ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
              ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) h };
    have hInl : π (Inl a ∈ sum A B)
      { refine ind_eq (eq_sym (fst_conv (Inl a) (Inr b))) (λ w, w ∈ sum A B)
          (SigmaD1 (Pair (Inl a) (Inr b)) (sum A B) (λ _, sum A B) hSig) };
    have hInr : π (Inr b ∈ sum A B)
      { refine ind_eq (eq_sym (snd_conv (Inl a) (Inr b))) (λ w, w ∈ sum A B)
          (SigmaD2 (Pair (Inl a) (Inr b)) (sum A B) (λ _, sum A B) hSig) };
    refine ∧ᵢ (InlD a A B hInl) (InrD b A B hInr) }
  { assume h;
    refine CollectI (Pair (Inl a) (Inr b)) (Sigma (sum A B) (λ _, sum A B))
        (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
            ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
            ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) _ _
    { refine SigmaI (Inl a) (Inr b) (sum A B) (λ _, sum A B)
        (InlI a A B (∧ₑ₁ h)) (InrI b A B (∧ₑ₂ h)) }
    { refine ∨ᵢ₁ (∃ᵢ a (∃ᵢ b (eq_refl (Pair (Inl a) (Inr b))))) } }
end;

// radd_Inl_iff: <Inl a', Inl a> ∈ radd(A,r,B,s) ⟷ a'∈A ∧ a∈A ∧ <a',a>∈r
opaque symbol radd_Inl_iff (ap a A r B s : τ ι) :
  π (Pair (Inl ap) (Inl a) ∈ radd A r B s ⇔ ap ∈ A ∧ a ∈ A ∧ Pair ap a ∈ r) ≔
begin
  assume ap a A r B s;
  apply ∧ᵢ
  { assume h;
    have hSig : π (Pair (Inl ap) (Inl a) ∈ Sigma (sum A B) (λ _, sum A B))
      { refine CollectD1 (Pair (Inl ap) (Inl a)) (Sigma (sum A B) (λ _, sum A B))
          (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
              ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
              ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) h };
    have hapA : π (ap ∈ A)
      { refine InlD ap A B (ind_eq (eq_sym (fst_conv (Inl ap) (Inl a))) (λ w, w ∈ sum A B)
          (SigmaD1 (Pair (Inl ap) (Inl a)) (sum A B) (λ _, sum A B) hSig)) };
    have haA : π (a ∈ A)
      { refine InlD a A B (ind_eq (eq_sym (snd_conv (Inl ap) (Inl a))) (λ w, w ∈ sum A B)
          (SigmaD2 (Pair (Inl ap) (Inl a)) (sum A B) (λ _, sum A B) hSig)) };
    have hpred : π ((`∃ (x : τ ι), `∃ (y : τ ι), Pair (Inl ap) (Inl a) = Pair (Inl x) (Inr y))
                  ∨ (`∃ (xp : τ ι), `∃ (x : τ ι),
                       Pair (Inl ap) (Inl a) = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
                  ∨ (`∃ (yp : τ ι), `∃ (y : τ ι),
                       Pair (Inl ap) (Inl a) = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s))
      { refine CollectD2 (Pair (Inl ap) (Inl a)) (Sigma (sum A B) (λ _, sum A B))
          (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
              ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
              ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) h };
    have hr : π (Pair ap a ∈ r) {
      refine ∨ₑ hpred _ _
      { assume hd1;
        refine ∃ₑ hd1 _; assume x hx; refine ∃ₑ hx _; assume y hy;
        refine Inl_neq_Inr a y (Pair ap a ∈ r)
          (Pair_inject2 (Inl ap) (Inl a) (Inl x) (Inr y) hy) }
      { assume hd23;
        refine ∨ₑ hd23 _ _
        { assume hd2;
          refine ∃ₑ hd2 _; assume xp hxp; refine ∃ₑ hxp _; assume x hx2;
          have heq : π (Pair (Inl ap) (Inl a) = Pair (Inl xp) (Inl x)) { refine ∧ₑ₁ hx2 };
          have hapxp : π (ap = xp)
            { refine Inl_inject ap xp (Pair_inject1 (Inl ap) (Inl a) (Inl xp) (Inl x) heq) };
          have hax : π (a = x)
            { refine Inl_inject a x (Pair_inject2 (Inl ap) (Inl a) (Inl xp) (Inl x) heq) };
          rewrite hapxp; rewrite hax; refine ∧ₑ₂ hx2 }
        { assume hd3;
          refine ∃ₑ hd3 _; assume yp hyp; refine ∃ₑ hyp _; assume y hy3;
          refine Inl_neq_Inr ap yp (Pair ap a ∈ r)
            (Pair_inject1 (Inl ap) (Inl a) (Inr yp) (Inr y) (∧ₑ₁ hy3)) } } };
    refine ∧ᵢ hapA (∧ᵢ haA hr) }
  { assume h;
    refine CollectI (Pair (Inl ap) (Inl a)) (Sigma (sum A B) (λ _, sum A B))
        (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
            ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
            ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) _ _
    { refine SigmaI (Inl ap) (Inl a) (sum A B) (λ _, sum A B)
        (InlI ap A B (∧ₑ₁ h)) (InlI a A B (∧ₑ₁ (∧ₑ₂ h))) }
    { refine ∨ᵢ₂ (∨ᵢ₁ (∃ᵢ ap (∃ᵢ a
        (∧ᵢ (eq_refl (Pair (Inl ap) (Inl a))) (∧ₑ₂ (∧ₑ₂ h)))))) } }
end;

// radd_Inr_iff: <Inr b', Inr b> ∈ radd(A,r,B,s) ⟷ b'∈B ∧ b∈B ∧ <b',b>∈s
opaque symbol radd_Inr_iff (bp b A r B s : τ ι) :
  π (Pair (Inr bp) (Inr b) ∈ radd A r B s ⇔ bp ∈ B ∧ b ∈ B ∧ Pair bp b ∈ s) ≔
begin
  assume bp b A r B s;
  apply ∧ᵢ
  { assume h;
    have hSig : π (Pair (Inr bp) (Inr b) ∈ Sigma (sum A B) (λ _, sum A B))
      { refine CollectD1 (Pair (Inr bp) (Inr b)) (Sigma (sum A B) (λ _, sum A B))
          (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
              ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
              ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) h };
    have hbpB : π (bp ∈ B)
      { refine InrD bp A B (ind_eq (eq_sym (fst_conv (Inr bp) (Inr b))) (λ w, w ∈ sum A B)
          (SigmaD1 (Pair (Inr bp) (Inr b)) (sum A B) (λ _, sum A B) hSig)) };
    have hbB : π (b ∈ B)
      { refine InrD b A B (ind_eq (eq_sym (snd_conv (Inr bp) (Inr b))) (λ w, w ∈ sum A B)
          (SigmaD2 (Pair (Inr bp) (Inr b)) (sum A B) (λ _, sum A B) hSig)) };
    have hpred : π ((`∃ (x : τ ι), `∃ (y : τ ι), Pair (Inr bp) (Inr b) = Pair (Inl x) (Inr y))
                  ∨ (`∃ (xp : τ ι), `∃ (x : τ ι),
                       Pair (Inr bp) (Inr b) = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
                  ∨ (`∃ (yp : τ ι), `∃ (y : τ ι),
                       Pair (Inr bp) (Inr b) = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s))
      { refine CollectD2 (Pair (Inr bp) (Inr b)) (Sigma (sum A B) (λ _, sum A B))
          (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
              ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
              ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) h };
    have hs : π (Pair bp b ∈ s) {
      refine ∨ₑ hpred _ _
      { assume hd1;
        refine ∃ₑ hd1 _; assume x hx; refine ∃ₑ hx _; assume y hy;
        refine Inr_neq_Inl x bp (Pair bp b ∈ s)
          (Pair_inject1 (Inr bp) (Inr b) (Inl x) (Inr y) hy) }
      { assume hd23;
        refine ∨ₑ hd23 _ _
        { assume hd2;
          refine ∃ₑ hd2 _; assume xp hxp; refine ∃ₑ hxp _; assume x hx2;
          refine Inr_neq_Inl xp bp (Pair bp b ∈ s)
            (Pair_inject1 (Inr bp) (Inr b) (Inl xp) (Inl x) (∧ₑ₁ hx2)) }
        { assume hd3;
          refine ∃ₑ hd3 _; assume yp hyp; refine ∃ₑ hyp _; assume y hy3;
          have heq : π (Pair (Inr bp) (Inr b) = Pair (Inr yp) (Inr y)) { refine ∧ₑ₁ hy3 };
          have hbpyp : π (bp = yp)
            { refine Inr_inject bp yp (Pair_inject1 (Inr bp) (Inr b) (Inr yp) (Inr y) heq) };
          have hby : π (b = y)
            { refine Inr_inject b y (Pair_inject2 (Inr bp) (Inr b) (Inr yp) (Inr y) heq) };
          rewrite hbpyp; rewrite hby; refine ∧ₑ₂ hy3 } } };
    refine ∧ᵢ hbpB (∧ᵢ hbB hs) }
  { assume h;
    refine CollectI (Pair (Inr bp) (Inr b)) (Sigma (sum A B) (λ _, sum A B))
        (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
            ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
            ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) _ _
    { refine SigmaI (Inr bp) (Inr b) (sum A B) (λ _, sum A B)
        (InrI bp A B (∧ₑ₁ h)) (InrI b A B (∧ₑ₁ (∧ₑ₂ h))) }
    { refine ∨ᵢ₂ (∨ᵢ₂ (∃ᵢ bp (∃ᵢ b
        (∧ᵢ (eq_refl (Pair (Inr bp) (Inr b))) (∧ₑ₂ (∧ₑ₂ h)))))) } }
end;

// radd_Inr_Inl_iff: <Inr b, Inl a> ∈ radd(A,r,B,s) ⟷ False
opaque symbol radd_Inr_Inl_iff (b a A r B s : τ ι) :
  π (Pair (Inr b) (Inl a) ∈ radd A r B s ⇔ ⊥) ≔
begin
  assume b a A r B s;
  apply ∧ᵢ
  { assume h;
    have hpred : π ((`∃ (x : τ ι), `∃ (y : τ ι), Pair (Inr b) (Inl a) = Pair (Inl x) (Inr y))
                  ∨ (`∃ (xp : τ ι), `∃ (x : τ ι),
                       Pair (Inr b) (Inl a) = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
                  ∨ (`∃ (yp : τ ι), `∃ (y : τ ι),
                       Pair (Inr b) (Inl a) = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s))
      { refine CollectD2 (Pair (Inr b) (Inl a)) (Sigma (sum A B) (λ _, sum A B))
          (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
              ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
              ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) h };
    refine ∨ₑ hpred _ _
    { assume hd1;
      refine ∃ₑ hd1 _; assume x hx; refine ∃ₑ hx _; assume y hy;
      refine Inr_neq_Inl x b ⊥ (Pair_inject1 (Inr b) (Inl a) (Inl x) (Inr y) hy) }
    { assume hd23;
      refine ∨ₑ hd23 _ _
      { assume hd2;
        refine ∃ₑ hd2 _; assume xp hxp; refine ∃ₑ hxp _; assume x hx2;
        refine Inr_neq_Inl xp b ⊥
          (Pair_inject1 (Inr b) (Inl a) (Inl xp) (Inl x) (∧ₑ₁ hx2)) }
      { assume hd3;
        refine ∃ₑ hd3 _; assume yp hyp; refine ∃ₑ hyp _; assume y hy3;
        refine Inl_neq_Inr a y ⊥
          (Pair_inject2 (Inr b) (Inl a) (Inr yp) (Inr y) (∧ₑ₁ hy3)) } } }
  { assume h; refine ⊥ₑ h }
end;

// --- Elimination Rule ---
opaque symbol raddE (pp p A r B s : τ ι) (Q : Prop) :
  π (Pair pp p ∈ radd A r B s) →
  (Π (x y : τ ι), π (pp = Inl x) → π (x ∈ A) → π (p = Inr y) → π (y ∈ B) → π Q) →
  (Π (xp x : τ ι), π (pp = Inl xp) → π (p = Inl x) → π (Pair xp x ∈ r) →
     π (xp ∈ A) → π (x ∈ A) → π Q) →
  (Π (yp y : τ ι), π (pp = Inr yp) → π (p = Inr y) → π (Pair yp y ∈ s) →
     π (yp ∈ B) → π (y ∈ B) → π Q) →
  π Q ≔
begin
  assume pp p A r B s Q h f1 f2 f3;
  have hSig : π (Pair pp p ∈ Sigma (sum A B) (λ _, sum A B))
    { refine CollectD1 (Pair pp p) (Sigma (sum A B) (λ _, sum A B))
        (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
            ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
            ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) h };
  have hppS : π (pp ∈ sum A B)
    { refine ind_eq (eq_sym (fst_conv pp p)) (λ w, w ∈ sum A B)
        (SigmaD1 (Pair pp p) (sum A B) (λ _, sum A B) hSig) };
  have hpS : π (p ∈ sum A B)
    { refine ind_eq (eq_sym (snd_conv pp p)) (λ w, w ∈ sum A B)
        (SigmaD2 (Pair pp p) (sum A B) (λ _, sum A B) hSig) };
  have hpred : π ((`∃ (x : τ ι), `∃ (y : τ ι), Pair pp p = Pair (Inl x) (Inr y))
                ∨ (`∃ (xp : τ ι), `∃ (x : τ ι),
                     Pair pp p = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
                ∨ (`∃ (yp : τ ι), `∃ (y : τ ι),
                     Pair pp p = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s))
    { refine CollectD2 (Pair pp p) (Sigma (sum A B) (λ _, sum A B))
        (λ z, (`∃ (x : τ ι), `∃ (y : τ ι), z = Pair (Inl x) (Inr y))
            ∨ (`∃ (xp : τ ι), `∃ (x : τ ι), z = Pair (Inl xp) (Inl x) ∧ Pair xp x ∈ r)
            ∨ (`∃ (yp : τ ι), `∃ (y : τ ι), z = Pair (Inr yp) (Inr y) ∧ Pair yp y ∈ s)) h };
  refine ∨ₑ hpred _ _
  { assume hd1;
    refine ∃ₑ hd1 _; assume x hx; refine ∃ₑ hx _; assume y hy;
    have hpx : π (pp = Inl x) { refine Pair_inject1 pp p (Inl x) (Inr y) hy };
    have hpy : π (p = Inr y) { refine Pair_inject2 pp p (Inl x) (Inr y) hy };
    have hxA : π (x ∈ A) { refine InlD x A B (ind_eq (eq_sym hpx) (λ w, w ∈ sum A B) hppS) };
    have hyB : π (y ∈ B) { refine InrD y A B (ind_eq (eq_sym hpy) (λ w, w ∈ sum A B) hpS) };
    refine f1 x y hpx hxA hpy hyB }
  { assume hd23;
    refine ∨ₑ hd23 _ _
    { assume hd2;
      refine ∃ₑ hd2 _; assume xp hxp; refine ∃ₑ hxp _; assume x hx2;
      have heq : π (Pair pp p = Pair (Inl xp) (Inl x)) { refine ∧ₑ₁ hx2 };
      have hpxp : π (pp = Inl xp) { refine Pair_inject1 pp p (Inl xp) (Inl x) heq };
      have hpx : π (p = Inl x) { refine Pair_inject2 pp p (Inl xp) (Inl x) heq };
      have hxpA : π (xp ∈ A) { refine InlD xp A B (ind_eq (eq_sym hpxp) (λ w, w ∈ sum A B) hppS) };
      have hxA : π (x ∈ A) { refine InlD x A B (ind_eq (eq_sym hpx) (λ w, w ∈ sum A B) hpS) };
      refine f2 xp x hpxp hpx (∧ₑ₂ hx2) hxpA hxA }
    { assume hd3;
      refine ∃ₑ hd3 _; assume yp hyp; refine ∃ₑ hyp _; assume y hy3;
      have heq : π (Pair pp p = Pair (Inr yp) (Inr y)) { refine ∧ₑ₁ hy3 };
      have hpyp : π (pp = Inr yp) { refine Pair_inject1 pp p (Inr yp) (Inr y) heq };
      have hpy : π (p = Inr y) { refine Pair_inject2 pp p (Inr yp) (Inr y) heq };
      have hypB : π (yp ∈ B) { refine InrD yp A B (ind_eq (eq_sym hpyp) (λ w, w ∈ sum A B) hppS) };
      have hyB : π (y ∈ B) { refine InrD y A B (ind_eq (eq_sym hpy) (λ w, w ∈ sum A B) hpS) };
      refine f3 yp y hpyp hpy (∧ₑ₂ hy3) hypB hyB } }
end;

// --- Type checking ---

// radd_type: radd(A,r,B,s) ⊆ (A+B)*(A+B)
opaque symbol radd_type (A r B s : τ ι) :
  π (radd A r B s ⊆ Sigma (sum A B) (λ _, sum A B)) ≔
begin
  assume A r B s;
  refine Collect_subset (Sigma (sum A B) (λ _, sum A B)) _
end;

// field_radd: field(radd(A,r,B,s)) ⊆ A+B
opaque symbol field_radd (A r B s : τ ι) :
  π (field (radd A r B s) ⊆ sum A B) ≔
begin
  assume A r B s;
  refine field_rel_subset (radd A r B s) (sum A B) (radd_type A r B s)
end;

// --- Linearity ---
opaque symbol linear_radd (A r B s : τ ι) :
  π (linear A r) → π (linear B s) → π (linear (sum A B) (radd A r B s)) ≔
begin
  assume A r B s hlinA hlinB p hp q hq;
  refine sumE p A B _ hp _ _
  { assume px hpxA hpe;
    rewrite hpe;
    refine sumE q A B _ hq _ _
    { assume qx hqxA hqe;
      rewrite hqe;
      have hc : π (Pair px qx ∈ r ∨ (px = qx ∨ Pair qx px ∈ r))
        { refine hlinA px hpxA qx hqxA };
      refine ∨ₑ hc _ _
      { assume h1;
        refine ∨ᵢ₁ (∧ₑ₂ (radd_Inl_iff px qx A r B s) (∧ᵢ hpxA (∧ᵢ hqxA h1))) }
      { assume h2;
        refine ∨ₑ h2 _ _
        { assume heq; refine ∨ᵢ₂ (∨ᵢ₁ _); rewrite heq; reflexivity }
        { assume h3;
          refine ∨ᵢ₂ (∨ᵢ₂ (∧ₑ₂ (radd_Inl_iff qx px A r B s)
            (∧ᵢ hqxA (∧ᵢ hpxA h3)))) } } }
    { assume qy hqyB hqe;
      rewrite hqe;
      refine ∨ᵢ₁ (∧ₑ₂ (radd_Inl_Inr_iff px qy A r B s) (∧ᵢ hpxA hqyB)) } }
  { assume py hpyB hpe;
    rewrite hpe;
    refine sumE q A B _ hq _ _
    { assume qx hqxA hqe;
      rewrite hqe;
      refine ∨ᵢ₂ (∨ᵢ₂ (∧ₑ₂ (radd_Inl_Inr_iff qx py A r B s) (∧ᵢ hqxA hpyB))) }
    { assume qy hqyB hqe;
      rewrite hqe;
      have hc : π (Pair py qy ∈ s ∨ (py = qy ∨ Pair qy py ∈ s))
        { refine hlinB py hpyB qy hqyB };
      refine ∨ₑ hc _ _
      { assume h1;
        refine ∨ᵢ₁ (∧ₑ₂ (radd_Inr_iff py qy A r B s) (∧ᵢ hpyB (∧ᵢ hqyB h1))) }
      { assume h2;
        refine ∨ₑ h2 _ _
        { assume heq; refine ∨ᵢ₂ (∨ᵢ₁ _); rewrite heq; reflexivity }
        { assume h3;
          refine ∨ᵢ₂ (∨ᵢ₂ (∧ₑ₂ (radd_Inr_iff qy py A r B s)
            (∧ᵢ hqyB (∧ᵢ hpyB h3)))) } } } }
end;

// --- Well-foundedness ---
// Direct minimal-element proof: given nonempty Z ⊆ A+B, look at
// ZA = {x∈A. Inl x ∈ Z}.  If ZA ≠ 0 its r-minimal x0 gives the radd-minimal
// Inl x0 (nothing precedes an Inl but smaller Inls).  If ZA = 0, Z consists of
// Inrs only; the s-minimal y0 of ZB = {y∈B. Inr y ∈ Z} gives the radd-minimal
// Inr y0 (Inl-predecessors would put an element into the empty ZA).
opaque symbol wf_on_radd (A r B s : τ ι) :
  π (wf A r) → π (wf B s) → π (wf (sum A B) (radd A r B s)) ≔
begin
  assume A r B s hwfA hwfB Z hZsub hZne;
  refine ∨ₑ (em (Collect A (λ x, Inl x ∈ Z) = empty)) _ _
  { // ZA = 0: Z is all Inrs; use the s-minimal element of ZB.
    assume hZAe;
    refine not_emptyE Z _ hZne _;
    assume z0 hz0Z;
    refine sumE z0 A B _ (hZsub z0 hz0Z) _ _
    { assume a haA hz0e;
      have hInlZ : π (Inl a ∈ Z)
        { refine ind_eq (eq_sym hz0e) (λ w, w ∈ Z) hz0Z };
      refine ⊥ₑ (equals0D (Collect A (λ x, Inl x ∈ Z)) a hZAe
        (CollectI a A (λ x, Inl x ∈ Z) haA hInlZ)) }
    { assume b hbB hz0e;
      have hInrZ : π (Inr b ∈ Z)
        { refine ind_eq (eq_sym hz0e) (λ w, w ∈ Z) hz0Z };
      have hZBsub : π (Collect B (λ y, Inr y ∈ Z) ⊆ B)
        { assume w hw; refine CollectD1 w B (λ y, Inr y ∈ Z) hw };
      have hZBne : π (Collect B (λ y, Inr y ∈ Z) ≠ empty)
        { assume heq;
          refine equals0D (Collect B (λ y, Inr y ∈ Z)) b heq
            (CollectI b B (λ y, Inr y ∈ Z) hbB hInrZ) };
      have hminB : π (Bex (Collect B (λ y, Inr y ∈ Z))
                       (λ y, Ball (Collect B (λ y2, Inr y2 ∈ Z)) (λ y2, Pair y2 y ∉ s)))
        { refine hwfB (Collect B (λ y, Inr y ∈ Z)) hZBsub hZBne };
      refine ∃ₑ hminB _; assume y0 hy0;
      have hy0B : π (y0 ∈ B) { refine CollectD1 y0 B (λ y, Inr y ∈ Z) (∧ₑ₁ hy0) };
      have hy0Z : π (Inr y0 ∈ Z) { refine CollectD2 y0 B (λ y, Inr y ∈ Z) (∧ₑ₁ hy0) };
      have hy0min : π (Ball (Collect B (λ y, Inr y ∈ Z)) (λ y2, Pair y2 y0 ∉ s))
        { refine ∧ₑ₂ hy0 };
      refine ∃ᵢ (Inr y0) (∧ᵢ hy0Z _);
      assume w hwZ hmem;
      refine raddE w (Inr y0) A r B s ⊥ hmem _ _ _
      { assume x y hwe hxA hpe hyB;
        have hInlxZ : π (Inl x ∈ Z)
          { refine ind_eq (eq_sym hwe) (λ v, v ∈ Z) hwZ };
        refine equals0D (Collect A (λ x2, Inl x2 ∈ Z)) x hZAe
          (CollectI x A (λ x2, Inl x2 ∈ Z) hxA hInlxZ) }
      { assume xp x hwe hpe hr1 hxpA hxA;
        refine Inr_neq_Inl x y0 ⊥ hpe }
      { assume yp y hwe hpe hs1 hypB hyB;
        have hyy0 : π (y0 = y) { refine Inr_inject y0 y hpe };
        have hs0 : π (Pair yp y0 ∈ s)
          { refine ind_eq hyy0 (λ v, Pair yp v ∈ s) hs1 };
        have hypZ : π (Inr yp ∈ Z)
          { refine ind_eq (eq_sym hwe) (λ v, v ∈ Z) hwZ };
        refine hy0min yp (CollectI yp B (λ y2, Inr y2 ∈ Z) hypB hypZ) hs0 } } }
  { // ZA ≠ 0: use the r-minimal element of ZA.
    assume hZAne;
    have hZAsub : π (Collect A (λ x, Inl x ∈ Z) ⊆ A)
      { assume w hw; refine CollectD1 w A (λ x, Inl x ∈ Z) hw };
    have hminA : π (Bex (Collect A (λ x, Inl x ∈ Z))
                     (λ x, Ball (Collect A (λ x2, Inl x2 ∈ Z)) (λ x2, Pair x2 x ∉ r)))
      { refine hwfA (Collect A (λ x, Inl x ∈ Z)) hZAsub hZAne };
    refine ∃ₑ hminA _; assume x0 hx0;
    have hx0A : π (x0 ∈ A) { refine CollectD1 x0 A (λ x, Inl x ∈ Z) (∧ₑ₁ hx0) };
    have hx0Z : π (Inl x0 ∈ Z) { refine CollectD2 x0 A (λ x, Inl x ∈ Z) (∧ₑ₁ hx0) };
    have hx0min : π (Ball (Collect A (λ x, Inl x ∈ Z)) (λ x2, Pair x2 x0 ∉ r))
      { refine ∧ₑ₂ hx0 };
    refine ∃ᵢ (Inl x0) (∧ᵢ hx0Z _);
    assume w hwZ hmem;
    refine raddE w (Inl x0) A r B s ⊥ hmem _ _ _
    { assume x y hwe hxA hpe hyB;
      refine Inl_neq_Inr x0 y ⊥ hpe }
    { assume xp x hwe hpe hr1 hxpA hxA;
      have hxx0 : π (x0 = x) { refine Inl_inject x0 x hpe };
      have hr0 : π (Pair xp x0 ∈ r)
        { refine ind_eq hxx0 (λ v, Pair xp v ∈ r) hr1 };
      have hxpZ : π (Inl xp ∈ Z)
        { refine ind_eq (eq_sym hwe) (λ v, v ∈ Z) hwZ };
      refine hx0min xp (CollectI xp A (λ x2, Inl x2 ∈ Z) hxpA hxpZ) hr0 }
    { assume yp y hwe hpe hs1 hypB hyB;
      refine Inl_neq_Inr x0 y ⊥ hpe } }
end;

opaque symbol wf_radd (r s : τ ι) :
  π (wf_global r) → π (wf_global s) →
  π (wf_global (radd (field r) r (field s) s)) ≔
begin
  assume r s hr hs;
  have hwfsum : π (wf (sum (field r) (field s)) (radd (field r) r (field s) s))
    { refine wf_on_radd (field r) r (field s) s
        (wf_imp_wf_on (field r) r hr) (wf_imp_wf_on (field s) s hs) };
  have hwffield : π (wf (field (radd (field r) r (field s) s))
                       (radd (field r) r (field s) s))
    { refine wf_subset (sum (field r) (field s))
        (field (radd (field r) r (field s) s)) (radd (field r) r (field s) s)
        hwfsum (field_radd (field r) r (field s) s) };
  refine ∧ₑ₂ (wf_iff_wf_on_field (radd (field r) r (field s) s)) hwffield
end;

opaque symbol well_ord_radd (A r B s : τ ι) :
  π (well_ord A r) → π (well_ord B s) →
  π (well_ord (sum A B) (radd A r B s)) ≔
begin
  assume A r B s hA hB;
  refine well_ordI (sum A B) (radd A r B s)
    (wf_on_radd A r B s (well_ord_is_wf A r hA) (well_ord_is_wf B s hB))
    (linear_radd A r B s (well_ord_is_linear A r hA) (well_ord_is_linear B s hB))
end;

// --- ord_iso congruence laws ---

// sum_bij
opaque symbol sum_bij (f g A B C D : τ ι) :
  π (f ∈ bij A C) → π (g ∈ bij B D) →
  π (Lambda (sum A B) (λ z, case_sum (λ x, Inl (fapply f x)) (λ y, Inr (fapply g y)) z)
       ∈ bij (sum A B) (sum C D)) ≔
begin
  assume f g A B C D hf hg;
  refine lam_bijective (sum A B) (sum C D)
    (λ z, case_sum (λ x, Inl (fapply f x)) (λ y, Inr (fapply g y)) z)
    (λ w, case_sum (λ x, Inl (fapply (converse f) x))
                   (λ y, Inr (fapply (converse g) y)) w)
    _ _ _ _
  { // forward ∈ codomain
    assume z hz;
    refine case_type z A B (λ x, Inl (fapply f x)) (λ y, Inr (fapply g y))
      (λ _, sum C D) hz _ _
    { assume x hxA;
      refine InlI (fapply f x) C D (apply_type f A C x (bij_is_fun f A C hf) hxA) }
    { assume y hyB;
      refine InrI (fapply g y) C D (apply_type g B D y (bij_is_fun g B D hg) hyB) } }
  { // inverse ∈ domain
    assume w hw;
    refine case_type w C D (λ x, Inl (fapply (converse f) x))
      (λ y, Inr (fapply (converse g) y)) (λ _, sum A B) hw _ _
    { assume x hxC;
      refine InlI (fapply (converse f) x) A B (converse_bij_apply_type f A C x hf hxC) }
    { assume y hyD;
      refine InrI (fapply (converse g) y) A B (converse_bij_apply_type g B D y hg hyD) } }
  { // d (c z) = z on A+B
    assume z hz;
    refine sumE z A B _ hz _ _
    { assume x hxA hze;
      rewrite hze;
      have h1 : π (case_sum (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) (Inl x)
                   = Inl (fapply f x))
        { refine case_Inl (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) x };
      rewrite h1;
      have h2 : π (case_sum (λ x2, Inl (fapply (converse f) x2))
                            (λ y2, Inr (fapply (converse g) y2)) (Inl (fapply f x))
                   = Inl (fapply (converse f) (fapply f x)))
        { refine case_Inl (λ x2, Inl (fapply (converse f) x2))
            (λ y2, Inr (fapply (converse g) y2)) (fapply f x) };
      rewrite h2;
      rewrite (left_inverse_bij f A C x hf hxA);
      reflexivity }
    { assume y hyB hze;
      rewrite hze;
      have h1 : π (case_sum (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) (Inr y)
                   = Inr (fapply g y))
        { refine case_Inr (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) y };
      rewrite h1;
      have h2 : π (case_sum (λ x2, Inl (fapply (converse f) x2))
                            (λ y2, Inr (fapply (converse g) y2)) (Inr (fapply g y))
                   = Inr (fapply (converse g) (fapply g y)))
        { refine case_Inr (λ x2, Inl (fapply (converse f) x2))
            (λ y2, Inr (fapply (converse g) y2)) (fapply g y) };
      rewrite h2;
      rewrite (left_inverse_bij g B D y hg hyB);
      reflexivity } }
  { // c (d w) = w on C+D
    assume w hw;
    refine sumE w C D _ hw _ _
    { assume x hxC hwe;
      rewrite hwe;
      have h1 : π (case_sum (λ x2, Inl (fapply (converse f) x2))
                            (λ y2, Inr (fapply (converse g) y2)) (Inl x)
                   = Inl (fapply (converse f) x))
        { refine case_Inl (λ x2, Inl (fapply (converse f) x2))
            (λ y2, Inr (fapply (converse g) y2)) x };
      rewrite h1;
      have h2 : π (case_sum (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2))
                            (Inl (fapply (converse f) x))
                   = Inl (fapply f (fapply (converse f) x)))
        { refine case_Inl (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2))
            (fapply (converse f) x) };
      rewrite h2;
      rewrite (right_inverse_bij f A C x hf hxC);
      reflexivity }
    { assume y hyD hwe;
      rewrite hwe;
      have h1 : π (case_sum (λ x2, Inl (fapply (converse f) x2))
                            (λ y2, Inr (fapply (converse g) y2)) (Inr y)
                   = Inr (fapply (converse g) y))
        { refine case_Inr (λ x2, Inl (fapply (converse f) x2))
            (λ y2, Inr (fapply (converse g) y2)) y };
      rewrite h1;
      have h2 : π (case_sum (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2))
                            (Inr (fapply (converse g) y))
                   = Inr (fapply g (fapply (converse g) y)))
        { refine case_Inr (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2))
            (fapply (converse g) y) };
      rewrite h2;
      rewrite (right_inverse_bij g B D y hg hyD);
      reflexivity } }
end;

// Computation helpers: the sum_bij Lambda applied to Inl/Inr, β-normal.
private opaque symbol sum_bij_lam_Inl (f g A B x : τ ι) :
  π (x ∈ A) →
  π (fapply (Lambda (sum A B)
       (λ z, case_sum (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) z)) (Inl x)
     = Inl (fapply f x)) ≔
begin
  assume f g A B x hxA;
  rewrite (beta (sum A B)
    (λ z, case_sum (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) z)
    (Inl x) (InlI x A B hxA));
  refine case_Inl (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) x
end;

private opaque symbol sum_bij_lam_Inr (f g A B y : τ ι) :
  π (y ∈ B) →
  π (fapply (Lambda (sum A B)
       (λ z, case_sum (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) z)) (Inr y)
     = Inr (fapply g y)) ≔
begin
  assume f g A B y hyB;
  rewrite (beta (sum A B)
    (λ z, case_sum (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) z)
    (Inr y) (InrI y A B hyB));
  refine case_Inr (λ x2, Inl (fapply f x2)) (λ y2, Inr (fapply g y2)) y
end;

// sum_ord_iso_cong
opaque symbol sum_ord_iso_cong (f g A r Ap rp B s Bp sp : τ ι) :
  π (f ∈ ord_iso A r Ap rp) → π (g ∈ ord_iso B s Bp sp) →
  π (Lambda (sum A B) (λ z, case_sum (λ x, Inl (fapply f x)) (λ y, Inr (fapply g y)) z)
       ∈ ord_iso (sum A B) (radd A r B s) (sum Ap Bp) (radd Ap rp Bp sp)) ≔
begin
  assume f g A r Ap rp B s Bp sp hf hg;
  have hbf : π (f ∈ bij A Ap) { refine ord_iso_is_bij f A r Ap rp hf };
  have hbg : π (g ∈ bij B Bp) { refine ord_iso_is_bij g B s Bp sp hg };
  have hcondf : π (Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ rp))))
    { refine CollectD2 f (bij A Ap) (λ h, Ball A (λ x, Ball A (λ y,
        (Pair x y ∈ r) ⇔ (Pair (fapply h x) (fapply h y) ∈ rp)))) hf };
  have hcondg : π (Ball B (λ x, Ball B (λ y,
      (Pair x y ∈ s) ⇔ (Pair (fapply g x) (fapply g y) ∈ sp))))
    { refine CollectD2 g (bij B Bp) (λ h, Ball B (λ x, Ball B (λ y,
        (Pair x y ∈ s) ⇔ (Pair (fapply h x) (fapply h y) ∈ sp)))) hg };
  refine ord_isoI (Lambda (sum A B)
      (λ z, case_sum (λ x, Inl (fapply f x)) (λ y, Inr (fapply g y)) z))
    (sum A B) (radd A r B s) (sum Ap Bp) (radd Ap rp Bp sp)
    (sum_bij f g A B Ap Bp hbf hbg) _;
  assume z hz w hw;
  refine sumE z A B _ hz _ _
  { assume x hxA hze;
    rewrite hze;
    rewrite (sum_bij_lam_Inl f g A B x hxA);
    refine sumE w A B _ hw _ _
    { assume xp hxpA hwe;
      rewrite hwe;
      rewrite (sum_bij_lam_Inl f g A B xp hxpA);
      apply ∧ᵢ
      { assume h;
        have hr1 : π (Pair x xp ∈ r)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff x xp A r B s) h)) };
        refine ∧ₑ₂ (radd_Inl_iff (fapply f x) (fapply f xp) Ap rp Bp sp)
          (∧ᵢ (apply_type f A Ap x (bij_is_fun f A Ap hbf) hxA)
              (∧ᵢ (apply_type f A Ap xp (bij_is_fun f A Ap hbf) hxpA)
                  (∧ₑ₁ (hcondf x hxA xp hxpA) hr1))) }
      { assume h;
        have hrp1 : π (Pair (fapply f x) (fapply f xp) ∈ rp)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁
              (radd_Inl_iff (fapply f x) (fapply f xp) Ap rp Bp sp) h)) };
        refine ∧ₑ₂ (radd_Inl_iff x xp A r B s)
          (∧ᵢ hxA (∧ᵢ hxpA (∧ₑ₂ (hcondf x hxA xp hxpA) hrp1))) } }
    { assume yp hypB hwe;
      rewrite hwe;
      rewrite (sum_bij_lam_Inr f g A B yp hypB);
      apply ∧ᵢ
      { assume h;
        refine ∧ₑ₂ (radd_Inl_Inr_iff (fapply f x) (fapply g yp) Ap rp Bp sp)
          (∧ᵢ (apply_type f A Ap x (bij_is_fun f A Ap hbf) hxA)
              (apply_type g B Bp yp (bij_is_fun g B Bp hbg) hypB)) }
      { assume h;
        refine ∧ₑ₂ (radd_Inl_Inr_iff x yp A r B s) (∧ᵢ hxA hypB) } } }
  { assume y hyB hze;
    rewrite hze;
    rewrite (sum_bij_lam_Inr f g A B y hyB);
    refine sumE w A B _ hw _ _
    { assume xp hxpA hwe;
      rewrite hwe;
      rewrite (sum_bij_lam_Inl f g A B xp hxpA);
      apply ∧ᵢ
      { assume h;
        refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff y xp A r B s) h) }
      { assume h;
        refine ⊥ₑ (∧ₑ₁
          (radd_Inr_Inl_iff (fapply g y) (fapply f xp) Ap rp Bp sp) h) } }
    { assume yp hypB hwe;
      rewrite hwe;
      rewrite (sum_bij_lam_Inr f g A B yp hypB);
      apply ∧ᵢ
      { assume h;
        have hs1 : π (Pair y yp ∈ s)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff y yp A r B s) h)) };
        refine ∧ₑ₂ (radd_Inr_iff (fapply g y) (fapply g yp) Ap rp Bp sp)
          (∧ᵢ (apply_type g B Bp y (bij_is_fun g B Bp hbg) hyB)
              (∧ᵢ (apply_type g B Bp yp (bij_is_fun g B Bp hbg) hypB)
                  (∧ₑ₁ (hcondg y hyB yp hypB) hs1))) }
      { assume h;
        have hsp1 : π (Pair (fapply g y) (fapply g yp) ∈ sp)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁
              (radd_Inr_iff (fapply g y) (fapply g yp) Ap rp Bp sp) h)) };
        refine ∧ₑ₂ (radd_Inr_iff y yp A r B s)
          (∧ᵢ hyB (∧ᵢ hypB (∧ₑ₂ (hcondg y hyB yp hypB) hsp1))) } } }
end;

// sum_disjoint_bij: A∩B=0 → (λz∈A+B. case(λx.x,λy.y,z)) ∈ bij(A+B, A∪B)
opaque symbol sum_disjoint_bij (A B : τ ι) :
  π (Int A B = empty) →
  π (Lambda (sum A B) (λ z, case_sum (λ x, x) (λ y, y) z) ∈ bij (sum A B) (Un A B)) ≔
begin
  assume A B hdisj;
  refine lam_bijective (sum A B) (Un A B)
    (λ z, case_sum (λ x, x) (λ y, y) z)
    (λ w, If (w ∈ A) (Inl w) (Inr w))
    _ _ _ _
  { // forward ∈ codomain
    assume z hz;
    refine case_type z A B (λ x, x) (λ y, y) (λ _, Un A B) hz _ _
    { assume x hxA; refine UnI1 x A B hxA }
    { assume y hyB; refine UnI2 y A B hyB } }
  { // inverse ∈ domain
    assume w hw;
    refine ∨ₑ (em (w ∈ A)) _ _
    { assume hwA;
      rewrite (If_P (w ∈ A) (Inl w) (Inr w) hwA);
      refine InlI w A B hwA }
    { assume hwnA;
      rewrite (If_not_P (w ∈ A) (Inl w) (Inr w) hwnA);
      have hwB : π (w ∈ B)
        { refine ∨ₑ (UnE w A B hw) _ _
          { assume hwA2; refine ⊥ₑ (hwnA hwA2) }
          { assume hwB2; refine hwB2 } };
      refine InrI w A B hwB } }
  { // d (c z) = z on A+B
    assume z hz;
    refine sumE z A B _ hz _ _
    { assume x hxA hze;
      rewrite hze;
      have h1 : π (case_sum (λ x2, x2) (λ y2, y2) (Inl x) = x)
        { refine case_Inl (λ x2, x2) (λ y2, y2) x };
      rewrite h1;
      rewrite (If_P (x ∈ A) (Inl x) (Inr x) hxA);
      reflexivity }
    { assume y hyB hze;
      rewrite hze;
      have h1 : π (case_sum (λ x2, x2) (λ y2, y2) (Inr y) = y)
        { refine case_Inr (λ x2, x2) (λ y2, y2) y };
      rewrite h1;
      have hynA : π (¬ (y ∈ A))
        { assume hyA;
          refine emptyE y (ind_eq (eq_sym hdisj) (λ t, y ∈ t) (IntI y A B hyA hyB)) };
      rewrite (If_not_P (y ∈ A) (Inl y) (Inr y) hynA);
      reflexivity } }
  { // c (d w) = w on A∪B
    assume w hw;
    refine ∨ₑ (em (w ∈ A)) _ _
    { assume hwA;
      rewrite (If_P (w ∈ A) (Inl w) (Inr w) hwA);
      have h1 : π (case_sum (λ x2, x2) (λ y2, y2) (Inl w) = w)
        { refine case_Inl (λ x2, x2) (λ y2, y2) w };
      rewrite h1;
      reflexivity }
    { assume hwnA;
      rewrite (If_not_P (w ∈ A) (Inl w) (Inr w) hwnA);
      have h1 : π (case_sum (λ x2, x2) (λ y2, y2) (Inr w) = w)
        { refine case_Inr (λ x2, x2) (λ y2, y2) w };
      rewrite h1;
      reflexivity } }
end;

// --- Associativity ---

// sum_assoc_bij
opaque symbol sum_assoc_bij (A B C : τ ι) :
  π (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x, Inl x) (λ y, Inr (Inl y))) (λ y, Inr (Inr y)) z)
       ∈ bij (sum (sum A B) C) (sum A (sum B C))) ≔
begin
  assume A B C;
  refine lam_bijective (sum (sum A B) C) (sum A (sum B C))
    (λ z, case_sum (case_sum (λ x, Inl x) (λ y, Inr (Inl y))) (λ y, Inr (Inr y)) z)
    (λ w, case_sum (λ x, Inl (Inl x))
                   (case_sum (λ y, Inl (Inr y)) (λ v, Inr v)) w)
    _ _ _ _
  { // forward ∈ codomain
    assume z hz;
    refine case_type z (sum A B) C
      (case_sum (λ x, Inl x) (λ y, Inr (Inl y))) (λ y, Inr (Inr y))
      (λ _, sum A (sum B C)) hz _ _
    { assume u huAB;
      refine case_type u A B (λ x, Inl x) (λ y, Inr (Inl y))
        (λ _, sum A (sum B C)) huAB _ _
      { assume x hxA; refine InlI x A (sum B C) hxA }
      { assume y hyB; refine InrI (Inl y) A (sum B C) (InlI y B C hyB) } }
    { assume v hvC; refine InrI (Inr v) A (sum B C) (InrI v B C hvC) } }
  { // inverse ∈ domain
    assume w hw;
    refine case_type w A (sum B C)
      (λ x, Inl (Inl x)) (case_sum (λ y, Inl (Inr y)) (λ v, Inr v))
      (λ _, sum (sum A B) C) hw _ _
    { assume x hxA; refine InlI (Inl x) (sum A B) C (InlI x A B hxA) }
    { assume u huBC;
      refine case_type u B C (λ y, Inl (Inr y)) (λ v, Inr v)
        (λ _, sum (sum A B) C) huBC _ _
      { assume y hyB; refine InlI (Inr y) (sum A B) C (InrI y A B hyB) }
      { assume v hvC; refine InrI v (sum A B) C hvC } } }
  { // d (c z) = z on (A+B)+C
    assume z hz;
    refine sumE z (sum A B) C _ hz _ _
    { assume u huAB hze;
      rewrite hze;
      refine sumE u A B _ huAB _ _
      { assume x hxA hue;
        rewrite hue;
        have h1 : π (case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                              (λ y2, Inr (Inr y2)) (Inl (Inl x)) = Inl x)
          { rewrite (case_Inl (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
              (λ y2, Inr (Inr y2)) (Inl x));
            refine case_Inl (λ x2, Inl x2) (λ y2, Inr (Inl y2)) x };
        rewrite h1;
        have h2 : π (case_sum (λ x2, Inl (Inl x2))
                              (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2))
                              (Inl x) = Inl (Inl x))
          { refine case_Inl (λ x2, Inl (Inl x2))
              (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2)) x };
        rewrite h2;
        reflexivity }
      { assume y hyB hue;
        rewrite hue;
        have h1 : π (case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                              (λ y2, Inr (Inr y2)) (Inl (Inr y)) = Inr (Inl y))
          { rewrite (case_Inl (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
              (λ y2, Inr (Inr y2)) (Inr y));
            refine case_Inr (λ x2, Inl x2) (λ y2, Inr (Inl y2)) y };
        rewrite h1;
        have h2 : π (case_sum (λ x2, Inl (Inl x2))
                              (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2))
                              (Inr (Inl y)) = Inl (Inr y))
          { rewrite (case_Inr (λ x2, Inl (Inl x2))
              (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2)) (Inl y));
            refine case_Inl (λ y2, Inl (Inr y2)) (λ v2, Inr v2) y };
        rewrite h2;
        reflexivity } }
    { assume v hvC hze;
      rewrite hze;
      have h1 : π (case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                            (λ y2, Inr (Inr y2)) (Inr v) = Inr (Inr v))
        { refine case_Inr (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
            (λ y2, Inr (Inr y2)) v };
      rewrite h1;
      have h2 : π (case_sum (λ x2, Inl (Inl x2))
                            (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2))
                            (Inr (Inr v)) = Inr v)
        { rewrite (case_Inr (λ x2, Inl (Inl x2))
            (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2)) (Inr v));
          refine case_Inr (λ y2, Inl (Inr y2)) (λ v2, Inr v2) v };
      rewrite h2;
      reflexivity } }
  { // c (d w) = w on A+(B+C)
    assume w hw;
    refine sumE w A (sum B C) _ hw _ _
    { assume x hxA hwe;
      rewrite hwe;
      have h1 : π (case_sum (λ x2, Inl (Inl x2))
                            (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2))
                            (Inl x) = Inl (Inl x))
        { refine case_Inl (λ x2, Inl (Inl x2))
            (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2)) x };
      rewrite h1;
      have h2 : π (case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                            (λ y2, Inr (Inr y2)) (Inl (Inl x)) = Inl x)
        { rewrite (case_Inl (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
            (λ y2, Inr (Inr y2)) (Inl x));
          refine case_Inl (λ x2, Inl x2) (λ y2, Inr (Inl y2)) x };
      rewrite h2;
      reflexivity }
    { assume u huBC hwe;
      rewrite hwe;
      refine sumE u B C _ huBC _ _
      { assume y hyB hue;
        rewrite hue;
        have h1 : π (case_sum (λ x2, Inl (Inl x2))
                              (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2))
                              (Inr (Inl y)) = Inl (Inr y))
          { rewrite (case_Inr (λ x2, Inl (Inl x2))
              (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2)) (Inl y));
            refine case_Inl (λ y2, Inl (Inr y2)) (λ v2, Inr v2) y };
        rewrite h1;
        have h2 : π (case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                              (λ y2, Inr (Inr y2)) (Inl (Inr y)) = Inr (Inl y))
          { rewrite (case_Inl (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
              (λ y2, Inr (Inr y2)) (Inr y));
            refine case_Inr (λ x2, Inl x2) (λ y2, Inr (Inl y2)) y };
        rewrite h2;
        reflexivity }
      { assume v hvC hue;
        rewrite hue;
        have h1 : π (case_sum (λ x2, Inl (Inl x2))
                              (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2))
                              (Inr (Inr v)) = Inr v)
          { rewrite (case_Inr (λ x2, Inl (Inl x2))
              (case_sum (λ y2, Inl (Inr y2)) (λ v2, Inr v2)) (Inr v));
            refine case_Inr (λ y2, Inl (Inr y2)) (λ v2, Inr v2) v };
        rewrite h1;
        have h2 : π (case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                              (λ y2, Inr (Inr y2)) (Inr v) = Inr (Inr v))
          { refine case_Inr (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
              (λ y2, Inr (Inr y2)) v };
        rewrite h2;
        reflexivity } } }
end;

// Computation helpers: the sum_assoc Lambda applied to the three shapes.
private opaque symbol sum_assoc_lam_ll (A B C x : τ ι) :
  π (x ∈ A) →
  π (fapply (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                      (λ y2, Inr (Inr y2)) z)) (Inl (Inl x))
     = Inl x) ≔
begin
  assume A B C x hxA;
  have hb : π (fapply (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                      (λ y2, Inr (Inr y2)) z)) (Inl (Inl x))
     = case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                (λ y2, Inr (Inr y2)) (Inl (Inl x)))
    { refine beta (sum (sum A B) C)
        (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                       (λ y2, Inr (Inr y2)) z)
        (Inl (Inl x)) (InlI (Inl x) (sum A B) C (InlI x A B hxA)) };
  rewrite hb;
  rewrite (case_Inl (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
    (λ y2, Inr (Inr y2)) (Inl x));
  refine case_Inl (λ x2, Inl x2) (λ y2, Inr (Inl y2)) x
end;

private opaque symbol sum_assoc_lam_lr (A B C y : τ ι) :
  π (y ∈ B) →
  π (fapply (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                      (λ y2, Inr (Inr y2)) z)) (Inl (Inr y))
     = Inr (Inl y)) ≔
begin
  assume A B C y hyB;
  have hb : π (fapply (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                      (λ y2, Inr (Inr y2)) z)) (Inl (Inr y))
     = case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                (λ y2, Inr (Inr y2)) (Inl (Inr y)))
    { refine beta (sum (sum A B) C)
        (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                       (λ y2, Inr (Inr y2)) z)
        (Inl (Inr y)) (InlI (Inr y) (sum A B) C (InrI y A B hyB)) };
  rewrite hb;
  rewrite (case_Inl (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
    (λ y2, Inr (Inr y2)) (Inr y));
  refine case_Inr (λ x2, Inl x2) (λ y2, Inr (Inl y2)) y
end;

private opaque symbol sum_assoc_lam_r (A B C v : τ ι) :
  π (v ∈ C) →
  π (fapply (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                      (λ y2, Inr (Inr y2)) z)) (Inr v)
     = Inr (Inr v)) ≔
begin
  assume A B C v hvC;
  have hb : π (fapply (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                      (λ y2, Inr (Inr y2)) z)) (Inr v)
     = case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                (λ y2, Inr (Inr y2)) (Inr v))
    { refine beta (sum (sum A B) C)
        (λ z, case_sum (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
                       (λ y2, Inr (Inr y2)) z)
        (Inr v) (InrI v (sum A B) C hvC) };
  rewrite hb;
  refine case_Inr (case_sum (λ x2, Inl x2) (λ y2, Inr (Inl y2)))
    (λ y2, Inr (Inr y2)) v
end;

// sum_assoc_ord_iso
opaque symbol sum_assoc_ord_iso (A r B s C t : τ ι) :
  π (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x, Inl x) (λ y, Inr (Inl y))) (λ y, Inr (Inr y)) z)
       ∈ ord_iso (sum (sum A B) C) (radd (sum A B) (radd A r B s) C t)
                 (sum A (sum B C)) (radd A r (sum B C) (radd B s C t))) ≔
begin
  assume A r B s C t;
  refine ord_isoI (Lambda (sum (sum A B) C)
      (λ z, case_sum (case_sum (λ x, Inl x) (λ y, Inr (Inl y))) (λ y, Inr (Inr y)) z))
    (sum (sum A B) C) (radd (sum A B) (radd A r B s) C t)
    (sum A (sum B C)) (radd A r (sum B C) (radd B s C t))
    (sum_assoc_bij A B C) _;
  assume z hz w hw;
  refine sumE z (sum A B) C _ hz _ _
  { assume u huAB hze;
    rewrite hze;
    refine sumE u A B _ huAB _ _
    { // z = Inl (Inl x)
      assume x hxA hue;
      rewrite hue;
      rewrite (sum_assoc_lam_ll A B C x hxA);
      refine sumE w (sum A B) C _ hw _ _
      { assume up hupAB hwe;
        rewrite hwe;
        refine sumE up A B _ hupAB _ _
        { assume xp hxpA hupe;
          rewrite hupe;
          rewrite (sum_assoc_lam_ll A B C xp hxpA);
          apply ∧ᵢ
          { assume h;
            have hinner : π (Pair (Inl x) (Inl xp) ∈ radd A r B s)
              { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff (Inl x) (Inl xp)
                  (sum A B) (radd A r B s) C t) h)) };
            have hr1 : π (Pair x xp ∈ r)
              { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff x xp A r B s) hinner)) };
            refine ∧ₑ₂ (radd_Inl_iff x xp A r (sum B C) (radd B s C t))
              (∧ᵢ hxA (∧ᵢ hxpA hr1)) }
          { assume h;
            have hr1 : π (Pair x xp ∈ r)
              { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff x xp A r
                  (sum B C) (radd B s C t)) h)) };
            refine ∧ₑ₂ (radd_Inl_iff (Inl x) (Inl xp) (sum A B) (radd A r B s) C t)
              (∧ᵢ (InlI x A B hxA) (∧ᵢ (InlI xp A B hxpA)
                (∧ₑ₂ (radd_Inl_iff x xp A r B s) (∧ᵢ hxA (∧ᵢ hxpA hr1))))) } }
        { assume yp hypB hupe;
          rewrite hupe;
          rewrite (sum_assoc_lam_lr A B C yp hypB);
          apply ∧ᵢ
          { assume h;
            refine ∧ₑ₂ (radd_Inl_Inr_iff x (Inl yp) A r (sum B C) (radd B s C t))
              (∧ᵢ hxA (InlI yp B C hypB)) }
          { assume h;
            refine ∧ₑ₂ (radd_Inl_iff (Inl x) (Inr yp) (sum A B) (radd A r B s) C t)
              (∧ᵢ (InlI x A B hxA) (∧ᵢ (InrI yp A B hypB)
                (∧ₑ₂ (radd_Inl_Inr_iff x yp A r B s) (∧ᵢ hxA hypB)))) } } }
      { assume vp hvpC hwe;
        rewrite hwe;
        rewrite (sum_assoc_lam_r A B C vp hvpC);
        apply ∧ᵢ
        { assume h;
          refine ∧ₑ₂ (radd_Inl_Inr_iff x (Inr vp) A r (sum B C) (radd B s C t))
            (∧ᵢ hxA (InrI vp B C hvpC)) }
        { assume h;
          refine ∧ₑ₂ (radd_Inl_Inr_iff (Inl x) vp (sum A B) (radd A r B s) C t)
            (∧ᵢ (InlI x A B hxA) hvpC) } } }
    { // z = Inl (Inr y)
      assume y hyB hue;
      rewrite hue;
      rewrite (sum_assoc_lam_lr A B C y hyB);
      refine sumE w (sum A B) C _ hw _ _
      { assume up hupAB hwe;
        rewrite hwe;
        refine sumE up A B _ hupAB _ _
        { assume xp hxpA hupe;
          rewrite hupe;
          rewrite (sum_assoc_lam_ll A B C xp hxpA);
          apply ∧ᵢ
          { assume h;
            have hinner : π (Pair (Inr y) (Inl xp) ∈ radd A r B s)
              { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff (Inr y) (Inl xp)
                  (sum A B) (radd A r B s) C t) h)) };
            refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff y xp A r B s) hinner) }
          { assume h;
            refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff (Inl y) xp A r
              (sum B C) (radd B s C t)) h) } }
        { assume yp hypB hupe;
          rewrite hupe;
          rewrite (sum_assoc_lam_lr A B C yp hypB);
          apply ∧ᵢ
          { assume h;
            have hinner : π (Pair (Inr y) (Inr yp) ∈ radd A r B s)
              { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff (Inr y) (Inr yp)
                  (sum A B) (radd A r B s) C t) h)) };
            have hs1 : π (Pair y yp ∈ s)
              { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff y yp A r B s) hinner)) };
            refine ∧ₑ₂ (radd_Inr_iff (Inl y) (Inl yp) A r (sum B C) (radd B s C t))
              (∧ᵢ (InlI y B C hyB) (∧ᵢ (InlI yp B C hypB)
                (∧ₑ₂ (radd_Inl_iff y yp B s C t) (∧ᵢ hyB (∧ᵢ hypB hs1))))) }
          { assume h;
            have hinner : π (Pair (Inl y) (Inl yp) ∈ radd B s C t)
              { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff (Inl y) (Inl yp) A r
                  (sum B C) (radd B s C t)) h)) };
            have hs1 : π (Pair y yp ∈ s)
              { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff y yp B s C t) hinner)) };
            refine ∧ₑ₂ (radd_Inl_iff (Inr y) (Inr yp) (sum A B) (radd A r B s) C t)
              (∧ᵢ (InrI y A B hyB) (∧ᵢ (InrI yp A B hypB)
                (∧ₑ₂ (radd_Inr_iff y yp A r B s) (∧ᵢ hyB (∧ᵢ hypB hs1))))) } } }
      { assume vp hvpC hwe;
        rewrite hwe;
        rewrite (sum_assoc_lam_r A B C vp hvpC);
        apply ∧ᵢ
        { assume h;
          refine ∧ₑ₂ (radd_Inr_iff (Inl y) (Inr vp) A r (sum B C) (radd B s C t))
            (∧ᵢ (InlI y B C hyB) (∧ᵢ (InrI vp B C hvpC)
              (∧ₑ₂ (radd_Inl_Inr_iff y vp B s C t) (∧ᵢ hyB hvpC)))) }
        { assume h;
          refine ∧ₑ₂ (radd_Inl_Inr_iff (Inr y) vp (sum A B) (radd A r B s) C t)
            (∧ᵢ (InrI y A B hyB) hvpC) } } } }
  { // z = Inr v
    assume v hvC hze;
    rewrite hze;
    rewrite (sum_assoc_lam_r A B C v hvC);
    refine sumE w (sum A B) C _ hw _ _
    { assume up hupAB hwe;
      rewrite hwe;
      refine sumE up A B _ hupAB _ _
      { assume xp hxpA hupe;
        rewrite hupe;
        rewrite (sum_assoc_lam_ll A B C xp hxpA);
        apply ∧ᵢ
        { assume h;
          refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff v (Inl xp)
            (sum A B) (radd A r B s) C t) h) }
        { assume h;
          refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff (Inr v) xp A r
            (sum B C) (radd B s C t)) h) } }
      { assume yp hypB hupe;
        rewrite hupe;
        rewrite (sum_assoc_lam_lr A B C yp hypB);
        apply ∧ᵢ
        { assume h;
          refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff v (Inr yp)
            (sum A B) (radd A r B s) C t) h) }
        { assume h;
          have hinner : π (Pair (Inr v) (Inl yp) ∈ radd B s C t)
            { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff (Inr v) (Inl yp) A r
                (sum B C) (radd B s C t)) h)) };
          refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff v yp B s C t) hinner) } } }
    { assume vp hvpC hwe;
      rewrite hwe;
      rewrite (sum_assoc_lam_r A B C vp hvpC);
      apply ∧ᵢ
      { assume h;
        have ht1 : π (Pair v vp ∈ t)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff v vp
              (sum A B) (radd A r B s) C t) h)) };
        refine ∧ₑ₂ (radd_Inr_iff (Inr v) (Inr vp) A r (sum B C) (radd B s C t))
          (∧ᵢ (InrI v B C hvC) (∧ᵢ (InrI vp B C hvpC)
            (∧ₑ₂ (radd_Inr_iff v vp B s C t) (∧ᵢ hvC (∧ᵢ hvpC ht1))))) }
      { assume h;
        have hinner : π (Pair (Inr v) (Inr vp) ∈ radd B s C t)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff (Inr v) (Inr vp) A r
              (sum B C) (radd B s C t)) h)) };
        have ht1 : π (Pair v vp ∈ t)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff v vp B s C t) hinner)) };
        refine ∧ₑ₂ (radd_Inr_iff v vp (sum A B) (radd A r B s) C t)
          (∧ᵢ hvC (∧ᵢ hvpC ht1)) } } }
end;

// ===========================================================================
// Multiplication of Relations -- Lexicographic Product
// ===========================================================================

// rmult_iff
opaque symbol rmult_iff (ap bp a b A r B s : τ ι) :
  π (Pair (Pair ap bp) (Pair a b) ∈ rmult A r B s ⇔
     ((Pair ap a ∈ r ∧ ap ∈ A ∧ a ∈ A ∧ bp ∈ B ∧ b ∈ B)
      ∨ (Pair bp b ∈ s ∧ ap = a ∧ a ∈ A ∧ bp ∈ B ∧ b ∈ B))) ≔
begin
  assume ap bp a b A r B s;
  apply ∧ᵢ
  { // →
    assume h;
    have hWS : π (Pair (Pair ap bp) (Pair a b)
                  ∈ Sigma (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B)))
      { refine CollectD1 (Pair (Pair ap bp) (Pair a b))
          (Sigma (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B)))
          (λ z, `∃ (xp : τ ι), `∃ (yp : τ ι), `∃ (x : τ ι), `∃ (y : τ ι),
             z = Pair (Pair xp yp) (Pair x y)
             ∧ (Pair xp x ∈ r ∨ (xp = x ∧ Pair yp y ∈ s))) h };
    have hL : π (Pair ap bp ∈ Sigma A (λ _, B))
      { refine ind_eq (eq_sym (fst_conv (Pair ap bp) (Pair a b)))
          (λ w, w ∈ Sigma A (λ _, B))
          (SigmaD1 (Pair (Pair ap bp) (Pair a b)) (Sigma A (λ _, B))
             (λ _, Sigma A (λ _, B)) hWS) };
    have hR : π (Pair a b ∈ Sigma A (λ _, B))
      { refine ind_eq (eq_sym (snd_conv (Pair ap bp) (Pair a b)))
          (λ w, w ∈ Sigma A (λ _, B))
          (SigmaD2 (Pair (Pair ap bp) (Pair a b)) (Sigma A (λ _, B))
             (λ _, Sigma A (λ _, B)) hWS) };
    have hapA : π (ap ∈ A)
      { refine ind_eq (eq_sym (fst_conv ap bp)) (λ w, w ∈ A)
          (SigmaD1 (Pair ap bp) A (λ _, B) hL) };
    have hbpB : π (bp ∈ B)
      { refine ind_eq (eq_sym (snd_conv ap bp)) (λ w, w ∈ B)
          (SigmaD2 (Pair ap bp) A (λ _, B) hL) };
    have haA : π (a ∈ A)
      { refine ind_eq (eq_sym (fst_conv a b)) (λ w, w ∈ A)
          (SigmaD1 (Pair a b) A (λ _, B) hR) };
    have hbB : π (b ∈ B)
      { refine ind_eq (eq_sym (snd_conv a b)) (λ w, w ∈ B)
          (SigmaD2 (Pair a b) A (λ _, B) hR) };
    have hpred : π (`∃ (xp : τ ι), `∃ (yp : τ ι), `∃ (x : τ ι), `∃ (y : τ ι),
                    Pair (Pair ap bp) (Pair a b) = Pair (Pair xp yp) (Pair x y)
                    ∧ (Pair xp x ∈ r ∨ (xp = x ∧ Pair yp y ∈ s)))
      { refine CollectD2 (Pair (Pair ap bp) (Pair a b))
          (Sigma (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B)))
          (λ z, `∃ (xp : τ ι), `∃ (yp : τ ι), `∃ (x : τ ι), `∃ (y : τ ι),
             z = Pair (Pair xp yp) (Pair x y)
             ∧ (Pair xp x ∈ r ∨ (xp = x ∧ Pair yp y ∈ s))) h };
    refine ∃ₑ hpred _; assume xp hxp;
    refine ∃ₑ hxp _; assume yp hyp;
    refine ∃ₑ hyp _; assume x hx;
    refine ∃ₑ hx _; assume y hy;
    have heq : π (Pair (Pair ap bp) (Pair a b) = Pair (Pair xp yp) (Pair x y))
      { refine ∧ₑ₁ hy };
    have hdisj : π (Pair xp x ∈ r ∨ (xp = x ∧ Pair yp y ∈ s)) { refine ∧ₑ₂ hy };
    have heqL : π (Pair ap bp = Pair xp yp)
      { refine Pair_inject1 (Pair ap bp) (Pair a b) (Pair xp yp) (Pair x y) heq };
    have heqR : π (Pair a b = Pair x y)
      { refine Pair_inject2 (Pair ap bp) (Pair a b) (Pair xp yp) (Pair x y) heq };
    have hapxp : π (ap = xp) { refine Pair_inject1 ap bp xp yp heqL };
    have hbpyp : π (bp = yp) { refine Pair_inject2 ap bp xp yp heqL };
    have hax : π (a = x) { refine Pair_inject1 a b x y heqR };
    have hby : π (b = y) { refine Pair_inject2 a b x y heqR };
    refine ∨ₑ hdisj _ _
    { assume h1;
      have hr1 : π (Pair ap a ∈ r)
        { rewrite hapxp; rewrite hax; refine h1 };
      refine ∨ᵢ₁ (∧ᵢ hr1 (∧ᵢ hapA (∧ᵢ haA (∧ᵢ hbpB hbB)))) }
    { assume h2;
      have hxx : π (xp = x) { refine ∧ₑ₁ h2 };
      have hs1 : π (Pair bp b ∈ s)
        { rewrite hbpyp; rewrite hby; refine ∧ₑ₂ h2 };
      have hapa : π (ap = a)
        { rewrite hapxp; rewrite hxx; refine eq_sym hax };
      refine ∨ᵢ₂ (∧ᵢ hs1 (∧ᵢ hapa (∧ᵢ haA (∧ᵢ hbpB hbB)))) } }
  { // ←
    assume h;
    refine ∨ₑ h _ _
    { assume hl;
      have hr1 : π (Pair ap a ∈ r) { refine ∧ₑ₁ hl };
      have hapA : π (ap ∈ A) { refine ∧ₑ₁ (∧ₑ₂ hl) };
      have haA : π (a ∈ A) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hl)) };
      have hbpB : π (bp ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hl))) };
      have hbB : π (b ∈ B) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hl))) };
      refine CollectI (Pair (Pair ap bp) (Pair a b))
        (Sigma (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B)))
        (λ z, `∃ (xp : τ ι), `∃ (yp : τ ι), `∃ (x : τ ι), `∃ (y : τ ι),
           z = Pair (Pair xp yp) (Pair x y)
           ∧ (Pair xp x ∈ r ∨ (xp = x ∧ Pair yp y ∈ s))) _ _
      { refine SigmaI (Pair ap bp) (Pair a b) (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B))
          (SigmaI ap bp A (λ _, B) hapA hbpB) (SigmaI a b A (λ _, B) haA hbB) }
      { refine ∃ᵢ ap (∃ᵢ bp (∃ᵢ a (∃ᵢ b
          (∧ᵢ (eq_refl (Pair (Pair ap bp) (Pair a b))) (∨ᵢ₁ hr1))))) } }
    { assume hrr;
      have hs1 : π (Pair bp b ∈ s) { refine ∧ₑ₁ hrr };
      have hapa : π (ap = a) { refine ∧ₑ₁ (∧ₑ₂ hrr) };
      have haA : π (a ∈ A) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hrr)) };
      have hbpB : π (bp ∈ B) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hrr))) };
      have hbB : π (b ∈ B) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hrr))) };
      have hapA : π (ap ∈ A) { rewrite hapa; refine haA };
      refine CollectI (Pair (Pair ap bp) (Pair a b))
        (Sigma (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B)))
        (λ z, `∃ (xp : τ ι), `∃ (yp : τ ι), `∃ (x : τ ι), `∃ (y : τ ι),
           z = Pair (Pair xp yp) (Pair x y)
           ∧ (Pair xp x ∈ r ∨ (xp = x ∧ Pair yp y ∈ s))) _ _
      { refine SigmaI (Pair ap bp) (Pair a b) (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B))
          (SigmaI ap bp A (λ _, B) hapA hbpB) (SigmaI a b A (λ _, B) haA hbB) }
      { refine ∃ᵢ ap (∃ᵢ bp (∃ᵢ a (∃ᵢ b
          (∧ᵢ (eq_refl (Pair (Pair ap bp) (Pair a b))) (∨ᵢ₂ (∧ᵢ hapa hs1)))))) } } }
end;

// rmultE
opaque symbol rmultE (ap bp a b A r B s : τ ι) (Q : Prop) :
  π (Pair (Pair ap bp) (Pair a b) ∈ rmult A r B s) →
  (π (Pair ap a ∈ r) → π (ap ∈ A) → π (a ∈ A) → π (bp ∈ B) → π (b ∈ B) → π Q) →
  (π (Pair bp b ∈ s) → π (a ∈ A) → π (ap = a) → π (bp ∈ B) → π (b ∈ B) → π Q) →
  π Q ≔
begin
  assume ap bp a b A r B s Q hmem f1 f2;
  have hdisj : π ((Pair ap a ∈ r ∧ ap ∈ A ∧ a ∈ A ∧ bp ∈ B ∧ b ∈ B)
                  ∨ (Pair bp b ∈ s ∧ ap = a ∧ a ∈ A ∧ bp ∈ B ∧ b ∈ B))
    { refine ∧ₑ₁ (rmult_iff ap bp a b A r B s) hmem };
  refine ∨ₑ hdisj _ _
  { assume hl;
    refine f1 (∧ₑ₁ hl) (∧ₑ₁ (∧ₑ₂ hl)) (∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hl)))
             (∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hl)))) (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hl)))) }
  { assume hr;
    refine f2 (∧ₑ₁ hr) (∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hr))) (∧ₑ₁ (∧ₑ₂ hr))
             (∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hr)))) (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hr)))) }
end;

// rmult_type: rmult(A,r,B,s) ⊆ (A*B)*(A*B)
opaque symbol rmult_type (A r B s : τ ι) :
  π (rmult A r B s ⊆ Sigma (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B))) ≔
begin
  assume A r B s;
  refine Collect_subset (Sigma (Sigma A (λ _, B)) (λ _, Sigma A (λ _, B))) _
end;

// field_rmult
opaque symbol field_rmult (A r B s : τ ι) :
  π (field (rmult A r B s) ⊆ Sigma A (λ _, B)) ≔
begin
  assume A r B s;
  refine field_rel_subset (rmult A r B s) (Sigma A (λ _, B)) (rmult_type A r B s)
end;

// linear_rmult
opaque symbol linear_rmult (A r B s : τ ι) :
  π (linear A r) → π (linear B s) → π (linear (Sigma A (λ _, B)) (rmult A r B s)) ≔
begin
  assume A r B s hlinA hlinB p hp q hq;
  refine ∃ₑ (SigmaE p A (λ _, B) hp) _; assume px hpx;
  have hpxA : π (px ∈ A) { refine ∧ₑ₁ hpx };
  refine ∃ₑ (∧ₑ₂ hpx) _; assume py hpy;
  have hpyB : π (py ∈ B) { refine ∧ₑ₁ hpy };
  have hpe : π (p = Pair px py) { refine ∧ₑ₂ hpy };
  refine ∃ₑ (SigmaE q A (λ _, B) hq) _; assume qx hqx;
  have hqxA : π (qx ∈ A) { refine ∧ₑ₁ hqx };
  refine ∃ₑ (∧ₑ₂ hqx) _; assume qy hqy;
  have hqyB : π (qy ∈ B) { refine ∧ₑ₁ hqy };
  have hqe : π (q = Pair qx qy) { refine ∧ₑ₂ hqy };
  rewrite hpe; rewrite hqe;
  have hxcase : π (Pair px qx ∈ r ∨ (px = qx ∨ Pair qx px ∈ r))
    { refine hlinA px hpxA qx hqxA };
  refine ∨ₑ hxcase _ _
  { assume h1;
    refine ∨ᵢ₁ (∧ₑ₂ (rmult_iff px py qx qy A r B s)
      (∨ᵢ₁ (∧ᵢ h1 (∧ᵢ hpxA (∧ᵢ hqxA (∧ᵢ hpyB hqyB)))))) }
  { assume hx2;
    refine ∨ₑ hx2 _ _
    { assume hpxqx;
      have hycase : π (Pair py qy ∈ s ∨ (py = qy ∨ Pair qy py ∈ s))
        { refine hlinB py hpyB qy hqyB };
      refine ∨ₑ hycase _ _
      { assume hy1;
        refine ∨ᵢ₁ (∧ₑ₂ (rmult_iff px py qx qy A r B s)
          (∨ᵢ₂ (∧ᵢ hy1 (∧ᵢ hpxqx (∧ᵢ hqxA (∧ᵢ hpyB hqyB)))))) }
      { assume hy2;
        refine ∨ₑ hy2 _ _
        { assume hpyqy;
          refine ∨ᵢ₂ (∨ᵢ₁ _);
          rewrite hpxqx; rewrite hpyqy; reflexivity }
        { assume hy3;
          refine ∨ᵢ₂ (∨ᵢ₂ (∧ₑ₂ (rmult_iff qx qy px py A r B s)
            (∨ᵢ₂ (∧ᵢ hy3 (∧ᵢ (eq_sym hpxqx) (∧ᵢ hpxA (∧ᵢ hqyB hpyB))))))) } } }
    { assume h3;
      refine ∨ᵢ₂ (∨ᵢ₂ (∧ₑ₂ (rmult_iff qx qy px py A r B s)
        (∨ᵢ₁ (∧ᵢ h3 (∧ᵢ hqxA (∧ᵢ hpxA (∧ᵢ hqyB hpyB))))))) } }
end;

// wf_on_rmult
// Direct minimal-element proof: for nonempty Z ⊆ A*B take the r-minimal x0 of
// X = {x∈A. ∃y∈B. <x,y>∈Z}, then the s-minimal y0 of Y = {y∈B. <x0,y>∈Z};
// <x0,y0> is rmult-minimal in Z (a predecessor either drops the first
// component, contradicting x0's minimality, or keeps it and drops the second,
// contradicting y0's).
opaque symbol wf_on_rmult (A r B s : τ ι) :
  π (wf A r) → π (wf B s) → π (wf (Sigma A (λ _, B)) (rmult A r B s)) ≔
begin
  assume A r B s hwfA hwfB Z hZsub hZne;
  have hXsub : π (Collect A (λ x, Bex B (λ y, Pair x y ∈ Z)) ⊆ A)
    { assume w hw; refine CollectD1 w A (λ x, Bex B (λ y, Pair x y ∈ Z)) hw };
  have hXne : π (Collect A (λ x, Bex B (λ y, Pair x y ∈ Z)) ≠ empty)
    { assume heq;
      refine not_emptyE Z _ hZne _;
      assume z0 hz0;
      refine ∃ₑ (SigmaE z0 A (λ _, B) (hZsub z0 hz0)) _; assume u hu;
      refine ∃ₑ (∧ₑ₂ hu) _; assume v hv;
      have hz0e : π (z0 = Pair u v) { refine ∧ₑ₂ hv };
      have hPZ : π (Pair u v ∈ Z)
        { refine ind_eq (eq_sym hz0e) (λ w, w ∈ Z) hz0 };
      refine equals0D (Collect A (λ x, Bex B (λ y, Pair x y ∈ Z))) u heq
        (CollectI u A (λ x, Bex B (λ y, Pair x y ∈ Z)) (∧ₑ₁ hu)
          (∃ᵢ v (∧ᵢ (∧ₑ₁ hv) hPZ))) };
  have hminX : π (Bex (Collect A (λ x, Bex B (λ y, Pair x y ∈ Z)))
                   (λ x, Ball (Collect A (λ x2, Bex B (λ y, Pair x2 y ∈ Z)))
                           (λ x2, Pair x2 x ∉ r)))
    { refine hwfA (Collect A (λ x, Bex B (λ y, Pair x y ∈ Z))) hXsub hXne };
  refine ∃ₑ hminX _; assume x0 hx0;
  have hx0A : π (x0 ∈ A)
    { refine CollectD1 x0 A (λ x, Bex B (λ y, Pair x y ∈ Z)) (∧ₑ₁ hx0) };
  have hx0ex : π (Bex B (λ y, Pair x0 y ∈ Z))
    { refine CollectD2 x0 A (λ x, Bex B (λ y, Pair x y ∈ Z)) (∧ₑ₁ hx0) };
  have hx0min : π (Ball (Collect A (λ x2, Bex B (λ y, Pair x2 y ∈ Z)))
                    (λ x2, Pair x2 x0 ∉ r))
    { refine ∧ₑ₂ hx0 };
  have hYsub : π (Collect B (λ y, Pair x0 y ∈ Z) ⊆ B)
    { assume w hw; refine CollectD1 w B (λ y, Pair x0 y ∈ Z) hw };
  have hYne : π (Collect B (λ y, Pair x0 y ∈ Z) ≠ empty)
    { assume heq;
      refine ∃ₑ hx0ex _; assume v hv;
      refine equals0D (Collect B (λ y, Pair x0 y ∈ Z)) v heq
        (CollectI v B (λ y, Pair x0 y ∈ Z) (∧ₑ₁ hv) (∧ₑ₂ hv)) };
  have hminY : π (Bex (Collect B (λ y, Pair x0 y ∈ Z))
                   (λ y, Ball (Collect B (λ y2, Pair x0 y2 ∈ Z)) (λ y2, Pair y2 y ∉ s)))
    { refine hwfB (Collect B (λ y, Pair x0 y ∈ Z)) hYsub hYne };
  refine ∃ₑ hminY _; assume y0 hy0;
  have hy0B : π (y0 ∈ B) { refine CollectD1 y0 B (λ y, Pair x0 y ∈ Z) (∧ₑ₁ hy0) };
  have hy0Z : π (Pair x0 y0 ∈ Z) { refine CollectD2 y0 B (λ y, Pair x0 y ∈ Z) (∧ₑ₁ hy0) };
  have hy0min : π (Ball (Collect B (λ y2, Pair x0 y2 ∈ Z)) (λ y2, Pair y2 y0 ∉ s))
    { refine ∧ₑ₂ hy0 };
  refine ∃ᵢ (Pair x0 y0) (∧ᵢ hy0Z _);
  assume w hwZ hmem;
  refine ∃ₑ (SigmaE w A (λ _, B) (hZsub w hwZ)) _; assume u hu;
  refine ∃ₑ (∧ₑ₂ hu) _; assume v hv;
  have hwe : π (w = Pair u v) { refine ∧ₑ₂ hv };
  have huA : π (u ∈ A) { refine ∧ₑ₁ hu };
  have hvB : π (v ∈ B) { refine ∧ₑ₁ hv };
  have hPuvZ : π (Pair u v ∈ Z) { refine ind_eq (eq_sym hwe) (λ t, t ∈ Z) hwZ };
  have hmem2 : π (Pair (Pair u v) (Pair x0 y0) ∈ rmult A r B s)
    { refine ind_eq (eq_sym hwe) (λ t, Pair t (Pair x0 y0) ∈ rmult A r B s) hmem };
  refine rmultE u v x0 y0 A r B s ⊥ hmem2 _ _
  { assume hur hu2 hx02 hv2 hy02;
    refine hx0min u (CollectI u A (λ x, Bex B (λ y, Pair x y ∈ Z)) huA
      (∃ᵢ v (∧ᵢ hvB hPuvZ))) hur }
  { assume hvs hx02 hux0 hv2 hy02;
    have hPx0vZ : π (Pair x0 v ∈ Z)
      { refine ind_eq (eq_sym hux0) (λ t, Pair t v ∈ Z) hPuvZ };
    refine hy0min v (CollectI v B (λ y, Pair x0 y ∈ Z) hvB hPx0vZ) hvs }
end;

// wf_rmult
opaque symbol wf_rmult (r s : τ ι) :
  π (wf_global r) → π (wf_global s) →
  π (wf_global (rmult (field r) r (field s) s)) ≔
begin
  assume r s hr hs;
  have hwfprod : π (wf (Sigma (field r) (λ _, field s)) (rmult (field r) r (field s) s))
    { refine wf_on_rmult (field r) r (field s) s
        (wf_imp_wf_on (field r) r hr) (wf_imp_wf_on (field s) s hs) };
  have hwffield : π (wf (field (rmult (field r) r (field s) s))
                       (rmult (field r) r (field s) s))
    { refine wf_subset (Sigma (field r) (λ _, field s))
        (field (rmult (field r) r (field s) s)) (rmult (field r) r (field s) s)
        hwfprod (field_rmult (field r) r (field s) s) };
  refine ∧ₑ₂ (wf_iff_wf_on_field (rmult (field r) r (field s) s)) hwffield
end;

// well_ord_rmult
opaque symbol well_ord_rmult (A r B s : τ ι) :
  π (well_ord A r) → π (well_ord B s) →
  π (well_ord (Sigma A (λ _, B)) (rmult A r B s)) ≔
begin
  assume A r B s hA hB;
  refine well_ordI (Sigma A (λ _, B)) (rmult A r B s)
    (wf_on_rmult A r B s (well_ord_is_wf A r hA) (well_ord_is_wf B s hB))
    (linear_rmult A r B s (well_ord_is_linear A r hA) (well_ord_is_linear B s hB))
end;

// --- ord_iso congruence law ---

// prod_bij
opaque symbol prod_bij (f g A B C D : τ ι) :
  π (f ∈ bij A C) → π (g ∈ bij B D) →
  π (Lambda (Sigma A (λ _, B)) (λ p, Pair (fapply f (fst p)) (fapply g (snd p)))
       ∈ bij (Sigma A (λ _, B)) (Sigma C (λ _, D))) ≔
begin
  assume f g A B C D hf hg;
  refine lam_bijective (Sigma A (λ _, B)) (Sigma C (λ _, D))
    (λ p, Pair (fapply f (fst p)) (fapply g (snd p)))
    (λ q, Pair (fapply (converse f) (fst q)) (fapply (converse g) (snd q)))
    _ _ _ _
  { // forward ∈ codomain
    assume p hp;
    refine SigmaI (fapply f (fst p)) (fapply g (snd p)) C (λ _, D)
      (apply_type f A C (fst p) (bij_is_fun f A C hf) (SigmaD1 p A (λ _, B) hp))
      (apply_type g B D (snd p) (bij_is_fun g B D hg) (SigmaD2 p A (λ _, B) hp)) }
  { // inverse ∈ domain
    assume q hq;
    refine SigmaI (fapply (converse f) (fst q)) (fapply (converse g) (snd q)) A (λ _, B)
      (converse_bij_apply_type f A C (fst q) hf (SigmaD1 q C (λ _, D) hq))
      (converse_bij_apply_type g B D (snd q) hg (SigmaD2 q C (λ _, D) hq)) }
  { // d (c p) = p
    assume p hp;
    rewrite (fst_conv (fapply f (fst p)) (fapply g (snd p)));
    rewrite (snd_conv (fapply f (fst p)) (fapply g (snd p)));
    rewrite (left_inverse_bij f A C (fst p) hf (SigmaD1 p A (λ _, B) hp));
    rewrite (left_inverse_bij g B D (snd p) hg (SigmaD2 p A (λ _, B) hp));
    refine Pair_fst_snd p A (λ _, B) hp }
  { // c (d q) = q
    assume q hq;
    rewrite (fst_conv (fapply (converse f) (fst q)) (fapply (converse g) (snd q)));
    rewrite (snd_conv (fapply (converse f) (fst q)) (fapply (converse g) (snd q)));
    rewrite (right_inverse_bij f A C (fst q) hf (SigmaD1 q C (λ _, D) hq));
    rewrite (right_inverse_bij g B D (snd q) hg (SigmaD2 q C (λ _, D) hq));
    refine Pair_fst_snd q C (λ _, D) hq }
end;

// Computation helper: the prod_bij Lambda applied to a pair, β-normal.
private opaque symbol prod_bij_lam_pair (f g A B x y : τ ι) :
  π (x ∈ A) → π (y ∈ B) →
  π (fapply (Lambda (Sigma A (λ _, B))
       (λ p, Pair (fapply f (fst p)) (fapply g (snd p)))) (Pair x y)
     = Pair (fapply f x) (fapply g y)) ≔
begin
  assume f g A B x y hxA hyB;
  have hb : π (fapply (Lambda (Sigma A (λ _, B))
       (λ p, Pair (fapply f (fst p)) (fapply g (snd p)))) (Pair x y)
     = Pair (fapply f (fst (Pair x y))) (fapply g (snd (Pair x y))))
    { refine beta (Sigma A (λ _, B))
        (λ p, Pair (fapply f (fst p)) (fapply g (snd p))) (Pair x y)
        (SigmaI x y A (λ _, B) hxA hyB) };
  rewrite hb;
  rewrite (fst_conv x y);
  rewrite (snd_conv x y);
  reflexivity
end;

// prod_ord_iso_cong
opaque symbol prod_ord_iso_cong (f g A r Ap rp B s Bp sp : τ ι) :
  π (f ∈ ord_iso A r Ap rp) → π (g ∈ ord_iso B s Bp sp) →
  π (Lambda (Sigma A (λ _, B)) (λ p, Pair (fapply f (fst p)) (fapply g (snd p)))
       ∈ ord_iso (Sigma A (λ _, B)) (rmult A r B s)
                 (Sigma Ap (λ _, Bp)) (rmult Ap rp Bp sp)) ≔
begin
  assume f g A r Ap rp B s Bp sp hf hg;
  have hbf : π (f ∈ bij A Ap) { refine ord_iso_is_bij f A r Ap rp hf };
  have hbg : π (g ∈ bij B Bp) { refine ord_iso_is_bij g B s Bp sp hg };
  have hcondf : π (Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ r) ⇔ (Pair (fapply f x) (fapply f y) ∈ rp))))
    { refine CollectD2 f (bij A Ap) (λ h, Ball A (λ x, Ball A (λ y,
        (Pair x y ∈ r) ⇔ (Pair (fapply h x) (fapply h y) ∈ rp)))) hf };
  have hcondg : π (Ball B (λ x, Ball B (λ y,
      (Pair x y ∈ s) ⇔ (Pair (fapply g x) (fapply g y) ∈ sp))))
    { refine CollectD2 g (bij B Bp) (λ h, Ball B (λ x, Ball B (λ y,
        (Pair x y ∈ s) ⇔ (Pair (fapply h x) (fapply h y) ∈ sp)))) hg };
  refine ord_isoI (Lambda (Sigma A (λ _, B))
      (λ p, Pair (fapply f (fst p)) (fapply g (snd p))))
    (Sigma A (λ _, B)) (rmult A r B s) (Sigma Ap (λ _, Bp)) (rmult Ap rp Bp sp)
    (prod_bij f g A B Ap Bp hbf hbg) _;
  assume p hp q hq;
  refine ∃ₑ (SigmaE p A (λ _, B) hp) _; assume x hx;
  refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hyB : π (y ∈ B) { refine ∧ₑ₁ hy };
  have hpe : π (p = Pair x y) { refine ∧ₑ₂ hy };
  refine ∃ₑ (SigmaE q A (λ _, B) hq) _; assume u hu;
  refine ∃ₑ (∧ₑ₂ hu) _; assume v hv;
  have huA : π (u ∈ A) { refine ∧ₑ₁ hu };
  have hvB : π (v ∈ B) { refine ∧ₑ₁ hv };
  have hqe : π (q = Pair u v) { refine ∧ₑ₂ hv };
  rewrite hpe; rewrite hqe;
  rewrite (prod_bij_lam_pair f g A B x y hxA hyB);
  rewrite (prod_bij_lam_pair f g A B u v huA hvB);
  apply ∧ᵢ
  { assume h;
    have hcases : π ((Pair x u ∈ r ∧ x ∈ A ∧ u ∈ A ∧ y ∈ B ∧ v ∈ B)
                    ∨ (Pair y v ∈ s ∧ x = u ∧ u ∈ A ∧ y ∈ B ∧ v ∈ B))
      { refine ∧ₑ₁ (rmult_iff x y u v A r B s) h };
    refine ∨ₑ hcases _ _
    { assume h1;
      refine ∧ₑ₂ (rmult_iff (fapply f x) (fapply g y) (fapply f u) (fapply g v)
          Ap rp Bp sp)
        (∨ᵢ₁ (∧ᵢ (∧ₑ₁ (hcondf x hxA u huA) (∧ₑ₁ h1))
             (∧ᵢ (apply_type f A Ap x (bij_is_fun f A Ap hbf) hxA)
             (∧ᵢ (apply_type f A Ap u (bij_is_fun f A Ap hbf) huA)
             (∧ᵢ (apply_type g B Bp y (bij_is_fun g B Bp hbg) hyB)
                 (apply_type g B Bp v (bij_is_fun g B Bp hbg) hvB)))))) }
    { assume h2;
      have hxu : π (x = u) { refine ∧ₑ₁ (∧ₑ₂ h2) };
      have hfeq : π (fapply f x = fapply f u)
        { refine ind_eq hxu (λ w, fapply f w = fapply f u) (eq_refl (fapply f u)) };
      refine ∧ₑ₂ (rmult_iff (fapply f x) (fapply g y) (fapply f u) (fapply g v)
          Ap rp Bp sp)
        (∨ᵢ₂ (∧ᵢ (∧ₑ₁ (hcondg y hyB v hvB) (∧ₑ₁ h2))
             (∧ᵢ hfeq
             (∧ᵢ (apply_type f A Ap u (bij_is_fun f A Ap hbf) huA)
             (∧ᵢ (apply_type g B Bp y (bij_is_fun g B Bp hbg) hyB)
                 (apply_type g B Bp v (bij_is_fun g B Bp hbg) hvB)))))) } }
  { assume h;
    have hcases : π ((Pair (fapply f x) (fapply f u) ∈ rp
                      ∧ fapply f x ∈ Ap ∧ fapply f u ∈ Ap
                      ∧ fapply g y ∈ Bp ∧ fapply g v ∈ Bp)
                    ∨ (Pair (fapply g y) (fapply g v) ∈ sp
                      ∧ fapply f x = fapply f u ∧ fapply f u ∈ Ap
                      ∧ fapply g y ∈ Bp ∧ fapply g v ∈ Bp))
      { refine ∧ₑ₁ (rmult_iff (fapply f x) (fapply g y) (fapply f u) (fapply g v)
          Ap rp Bp sp) h };
    refine ∨ₑ hcases _ _
    { assume h1;
      refine ∧ₑ₂ (rmult_iff x y u v A r B s)
        (∨ᵢ₁ (∧ᵢ (∧ₑ₂ (hcondf x hxA u huA) (∧ₑ₁ h1))
             (∧ᵢ hxA (∧ᵢ huA (∧ᵢ hyB hvB))))) }
    { assume h2;
      have hfeq : π (fapply f x = fapply f u) { refine ∧ₑ₁ (∧ₑ₂ h2) };
      have hxu : π (x = u)
        { refine inj_apply_equality f A Ap x u (bij_is_inj f A Ap hbf) hfeq hxA huA };
      refine ∧ₑ₂ (rmult_iff x y u v A r B s)
        (∨ᵢ₂ (∧ᵢ (∧ₑ₂ (hcondg y hyB v hvB) (∧ₑ₁ h2))
             (∧ᵢ hxu (∧ᵢ huA (∧ᵢ hyB hvB))))) } }
end;

// singleton_prod_bij: (λz∈A. <x,z>) ∈ bij(A, {x}*A)
opaque symbol singleton_prod_bij (x A : τ ι) :
  π (Lambda A (λ z, Pair x z) ∈ bij A (Sigma (singleton x) (λ _, A))) ≔
begin
  assume x A;
  refine lam_bijective A (Sigma (singleton x) (λ _, A))
    (λ z, Pair x z) (λ w, snd w) _ _ _ _
  { assume z hz;
    refine SigmaI x z (singleton x) (λ _, A) (singletonI x) hz }
  { assume w hw;
    refine SigmaD2 w (singleton x) (λ _, A) hw }
  { assume z hz;
    refine snd_conv x z }
  { assume w hw;
    refine ∃ₑ (SigmaE w (singleton x) (λ _, A) hw) _; assume a ha;
    have haS : π (a ∈ singleton x) { refine ∧ₑ₁ ha };
    refine ∃ₑ (∧ₑ₂ ha) _; assume bb hbb;
    have hweq : π (w = Pair a bb) { refine ∧ₑ₂ hbb };
    have hax : π (a = x) { refine ∧ₑ₁ (singleton_iff a x) haS };
    rewrite hweq;
    rewrite (snd_conv a bb);
    rewrite hax;
    reflexivity }
end;

// singleton_prod_ord_iso
opaque symbol singleton_prod_ord_iso (x xr A r : τ ι) :
  π (well_ord (singleton x) xr) →
  π (Lambda A (λ z, Pair x z)
       ∈ ord_iso A r (Sigma (singleton x) (λ _, A)) (rmult (singleton x) xr A r)) ≔
begin
  assume x xr A r hwo;
  have hwf : π (wf (singleton x) xr) { refine well_ord_is_wf (singleton x) xr hwo };
  have hxs : π (x ∈ singleton x) { refine singletonI x };
  refine ord_isoI (Lambda A (λ z, Pair x z)) A r
    (Sigma (singleton x) (λ _, A)) (rmult (singleton x) xr A r)
    (singleton_prod_bij x A) _;
  assume a haA b hbA;
  // f`a = ⟨x,a⟩, f`b = ⟨x,b⟩.
  have hfa : π (fapply (Lambda A (λ z, Pair x z)) a = Pair x a)
    { refine beta A (λ z, Pair x z) a haA };
  have hfb : π (fapply (Lambda A (λ z, Pair x z)) b = Pair x b)
    { refine beta A (λ z, Pair x z) b hbA };
  rewrite hfa; rewrite hfb;
  apply ∧ᵢ
  { // ⟨a,b⟩∈r → the rmult second disjunct (with x=x, x∈{x}).
    assume hab;
    refine ∧ₑ₂ (rmult_iff x a x b (singleton x) xr A r)
      (∨ᵢ₂ (∧ᵢ hab (∧ᵢ (eq_refl x) (∧ᵢ hxs (∧ᵢ haA hbA))))) }
  { // membership → ⟨a,b⟩∈r; the first disjunct needs ⟨x,x⟩∈xr, impossible (wf_not_refl).
    assume hm;
    have hdisj : π ((Pair x x ∈ xr ∧ x ∈ singleton x ∧ x ∈ singleton x ∧ a ∈ A ∧ b ∈ A)
                    ∨ (Pair a b ∈ r ∧ x = x ∧ x ∈ singleton x ∧ a ∈ A ∧ b ∈ A))
      { refine ∧ₑ₁ (rmult_iff x a x b (singleton x) xr A r) hm };
    refine ∨ₑ hdisj _ _
    { assume h1; refine ⊥ₑ (wf_not_refl (singleton x) xr x hwf hxs (∧ₑ₁ h1)) }
    { assume h2; refine ∧ₑ₁ h2 } }
end;

// prod_sum_singleton_bij: a∉C → (λx∈C*B+D. case(λx.x, λy.<a,y>, x)) ∈ bij(C*B+D, C*B∪{a}*D)
opaque symbol prod_sum_singleton_bij (a B C D : τ ι) :
  π (a ∉ C) →
  π (Lambda (sum (Sigma C (λ _, B)) D) (λ x, case_sum (λ x, x) (λ y, Pair a y) x)
       ∈ bij (sum (Sigma C (λ _, B)) D)
             (Un (Sigma C (λ _, B)) (Sigma (singleton a) (λ _, D)))) ≔
// Direct lam_bijective with the classical inverse
//   d z = If (z ∈ C×B) (Inl z) (Inr (snd z)),
// well-defined because a ∉ C makes the union disjoint.
begin
  assume a B C D hnaC;
  refine lam_bijective (sum (Sigma C (λ _, B)) D)
    (Un (Sigma C (λ _, B)) (Sigma (singleton a) (λ _, D)))
    (λ x, case_sum (λ x2, x2) (λ y, Pair a y) x)
    (λ z, If (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)))
    _ _ _ _
  { // forward ∈ codomain
    assume x hx;
    refine sumE x (Sigma C (λ _, B)) D _ hx _ _
    { assume u hu he;
      rewrite he;
      have hcase : π (case_sum (λ x2, x2) (λ y, Pair a y) (Inl u) = u)
        { refine case_Inl (λ x2, x2) (λ y, Pair a y) u };
      rewrite hcase;
      refine UnI1 u (Sigma C (λ _, B)) (Sigma (singleton a) (λ _, D)) hu }
    { assume w hw he;
      rewrite he;
      have hcase : π (case_sum (λ x2, x2) (λ y, Pair a y) (Inr w) = Pair a w)
        { refine case_Inr (λ x2, x2) (λ y, Pair a y) w };
      rewrite hcase;
      refine UnI2 (Pair a w) (Sigma C (λ _, B)) (Sigma (singleton a) (λ _, D))
        (SigmaI a w (singleton a) (λ _, D) (singletonI a) hw) } }
  { // inverse ∈ domain
    assume z hz;
    refine ∨ₑ (UnE z (Sigma C (λ _, B)) (Sigma (singleton a) (λ _, D)) hz) _ _
    { assume hz1;
      have hd : π (If (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)) = Inl z)
        { refine If_P (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)) hz1 };
      rewrite hd;
      refine InlI z (Sigma C (λ _, B)) D hz1 }
    { assume hz2;
      have hfza : π (fst z = a)
        { refine ∧ₑ₁ (singleton_iff (fst z) a) (SigmaD1 z (singleton a) (λ _, D) hz2) };
      have hnot : π (¬ (z ∈ Sigma C (λ _, B)))
        { assume hzc;
          refine hnaC (ind_eq (eq_sym hfza) (λ w, w ∈ C) (SigmaD1 z C (λ _, B) hzc)) };
      have hd : π (If (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)) = Inr (snd z))
        { refine If_not_P (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)) hnot };
      rewrite hd;
      refine InrI (snd z) (Sigma C (λ _, B)) D (SigmaD2 z (singleton a) (λ _, D) hz2) } }
  { // inv ∘ fwd = id
    assume x hx;
    refine sumE x (Sigma C (λ _, B)) D _ hx _ _
    { assume u hu he;
      rewrite he;
      have hcase : π (case_sum (λ x2, x2) (λ y, Pair a y) (Inl u) = u)
        { refine case_Inl (λ x2, x2) (λ y, Pair a y) u };
      rewrite hcase;
      refine If_P (u ∈ Sigma C (λ _, B)) (Inl u) (Inr (snd u)) hu }
    { assume w hw he;
      rewrite he;
      have hcase : π (case_sum (λ x2, x2) (λ y, Pair a y) (Inr w) = Pair a w)
        { refine case_Inr (λ x2, x2) (λ y, Pair a y) w };
      rewrite hcase;
      have hnot : π (¬ (Pair a w ∈ Sigma C (λ _, B)))
        { assume hin;
          refine hnaC (ind_eq (eq_sym (fst_conv a w)) (λ v, v ∈ C)
            (SigmaD1 (Pair a w) C (λ _, B) hin)) };
      have hd : π (If (Pair a w ∈ Sigma C (λ _, B)) (Inl (Pair a w)) (Inr (snd (Pair a w)))
                   = Inr (snd (Pair a w)))
        { refine If_not_P (Pair a w ∈ Sigma C (λ _, B)) (Inl (Pair a w)) (Inr (snd (Pair a w))) hnot };
      rewrite hd;
      rewrite (snd_conv a w);
      reflexivity } }
  { // fwd ∘ inv = id
    assume z hz;
    refine ∨ₑ (UnE z (Sigma C (λ _, B)) (Sigma (singleton a) (λ _, D)) hz) _ _
    { assume hz1;
      have hd : π (If (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)) = Inl z)
        { refine If_P (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)) hz1 };
      rewrite hd;
      have hcase : π (case_sum (λ x2, x2) (λ y, Pair a y) (Inl z) = z)
        { refine case_Inl (λ x2, x2) (λ y, Pair a y) z };
      refine hcase }
    { assume hz2;
      have hfza : π (fst z = a)
        { refine ∧ₑ₁ (singleton_iff (fst z) a) (SigmaD1 z (singleton a) (λ _, D) hz2) };
      have hnot : π (¬ (z ∈ Sigma C (λ _, B)))
        { assume hzc;
          refine hnaC (ind_eq (eq_sym hfza) (λ w, w ∈ C) (SigmaD1 z C (λ _, B) hzc)) };
      have hd : π (If (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)) = Inr (snd z))
        { refine If_not_P (z ∈ Sigma C (λ _, B)) (Inl z) (Inr (snd z)) hnot };
      rewrite hd;
      have hcase : π (case_sum (λ x2, x2) (λ y, Pair a y) (Inr (snd z)) = Pair a (snd z))
        { refine case_Inr (λ x2, x2) (λ y, Pair a y) (snd z) };
      rewrite hcase;
      rewrite (eq_sym hfza);
      refine Pair_fst_snd z (singleton a) (λ _, D) hz2 } }
end;

// Beta-computation helpers for the prod_sum_singleton map.
private opaque symbol prod_sum_singleton_lam_Inl (a S Q u : τ ι) :
  π (u ∈ S) →
  π (fapply (Lambda (sum S Q) (λ x, case_sum (λ x2, x2) (λ y, Pair a y) x)) (Inl u) = u) ≔
begin
  assume a S Q u hu;
  have hm : π (Inl u ∈ sum S Q) { refine InlI u S Q hu };
  have hstep : π (case_sum (λ x2, x2) (λ y, Pair a y) (Inl u) = u)
    { refine case_Inl (λ x2, x2) (λ y, Pair a y) u };
  rewrite (beta (sum S Q) (λ x, case_sum (λ x2, x2) (λ y, Pair a y) x) (Inl u) hm);
  refine hstep
end;

private opaque symbol prod_sum_singleton_lam_Inr (a S Q w : τ ι) :
  π (w ∈ Q) →
  π (fapply (Lambda (sum S Q) (λ x, case_sum (λ x2, x2) (λ y, Pair a y) x)) (Inr w) = Pair a w) ≔
begin
  assume a S Q w hw;
  have hm : π (Inr w ∈ sum S Q) { refine InrI w S Q hw };
  have hstep : π (case_sum (λ x2, x2) (λ y, Pair a y) (Inr w) = Pair a w)
    { refine case_Inr (λ x2, x2) (λ y, Pair a y) w };
  rewrite (beta (sum S Q) (λ x, case_sum (λ x2, x2) (λ y, Pair a y) x) (Inr w) hm);
  refine hstep
end;

// prod_sum_singleton_ord_iso
opaque symbol prod_sum_singleton_ord_iso (a A r b B s : τ ι) :
  π (a ∈ A) → π (well_ord A r) →
  π (Lambda (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
            (λ x, case_sum (λ x, x) (λ y, Pair a y) x)
       ∈ ord_iso (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
                 (radd (Sigma A (λ _, B)) (rmult A r B s) B s)
                 (Un (Sigma (pred A a r) (λ _, B)) (Sigma (singleton a) (λ _, pred B b s)))
                 (rmult A r B s)) ≔
begin
  assume a A r b B s haA hwo;
  have hwf : π (wf A r) { refine well_ord_is_wf A r hwo };
  have hnaP : π (a ∉ pred A a r)
    { assume hin;
      refine wf_not_refl A r a hwf haA (∧ₑ₁ (∧ₑ₁ (pred_iff a A a r) hin)) };
  refine ord_isoI (Lambda (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
       (λ x, case_sum (λ x2, x2) (λ y, Pair a y) x))
    (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
    (radd (Sigma A (λ _, B)) (rmult A r B s) B s)
    (Un (Sigma (pred A a r) (λ _, B)) (Sigma (singleton a) (λ _, pred B b s)))
    (rmult A r B s)
    (prod_sum_singleton_bij a B (pred A a r) (pred B b s) hnaP) _;
  assume x1 hx1 x2 hx2;
  refine sumE x1 (Sigma (pred A a r) (λ _, B)) (pred B b s) _ hx1 _ _
  { assume u1 hu1 he1;
    rewrite he1;
    rewrite (prod_sum_singleton_lam_Inl a (Sigma (pred A a r) (λ _, B)) (pred B b s) u1 hu1);
    refine ∃ₑ (SigmaE u1 (pred A a r) (λ _, B) hu1) _; assume z1 hz1;
    refine ∃ₑ (∧ₑ₂ hz1) _; assume y1 hy1;
    rewrite (∧ₑ₂ hy1);
    have hz1r : π (Pair z1 a ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z1 A a r) (∧ₑ₁ hz1)) };
    have hz1A : π (z1 ∈ A) { refine ∧ₑ₂ (∧ₑ₁ (pred_iff z1 A a r) (∧ₑ₁ hz1)) };
    have hy1B : π (y1 ∈ B) { refine ∧ₑ₁ hy1 };
    have hab1 : π (Pair z1 y1 ∈ Sigma A (λ _, B)) { refine SigmaI z1 y1 A (λ _, B) hz1A hy1B };
    refine sumE x2 (Sigma (pred A a r) (λ _, B)) (pred B b s) _ hx2 _ _
    { // Inl / Inl
      assume u2 hu2 he2;
      rewrite he2;
      rewrite (prod_sum_singleton_lam_Inl a (Sigma (pred A a r) (λ _, B)) (pred B b s) u2 hu2);
      refine ∃ₑ (SigmaE u2 (pred A a r) (λ _, B) hu2) _; assume z2 hz2;
      refine ∃ₑ (∧ₑ₂ hz2) _; assume y2 hy2;
      rewrite (∧ₑ₂ hy2);
      have hz2A : π (z2 ∈ A) { refine ∧ₑ₂ (∧ₑ₁ (pred_iff z2 A a r) (∧ₑ₁ hz2)) };
      have hy2B : π (y2 ∈ B) { refine ∧ₑ₁ hy2 };
      have hab2 : π (Pair z2 y2 ∈ Sigma A (λ _, B)) { refine SigmaI z2 y2 A (λ _, B) hz2A hy2B };
      apply ∧ᵢ
      { assume h;
        refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff (Pair z1 y1) (Pair z2 y2)
          (Sigma A (λ _, B)) (rmult A r B s) B s) h)) }
      { assume h;
        refine ∧ₑ₂ (radd_Inl_iff (Pair z1 y1) (Pair z2 y2)
          (Sigma A (λ _, B)) (rmult A r B s) B s) (∧ᵢ hab1 (∧ᵢ hab2 h)) } }
    { // Inl / Inr — both sides always hold
      assume w2 hw2 he2;
      rewrite he2;
      rewrite (prod_sum_singleton_lam_Inr a (Sigma (pred A a r) (λ _, B)) (pred B b s) w2 hw2);
      have hw2B : π (w2 ∈ B) { refine ∧ₑ₂ (∧ₑ₁ (pred_iff w2 B b s) hw2) };
      apply ∧ᵢ
      { assume h;
        refine ∧ₑ₂ (rmult_iff z1 y1 a w2 A r B s)
          (∨ᵢ₁ (∧ᵢ hz1r (∧ᵢ hz1A (∧ᵢ haA (∧ᵢ hy1B hw2B))))) }
      { assume h;
        refine ∧ₑ₂ (radd_Inl_Inr_iff (Pair z1 y1) w2
          (Sigma A (λ _, B)) (rmult A r B s) B s) (∧ᵢ hab1 hw2B) } } }
  { assume w1 hw1 he1;
    rewrite he1;
    rewrite (prod_sum_singleton_lam_Inr a (Sigma (pred A a r) (λ _, B)) (pred B b s) w1 hw1);
    have hw1B : π (w1 ∈ B) { refine ∧ₑ₂ (∧ₑ₁ (pred_iff w1 B b s) hw1) };
    refine sumE x2 (Sigma (pred A a r) (λ _, B)) (pred B b s) _ hx2 _ _
    { // Inr / Inl — both sides always fail
      assume u2 hu2 he2;
      rewrite he2;
      rewrite (prod_sum_singleton_lam_Inl a (Sigma (pred A a r) (λ _, B)) (pred B b s) u2 hu2);
      refine ∃ₑ (SigmaE u2 (pred A a r) (λ _, B) hu2) _; assume z2 hz2;
      refine ∃ₑ (∧ₑ₂ hz2) _; assume y2 hy2;
      rewrite (∧ₑ₂ hy2);
      have hz2r : π (Pair z2 a ∈ r) { refine ∧ₑ₁ (∧ₑ₁ (pred_iff z2 A a r) (∧ₑ₁ hz2)) };
      have hz2A : π (z2 ∈ A) { refine ∧ₑ₂ (∧ₑ₁ (pred_iff z2 A a r) (∧ₑ₁ hz2)) };
      apply ∧ᵢ
      { assume h;
        refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff w1 (Pair z2 y2)
          (Sigma A (λ _, B)) (rmult A r B s) B s) h) }
      { assume h;
        refine ∨ₑ (∧ₑ₁ (rmult_iff a w1 z2 y2 A r B s) h) _ _
        { assume h1;
          refine ⊥ₑ (wf_asym A r z2 a hwf hz2A haA hz2r (∧ₑ₁ h1)) }
        { assume h2;
          have haar : π (Pair a a ∈ r)
            { refine ind_eq (∧ₑ₁ (∧ₑ₂ h2)) (λ w, Pair w a ∈ r) hz2r };
          refine ⊥ₑ (wf_not_refl A r a hwf haA haar) } } }
    { // Inr / Inr
      assume w2 hw2 he2;
      rewrite he2;
      rewrite (prod_sum_singleton_lam_Inr a (Sigma (pred A a r) (λ _, B)) (pred B b s) w2 hw2);
      have hw2B : π (w2 ∈ B) { refine ∧ₑ₂ (∧ₑ₁ (pred_iff w2 B b s) hw2) };
      apply ∧ᵢ
      { assume h;
        have hs12 : π (Pair w1 w2 ∈ s)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff w1 w2
              (Sigma A (λ _, B)) (rmult A r B s) B s) h)) };
        refine ∧ₑ₂ (rmult_iff a w1 a w2 A r B s)
          (∨ᵢ₂ (∧ᵢ hs12 (∧ᵢ (eq_refl a) (∧ᵢ haA (∧ᵢ hw1B hw2B))))) }
      { assume h;
        refine ∨ₑ (∧ₑ₁ (rmult_iff a w1 a w2 A r B s) h) _ _
        { assume h1;
          refine ⊥ₑ (wf_not_refl A r a hwf haA (∧ₑ₁ h1)) }
        { assume h2;
          refine ∧ₑ₂ (radd_Inr_iff w1 w2 (Sigma A (λ _, B)) (rmult A r B s) B s)
            (∧ᵢ hw1B (∧ᵢ hw2B (∧ₑ₁ h2))) } } } }
end;

// --- Distributive law ---

// sum_prod_distrib_bij
opaque symbol sum_prod_distrib_bij (A B C : τ ι) :
  π (Lambda (Sigma (sum A B) (λ _, C))
       (λ p, case_sum (λ y, Inl (Pair y (snd p))) (λ y, Inr (Pair y (snd p))) (fst p))
       ∈ bij (Sigma (sum A B) (λ _, C))
             (sum (Sigma A (λ _, C)) (Sigma B (λ _, C)))) ≔
begin
  assume A B C;
  refine lam_bijective (Sigma (sum A B) (λ _, C)) (sum (Sigma A (λ _, C)) (Sigma B (λ _, C)))
    (λ p, case_sum (λ y, Inl (Pair y (snd p))) (λ y, Inr (Pair y (snd p))) (fst p))
    (λ q, case_sum (λ u, Pair (Inl (fst u)) (snd u)) (λ u, Pair (Inr (fst u)) (snd u)) q)
    _ _ _ _
  { // forward ∈ codomain
    assume p hp;
    have hu : π (fst p ∈ sum A B) { refine SigmaD1 p (sum A B) (λ _, C) hp };
    have hc : π (snd p ∈ C) { refine SigmaD2 p (sum A B) (λ _, C) hp };
    refine sumE (fst p) A B _ hu _ _
    { assume x hx he;
      rewrite he;
      rewrite (case_Inl (λ y, Inl (Pair y (snd p))) (λ y, Inr (Pair y (snd p))) x);
      refine InlI (Pair x (snd p)) (Sigma A (λ _, C)) (Sigma B (λ _, C))
        (SigmaI x (snd p) A (λ _, C) hx hc) }
    { assume y hy he;
      rewrite he;
      rewrite (case_Inr (λ y2, Inl (Pair y2 (snd p))) (λ y2, Inr (Pair y2 (snd p))) y);
      refine InrI (Pair y (snd p)) (Sigma A (λ _, C)) (Sigma B (λ _, C))
        (SigmaI y (snd p) B (λ _, C) hy hc) } }
  { // inverse ∈ domain
    assume q hq;
    refine sumE q (Sigma A (λ _, C)) (Sigma B (λ _, C)) _ hq _ _
    { assume u hu he;
      rewrite he;
      rewrite (case_Inl (λ u2, Pair (Inl (fst u2)) (snd u2)) (λ u2, Pair (Inr (fst u2)) (snd u2)) u);
      refine SigmaI (Inl (fst u)) (snd u) (sum A B) (λ _, C)
        (InlI (fst u) A B (SigmaD1 u A (λ _, C) hu)) (SigmaD2 u A (λ _, C) hu) }
    { assume u hu he;
      rewrite he;
      rewrite (case_Inr (λ u2, Pair (Inl (fst u2)) (snd u2)) (λ u2, Pair (Inr (fst u2)) (snd u2)) u);
      refine SigmaI (Inr (fst u)) (snd u) (sum A B) (λ _, C)
        (InrI (fst u) A B (SigmaD1 u B (λ _, C) hu)) (SigmaD2 u B (λ _, C) hu) } }
  { // inv ∘ fwd = id
    assume p hp;
    have hu : π (fst p ∈ sum A B) { refine SigmaD1 p (sum A B) (λ _, C) hp };
    refine sumE (fst p) A B _ hu _ _
    { assume x hx he;
      rewrite he;
      have hc1 : π (case_sum (λ y, Inl (Pair y (snd p))) (λ y, Inr (Pair y (snd p))) (Inl x)
                   = Inl (Pair x (snd p)))
        { refine case_Inl (λ y, Inl (Pair y (snd p))) (λ y, Inr (Pair y (snd p))) x };
      rewrite hc1;
      have hc2 : π (case_sum (λ u, Pair (Inl (fst u)) (snd u)) (λ u, Pair (Inr (fst u)) (snd u))
                      (Inl (Pair x (snd p)))
                   = Pair (Inl (fst (Pair x (snd p)))) (snd (Pair x (snd p))))
        { refine case_Inl (λ u, Pair (Inl (fst u)) (snd u)) (λ u, Pair (Inr (fst u)) (snd u))
            (Pair x (snd p)) };
      rewrite hc2;
      rewrite (fst_conv x (snd p));
      rewrite (snd_conv x (snd p));
      rewrite (eq_sym he);
      refine Pair_fst_snd p (sum A B) (λ _, C) hp }
    { assume y hy he;
      rewrite he;
      have hc1 : π (case_sum (λ y2, Inl (Pair y2 (snd p))) (λ y2, Inr (Pair y2 (snd p))) (Inr y)
                   = Inr (Pair y (snd p)))
        { refine case_Inr (λ y2, Inl (Pair y2 (snd p))) (λ y2, Inr (Pair y2 (snd p))) y };
      rewrite hc1;
      have hc2 : π (case_sum (λ u, Pair (Inl (fst u)) (snd u)) (λ u, Pair (Inr (fst u)) (snd u))
                      (Inr (Pair y (snd p)))
                   = Pair (Inr (fst (Pair y (snd p)))) (snd (Pair y (snd p))))
        { refine case_Inr (λ u, Pair (Inl (fst u)) (snd u)) (λ u, Pair (Inr (fst u)) (snd u))
            (Pair y (snd p)) };
      rewrite hc2;
      rewrite (fst_conv y (snd p));
      rewrite (snd_conv y (snd p));
      rewrite (eq_sym he);
      refine Pair_fst_snd p (sum A B) (λ _, C) hp } }
  { // fwd ∘ inv = id
    assume q hq;
    refine sumE q (Sigma A (λ _, C)) (Sigma B (λ _, C)) _ hq _ _
    { assume u hu he;
      rewrite he;
      have hd : π (case_sum (λ u2, Pair (Inl (fst u2)) (snd u2)) (λ u2, Pair (Inr (fst u2)) (snd u2))
                     (Inl u) = Pair (Inl (fst u)) (snd u))
        { refine case_Inl (λ u2, Pair (Inl (fst u2)) (snd u2)) (λ u2, Pair (Inr (fst u2)) (snd u2)) u };
      rewrite hd;
      rewrite (fst_conv (Inl (fst u)) (snd u));
      rewrite (snd_conv (Inl (fst u)) (snd u));
      have hc : π (case_sum (λ y, Inl (Pair y (snd u))) (λ y, Inr (Pair y (snd u))) (Inl (fst u))
                   = Inl (Pair (fst u) (snd u)))
        { refine case_Inl (λ y, Inl (Pair y (snd u))) (λ y, Inr (Pair y (snd u))) (fst u) };
      rewrite hc;
      rewrite (Pair_fst_snd u A (λ _, C) hu);
      reflexivity }
    { assume u hu he;
      rewrite he;
      have hd : π (case_sum (λ u2, Pair (Inl (fst u2)) (snd u2)) (λ u2, Pair (Inr (fst u2)) (snd u2))
                     (Inr u) = Pair (Inr (fst u)) (snd u))
        { refine case_Inr (λ u2, Pair (Inl (fst u2)) (snd u2)) (λ u2, Pair (Inr (fst u2)) (snd u2)) u };
      rewrite hd;
      rewrite (fst_conv (Inr (fst u)) (snd u));
      rewrite (snd_conv (Inr (fst u)) (snd u));
      have hc : π (case_sum (λ y, Inl (Pair y (snd u))) (λ y, Inr (Pair y (snd u))) (Inr (fst u))
                   = Inr (Pair (fst u) (snd u)))
        { refine case_Inr (λ y, Inl (Pair y (snd u))) (λ y, Inr (Pair y (snd u))) (fst u) };
      rewrite hc;
      rewrite (Pair_fst_snd u B (λ _, C) hu);
      reflexivity } }
end;

// Beta-computation helpers for the distributive map.
private opaque symbol sum_prod_distrib_lam_Inl (A B C x c : τ ι) :
  π (x ∈ A) → π (c ∈ C) →
  π (fapply (Lambda (Sigma (sum A B) (λ _, C))
       (λ w, case_sum (λ y, Inl (Pair y (snd w))) (λ y, Inr (Pair y (snd w))) (fst w)))
     (Pair (Inl x) c) = Inl (Pair x c)) ≔
begin
  assume A B C x c hx hc;
  have hm : π (Pair (Inl x) c ∈ Sigma (sum A B) (λ _, C))
    { refine SigmaI (Inl x) c (sum A B) (λ _, C) (InlI x A B hx) hc };
  have hstep : π (case_sum (λ y, Inl (Pair y (snd (Pair (Inl x) c))))
                           (λ y, Inr (Pair y (snd (Pair (Inl x) c))))
                           (fst (Pair (Inl x) c)) = Inl (Pair x c))
    { rewrite (fst_conv (Inl x) c);
      rewrite (snd_conv (Inl x) c);
      refine case_Inl (λ y, Inl (Pair y c)) (λ y, Inr (Pair y c)) x };
  rewrite (beta (Sigma (sum A B) (λ _, C))
    (λ w, case_sum (λ y, Inl (Pair y (snd w))) (λ y, Inr (Pair y (snd w))) (fst w))
    (Pair (Inl x) c) hm);
  refine hstep
end;

private opaque symbol sum_prod_distrib_lam_Inr (A B C y c : τ ι) :
  π (y ∈ B) → π (c ∈ C) →
  π (fapply (Lambda (Sigma (sum A B) (λ _, C))
       (λ w, case_sum (λ y2, Inl (Pair y2 (snd w))) (λ y2, Inr (Pair y2 (snd w))) (fst w)))
     (Pair (Inr y) c) = Inr (Pair y c)) ≔
begin
  assume A B C y c hy hc;
  have hm : π (Pair (Inr y) c ∈ Sigma (sum A B) (λ _, C))
    { refine SigmaI (Inr y) c (sum A B) (λ _, C) (InrI y A B hy) hc };
  have hstep : π (case_sum (λ y2, Inl (Pair y2 (snd (Pair (Inr y) c))))
                           (λ y2, Inr (Pair y2 (snd (Pair (Inr y) c))))
                           (fst (Pair (Inr y) c)) = Inr (Pair y c))
    { rewrite (fst_conv (Inr y) c);
      rewrite (snd_conv (Inr y) c);
      refine case_Inr (λ y2, Inl (Pair y2 c)) (λ y2, Inr (Pair y2 c)) y };
  rewrite (beta (Sigma (sum A B) (λ _, C))
    (λ w, case_sum (λ y2, Inl (Pair y2 (snd w))) (λ y2, Inr (Pair y2 (snd w))) (fst w))
    (Pair (Inr y) c) hm);
  refine hstep
end;

// sum_prod_distrib_ord_iso
opaque symbol sum_prod_distrib_ord_iso (A r B s C t : τ ι) :
  π (Lambda (Sigma (sum A B) (λ _, C))
       (λ p, case_sum (λ y, Inl (Pair y (snd p))) (λ y, Inr (Pair y (snd p))) (fst p))
       ∈ ord_iso (Sigma (sum A B) (λ _, C)) (rmult (sum A B) (radd A r B s) C t)
                 (sum (Sigma A (λ _, C)) (Sigma B (λ _, C)))
                 (radd (Sigma A (λ _, C)) (rmult A r C t)
                       (Sigma B (λ _, C)) (rmult B s C t))) ≔
begin
  assume A r B s C t;
  refine ord_isoI (Lambda (Sigma (sum A B) (λ _, C))
       (λ w, case_sum (λ y, Inl (Pair y (snd w))) (λ y, Inr (Pair y (snd w))) (fst w)))
    (Sigma (sum A B) (λ _, C)) (rmult (sum A B) (radd A r B s) C t)
    (sum (Sigma A (λ _, C)) (Sigma B (λ _, C)))
    (radd (Sigma A (λ _, C)) (rmult A r C t) (Sigma B (λ _, C)) (rmult B s C t))
    (sum_prod_distrib_bij A B C) _;
  assume p hp q hq;
  refine ∃ₑ (SigmaE p (sum A B) (λ _, C) hp) _; assume u1 hu1;
  refine ∃ₑ (∧ₑ₂ hu1) _; assume c1 hc1;
  refine ∃ₑ (SigmaE q (sum A B) (λ _, C) hq) _; assume u2 hu2;
  refine ∃ₑ (∧ₑ₂ hu2) _; assume c2 hc2;
  have hc1C : π (c1 ∈ C) { refine ∧ₑ₁ hc1 };
  have hc2C : π (c2 ∈ C) { refine ∧ₑ₁ hc2 };
  rewrite (∧ₑ₂ hc1); rewrite (∧ₑ₂ hc2);
  refine sumE u1 A B _ (∧ₑ₁ hu1) _ _
  { assume x1 hx1 he1;
    rewrite he1;
    rewrite (sum_prod_distrib_lam_Inl A B C x1 c1 hx1 hc1C);
    have hxc1 : π (Pair x1 c1 ∈ Sigma A (λ _, C)) { refine SigmaI x1 c1 A (λ _, C) hx1 hc1C };
    refine sumE u2 A B _ (∧ₑ₁ hu2) _ _
    { // Inl / Inl
      assume x2 hx2 he2;
      rewrite he2;
      rewrite (sum_prod_distrib_lam_Inl A B C x2 c2 hx2 hc2C);
      have hxc2 : π (Pair x2 c2 ∈ Sigma A (λ _, C)) { refine SigmaI x2 c2 A (λ _, C) hx2 hc2C };
      apply ∧ᵢ
      { assume h;
        refine ∨ₑ (∧ₑ₁ (rmult_iff (Inl x1) c1 (Inl x2) c2 (sum A B) (radd A r B s) C t) h) _ _
        { assume h1;
          have hr : π (Pair x1 x2 ∈ r)
            { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff x1 x2 A r B s) (∧ₑ₁ h1))) };
          have hin : π (Pair (Pair x1 c1) (Pair x2 c2) ∈ rmult A r C t)
            { refine ∧ₑ₂ (rmult_iff x1 c1 x2 c2 A r C t)
                (∨ᵢ₁ (∧ᵢ hr (∧ᵢ hx1 (∧ᵢ hx2 (∧ᵢ hc1C hc2C))))) };
          refine ∧ₑ₂ (radd_Inl_iff (Pair x1 c1) (Pair x2 c2) (Sigma A (λ _, C)) (rmult A r C t)
                        (Sigma B (λ _, C)) (rmult B s C t))
            (∧ᵢ hxc1 (∧ᵢ hxc2 hin)) }
        { assume h2;
          have hxx : π (x1 = x2) { refine ∧ₑ₁ (Inl_iff x1 x2) (∧ₑ₁ (∧ₑ₂ h2)) };
          have hin : π (Pair (Pair x1 c1) (Pair x2 c2) ∈ rmult A r C t)
            { refine ∧ₑ₂ (rmult_iff x1 c1 x2 c2 A r C t)
                (∨ᵢ₂ (∧ᵢ (∧ₑ₁ h2) (∧ᵢ hxx (∧ᵢ hx2 (∧ᵢ hc1C hc2C))))) };
          refine ∧ₑ₂ (radd_Inl_iff (Pair x1 c1) (Pair x2 c2) (Sigma A (λ _, C)) (rmult A r C t)
                        (Sigma B (λ _, C)) (rmult B s C t))
            (∧ᵢ hxc1 (∧ᵢ hxc2 hin)) } }
      { assume h;
        have hin : π (Pair (Pair x1 c1) (Pair x2 c2) ∈ rmult A r C t)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inl_iff (Pair x1 c1) (Pair x2 c2)
              (Sigma A (λ _, C)) (rmult A r C t) (Sigma B (λ _, C)) (rmult B s C t)) h)) };
        refine ∨ₑ (∧ₑ₁ (rmult_iff x1 c1 x2 c2 A r C t) hin) _ _
        { assume h1;
          have hradd : π (Pair (Inl x1) (Inl x2) ∈ radd A r B s)
            { refine ∧ₑ₂ (radd_Inl_iff x1 x2 A r B s) (∧ᵢ hx1 (∧ᵢ hx2 (∧ₑ₁ h1))) };
          refine ∧ₑ₂ (rmult_iff (Inl x1) c1 (Inl x2) c2 (sum A B) (radd A r B s) C t)
            (∨ᵢ₁ (∧ᵢ hradd (∧ᵢ (InlI x1 A B hx1) (∧ᵢ (InlI x2 A B hx2) (∧ᵢ hc1C hc2C))))) }
        { assume h2;
          have heq : π (Inl x1 = Inl x2) { refine ∧ₑ₂ (Inl_iff x1 x2) (∧ₑ₁ (∧ₑ₂ h2)) };
          refine ∧ₑ₂ (rmult_iff (Inl x1) c1 (Inl x2) c2 (sum A B) (radd A r B s) C t)
            (∨ᵢ₂ (∧ᵢ (∧ₑ₁ h2) (∧ᵢ heq (∧ᵢ (InlI x2 A B hx2) (∧ᵢ hc1C hc2C))))) } } }
    { // Inl / Inr — both sides always hold
      assume y2 hy2 he2;
      rewrite he2;
      rewrite (sum_prod_distrib_lam_Inr A B C y2 c2 hy2 hc2C);
      have hyc2 : π (Pair y2 c2 ∈ Sigma B (λ _, C)) { refine SigmaI y2 c2 B (λ _, C) hy2 hc2C };
      apply ∧ᵢ
      { assume h;
        refine ∧ₑ₂ (radd_Inl_Inr_iff (Pair x1 c1) (Pair y2 c2) (Sigma A (λ _, C)) (rmult A r C t)
                      (Sigma B (λ _, C)) (rmult B s C t))
          (∧ᵢ hxc1 hyc2) }
      { assume h;
        have hradd : π (Pair (Inl x1) (Inr y2) ∈ radd A r B s)
          { refine ∧ₑ₂ (radd_Inl_Inr_iff x1 y2 A r B s) (∧ᵢ hx1 hy2) };
        refine ∧ₑ₂ (rmult_iff (Inl x1) c1 (Inr y2) c2 (sum A B) (radd A r B s) C t)
          (∨ᵢ₁ (∧ᵢ hradd (∧ᵢ (InlI x1 A B hx1) (∧ᵢ (InrI y2 A B hy2) (∧ᵢ hc1C hc2C))))) } } }
  { assume y1 hy1 he1;
    rewrite he1;
    rewrite (sum_prod_distrib_lam_Inr A B C y1 c1 hy1 hc1C);
    have hyc1 : π (Pair y1 c1 ∈ Sigma B (λ _, C)) { refine SigmaI y1 c1 B (λ _, C) hy1 hc1C };
    refine sumE u2 A B _ (∧ₑ₁ hu2) _ _
    { // Inr / Inl — both sides always fail
      assume x2 hx2 he2;
      rewrite he2;
      rewrite (sum_prod_distrib_lam_Inl A B C x2 c2 hx2 hc2C);
      apply ∧ᵢ
      { assume h;
        refine ∨ₑ (∧ₑ₁ (rmult_iff (Inr y1) c1 (Inl x2) c2 (sum A B) (radd A r B s) C t) h) _ _
        { assume h1;
          refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff y1 x2 A r B s) (∧ₑ₁ h1)) }
        { assume h2;
          refine ⊥ₑ (∧ₑ₁ (Inl_Inr_iff x2 y1) (eq_sym (∧ₑ₁ (∧ₑ₂ h2)))) } }
      { assume h;
        refine ⊥ₑ (∧ₑ₁ (radd_Inr_Inl_iff (Pair y1 c1) (Pair x2 c2) (Sigma A (λ _, C))
                          (rmult A r C t) (Sigma B (λ _, C)) (rmult B s C t)) h) } }
    { // Inr / Inr
      assume y2 hy2 he2;
      rewrite he2;
      rewrite (sum_prod_distrib_lam_Inr A B C y2 c2 hy2 hc2C);
      have hyc2 : π (Pair y2 c2 ∈ Sigma B (λ _, C)) { refine SigmaI y2 c2 B (λ _, C) hy2 hc2C };
      apply ∧ᵢ
      { assume h;
        refine ∨ₑ (∧ₑ₁ (rmult_iff (Inr y1) c1 (Inr y2) c2 (sum A B) (radd A r B s) C t) h) _ _
        { assume h1;
          have hs : π (Pair y1 y2 ∈ s)
            { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff y1 y2 A r B s) (∧ₑ₁ h1))) };
          have hin : π (Pair (Pair y1 c1) (Pair y2 c2) ∈ rmult B s C t)
            { refine ∧ₑ₂ (rmult_iff y1 c1 y2 c2 B s C t)
                (∨ᵢ₁ (∧ᵢ hs (∧ᵢ hy1 (∧ᵢ hy2 (∧ᵢ hc1C hc2C))))) };
          refine ∧ₑ₂ (radd_Inr_iff (Pair y1 c1) (Pair y2 c2) (Sigma A (λ _, C)) (rmult A r C t)
                        (Sigma B (λ _, C)) (rmult B s C t))
            (∧ᵢ hyc1 (∧ᵢ hyc2 hin)) }
        { assume h2;
          have hyy : π (y1 = y2) { refine ∧ₑ₁ (Inr_iff y1 y2) (∧ₑ₁ (∧ₑ₂ h2)) };
          have hin : π (Pair (Pair y1 c1) (Pair y2 c2) ∈ rmult B s C t)
            { refine ∧ₑ₂ (rmult_iff y1 c1 y2 c2 B s C t)
                (∨ᵢ₂ (∧ᵢ (∧ₑ₁ h2) (∧ᵢ hyy (∧ᵢ hy2 (∧ᵢ hc1C hc2C))))) };
          refine ∧ₑ₂ (radd_Inr_iff (Pair y1 c1) (Pair y2 c2) (Sigma A (λ _, C)) (rmult A r C t)
                        (Sigma B (λ _, C)) (rmult B s C t))
            (∧ᵢ hyc1 (∧ᵢ hyc2 hin)) } }
      { assume h;
        have hin : π (Pair (Pair y1 c1) (Pair y2 c2) ∈ rmult B s C t)
          { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (radd_Inr_iff (Pair y1 c1) (Pair y2 c2)
              (Sigma A (λ _, C)) (rmult A r C t) (Sigma B (λ _, C)) (rmult B s C t)) h)) };
        refine ∨ₑ (∧ₑ₁ (rmult_iff y1 c1 y2 c2 B s C t) hin) _ _
        { assume h1;
          have hradd : π (Pair (Inr y1) (Inr y2) ∈ radd A r B s)
            { refine ∧ₑ₂ (radd_Inr_iff y1 y2 A r B s) (∧ᵢ hy1 (∧ᵢ hy2 (∧ₑ₁ h1))) };
          refine ∧ₑ₂ (rmult_iff (Inr y1) c1 (Inr y2) c2 (sum A B) (radd A r B s) C t)
            (∨ᵢ₁ (∧ᵢ hradd (∧ᵢ (InrI y1 A B hy1) (∧ᵢ (InrI y2 A B hy2) (∧ᵢ hc1C hc2C))))) }
        { assume h2;
          have heq : π (Inr y1 = Inr y2) { refine ∧ₑ₂ (Inr_iff y1 y2) (∧ₑ₁ (∧ₑ₂ h2)) };
          refine ∧ₑ₂ (rmult_iff (Inr y1) c1 (Inr y2) c2 (sum A B) (radd A r B s) C t)
            (∨ᵢ₂ (∧ᵢ (∧ₑ₁ h2) (∧ᵢ heq (∧ᵢ (InrI y2 A B hy2) (∧ᵢ hc1C hc2C))))) } } } }
end;

// --- Associativity ---

// prod_assoc_bij
opaque symbol prod_assoc_bij (A B C : τ ι) :
  π (Lambda (Sigma (Sigma A (λ _, B)) (λ _, C))
       (λ p, Pair (fst (fst p)) (Pair (snd (fst p)) (snd p)))
       ∈ bij (Sigma (Sigma A (λ _, B)) (λ _, C)) (Sigma A (λ _, Sigma B (λ _, C)))) ≔
begin
  assume A B C;
  refine lam_bijective (Sigma (Sigma A (λ _, B)) (λ _, C)) (Sigma A (λ _, Sigma B (λ _, C)))
    (λ p, Pair (fst (fst p)) (Pair (snd (fst p)) (snd p)))
    (λ q, Pair (Pair (fst q) (fst (snd q))) (snd (snd q)))
    _ _ _ _
  { // forward ∈ codomain
    assume p hp;
    have hfstp : π (fst p ∈ Sigma A (λ _, B)) { refine SigmaD1 p (Sigma A (λ _, B)) (λ _, C) hp };
    have hsndp : π (snd p ∈ C) { refine SigmaD2 p (Sigma A (λ _, B)) (λ _, C) hp };
    have hffp : π (fst (fst p) ∈ A) { refine SigmaD1 (fst p) A (λ _, B) hfstp };
    have hsfp : π (snd (fst p) ∈ B) { refine SigmaD2 (fst p) A (λ _, B) hfstp };
    refine SigmaI (fst (fst p)) (Pair (snd (fst p)) (snd p)) A (λ _, Sigma B (λ _, C))
      hffp (SigmaI (snd (fst p)) (snd p) B (λ _, C) hsfp hsndp) }
  { // inverse ∈ domain
    assume q hq;
    have hfstq : π (fst q ∈ A) { refine SigmaD1 q A (λ _, Sigma B (λ _, C)) hq };
    have hsndq : π (snd q ∈ Sigma B (λ _, C)) { refine SigmaD2 q A (λ _, Sigma B (λ _, C)) hq };
    have hfsq : π (fst (snd q) ∈ B) { refine SigmaD1 (snd q) B (λ _, C) hsndq };
    have hssq : π (snd (snd q) ∈ C) { refine SigmaD2 (snd q) B (λ _, C) hsndq };
    refine SigmaI (Pair (fst q) (fst (snd q))) (snd (snd q)) (Sigma A (λ _, B)) (λ _, C)
      (SigmaI (fst q) (fst (snd q)) A (λ _, B) hfstq hfsq) hssq }
  { // inv ∘ fwd = id
    assume p hp;
    rewrite (fst_conv (fst (fst p)) (Pair (snd (fst p)) (snd p)));
    rewrite (snd_conv (fst (fst p)) (Pair (snd (fst p)) (snd p)));
    rewrite (fst_conv (snd (fst p)) (snd p));
    rewrite (snd_conv (snd (fst p)) (snd p));
    rewrite (Pair_fst_snd (fst p) A (λ _, B) (SigmaD1 p (Sigma A (λ _, B)) (λ _, C) hp));
    refine Pair_fst_snd p (Sigma A (λ _, B)) (λ _, C) hp }
  { // fwd ∘ inv = id
    assume q hq;
    rewrite (fst_conv (Pair (fst q) (fst (snd q))) (snd (snd q)));
    rewrite (snd_conv (Pair (fst q) (fst (snd q))) (snd (snd q)));
    rewrite (fst_conv (fst q) (fst (snd q)));
    rewrite (snd_conv (fst q) (fst (snd q)));
    rewrite (Pair_fst_snd (snd q) B (λ _, C) (SigmaD2 q A (λ _, Sigma B (λ _, C)) hq));
    refine Pair_fst_snd q A (λ _, Sigma B (λ _, C)) hq }
end;

// prod_assoc_ord_iso
opaque symbol prod_assoc_ord_iso (A r B s C t : τ ι) :
  π (Lambda (Sigma (Sigma A (λ _, B)) (λ _, C))
       (λ p, Pair (fst (fst p)) (Pair (snd (fst p)) (snd p)))
       ∈ ord_iso (Sigma (Sigma A (λ _, B)) (λ _, C)) (rmult (Sigma A (λ _, B)) (rmult A r B s) C t)
                 (Sigma A (λ _, Sigma B (λ _, C))) (rmult A r (Sigma B (λ _, C)) (rmult B s C t))) ≔
begin
  assume A r B s C t;
  refine ord_isoI (Lambda (Sigma (Sigma A (λ _, B)) (λ _, C))
       (λ w, Pair (fst (fst w)) (Pair (snd (fst w)) (snd w))))
    (Sigma (Sigma A (λ _, B)) (λ _, C)) (rmult (Sigma A (λ _, B)) (rmult A r B s) C t)
    (Sigma A (λ _, Sigma B (λ _, C))) (rmult A r (Sigma B (λ _, C)) (rmult B s C t))
    (prod_assoc_bij A B C) _;
  assume p hp q hq;
  refine ∃ₑ (SigmaE p (Sigma A (λ _, B)) (λ _, C) hp) _; assume u1 hu1;
  refine ∃ₑ (∧ₑ₂ hu1) _; assume c1 hc1;
  refine ∃ₑ (SigmaE u1 A (λ _, B) (∧ₑ₁ hu1)) _; assume a1 ha1;
  refine ∃ₑ (∧ₑ₂ ha1) _; assume b1 hb1;
  refine ∃ₑ (SigmaE q (Sigma A (λ _, B)) (λ _, C) hq) _; assume u2 hu2;
  refine ∃ₑ (∧ₑ₂ hu2) _; assume c2 hc2;
  refine ∃ₑ (SigmaE u2 A (λ _, B) (∧ₑ₁ hu2)) _; assume a2 ha2;
  refine ∃ₑ (∧ₑ₂ ha2) _; assume b2 hb2;
  have ha1A : π (a1 ∈ A) { refine ∧ₑ₁ ha1 };
  have hb1B : π (b1 ∈ B) { refine ∧ₑ₁ hb1 };
  have hc1C : π (c1 ∈ C) { refine ∧ₑ₁ hc1 };
  have ha2A : π (a2 ∈ A) { refine ∧ₑ₁ ha2 };
  have hb2B : π (b2 ∈ B) { refine ∧ₑ₁ hb2 };
  have hc2C : π (c2 ∈ C) { refine ∧ₑ₁ hc2 };
  rewrite (∧ₑ₂ hc1); rewrite (∧ₑ₂ hb1);
  rewrite (∧ₑ₂ hc2); rewrite (∧ₑ₂ hb2);
  have hab1 : π (Pair a1 b1 ∈ Sigma A (λ _, B)) { refine SigmaI a1 b1 A (λ _, B) ha1A hb1B };
  have hab2 : π (Pair a2 b2 ∈ Sigma A (λ _, B)) { refine SigmaI a2 b2 A (λ _, B) ha2A hb2B };
  have hbc1 : π (Pair b1 c1 ∈ Sigma B (λ _, C)) { refine SigmaI b1 c1 B (λ _, C) hb1B hc1C };
  have hbc2 : π (Pair b2 c2 ∈ Sigma B (λ _, C)) { refine SigmaI b2 c2 B (λ _, C) hb2B hc2C };
  have hm1 : π (Pair (Pair a1 b1) c1 ∈ Sigma (Sigma A (λ _, B)) (λ _, C))
    { refine SigmaI (Pair a1 b1) c1 (Sigma A (λ _, B)) (λ _, C) hab1 hc1C };
  have hm2 : π (Pair (Pair a2 b2) c2 ∈ Sigma (Sigma A (λ _, B)) (λ _, C))
    { refine SigmaI (Pair a2 b2) c2 (Sigma A (λ _, B)) (λ _, C) hab2 hc2C };
  have hf1 : π (fapply (Lambda (Sigma (Sigma A (λ _, B)) (λ _, C))
                  (λ w, Pair (fst (fst w)) (Pair (snd (fst w)) (snd w))))
                (Pair (Pair a1 b1) c1) = Pair a1 (Pair b1 c1))
    { have hstep1 : π (Pair (fst (fst (Pair (Pair a1 b1) c1)))
                         (Pair (snd (fst (Pair (Pair a1 b1) c1))) (snd (Pair (Pair a1 b1) c1)))
                       = Pair a1 (Pair b1 c1))
        { rewrite (fst_conv (Pair a1 b1) c1);
          rewrite (snd_conv (Pair a1 b1) c1);
          rewrite (fst_conv a1 b1);
          rewrite (snd_conv a1 b1);
          reflexivity };
      rewrite (beta (Sigma (Sigma A (λ _, B)) (λ _, C))
        (λ w, Pair (fst (fst w)) (Pair (snd (fst w)) (snd w))) (Pair (Pair a1 b1) c1) hm1);
      refine hstep1 };
  have hf2 : π (fapply (Lambda (Sigma (Sigma A (λ _, B)) (λ _, C))
                  (λ w, Pair (fst (fst w)) (Pair (snd (fst w)) (snd w))))
                (Pair (Pair a2 b2) c2) = Pair a2 (Pair b2 c2))
    { have hstep2 : π (Pair (fst (fst (Pair (Pair a2 b2) c2)))
                         (Pair (snd (fst (Pair (Pair a2 b2) c2))) (snd (Pair (Pair a2 b2) c2)))
                       = Pair a2 (Pair b2 c2))
        { rewrite (fst_conv (Pair a2 b2) c2);
          rewrite (snd_conv (Pair a2 b2) c2);
          rewrite (fst_conv a2 b2);
          rewrite (snd_conv a2 b2);
          reflexivity };
      rewrite (beta (Sigma (Sigma A (λ _, B)) (λ _, C))
        (λ w, Pair (fst (fst w)) (Pair (snd (fst w)) (snd w))) (Pair (Pair a2 b2) c2) hm2);
      refine hstep2 };
  rewrite hf1; rewrite hf2;
  apply ∧ᵢ
  { // lex on (A×B)×C → lex on A×(B×C)
    assume h;
    refine ∨ₑ (∧ₑ₁ (rmult_iff (Pair a1 b1) c1 (Pair a2 b2) c2
                      (Sigma A (λ _, B)) (rmult A r B s) C t) h) _ _
    { assume h1;
      refine ∨ₑ (∧ₑ₁ (rmult_iff a1 b1 a2 b2 A r B s) (∧ₑ₁ h1)) _ _
      { assume h1a;
        refine ∧ₑ₂ (rmult_iff a1 (Pair b1 c1) a2 (Pair b2 c2) A r
                      (Sigma B (λ _, C)) (rmult B s C t))
          (∨ᵢ₁ (∧ᵢ (∧ₑ₁ h1a) (∧ᵢ ha1A (∧ᵢ ha2A (∧ᵢ hbc1 hbc2))))) }
      { assume h1b;
        have hin : π (Pair (Pair b1 c1) (Pair b2 c2) ∈ rmult B s C t)
          { refine ∧ₑ₂ (rmult_iff b1 c1 b2 c2 B s C t)
              (∨ᵢ₁ (∧ᵢ (∧ₑ₁ h1b) (∧ᵢ hb1B (∧ᵢ hb2B (∧ᵢ hc1C hc2C))))) };
        refine ∧ₑ₂ (rmult_iff a1 (Pair b1 c1) a2 (Pair b2 c2) A r
                      (Sigma B (λ _, C)) (rmult B s C t))
          (∨ᵢ₂ (∧ᵢ hin (∧ᵢ (∧ₑ₁ (∧ₑ₂ h1b)) (∧ᵢ ha2A (∧ᵢ hbc1 hbc2))))) } }
    { assume h2;
      have haa : π (a1 = a2) { refine Pair_inject1 a1 b1 a2 b2 (∧ₑ₁ (∧ₑ₂ h2)) };
      have hbb : π (b1 = b2) { refine Pair_inject2 a1 b1 a2 b2 (∧ₑ₁ (∧ₑ₂ h2)) };
      have hin : π (Pair (Pair b1 c1) (Pair b2 c2) ∈ rmult B s C t)
        { refine ∧ₑ₂ (rmult_iff b1 c1 b2 c2 B s C t)
            (∨ᵢ₂ (∧ᵢ (∧ₑ₁ h2) (∧ᵢ hbb (∧ᵢ hb2B (∧ᵢ hc1C hc2C))))) };
      refine ∧ₑ₂ (rmult_iff a1 (Pair b1 c1) a2 (Pair b2 c2) A r
                    (Sigma B (λ _, C)) (rmult B s C t))
        (∨ᵢ₂ (∧ᵢ hin (∧ᵢ haa (∧ᵢ ha2A (∧ᵢ hbc1 hbc2))))) } }
  { // lex on A×(B×C) → lex on (A×B)×C
    assume h;
    refine ∨ₑ (∧ₑ₁ (rmult_iff a1 (Pair b1 c1) a2 (Pair b2 c2) A r
                      (Sigma B (λ _, C)) (rmult B s C t)) h) _ _
    { assume h1;
      have hin : π (Pair (Pair a1 b1) (Pair a2 b2) ∈ rmult A r B s)
        { refine ∧ₑ₂ (rmult_iff a1 b1 a2 b2 A r B s)
            (∨ᵢ₁ (∧ᵢ (∧ₑ₁ h1) (∧ᵢ ha1A (∧ᵢ ha2A (∧ᵢ hb1B hb2B))))) };
      refine ∧ₑ₂ (rmult_iff (Pair a1 b1) c1 (Pair a2 b2) c2
                    (Sigma A (λ _, B)) (rmult A r B s) C t)
        (∨ᵢ₁ (∧ᵢ hin (∧ᵢ hab1 (∧ᵢ hab2 (∧ᵢ hc1C hc2C))))) }
    { assume h2;
      refine ∨ₑ (∧ₑ₁ (rmult_iff b1 c1 b2 c2 B s C t) (∧ₑ₁ h2)) _ _
      { assume h2a;
        have hin : π (Pair (Pair a1 b1) (Pair a2 b2) ∈ rmult A r B s)
          { refine ∧ₑ₂ (rmult_iff a1 b1 a2 b2 A r B s)
              (∨ᵢ₂ (∧ᵢ (∧ₑ₁ h2a) (∧ᵢ (∧ₑ₁ (∧ₑ₂ h2)) (∧ᵢ ha2A (∧ᵢ hb1B hb2B))))) };
        refine ∧ₑ₂ (rmult_iff (Pair a1 b1) c1 (Pair a2 b2) c2
                      (Sigma A (λ _, B)) (rmult A r B s) C t)
          (∨ᵢ₁ (∧ᵢ hin (∧ᵢ hab1 (∧ᵢ hab2 (∧ᵢ hc1C hc2C))))) }
      { assume h2b;
        have haa : π (a1 = a2) { refine ∧ₑ₁ (∧ₑ₂ h2) };
        have hbb : π (b1 = b2) { refine ∧ₑ₁ (∧ₑ₂ h2b) };
        have habeq : π (Pair a1 b1 = Pair a2 b2) { rewrite haa; rewrite hbb; reflexivity };
        refine ∧ₑ₂ (rmult_iff (Pair a1 b1) c1 (Pair a2 b2) c2
                      (Sigma A (λ _, B)) (rmult A r B s) C t)
          (∨ᵢ₂ (∧ᵢ (∧ₑ₁ h2b) (∧ᵢ habeq (∧ᵢ hab2 (∧ᵢ hc1C hc2C))))) } } }
end;

// ===========================================================================
// Inverse Image of a Relation
// ===========================================================================

// rvimage_iff: <a,b> ∈ rvimage(A,f,r) ⟷ <f`a,f`b>∈r ∧ a∈A ∧ b∈A
opaque symbol rvimage_iff (a b A f r : τ ι) :
  π (Pair a b ∈ rvimage A f r ⇔
     Pair (fapply f a) (fapply f b) ∈ r ∧ a ∈ A ∧ b ∈ A) ≔
begin
  assume a b A f r;
  apply ∧ᵢ
  { // →
    assume h;
    have hSig : π (Pair a b ∈ Sigma A (λ _, A))
      { refine CollectD1 (Pair a b) (Sigma A (λ _, A))
          (λ z, `∃ (x : τ ι), `∃ (y : τ ι),
             z = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ r) h };
    have haA : π (a ∈ A)
      { refine ind_eq (eq_sym (fst_conv a b)) (λ w, w ∈ A)
          (SigmaD1 (Pair a b) A (λ _, A) hSig) };
    have hbA : π (b ∈ A)
      { refine ind_eq (eq_sym (snd_conv a b)) (λ w, w ∈ A)
          (SigmaD2 (Pair a b) A (λ _, A) hSig) };
    have hpred : π (`∃ (x : τ ι), `∃ (y : τ ι),
                    Pair a b = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ r)
      { refine CollectD2 (Pair a b) (Sigma A (λ _, A))
          (λ z, `∃ (x : τ ι), `∃ (y : τ ι),
             z = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ r) h };
    refine ∃ₑ hpred _; assume x hx;
    refine ∃ₑ hx _; assume y hy;
    have heq : π (Pair a b = Pair x y) { refine ∧ₑ₁ hy };
    have hr : π (Pair (fapply f x) (fapply f y) ∈ r) { refine ∧ₑ₂ hy };
    have hax : π (a = x) { refine Pair_inject1 a b x y heq };
    have hby : π (b = y) { refine Pair_inject2 a b x y heq };
    refine ∧ᵢ _ (∧ᵢ haA hbA);
    refine ind_eq hax (λ w, Pair (fapply f w) (fapply f b) ∈ r) _;
    refine ind_eq hby (λ w, Pair (fapply f x) (fapply f w) ∈ r) hr }
  { // ←
    assume h;
    have hr : π (Pair (fapply f a) (fapply f b) ∈ r) { refine ∧ₑ₁ h };
    have haA : π (a ∈ A) { refine ∧ₑ₁ (∧ₑ₂ h) };
    have hbA : π (b ∈ A) { refine ∧ₑ₂ (∧ₑ₂ h) };
    refine CollectI (Pair a b) (Sigma A (λ _, A))
      (λ z, `∃ (x : τ ι), `∃ (y : τ ι),
         z = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ r) _ _
    { refine SigmaI a b A (λ _, A) haA hbA }
    { refine ∃ᵢ a (∃ᵢ b (∧ᵢ (eq_refl (Pair a b)) hr)) } }
end;

// rvimage_type: rvimage(A,f,r) ⊆ A*A
opaque symbol rvimage_type (A f r : τ ι) :
  π (rvimage A f r ⊆ Sigma A (λ _, A)) ≔
begin
  assume A f r;
  refine Collect_subset (Sigma A (λ _, A)) _
end;

// field_rvimage
opaque symbol field_rvimage (A f r : τ ι) :
  π (field (rvimage A f r) ⊆ A) ≔
begin
  assume A f r;
  refine field_rel_subset (rvimage A f r) A (rvimage_type A f r)
end;

// rvimage_converse: rvimage(A,f,converse(r)) = converse(rvimage(A,f,r))
opaque symbol rvimage_converse (A f r : τ ι) :
  π (rvimage A f (converse r) = converse (rvimage A f r)) ≔
begin
  assume A f r;
  refine equality_iffI (rvimage A f (converse r)) (converse (rvimage A f r)) _;
  assume z;
  apply ∧ᵢ
  { // rvimage(A,f,converse r) ⊆ converse(rvimage(A,f,r))
    assume hz;
    have hzS : π (z ∈ Sigma A (λ _, A)) { refine rvimage_type A f (converse r) z hz };
    refine ∃ₑ (SigmaE z A (λ _, A) hzS) _; assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
    have hyA : π (y ∈ A) { refine ∧ₑ₁ hy };
    have hzeq : π (z = Pair x y) { refine ∧ₑ₂ hy };
    have hzr : π (Pair x y ∈ rvimage A f (converse r))
      { refine ind_eq (eq_sym hzeq) (λ w, w ∈ rvimage A f (converse r)) hz };
    have hconv : π (Pair (fapply f x) (fapply f y) ∈ converse r)
      { refine ∧ₑ₁ (∧ₑ₁ (rvimage_iff x y A f (converse r)) hzr) };
    have hr : π (Pair (fapply f y) (fapply f x) ∈ r)
      { refine converseD (fapply f x) (fapply f y) r hconv };
    have hrv2 : π (Pair y x ∈ rvimage A f r)
      { refine ∧ₑ₂ (rvimage_iff y x A f r) (∧ᵢ hr (∧ᵢ hyA hxA)) };
    have hconv2 : π (Pair x y ∈ converse (rvimage A f r))
      { refine converseI y x (rvimage A f r) hrv2 };
    refine ind_eq hzeq (λ w, w ∈ converse (rvimage A f r)) hconv2 }
  { // converse(rvimage(A,f,r)) ⊆ rvimage(A,f,converse r)
    assume hz;
    refine ∃ₑ (converseE z (rvimage A f r) hz) _; assume x hx;
    refine ∃ₑ hx _; assume y hy;
    have hzeq : π (z = Pair x y) { refine ∧ₑ₁ hy };
    have hyx_rv : π (Pair y x ∈ rvimage A f r) { refine ∧ₑ₂ hy };
    have hpred : π (Pair (fapply f y) (fapply f x) ∈ r ∧ y ∈ A ∧ x ∈ A)
      { refine ∧ₑ₁ (rvimage_iff y x A f r) hyx_rv };
    have hconv : π (Pair (fapply f x) (fapply f y) ∈ converse r)
      { refine converseI (fapply f y) (fapply f x) r (∧ₑ₁ hpred) };
    have hrv : π (Pair x y ∈ rvimage A f (converse r))
      { refine ∧ₑ₂ (rvimage_iff x y A f (converse r))
          (∧ᵢ hconv (∧ᵢ (∧ₑ₂ (∧ₑ₂ hpred)) (∧ₑ₁ (∧ₑ₂ hpred)))) };
    refine ind_eq hzeq (λ w, w ∈ rvimage A f (converse r)) hrv }
end;

// --- Partial Ordering Properties ---

// irrefl_rvimage
opaque symbol irrefl_rvimage (f A B r : τ ι) :
  π (f ∈ inj A B) → π (irrefl_on B r) → π (irrefl_on A (rvimage A f r)) ≔
begin
  assume f A B r hinj hirr x hxA hmem;
  have hr : π (Pair (fapply f x) (fapply f x) ∈ r)
    { refine ∧ₑ₁ (∧ₑ₁ (rvimage_iff x x A f r) hmem) };
  have hfx : π (fapply f x ∈ B)
    { refine fapply_type f x A (λ _, B) (inj_is_fun f A B hinj) hxA };
  refine hirr (fapply f x) hfx hr
end;

// trans_on_rvimage
opaque symbol trans_on_rvimage (f A B r : τ ι) :
  π (f ∈ inj A B) → π (trans_on B r) → π (trans_on A (rvimage A f r)) ≔
begin
  assume f A B r hinj htr x hxA y hyA z hzA hxy hyz;
  have hfun : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  have hfx : π (fapply f x ∈ B) { refine fapply_type f x A (λ _, B) hfun hxA };
  have hfy : π (fapply f y ∈ B) { refine fapply_type f y A (λ _, B) hfun hyA };
  have hfz : π (fapply f z ∈ B) { refine fapply_type f z A (λ _, B) hfun hzA };
  have hxy_r : π (Pair (fapply f x) (fapply f y) ∈ r)
    { refine ∧ₑ₁ (∧ₑ₁ (rvimage_iff x y A f r) hxy) };
  have hyz_r : π (Pair (fapply f y) (fapply f z) ∈ r)
    { refine ∧ₑ₁ (∧ₑ₁ (rvimage_iff y z A f r) hyz) };
  have hxz_r : π (Pair (fapply f x) (fapply f z) ∈ r)
    { refine htr (fapply f x) hfx (fapply f y) hfy (fapply f z) hfz hxy_r hyz_r };
  refine ∧ₑ₂ (rvimage_iff x z A f r) (∧ᵢ hxz_r (∧ᵢ hxA hzA))
end;

// part_ord_rvimage
opaque symbol part_ord_rvimage (f A B r : τ ι) :
  π (f ∈ inj A B) → π (part_ord B r) → π (part_ord A (rvimage A f r)) ≔
begin
  assume f A B r hinj hpo;
  refine ∧ᵢ
    (irrefl_rvimage f A B r hinj (∧ₑ₁ hpo))
    (trans_on_rvimage f A B r hinj (∧ₑ₂ hpo))
end;

// linear_rvimage
opaque symbol linear_rvimage (f A B r : τ ι) :
  π (f ∈ inj A B) → π (linear B r) → π (linear A (rvimage A f r)) ≔
begin
  assume f A B r hinj hlin x hxA y hyA;
  have hfun : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  have hfx : π (fapply f x ∈ B) { refine fapply_type f x A (λ _, B) hfun hxA };
  have hfy : π (fapply f y ∈ B) { refine fapply_type f y A (λ _, B) hfun hyA };
  have hcase : π (Pair (fapply f x) (fapply f y) ∈ r
                  ∨ (fapply f x = fapply f y ∨ Pair (fapply f y) (fapply f x) ∈ r))
    { refine hlin (fapply f x) hfx (fapply f y) hfy };
  refine ∨ₑ hcase _ _
  { assume h1;
    refine ∨ᵢ₁ (∧ₑ₂ (rvimage_iff x y A f r) (∧ᵢ h1 (∧ᵢ hxA hyA))) }
  { assume h2;
    refine ∨ₑ h2 _ _
    { assume heq;
      refine ∨ᵢ₂ (∨ᵢ₁ (inj_apply_equality f A B x y hinj heq hxA hyA)) }
    { assume h3;
      refine ∨ᵢ₂ (∨ᵢ₂ (∧ₑ₂ (rvimage_iff y x A f r) (∧ᵢ h3 (∧ᵢ hyA hxA)))) } }
end;

// tot_ord_rvimage
opaque symbol tot_ord_rvimage (f A B r : τ ι) :
  π (f ∈ inj A B) → π (tot_ord B r) → π (tot_ord A (rvimage A f r)) ≔
begin
  assume f A B r hinj hto;
  refine ∧ᵢ
    (part_ord_rvimage f A B r hinj (∧ₑ₁ hto))
    (linear_rvimage f A B r hinj (∧ₑ₂ hto))
end;

// --- Well-foundedness ---

// wf_rvimage: wf(r) → wf(rvimage(A,f,r))   (global)
opaque symbol wf_rvimage (A f r : τ ι) :
  π (wf_global r) → π (wf_global (rvimage A f r)) ≔
begin
  assume A f r hwf Q;
  // Apply global wf of r to the image I = {f`x | x ∈ Q}.
  have hcase : π (RepFun Q (λ x, fapply f x) = empty
                  ∨ Bex (RepFun Q (λ x, fapply f x))
                      (λ w, `∀ (v : τ ι), Pair v w ∈ r ⇒ v ∉ RepFun Q (λ x, fapply f x)))
    { refine hwf (RepFun Q (λ x, fapply f x)) };
  refine ∨ₑ hcase _ _
  { assume hIempty;
    refine ∨ᵢ₁ _;
    refine equals0I Q _;
    assume x hxQ;
    refine emptyE (fapply f x) _;
    rewrite left hIempty;
    refine RepFunI x Q (λ x, fapply f x) hxQ }
  { assume hex;
    refine ∨ᵢ₂ _;
    refine ∃ₑ hex _; assume w hw;
    have hwmin : π (`∀ (v : τ ι), Pair v w ∈ r ⇒ v ∉ RepFun Q (λ x, fapply f x))
      { refine ∧ₑ₂ hw };
    refine ∃ₑ (∧ₑ₁ (RepFun_iff w Q (λ x, fapply f x)) (∧ₑ₁ hw)) _; assume x0 hx0;
    have hweq : π (w = fapply f x0) { refine ∧ₑ₂ hx0 };
    refine ∃ᵢ x0 (∧ᵢ (∧ₑ₁ hx0) _);
    assume y hyr hyQ;
    have hfr : π (Pair (fapply f y) (fapply f x0) ∈ r)
      { refine ∧ₑ₁ (∧ₑ₁ (rvimage_iff y x0 A f r) hyr) };
    refine hwmin (fapply f y) (ind_eq hweq (λ t, Pair (fapply f y) t ∈ r) hfr)
      (RepFunI y Q (λ x, fapply f x) hyQ) }
end;

// wf_on_rvimage: f∈A→B → wf[B](r) → wf[A](rvimage(A,f,r))
opaque symbol wf_on_rvimage (A B f r : τ ι) :
  π (f ∈ Pi A (λ _, B)) → π (wf B r) → π (wf A (rvimage A f r)) ≔
begin
  assume A B f r hf hwfB Z hZA hZne;
  // The image f''Z = {f`z | z ∈ Z} is a nonempty subset of B.
  have hImgSub : π (RepFun Z (λ z, fapply f z) ⊆ B) {
    assume w hw;
    refine ∃ₑ (∧ₑ₁ (RepFun_iff w Z (λ z, fapply f z)) hw) _; assume z hz;
    rewrite (∧ₑ₂ hz);
    refine fapply_type f z A (λ _, B) hf (hZA z (∧ₑ₁ hz)) };
  have hImgne : π (RepFun Z (λ z, fapply f z) ≠ empty) {
    assume heq;
    refine not_emptyE Z _ hZne _;
    assume z hzZ;
    refine emptyE (fapply f z) _;
    rewrite left heq;
    refine RepFunI z Z (λ z, fapply f z) hzZ };
  // wf[B](r) gives an r-minimal element of the image, which is f`x0 for some x0∈Z.
  have hmin : π (Bex (RepFun Z (λ z, fapply f z))
                  (λ w, Ball (RepFun Z (λ z, fapply f z)) (λ v, Pair v w ∉ r)))
    { refine hwfB (RepFun Z (λ z, fapply f z)) hImgSub hImgne };
  refine ∃ₑ hmin _; assume w hw;
  have hwmin : π (Ball (RepFun Z (λ z, fapply f z)) (λ v, Pair v w ∉ r))
    { refine ∧ₑ₂ hw };
  refine ∃ₑ (∧ₑ₁ (RepFun_iff w Z (λ z, fapply f z)) (∧ₑ₁ hw)) _; assume x0 hx0;
  have hweq : π (w = fapply f x0) { refine ∧ₑ₂ hx0 };
  // x0 is rvimage-minimal in Z.
  refine ∃ᵢ x0 (∧ᵢ (∧ₑ₁ hx0) _);
  assume y hyZ hyr;
  have hfr : π (Pair (fapply f y) (fapply f x0) ∈ r)
    { refine ∧ₑ₁ (∧ₑ₁ (rvimage_iff y x0 A f r) hyr) };
  refine hwmin (fapply f y) (RepFunI y Z (λ z, fapply f z) hyZ)
    (ind_eq hweq (λ t, Pair (fapply f y) t ∈ r) hfr)
end;

// well_ord_rvimage: f∈inj(A,B) → well_ord(B,r) → well_ord(A,rvimage(A,f,r))
opaque symbol well_ord_rvimage (A B f r : τ ι) :
  π (f ∈ inj A B) → π (well_ord B r) → π (well_ord A (rvimage A f r)) ≔
begin
  assume A B f r hinj hwo;
  refine well_ordI A (rvimage A f r)
    (wf_on_rvimage A B f r (inj_is_fun f A B hinj) (well_ord_is_wf B r hwo))
    (linear_rvimage f A B r hinj (well_ord_is_linear B r hwo))
end;

// ord_iso_rvimage: f∈bij(A,B) → f∈ord_iso(A,rvimage(A,f,s),B,s)
opaque symbol ord_iso_rvimage (f A B s : τ ι) :
  π (f ∈ bij A B) → π (f ∈ ord_iso A (rvimage A f s) B s) ≔
begin
  assume f A B s hbij;
  refine CollectI f (bij A B)
    (λ g, Ball A (λ x, Ball A (λ y,
      (Pair x y ∈ rvimage A f s) ⇔ (Pair (fapply g x) (fapply g y) ∈ s)))) hbij _;
  assume x hxA y hyA;
  apply ∧ᵢ
  { assume h;
    refine ∧ₑ₁ (∧ₑ₁ (rvimage_iff x y A f s) h) }
  { assume h;
    refine ∧ₑ₂ (rvimage_iff x y A f s) (∧ᵢ h (∧ᵢ hxA hyA)) }
end;

// ord_iso_rvimage_eq: f∈ord_iso(A,r,B,s) → rvimage(A,f,s) = r ∩ A*A
opaque symbol ord_iso_rvimage_eq (f A r B s : τ ι) :
  π (f ∈ ord_iso A r B s) → π (rvimage A f s = Int r (Sigma A (λ _, A))) ≔
begin
  assume f A r B s hiso;
  have hcond : π (Ball A (λ a, Ball A (λ b,
                  (Pair a b ∈ r) ⇔ (Pair (fapply f a) (fapply f b) ∈ s))))
    { refine CollectD2 f (bij A B)
        (λ g, Ball A (λ a, Ball A (λ b,
          (Pair a b ∈ r) ⇔ (Pair (fapply g a) (fapply g b) ∈ s)))) hiso };
  refine equality_iffI (rvimage A f s) (Int r (Sigma A (λ _, A))) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    have hzS : π (z ∈ Sigma A (λ _, A))
      { refine CollectD1 z (Sigma A (λ _, A))
          (λ w, `∃ (x : τ ι), `∃ (y : τ ι),
             w = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ s) hz };
    have hpred : π (`∃ (x : τ ι), `∃ (y : τ ι),
                    z = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ s)
      { refine CollectD2 z (Sigma A (λ _, A))
          (λ w, `∃ (x : τ ι), `∃ (y : τ ι),
             w = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ s) hz };
    refine ∃ₑ hpred _; assume x hx; refine ∃ₑ hx _; assume y hy;
    have hzeq : π (z = Pair x y) { refine ∧ₑ₁ hy };
    have hs1 : π (Pair (fapply f x) (fapply f y) ∈ s) { refine ∧ₑ₂ hy };
    have hzS2 : π (Pair x y ∈ Sigma A (λ _, A))
      { refine ind_eq (eq_sym hzeq) (λ w, w ∈ Sigma A (λ _, A)) hzS };
    have hxA : π (x ∈ A)
      { refine ind_eq (eq_sym (fst_conv x y)) (λ w, w ∈ A)
          (SigmaD1 (Pair x y) A (λ _, A) hzS2) };
    have hyA : π (y ∈ A)
      { refine ind_eq (eq_sym (snd_conv x y)) (λ w, w ∈ A)
          (SigmaD2 (Pair x y) A (λ _, A) hzS2) };
    have hr1 : π (Pair x y ∈ r) { refine ∧ₑ₂ (hcond x hxA y hyA) hs1 };
    refine IntI z r (Sigma A (λ _, A)) (ind_eq hzeq (λ w, w ∈ r) hr1) hzS }
  { assume hz;
    have hzr : π (z ∈ r) { refine IntD1 z r (Sigma A (λ _, A)) hz };
    have hzS : π (z ∈ Sigma A (λ _, A)) { refine IntD2 z r (Sigma A (λ _, A)) hz };
    refine ∃ₑ (SigmaE z A (λ _, A) hzS) _; assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
    have hyA : π (y ∈ A) { refine ∧ₑ₁ hy };
    have hzeq : π (z = Pair x y) { refine ∧ₑ₂ hy };
    have hr1 : π (Pair x y ∈ r) { refine ind_eq (eq_sym hzeq) (λ w, w ∈ r) hzr };
    have hs1 : π (Pair (fapply f x) (fapply f y) ∈ s)
      { refine ∧ₑ₁ (hcond x hxA y hyA) hr1 };
    refine CollectI z (Sigma A (λ _, A))
      (λ w, `∃ (x : τ ι), `∃ (y : τ ι),
         w = Pair x y ∧ Pair (fapply f x) (fapply f y) ∈ s) hzS _;
    refine ∃ᵢ x (∃ᵢ y (∧ᵢ hzeq hs1)) }
end;

// ===========================================================================
// Every well-founded relation is a subset of some inverse image of an ordinal
// ===========================================================================

// wf_rvimage_Ord: Ord(i) → wf(rvimage(A,f,Memrel(i)))
opaque symbol wf_rvimage_Ord (i A f : τ ι) :
  π (Ord i) → π (wf_global (rvimage A f (Memrel i))) ≔
begin
  assume i A f hOrd;
  refine wf_rvimage A f (Memrel i) (wf_Memrel i)
end;

// wfrank (Isabelle lemma `wfrank`, renamed to avoid clash with the definition):
//   wf(r) → wfrank(r,a) = (⋃y∈r-``{a}. succ(wfrank(r,y)))
opaque symbol wfrank_unfold (r a : τ ι) :
  π (wf_global r) →
  π (wfrank r a = Union (RepFun (vimage_singleton r a) (λ y, succ (wfrank r y)))) ≔
begin
  assume r a hwf;
  // wfrec_eq unfolds one step: the recursion body applied to the cut λ-abstraction.
  have hrec : π (wfrank r a =
    Union (RepFun (vimage_singleton r a)
      (λ y, succ (fapply (Lambda (vimage_singleton r a) (λ x, wfrank r x)) y))))
    { refine wfrec_eq r a
        (λ x f, Union (RepFun (vimage_singleton r x) (λ y, succ (fapply f y)))) hwf };
  // Under the RepFun, fapply(Lambda …) y β-reduces to wfrank r y for y in the domain.
  have hcong : π (RepFun (vimage_singleton r a)
      (λ y, succ (fapply (Lambda (vimage_singleton r a) (λ x, wfrank r x)) y))
    = RepFun (vimage_singleton r a) (λ y, succ (wfrank r y)))
    { refine RepFun_cong (vimage_singleton r a)
        (λ y, succ (fapply (Lambda (vimage_singleton r a) (λ x, wfrank r x)) y))
        (λ y, succ (wfrank r y)) _;
      assume y hy;
      have hbeta : π (fapply (Lambda (vimage_singleton r a) (λ x, wfrank r x)) y = wfrank r y)
        { refine beta (vimage_singleton r a) (λ x, wfrank r x) y hy };
      rewrite hbeta; reflexivity };
  rewrite hrec; rewrite hcong; reflexivity
end;

// Ord_wfrank: wf(r) → Ord(wfrank(r,a))
opaque symbol Ord_wfrank (r a : τ ι) :
  π (wf_global r) → π (Ord (wfrank r a)) ≔
begin
  assume r a hwf;
  refine wf_global_induct r (λ w, Ord (wfrank r w)) a hwf _;
  assume x IH;
  // wfrank r x = ⋃ y∈r⁻¹{x}. succ(wfrank r y); every element is an ordinal.
  rewrite (wfrank_unfold r x hwf);
  refine Ord_Union (RepFun (vimage_singleton r x) (λ y, succ (wfrank r y))) _;
  assume z hz;
  have hbex : π (Bex (vimage_singleton r x) (λ y, z = succ (wfrank r y)))
    { refine ∧ₑ₁ (RepFun_iff z (vimage_singleton r x) (λ y, succ (wfrank r y))) hz };
  refine ∃ₑ hbex _; assume y hy;
  have hyvim : π (y ∈ vimage_singleton r x) { refine ∧ₑ₁ hy };
  have hzeq : π (z = succ (wfrank r y)) { refine ∧ₑ₂ hy };
  have hyx : π (Pair y x ∈ r) { refine vimage_singletonD y x r hyvim };
  rewrite hzeq;
  refine Ord_succ (wfrank r y) (IH y hyx)
end;

// wfrank_lt: wf(r) → <a,b>∈r → wfrank(r,a) < wfrank(r,b)
opaque symbol wfrank_lt (r a b : τ ι) :
  π (wf_global r) → π (Pair a b ∈ r) → π (lt (wfrank r a) (wfrank r b)) ≔
begin
  assume r a b hwf hab;
  have havim : π (a ∈ vimage_singleton r b) { refine vimage_singletonI a b r hab };
  have hrep : π (succ (wfrank r a) ∈ RepFun (vimage_singleton r b) (λ y, succ (wfrank r y)))
    { refine RepFunI a (vimage_singleton r b) (λ y, succ (wfrank r y)) havim };
  have hmemU : π (wfrank r a ∈ Union (RepFun (vimage_singleton r b) (λ y, succ (wfrank r y))))
    { refine UnionI (wfrank r a) (succ (wfrank r a))
        (RepFun (vimage_singleton r b) (λ y, succ (wfrank r y)))
        (succI1 (wfrank r a)) hrep };
  have hmem : π (wfrank r a ∈ wfrank r b)
    { rewrite (wfrank_unfold r b hwf); refine hmemU };
  refine ltI (wfrank r a) (wfrank r b) hmem (Ord_wfrank r b hwf)
end;

// Ord_wftype: wf(r) → Ord(wftype(r))
opaque symbol Ord_wftype (r : τ ι) :
  π (wf_global r) → π (Ord (wftype r)) ≔
begin
  assume r hwf;
  // wftype r = ⋃ y∈range(r). succ(wfrank r y); every element is an ordinal.
  refine Ord_Union (RepFun (range r) (λ y, succ (wfrank r y))) _;
  assume z hz;
  have hbex : π (Bex (range r) (λ y, z = succ (wfrank r y)))
    { refine ∧ₑ₁ (RepFun_iff z (range r) (λ y, succ (wfrank r y))) hz };
  refine ∃ₑ hbex _; assume y hy;
  have hzeq : π (z = succ (wfrank r y)) { refine ∧ₑ₂ hy };
  rewrite hzeq;
  refine Ord_succ (wfrank r y) (Ord_wfrank r y hwf)
end;

// wftypeI: wf(r) → x∈field(r) → wfrank(r,x) ∈ wftype(r)
opaque symbol wftypeI (r x : τ ι) :
  π (wf_global r) → π (x ∈ field r) → π (wfrank r x ∈ wftype r) ≔
begin
  assume r x hwf hxfield;
  // field r = domain r ∪ range r
  have hxfield' : π (x ∈ Un (domain r) (range r))
    { refine ind_eq (eq_sym (field_def r)) (λ s, x ∈ s) hxfield };
  have hdisj : π (x ∈ domain r ∨ x ∈ range r)
    { refine ∧ₑ₁ (Un_iff x (domain r) (range r)) hxfield' };
  refine ∨ₑ hdisj _ _
  { // x ∈ domain r: some ⟨x,z⟩∈r, so wfrank r x < wfrank r z with z∈range r.
    assume hxdom;
    have hex : π (`∃ z, Pair x z ∈ r) { refine domainE x r hxdom };
    refine ∃ₑ hex _; assume z hz;
    have hzrange : π (z ∈ range r) { refine rangeI x z r hz };
    have hlt : π (lt (wfrank r x) (wfrank r z)) { refine wfrank_lt r x z hwf hz };
    have hmem_wz : π (wfrank r x ∈ wfrank r z) { refine ltD (wfrank r x) (wfrank r z) hlt };
    have hrep : π (succ (wfrank r z) ∈ RepFun (range r) (λ y, succ (wfrank r y)))
      { refine RepFunI z (range r) (λ y, succ (wfrank r y)) hzrange };
    have hmem_succ : π (wfrank r x ∈ succ (wfrank r z))
      { refine succI2 (wfrank r x) (wfrank r z) hmem_wz };
    refine UnionI (wfrank r x) (succ (wfrank r z))
      (RepFun (range r) (λ y, succ (wfrank r y))) hmem_succ hrep }
  { // x ∈ range r: wfrank r x ∈ succ(wfrank r x), which is one of the union'd sets.
    assume hxrange;
    have hrep : π (succ (wfrank r x) ∈ RepFun (range r) (λ y, succ (wfrank r y)))
      { refine RepFunI x (range r) (λ y, succ (wfrank r y)) hxrange };
    refine UnionI (wfrank r x) (succ (wfrank r x))
      (RepFun (range r) (λ y, succ (wfrank r y))) (succI1 (wfrank r x)) hrep }
end;

// wf_imp_subset_rvimage:
//   wf(r) → r⊆A*A → ∃i f. Ord(i) ∧ r ⊆ rvimage(A,f,Memrel(i))
opaque symbol wf_imp_subset_rvimage (r A : τ ι) :
  π (wf_global r) → π (r ⊆ Sigma A (λ _, A)) →
  π (`∃ (i : τ ι), `∃ (f : τ ι),
       Ord i ∧ r ⊆ rvimage A f (Memrel i)) ≔
begin
  assume r A hwf hsub;
  // Witness i = wftype(r), f = (λx∈A. wfrank(r,x)).
  refine ∃ᵢ (wftype r) (∃ᵢ (Lambda A (λ x, wfrank r x)) (∧ᵢ _ _))
  { refine Ord_wftype r hwf }
  { assume p hp;
    // p ∈ r ⊆ A*A, so p = ⟨a,b⟩ with a,b ∈ A and ⟨a,b⟩ ∈ r.
    have hpS : π (p ∈ Sigma A (λ _, A)) { refine hsub p hp };
    refine ∃ₑ (SigmaE p A (λ _, A) hpS) _; assume a ha;
    have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
    refine ∃ₑ (∧ₑ₂ ha) _; assume b hb;
    have hbA : π (b ∈ A) { refine ∧ₑ₁ hb };
    have hpeq : π (p = Pair a b) { refine ∧ₑ₂ hb };
    have hab_r : π (Pair a b ∈ r) { refine ind_eq (eq_sym hpeq) (λ z, z ∈ r) hp };
    // f`a = wfrank r a, f`b = wfrank r b (β on the Lambda).
    have hfa : π (fapply (Lambda A (λ x, wfrank r x)) a = wfrank r a)
      { refine beta A (λ x, wfrank r x) a haA };
    have hfb : π (fapply (Lambda A (λ x, wfrank r x)) b = wfrank r b)
      { refine beta A (λ x, wfrank r x) b hbA };
    // wfrank r a ∈ wfrank r b, and both ranks lie in wftype r.
    have hmem : π (wfrank r a ∈ wfrank r b)
      { refine ltD (wfrank r a) (wfrank r b) (wfrank_lt r a b hwf hab_r) };
    have hwa : π (wfrank r a ∈ wftype r) { refine wftypeI r a hwf (fieldI1 a b r hab_r) };
    have hwb : π (wfrank r b ∈ wftype r) { refine wftypeI r b hwf (fieldI2 a b r hab_r) };
    have hMem : π (Pair (wfrank r a) (wfrank r b) ∈ Memrel (wftype r))
      { refine MemrelI (wfrank r a) (wfrank r b) (wftype r) hmem hwa hwb };
    have hMem2 : π (Pair (fapply (Lambda A (λ x, wfrank r x)) a)
                        (fapply (Lambda A (λ x, wfrank r x)) b) ∈ Memrel (wftype r))
      { rewrite hfa; rewrite hfb; refine hMem };
    have hrv : π (Pair a b ∈ rvimage A (Lambda A (λ x, wfrank r x)) (Memrel (wftype r)))
      { refine ∧ₑ₂ (rvimage_iff a b A (Lambda A (λ x, wfrank r x)) (Memrel (wftype r)))
          (∧ᵢ hMem2 (∧ᵢ haA hbA)) };
    refine ind_eq hpeq
      (λ z, z ∈ rvimage A (Lambda A (λ x, wfrank r x)) (Memrel (wftype r))) hrv }
end;

// wf_iff_subset_rvimage:
//   relation(r) → (wf(r) ⟷ ∃i f A. Ord(i) ∧ r ⊆ rvimage(A,f,Memrel(i)))
opaque symbol wf_iff_subset_rvimage (r : τ ι) :
  π (relation r) →
  π (wf_global r ⇔
     `∃ (i : τ ι), `∃ (f : τ ι), `∃ (A : τ ι),
        Ord i ∧ r ⊆ rvimage A f (Memrel i)) ≔
begin
  assume r hrel;
  have hrel' : π (`∀ (z : τ ι), z ∈ r ⇒ `∃ (x : τ ι), `∃ (y : τ ι), z = Pair x y)
    { refine ind_eq (eq_sym (relation_def r)) (λ p, p) hrel };
  apply ∧ᵢ
  { // →: a relation is ⊆ field(r)*field(r); apply wf_imp_subset_rvimage.
    assume hwf;
    have hsub : π (r ⊆ Sigma (field r) (λ _, field r)) {
      assume z hz;
      refine ∃ₑ (hrel' z hz) _; assume x hx;
      refine ∃ₑ hx _; assume y hy;
      have hzeq : π (z = Pair x y) { refine hy };
      have hzr : π (Pair x y ∈ r) { refine ind_eq (eq_sym hzeq) (λ w, w ∈ r) hz };
      refine ind_eq hzeq (λ w, w ∈ Sigma (field r) (λ _, field r))
        (SigmaI x y (field r) (λ _, field r) (fieldI1 x y r hzr) (fieldI2 x y r hzr)) };
    have hex : π (`∃ (i : τ ι), `∃ (f : τ ι),
                    Ord i ∧ r ⊆ rvimage (field r) f (Memrel i))
      { refine wf_imp_subset_rvimage r (field r) hwf hsub };
    refine ∃ₑ hex _; assume i hi;
    refine ∃ₑ hi _; assume f hf;
    refine ∃ᵢ i (∃ᵢ f (∃ᵢ (field r) hf)) }
  { // ←: rvimage of Memrel of an ordinal is wf; r is a subset of it.
    assume hex;
    refine ∃ₑ hex _; assume i hi;
    refine ∃ₑ hi _; assume f hf;
    refine ∃ₑ hf _; assume A hA;
    have hwfrv : π (wf_global (rvimage A f (Memrel i)))
      { refine wf_rvimage_Ord i A f (∧ₑ₁ hA) };
    refine wf_global_subset (rvimage A f (Memrel i)) r hwfrv (∧ₑ₂ hA) }
end;

// ===========================================================================
// Other Results
// ===========================================================================

// wf_times: A∩B=0 → wf(A*B)
opaque symbol wf_times (A B : τ ι) :
  π (Int A B = empty) → π (wf_global (Sigma A (λ _, B))) ≔
begin
  assume A B hdisj Z;
  refine ∨ₑ (em (Z = empty)) _ _
  { assume h; refine ∨ᵢ₁ h }
  { assume hZne;
    refine ∨ᵢ₂ _;
    refine not_emptyE Z _ hZne _;
    assume x0 hx0Z;
    refine ∨ₑ (em (Bex Z (λ y, Pair y x0 ∈ Sigma A (λ _, B)))) _ _
    { // x0 has a Z-predecessor y; that y is minimal (no length-2 chains).
      assume hpre;
      refine ∃ₑ hpre _; assume y hy;
      have hyA : π (y ∈ A)
        { refine ind_eq (eq_sym (fst_conv y x0)) (λ w, w ∈ A)
            (SigmaD1 (Pair y x0) A (λ _, B) (∧ₑ₂ hy)) };
      refine ∃ᵢ y (∧ᵢ (∧ₑ₁ hy) _);
      assume z hzr hzZ;
      have hyB : π (y ∈ B)
        { refine ind_eq (eq_sym (snd_conv z y)) (λ w, w ∈ B)
            (SigmaD2 (Pair z y) A (λ _, B) hzr) };
      refine emptyE y (ind_eq (eq_sym hdisj) (λ s, y ∈ s) (IntI y A B hyA hyB)) }
    { // x0 has no Z-predecessor, so x0 itself is minimal.
      assume hnopre;
      refine ∃ᵢ x0 (∧ᵢ hx0Z _);
      assume y hyr hyZ;
      refine hnopre (∃ᵢ y (∧ᵢ hyZ hyr)) } }
end;

// wf_Un: range(r)∩domain(s)=0 → wf(r) → wf(s) → wf(r∪s)
opaque symbol wf_Un (r s : τ ι) :
  π (Int (range r) (domain s) = empty) →
  π (wf_global r) → π (wf_global s) → π (wf_global (Un r s)) ≔
// Let Z0 = {z∈Z. no r-predecessor of z lies in Z}; it is nonempty (it contains
// the r-minimal element of Z), and the s-minimal element x2 of Z0 is
// (r∪s)-minimal in Z: an r-predecessor is barred since x2∈Z0, and an
// s-predecessor y∈Z would itself have to lie outside Z0 — i.e. have an
// r-predecessor in Z — putting y ∈ range(r) ∩ domain(s) = 0.
begin
  assume r s hdisj hwfr hwfs Z;
  refine ∨ₑ (hwfr Z) _ _
  { assume hZe; refine ∨ᵢ₁ hZe }
  { assume hminr;
    refine ∨ᵢ₂ _;
    refine ∃ₑ hminr _; assume x1 hx1;
    have hx1Z0 : π (x1 ∈ Collect Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z))
      { refine CollectI x1 Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z)
          (∧ₑ₁ hx1) (∧ₑ₂ hx1) };
    refine ∨ₑ (hwfs (Collect Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z))) _ _
    { assume hZ0e;
      refine ⊥ₑ (equals0D (Collect Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z))
        x1 hZ0e hx1Z0) }
    { assume hmins;
      refine ∃ₑ hmins _; assume x2 hx2;
      have hx2Z0 : π (x2 ∈ Collect Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z))
        { refine ∧ₑ₁ hx2 };
      have hx2Z : π (x2 ∈ Z)
        { refine CollectD1 x2 Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z) hx2Z0 };
      have hx2nr : π (`∀ (w : τ ι), Pair w x2 ∈ r ⇒ w ∉ Z)
        { refine CollectD2 x2 Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z) hx2Z0 };
      have hx2min : π (`∀ (y : τ ι), Pair y x2 ∈ s ⇒
                        y ∉ Collect Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z))
        { refine ∧ₑ₂ hx2 };
      refine ∃ᵢ x2 (∧ᵢ hx2Z _);
      assume y hyUn hyZ;
      refine ∨ₑ (UnE (Pair y x2) r s hyUn) _ _
      { assume hyr; refine hx2nr y hyr hyZ }
      { assume hys;
        refine ∨ₑ (em (Bex Z (λ w, Pair w y ∈ r))) _ _
        { assume hex;
          refine ∃ₑ hex _; assume w hw;
          have hyrange : π (y ∈ range r) { refine rangeI w y r (∧ₑ₂ hw) };
          have hydom : π (y ∈ domain s) { refine domainI y x2 s hys };
          refine emptyE y (ind_eq (eq_sym hdisj) (λ t, y ∈ t)
            (IntI y (range r) (domain s) hyrange hydom)) }
        { assume hno;
          have hPy : π (`∀ (w : τ ι), Pair w y ∈ r ⇒ w ∉ Z)
            { assume w hwr hwZ; refine hno (∃ᵢ w (∧ᵢ hwZ hwr)) };
          refine hx2min y hys
            (CollectI y Z (λ z, `∀ (w : τ ι), Pair w z ∈ r ⇒ w ∉ Z) hyZ hPy) } } } }
end;

// --- The Empty Relation ---

// wf0: wf(0)
opaque symbol wf0 : π (wf_global empty) ≔
begin
  assume Z;
  refine ∨ₑ (em (Z = empty)) _ _
  { assume h; refine ∨ᵢ₁ h }
  { assume hne;
    refine ∨ᵢ₂ _;
    refine not_emptyE Z _ hne _;
    assume x hxZ;
    refine ∃ᵢ x (∧ᵢ hxZ _);
    assume y hyr;
    refine ⊥ₑ (emptyE (Pair y x) hyr) }
end;

// linear0: linear(0,0)
opaque symbol linear0 : π (linear empty empty) ≔
begin
  refine linear_0 empty
end;

// well_ord0: well_ord(0,0)
opaque symbol well_ord0 : π (well_ord empty empty) ≔
begin
  refine well_ord_0 empty
end;

// --- The "measure" relation ---

// measure_iff: <x,y>∈measure(A,f) ⟷ x∈A ∧ y∈A ∧ f(x)<f(y)
opaque symbol measure_iff (A : τ ι) (f : τ ι → τ ι) (x y : τ ι) :
  π (Pair x y ∈ measure A f ⇔ x ∈ A ∧ y ∈ A ∧ lt (f x) (f y)) ≔
begin
  assume A f x y;
  apply ∧ᵢ
  { assume h;
    have hSig : π (Pair x y ∈ Sigma A (λ _, A))
      { refine CollectD1 (Pair x y) (Sigma A (λ _, A))
          (λ z, lt (f (fst z)) (f (snd z))) h };
    have hxA : π (x ∈ A)
      { refine ind_eq (eq_sym (fst_conv x y)) (λ w, w ∈ A)
          (SigmaD1 (Pair x y) A (λ _, A) hSig) };
    have hyA : π (y ∈ A)
      { refine ind_eq (eq_sym (snd_conv x y)) (λ w, w ∈ A)
          (SigmaD2 (Pair x y) A (λ _, A) hSig) };
    have hlt : π (lt (f (fst (Pair x y))) (f (snd (Pair x y))))
      { refine CollectD2 (Pair x y) (Sigma A (λ _, A))
          (λ z, lt (f (fst z)) (f (snd z))) h };
    have hlt1 : π (lt (f x) (f (snd (Pair x y))))
      { refine ind_eq (eq_sym (fst_conv x y)) (λ w, lt (f w) (f (snd (Pair x y)))) hlt };
    have hlt2 : π (lt (f x) (f y))
      { refine ind_eq (eq_sym (snd_conv x y)) (λ w, lt (f x) (f w)) hlt1 };
    refine ∧ᵢ hxA (∧ᵢ hyA hlt2) }
  { assume h;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ h };
    have hyA : π (y ∈ A) { refine ∧ₑ₁ (∧ₑ₂ h) };
    have hlt : π (lt (f x) (f y)) { refine ∧ₑ₂ (∧ₑ₂ h) };
    refine CollectI (Pair x y) (Sigma A (λ _, A)) (λ z, lt (f (fst z)) (f (snd z))) _ _
    { refine SigmaI x y A (λ _, A) hxA hyA }
    { have hlt1 : π (lt (f (fst (Pair x y))) (f y))
        { refine ind_eq (fst_conv x y) (λ w, lt (f w) (f y)) hlt };
      refine ind_eq (snd_conv x y) (λ w, lt (f (fst (Pair x y))) (f w)) hlt1 } }
end;

// measure_eq_rvimage_Memrel:
//   measure(A,f) = rvimage(A, Lambda(A,f), Memrel(Collect(RepFun(A,f),Ord)))
opaque symbol measure_eq_rvimage_Memrel (A : τ ι) (f : τ ι → τ ι) :
  π (measure A f
     = rvimage A (Lambda A f) (Memrel (Collect (RepFun A f) (λ x, Ord x)))) ≔
begin
  assume A f;
  refine equality_iffI (measure A f)
    (rvimage A (Lambda A f) (Memrel (Collect (RepFun A f) (λ x, Ord x)))) _;
  assume z;
  apply ∧ᵢ
  { // measure ⊆ rvimage
    assume hz;
    have hzS : π (z ∈ Sigma A (λ _, A))
      { refine CollectD1 z (Sigma A (λ _, A)) (λ w, lt (f (fst w)) (f (snd w))) hz };
    refine ∃ₑ (SigmaE z A (λ _, A) hzS) _; assume a ha;
    have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
    refine ∃ₑ (∧ₑ₂ ha) _; assume b hb;
    have hbA : π (b ∈ A) { refine ∧ₑ₁ hb };
    have hzeq : π (z = Pair a b) { refine ∧ₑ₂ hb };
    have hzm : π (Pair a b ∈ measure A f)
      { refine ind_eq (eq_sym hzeq) (λ w, w ∈ measure A f) hz };
    have hlt : π (lt (f a) (f b)) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₁ (measure_iff A f a b) hzm)) };
    have hab_mem : π (f a ∈ f b) { refine ltD (f a) (f b) hlt };
    have hOb : π (Ord (f b)) { refine ∧ₑ₂ hlt };
    have hOa : π (Ord (f a)) { refine Ord_in_Ord (f b) (f a) hOb hab_mem };
    have hfaC : π (f a ∈ Collect (RepFun A f) (λ x, Ord x))
      { refine CollectI (f a) (RepFun A f) (λ x, Ord x) (RepFunI a A f haA) hOa };
    have hfbC : π (f b ∈ Collect (RepFun A f) (λ x, Ord x))
      { refine CollectI (f b) (RepFun A f) (λ x, Ord x) (RepFunI b A f hbA) hOb };
    have hMem : π (Pair (f a) (f b) ∈ Memrel (Collect (RepFun A f) (λ x, Ord x)))
      { refine MemrelI (f a) (f b) (Collect (RepFun A f) (λ x, Ord x)) hab_mem hfaC hfbC };
    have hga : π (fapply (Lambda A f) a = f a) { refine beta A f a haA };
    have hgb : π (fapply (Lambda A f) b = f b) { refine beta A f b hbA };
    have hMem2 : π (Pair (fapply (Lambda A f) a) (fapply (Lambda A f) b)
                    ∈ Memrel (Collect (RepFun A f) (λ x, Ord x)))
      { rewrite hga; rewrite hgb; refine hMem };
    have hrv : π (Pair a b
                  ∈ rvimage A (Lambda A f) (Memrel (Collect (RepFun A f) (λ x, Ord x))))
      { refine ∧ₑ₂ (rvimage_iff a b A (Lambda A f)
          (Memrel (Collect (RepFun A f) (λ x, Ord x))))
          (∧ᵢ hMem2 (∧ᵢ haA hbA)) };
    refine ind_eq hzeq
      (λ w, w ∈ rvimage A (Lambda A f) (Memrel (Collect (RepFun A f) (λ x, Ord x)))) hrv }
  { // rvimage ⊆ measure
    assume hz;
    have hzS : π (z ∈ Sigma A (λ _, A))
      { refine rvimage_type A (Lambda A f)
          (Memrel (Collect (RepFun A f) (λ x, Ord x))) z hz };
    refine ∃ₑ (SigmaE z A (λ _, A) hzS) _; assume a ha;
    have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
    refine ∃ₑ (∧ₑ₂ ha) _; assume b hb;
    have hbA : π (b ∈ A) { refine ∧ₑ₁ hb };
    have hzeq : π (z = Pair a b) { refine ∧ₑ₂ hb };
    have hzr : π (Pair a b
                  ∈ rvimage A (Lambda A f) (Memrel (Collect (RepFun A f) (λ x, Ord x))))
      { refine ind_eq (eq_sym hzeq)
          (λ w, w ∈ rvimage A (Lambda A f) (Memrel (Collect (RepFun A f) (λ x, Ord x)))) hz };
    have hgab : π (Pair (fapply (Lambda A f) a) (fapply (Lambda A f) b)
                   ∈ Memrel (Collect (RepFun A f) (λ x, Ord x)))
      { refine ∧ₑ₁ (∧ₑ₁ (rvimage_iff a b A (Lambda A f)
          (Memrel (Collect (RepFun A f) (λ x, Ord x)))) hzr) };
    have hga : π (fapply (Lambda A f) a = f a) { refine beta A f a haA };
    have hgb : π (fapply (Lambda A f) b = f b) { refine beta A f b hbA };
    have hMem : π (Pair (f a) (f b) ∈ Memrel (Collect (RepFun A f) (λ x, Ord x)))
      { rewrite left hga; rewrite left hgb; refine hgab };
    have hME : π (f a ∈ Collect (RepFun A f) (λ x, Ord x)
                  ∧ f b ∈ Collect (RepFun A f) (λ x, Ord x) ∧ f a ∈ f b)
      { refine MemrelE (f a) (f b) (Collect (RepFun A f) (λ x, Ord x)) hMem };
    have hab_mem : π (f a ∈ f b) { refine ∧ₑ₂ (∧ₑ₂ hME) };
    have hOb : π (Ord (f b))
      { refine CollectD2 (f b) (RepFun A f) (λ x, Ord x) (∧ₑ₁ (∧ₑ₂ hME)) };
    have hlt : π (lt (f a) (f b)) { refine ltI (f a) (f b) hab_mem hOb };
    have hmeas : π (Pair a b ∈ measure A f)
      { refine ∧ₑ₂ (measure_iff A f a b) (∧ᵢ haA (∧ᵢ hbA hlt)) };
    refine ind_eq hzeq (λ w, w ∈ measure A f) hmeas }
end;

// wf_measure: wf(measure(A,f))
opaque symbol wf_measure (A : τ ι) (f : τ ι → τ ι) :
  π (wf_global (measure A f)) ≔
begin
  assume A f;
  rewrite (measure_eq_rvimage_Memrel A f);
  refine wf_rvimage A (Lambda A f) (Memrel (Collect (RepFun A f) (λ x, Ord x)))
    (wf_Memrel (Collect (RepFun A f) (λ x, Ord x)))
end;

// linear_measure
opaque symbol linear_measure (A : τ ι) (f : τ ι → τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Ord (f x))) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ A) → π (f x = f y) → π (x = y)) →
  π (linear A (measure A f)) ≔
begin
  assume A f hOrd hinj x hxA y hyA;
  have hOx : π (Ord (f x)) { refine hOrd x hxA };
  have hOy : π (Ord (f y)) { refine hOrd y hyA };
  // Linearity of ordinals on f(x), f(y).
  have hcase : π (f x ∈ f y ∨ f x = f y ∨ f y ∈ f x)
    { refine Ord_linear (f x) (f y) hOx hOy };
  refine ∨ₑ hcase _ _
  { assume h1;
    refine ∨ᵢ₁ (∧ₑ₂ (measure_iff A f x y)
      (∧ᵢ hxA (∧ᵢ hyA (ltI (f x) (f y) h1 hOy)))) }
  { assume h23;
    refine ∨ₑ h23 _ _
    { assume heq; refine ∨ᵢ₂ (∨ᵢ₁ (hinj x y hxA hyA heq)) }
    { assume h3;
      refine ∨ᵢ₂ (∨ᵢ₂ (∧ₑ₂ (measure_iff A f y x)
        (∧ᵢ hyA (∧ᵢ hxA (ltI (f y) (f x) h3 hOx))))) } }
end;

// wf_on_measure: wf[B](measure(A,f))
opaque symbol wf_on_measure (A B : τ ι) (f : τ ι → τ ι) :
  π (wf B (measure A f)) ≔
begin
  assume A B f;
  refine wf_imp_wf_on B (measure A f) (wf_measure A f)
end;

// well_ord_measure
opaque symbol well_ord_measure (A : τ ι) (f : τ ι → τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Ord (f x))) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ A) → π (f x = f y) → π (x = y)) →
  π (well_ord A (measure A f)) ≔
begin
  assume A f hOrd hinj;
  refine well_ordI A (measure A f)
    (wf_on_measure A A f)
    (linear_measure A f hOrd hinj)
end;

// measure_type: measure(A,f) ⊆ A*A
opaque symbol measure_type (A : τ ι) (f : τ ι → τ ι) :
  π (measure A f ⊆ Sigma A (λ _, A)) ≔
begin
  assume A f;
  refine Collect_subset (Sigma A (λ _, A)) _
end;

// --- Well-foundedness of Unions ---

// wf_on_Union
opaque symbol wf_on_Union (A r s : τ ι) (B : τ ι → τ ι) :
  π (wf A r) →
  (Π (a : τ ι), π (a ∈ A) → π (wf (B a) s)) →
  (Π (a u v : τ ι), π (Pair u v ∈ s) → π (v ∈ B a) → π (a ∈ A) →
     π (Bex A (λ ap, Pair ap a ∈ r ∧ u ∈ B ap) ∨ u ∈ B a)) →
  π (wf (Union (RepFun A B)) s) ≔
// Direct minimal-element proof: take the r-minimal a0 of
// W = {a∈A. ∃z∈Z. z∈B(a)}, then the s-minimal v0 of {v ∈ B(a0). v∈Z}.
// An s-predecessor u∈Z of v0 lands (by the hypothesis) either in some B(a')
// with <a',a0>∈r — putting a' into W below a0 — or in B(a0) below v0.
begin
  assume A r s B hwfA hwfB hstep Z hZsub hZne;
  have hWsub : π (Collect A (λ a, Bex Z (λ z, z ∈ B a)) ⊆ A)
    { assume w hw; refine CollectD1 w A (λ a, Bex Z (λ z, z ∈ B a)) hw };
  have hWne : π (Collect A (λ a, Bex Z (λ z, z ∈ B a)) ≠ empty)
    { assume heq;
      refine not_emptyE Z _ hZne _;
      assume z0 hz0;
      refine ∃ₑ (UnionE z0 (RepFun A B) (hZsub z0 hz0)) _; assume C hC;
      refine ∃ₑ (∧ₑ₁ (RepFun_iff C A B) (∧ₑ₁ hC)) _; assume a ha;
      have hz0Ba : π (z0 ∈ B a)
        { refine ind_eq (eq_sym (∧ₑ₂ ha)) (λ w, z0 ∈ w) (∧ₑ₂ hC) };
      refine equals0D (Collect A (λ a2, Bex Z (λ z, z ∈ B a2))) a heq
        (CollectI a A (λ a2, Bex Z (λ z, z ∈ B a2)) (∧ₑ₁ ha)
          (∃ᵢ z0 (∧ᵢ hz0 hz0Ba))) };
  have hminW : π (Bex (Collect A (λ a, Bex Z (λ z, z ∈ B a)))
                   (λ a, Ball (Collect A (λ a2, Bex Z (λ z, z ∈ B a2)))
                           (λ a2, Pair a2 a ∉ r)))
    { refine hwfA (Collect A (λ a, Bex Z (λ z, z ∈ B a))) hWsub hWne };
  refine ∃ₑ hminW _; assume a0 ha0;
  have ha0A : π (a0 ∈ A)
    { refine CollectD1 a0 A (λ a, Bex Z (λ z, z ∈ B a)) (∧ₑ₁ ha0) };
  have ha0ex : π (Bex Z (λ z, z ∈ B a0))
    { refine CollectD2 a0 A (λ a, Bex Z (λ z, z ∈ B a)) (∧ₑ₁ ha0) };
  have ha0min : π (Ball (Collect A (λ a2, Bex Z (λ z, z ∈ B a2)))
                    (λ a2, Pair a2 a0 ∉ r))
    { refine ∧ₑ₂ ha0 };
  have hVsub : π (Collect (B a0) (λ v, v ∈ Z) ⊆ B a0)
    { assume w hw; refine CollectD1 w (B a0) (λ v, v ∈ Z) hw };
  have hVne : π (Collect (B a0) (λ v, v ∈ Z) ≠ empty)
    { assume heq;
      refine ∃ₑ ha0ex _; assume z1 hz1;
      refine equals0D (Collect (B a0) (λ v, v ∈ Z)) z1 heq
        (CollectI z1 (B a0) (λ v, v ∈ Z) (∧ₑ₂ hz1) (∧ₑ₁ hz1)) };
  have hminV : π (Bex (Collect (B a0) (λ v, v ∈ Z))
                   (λ v, Ball (Collect (B a0) (λ v2, v2 ∈ Z)) (λ v2, Pair v2 v ∉ s)))
    { refine hwfB a0 ha0A (Collect (B a0) (λ v, v ∈ Z)) hVsub hVne };
  refine ∃ₑ hminV _; assume v0 hv0;
  have hv0B : π (v0 ∈ B a0)
    { refine CollectD1 v0 (B a0) (λ v, v ∈ Z) (∧ₑ₁ hv0) };
  have hv0Z : π (v0 ∈ Z)
    { refine CollectD2 v0 (B a0) (λ v, v ∈ Z) (∧ₑ₁ hv0) };
  have hv0min : π (Ball (Collect (B a0) (λ v2, v2 ∈ Z)) (λ v2, Pair v2 v0 ∉ s))
    { refine ∧ₑ₂ hv0 };
  refine ∃ᵢ v0 (∧ᵢ hv0Z _);
  assume u huZ hus;
  have hcase : π (Bex A (λ ap, Pair ap a0 ∈ r ∧ u ∈ B ap) ∨ u ∈ B a0)
    { refine hstep a0 u v0 hus hv0B ha0A };
  refine ∨ₑ hcase _ _
  { assume hex;
    refine ∃ₑ hex _; assume ap hap;
    refine ha0min ap (CollectI ap A (λ a2, Bex Z (λ z, z ∈ B a2)) (∧ₑ₁ hap)
      (∃ᵢ u (∧ᵢ huZ (∧ₑ₂ (∧ₑ₂ hap))))) (∧ₑ₁ (∧ₑ₂ hap)) }
  { assume huBa0;
    refine hv0min u (CollectI u (B a0) (λ v, v ∈ Z) huBa0 huZ) hus }
end;

// ===========================================================================
// Bijections involving Powersets
// ===========================================================================

// Pow_sum_bij
opaque symbol Pow_sum_bij (A B : τ ι) :
  π (Lambda (Pow (sum A B))
       (λ Z, Pair (Collect A (λ x, Inl x ∈ Z)) (Collect B (λ y, Inr y ∈ Z)))
       ∈ bij (Pow (sum A B)) (Sigma (Pow A) (λ _, Pow B))) ≔
begin
  assume A B;
  refine lam_bijective (Pow (sum A B)) (Sigma (Pow A) (λ _, Pow B))
    (λ Z, Pair (Collect A (λ x, Inl x ∈ Z)) (Collect B (λ y, Inr y ∈ Z)))
    (λ q, Un (RepFun (fst q) (λ x, Inl x)) (RepFun (snd q) (λ y, Inr y)))
    _ _ _ _
  { // forward ∈ codomain
    assume Z hZ;
    refine SigmaI (Collect A (λ x, Inl x ∈ Z)) (Collect B (λ y, Inr y ∈ Z))
      (Pow A) (λ _, Pow B) _ _
    { refine PowI (Collect A (λ x, Inl x ∈ Z)) A _;
      assume x hx; refine CollectD1 x A (λ x2, Inl x2 ∈ Z) hx }
    { refine PowI (Collect B (λ y, Inr y ∈ Z)) B _;
      assume y hy; refine CollectD1 y B (λ y2, Inr y2 ∈ Z) hy } }
  { // inverse ∈ domain
    assume q hq;
    have hXsub : π (fst q ⊆ A) { refine PowD (fst q) A (SigmaD1 q (Pow A) (λ _, Pow B) hq) };
    have hYsub : π (snd q ⊆ B) { refine PowD (snd q) B (SigmaD2 q (Pow A) (λ _, Pow B) hq) };
    refine PowI (Un (RepFun (fst q) (λ x, Inl x)) (RepFun (snd q) (λ y, Inr y))) (sum A B) _;
    assume w hw;
    refine ∨ₑ (UnE w (RepFun (fst q) (λ x, Inl x)) (RepFun (snd q) (λ y, Inr y)) hw) _ _
    { assume hw1;
      refine ∃ₑ (∧ₑ₁ (RepFun_iff w (fst q) (λ x, Inl x)) hw1) _;
      assume x hx;
      rewrite (∧ₑ₂ hx);
      refine InlI x A B (subsetD (fst q) A x hXsub (∧ₑ₁ hx)) }
    { assume hw2;
      refine ∃ₑ (∧ₑ₁ (RepFun_iff w (snd q) (λ y, Inr y)) hw2) _;
      assume y hy;
      rewrite (∧ₑ₂ hy);
      refine InrI y A B (subsetD (snd q) B y hYsub (∧ₑ₁ hy)) } }
  { // inv ∘ fwd = id
    assume Z hZ;
    have hZsub : π (Z ⊆ sum A B) { refine PowD Z (sum A B) hZ };
    rewrite (fst_conv (Collect A (λ x, Inl x ∈ Z)) (Collect B (λ y, Inr y ∈ Z)));
    rewrite (snd_conv (Collect A (λ x, Inl x ∈ Z)) (Collect B (λ y, Inr y ∈ Z)));
    refine equality_iffI (Un (RepFun (Collect A (λ x, Inl x ∈ Z)) (λ x, Inl x))
                             (RepFun (Collect B (λ y, Inr y ∈ Z)) (λ y, Inr y))) Z _;
    assume w;
    apply ∧ᵢ
    { assume hw;
      refine ∨ₑ (UnE w (RepFun (Collect A (λ x, Inl x ∈ Z)) (λ x, Inl x))
                       (RepFun (Collect B (λ y, Inr y ∈ Z)) (λ y, Inr y)) hw) _ _
      { assume hw1;
        refine ∃ₑ (∧ₑ₁ (RepFun_iff w (Collect A (λ x, Inl x ∈ Z)) (λ x, Inl x)) hw1) _;
        assume x hx;
        rewrite (∧ₑ₂ hx);
        refine CollectD2 x A (λ x2, Inl x2 ∈ Z) (∧ₑ₁ hx) }
      { assume hw2;
        refine ∃ₑ (∧ₑ₁ (RepFun_iff w (Collect B (λ y, Inr y ∈ Z)) (λ y, Inr y)) hw2) _;
        assume y hy;
        rewrite (∧ₑ₂ hy);
        refine CollectD2 y B (λ y2, Inr y2 ∈ Z) (∧ₑ₁ hy) } }
    { assume hwZ;
      refine sumE w A B _ (subsetD Z (sum A B) w hZsub hwZ) _ _
      { assume x hx he;
        rewrite he;
        have hInlZ : π (Inl x ∈ Z) { refine ind_eq (eq_sym he) (λ v, v ∈ Z) hwZ };
        refine UnI1 (Inl x) (RepFun (Collect A (λ x2, Inl x2 ∈ Z)) (λ x2, Inl x2))
                            (RepFun (Collect B (λ y, Inr y ∈ Z)) (λ y, Inr y))
          (RepFunI x (Collect A (λ x2, Inl x2 ∈ Z)) (λ x2, Inl x2)
            (CollectI x A (λ x2, Inl x2 ∈ Z) hx hInlZ)) }
      { assume y hy he;
        rewrite he;
        have hInrZ : π (Inr y ∈ Z) { refine ind_eq (eq_sym he) (λ v, v ∈ Z) hwZ };
        refine UnI2 (Inr y) (RepFun (Collect A (λ x, Inl x ∈ Z)) (λ x, Inl x))
                            (RepFun (Collect B (λ y2, Inr y2 ∈ Z)) (λ y2, Inr y2))
          (RepFunI y (Collect B (λ y2, Inr y2 ∈ Z)) (λ y2, Inr y2)
            (CollectI y B (λ y2, Inr y2 ∈ Z) hy hInrZ)) } } }
  { // fwd ∘ inv = id
    assume q hq;
    refine ∃ₑ (SigmaE q (Pow A) (λ _, Pow B) hq) _; assume X hX;
    refine ∃ₑ (∧ₑ₂ hX) _; assume Y hY;
    rewrite (∧ₑ₂ hY);
    rewrite (fst_conv X Y); rewrite (snd_conv X Y);
    have hXsub : π (X ⊆ A) { refine PowD X A (∧ₑ₁ hX) };
    have hYsub : π (Y ⊆ B) { refine PowD Y B (∧ₑ₁ hY) };
    have hXeq : π (Collect A (λ x, Inl x ∈ Un (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2)))
                   = X)
      { refine equality_iffI
          (Collect A (λ x, Inl x ∈ Un (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2)))) X _;
        assume x;
        apply ∧ᵢ
        { assume hx;
          have hmem : π (Inl x ∈ Un (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2)))
            { refine CollectD2 x A
                (λ x2, Inl x2 ∈ Un (RepFun X (λ x3, Inl x3)) (RepFun Y (λ y2, Inr y2))) hx };
          refine ∨ₑ (UnE (Inl x) (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2)) hmem) _ _
          { assume h1;
            refine ∃ₑ (∧ₑ₁ (RepFun_iff (Inl x) X (λ x2, Inl x2)) h1) _;
            assume x2 hx2;
            have hxeq : π (x = x2) { refine ∧ₑ₁ (Inl_iff x x2) (∧ₑ₂ hx2) };
            rewrite hxeq; refine ∧ₑ₁ hx2 }
          { assume h2;
            refine ∃ₑ (∧ₑ₁ (RepFun_iff (Inl x) Y (λ y2, Inr y2)) h2) _;
            assume y2 hy2;
            refine ⊥ₑ (∧ₑ₁ (Inl_Inr_iff x y2) (∧ₑ₂ hy2)) } }
        { assume hxX;
          refine CollectI x A
            (λ x2, Inl x2 ∈ Un (RepFun X (λ x3, Inl x3)) (RepFun Y (λ y2, Inr y2)))
            (subsetD X A x hXsub hxX)
            (UnI1 (Inl x) (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2))
              (RepFunI x X (λ x2, Inl x2) hxX)) } };
    have hYeq : π (Collect B (λ y, Inr y ∈ Un (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2)))
                   = Y)
      { refine equality_iffI
          (Collect B (λ y, Inr y ∈ Un (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2)))) Y _;
        assume y;
        apply ∧ᵢ
        { assume hy;
          have hmem : π (Inr y ∈ Un (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2)))
            { refine CollectD2 y B
                (λ y2, Inr y2 ∈ Un (RepFun X (λ x3, Inl x3)) (RepFun Y (λ y3, Inr y3))) hy };
          refine ∨ₑ (UnE (Inr y) (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2)) hmem) _ _
          { assume h1;
            refine ∃ₑ (∧ₑ₁ (RepFun_iff (Inr y) X (λ x2, Inl x2)) h1) _;
            assume x2 hx2;
            refine ⊥ₑ (∧ₑ₁ (Inl_Inr_iff x2 y) (eq_sym (∧ₑ₂ hx2))) }
          { assume h2;
            refine ∃ₑ (∧ₑ₁ (RepFun_iff (Inr y) Y (λ y2, Inr y2)) h2) _;
            assume y2 hy2;
            have hyeq : π (y = y2) { refine ∧ₑ₁ (Inr_iff y y2) (∧ₑ₂ hy2) };
            rewrite hyeq; refine ∧ₑ₁ hy2 } }
        { assume hyY;
          refine CollectI y B
            (λ y2, Inr y2 ∈ Un (RepFun X (λ x3, Inl x3)) (RepFun Y (λ y3, Inr y3)))
            (subsetD Y B y hYsub hyY)
            (UnI2 (Inr y) (RepFun X (λ x2, Inl x2)) (RepFun Y (λ y2, Inr y2))
              (RepFunI y Y (λ y2, Inr y2) hyY)) } };
    rewrite hXeq; rewrite hYeq;
    reflexivity }
end;

// Typing of the inverse map f ↦ ⋃x∈A. ⋃y∈f`x. {⟨x,y⟩}.
private opaque symbol Pow_Sigma_bij_d_type (A : τ ι) (B : τ ι → τ ι) (f : τ ι) :
  π (f ∈ Pi A (λ x, Pow (B x))) →
  π (Union (RepFun A (λ x, RepFun (fapply f x) (λ y, Pair x y))) ∈ Pow (Sigma A B)) ≔
begin
  assume A B f hf;
  refine PowI (Union (RepFun A (λ x, RepFun (fapply f x) (λ y, Pair x y)))) (Sigma A B) _;
  assume w hw;
  refine ∃ₑ (UnionE w (RepFun A (λ x, RepFun (fapply f x) (λ y, Pair x y))) hw) _;
  assume S hS;
  refine ∃ₑ (∧ₑ₁ (RepFun_iff S A (λ x, RepFun (fapply f x) (λ y, Pair x y))) (∧ₑ₁ hS)) _;
  assume x hx;
  have hwS : π (w ∈ RepFun (fapply f x) (λ y, Pair x y))
    { refine ind_eq (eq_sym (∧ₑ₂ hx)) (λ t, w ∈ t) (∧ₑ₂ hS) };
  refine ∃ₑ (∧ₑ₁ (RepFun_iff w (fapply f x) (λ y, Pair x y)) hwS) _;
  assume y hy;
  rewrite (∧ₑ₂ hy);
  refine SigmaI x y A B (∧ₑ₁ hx)
    (subsetD (fapply f x) (B x) y
      (PowD (fapply f x) (B x) (fapply_type f x A (λ x2, Pow (B x2)) hf (∧ₑ₁ hx)))
      (∧ₑ₁ hy))
end;

// Pow_Sigma_bij
// Isabelle's r``{x} is the RELATIONAL image, so the faithful statement uses
// rel_image_sing; ZF.func's Image (function image) would make this false for
// multi-valued r ∈ Pow(Sigma(A,B)).
opaque symbol Pow_Sigma_bij (A : τ ι) (B : τ ι → τ ι) :
  π (Lambda (Pow (Sigma A B)) (λ r, Lambda A (λ x, rel_image_sing r x))
       ∈ bij (Pow (Sigma A B)) (Pi A (λ x, Pow (B x)))) ≔
begin
  assume A B;
  refine lam_bijective (Pow (Sigma A B)) (Pi A (λ x, Pow (B x)))
    (λ r, Lambda A (λ x, rel_image_sing r x))
    (λ f, Union (RepFun A (λ x, RepFun (fapply f x) (λ y, Pair x y))))
    _ _ _ _
  { // forward ∈ codomain
    assume r hr;
    refine lam_type A (λ x, rel_image_sing r x) (λ x, Pow (B x)) _;
    assume x hx;
    refine PowI (rel_image_sing r x) (B x) _;
    assume y hy;
    have hpair : π (Pair x y ∈ Sigma A B)
      { refine subsetD r (Sigma A B) (Pair x y) (PowD r (Sigma A B) hr)
          (rel_image_singD x y r hy) };
    have h2 : π (y ∈ B (fst (Pair x y)))
      { refine ind_eq (eq_sym (snd_conv x y)) (λ w, w ∈ B (fst (Pair x y)))
          (SigmaD2 (Pair x y) A B hpair) };
    refine ind_eq (eq_sym (fst_conv x y)) (λ w, y ∈ B w) h2 }
  { // inverse ∈ domain
    assume f hf;
    refine Pow_Sigma_bij_d_type A B f hf }
  { // inv ∘ fwd = id
    assume r hr;
    refine equality_iffI (Union (RepFun A (λ x, RepFun
        (fapply (Lambda A (λ x2, rel_image_sing r x2)) x) (λ y, Pair x y)))) r _;
    assume w;
    apply ∧ᵢ
    { assume hw;
      refine ∃ₑ (UnionE w (RepFun A (λ x, RepFun
          (fapply (Lambda A (λ x2, rel_image_sing r x2)) x) (λ y, Pair x y))) hw) _;
      assume S hS;
      refine ∃ₑ (∧ₑ₁ (RepFun_iff S A (λ x, RepFun
          (fapply (Lambda A (λ x2, rel_image_sing r x2)) x) (λ y, Pair x y))) (∧ₑ₁ hS)) _;
      assume x hx;
      have hwS : π (w ∈ RepFun (fapply (Lambda A (λ x2, rel_image_sing r x2)) x) (λ y, Pair x y))
        { refine ind_eq (eq_sym (∧ₑ₂ hx)) (λ t, w ∈ t) (∧ₑ₂ hS) };
      refine ∃ₑ (∧ₑ₁ (RepFun_iff w (fapply (Lambda A (λ x2, rel_image_sing r x2)) x)
          (λ y, Pair x y)) hwS) _;
      assume y hy;
      have hyr : π (y ∈ rel_image_sing r x)
        { refine ind_eq (eq_sym (beta A (λ x2, rel_image_sing r x2) x (∧ₑ₁ hx)))
            (λ t, y ∈ t) (∧ₑ₁ hy) };
      rewrite (∧ₑ₂ hy);
      refine rel_image_singD x y r hyr }
    { assume hwr;
      have hwSig : π (w ∈ Sigma A B)
        { refine subsetD r (Sigma A B) w (PowD r (Sigma A B) hr) hwr };
      refine ∃ₑ (SigmaE w A B hwSig) _; assume x hx;
      refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
      have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
      have hpr : π (Pair x y ∈ r)
        { refine ind_eq (eq_sym (∧ₑ₂ hy)) (λ t, t ∈ r) hwr };
      have hyfx : π (y ∈ fapply (Lambda A (λ x2, rel_image_sing r x2)) x)
        { refine ind_eq (beta A (λ x2, rel_image_sing r x2) x hxA)
            (λ t, y ∈ t) (rel_image_singI x y r hpr) };
      rewrite (∧ₑ₂ hy);
      refine UnionI (Pair x y)
        (RepFun (fapply (Lambda A (λ x2, rel_image_sing r x2)) x) (λ y2, Pair x y2))
        (RepFun A (λ x2, RepFun (fapply (Lambda A (λ x3, rel_image_sing r x3)) x2)
                     (λ y2, Pair x2 y2)))
        (RepFunI y (fapply (Lambda A (λ x2, rel_image_sing r x2)) x) (λ y2, Pair x y2) hyfx)
        (RepFunI x A (λ x2, RepFun (fapply (Lambda A (λ x3, rel_image_sing r x3)) x2)
                        (λ y2, Pair x2 y2)) hxA) } }
  { // fwd ∘ inv = id
    assume f hf;
    have hDsub : π (Union (RepFun A (λ x, RepFun (fapply f x) (λ y, Pair x y))) ⊆ Sigma A B)
      { refine PowD (Union (RepFun A (λ x, RepFun (fapply f x) (λ y, Pair x y)))) (Sigma A B)
          (Pow_Sigma_bij_d_type A B f hf) };
    have hlam : π (Lambda A (λ x, rel_image_sing
          (Union (RepFun A (λ x2, RepFun (fapply f x2) (λ y, Pair x2 y)))) x)
        ∈ Pi A (λ x, Pow (B x)))
      { refine lam_type A (λ x, rel_image_sing
            (Union (RepFun A (λ x2, RepFun (fapply f x2) (λ y, Pair x2 y)))) x)
          (λ x, Pow (B x)) _;
        assume x hx;
        refine PowI (rel_image_sing
            (Union (RepFun A (λ x2, RepFun (fapply f x2) (λ y, Pair x2 y)))) x) (B x) _;
        assume y hy;
        have hpair : π (Pair x y ∈ Sigma A B)
          { refine subsetD (Union (RepFun A (λ x2, RepFun (fapply f x2) (λ y2, Pair x2 y2))))
              (Sigma A B) (Pair x y) hDsub
              (rel_image_singD x y
                (Union (RepFun A (λ x2, RepFun (fapply f x2) (λ y2, Pair x2 y2)))) hy) };
        have h2 : π (y ∈ B (fst (Pair x y)))
          { refine ind_eq (eq_sym (snd_conv x y)) (λ w, w ∈ B (fst (Pair x y)))
              (SigmaD2 (Pair x y) A B hpair) };
        refine ind_eq (eq_sym (fst_conv x y)) (λ w, y ∈ B w) h2 };
    have hall : π (Ball A (λ x, fapply (Lambda A (λ x2, rel_image_sing
          (Union (RepFun A (λ x3, RepFun (fapply f x3) (λ y, Pair x3 y)))) x2)) x
        = fapply f x))
      { assume x hx;
        rewrite (beta A (λ x2, rel_image_sing
            (Union (RepFun A (λ x3, RepFun (fapply f x3) (λ y, Pair x3 y)))) x2) x hx);
        refine equality_iffI (rel_image_sing
            (Union (RepFun A (λ x3, RepFun (fapply f x3) (λ y, Pair x3 y)))) x)
          (fapply f x) _;
        assume y;
        apply ∧ᵢ
        { assume hy;
          have hpD : π (Pair x y ∈ Union (RepFun A (λ x3, RepFun (fapply f x3) (λ y2, Pair x3 y2))))
            { refine rel_image_singD x y
                (Union (RepFun A (λ x3, RepFun (fapply f x3) (λ y2, Pair x3 y2)))) hy };
          refine ∃ₑ (UnionE (Pair x y)
              (RepFun A (λ x3, RepFun (fapply f x3) (λ y2, Pair x3 y2))) hpD) _;
          assume S hS;
          refine ∃ₑ (∧ₑ₁ (RepFun_iff S A (λ x3, RepFun (fapply f x3) (λ y2, Pair x3 y2)))
              (∧ₑ₁ hS)) _;
          assume x2 hx2;
          have hpS : π (Pair x y ∈ RepFun (fapply f x2) (λ y2, Pair x2 y2))
            { refine ind_eq (eq_sym (∧ₑ₂ hx2)) (λ t, Pair x y ∈ t) (∧ₑ₂ hS) };
          refine ∃ₑ (∧ₑ₁ (RepFun_iff (Pair x y) (fapply f x2) (λ y2, Pair x2 y2)) hpS) _;
          assume y2 hy2;
          have hxeq : π (x = x2) { refine Pair_inject1 x y x2 y2 (∧ₑ₂ hy2) };
          have hyeq : π (y = y2) { refine Pair_inject2 x y x2 y2 (∧ₑ₂ hy2) };
          rewrite hxeq; rewrite hyeq;
          refine ∧ₑ₁ hy2 }
        { assume hy;
          refine rel_image_singI x y
            (Union (RepFun A (λ x3, RepFun (fapply f x3) (λ y2, Pair x3 y2)))) _;
          refine UnionI (Pair x y) (RepFun (fapply f x) (λ y2, Pair x y2))
            (RepFun A (λ x3, RepFun (fapply f x3) (λ y2, Pair x3 y2)))
            (RepFunI y (fapply f x) (λ y2, Pair x y2) hy)
            (RepFunI x A (λ x3, RepFun (fapply f x3) (λ y2, Pair x3 y2)) hx) } };
    refine fun_extension (Lambda A (λ x, rel_image_sing
        (Union (RepFun A (λ x2, RepFun (fapply f x2) (λ y, Pair x2 y)))) x)) f A
      (λ x, Pow (B x)) (λ x, Pow (B x)) hlam hf hall }
end;
