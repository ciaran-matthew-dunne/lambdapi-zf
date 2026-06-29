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

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt
             Stdlib.Epsilon;
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
opaque symbol wf_on_radd (A r B s : τ ι) :
  π (wf A r) → π (wf B s) → π (wf (sum A B) (radd A r B s)) ≔
// TODO: needs wf_onI2-style introduction + nested wf_on_induct (missing infra).
begin
  admit
end;

opaque symbol wf_radd (r s : τ ι) :
  π (wf_global r) → π (wf_global s) →
  π (wf_global (radd (field r) r (field s) s)) ≔
// TODO: via wf_iff_wf_on_field + wf_on_subset_A field_radd + wf_on_radd.
begin
  admit
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
// TODO: lam_bijective with inverse case(λx.Inl(converse f`x), λy.Inr(converse g`y)).
begin
  admit
end;

// sum_ord_iso_cong
opaque symbol sum_ord_iso_cong (f g A r Ap rp B s Bp sp : τ ι) :
  π (f ∈ ord_iso A r Ap rp) → π (g ∈ ord_iso B s Bp sp) →
  π (Lambda (sum A B) (λ z, case_sum (λ x, Inl (fapply f x)) (λ y, Inr (fapply g y)) z)
       ∈ ord_iso (sum A B) (radd A r B s) (sum Ap Bp) (radd Ap rp Bp sp)) ≔
// TODO: ord_isoI on sum_bij; order condition via radd rewrite rules.
begin
  admit
end;

// sum_disjoint_bij: A∩B=0 → (λz∈A+B. case(λx.x,λy.y,z)) ∈ bij(A+B, A∪B)
opaque symbol sum_disjoint_bij (A B : τ ι) :
  π (Int A B = empty) →
  π (Lambda (sum A B) (λ z, case_sum (λ x, x) (λ y, y) z) ∈ bij (sum A B) (Un A B)) ≔
// TODO: lam_bijective with inverse (λz. if z∈A then Inl z else Inr z).
begin
  admit
end;

// --- Associativity ---

// sum_assoc_bij
opaque symbol sum_assoc_bij (A B C : τ ι) :
  π (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x, Inl x) (λ y, Inr (Inl y))) (λ y, Inr (Inr y)) z)
       ∈ bij (sum (sum A B) C) (sum A (sum B C))) ≔
// TODO: lam_bijective with the obvious inverse.
begin
  admit
end;

// sum_assoc_ord_iso
opaque symbol sum_assoc_ord_iso (A r B s C t : τ ι) :
  π (Lambda (sum (sum A B) C)
       (λ z, case_sum (case_sum (λ x, Inl x) (λ y, Inr (Inl y))) (λ y, Inr (Inr y)) z)
       ∈ ord_iso (sum (sum A B) C) (radd (sum A B) (radd A r B s) C t)
                 (sum A (sum B C)) (radd A r (sum B C) (radd B s C t))) ≔
// TODO: ord_isoI on sum_assoc_bij.
begin
  admit
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
opaque symbol wf_on_rmult (A r B s : τ ι) :
  π (wf A r) → π (wf B s) → π (wf (Sigma A (λ _, B)) (rmult A r B s)) ≔
// TODO: nested wf_on_induct (missing infra).
begin
  admit
end;

// wf_rmult
opaque symbol wf_rmult (r s : τ ι) :
  π (wf_global r) → π (wf_global s) →
  π (wf_global (rmult (field r) r (field s) s)) ≔
// TODO: via wf_iff_wf_on_field + field_rmult + wf_on_rmult.
begin
  admit
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
// TODO: lam_bijective with inverse <converse f`x, converse g`y>.
begin
  admit
end;

// prod_ord_iso_cong
opaque symbol prod_ord_iso_cong (f g A r Ap rp B s Bp sp : τ ι) :
  π (f ∈ ord_iso A r Ap rp) → π (g ∈ ord_iso B s Bp sp) →
  π (Lambda (Sigma A (λ _, B)) (λ p, Pair (fapply f (fst p)) (fapply g (snd p)))
       ∈ ord_iso (Sigma A (λ _, B)) (rmult A r B s)
                 (Sigma Ap (λ _, Bp)) (rmult Ap rp Bp sp)) ≔
// TODO: ord_isoI on prod_bij; order condition via rmult_iff + inj_apply_equality.
begin
  admit
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
// TODO: ord_isoI on singleton_prod_bij; uses well_ord_is_wf + wf_on_not_refl.
begin
  admit
end;

// prod_sum_singleton_bij: a∉C → (λx∈C*B+D. case(λx.x, λy.<a,y>, x)) ∈ bij(C*B+D, C*B∪{a}*D)
opaque symbol prod_sum_singleton_bij (a B C D : τ ι) :
  π (a ∉ C) →
  π (Lambda (sum (Sigma C (λ _, B)) D) (λ x, case_sum (λ x, x) (λ y, Pair a y) x)
       ∈ bij (sum (Sigma C (λ _, B)) D)
             (Un (Sigma C (λ _, B)) (Sigma (singleton a) (λ _, D)))) ≔
// TODO: composite bijection (id_bij/sum_bij/comp_bij/singleton_prod_bij/
//       sum_disjoint_bij); needs comp_lam / case_case (missing infra).
begin
  admit
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
// TODO: ord_isoI on prod_sum_singleton_bij; uses pred_iff + wf_on_not_refl/asym.
begin
  admit
end;

// --- Distributive law ---

// sum_prod_distrib_bij
opaque symbol sum_prod_distrib_bij (A B C : τ ι) :
  π (Lambda (Sigma (sum A B) (λ _, C))
       (λ p, case_sum (λ y, Inl (Pair y (snd p))) (λ y, Inr (Pair y (snd p))) (fst p))
       ∈ bij (Sigma (sum A B) (λ _, C))
             (sum (Sigma A (λ _, C)) (Sigma B (λ _, C)))) ≔
// TODO: lam_bijective with inverse case(λ<x,y>.<Inl x,y>, λ<x,y>.<Inr x,y>).
begin
  admit
end;

// sum_prod_distrib_ord_iso
opaque symbol sum_prod_distrib_ord_iso (A r B s C t : τ ι) :
  π (Lambda (Sigma (sum A B) (λ _, C))
       (λ p, case_sum (λ y, Inl (Pair y (snd p))) (λ y, Inr (Pair y (snd p))) (fst p))
       ∈ ord_iso (Sigma (sum A B) (λ _, C)) (rmult (sum A B) (radd A r B s) C t)
                 (sum (Sigma A (λ _, C)) (Sigma B (λ _, C)))
                 (radd (Sigma A (λ _, C)) (rmult A r C t)
                       (Sigma B (λ _, C)) (rmult B s C t))) ≔
// TODO: ord_isoI on sum_prod_distrib_bij.
begin
  admit
end;

// --- Associativity ---

// prod_assoc_bij
opaque symbol prod_assoc_bij (A B C : τ ι) :
  π (Lambda (Sigma (Sigma A (λ _, B)) (λ _, C))
       (λ p, Pair (fst (fst p)) (Pair (snd (fst p)) (snd p)))
       ∈ bij (Sigma (Sigma A (λ _, B)) (λ _, C)) (Sigma A (λ _, Sigma B (λ _, C)))) ≔
// TODO: lam_bijective with inverse <<x,y>,z>.
begin
  admit
end;

// prod_assoc_ord_iso
opaque symbol prod_assoc_ord_iso (A r B s C t : τ ι) :
  π (Lambda (Sigma (Sigma A (λ _, B)) (λ _, C))
       (λ p, Pair (fst (fst p)) (Pair (snd (fst p)) (snd p)))
       ∈ ord_iso (Sigma (Sigma A (λ _, B)) (λ _, C)) (rmult (Sigma A (λ _, B)) (rmult A r B s) C t)
                 (Sigma A (λ _, Sigma B (λ _, C))) (rmult A r (Sigma B (λ _, C)) (rmult B s C t))) ≔
// TODO: ord_isoI on prod_assoc_bij.
begin
  admit
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
// TODO (Stage B): equality_iffI + rvimage_iff + converseI/converseD.
begin
  admit
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
// TODO: wf_eq_minimal-style argument (missing infra).
begin
  admit
end;

// wf_on_rvimage: f∈A→B → wf[B](r) → wf[A](rvimage(A,f,r))
opaque symbol wf_on_rvimage (A B f r : τ ι) :
  π (f ∈ Pi A (λ _, B)) → π (wf B r) → π (wf A (rvimage A f r)) ≔
// TODO: wf_on_induct on f`y (missing infra).
begin
  admit
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
// TODO: wfrec_eq + beta on the recursion body.
begin
  admit
end;

// Ord_wfrank: wf(r) → Ord(wfrank(r,a))
opaque symbol Ord_wfrank (r a : τ ι) :
  π (wf_global r) → π (Ord (wfrank r a)) ≔
// TODO: wf_induct on a + Ord_succ/Ord_UN.
begin
  admit
end;

// wfrank_lt: wf(r) → <a,b>∈r → wfrank(r,a) < wfrank(r,b)
opaque symbol wfrank_lt (r a b : τ ι) :
  π (wf_global r) → π (Pair a b ∈ r) → π (lt (wfrank r a) (wfrank r b)) ≔
// TODO: unfold wfrank at b, UN_I/ltI.
begin
  admit
end;

// Ord_wftype: wf(r) → Ord(wftype(r))
opaque symbol Ord_wftype (r : τ ι) :
  π (wf_global r) → π (Ord (wftype r)) ≔
// TODO: wftype_def + Ord_wfrank + Ord_UN.
begin
  admit
end;

// wftypeI: wf(r) → x∈field(r) → wfrank(r,x) ∈ wftype(r)
opaque symbol wftypeI (r x : τ ι) :
  π (wf_global r) → π (x ∈ field r) → π (wfrank r x ∈ wftype r) ≔
// TODO: wftype_def + wfrank_lt [THEN ltD].
begin
  admit
end;

// wf_imp_subset_rvimage:
//   wf(r) → r⊆A*A → ∃i f. Ord(i) ∧ r ⊆ rvimage(A,f,Memrel(i))
opaque symbol wf_imp_subset_rvimage (r A : τ ι) :
  π (wf_global r) → π (r ⊆ Sigma A (λ _, A)) →
  π (`∃ (i : τ ι), `∃ (f : τ ι),
       Ord i ∧ r ⊆ rvimage A f (Memrel i)) ≔
// TODO: witness i=wftype(r), f=λx∈A. wfrank(r,x); uses wftypeI + wfrank_lt.
begin
  admit
end;

// wf_iff_subset_rvimage:
//   relation(r) → (wf(r) ⟷ ∃i f A. Ord(i) ∧ r ⊆ rvimage(A,f,Memrel(i)))
opaque symbol wf_iff_subset_rvimage (r : τ ι) :
  π (relation r) →
  π (wf_global r ⇔
     `∃ (i : τ ι), `∃ (f : τ ι), `∃ (A : τ ι),
        Ord i ∧ r ⊆ rvimage A f (Memrel i)) ≔
// TODO: wf_imp_subset_rvimage + wf_rvimage_Ord [THEN wf_subset].
begin
  admit
end;

// ===========================================================================
// Other Results
// ===========================================================================

// wf_times: A∩B=0 → wf(A*B)
opaque symbol wf_times (A B : τ ι) :
  π (Int A B = empty) → π (wf_global (Sigma A (λ _, B))) ≔
// TODO: from wf_global def; any pair in A*B has fst∈A, but minimal element of
//       a nonempty Z exists since A∩B=0 prevents chains.
begin
  admit
end;

// wf_Un: range(r)∩domain(s)=0 → wf(r) → wf(s) → wf(r∪s)
opaque symbol wf_Un (r s : τ ι) :
  π (Int (range r) (domain s) = empty) →
  π (wf_global r) → π (wf_global s) → π (wf_global (Un r s)) ≔
// TODO: minimal-element bookkeeping across the two relations.
begin
  admit
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

// measure_eq_rvimage_Memrel:
//   measure(A,f) = rvimage(A, Lambda(A,f), Memrel(Collect(RepFun(A,f),Ord)))
opaque symbol measure_eq_rvimage_Memrel (A : τ ι) (f : τ ι → τ ι) :
  π (measure A f
     = rvimage A (Lambda A f) (Memrel (Collect (RepFun A f) (λ x, Ord x)))) ≔
// TODO: equality_iffI + measure_def/rvimage_def/Memrel_iff + beta + lt_def.
begin
  admit
end;

// wf_measure: wf(measure(A,f))
opaque symbol wf_measure (A : τ ι) (f : τ ι → τ ι) :
  π (wf_global (measure A f)) ≔
// TODO: measure_eq_rvimage_Memrel + wf_Memrel + wf_rvimage.
begin
  admit
end;

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

// linear_measure
opaque symbol linear_measure (A : τ ι) (f : τ ι → τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Ord (f x))) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ A) → π (f x = f y) → π (x = y)) →
  π (linear A (measure A f)) ≔
// TODO: Ord_linear_lt on f(x),f(y) (Ord_linear_lt not yet ported).
begin
  admit
end;

// wf_on_measure: wf[B](measure(A,f))
opaque symbol wf_on_measure (A B : τ ι) (f : τ ι → τ ι) :
  π (wf B (measure A f)) ≔
// TODO: wf_imp_wf_on of wf_measure (wf_imp_wf_on missing).
begin
  admit
end;

// well_ord_measure
opaque symbol well_ord_measure (A : τ ι) (f : τ ι → τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Ord (f x))) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ A) → π (f x = f y) → π (x = y)) →
  π (well_ord A (measure A f)) ≔
// TODO: well_ordI from wf_on_measure + linear_measure.
begin
  admit
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
// TODO: nested wf_on_induct over r then s (missing infra).
begin
  admit
end;

// ===========================================================================
// Bijections involving Powersets
// ===========================================================================

// Pow_sum_bij
opaque symbol Pow_sum_bij (A B : τ ι) :
  π (Lambda (Pow (sum A B))
       (λ Z, Pair (Collect A (λ x, Inl x ∈ Z)) (Collect B (λ y, Inr y ∈ Z)))
       ∈ bij (Pow (sum A B)) (Sigma (Pow A) (λ _, Pow B))) ≔
// TODO: lam_bijective with inverse <X,Y>. {Inl x. x∈X} ∪ {Inr y. y∈Y}.
begin
  admit
end;

// Pow_Sigma_bij
opaque symbol Pow_Sigma_bij (A : τ ι) (B : τ ι → τ ι) :
  π (Lambda (Pow (Sigma A B)) (λ r, Lambda A (λ x, Image r (singleton x)))
       ∈ bij (Pow (Sigma A B)) (Pi A (λ x, Pow (B x)))) ≔
// TODO: lam_bijective with inverse f. ⋃x∈A.⋃y∈f`x.{<x,y>}; fun_extension.
begin
  admit
end;
