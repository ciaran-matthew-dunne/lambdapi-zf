// QPair: Quine-inspired ordered pairs and disjoint sums
//
// Isabelle source: QPair.thy
// Quine pairs are DISJOINT SUMS: <a;b> ≡ a+b (the `sum` of Sum.lp).
// Hence QPair = sum, and all QPair-level facts (QPair_iff, QPair_inject,
// QPair_empty, QPair_mono) reduce to the corresponding `sum` facts that are
// already proved in Sum.lp.
//
// The QSigma / qfst / qsnd / qsplit layer mirrors pair.lp's Sigma / fst / snd /
// split (projections are `The`-based, so they do NOT reduce — rewrite with
// qfst_conv / qsnd_conv).  The QInl / QInr / qsum / qcase / Part-QInl layer
// mirrors Sum.lp's Inl / Inr / sum / case / Part one level up.
//
// Faithfulness note on qsplit: Isabelle's `qsplit :: [[i,i]⇒'a,i]⇒'a` is sort
// polymorphic and is used at BOTH result sort i (qsplit/qsplit_type/expand_qsplit
// and qcase) and result sort o (qsplitI/qsplitE/qsplitD).  Lambdapi lacks that
// i/o polymorphism, so it is rendered by two symbols: `qsplit` (result τ ι) and
// `qsplit_pred` (result Prop), both faithful to qsplit(c,p) ≡ c(qfst p, qsnd p).

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt
             Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.Bool_ZF ZF.Sum;

// ===========================================================================
// Quine ordered pairing: <a;b> ≡ a+b
// ===========================================================================

symbol QPair (a b : τ ι) : τ ι ≔ sum a b;

// qfst(p) = THE a. ∃b. p = <a;b>      qsnd(p) = THE b. ∃a. p = <a;b>
symbol qfst (p : τ ι) : τ ι ≔ The (λ a, `∃ (b : τ ι), p = QPair a b);
symbol qsnd (p : τ ι) : τ ι ≔ The (λ b, `∃ (a : τ ι), p = QPair a b);

// ---------------------------------------------------------------------------
// Lemmas showing <a;b> uniquely determines a and b
// ---------------------------------------------------------------------------

// QPair_empty: <0;0> = 0   (since sum 0 0 = 0)
opaque symbol QPair_empty : π (QPair empty empty = empty) ≔
begin
  refine sum_empty
end;

// QPair_iff: <a;b> = <c;d> ⟷ a=c ∧ b=d   (it is sum_equal_iff)
opaque symbol QPair_iff (a b c d : τ ι) :
  π (QPair a b = QPair c d ⇔ (a = c ∧ b = d)) ≔
begin
  assume a b c d;
  refine sum_equal_iff a b c d
end;

// QPair_inject1: <a;b> = <c;d> ⟹ a=c
opaque symbol QPair_inject1 (a b c d : τ ι) :
  π (QPair a b = QPair c d) → π (a = c) ≔
begin
  assume a b c d h;
  refine ∧ₑ₁ (∧ₑ₁ (QPair_iff a b c d) h)
end;

// QPair_inject2: <a;b> = <c;d> ⟹ b=d
opaque symbol QPair_inject2 (a b c d : τ ι) :
  π (QPair a b = QPair c d) → π (b = d) ≔
begin
  assume a b c d h;
  refine ∧ₑ₂ (∧ₑ₁ (QPair_iff a b c d) h)
end;

// Combined injectivity
opaque symbol QPair_inject (a b c d : τ ι) :
  π (QPair a b = QPair c d) → π (a = c ∧ b = d) ≔
begin
  assume a b c d h;
  refine ∧ₑ₁ (QPair_iff a b c d) h
end;

// qfst_conv: qfst(<a;b>) = a
opaque symbol qfst_conv (a b : τ ι) : π (qfst (QPair a b) = a) ≔
begin
  assume a b;
  refine the_equality (λ x, `∃ (y : τ ι), QPair a b = QPair x y) a _ _
  { refine ∃ᵢ b (eq_refl (QPair a b)) }
  { assume x hx;
    refine ∃ₑ hx _;
    assume y hxy;
    refine eq_sym (QPair_inject1 a b x y hxy) }
end;

// qsnd_conv: qsnd(<a;b>) = b
opaque symbol qsnd_conv (a b : τ ι) : π (qsnd (QPair a b) = b) ≔
begin
  assume a b;
  refine the_equality (λ y, `∃ (x : τ ι), QPair a b = QPair x y) b _ _
  { refine ∃ᵢ a (eq_refl (QPair a b)) }
  { assume y hy;
    refine ∃ₑ hy _;
    assume x hxy;
    refine eq_sym (QPair_inject2 a b x y hxy) }
end;

// ===========================================================================
// QSigma: disjoint union of a family of sets (generalizes Cartesian product)
//   QSigma(A,B) = ⋃x∈A. ⋃y∈B(x). {<x;y>}
// ===========================================================================

symbol QSigma (A : τ ι) (B : τ ι → τ ι) : τ ι ≔
  Union (RepFun A (λ x, RepFun (B x) (λ y, QPair x y)));

// QSigmaI: a ∈ A → b ∈ B(a) → <a;b> ∈ QSigma(A,B)
opaque symbol QSigmaI (a b A : τ ι) (B : τ ι → τ ι) :
  π (a ∈ A) → π (b ∈ B a) → π (QPair a b ∈ QSigma A B) ≔
begin
  assume a b A B haA hbB;
  have h1 : π (QPair a b ∈ RepFun (B a) (λ z, QPair a z))
    { refine RepFunI b (B a) (λ z, QPair a z) hbB };
  have h2 : π (RepFun (B a) (λ z, QPair a z) ∈
               RepFun A (λ w, RepFun (B w) (λ z, QPair w z)))
    { refine RepFunI a A (λ w, RepFun (B w) (λ z, QPair w z)) haA };
  refine UnionI (QPair a b) (RepFun (B a) (λ z, QPair a z))
    (RepFun A (λ w, RepFun (B w) (λ z, QPair w z))) h1 h2
end;

// QSigmaE: c ∈ QSigma(A,B) → (⋀x y. x∈A → y∈B(x) → c=<x;y> → P) → P
opaque symbol QSigmaE (p A : τ ι) (B : τ ι → τ ι) (P : Prop) :
  π (p ∈ QSigma A B) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ B x) → π (p = QPair x y) → π P) →
  π P ≔
begin
  assume p A B P hp hk;
  have hbex : π (Bex (RepFun A (λ x, RepFun (B x) (λ y, QPair x y))) (λ C, p ∈ C))
    { refine UnionE p (RepFun A (λ x, RepFun (B x) (λ y, QPair x y))) hp };
  refine ∃ₑ hbex _;
  assume C hC;
  have hCmem : π (C ∈ RepFun A (λ x, RepFun (B x) (λ y, QPair x y))) { refine ∧ₑ₁ hC };
  have hpC : π (p ∈ C) { refine ∧ₑ₂ hC };
  have hbex2 : π (Bex A (λ x, C = RepFun (B x) (λ y, QPair x y)))
    { refine ∧ₑ₁ (RepFun_iff C A (λ x, RepFun (B x) (λ y, QPair x y))) hCmem };
  refine ∃ₑ hbex2 _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hCeq : π (C = RepFun (B x) (λ y, QPair x y)) { refine ∧ₑ₂ hx };
  have hpRF : π (p ∈ RepFun (B x) (λ y, QPair x y))
    { refine ind_eq (eq_sym hCeq) (λ s, p ∈ s) hpC };
  have hbex3 : π (Bex (B x) (λ y, p = QPair x y))
    { refine ∧ₑ₁ (RepFun_iff p (B x) (λ y, QPair x y)) hpRF };
  refine ∃ₑ hbex3 _;
  assume y hy;
  have hyB : π (y ∈ B x) { refine ∧ₑ₁ hy };
  have hpeq : π (p = QPair x y) { refine ∧ₑ₂ hy };
  refine hk x y hxA hyB hpeq
end;

// QSigmaE2: <a;b> ∈ QSigma(A,B) → (a∈A → b∈B(a) → P) → P
opaque symbol QSigmaE2 (a b A : τ ι) (B : τ ι → τ ι) (P : Prop) :
  π (QPair a b ∈ QSigma A B) →
  (π (a ∈ A) → π (b ∈ B a) → π P) → π P ≔
begin
  assume a b A B P h hk;
  refine QSigmaE (QPair a b) A B P h _;
  assume x y hxA hyB heq;
  have hax : π (a = x) { refine QPair_inject1 a b x y heq };
  have hby : π (b = y) { refine QPair_inject2 a b x y heq };
  refine hk (ind_eq hax (λ w, w ∈ A) hxA)
            (ind_eq hby (λ w, w ∈ B a) (ind_eq hax (λ w, y ∈ B w) hyB))
end;

// QSigmaD1: <a;b> ∈ QSigma(A,B) → a ∈ A
opaque symbol QSigmaD1 (a b A : τ ι) (B : τ ι → τ ι) :
  π (QPair a b ∈ QSigma A B) → π (a ∈ A) ≔
begin
  assume a b A B h;
  refine QSigmaE2 a b A B (a ∈ A) h _;
  assume haA hbB; refine haA
end;

// QSigmaD2: <a;b> ∈ QSigma(A,B) → b ∈ B(a)
opaque symbol QSigmaD2 (a b A : τ ι) (B : τ ι → τ ι) :
  π (QPair a b ∈ QSigma A B) → π (b ∈ B a) ≔
begin
  assume a b A B h;
  refine QSigmaE2 a b A B (b ∈ B a) h _;
  assume haA hbB; refine hbB
end;

// QSigma_cong: A=A' → (⋀x. x∈A' → B(x)=B'(x)) → QSigma(A,B) = QSigma(A',B')
opaque symbol QSigma_cong (A A' : τ ι) (B B' : τ ι → τ ι) :
  π (A = A') → (Π (x : τ ι), π (x ∈ A') → π (B x = B' x)) →
  π (QSigma A B = QSigma A' B') ≔
begin
  assume A A' B B' hA hB;
  rewrite hA;
  refine equality_iffI (QSigma A' B) (QSigma A' B') _;
  assume c;
  apply ∧ᵢ
  { assume hc;
    refine QSigmaE c A' B _ hc _;
    assume x y hxA hyB hceq;
    rewrite hceq;
    refine QSigmaI x y A' B' hxA (ind_eq (eq_sym (hB x hxA)) (λ s, y ∈ s) hyB) }
  { assume hc;
    refine QSigmaE c A' B' _ hc _;
    assume x y hxA hyB' hceq;
    rewrite hceq;
    refine QSigmaI x y A' B hxA (ind_eq (hB x hxA) (λ s, y ∈ s) hyB') }
end;

// QSigma_empty1: QSigma(0,B) = 0
opaque symbol QSigma_empty1 (B : τ ι → τ ι) : π (QSigma empty B = empty) ≔
begin
  assume B;
  refine equals0I (QSigma empty B) _;
  assume c hc;
  refine QSigmaE c empty B ⊥ hc _;
  assume x y hx hy heq;
  refine emptyE x hx
end;

// ---------------------------------------------------------------------------
// qprod: A <*> B = QSigma(A, λ_. B)
// ---------------------------------------------------------------------------

symbol qprod (A B : τ ι) : τ ι ≔ QSigma A (λ _, B);

// QSigma_empty2: A <*> 0 = 0
opaque symbol QSigma_empty2 (A : τ ι) : π (qprod A empty = empty) ≔
begin
  assume A;
  refine equals0I (qprod A empty) _;
  assume c hc;
  refine QSigmaE c A (λ _, empty) ⊥ hc _;
  assume x y hx hy heq;
  refine emptyE y hy
end;

// ---------------------------------------------------------------------------
// Projection typing and surjective pairing
// ---------------------------------------------------------------------------

// qfst_type: p ∈ QSigma(A,B) → qfst(p) ∈ A
opaque symbol qfst_type (p A : τ ι) (B : τ ι → τ ι) :
  π (p ∈ QSigma A B) → π (qfst p ∈ A) ≔
begin
  assume p A B hp;
  refine QSigmaE p A B (qfst p ∈ A) hp _;
  assume x y hxA hyB hpeq;
  rewrite hpeq;
  rewrite (qfst_conv x y);
  refine hxA
end;

// qsnd_type: p ∈ QSigma(A,B) → qsnd(p) ∈ B(qfst(p))
opaque symbol qsnd_type (p A : τ ι) (B : τ ι → τ ι) :
  π (p ∈ QSigma A B) → π (qsnd p ∈ B (qfst p)) ≔
begin
  assume p A B hp;
  refine QSigmaE p A B (qsnd p ∈ B (qfst p)) hp _;
  assume x y hxA hyB hpeq;
  rewrite hpeq;
  rewrite (qfst_conv x y);
  rewrite (qsnd_conv x y);
  refine hyB
end;

// QPair_qfst_qsnd_eq: a ∈ QSigma(A,B) → <qfst(a); qsnd(a)> = a
opaque symbol QPair_qfst_qsnd_eq (a A : τ ι) (B : τ ι → τ ι) :
  π (a ∈ QSigma A B) → π (QPair (qfst a) (qsnd a) = a) ≔
begin
  assume a A B ha;
  refine QSigmaE a A B (QPair (qfst a) (qsnd a) = a) ha _;
  assume x y hxA hyB haeq;
  rewrite haeq;
  rewrite (qfst_conv x y);
  rewrite (qsnd_conv x y);
  reflexivity
end;

// ===========================================================================
// Eliminator: qsplit (result sort i)
//   qsplit(c,p) = c(qfst p, qsnd p)
// ===========================================================================

symbol qsplit (c : τ ι → τ ι → τ ι) (p : τ ι) : τ ι ≔ c (qfst p) (qsnd p);

// qsplit (Isabelle simp): qsplit(λx y. c(x,y), <a;b>) ≡ c(a,b)
opaque symbol qsplit_conv (c : τ ι → τ ι → τ ι) (a b : τ ι) :
  π (qsplit c (QPair a b) = c a b) ≔
begin
  assume c a b;
  have key : π (c (qfst (QPair a b)) (qsnd (QPair a b)) = c a b) {
    rewrite (qfst_conv a b);
    rewrite (qsnd_conv a b);
    reflexivity };
  refine key
end;

// qsplit_type: p∈QSigma(A,B) → (⋀x y. x∈A → y∈B(x) → c(x,y):C(<x;y>))
//            → qsplit(c,p) ∈ C(p)
opaque symbol qsplit_type (p A : τ ι) (B : τ ι → τ ι)
  (c : τ ι → τ ι → τ ι) (C : τ ι → τ ι) :
  π (p ∈ QSigma A B) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ B x) → π (c x y ∈ C (QPair x y))) →
  π (qsplit c p ∈ C p) ≔
begin
  assume p A B c C hp hc;
  refine QSigmaE p A B (qsplit c p ∈ C p) hp _;
  assume x y hxA hyB hpeq;
  rewrite hpeq;
  rewrite (qsplit_conv c x y);
  refine hc x y hxA hyB
end;

// expand_qsplit: u ∈ A<*>B → (R(qsplit(c,u)) ⟷ (∀x∈A.∀y∈B. u=<x;y> → R(c(x,y))))
opaque symbol expand_qsplit (A B u : τ ι)
  (c : τ ι → τ ι → τ ι) (R : τ ι → Prop) :
  π (u ∈ qprod A B) →
  π (R (qsplit c u) ⇔ Ball A (λ x, Ball B (λ y, u = QPair x y ⇒ R (c x y)))) ≔
begin
  assume A B u c R hu;
  apply ∧ᵢ
  { assume hR x hx y hy hueq;
    have e : π (qsplit c u = c x y) { rewrite hueq; refine qsplit_conv c x y };
    refine ind_eq (eq_sym e) (λ w, R w) hR }
  { assume hall;
    refine QSigmaE u A (λ _, B) (R (qsplit c u)) hu _;
    assume x y hxA hyB hueq;
    have hRcxy : π (R (c x y)) { refine hall x hxA y hyB hueq };
    have e : π (qsplit c u = c x y) { rewrite hueq; refine qsplit_conv c x y };
    refine ind_eq e (λ w, R w) hRcxy }
end;

// ===========================================================================
// qsplit for predicates (result sort o)
// ===========================================================================

symbol qsplit_pred (R : τ ι → τ ι → Prop) (p : τ ι) : Prop ≔ R (qfst p) (qsnd p);

// qsplitI: R(a,b) → qsplit(R, <a;b>)
opaque symbol qsplitI (R : τ ι → τ ι → Prop) (a b : τ ι) :
  π (R a b) → π (qsplit_pred R (QPair a b)) ≔
begin
  assume R a b h;
  have key : π (R (qfst (QPair a b)) (qsnd (QPair a b))) {
    rewrite (qfst_conv a b);
    rewrite (qsnd_conv a b);
    refine h };
  refine key
end;

// qsplitD: qsplit(R, <a;b>) → R(a,b)
opaque symbol qsplitD (R : τ ι → τ ι → Prop) (a b : τ ι) :
  π (qsplit_pred R (QPair a b)) → π (R a b) ≔
begin
  assume R a b h;
  have h3 : π (R a (qsnd (QPair a b)))
    { refine ind_eq (eq_sym (qfst_conv a b)) (λ w, R w (qsnd (QPair a b))) h };
  refine ind_eq (eq_sym (qsnd_conv a b)) (λ w, R a w) h3
end;

// qsplitE: qsplit(R,z) → z∈QSigma(A,B) → (⋀x y. z=<x;y> → R(x,y) → P) → P
opaque symbol qsplitE (R : τ ι → τ ι → Prop) (z A : τ ι) (B : τ ι → τ ι) (P : Prop) :
  π (qsplit_pred R z) → π (z ∈ QSigma A B) →
  (Π (x y : τ ι), π (z = QPair x y) → π (R x y) → π P) → π P ≔
begin
  assume R z A B P hq hz hk;
  refine QSigmaE z A B P hz _;
  assume x y hxA hyB hzeq;
  have e1 : π (qfst z = x) { rewrite hzeq; refine qfst_conv x y };
  have e2 : π (qsnd z = y) { rewrite hzeq; refine qsnd_conv x y };
  have hq3 : π (R x (qsnd z))
    { refine ind_eq (eq_sym e1) (λ w, R w (qsnd z)) hq };
  have hRxy : π (R x y) { refine ind_eq (eq_sym e2) (λ w, R x w) hq3 };
  refine hk x y hzeq hRxy
end;

// ===========================================================================
// qconverse
//   qconverse(r) = {z. w ∈ r, ∃x y. w=<x;y> ∧ z=<y;x>}
// (rendered as RepFun over Collect, matching pair.lp's `converse`)
// ===========================================================================

symbol qconverse (r : τ ι) : τ ι ≔
  RepFun (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y))
    (λ p, QPair (qsnd p) (qfst p));

// qconverseI: <a;b> ∈ r → <b;a> ∈ qconverse(r)
opaque symbol qconverseI (a b r : τ ι) :
  π (QPair a b ∈ r) → π (QPair b a ∈ qconverse r) ≔
begin
  assume a b r h;
  have hcoll : π (QPair a b ∈ Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y))
    { refine CollectI (QPair a b) r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y)
        h (∃ᵢ a (∃ᵢ b (eq_refl (QPair a b)))) };
  have key : π (QPair b a = QPair (qsnd (QPair a b)) (qfst (QPair a b)))
    { rewrite (qsnd_conv a b); rewrite (qfst_conv a b); reflexivity };
  rewrite key;
  refine RepFunI (QPair a b)
    (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y))
    (λ p, QPair (qsnd p) (qfst p)) hcoll
end;

// qconverseD: <a;b> ∈ qconverse(r) → <b;a> ∈ r
opaque symbol qconverseD (a b r : τ ι) :
  π (QPair a b ∈ qconverse r) → π (QPair b a ∈ r) ≔
begin
  assume a b r h;
  have hbex : π (Bex (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y))
                     (λ p, QPair a b = QPair (qsnd p) (qfst p)))
    { refine ∧ₑ₁ (RepFun_iff (QPair a b)
        (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y))
        (λ p, QPair (qsnd p) (qfst p))) h };
  refine ∃ₑ hbex _;
  assume p hp;
  have hpC : π (p ∈ Collect r (λ q, `∃ (x : τ ι), `∃ (y : τ ι), q = QPair x y))
    { refine ∧ₑ₁ hp };
  have heq : π (QPair a b = QPair (qsnd p) (qfst p)) { refine ∧ₑ₂ hp };
  have hpr : π (p ∈ r)
    { refine CollectD1 p r (λ q, `∃ (x : τ ι), `∃ (y : τ ι), q = QPair x y) hpC };
  have hpair : π (`∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y)
    { refine CollectD2 p r (λ q, `∃ (x : τ ι), `∃ (y : τ ι), q = QPair x y) hpC };
  refine ∃ₑ hpair _;
  assume x hx;
  refine ∃ₑ hx _;
  assume y hpeq;
  have hqsnd : π (qsnd p = y) { rewrite hpeq; refine qsnd_conv x y };
  have hqfst : π (qfst p = x) { rewrite hpeq; refine qfst_conv x y };
  have t1 : π (QPair (qsnd p) (qfst p) = QPair y x)
    { rewrite hqsnd; rewrite hqfst; reflexivity };
  have heq2 : π (QPair a b = QPair y x) { refine ind_eq (eq_sym t1) (λ w, QPair a b = w) heq };
  have hay : π (a = y) { refine QPair_inject1 a b y x heq2 };
  have hbx : π (b = x) { refine QPair_inject2 a b y x heq2 };
  have hpr2 : π (QPair x y ∈ r) { refine ind_eq (eq_sym hpeq) (λ w, w ∈ r) hpr };
  refine ind_eq hay (λ w, QPair b w ∈ r) (ind_eq hbx (λ w, QPair w y ∈ r) hpr2)
end;

// qconverseE: yx ∈ qconverse(r) → (⋀x y. yx=<y;x> → <x;y>∈r → P) → P
opaque symbol qconverseE (yx r : τ ι) (P : Prop) :
  π (yx ∈ qconverse r) →
  (Π (x y : τ ι), π (yx = QPair y x) → π (QPair x y ∈ r) → π P) → π P ≔
begin
  assume yx r P h hk;
  have hbex : π (Bex (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y))
                     (λ p, yx = QPair (qsnd p) (qfst p)))
    { refine ∧ₑ₁ (RepFun_iff yx
        (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y))
        (λ p, QPair (qsnd p) (qfst p))) h };
  refine ∃ₑ hbex _;
  assume p hp;
  have hpC : π (p ∈ Collect r (λ q, `∃ (x : τ ι), `∃ (y : τ ι), q = QPair x y))
    { refine ∧ₑ₁ hp };
  have hyxeq : π (yx = QPair (qsnd p) (qfst p)) { refine ∧ₑ₂ hp };
  have hpr : π (p ∈ r)
    { refine CollectD1 p r (λ q, `∃ (x : τ ι), `∃ (y : τ ι), q = QPair x y) hpC };
  have hpair : π (`∃ (x : τ ι), `∃ (y : τ ι), p = QPair x y)
    { refine CollectD2 p r (λ q, `∃ (x : τ ι), `∃ (y : τ ι), q = QPair x y) hpC };
  refine ∃ₑ hpair _;
  assume x hx;
  refine ∃ₑ hx _;
  assume y hpeq;
  have hqsnd : π (qsnd p = y) { rewrite hpeq; refine qsnd_conv x y };
  have hqfst : π (qfst p = x) { rewrite hpeq; refine qfst_conv x y };
  have t1 : π (QPair (qsnd p) (qfst p) = QPair y x)
    { rewrite hqsnd; rewrite hqfst; reflexivity };
  have hyx2 : π (yx = QPair y x) { refine ind_eq (eq_sym t1) (λ w, yx = w) hyxeq };
  have hxyr : π (QPair x y ∈ r) { refine ind_eq (eq_sym hpeq) (λ w, w ∈ r) hpr };
  refine hk x y hyx2 hxyr
end;

// qconverse_qconverse: r ⊆ QSigma(A,B) → qconverse(qconverse(r)) = r
opaque symbol qconverse_qconverse (r A : τ ι) (B : τ ι → τ ι) :
  π (r ⊆ QSigma A B) → π (qconverse (qconverse r) = r) ≔
begin
  assume r A B hsub;
  refine equality_iffI (qconverse (qconverse r)) r _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine qconverseE z (qconverse r) (z ∈ r) hz _;
    assume x y hzeq hxyqc;
    have hyxr : π (QPair y x ∈ r) { refine qconverseD x y r hxyqc };
    rewrite hzeq;
    refine hyxr }
  { assume hz;
    have hzQ : π (z ∈ QSigma A B) { refine hsub z hz };
    refine QSigmaE z A B (z ∈ qconverse (qconverse r)) hzQ _;
    assume x y hxA hyB hzeq;
    have hxyr : π (QPair x y ∈ r) { refine ind_eq (eq_sym hzeq) (λ w, w ∈ r) hz };
    rewrite hzeq;
    refine qconverseI y x (qconverse r) (qconverseI x y r hxyr) }
end;

// qconverse_type: r ⊆ A<*>B → qconverse(r) ⊆ B<*>A
opaque symbol qconverse_type (r A B : τ ι) :
  π (r ⊆ qprod A B) → π (qconverse r ⊆ qprod B A) ≔
begin
  assume r A B hsub z hz;
  refine qconverseE z r (z ∈ qprod B A) hz _;
  assume x y hzeq hxyr;
  have hxyQ : π (QPair x y ∈ QSigma A (λ _, B)) { refine hsub (QPair x y) hxyr };
  have hxA : π (x ∈ A) { refine QSigmaD1 x y A (λ _, B) hxyQ };
  have hyB : π (y ∈ B) { refine QSigmaD2 x y A (λ _, B) hxyQ };
  rewrite hzeq;
  refine QSigmaI y x B (λ _, A) hyB hxA
end;

// qconverse_prod: qconverse(A<*>B) = B<*>A
opaque symbol qconverse_prod (A B : τ ι) :
  π (qconverse (qprod A B) = qprod B A) ≔
begin
  assume A B;
  refine subset_antisym (qconverse (qprod A B)) (qprod B A) _ _
  { refine qconverse_type (qprod A B) A B (subset_refl (qprod A B)) }
  { assume z hz;
    refine QSigmaE z B (λ _, A) (z ∈ qconverse (qprod A B)) hz _;
    assume y x hyB hxA hzeq;
    rewrite hzeq;
    have hxyP : π (QPair x y ∈ qprod A B) { refine QSigmaI x y A (λ _, B) hxA hyB };
    refine qconverseI x y (qprod A B) hxyP }
end;

// qconverse_empty: qconverse(0) = 0
opaque symbol qconverse_empty : π (qconverse empty = empty) ≔
begin
  refine equals0I (qconverse empty) _;
  assume z hz;
  refine qconverseE z empty ⊥ hz _;
  assume x y hzeq hxye;
  refine emptyE (QPair x y) hxye
end;

// ===========================================================================
// Quine-inspired disjoint sum
//   A <+> B = ({0} <*> A) ∪ ({1} <*> B)
//   QInl(a) = <0;a>     QInr(b) = <1;b>
//   qcase(c,d) = qsplit(λy z. cond(y, d(z), c(z)))
// ===========================================================================

symbol qsum (A B : τ ι) : τ ι ≔
  Un (qprod (singleton empty) A) (qprod (singleton one) B);

symbol QInl (a : τ ι) : τ ι ≔ QPair empty a;
symbol QInr (b : τ ι) : τ ι ≔ QPair one b;

symbol qcase (c d : τ ι → τ ι) (p : τ ι) : τ ι ≔
  cond (qfst p) (d (qsnd p)) (c (qsnd p));

// QInlI: a ∈ A → QInl(a) ∈ A<+>B
opaque symbol QInlI (a A B : τ ι) :
  π (a ∈ A) → π (QInl a ∈ qsum A B) ≔
begin
  assume a A B haA;
  have h : π (QPair empty a ∈ qprod (singleton empty) A)
    { refine QSigmaI empty a (singleton empty) (λ _, A) (singletonI empty) haA };
  refine UnI1 (QPair empty a)
    (qprod (singleton empty) A) (qprod (singleton one) B) h
end;

// QInrI: b ∈ B → QInr(b) ∈ A<+>B
opaque symbol QInrI (b A B : τ ι) :
  π (b ∈ B) → π (QInr b ∈ qsum A B) ≔
begin
  assume b A B hbB;
  have h : π (QPair one b ∈ qprod (singleton one) B)
    { refine QSigmaI one b (singleton one) (λ _, B) (singletonI one) hbB };
  refine UnI2 (QPair one b)
    (qprod (singleton empty) A) (qprod (singleton one) B) h
end;

// qsumE: u∈A<+>B → (⋀x. x∈A → u=QInl(x) → P) → (⋀y. y∈B → u=QInr(y) → P) → P
opaque symbol qsumE (u A B : τ ι) (P : Prop) :
  π (u ∈ qsum A B) →
  (Π (x : τ ι), π (x ∈ A) → π (u = QInl x) → π P) →
  (Π (y : τ ι), π (y ∈ B) → π (u = QInr y) → π P) →
  π P ≔
begin
  assume u A B P hu hleft hright;
  have hdisj : π (u ∈ qprod (singleton empty) A ∨ u ∈ qprod (singleton one) B)
    { refine UnE u (qprod (singleton empty) A) (qprod (singleton one) B) hu };
  refine ∨ₑ hdisj _ _
  { assume hleftσ;
    refine QSigmaE u (singleton empty) (λ _, A) P hleftσ _;
    assume x y hxsing hyA hueq;
    have hx0 : π (x = empty) { refine ∧ₑ₁ (singleton_iff x empty) hxsing };
    have hueq2 : π (u = QInl y) { refine ind_eq (eq_sym hx0) (λ w, u = QPair w y) hueq };
    refine hleft y hyA hueq2 }
  { assume hrightσ;
    refine QSigmaE u (singleton one) (λ _, B) P hrightσ _;
    assume x y hxsing hyB hueq;
    have hx1 : π (x = one) { refine ∧ₑ₁ (singleton_iff x one) hxsing };
    have hueq2 : π (u = QInr y) { refine ind_eq (eq_sym hx1) (λ w, u = QPair w y) hueq };
    refine hright y hyB hueq2 }
end;

// ---------------------------------------------------------------------------
// Injection and freeness equivalences
// ---------------------------------------------------------------------------

// QInl_iff: QInl(a)=QInl(b) ⟷ a=b
opaque symbol QInl_iff (a b : τ ι) : π (QInl a = QInl b ⇔ a = b) ≔
begin
  assume a b;
  apply ∧ᵢ
  { assume h; refine QPair_inject2 empty a empty b h }
  { assume h; rewrite h; reflexivity }
end;

// QInr_iff: QInr(a)=QInr(b) ⟷ a=b
opaque symbol QInr_iff (a b : τ ι) : π (QInr a = QInr b ⇔ a = b) ≔
begin
  assume a b;
  apply ∧ᵢ
  { assume h; refine QPair_inject2 one a one b h }
  { assume h; rewrite h; reflexivity }
end;

// QInl_QInr_iff: QInl(a)=QInr(b) ⟷ False
opaque symbol QInl_QInr_iff (a b : τ ι) : π (QInl a = QInr b ⇔ ⊥) ≔
begin
  assume a b;
  apply ∧ᵢ
  { assume h;
    have h01 : π (empty = one) { refine QPair_inject1 empty a one b h };
    refine zero_ne_one h01 }
  { assume hf; refine ⊥ₑ hf }
end;

// QInr_QInl_iff: QInr(b)=QInl(a) ⟷ False
opaque symbol QInr_QInl_iff (a b : τ ι) : π (QInr b = QInl a ⇔ ⊥) ≔
begin
  assume a b;
  apply ∧ᵢ
  { assume h;
    have h10 : π (one = empty) { refine QPair_inject1 one b empty a h };
    refine zero_ne_one (eq_sym h10) }
  { assume hf; refine ⊥ₑ hf }
end;

// qsum_empty: 0<+>0 = 0
opaque symbol qsum_empty : π (qsum empty empty = empty) ≔
begin
  refine equals0I (qsum empty empty) _;
  assume y hy;
  refine qsumE y empty empty ⊥ hy _ _
  { assume x hx heq; refine emptyE x hx }
  { assume x hx heq; refine emptyE x hx }
end;

// QInl_inject: QInl(a)=QInl(b) → a=b
opaque symbol QInl_inject (a b : τ ι) : π (QInl a = QInl b) → π (a = b) ≔
begin assume a b h; refine ∧ₑ₁ (QInl_iff a b) h end;

// QInr_inject: QInr(a)=QInr(b) → a=b
opaque symbol QInr_inject (a b : τ ι) : π (QInr a = QInr b) → π (a = b) ≔
begin assume a b h; refine ∧ₑ₁ (QInr_iff a b) h end;

// QInl_neq_QInr: QInl(a)=QInr(b) → P
opaque symbol QInl_neq_QInr (a b : τ ι) (P : Prop) : π (QInl a = QInr b) → π P ≔
begin assume a b P h; refine ⊥ₑ _; refine ∧ₑ₁ (QInl_QInr_iff a b) h end;

// QInr_neq_QInl: QInr(b)=QInl(a) → P
opaque symbol QInr_neq_QInl (a b : τ ι) (P : Prop) : π (QInr b = QInl a) → π P ≔
begin assume a b P h; refine ⊥ₑ _; refine ∧ₑ₁ (QInr_QInl_iff a b) h end;

// QInlD: QInl(a) ∈ A<+>B → a ∈ A
opaque symbol QInlD (a A B : τ ι) : π (QInl a ∈ qsum A B) → π (a ∈ A) ≔
begin
  assume a A B h;
  refine qsumE (QInl a) A B (a ∈ A) h _ _
  { assume x hxA heq;
    have hax : π (a = x) { refine QInl_inject a x heq };
    rewrite hax; apply hxA }
  { assume y hyB heq; refine QInl_neq_QInr a y (a ∈ A) heq }
end;

// QInrD: QInr(b) ∈ A<+>B → b ∈ B
opaque symbol QInrD (b A B : τ ι) : π (QInr b ∈ qsum A B) → π (b ∈ B) ≔
begin
  assume b A B h;
  refine qsumE (QInr b) A B (b ∈ B) h _ _
  { assume x hxA heq; refine QInr_neq_QInl x b (b ∈ B) heq }
  { assume y hyB heq;
    have hby : π (b = y) { refine QInr_inject b y heq };
    rewrite hby; apply hyB }
end;

// qsum_iff: u∈A<+>B ⟷ (∃x. x∈A ∧ u=QInl(x)) ∨ (∃y. y∈B ∧ u=QInr(y))
opaque symbol qsum_iff (u A B : τ ι) :
  π ((u ∈ qsum A B) ⇔
     ((`∃ (x : τ ι), x ∈ A ∧ u = QInl x) ∨
      (`∃ (y : τ ι), y ∈ B ∧ u = QInr y))) ≔
begin
  assume u A B;
  apply ∧ᵢ
  { assume hu;
    refine qsumE u A B _ hu _ _
    { assume x hxA hueq; refine ∨ᵢ₁ (∃ᵢ x (∧ᵢ hxA hueq)) }
    { assume y hyB hueq; refine ∨ᵢ₂ (∃ᵢ y (∧ᵢ hyB hueq)) } }
  { assume hdisj;
    refine ∨ₑ hdisj _ _
    { assume hex;
      refine ∃ₑ hex _;
      assume x hx;
      have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
      have hueq : π (u = QInl x) { refine ∧ₑ₂ hx };
      rewrite hueq;
      refine QInlI x A B hxA }
    { assume hex;
      refine ∃ₑ hex _;
      assume y hy;
      have hyB : π (y ∈ B) { refine ∧ₑ₁ hy };
      have hueq : π (u = QInr y) { refine ∧ₑ₂ hy };
      rewrite hueq;
      refine QInrI y A B hyB } }
end;

// qsum_subset_iff: A<+>B ⊆ C<+>D ⟷ A⊆C ∧ B⊆D
opaque symbol qsum_subset_iff (A B C D : τ ι) :
  π ((qsum A B ⊆ qsum C D) ⇔ (A ⊆ C ∧ B ⊆ D)) ≔
begin
  assume A B C D;
  apply ∧ᵢ
  { assume hsub;
    apply ∧ᵢ
    { assume x hx;
      have h : π (QInl x ∈ qsum A B) { refine QInlI x A B hx };
      have h2 : π (QInl x ∈ qsum C D) { refine hsub (QInl x) h };
      refine QInlD x C D h2 }
    { assume y hy;
      have h : π (QInr y ∈ qsum A B) { refine QInrI y A B hy };
      have h2 : π (QInr y ∈ qsum C D) { refine hsub (QInr y) h };
      refine QInrD y C D h2 } }
  { assume hpair;
    have hAC : π (A ⊆ C) { refine ∧ₑ₁ hpair };
    have hBD : π (B ⊆ D) { refine ∧ₑ₂ hpair };
    assume u hu;
    refine qsumE u A B _ hu _ _
    { assume x hxA hueq; rewrite hueq; refine QInlI x C D (hAC x hxA) }
    { assume y hyB hueq; rewrite hueq; refine QInrI y C D (hBD y hyB) } }
end;

// qsum_equal_iff: A<+>B = C<+>D ⟷ A=C ∧ B=D
opaque symbol qsum_equal_iff (A B C D : τ ι) :
  π ((qsum A B = qsum C D) ⇔ (A = C ∧ B = D)) ≔
begin
  assume A B C D;
  apply ∧ᵢ
  { assume heq;
    have hsub1 : π (qsum A B ⊆ qsum C D) { refine equalityD1 (qsum A B) (qsum C D) heq };
    have hsub2 : π (qsum C D ⊆ qsum A B) { refine equalityD2 (qsum A B) (qsum C D) heq };
    have h1 : π (A ⊆ C ∧ B ⊆ D) { refine ∧ₑ₁ (qsum_subset_iff A B C D) hsub1 };
    have h2 : π (C ⊆ A ∧ D ⊆ B) { refine ∧ₑ₁ (qsum_subset_iff C D A B) hsub2 };
    apply ∧ᵢ
    { refine subset_antisym A C (∧ₑ₁ h1) (∧ₑ₁ h2) }
    { refine subset_antisym B D (∧ₑ₂ h1) (∧ₑ₂ h2) } }
  { assume hpair;
    have hAC : π (A = C) { refine ∧ₑ₁ hpair };
    have hBD : π (B = D) { refine ∧ₑ₂ hpair };
    rewrite hAC; rewrite hBD; reflexivity }
end;

// ---------------------------------------------------------------------------
// Eliminator -- qcase
// ---------------------------------------------------------------------------

// qcase_QInl: qcase(c,d,QInl(a)) = c(a)
opaque symbol qcase_QInl (c d : τ ι → τ ι) (a : τ ι) :
  π (qcase c d (QInl a) = c a) ≔
begin
  assume c d a;
  have key : π (cond (qfst (QPair empty a)) (d (qsnd (QPair empty a)))
                     (c (qsnd (QPair empty a))) = c a) {
    rewrite (qfst_conv empty a);
    rewrite (qsnd_conv empty a);
    refine cond_0 (d a) (c a) };
  refine key
end;

// qcase_QInr: qcase(c,d,QInr(b)) = d(b)
opaque symbol qcase_QInr (c d : τ ι → τ ι) (b : τ ι) :
  π (qcase c d (QInr b) = d b) ≔
begin
  assume c d b;
  have key : π (cond (qfst (QPair one b)) (d (qsnd (QPair one b)))
                     (c (qsnd (QPair one b))) = d b) {
    rewrite (qfst_conv one b);
    rewrite (qsnd_conv one b);
    refine cond_1 (d b) (c b) };
  refine key
end;

// qcase_type: u∈A<+>B → (⋀x. x∈A → c(x):C(QInl(x))) → (⋀y. y∈B → d(y):C(QInr(y)))
//           → qcase(c,d,u) ∈ C(u)
opaque symbol qcase_type (u A B : τ ι) (c d : τ ι → τ ι) (C : τ ι → τ ι) :
  π (u ∈ qsum A B) →
  (Π (x : τ ι), π (x ∈ A) → π (c x ∈ C (QInl x))) →
  (Π (y : τ ι), π (y ∈ B) → π (d y ∈ C (QInr y))) →
  π (qcase c d u ∈ C u) ≔
begin
  assume u A B c d C hu hc hd;
  refine qsumE u A B (qcase c d u ∈ C u) hu _ _
  { assume x hxA hueq;
    rewrite hueq;
    rewrite (qcase_QInl c d x);
    refine hc x hxA }
  { assume y hyB hueq;
    rewrite hueq;
    rewrite (qcase_QInr c d y);
    refine hd y hyB }
end;

// ---------------------------------------------------------------------------
// Rules for the Part primitive
// ---------------------------------------------------------------------------

// Part_QInl: Part(A<+>B, QInl) = {QInl(x). x∈A}
opaque symbol Part_QInl (A B : τ ι) :
  π (Part (qsum A B) QInl = RepFun A QInl) ≔
begin
  assume A B;
  refine extension (Part (qsum A B) QInl) (RepFun A QInl) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hxsum : π (x ∈ qsum A B) { refine PartD1 x (qsum A B) QInl hx };
    have hex : π (`∃ (z : τ ι), x = QInl z)
      { refine CollectD2 x (qsum A B) (λ y, `∃ (z : τ ι), y = QInl z) hx };
    refine ∃ₑ hex _;
    assume z hz;
    have hzA : π (z ∈ A) { refine QInlD z A B (ind_eq (eq_sym hz) (λ w, w ∈ qsum A B) hxsum) };
    refine ind_eq hz (λ w, w ∈ RepFun A QInl) (RepFunI z A QInl hzA) }
  { assume hx;
    have hbex : π (Bex A (λ z, x = QInl z)) { refine ∧ₑ₁ (RepFun_iff x A QInl) hx };
    refine ∃ₑ hbex _;
    assume z hz;
    have hzA : π (z ∈ A) { refine ∧ₑ₁ hz };
    have hxeq : π (x = QInl z) { refine ∧ₑ₂ hz };
    have hinl : π (QInl z ∈ qsum A B) { refine QInlI z A B hzA };
    have hxsum : π (x ∈ qsum A B) { refine ind_eq hxeq (λ w, w ∈ qsum A B) hinl };
    refine Part_eqI x (qsum A B) QInl z hxsum hxeq }
end;

// Part_QInr: Part(A<+>B, QInr) = {QInr(y). y∈B}
opaque symbol Part_QInr (A B : τ ι) :
  π (Part (qsum A B) QInr = RepFun B QInr) ≔
begin
  assume A B;
  refine extension (Part (qsum A B) QInr) (RepFun B QInr) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hxsum : π (x ∈ qsum A B) { refine PartD1 x (qsum A B) QInr hx };
    have hex : π (`∃ (z : τ ι), x = QInr z)
      { refine CollectD2 x (qsum A B) (λ y, `∃ (z : τ ι), y = QInr z) hx };
    refine ∃ₑ hex _;
    assume z hz;
    have hzB : π (z ∈ B) { refine QInrD z A B (ind_eq (eq_sym hz) (λ w, w ∈ qsum A B) hxsum) };
    refine ind_eq hz (λ w, w ∈ RepFun B QInr) (RepFunI z B QInr hzB) }
  { assume hx;
    have hbex : π (Bex B (λ z, x = QInr z)) { refine ∧ₑ₁ (RepFun_iff x B QInr) hx };
    refine ∃ₑ hbex _;
    assume z hz;
    have hzB : π (z ∈ B) { refine ∧ₑ₁ hz };
    have hxeq : π (x = QInr z) { refine ∧ₑ₂ hz };
    have hinr : π (QInr z ∈ qsum A B) { refine QInrI z A B hzB };
    have hxsum : π (x ∈ qsum A B) { refine ind_eq hxeq (λ w, w ∈ qsum A B) hinr };
    refine Part_eqI x (qsum A B) QInr z hxsum hxeq }
end;

// Part_QInr2: Part(A<+>B, λx. QInr(h(x))) = {QInr(y). y∈Part(B,h)}
opaque symbol Part_QInr2 (A B : τ ι) (h : τ ι → τ ι) :
  π (Part (qsum A B) (λ x, QInr (h x)) = RepFun (Part B h) QInr) ≔
begin
  assume A B h;
  refine extension (Part (qsum A B) (λ x, QInr (h x))) (RepFun (Part B h) QInr) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hxsum : π (x ∈ qsum A B) { refine PartD1 x (qsum A B) (λ z, QInr (h z)) hx };
    have hex : π (`∃ (z : τ ι), x = QInr (h z))
      { refine CollectD2 x (qsum A B) (λ y, `∃ (z : τ ι), y = QInr (h z)) hx };
    refine ∃ₑ hex _;
    assume z hz;
    have hhzB : π (h z ∈ B)
      { refine QInrD (h z) A B (ind_eq (eq_sym hz) (λ w, w ∈ qsum A B) hxsum) };
    have hhzpart : π (h z ∈ Part B h) { refine PartI z B h hhzB };
    have hinr : π (QInr (h z) ∈ RepFun (Part B h) QInr)
      { refine RepFunI (h z) (Part B h) QInr hhzpart };
    refine ind_eq hz (λ w, w ∈ RepFun (Part B h) QInr) hinr }
  { assume hx;
    have hbex : π (Bex (Part B h) (λ z, x = QInr z))
      { refine ∧ₑ₁ (RepFun_iff x (Part B h) QInr) hx };
    refine ∃ₑ hbex _;
    assume z hz;
    have hzpart : π (z ∈ Part B h) { refine ∧ₑ₁ hz };
    have hxeq : π (x = QInr z) { refine ∧ₑ₂ hz };
    have hzB : π (z ∈ B) { refine PartD1 z B h hzpart };
    have hexw : π (`∃ (w : τ ι), z = h w)
      { refine CollectD2 z B (λ y, `∃ (w : τ ι), y = h w) hzpart };
    have hinr : π (QInr z ∈ qsum A B) { refine QInrI z A B hzB };
    have hxsum : π (x ∈ qsum A B) { refine ind_eq hxeq (λ w, w ∈ qsum A B) hinr };
    refine CollectI x (qsum A B) (λ y, `∃ (w : τ ι), y = QInr (h w)) hxsum _;
    refine ∃ₑ hexw _;
    assume w hw;
    have hxeq2 : π (x = QInr (h w)) { rewrite hxeq; rewrite hw; reflexivity };
    refine ∃ᵢ w hxeq2 }
end;

// Part_qsum_equality: C ⊆ A<+>B → Part(C,QInl) ∪ Part(C,QInr) = C
opaque symbol Part_qsum_equality (A B C : τ ι) :
  π (C ⊆ qsum A B) → π (Un (Part C QInl) (Part C QInr) = C) ≔
begin
  assume A B C hsub;
  refine extension (Un (Part C QInl) (Part C QInr)) C _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hdisj : π (x ∈ Part C QInl ∨ x ∈ Part C QInr)
      { refine UnE x (Part C QInl) (Part C QInr) hx };
    refine ∨ₑ hdisj _ _
    { assume h; refine PartD1 x C QInl h }
    { assume h; refine PartD1 x C QInr h } }
  { assume hxC;
    have hxsum : π (x ∈ qsum A B) { refine hsub x hxC };
    refine qsumE x A B _ hxsum _ _
    { assume a haA hxeq;
      refine UnI1 x (Part C QInl) (Part C QInr) _;
      refine Part_eqI x C QInl a hxC hxeq }
    { assume b hbB hxeq;
      refine UnI2 x (Part C QInl) (Part C QInr) _;
      refine Part_eqI x C QInr b hxC hxeq } }
end;

// ---------------------------------------------------------------------------
// Monotonicity
// ---------------------------------------------------------------------------

// QPair_mono: a⊆c → b⊆d → <a;b> ⊆ <c;d>   (it is sum monotonicity)
opaque symbol QPair_mono (a b c d : τ ι) :
  π (a ⊆ c) → π (b ⊆ d) → π (QPair a b ⊆ QPair c d) ≔
begin
  assume a b c d hac hbd;
  refine ∧ₑ₂ (sum_subset_iff a b c d) (∧ᵢ hac hbd)
end;

// QSigma_mono: A⊆C → (∀x∈A. B(x)⊆D(x)) → QSigma(A,B) ⊆ QSigma(C,D)
opaque symbol QSigma_mono (A C : τ ι) (B D : τ ι → τ ι) :
  π (A ⊆ C) → π (Ball A (λ x, B x ⊆ D x)) → π (QSigma A B ⊆ QSigma C D) ≔
begin
  assume A C B D hAC hBD z hz;
  refine QSigmaE z A B (z ∈ QSigma C D) hz _;
  assume x y hxA hyB hzeq;
  rewrite hzeq;
  refine QSigmaI x y C D (hAC x hxA) (bspec A (λ w, B w ⊆ D w) x hBD hxA y hyB)
end;

// QInl_mono: a⊆b → QInl(a) ⊆ QInl(b)
opaque symbol QInl_mono (a b : τ ι) : π (a ⊆ b) → π (QInl a ⊆ QInl b) ≔
begin
  assume a b h;
  refine QPair_mono empty a empty b (subset_refl empty) h
end;

// QInr_mono: a⊆b → QInr(a) ⊆ QInr(b)
opaque symbol QInr_mono (a b : τ ι) : π (a ⊆ b) → π (QInr a ⊆ QInr b) ≔
begin
  assume a b h;
  refine QPair_mono one a one b (subset_refl one) h
end;

// qsum_mono: A⊆C → B⊆D → A<+>B ⊆ C<+>D
opaque symbol qsum_mono (A B C D : τ ι) :
  π (A ⊆ C) → π (B ⊆ D) → π (qsum A B ⊆ qsum C D) ≔
begin
  assume A B C D hAC hBD;
  refine ∧ₑ₂ (qsum_subset_iff A B C D) (∧ᵢ hAC hBD)
end;
