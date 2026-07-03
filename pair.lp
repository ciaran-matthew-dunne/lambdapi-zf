// pair: Ordered pairs for ZF set theory
//
// Pair is the concrete Kuratowski encoding Pair(a,b) = {{a},{a,b}}
// (per CLAUDE.md §3). Consequently fst(Pair a b) and snd(Pair a b) do NOT
// reduce definitionally — project with the proved lemmas fst_conv / snd_conv.
//
// Defines: Pair, fst, snd, split, Sigma
// Proves:  Pair_inject1, Pair_inject2, Pair_neq_0, fst_conv, snd_conv

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt
             Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair;

// ===========================================================================
// Helper lemmas (the Kuratowski pair needs doubleton/singleton reasoning)
// ===========================================================================

// the_equality: if P holds at a and only at a, then The(P) = a.
opaque symbol the_equality (P : τ ι → Prop) (a : τ ι) :
  π (P a) → (Π (x : τ ι), π (P x) → π (x = a)) → π (The P = a) ≔
begin
  assume P a hPa huniq;
  refine huniq (ε P) (εᵢ P (∃ᵢ a hPa))
end;

// singleton_inject: {a} = {b} → a = b
opaque symbol singleton_inject (a b : τ ι) :
  π (singleton a = singleton b) → π (a = b) ≔
begin
  assume a b h;
  have ha : π (a ∈ singleton b) { rewrite (eq_sym h); refine singletonI a };
  refine ∧ₑ₁ (singleton_iff a b) ha
end;

// Upair_comm: {a,b} = {b,a}
opaque symbol Upair_comm (a b : τ ι) : π (Upair a b = Upair b a) ≔
begin
  assume a b;
  refine equality_iffI (Upair a b) (Upair b a) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    refine ∨ₑ (UpairE x a b hx) _ _
    { assume he; rewrite he; refine UpairI2 b a }
    { assume he; rewrite he; refine UpairI1 b a } }
  { assume hx;
    refine ∨ₑ (UpairE x b a hx) _ _
    { assume he; rewrite he; refine UpairI2 a b }
    { assume he; rewrite he; refine UpairI1 a b } }
end;

// doubleton_eq_iff: {a,b} = {c,d} ⟷ (a=c ∧ b=d) ∨ (a=d ∧ b=c)
opaque symbol doubleton_eq_iff (a b c d : τ ι) :
  π (Upair a b = Upair c d ⇔ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) ≔
begin
  assume a b c d;
  apply ∧ᵢ
  { assume heq;
    have hagcd : π (a = c ∨ a = d)
      { refine UpairE a c d _; rewrite (eq_sym heq); refine UpairI1 a b };
    have hbgcd : π (b = c ∨ b = d)
      { refine UpairE b c d _; rewrite (eq_sym heq); refine UpairI2 a b };
    have hcgab : π (c = a ∨ c = b)
      { refine UpairE c a b _; rewrite heq; refine UpairI1 c d };
    have hdgab : π (d = a ∨ d = b)
      { refine UpairE d a b _; rewrite heq; refine UpairI2 c d };
    refine ∨ₑ hagcd _ _
    { assume hac;
      refine ∨ₑ hbgcd _ _
      { assume hbc;
        refine ∨ᵢ₂ (∧ᵢ _ hbc);
        refine ∨ₑ hdgab _ _
        { assume hda; refine eq_sym hda }
        { assume hdb; rewrite hac; rewrite (eq_sym hbc); refine eq_sym hdb } }
      { assume hbd; refine ∨ᵢ₁ (∧ᵢ hac hbd) } }
    { assume had;
      refine ∨ₑ hbgcd _ _
      { assume hbc; refine ∨ᵢ₂ (∧ᵢ had hbc) }
      { assume hbd;
        refine ∨ᵢ₁ (∧ᵢ _ hbd);
        refine ∨ₑ hcgab _ _
        { assume hca; refine eq_sym hca }
        { assume hcb; rewrite had; rewrite (eq_sym hbd); refine eq_sym hcb } } } }
  { assume hdisj;
    refine ∨ₑ hdisj _ _
    { assume hc; rewrite (∧ₑ₁ hc); rewrite (∧ₑ₂ hc); reflexivity }
    { assume hc; rewrite (∧ₑ₁ hc); rewrite (∧ₑ₂ hc); refine Upair_comm d c } }
end;

// ===========================================================================
// Ordered pair — Kuratowski encoding ⟨a,b⟩ = {{a}, {a,b}}
// ===========================================================================

symbol Pair (a b : τ ι) : τ ι ≔ Upair (singleton a) (Upair a b);

// ===========================================================================
// Pair injectivity and non-emptiness (proved from the Kuratowski encoding)
// ===========================================================================

// Injectivity: Pair(a,b) = Pair(c,d) → a = c
opaque symbol Pair_inject1 (a b c d : τ ι) :
  π (Pair a b = Pair c d) → π (a = c) ≔
begin
  assume a b c d heq;
  have hcase : π ((singleton a = singleton c ∧ Upair a b = Upair c d) ∨
                  (singleton a = Upair c d ∧ Upair a b = singleton c))
    { refine ∧ₑ₁ (doubleton_eq_iff (singleton a) (Upair a b) (singleton c) (Upair c d)) heq };
  refine ∨ₑ hcase _ _
  { assume hc; refine singleton_inject a c (∧ₑ₁ hc) }
  { assume hc;
    have hsa : π (singleton a = Upair c d) { refine ∧ₑ₁ hc };
    have hcin : π (c ∈ singleton a) { rewrite hsa; refine UpairI1 c d };
    refine eq_sym (∧ₑ₁ (singleton_iff c a) hcin) }
end;

// Injectivity: Pair(a,b) = Pair(c,d) → b = d
opaque symbol Pair_inject2 (a b c d : τ ι) :
  π (Pair a b = Pair c d) → π (b = d) ≔
begin
  assume a b c d heq;
  have hcase : π ((singleton a = singleton c ∧ Upair a b = Upair c d) ∨
                  (singleton a = Upair c d ∧ Upair a b = singleton c))
    { refine ∧ₑ₁ (doubleton_eq_iff (singleton a) (Upair a b) (singleton c) (Upair c d)) heq };
  refine ∨ₑ hcase _ _
  { assume hc;
    have hac : π (a = c) { refine singleton_inject a c (∧ₑ₁ hc) };
    have hud : π (Upair a b = Upair c d) { refine ∧ₑ₂ hc };
    refine ∨ₑ (∧ₑ₁ (doubleton_eq_iff a b c d) hud) _ _
    { assume h2; refine ∧ₑ₂ h2 }
    { assume h2;
      have had : π (a = d) { refine ∧ₑ₁ h2 };
      have hbc : π (b = c) { refine ∧ₑ₂ h2 };
      rewrite hbc; rewrite (eq_sym hac); refine had } }
  { assume hc;
    have hsa : π (singleton a = Upair c d) { refine ∧ₑ₁ hc };
    have hab : π (Upair a b = singleton c) { refine ∧ₑ₂ hc };
    have hbc : π (b = c) {
      have hbin : π (b ∈ singleton c) { rewrite (eq_sym hab); refine UpairI2 a b };
      refine ∧ₑ₁ (singleton_iff b c) hbin };
    have hac : π (a = c) {
      have hain : π (a ∈ singleton c) { rewrite (eq_sym hab); refine UpairI1 a b };
      refine ∧ₑ₁ (singleton_iff a c) hain };
    have hda : π (d = a) {
      have hdin : π (d ∈ singleton a) { rewrite hsa; refine UpairI2 c d };
      refine ∧ₑ₁ (singleton_iff d a) hdin };
    rewrite hbc; rewrite (eq_sym hac); refine eq_sym hda }
end;

// Combined injectivity
opaque symbol Pair_inject (a b c d : τ ι) :
  π (Pair a b = Pair c d) → π (a = c ∧ b = d) ≔
begin
  assume a b c d heq;
  apply ∧ᵢ
  { refine Pair_inject1 a b c d heq }
  { refine Pair_inject2 a b c d heq }
end;

// Non-emptiness: Pair(a,b) ≠ ∅  (it is a Upair, which contains {a})
opaque symbol Pair_neq_0 (a b : τ ι) : π (Pair a b ≠ empty) ≔
begin
  assume a b heq;
  refine emptyE (singleton a) _;
  rewrite (eq_sym heq);
  refine UpairI1 (singleton a) (Upair a b)
end;

// Kuratowski content: Pair(a,b) = {{a}, {a,b}} — now true by definition.
// Kept as a named lemma since downstream proofs (e.g. Pair_not_Transset)
// refer to it to expose the set-theoretic structure of pairs.
opaque symbol Pair_def (a b : τ ι) :
  π (Pair a b = Upair (singleton a) (Upair a b)) ≔
begin
  assume a b; reflexivity
end;

// Pair(a,b) is not transitive: transitivity would require a ∈ Pair(a,b),
// giving a = {a} or a = {a,b}, both implying a ∈ a (contradicts Foundation).
opaque symbol Pair_not_Transset (a b : τ ι) :
  π (¬ (`∀ x : τ ι, x ∈ Pair a b ⇒ x ⊆ Pair a b)) ≔
begin
  assume a b hT;
  have hsin : π (singleton a ∈ Pair a b)
    { refine ind_eq (Pair_def a b) (λ s, singleton a ∈ s)
        (UpairI1 (singleton a) (Upair a b)) };
  have hsub : π (singleton a ⊆ Pair a b)
    { refine hT (singleton a) hsin };
  have haP : π (a ∈ Pair a b)
    { refine hsub a (singletonI a) };
  have haU : π (a ∈ Upair (singleton a) (Upair a b))
    { refine ind_eq (eq_sym (Pair_def a b)) (λ s, a ∈ s) haP };
  have hdisj : π (a = singleton a ∨ a = Upair a b)
    { refine UpairE a (singleton a) (Upair a b) haU };
  refine ∨ₑ hdisj _ _
  { assume heq;
    refine mem_irrefl a (ind_eq heq (λ s, a ∈ s) (singletonI a)) }
  { assume heq;
    refine mem_irrefl a (ind_eq heq (λ s, a ∈ s) (UpairI1 a b)) }
end;

// ---------------------------------------------------------------------------
// Projections fst/snd via definite description, and their conversions
// ---------------------------------------------------------------------------

// fst(p) = THE a. ∃b. p = ⟨a,b⟩      snd(p) = THE b. ∃a. p = ⟨a,b⟩
symbol fst (p : τ ι) : τ ι ≔ The (λ a, `∃ (b : τ ι), p = Pair a b);
symbol snd (p : τ ι) : τ ι ≔ The (λ b, `∃ (a : τ ι), p = Pair a b);

opaque symbol fst_conv (a b : τ ι) : π (fst (Pair a b) = a) ≔
begin
  assume a b;
  refine the_equality (λ x, `∃ (y : τ ι), Pair a b = Pair x y) a _ _
  { refine ∃ᵢ b (eq_refl (Pair a b)) }
  { assume x hx;
    refine ∃ₑ hx _;
    assume y hxy;
    refine eq_sym (Pair_inject1 a b x y hxy) }
end;

opaque symbol snd_conv (a b : τ ι) : π (snd (Pair a b) = b) ≔
begin
  assume a b;
  refine the_equality (λ y, `∃ (x : τ ι), Pair a b = Pair x y) b _ _
  { refine ∃ᵢ a (eq_refl (Pair a b)) }
  { assume y hy;
    refine ∃ₑ hy _;
    assume x hxy;
    refine eq_sym (Pair_inject2 a b x y hxy) }
end;

// ---------------------------------------------------------------------------
// split — split(c, p) = c(fst(p), snd(p))
// ---------------------------------------------------------------------------

symbol split (c : τ ι → τ ι → τ ι) (p : τ ι) : τ ι ≔ c (fst p) (snd p);

// ---------------------------------------------------------------------------
// Sigma — dependent product (set of ordered pairs)
// ---------------------------------------------------------------------------

// Sigma(A, B) = ⋃_{x ∈ A} { Pair(x, y) | y ∈ B(x) }
symbol Sigma (A : τ ι) (B : τ ι → τ ι) : τ ι ≔
  Union (RepFun A (λ x, RepFun (B x) (λ y, Pair x y)));

// SigmaI: x ∈ A → y ∈ B(x) → Pair(x,y) ∈ Sigma(A,B)
opaque symbol SigmaI (x y A : τ ι) (B : τ ι → τ ι) :
  π (x ∈ A) → π (y ∈ B x) → π (Pair x y ∈ Sigma A B) ≔
begin
  assume x y A B hxA hyB;
  // Pair(x,y) ∈ RepFun(B(x), λ z. Pair(x,z))
  have h1 : π (Pair x y ∈ RepFun (B x) (λ z, Pair x z))
    { refine RepFunI y (B x) (λ z, Pair x z) hyB };
  // RepFun(B(x), ...) ∈ RepFun(A, λ x. RepFun(B(x), ...))
  have h2 : π (RepFun (B x) (λ z, Pair x z) ∈ RepFun A (λ w, RepFun (B w) (λ z, Pair w z)))
    { refine RepFunI x A (λ w, RepFun (B w) (λ z, Pair w z)) hxA };
  // By UnionI
  refine UnionI (Pair x y) (RepFun (B x) (λ z, Pair x z))
    (RepFun A (λ w, RepFun (B w) (λ z, Pair w z))) h1 h2
end;

// SigmaE: p ∈ Sigma(A,B) → ∃x ∈ A. ∃y ∈ B(x). p = Pair(x,y)
opaque symbol SigmaE (p A : τ ι) (B : τ ι → τ ι) :
  π (p ∈ Sigma A B) → π (Bex A (λ x, Bex (B x) (λ y, p = Pair x y))) ≔
begin
  assume p A B hp;
  // p ∈ Union(RepFun A (λ x, RepFun (B x) (λ y, Pair x y)))
  // So ∃C ∈ RepFun(A, ...). p ∈ C
  have hbex : π (Bex (RepFun A (λ x, RepFun (B x) (λ y, Pair x y))) (λ C, p ∈ C))
    { refine UnionE p (RepFun A (λ x, RepFun (B x) (λ y, Pair x y))) hp };
  refine ∃ₑ hbex _;
  assume C hC;
  have hCmem : π (C ∈ RepFun A (λ x, RepFun (B x) (λ y, Pair x y))) { refine ∧ₑ₁ hC };
  have hpC : π (p ∈ C) { refine ∧ₑ₂ hC };
  // C ∈ RepFun(A, ...) → ∃x ∈ A. C = RepFun(B(x), λ y. Pair(x,y))
  have hbex2 : π (Bex A (λ x, C = RepFun (B x) (λ y, Pair x y)))
    { refine ∧ₑ₁ (RepFun_iff C A (λ x, RepFun (B x) (λ y, Pair x y))) hCmem };
  refine ∃ₑ hbex2 _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hCeq : π (C = RepFun (B x) (λ y, Pair x y)) { refine ∧ₑ₂ hx };
  // p ∈ C = RepFun(B(x), λ y. Pair(x,y))
  have hpRF : π (p ∈ RepFun (B x) (λ y, Pair x y))
    { refine ind_eq (eq_sym hCeq) (λ s, p ∈ s) hpC };
  // ∃y ∈ B(x). p = Pair(x,y)
  have hbex3 : π (Bex (B x) (λ y, p = Pair x y))
    { refine ∧ₑ₁ (RepFun_iff p (B x) (λ y, Pair x y)) hpRF };
  refine ∃ᵢ x (∧ᵢ hxA hbex3)
end;

// SigmaD1: p ∈ Sigma(A,B) → fst(p) ∈ A
opaque symbol SigmaD1 (p A : τ ι) (B : τ ι → τ ι) :
  π (p ∈ Sigma A B) → π (fst p ∈ A) ≔
begin
  assume p A B hp;
  have hbex : π (Bex A (λ x, Bex (B x) (λ y, p = Pair x y)))
    { refine SigmaE p A B hp };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  refine ∃ₑ (∧ₑ₂ hx) _;
  assume y hy;
  have hpeq : π (p = Pair x y) { refine ∧ₑ₂ hy };
  rewrite hpeq;
  rewrite (fst_conv x y);
  refine hxA
end;

// SigmaD2: p ∈ Sigma(A,B) → snd(p) ∈ B(fst(p))
opaque symbol SigmaD2 (p A : τ ι) (B : τ ι → τ ι) :
  π (p ∈ Sigma A B) → π (snd p ∈ B (fst p)) ≔
begin
  assume p A B hp;
  have hbex : π (Bex A (λ x, Bex (B x) (λ y, p = Pair x y)))
    { refine SigmaE p A B hp };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  refine ∃ₑ (∧ₑ₂ hx) _;
  assume y hy;
  have hyB : π (y ∈ B x) { refine ∧ₑ₁ hy };
  have hpeq : π (p = Pair x y) { refine ∧ₑ₂ hy };
  rewrite hpeq;
  rewrite (fst_conv x y);
  rewrite (snd_conv x y);
  refine hyB
end;

// Pair_fst_snd (surjective pairing): every element of a Sigma equals the pair
// of its projections.  p ∈ Sigma(A,B) → Pair(fst p, snd p) = p.
opaque symbol Pair_fst_snd (p A : τ ι) (B : τ ι → τ ι) :
  π (p ∈ Sigma A B) → π (Pair (fst p) (snd p) = p) ≔
begin
  assume p A B hp;
  refine ∃ₑ (SigmaE p A B hp) _; assume x hx;
  refine ∃ₑ (∧ₑ₂ hx) _; assume y hy;
  have hpeq : π (p = Pair x y) { refine ∧ₑ₂ hy };
  have hfst : π (fst p = x) { rewrite hpeq; refine fst_conv x y };
  have hsnd : π (snd p = y) { rewrite hpeq; refine snd_conv x y };
  rewrite hfst; rewrite hsnd; rewrite hpeq; reflexivity
end;

// ---------------------------------------------------------------------------
// Domain, range, converse, field
// ---------------------------------------------------------------------------

// domain(r) = { fst(p) | p ∈ r }  (but using Collect for the right form)
symbol domain (r : τ ι) : τ ι ≔
  RepFun (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = Pair x y))
    (λ p, fst p);

// domainI: Pair(a,b) ∈ r → a ∈ domain(r)
opaque symbol domainI (a b r : τ ι) :
  π (Pair a b ∈ r) → π (a ∈ domain r) ≔
begin
  assume a b r h;
  have hcoll : π (Pair a b ∈ Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    { refine CollectI (Pair a b) r
        (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y)
        h (∃ᵢ a (∃ᵢ b (eq_refl (Pair a b)))) };
  // RepFunI gives fst(Pair a b) ∈ domain(r); rewrite via fst_conv to get a.
  refine ind_eq (eq_sym (fst_conv a b)) (λ w, w ∈ domain r)
    (RepFunI (Pair a b)
      (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
      (λ p, fst p) hcoll)
end;

// domainE: a ∈ domain(r) → ∃b. Pair(a,b) ∈ r
opaque symbol domainE (a r : τ ι) :
  π (a ∈ domain r) → π (`∃ (b : τ ι), Pair a b ∈ r) ≔
begin
  assume a r h;
  have hbex : π (Bex (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    (λ p, a = fst p))
    { refine ∧ₑ₁ (RepFun_iff a
        (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
        (λ p, fst p)) h };
  refine ∃ₑ hbex _;
  assume p hp;
  have hpC : π (p ∈ Collect r (λ q, `∃ x : τ ι, `∃ y : τ ι, q = Pair x y))
    { refine ∧ₑ₁ hp };
  have hafst : π (a = fst p) { refine ∧ₑ₂ hp };
  have hpr : π (p ∈ r) { refine CollectD1 p r (λ q, `∃ x : τ ι, `∃ y : τ ι, q = Pair x y) hpC };
  have hpair : π (`∃ x : τ ι, `∃ y : τ ι, p = Pair x y)
    { refine CollectD2 p r (λ q, `∃ x : τ ι, `∃ y : τ ι, q = Pair x y) hpC };
  refine ∃ₑ hpair _;
  assume x hx;
  refine ∃ₑ hx _;
  assume y hy;
  // p = Pair(x,y), so fst(p) = x, and a = fst(p) = x
  // Pair(x,y) ∈ r, so Pair(a,y) ∈ r
  have hpeq : π (p = Pair x y) { refine hy };
  have hpr2 : π (Pair x y ∈ r) { refine ind_eq (eq_sym hpeq) (λ z, z ∈ r) hpr };
  // a = fst(p) = fst(Pair(x,y)) = x
  have hax : π (a = x) { rewrite hafst; rewrite hpeq; refine fst_conv x y };
  have hpr3 : π (Pair a y ∈ r)
    { refine ind_eq hax (λ z, Pair z y ∈ r) hpr2 };
  refine ∃ᵢ y hpr3
end;

// range(r) = { snd(p) | p ∈ r, p is a pair }
symbol range (r : τ ι) : τ ι ≔
  RepFun (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = Pair x y))
    (λ p, snd p);

// rangeI: Pair(a,b) ∈ r → b ∈ range(r)
opaque symbol rangeI (a b r : τ ι) :
  π (Pair a b ∈ r) → π (b ∈ range r) ≔
begin
  assume a b r h;
  have hcoll : π (Pair a b ∈ Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    { refine CollectI (Pair a b) r
        (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y)
        h (∃ᵢ a (∃ᵢ b (eq_refl (Pair a b)))) };
  refine ind_eq (eq_sym (snd_conv a b)) (λ w, w ∈ range r)
    (RepFunI (Pair a b)
      (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
      (λ p, snd p) hcoll)
end;

// rangeE: b ∈ range(r) → ∃a. Pair a b ∈ r
opaque symbol rangeE (b r : τ ι) :
  π (b ∈ range r) → π (`∃ a : τ ι, Pair a b ∈ r) ≔
begin
  assume b r h;
  // range(r) = RepFun(Collect r (λ p. ∃x∃y. p = Pair x y)) (λ p. snd p)
  // So b ∈ range(r) → ∃q ∈ Collect(...). b = snd q
  have hbex : π (Bex (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
                     (λ q, b = snd q))
    { refine ∧ₑ₁ (RepFun_iff b
        (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
        (λ p, snd p)) h };
  refine ∃ₑ hbex _;
  assume q hq;
  have hqC : π (q ∈ Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    { refine ∧ₑ₁ hq };
  have hbsnd : π (b = snd q) { refine ∧ₑ₂ hq };
  have hqr : π (q ∈ r)
    { refine CollectD1 q r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y) hqC };
  have hpair : π (`∃ x : τ ι, `∃ y : τ ι, q = Pair x y)
    { refine CollectD2 q r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y) hqC };
  // q = Pair x y for some x, y
  refine ∃ₑ hpair _;
  assume x hx;
  refine ∃ₑ hx _;
  assume y hy;
  // q = Pair x y, so snd q = y, and b = snd q = y
  have hqeq : π (q = Pair x y) { refine hy };
  have hsndy : π (snd q = y) { rewrite hqeq; refine snd_conv x y };
  have hby : π (b = y) { rewrite hbsnd; refine hsndy };
  // Pair x y ∈ r
  have hxyr : π (Pair x y ∈ r)
    { refine ind_eq (eq_sym hqeq) (λ z, z ∈ r) hqr };
  // Pair x b ∈ r (since b = y)
  refine ∃ᵢ x (ind_eq hby (λ w, Pair x w ∈ r) hxyr)
end;

// converse(r) = { Pair(y,x) | Pair(x,y) ∈ r }
symbol converse (r : τ ι) : τ ι ≔
  RepFun (Collect r (λ p, `∃ (x : τ ι), `∃ (y : τ ι), p = Pair x y))
    (λ p, Pair (snd p) (fst p));

// field(r) = domain(r) ∪ range(r)
symbol field (r : τ ι) : τ ι ≔ Un (domain r) (range r);

// ---------------------------------------------------------------------------
// Relational composition
// ---------------------------------------------------------------------------

// rcomp(r, s) = { Pair(x,z) | ∃y. Pair(x,y) ∈ s ∧ Pair(y,z) ∈ r }
symbol rcomp (r s : τ ι) : τ ι ≔
  Collect (Sigma (domain s) (λ _, range r))
    (λ p, `∃ (y : τ ι), Pair (fst p) y ∈ s ∧ Pair y (snd p) ∈ r);

// id_rel(A) = { Pair(x,x) | x ∈ A }
symbol id_rel (A : τ ι) : τ ι ≔ RepFun A (λ x, Pair x x);

// relation(r): every element of r is a pair
symbol relation (r : τ ι) : Prop ≔
  `∀ z : τ ι, z ∈ r ⇒ `∃ (x : τ ι), `∃ (y : τ ι), z = Pair x y;

// ---------------------------------------------------------------------------
// Pi — function space
// ---------------------------------------------------------------------------

// Pi (dependent function space) is defined in func.lp — its proper home.
// A duplicate ∃!-style definition previously lived here; removed so there is a
// single `Pi` (avoids two same-named definitions in scope downstream).

symbol function (f : τ ι) : Prop ≔
  `∀ x : τ ι, `∀ y : τ ι, `∀ y' : τ ι,
    Pair x y ∈ f ⇒ Pair x y' ∈ f ⇒ y = y';

// ---------------------------------------------------------------------------
// Lambda and fapply (function application)
// ---------------------------------------------------------------------------

// Lambda(A, b) = { Pair(x, b(x)) | x ∈ A }
symbol Lambda (A : τ ι) (b : τ ι → τ ι) : τ ι ≔
  RepFun A (λ x, Pair x (b x));

// fapply(f, a) = The(λ y. Pair(a,y) ∈ f)
symbol fapply (f a : τ ι) : τ ι ≔
  The (λ y, Pair a y ∈ f);

// ---------------------------------------------------------------------------
// vimage_singleton — preimage of a single element
// ---------------------------------------------------------------------------

symbol vimage_singleton (r a : τ ι) : τ ι ≔
  Collect (domain r) (λ x, Pair x a ∈ r);

// x ∈ vimage_singleton r a ← Pair x a ∈ r
opaque symbol vimage_singletonI (x a r : τ ι) :
  π (Pair x a ∈ r) → π (x ∈ vimage_singleton r a) ≔
begin
  assume x a r h;
  refine CollectI x (domain r) (λ z, Pair z a ∈ r) (domainI x a r h) h
end;

// x ∈ vimage_singleton r a → Pair x a ∈ r
opaque symbol vimage_singletonD (x a r : τ ι) :
  π (x ∈ vimage_singleton r a) → π (Pair x a ∈ r) ≔
begin
  assume x a r h;
  refine CollectD2 x (domain r) (λ z, Pair z a ∈ r) h
end;

// restrict is defined in func.lp — its proper home. A DIVERGENT duplicate lived
// here (`{p ∈ f | fst p ∈ A}`, differing from Isabelle/func on non-pairs); removed.

// ===========================================================================
// field_rel_subset: r ⊆ A*A → field(r) ⊆ A   (from Order.thy / WF infra)
//   field(r) = domain(r) ∪ range(r); both project into A when r ⊆ A*A.
// ===========================================================================
opaque symbol field_rel_subset (r A : τ ι) :
  π (r ⊆ Sigma A (λ _, A)) → π (field r ⊆ A) ≔
begin
  assume r A hsub x hx;
  // hx : x ∈ field r = Un (domain r) (range r)
  have hor : π (x ∈ domain r ∨ x ∈ range r)
    { refine UnE x (domain r) (range r) hx };
  refine ∨ₑ hor _ _
  { // x ∈ domain r : ∃b. Pair x b ∈ r ⊆ A*A, so fst = x ∈ A
    assume hdom;
    refine ∃ₑ (domainE x r hdom) _;
    assume b hb;
    have hS : π (Pair x b ∈ Sigma A (λ _, A)) { refine hsub (Pair x b) hb };
    refine ind_eq (eq_sym (fst_conv x b)) (λ w, w ∈ A)
      (SigmaD1 (Pair x b) A (λ _, A) hS) }
  { // x ∈ range r : ∃a. Pair a x ∈ r ⊆ A*A, so snd = x ∈ A
    assume hran;
    refine ∃ₑ (rangeE x r hran) _;
    assume a ha;
    have hS : π (Pair a x ∈ Sigma A (λ _, A)) { refine hsub (Pair a x) ha };
    refine ind_eq (eq_sym (snd_conv a x)) (λ w, w ∈ A)
      (SigmaD2 (Pair a x) A (λ _, A) hS) }
end;
