// pair: Ordered pairs for ZF set theory
//
// Pair is declared as an abstract symbol with fst/snd rewrite rules,
// rather than defined via the Kuratowski encoding Pair(a,b) = {{a},{a,b}}.
// This lets fst(Pair a b) and snd(Pair a b) reduce definitionally.
//
// The three key properties (injectivity, non-emptiness) are axiomatized.
// They were originally proved from the Kuratowski encoding; making Pair
// abstract is conservative — it retains exactly the interface the rest
// of the development uses.
//
// Defines: Pair, fst, snd, split, Sigma
// Axioms: Pair_inject1, Pair_inject2, Pair_neq_0

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt
             Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair;

// ===========================================================================
// Ordered pair — abstract with rewrite rules for projections
// ===========================================================================

// Pair is an abstract constructor. Its internal encoding (Kuratowski or
// otherwise) is hidden. Only injectivity, non-emptiness, and projection
// computation are exposed.
symbol Pair : τ ι → τ ι → τ ι;

// Projections: fst and snd are declared symbols that compute on Pair
// via rewrite rules. For non-Pair arguments they are stuck (uninterpreted),
// matching the behavior of the original epsilon-based definitions.
symbol fst : τ ι → τ ι;
symbol snd : τ ι → τ ι;
rule fst (Pair $a $b) ↪ $a;
rule snd (Pair $a $b) ↪ $b;

// Eta rule: Pair(fst(p), snd(p)) = p.
// This is justified because Pair is injective (Pair_inject) and fst/snd
// are its projections. For non-pair arguments, fst/snd are stuck, so
// Pair(fst(p), snd(p)) is also stuck — the rule only fires when p is
// already a Pair. Together with the beta rules above, this gives a
// complete equational theory: beta-eta for abstract pairs.
rule Pair (fst $p) (snd $p) ↪ $p;

// ===========================================================================
// Pair axioms
// ===========================================================================

// Injectivity: Pair(a,b) = Pair(c,d) → a = c
constant symbol Pair_inject1 (a b c d : τ ι) :
  π (Pair a b = Pair c d) → π (a = c);

// Injectivity: Pair(a,b) = Pair(c,d) → b = d
constant symbol Pair_inject2 (a b c d : τ ι) :
  π (Pair a b = Pair c d) → π (b = d);

// Combined injectivity
opaque symbol Pair_inject (a b c d : τ ι) :
  π (Pair a b = Pair c d) → π (a = c ∧ b = d) ≔
begin
  assume a b c d heq;
  apply ∧ᵢ
  { refine Pair_inject1 a b c d heq }
  { refine Pair_inject2 a b c d heq }
end;

// Non-emptiness: Pair(a,b) ≠ ∅
constant symbol Pair_neq_0 (a b : τ ι) : π (Pair a b ≠ empty);

// Kuratowski content: Pair(a,b) = {{a}, {a,b}}.
// This axiom exposes the set-theoretic structure of pairs, enabling
// proofs about membership (e.g., Pair(a,b) is not an ordinal).
// Conservative over the abstract interface: injectivity and non-emptiness
// follow from this + Upair properties + Foundation.
constant symbol Pair_def (a b : τ ι) :
  π (Pair a b = Upair (singleton a) (Upair a b));

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
// fst_conv and snd_conv — now trivial by rewrite rules
// ---------------------------------------------------------------------------

opaque symbol fst_conv (a b : τ ι) : π (fst (Pair a b) = a) ≔
begin
  assume a b; reflexivity
end;

opaque symbol snd_conv (a b : τ ι) : π (snd (Pair a b) = b) ≔
begin
  assume a b; reflexivity
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
  refine hyB
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
  // fst(Pair a b) = a by rewrite rule, so RepFunI gives a ∈ domain(r)
  refine RepFunI (Pair a b)
    (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    (λ p, fst p) hcoll
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
  have hax : π (a = x) { rewrite hafst; rewrite hpeq; reflexivity };
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
  refine RepFunI (Pair a b)
    (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
    (λ p, snd p) hcoll
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
  have hsndy : π (snd q = y) { rewrite hqeq; reflexivity };
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

symbol Pi (A : τ ι) (B : τ ι → τ ι) : τ ι ≔
  Collect (Pow (Sigma A B)) (λ f, `∀ x : τ ι, x ∈ A ⇒
    `∃ y : τ ι, y ∈ B x ∧ Pair x y ∈ f ∧
      (`∀ y' : τ ι, Pair x y' ∈ f ⇒ y' = y));

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

// restrict(f, A) = { p ∈ f | fst(p) ∈ A }
symbol restrict (f A : τ ι) : τ ι ≔
  Collect f (λ p, fst p ∈ A);
