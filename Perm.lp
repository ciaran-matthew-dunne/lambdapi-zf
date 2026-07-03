// Perm: Injections, Surjections, Bijections, Composition
//
// Isabelle source: Perm.thy
// The theory underlying permutation groups:
//   -- Composition of relations, the identity relation
//   -- Injections, surjections, bijections
//   -- Lemmas for the Schroeder-Bernstein Theorem

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt
             Stdlib.Epsilon;
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
// TODO: prove — needs range_of_fun, apply_equality, domain_type
opaque symbol fun_is_surj (f A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (f ∈ surj A (range f)) ≔
begin
  assume f A B hf;
  admit
end;

// surj_range: f ∈ surj(A,B) → range(f) = B
// TODO: prove — needs apply_Pair, range_type
opaque symbol surj_range (f A B : τ ι) :
  π (f ∈ surj A B) → π (range f = B) ≔
begin
  assume f A B hf;
  admit
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

// bij_inverse_exists: f ∈ bij(A,B) → ∃g∈B→A. ∀a∈A. g`(f`a)=a ∧ f`(g`(f`a))=f`a
// TODO: prove — needs inj/surj properties
opaque symbol bij_inverse_exists (f A B : τ ι) :
  π (f ∈ bij A B) →
  π (Bex (Pi B (λ _, A)) (λ g,
    Ball A (λ a, fapply g (fapply f a) = a ∧ fapply f (fapply g (fapply f a)) = fapply f a))) ≔
begin
  assume f A B hf;
  admit
end;

// ===========================================================================
// Section: Composition helper lemmas (selected)
// ===========================================================================

// comp_mono: r ⊆ r' → s ⊆ s' → comp(r,s) ⊆ comp(r',s')
opaque symbol comp_mono (r r' s s' : τ ι) :
  π (r ⊆ r') → π (s ⊆ s') → π (rcomp r s ⊆ rcomp r' s') ≔
begin
  assume r r' s s' hr hs p hp;
  admit
end;

// rcomp_Int_subset: rcomp(r∩r', s∩s') ⊆ rcomp(r,s) ∩ rcomp(r',s')
opaque symbol rcomp_Int_subset (r r' s s' : τ ι) :
  π (rcomp (Int r r') (Int s s') ⊆ Int (rcomp r s) (rcomp r' s')) ≔
begin
  assume r r' s s' p hp;
  admit
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
    { refine RepFunI (Pair a b)
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
  have hbex : π (Bex (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
                     (λ q, Pair a b = Pair (snd q) (fst q)))
    { refine ∧ₑ₁ (RepFun_iff (Pair a b)
        (Collect r (λ p, `∃ x : τ ι, `∃ y : τ ι, p = Pair x y))
        (λ p, Pair (snd p) (fst p))) h };
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
  have hPow : π (f ∈ Pow (Sigma A B)) { refine CollectD1 f (Pow (Sigma A B)) _ hfPi };
  have hsub : π (f ⊆ Sigma A B) { refine PowD f (Sigma A B) hPow };
  have hSig : π (Pair a b ∈ Sigma A B) { refine subsetD f (Sigma A B) (Pair a b) hsub hmem };
  refine ind_eq (eq_sym (fst_conv a b)) (λ w, w ∈ A) (SigmaD1 (Pair a b) A B hSig)
end;

// range_type: Pair(a,b) ∈ f → f ∈ Pi(A,B) → b ∈ B(a)
opaque symbol range_type (a b f A : τ ι) (B : τ ι → τ ι) :
  π (Pair a b ∈ f) → π (f ∈ Pi A B) → π (b ∈ B a) ≔
begin
  assume a b f A B hmem hfPi;
  have hPow : π (f ∈ Pow (Sigma A B)) { refine CollectD1 f (Pow (Sigma A B)) _ hfPi };
  have hsub : π (f ⊆ Sigma A B) { refine PowD f (Sigma A B) hPow };
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
