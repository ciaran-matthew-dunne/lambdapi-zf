// func: ZF functions as sets of ordered pairs
//
// Isabelle source: func.thy (subset)
// Defines: function, fapply, Lambda, Pi, restrict, Image
// Proves: beta, lam_type, fapply_type, fun_extension, eta

require open ZF.ZF_Base ZF.upair ZF.pair;

// ===========================================================================
// Function predicate
// ===========================================================================

// function(f) ≡ ∀x y y'. Pair(x,y) ∈ f → Pair(x,y') ∈ f → y = y'
constant symbol function (f : τ ι) : Prop;
constant symbol function_def (f : τ ι) :
  π (function f = (`∀ (x : τ ι), `∀ (y : τ ι), `∀ (yp : τ ι),
    Pair x y ∈ f ⇒ Pair x yp ∈ f ⇒ y = yp));

// functionD: unfold a function-hypothesis to its ∀-form (via function_def).
opaque symbol functionD (f : τ ι) :
  π (function f) →
  π (`∀ (x : τ ι), `∀ (y : τ ι), `∀ (yp : τ ι),
     Pair x y ∈ f ⇒ Pair x yp ∈ f ⇒ y = yp) ≔
begin
  assume f h;
  refine ind_eq (eq_sym (function_def f)) (λ p, p) h
end;

// ===========================================================================
// Function application — fapply(f, a) = The(λ y. Pair(a,y) ∈ f)
// ===========================================================================

constant symbol fapply (f a : τ ι) : τ ι;
constant symbol fapply_def (f a : τ ι) :
  π (fapply f a = The (λ y, Pair a y ∈ f));

// ===========================================================================
// Lambda — Lambda(A, b) = {Pair(x, b(x)) | x ∈ A}
// ===========================================================================

constant symbol Lambda (A : τ ι) (b : τ ι → τ ι) : τ ι;
constant symbol Lambda_def (A : τ ι) (b : τ ι → τ ι) :
  π (Lambda A b = RepFun A (λ x, Pair x (b x)));

// ===========================================================================
// Pi — dependent function space
// Pi(A, B) = {f ∈ Pow(Sigma(A, ⋃B)) | A ⊆ domain(f)}
// Actually: Pi(A, B) = {f ∈ Pow(Sigma(A,B)). A ⊆ domain(f)}
// where B : τ ι → τ ι
// ===========================================================================

constant symbol Pi (A : τ ι) (B : τ ι → τ ι) : τ ι;
constant symbol Pi_def (A : τ ι) (B : τ ι → τ ι) :
  π (Pi A B = Collect (Pow (Sigma A B)) (λ f, A ⊆ domain f ∧ function f));

// ===========================================================================
// Restrict — restrict(f, A) = {p ∈ f | ∃x∈A. ∃y. p = Pair(x,y)}
// ===========================================================================

constant symbol restrict (f A : τ ι) : τ ι;
constant symbol restrict_def (f A : τ ι) :
  π (restrict f A = Collect f (λ p, Bex A (λ x, `∃ (y : τ ι), p = Pair x y)));

// ===========================================================================
// Image — Image(f, C) = {fapply(f,x) | x ∈ C ∩ domain(f)}
// CAVEAT: this is the FUNCTION image. It agrees with Isabelle's relational
// image f``C whenever `function f` holds, but diverges on non-functions
// (fapply collapses multi-valued points). Statements about arbitrary
// relations must use ZF.pair's rel_image_sing (Isabelle's r``{a}) instead.
// ===========================================================================

constant symbol Image (f C : τ ι) : τ ι;
constant symbol Image_def (f C : τ ι) :
  π (Image f C = RepFun (Int C (domain f)) (λ x, fapply f x));

// ===========================================================================
// Key Theorems
// ===========================================================================

// ---------------------------------------------------------------------------
// Lambda membership: Pair(a, b(a)) ∈ Lambda(A, b) when a ∈ A
// ---------------------------------------------------------------------------

opaque symbol LambdaI (a A : τ ι) (b : τ ι → τ ι) :
  π (a ∈ A) → π (Pair a (b a) ∈ Lambda A b) ≔
begin
  assume a A b ha;
  rewrite Lambda_def;
  refine RepFunI a A (λ x, Pair x (b x)) ha
end;

// Lambda is a function
opaque symbol Lambda_function (A : τ ι) (b : τ ι → τ ι) :
  π (function (Lambda A b)) ≔
begin
  assume A b;
  rewrite function_def;
  assume x y yp h1 h2;
  // h1 : Pair(x,y) ∈ Lambda(A,b) — unfold to RepFun form via Lambda_def
  // h2 : Pair(x,yp) ∈ Lambda(A,b)
  have h1' : π (Pair x y ∈ RepFun A (λ z, Pair z (b z)))
    { refine ind_eq (eq_sym (Lambda_def A b)) (λ s, Pair x y ∈ s) h1 };
  have h2' : π (Pair x yp ∈ RepFun A (λ z, Pair z (b z)))
    { refine ind_eq (eq_sym (Lambda_def A b)) (λ s, Pair x yp ∈ s) h2 };
  have hbex1 : π (Bex A (λ z, Pair x y = Pair z (b z)))
    { refine ∧ₑ₁ (RepFun_iff (Pair x y) A (λ z, Pair z (b z))) h1' };
  have hbex2 : π (Bex A (λ z, Pair x yp = Pair z (b z)))
    { refine ∧ₑ₁ (RepFun_iff (Pair x yp) A (λ z, Pair z (b z))) h2' };
  refine ∃ₑ hbex1 _;
  assume z1 hz1;
  have hz1A : π (z1 ∈ A) { refine ∧ₑ₁ hz1 };
  have heq1 : π (Pair x y = Pair z1 (b z1)) { refine ∧ₑ₂ hz1 };
  have hy : π (y = b z1) { refine Pair_inject2 x y z1 (b z1) heq1 };
  have hxz1 : π (x = z1) { refine Pair_inject1 x y z1 (b z1) heq1 };
  refine ∃ₑ hbex2 _;
  assume z2 hz2;
  have heq2 : π (Pair x yp = Pair z2 (b z2)) { refine ∧ₑ₂ hz2 };
  have hyp : π (yp = b z2) { refine Pair_inject2 x yp z2 (b z2) heq2 };
  have hxz2 : π (x = z2) { refine Pair_inject1 x yp z2 (b z2) heq2 };
  // z1 = x = z2, so b(z1) = b(z2)
  have hxz1s : π (z1 = x) { symmetry; apply hxz1 };
  have hz12 : π (z1 = z2)
    { rewrite hxz1s; apply hxz2 };
  rewrite hy; rewrite hyp;
  rewrite hz12; reflexivity
end;

// ---------------------------------------------------------------------------
// Beta: a ∈ A → fapply(Lambda(A,b), a) = b(a)
// ---------------------------------------------------------------------------

opaque symbol beta (A : τ ι) (b : τ ι → τ ι) (a : τ ι) :
  π (a ∈ A) → π (fapply (Lambda A b) a = b a) ≔
begin
  assume A b a ha;
  // fapply(Lambda(A,b), a) = The(λ y. Pair(a,y) ∈ Lambda(A,b)); the
  // description is unique because Lambda is functional, so the_equality
  // applies with witness b(a).
  have hmem : π (Pair a (b a) ∈ Lambda A b) { refine LambdaI a A b ha };
  rewrite fapply_def;
  refine the_equality (λ y, Pair a y ∈ Lambda A b) (b a) hmem _;
  assume y hy;
  refine functionD (Lambda A b) (Lambda_function A b) a y (b a) hy hmem
end;

// ---------------------------------------------------------------------------
// Lambda domain: domain(Lambda(A,b)) = A  (we prove ⊇ and ⊆)
// ---------------------------------------------------------------------------

opaque symbol Lambda_domain_subset (A : τ ι) (b : τ ι → τ ι) :
  π (A ⊆ domain (Lambda A b)) ≔
begin
  assume A b x hx;
  refine domainI x (b x) (Lambda A b) (LambdaI x A b hx)
end;

opaque symbol domain_Lambda_subset (A : τ ι) (b : τ ι → τ ι) :
  π (domain (Lambda A b) ⊆ A) ≔
begin
  assume A b x hx;
  have hex : π (`∃ (y : τ ι), Pair x y ∈ Lambda A b)
    { refine domainE x (Lambda A b) hx };
  refine ∃ₑ hex _;
  assume y hy;
  have hy' : π (Pair x y ∈ RepFun A (λ z, Pair z (b z)))
    { refine ind_eq (eq_sym (Lambda_def A b)) (λ s, Pair x y ∈ s) hy };
  have hbex : π (Bex A (λ z, Pair x y = Pair z (b z)))
    { refine ∧ₑ₁ (RepFun_iff (Pair x y) A (λ z, Pair z (b z))) hy' };
  refine ∃ₑ hbex _;
  assume z hz;
  have hzA : π (z ∈ A) { refine ∧ₑ₁ hz };
  have heq : π (Pair x y = Pair z (b z)) { refine ∧ₑ₂ hz };
  have hxz : π (x = z) { refine Pair_inject1 x y z (b z) heq };
  rewrite hxz; apply hzA
end;

// ---------------------------------------------------------------------------
// Lambda subset Sigma: Lambda(A,b) ⊆ Sigma(A, B) when ∀x∈A. b(x) ∈ B(x)
// ---------------------------------------------------------------------------

opaque symbol Lambda_subset_Sigma (A : τ ι) (b : τ ι → τ ι) (B : τ ι → τ ι) :
  π (Ball A (λ x, b x ∈ B x)) → π (Lambda A b ⊆ Sigma A B) ≔
begin
  assume A b B hall p hp;
  // p ∈ Lambda(A,b) = RepFun(A, λx. Pair(x,b(x)))
  have hp' : π (p ∈ RepFun A (λ x, Pair x (b x)))
    { refine ind_eq (eq_sym (Lambda_def A b)) (λ s, p ∈ s) hp };
  have hbex : π (Bex A (λ x, p = Pair x (b x)))
    { refine ∧ₑ₁ (RepFun_iff p A (λ x, Pair x (b x))) hp' };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hpeq : π (p = Pair x (b x)) { refine ∧ₑ₂ hx };
  have hbxB : π (b x ∈ B x) { refine hall x hxA };
  rewrite hpeq;
  refine SigmaI x (b x) A B hxA hbxB
end;

// ---------------------------------------------------------------------------
// lam_type: Ball A (λ x, b(x) ∈ B(x)) → Lambda(A,b) ∈ Pi(A,B)
// ---------------------------------------------------------------------------

opaque symbol lam_type (A : τ ι) (b : τ ι → τ ι) (B : τ ι → τ ι) :
  π (Ball A (λ x, b x ∈ B x)) → π (Lambda A b ∈ Pi A B) ≔
begin
  assume A b B hall;
  // Pi(A,B) = Collect(Pow(Sigma(A,B)), λ f. A ⊆ domain(f) ∧ function(f))
  rewrite Pi_def;
  refine CollectI (Lambda A b) (Pow (Sigma A B))
    (λ f, A ⊆ domain f ∧ function f) _ _
  { // Lambda(A,b) ∈ Pow(Sigma(A,B))
    refine PowI (Lambda A b) (Sigma A B) (Lambda_subset_Sigma A b B hall) }
  { // A ⊆ domain(Lambda(A,b)) ∧ function(Lambda(A,b))
    apply ∧ᵢ
    { refine Lambda_domain_subset A b }
    { refine Lambda_function A b } }
end;

// ---------------------------------------------------------------------------
// Pi implies function and relation
// ---------------------------------------------------------------------------

opaque symbol Pi_function (f A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (function f) ≔
begin
  assume f A B hf;
  // Pi(A,B) = Collect(Pow(Sigma(A,B)), λ f. A ⊆ domain(f) ∧ function(f))
  have hf' : π (f ∈ Collect (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g))
    { refine ind_eq (eq_sym (Pi_def A B)) (λ s, f ∈ s) hf };
  have hcond : π (A ⊆ domain f ∧ function f)
    { refine CollectD2 f (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g) hf' };
  refine ∧ₑ₂ hcond
end;

opaque symbol Pi_relation (f A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (relation f) ≔
begin
  assume f A B hf;
  // f ∈ Pow(Sigma(A,B)), so f ⊆ Sigma(A,B)
  have hf' : π (f ∈ Collect (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g))
    { refine ind_eq (eq_sym (Pi_def A B)) (λ s, f ∈ s) hf };
  have hpow : π (f ∈ Pow (Sigma A B))
    { refine CollectD1 f (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g) hf' };
  have hsub : π (f ⊆ Sigma A B) { refine PowD f (Sigma A B) hpow };
  // relation(f) = ∀p∈f. ∃x y. p = Pair(x,y)
  rewrite relation_def;
  assume p hp;
  // p ∈ f and f ⊆ Sigma(A,B), so p ∈ Sigma(A,B)
  have hpS : π (p ∈ Sigma A B) { refine hsub p hp };
  // By SigmaE: ∃x∈A. ∃y∈B(x). p = Pair(x,y)
  have hbex : π (Bex A (λ x, Bex (B x) (λ y, p = Pair x y)))
    { refine SigmaE p A B hpS };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hbex2 : π (Bex (B x) (λ y, p = Pair x y)) { refine ∧ₑ₂ hx };
  refine ∃ₑ hbex2 _;
  assume y hy;
  have hyB : π (y ∈ B x) { refine ∧ₑ₁ hy };
  have hpeq : π (p = Pair x y) { refine ∧ₑ₂ hy };
  refine ∃ᵢ x (∃ᵢ y hpeq)
end;

// Image_iff: z ∈ Image(f,C) ⟷ ∃x ∈ C ∩ domain(f). z = f`x  (function image)
opaque symbol Image_iff (z f C : τ ι) :
  π ((z ∈ Image f C) ⇔ Bex (Int C (domain f)) (λ x, z = fapply f x)) ≔
begin
  assume z f C;
  rewrite Image_def;
  refine RepFun_iff z (Int C (domain f)) (λ x, fapply f x)
end;

// Pi_iff (Isabelle func.thy): membership in Pi unpacked to its three parts.
// The one-stop interface for Pi — use it instead of unfolding Pi_def raw.
opaque symbol Pi_iff (f A : τ ι) (B : τ ι → τ ι) :
  π ((f ∈ Pi A B) ⇔ (function f ∧ (f ⊆ Sigma A B ∧ A ⊆ domain f))) ≔
begin
  assume f A B;
  rewrite Pi_def;
  apply ∧ᵢ
  { assume h;
    have h1 : π (f ∈ Pow (Sigma A B))
      { refine CollectD1 f (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g) h };
    have h2 : π (A ⊆ domain f ∧ function f)
      { refine CollectD2 f (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g) h };
    refine ∧ᵢ (∧ₑ₂ h2) (∧ᵢ (PowD f (Sigma A B) h1) (∧ₑ₁ h2)) }
  { assume h;
    refine CollectI f (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g)
      (PowI f (Sigma A B) (∧ₑ₁ (∧ₑ₂ h))) (∧ᵢ (∧ₑ₂ (∧ₑ₂ h)) (∧ₑ₁ h)) }
end;

// ---------------------------------------------------------------------------
// fapply_type: f ∈ Pi(A,B) → a ∈ A → fapply(f,a) ∈ B(a)
// ---------------------------------------------------------------------------

// Helper: function(f) → a ∈ domain(f) → Pair(a, fapply(f,a)) ∈ f
opaque symbol apply_Pair (f a : τ ι) :
  π (function f) → π (a ∈ domain f) → π (Pair a (fapply f a) ∈ f) ≔
begin
  assume f a hfunc hdom;
  // a ∈ domain(f) → ∃y. Pair(a,y) ∈ f; function(f) makes that y unique,
  // so theI yields Pair(a, The(λy. Pair(a,y) ∈ f)) ∈ f.
  rewrite fapply_def;
  have hex : π (`∃ (y : τ ι), Pair a y ∈ f) { refine domainE a f hdom };
  refine ∃ₑ hex _;
  assume y hy;
  have huniq : π (`∀ (z : τ ι), Pair a z ∈ f ⇒ z = y)
    { assume z hz; refine functionD f hfunc a z y hz hy };
  refine theI (λ y, Pair a y ∈ f) (∃ᵢ y (∧ᵢ hy huniq))
end;

// Helper: f ∈ Pi(A,B) → a ∈ A → Pair(a, fapply(f,a)) ∈ f
opaque symbol Pi_apply_Pair (f a A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (a ∈ A) → π (Pair a (fapply f a) ∈ f) ≔
begin
  assume f a A B hf ha;
  have hfunc : π (function f) { refine Pi_function f A B hf };
  have hf' : π (f ∈ Collect (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g))
    { refine ind_eq (eq_sym (Pi_def A B)) (λ s, f ∈ s) hf };
  have hcond : π (A ⊆ domain f ∧ function f)
    { refine CollectD2 f (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g) hf' };
  have hAsub : π (A ⊆ domain f) { refine ∧ₑ₁ hcond };
  have hdom : π (a ∈ domain f) { refine hAsub a ha };
  refine apply_Pair f a hfunc hdom
end;

// Helper: f ∈ Pi(A,B) → f ⊆ Sigma(A,B)
opaque symbol Pi_subset_Sigma (f A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (f ⊆ Sigma A B) ≔
begin
  assume f A B hf;
  have hf' : π (f ∈ Collect (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g))
    { refine ind_eq (eq_sym (Pi_def A B)) (λ s, f ∈ s) hf };
  have hpow : π (f ∈ Pow (Sigma A B))
    { refine CollectD1 f (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g) hf' };
  refine PowD f (Sigma A B) hpow
end;

opaque symbol fapply_type (f a A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (a ∈ A) → π (fapply f a ∈ B a) ≔
begin
  assume f a A B hf ha;
  have hmem : π (Pair a (fapply f a) ∈ f) { refine Pi_apply_Pair f a A B hf ha };
  have hsub : π (f ⊆ Sigma A B) { refine Pi_subset_Sigma f A B hf };
  have hpS : π (Pair a (fapply f a) ∈ Sigma A B) { refine hsub (Pair a (fapply f a)) hmem };
  // SigmaE gives ∃x∈A. ∃y∈B(x). Pair(a, fapply(f,a)) = Pair(x,y)
  have hbex : π (Bex A (λ x, Bex (B x) (λ y, Pair a (fapply f a) = Pair x y)))
    { refine SigmaE (Pair a (fapply f a)) A B hpS };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hbex2 : π (Bex (B x) (λ y, Pair a (fapply f a) = Pair x y)) { refine ∧ₑ₂ hx };
  refine ∃ₑ hbex2 _;
  assume y hy;
  have hyB : π (y ∈ B x) { refine ∧ₑ₁ hy };
  have hpeq : π (Pair a (fapply f a) = Pair x y) { refine ∧ₑ₂ hy };
  have hax : π (a = x) { refine Pair_inject1 a (fapply f a) x y hpeq };
  have hfy : π (fapply f a = y) { refine Pair_inject2 a (fapply f a) x y hpeq };
  rewrite hfy;
  rewrite hax;
  apply hyB
end;

// ---------------------------------------------------------------------------
// fun_extension: f ∈ Pi(A,B) → g ∈ Pi(A,B) → Ball A (λ x, fapply(f,x) = fapply(g,x)) → f = g
// ---------------------------------------------------------------------------

// Helper: Pair(a,b) ∈ f → function(f) → fapply(f,a) = b
opaque symbol function_apply_equality (a b f : τ ι) :
  π (Pair a b ∈ f) → π (function f) → π (fapply f a = b) ≔
begin
  assume a b f hmem hfunc;
  // fapply(f,a) = The(λ y. Pair(a,y) ∈ f); b is the unique such y because
  // f is a function, so the_equality closes the goal directly.
  rewrite fapply_def;
  refine the_equality (λ y, Pair a y ∈ f) b hmem _;
  assume z hz;
  refine functionD f hfunc a z b hz hmem
end;

// Helper: f ∈ Pi(A,B) → domain(f) = A
opaque symbol domain_of_fun (f A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (domain f = A) ≔
begin
  assume f A B hf;
  have hsub : π (f ⊆ Sigma A B) { refine Pi_subset_Sigma f A B hf };
  have hf' : π (f ∈ Collect (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g))
    { refine ind_eq (eq_sym (Pi_def A B)) (λ s, f ∈ s) hf };
  have hcond : π (A ⊆ domain f ∧ function f)
    { refine CollectD2 f (Pow (Sigma A B)) (λ g, A ⊆ domain g ∧ function g) hf' };
  have hAsub : π (A ⊆ domain f) { refine ∧ₑ₁ hcond };
  // domain(f) ⊆ A: if x ∈ domain(f), then ∃y. Pair(x,y) ∈ f ⊆ Sigma(A,B),
  // so by SigmaE, x ∈ A
  have hdomsub : π (domain f ⊆ A)
  { assume x hx;
    have hex : π (`∃ (y : τ ι), Pair x y ∈ f) { refine domainE x f hx };
    refine ∃ₑ hex _;
    assume y hy;
    have hpS : π (Pair x y ∈ Sigma A B) { refine hsub (Pair x y) hy };
    have hbex : π (Bex A (λ a, Bex (B a) (λ b, Pair x y = Pair a b)))
      { refine SigmaE (Pair x y) A B hpS };
    refine ∃ₑ hbex _;
    assume a ha;
    have haA : π (a ∈ A) { refine ∧ₑ₁ ha };
    have hbex2 : π (Bex (B a) (λ b, Pair x y = Pair a b)) { refine ∧ₑ₂ ha };
    refine ∃ₑ hbex2 _;
    assume b hb;
    have hpeq : π (Pair x y = Pair a b) { refine ∧ₑ₂ hb };
    have hxa : π (x = a) { refine Pair_inject1 x y a b hpeq };
    rewrite hxa; apply haA };
  refine subset_antisym (domain f) A hdomsub hAsub
end;

// fun_subset: f ∈ Pi(A,B) → g ∈ Pi(C,D) → A ⊆ C →
//   Ball A (λ x, fapply f x = fapply g x) → f ⊆ g
opaque symbol fun_subset (f g A : τ ι) (B : τ ι → τ ι) (C : τ ι) (D : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (g ∈ Pi C D) → π (A ⊆ C) →
  π (Ball A (λ x, fapply f x = fapply g x)) → π (f ⊆ g) ≔
begin
  assume f g A B C D hf hg hAC hall p hp;
  // p ∈ f. Since f is a relation, ∃x y. p = Pair(x,y)
  have hrel : π (relation f) { refine Pi_relation f A B hf };
  have hrel' : π (`∀ (z : τ ι), z ∈ f ⇒ `∃ (u : τ ι), `∃ (v : τ ι), z = Pair u v)
    { refine ind_eq (eq_sym (relation_def f)) (λ q, q) hrel };
  have hpair : π (`∃ (u : τ ι), `∃ (v : τ ι), p = Pair u v)
    { refine hrel' p hp };
  refine ∃ₑ hpair _;
  assume u hu;
  refine ∃ₑ hu _;
  assume v hpeq;
  // p = Pair(u,v) and Pair(u,v) ∈ f
  have hmem : π (Pair u v ∈ f) { rewrite left hpeq; apply hp };
  // fapply(f,u) = v
  have hfunc : π (function f) { refine Pi_function f A B hf };
  have hfv : π (fapply f u = v) { refine function_apply_equality u v f hmem hfunc };
  // u ∈ domain(f) = A
  have hdom : π (domain f = A) { refine domain_of_fun f A B hf };
  have hudom : π (u ∈ domain f) { refine domainI u v f hmem };
  have huA : π (u ∈ A) { refine ind_eq (eq_sym hdom) (λ z, u ∈ z) hudom };
  // fapply(f,u) = fapply(g,u)
  have heqfg : π (fapply f u = fapply g u) { refine hall u huA };
  // fapply(g,u) = v
  have hgv : π (fapply g u = v) { rewrite left heqfg; apply hfv };
  // u ∈ C
  have huC : π (u ∈ C) { refine hAC u huA };
  // Pair(u, fapply(g,u)) ∈ g
  have hgmem : π (Pair u (fapply g u) ∈ g) { refine Pi_apply_Pair g u C D hg huC };
  // Pair(u, v) ∈ g since fapply(g,u) = v
  have hmemg : π (Pair u v ∈ g)
    { rewrite left hgv; apply hgmem };
  // p = Pair(u,v) ∈ g
  rewrite hpeq; apply hmemg
end;

// fun_extension: f∈Pi(A,B) → g∈Pi(A,D) → (∀x∈A. f`x=g`x) → f=g
// Faithful to Isabelle: g's codomain family D may differ from f's B.
opaque symbol fun_extension (f g A : τ ι) (B D : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (g ∈ Pi A D) →
  π (Ball A (λ x, fapply f x = fapply g x)) →
  π (f = g) ≔
begin
  assume f g A B D hf hg hall;
  // f ⊆ g
  have hfg : π (f ⊆ g)
    { refine fun_subset f g A B A D hf hg (subset_refl A) hall };
  // g ⊆ f: need Ball A (λ x, fapply g x = fapply f x)
  have hallr : π (Ball A (λ x, fapply g x = fapply f x))
    { assume x hxA;
      symmetry;
      refine hall x hxA };
  have hgf : π (g ⊆ f)
    { refine fun_subset g f A D A B hg hf (subset_refl A) hallr };
  refine subset_antisym f g hfg hgf
end;

// ---------------------------------------------------------------------------
// eta: f ∈ Pi(A,B) → Lambda(A, λ x. fapply(f,x)) = f
// ---------------------------------------------------------------------------

opaque symbol eta (f A : τ ι) (B : τ ι → τ ι) :
  π (f ∈ Pi A B) → π (Lambda A (λ x, fapply f x) = f) ≔
begin
  assume f A B hf;
  // Lambda(A, λ x. fapply(f,x)) ∈ Pi(A,B)
  have hlam : π (Lambda A (λ x, fapply f x) ∈ Pi A B)
    { refine lam_type A (λ x, fapply f x) B _;
      assume x hxA;
      refine fapply_type f x A B hf hxA };
  // For all x ∈ A, fapply(Lambda(A, λ x. fapply(f,x)), x) = fapply(f,x)
  have hall : π (Ball A (λ x, fapply (Lambda A (λ z, fapply f z)) x = fapply f x))
    { assume x hxA;
      refine beta A (λ z, fapply f z) x hxA };
  refine fun_extension (Lambda A (λ x, fapply f x)) f A B B hlam hf hall
end;

// ===========================================================================
// Restrict lemmas
// ===========================================================================

// restrictI: Pair(a,b) ∈ f → a ∈ A → Pair(a,b) ∈ restrict(f, A)
opaque symbol restrictI (a b f A : τ ι) :
  π (Pair a b ∈ f) → π (a ∈ A) → π (Pair a b ∈ restrict f A) ≔
begin
  assume a b f A hpf haA;
  rewrite restrict_def;
  refine CollectI (Pair a b) f (λ p, Bex A (λ x, `∃ (y : τ ι), p = Pair x y)) hpf _;
  refine ∃ᵢ a _;
  apply ∧ᵢ haA _;
  refine ∃ᵢ b (eq_refl (Pair a b))
end;

// restrictD1: p ∈ restrict(f, A) → p ∈ f
opaque symbol restrictD1 (p f A : τ ι) :
  π (p ∈ restrict f A) → π (p ∈ f) ≔
begin
  assume p f A h;
  have h' : π (p ∈ Collect f (λ q, Bex A (λ x, `∃ (y : τ ι), q = Pair x y)))
    { refine ind_eq (eq_sym (restrict_def f A)) (λ s, p ∈ s) h };
  refine CollectD1 p f (λ q, Bex A (λ x, `∃ (y : τ ι), q = Pair x y)) h'
end;

// restrictE: p ∈ restrict(f, A) → p ∈ f ∧ Bex A (λ x, ∃y. p = Pair(x,y))
opaque symbol restrictE (p f A : τ ι) :
  π (p ∈ restrict f A) → π (p ∈ f ∧ Bex A (λ x, `∃ (y : τ ι), p = Pair x y)) ≔
begin
  assume p f A h;
  have h' : π (p ∈ Collect f (λ q, Bex A (λ x, `∃ (y : τ ι), q = Pair x y)))
    { refine ind_eq (eq_sym (restrict_def f A)) (λ s, p ∈ s) h };
  apply ∧ᵢ
  { refine CollectD1 p f (λ q, Bex A (λ x, `∃ (y : τ ι), q = Pair x y)) h' }
  { refine CollectD2 p f (λ q, Bex A (λ x, `∃ (y : τ ι), q = Pair x y)) h' }
end;

// restrict_subset: restrict(f, A) ⊆ f
opaque symbol restrict_subset (f A : τ ι) :
  π (restrict f A ⊆ f) ≔
begin
  assume f A p hp;
  refine restrictD1 p f A hp
end;

// function_restrictI: function(f) → function(restrict(f, A))
opaque symbol function_restrictI (f A : τ ι) :
  π (function f) → π (function (restrict f A)) ≔
begin
  assume f A hfunc;
  rewrite function_def;
  assume x y yp h1 h2;
  have h1f : π (Pair x y ∈ f) { refine restrictD1 (Pair x y) f A h1 };
  have h2f : π (Pair x yp ∈ f) { refine restrictD1 (Pair x yp) f A h2 };
  refine functionD f hfunc x y yp h1f h2f
end;

// restrict_apply: function(f) → a ∈ A → a ∈ domain(f) →
//   fapply(restrict(f,A), a) = fapply(f, a)
opaque symbol restrict_apply (f A a : τ ι) :
  π (function f) → π (a ∈ A) → π (a ∈ domain f) →
  π (fapply (restrict f A) a = fapply f a) ≔
begin
  assume f A a hfunc haA hadom;
  // Pair(a, fapply(f,a)) ∈ f
  have hpf : π (Pair a (fapply f a) ∈ f)
    { refine apply_Pair f a hfunc hadom };
  // Pair(a, fapply(f,a)) ∈ restrict(f, A)
  have hpr : π (Pair a (fapply f a) ∈ restrict f A)
    { refine restrictI a (fapply f a) f A hpf haA };
  // function(restrict(f,A))
  have hfuncr : π (function (restrict f A))
    { refine function_restrictI f A hfunc };
  // a ∈ domain(restrict(f,A))
  have hadomr : π (a ∈ domain (restrict f A))
    { refine domainI a (fapply f a) (restrict f A) hpr };
  // Pair(a, fapply(restrict(f,A),a)) ∈ restrict(f,A)
  have hpr2 : π (Pair a (fapply (restrict f A) a) ∈ restrict f A)
    { refine apply_Pair (restrict f A) a hfuncr hadomr };
  // Both in restrict, so by function: fapply(restrict(f,A),a) = fapply(f,a)
  refine functionD (restrict f A) hfuncr a (fapply (restrict f A) a) (fapply f a)
    hpr2 hpr
end;

// restrict_lam_eq: A ⊆ C → restrict(Lambda(C,b), A) = Lambda(A,b)
opaque symbol restrict_lam_eq (A C : τ ι) (b : τ ι → τ ι) :
  π (A ⊆ C) → π (restrict (Lambda C b) A = Lambda A b) ≔
begin
  assume A C b hAC;
  refine subset_antisym (restrict (Lambda C b) A) (Lambda A b) _ _
  { // restrict(Lambda(C,b), A) ⊆ Lambda(A,b)
    assume p hp;
    have hp' : π (p ∈ Collect (Lambda C b) (λ q, Bex A (λ x, `∃ (y : τ ι), q = Pair x y)))
      { refine ind_eq (eq_sym (restrict_def (Lambda C b) A)) (λ s, p ∈ s) hp };
    have hpf : π (p ∈ Lambda C b) { refine restrictD1 p (Lambda C b) A hp };
    have hpf' : π (p ∈ RepFun C (λ z, Pair z (b z)))
      { refine ind_eq (eq_sym (Lambda_def C b)) (λ s, p ∈ s) hpf };
    have hbex_outer : π (Bex A (λ x, `∃ (y : τ ι), p = Pair x y))
      { refine CollectD2 p (Lambda C b) (λ q, Bex A (λ x, `∃ (y : τ ι), q = Pair x y)) hp' };
    // p ∈ Lambda(C,b) = RepFun(C, λx.Pair(x,b(x))), so ∃z∈C. p = Pair(z,b(z))
    have hrep : π (Bex C (λ z, p = Pair z (b z)))
      { refine ∧ₑ₁ (RepFun_iff p C (λ z, Pair z (b z))) hpf' };
    // From hbex_outer: ∃x∈A. ∃y. p = Pair(x,y)
    refine ∃ₑ hbex_outer _;
    assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    have hex_y : π (`∃ (y : τ ι), p = Pair x y) { refine ∧ₑ₂ hx };
    refine ∃ₑ hex_y _;
    assume y hpeq_xy;
    // From hrep: ∃z∈C. p = Pair(z, b(z))
    refine ∃ₑ hrep _;
    assume z hz;
    have hzC : π (z ∈ C) { refine ∧ₑ₁ hz };
    have hpeq_zb : π (p = Pair z (b z)) { refine ∧ₑ₂ hz };
    // p = Pair(x,y) = Pair(z, b(z)), so x = z and y = b(z)
    have heq_pairs : π (Pair x y = Pair z (b z))
      { rewrite left hpeq_xy; apply hpeq_zb };
    have hxz : π (x = z) { refine Pair_inject1 x y z (b z) heq_pairs };
    // p = Pair(z, b(z)) = Pair(x, b(x))
    rewrite hpeq_zb;
    rewrite left hxz;
    rewrite Lambda_def;
    refine RepFunI x A (λ w, Pair w (b w)) hxA }
  { // Lambda(A,b) ⊆ restrict(Lambda(C,b), A)
    assume p hp;
    // p ∈ Lambda(A,b) = RepFun(A, λx.Pair(x,b(x)))
    have hp' : π (p ∈ RepFun A (λ z, Pair z (b z)))
      { refine ind_eq (eq_sym (Lambda_def A b)) (λ s, p ∈ s) hp };
    have hrep : π (Bex A (λ z, p = Pair z (b z)))
      { refine ∧ₑ₁ (RepFun_iff p A (λ z, Pair z (b z))) hp' };
    refine ∃ₑ hrep _;
    assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    have hpeq : π (p = Pair x (b x)) { refine ∧ₑ₂ hx };
    have hxC : π (x ∈ C) { refine hAC x hxA };
    // Pair(x, b(x)) ∈ Lambda(C, b)
    have hpC : π (Pair x (b x) ∈ Lambda C b)
      { rewrite Lambda_def; refine RepFunI x C (λ z, Pair z (b z)) hxC };
    // p ∈ Lambda(C, b)
    have hpinC : π (p ∈ Lambda C b) { rewrite hpeq; apply hpC };
    // Bex condition: x ∈ A witnesses it
    rewrite restrict_def;
    refine CollectI p (Lambda C b) (λ q, Bex A (λ w, `∃ (y : τ ι), q = Pair w y)) hpinC _;
    refine ∃ᵢ x _;
    apply ∧ᵢ hxA _;
    refine ∃ᵢ (b x) hpeq }
end;

// ===========================================================================
// lam_cong: A = B → Ball A (λ x, f x = g x) → Lambda(A,f) = Lambda(B,g)
// ===========================================================================

opaque symbol lam_cong (A B : τ ι) (f g : τ ι → τ ι) :
  π (A = B) → π (Ball A (λ x, f x = g x)) → π (Lambda A f = Lambda B g) ≔
begin
  assume A B f g hAB hfg;
  refine subset_antisym (Lambda A f) (Lambda B g) _ _
  { // Lambda(A,f) ⊆ Lambda(B,g)
    assume p hp;
    have hp' : π (p ∈ RepFun A (λ z, Pair z (f z)))
      { refine ind_eq (eq_sym (Lambda_def A f)) (λ s, p ∈ s) hp };
    have hrep : π (Bex A (λ z, p = Pair z (f z)))
      { refine ∧ₑ₁ (RepFun_iff p A (λ z, Pair z (f z))) hp' };
    refine ∃ₑ hrep _;
    assume x hx;
    have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
    have hpeq : π (p = Pair x (f x)) { refine ∧ₑ₂ hx };
    have hxB : π (x ∈ B) { refine ind_eq (eq_sym hAB) (λ z, x ∈ z) hxA };
    have hfxgx : π (f x = g x) { refine hfg x hxA };
    // p = Pair(x, f(x)) = Pair(x, g(x))
    rewrite hpeq;
    rewrite hfxgx;
    rewrite Lambda_def;
    refine RepFunI x B (λ z, Pair z (g z)) hxB }
  { // Lambda(B,g) ⊆ Lambda(A,f)
    assume p hp;
    have hp' : π (p ∈ RepFun B (λ z, Pair z (g z)))
      { refine ind_eq (eq_sym (Lambda_def B g)) (λ s, p ∈ s) hp };
    have hrep : π (Bex B (λ z, p = Pair z (g z)))
      { refine ∧ₑ₁ (RepFun_iff p B (λ z, Pair z (g z))) hp' };
    refine ∃ₑ hrep _;
    assume x hx;
    have hxB : π (x ∈ B) { refine ∧ₑ₁ hx };
    have hpeq : π (p = Pair x (g x)) { refine ∧ₑ₂ hx };
    have hxA : π (x ∈ A) { refine ind_eq hAB (λ z, x ∈ z) hxB };
    have hfxgx : π (f x = g x) { refine hfg x hxA };
    rewrite hpeq;
    rewrite left hfxgx;
    rewrite Lambda_def;
    refine RepFunI x A (λ z, Pair z (f z)) hxA }
end;

// ===========================================================================
// apply_iff: function(f) → a ∈ domain(f) → (Pair(a,b) ∈ f ⇔ fapply(f,a) = b)
// ===========================================================================

opaque symbol apply_iff (f a b : τ ι) :
  π (function f) → π (a ∈ domain f) →
  π ((Pair a b ∈ f) ⇔ (fapply f a = b)) ≔
begin
  assume f a b hfunc hdom;
  apply ∧ᵢ
  { // Forward: Pair(a,b) ∈ f → fapply(f,a) = b
    assume hmem;
    refine function_apply_equality a b f hmem hfunc }
  { // Backward: fapply(f,a) = b → Pair(a,b) ∈ f
    assume heq;
    have hpf : π (Pair a (fapply f a) ∈ f)
      { refine apply_Pair f a hfunc hdom };
    rewrite left heq;
    apply hpf }
end;
