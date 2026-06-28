// Sum: Disjoint Sums for ZF set theory
//
// Isabelle source: Sum.thy
// Defines: Inl, Inr, sum (A+B), case/when, Part
// And the "Part" primitive for simultaneous recursive type definitions

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.Bool_ZF;

// ===========================================================================
// Definitions
// ===========================================================================

// sum: A + B = {0} * A ∪ {1} * B
symbol sum (A B : τ ι) : τ ι ≔
  Un (Sigma (singleton empty) (λ _, A))
     (Sigma (singleton one) (λ _, B));

// Inl(a) = <0, a>
symbol Inl (a : τ ι) : τ ι ≔ Pair empty a;

// Inr(b) = <1, b>
symbol Inr (b : τ ι) : τ ι ≔ Pair one b;

// case(c, d, p) = split(λ y z. cond(y, d(z), c(z)), p)
//   = cond(fst(p), d(snd(p)), c(snd(p)))
// In Isabelle: case(c,d) ≡ (λ<y,z>. cond(y, d(z), c(z)))
// When y=0 (Inl): cond(0,d(z),c(z)) = c(z)   [since 0 ≠ 1]
// When y=1 (Inr): cond(1,d(z),c(z)) = d(z)   [since 1 = 1]
symbol case_sum (c d : τ ι → τ ι) (p : τ ι) : τ ι ≔
  cond (fst p) (d (snd p)) (c (snd p));

// Part(A, h) = {x ∈ A | ∃z. x = h(z)}
symbol Part (A : τ ι) (h : τ ι → τ ι) : τ ι ≔
  Collect A (λ x, `∃ (z : τ ι), x = h z);

// ===========================================================================
// Rules for Part
// ===========================================================================

// Part_iff: a ∈ Part(A,h) ⟷ a ∈ A ∧ (∃y. a = h(y))
opaque symbol Part_iff (a A : τ ι) (h : τ ι → τ ι) :
  π ((a ∈ Part A h) ⇔ (a ∈ A ∧ (`∃ (y : τ ι), a = h y))) ≔
begin
  assume a A h;
  apply (Collect_iff a A (λ x, `∃ (z : τ ι), x = h z))
end;

// Part_eqI: a ∈ A → a = h(b) → a ∈ Part(A,h)
opaque symbol Part_eqI (a A : τ ι) (h : τ ι → τ ι) (b : τ ι) :
  π (a ∈ A) → π (a = h b) → π (a ∈ Part A h) ≔
begin
  assume a A h b haA heq;
  refine CollectI a A (λ x, `∃ (z : τ ι), x = h z) haA _;
  refine ∃ᵢ b heq
end;

// PartI: h(b) ∈ A → h(b) ∈ Part(A,h)
opaque symbol PartI (b A : τ ι) (h : τ ι → τ ι) :
  π (h b ∈ A) → π (h b ∈ Part A h) ≔
begin
  assume b A h hA;
  refine Part_eqI (h b) A h b hA (eq_refl (h b))
end;

// PartE: a ∈ Part(A,h) → (∀z. a ∈ A → a = h(z) → P) → P
opaque symbol PartE (a A : τ ι) (h : τ ι → τ ι) (P : Prop) :
  π (a ∈ Part A h) →
  (Π (z : τ ι), π (a ∈ A) → π (a = h z) → π P) →
  π P ≔
begin
  assume a A h P hpart hk;
  have haA : π (a ∈ A) { refine CollectD1 a A (λ x, `∃ (z : τ ι), x = h z) hpart };
  have hex : π (`∃ (z : τ ι), a = h z)
    { refine CollectD2 a A (λ x, `∃ (z : τ ι), x = h z) hpart };
  refine ∃ₑ hex _;
  assume z hz;
  refine hk z haA hz
end;

// Part_subset: Part(A,h) ⊆ A
opaque symbol Part_subset (A : τ ι) (h : τ ι → τ ι) :
  π (Part A h ⊆ A) ≔
begin
  assume A h x hx;
  refine CollectD1 x A (λ y, `∃ (z : τ ι), y = h z) hx
end;

// ===========================================================================
// Rules for Disjoint Sums
// ===========================================================================

// InlI: a ∈ A → Inl(a) ∈ A + B
opaque symbol InlI (a A B : τ ι) :
  π (a ∈ A) → π (Inl a ∈ sum A B) ≔
begin
  assume a A B haA;
  // Inl(a) = Pair(empty, a)
  // Need: Pair(empty,a) ∈ Sigma(singleton(empty), λ_. A) ∪ Sigma(singleton(one), λ_. B)
  // empty ∈ singleton(empty) and a ∈ A, so Pair(empty,a) ∈ Sigma(singleton(empty), λ_.A)
  have h : π (Pair empty a ∈ Sigma (singleton empty) (λ _, A))
    { refine SigmaI empty a (singleton empty) (λ _, A) (singletonI empty) haA };
  refine UnI1 (Pair empty a)
    (Sigma (singleton empty) (λ _, A))
    (Sigma (singleton one) (λ _, B)) h
end;

// InrI: b ∈ B → Inr(b) ∈ A + B
opaque symbol InrI (b A B : τ ι) :
  π (b ∈ B) → π (Inr b ∈ sum A B) ≔
begin
  assume b A B hbB;
  have h : π (Pair one b ∈ Sigma (singleton one) (λ _, B))
    { refine SigmaI one b (singleton one) (λ _, B) (singletonI one) hbB };
  refine UnI2 (Pair one b)
    (Sigma (singleton empty) (λ _, A))
    (Sigma (singleton one) (λ _, B)) h
end;

// sumE: u ∈ A+B → (∀x. x∈A → u=Inl(x) → P) → (∀y. y∈B → u=Inr(y) → P) → P
opaque symbol sumE (u A B : τ ι) (P : Prop) :
  π (u ∈ sum A B) →
  (Π (x : τ ι), π (x ∈ A) → π (u = Inl x) → π P) →
  (Π (y : τ ι), π (y ∈ B) → π (u = Inr y) → π P) →
  π P ≔
begin
  assume u A B P hu hleft hright;
  // u ∈ Sigma(singleton(0), λ_.A) ∪ Sigma(singleton(1), λ_.B)
  have hdisj : π (u ∈ Sigma (singleton empty) (λ _, A) ∨
                   u ∈ Sigma (singleton one) (λ _, B))
    { refine UnE u (Sigma (singleton empty) (λ _, A))
                   (Sigma (singleton one) (λ _, B)) hu };
  refine ∨ₑ hdisj _ _
  { // u ∈ Sigma(singleton(0), λ_.A)
    assume hleftσ;
    have hbex : π (Bex (singleton empty) (λ x, Bex A (λ y, u = Pair x y)))
      { refine SigmaE u (singleton empty) (λ _, A) hleftσ };
    refine ∃ₑ hbex _;
    assume x hx;
    have hxsing : π (x ∈ singleton empty) { refine ∧ₑ₁ hx };
    have hbex2 : π (Bex A (λ y, u = Pair x y)) { refine ∧ₑ₂ hx };
    have hx0 : π (x = empty) { refine ∧ₑ₁ (singleton_iff x empty) hxsing };
    refine ∃ₑ hbex2 _;
    assume y hy;
    have hyA : π (y ∈ A) { refine ∧ₑ₁ hy };
    have hueq : π (u = Pair x y) { refine ∧ₑ₂ hy };
    // u = Pair(x,y) = Pair(0,y) = Inl(y)
    have hueq2 : π (u = Pair empty y)
      { refine ind_eq (eq_sym hx0) (λ z, u = Pair z y) hueq };
    refine hleft y hyA hueq2 }
  { // u ∈ Sigma(singleton(1), λ_.B)
    assume hrightσ;
    have hbex : π (Bex (singleton one) (λ x, Bex B (λ y, u = Pair x y)))
      { refine SigmaE u (singleton one) (λ _, B) hrightσ };
    refine ∃ₑ hbex _;
    assume x hx;
    have hxsing : π (x ∈ singleton one) { refine ∧ₑ₁ hx };
    have hbex2 : π (Bex B (λ y, u = Pair x y)) { refine ∧ₑ₂ hx };
    have hx1 : π (x = one) { refine ∧ₑ₁ (singleton_iff x one) hxsing };
    refine ∃ₑ hbex2 _;
    assume y hy;
    have hyB : π (y ∈ B) { refine ∧ₑ₁ hy };
    have hueq : π (u = Pair x y) { refine ∧ₑ₂ hy };
    have hueq2 : π (u = Pair one y)
      { refine ind_eq (eq_sym hx1) (λ z, u = Pair z y) hueq };
    refine hright y hyB hueq2 }
end;

// ===========================================================================
// Injection and freeness
// ===========================================================================

// Inl_iff: Inl(a) = Inl(b) ⟷ a = b
opaque symbol Inl_iff (a b : τ ι) :
  π (Inl a = Inl b ⇔ a = b) ≔
begin
  assume a b;
  apply ∧ᵢ
  { assume h;
    // Pair(0,a) = Pair(0,b) → a = b by Pair_inject2
    refine Pair_inject2 empty a empty b h }
  { assume h; rewrite h; reflexivity }
end;

// Inr_iff: Inr(a) = Inr(b) ⟷ a = b
opaque symbol Inr_iff (a b : τ ι) :
  π (Inr a = Inr b ⇔ a = b) ≔
begin
  assume a b;
  apply ∧ᵢ
  { assume h;
    refine Pair_inject2 one a one b h }
  { assume h; rewrite h; reflexivity }
end;

// Inl_Inr_iff: Inl(a) = Inr(b) ⟷ False
opaque symbol Inl_Inr_iff (a b : τ ι) :
  π (Inl a = Inr b ⇔ ⊥) ≔
begin
  assume a b;
  apply ∧ᵢ
  { assume h;
    // Pair(0,a) = Pair(1,b) → 0 = 1 by Pair_inject1, contradiction
    have h01 : π (empty = one) { refine Pair_inject1 empty a one b h };
    refine zero_ne_one h01 }
  { assume hf; refine ⊥ₑ hf }
end;

// Inr_Inl_iff: Inr(b) = Inl(a) ⟷ False
opaque symbol Inr_Inl_iff (a b : τ ι) :
  π (Inr b = Inl a ⇔ ⊥) ≔
begin
  assume a b;
  apply ∧ᵢ
  { assume h;
    have h10 : π (one = empty) { refine Pair_inject1 one b empty a h };
    refine zero_ne_one (eq_sym h10) }
  { assume hf; refine ⊥ₑ hf }
end;

// Inl_inject: Inl(a) = Inl(b) → a = b
opaque symbol Inl_inject (a b : τ ι) :
  π (Inl a = Inl b) → π (a = b) ≔
begin
  assume a b h;
  refine ∧ₑ₁ (Inl_iff a b) h
end;

// Inr_inject: Inr(a) = Inr(b) → a = b
opaque symbol Inr_inject (a b : τ ι) :
  π (Inr a = Inr b) → π (a = b) ≔
begin
  assume a b h;
  refine ∧ₑ₁ (Inr_iff a b) h
end;

// Inl_neq_Inr: Inl(a) = Inr(b) → P (ex falso from injection)
opaque symbol Inl_neq_Inr (a b : τ ι) (P : Prop) :
  π (Inl a = Inr b) → π P ≔
begin
  assume a b P h;
  refine ⊥ₑ _;
  refine ∧ₑ₁ (Inl_Inr_iff a b) h
end;

// Inr_neq_Inl: Inr(b) = Inl(a) → P
opaque symbol Inr_neq_Inl (a b : τ ι) (P : Prop) :
  π (Inr b = Inl a) → π P ≔
begin
  assume a b P h;
  refine ⊥ₑ _;
  refine ∧ₑ₁ (Inr_Inl_iff a b) h
end;

// ===========================================================================
// Sum membership lemmas
// ===========================================================================

// InlD: Inl(a) ∈ A+B → a ∈ A
opaque symbol InlD (a A B : τ ι) :
  π (Inl a ∈ sum A B) → π (a ∈ A) ≔
begin
  assume a A B h;
  refine sumE (Inl a) A B (a ∈ A) h _ _
  { assume x hxA heq;
    // Inl(a) = Inl(x) → a = x
    have hax : π (a = x) { refine Inl_inject a x heq };
    rewrite hax; apply hxA }
  { assume y hyB heq;
    // Inl(a) = Inr(y) → ⊥
    refine Inl_neq_Inr a y (a ∈ A) heq }
end;

// InrD: Inr(b) ∈ A+B → b ∈ B
opaque symbol InrD (b A B : τ ι) :
  π (Inr b ∈ sum A B) → π (b ∈ B) ≔
begin
  assume b A B h;
  refine sumE (Inr b) A B (b ∈ B) h _ _
  { assume x hxA heq;
    refine Inr_neq_Inl x b (b ∈ B) heq }
  { assume y hyB heq;
    have hby : π (b = y) { refine Inr_inject b y heq };
    rewrite hby; apply hyB }
end;

// sum_iff: u ∈ A+B ⟷ (∃x. x ∈ A ∧ u = Inl(x)) ∨ (∃y. y ∈ B ∧ u = Inr(y))
opaque symbol sum_iff (u A B : τ ι) :
  π ((u ∈ sum A B) ⇔
     ((`∃ (x : τ ι), x ∈ A ∧ u = Inl x) ∨
      (`∃ (y : τ ι), y ∈ B ∧ u = Inr y))) ≔
begin
  assume u A B;
  apply ∧ᵢ
  { assume hu;
    refine sumE u A B _ hu _ _
    { assume x hxA hueq;
      refine ∨ᵢ₁ (∃ᵢ x (∧ᵢ hxA hueq)) }
    { assume y hyB hueq;
      refine ∨ᵢ₂ (∃ᵢ y (∧ᵢ hyB hueq)) } }
  { assume hdisj;
    refine ∨ₑ hdisj _ _
    { assume hex;
      refine ∃ₑ hex _;
      assume x hx;
      have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
      have hueq : π (u = Inl x) { refine ∧ₑ₂ hx };
      rewrite hueq;
      refine InlI x A B hxA }
    { assume hex;
      refine ∃ₑ hex _;
      assume y hy;
      have hyB : π (y ∈ B) { refine ∧ₑ₁ hy };
      have hueq : π (u = Inr y) { refine ∧ₑ₂ hy };
      rewrite hueq;
      refine InrI y A B hyB } }
end;

// Inl_in_sum_iff: Inl(x) ∈ A+B ⟷ x ∈ A
opaque symbol Inl_in_sum_iff (x A B : τ ι) :
  π ((Inl x ∈ sum A B) ⇔ (x ∈ A)) ≔
begin
  assume x A B;
  apply ∧ᵢ
  { assume h; refine InlD x A B h }
  { assume h; refine InlI x A B h }
end;

// Inr_in_sum_iff: Inr(y) ∈ A+B ⟷ y ∈ B
opaque symbol Inr_in_sum_iff (y A B : τ ι) :
  π ((Inr y ∈ sum A B) ⇔ (y ∈ B)) ≔
begin
  assume y A B;
  apply ∧ᵢ
  { assume h; refine InrD y A B h }
  { assume h; refine InrI y A B h }
end;

// sum_subset_iff: A+B ⊆ C+D ⟷ A ⊆ C ∧ B ⊆ D
// TODO: prove (needs detailed element-chasing)
opaque symbol sum_subset_iff (A B C D : τ ι) :
  π ((sum A B ⊆ sum C D) ⇔ (A ⊆ C ∧ B ⊆ D)) ≔
begin
  assume A B C D;
  apply ∧ᵢ
  { assume hsub;
    apply ∧ᵢ
    { assume x hx;
      have h : π (Inl x ∈ sum A B) { refine InlI x A B hx };
      have h2 : π (Inl x ∈ sum C D) { refine hsub (Inl x) h };
      refine InlD x C D h2 }
    { assume y hy;
      have h : π (Inr y ∈ sum A B) { refine InrI y A B hy };
      have h2 : π (Inr y ∈ sum C D) { refine hsub (Inr y) h };
      refine InrD y C D h2 } }
  { assume hpair;
    have hAC : π (A ⊆ C) { refine ∧ₑ₁ hpair };
    have hBD : π (B ⊆ D) { refine ∧ₑ₂ hpair };
    assume u hu;
    refine sumE u A B _ hu _ _
    { assume x hxA hueq;
      rewrite hueq;
      refine InlI x C D (hAC x hxA) }
    { assume y hyB hueq;
      rewrite hueq;
      refine InrI y C D (hBD y hyB) } }
end;

// sum_equal_iff: A+B = C+D ⟷ A = C ∧ B = D
opaque symbol sum_equal_iff (A B C D : τ ι) :
  π ((sum A B = sum C D) ⇔ (A = C ∧ B = D)) ≔
begin
  assume A B C D;
  apply ∧ᵢ
  { assume heq;
    have hsub1 : π (sum A B ⊆ sum C D) { refine equalityD1 (sum A B) (sum C D) heq };
    have hsub2 : π (sum C D ⊆ sum A B) { refine equalityD2 (sum A B) (sum C D) heq };
    have h1 : π (A ⊆ C ∧ B ⊆ D) { refine ∧ₑ₁ (sum_subset_iff A B C D) hsub1 };
    have h2 : π (C ⊆ A ∧ D ⊆ B) { refine ∧ₑ₁ (sum_subset_iff C D A B) hsub2 };
    apply ∧ᵢ
    { refine subset_antisym A C (∧ₑ₁ h1) (∧ₑ₁ h2) }
    { refine subset_antisym B D (∧ₑ₂ h1) (∧ₑ₂ h2) } }
  { assume hpair;
    have hAC : π (A = C) { refine ∧ₑ₁ hpair };
    have hBD : π (B = D) { refine ∧ₑ₂ hpair };
    rewrite hAC; rewrite hBD; reflexivity }
end;

// sum_empty: 0 + 0 = 0
// TODO: prove (needs showing Sigma over singleton of empty set with empty range is empty)
opaque symbol sum_empty :
  π (sum empty empty = empty) ≔
begin
  refine equals0I (sum empty empty) _;
  assume y hy;
  refine sumE y empty empty ⊥ hy _ _
  { assume x hx heq; refine emptyE x hx }
  { assume x hx heq; refine emptyE x hx }
end;

// ===========================================================================
// The Eliminator: case_sum
// ===========================================================================

// case_Inl: case(c, d, Inl(a)) = c(a)
// Inl(a) = ⟨0,a⟩; case_sum c d (Inl a) is convertible to
// cond(fst⟨0,a⟩, d(snd⟨0,a⟩), c(snd⟨0,a⟩)); rewrite the Kuratowski
// projections via fst_conv/snd_conv to cond(0, d a, c a), then cond_0.
opaque symbol case_Inl (c d : τ ι → τ ι) (a : τ ι) :
  π (case_sum c d (Inl a) = c a) ≔
begin
  assume c d a;
  have key : π (cond (fst (Pair empty a)) (d (snd (Pair empty a)))
                     (c (snd (Pair empty a))) = c a) {
    rewrite (fst_conv empty a);
    rewrite (snd_conv empty a);
    refine cond_0 (d a) (c a) };
  refine key
end;

// case_Inr: case(c, d, Inr(b)) = d(b)   (symmetric, cond_1)
opaque symbol case_Inr (c d : τ ι → τ ι) (b : τ ι) :
  π (case_sum c d (Inr b) = d b) ≔
begin
  assume c d b;
  have key : π (cond (fst (Pair one b)) (d (snd (Pair one b)))
                     (c (snd (Pair one b))) = d b) {
    rewrite (fst_conv one b);
    rewrite (snd_conv one b);
    refine cond_1 (d b) (c b) };
  refine key
end;

// case_type: u ∈ A+B → c(x)∈C(Inl(x)) for x∈A → d(y)∈C(Inr(y)) for y∈B
//   → case(c,d,u) ∈ C(u)
// Case-split u with sumE; rewrite u to Inl x / Inr y, then collapse the
// case via case_Inl / case_Inr to the corresponding hypothesis.
opaque symbol case_type (u A B : τ ι) (c d : τ ι → τ ι)
  (C : τ ι → τ ι) :
  π (u ∈ sum A B) →
  (Π (x : τ ι), π (x ∈ A) → π (c x ∈ C (Inl x))) →
  (Π (y : τ ι), π (y ∈ B) → π (d y ∈ C (Inr y))) →
  π (case_sum c d u ∈ C u) ≔
begin
  assume u A B c d C hu hc hd;
  refine sumE u A B (case_sum c d u ∈ C u) hu _ _
  { assume x hxA hueq;
    rewrite hueq;
    rewrite (case_Inl c d x);
    refine hc x hxA }
  { assume y hyB hueq;
    rewrite hueq;
    rewrite (case_Inr c d y);
    refine hd y hyB }
end;

// ===========================================================================
// More rules for Part(A,h)
// ===========================================================================

// Part_mono: A ⊆ B → Part(A,h) ⊆ Part(B,h)
opaque symbol Part_mono (A B : τ ι) (h : τ ι → τ ι) :
  π (A ⊆ B) → π (Part A h ⊆ Part B h) ≔
begin
  assume A B h hsub x hx;
  refine PartE x A h (x ∈ Part B h) hx _;
  assume z hxA heq;
  refine Part_eqI x B h z (hsub x hxA) heq
end;

// PartD1: a ∈ Part(A,h) → a ∈ A
opaque symbol PartD1 (a A : τ ι) (h : τ ι → τ ι) :
  π (a ∈ Part A h) → π (a ∈ A) ≔
begin
  assume a A h h1;
  refine CollectD1 a A (λ x, `∃ (z : τ ι), x = h z) h1
end;

// Part_Inl: Part(A+B, Inl) = {Inl(x) | x ∈ A}
// i.e., Part(A+B, Inl) = RepFun(A, Inl)
opaque symbol Part_Inl (A B : τ ι) :
  π (Part (sum A B) Inl = RepFun A Inl) ≔
begin
  assume A B;
  refine extension (Part (sum A B) Inl) (RepFun A Inl) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    // x ∈ Part(A+B, Inl) → x ∈ A+B ∧ ∃z. x = Inl(z)
    have hxsum : π (x ∈ sum A B) { refine PartD1 x (sum A B) Inl hx };
    have hex : π (`∃ (z : τ ι), x = Inl z)
      { refine CollectD2 x (sum A B) (λ y, `∃ (z : τ ι), y = Inl z) hx };
    refine ∃ₑ hex _;
    assume z hz;
    // x = Inl(z) and x ∈ A+B, so Inl(z) ∈ A+B, so z ∈ A
    have hzA : π (z ∈ A) { refine InlD z A B (ind_eq (eq_sym hz) (λ w, w ∈ sum A B) hxsum) };
    // x = Inl(z) and z ∈ A → x ∈ RepFun(A, Inl)
    refine ind_eq hz (λ w, w ∈ RepFun A Inl) (RepFunI z A Inl hzA) }
  { assume hx;
    // x ∈ RepFun(A, Inl) → ∃z∈A. x = Inl(z)
    have hbex : π (Bex A (λ z, x = Inl z))
      { refine ∧ₑ₁ (RepFun_iff x A Inl) hx };
    refine ∃ₑ hbex _;
    assume z hz;
    have hzA : π (z ∈ A) { refine ∧ₑ₁ hz };
    have hxeq : π (x = Inl z) { refine ∧ₑ₂ hz };
    // Inl(z) ∈ A+B since z ∈ A
    have hinl : π (Inl z ∈ sum A B) { refine InlI z A B hzA };
    have hxsum : π (x ∈ sum A B) { refine ind_eq hxeq (λ w, w ∈ sum A B) hinl };
    refine Part_eqI x (sum A B) Inl z hxsum hxeq }
end;

// Part_Inr: Part(A+B, Inr) = {Inr(y) | y ∈ B}
opaque symbol Part_Inr (A B : τ ι) :
  π (Part (sum A B) Inr = RepFun B Inr) ≔
begin
  assume A B;
  refine extension (Part (sum A B) Inr) (RepFun B Inr) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hxsum : π (x ∈ sum A B) { refine PartD1 x (sum A B) Inr hx };
    have hex : π (`∃ (z : τ ι), x = Inr z)
      { refine CollectD2 x (sum A B) (λ y, `∃ (z : τ ι), y = Inr z) hx };
    refine ∃ₑ hex _;
    assume z hz;
    have hzB : π (z ∈ B) { refine InrD z A B (ind_eq (eq_sym hz) (λ w, w ∈ sum A B) hxsum) };
    refine ind_eq hz (λ w, w ∈ RepFun B Inr) (RepFunI z B Inr hzB) }
  { assume hx;
    have hbex : π (Bex B (λ z, x = Inr z))
      { refine ∧ₑ₁ (RepFun_iff x B Inr) hx };
    refine ∃ₑ hbex _;
    assume z hz;
    have hzB : π (z ∈ B) { refine ∧ₑ₁ hz };
    have hxeq : π (x = Inr z) { refine ∧ₑ₂ hz };
    have hinr : π (Inr z ∈ sum A B) { refine InrI z A B hzB };
    have hxsum : π (x ∈ sum A B) { refine ind_eq hxeq (λ w, w ∈ sum A B) hinr };
    refine Part_eqI x (sum A B) Inr z hxsum hxeq }
end;

// Part_id: Part(A, λx. x) = A
opaque symbol Part_id (A : τ ι) :
  π (Part A (λ x, x) = A) ≔
begin
  assume A;
  refine extension (Part A (λ x, x)) A _;
  assume x;
  apply ∧ᵢ
  { assume hx; refine PartD1 x A (λ y, y) hx }
  { assume hx;
    refine Part_eqI x A (λ y, y) x hx (eq_refl x) }
end;

// Part_sum_equality: C ⊆ A+B → Part(C,Inl) ∪ Part(C,Inr) = C
opaque symbol Part_sum_equality (A B C : τ ι) :
  π (C ⊆ sum A B) → π (Un (Part C Inl) (Part C Inr) = C) ≔
begin
  assume A B C hsub;
  refine extension (Un (Part C Inl) (Part C Inr)) C _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hdisj : π (x ∈ Part C Inl ∨ x ∈ Part C Inr)
      { refine UnE x (Part C Inl) (Part C Inr) hx };
    refine ∨ₑ hdisj _ _
    { assume h; refine PartD1 x C Inl h }
    { assume h; refine PartD1 x C Inr h } }
  { assume hxC;
    // x ∈ C, and C ⊆ A+B, so x ∈ A+B
    have hxsum : π (x ∈ sum A B) { refine hsub x hxC };
    refine sumE x A B _ hxsum _ _
    { assume a haA hxeq;
      // x = Inl(a), so x ∈ Part(C, Inl)
      refine UnI1 x (Part C Inl) (Part C Inr) _;
      refine Part_eqI x C Inl a hxC hxeq }
    { assume b hbB hxeq;
      refine UnI2 x (Part C Inl) (Part C Inr) _;
      refine Part_eqI x C Inr b hxC hxeq } }
end;

// Part_Collect: Part(Collect(A,P), h) = Collect(Part(A,h), P)
// TODO: prove (straightforward set equality)
opaque symbol Part_Collect (A : τ ι) (P : τ ι → Prop) (h : τ ι → τ ι) :
  π (Part (Collect A P) h = Collect (Part A h) P) ≔
begin
  assume A P h;
  refine extension (Part (Collect A P) h) (Collect (Part A h) P) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    // x ∈ Part(Collect(A,P), h) → x ∈ Collect(A,P) ∧ ∃z. x = h(z)
    have hxcol : π (x ∈ Collect A P)
      { refine PartD1 x (Collect A P) h hx };
    have hex : π (`∃ (z : τ ι), x = h z)
      { refine CollectD2 x (Collect A P) (λ y, `∃ (z : τ ι), y = h z) hx };
    have hxA : π (x ∈ A) { refine CollectD1 x A P hxcol };
    have hPx : π (P x) { refine CollectD2 x A P hxcol };
    // x ∈ Part(A,h) since x ∈ A and ∃z. x = h(z)
    have hxpart : π (x ∈ Part A h)
      { refine CollectI x A (λ y, `∃ (z : τ ι), y = h z) hxA hex };
    refine CollectI x (Part A h) P hxpart hPx }
  { assume hx;
    // x ∈ Collect(Part(A,h), P) → x ∈ Part(A,h) ∧ P(x)
    have hxpart : π (x ∈ Part A h)
      { refine CollectD1 x (Part A h) P hx };
    have hPx : π (P x) { refine CollectD2 x (Part A h) P hx };
    have hxA : π (x ∈ A) { refine PartD1 x A h hxpart };
    have hex : π (`∃ (z : τ ι), x = h z)
      { refine CollectD2 x A (λ y, `∃ (z : τ ι), y = h z) hxpart };
    // x ∈ Collect(A,P) since x ∈ A and P(x)
    have hxcol : π (x ∈ Collect A P)
      { refine CollectI x A P hxA hPx };
    // x ∈ Part(Collect(A,P), h) since x ∈ Collect(A,P) and ∃z. x = h(z)
    refine CollectI x (Collect A P) (λ y, `∃ (z : τ ι), y = h z) hxcol hex }
end;

// Part_Inr2: Part(A+B, λx. Inr(h(x))) = {Inr(y) | y ∈ Part(B,h)}
opaque symbol Part_Inr2 (A B : τ ι) (h : τ ι → τ ι) :
  π (Part (sum A B) (λ x, Inr (h x)) = RepFun (Part B h) Inr) ≔
begin
  assume A B h;
  refine extension (Part (sum A B) (λ x, Inr (h x))) (RepFun (Part B h) Inr) _;
  assume x;
  apply ∧ᵢ
  { assume hx;
    have hxsum : π (x ∈ sum A B)
      { refine PartD1 x (sum A B) (λ z, Inr (h z)) hx };
    have hex : π (`∃ (z : τ ι), x = Inr (h z))
      { refine CollectD2 x (sum A B) (λ y, `∃ (z : τ ι), y = Inr (h z)) hx };
    refine ∃ₑ hex _;
    assume z hz;
    // x = Inr(h(z)), so x ∈ A+B → Inr(h(z)) ∈ A+B → h(z) ∈ B
    have hhzB : π (h z ∈ B)
      { refine InrD (h z) A B (ind_eq (eq_sym hz) (λ w, w ∈ sum A B) hxsum) };
    // h(z) ∈ Part(B, h)
    have hhzpart : π (h z ∈ Part B h)
      { refine PartI z B h hhzB };
    // Inr(h(z)) ∈ RepFun(Part(B,h), Inr)
    have hinr : π (Inr (h z) ∈ RepFun (Part B h) Inr)
      { refine RepFunI (h z) (Part B h) Inr hhzpart };
    refine ind_eq hz (λ w, w ∈ RepFun (Part B h) Inr) hinr }
  { assume hx;
    have hbex : π (Bex (Part B h) (λ z, x = Inr z))
      { refine ∧ₑ₁ (RepFun_iff x (Part B h) Inr) hx };
    refine ∃ₑ hbex _;
    assume z hz;
    have hzpart : π (z ∈ Part B h) { refine ∧ₑ₁ hz };
    have hxeq : π (x = Inr z) { refine ∧ₑ₂ hz };
    // z ∈ Part(B, h) → z ∈ B ∧ ∃w. z = h(w)
    have hzB : π (z ∈ B) { refine PartD1 z B h hzpart };
    have hexw : π (`∃ (w : τ ι), z = h w)
      { refine CollectD2 z B (λ y, `∃ (w : τ ι), y = h w) hzpart };
    // x = Inr(z), z ∈ B → Inr(z) ∈ A+B
    have hinr : π (Inr z ∈ sum A B) { refine InrI z A B hzB };
    have hxsum : π (x ∈ sum A B)
      { refine ind_eq hxeq (λ w, w ∈ sum A B) hinr };
    // Need: ∃w. x = Inr(h(w))
    // From hexw: ∃w. z = h(w), and x = Inr(z), so x = Inr(h(w))
    refine CollectI x (sum A B) (λ y, `∃ (w : τ ι), y = Inr (h w)) hxsum _;
    refine ∃ₑ hexw _;
    assume w hw;
    // z = h(w), so x = Inr(z) = Inr(h(w))
    have hxeq2 : π (x = Inr (h w))
      { rewrite hxeq; rewrite hw; reflexivity };
    refine ∃ᵢ w hxeq2 }
end;
