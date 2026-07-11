// ZF.InfDatatype — Infinite-Branching Datatype Definitions
// Complete port of isabelle-src/InfDatatype.thy — every lemma/theorem PROVED
// (2026-07-11).
// (Source: L. C. Paulson, ZF/InfDatatype.thy.)
//
// Most facts here are Isabelle `lemmas foo = bar [THEN baz, OF qux]` derived
// aliases built from VLimit-family facts in Univ.thy (`Limit_VfromE`,
// `Pair_in_VLimit`, `Inl_in_VLimit`, `Inr_in_VLimit`, `zero_in_VLimit`,
// `nat_into_VLimit`) — NONE of which are ported yet in this repo's Univ.lp
// (a "base file" with known simp-noise-heavy gaps per CLAUDE.md §4).  Rather
// than add those intermediate names to Univ.lp, each alias below is rendered
// directly as the final COMPOSED fact (per CLAUDE.md's standard treatment of
// this idiom — see Int.lp's eq_intrelD/zless_asym for the precedent), using
// only already-existing primitives (Vfrom, Limit, csucc, InfCard, Pair, Inl,
// Inr, cardinal).  The exact source statements of the Univ.thy lemmas being
// composed were read directly from isabelle-src/Univ.thy to keep the
// derivations exact, not guessed.
//
// `Data_Arg_intros`/`inf_datatype_intros` are named hint BUNDLES (bags of
// pre-existing facts for the ML datatype package's type-checking tactic),
// not single Prop-typed statements — skipped, same precedent as `div_rls`.

require open ZF.Datatype ZF.Univ ZF.Finite ZF.Cardinal_AC;

// ===========================================================================
// port-internal helpers — re-derivations of Univ.thy/Ordinal.thy facts this
// module composes but which are not ported in Univ.lp/Ordinal.lp (see header).
// All private; exact Isabelle source lemma noted on each.
// ===========================================================================

// port-internal helper (Isabelle Ordinal.Un_least_lt): i<k → j<k → i∪j<k
private opaque symbol priv_Un_least_lt (i j k : τ ι) :
  π (lt i k) → π (lt j k) → π (lt (Un i j) k) ≔
begin
  assume i j k hik hjk;
  have hOi : π (Ord i) { refine lt_Ord i k hik };
  have hOj : π (Ord j) { refine lt_Ord j k hjk };
  refine ∨ₑ (Ord_linear i j hOi hOj) _ _
  { assume hij;
    have heq : π (Un i j = j)
      { refine subset_antisym (Un i j) j
          (Un_least i j j (OrdmemD j i hij hOj) (subset_refl j)) (Un_upper2 i j) };
    refine ind_eq heq (λ w, lt w k) hjk }
  { assume hd;
    refine ∨ₑ hd _ _
    { assume heqij;
      have heq : π (Un i j = j)
        { refine ind_eq heqij (λ w, Un w j = j) (Un_absorb j) };
      refine ind_eq heq (λ w, lt w k) hjk }
    { assume hji;
      have heq : π (Un i j = i)
        { refine subset_antisym (Un i j) i
            (Un_least i j i (subset_refl i) (OrdmemD i j hji hOi)) (Un_upper1 i j) };
      refine ind_eq heq (λ w, lt w k) hik } }
end;

// port-internal helper (Isabelle Univ.VfromI): a ∈ Vfrom(A,j) → j<i → a ∈ Vfrom(A,i)
private opaque symbol priv_VfromI (a A j i : τ ι) :
  π (a ∈ Vfrom A j) → π (lt j i) → π (a ∈ Vfrom A i) ≔
begin
  assume a A j i ha hji;
  refine Vfrom_mono A A j i (subset_refl A)
    (OrdmemD i j (ltD j i hji) (lt_Ord2 j i hji)) a ha
end;

// port-internal helper (Isabelle Univ.Limit_VfromE):
//   a ∈ Vfrom(A,i) → Limit(i) → (⋀x. x<i → a ∈ Vfrom(A,x) → Q) → Q
private opaque symbol priv_Limit_VfromE (a A i : τ ι) (Q : Prop) :
  π (a ∈ Vfrom A i) → π (Limit i) →
  (Π (x : τ ι), π (lt x i) → π (a ∈ Vfrom A x) → π Q) → π Q ≔
begin
  assume a A i Q ha hLim hcont;
  have hU : π (a ∈ Union (RepFun i (λ j, Vfrom A j)))
    { refine ind_eq (eq_sym (Limit_Vfrom_eq A i hLim)) (λ w, a ∈ w) ha };
  refine ∃ₑ (UnionE a (RepFun i (λ j, Vfrom A j)) hU) _;
  assume S hS;
  refine ∃ₑ (∧ₑ₁ (RepFun_iff S i (λ j, Vfrom A j)) (∧ₑ₁ hS)) _;
  assume x hx;
  refine hcont x (ltI x i (∧ₑ₁ hx) (Limit_is_Ord i hLim))
    (ind_eq (eq_sym (∧ₑ₂ hx)) (λ w, a ∈ w) (∧ₑ₂ hS))
end;

// port-internal helper (kernel of Univ.thy's *_in_Vfrom lemmas):
//   X ⊆ Vfrom(A,i) → X ∈ Vfrom(A,succ(i))
private opaque symbol priv_subset_mem_Vfrom_succ (X A i : τ ι) :
  π (X ⊆ Vfrom A i) → π (X ∈ Vfrom A (succ i)) ≔
begin
  assume X A i hsub;
  refine ind_eq (Vfrom_succ A i) (λ w, X ∈ w)
    (Un_upper2 A (Pow (Vfrom A i)) X (PowI X (Vfrom A i) hsub))
end;

// port-internal helper (Isabelle Univ.doubleton_in_Vfrom)
private opaque symbol priv_doubleton_in_Vfrom (a b A i : τ ι) :
  π (a ∈ Vfrom A i) → π (b ∈ Vfrom A i) → π (Upair a b ∈ Vfrom A (succ i)) ≔
begin
  assume a b A i ha hb;
  refine priv_subset_mem_Vfrom_succ (Upair a b) A i _;
  assume z hz;
  refine ∨ₑ (UpairE z a b hz) _ _
  { assume hza; rewrite hza; refine ha }
  { assume hzb; rewrite hzb; refine hb }
end;

// port-internal helper (Isabelle Univ.singleton_in_Vfrom)
private opaque symbol priv_singleton_in_Vfrom (a A i : τ ι) :
  π (a ∈ Vfrom A i) → π (singleton a ∈ Vfrom A (succ i)) ≔
begin
  assume a A i ha;
  refine priv_subset_mem_Vfrom_succ (singleton a) A i _;
  assume z hz;
  have hza : π (z = a) { refine ∧ₑ₁ (singleton_iff z a) hz };
  rewrite hza; refine ha
end;

// port-internal helper (Isabelle Univ.Pair_in_Vfrom)
private opaque symbol priv_Pair_in_Vfrom (a b A i : τ ι) :
  π (a ∈ Vfrom A i) → π (b ∈ Vfrom A i) → π (Pair a b ∈ Vfrom A (succ (succ i))) ≔
begin
  assume a b A i ha hb;
  have hres : π (Upair (singleton a) (Upair a b) ∈ Vfrom A (succ (succ i)))
    { refine priv_doubleton_in_Vfrom (singleton a) (Upair a b) A (succ i)
        (priv_singleton_in_Vfrom a A i ha) (priv_doubleton_in_Vfrom a b A i ha hb) };
  refine ind_eq (Pair_def a b) (λ w, w ∈ Vfrom A (succ (succ i))) hres
end;

// port-internal helper (Isabelle Univ.Pair_in_VLimit)
private opaque symbol priv_Pair_in_VLimit (a b A i : τ ι) :
  π (a ∈ Vfrom A i) → π (b ∈ Vfrom A i) → π (Limit i) → π (Pair a b ∈ Vfrom A i) ≔
begin
  assume a b A i ha hb hLim;
  refine priv_Limit_VfromE a A i (Pair a b ∈ Vfrom A i) ha hLim _;
  assume x hx hax;
  refine priv_Limit_VfromE b A i (Pair a b ∈ Vfrom A i) hb hLim _;
  assume y hy hby;
  have hax' : π (a ∈ Vfrom A (Un x y))
    { refine Vfrom_mono A A x (Un x y) (subset_refl A) (Un_upper1 x y) a hax };
  have hby' : π (b ∈ Vfrom A (Un x y))
    { refine Vfrom_mono A A y (Un x y) (subset_refl A) (Un_upper2 x y) b hby };
  have hUn_lt : π (lt (Un x y) i) { refine priv_Un_least_lt x y i hx hy };
  have hs1 : π (succ (Un x y) ∈ i)
    { refine Limit_has_succ i (Un x y) hLim (ltD (Un x y) i hUn_lt) };
  have hs2 : π (succ (succ (Un x y)) ∈ i)
    { refine Limit_has_succ i (succ (Un x y)) hLim hs1 };
  refine priv_VfromI (Pair a b) A (succ (succ (Un x y))) i
    (priv_Pair_in_Vfrom a b A (Un x y) hax' hby')
    (ltI (succ (succ (Un x y))) i hs2 (Limit_is_Ord i hLim))
end;

// port-internal helper (Isabelle Univ.zero_in_VLimit)
private opaque symbol priv_zero_in_VLimit (A i : τ ι) :
  π (Limit i) → π (empty ∈ Vfrom A i) ≔
begin
  assume A i hLim;
  refine i_subset_Vfrom A i empty (ltD empty i (Limit_has_0 i hLim))
end;

// port-internal helper (Isabelle Univ.nat_into_VLimit)
private opaque symbol priv_nat_into_VLimit (n A i : τ ι) :
  π (n ∈ omega) → π (Limit i) → π (n ∈ Vfrom A i) ≔
begin
  assume n A i hn hLim;
  refine i_subset_Vfrom A i n
    (le_imp_subset omega i (nat_le_Limit i hLim) n hn)
end;

// port-internal helper (Isabelle func.Pi_type, membership form:
//   f ∈ Pi(A,B) → (⋀x. x∈A → f`x ∈ D(x)) → f ∈ Pi(A,D);
//   func.lp's Pi_type is the pointwise-subset weakening, which is too weak here)
private opaque symbol priv_Pi_type_mem (f A : τ ι) (B D : τ ι → τ ι) :
  π (f ∈ Pi A B) → (Π (x : τ ι), π (x ∈ A) → π (fapply f x ∈ D x)) → π (f ∈ Pi A D) ≔
begin
  assume f A B D hf happ;
  have hparts : π (function f ∧ (f ⊆ Sigma A B ∧ A ⊆ domain f))
    { refine ∧ₑ₁ (Pi_iff f A B) hf };
  refine ∧ₑ₂ (Pi_iff f A D) _;
  refine ∧ᵢ (∧ₑ₁ hparts) (∧ᵢ _ (∧ₑ₂ (∧ₑ₂ hparts)));
  assume p hp;
  have hpS : π (p ∈ Sigma A B) { refine ∧ₑ₁ (∧ₑ₂ hparts) p hp };
  refine ∃ₑ (SigmaE p A B hpS) _;
  assume x hx;
  refine ∃ₑ (∧ₑ₂ hx) _;
  assume y hy;
  have hpeq : π (p = Pair x y) { refine ∧ₑ₂ hy };
  have hxy_f : π (Pair x y ∈ f) { refine ind_eq (eq_sym hpeq) (λ w, w ∈ f) hp };
  have hfx : π (fapply f x = y)
    { refine function_apply_equality x y f hxy_f (∧ₑ₁ hparts) };
  have hyD : π (y ∈ D x)
    { refine ind_eq (eq_sym hfx) (λ w, w ∈ D x) (happ x (∧ₑ₁ hx)) };
  rewrite hpeq;
  refine SigmaI x y A D (∧ₑ₁ hx) hyD
end;

// fun_Limit_VfromE = Limit_VfromE [OF apply_funtype InfCard_csucc [THEN InfCard_is_Limit]]
opaque symbol fun_Limit_VfromE (f D A K d : τ ι) (Q : Prop) :
  π (f ∈ Pi D (λ _, Vfrom A (csucc K))) → π (d ∈ D) → π (InfCard K) →
  (Π (x : τ ι), π (lt x (csucc K)) → π (fapply f d ∈ Vfrom A x) → π Q) → π Q ≔
begin
  assume f D A K d Q hf hd hICK hcont;
  refine priv_Limit_VfromE (fapply f d) A (csucc K) Q
    (fapply_type f d D (λ _, Vfrom A (csucc K)) hf hd)
    (InfCard_is_Limit (csucc K) (InfCard_csucc K hICK)) hcont
end;

opaque symbol fun_Vcsucc_lemma (f D A K : τ ι) :
  π (f ∈ Pi D (λ _, Vfrom A (csucc K))) → π (le (cardinal D) K) → π (InfCard K) →
  π (`∃ (j : τ ι), f ∈ Pi D (λ _, Vfrom A j) ∧ lt j (csucc K)) ≔
begin
  assume f D A K hf hDK hICK;
  // witness: j := ⋃_{z∈D} μ i. f`z ∈ Vfrom(A,i)
  refine ∃ᵢ (Union (RepFun D (λ z, Least (λ i, fapply f z ∈ Vfrom A i)))) _;
  refine ∧ᵢ _ _
  { // f ∈ D → Vfrom(A, ⋃_{z∈D} μ i. f`z ∈ Vfrom(A,i))
    refine priv_Pi_type_mem f D (λ _, Vfrom A (csucc K))
      (λ _, Vfrom A (Union (RepFun D (λ z, Least (λ i, fapply f z ∈ Vfrom A i))))) hf _;
    assume d hd;
    refine fun_Limit_VfromE f D A K d _ hf hd hICK _;
    assume x hx hfdx;
    have hLeast : π (fapply f d ∈ Vfrom A (Least (λ i, fapply f d ∈ Vfrom A i)))
      { refine LeastI (λ i, fapply f d ∈ Vfrom A i) x hfdx (lt_Ord x (csucc K) hx) };
    refine Vfrom_mono A A (Least (λ i, fapply f d ∈ Vfrom A i))
      (Union (RepFun D (λ z, Least (λ i, fapply f z ∈ Vfrom A i)))) (subset_refl A)
      (UN_upper d D (λ z, Least (λ i, fapply f z ∈ Vfrom A i)) hd)
      (fapply f d) hLeast }
  { // (⋃_{z∈D} μ i. f`z ∈ Vfrom(A,i)) < csucc(K)
    refine le_UN_Ord_lt_csucc K D (λ z, Least (λ i, fapply f z ∈ Vfrom A i)) hICK hDK _;
    assume d hd;
    refine fun_Limit_VfromE f D A K d _ hf hd hICK _;
    assume x hx hfdx;
    refine lt_trans1 (Least (λ i, fapply f d ∈ Vfrom A i)) x (csucc K)
      (Least_le (λ i, fapply f d ∈ Vfrom A i) x hfdx (lt_Ord x (csucc K) hx)) hx }
end;

opaque symbol subset_Vcsucc (D A K : τ ι) :
  π (D ⊆ Vfrom A (csucc K)) → π (le (cardinal D) K) → π (InfCard K) →
  π (`∃ (j : τ ι), D ⊆ Vfrom A j ∧ lt j (csucc K)) ≔
begin
  assume D A K hDsub hDK hICK;
  have hLim : π (Limit (csucc K))
    { refine InfCard_is_Limit (csucc K) (InfCard_csucc K hICK) };
  // witness: j := ⋃_{z∈D} μ i. z ∈ Vfrom(A,i)
  refine ∃ᵢ (Union (RepFun D (λ z, Least (λ i, z ∈ Vfrom A i)))) _;
  refine ∧ᵢ _ _
  { // D ⊆ Vfrom(A, ⋃_{z∈D} μ i. z ∈ Vfrom(A,i))
    assume d hd;
    refine priv_Limit_VfromE d A (csucc K)
      (d ∈ Vfrom A (Union (RepFun D (λ z, Least (λ i, z ∈ Vfrom A i)))))
      (hDsub d hd) hLim _;
    assume x hx hdx;
    have hLeast : π (d ∈ Vfrom A (Least (λ i, d ∈ Vfrom A i)))
      { refine LeastI (λ i, d ∈ Vfrom A i) x hdx (lt_Ord x (csucc K) hx) };
    refine Vfrom_mono A A (Least (λ i, d ∈ Vfrom A i))
      (Union (RepFun D (λ z, Least (λ i, z ∈ Vfrom A i)))) (subset_refl A)
      (UN_upper d D (λ z, Least (λ i, z ∈ Vfrom A i)) hd) d hLeast }
  { // (⋃_{z∈D} μ i. z ∈ Vfrom(A,i)) < csucc(K)
    refine le_UN_Ord_lt_csucc K D (λ z, Least (λ i, z ∈ Vfrom A i)) hICK hDK _;
    assume d hd;
    refine priv_Limit_VfromE d A (csucc K)
      (lt (Least (λ i, d ∈ Vfrom A i)) (csucc K)) (hDsub d hd) hLim _;
    assume x hx hdx;
    refine lt_trans1 (Least (λ i, d ∈ Vfrom A i)) x (csucc K)
      (Least_le (λ i, d ∈ Vfrom A i) x hdx (lt_Ord x (csucc K) hx)) hx }
end;

// Version for arbitrary index sets
opaque symbol fun_Vcsucc (D A K : τ ι) :
  π (le (cardinal D) K) → π (InfCard K) → π (D ⊆ Vfrom A (csucc K)) →
  π (Pi D (λ _, Vfrom A (csucc K)) ⊆ Vfrom A (csucc K)) ≔
begin
  assume D A K hDK hICK hDsub;
  have hLim : π (Limit (csucc K))
    { refine InfCard_is_Limit (csucc K) (InfCard_csucc K hICK) };
  assume f hf;
  // f ∈ D → Vfrom(A,j) with j < csucc(K);  D ⊆ Vfrom(A,ja) with ja < csucc(K)
  refine ∃ₑ (fun_Vcsucc_lemma f D A K hf hDK hICK) _;
  assume j hj;
  refine ∃ₑ (subset_Vcsucc D A K hDsub hDK hICK) _;
  assume ja hja;
  have hfj : π (f ∈ Pi D (λ _, Vfrom A j)) { refine ∧ₑ₁ hj };
  have hjlt : π (lt j (csucc K)) { refine ∧ₑ₂ hj };
  have hDja : π (D ⊆ Vfrom A ja) { refine ∧ₑ₁ hja };
  have hjalt : π (lt ja (csucc K)) { refine ∧ₑ₂ hja };
  have hrel : π (f ⊆ Sigma D (λ _, Vfrom A j))
    { refine Pi_subset_Sigma f D (λ _, Vfrom A j) hfj };
  // every pair of f lands in Vfrom(A, succ(succ(j ∪ ja)))
  have hfsub : π (f ⊆ Vfrom A (succ (succ (Un j ja))))
    { assume p hp;
      refine ∃ₑ (SigmaE p D (λ _, Vfrom A j) (hrel p hp)) _;
      assume x hx;
      refine ∃ₑ (∧ₑ₂ hx) _;
      assume y hy;
      have hxV : π (x ∈ Vfrom A (Un j ja))
        { refine Vfrom_mono A A ja (Un j ja) (subset_refl A) (Un_upper2 j ja)
            x (hDja x (∧ₑ₁ hx)) };
      have hyV : π (y ∈ Vfrom A (Un j ja))
        { refine Vfrom_mono A A j (Un j ja) (subset_refl A) (Un_upper1 j ja)
            y (∧ₑ₁ hy) };
      refine ind_eq (∧ₑ₂ hy) (λ w, w ∈ Vfrom A (succ (succ (Un j ja))))
        (priv_Pair_in_Vfrom x y A (Un j ja) hxV hyV) };
  // that level lies inside csucc(K): Limit gives succ-closure
  have hUn_lt : π (lt (Un j ja) (csucc K))
    { refine priv_Un_least_lt j ja (csucc K) hjlt hjalt };
  have hs1 : π (succ (Un j ja) ∈ csucc K)
    { refine Limit_has_succ (csucc K) (Un j ja) hLim (ltD (Un j ja) (csucc K) hUn_lt) };
  have hs2 : π (succ (succ (Un j ja)) ∈ csucc K)
    { refine Limit_has_succ (csucc K) (succ (Un j ja)) hLim hs1 };
  // f ∈ Pow(Vfrom(A, succ succ (j∪ja))) ⊆ ⋃_{y∈csucc K} Pow(Vfrom(A,y)) ⊆ Vfrom(A, csucc K)
  have hfU : π (f ∈ Union (RepFun (csucc K) (λ y, Pow (Vfrom A y))))
    { refine UnionI f (Pow (Vfrom A (succ (succ (Un j ja)))))
        (RepFun (csucc K) (λ y, Pow (Vfrom A y)))
        (PowI f (Vfrom A (succ (succ (Un j ja)))) hfsub)
        (RepFunI (succ (succ (Un j ja))) (csucc K) (λ y, Pow (Vfrom A y)) hs2) };
  refine ind_eq (Vfrom_eq A (csucc K)) (λ w, f ∈ w)
    (Un_upper2 A (Union (RepFun (csucc K) (λ y, Pow (Vfrom A y)))) f hfU)
end;

opaque symbol fun_in_Vcsucc (f D A K : τ ι) :
  π (f ∈ Pi D (λ _, Vfrom A (csucc K))) → π (le (cardinal D) K) → π (InfCard K) →
  π (D ⊆ Vfrom A (csucc K)) → π (f ∈ Vfrom A (csucc K)) ≔
begin
  assume f D A K hf hDK hICK hDsub;
  refine fun_Vcsucc D A K hDK hICK hDsub f hf
end;

// Remove ⊆ from the rule above
// fun_in_Vcsucc' = fun_in_Vcsucc [OF _ _ _ subsetI]
opaque symbol fun_in_Vcsucc' (f D A K : τ ι) :
  π (f ∈ Pi D (λ _, Vfrom A (csucc K))) → π (le (cardinal D) K) → π (InfCard K) →
  (Π (x : τ ι), π (x ∈ D) → π (x ∈ Vfrom A (csucc K))) →
  π (f ∈ Vfrom A (csucc K)) ≔
begin
  assume f D A K hf hDK hICK hmem;
  refine fun_in_Vcsucc f D A K hf hDK hICK hmem
end;

// ** Version where K itself is the index set **

opaque symbol Card_fun_Vcsucc (K A : τ ι) :
  π (InfCard K) → π (Pi K (λ _, Vfrom A (csucc K)) ⊆ Vfrom A (csucc K)) ≔
begin
  assume K A hICK;
  have hOK : π (Ord K) { refine Card_is_Ord K (InfCard_is_Card K hICK) };
  have hlt : π (lt K (csucc K)) { refine lt_csucc K hOK };
  have hKsub : π (K ⊆ Vfrom A (csucc K))
    { refine subset_trans K (csucc K) (Vfrom A (csucc K))
        (OrdmemD (csucc K) K (ltD K (csucc K) hlt) (lt_Ord2 K (csucc K) hlt))
        (i_subset_Vfrom A (csucc K)) };
  refine fun_Vcsucc K A K (Ord_cardinal_le K hOK) hICK hKsub
end;

opaque symbol Card_fun_in_Vcsucc (f K A : τ ι) :
  π (f ∈ Pi K (λ _, Vfrom A (csucc K))) → π (InfCard K) → π (f ∈ Vfrom A (csucc K)) ≔
begin
  assume f K A hf hICK;
  refine Card_fun_Vcsucc K A hICK f hf
end;

opaque symbol Limit_csucc (K : τ ι) : π (InfCard K) → π (Limit (csucc K)) ≔
begin
  assume K hICK;
  refine InfCard_is_Limit (csucc K) (InfCard_csucc K hICK)
end;

// Pair_in_Vcsucc = Pair_in_VLimit [OF _ _ Limit_csucc]
opaque symbol Pair_in_Vcsucc (a b A K : τ ι) :
  π (a ∈ Vfrom A (csucc K)) → π (b ∈ Vfrom A (csucc K)) → π (InfCard K) →
  π (Pair a b ∈ Vfrom A (csucc K)) ≔
begin
  assume a b A K ha hb hICK;
  refine priv_Pair_in_VLimit a b A (csucc K) ha hb (Limit_csucc K hICK)
end;

// Inl_in_Vcsucc = Inl_in_VLimit [OF _ Limit_csucc]
opaque symbol Inl_in_Vcsucc (a A K : τ ι) :
  π (a ∈ Vfrom A (csucc K)) → π (InfCard K) → π (Inl a ∈ Vfrom A (csucc K)) ≔
begin
  assume a A K ha hICK;
  have hLim : π (Limit (csucc K)) { refine Limit_csucc K hICK };
  have hp : π (Pair empty a ∈ Vfrom A (csucc K))
    { refine priv_Pair_in_VLimit empty a A (csucc K)
        (priv_zero_in_VLimit A (csucc K) hLim) ha hLim };
  refine ind_eq (Inl_def a) (λ w, w ∈ Vfrom A (csucc K)) hp
end;

// Inr_in_Vcsucc = Inr_in_VLimit [OF _ Limit_csucc]
opaque symbol Inr_in_Vcsucc (b A K : τ ι) :
  π (b ∈ Vfrom A (csucc K)) → π (InfCard K) → π (Inr b ∈ Vfrom A (csucc K)) ≔
begin
  assume b A K hb hICK;
  have hLim : π (Limit (csucc K)) { refine Limit_csucc K hICK };
  have h1 : π (one ∈ Vfrom A (csucc K))
    { refine priv_nat_into_VLimit one A (csucc K) nat_1I hLim };
  have hp : π (Pair one b ∈ Vfrom A (csucc K))
    { refine priv_Pair_in_VLimit one b A (csucc K) h1 hb hLim };
  refine ind_eq (Inr_def b) (λ w, w ∈ Vfrom A (csucc K)) hp
end;

// zero_in_Vcsucc = Limit_csucc [THEN zero_in_VLimit]
opaque symbol zero_in_Vcsucc (A K : τ ι) :
  π (InfCard K) → π (empty ∈ Vfrom A (csucc K)) ≔
begin
  assume A K hICK;
  refine priv_zero_in_VLimit A (csucc K) (Limit_csucc K hICK)
end;

// nat_into_Vcsucc = nat_into_VLimit [OF _ Limit_csucc]
opaque symbol nat_into_Vcsucc (n A K : τ ι) :
  π (n ∈ omega) → π (InfCard K) → π (n ∈ Vfrom A (csucc K)) ≔
begin
  assume n A K hn hICK;
  refine priv_nat_into_VLimit n A (csucc K) hn (Limit_csucc K hICK)
end;

// For handling Cardinals of the form  nat ∪ |X|

// InfCard_nat_Un_cardinal = InfCard_Un [OF InfCard_nat Card_cardinal]
opaque symbol InfCard_nat_Un_cardinal (A : τ ι) : π (InfCard (Un omega (cardinal A))) ≔
begin
  assume A;
  refine InfCard_Un omega (cardinal A) InfCard_nat (Card_cardinal A)
end;

// le_nat_Un_cardinal = Un_upper2_le [OF Ord_nat Card_cardinal [THEN Card_is_Ord]]
opaque symbol le_nat_Un_cardinal (A : τ ι) :
  π (le (cardinal A) (Un omega (cardinal A))) ≔
begin
  assume A;
  refine Un_upper2_le omega (cardinal A) Ord_omega
    (Card_is_Ord (cardinal A) (Card_cardinal A))
end;

// UN_upper_cardinal = UN_upper [THEN subset_imp_lepoll, THEN lepoll_imp_cardinal_le]
opaque symbol UN_upper_cardinal (a A : τ ι) (B : τ ι → τ ι) :
  π (a ∈ A) → π (le (cardinal (B a)) (cardinal (Union (RepFun A B)))) ≔
begin
  assume a A B ha;
  refine lepoll_imp_cardinal_le (B a) (Union (RepFun A B))
    (subset_imp_lepoll (B a) (Union (RepFun A B)) (UN_upper a A B ha))
end;
