// Univ.lp — The cumulative hierarchy Vfrom/Vset.
// Translated from Isabelle/ZF Univ.thy (Paulson).
//
// Key definitions: Vfrom(A,i), Vset(i) = Vfrom(0,i)
// Key results: unfolding, monotonicity, 0/succ/limit cases,
//   rank characterization of membership.

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities
            ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Ordinal ZF.Nat_ZF ZF.Epsilon;

// ===========================================================================
// Vfrom(A, i) = A ∪ ⋃_{j ∈ i} Pow(Vfrom(A, j))
// Defined via transrec: Vfrom(A,i) = transrec(i, λx f. A ∪ ⋃_{y∈x} Pow(f`y))
// ===========================================================================

symbol Vfrom (A i : τ ι) : τ ι ≔
  transrec i (λ x f, Un A (Union (RepFun x (λ y, Pow (fapply f y)))));

// Vset(i) = Vfrom(∅, i)
symbol Vset (i : τ ι) : τ ι ≔ Vfrom empty i;

// ===========================================================================
// Recursion over Vset levels (Univ.thy)
//   Vrec(a,H)      = transrec(rank a, λx g. λz∈Vset(succ x). H(z, λw∈Vset x. g`rank w`w)) ` a
//   Vrecursor(H,a) = transrec(rank a, λx g. λz∈Vset(succ x). H(λw∈Vset x. g`rank w`w, z)) ` a
// ===========================================================================

symbol Vrec (a : τ ι) (H : τ ι → τ ι → τ ι) : τ ι ≔
  fapply (transrec (rank a)
    (λ x g, Lambda (Vset (succ x))
      (λ z, H z (Lambda (Vset x) (λ w, fapply (fapply g (rank w)) w))))) a;

symbol Vrecursor (H : τ ι → τ ι → τ ι) (a : τ ι) : τ ι ≔
  fapply (transrec (rank a)
    (λ x g, Lambda (Vset (succ x))
      (λ z, H (Lambda (Vset x) (λ w, fapply (fapply g (rank w)) w)) z))) a;

// univ(A) = Vfrom(A, nat)  [nat = omega in this port]
symbol univ (A : τ ι) : τ ι ≔ Vfrom A omega;

// ---------------------------------------------------------------------------
// Unfolding
// ---------------------------------------------------------------------------

// Vfrom(A, i) = A ∪ ⋃_{j ∈ i} Pow(Vfrom(A, j))   (Isabelle Univ.thy:43, def_transrec)
opaque symbol Vfrom_eq (A i : τ ι) :
  π (Vfrom A i = Un A (Union (RepFun i (λ j, Pow (Vfrom A j))))) ≔
begin
  assume A i;
  have hdt : π (Vfrom A i =
      Un A (Union (RepFun i (λ y, Pow (fapply (Lambda i (λ x, Vfrom A x)) y)))))
    { refine def_transrec (λ z, Vfrom A z)
        (λ x f, Un A (Union (RepFun x (λ y, Pow (fapply f y))))) i _;
      assume x; reflexivity };
  have hcong : π (Un A (Union (RepFun i (λ y, Pow (fapply (Lambda i (λ x, Vfrom A x)) y)))) =
      Un A (Union (RepFun i (λ j, Pow (Vfrom A j)))))
    { refine feq (Un A) _; refine feq Union _;
      refine RepFun_cong i (λ y, Pow (fapply (Lambda i (λ x, Vfrom A x)) y))
        (λ j, Pow (Vfrom A j)) _;
      assume y hy; refine feq Pow (beta i (λ x, Vfrom A x) y hy) };
  refine eq_trans hdt hcong
end;

// Vset(i) = ⋃_{j ∈ i} Pow(Vset(j))    (Isabelle Univ.thy:409)
// (Since A = ∅, the A ∪ ... simplifies to just the union via Un_empty_left)
opaque symbol Vset_eq (i : τ ι) :
  π (Vset i = Union (RepFun i (λ j, Pow (Vset j)))) ≔
begin
  assume i;
  refine eq_trans (Vfrom_eq empty i)
    (Un_empty_left (Union (RepFun i (λ j, Pow (Vfrom empty j)))))
end;

// ---------------------------------------------------------------------------
// Base cases
// ---------------------------------------------------------------------------

// Vfrom(A, 0) = A    (Isabelle Univ.thy:140)
opaque symbol Vfrom_0 (A : τ ι) :
  π (Vfrom A empty = A) ≔
begin
  assume A;
  have hempty : π (Union (RepFun empty (λ j, Pow (Vfrom A j))) = empty)
    { refine subset_antisym (Union (RepFun empty (λ j, Pow (Vfrom A j)))) empty _
        (empty_subset (Union (RepFun empty (λ j, Pow (Vfrom A j)))));
      assume z hz;
      have hbex : π (Bex (RepFun empty (λ j, Pow (Vfrom A j))) (λ S, z ∈ S))
        { refine UnionE z (RepFun empty (λ j, Pow (Vfrom A j))) hz };
      refine ∃ₑ hbex _; assume S hS;
      have hbex2 : π (Bex empty (λ j, S = Pow (Vfrom A j)))
        { refine ∧ₑ₁ (RepFun_iff S empty (λ j, Pow (Vfrom A j))) (∧ₑ₁ hS) };
      refine ∃ₑ hbex2 _; assume j hj; refine ⊥ₑ (emptyE j (∧ₑ₁ hj)) };
  refine eq_trans (Vfrom_eq A empty)
    (eq_trans (feq (Un A) hempty) (Un_empty_right A))
end;

// Vset(0) = ∅    (Vfrom_0 at A := ∅)
opaque symbol Vset_0 : π (Vset empty = empty) ≔
begin
  refine Vfrom_0 empty
end;

// Successor equations (Vfrom_succ, Vset_succ, Vfrom_succ_Transset) are proved
// in the "Successor & Transset equations" section at the end of this file —
// they depend on Vfrom_rank_eq / A_subset_Vfrom / Transset_Vfrom below.

// Limit equations (Limit_Vfrom_eq, Limit_Vset_eq) and the helper Vfrom_Union are
// proved in the "Limit equations" section at the end of this file — they depend
// on A_subset_Vfrom below.

// ---------------------------------------------------------------------------
// Monotonicity
// ---------------------------------------------------------------------------

// A ⊆ B → i ⊆ j → Vfrom(A, i) ⊆ Vfrom(B, j)   (Isabelle Univ.thy:48)
opaque symbol Vfrom_mono (A B i j : τ ι) :
  π (A ⊆ B) → π (i ⊆ j) → π (Vfrom A i ⊆ Vfrom B j) ≔
begin
  assume A B i j hAB hij;
  refine eps_induct
    (λ i', `∀ (j' : τ ι), i' ⊆ j' ⇒ Vfrom A i' ⊆ Vfrom B j') i _ j hij;
  assume x IH j' hxj';
  // hxj' : x ⊆ j' ;  goal : Vfrom A x ⊆ Vfrom B j'
  rewrite (Vfrom_eq A x);
  rewrite (Vfrom_eq B j');
  refine Un_mono A (Union (RepFun x (λ y, Pow (Vfrom A y)))) B
    (Union (RepFun j' (λ k, Pow (Vfrom B k)))) hAB _;
  refine UN_mono x j' (λ y, Pow (Vfrom A y)) (λ k, Pow (Vfrom B k)) hxj' _;
  assume y hy;
  refine Pow_mono (Vfrom A y) (Vfrom B y) (IH y hy y (subset_refl y))
end;

// Vfrom(A, x) ⊆ Vfrom(A, rank(x))   (Isabelle Univ.thy:66)
opaque symbol Vfrom_rank_subset1 (A x : τ ι) :
  π (Vfrom A x ⊆ Vfrom A (rank x)) ≔
begin
  assume A x;
  refine eps_induct (λ x', Vfrom A x' ⊆ Vfrom A (rank x')) x _;
  assume x0 IH;
  rewrite (Vfrom_eq A x0);
  rewrite (Vfrom_eq A (rank x0));
  refine Un_least A (Union (RepFun x0 (λ y, Pow (Vfrom A y))))
    (Un A (Union (RepFun (rank x0) (λ k, Pow (Vfrom A k)))))
    (Un_upper1 A (Union (RepFun (rank x0) (λ k, Pow (Vfrom A k))))) _;
  refine subset_trans (Union (RepFun x0 (λ y, Pow (Vfrom A y))))
    (Union (RepFun (rank x0) (λ k, Pow (Vfrom A k))))
    (Un A (Union (RepFun (rank x0) (λ k, Pow (Vfrom A k))))) _
    (Un_upper2 A (Union (RepFun (rank x0) (λ k, Pow (Vfrom A k)))));
  refine UN_least x0 (Union (RepFun (rank x0) (λ k, Pow (Vfrom A k))))
    (λ y, Pow (Vfrom A y)) _;
  assume y hy;
  refine subset_trans (Pow (Vfrom A y)) (Pow (Vfrom A (rank y)))
    (Union (RepFun (rank x0) (λ k, Pow (Vfrom A k))))
    (Pow_mono (Vfrom A y) (Vfrom A (rank y)) (IH y hy))
    (UN_upper (rank y) (rank x0) (λ k, Pow (Vfrom A k))
      (ltD (rank y) (rank x0) (rank_lt y x0 hy)))
end;

// Vfrom(A, rank(x)) ⊆ Vfrom(A, x)   (Isabelle Univ.thy:75)
opaque symbol Vfrom_rank_subset2 (A x : τ ι) :
  π (Vfrom A (rank x) ⊆ Vfrom A x) ≔
begin
  assume A x;
  refine eps_induct (λ x', Vfrom A (rank x') ⊆ Vfrom A x') x _;
  assume x0 IH;
  rewrite (Vfrom_eq A (rank x0));
  rewrite (Vfrom_eq A x0);
  refine Un_mono A (Union (RepFun (rank x0) (λ k, Pow (Vfrom A k)))) A
    (Union (RepFun x0 (λ y, Pow (Vfrom A y)))) (subset_refl A) _;
  refine UN_least (rank x0) (Union (RepFun x0 (λ y, Pow (Vfrom A y))))
    (λ k, Pow (Vfrom A k)) _;
  assume k hk;
  // hk : k ∈ rank x0 = ⋃_{y∈x0} succ(rank y)
  have hkU : π (k ∈ Union (RepFun x0 (λ y, succ (rank y))))
    { refine ind_eq (eq_sym (rank_eq x0)) (λ w, k ∈ w) hk };
  have hbex : π (Bex (RepFun x0 (λ y, succ (rank y))) (λ S, k ∈ S))
    { refine UnionE k (RepFun x0 (λ y, succ (rank y))) hkU };
  refine ∃ₑ hbex _; assume S hS;
  have hSrep : π (Bex x0 (λ y, S = succ (rank y)))
    { refine ∧ₑ₁ (RepFun_iff S x0 (λ y, succ (rank y))) (∧ₑ₁ hS) };
  refine ∃ₑ hSrep _; assume y hy;
  have hyx : π (y ∈ x0) { refine ∧ₑ₁ hy };
  have hksucc : π (k ∈ succ (rank y))
    { refine ind_eq (eq_sym (∧ₑ₂ hy)) (λ w, k ∈ w) (∧ₑ₂ hS) };
  have hksub : π (k ⊆ rank y)
    { refine le_imp_subset k (rank y)
        (ltI k (succ (rank y)) hksucc (Ord_succ (rank y) (Ord_rank y))) };
  have hVsub : π (Vfrom A k ⊆ Vfrom A y)
    { refine subset_trans (Vfrom A k) (Vfrom A (rank y)) (Vfrom A y)
        (Vfrom_mono A A k (rank y) (subset_refl A) hksub) (IH y hyx) };
  refine subset_trans (Pow (Vfrom A k)) (Pow (Vfrom A y))
    (Union (RepFun x0 (λ y', Pow (Vfrom A y'))))
    (Pow_mono (Vfrom A k) (Vfrom A y) hVsub)
    (UN_upper y x0 (λ y', Pow (Vfrom A y')) hyx)
end;

// Vfrom(A, rank(x)) = Vfrom(A, x)   (Isabelle Univ.thy:90)
opaque symbol Vfrom_rank_eq (A x : τ ι) :
  π (Vfrom A (rank x) = Vfrom A x) ≔
begin
  assume A x;
  refine subset_antisym (Vfrom A (rank x)) (Vfrom A x)
    (Vfrom_rank_subset2 A x) (Vfrom_rank_subset1 A x)
end;

// ---------------------------------------------------------------------------
// Inclusion properties
// ---------------------------------------------------------------------------

// A ⊆ Vfrom(A, i)   (Isabelle Univ.thy:107)
opaque symbol A_subset_Vfrom (A i : τ ι) :
  π (A ⊆ Vfrom A i) ≔
begin
  assume A i;
  refine ind_eq (Vfrom_eq A i) (λ w, A ⊆ w)
    (Un_upper1 A (Union (RepFun i (λ j, Pow (Vfrom A j)))))
end;

// i ⊆ Vfrom(A, i)   (Isabelle Univ.thy:102)
opaque symbol i_subset_Vfrom (A i : τ ι) :
  π (i ⊆ Vfrom A i) ≔
begin
  assume A i;
  refine eps_induct (λ i', i' ⊆ Vfrom A i') i _;
  assume x IH c hc;
  // hc : c ∈ x ;  goal : c ∈ Vfrom A x
  have hcU : π (c ∈ Union (RepFun x (λ j, Pow (Vfrom A j))))
    { refine UnionI c (Pow (Vfrom A c)) (RepFun x (λ j, Pow (Vfrom A j)))
        (PowI c (Vfrom A c) (IH c hc))
        (RepFunI c x (λ j, Pow (Vfrom A j)) hc) };
  refine ind_eq (Vfrom_eq A x) (λ w, c ∈ w)
    (Un_upper2 A (Union (RepFun x (λ j, Pow (Vfrom A j)))) c hcU)
end;

// Transset(A) → Transset(Vfrom(A, i))   (Isabelle Univ.thy:271)
opaque symbol Transset_Vfrom (A i : τ ι) :
  π (Transset A) → π (Transset (Vfrom A i)) ≔
begin
  assume A i hTA;
  refine eps_induct (λ i', Transset (Vfrom A i')) i _;
  assume x IH;
  rewrite (Vfrom_eq A x);
  refine Transset_Un A (Union (RepFun x (λ j, Pow (Vfrom A j)))) hTA _;
  refine Transset_Union_family (RepFun x (λ j, Pow (Vfrom A j))) _;
  assume S hS;
  have hbex : π (Bex x (λ j, S = Pow (Vfrom A j)))
    { refine ∧ₑ₁ (RepFun_iff S x (λ j, Pow (Vfrom A j))) hS };
  refine ∃ₑ hbex _; assume j hj;
  refine ind_eq (∧ₑ₂ hj) (λ w, Transset w)
    (Transset_Pow (Vfrom A j) (IH j (∧ₑ₁ hj)))
end;

// Transset(Vset(i))   (Isabelle Univ.thy:413)
opaque symbol Transset_Vset (i : τ ι) :
  π (Transset (Vset i)) ≔
begin
  assume i;
  refine Transset_Vfrom empty i Transset_0
end;

// ---------------------------------------------------------------------------
// Rank characterization of Vset membership
// ---------------------------------------------------------------------------

// Ord(i) → b ∈ Vset(i) → rank(b) < i   (Isabelle Univ.thy:417)
opaque symbol VsetD (i b : τ ι) :
  π (Ord i) → π (b ∈ Vset i) → π (lt (rank b) i) ≔
begin
  assume i b hOi hbV;
  refine trans_induct i (λ k, `∀ (c : τ ι), c ∈ Vset k ⇒ lt (rank c) k) hOi _ b hbV;
  assume x hOx IH c hcV;
  // hcV : c ∈ Vset x ;  goal : lt (rank c) x
  have hcU : π (c ∈ Union (RepFun x (λ j, Pow (Vset j))))
    { refine ind_eq (eq_sym (Vset_eq x)) (λ w, c ∈ w) hcV };
  have hbex : π (Bex (RepFun x (λ j, Pow (Vset j))) (λ S, c ∈ S))
    { refine UnionE c (RepFun x (λ j, Pow (Vset j))) hcU };
  refine ∃ₑ hbex _; assume S hS;
  have hSrep : π (Bex x (λ j, S = Pow (Vset j)))
    { refine ∧ₑ₁ (RepFun_iff S x (λ j, Pow (Vset j))) (∧ₑ₁ hS) };
  refine ∃ₑ hSrep _; assume j hj;
  have hjx : π (j ∈ x) { refine ∧ₑ₁ hj };
  have hcPow : π (c ∈ Pow (Vset j))
    { refine ind_eq (eq_sym (∧ₑ₂ hj)) (λ w, c ∈ w) (∧ₑ₂ hS) };
  have hcsub : π (c ⊆ Vset j) { refine PowD c (Vset j) hcPow };
  have hlt : π (lt (Union (RepFun c (λ d, succ (rank d)))) x)
    { refine UN_succ_least_lt x j c (λ d, rank d) (ltI j x hjx hOx) _;
      assume d hd;
      refine IH j hjx d (hcsub d hd) };
  refine ind_eq (rank_eq c) (λ w, lt w x) hlt
end;

// VsetI_lemma: Ord(i) → ∀b. rank(b) ∈ i → b ∈ Vset(i)   (Isabelle Univ.thy:424)
opaque symbol VsetI_lemma (i : τ ι) :
  π (Ord i) → π (`∀ (b : τ ι), rank b ∈ i ⇒ b ∈ Vset i) ≔
begin
  assume i hOi;
  refine trans_induct i (λ k, `∀ (b : τ ι), rank b ∈ k ⇒ b ∈ Vset k) hOi _;
  assume x hOx IH b hb;
  // hb : rank b ∈ x ;  goal : b ∈ Vset x
  have hsub : π (b ⊆ Vset (rank b))
    { assume c hc;
      refine IH (rank b) hb c (ltD (rank c) (rank b) (rank_lt c b hc)) };
  have hbU : π (b ∈ Union (RepFun x (λ j, Pow (Vset j))))
    { refine UnionI b (Pow (Vset (rank b))) (RepFun x (λ j, Pow (Vset j)))
        (PowI b (Vset (rank b)) hsub)
        (RepFunI (rank b) x (λ j, Pow (Vset j)) hb) };
  refine ind_eq (Vset_eq x) (λ w, b ∈ w) hbU
end;

// rank(x) < i → x ∈ Vset(i)   (Isabelle Univ.thy:432)
opaque symbol VsetI (x i : τ ι) :
  π (lt (rank x) i) → π (x ∈ Vset i) ≔
begin
  assume x i hlt;
  refine ltE (rank x) i (x ∈ Vset i) hlt _;
  assume hmem hOrx hOi;
  refine VsetI_lemma i hOi x hmem
end;

// b ∈ Vset(i) ↔ rank(b) < i, for ordinal i   (Isabelle Univ.thy:435)
opaque symbol Vset_Ord_rank_iff (i b : τ ι) :
  π (Ord i) → π (b ∈ Vset i ⇔ lt (rank b) i) ≔
begin
  assume i b hOi;
  refine ∧ᵢ _ _
  { assume hbV; refine VsetD i b hOi hbV }
  { assume hlt; refine VsetI b i hlt }
end;

// b ∈ Vset(a) ↔ rank(b) < rank(a)   (Isabelle Univ.thy:439)
opaque symbol Vset_rank_iff (a b : τ ι) :
  π (b ∈ Vset a ⇔ lt (rank b) (rank a)) ≔
begin
  assume a b;
  // Vset(a) = Vset(rank a) via Vfrom_rank_eq (at A := ∅)
  have heq : π (Vset a = Vset (rank a)) { refine eq_sym (Vfrom_rank_eq empty a) };
  refine ind_eq heq (λ w, b ∈ w ⇔ lt (rank b) (rank a))
    (Vset_Ord_rank_iff (rank a) b (Ord_rank a))
end;

// Ord(i) → rank(Vset(i)) = i   (Isabelle Univ.thy:447)
opaque symbol rank_Vset (i : τ ι) :
  π (Ord i) → π (rank (Vset i) = i) ≔
begin
  assume i hOi;
  refine eq_trans (rank_eq (Vset i)) _;
  // goal: ⋃_{y ∈ Vset i} succ(rank y) = i
  refine subset_antisym (Union (RepFun (Vset i) (λ y, succ (rank y)))) i _ _
  { // ⊆ : for y ∈ Vset i, rank y < i, so succ(rank y) ≤ i, so succ(rank y) ⊆ i
    refine UN_least (Vset i) i (λ y, succ (rank y)) _;
    assume y hy;
    refine le_imp_subset (succ (rank y)) i
      (succ_leI (rank y) i hOi (ltD (rank y) i (VsetD i y hOi hy))) }
  { // ⊇ : for w ∈ i, w is an ordinal, rank w = w, so w ∈ Vset i and w ∈ succ(rank w)
    assume w hw;
    have hOw : π (Ord w) { refine Ord_in_Ord i w hOi hw };
    have hrw : π (rank w = w) { refine rank_of_Ord w hOw };
    have hwV : π (w ∈ Vset i)
      { refine VsetI w i (ind_eq hrw (λ z, lt z i) (∧ᵢ hw hOi)) };
    have hwsucc : π (w ∈ succ (rank w))
      { refine ind_eq (feq succ hrw) (λ z, w ∈ z) (succI1 w) };
    refine UnionI w (succ (rank w)) (RepFun (Vset i) (λ y, succ (rank y)))
      hwsucc (RepFunI w (Vset i) (λ y, succ (rank y)) hwV) }
end;

// Every set belongs to some Vset (take i = succ(rank x)).
// Port-specific helper (not an Isabelle/ZF Univ.thy lemma), kept for consumers.
opaque symbol Vset_rank_exists (x : τ ι) :
  π (`∃ i : τ ι, Ord i ∧ x ∈ Vset i) ≔
begin
  assume x;
  have hOs : π (Ord (succ (rank x))) { refine Ord_succ (rank x) (Ord_rank x) };
  have hlt : π (lt (rank x) (succ (rank x))) { refine ∧ᵢ (succI1 (rank x)) hOs };
  refine ∃ᵢ (succ (rank x)) (∧ᵢ hOs (VsetI x (succ (rank x)) hlt))
end;

// ===========================================================================
// Successor & Transset equations
// (placed here: they depend on Vfrom_rank_eq / A_subset_Vfrom / Transset_Vfrom)
// ===========================================================================

// Ord(i) → Vfrom(A, succ(i)) = A ∪ Pow(Vfrom(A, i))   (Isabelle Univ.thy:143)
opaque symbol Vfrom_succ_lemma (A i : τ ι) :
  π (Ord i) → π (Vfrom A (succ i) = Un A (Pow (Vfrom A i))) ≔
begin
  assume A i hOi;
  refine eq_trans (Vfrom_eq A (succ i)) _;
  refine feq (Un A) _;
  refine subset_antisym (Union (RepFun (succ i) (λ j, Pow (Vfrom A j)))) (Pow (Vfrom A i)) _
    (UN_upper i (succ i) (λ j, Pow (Vfrom A j)) (succI1 i));
  refine UN_least (succ i) (Pow (Vfrom A i)) (λ j, Pow (Vfrom A j)) _;
  assume j hj;
  refine Pow_mono (Vfrom A j) (Vfrom A i)
    (Vfrom_mono A A j i (subset_refl A)
      (le_imp_subset j i (ltI j (succ i) hj (Ord_succ i hOi))))
end;

// Vfrom(A, succ(i)) = A ∪ Pow(Vfrom(A, i))   (Isabelle Univ.thy:153)
opaque symbol Vfrom_succ (A i : τ ι) :
  π (Vfrom A (succ i) = Un A (Pow (Vfrom A i))) ≔
begin
  assume A i;
  have e1 : π (Vfrom A (succ i) = Vfrom A (succ (rank i)))
    { refine eq_trans (eq_sym (Vfrom_rank_eq A (succ i))) (feq (Vfrom A) (rank_succ i)) };
  have e2 : π (Vfrom A (succ (rank i)) = Un A (Pow (Vfrom A (rank i))))
    { refine Vfrom_succ_lemma A (rank i) (Ord_rank i) };
  have e3 : π (Un A (Pow (Vfrom A (rank i))) = Un A (Pow (Vfrom A i)))
    { refine feq (λ w, Un A (Pow w)) (Vfrom_rank_eq A i) };
  refine eq_trans e1 (eq_trans e2 e3)
end;

// Vset(succ(i)) = Pow(Vset(i))   (Isabelle Univ.thy:412)
opaque symbol Vset_succ (i : τ ι) :
  π (Vset (succ i) = Pow (Vset i)) ≔
begin
  assume i;
  refine eq_trans (Vfrom_succ empty i) (Un_empty_left (Pow (Vfrom empty i)))
end;

// Transset(A) → Vfrom(A, succ(i)) = Pow(Vfrom(A, i))   (Isabelle Univ.thy:277)
opaque symbol Vfrom_succ_Transset (A i : τ ι) :
  π (Transset A) → π (Vfrom A (succ i) = Pow (Vfrom A i)) ≔
begin
  assume A i hTA;
  refine eq_trans (Vfrom_succ A i) _;
  refine subset_antisym (Un A (Pow (Vfrom A i))) (Pow (Vfrom A i)) _
    (Un_upper2 A (Pow (Vfrom A i)));
  refine Un_least A (Pow (Vfrom A i)) (Pow (Vfrom A i)) _ (subset_refl (Pow (Vfrom A i)));
  refine subset_trans A (Vfrom A i) (Pow (Vfrom A i))
    (A_subset_Vfrom A i)
    (Transset_iff_Pow_fwd (Vfrom A i) (Transset_Vfrom A i hTA))
end;

// ===========================================================================
// Limit equations
// (Vfrom_Union depends on A_subset_Vfrom; the Limit lemmas depend on Vfrom_Union)
// ===========================================================================

// y ∈ X → Vfrom(A, ⋃X) = ⋃_{y ∈ X} Vfrom(A, y)   (Isabelle Univ.thy:162)
opaque symbol Vfrom_Union (A X y0 : τ ι) :
  π (y0 ∈ X) → π (Vfrom A (Union X) = Union (RepFun X (λ y, Vfrom A y))) ≔
begin
  assume A X y0 hy0;
  refine eq_trans (Vfrom_eq A (Union X)) _;
  refine subset_antisym
    (Un A (Union (RepFun (Union X) (λ j, Pow (Vfrom A j)))))
    (Union (RepFun X (λ y, Vfrom A y))) _ _
  { // A ∪ ⋃_{j∈⋃X} Pow(Vfrom A j)  ⊆  ⋃_{y∈X} Vfrom A y
    refine Un_least A (Union (RepFun (Union X) (λ j, Pow (Vfrom A j))))
      (Union (RepFun X (λ y, Vfrom A y))) _ _
    { // A ⊆ Vfrom A y0 ⊆ ⋃
      refine subset_trans A (Vfrom A y0) (Union (RepFun X (λ y, Vfrom A y)))
        (A_subset_Vfrom A y0) (UN_upper y0 X (λ y, Vfrom A y) hy0) }
    { // ⋃_{j∈⋃X} Pow(Vfrom A j) ⊆ ⋃_{y∈X} Vfrom A y
      refine UN_least (Union X) (Union (RepFun X (λ y, Vfrom A y)))
        (λ j, Pow (Vfrom A j)) _;
      assume j hj;
      have hbex : π (Bex X (λ W, j ∈ W)) { refine UnionE j X hj };
      refine ∃ₑ hbex _; assume W hW;
      have hWX : π (W ∈ X) { refine ∧ₑ₁ hW };
      have hjW : π (j ∈ W) { refine ∧ₑ₂ hW };
      // Pow(Vfrom A j) ⊆ Vfrom A W ⊆ ⋃
      refine subset_trans (Pow (Vfrom A j)) (Vfrom A W)
        (Union (RepFun X (λ y, Vfrom A y)))
        _ (UN_upper W X (λ y, Vfrom A y) hWX);
      rewrite (Vfrom_eq A W);
      refine subset_trans (Pow (Vfrom A j)) (Union (RepFun W (λ k, Pow (Vfrom A k))))
        (Un A (Union (RepFun W (λ k, Pow (Vfrom A k)))))
        (UN_upper j W (λ k, Pow (Vfrom A k)) hjW)
        (Un_upper2 A (Union (RepFun W (λ k, Pow (Vfrom A k))))) } }
  { // ⋃_{y∈X} Vfrom A y  ⊆  A ∪ ⋃_{j∈⋃X} Pow(Vfrom A j)
    refine UN_least X (Un A (Union (RepFun (Union X) (λ j, Pow (Vfrom A j)))))
      (λ y, Vfrom A y) _;
    assume y hyX;
    rewrite (Vfrom_eq A y);
    refine Un_mono A (Union (RepFun y (λ k, Pow (Vfrom A k)))) A
      (Union (RepFun (Union X) (λ j, Pow (Vfrom A j)))) (subset_refl A) _;
    refine UN_mono y (Union X) (λ k, Pow (Vfrom A k)) (λ j, Pow (Vfrom A j)) _ _
    { assume c hc; refine UnionI c y X hc hyX }
    { assume k hk; refine subset_refl (Pow (Vfrom A k)) } }
end;

// Limit(i) → Vfrom(A, i) = ⋃_{j ∈ i} Vfrom(A, j)   (Isabelle Univ.thy:183)
opaque symbol Limit_Vfrom_eq (A i : τ ι) :
  π (Limit i) → π (Vfrom A i = Union (RepFun i (λ j, Vfrom A j))) ≔
begin
  assume A i hLim;
  have h0i : π (empty ∈ i) { refine ltD empty i (Limit_has_0 i hLim) };
  have hVU : π (Vfrom A (Union i) = Union (RepFun i (λ j, Vfrom A j)))
    { refine Vfrom_Union A i empty h0i };
  refine eq_trans (feq (Vfrom A) (eq_sym (Limit_Union_eq i hLim))) hVU
end;

// Limit(i) → Vset(i) = ⋃_{j ∈ i} Vset(j)   (Limit_Vfrom_eq at A := ∅)
opaque symbol Limit_Vset_eq (i : τ ι) :
  π (Limit i) → π (Vset i = Union (RepFun i (λ j, Vset j))) ≔
begin
  assume i hLim;
  refine Limit_Vfrom_eq empty i hLim
end;

// ===========================================================================
// Recursion equations for Vrec / Vrecursor (Univ.thy:493-521)
// NOT suitable for rewriting: recursive.
// ===========================================================================

// Vrec(a,H) = H(a, λx∈Vset(rank a). Vrec(x,H))
opaque symbol Vrec_eq (a : τ ι) (H : τ ι → τ ι → τ ι) :
  π (Vrec a H = H a (Lambda (Vset (rank a)) (λ x, Vrec x H))) ≔
begin
  assume a H;
  have hOra : π (Ord (rank a)) { refine Ord_rank a };
  have hOsra : π (Ord (succ (rank a))) { refine Ord_succ (rank a) hOra };
  have ha_in : π (a ∈ Vset (succ (rank a)))
    { refine VsetI a (succ (rank a))
        (ltI (rank a) (succ (rank a)) (succI1 (rank a)) hOsra) };
  // the recursive calls g`rank(w)`w collapse to Vrec w H on Vset(rank a)
  have hlam : π (Lambda (Vset (rank a))
        (λ w, fapply (fapply (Lambda (rank a)
          (λ xk, transrec xk (λ x2 g, Lambda (Vset (succ x2))
            (λ z, H z (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)))))) (rank w)) w)
      = Lambda (Vset (rank a)) (λ x, Vrec x H)) {
    refine lam_cong (Vset (rank a)) (Vset (rank a)) _ _ (eq_refl (Vset (rank a))) _;
    assume w hw;
    have hrw : π (rank w ∈ rank a)
      { refine ltD (rank w) (rank a) (VsetD (rank a) w hOra hw) };
    have hb : π (fapply (Lambda (rank a)
          (λ xk, transrec xk (λ x2 g, Lambda (Vset (succ x2))
            (λ z, H z (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)))))) (rank w)
        = transrec (rank w) (λ x2 g, Lambda (Vset (succ x2))
            (λ z, H z (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)))))
      { refine beta (rank a) (λ xk, transrec xk (λ x2 g, Lambda (Vset (succ x2))
            (λ z, H z (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2))))) (rank w) hrw };
    rewrite hb;
    reflexivity
  };
  have h1 : π (fapply (transrec (rank a) (λ x2 g, Lambda (Vset (succ x2))
        (λ z, H z (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2))))) a
      = H a (Lambda (Vset (rank a)) (λ x, Vrec x H))) {
    rewrite transrec_eq;
    simplify rule off;
    rewrite (beta (Vset (succ (rank a)))
      (λ z, H z (Lambda (Vset (rank a))
        (λ w, fapply (fapply (Lambda (rank a)
          (λ xk, transrec xk (λ x2 g, Lambda (Vset (succ x2))
            (λ z2, H z2 (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)))))) (rank w)) w)))
      a ha_in);
    simplify rule off;
    rewrite hlam;
    reflexivity
  };
  refine h1
end;

// Vrecursor(H,a) = H(λx∈Vset(rank a). Vrecursor(H,x), a)
opaque symbol Vrecursor_eq (H : τ ι → τ ι → τ ι) (a : τ ι) :
  π (Vrecursor H a = H (Lambda (Vset (rank a)) (λ x, Vrecursor H x)) a) ≔
begin
  assume H a;
  have hOra : π (Ord (rank a)) { refine Ord_rank a };
  have hOsra : π (Ord (succ (rank a))) { refine Ord_succ (rank a) hOra };
  have ha_in : π (a ∈ Vset (succ (rank a)))
    { refine VsetI a (succ (rank a))
        (ltI (rank a) (succ (rank a)) (succI1 (rank a)) hOsra) };
  have hlam : π (Lambda (Vset (rank a))
        (λ w, fapply (fapply (Lambda (rank a)
          (λ xk, transrec xk (λ x2 g, Lambda (Vset (succ x2))
            (λ z, H (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)) z)))) (rank w)) w)
      = Lambda (Vset (rank a)) (λ x, Vrecursor H x)) {
    refine lam_cong (Vset (rank a)) (Vset (rank a)) _ _ (eq_refl (Vset (rank a))) _;
    assume w hw;
    have hrw : π (rank w ∈ rank a)
      { refine ltD (rank w) (rank a) (VsetD (rank a) w hOra hw) };
    have hb : π (fapply (Lambda (rank a)
          (λ xk, transrec xk (λ x2 g, Lambda (Vset (succ x2))
            (λ z, H (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)) z)))) (rank w)
        = transrec (rank w) (λ x2 g, Lambda (Vset (succ x2))
            (λ z, H (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)) z)))
      { refine beta (rank a) (λ xk, transrec xk (λ x2 g, Lambda (Vset (succ x2))
            (λ z, H (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)) z))) (rank w) hrw };
    rewrite hb;
    reflexivity
  };
  have h1 : π (fapply (transrec (rank a) (λ x2 g, Lambda (Vset (succ x2))
        (λ z, H (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)) z))) a
      = H (Lambda (Vset (rank a)) (λ x, Vrecursor H x)) a) {
    rewrite transrec_eq;
    simplify rule off;
    rewrite (beta (Vset (succ (rank a)))
      (λ z, H (Lambda (Vset (rank a))
        (λ w, fapply (fapply (Lambda (rank a)
          (λ xk, transrec xk (λ x2 g, Lambda (Vset (succ x2))
            (λ z2, H (Lambda (Vset x2) (λ w2, fapply (fapply g (rank w2)) w2)) z2)))) (rank w)) w)) z)
      a ha_in);
    simplify rule off;
    rewrite hlam;
    reflexivity
  };
  refine h1
end;

// def_Vrec / def_Vrecursor: the h≡Vrec(_,H) form (avoids re-unfolding h)
opaque symbol def_Vrec (h : τ ι → τ ι) (H : τ ι → τ ι → τ ι)
  (hdef : Π x, π (h x = Vrec x H)) (a : τ ι) :
  π (h a = H a (Lambda (Vset (rank a)) (λ x, h x))) ≔
begin
  assume h H hdef a;
  rewrite (hdef a);
  have hlam : π (Lambda (Vset (rank a)) (λ x, h x) = Lambda (Vset (rank a)) (λ x, Vrec x H))
    { refine lam_cong (Vset (rank a)) (Vset (rank a)) _ _ (eq_refl (Vset (rank a))) _;
      assume x hx; refine hdef x };
  rewrite hlam;
  refine Vrec_eq a H
end;

opaque symbol def_Vrecursor (h : τ ι → τ ι) (H : τ ι → τ ι → τ ι)
  (hdef : Π x, π (h x = Vrecursor H x)) (a : τ ι) :
  π (h a = H (Lambda (Vset (rank a)) (λ x, h x)) a) ≔
begin
  assume h H hdef a;
  rewrite (hdef a);
  have hlam : π (Lambda (Vset (rank a)) (λ x, h x) = Lambda (Vset (rank a)) (λ x, Vrecursor H x))
    { refine lam_cong (Vset (rank a)) (Vset (rank a)) _ _ (eq_refl (Vset (rank a))) _;
      assume x hx; refine hdef x };
  rewrite hlam;
  refine Vrecursor_eq H a
end;
