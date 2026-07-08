// Nat_ZF: Natural numbers as a ZF set (ω)
//
// Isabelle source: Nat.thy
// Defines: nat (ω), nat_case, nat_rec
// ω is the smallest limit ordinal (= Inf ∩ {all inductive sets})

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func ZF.WF ZF.Ordinal ZF.Bool_ZF;

// ===========================================================================
// ω — the set of natural numbers
// ===========================================================================

// An inductive set contains 0 and is closed under succ
symbol inductive_set (A : τ ι) : Prop ≔
  empty ∈ A ∧ (`∀ (y : τ ι), y ∈ A ⇒ succ y ∈ A);

// ω = ⋂{X ∈ Pow(Inf) | inductive_set(X)}
// i.e., the smallest inductive subset of Inf
symbol omega : τ ι ≔
  Inter (Collect (Pow Inf) (λ X, inductive_set X));

// ===========================================================================
// ω is inductive
// ===========================================================================

// Inf is inductive (from the infinity axiom)
opaque symbol Inf_inductive : π (inductive_set Inf) ≔
begin
  refine infinity
end;

// 0 ∈ ω
opaque symbol zero_in_omega : π (empty ∈ omega) ≔
begin
  // no params to assume
  // omega = Inter(Collect(Pow Inf, inductive_set))
  // Need: empty ∈ Inter(...)
  // i.e., empty ∈ Collect(Union(...), Ball(...))
  // i.e., empty is in every inductive subset of Inf in Pow(Inf)
  // Use CollectI on the Inter definition
  have hinf_in : π (Inf ∈ Collect (Pow Inf) (λ X, inductive_set X))
    { refine CollectI Inf (Pow Inf) (λ X, inductive_set X)
        (PowI Inf Inf (subset_refl Inf)) Inf_inductive };
  // empty ∈ Union(Collect(...))
  have hun : π (empty ∈ Union (Collect (Pow Inf) (λ X, inductive_set X)))
    { refine UnionI empty Inf (Collect (Pow Inf) (λ X, inductive_set X))
        (∧ₑ₁ infinity) hinf_in };
  // Ball: empty is in every element of Collect(Pow Inf, inductive_set)
  refine CollectI empty
    (Union (Collect (Pow Inf) (λ X, inductive_set X)))
    (λ z, Ball (Collect (Pow Inf) (λ X, inductive_set X)) (λ Y, z ∈ Y))
    hun _;
  assume Y hY;
  have hind : π (inductive_set Y)
    { refine CollectD2 Y (Pow Inf) (λ X, inductive_set X) hY };
  refine ∧ₑ₁ hind
end;

// Helper: Inf is in the family Collect(Pow Inf, inductive_set)
opaque symbol Inf_in_family :
  π (Inf ∈ Collect (Pow Inf) (λ X, inductive_set X)) ≔
begin
  refine CollectI Inf (Pow Inf) (λ X, inductive_set X)
    (PowI Inf Inf (subset_refl Inf)) Inf_inductive
end;

// Helper: n ∈ omega → n ∈ Inf (omega is a subset of Inf)
opaque symbol omega_in_Inf (n : τ ι) :
  π (n ∈ omega) → π (n ∈ Inf) ≔
begin
  assume n hn;
  // n ∈ omega = Inter(Collect(Pow Inf, inductive_set))
  // = Collect(Union(...), λ x, Ball(..., λ Y, x ∈ Y))
  // So Ball(Collect(Pow Inf, inductive_set), λ Y, n ∈ Y)
  have hball : π (Ball (Collect (Pow Inf) (λ X, inductive_set X)) (λ Y, n ∈ Y))
    { refine CollectD2 n
        (Union (Collect (Pow Inf) (λ X, inductive_set X)))
        (λ z, Ball (Collect (Pow Inf) (λ X, inductive_set X)) (λ Y, z ∈ Y))
        hn };
  // Inf ∈ Collect(Pow Inf, inductive_set), so n ∈ Inf
  refine hball Inf Inf_in_family
end;

// Helper: omega ⊆ Inf
opaque symbol omega_subset_Inf : π (omega ⊆ Inf) ≔
begin
  assume x hx;
  refine omega_in_Inf x hx
end;

// succ(n) ∈ ω when n ∈ ω
opaque symbol succ_in_omega (n : τ ι) :
  π (n ∈ omega) → π (succ n ∈ omega) ≔
begin
  assume n hn;
  // succ(n) ∈ Inf (since n ∈ Inf and Inf is inductive)
  have hn_inf : π (n ∈ Inf) { refine omega_in_Inf n hn };
  have hsucc_inf : π (succ n ∈ Inf)
    { refine ∧ₑ₂ infinity n hn_inf };
  // succ(n) ∈ Union(Collect(Pow Inf, inductive_set))
  have hun : π (succ n ∈ Union (Collect (Pow Inf) (λ X, inductive_set X)))
    { refine UnionI (succ n) Inf (Collect (Pow Inf) (λ X, inductive_set X))
        hsucc_inf Inf_in_family };
  // Ball: succ(n) is in every element of Collect(Pow Inf, inductive_set)
  refine CollectI (succ n)
    (Union (Collect (Pow Inf) (λ X, inductive_set X)))
    (λ z, Ball (Collect (Pow Inf) (λ X, inductive_set X)) (λ Y, z ∈ Y))
    hun _;
  assume Y hY;
  // Y is inductive
  have hind : π (inductive_set Y)
    { refine CollectD2 Y (Pow Inf) (λ X, inductive_set X) hY };
  // n ∈ Y (from n ∈ omega, Ball)
  have hball : π (Ball (Collect (Pow Inf) (λ X, inductive_set X)) (λ Z, n ∈ Z))
    { refine CollectD2 n
        (Union (Collect (Pow Inf) (λ X, inductive_set X)))
        (λ z, Ball (Collect (Pow Inf) (λ X, inductive_set X)) (λ Z, z ∈ Z))
        hn };
  have hn_Y : π (n ∈ Y) { refine hball Y hY };
  // inductive_set(Y) gives closure under succ
  refine ∧ₑ₂ hind n hn_Y
end;

// ω is a limit ordinal
// Limit(ω) = Ord(ω) ∧ ω ≠ empty ∧ ∀y∈ω. succ(y) ∈ ω
// Proved after Ord_omega (below), but declared here — actually needs Ord_omega.
// We prove it after Ord_omega.

// ===========================================================================
// Natural number induction
// ===========================================================================

// Helper: Collect(omega, P) ⊆ omega
opaque symbol Collect_omega_sub (P : τ ι → Prop) :
  π (Collect omega P ⊆ omega) ≔
begin
  assume P x hx;
  refine CollectD1 x omega P hx
end;

// Helper: Collect(omega, P) ⊆ Inf
opaque symbol Collect_omega_sub_Inf (P : τ ι → Prop) :
  π (Collect omega P ⊆ Inf) ≔
begin
  assume P x hx;
  refine omega_in_Inf x (CollectD1 x omega P hx)
end;

opaque symbol nat_induct (P : τ ι → Prop) :
  π (P empty) →
  π (`∀ (n : τ ι), n ∈ omega ⇒ P n ⇒ P (succ n)) →
  π (Ball omega (λ n, P n)) ≔
begin
  assume P hbase hstep;
  // Strategy: show Collect(omega, P) is inductive and in Pow(Inf),
  // so omega ⊆ Collect(omega, P), hence Ball(omega, P).
  //
  // Step 1: Collect(omega, P) ∈ Pow(Inf)
  have hpow : π (Collect omega P ∈ Pow Inf)
    { refine PowI (Collect omega P) Inf (Collect_omega_sub_Inf P) };
  // Step 2: inductive_set(Collect(omega, P))
  have hind : π (inductive_set (Collect omega P)) {
    apply ∧ᵢ
    { // empty ∈ Collect(omega, P): empty ∈ omega and P(empty)
      refine CollectI empty omega P zero_in_omega hbase }
    { // ∀y. y ∈ Collect(omega, P) → succ(y) ∈ Collect(omega, P)
      assume y hy;
      have hy_omega : π (y ∈ omega) { refine CollectD1 y omega P hy };
      have hPy : π (P y) { refine CollectD2 y omega P hy };
      have hsucc_omega : π (succ y ∈ omega) { refine succ_in_omega y hy_omega };
      have hPsucc : π (P (succ y)) { refine hstep y hy_omega hPy };
      refine CollectI (succ y) omega P hsucc_omega hPsucc }
  };
  // Step 3: Collect(omega, P) ∈ Collect(Pow Inf, inductive_set)
  have hfam : π (Collect omega P ∈ Collect (Pow Inf) (λ X, inductive_set X))
    { refine CollectI (Collect omega P) (Pow Inf) (λ X, inductive_set X) hpow hind };
  // Step 4: omega ⊆ Collect(omega, P)
  // For x ∈ omega: x ∈ Inter(Collect(Pow Inf, inductive_set))
  // so Ball(Collect(Pow Inf, inductive_set), λ Y, x ∈ Y)
  // so x ∈ Collect(omega, P)
  assume x hx;
  have hball : π (Ball (Collect (Pow Inf) (λ X, inductive_set X)) (λ Y, x ∈ Y))
    { refine CollectD2 x
        (Union (Collect (Pow Inf) (λ X, inductive_set X)))
        (λ z, Ball (Collect (Pow Inf) (λ X, inductive_set X)) (λ Y, z ∈ Y))
        hx };
  have hx_coll : π (x ∈ Collect omega P) { refine hball (Collect omega P) hfam };
  refine CollectD2 x omega P hx_coll
end;

// ===========================================================================
// Every natural number is an ordinal
// ===========================================================================

opaque symbol nat_into_Ord (n : τ ι) :
  π (n ∈ omega) → π (Ord n) ≔
begin
  assume n hn;
  // Use nat_induct with P(n) = Ord(n)
  refine nat_induct (λ n, Ord n) Ord_0 _ n hn;
  // Step: ∀n∈ω. Ord(n) → Ord(succ(n))
  assume m hm hOm;
  refine Ord_succ m hOm
end;

// ===========================================================================
// Ordinal of ω
// ===========================================================================

opaque symbol Ord_omega : π (Ord omega) ≔
begin
  // Ord(ω) = Transset(ω) ∧ Ball(ω, Transset)
  apply ∧ᵢ
  { // Transset(ω): ∀x∈ω. x ⊆ ω
    // Use nat_induct with P(x) = x ⊆ omega
    // Actually, we need to show directly: for x ∈ omega, x ⊆ omega
    // Since x ∈ omega → Ord(x), and Ord(x) = Transset(x) ∧ Ball(x, Transset)
    // We need x ⊆ omega. Key: if y ∈ x and x ∈ omega, is y ∈ omega?
    // Use nat_induct with P(x) = Ball(x, λ y, y ∈ omega)
    // i.e., P(x) = x ⊆ omega
    have hsub : π (Ball omega (λ x, x ⊆ omega)) {
      refine nat_induct (λ x, x ⊆ omega) _ _
      { // Base: empty ⊆ omega
        refine empty_subset omega }
      { // Step: n ∈ omega, n ⊆ omega → succ(n) ⊆ omega
        assume m hm ihm;
        // succ(m) = cons(m, m). x ∈ succ(m) → x = m ∨ x ∈ m
        assume x hxs;
        have hdisj : π (x = m ∨ x ∈ m)
          { refine ∧ₑ₁ (succ_iff x m) hxs };
        refine ∨ₑ hdisj _ _
        { assume hxm; rewrite hxm; apply hm }
        { assume hxm; refine ihm x hxm } }
    };
    assume x hx;
    refine hsub x hx }
  { // Ball(ω, Transset): ∀x∈ω. Transset(x)
    assume x hx;
    refine ∧ₑ₁ (nat_into_Ord x hx) }
end;

// ω is a limit ordinal
opaque symbol Limit_omega : π (Limit omega) ≔
begin
  // Limit(ω) = Ord(ω) ∧ ω ≠ empty ∧ ∀y∈ω. succ(y) ∈ ω
  apply ∧ᵢ
  { apply Ord_omega }
  { apply ∧ᵢ
    { // ω ≠ empty: 0 ∈ ω
      refine ne_empty omega empty zero_in_omega }
    { // ∀y∈ω. succ(y) ∈ ω
      assume y hy;
      refine succ_in_omega y hy } }
end;

// ===========================================================================
// Successor injectivity
// ===========================================================================

// succ(m) = succ(n) → m = n
// Proof: m ∈ succ(m) = succ(n), so m = n ∨ m ∈ n.
//        n ∈ succ(n) = succ(m), so n = m ∨ n ∈ m.
//        If m ∈ n and n ∈ m, contradiction by mem_asym.
opaque symbol succ_inject (m n : τ ι) :
  π (succ m = succ n) → π (m = n) ≔
begin
  assume m n heq;
  // m ∈ succ(m) by succI1
  have hm_sm : π (m ∈ succ m) { refine succI1 m };
  // transport to m ∈ succ(n)
  have hm_sn : π (m ∈ succ n) { refine ind_eq (eq_sym heq) (λ z, m ∈ z) hm_sm };
  // m = n ∨ m ∈ n
  have hdisj1 : π (m = n ∨ m ∈ n)
    { refine ∧ₑ₁ (succ_iff m n) hm_sn };
  // n ∈ succ(n) by succI1
  have hn_sn : π (n ∈ succ n) { refine succI1 n };
  // transport to n ∈ succ(m)
  have hn_sm : π (n ∈ succ m)
    { refine ind_eq heq (λ z, n ∈ z) hn_sn };
  // n = m ∨ n ∈ m
  have hdisj2 : π (n = m ∨ n ∈ m)
    { refine ∧ₑ₁ (succ_iff n m) hn_sm };
  // case split on hdisj1
  refine ∨ₑ hdisj1 _ _
  { // m = n: done
    assume h; apply h }
  { // m ∈ n: case split on hdisj2
    assume hm_n;
    refine ∨ₑ hdisj2 _ _
    { // n = m: so m = n
      assume hn_m; symmetry; apply hn_m }
    { // n ∈ m: contradiction with mem_asym
      assume hn_m;
      refine ⊥ₑ (mem_asym m n hm_n hn_m) } }
end;

// ===========================================================================
// Case analysis on natural numbers (natE)
// ===========================================================================

// n ∈ omega → (n = empty → P) → (∀x∈omega. n = succ(x) → P) → P
opaque symbol natE (n : τ ι) (P : Prop) :
  π (n ∈ omega) →
  π (n = empty ⇒ P) →
  π ((`∀ (x : τ ι), x ∈ omega ⇒ n = succ x ⇒ P)) →
  π P ≔
begin
  assume n P hn h0 hsucc;
  // Use nat_induct with Q(k) = (k = n ⇒ P)
  // Then Q(0): 0 = n → P, and Q(succ m): succ(m) = n → P
  // Since n ∈ omega, Q(n) gives n = n → P, i.e., P.
  have hind : π (Ball omega (λ k, k = n ⇒ P)) {
    refine nat_induct (λ k, k = n ⇒ P) _ _
    { // Base: 0 = n → P
      assume heq;
      refine h0 (eq_sym heq) }
    { // Step: m ∈ ω, (m = n → P) → succ(m) = n → P
      assume m hm ih heq;
      refine hsucc m hm (eq_sym heq) }
  };
  refine hind n hn (eq_refl n)
end;

// ===========================================================================
// nat_case — case split function on natural numbers
// ===========================================================================

// nat_case(a, b, k) = THE y. (k = 0 ∧ y = a) ∨ (∃x. k = succ(x) ∧ y = b(x))
symbol nat_case (a : τ ι) (b : τ ι → τ ι) (k : τ ι) : τ ι ≔
  The (λ y, (k = empty ∧ y = a) ∨ (`∃ (x : τ ι), k = succ x ∧ y = b x));

// nat_case(a, b, 0) = a
opaque symbol nat_case_0 (a : τ ι) (b : τ ι → τ ι) :
  π (nat_case a b empty = a) ≔
begin
  assume a b;
  // P(y) = (empty = empty ∧ y = a) ∨ (∃x. empty = succ(x) ∧ y = b(x))
  // a is the unique witness (the succ disjunct is impossible), so
  // the_equality applies.
  refine the_equality
    (λ y, (empty = empty ∧ y = a) ∨ (`∃ (x : τ ι), empty = succ x ∧ y = b x))
    a (∨ᵢ₁ (∧ᵢ (eq_refl empty) (eq_refl a))) _;
  assume y hy;
  refine ∨ₑ hy _ _
  { assume h; refine ∧ₑ₂ h }
  { assume h;
    refine ∃ₑ h _;
    assume x hx;
    have habs : π (empty = succ x) { refine ∧ₑ₁ hx };
    refine ⊥ₑ (cons_not_empty x x (eq_sym habs)) }
end;

// nat_case(a, b, succ(n)) = b(n)
opaque symbol nat_case_succ (a : τ ι) (b : τ ι → τ ι) (n : τ ι) :
  π (nat_case a b (succ n) = b n) ≔
begin
  assume a b n;
  // P(y) = (succ(n) = empty ∧ y = a) ∨ (∃x. succ(n) = succ(x) ∧ y = b(x))
  // b(n) is the unique witness: the empty disjunct is impossible and
  // succ_inject collapses any other succ witness onto n.
  refine the_equality
    (λ y, (succ n = empty ∧ y = a)
          ∨ (`∃ (x : τ ι), succ n = succ x ∧ y = b x))
    (b n) (∨ᵢ₂ (∃ᵢ n (∧ᵢ (eq_refl (succ n)) (eq_refl (b n))))) _;
  assume y hy;
  refine ∨ₑ hy _ _
  { assume h;
    have habs : π (succ n = empty) { refine ∧ₑ₁ h };
    refine ⊥ₑ (cons_not_empty n n habs) }
  { assume h;
    refine ∃ₑ h _;
    assume x hx;
    have hn_x : π (n = x) { refine succ_inject n x (∧ₑ₁ hx) };
    refine ind_eq hn_x (λ z, y = b z) (∧ₑ₂ hx) }
end;

// ===========================================================================
// nat_rec — primitive recursion on ω
// ===========================================================================

// nat_rec(k, a, b) = wfrec(Memrel(ω), k, λ n f. nat_case(a, λ m. b(m, f`m), n))
symbol nat_rec (k a : τ ι) (b : τ ι → τ ι → τ ι) : τ ι ≔
  wfrec (Memrel omega) k (λ n f, nat_case a (λ m, b m (fapply f m)) n);

// nat_rec(0, a, b) = a
opaque symbol nat_rec_0 (a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (nat_rec empty a b = a) ≔
begin
  assume a b;
  have hwf : π (wf_global (Memrel omega)) { refine wf_Memrel omega };
  // wfrec_eq unfolds the wfrec; its RHS is convertible to nat_case a g 0,
  // with the recursion-function Lambda L = λx∈(Memrel ω)⁻¹{0}. nat_rec x a b.
  have h1 : π (nat_rec empty a b
    = nat_case a (λ m, b m (fapply (Lambda (vimage_singleton (Memrel omega) empty)
        (λ x, nat_rec x a b)) m)) empty)
    { refine wfrec_eq (Memrel omega) empty
        (λ n f, nat_case a (λ m, b m (fapply f m)) n) hwf };
  rewrite h1;
  // supply the case-function explicitly: nat_case reduces, so `apply nat_case_0`
  // would force a higher-order unification for it and fail.
  refine nat_case_0 a (λ m, b m (fapply (Lambda (vimage_singleton (Memrel omega) empty)
    (λ x, nat_rec x a b)) m))
end;

// nat_rec(succ(m), a, b) = b(m, nat_rec(m, a, b))
opaque symbol nat_rec_succ (m a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (m ∈ omega) → π (nat_rec (succ m) a b = b m (nat_rec m a b)) ≔
begin
  assume m a b hm;
  have hwf : π (wf_global (Memrel omega)) { refine wf_Memrel omega };
  have hsm : π (succ m ∈ omega) { refine succ_in_omega m hm };
  // m ∈ Memrel(ω)⁻¹{succ m}, since Pair m (succ m) ∈ Memrel(ω)
  have hmD : π (m ∈ vimage_singleton (Memrel omega) (succ m))
    { refine vimage_singletonI m (succ m) (Memrel omega)
        (MemrelI m (succ m) omega (succI1 m) hm hsm) };
  // Unfold via wfrec_eq into a clean nat_case application (L = recfun Lambda).
  have h1 : π (nat_rec (succ m) a b
    = nat_case a (λ k, b k (fapply (Lambda (vimage_singleton (Memrel omega) (succ m))
        (λ x, nat_rec x a b)) k)) (succ m))
    { refine wfrec_eq (Memrel omega) (succ m)
        (λ n f, nat_case a (λ k, b k (fapply f k)) n) hwf };
  rewrite h1;
  // nat_case … (succ m) = b m (fapply L m)
  have h2 : π (nat_case a (λ k, b k (fapply (Lambda (vimage_singleton (Memrel omega) (succ m))
        (λ x, nat_rec x a b)) k)) (succ m)
    = b m (fapply (Lambda (vimage_singleton (Memrel omega) (succ m))
        (λ x, nat_rec x a b)) m))
    { refine nat_case_succ a (λ k, b k (fapply (Lambda (vimage_singleton (Memrel omega) (succ m))
        (λ x, nat_rec x a b)) k)) m };
  rewrite h2;
  // fapply L m = nat_rec m a b  by beta
  refine feq (b m) _;
  refine beta (vimage_singleton (Memrel omega) (succ m)) (λ x, nat_rec x a b) m hmD
end;

// ===========================================================================
// Additional nat lemmas (Nat.thy) needed downstream (e.g. Arith)
// ===========================================================================

// succ(i) ∈ nat ⟹ i ∈ nat
opaque symbol succ_natD (i : τ ι) : π (succ i ∈ omega) → π (i ∈ omega) ≔
begin
  assume i hsi;
  refine natE (succ i) (i ∈ omega) hsi _ _
  { assume heq; refine ⊥ₑ (cons_not_empty i i heq) }
  { assume x hx heq;
    have hix : π (i = x) { refine succ_inject i x heq };
    rewrite hix; refine hx }
end;

// succ(n) ∈ nat ⟺ n ∈ nat
opaque symbol nat_succ_iff (n : τ ι) : π (succ n ∈ omega ⇔ n ∈ omega) ≔
begin
  assume n;
  refine ∧ᵢ _ _
  { assume h; refine succ_natD n h }
  { assume h; refine succ_in_omega n h }
end;

// ⟦m<n; n∈nat⟧ ⟹ m∈nat   (nat is transitive: m∈n∈omega, Ord omega)
opaque symbol lt_nat_in_nat (m n : τ ι) : π (lt m n) → π (n ∈ omega) → π (m ∈ omega) ≔
begin
  assume m n hlt hn;
  refine Ord_trans m n omega (ltD m n hlt) hn Ord_omega
end;

// ⟦m≤n; n∈nat⟧ ⟹ m∈nat
opaque symbol le_in_nat (m n : τ ι) : π (le m n) → π (n ∈ omega) → π (m ∈ omega) ≔
begin
  assume m n hle hn;
  refine ∨ₑ (leE m n hle) _ _
  { assume hmn; refine Ord_trans m n omega hmn hn Ord_omega }
  { assume heq; rewrite heq; refine hn }
end;

// 1 ∈ nat
opaque symbol nat_1I : π (succ empty ∈ omega) ≔
begin refine succ_in_omega empty zero_in_omega end;

// 2 ∈ nat
opaque symbol nat_2I : π (succ (succ empty) ∈ omega) ≔
begin refine succ_in_omega (succ empty) nat_1I end;

// nat ≠ 0
opaque symbol nat_nonempty : π (omega ≠ empty) ≔
begin
  assume h;
  refine emptyE empty (ind_eq (eq_sym h) (λ w, empty ∈ w) zero_in_omega)
end;

// a ∈ nat ⟹ ¬ Limit(a)   (0 fails i≠0; succ x by not_succ_Limit)
opaque symbol naturals_not_limit (a : τ ι) : π (a ∈ omega) → π (¬ (Limit a)) ≔
begin
  assume a ha;
  refine natE a (¬ (Limit a)) ha _ _
  { assume heq; rewrite heq; assume hL;
    refine (∧ₑ₁ (∧ₑ₂ hL)) (eq_refl empty) }
  { assume x hx heq; rewrite heq; refine not_succ_Limit x }
end;

// ===========================================================================
// quasinat — allows a case split for nat_case
// ===========================================================================

symbol quasinat (n : τ ι) : Prop ≔ (n = empty) ∨ (`∃ m, n = succ m);

opaque symbol quasinat_0 : π (quasinat empty) ≔
begin refine ∨ᵢ₁ (eq_refl empty) end;

opaque symbol quasinat_succ (x : τ ι) : π (quasinat (succ x)) ≔
begin assume x; refine ∨ᵢ₂ (∃ᵢ x (eq_refl (succ x))) end;

// n ∈ nat ⟹ quasinat(n)
opaque symbol nat_imp_quasinat (n : τ ι) : π (n ∈ omega) → π (quasinat n) ≔
begin
  assume n hn;
  refine natE n (quasinat n) hn _ _
  { assume heq; rewrite heq; refine quasinat_0 }
  { assume x hx heq; rewrite heq; refine quasinat_succ x }
end;

// k=0 | (∃y. k=succ y) | ¬quasinat(k)
opaque symbol nat_cases_disj (k : τ ι) :
  π ((k = empty) ∨ ((`∃ y, k = succ y) ∨ (¬ (quasinat k)))) ≔
begin
  assume k;
  refine ∨ₑ (em (k = empty)) _ _
  { assume h0; refine ∨ᵢ₁ h0 }
  { assume hn0;
    refine ∨ₑ (em (`∃ y, k = succ y)) _ _
    { assume hex; refine ∨ᵢ₂ (∨ᵢ₁ hex) }
    { assume hnex;
      refine ∨ᵢ₂ (∨ᵢ₂ _);
      assume hq;
      refine ∨ₑ hq _ _
      { assume h0; refine hn0 h0 }
      { assume hex; refine hnex hex } } }
end;

// case rule: k=0 / k=succ y / ¬quasinat(k)
opaque symbol nat_cases (k : τ ι) (P : Prop) :
  π (k = empty ⇒ P) → π (`∀ y, k = succ y ⇒ P) → π (¬ (quasinat k) ⇒ P) → π P ≔
begin
  assume k P h0 hsucc hnq;
  refine ∨ₑ (nat_cases_disj k) _ _
  { assume he0; refine h0 he0 }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume hex; refine ∃ₑ hex _; assume y hy; refine hsucc y hy }
    { assume hnq2; refine hnq hnq2 } }
end;

// ⟦n∈nat; a∈C(0); ⋀m. m∈nat⟹b(m)∈C(succ m)⟧ ⟹ nat_case(a,b,n)∈C(n)
opaque symbol nat_case_type (n a : τ ι) (b : τ ι → τ ι) (C : τ ι → τ ι)
  (hn : π (n ∈ omega)) (ha : π (a ∈ C empty))
  (hb : Π m, π (m ∈ omega) → π (b m ∈ C (succ m))) :
  π (nat_case a b n ∈ C n) ≔
begin
  assume n a b C hn ha hb;
  refine natE n (nat_case a b n ∈ C n) hn _ _
  { assume heq; rewrite heq; rewrite (nat_case_0 a b); refine ha }
  { assume m hm heq; rewrite heq; rewrite (nat_case_succ a b m); refine hb m hm }
end;

// ===========================================================================
// nat closed under ∪ / ∩  (= max / min of two ordinals)
// ===========================================================================

// ⟦i∈nat; j∈nat⟧ ⟹ i ∪ j ∈ nat
opaque symbol Un_nat_type (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (Un i j ∈ omega) ≔
begin
  assume i j hi hj;
  refine ∨ₑ (Ord_linear i j (nat_into_Ord i hi) (nat_into_Ord j hj)) _ _
  { assume hij;
    have hisub : π (i ⊆ j) { refine OrdmemD j i hij (nat_into_Ord j hj) };
    have heq : π (Un i j = j)
      { refine subset_antisym (Un i j) j
          (Un_least i j j hisub (subset_refl j)) (Un_upper2 i j) };
    rewrite heq; refine hj }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume hij; rewrite hij; rewrite (Un_absorb j); refine hj }
    { assume hji;
      have hjsub : π (j ⊆ i) { refine OrdmemD i j hji (nat_into_Ord i hi) };
      have heq : π (Un i j = i)
        { refine subset_antisym (Un i j) i
            (Un_least i j i (subset_refl i) hjsub) (Un_upper1 i j) };
      rewrite heq; refine hi } }
end;

// ⟦i∈nat; j∈nat⟧ ⟹ i ∩ j ∈ nat
opaque symbol Int_nat_type (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (Int i j ∈ omega) ≔
begin
  assume i j hi hj;
  refine ∨ₑ (Ord_linear i j (nat_into_Ord i hi) (nat_into_Ord j hj)) _ _
  { assume hij;
    have hisub : π (i ⊆ j) { refine OrdmemD j i hij (nat_into_Ord j hj) };
    have heq : π (Int i j = i)
      { refine subset_antisym (Int i j) i
          (Int_lower1 i j) (Int_greatest i j i (subset_refl i) hisub) };
    rewrite heq; refine hi }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume hij; rewrite hij;
      have heq : π (Int j j = j)
        { refine subset_antisym (Int j j) j
            (Int_lower1 j j) (Int_greatest j j j (subset_refl j) (subset_refl j)) };
      rewrite heq; refine hj }
    { assume hji;
      have hjsub : π (j ⊆ i) { refine OrdmemD i j hji (nat_into_Ord i hi) };
      have heq : π (Int i j = j)
        { refine subset_antisym (Int i j) j
            (Int_lower2 i j) (Int_greatest i j j hjsub (subset_refl j)) };
      rewrite heq; refine hj } }
end;

// Limit(i) ⟹ nat ≤ i   (omega ⊆ i by induction: 0∈i, closed under succ)
opaque symbol nat_le_Limit (i : τ ι) : π (Limit i) → π (le omega i) ≔
begin
  assume i hL;
  have hall : π (Ball omega (λ w, w ∈ i)) {
    refine nat_induct (λ w, w ∈ i) _ _
    { simplify rule off; refine ltD empty i (Limit_has_0 i hL) }
    { assume w hw hIH; refine Limit_has_succ i w hL hIH }
  };
  have hsub : π (omega ⊆ i) { assume x hx; refine bspec omega (λ w, w ∈ i) x hall hx };
  refine subset_imp_le i omega hsub (Limit_is_Ord i hL) Ord_omega
end;

// i ∈ nat ⟹ {j ∈ nat. j < i} = i   (the nats below i are exactly its elements)
opaque symbol nat_eq_Collect_lt (i : τ ι) :
  π (i ∈ omega) → π (Collect omega (λ j, lt j i) = i) ≔
begin
  assume i hi;
  refine equality_iffI (Collect omega (λ j, lt j i)) i _;
  assume x;
  refine ∧ᵢ _ _
  { assume hx; refine ltD x i (CollectD2 x omega (λ j, lt j i) hx) }
  { assume hx;
    refine CollectI x omega (λ j, lt j i)
      (Ord_trans x i omega hx hi Ord_omega) (ltI x i hx (nat_into_Ord i hi)) }
end;

// diff_induct: the "difference" double-recursion induction scheme.
// ⟦m∈nat; n∈nat; ⋀x. x∈nat⟹P(x,0); ⋀y. y∈nat⟹P(0,succ y);
//   ⋀x y. ⟦x∈nat;y∈nat;P(x,y)⟧⟹P(succ x,succ y)⟧ ⟹ P(m,n).
// (outer nat_induct on n, inner natE on m — the inner IH is not needed)
opaque symbol diff_induct (m n : τ ι) (P : τ ι → τ ι → Prop)
  (hm : π (m ∈ omega)) (hn : π (n ∈ omega))
  (h0 : Π x, π (x ∈ omega) → π (P x empty))
  (h0s : Π y, π (y ∈ omega) → π (P empty (succ y)))
  (hss : Π x y, π (x ∈ omega) → π (y ∈ omega) → π (P x y) → π (P (succ x) (succ y))) :
  π (P m n) ≔
begin
  assume m n P hm hn h0 h0s hss;
  have hall : π (Ball omega (λ b, Ball omega (λ a, P a b))) {
    refine nat_induct (λ b, Ball omega (λ a, P a b)) _ _
    { simplify rule off; assume a ha; refine h0 a ha }
    { assume b hb IHb; assume a ha;
      refine natE a (P a (succ b)) ha _ _
      { assume heq; rewrite heq; refine h0s b hb }
      { assume a' ha' heq; rewrite heq;
        refine hss a' b ha' hb (bspec omega (λ w, P w b) a' IHb ha') } }
  };
  refine bspec omega (λ a, P a n) m
    (bspec omega (λ b, Ball omega (λ a, P a b)) n hall hn) hm
end;

// ¬quasinat(x) ⟹ nat_case(a,b,x) = 0   (the defining predicate is unsatisfiable)
opaque symbol non_nat_case (a : τ ι) (b : τ ι → τ ι) (x : τ ι) :
  π (¬ (quasinat x)) → π (nat_case a b x = empty) ≔
begin
  assume a b x hnq;
  refine the_0 (λ y, (x = empty ∧ y = a) ∨ (`∃ (z : τ ι), x = succ z ∧ y = b z)) _;
  assume hex;
  refine ∃ₑ hex _;
  assume y0 hy0;
  refine hnq _;
  refine ∨ₑ (∧ₑ₁ hy0) _ _
  { assume h; refine ∨ᵢ₁ (∧ₑ₁ h) }
  { assume h; refine ∨ᵢ₂ _; refine ∃ₑ h _; assume z hz; refine ∃ᵢ z (∧ₑ₁ hz) }
end;

// bool ⊆ nat   (bool = {0,1}, both naturals)
opaque symbol bool_subset_nat : π (bool_set ⊆ omega) ≔
begin
  assume x hx;
  refine ∨ₑ (∧ₑ₁ (bool_iff x) hx) _ _
  { assume h0; rewrite h0; refine zero_in_omega }
  { assume h1; rewrite h1; refine nat_1I }
end;

// split rule for nat_case: P(nat_case a b k) ⟷
//   (k=0 ⟶ P a) ∧ (∀x. k=succ x ⟶ P(b x)) ∧ (¬quasinat k ⟶ P 0)
opaque symbol split_nat_case (P : τ ι → Prop) (a : τ ι) (b : τ ι → τ ι) (k : τ ι) :
  π (P (nat_case a b k) ⇔
     ((k = empty ⇒ P a) ∧ ((`∀ x, k = succ x ⇒ P (b x)) ∧ (¬ (quasinat k) ⇒ P empty)))) ≔
begin
  assume P a b k;
  refine nat_cases k
    (P (nat_case a b k) ⇔
     ((k = empty ⇒ P a) ∧ ((`∀ x, k = succ x ⇒ P (b x)) ∧ (¬ (quasinat k) ⇒ P empty))))
    _ _ _
  { assume hk0; rewrite hk0; rewrite (nat_case_0 a b);
    refine ∧ᵢ _ _
    { assume hpa; refine ∧ᵢ _ _
      { assume he; refine hpa }
      { refine ∧ᵢ _ _
        { assume x hx; refine ⊥ₑ (cons_not_empty x x (eq_sym hx)) }
        { assume h; refine ⊥ₑ (h quasinat_0) } } }
    { assume hrhs; refine ∧ₑ₁ hrhs (eq_refl empty) } }
  { assume y hky; rewrite hky; rewrite (nat_case_succ a b y);
    refine ∧ᵢ _ _
    { assume hpby; refine ∧ᵢ _ _
      { assume h; refine ⊥ₑ (cons_not_empty y y h) }
      { refine ∧ᵢ _ _
        { assume x hx; rewrite left (succ_inject y x hx); refine hpby }
        { assume h; refine ⊥ₑ (h (quasinat_succ y)) } } }
    { assume hrhs; refine ∧ₑ₁ (∧ₑ₂ hrhs) y (eq_refl (succ y)) } }
  { assume hnq; rewrite (non_nat_case a b k hnq);
    refine ∧ᵢ _ _
    { assume hpe; refine ∧ᵢ _ _
      { assume h0; refine ⊥ₑ (hnq (∨ᵢ₁ h0)) }
      { refine ∧ᵢ _ _
        { assume x hx; refine ⊥ₑ (hnq (∨ᵢ₂ (∃ᵢ x hx))) }
        { assume hnq2; refine hpe } } }
    { assume hrhs; refine ∧ₑ₂ (∧ₑ₂ hrhs) hnq } }
end;
