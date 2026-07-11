// ZF.Bin — Arithmetic on Binary Integers
// Faithful port of isabelle-src/Bin.thy — COMPLETE: every lemma/theorem is
// proved, 0 admits.  bin_rec_def is a declared `_def` axiom (the defining
// equation of the abstract Vrec-based recursor), per Arith.lp's precedent.
// (Source: L. C. Paulson, ZF/Bin.thy.)
//
// BOOTSTRAP (hand-built, no proofs — same treatment as List.lp's list(A)):
//
//   bin is the package-generated 3-constructor datatype
//     "bin = Pls | Min | Bit(w∈bin, b∈bool)"     (infix "w BIT b")
//   encoded, as the datatype package genuinely does for a 3-way choice, via
//   a NESTED disjoint sum (domain univ(bool)):
//     Pls        = Inl(Inl(0))
//     Min        = Inl(Inr(0))
//     Bit(w,b)   = Inr(⟨w,b⟩)
//   freeness follows from Inl/Inr already being proved disjoint+injective in
//   Sum.lp, exactly as for List.lp's Nil/Cons.
//
//   bin_case/bin_rec are the package-generated case-analysis/recursor,
//   bin_rec built on Vrec (abstract symbol + defining axiom, per Arith.lp's
//   established precedent for Vrec-based recursors — see that file's header
//   and List.lp's list_rec for the identical treatment).
//
//   Every `primrec`'d function in Bin.thy (integ_of, NCons, bin_succ,
//   bin_pred, bin_minus, bin_adder, bin_mult) is a direct instance of
//   bin_rec — e.g. integ_of(w BIT b) = $#b $+ integ_of(w) $+ integ_of(w)
//   becomes `bin_rec ... (λ w2 b r, zadd (int_of b) (zadd r r)) w` where `r`
//   is the recursive value integ_of(w2).  bin_adder is recursion producing a
//   FUNCTION (λw∈bin. ...), i.e. `Lambda bin (λ w, ...)`, with the recursive
//   value `r` (= bin_adder(v2), itself a function) applied via `fapply r _`.
//
//   The numeral abbreviations #0/#1/#2/#-1/#-2 (not valid Lambdapi
//   identifiers) are rendered as Int0/Int1/Int2/NegInt1/NegInt2.

require open ZF.Int ZF.Datatype;

// ===========================================================================
// The datatype bin, its constructors, case analysis and recursor
// ===========================================================================

symbol bin : τ ι ≔
  lfp (univ bool_set)
    (λ X, sum (sum (singleton empty) (singleton empty)) (Sigma X (λ _, bool_set)));

symbol Pls : τ ι ≔ Inl (Inl empty);
symbol Min : τ ι ≔ Inl (Inr empty);
symbol Bit (w b : τ ι) : τ ι ≔ Inr (Pair w b);

symbol bin_case (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι) (z : τ ι) : τ ι ≔
  case_sum (case_sum (λ _, fPls) (λ _, fMin)) (split fBit) z;

// bin_rec(fPls,fMin,fBit,z) ≡
//   Vrec(z, λz2 g. bin_case(fPls, fMin, λw b. fBit(w,b,g`w), z2))
symbol bin_rec : τ ι → τ ι → (τ ι → τ ι → τ ι → τ ι) → τ ι → τ ι;
symbol bin_rec_def (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι → τ ι) (z : τ ι) :
  π (bin_rec fPls fMin fBit z =
     Vrec z (λ z2 g, bin_case fPls fMin (λ w b, fBit w b (fapply g w)) z2));

// ===========================================================================
// port-internal helpers: what Isabelle's datatype package generates and
// proves automatically for bin — closure of univ(bool) under the datatype
// operator, Knaster-Tarski unfolding, case/recursor equations, and the
// structural induction principle.
// ===========================================================================

// port-internal helper: the datatype operator of bin
private symbol bin_op : τ ι → τ ι ≔
  λ X, sum (sum (singleton empty) (singleton empty)) (Sigma X (λ _, bool_set));

// port-internal helper: naturals live in univ(A)  (i_subset_Vfrom at ω)
private opaque symbol nat_into_univ (n A : τ ι) :
  π (n ∈ omega) → π (n ∈ univ A) ≔
begin
  assume n A hn;
  rewrite univ_def;
  refine i_subset_Vfrom A omega n hn
end;

// port-internal helper: every finite stage is below univ(A)
private opaque symbol Vfrom_subset_univ (A i : τ ι) :
  π (i ∈ omega) → π (Vfrom A i ⊆ univ A) ≔
begin
  assume A i hi;
  rewrite univ_def;
  refine Vfrom_mono A A i omega (subset_refl A) (OrdmemD omega i hi Ord_omega)
end;

// port-internal helper: membership in univ(A) comes from some finite stage
private opaque symbol univ_stage (a A : τ ι) :
  π (a ∈ univ A) → π (Bex omega (λ i, a ∈ Vfrom A i)) ≔
begin
  assume a A ha;
  have heq : π (univ A = Union (RepFun omega (λ j, Vfrom A j)))
    { refine eq_trans (univ_def A) (Limit_Vfrom_eq A omega Limit_omega) };
  have ha' : π (a ∈ Union (RepFun omega (λ j, Vfrom A j)))
    { refine ind_eq (eq_sym heq) (λ w, a ∈ w) ha };
  refine ∃ₑ (UnionE a (RepFun omega (λ j, Vfrom A j)) ha') _;
  assume C hC;
  refine ∃ₑ (∧ₑ₁ (RepFun_iff C omega (λ j, Vfrom A j)) (∧ₑ₁ hC)) _;
  assume j hj;
  refine ∃ᵢ j (∧ᵢ (∧ₑ₁ hj) (ind_eq (eq_sym (∧ₑ₂ hj)) (λ w, a ∈ w) (∧ₑ₂ hC)))
end;

// port-internal helper: Kuratowski pairing climbs two stages
private opaque symbol Pair_in_Vfrom_h (a b A i : τ ι) :
  π (a ∈ Vfrom A i) → π (b ∈ Vfrom A i) →
  π (Pair a b ∈ Vfrom A (succ (succ i))) ≔
begin
  assume a b A i ha hb;
  have hsingle : π (singleton a ∈ Vfrom A (succ i))
    { rewrite Vfrom_succ;
      refine UnI2 (singleton a) A (Pow (Vfrom A i))
        (PowI (singleton a) (Vfrom A i) (singleton_subsetI a (Vfrom A i) ha)) };
  have hupair : π (Upair a b ∈ Vfrom A (succ i))
    { rewrite Vfrom_succ;
      refine UnI2 (Upair a b) A (Pow (Vfrom A i)) (PowI (Upair a b) (Vfrom A i) _);
      assume x hx;
      refine ∨ₑ (∧ₑ₁ (Upair_iff x a b) hx) _ _
      { assume hxa; rewrite hxa; refine ha }
      { assume hxb; rewrite hxb; refine hb } };
  have hsub : π (Upair (singleton a) (Upair a b) ⊆ Vfrom A (succ i))
    { assume x hx;
      refine ∨ₑ (∧ₑ₁ (Upair_iff x (singleton a) (Upair a b)) hx) _ _
      { assume h1; rewrite h1; refine hsingle }
      { assume h2; rewrite h2; refine hupair } };
  rewrite Pair_def;
  rewrite Vfrom_succ;
  refine UnI2 (Upair (singleton a) (Upair a b)) A (Pow (Vfrom A (succ i)))
    (PowI (Upair (singleton a) (Upair a b)) (Vfrom A (succ i)) hsub)
end;

// port-internal helper: univ(A) is closed under Pair
private opaque symbol Pair_in_univ_h (a b A : τ ι) :
  π (a ∈ univ A) → π (b ∈ univ A) → π (Pair a b ∈ univ A) ≔
begin
  assume a b A ha hb;
  refine ∃ₑ (univ_stage a A ha) _; assume i hi;
  refine ∃ₑ (univ_stage b A hb) _; assume j hj;
  have hak : π (a ∈ Vfrom A (Un i j))
    { refine Vfrom_mono A A i (Un i j) (subset_refl A) (Un_upper1 i j) a (∧ₑ₂ hi) };
  have hbk : π (b ∈ Vfrom A (Un i j))
    { refine Vfrom_mono A A j (Un i j) (subset_refl A) (Un_upper2 i j) b (∧ₑ₂ hj) };
  have hkw : π (Un i j ∈ omega) { refine Un_nat_type i j (∧ₑ₁ hi) (∧ₑ₁ hj) };
  refine Vfrom_subset_univ A (succ (succ (Un i j)))
    (succ_in_omega (succ (Un i j)) (succ_in_omega (Un i j) hkw))
    (Pair a b) (Pair_in_Vfrom_h a b A (Un i j) hak hbk)
end;

// port-internal helper: univ(A) is closed under Inl / Inr
private opaque symbol Inl_in_univ_h (a A : τ ι) :
  π (a ∈ univ A) → π (Inl a ∈ univ A) ≔
begin
  assume a A ha;
  rewrite Inl_def;
  refine Pair_in_univ_h empty a A (nat_into_univ empty A zero_in_omega) ha
end;

private opaque symbol Inr_in_univ_h (b A : τ ι) :
  π (b ∈ univ A) → π (Inr b ∈ univ A) ≔
begin
  assume b A hb;
  rewrite Inr_def;
  refine Pair_in_univ_h one b A
    (nat_into_univ one A (succ_in_omega empty zero_in_omega)) hb
end;

// port-internal helper: the bin operator is bounded-monotone on univ(bool)
private opaque symbol bin_bnd_mono : π (bnd_mono (univ bool_set) bin_op) ≔
begin
  refine bnd_monoI (univ bool_set) bin_op _ _
  { // bin_op(univ(bool)) ⊆ univ(bool)
    assume x hx;
    refine sumE x (sum (singleton empty) (singleton empty))
      (Sigma (univ bool_set) (λ _, bool_set)) (x ∈ univ bool_set) hx _ _
    { assume u hu heq;
      have hu_univ : π (u ∈ univ bool_set)
        { refine sumE u (singleton empty) (singleton empty) (u ∈ univ bool_set) hu _ _
          { assume v hv heqv;
            rewrite heqv;
            rewrite (∧ₑ₁ (singleton_iff v empty) hv);
            refine Inl_in_univ_h empty bool_set
              (nat_into_univ empty bool_set zero_in_omega) }
          { assume v hv heqv;
            rewrite heqv;
            rewrite (∧ₑ₁ (singleton_iff v empty) hv);
            refine Inr_in_univ_h empty bool_set
              (nat_into_univ empty bool_set zero_in_omega) } };
      rewrite heq;
      refine Inl_in_univ_h u bool_set hu_univ }
    { assume p hp heq;
      rewrite heq;
      refine ∃ₑ (SigmaE p (univ bool_set) (λ _, bool_set) hp) _;
      assume w hw;
      refine ∃ₑ (∧ₑ₂ hw) _;
      assume c hc;
      rewrite (∧ₑ₂ hc);
      have hc_univ : π (c ∈ univ bool_set)
        { have hbsub : π (bool_set ⊆ univ bool_set)
            { rewrite univ_def; refine A_subset_Vfrom bool_set omega };
          refine hbsub c (∧ₑ₁ hc) };
      refine Inr_in_univ_h (Pair w c) bool_set
        (Pair_in_univ_h w c bool_set (∧ₑ₁ hw) hc_univ) } }
  { // monotonicity
    assume W X hWX hXD x hx;
    refine sumE x (sum (singleton empty) (singleton empty))
      (Sigma W (λ _, bool_set)) (x ∈ bin_op X) hx _ _
    { assume u hu heq;
      rewrite heq;
      refine InlI u (sum (singleton empty) (singleton empty))
        (Sigma X (λ _, bool_set)) hu }
    { assume p hp heq;
      rewrite heq;
      refine ∃ₑ (SigmaE p W (λ _, bool_set) hp) _;
      assume w hw;
      refine ∃ₑ (∧ₑ₂ hw) _;
      assume c hc;
      rewrite (∧ₑ₂ hc);
      refine InrI (Pair w c) (sum (singleton empty) (singleton empty))
        (Sigma X (λ _, bool_set))
        (SigmaI w c X (λ _, bool_set) (hWX w (∧ₑ₁ hw)) (∧ₑ₁ hc)) } }
end;

// port-internal helper: Knaster-Tarski unfolding of bin
private opaque symbol bin_unfold :
  π (bin = sum (sum (singleton empty) (singleton empty))
               (Sigma bin (λ _, bool_set))) ≔
begin
  refine lfp_unfold (univ bool_set) bin_op bin_bnd_mono
end;

// ===========================================================================
// Basic freeness / typing
// ===========================================================================

opaque symbol bin_PlsI : π (Pls ∈ bin) ≔
begin
  rewrite bin_unfold;
  refine InlI (Inl empty) (sum (singleton empty) (singleton empty))
    (Sigma bin (λ _, bool_set))
    (InlI empty (singleton empty) (singleton empty) (singletonI empty))
end;

opaque symbol bin_MinI : π (Min ∈ bin) ≔
begin
  rewrite bin_unfold;
  refine InlI (Inr empty) (sum (singleton empty) (singleton empty))
    (Sigma bin (λ _, bool_set))
    (InrI empty (singleton empty) (singleton empty) (singletonI empty))
end;

opaque symbol bin_BitI (w b : τ ι) :
  π (w ∈ bin) → π (b ∈ bool_set) → π (Bit w b ∈ bin) ≔
begin
  assume w b hw hb;
  rewrite bin_unfold;
  refine InrI (Pair w b) (sum (singleton empty) (singleton empty))
    (Sigma bin (λ _, bool_set)) (SigmaI w b bin (λ _, bool_set) hw hb)
end;

// port-internal helper: structural induction over bin (bin.induct)
private opaque symbol bin_induct (P : τ ι → Prop) (z : τ ι) :
  π (z ∈ bin) → π (P Pls) → π (P Min) →
  (Π (w b : τ ι), π (w ∈ bin) → π (b ∈ bool_set) → π (P w) → π (P (Bit w b))) →
  π (P z) ≔
begin
  assume P z hz hPls hMin hstep;
  refine induct (univ bool_set) z bin_op P hz bin_bnd_mono _;
  assume x hx;
  refine sumE x (sum (singleton empty) (singleton empty))
    (Sigma (Collect bin P) (λ _, bool_set)) (P x) hx _ _
  { assume u hu heq;
    refine sumE u (singleton empty) (singleton empty) (P x) hu _ _
    { assume v hv heqv;
      rewrite heq; rewrite heqv;
      rewrite (∧ₑ₁ (singleton_iff v empty) hv);
      refine hPls }
    { assume v hv heqv;
      rewrite heq; rewrite heqv;
      rewrite (∧ₑ₁ (singleton_iff v empty) hv);
      refine hMin } }
  { assume p hp heq;
    refine ∃ₑ (SigmaE p (Collect bin P) (λ _, bool_set) hp) _;
    assume w hw;
    refine ∃ₑ (∧ₑ₂ hw) _;
    assume c hc;
    rewrite heq;
    rewrite (∧ₑ₂ hc);
    refine hstep w c (CollectD1 w bin P (∧ₑ₁ hw)) (∧ₑ₁ hc)
      (CollectD2 w bin P (∧ₑ₁ hw)) }
end;

// port-internal helper: case analysis on a ZF boolean
private opaque symbol boolE_h (b : τ ι) (P : Prop) :
  π (b ∈ bool_set) → (π (b = empty) → π P) → (π (b = one) → π P) → π P ≔
begin
  assume b P hb h0 h1;
  refine ∨ₑ (∧ₑ₁ (bool_iff b) hb) h0 h1
end;

// port-internal helpers: ⇔ plumbing
private opaque symbol iff_refl_h (P : Prop) : π (P ⇔ P) ≔
begin assume P; refine ∧ᵢ (λ h, h) (λ h, h) end;

private opaque symbol iff_sym_h (P Q : Prop) : π (P ⇔ Q) → π (Q ⇔ P) ≔
begin assume P Q h; refine ∧ᵢ (∧ₑ₂ h) (∧ₑ₁ h) end;

private opaque symbol iff_trans_h (P Q R : Prop) :
  π (P ⇔ Q) → π (Q ⇔ R) → π (P ⇔ R) ≔
begin
  assume P Q R h1 h2;
  refine ∧ᵢ (λ hp, ∧ₑ₁ h2 (∧ₑ₁ h1 hp)) (λ hr, ∧ₑ₂ h1 (∧ₑ₂ h2 hr))
end;

// port-internal helpers: case equations for bin_case
private opaque symbol bin_case_Pls (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι) :
  π (bin_case fPls fMin fBit Pls = fPls) ≔
begin
  assume fPls fMin fBit;
  refine eq_trans
    (case_Inl (case_sum (λ _, fPls) (λ _, fMin)) (split fBit) (Inl empty))
    (case_Inl (λ _, fPls) (λ _, fMin) empty)
end;

private opaque symbol bin_case_Min (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι) :
  π (bin_case fPls fMin fBit Min = fMin) ≔
begin
  assume fPls fMin fBit;
  refine eq_trans
    (case_Inl (case_sum (λ _, fPls) (λ _, fMin)) (split fBit) (Inr empty))
    (case_Inr (λ _, fPls) (λ _, fMin) empty)
end;

private opaque symbol bin_case_Bit (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι) (w b : τ ι) :
  π (bin_case fPls fMin fBit (Bit w b) = fBit w b) ≔
begin
  assume fPls fMin fBit w b;
  have h2 : π (split fBit (Pair w b) = fBit w b)
    { rewrite split_def; rewrite fst_conv; rewrite snd_conv; reflexivity };
  refine eq_trans
    (case_Inr (case_sum (λ _, fPls) (λ _, fMin)) (split fBit) (Pair w b)) h2
end;

// port-internal helpers: rank facts justifying the recursive call in bin_rec
private opaque symbol rank_pair1_h (a b : τ ι) :
  π (lt (rank a) (rank (Pair a b))) ≔
begin
  assume a b;
  have h1 : π (lt (rank a) (rank (singleton a)))
    { refine rank_lt a (singleton a) (singletonI a) };
  have hm : π (singleton a ∈ Pair a b)
    { rewrite Pair_def; refine UpairI1 (singleton a) (Upair a b) };
  refine lt_trans (rank a) (rank (singleton a)) (rank (Pair a b)) h1
    (rank_lt (singleton a) (Pair a b) hm)
end;

private opaque symbol rank_pair2_h (a b : τ ι) :
  π (lt (rank b) (rank (Pair a b))) ≔
begin
  assume a b;
  have h1 : π (lt (rank b) (rank (Upair a b)))
    { refine rank_lt b (Upair a b) (UpairI2 a b) };
  have hm : π (Upair a b ∈ Pair a b)
    { rewrite Pair_def; refine UpairI2 (singleton a) (Upair a b) };
  refine lt_trans (rank b) (rank (Upair a b)) (rank (Pair a b)) h1
    (rank_lt (Upair a b) (Pair a b) hm)
end;

private opaque symbol Bit_arg_in_Vset (w b : τ ι) :
  π (w ∈ Vset (rank (Bit w b))) ≔
begin
  assume w b;
  refine VsetI w (rank (Bit w b)) _;
  have h3 : π (lt (rank w) (rank (Pair one (Pair w b))))
    { refine lt_trans (rank w) (rank (Pair w b)) (rank (Pair one (Pair w b)))
        (rank_pair1_h w b) (rank_pair2_h one (Pair w b)) };
  refine ind_eq (Inr_def (Pair w b)) (λ z, lt (rank w) (rank z)) h3
end;

// port-internal helpers: the recursion equations of bin_rec
private opaque symbol bin_rec_Pls (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι → τ ι) :
  π (bin_rec fPls fMin fBit Pls = fPls) ≔
begin
  assume fPls fMin fBit;
  rewrite (bin_rec_def fPls fMin fBit Pls);
  rewrite (Vrec_eq Pls
    (λ z2 g, bin_case fPls fMin (λ w3 b3, fBit w3 b3 (fapply g w3)) z2));
  try simplify rule off;
  refine bin_case_Pls fPls fMin _
end;

private opaque symbol bin_rec_Min (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι → τ ι) :
  π (bin_rec fPls fMin fBit Min = fMin) ≔
begin
  assume fPls fMin fBit;
  rewrite (bin_rec_def fPls fMin fBit Min);
  rewrite (Vrec_eq Min
    (λ z2 g, bin_case fPls fMin (λ w3 b3, fBit w3 b3 (fapply g w3)) z2));
  try simplify rule off;
  refine bin_case_Min fPls fMin _
end;

private opaque symbol bin_rec_Bit (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι → τ ι)
  (w b : τ ι) :
  π (bin_rec fPls fMin fBit (Bit w b) = fBit w b (bin_rec fPls fMin fBit w)) ≔
begin
  assume fPls fMin fBit w b;
  rewrite (bin_rec_def fPls fMin fBit (Bit w b));
  rewrite (bin_rec_def fPls fMin fBit w);
  rewrite (Vrec_eq (Bit w b)
    (λ z2 g, bin_case fPls fMin (λ w3 b3, fBit w3 b3 (fapply g w3)) z2));
  try simplify rule off;
  refine eq_trans (bin_case_Bit fPls fMin _ w b) _;
  try simplify rule off;
  refine feq (fBit w b)
    (beta (Vset (rank (Bit w b)))
      (λ x, Vrec x
        (λ z2 g, bin_case fPls fMin (λ w3 b3, fBit w3 b3 (fapply g w3)) z2))
      w (Bit_arg_in_Vset w b))
end;

// ===========================================================================
// integ_of, NCons, bin_succ, bin_pred, bin_minus, bin_adder, bin_add, bin_mult
// ===========================================================================

symbol integ_of (w : τ ι) : τ ι ≔
  bin_rec (int_of empty) (zminus (int_of one))
    (λ w2 b r, zadd (int_of b) (zadd r r)) w;

// NCons adds a bit, suppressing leading 0s and 1s
symbol NCons (w b : τ ι) : τ ι ≔
  bin_rec (cond b (Bit Pls b) Pls) (cond b Min (Bit Min b))
    (λ w2 c r, Bit (Bit w2 c) b) w;

// successor. If a BIT, can change a 0 to a 1 without recursion.
symbol bin_succ (w : τ ι) : τ ι ≔
  bin_rec (Bit Pls one) Pls
    (λ w2 b r, cond b (Bit r empty) (NCons w2 one)) w;

// predecessor
symbol bin_pred (w : τ ι) : τ ι ≔
  bin_rec Min (Bit Min empty)
    (λ w2 b r, cond b (NCons w2 empty) (Bit r one)) w;

// unary negation
symbol bin_minus (w : τ ι) : τ ι ≔
  bin_rec Pls (Bit Pls one)
    (λ w2 b r, cond b (bin_pred (NCons r empty)) (Bit r empty)) w;

// sum: bin_adder(v) is the FUNCTION λw∈bin. v $+ w  (as bin values)
symbol bin_adder (v : τ ι) : τ ι ≔
  bin_rec (Lambda bin (λ w, w)) (Lambda bin (λ w, bin_pred w))
    (λ v2 x r, Lambda bin (λ w,
      bin_case (Bit v2 x) (bin_pred (Bit v2 x))
        (λ w2 y, NCons (fapply r (cond (and x y) (bin_succ w2) w2)) (xor x y))
        w))
    v;

constant symbol bin_add (v w : τ ι) : τ ι;
constant symbol bin_add_def (v w : τ ι) :
  π (bin_add v w = fapply (bin_adder v) w);

symbol bin_mult (v w : τ ι) : τ ι ≔
  bin_rec Pls (bin_minus w)
    (λ v2 b r, cond b (bin_add (NCons r empty) w) (NCons r empty)) v;

// ===========================================================================
// Numeral abbreviations (Isabelle syntax #0 #1 #2 #-1 #-2)
// ===========================================================================

symbol Int0 : τ ι ≔ integ_of Pls;
symbol Int1 : τ ι ≔ integ_of (Bit Pls one);
symbol Int2 : τ ι ≔ integ_of (Bit (Bit Pls one) empty);
symbol NegInt1 : τ ι ≔ integ_of Min;
symbol NegInt2 : τ ι ≔ integ_of (Bit Min empty);

// ===========================================================================
// port-internal helpers: the primrec equations of each bin_rec-defined
// function (instances of bin_rec_Pls/Min/Bit; Isabelle's primrec equations)
// ===========================================================================

private opaque symbol integ_of_Pls_eq : π (integ_of Pls = int_of empty) ≔
begin
  refine bin_rec_Pls (int_of empty) (zminus (int_of one))
    (λ w2 b r, zadd (int_of b) (zadd r r))
end;

private opaque symbol integ_of_Min_eq : π (integ_of Min = zminus (int_of one)) ≔
begin
  refine bin_rec_Min (int_of empty) (zminus (int_of one))
    (λ w2 b r, zadd (int_of b) (zadd r r))
end;

private opaque symbol integ_of_Bit_eq (w b : τ ι) :
  π (integ_of (Bit w b) = zadd (int_of b) (zadd (integ_of w) (integ_of w))) ≔
begin
  assume w b;
  refine bin_rec_Bit (int_of empty) (zminus (int_of one))
    (λ w2 b2 r, zadd (int_of b2) (zadd r r)) w b
end;

private opaque symbol NCons_Pls_eq (b : τ ι) :
  π (NCons Pls b = cond b (Bit Pls b) Pls) ≔
begin
  assume b;
  refine bin_rec_Pls (cond b (Bit Pls b) Pls) (cond b Min (Bit Min b))
    (λ w2 c r, Bit (Bit w2 c) b)
end;

private opaque symbol NCons_Min_eq (b : τ ι) :
  π (NCons Min b = cond b Min (Bit Min b)) ≔
begin
  assume b;
  refine bin_rec_Min (cond b (Bit Pls b) Pls) (cond b Min (Bit Min b))
    (λ w2 c r, Bit (Bit w2 c) b)
end;

private opaque symbol bin_succ_Pls_eq : π (bin_succ Pls = Bit Pls one) ≔
begin
  refine bin_rec_Pls (Bit Pls one) Pls
    (λ w2 b r, cond b (Bit r empty) (NCons w2 one))
end;

private opaque symbol bin_succ_Min_eq : π (bin_succ Min = Pls) ≔
begin
  refine bin_rec_Min (Bit Pls one) Pls
    (λ w2 b r, cond b (Bit r empty) (NCons w2 one))
end;

private opaque symbol bin_succ_Bit_eq (w b : τ ι) :
  π (bin_succ (Bit w b) = cond b (Bit (bin_succ w) empty) (NCons w one)) ≔
begin
  assume w b;
  refine bin_rec_Bit (Bit Pls one) Pls
    (λ w2 b2 r, cond b2 (Bit r empty) (NCons w2 one)) w b
end;

private opaque symbol bin_pred_Pls_eq : π (bin_pred Pls = Min) ≔
begin
  refine bin_rec_Pls Min (Bit Min empty)
    (λ w2 b r, cond b (NCons w2 empty) (Bit r one))
end;

private opaque symbol bin_pred_Min_eq : π (bin_pred Min = Bit Min empty) ≔
begin
  refine bin_rec_Min Min (Bit Min empty)
    (λ w2 b r, cond b (NCons w2 empty) (Bit r one))
end;

private opaque symbol bin_pred_Bit_eq (w b : τ ι) :
  π (bin_pred (Bit w b) = cond b (NCons w empty) (Bit (bin_pred w) one)) ≔
begin
  assume w b;
  refine bin_rec_Bit Min (Bit Min empty)
    (λ w2 b2 r, cond b2 (NCons w2 empty) (Bit r one)) w b
end;

private opaque symbol bin_minus_Pls_eq : π (bin_minus Pls = Pls) ≔
begin
  refine bin_rec_Pls Pls (Bit Pls one)
    (λ w2 b r, cond b (bin_pred (NCons r empty)) (Bit r empty))
end;

private opaque symbol bin_minus_Min_eq : π (bin_minus Min = Bit Pls one) ≔
begin
  refine bin_rec_Min Pls (Bit Pls one)
    (λ w2 b r, cond b (bin_pred (NCons r empty)) (Bit r empty))
end;

private opaque symbol bin_minus_Bit_eq (w b : τ ι) :
  π (bin_minus (Bit w b) =
     cond b (bin_pred (NCons (bin_minus w) empty)) (Bit (bin_minus w) empty)) ≔
begin
  assume w b;
  refine bin_rec_Bit Pls (Bit Pls one)
    (λ w2 b2 r, cond b2 (bin_pred (NCons r empty)) (Bit r empty)) w b
end;

private opaque symbol bin_adder_Pls_eq : π (bin_adder Pls = Lambda bin (λ w, w)) ≔
begin
  refine bin_rec_Pls (Lambda bin (λ w, w)) (Lambda bin (λ w, bin_pred w))
    (λ v2 x r, Lambda bin (λ w,
      bin_case (Bit v2 x) (bin_pred (Bit v2 x))
        (λ w2 y, NCons (fapply r (cond (and x y) (bin_succ w2) w2)) (xor x y))
        w))
end;

private opaque symbol bin_adder_Min_eq :
  π (bin_adder Min = Lambda bin (λ w, bin_pred w)) ≔
begin
  refine bin_rec_Min (Lambda bin (λ w, w)) (Lambda bin (λ w, bin_pred w))
    (λ v2 x r, Lambda bin (λ w,
      bin_case (Bit v2 x) (bin_pred (Bit v2 x))
        (λ w2 y, NCons (fapply r (cond (and x y) (bin_succ w2) w2)) (xor x y))
        w))
end;

private opaque symbol bin_adder_Bit_eq (v x : τ ι) :
  π (bin_adder (Bit v x) = Lambda bin (λ w,
      bin_case (Bit v x) (bin_pred (Bit v x))
        (λ w2 y, NCons (fapply (bin_adder v) (cond (and x y) (bin_succ w2) w2))
                 (xor x y))
        w)) ≔
begin
  assume v x;
  refine bin_rec_Bit (Lambda bin (λ w, w)) (Lambda bin (λ w, bin_pred w))
    (λ v2 x2 r, Lambda bin (λ w,
      bin_case (Bit v2 x2) (bin_pred (Bit v2 x2))
        (λ w2 y, NCons (fapply r (cond (and x2 y) (bin_succ w2) w2)) (xor x2 y))
        w)) v x
end;

private opaque symbol bin_mult_Pls_eq (w : τ ι) : π (bin_mult Pls w = Pls) ≔
begin
  assume w;
  refine bin_rec_Pls Pls (bin_minus w)
    (λ v2 b r, cond b (bin_add (NCons r empty) w) (NCons r empty))
end;

private opaque symbol bin_mult_Min_eq (w : τ ι) : π (bin_mult Min w = bin_minus w) ≔
begin
  assume w;
  refine bin_rec_Min Pls (bin_minus w)
    (λ v2 b r, cond b (bin_add (NCons r empty) w) (NCons r empty))
end;

private opaque symbol bin_mult_Bit_eq (v b w : τ ι) :
  π (bin_mult (Bit v b) w =
     cond b (bin_add (NCons (bin_mult v w) empty) w) (NCons (bin_mult v w) empty)) ≔
begin
  assume v b w;
  refine bin_rec_Bit Pls (bin_minus w)
    (λ v2 b2 r, cond b2 (bin_add (NCons r empty) w) (NCons r empty)) v b
end;

// port-internal helpers: numeral values
private opaque symbol Int0_eq : π (Int0 = int_of empty) ≔
begin refine integ_of_Pls_eq end;

private opaque symbol NegInt1_eq : π (NegInt1 = zminus (int_of one)) ≔
begin refine integ_of_Min_eq end;

private opaque symbol Int1_eq : π (Int1 = int_of one) ≔
begin
  have h1 : π (Int1 = zadd (int_of one) (zadd (integ_of Pls) (integ_of Pls)))
    { refine integ_of_Bit_eq Pls one };
  rewrite h1;
  rewrite integ_of_Pls_eq;
  rewrite (zadd_int0 (int_of empty) (int_of_type empty));
  refine zadd_int0_right (int_of one) (int_of_type one)
end;

// port-internal helper: AC interchange law for zadd
private opaque symbol zadd_interchange (a b c d : τ ι) :
  π (zadd (zadd a b) (zadd c d) = zadd (zadd a c) (zadd b d)) ≔
begin
  assume a b c d;
  rewrite zadd_assoc;
  rewrite zadd_assoc;
  rewrite (zadd_left_commute b c d);
  reflexivity
end;

// ===========================================================================
// NCons_simps (`declare bin.intros [simp,TC]`, plus the immediate NCons
// simplification lemmas)
// ===========================================================================

opaque symbol NCons_Pls_0 : π (NCons Pls empty = Pls) ≔
begin
  refine eq_trans (NCons_Pls_eq empty) (cond_0 (Bit Pls empty) Pls)
end;

opaque symbol NCons_Pls_1 : π (NCons Pls one = Bit Pls one) ≔
begin
  refine eq_trans (NCons_Pls_eq one) (cond_1 (Bit Pls one) Pls)
end;

opaque symbol NCons_Min_0 : π (NCons Min empty = Bit Min empty) ≔
begin
  refine eq_trans (NCons_Min_eq empty) (cond_0 Min (Bit Min empty))
end;

opaque symbol NCons_Min_1 : π (NCons Min one = Min) ≔
begin
  refine eq_trans (NCons_Min_eq one) (cond_1 Min (Bit Min one))
end;

opaque symbol NCons_BIT (w x b : τ ι) : π (NCons (Bit w x) b = Bit (Bit w x) b) ≔
begin
  assume w x b;
  refine bin_rec_Bit (cond b (Bit Pls b) Pls) (cond b Min (Bit Min b))
    (λ w2 c r, Bit (Bit w2 c) b) w x
end;

// port-internal helpers: boolean operator computation rules
private opaque symbol and_0 (y : τ ι) : π (and empty y = empty) ≔
begin assume y; refine cond_0 y empty end;

private opaque symbol and_1 (y : τ ι) : π (and one y = y) ≔
begin assume y; refine cond_1 y empty end;

private opaque symbol xor_0 (y : τ ι) : π (xor empty y = y) ≔
begin assume y; refine cond_0 (not y) y end;

private opaque symbol xor_1_0 : π (xor one empty = one) ≔
begin refine eq_trans (cond_1 (not empty) empty) (cond_0 empty one) end;

private opaque symbol xor_1_1 : π (xor one one = empty) ≔
begin refine eq_trans (cond_1 (not one) one) (cond_1 empty one) end;

// port-internal helpers: bin_add computation rules (bin_add_def + bin_adder
// equations + β; the corresponding public lemmas are stated further below,
// after this Type-checking section, exactly as in Bin.thy)
private opaque symbol bin_add_Pls_h (w : τ ι) :
  π (w ∈ bin) → π (bin_add Pls w = w) ≔
begin
  assume w hw;
  rewrite bin_add_def;
  rewrite bin_adder_Pls_eq;
  refine beta bin (λ u, u) w hw
end;

private opaque symbol bin_add_Min_h (w : τ ι) :
  π (w ∈ bin) → π (bin_add Min w = bin_pred w) ≔
begin
  assume w hw;
  rewrite bin_add_def;
  rewrite bin_adder_Min_eq;
  refine beta bin (λ u, bin_pred u) w hw
end;

private opaque symbol bin_add_BIT_Pls_h (v x : τ ι) :
  π (bin_add (Bit v x) Pls = Bit v x) ≔
begin
  assume v x;
  rewrite bin_add_def;
  rewrite (bin_adder_Bit_eq v x);
  refine eq_trans
    (beta bin (λ w, bin_case (Bit v x) (bin_pred (Bit v x))
      (λ w2 y, NCons (fapply (bin_adder v) (cond (and x y) (bin_succ w2) w2))
               (xor x y)) w)
      Pls bin_PlsI) _;
  try simplify rule off;
  refine bin_case_Pls (Bit v x) (bin_pred (Bit v x)) _
end;

private opaque symbol bin_add_BIT_Min_h (v x : τ ι) :
  π (bin_add (Bit v x) Min = bin_pred (Bit v x)) ≔
begin
  assume v x;
  rewrite bin_add_def;
  rewrite (bin_adder_Bit_eq v x);
  refine eq_trans
    (beta bin (λ w, bin_case (Bit v x) (bin_pred (Bit v x))
      (λ w2 y, NCons (fapply (bin_adder v) (cond (and x y) (bin_succ w2) w2))
               (xor x y)) w)
      Min bin_MinI) _;
  try simplify rule off;
  refine bin_case_Min (Bit v x) (bin_pred (Bit v x)) _
end;

private opaque symbol bin_add_BIT_BIT_h (v x w y : τ ι) :
  π (w ∈ bin) → π (y ∈ bool_set) →
  π (bin_add (Bit v x) (Bit w y) =
     NCons (bin_add v (cond (and x y) (bin_succ w) w)) (xor x y)) ≔
begin
  assume v x w y hw hy;
  rewrite (bin_add_def (Bit v x) (Bit w y));
  rewrite (bin_add_def v (cond (and x y) (bin_succ w) w));
  rewrite (bin_adder_Bit_eq v x);
  refine eq_trans
    (beta bin (λ w0, bin_case (Bit v x) (bin_pred (Bit v x))
      (λ w2 y2, NCons (fapply (bin_adder v) (cond (and x y2) (bin_succ w2) w2))
                (xor x y2)) w0)
      (Bit w y) (bin_BitI w y hw hy)) _;
  try simplify rule off;
  refine bin_case_Bit (Bit v x) (bin_pred (Bit v x)) _ w y
end;

// ===========================================================================
// Type checking
// ===========================================================================

opaque symbol integ_of_type (w : τ ι) : π (w ∈ bin) → π (integ_of w ∈ int) ≔
begin
  assume w hw;
  refine bin_induct (λ u, integ_of u ∈ int) w hw _ _ _
  { try simplify rule off; rewrite integ_of_Pls_eq; refine int_of_type empty }
  { try simplify rule off; rewrite integ_of_Min_eq; refine zminus_type (int_of one) }
  { assume v b hv hb hIH;
    try simplify rule off;
    rewrite (integ_of_Bit_eq v b);
    refine zadd_type (int_of b) (zadd (integ_of v) (integ_of v)) }
end;

opaque symbol NCons_type (w b : τ ι) :
  π (w ∈ bin) → π (b ∈ bool_set) → π (NCons w b ∈ bin) ≔
begin
  assume w b hw hb;
  refine bin_induct (λ u, NCons u b ∈ bin) w hw _ _ _
  { try simplify rule off;
    refine boolE_h b (NCons Pls b ∈ bin) hb _ _
    { assume h0; rewrite h0; rewrite NCons_Pls_0; refine bin_PlsI }
    { assume h1; rewrite h1; rewrite NCons_Pls_1;
      refine bin_BitI Pls one bin_PlsI one_in_bool } }
  { try simplify rule off;
    refine boolE_h b (NCons Min b ∈ bin) hb _ _
    { assume h0; rewrite h0; rewrite NCons_Min_0;
      refine bin_BitI Min empty bin_MinI zero_in_bool }
    { assume h1; rewrite h1; rewrite NCons_Min_1; refine bin_MinI } }
  { assume v c hv hc hIH;
    try simplify rule off;
    rewrite (NCons_BIT v c b);
    refine bin_BitI (Bit v c) b (bin_BitI v c hv hc) hb }
end;

opaque symbol bin_succ_type (w : τ ι) : π (w ∈ bin) → π (bin_succ w ∈ bin) ≔
begin
  assume w hw;
  refine bin_induct (λ u, bin_succ u ∈ bin) w hw _ _ _
  { try simplify rule off; rewrite bin_succ_Pls_eq;
    refine bin_BitI Pls one bin_PlsI one_in_bool }
  { try simplify rule off; rewrite bin_succ_Min_eq; refine bin_PlsI }
  { assume v c hv hc hIH;
    try simplify rule off;
    rewrite (bin_succ_Bit_eq v c);
    refine boolE_h c _ hc _ _
    { assume h0; rewrite h0; rewrite (cond_0 (Bit (bin_succ v) empty) (NCons v one));
      refine NCons_type v one hv one_in_bool }
    { assume h1; rewrite h1; rewrite (cond_1 (Bit (bin_succ v) empty) (NCons v one));
      refine bin_BitI (bin_succ v) empty hIH zero_in_bool } }
end;

opaque symbol bin_pred_type (w : τ ι) : π (w ∈ bin) → π (bin_pred w ∈ bin) ≔
begin
  assume w hw;
  refine bin_induct (λ u, bin_pred u ∈ bin) w hw _ _ _
  { try simplify rule off; rewrite bin_pred_Pls_eq; refine bin_MinI }
  { try simplify rule off; rewrite bin_pred_Min_eq;
    refine bin_BitI Min empty bin_MinI zero_in_bool }
  { assume v c hv hc hIH;
    try simplify rule off;
    rewrite (bin_pred_Bit_eq v c);
    refine boolE_h c _ hc _ _
    { assume h0; rewrite h0; rewrite (cond_0 (NCons v empty) (Bit (bin_pred v) one));
      refine bin_BitI (bin_pred v) one hIH one_in_bool }
    { assume h1; rewrite h1; rewrite (cond_1 (NCons v empty) (Bit (bin_pred v) one));
      refine NCons_type v empty hv zero_in_bool } }
end;

opaque symbol bin_minus_type (w : τ ι) : π (w ∈ bin) → π (bin_minus w ∈ bin) ≔
begin
  assume w hw;
  refine bin_induct (λ u, bin_minus u ∈ bin) w hw _ _ _
  { try simplify rule off; rewrite bin_minus_Pls_eq; refine bin_PlsI }
  { try simplify rule off; rewrite bin_minus_Min_eq;
    refine bin_BitI Pls one bin_PlsI one_in_bool }
  { assume v c hv hc hIH;
    try simplify rule off;
    rewrite (bin_minus_Bit_eq v c);
    refine boolE_h c _ hc _ _
    { assume h0; rewrite h0;
      rewrite (cond_0 (bin_pred (NCons (bin_minus v) empty)) (Bit (bin_minus v) empty));
      refine bin_BitI (bin_minus v) empty hIH zero_in_bool }
    { assume h1; rewrite h1;
      rewrite (cond_1 (bin_pred (NCons (bin_minus v) empty)) (Bit (bin_minus v) empty));
      refine bin_pred_type (NCons (bin_minus v) empty)
        (NCons_type (bin_minus v) empty hIH zero_in_bool) } }
end;

// This proof is complicated by the mutual recursion
opaque symbol bin_add_type (v : τ ι) :
  π (v ∈ bin) → π (Ball bin (λ w, bin_add v w ∈ bin)) ≔
begin
  assume v hv;
  refine bin_induct (λ u, Ball bin (λ w, bin_add u w ∈ bin)) v hv _ _ _
  { try simplify rule off; assume w hw; rewrite (bin_add_Pls_h w hw); refine hw }
  { try simplify rule off; assume w hw; rewrite (bin_add_Min_h w hw);
    refine bin_pred_type w hw }
  { assume u x hu hx hIH;
    try simplify rule off;
    assume w0 hw0;
    refine bin_induct (λ w, bin_add (Bit u x) w ∈ bin) w0 hw0 _ _ _
    { try simplify rule off; rewrite (bin_add_BIT_Pls_h u x);
      refine bin_BitI u x hu hx }
    { try simplify rule off; rewrite (bin_add_BIT_Min_h u x);
      refine bin_pred_type (Bit u x) (bin_BitI u x hu hx) }
    { assume w y hw hy hIH2;
      try simplify rule off;
      rewrite (bin_add_BIT_BIT_h u x w y hw hy);
      have hc : π (cond (and x y) (bin_succ w) w ∈ bin)
        { refine boolE_h x _ hx _ _
          { assume h0; rewrite h0; rewrite (and_0 y);
            rewrite (cond_0 (bin_succ w) w); refine hw }
          { assume h1; rewrite h1; rewrite (and_1 y);
            refine boolE_h y _ hy _ _
            { assume hy0; rewrite hy0; rewrite (cond_0 (bin_succ w) w); refine hw }
            { assume hy1; rewrite hy1; rewrite (cond_1 (bin_succ w) w);
              refine bin_succ_type w hw } } };
      have hxor : π (xor x y ∈ bool_set)
        { refine boolE_h x _ hx _ _
          { assume h0; rewrite h0; rewrite (xor_0 y); refine hy }
          { assume h1; rewrite h1;
            refine boolE_h y _ hy _ _
            { assume hy0; rewrite hy0; rewrite xor_1_0; refine one_in_bool }
            { assume hy1; rewrite hy1; rewrite xor_1_1; refine zero_in_bool } } };
      refine NCons_type (bin_add u (cond (and x y) (bin_succ w) w)) (xor x y)
        (hIH (cond (and x y) (bin_succ w) w) hc) hxor } }
end;

opaque symbol bin_mult_type (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) → π (bin_mult v w ∈ bin) ≔
begin
  assume v w hv hw;
  refine bin_induct (λ u, bin_mult u w ∈ bin) v hv _ _ _
  { try simplify rule off; rewrite (bin_mult_Pls_eq w); refine bin_PlsI }
  { try simplify rule off; rewrite (bin_mult_Min_eq w); refine bin_minus_type w hw }
  { assume u b hu hb hIH;
    try simplify rule off;
    rewrite (bin_mult_Bit_eq u b w);
    refine boolE_h b _ hb _ _
    { assume h0; rewrite h0;
      rewrite (cond_0 (bin_add (NCons (bin_mult u w) empty) w)
                      (NCons (bin_mult u w) empty));
      refine NCons_type (bin_mult u w) empty hIH zero_in_bool }
    { assume h1; rewrite h1;
      rewrite (cond_1 (bin_add (NCons (bin_mult u w) empty) w)
                      (NCons (bin_mult u w) empty));
      refine bin_add_type (NCons (bin_mult u w) empty)
        (NCons_type (bin_mult u w) empty hIH zero_in_bool) w hw } }
end;

// ===========================================================================
// The Carry and Borrow Functions: bin_succ and bin_pred
// ===========================================================================

// NCons preserves the integer value of its argument
opaque symbol integ_of_NCons (w b : τ ι) :
  π (w ∈ bin) → π (b ∈ bool_set) → π (integ_of (NCons w b) = integ_of (Bit w b)) ≔
begin
  assume w b hw hb;
  refine bin_induct (λ u, integ_of (NCons u b) = integ_of (Bit u b)) w hw _ _ _
  { try simplify rule off;
    refine boolE_h b _ hb _ _
    { assume h0; rewrite h0; rewrite NCons_Pls_0;
      rewrite (integ_of_Bit_eq Pls empty);
      rewrite integ_of_Pls_eq;
      rewrite (zadd_int0 (int_of empty) (int_of_type empty));
      rewrite (zadd_int0 (int_of empty) (int_of_type empty));
      reflexivity }
    { assume h1; rewrite h1; rewrite NCons_Pls_1; reflexivity } }
  { try simplify rule off;
    refine boolE_h b _ hb _ _
    { assume h0; rewrite h0; rewrite NCons_Min_0; reflexivity }
    { assume h1; rewrite h1; rewrite NCons_Min_1;
      rewrite (integ_of_Bit_eq Min one);
      rewrite integ_of_Min_eq;
      rewrite left (zadd_assoc (int_of one) (zminus (int_of one)) (zminus (int_of one)));
      rewrite (zadd_zminus_inverse (int_of one));
      rewrite (zadd_int0 (zminus (int_of one)) (zminus_type (int_of one)));
      reflexivity } }
  { assume v c hv hc hIH;
    try simplify rule off;
    rewrite (NCons_BIT v c b);
    reflexivity }
end;

opaque symbol integ_of_succ (w : τ ι) :
  π (w ∈ bin) → π (integ_of (bin_succ w) = zadd (int_of one) (integ_of w)) ≔
begin
  assume w hw;
  refine bin_induct (λ u, integ_of (bin_succ u) = zadd (int_of one) (integ_of u))
    w hw _ _ _
  { try simplify rule off;
    rewrite bin_succ_Pls_eq;
    rewrite (integ_of_Bit_eq Pls one);
    rewrite integ_of_Pls_eq;
    rewrite (zadd_int0 (int_of empty) (int_of_type empty));
    reflexivity }
  { try simplify rule off;
    rewrite bin_succ_Min_eq;
    rewrite integ_of_Pls_eq;
    rewrite integ_of_Min_eq;
    rewrite (zadd_zminus_inverse (int_of one));
    reflexivity }
  { assume v c hv hc hIH;
    try simplify rule off;
    rewrite (bin_succ_Bit_eq v c);
    refine boolE_h c _ hc _ _
    { assume h0; rewrite h0;
      rewrite (cond_0 (Bit (bin_succ v) empty) (NCons v one));
      rewrite (integ_of_NCons v one hv one_in_bool);
      rewrite (integ_of_Bit_eq v one);
      rewrite (integ_of_Bit_eq v empty);
      rewrite (zadd_int0 (zadd (integ_of v) (integ_of v))
                         (zadd_type (integ_of v) (integ_of v)));
      reflexivity }
    { assume h1; rewrite h1;
      rewrite (cond_1 (Bit (bin_succ v) empty) (NCons v one));
      rewrite (integ_of_Bit_eq (bin_succ v) empty);
      rewrite hIH;
      rewrite (integ_of_Bit_eq v one);
      rewrite (zadd_int0
        (zadd (zadd (int_of one) (integ_of v)) (zadd (int_of one) (integ_of v)))
        (zadd_type (zadd (int_of one) (integ_of v)) (zadd (int_of one) (integ_of v))));
      rewrite (zadd_interchange (int_of one) (integ_of v) (int_of one) (integ_of v));
      rewrite zadd_assoc;
      reflexivity } }
end;

opaque symbol integ_of_pred (w : τ ι) :
  π (w ∈ bin) → π (integ_of (bin_pred w) = zadd (zminus (int_of one)) (integ_of w)) ≔
begin
  assume w hw;
  refine bin_induct
    (λ u, integ_of (bin_pred u) = zadd (zminus (int_of one)) (integ_of u))
    w hw _ _ _
  { try simplify rule off;
    rewrite bin_pred_Pls_eq;
    rewrite integ_of_Min_eq;
    rewrite integ_of_Pls_eq;
    rewrite (zadd_int0_right (zminus (int_of one)) (zminus_type (int_of one)));
    reflexivity }
  { try simplify rule off;
    rewrite bin_pred_Min_eq;
    rewrite (integ_of_Bit_eq Min empty);
    rewrite integ_of_Min_eq;
    rewrite (zadd_int0 (zadd (zminus (int_of one)) (zminus (int_of one)))
                       (zadd_type (zminus (int_of one)) (zminus (int_of one))));
    reflexivity }
  { assume v c hv hc hIH;
    try simplify rule off;
    rewrite (bin_pred_Bit_eq v c);
    refine boolE_h c _ hc _ _
    { assume h0; rewrite h0;
      rewrite (cond_0 (NCons v empty) (Bit (bin_pred v) one));
      rewrite (integ_of_Bit_eq (bin_pred v) one);
      rewrite hIH;
      rewrite (integ_of_Bit_eq v empty);
      rewrite (zadd_int0 (zadd (integ_of v) (integ_of v))
                         (zadd_type (integ_of v) (integ_of v)));
      rewrite (zadd_interchange (zminus (int_of one)) (integ_of v)
                                (zminus (int_of one)) (integ_of v));
      rewrite left (zadd_assoc (int_of one)
        (zadd (zminus (int_of one)) (zminus (int_of one)))
        (zadd (integ_of v) (integ_of v)));
      rewrite left (zadd_assoc (int_of one) (zminus (int_of one)) (zminus (int_of one)));
      rewrite (zadd_zminus_inverse (int_of one));
      rewrite (zadd_int0 (zminus (int_of one)) (zminus_type (int_of one)));
      reflexivity }
    { assume h1; rewrite h1;
      rewrite (cond_1 (NCons v empty) (Bit (bin_pred v) one));
      rewrite (integ_of_NCons v empty hv zero_in_bool);
      rewrite (integ_of_Bit_eq v empty);
      rewrite (integ_of_Bit_eq v one);
      rewrite (zadd_int0 (zadd (integ_of v) (integ_of v))
                         (zadd_type (integ_of v) (integ_of v)));
      rewrite left (zadd_assoc (zminus (int_of one)) (int_of one)
                               (zadd (integ_of v) (integ_of v)));
      rewrite (zadd_zminus_inverse2 (int_of one));
      rewrite (zadd_int0 (zadd (integ_of v) (integ_of v))
                         (zadd_type (integ_of v) (integ_of v)));
      reflexivity } }
end;

// ===========================================================================
// bin_minus: Unary Negation of Binary Integers
// ===========================================================================

opaque symbol integ_of_minus (w : τ ι) :
  π (w ∈ bin) → π (integ_of (bin_minus w) = zminus (integ_of w)) ≔
begin
  assume w hw;
  refine bin_induct (λ u, integ_of (bin_minus u) = zminus (integ_of u)) w hw _ _ _
  { try simplify rule off;
    rewrite bin_minus_Pls_eq;
    rewrite integ_of_Pls_eq;
    rewrite zminus_int0;
    reflexivity }
  { try simplify rule off;
    rewrite bin_minus_Min_eq;
    rewrite (integ_of_Bit_eq Pls one);
    rewrite integ_of_Pls_eq;
    rewrite integ_of_Min_eq;
    rewrite (zadd_int0 (int_of empty) (int_of_type empty));
    rewrite (zadd_int0_right (int_of one) (int_of_type one));
    rewrite (zminus_zminus (int_of one) (int_of_type one));
    reflexivity }
  { assume v c hv hc hIH;
    try simplify rule off;
    rewrite (bin_minus_Bit_eq v c);
    refine boolE_h c _ hc _ _
    { assume h0; rewrite h0;
      rewrite (cond_0 (bin_pred (NCons (bin_minus v) empty)) (Bit (bin_minus v) empty));
      rewrite (integ_of_Bit_eq (bin_minus v) empty);
      rewrite hIH;
      rewrite (integ_of_Bit_eq v empty);
      rewrite (zadd_int0 (zadd (zminus (integ_of v)) (zminus (integ_of v)))
                         (zadd_type (zminus (integ_of v)) (zminus (integ_of v))));
      rewrite (zadd_int0 (zadd (integ_of v) (integ_of v))
                         (zadd_type (integ_of v) (integ_of v)));
      rewrite (zminus_zadd_distrib (integ_of v) (integ_of v));
      reflexivity }
    { assume h1; rewrite h1;
      rewrite (cond_1 (bin_pred (NCons (bin_minus v) empty)) (Bit (bin_minus v) empty));
      rewrite (integ_of_pred (NCons (bin_minus v) empty)
        (NCons_type (bin_minus v) empty (bin_minus_type v hv) zero_in_bool));
      rewrite (integ_of_NCons (bin_minus v) empty (bin_minus_type v hv) zero_in_bool);
      rewrite (integ_of_Bit_eq (bin_minus v) empty);
      rewrite hIH;
      rewrite (integ_of_Bit_eq v one);
      rewrite (zadd_int0 (zadd (zminus (integ_of v)) (zminus (integ_of v)))
                         (zadd_type (zminus (integ_of v)) (zminus (integ_of v))));
      rewrite (zminus_zadd_distrib (int_of one) (zadd (integ_of v) (integ_of v)));
      rewrite (zminus_zadd_distrib (integ_of v) (integ_of v));
      reflexivity } }
end;

// ===========================================================================
// bin_add: Binary Addition
// ===========================================================================

opaque symbol bin_add_Pls (w : τ ι) : π (w ∈ bin) → π (bin_add Pls w = w) ≔
begin assume w hw; refine bin_add_Pls_h w hw end;

opaque symbol bin_add_Pls_right (w : τ ι) : π (w ∈ bin) → π (bin_add w Pls = w) ≔
begin
  assume w hw;
  refine bin_induct (λ u, bin_add u Pls = u) w hw _ _ _
  { try simplify rule off; refine bin_add_Pls_h Pls bin_PlsI }
  { try simplify rule off;
    refine eq_trans (bin_add_Min_h Pls bin_PlsI) bin_pred_Pls_eq }
  { assume v c hv hc hIH;
    try simplify rule off;
    refine bin_add_BIT_Pls_h v c }
end;

opaque symbol bin_add_Min (w : τ ι) : π (w ∈ bin) → π (bin_add Min w = bin_pred w) ≔
begin assume w hw; refine bin_add_Min_h w hw end;

opaque symbol bin_add_Min_right (w : τ ι) :
  π (w ∈ bin) → π (bin_add w Min = bin_pred w) ≔
begin
  assume w hw;
  refine bin_induct (λ u, bin_add u Min = bin_pred u) w hw _ _ _
  { try simplify rule off;
    refine eq_trans (bin_add_Pls_h Min bin_MinI) (eq_sym bin_pred_Pls_eq) }
  { try simplify rule off; refine bin_add_Min_h Min bin_MinI }
  { assume v c hv hc hIH;
    try simplify rule off;
    refine bin_add_BIT_Min_h v c }
end;

opaque symbol bin_add_BIT_Pls (v x : τ ι) : π (bin_add (Bit v x) Pls = Bit v x) ≔
begin assume v x; refine bin_add_BIT_Pls_h v x end;

opaque symbol bin_add_BIT_Min (v x : τ ι) :
  π (bin_add (Bit v x) Min = bin_pred (Bit v x)) ≔
begin assume v x; refine bin_add_BIT_Min_h v x end;

opaque symbol bin_add_BIT_BIT (v x w y : τ ι) :
  π (w ∈ bin) → π (y ∈ bool_set) →
  π (bin_add (Bit v x) (Bit w y) =
     NCons (bin_add v (cond (and x y) (bin_succ w) w)) (xor x y)) ≔
begin assume v x w y hw hy; refine bin_add_BIT_BIT_h v x w y hw hy end;

opaque symbol integ_of_add (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (integ_of (bin_add v w) = zadd (integ_of v) (integ_of w)) ≔
begin
  assume v w hv hw;
  have hall : π (Ball bin (λ u2, integ_of (bin_add v u2) =
                                 zadd (integ_of v) (integ_of u2)))
  { refine bin_induct
      (λ u, Ball bin (λ u2, integ_of (bin_add u u2) =
                            zadd (integ_of u) (integ_of u2))) v hv _ _ _
    { try simplify rule off;
      assume u2 hu2;
      rewrite (bin_add_Pls_h u2 hu2);
      rewrite integ_of_Pls_eq;
      rewrite (zadd_int0 (integ_of u2) (integ_of_type u2 hu2));
      reflexivity }
    { try simplify rule off;
      assume u2 hu2;
      rewrite (bin_add_Min_h u2 hu2);
      rewrite (integ_of_pred u2 hu2);
      rewrite integ_of_Min_eq;
      reflexivity }
    { assume u x hu hx hIH;
      try simplify rule off;
      assume w0 hw0;
      refine bin_induct
        (λ u2, integ_of (bin_add (Bit u x) u2) =
               zadd (integ_of (Bit u x)) (integ_of u2)) w0 hw0 _ _ _
      { try simplify rule off;
        rewrite (bin_add_BIT_Pls_h u x);
        rewrite integ_of_Pls_eq;
        rewrite (zadd_int0_right (integ_of (Bit u x))
                  (integ_of_type (Bit u x) (bin_BitI u x hu hx)));
        reflexivity }
      { try simplify rule off;
        rewrite (bin_add_BIT_Min_h u x);
        rewrite (integ_of_pred (Bit u x) (bin_BitI u x hu hx));
        rewrite integ_of_Min_eq;
        rewrite (zadd_commute (zminus (int_of one)) (integ_of (Bit u x)));
        reflexivity }
      { assume w2 y hw2 hy hIH2;
        try simplify rule off;
        rewrite (bin_add_BIT_BIT_h u x w2 y hw2 hy);
        refine boolE_h x _ hx _ _
        { assume hx0; rewrite hx0;
          rewrite (and_0 y);
          rewrite (cond_0 (bin_succ w2) w2);
          rewrite (xor_0 y);
          have hadd : π (bin_add u w2 ∈ bin) { refine bin_add_type u hu w2 hw2 };
          rewrite (integ_of_NCons (bin_add u w2) y hadd hy);
          rewrite (integ_of_Bit_eq (bin_add u w2) y);
          rewrite (hIH w2 hw2);
          rewrite (integ_of_Bit_eq u empty);
          rewrite (integ_of_Bit_eq w2 y);
          rewrite (zadd_int0 (zadd (integ_of u) (integ_of u))
                    (zadd_type (integ_of u) (integ_of u)));
          rewrite (zadd_interchange (integ_of u) (integ_of w2)
                                    (integ_of u) (integ_of w2));
          rewrite (zadd_left_commute (int_of y)
                    (zadd (integ_of u) (integ_of u))
                    (zadd (integ_of w2) (integ_of w2)));
          reflexivity }
        { assume hx1; rewrite hx1;
          rewrite (and_1 y);
          refine boolE_h y _ hy _ _
          { assume hy0; rewrite hy0;
            rewrite (cond_0 (bin_succ w2) w2);
            rewrite xor_1_0;
            have hadd : π (bin_add u w2 ∈ bin) { refine bin_add_type u hu w2 hw2 };
            rewrite (integ_of_NCons (bin_add u w2) one hadd one_in_bool);
            rewrite (integ_of_Bit_eq (bin_add u w2) one);
            rewrite (hIH w2 hw2);
            rewrite (integ_of_Bit_eq u one);
            rewrite (integ_of_Bit_eq w2 empty);
            rewrite (zadd_int0 (zadd (integ_of w2) (integ_of w2))
                      (zadd_type (integ_of w2) (integ_of w2)));
            rewrite (zadd_interchange (integ_of u) (integ_of w2)
                                      (integ_of u) (integ_of w2));
            rewrite left (zadd_assoc (int_of one)
                      (zadd (integ_of u) (integ_of u))
                      (zadd (integ_of w2) (integ_of w2)));
            reflexivity }
          { assume hy1; rewrite hy1;
            rewrite (cond_1 (bin_succ w2) w2);
            rewrite xor_1_1;
            have hsw2 : π (bin_succ w2 ∈ bin) { refine bin_succ_type w2 hw2 };
            have hadd : π (bin_add u (bin_succ w2) ∈ bin)
              { refine bin_add_type u hu (bin_succ w2) hsw2 };
            rewrite (integ_of_NCons (bin_add u (bin_succ w2)) empty hadd zero_in_bool);
            rewrite (integ_of_Bit_eq (bin_add u (bin_succ w2)) empty);
            rewrite (hIH (bin_succ w2) hsw2);
            rewrite (integ_of_succ w2 hw2);
            rewrite (zadd_int0
              (zadd (zadd (integ_of u) (zadd (int_of one) (integ_of w2)))
                    (zadd (integ_of u) (zadd (int_of one) (integ_of w2))))
              (zadd_type
                (zadd (integ_of u) (zadd (int_of one) (integ_of w2)))
                (zadd (integ_of u) (zadd (int_of one) (integ_of w2)))));
            rewrite (integ_of_Bit_eq u one);
            rewrite (integ_of_Bit_eq w2 one);
            rewrite (zadd_interchange (integ_of u) (zadd (int_of one) (integ_of w2))
                                      (integ_of u) (zadd (int_of one) (integ_of w2)));
            rewrite (zadd_interchange (int_of one) (integ_of w2)
                                      (int_of one) (integ_of w2));
            rewrite (zadd_interchange (int_of one) (zadd (integ_of u) (integ_of u))
                                      (int_of one) (zadd (integ_of w2) (integ_of w2)));
            rewrite (zadd_left_commute (zadd (integ_of u) (integ_of u))
                      (zadd (int_of one) (int_of one))
                      (zadd (integ_of w2) (integ_of w2)));
            reflexivity } } } } };
  refine hall w hw
end;

// Subtraction
opaque symbol diff_integ_of_eq (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zdiff (integ_of v) (integ_of w) = integ_of (bin_add v (bin_minus w))) ≔
begin
  assume v w hv hw;
  rewrite zdiff_def;
  rewrite (integ_of_add v (bin_minus w) hv (bin_minus_type w hw));
  rewrite (integ_of_minus w hw);
  reflexivity
end;

// ===========================================================================
// bin_mult: Binary Multiplication
// ===========================================================================

opaque symbol integ_of_mult (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (integ_of (bin_mult v w) = zmult (integ_of v) (integ_of w)) ≔
begin
  assume v w hv hw;
  refine bin_induct
    (λ u, integ_of (bin_mult u w) = zmult (integ_of u) (integ_of w)) v hv _ _ _
  { try simplify rule off;
    rewrite (bin_mult_Pls_eq w);
    rewrite integ_of_Pls_eq;
    rewrite (zmult_int0 (integ_of w));
    reflexivity }
  { try simplify rule off;
    rewrite (bin_mult_Min_eq w);
    rewrite (integ_of_minus w hw);
    rewrite integ_of_Min_eq;
    rewrite (zmult_zminus (int_of one) (integ_of w));
    have hz1 : π (zmult (int_of one) (integ_of w) = integ_of w)
      { refine zmult_int1 (integ_of w) (integ_of_type w hw) };
    rewrite hz1;
    reflexivity }
  { assume u b hu hb hIH;
    try simplify rule off;
    rewrite (bin_mult_Bit_eq u b w);
    have hmul : π (bin_mult u w ∈ bin) { refine bin_mult_type u w hu hw };
    refine boolE_h b _ hb _ _
    { assume h0; rewrite h0;
      rewrite (cond_0 (bin_add (NCons (bin_mult u w) empty) w)
                      (NCons (bin_mult u w) empty));
      rewrite (integ_of_NCons (bin_mult u w) empty hmul zero_in_bool);
      rewrite (integ_of_Bit_eq (bin_mult u w) empty);
      rewrite hIH;
      rewrite (integ_of_Bit_eq u empty);
      rewrite (zadd_int0
        (zadd (zmult (integ_of u) (integ_of w)) (zmult (integ_of u) (integ_of w)))
        (zadd_type (zmult (integ_of u) (integ_of w)) (zmult (integ_of u) (integ_of w))));
      rewrite (zadd_int0 (zadd (integ_of u) (integ_of u))
                (zadd_type (integ_of u) (integ_of u)));
      rewrite (zadd_zmult_distrib (integ_of u) (integ_of u) (integ_of w));
      reflexivity }
    { assume h1; rewrite h1;
      rewrite (cond_1 (bin_add (NCons (bin_mult u w) empty) w)
                      (NCons (bin_mult u w) empty));
      have hnc : π (NCons (bin_mult u w) empty ∈ bin)
        { refine NCons_type (bin_mult u w) empty hmul zero_in_bool };
      rewrite (integ_of_add (NCons (bin_mult u w) empty) w hnc hw);
      rewrite (integ_of_NCons (bin_mult u w) empty hmul zero_in_bool);
      rewrite (integ_of_Bit_eq (bin_mult u w) empty);
      rewrite hIH;
      rewrite (integ_of_Bit_eq u one);
      rewrite (zadd_int0
        (zadd (zmult (integ_of u) (integ_of w)) (zmult (integ_of u) (integ_of w)))
        (zadd_type (zmult (integ_of u) (integ_of w)) (zmult (integ_of u) (integ_of w))));
      rewrite (zadd_zmult_distrib (int_of one) (zadd (integ_of u) (integ_of u))
                                  (integ_of w));
      have hz1 : π (zmult (int_of one) (integ_of w) = integ_of w)
        { refine zmult_int1 (integ_of w) (integ_of_type w hw) };
      rewrite hz1;
      rewrite (zadd_zmult_distrib (integ_of u) (integ_of u) (integ_of w));
      rewrite (zadd_commute
        (zadd (zmult (integ_of u) (integ_of w)) (zmult (integ_of u) (integ_of w)))
        (integ_of w));
      reflexivity } }
end;

// ===========================================================================
// Computations
// ===========================================================================

// extra rules for bin_succ, bin_pred
opaque symbol bin_succ_1 (w : τ ι) : π (bin_succ (Bit w one) = Bit (bin_succ w) empty) ≔
begin
  assume w;
  refine eq_trans (bin_succ_Bit_eq w one)
    (cond_1 (Bit (bin_succ w) empty) (NCons w one))
end;

opaque symbol bin_succ_0 (w : τ ι) : π (bin_succ (Bit w empty) = NCons w one) ≔
begin
  assume w;
  refine eq_trans (bin_succ_Bit_eq w empty)
    (cond_0 (Bit (bin_succ w) empty) (NCons w one))
end;

opaque symbol bin_pred_1 (w : τ ι) : π (bin_pred (Bit w one) = NCons w empty) ≔
begin
  assume w;
  refine eq_trans (bin_pred_Bit_eq w one)
    (cond_1 (NCons w empty) (Bit (bin_pred w) one))
end;

opaque symbol bin_pred_0 (w : τ ι) : π (bin_pred (Bit w empty) = Bit (bin_pred w) one) ≔
begin
  assume w;
  refine eq_trans (bin_pred_Bit_eq w empty)
    (cond_0 (NCons w empty) (Bit (bin_pred w) one))
end;

// extra rules for bin_minus
opaque symbol bin_minus_1 (w : τ ι) :
  π (bin_minus (Bit w one) = bin_pred (NCons (bin_minus w) empty)) ≔
begin
  assume w;
  refine eq_trans (bin_minus_Bit_eq w one)
    (cond_1 (bin_pred (NCons (bin_minus w) empty)) (Bit (bin_minus w) empty))
end;

opaque symbol bin_minus_0 (w : τ ι) :
  π (bin_minus (Bit w empty) = Bit (bin_minus w) empty) ≔
begin
  assume w;
  refine eq_trans (bin_minus_Bit_eq w empty)
    (cond_0 (bin_pred (NCons (bin_minus w) empty)) (Bit (bin_minus w) empty))
end;

// extra rules for bin_add
opaque symbol bin_add_BIT_11 (v w : τ ι) :
  π (w ∈ bin) →
  π (bin_add (Bit v one) (Bit w one) = NCons (bin_add v (bin_succ w)) empty) ≔
begin
  assume v w hw;
  rewrite (bin_add_BIT_BIT_h v one w one hw one_in_bool);
  rewrite (and_1 one);
  rewrite (cond_1 (bin_succ w) w);
  rewrite xor_1_1;
  reflexivity
end;

opaque symbol bin_add_BIT_10 (v w : τ ι) :
  π (w ∈ bin) →
  π (bin_add (Bit v one) (Bit w empty) = NCons (bin_add v w) one) ≔
begin
  assume v w hw;
  rewrite (bin_add_BIT_BIT_h v one w empty hw zero_in_bool);
  rewrite (and_1 empty);
  rewrite (cond_0 (bin_succ w) w);
  rewrite xor_1_0;
  reflexivity
end;

opaque symbol bin_add_BIT_0 (v w y : τ ι) :
  π (w ∈ bin) → π (y ∈ bool_set) →
  π (bin_add (Bit v empty) (Bit w y) = NCons (bin_add v w) y) ≔
begin
  assume v w y hw hy;
  rewrite (bin_add_BIT_BIT_h v empty w y hw hy);
  rewrite (and_0 y);
  rewrite (cond_0 (bin_succ w) w);
  rewrite (xor_0 y);
  reflexivity
end;

// extra rules for bin_mult
opaque symbol bin_mult_1 (v w : τ ι) :
  π (bin_mult (Bit v one) w = bin_add (NCons (bin_mult v w) empty) w) ≔
begin
  assume v w;
  refine eq_trans (bin_mult_Bit_eq v one w)
    (cond_1 (bin_add (NCons (bin_mult v w) empty) w) (NCons (bin_mult v w) empty))
end;

opaque symbol bin_mult_0 (v w : τ ι) :
  π (bin_mult (Bit v empty) w = NCons (bin_mult v w) empty) ≔
begin
  assume v w;
  refine eq_trans (bin_mult_Bit_eq v empty w)
    (cond_0 (bin_add (NCons (bin_mult v w) empty) w) (NCons (bin_mult v w) empty))
end;

// ===========================================================================
// Simplification rules with integer constants
// ===========================================================================

opaque symbol int_of_0 : π (int_of empty = Int0) ≔
begin refine eq_sym Int0_eq end;

opaque symbol int_of_succ (n : τ ι) : π (int_of (succ n) = zadd Int1 (int_of n)) ≔
begin
  assume n;
  rewrite Int1_eq;
  refine int_succ_int_1 n
end;

opaque symbol zminus_0 : π (zminus Int0 = Int0) ≔
begin rewrite Int0_eq; refine zminus_int0 end;

opaque symbol zadd_0_intify (z : τ ι) : π (zadd Int0 z = intify z) ≔
begin assume z; rewrite Int0_eq; refine zadd_int0_intify z end;

opaque symbol zadd_0_right_intify (z : τ ι) : π (zadd z Int0 = intify z) ≔
begin assume z; rewrite Int0_eq; refine zadd_int0_right_intify z end;

opaque symbol zmult_1_intify (z : τ ι) : π (zmult Int1 z = intify z) ≔
begin assume z; rewrite Int1_eq; refine zmult_int1_intify z end;

opaque symbol zmult_1_right_intify (z : τ ι) : π (zmult z Int1 = intify z) ≔
begin
  assume z;
  rewrite (zmult_commute z Int1);
  rewrite Int1_eq;
  refine zmult_int1_intify z
end;

opaque symbol zmult_0 (z : τ ι) : π (zmult Int0 z = Int0) ≔
begin assume z; rewrite Int0_eq; refine zmult_int0 z end;

opaque symbol zmult_0_right (z : τ ι) : π (zmult z Int0 = Int0) ≔
begin
  assume z;
  rewrite (zmult_commute z Int0);
  rewrite Int0_eq;
  refine zmult_int0 z
end;

opaque symbol zmult_minus1 (z : τ ι) : π (zmult NegInt1 z = zminus z) ≔
begin
  assume z;
  rewrite NegInt1_eq;
  rewrite (zmult_zminus (int_of one) z);
  have h1 : π (zmult (int_of one) z = intify z) { refine zmult_int1_intify z };
  rewrite h1;
  refine zminus_intify z
end;

opaque symbol zmult_minus1_right (z : τ ι) : π (zmult z NegInt1 = zminus z) ≔
begin
  assume z;
  rewrite (zmult_commute z NegInt1);
  rewrite NegInt1_eq;
  rewrite (zmult_zminus (int_of one) z);
  have h1 : π (zmult (int_of one) z = intify z) { refine zmult_int1_intify z };
  rewrite h1;
  refine zminus_intify z
end;

// ===========================================================================
// Simplification Rules for Comparison of Binary Numbers (Thanks to Norbert Voelker)
// ===========================================================================

// Equals (=)

// port-internal helper: $#(succ q) ≠ $#0
private opaque symbol int_of_succ_neq_0 (q : τ ι) :
  π (int_of (succ q) = int_of empty) → π ⊥ ≔
begin
  assume q h;
  have h2 : π (natify (succ q) = natify empty)
    { refine ∧ₑ₁ (int_of_eq (succ q) empty) h };
  have h3 : π (succ (natify q) = empty)
    { refine eq_trans (eq_sym (natify_succ q)) (eq_trans h2 natify_0) };
  refine succ_neq_0 (natify q) h3
end;

// port-internal helper: $-$#(succ q) ≠ $#0
private opaque symbol zminus_int_of_succ_neq_0 (q : τ ι) :
  π (zminus (int_of (succ q)) = int_of empty) → π ⊥ ≔
begin
  assume q h;
  have h2 : π (int_of (succ q) = int_of empty)
    { refine eq_trans
        (eq_sym (zminus_zminus (int_of (succ q)) (int_of_type (succ q))))
        (eq_trans (feq zminus h) zminus_int0) };
  refine int_of_succ_neq_0 q h2
end;

// port-internal helper: $#1 $+ $-$#(succ q) = $-$#q
private opaque symbol one_plus_zminus_succ (q : τ ι) :
  π (zadd (int_of one) (zminus (int_of (succ q))) = zminus (int_of q)) ≔
begin
  assume q;
  have h1 : π (int_of (succ q) = zadd (int_of one) (int_of q))
    { refine int_succ_int_1 q };
  rewrite h1;
  rewrite (zminus_zadd_distrib (int_of one) (int_of q));
  rewrite left (zadd_assoc (int_of one) (zminus (int_of one)) (zminus (int_of q)));
  rewrite (zadd_zminus_inverse (int_of one));
  refine zadd_int0 (zminus (int_of q)) (zminus_type (int_of q))
end;

// port-internal helper: $#(succ n) $+ $#(succ n) = $#(succ(succ(n#+n)))
private opaque symbol double_int_of_succ (n : τ ι) :
  π (zadd (int_of (succ n)) (int_of (succ n)) = int_of (succ (succ (add n n)))) ≔
begin
  assume n;
  rewrite left (int_of_add (succ n) (succ n));
  rewrite (add_succ n (succ n));
  rewrite (add_succ_right n n);
  reflexivity
end;

opaque symbol eq_integ_of_eq (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (integ_of v = integ_of w ⇔ iszero (integ_of (bin_add v (bin_minus w)))) ≔
begin
  assume v w hv hw;
  rewrite (iszero_def (integ_of (bin_add v (bin_minus w))));
  rewrite left (diff_integ_of_eq v w hv hw);
  refine ∧ᵢ _ _
  { assume h; rewrite h; rewrite (zdiff_def (integ_of w) (integ_of w));
    refine zadd_zminus_inverse (integ_of w) }
  { assume h;
    refine eq_trans
      (∧ₑ₁ (zdiff_eq_iff (integ_of v) (integ_of w) (int_of empty)
        (integ_of_type v hv) (int_of_type empty)) h)
      (zadd_int0 (integ_of w) (integ_of_type w hw)) }
end;

opaque symbol iszero_integ_of_Pls : π (iszero (integ_of Pls)) ≔
begin
  rewrite (iszero_def (integ_of Pls));
  refine integ_of_Pls_eq
end;

opaque symbol nonzero_integ_of_Min : π (¬ iszero (integ_of Min)) ≔
begin
  rewrite (iszero_def (integ_of Min));
  rewrite integ_of_Min_eq;
  assume h;
  refine zminus_int_of_succ_neq_0 empty h
end;

opaque symbol iszero_integ_of_BIT (w x : τ ι) :
  π (w ∈ bin) → π (x ∈ bool_set) →
  π (iszero (integ_of (Bit w x)) ⇔ (x = empty ∧ iszero (integ_of w))) ≔
begin
  assume w x hw hx;
  rewrite (integ_of_Bit_eq w x);
  rewrite (iszero_def (zadd (int_of x) (zadd (integ_of w) (integ_of w))));
  rewrite (iszero_def (integ_of w));
  refine ∃ₑ (int_cases (integ_of w) (integ_of_type w hw)) _;
  assume n hn;
  have hnw : π (n ∈ omega) { refine ∧ₑ₁ hn };
  refine ∨ₑ (∧ₑ₂ hn) _ _
  { assume hpos; rewrite hpos;
    refine boolE_h x _ hx _ _
    { assume h0; rewrite h0;
      rewrite (zadd_int0 (zadd (int_of n) (int_of n))
                (zadd_type (int_of n) (int_of n)));
      rewrite left (int_of_add n n);
      refine ∧ᵢ _ _
      { assume h;
        have hnn : π (natify (add n n) = natify empty)
          { refine ∧ₑ₁ (int_of_eq (add n n) empty) h };
        have hadd : π (add n n = empty)
          { refine eq_trans (eq_sym (natify_ident (add n n) (add_type n n)))
              (eq_trans hnn natify_0) };
        have hn0 : π (n = empty)
          { refine natE n (n = empty) hnw _ _
            { assume he; refine he }
            { assume m hm hsm;
              have hc : π (succ (add m n) = empty)
                { refine eq_trans (eq_sym (add_succ m n))
                    (ind_eq (eq_sym hsm) (λ u, add u n = empty) hadd) };
              refine ⊥ₑ (succ_neq_0 (add m n) hc) } };
        have hsecond : π (int_of n = int_of empty)
          { rewrite hn0; reflexivity };
        refine ∧ᵢ (eq_refl empty) hsecond }
      { assume h;
        have h2 : π (int_of n = int_of empty) { refine ∧ₑ₂ h };
        have hn0 : π (natify n = empty)
          { refine eq_trans (∧ₑ₁ (int_of_eq n empty) h2) natify_0 };
        have hn0' : π (n = empty)
          { refine eq_trans (eq_sym (natify_ident n hnw)) hn0 };
        rewrite hn0';
        rewrite (add_0 empty zero_in_omega);
        reflexivity } }
    { assume h1x; rewrite h1x;
      rewrite left (int_of_add n n);
      rewrite left (int_of_add one (add n n));
      refine ∧ᵢ _ _
      { assume h;
        have h2 : π (int_of (succ (add empty (add n n))) = int_of empty)
          { refine eq_trans (eq_sym (feq int_of (add_succ empty (add n n)))) h };
        refine ⊥ₑ (int_of_succ_neq_0 (add empty (add n n)) h2) }
      { assume h; refine ⊥ₑ (succ_neq_0 empty (∧ₑ₁ h)) } } }
  { assume hneg; rewrite hneg;
    have hns : π (zadd (zminus (int_of (succ n))) (zminus (int_of (succ n)))
                  = zminus (int_of (succ (succ (add n n)))))
      { rewrite left (zminus_zadd_distrib (int_of (succ n)) (int_of (succ n)));
        refine feq zminus (double_int_of_succ n) };
    rewrite hns;
    refine boolE_h x _ hx _ _
    { assume h0; rewrite h0;
      rewrite (zadd_int0 (zminus (int_of (succ (succ (add n n)))))
                (zminus_type (int_of (succ (succ (add n n))))));
      refine ∧ᵢ _ _
      { assume h; refine ⊥ₑ (zminus_int_of_succ_neq_0 (succ (add n n)) h) }
      { assume h; refine ⊥ₑ (zminus_int_of_succ_neq_0 n (∧ₑ₂ h)) } }
    { assume h1x; rewrite h1x;
      rewrite (one_plus_zminus_succ (succ (add n n)));
      refine ∧ᵢ _ _
      { assume h; refine ⊥ₑ (zminus_int_of_succ_neq_0 (add n n) h) }
      { assume h; refine ⊥ₑ (succ_neq_0 empty (∧ₑ₁ h)) } } }
end;

opaque symbol iszero_integ_of_0 (w : τ ι) :
  π (w ∈ bin) → π (iszero (integ_of (Bit w empty)) ⇔ iszero (integ_of w)) ≔
begin
  assume w hw;
  have hBIT : π (iszero (integ_of (Bit w empty)) ⇔ (empty = empty ∧ iszero (integ_of w)))
    { refine iszero_integ_of_BIT w empty hw zero_in_bool };
  refine ∧ᵢ _ _
  { assume h; refine ∧ₑ₂ (∧ₑ₁ hBIT h) }
  { assume h; refine ∧ₑ₂ hBIT (∧ᵢ (eq_refl empty) h) }
end;

opaque symbol iszero_integ_of_1 (w : τ ι) :
  π (w ∈ bin) → π (¬ iszero (integ_of (Bit w one))) ≔
begin
  assume w hw h;
  refine succ_neq_0 empty
    (∧ₑ₁ (∧ₑ₁ (iszero_integ_of_BIT w one hw one_in_bool) h))
end;

// Less-than (<)

opaque symbol less_integ_of_eq_neg (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zless (integ_of v) (integ_of w) ⇔
     znegative (integ_of (bin_add v (bin_minus w)))) ≔
begin
  assume v w hv hw;
  rewrite (zless_def (integ_of v) (integ_of w));
  rewrite (diff_integ_of_eq v w hv hw);
  refine iff_refl_h (znegative (integ_of (bin_add v (bin_minus w))))
end;

opaque symbol not_neg_integ_of_Pls : π (¬ znegative (integ_of Pls)) ≔
begin
  rewrite integ_of_Pls_eq;
  refine not_znegative_int_of empty
end;

opaque symbol neg_integ_of_Min : π (znegative (integ_of Min)) ≔
begin
  rewrite integ_of_Min_eq;
  refine znegative_zminus_int_of empty
end;

opaque symbol neg_integ_of_BIT (w x : τ ι) :
  π (w ∈ bin) → π (x ∈ bool_set) →
  π (znegative (integ_of (Bit w x)) ⇔ znegative (integ_of w)) ≔
begin
  assume w x hw hx;
  rewrite (integ_of_Bit_eq w x);
  refine ∃ₑ (int_cases (integ_of w) (integ_of_type w hw)) _;
  assume n hn;
  refine ∨ₑ (∧ₑ₂ hn) _ _
  { assume hpos; rewrite hpos;
    rewrite left (int_of_add n n);
    rewrite left (int_of_add x (add n n));
    refine ∧ᵢ _ _
    { assume h; refine ⊥ₑ (not_znegative_int_of (add x (add n n)) h) }
    { assume h; refine ⊥ₑ (not_znegative_int_of n h) } }
  { assume hneg; rewrite hneg;
    have hns : π (zadd (zminus (int_of (succ n))) (zminus (int_of (succ n)))
                  = zminus (int_of (succ (succ (add n n)))))
      { rewrite left (zminus_zadd_distrib (int_of (succ n)) (int_of (succ n)));
        refine feq zminus (double_int_of_succ n) };
    rewrite hns;
    refine boolE_h x _ hx _ _
    { assume h0; rewrite h0;
      rewrite (zadd_int0 (zminus (int_of (succ (succ (add n n)))))
                (zminus_type (int_of (succ (succ (add n n))))));
      refine ∧ᵢ (λ _, znegative_zminus_int_of n)
                (λ _, znegative_zminus_int_of (succ (add n n))) }
    { assume h1x; rewrite h1x;
      rewrite (one_plus_zminus_succ (succ (add n n)));
      refine ∧ᵢ (λ _, znegative_zminus_int_of n)
                (λ _, znegative_zminus_int_of (add n n)) } }
end;

// Less-than-or-equals (<=)

opaque symbol le_integ_of_eq_not_less (x w : τ ι) :
  π (zle (integ_of x) (integ_of w) ⇔ ¬ zless (integ_of w) (integ_of x)) ≔
begin
  assume x w;
  refine iff_sym_h (¬ zless (integ_of w) (integ_of x))
    (zle (integ_of x) (integ_of w))
    (not_zless_iff_zle (integ_of w) (integ_of x))
end;

// SKIPPED: `declare bin_succ_BIT [simp del] bin_pred_BIT [simp del]
// bin_minus_BIT [simp del] NCons_Pls [simp del] NCons_Min [simp del]
// bin_adder_BIT [simp del] bin_mult_BIT [simp del]` and `declare
// integ_of_Pls [simp del] integ_of_Min [simp del] integ_of_BIT [simp del]`
// — all ten names are the auto-generated `primrec` defining equations (from
// the primrec blocks at the top of the .thy); in this port they are already
// absorbed into the `≔`-definitions of integ_of/NCons/bin_succ/bin_pred/
// bin_minus/bin_adder/bin_mult via bin_rec, not separate lemma statements —
// nothing to (un)declare.

// SKIPPED: `lemmas bin_arith_extra_simps = ...`, `lemmas bin_arith_simps =
// ...`, `lemmas bin_rel_simps = ...`, and the following
// `declare bin_arith_simps [simp]` / `declare bin_rel_simps [simp]` — named
// hint bundles of already-ported facts (mixed with the primrec equations
// noted above), not fresh Prop-typed statements (same precedent as
// `div_rls` in ArithSimp.lp).

// ===========================================================================
// Simplification of arithmetic when nested to the right
// ===========================================================================

opaque symbol add_integ_of_left (v w z : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zadd (integ_of v) (zadd (integ_of w) z) = zadd (integ_of (bin_add v w)) z) ≔
begin
  assume v w z hv hw;
  rewrite left (zadd_assoc (integ_of v) (integ_of w) z);
  rewrite left (integ_of_add v w hv hw);
  reflexivity
end;

opaque symbol mult_integ_of_left (v w z : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zmult (integ_of v) (zmult (integ_of w) z) = zmult (integ_of (bin_mult v w)) z) ≔
begin
  assume v w z hv hw;
  rewrite left (zmult_assoc (integ_of v) (integ_of w) z);
  rewrite left (integ_of_mult v w hv hw);
  reflexivity
end;

opaque symbol add_integ_of_diff1 (v w c : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zadd (integ_of v) (zdiff (integ_of w) c) = zdiff (integ_of (bin_add v w)) c) ≔
begin
  assume v w c hv hw;
  rewrite (zdiff_def (integ_of w) c);
  rewrite (zdiff_def (integ_of (bin_add v w)) c);
  rewrite left (zadd_assoc (integ_of v) (integ_of w) (zminus c));
  rewrite left (integ_of_add v w hv hw);
  reflexivity
end;

opaque symbol add_integ_of_diff2 (v w c : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zadd (integ_of v) (zdiff c (integ_of w)) =
     zadd (integ_of (bin_add v (bin_minus w))) c) ≔
begin
  assume v w c hv hw;
  rewrite left (diff_integ_of_eq v w hv hw);
  rewrite (zdiff_def c (integ_of w));
  rewrite (zdiff_def (integ_of v) (integ_of w));
  rewrite (zadd_assoc (integ_of v) (zminus (integ_of w)) c);
  rewrite (zadd_commute (zminus (integ_of w)) c);
  reflexivity
end;

// ===========================================================================
// More for integer constants
// ===========================================================================

// SKIPPED: `declare int_of_0 [simp] int_of_succ [simp]` — simp-attribute
// toggle on the two facts already stated above (int_of_0, int_of_succ), no
// new content.

opaque symbol zdiff0 (x : τ ι) : π (zdiff Int0 x = zminus x) ≔
begin
  assume x;
  rewrite Int0_eq;
  rewrite (zdiff_def (int_of empty) x);
  refine eq_trans (zadd_int0_intify (zminus x)) (intify_ident (zminus x) (zminus_type x))
end;

opaque symbol zdiff0_right (x : τ ι) : π (zdiff x Int0 = intify x) ≔
begin
  assume x;
  rewrite Int0_eq;
  rewrite (zdiff_def x (int_of empty));
  rewrite zminus_int0;
  refine zadd_int0_right_intify x
end;

opaque symbol zdiff_self (x : τ ι) : π (zdiff x x = Int0) ≔
begin
  assume x;
  rewrite Int0_eq;
  rewrite (zdiff_def x x);
  refine zadd_zminus_inverse x
end;

opaque symbol znegative_iff_zless_0 (k : τ ι) :
  π (k ∈ int) → π (znegative k ⇔ zless k Int0) ≔
begin
  assume k hk;
  rewrite (zless_def k Int0);
  have hd : π (zdiff k Int0 = k)
    { rewrite Int0_eq;
      rewrite (zdiff_def k (int_of empty));
      rewrite zminus_int0;
      refine zadd_int0_right k hk };
  rewrite hd;
  refine iff_refl_h (znegative k)
end;

opaque symbol zero_zless_imp_znegative_zminus (k : τ ι) :
  π (zless Int0 k) → π (k ∈ int) → π (znegative (zminus k)) ≔
begin
  assume k h hk;
  have h2 : π (znegative (zdiff Int0 k))
    { refine ind_eq (eq_sym (zless_def Int0 k)) (λ p, p) h };
  refine ind_eq (eq_sym (zdiff0 k)) (λ u, znegative u) h2
end;

opaque symbol zero_zle_int_of (n : τ ι) : π (zle Int0 (int_of n)) ≔
begin
  assume n;
  have h1 : π (¬ zless (int_of n) Int0)
    { assume hl;
      refine not_znegative_int_of n
        (∧ₑ₂ (znegative_iff_zless_0 (int_of n) (int_of_type n)) hl) };
  refine ∧ₑ₁ (not_zless_iff_zle (int_of n) Int0) h1
end;

opaque symbol nat_of_0 : π (nat_of Int0 = empty) ≔
begin
  rewrite Int0_eq;
  refine eq_trans (nat_of_int_of empty) natify_0
end;

opaque symbol nat_le_int0_lemma (z : τ ι) :
  π (zle z (int_of empty)) → π (z ∈ int) → π (nat_of z = empty) ≔
begin
  assume z hle hz;
  have hor : π (zless z (int_of empty) ∨ intify z = intify (int_of empty))
    { refine ind_eq (eq_sym (zle_def z (int_of empty))) (λ p, p) hle };
  refine ∨ₑ hor _ _
  { assume hlt;
    have hzn : π (znegative z)
      { refine ∧ₑ₂ (znegative_iff_zless_0 z hz)
          (ind_eq Int0_eq (λ u, zless z u) hlt) };
    have hzi : π (znegative (intify z))
      { rewrite (intify_ident z hz); refine hzn };
    refine zneg_nat_of z hzi }
  { assume heq;
    have hz0 : π (z = int_of empty)
      { refine eq_trans (eq_sym (intify_ident z hz))
          (eq_trans heq (intify_ident (int_of empty) (int_of_type empty))) };
    rewrite hz0;
    refine eq_trans (nat_of_int_of empty) natify_0 }
end;

opaque symbol nat_le_int0 (z : τ ι) :
  π (zle z (int_of empty)) → π (nat_of z = empty) ≔
begin
  assume z hle;
  have h2 : π (zle (intify z) (int_of empty))
    { refine ∧ₑ₂ (zle_intify1 z (int_of empty)) hle };
  refine eq_trans (eq_sym (nat_of_intify z))
    (nat_le_int0_lemma (intify z) h2 (intify_in_int z))
end;

opaque symbol int_of_eq_0_imp_natify_eq_0 (n : τ ι) :
  π (int_of n = Int0) → π (natify n = empty) ≔
begin
  assume n h;
  have h2 : π (int_of n = int_of empty) { refine eq_trans h Int0_eq };
  refine eq_trans (∧ₑ₁ (int_of_eq n empty) h2) natify_0
end;

opaque symbol nat_of_zminus_int_of (n : τ ι) : π (nat_of (zminus (int_of n)) = empty) ≔
begin
  assume n;
  have hkey : π (nat_of (zminus (int_of (natify n))) = empty)
    { refine natE (natify n) (nat_of (zminus (int_of (natify n))) = empty)
        (natify_in_nat n) _ _
      { assume he; rewrite he;
        rewrite zminus_int0;
        refine eq_trans (nat_of_int_of empty) natify_0 }
      { assume x hx he; rewrite he;
        have hneg : π (znegative (intify (zminus (int_of (succ x)))))
          { rewrite (intify_ident (zminus (int_of (succ x)))
              (zminus_type (int_of (succ x))));
            refine znegative_zminus_int_of x };
        refine zneg_nat_of (zminus (int_of (succ x))) hneg } };
  refine ind_eq (eq_sym (int_of_natify n)) (λ u, nat_of (zminus u) = empty) hkey
end;

opaque symbol int_of_nat_of (z : τ ι) :
  π (zle Int0 z) → π (int_of (nat_of z) = intify z) ≔
begin
  assume z hle;
  refine not_zneg_nat_of_intify z _;
  assume hneg;
  have h1 : π (zless (intify z) Int0)
    { refine ∧ₑ₁ (znegative_iff_zless_0 (intify z) (intify_in_int z)) hneg };
  have h2 : π (zless z Int0) { refine ∧ₑ₁ (zless_intify1 z Int0) h1 };
  refine ∧ₑ₂ (not_zless_iff_zle z Int0) hle h2
end;

// SKIPPED: `declare int_of_nat_of [simp] nat_of_zminus_int_of [simp]` —
// simp-attribute toggle on the two facts just stated, no new content.

opaque symbol int_of_nat_of_if (z : τ ι) :
  π (int_of (nat_of z) = If (zle Int0 z) (intify z) Int0) ≔
begin
  assume z;
  refine ∨ₑ (em (zle Int0 z)) _ _
  { assume hle;
    rewrite (If_P (zle Int0 z) (intify z) Int0 hle);
    refine int_of_nat_of z hle }
  { assume hnle;
    rewrite (If_not_P (zle Int0 z) (intify z) Int0 hnle);
    have hlt : π (zless z Int0) { refine ∧ₑ₁ (not_zle_iff_zless Int0 z) hnle };
    have hzneg : π (znegative (intify z))
      { refine ∧ₑ₂ (znegative_iff_zless_0 (intify z) (intify_in_int z))
          (∧ₑ₂ (zless_intify1 z Int0) hlt) };
    rewrite (zneg_nat_of z hzneg);
    refine eq_sym Int0_eq }
end;

opaque symbol zless_nat_iff_int_zless (m z : τ ι) :
  π (m ∈ omega) → π (z ∈ int) → π (lt m (nat_of z) ⇔ zless (int_of m) z) ≔
begin
  assume m z hm hz;
  refine ∨ₑ (em (znegative z)) _ _
  { assume hneg;
    have hzi : π (znegative (intify z))
      { rewrite (intify_ident z hz); refine hneg };
    have hn0 : π (nat_of z = empty) { refine zneg_nat_of z hzi };
    have hzlt : π (zless z Int0)
      { refine ∧ₑ₁ (znegative_iff_zless_0 z hz) hneg };
    refine ∧ᵢ _ _
    { assume hl;
      have hm0 : π (m ∈ empty)
        { refine ind_eq (eq_sym hn0) (λ u, m ∈ u) (ltD m (nat_of z) hl) };
      refine ⊥ₑ (emptyE m hm0) }
    { assume hr;
      have hmlt : π (zless (int_of m) Int0)
        { refine zless_zle_trans (int_of m) z Int0 hr (zless_imp_zle z Int0 hzlt) };
      refine ⊥ₑ (not_znegative_int_of m
        (∧ₑ₂ (znegative_iff_zless_0 (int_of m) (int_of_type m)) hmlt)) } }
  { assume hnneg;
    have h2 : π (int_of (nat_of z) = z) { refine not_zneg_nat_of z hnneg hz };
    have h1 : π (lt m (nat_of z) ⇔ zless (int_of m) (int_of (nat_of z)))
      { refine iff_sym_h _ _ (zless_int_of m (nat_of z) hm (nat_of_type z)) };
    have h3 : π (zless (int_of m) (int_of (nat_of z)) ⇔ zless (int_of m) z)
      { rewrite h2; refine iff_refl_h (zless (int_of m) z) };
    refine iff_trans_h _ _ _ h1 h3 }
end;

// ===========================================================================
// nat_of and zless
// ===========================================================================

// An alternative condition is $#0 ⊆ w
opaque symbol zless_nat_conj_lemma (w z : τ ι) :
  π (zless (int_of empty) z) → π (lt (nat_of w) (nat_of z) ⇔ zless w z) ≔
begin
  assume w z h;
  have hle : π (zle Int0 z)
    { refine ind_eq Int0_eq (λ u, zle u z) (zless_imp_zle (int_of empty) z h) };
  have hz2 : π (int_of (nat_of z) = intify z) { refine int_of_nat_of z hle };
  have h1 : π (lt (nat_of w) (nat_of z) ⇔
               zless (int_of (nat_of w)) (int_of (nat_of z)))
    { refine iff_sym_h _ _
        (zless_int_of (nat_of w) (nat_of z) (nat_of_type w) (nat_of_type z)) };
  have h2 : π (zless (int_of (nat_of w)) (int_of (nat_of z)) ⇔
               zless (int_of (nat_of w)) z)
    { rewrite hz2; refine zless_intify2 (int_of (nat_of w)) z };
  refine ∨ₑ (em (znegative (intify w))) _ _
  { assume hneg;
    have hnw0 : π (nat_of w = empty) { refine zneg_nat_of w hneg };
    have hlhs : π (zless (int_of (nat_of w)) z) { rewrite hnw0; refine h };
    have hInt0z : π (zless Int0 z) { refine ind_eq Int0_eq (λ u, zless u z) h };
    have hwneg : π (zless (intify w) Int0)
      { refine ∧ₑ₁ (znegative_iff_zless_0 (intify w) (intify_in_int w)) hneg };
    have hrhs : π (zless w z)
      { refine ∧ₑ₁ (zless_intify1 w z)
          (zless_trans (intify w) Int0 z hwneg hInt0z) };
    have h3 : π (zless (int_of (nat_of w)) z ⇔ zless w z)
      { refine ∧ᵢ (λ _, hrhs) (λ _, hlhs) };
    refine iff_trans_h _ _ _ h1 (iff_trans_h _ _ _ h2 h3) }
  { assume hnneg;
    have hw2 : π (int_of (nat_of w) = intify w)
      { refine not_zneg_nat_of_intify w hnneg };
    have h3 : π (zless (int_of (nat_of w)) z ⇔ zless w z)
      { rewrite hw2; refine zless_intify1 w z };
    refine iff_trans_h _ _ _ h1 (iff_trans_h _ _ _ h2 h3) }
end;

opaque symbol zless_nat_conj (w z : τ ι) :
  π (lt (nat_of w) (nat_of z) ⇔ (zless (int_of empty) z ∧ zless w z)) ≔
begin
  assume w z;
  refine ∨ₑ (em (zless (int_of empty) z)) _ _
  { assume h;
    refine ∧ᵢ
      (λ hl, ∧ᵢ h (∧ₑ₁ (zless_nat_conj_lemma w z h) hl))
      (λ hc, ∧ₑ₂ (zless_nat_conj_lemma w z h) (∧ₑ₂ hc)) }
  { assume hn;
    have hzle : π (zle z (int_of empty))
      { refine ∧ₑ₁ (not_zless_iff_zle (int_of empty) z) hn };
    have hnz0 : π (nat_of z = empty) { refine nat_le_int0 z hzle };
    refine ∧ᵢ _ _
    { assume hl;
      refine ⊥ₑ (emptyE (nat_of w)
        (ind_eq (eq_sym hnz0) (λ u, nat_of w ∈ u)
          (ltD (nat_of w) (nat_of z) hl))) }
    { assume hc; refine ⊥ₑ (hn (∧ₑ₁ hc)) } }
end;

// SKIPPED: the commented-out `integ_of_reorient` lemma (the .thy's own
// `(* ... *)` block) — an abandoned draft with no live content ("The
// condition True is a hack to prevent looping" — the author's note
// explains why it was never enabled).

// port-internal helper: symmetry of equality as an ⇔
private opaque symbol eq_reorient_h (a b : τ ι) : π ((a = b) ⇔ (b = a)) ≔
begin assume a b; refine ∧ᵢ (λ h, eq_sym h) (λ h, eq_sym h) end;

opaque symbol integ_of_minus_reorient (w x : τ ι) :
  π (integ_of w = zminus x ⇔ zminus x = integ_of w) ≔
begin assume w x; refine eq_reorient_h (integ_of w) (zminus x) end;

opaque symbol integ_of_add_reorient (w x y : τ ι) :
  π (integ_of w = zadd x y ⇔ zadd x y = integ_of w) ≔
begin assume w x y; refine eq_reorient_h (integ_of w) (zadd x y) end;

opaque symbol integ_of_diff_reorient (w x y : τ ι) :
  π (integ_of w = zdiff x y ⇔ zdiff x y = integ_of w) ≔
begin assume w x y; refine eq_reorient_h (integ_of w) (zdiff x y) end;

opaque symbol integ_of_mult_reorient (w x y : τ ι) :
  π (integ_of w = zmult x y ⇔ zmult x y = integ_of w) ≔
begin assume w x y; refine eq_reorient_h (integ_of w) (zmult x y) end;

// SKIPPED: `lemmas [simp] = zminus_equation [where y="integ_of(w)"]
// equation_zminus [where x="integ_of(w)"] for w`, `lemmas [iff] =
// zminus_zless [where y="integ_of(w)"] zless_zminus [where x="integ_of(w)"]
// for w`, `lemmas [iff] = zminus_zle [where y="integ_of(w)"] zle_zminus
// [where x="integ_of(w)"] for w`, and `lemmas [simp] = Let_def
// [where s="integ_of(w)"] for w` — each is a bare `[where ...]`
// SPECIALIZATION of an already fully-general lemma proved in Int.lp
// (zminus_equation, equation_zminus, zminus_zless, zless_zminus,
// zminus_zle, zle_zminus), adding no new propositional content beyond
// instantiating a bound variable (unlike a `[THEN ...]` derivation, which
// composes genuinely new content — see Int.lp's `eq_intrelD`/`zless_asym`).
// `Let_def` is not part of this port. Same treatment as `rel_iff_rel_0_rls`
// below.

// ===========================================================================
// Simprocs for numeric literals: combining of literal coefficients in sums
// of products
// ===========================================================================

opaque symbol zless_iff_zdiff_zless_0 (x y : τ ι) :
  π (zless x y ⇔ zless (zdiff x y) Int0) ≔
begin
  assume x y;
  rewrite (zless_def x y);
  refine znegative_iff_zless_0 (zdiff x y) (zdiff_type x y)
end;

opaque symbol eq_iff_zdiff_eq_0 (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (x = y ⇔ zdiff x y = Int0) ≔
begin
  assume x y hx hy;
  have hInt0 : π (Int0 ∈ int) { rewrite Int0_eq; refine int_of_type empty };
  have h1 : π (zdiff x y = Int0 ⇔ x = zadd Int0 y)
    { refine zdiff_eq_iff x y Int0 hx hInt0 };
  have h2 : π (zadd Int0 y = y)
    { refine eq_trans (zadd_0_intify y) (intify_ident y hy) };
  have h3 : π (x = zadd Int0 y ⇔ x = y)
    { rewrite h2; refine iff_refl_h (x = y) };
  refine iff_sym_h (zdiff x y = Int0) (x = y) (iff_trans_h _ _ _ h1 h3)
end;

opaque symbol zle_iff_zdiff_zle_0 (x y : τ ι) :
  π (zle x y ⇔ zle (zdiff x y) Int0) ≔
begin
  assume x y;
  have h1 : π (zle (zdiff x y) Int0 ⇔ zle x (zadd Int0 y))
    { refine zdiff_zle_iff x y Int0 };
  have h2 : π (zadd Int0 y = intify y) { refine zadd_0_intify y };
  have h3 : π (zle x (zadd Int0 y) ⇔ zle x y)
    { rewrite h2; refine zle_intify2 x y };
  refine iff_sym_h (zle (zdiff x y) Int0) (zle x y) (iff_trans_h _ _ _ h1 h3)
end;

// For combine_numerals

opaque symbol left_zadd_zmult_distrib (i u j k : τ ι) :
  π (zadd (zmult i u) (zadd (zmult j u) k) = zadd (zmult (zadd i j) u) k) ≔
begin
  assume i u j k;
  rewrite (zadd_zmult_distrib i j u);
  rewrite (zadd_assoc (zmult i u) (zmult j u) k);
  reflexivity
end;

// For cancel_numerals

opaque symbol eq_add_iff1 (i u m j n : τ ι) :
  π (zadd (zmult i u) m = zadd (zmult j u) n ⇔
     zadd (zmult (zdiff i j) u) m = intify n) ≔
begin
  assume i u m j n;
  have h1 : π (zadd (zmult (zdiff i j) u) m = zdiff (zadd (zmult i u) m) (zmult j u))
    { rewrite (zdiff_zmult_distrib i j u);
      refine zdiff_zadd_eq (zmult i u) (zmult j u) m };
  refine ∧ᵢ _ _
  { assume h;
    rewrite h1;
    rewrite h;
    rewrite (zdiff_def (zadd (zmult j u) n) (zmult j u));
    rewrite (zadd_commute (zmult j u) n);
    rewrite (zadd_assoc n (zmult j u) (zminus (zmult j u)));
    rewrite (zadd_zminus_inverse (zmult j u));
    refine zadd_int0_right_intify n }
  { assume h;
    refine eq_trans
      (∧ₑ₁ (zdiff_eq_iff (zadd (zmult i u) m) (zmult j u) (intify n)
        (zadd_type (zmult i u) m) (intify_in_int n))
        (eq_trans (eq_sym h1) h))
      (eq_trans (zadd_intify1 n (zmult j u)) (zadd_commute n (zmult j u))) }
end;

opaque symbol eq_add_iff2 (i u m j n : τ ι) :
  π (zadd (zmult i u) m = zadd (zmult j u) n ⇔
     intify m = zadd (zmult (zdiff j i) u) n) ≔
begin
  assume i u m j n;
  have h1 : π (zadd (zmult (zdiff j i) u) n = zdiff (zadd (zmult j u) n) (zmult i u))
    { rewrite (zdiff_zmult_distrib j i u);
      refine zdiff_zadd_eq (zmult j u) (zmult i u) n };
  refine ∧ᵢ _ _
  { assume h;
    rewrite h1;
    rewrite left h;
    rewrite (zdiff_def (zadd (zmult i u) m) (zmult i u));
    rewrite (zadd_commute (zmult i u) m);
    rewrite (zadd_assoc m (zmult i u) (zminus (zmult i u)));
    rewrite (zadd_zminus_inverse (zmult i u));
    refine eq_sym (zadd_int0_right_intify m) }
  { assume h;
    have h2 : π (zadd (intify m) (zmult i u) = zadd (zmult j u) n)
      { refine ∧ₑ₁ (eq_zdiff_iff (intify m) (zmult i u) (zadd (zmult j u) n)
          (intify_in_int m) (zadd_type (zmult j u) n)) (eq_trans h h1) };
    refine eq_trans (zadd_commute (zmult i u) m)
      (eq_trans (eq_sym (zadd_intify1 m (zmult i u))) h2) }
end;

// SKIPPED: `context fixes n :: i begin lemmas rel_iff_rel_0_rls = ... for u
// v end` — a hint bundle of `[where ...]` specializations of
// zless_iff_zdiff_zless_0 / eq_iff_zdiff_eq_0 / zle_iff_zdiff_zle_0 (just
// proved above), adding no new content — same reasoning as the
// reorient-adjacent skips above. `less_add_iff1`/`less_add_iff2` ARE
// genuine standalone lemmas textually nested in the same `context` block
// (they don't actually use its `fixes n`); ported normally below.

opaque symbol less_add_iff1 (i u m j n : τ ι) :
  π (zless (zadd (zmult i u) m) (zadd (zmult j u) n) ⇔
     zless (zadd (zmult (zdiff i j) u) m) n) ≔
begin
  assume i u m j n;
  have h1 : π (zadd (zmult (zdiff i j) u) m = zdiff (zadd (zmult i u) m) (zmult j u))
    { rewrite (zdiff_zmult_distrib i j u);
      refine zdiff_zadd_eq (zmult i u) (zmult j u) m };
  have h4 : π (zless (zadd (zmult (zdiff i j) u) m) n ⇔
               zless (zadd (zmult i u) m) (zadd n (zmult j u)))
    { rewrite h1; refine zdiff_zless_iff (zadd (zmult i u) m) (zmult j u) n };
  have h6 : π (zless (zadd (zmult i u) m) (zadd n (zmult j u)) ⇔
               zless (zadd (zmult i u) m) (zadd (zmult j u) n))
    { rewrite (zadd_commute n (zmult j u));
      refine iff_refl_h (zless (zadd (zmult i u) m) (zadd (zmult j u) n)) };
  refine iff_sym_h _ _ (iff_trans_h _ _ _ h4 h6)
end;

opaque symbol less_add_iff2 (i u m j n : τ ι) :
  π (zless (zadd (zmult i u) m) (zadd (zmult j u) n) ⇔
     zless m (zadd (zmult (zdiff j i) u) n)) ≔
begin
  assume i u m j n;
  have h1 : π (zadd (zmult (zdiff j i) u) n = zdiff (zadd (zmult j u) n) (zmult i u))
    { rewrite (zdiff_zmult_distrib j i u);
      refine zdiff_zadd_eq (zmult j u) (zmult i u) n };
  have h4 : π (zless m (zadd (zmult (zdiff j i) u) n) ⇔
               zless (zadd m (zmult i u)) (zadd (zmult j u) n))
    { rewrite h1; refine zless_zdiff_iff m (zmult i u) (zadd (zmult j u) n) };
  have h6 : π (zless (zadd m (zmult i u)) (zadd (zmult j u) n) ⇔
               zless (zadd (zmult i u) m) (zadd (zmult j u) n))
    { rewrite (zadd_commute m (zmult i u));
      refine iff_refl_h (zless (zadd (zmult i u) m) (zadd (zmult j u) n)) };
  refine iff_sym_h _ _ (iff_trans_h _ _ _ h4 h6)
end;

opaque symbol le_add_iff1 (i u m j n : τ ι) :
  π (zle (zadd (zmult i u) m) (zadd (zmult j u) n) ⇔
     zle (zadd (zmult (zdiff i j) u) m) n) ≔
begin
  assume i u m j n;
  have h1 : π (zadd (zmult (zdiff i j) u) m = zdiff (zadd (zmult i u) m) (zmult j u))
    { rewrite (zdiff_zmult_distrib i j u);
      refine zdiff_zadd_eq (zmult i u) (zmult j u) m };
  have h4 : π (zle (zadd (zmult (zdiff i j) u) m) n ⇔
               zle (zadd (zmult i u) m) (zadd n (zmult j u)))
    { rewrite h1; refine zdiff_zle_iff (zadd (zmult i u) m) (zmult j u) n };
  have h6 : π (zle (zadd (zmult i u) m) (zadd n (zmult j u)) ⇔
               zle (zadd (zmult i u) m) (zadd (zmult j u) n))
    { rewrite (zadd_commute n (zmult j u));
      refine iff_refl_h (zle (zadd (zmult i u) m) (zadd (zmult j u) n)) };
  refine iff_sym_h _ _ (iff_trans_h _ _ _ h4 h6)
end;

opaque symbol le_add_iff2 (i u m j n : τ ι) :
  π (zle (zadd (zmult i u) m) (zadd (zmult j u) n) ⇔
     zle m (zadd (zmult (zdiff j i) u) n)) ≔
begin
  assume i u m j n;
  have h1 : π (zadd (zmult (zdiff j i) u) n = zdiff (zadd (zmult j u) n) (zmult i u))
    { rewrite (zdiff_zmult_distrib j i u);
      refine zdiff_zadd_eq (zmult j u) (zmult i u) n };
  have h4 : π (zle m (zadd (zmult (zdiff j i) u) n) ⇔
               zle (zadd m (zmult i u)) (zadd (zmult j u) n))
    { rewrite h1; refine zle_zdiff_iff m (zmult i u) (zadd (zmult j u) n) };
  have h6 : π (zle (zadd m (zmult i u)) (zadd (zmult j u) n) ⇔
               zle (zadd (zmult i u) m) (zadd (zmult j u) n))
    { rewrite (zadd_commute m (zmult i u));
      refine iff_refl_h (zle (zadd (zmult i u) m) (zadd (zmult j u) n)) };
  refine iff_sym_h _ _ (iff_trans_h _ _ _ h4 h6)
end;

// SKIPPED FROM HERE ON: `ML_file "int_arith.ML"` (the numeral-literal
// cancel/combine simplification procedures, implemented in ML) and the
// trailing `simproc_setup` blocks plus the long run of
// `lemma "..." apply simp oops` demo goals at the end of Bin.thy — pure ML
// infrastructure / abandoned example goals with zero provable ZF content.
