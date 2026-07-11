// ZF.ArithSimp — Arithmetic with simplification
// Faithful COMPLETE port of isabelle-src/ArithSimp.thy (all proofs done).
// (Source: L. C. Paulson, ZF/ArithSimp.thy.)
//
// The .thy's opening block (simproc setup + a dozen `apply simp oops`
// examples) is ML/demo infrastructure with no proved statement — nothing to
// port there.  `div_rls` is a named bag of *existing* facts (Isabelle
// `lemmas div_rls = ...`), not a fresh statement — likewise skipped.

require open ZF.Arith;

// ===========================================================================
// Difference
// ===========================================================================

opaque symbol diff_self_eq_0 (m : τ ι) : π (diff m m = empty) ≔
begin
  assume m;
  have hkey : π (Ball omega (λ x, diff x x = empty)) {
    refine nat_induct (λ x, diff x x = empty) _ _
    { simplify rule off; rewrite (diff_0 empty); refine natify_0 }
    { assume x hx hIH; rewrite (diff_succ_succ x x); refine hIH }
  };
  rewrite left (diff_natify1 m m);
  rewrite left (diff_natify2 (natify m) m);
  refine bspec omega (λ x, diff x x = empty) (natify m) hkey (natify_in_nat m)
end;

// We need m:nat even if we replace the RHS by natify(m), for consider e.g.
// n=2, m=omega; then n + (m-n) = 2 + (0-2) = 2 ≠ 0 = natify(m).
opaque symbol add_diff_inverse (n m : τ ι) :
  π (le n m) → π (m ∈ omega) → π (add n (diff m n) = m) ≔
begin
  assume n m hle hm;
  have hn : π (n ∈ omega) { refine le_in_nat n m hle hm };
  have hkey : π (le n m ⇒ add n (diff m n) = m) {
    refine diff_induct m n (λ x y, le y x ⇒ add y (diff x y) = x) hm hn _ _ _
    { assume x hx h0;
      rewrite (diff_0 x); rewrite (natify_ident x hx); refine add_0 x hx }
    { assume y hy hle0;
      refine ⊥ₑ _;
      refine ∨ₑ (leE (succ y) empty hle0) _ _
      { assume hmem; refine emptyE (succ y) hmem }
      { assume heq; refine succ_neq_0 y heq } }
    { assume x y hx hy hIH hles;
      have hyx : π (le y x) { refine succ_leE y (succ x) hles };
      rewrite (diff_succ_succ x y);
      rewrite (add_succ y (diff x y));
      rewrite (hIH hyx); reflexivity }
  };
  refine hkey hle
end;

opaque symbol add_diff_inverse2 (n m : τ ι) :
  π (le n m) → π (m ∈ omega) → π (add (diff m n) n = m) ≔
begin
  assume n m hle hm;
  rewrite (add_commute (diff m n) n);
  refine add_diff_inverse n m hle hm
end;

// Proof is IDENTICAL to that of add_diff_inverse
opaque symbol diff_succ (n m : τ ι) :
  π (le n m) → π (m ∈ omega) → π (diff (succ m) n = succ (diff m n)) ≔
begin
  assume n m hle hm;
  have hn : π (n ∈ omega) { refine le_in_nat n m hle hm };
  have hkey : π (le n m ⇒ diff (succ m) n = succ (diff m n)) {
    refine diff_induct m n (λ x y, le y x ⇒ diff (succ x) y = succ (diff x y)) hm hn _ _ _
    { assume x hx h0;
      rewrite (diff_0 (succ x)); rewrite (natify_succ x);
      rewrite (natify_ident x hx);
      rewrite (diff_0 x); rewrite (natify_ident x hx); reflexivity }
    { assume y hy hle0;
      refine ⊥ₑ _;
      refine ∨ₑ (leE (succ y) empty hle0) _ _
      { assume hmem; refine emptyE (succ y) hmem }
      { assume heq; refine succ_neq_0 y heq } }
    { assume x y hx hy hIH hles;
      have hyx : π (le y x) { refine succ_leE y (succ x) hles };
      rewrite (diff_succ_succ (succ x) y);
      rewrite (diff_succ_succ x y);
      refine hIH hyx }
  };
  refine hkey hle
end;

opaque symbol zero_less_diff (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (lt empty (diff n m) ⇔ lt m n) ≔
begin
  assume m n hm hn;
  refine diff_induct m n (λ x y, lt empty (diff y x) ⇔ lt x y) hm hn _ _ _
  { assume x hx;
    rewrite (diff_0_eq_0 x);
    refine ∧ᵢ _ _
    { assume h; refine ⊥ₑ (not_lt0 empty h) }
    { assume h; refine ⊥ₑ (not_lt0 x h) } }
  { assume y hy;
    rewrite (diff_0 (succ y)); rewrite (natify_succ y);
    rewrite (natify_ident y hy);
    refine ∧ᵢ _ _
    { assume h; refine h }
    { assume h; refine h } }
  { assume x y hx hy hIH;
    rewrite (diff_succ_succ y x);
    refine ∧ᵢ _ _
    { assume h; refine succ_lt_mono x y (∧ₑ₁ hIH h) }
    { assume h; refine ∧ₑ₂ hIH (succ_leE x y h) } }
end;

// Difference distributes over multiplication
opaque symbol diff_mult_distrib (m n k : τ ι) :
  π (mult (diff m n) k = diff (mult m k) (mult n k)) ≔
begin
  assume m n k;
  have hkey : π (mult (diff (natify m) (natify n)) k
                 = diff (mult (natify m) k) (mult (natify n) k)) {
    refine diff_induct (natify m) (natify n)
      (λ x y, mult (diff x y) k = diff (mult x k) (mult y k))
      (natify_in_nat m) (natify_in_nat n) _ _ _
    { assume x hx;
      rewrite (diff_0 x); rewrite (natify_ident x hx);
      rewrite (mult_0 k);
      rewrite (diff_0 (mult x k));
      rewrite (natify_ident (mult x k) (mult_type x k)); reflexivity }
    { assume y hy;
      rewrite (diff_0_eq_0 (succ y)); rewrite (mult_0 k);
      rewrite (diff_0_eq_0 (mult (succ y) k)); reflexivity }
    { assume x y hx hy hIH;
      rewrite (diff_succ_succ x y);
      rewrite hIH;
      rewrite (mult_succ x k); rewrite (mult_succ y k);
      rewrite (diff_cancel k (mult x k) (mult y k)); reflexivity }
  };
  rewrite left (diff_natify1 m n);
  rewrite left (diff_natify2 (natify m) n);
  rewrite left (mult_natify1 m k);
  rewrite left (mult_natify1 n k);
  refine hkey
end;

opaque symbol diff_mult_distrib2 (k m n : τ ι) :
  π (mult k (diff m n) = diff (mult k m) (mult k n)) ≔
begin
  assume k m n;
  rewrite (mult_commute k (diff m n));
  rewrite (mult_commute k m);
  rewrite (mult_commute k n);
  refine diff_mult_distrib m n k
end;

// ===========================================================================
// Remainder
// ===========================================================================

// We need m:nat even with natify
opaque symbol div_termination (n m : τ ι) :
  π (lt empty n) → π (le n m) → π (m ∈ omega) → π (lt (diff m n) m) ≔
begin
  assume n m h0 hle hm;
  have hn : π (n ∈ omega) { refine le_in_nat n m hle hm };
  have hkey : π (lt empty n ⇒ le n m ⇒ lt (diff m n) m) {
    refine diff_induct m n (λ x y, lt empty y ⇒ le y x ⇒ lt (diff x y) x) hm hn _ _ _
    { assume x hx h0' hle';
      refine ⊥ₑ (not_lt0 empty h0') }
    { assume y hy h0' hle';
      refine ⊥ₑ _;
      refine ∨ₑ (leE (succ y) empty hle') _ _
      { assume hmem; refine emptyE (succ y) hmem }
      { assume heq; refine succ_neq_0 y heq } }
    { assume x y hx hy hIH h0' hle';
      rewrite (diff_succ_succ x y);
      refine diff_le_self x y hx }
  };
  refine hkey h0 hle
end;

// port-internal helper: the transrec unfolding of raw_mod
// (Isabelle: raw_mod_def [THEN def_transrec]).
private opaque symbol raw_mod_unfold (m n : τ ι) :
  π (raw_mod m n
     = If (lt m n ∨ (n = empty)) m
          (fapply (Lambda m (λ x, raw_mod x n)) (diff m n))) ≔
begin
  assume m n;
  refine def_transrec (λ z, raw_mod z n)
    (λ j f, If (lt j n ∨ (n = empty)) j (fapply f (diff j n))) m _;
  assume x; refine raw_mod_def x n
end;

// port-internal helper: the transrec unfolding of raw_div
// (Isabelle: raw_div_def [THEN def_transrec]).
private opaque symbol raw_div_unfold (m n : τ ι) :
  π (raw_div m n
     = If (lt m n ∨ (n = empty)) empty
          (succ (fapply (Lambda m (λ x, raw_div x n)) (diff m n)))) ≔
begin
  assume m n;
  refine def_transrec (λ z, raw_div z n)
    (λ j f, If (lt j n ∨ (n = empty)) empty (succ (fapply f (diff j n)))) m _;
  assume x; refine raw_div_def x n
end;

opaque symbol raw_mod_type (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (raw_mod m n ∈ omega) ≔
begin
  assume m n hm hn;
  refine complete_induct_rule m (λ z, raw_mod z n ∈ omega) hm _;
  assume x hx hIH;
  rewrite (raw_mod_unfold x n);
  refine ∨ₑ (em (lt x n ∨ (n = empty))) _ _
  { assume hcond;
    rewrite (If_P (lt x n ∨ (n = empty)) x
      (fapply (Lambda x (λ z, raw_mod z n)) (diff x n)) hcond);
    refine hx }
  { assume hncond;
    rewrite (If_not_P (lt x n ∨ (n = empty)) x
      (fapply (Lambda x (λ z, raw_mod z n)) (diff x n)) hncond);
    have hne : π (n ≠ empty) { assume he; refine hncond (∨ᵢ₂ he) };
    have h0n : π (lt empty n) { refine Ord_0_lt n (nat_into_Ord n hn) hne };
    have hnlt : π (¬ (lt x n)) { assume hl; refine hncond (∨ᵢ₁ hl) };
    have hnx : π (le n x)
      { refine not_lt_imp_le x n (nat_into_Ord x hx) (nat_into_Ord n hn) hnlt };
    have hmem : π (diff x n ∈ x)
      { refine ltD (diff x n) x (div_termination n x h0n hnx hx) };
    rewrite (beta x (λ z, raw_mod z n) (diff x n) hmem);
    refine hIH (diff x n) hmem }
end;

opaque symbol mod_type (m n : τ ι) : π (mod m n ∈ omega) ≔
begin
  assume m n;
  rewrite mod_def;
  refine raw_mod_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n)
end;

// Arbitrary definitions for division by zero. Useful to simplify certain equations
opaque symbol DIVISION_BY_ZERO_DIV (a : τ ι) : π (div a empty = empty) ≔
begin
  assume a;
  rewrite div_def; rewrite natify_0;
  rewrite (raw_div_unfold (natify a) empty);
  refine If_P (lt (natify a) empty ∨ (empty = empty)) empty
    (succ (fapply (Lambda (natify a) (λ x, raw_div x empty)) (diff (natify a) empty)))
    (∨ᵢ₂ (eq_refl empty))
end;

opaque symbol DIVISION_BY_ZERO_MOD (a : τ ι) : π (mod a empty = natify a) ≔
begin
  assume a;
  rewrite mod_def; rewrite natify_0;
  rewrite (raw_mod_unfold (natify a) empty);
  refine If_P (lt (natify a) empty ∨ (empty = empty)) (natify a)
    (fapply (Lambda (natify a) (λ x, raw_mod x empty)) (diff (natify a) empty))
    (∨ᵢ₂ (eq_refl empty))
end;

opaque symbol raw_mod_less (m n : τ ι) : π (lt m n) → π (raw_mod m n = m) ≔
begin
  assume m n hlt;
  rewrite (raw_mod_unfold m n);
  refine If_P (lt m n ∨ (n = empty)) m
    (fapply (Lambda m (λ x, raw_mod x n)) (diff m n)) (∨ᵢ₁ hlt)
end;

opaque symbol mod_less (m n : τ ι) : π (lt m n) → π (n ∈ omega) → π (mod m n = m) ≔
begin
  assume m n hlt hn;
  have hm : π (m ∈ omega) { refine lt_nat_in_nat m n hlt hn };
  rewrite mod_def;
  rewrite (natify_ident m hm); rewrite (natify_ident n hn);
  refine raw_mod_less m n hlt
end;

opaque symbol raw_mod_geq (n m : τ ι) :
  π (lt empty n) → π (le n m) → π (m ∈ omega) →
  π (raw_mod m n = raw_mod (diff m n) n) ≔
begin
  assume n m h0n hle hm;
  have hncond : π (¬ (lt m n ∨ (n = empty))) {
    assume hd;
    refine ∨ₑ hd _ _
    { assume hl; refine le_imp_not_lt m n hle hl }
    { assume he;
      refine not_lt0 empty (ind_eq (eq_sym he) (λ w, lt empty w) h0n) }
  };
  have hmem : π (diff m n ∈ m)
    { refine ltD (diff m n) m (div_termination n m h0n hle hm) };
  rewrite (raw_mod_unfold m n);
  rewrite (If_not_P (lt m n ∨ (n = empty)) m
    (fapply (Lambda m (λ x, raw_mod x n)) (diff m n)) hncond);
  refine beta m (λ x, raw_mod x n) (diff m n) hmem
end;

opaque symbol mod_geq (n m : τ ι) :
  π (le n m) → π (m ∈ omega) → π (mod m n = mod (diff m n) n) ≔
begin
  assume n m hle hm;
  have hn : π (n ∈ omega) { refine le_in_nat n m hle hm };
  refine ∨ₑ (em (n = empty)) _ _
  { assume heq; rewrite heq;
    rewrite (DIVISION_BY_ZERO_MOD m);
    rewrite (DIVISION_BY_ZERO_MOD (diff m empty));
    rewrite (diff_0 m); rewrite (natify_idem m); reflexivity }
  { assume hne;
    have h0n : π (lt empty n) { refine Ord_0_lt n (nat_into_Ord n hn) hne };
    rewrite (mod_def m n);
    rewrite (natify_ident m hm); rewrite (natify_ident n hn);
    rewrite (mod_def (diff m n) n);
    rewrite (natify_ident (diff m n) (diff_type m n));
    rewrite (natify_ident n hn);
    refine raw_mod_geq n m h0n hle hm }
end;

// ===========================================================================
// Division
// ===========================================================================

opaque symbol raw_div_type (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (raw_div m n ∈ omega) ≔
begin
  assume m n hm hn;
  refine complete_induct_rule m (λ z, raw_div z n ∈ omega) hm _;
  assume x hx hIH;
  rewrite (raw_div_unfold x n);
  refine ∨ₑ (em (lt x n ∨ (n = empty))) _ _
  { assume hcond;
    rewrite (If_P (lt x n ∨ (n = empty)) empty
      (succ (fapply (Lambda x (λ z, raw_div z n)) (diff x n))) hcond);
    refine zero_in_omega }
  { assume hncond;
    rewrite (If_not_P (lt x n ∨ (n = empty)) empty
      (succ (fapply (Lambda x (λ z, raw_div z n)) (diff x n))) hncond);
    have hne : π (n ≠ empty) { assume he; refine hncond (∨ᵢ₂ he) };
    have h0n : π (lt empty n) { refine Ord_0_lt n (nat_into_Ord n hn) hne };
    have hnlt : π (¬ (lt x n)) { assume hl; refine hncond (∨ᵢ₁ hl) };
    have hnx : π (le n x)
      { refine not_lt_imp_le x n (nat_into_Ord x hx) (nat_into_Ord n hn) hnlt };
    have hmem : π (diff x n ∈ x)
      { refine ltD (diff x n) x (div_termination n x h0n hnx hx) };
    rewrite (beta x (λ z, raw_div z n) (diff x n) hmem);
    refine succ_in_omega (raw_div (diff x n) n) (hIH (diff x n) hmem) }
end;

opaque symbol div_type (m n : τ ι) : π (div m n ∈ omega) ≔
begin
  assume m n;
  rewrite div_def;
  refine raw_div_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n)
end;

opaque symbol raw_div_less (m n : τ ι) : π (lt m n) → π (raw_div m n = empty) ≔
begin
  assume m n hlt;
  rewrite (raw_div_unfold m n);
  refine If_P (lt m n ∨ (n = empty)) empty
    (succ (fapply (Lambda m (λ x, raw_div x n)) (diff m n))) (∨ᵢ₁ hlt)
end;

opaque symbol div_less (m n : τ ι) : π (lt m n) → π (n ∈ omega) → π (div m n = empty) ≔
begin
  assume m n hlt hn;
  have hm : π (m ∈ omega) { refine lt_nat_in_nat m n hlt hn };
  rewrite div_def;
  rewrite (natify_ident m hm); rewrite (natify_ident n hn);
  refine raw_div_less m n hlt
end;

opaque symbol raw_div_geq (n m : τ ι) :
  π (lt empty n) → π (le n m) → π (m ∈ omega) →
  π (raw_div m n = succ (raw_div (diff m n) n)) ≔
begin
  assume n m h0n hle hm;
  have hncond : π (¬ (lt m n ∨ (n = empty))) {
    assume hd;
    refine ∨ₑ hd _ _
    { assume hl; refine le_imp_not_lt m n hle hl }
    { assume he;
      refine not_lt0 empty (ind_eq (eq_sym he) (λ w, lt empty w) h0n) }
  };
  have hmem : π (diff m n ∈ m)
    { refine ltD (diff m n) m (div_termination n m h0n hle hm) };
  rewrite (raw_div_unfold m n);
  rewrite (If_not_P (lt m n ∨ (n = empty)) empty
    (succ (fapply (Lambda m (λ x, raw_div x n)) (diff m n))) hncond);
  rewrite (beta m (λ x, raw_div x n) (diff m n) hmem);
  reflexivity
end;

opaque symbol div_geq (n m : τ ι) :
  π (lt empty n) → π (le n m) → π (m ∈ omega) →
  π (div m n = succ (div (diff m n) n)) ≔
begin
  assume n m h0n hle hm;
  have hn : π (n ∈ omega) { refine le_in_nat n m hle hm };
  rewrite (div_def m n);
  rewrite (natify_ident m hm); rewrite (natify_ident n hn);
  rewrite (div_def (diff m n) n);
  rewrite (natify_ident (diff m n) (diff_type m n));
  rewrite (natify_ident n hn);
  refine raw_div_geq n m h0n hle hm
end;

// A key result
opaque symbol mod_div_lemma (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (add (mult (div m n) n) (mod m n) = m) ≔
begin
  assume m n hm hn;
  refine ∨ₑ (em (n = empty)) _ _
  { assume heq; rewrite heq;
    rewrite (DIVISION_BY_ZERO_DIV m);
    rewrite (DIVISION_BY_ZERO_MOD m);
    rewrite (mult_0 empty);
    rewrite (add_0_natify (natify m));
    rewrite (natify_idem m);
    refine natify_ident m hm }
  { assume hne;
    have h0n : π (lt empty n) { refine Ord_0_lt n (nat_into_Ord n hn) hne };
    refine complete_induct_rule m (λ z, add (mult (div z n) n) (mod z n) = z) hm _;
    assume x hx hIH;
    refine ∨ₑ (em (lt x n)) _ _
    { assume hxn;
      rewrite (div_less x n hxn hn); rewrite (mult_0 n);
      rewrite (mod_less x n hxn hn);
      refine add_0 x hx }
    { assume hnlt;
      have hnx : π (le n x)
        { refine not_lt_imp_le x n (nat_into_Ord x hx) (nat_into_Ord n hn) hnlt };
      have hmem : π (diff x n ∈ x)
        { refine ltD (diff x n) x (div_termination n x h0n hnx hx) };
      have hIHy : π (add (mult (div (diff x n) n) n) (mod (diff x n) n) = diff x n)
        { refine hIH (diff x n) hmem };
      rewrite (div_geq n x h0n hnx hx);
      rewrite (mod_geq n x hnx hx);
      rewrite (mult_succ (div (diff x n) n) n);
      rewrite (add_assoc n (mult (div (diff x n) n) n) (mod (diff x n) n));
      rewrite hIHy;
      refine add_diff_inverse n x hnx hx } }
end;

opaque symbol mod_div_equality_natify (m n : τ ι) :
  π (add (mult (div m n) n) (mod m n) = natify m) ≔
begin
  assume m n;
  rewrite left (div_natify1 m n);
  rewrite left (div_natify2 (natify m) n);
  rewrite left (mult_natify2 (div (natify m) (natify n)) n);
  rewrite left (mod_natify1 m n);
  rewrite left (mod_natify2 (natify m) n);
  refine mod_div_lemma (natify m) (natify n) (natify_in_nat m) (natify_in_nat n)
end;

opaque symbol mod_div_equality (m n : τ ι) :
  π (m ∈ omega) → π (add (mult (div m n) n) (mod m n) = m) ≔
begin
  assume m n hm;
  refine eq_trans (mod_div_equality_natify m n) (natify_ident m hm)
end;

// ===========================================================================
// Further Facts about Remainder
// ===========================================================================

// (mainly for mutilated chess board)
opaque symbol mod_succ_lemma (n m : τ ι) :
  π (lt empty n) → π (m ∈ omega) → π (n ∈ omega) →
  π (mod (succ m) n = If (succ (mod m n) = n) empty (succ (mod m n))) ≔
begin
  assume n m h0n hm hn;
  refine complete_induct_rule m
    (λ z, mod (succ z) n = If (succ (mod z n) = n) empty (succ (mod z n))) hm _;
  assume x hx hIH;
  have hOx : π (Ord x) { refine nat_into_Ord x hx };
  have hsx : π (succ x ∈ omega) { refine succ_in_omega x hx };
  refine ∨ₑ (em (lt (succ x) n)) _ _
  { assume hA;
    have hxn : π (lt x n) { refine lt_trans x (succ x) n (lt_succ x hOx) hA };
    rewrite (mod_less (succ x) n hA hn);
    rewrite (mod_less x n hxn hn);
    have hne : π (¬ (succ x = n))
      { assume he;
        refine mem_irrefl n (ind_eq (eq_sym he) (λ w, w ∈ n) (ltD (succ x) n hA)) };
    rewrite (If_not_P (succ x = n) empty (succ x) hne);
    reflexivity }
  { assume hnlt;
    have hB : π (le n (succ x))
      { refine not_lt_imp_le (succ x) n (nat_into_Ord (succ x) hsx) (nat_into_Ord n hn) hnlt };
    refine ∨ₑ (leE n (succ x) hB) _ _
    { assume hmem;
      have hle_nx : π (le n x) { refine ltI n (succ x) hmem (Ord_succ x hOx) };
      have hd : π (diff x n ∈ x)
        { refine ltD (diff x n) x (div_termination n x h0n hle_nx hx) };
      rewrite (mod_geq n (succ x) hB hsx);
      rewrite (diff_succ n x hle_nx hx);
      rewrite (mod_geq n x hle_nx hx);
      refine hIH (diff x n) hd }
    { assume heq;
      rewrite heq;
      have hOsx : π (Ord (succ x)) { refine Ord_succ x hOx };
      have hxsx : π (lt x (succ x)) { refine lt_succ x hOx };
      have h0sx : π (lt empty (succ x)) { refine Ord_0_lt (succ x) hOsx (succ_neq_0 x) };
      rewrite (mod_geq (succ x) (succ x) (le_refl (succ x) hOsx) hsx);
      rewrite (diff_self_eq_0 (succ x));
      rewrite (mod_less empty (succ x) h0sx hsx);
      rewrite (mod_less x (succ x) hxsx hsx);
      rewrite (If_P (succ x = succ x) empty (succ x) (eq_refl (succ x)));
      reflexivity } }
end;

opaque symbol mod_succ (n m : τ ι) :
  π (n ∈ omega) →
  π (mod (succ m) n = If (succ (mod m n) = n) empty (succ (mod m n))) ≔
begin
  assume n m hn;
  refine ∨ₑ (em (n = empty)) _ _
  { assume heq; rewrite heq;
    rewrite (DIVISION_BY_ZERO_MOD (succ m));
    rewrite (DIVISION_BY_ZERO_MOD m);
    rewrite (natify_succ m);
    rewrite (If_not_P (succ (natify m) = empty) empty (succ (natify m))
      (succ_neq_0 (natify m)));
    reflexivity }
  { assume hne;
    have h0n : π (lt empty n) { refine Ord_0_lt n (nat_into_Ord n hn) hne };
    rewrite left (mod_natify1 m n);
    rewrite left (mod_natify1 (succ m) n);
    rewrite (natify_succ m);
    refine mod_succ_lemma n (natify m) h0n (natify_in_nat m) hn }
end;

opaque symbol mod_less_divisor (n m : τ ι) :
  π (lt empty n) → π (n ∈ omega) → π (lt (mod m n) n) ≔
begin
  assume n m h0n hn;
  have hkey : π (lt (mod (natify m) n) n) {
    refine complete_induct_rule (natify m) (λ z, lt (mod z n) n) (natify_in_nat m) _;
    assume x hx hIH;
    refine ∨ₑ (em (lt x n)) _ _
    { assume hxn; rewrite (mod_less x n hxn hn); refine hxn }
    { assume hnlt;
      have hnx : π (le n x)
        { refine not_lt_imp_le x n (nat_into_Ord x hx) (nat_into_Ord n hn) hnlt };
      have hmem : π (diff x n ∈ x)
        { refine ltD (diff x n) x (div_termination n x h0n hnx hx) };
      rewrite (mod_geq n x hnx hx);
      refine hIH (diff x n) hmem }
  };
  rewrite left (mod_natify1 m n);
  refine hkey
end;

opaque symbol mod_1_eq (m : τ ι) : π (mod m (succ empty) = empty) ≔
begin
  assume m;
  have h : π (lt (mod m (succ empty)) (succ empty))
    { refine mod_less_divisor (succ empty) m (lt_succ empty Ord_0) nat_1I };
  refine ∨ₑ (leE (mod m (succ empty)) empty h) _ _
  { assume hmem; refine ⊥ₑ (emptyE (mod m (succ empty)) hmem) }
  { assume heq; refine heq }
end;

opaque symbol mod2_cases (b k : τ ι) :
  π (lt b (succ (succ empty))) →
  π (mod k (succ (succ empty)) = b ∨
     mod k (succ (succ empty)) = If (b = succ empty) empty (succ empty)) ≔
begin
  assume b k hb;
  have h02 : π (lt empty (succ (succ empty)))
    { refine Ord_0_lt (succ (succ empty))
        (nat_into_Ord (succ (succ empty)) nat_2I) (succ_neq_0 (succ empty)) };
  have hmem : π (mod k (succ (succ empty)) ∈ succ (succ empty))
    { refine ltD (mod k (succ (succ empty))) (succ (succ empty))
        (mod_less_divisor (succ (succ empty)) k h02 nat_2I) };
  have hcases : π ((mod k (succ (succ empty)) = empty)
                   ∨ (mod k (succ (succ empty)) = succ empty)) {
    refine ∨ₑ (∧ₑ₁ (succ_iff (mod k (succ (succ empty))) (succ empty)) hmem) _ _
    { assume h1; refine ∨ᵢ₂ h1 }
    { assume h0;
      refine ∨ₑ (∧ₑ₁ (succ_iff (mod k (succ (succ empty))) empty) h0) _ _
      { assume he; refine ∨ᵢ₁ he }
      { assume habs; refine ⊥ₑ (emptyE (mod k (succ (succ empty))) habs) } }
  };
  have hbmem : π (b ∈ succ (succ empty))
    { refine ltD b (succ (succ empty)) hb };
  have hbcases : π ((b = empty) ∨ (b = succ empty)) {
    refine ∨ₑ (∧ₑ₁ (succ_iff b (succ empty)) hbmem) _ _
    { assume h1; refine ∨ᵢ₂ h1 }
    { assume h0;
      refine ∨ₑ (∧ₑ₁ (succ_iff b empty) h0) _ _
      { assume he; refine ∨ᵢ₁ he }
      { assume habs; refine ⊥ₑ (emptyE b habs) } }
  };
  refine ∨ₑ hbcases _ _
  { assume hb0; rewrite hb0;
    have hcond : π (¬ (empty = succ empty))
      { assume he; refine succ_neq_0 empty (eq_sym he) };
    rewrite (If_not_P (empty = succ empty) empty (succ empty) hcond);
    refine hcases }
  { assume hb1; rewrite hb1;
    rewrite (If_P (succ empty = succ empty) empty (succ empty) (eq_refl (succ empty)));
    refine ∨ₑ hcases _ _
    { assume h; refine ∨ᵢ₂ h }
    { assume h; refine ∨ᵢ₁ h } }
end;

opaque symbol mod2_succ_succ (m : τ ι) :
  π (mod (succ (succ m)) (succ (succ empty)) = mod m (succ (succ empty))) ≔
begin
  assume m;
  have h02 : π (lt empty (succ (succ empty)))
    { refine Ord_0_lt (succ (succ empty))
        (nat_into_Ord (succ (succ empty)) nat_2I) (succ_neq_0 (succ empty)) };
  have hmem : π (mod m (succ (succ empty)) ∈ succ (succ empty))
    { refine ltD (mod m (succ (succ empty))) (succ (succ empty))
        (mod_less_divisor (succ (succ empty)) m h02 nat_2I) };
  have hcases : π ((mod m (succ (succ empty)) = empty)
                   ∨ (mod m (succ (succ empty)) = succ empty)) {
    refine ∨ₑ (∧ₑ₁ (succ_iff (mod m (succ (succ empty))) (succ empty)) hmem) _ _
    { assume h1; refine ∨ᵢ₂ h1 }
    { assume h0;
      refine ∨ₑ (∧ₑ₁ (succ_iff (mod m (succ (succ empty))) empty) h0) _ _
      { assume he; refine ∨ᵢ₁ he }
      { assume habs; refine ⊥ₑ (emptyE (mod m (succ (succ empty))) habs) } }
  };
  have h1ne2 : π (¬ (succ empty = succ (succ empty)))
    { assume he;
      refine succ_neq_0 empty (eq_sym (succ_inject empty (succ empty) he)) };
  rewrite (mod_succ (succ (succ empty)) (succ m) nat_2I);
  rewrite (mod_succ (succ (succ empty)) m nat_2I);
  refine ∨ₑ hcases _ _
  { assume h0; rewrite h0;
    rewrite (If_not_P (succ empty = succ (succ empty)) empty (succ empty) h1ne2);
    rewrite (If_P (succ (succ empty) = succ (succ empty)) empty (succ (succ empty))
      (eq_refl (succ (succ empty))));
    reflexivity }
  { assume h1; rewrite h1;
    rewrite (If_P (succ (succ empty) = succ (succ empty)) empty (succ (succ empty))
      (eq_refl (succ (succ empty))));
    rewrite (If_not_P (succ empty = succ (succ empty)) empty (succ empty) h1ne2);
    reflexivity }
end;

opaque symbol mod2_add_more (m n : τ ι) :
  π (mod (add (add m m) n) (succ (succ empty)) = mod n (succ (succ empty))) ≔
begin
  assume m n;
  have hkey : π (Ball omega
      (λ c, mod (add (add c c) n) (succ (succ empty)) = mod n (succ (succ empty)))) {
    refine nat_induct
      (λ c, mod (add (add c c) n) (succ (succ empty)) = mod n (succ (succ empty))) _ _
    { simplify rule off;
      rewrite (add_0_natify empty); rewrite natify_0;
      rewrite (add_0_natify n);
      rewrite (mod_natify1 n (succ (succ empty)));
      reflexivity }
    { assume c hc hIH;
      rewrite (add_succ c (succ c));
      rewrite (add_succ_right c c);
      rewrite (add_succ (succ (add c c)) n);
      rewrite (add_succ (add c c) n);
      rewrite (mod2_succ_succ (add (add c c) n));
      refine hIH }
  };
  rewrite left (add_natify1 m m);
  rewrite left (add_natify2 (natify m) m);
  refine bspec omega
    (λ c, mod (add (add c c) n) (succ (succ empty)) = mod n (succ (succ empty)))
    (natify m) hkey (natify_in_nat m)
end;

opaque symbol mod2_add_self (m : τ ι) :
  π (mod (add m m) (succ (succ empty)) = empty) ≔
begin
  assume m;
  have h02 : π (lt empty (succ (succ empty)))
    { refine Ord_0_lt (succ (succ empty))
        (nat_into_Ord (succ (succ empty)) nat_2I) (succ_neq_0 (succ empty)) };
  have h3 : π (add (add m m) empty = add m m)
    { refine eq_trans (add_0_right_natify (add m m)) (natify_ident (add m m) (add_type m m)) };
  rewrite left h3;
  rewrite (mod2_add_more m empty);
  refine mod_less empty (succ (succ empty)) h02 nat_2I
end;

// ===========================================================================
// Additional theorems about ≤
// ===========================================================================

opaque symbol add_le_self (m n : τ ι) : π (m ∈ omega) → π (le m (add m n)) ≔
begin
  assume m n hm;
  rewrite (add_commute m n);
  rewrite left (add_natify1 n m);
  refine ind_eq (eq_sym (add_0 m hm)) (λ w, le w (add (natify n) m))
    (add_le_mono1 empty (natify n) m
      (Ord_0_le (natify n) (nat_into_Ord (natify n) (natify_in_nat n)))
      (natify_in_nat n))
end;

opaque symbol add_le_self2 (m n : τ ι) : π (m ∈ omega) → π (le m (add n m)) ≔
begin
  assume m n hm;
  rewrite (add_commute n m);
  refine add_le_self m n hm
end;

// *** Monotonicity of Multiplication ***

opaque symbol mult_le_mono1 (i j k : τ ι) :
  π (le i j) → π (j ∈ omega) → π (le (mult i k) (mult j k)) ≔
begin
  assume i j k hij hj;
  have hkey : π (Ball omega (λ c, le (mult i c) (mult j c))) {
    refine nat_induct (λ c, le (mult i c) (mult j c)) _ _
    { simplify rule off;
      rewrite (mult_0_right i); rewrite (mult_0_right j);
      refine le_refl empty Ord_0 }
    { assume c hc hIH;
      rewrite (mult_succ_right i c); rewrite (mult_succ_right j c);
      refine add_le_mono i j (mult i c) (mult j c) hij hIH hj (mult_type j c) }
  };
  rewrite left (mult_natify2 i k);
  rewrite left (mult_natify2 j k);
  refine bspec omega (λ c, le (mult i c) (mult j c)) (natify k) hkey (natify_in_nat k)
end;

// ≤ monotonicity, BOTH arguments
opaque symbol mult_le_mono (i j k l : τ ι) :
  π (le i j) → π (le k l) → π (j ∈ omega) → π (l ∈ omega) →
  π (le (mult i k) (mult j l)) ≔
begin
  assume i j k l hij hkl hj hl;
  refine le_trans (mult i k) (mult j k) (mult j l)
    (mult_le_mono1 i j k hij hj) _;
  rewrite (mult_commute j k); rewrite (mult_commute j l);
  refine mult_le_mono1 k l j hkl hl
end;

// strict, in 1st argument; proof is by induction on k>0.
opaque symbol mult_lt_mono2 (i j k : τ ι) :
  π (lt i j) → π (lt empty k) → π (j ∈ omega) → π (k ∈ omega) →
  π (lt (mult k i) (mult k j)) ≔
begin
  assume i j k hij h0k hj hk;
  have hi : π (i ∈ omega) { refine lt_nat_in_nat i j hij hj };
  have hkey : π (Ball omega (λ c, lt (mult (succ c) i) (mult (succ c) j))) {
    refine nat_induct (λ c, lt (mult (succ c) i) (mult (succ c) j)) _ _
    { simplify rule off;
      rewrite (mult_1_natify i); rewrite (mult_1_natify j);
      rewrite (natify_ident i hi); rewrite (natify_ident j hj);
      refine hij }
    { assume c hc hIH;
      rewrite (mult_succ (succ c) i); rewrite (mult_succ (succ c) j);
      refine add_lt_mono i j (mult (succ c) i) (mult (succ c) j)
        hij hIH hj (mult_type (succ c) j) }
  };
  refine bexE omega (λ x, k = succ x) (lt (mult k i) (mult k j))
    (zero_lt_lemma k h0k hk) _;
  assume x hx heq;
  rewrite heq;
  refine bspec omega (λ c, lt (mult (succ c) i) (mult (succ c) j)) x hkey hx
end;

opaque symbol mult_lt_mono1 (i j k : τ ι) :
  π (lt i j) → π (lt empty k) → π (j ∈ omega) → π (k ∈ omega) →
  π (lt (mult i k) (mult j k)) ≔
begin
  assume i j k hij h0k hj hk;
  rewrite (mult_commute i k); rewrite (mult_commute j k);
  refine mult_lt_mono2 i j k hij h0k hj hk
end;

opaque symbol add_eq_0_iff (m n : τ ι) :
  π (add m n = empty ⇔ (natify m = empty ∧ natify n = empty)) ≔
begin
  assume m n;
  rewrite left (add_natify1 m n);
  rewrite left (add_natify2 (natify m) n);
  refine natE (natify m) _ (natify_in_nat m) _ _
  { assume heqm; rewrite heqm;
    rewrite (add_0_natify (natify n)); rewrite (natify_idem n);
    refine ∧ᵢ _ _
    { assume h; refine ∧ᵢ (eq_refl empty) h }
    { assume h; refine ∧ₑ₂ h } }
  { assume x hx heqm; rewrite heqm;
    rewrite (add_succ x (natify n));
    refine ∧ᵢ _ _
    { assume h; refine ⊥ₑ (succ_neq_0 (add x (natify n)) h) }
    { assume h; refine ⊥ₑ (succ_neq_0 x (∧ₑ₁ h)) } }
end;

opaque symbol zero_lt_mult_iff (m n : τ ι) :
  π (lt empty (mult m n) ⇔ (lt empty (natify m) ∧ lt empty (natify n))) ≔
begin
  assume m n;
  rewrite left (mult_natify1 m n);
  rewrite left (mult_natify2 (natify m) n);
  refine natE (natify m) _ (natify_in_nat m) _ _
  { assume heqm; rewrite heqm;
    rewrite (mult_0 (natify n));
    refine ∧ᵢ _ _
    { assume h; refine ⊥ₑ (not_lt0 empty h) }
    { assume h; refine ⊥ₑ (not_lt0 empty (∧ₑ₁ h)) } }
  { assume x hx heqm; rewrite heqm;
    refine natE (natify n) _ (natify_in_nat n) _ _
    { assume heqn; rewrite heqn;
      rewrite (mult_0_right (succ x));
      refine ∧ᵢ _ _
      { assume h; refine ⊥ₑ (not_lt0 empty h) }
      { assume h; refine ⊥ₑ (not_lt0 empty (∧ₑ₂ h)) } }
    { assume y hy heqn; rewrite heqn;
      rewrite (mult_succ x (succ y));
      rewrite (add_succ y (mult x (succ y)));
      refine ∧ᵢ _ _
      { assume h;
        refine ∧ᵢ
          (Ord_0_lt (succ x) (nat_into_Ord (succ x) (succ_in_omega x hx)) (succ_neq_0 x))
          (Ord_0_lt (succ y) (nat_into_Ord (succ y) (succ_in_omega y hy)) (succ_neq_0 y)) }
      { assume h;
        have hz : π (succ (add y (mult x (succ y))) ∈ omega)
          { refine succ_in_omega (add y (mult x (succ y))) (add_type y (mult x (succ y))) };
        refine Ord_0_lt (succ (add y (mult x (succ y))))
          (nat_into_Ord (succ (add y (mult x (succ y)))) hz)
          (succ_neq_0 (add y (mult x (succ y)))) } } }
end;

opaque symbol mult_eq_1_iff (m n : τ ι) :
  π (mult m n = succ empty ⇔ (natify m = succ empty ∧ natify n = succ empty)) ≔
begin
  assume m n;
  rewrite left (mult_natify1 m n);
  rewrite left (mult_natify2 (natify m) n);
  refine natE (natify m) _ (natify_in_nat m) _ _
  { assume heqm; rewrite heqm;
    rewrite (mult_0 (natify n));
    refine ∧ᵢ _ _
    { assume h; refine ⊥ₑ (succ_neq_0 empty (eq_sym h)) }
    { assume h; refine ⊥ₑ (succ_neq_0 empty (eq_sym (∧ₑ₁ h))) } }
  { assume x hx heqm; rewrite heqm;
    refine natE (natify n) _ (natify_in_nat n) _ _
    { assume heqn; rewrite heqn;
      rewrite (mult_0_right (succ x));
      refine ∧ᵢ _ _
      { assume h; refine ⊥ₑ (succ_neq_0 empty (eq_sym h)) }
      { assume h; refine ⊥ₑ (succ_neq_0 empty (eq_sym (∧ₑ₂ h))) } }
    { assume y hy heqn; rewrite heqn;
      rewrite (mult_succ x (succ y));
      rewrite (add_succ y (mult x (succ y)));
      refine ∧ᵢ _ _
      { assume h;
        have hA : π (add y (mult x (succ y)) = empty)
          { refine succ_inject (add y (mult x (succ y))) empty h };
        have hy0 : π (y = empty)
          { refine eq_trans (eq_sym (natify_ident y hy))
              (∧ₑ₁ (∧ₑ₁ (add_eq_0_iff y (mult x (succ y))) hA)) };
        have hxs0 : π (mult x (succ y) = empty)
          { refine eq_trans (eq_sym (natify_ident (mult x (succ y)) (mult_type x (succ y))))
              (∧ₑ₂ (∧ₑ₁ (add_eq_0_iff y (mult x (succ y))) hA)) };
        have hx1 : π (mult x (succ empty) = empty)
          { refine ind_eq (eq_sym hy0) (λ w, mult x (succ w) = empty) hxs0 };
        have hx0 : π (x = empty)
          { refine eq_trans (eq_sym (natify_ident x hx))
              (eq_trans (eq_sym (mult_1_right_natify x)) hx1) };
        refine ∧ᵢ (feq succ hx0) (feq succ hy0) }
      { assume h;
        have hx0 : π (x = empty) { refine succ_inject x empty (∧ₑ₁ h) };
        have hy0 : π (y = empty) { refine succ_inject y empty (∧ₑ₂ h) };
        rewrite hx0; rewrite hy0;
        rewrite (mult_0 (succ empty));
        rewrite (add_0_right_natify empty); rewrite natify_0;
        reflexivity } } }
end;

opaque symbol mult_is_zero (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) →
  π (mult m n = empty ⇔ (m = empty ∨ n = empty)) ≔
begin
  assume m n hm hn;
  refine ∧ᵢ _ _
  { assume h;
    refine natE m _ hm _ _
    { assume heqm; refine ∨ᵢ₁ heqm }
    { assume x hx heqm;
      refine natE n _ hn _ _
      { assume heqn; refine ∨ᵢ₂ heqn }
      { assume y hy heqn;
        refine ⊥ₑ _;
        have h2 : π (mult (succ x) (succ y) = empty)
          { refine ind_eq (eq_sym heqm) (λ w, mult w (succ y) = empty)
              (ind_eq (eq_sym heqn) (λ w, mult m w = empty) h) };
        have h3 : π (succ (add y (mult x (succ y))) = empty)
          { refine eq_trans (eq_sym (add_succ y (mult x (succ y))))
              (eq_trans (eq_sym (mult_succ x (succ y))) h2) };
        refine succ_neq_0 (add y (mult x (succ y))) h3 } } }
  { assume h;
    refine ∨ₑ h _ _
    { assume heqm; rewrite heqm; refine mult_0 n }
    { assume heqn; rewrite heqn; refine mult_0_right m } }
end;

opaque symbol mult_is_zero_natify (m n : τ ι) :
  π (mult m n = empty ⇔ (natify m = empty ∨ natify n = empty)) ≔
begin
  assume m n;
  rewrite left (mult_natify1 m n);
  rewrite left (mult_natify2 (natify m) n);
  refine mult_is_zero (natify m) (natify n) (natify_in_nat m) (natify_in_nat n)
end;

// ===========================================================================
// Cancellation Laws for Common Factors in Comparisons
// ===========================================================================

opaque symbol mult_less_cancel_lemma (k m n : τ ι) :
  π (k ∈ omega) → π (m ∈ omega) → π (n ∈ omega) →
  π (lt (mult m k) (mult n k) ⇔ (lt empty k ∧ lt m n)) ≔
begin
  assume k m n hk hm hn;
  refine ∧ᵢ _ _
  { assume h;
    have h0k : π (lt empty k) {
      refine Ord_0_lt k (nat_into_Ord k hk) _;
      assume he;
      have h1 : π (lt (mult m empty) (mult n empty))
        { refine ind_eq (eq_sym he) (λ w, lt (mult m w) (mult n w)) h };
      have h2 : π (lt empty (mult n empty))
        { refine ind_eq (eq_sym (mult_0_right m)) (λ w, lt w (mult n empty)) h1 };
      refine not_lt0 empty (ind_eq (eq_sym (mult_0_right n)) (λ w, lt empty w) h2) };
    refine ∧ᵢ h0k _;
    refine ∨ₑ (Ord_linear m n (nat_into_Ord m hm) (nat_into_Ord n hn)) _ _
    { assume hmn; refine ltI m n hmn (nat_into_Ord n hn) }
    { assume hd;
      refine ∨ₑ hd _ _
      { assume heq;
        refine ⊥ₑ (lt_not_refl (mult n k)
          (ind_eq (eq_sym (feq (λ w, mult w k) heq)) (λ w, lt w (mult n k)) h)) }
      { assume hnm;
        have hle : π (le (mult n k) (mult m k))
          { refine mult_le_mono1 n m k (leI n m hnm (nat_into_Ord m hm)) hm };
        refine ⊥ₑ (le_imp_not_lt (mult m k) (mult n k) hle h) } } }
  { assume h;
    refine mult_lt_mono1 m n k (∧ₑ₂ h) (∧ₑ₁ h) hn hk }
end;

opaque symbol mult_less_cancel2 (m k n : τ ι) :
  π (lt (mult m k) (mult n k) ⇔ (lt empty (natify k) ∧ lt (natify m) (natify n))) ≔
begin
  assume m k n;
  rewrite left (mult_natify1 m k);
  rewrite left (mult_natify2 (natify m) k);
  rewrite left (mult_natify1 n k);
  rewrite left (mult_natify2 (natify n) k);
  refine mult_less_cancel_lemma (natify k) (natify m) (natify n)
    (natify_in_nat k) (natify_in_nat m) (natify_in_nat n)
end;

opaque symbol mult_less_cancel1 (k m n : τ ι) :
  π (lt (mult k m) (mult k n) ⇔ (lt empty (natify k) ∧ lt (natify m) (natify n))) ≔
begin
  assume k m n;
  rewrite (mult_commute k m); rewrite (mult_commute k n);
  refine mult_less_cancel2 m k n
end;

opaque symbol mult_le_cancel2 (m k n : τ ι) :
  π (le (mult m k) (mult n k) ⇔ (lt empty (natify k) ⇒ le (natify m) (natify n))) ≔
begin
  assume m k n;
  refine ∧ᵢ _ _
  { assume h h0k;
    refine not_lt_imp_le (natify n) (natify m)
      (nat_into_Ord (natify n) (natify_in_nat n))
      (nat_into_Ord (natify m) (natify_in_nat m)) _;
    assume hlt;
    have hcontra : π (lt (mult n k) (mult m k))
      { refine ∧ₑ₂ (mult_less_cancel2 n k m) (∧ᵢ h0k hlt) };
    refine le_imp_not_lt (mult n k) (mult m k) h hcontra }
  { assume h;
    refine ∨ₑ (em (lt empty (natify k))) _ _
    { assume h0k;
      have hmn : π (le (natify m) (natify n)) { refine h h0k };
      rewrite left (mult_natify1 m k);
      rewrite left (mult_natify1 n k);
      refine mult_le_mono1 (natify m) (natify n) k hmn (natify_in_nat n) }
    { assume hn0lt;
      have hle0 : π (le (natify k) empty)
        { refine not_lt_imp_le empty (natify k) Ord_0
            (nat_into_Ord (natify k) (natify_in_nat k)) hn0lt };
      have hk0 : π (natify k = empty) {
        refine ∨ₑ (leE (natify k) empty hle0) _ _
        { assume hmem; refine ⊥ₑ (emptyE (natify k) hmem) }
        { assume heq; refine heq } };
      rewrite left (mult_natify2 m k);
      rewrite left (mult_natify2 n k);
      rewrite hk0;
      rewrite (mult_0_right m); rewrite (mult_0_right n);
      refine le_refl empty Ord_0 } }
end;

opaque symbol mult_le_cancel1 (k m n : τ ι) :
  π (le (mult k m) (mult k n) ⇔ (lt empty (natify k) ⇒ le (natify m) (natify n))) ≔
begin
  assume k m n;
  rewrite (mult_commute k m); rewrite (mult_commute k n);
  refine mult_le_cancel2 m k n
end;

opaque symbol mult_le_cancel_le1 (k m : τ ι) :
  π (k ∈ omega) →
  π (le (mult k m) k ⇔ (lt empty k ⇒ le (natify m) (succ empty))) ≔
begin
  assume k m hk;
  have h1 : π (mult k (succ empty) = k)
    { refine eq_trans (mult_1_right_natify k) (natify_ident k hk) };
  have h2 : π (natify (succ empty) = succ empty)
    { refine eq_trans (natify_succ empty) (feq succ natify_0) };
  have hb2 : π (le (mult k m) k ⇔ (lt empty (natify k) ⇒ le (natify m) (natify (succ empty))))
    { refine ind_eq (eq_sym h1)
        (λ w, le (mult k m) w ⇔ (lt empty (natify k) ⇒ le (natify m) (natify (succ empty))))
        (mult_le_cancel1 k m (succ empty)) };
  have hb3 : π (le (mult k m) k ⇔ (lt empty (natify k) ⇒ le (natify m) (succ empty)))
    { refine ind_eq (eq_sym h2)
        (λ w, le (mult k m) k ⇔ (lt empty (natify k) ⇒ le (natify m) w)) hb2 };
  refine ind_eq (eq_sym (natify_ident k hk))
    (λ w, le (mult k m) k ⇔ (lt empty w ⇒ le (natify m) (succ empty))) hb3
end;

opaque symbol Ord_eq_iff_le (m n : τ ι) :
  π (Ord m) → π (Ord n) → π (m = n ⇔ (le m n ∧ le n m)) ≔
begin
  assume m n hOm hOn;
  refine ∧ᵢ _ _
  { assume h; refine ∧ᵢ (le_eqI m n h hOn) (le_eqI n m (eq_sym h) hOm) }
  { assume h; refine le_anti_sym m n (∧ₑ₁ h) (∧ₑ₂ h) }
end;

opaque symbol mult_cancel2_lemma (k m n : τ ι) :
  π (k ∈ omega) → π (m ∈ omega) → π (n ∈ omega) →
  π (mult m k = mult n k ⇔ (m = n ∨ k = empty)) ≔
begin
  assume k m n hk hm hn;
  refine ∧ᵢ _ _
  { assume h;
    refine ∨ₑ (em (k = empty)) _ _
    { assume he; refine ∨ᵢ₂ he }
    { assume hne;
      have h0k : π (lt empty k) { refine Ord_0_lt k (nat_into_Ord k hk) hne };
      refine ∨ᵢ₁ _;
      refine ∨ₑ (Ord_linear m n (nat_into_Ord m hm) (nat_into_Ord n hn)) _ _
      { assume hmn;
        have hlt : π (lt (mult m k) (mult n k))
          { refine mult_lt_mono1 m n k (ltI m n hmn (nat_into_Ord n hn)) h0k hn hk };
        refine ⊥ₑ (lt_not_refl (mult n k)
          (ind_eq (eq_sym h) (λ w, lt w (mult n k)) hlt)) }
      { assume hd;
        refine ∨ₑ hd _ _
        { assume heq; refine heq }
        { assume hnm;
          have hlt : π (lt (mult n k) (mult m k))
            { refine mult_lt_mono1 n m k (ltI n m hnm (nat_into_Ord m hm)) h0k hm hk };
          refine ⊥ₑ (lt_not_refl (mult m k)
            (ind_eq h (λ w, lt w (mult m k)) hlt)) } } } }
  { assume h;
    refine ∨ₑ h _ _
    { assume heq; rewrite heq; reflexivity }
    { assume heq; rewrite heq;
      rewrite (mult_0_right m); rewrite (mult_0_right n); reflexivity } }
end;

opaque symbol mult_cancel2 (m k n : τ ι) :
  π (mult m k = mult n k ⇔ (natify m = natify n ∨ natify k = empty)) ≔
begin
  assume m k n;
  rewrite left (mult_natify1 m k);
  rewrite left (mult_natify2 (natify m) k);
  rewrite left (mult_natify1 n k);
  rewrite left (mult_natify2 (natify n) k);
  refine mult_cancel2_lemma (natify k) (natify m) (natify n)
    (natify_in_nat k) (natify_in_nat m) (natify_in_nat n)
end;

opaque symbol mult_cancel1 (k m n : τ ι) :
  π (mult k m = mult k n ⇔ (natify m = natify n ∨ natify k = empty)) ≔
begin
  assume k m n;
  rewrite (mult_commute k m); rewrite (mult_commute k n);
  refine mult_cancel2 m k n
end;

// ** Cancellation law for division **

opaque symbol div_cancel_raw (n k m : τ ι) :
  π (lt empty n) → π (lt empty k) → π (k ∈ omega) → π (m ∈ omega) → π (n ∈ omega) →
  π (div (mult k m) (mult k n) = div m n) ≔
begin
  assume n k m h0n h0k hk hm hn;
  have hkn : π (mult k n ∈ omega) { refine mult_type k n };
  have h0kn : π (lt empty (mult k n)) {
    refine ∧ₑ₂ (zero_lt_mult_iff k n) (∧ᵢ
      (ind_eq (natify_ident k hk) (λ w, lt empty w) h0k)
      (ind_eq (natify_ident n hn) (λ w, lt empty w) h0n)) };
  refine complete_induct_rule m (λ z, div (mult k z) (mult k n) = div z n) hm _;
  assume x hx hIH;
  refine ∨ₑ (em (lt x n)) _ _
  { assume hxn;
    rewrite (div_less x n hxn hn);
    refine div_less (mult k x) (mult k n)
      (mult_lt_mono2 x n k hxn h0k hn hk) hkn }
  { assume hnlt;
    have hnx : π (le n x)
      { refine not_lt_imp_le x n (nat_into_Ord x hx) (nat_into_Ord n hn) hnlt };
    have hmem : π (diff x n ∈ x)
      { refine ltD (diff x n) x (div_termination n x h0n hnx hx) };
    have hknx : π (le (mult k n) (mult k x))
      { refine mult_le_mono k k n x (le_refl k (nat_into_Ord k hk)) hnx hk hx };
    rewrite (div_geq n x h0n hnx hx);
    rewrite (div_geq (mult k n) (mult k x) h0kn hknx (mult_type k x));
    rewrite left (diff_mult_distrib2 k x n);
    rewrite (hIH (diff x n) hmem);
    reflexivity }
end;

opaque symbol div_cancel (n k m : τ ι) :
  π (lt empty (natify n)) → π (lt empty (natify k)) →
  π (div (mult k m) (mult k n) = div m n) ≔
begin
  assume n k m h0n h0k;
  rewrite left (mult_natify1 k m);
  rewrite left (mult_natify2 (natify k) m);
  rewrite left (mult_natify1 k n);
  rewrite left (mult_natify2 (natify k) n);
  rewrite left (div_natify1 m n);
  rewrite left (div_natify2 (natify m) n);
  refine div_cancel_raw (natify n) (natify k) (natify m) h0n h0k
    (natify_in_nat k) (natify_in_nat m) (natify_in_nat n)
end;

// ===========================================================================
// More Lemmas about Remainder
// ===========================================================================

opaque symbol mult_mod_distrib_raw (k m n : τ ι) :
  π (k ∈ omega) → π (m ∈ omega) → π (n ∈ omega) →
  π (mod (mult k m) (mult k n) = mult k (mod m n)) ≔
begin
  assume k m n hk hm hn;
  refine ∨ₑ (em (k = empty)) _ _
  { assume heq; rewrite heq;
    rewrite (mult_0 m); rewrite (mult_0 n); rewrite (mult_0 (mod m n));
    rewrite (DIVISION_BY_ZERO_MOD empty); refine natify_0 }
  { assume hkne;
    have h0k : π (lt empty k) { refine Ord_0_lt k (nat_into_Ord k hk) hkne };
    refine ∨ₑ (em (n = empty)) _ _
    { assume heq; rewrite heq;
      rewrite (mult_0_right k);
      rewrite (DIVISION_BY_ZERO_MOD (mult k m));
      rewrite (DIVISION_BY_ZERO_MOD m);
      rewrite (natify_ident (mult k m) (mult_type k m));
      rewrite (mult_natify2 k m);
      reflexivity }
    { assume hnne;
      have h0n : π (lt empty n) { refine Ord_0_lt n (nat_into_Ord n hn) hnne };
      have hkn : π (mult k n ∈ omega) { refine mult_type k n };
      have h0kn : π (lt empty (mult k n)) {
        refine ∧ₑ₂ (zero_lt_mult_iff k n) (∧ᵢ
          (ind_eq (natify_ident k hk) (λ w, lt empty w) h0k)
          (ind_eq (natify_ident n hn) (λ w, lt empty w) h0n)) };
      refine complete_induct_rule m (λ z, mod (mult k z) (mult k n) = mult k (mod z n)) hm _;
      assume x hx hIH;
      refine ∨ₑ (em (lt x n)) _ _
      { assume hxn;
        rewrite (mod_less x n hxn hn);
        refine mod_less (mult k x) (mult k n)
          (mult_lt_mono2 x n k hxn h0k hn hk) hkn }
      { assume hnlt;
        have hnx : π (le n x)
          { refine not_lt_imp_le x n (nat_into_Ord x hx) (nat_into_Ord n hn) hnlt };
        have hmem : π (diff x n ∈ x)
          { refine ltD (diff x n) x (div_termination n x h0n hnx hx) };
        have hknx : π (le (mult k n) (mult k x))
          { refine mult_le_mono k k n x (le_refl k (nat_into_Ord k hk)) hnx hk hx };
        rewrite (mod_geq n x hnx hx);
        rewrite (mod_geq (mult k n) (mult k x) hknx (mult_type k x));
        rewrite left (diff_mult_distrib2 k x n);
        refine hIH (diff x n) hmem } } }
end;

opaque symbol mod_mult_distrib2 (k m n : τ ι) :
  π (mult k (mod m n) = mod (mult k m) (mult k n)) ≔
begin
  assume k m n;
  symmetry;
  rewrite left (mult_natify1 k m);
  rewrite left (mult_natify2 (natify k) m);
  rewrite left (mult_natify1 k n);
  rewrite left (mult_natify2 (natify k) n);
  rewrite left (mod_natify1 m n);
  rewrite left (mod_natify2 (natify m) n);
  rewrite left (mult_natify1 k (mod (natify m) (natify n)));
  refine mult_mod_distrib_raw (natify k) (natify m) (natify n)
    (natify_in_nat k) (natify_in_nat m) (natify_in_nat n)
end;

opaque symbol mult_mod_distrib (m n k : τ ι) :
  π (mult (mod m n) k = mod (mult m k) (mult n k)) ≔
begin
  assume m n k;
  rewrite (mult_commute (mod m n) k);
  rewrite (mult_commute m k);
  rewrite (mult_commute n k);
  refine mod_mult_distrib2 k m n
end;

opaque symbol mod_add_self2_raw (n m : τ ι) :
  π (n ∈ omega) → π (mod (add m n) n = mod m n) ≔
begin
  assume n m hn;
  rewrite (add_commute m n);
  rewrite (mod_geq n (add n m) (add_le_self n m hn) (add_type n m));
  rewrite (diff_add_inverse n m);
  refine mod_natify1 m n
end;

opaque symbol mod_add_self2 (m n : τ ι) : π (mod (add m n) n = mod m n) ≔
begin
  assume m n;
  rewrite left (add_natify2 m n);
  rewrite left (mod_natify2 (add m (natify n)) n);
  rewrite left (mod_natify2 m n);
  refine mod_add_self2_raw (natify n) m (natify_in_nat n)
end;

opaque symbol mod_add_self1 (n m : τ ι) : π (mod (add n m) n = mod m n) ≔
begin
  assume n m;
  rewrite (add_commute n m);
  refine mod_add_self2 m n
end;

opaque symbol mod_mult_self1_raw (k m n : τ ι) :
  π (k ∈ omega) → π (mod (add m (mult k n)) n = mod m n) ≔
begin
  assume k m n hk;
  refine bspec omega (λ c, mod (add m (mult c n)) n = mod m n) k _ hk;
  refine nat_induct (λ c, mod (add m (mult c n)) n = mod m n) _ _
  { simplify rule off;
    rewrite (mult_0 n);
    rewrite (add_0_right_natify m);
    refine mod_natify1 m n }
  { assume c hc hIH;
    rewrite (mult_succ c n);
    rewrite (add_left_commute m n (mult c n));
    rewrite (mod_add_self1 n (add m (mult c n)));
    refine hIH }
end;

opaque symbol mod_mult_self1 (m k n : τ ι) :
  π (mod (add m (mult k n)) n = mod m n) ≔
begin
  assume m k n;
  rewrite left (mult_natify1 k n);
  refine mod_mult_self1_raw (natify k) m n (natify_in_nat k)
end;

opaque symbol mod_mult_self2 (m n k : τ ι) :
  π (mod (add m (mult n k)) n = mod m n) ≔
begin
  assume m n k;
  rewrite (mult_commute n k);
  refine mod_mult_self1 m k n
end;

// Lemma for gcd
opaque symbol mult_eq_self_implies_10 (m n : τ ι) :
  π (m = mult m n) → π (natify n = succ empty ∨ m = empty) ≔
begin
  assume m n h;
  have hm : π (m ∈ omega) { refine ind_eq h (λ w, w ∈ omega) (mult_type m n) };
  refine ∨ₑ (em (m = empty)) _ _
  { assume he; refine ∨ᵢ₂ he }
  { assume hmne;
    have h0m : π (lt empty m) { refine Ord_0_lt m (nat_into_Ord m hm) hmne };
    have hOn' : π (Ord (natify n)) { refine nat_into_Ord (natify n) (natify_in_nat n) };
    refine ∨ᵢ₁ _;
    refine ∨ₑ (Ord_linear (natify n) (succ empty) hOn' (nat_into_Ord (succ empty) nat_1I)) _ _
    { assume hlt1;
      have hn0 : π (natify n = empty) {
        refine ∨ₑ (∧ₑ₁ (succ_iff (natify n) empty) hlt1) _ _
        { assume he; refine he }
        { assume habs; refine ⊥ₑ (emptyE (natify n) habs) } };
      refine ⊥ₑ _;
      have h2 : π (m = mult m (natify n))
        { refine eq_trans h (eq_sym (mult_natify2 m n)) };
      have h3 : π (m = empty)
        { refine eq_trans h2 (eq_trans (feq (mult m) hn0) (mult_0_right m)) };
      refine hmne h3 }
    { assume hd;
      refine ∨ₑ hd _ _
      { assume heq; refine heq }
      { assume h1lt;
        refine ⊥ₑ _;
        have hlt : π (lt (mult m (succ empty)) (mult m (natify n)))
          { refine mult_lt_mono2 (succ empty) (natify n) m
              (ltI (succ empty) (natify n) h1lt hOn') h0m (natify_in_nat n) hm };
        have e1 : π (mult m (succ empty) = m)
          { refine eq_trans (mult_1_right_natify m) (natify_ident m hm) };
        have e2 : π (mult m (natify n) = m)
          { refine eq_trans (mult_natify2 m n) (eq_sym h) };
        have ha : π (lt m (mult m (natify n)))
          { refine ind_eq (eq_sym e1) (λ w, lt w (mult m (natify n))) hlt };
        refine lt_not_refl m (ind_eq (eq_sym e2) (λ w, lt m w) ha) } } }
end;

opaque symbol less_imp_succ_add (m n : τ ι) :
  π (lt m n) → π (n ∈ omega) → π (Bex omega (λ k, n = succ (add m k))) ≔
begin
  assume m n hlt hn;
  have hall : π (Ball omega (λ b, lt m b ⇒ Bex omega (λ k, b = succ (add m k)))) {
    refine nat_induct (λ b, lt m b ⇒ Bex omega (λ k, b = succ (add m k))) _ _
    { simplify rule off; assume h; refine ⊥ₑ (not_lt0 m h) }
    { assume b hb hIH hlt2;
      refine ∨ₑ (leE m b hlt2) _ _
      { assume hmem;
        refine bexE omega (λ k, b = succ (add m k)) _
          (hIH (ltI m b hmem (nat_into_Ord b hb))) _;
        assume k hk heqb;
        refine bexI omega (λ k2, succ b = succ (add m k2)) (succ k)
          (feq succ (eq_sym (eq_trans (add_succ_right m k) (eq_sym heqb))))
          (succ_in_omega k hk) }
      { assume heq;
        have hm : π (m ∈ omega) { refine ind_eq heq (λ w, w ∈ omega) hb };
        refine bexI omega (λ k2, succ b = succ (add m k2)) empty
          (feq succ (eq_sym (eq_trans (add_0_right_natify m)
            (eq_trans (natify_ident m hm) heq))))
          zero_in_omega } }
  };
  refine bspec omega (λ b, lt m b ⇒ Bex omega (λ k, b = succ (add m k))) n hall hn hlt
end;

opaque symbol less_iff_succ_add (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) →
  π (lt m n ⇔ Bex omega (λ k, n = succ (add m k))) ≔
begin
  assume m n hm hn;
  refine ∧ᵢ _ _
  { assume h; refine less_imp_succ_add m n h hn }
  { assume h;
    refine bexE omega (λ k, n = succ (add m k)) (lt m n) h _;
    assume k hk heqn;
    rewrite heqn;
    refine add_le_self m k hm }
end;

opaque symbol add_lt_elim2 (a d b c : τ ι) :
  π (add a d = add b c) → π (lt a b) → π (b ∈ omega) → π (c ∈ omega) → π (d ∈ omega) →
  π (lt c d) ≔
begin
  assume a d b c heq hab hb hc hd;
  refine bexE omega (λ k, b = succ (add a k)) (lt c d)
    (less_imp_succ_add a b hab hb) _;
  assume k hk heqb;
  have h2 : π (add a d = add a (succ (add k c))) {
    refine eq_trans heq _;
    rewrite heqb;
    rewrite (add_succ (add a k) c);
    rewrite (add_assoc a k c);
    rewrite (add_succ_right a (add k c));
    reflexivity };
  have h3 : π (natify d = natify (succ (add k c)))
    { refine add_left_cancel_natify a d (succ (add k c)) h2 };
  have h4 : π (d = succ (add k c)) {
    refine eq_trans (eq_sym (natify_ident d hd)) (eq_trans h3 _);
    rewrite (natify_succ (add k c));
    rewrite (natify_ident (add k c) (add_type k c));
    reflexivity };
  rewrite h4;
  refine add_le_self2 c k hc
end;

opaque symbol add_le_elim2 (a d b c : τ ι) :
  π (add a d = add b c) → π (le a b) → π (b ∈ omega) → π (c ∈ omega) → π (d ∈ omega) →
  π (le c d) ≔
begin
  assume a d b c heq hab hb hc hd;
  refine ∨ₑ (leE a b hab) _ _
  { assume hmem;
    have hcd : π (lt c d)
      { refine add_lt_elim2 a d b c heq (ltI a b hmem (nat_into_Ord b hb)) hb hc hd };
    refine leI c d (ltD c d hcd) (nat_into_Ord d hd) }
  { assume heqab;
    have h2 : π (add a d = add a c)
      { refine eq_trans heq (feq (λ w, add w c) (eq_sym heqab)) };
    have h3 : π (natify d = natify c) { refine add_left_cancel_natify a d c h2 };
    have h4 : π (c = d)
      { refine eq_trans (eq_sym (natify_ident c hc))
          (eq_trans (eq_sym h3) (natify_ident d hd)) };
    refine le_eqI c d h4 (nat_into_Ord d hd) }
end;

// ===========================================================================
// More Lemmas About Difference
// ===========================================================================

opaque symbol diff_is_0_lemma (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (diff m n = empty ⇔ le m n) ≔
begin
  assume m n hm hn;
  refine diff_induct m n (λ x y, diff x y = empty ⇔ le x y) hm hn _ _ _
  { assume x hx;
    rewrite (diff_0 x); rewrite (natify_ident x hx);
    refine ∧ᵢ _ _
    { assume h; refine le_eqI x empty h Ord_0 }
    { assume h;
      refine ∨ₑ (leE x empty h) _ _
      { assume hmem; refine ⊥ₑ (emptyE x hmem) }
      { assume heq; refine heq } } }
  { assume y hy;
    rewrite (diff_0_eq_0 (succ y));
    refine ∧ᵢ _ _
    { assume h; refine Ord_0_le (succ y) (Ord_succ y (nat_into_Ord y hy)) }
    { assume h; reflexivity } }
  { assume x y hx hy hIH;
    rewrite (diff_succ_succ x y);
    refine ∧ᵢ _ _
    { assume h;
      refine succ_leI x (succ y) (Ord_succ y (nat_into_Ord y hy))
        (ltD x (succ y) (∧ₑ₁ hIH h)) }
    { assume h; refine ∧ₑ₂ hIH (succ_leE x (succ y) h) } }
end;

opaque symbol diff_is_0_iff (m n : τ ι) :
  π (diff m n = empty ⇔ le (natify m) (natify n)) ≔
begin
  assume m n;
  rewrite left (diff_natify1 m n);
  rewrite left (diff_natify2 (natify m) n);
  refine diff_is_0_lemma (natify m) (natify n) (natify_in_nat m) (natify_in_nat n)
end;

opaque symbol nat_lt_imp_diff_eq_0 (a b : τ ι) :
  π (a ∈ omega) → π (b ∈ omega) → π (lt a b) → π (diff a b = empty) ≔
begin
  assume a b ha hb hab;
  refine ∧ₑ₂ (diff_is_0_lemma a b ha hb)
    (leI a b (ltD a b hab) (nat_into_Ord b hb))
end;

opaque symbol raw_nat_diff_split (a b : τ ι) (P : τ ι → Prop) :
  π (a ∈ omega) → π (b ∈ omega) →
  π (P (diff a b) ⇔ ((lt a b ⇒ P empty) ∧ Ball omega (λ d, a = add b d ⇒ P d))) ≔
begin
  assume a b P ha hb;
  refine ∨ₑ (em (lt a b)) _ _
  { assume hab;
    have hd0 : π (diff a b = empty) { refine nat_lt_imp_diff_eq_0 a b ha hb hab };
    refine ∧ᵢ _ _
    { assume h;
      refine ∧ᵢ _ _
      { assume h2; refine ind_eq (eq_sym hd0) (λ w, P w) h }
      { assume d hd heq;
        have hba : π (le b a)
          { refine ind_eq heq (λ w, le b w) (add_le_self b d hb) };
        refine ⊥ₑ (le_imp_not_lt a b hba hab) } }
    { assume h;
      refine ind_eq hd0 (λ w, P w) (∧ₑ₁ h hab) } }
  { assume hnab;
    have hba : π (le b a)
      { refine not_lt_imp_le a b (nat_into_Ord a ha) (nat_into_Ord b hb) hnab };
    refine ∧ᵢ _ _
    { assume h;
      refine ∧ᵢ _ _
      { assume hab; refine ⊥ₑ (hnab hab) }
      { assume d hd heq;
        have e : π (diff a b = d)
          { refine eq_trans (feq (λ w, diff w b) heq)
              (eq_trans (diff_add_inverse b d) (natify_ident d hd)) };
        refine ind_eq (eq_sym e) (λ w, P w) h } }
    { assume h;
      refine bspec omega (λ d, a = add b d ⇒ P d) (diff a b) (∧ₑ₂ h) (diff_type a b)
        (eq_sym (add_diff_inverse b a hba ha)) } }
end;

opaque symbol nat_diff_split (a b : τ ι) (P : τ ι → Prop) :
  π (P (diff a b) ⇔
     ((lt (natify a) (natify b) ⇒ P empty) ∧
      Ball omega (λ d, natify a = add b d ⇒ P d))) ≔
begin
  assume a b P;
  have hraw : π (P (diff (natify a) (natify b)) ⇔
      ((lt (natify a) (natify b) ⇒ P empty) ∧
       Ball omega (λ d, natify a = add (natify b) d ⇒ P d)))
    { refine raw_nat_diff_split (natify a) (natify b) P (natify_in_nat a) (natify_in_nat b) };
  rewrite left (diff_natify1 a b);
  rewrite left (diff_natify2 (natify a) b);
  refine ∧ᵢ _ _
  { assume h;
    have hc : π ((lt (natify a) (natify b) ⇒ P empty) ∧
                 Ball omega (λ d, natify a = add (natify b) d ⇒ P d))
      { refine ∧ₑ₁ hraw h };
    refine ∧ᵢ (∧ₑ₁ hc) _;
    assume d hd heq;
    refine bspec omega (λ d2, natify a = add (natify b) d2 ⇒ P d2) d (∧ₑ₂ hc) hd
      (eq_trans heq (eq_sym (add_natify1 b d))) }
  { assume h;
    refine ∧ₑ₂ hraw (∧ᵢ (∧ₑ₁ h) _);
    assume d hd heq;
    refine bspec omega (λ d2, natify a = add b d2 ⇒ P d2) d (∧ₑ₂ h) hd
      (eq_trans heq (add_natify1 b d)) }
end;

// Difference and less-than
opaque symbol diff_lt_imp_lt (k i j : τ ι) :
  π (lt (diff k i) (diff k j)) → π (i ∈ omega) → π (j ∈ omega) → π (k ∈ omega) →
  π (lt j i) ≔
begin
  assume k i j h hi hj hk;
  refine ∨ₑ (em (lt k j)) _ _
  { assume hkj;
    refine ⊥ₑ (not_lt0 (diff k i)
      (ind_eq (eq_sym (nat_lt_imp_diff_eq_0 k j hk hj hkj)) (λ w, lt (diff k i) w) h)) }
  { assume hnkj;
    have hjk : π (le j k)
      { refine not_lt_imp_le k j (nat_into_Ord k hk) (nat_into_Ord j hj) hnkj };
    refine ∨ₑ (em (lt k i)) _ _
    { assume hki; refine lt_trans1 j k i hjk hki }
    { assume hnki;
      have hik : π (le i k)
        { refine not_lt_imp_le k i (nat_into_Ord k hk) (nat_into_Ord i hi) hnki };
      refine ∨ₑ (em (lt j i)) _ _
      { assume hji; refine hji }
      { assume hnji;
        have hij : π (le i j)
          { refine not_lt_imp_le j i (nat_into_Ord j hj) (nat_into_Ord i hi) hnji };
        have he : π (add i (diff k i) = add j (diff k j))
          { refine eq_trans (add_diff_inverse i k hik hk)
              (eq_sym (add_diff_inverse j k hjk hk)) };
        have hle : π (le (diff k j) (diff k i))
          { refine add_le_elim2 i (diff k i) j (diff k j) he hij hj
              (diff_type k j) (diff_type k i) };
        refine ⊥ₑ (le_imp_not_lt (diff k i) (diff k j) hle h) } } }
end;

opaque symbol lt_imp_diff_lt (j i k : τ ι) :
  π (lt j i) → π (le i k) → π (k ∈ omega) → π (lt (diff k i) (diff k j)) ≔
begin
  assume j i k hji hik hk;
  have hi : π (i ∈ omega) { refine le_in_nat i k hik hk };
  have hj : π (j ∈ omega) { refine lt_nat_in_nat j i hji hi };
  have hjk : π (le j k)
    { refine leI j k (ltD j k (lt_trans2 j i k hji hik)) (nat_into_Ord k hk) };
  refine ∨ₑ (em (lt (diff k i) (diff k j))) _ _
  { assume h; refine h }
  { assume hnot;
    have hle : π (le (diff k j) (diff k i))
      { refine not_lt_imp_le (diff k i) (diff k j)
          (nat_into_Ord (diff k i) (diff_type k i))
          (nat_into_Ord (diff k j) (diff_type k j)) hnot };
    have he : π (add (diff k j) j = add (diff k i) i)
      { refine eq_trans (add_diff_inverse2 j k hjk hk)
          (eq_sym (add_diff_inverse2 i k hik hk)) };
    have hij : π (le i j)
      { refine add_le_elim2 (diff k j) j (diff k i) i he hle (diff_type k i) hi hj };
    refine ⊥ₑ (le_imp_not_lt j i hij hji) }
end;

opaque symbol diff_lt_iff_lt (i k j : τ ι) :
  π (le i k) → π (j ∈ omega) → π (k ∈ omega) → π (lt (diff k i) (diff k j) ⇔ lt j i) ≔
begin
  assume i k j hik hj hk;
  have hi : π (i ∈ omega) { refine le_in_nat i k hik hk };
  refine ∧ᵢ _ _
  { assume h; refine diff_lt_imp_lt k i j h hi hj hk }
  { assume h; refine lt_imp_diff_lt j i k h hik hk }
end;
