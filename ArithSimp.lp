// ZF.ArithSimp — Arithmetic with simplification
// Faithful SKELETON port of isabelle-src/ArithSimp.thy.
// Every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/ArithSimp.thy.)
//
// The .thy's opening block (simproc setup + a dozen `apply simp oops`
// examples) is ML/demo infrastructure with no proved statement — nothing to
// port there.  `div_rls` is a named bag of *existing* facts (Isabelle
// `lemmas div_rls = ...`), not a fresh statement — likewise skipped.

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func
             ZF.Ordinal ZF.Nat_ZF ZF.Epsilon ZF.Univ ZF.Arith;

// ===========================================================================
// Difference
// ===========================================================================

opaque symbol diff_self_eq_0 (m : τ ι) : π (diff m m = empty) ≔
begin admit end;

// We need m:nat even if we replace the RHS by natify(m), for consider e.g.
// n=2, m=omega; then n + (m-n) = 2 + (0-2) = 2 ≠ 0 = natify(m).
opaque symbol add_diff_inverse (n m : τ ι) :
  π (le n m) → π (m ∈ omega) → π (add n (diff m n) = m) ≔
begin admit end;

opaque symbol add_diff_inverse2 (n m : τ ι) :
  π (le n m) → π (m ∈ omega) → π (add (diff m n) n = m) ≔
begin admit end;

// Proof is IDENTICAL to that of add_diff_inverse
opaque symbol diff_succ (n m : τ ι) :
  π (le n m) → π (m ∈ omega) → π (diff (succ m) n = succ (diff m n)) ≔
begin admit end;

opaque symbol zero_less_diff (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (lt empty (diff n m) ⇔ lt m n) ≔
begin admit end;

// Difference distributes over multiplication
opaque symbol diff_mult_distrib (m n k : τ ι) :
  π (mult (diff m n) k = diff (mult m k) (mult n k)) ≔
begin admit end;

opaque symbol diff_mult_distrib2 (k m n : τ ι) :
  π (mult k (diff m n) = diff (mult k m) (mult k n)) ≔
begin admit end;

// ===========================================================================
// Remainder
// ===========================================================================

// We need m:nat even with natify
opaque symbol div_termination (n m : τ ι) :
  π (lt empty n) → π (le n m) → π (m ∈ omega) → π (lt (diff m n) m) ≔
begin admit end;

opaque symbol raw_mod_type (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (raw_mod m n ∈ omega) ≔
begin admit end;

opaque symbol mod_type (m n : τ ι) : π (mod m n ∈ omega) ≔
begin admit end;

// Arbitrary definitions for division by zero. Useful to simplify certain equations
opaque symbol DIVISION_BY_ZERO_DIV (a : τ ι) : π (div a empty = empty) ≔
begin admit end;

opaque symbol DIVISION_BY_ZERO_MOD (a : τ ι) : π (mod a empty = natify a) ≔
begin admit end;

opaque symbol raw_mod_less (m n : τ ι) : π (lt m n) → π (raw_mod m n = m) ≔
begin admit end;

opaque symbol mod_less (m n : τ ι) : π (lt m n) → π (n ∈ omega) → π (mod m n = m) ≔
begin admit end;

opaque symbol raw_mod_geq (n m : τ ι) :
  π (lt empty n) → π (le n m) → π (m ∈ omega) →
  π (raw_mod m n = raw_mod (diff m n) n) ≔
begin admit end;

opaque symbol mod_geq (n m : τ ι) :
  π (le n m) → π (m ∈ omega) → π (mod m n = mod (diff m n) n) ≔
begin admit end;

// ===========================================================================
// Division
// ===========================================================================

opaque symbol raw_div_type (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (raw_div m n ∈ omega) ≔
begin admit end;

opaque symbol div_type (m n : τ ι) : π (div m n ∈ omega) ≔
begin admit end;

opaque symbol raw_div_less (m n : τ ι) : π (lt m n) → π (raw_div m n = empty) ≔
begin admit end;

opaque symbol div_less (m n : τ ι) : π (lt m n) → π (n ∈ omega) → π (div m n = empty) ≔
begin admit end;

opaque symbol raw_div_geq (n m : τ ι) :
  π (lt empty n) → π (le n m) → π (m ∈ omega) →
  π (raw_div m n = succ (raw_div (diff m n) n)) ≔
begin admit end;

opaque symbol div_geq (n m : τ ι) :
  π (lt empty n) → π (le n m) → π (m ∈ omega) →
  π (div m n = succ (div (diff m n) n)) ≔
begin admit end;

// A key result
opaque symbol mod_div_lemma (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (add (mult (div m n) n) (mod m n) = m) ≔
begin admit end;

opaque symbol mod_div_equality_natify (m n : τ ι) :
  π (add (mult (div m n) n) (mod m n) = natify m) ≔
begin admit end;

opaque symbol mod_div_equality (m n : τ ι) :
  π (m ∈ omega) → π (add (mult (div m n) n) (mod m n) = m) ≔
begin admit end;

// ===========================================================================
// Further Facts about Remainder
// ===========================================================================

// (mainly for mutilated chess board)
opaque symbol mod_succ_lemma (n m : τ ι) :
  π (lt empty n) → π (m ∈ omega) → π (n ∈ omega) →
  π (mod (succ m) n = If (succ (mod m n) = n) empty (succ (mod m n))) ≔
begin admit end;

opaque symbol mod_succ (n m : τ ι) :
  π (n ∈ omega) →
  π (mod (succ m) n = If (succ (mod m n) = n) empty (succ (mod m n))) ≔
begin admit end;

opaque symbol mod_less_divisor (n m : τ ι) :
  π (lt empty n) → π (n ∈ omega) → π (lt (mod m n) n) ≔
begin admit end;

opaque symbol mod_1_eq (m : τ ι) : π (mod m (succ empty) = empty) ≔
begin admit end;

opaque symbol mod2_cases (b k : τ ι) :
  π (lt b (succ (succ empty))) →
  π (mod k (succ (succ empty)) = b ∨
     mod k (succ (succ empty)) = If (b = succ empty) empty (succ empty)) ≔
begin admit end;

opaque symbol mod2_succ_succ (m : τ ι) :
  π (mod (succ (succ m)) (succ (succ empty)) = mod m (succ (succ empty))) ≔
begin admit end;

opaque symbol mod2_add_more (m n : τ ι) :
  π (mod (add (add m m) n) (succ (succ empty)) = mod n (succ (succ empty))) ≔
begin admit end;

opaque symbol mod2_add_self (m : τ ι) :
  π (mod (add m m) (succ (succ empty)) = empty) ≔
begin admit end;

// ===========================================================================
// Additional theorems about ≤
// ===========================================================================

opaque symbol add_le_self (m n : τ ι) : π (m ∈ omega) → π (le m (add m n)) ≔
begin admit end;

opaque symbol add_le_self2 (m n : τ ι) : π (m ∈ omega) → π (le m (add n m)) ≔
begin admit end;

// *** Monotonicity of Multiplication ***

opaque symbol mult_le_mono1 (i j k : τ ι) :
  π (le i j) → π (j ∈ omega) → π (le (mult i k) (mult j k)) ≔
begin admit end;

// ≤ monotonicity, BOTH arguments
opaque symbol mult_le_mono (i j k l : τ ι) :
  π (le i j) → π (le k l) → π (j ∈ omega) → π (l ∈ omega) →
  π (le (mult i k) (mult j l)) ≔
begin admit end;

// strict, in 1st argument; proof is by induction on k>0.
opaque symbol mult_lt_mono2 (i j k : τ ι) :
  π (lt i j) → π (lt empty k) → π (j ∈ omega) → π (k ∈ omega) →
  π (lt (mult k i) (mult k j)) ≔
begin admit end;

opaque symbol mult_lt_mono1 (i j k : τ ι) :
  π (lt i j) → π (lt empty k) → π (j ∈ omega) → π (k ∈ omega) →
  π (lt (mult i k) (mult j k)) ≔
begin admit end;

opaque symbol add_eq_0_iff (m n : τ ι) :
  π (add m n = empty ⇔ (natify m = empty ∧ natify n = empty)) ≔
begin admit end;

opaque symbol zero_lt_mult_iff (m n : τ ι) :
  π (lt empty (mult m n) ⇔ (lt empty (natify m) ∧ lt empty (natify n))) ≔
begin admit end;

opaque symbol mult_eq_1_iff (m n : τ ι) :
  π (mult m n = succ empty ⇔ (natify m = succ empty ∧ natify n = succ empty)) ≔
begin admit end;

opaque symbol mult_is_zero (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) →
  π (mult m n = empty ⇔ (m = empty ∨ n = empty)) ≔
begin admit end;

opaque symbol mult_is_zero_natify (m n : τ ι) :
  π (mult m n = empty ⇔ (natify m = empty ∨ natify n = empty)) ≔
begin admit end;

// ===========================================================================
// Cancellation Laws for Common Factors in Comparisons
// ===========================================================================

opaque symbol mult_less_cancel_lemma (k m n : τ ι) :
  π (k ∈ omega) → π (m ∈ omega) → π (n ∈ omega) →
  π (lt (mult m k) (mult n k) ⇔ (lt empty k ∧ lt m n)) ≔
begin admit end;

opaque symbol mult_less_cancel2 (m k n : τ ι) :
  π (lt (mult m k) (mult n k) ⇔ (lt empty (natify k) ∧ lt (natify m) (natify n))) ≔
begin admit end;

opaque symbol mult_less_cancel1 (k m n : τ ι) :
  π (lt (mult k m) (mult k n) ⇔ (lt empty (natify k) ∧ lt (natify m) (natify n))) ≔
begin admit end;

opaque symbol mult_le_cancel2 (m k n : τ ι) :
  π (le (mult m k) (mult n k) ⇔ (lt empty (natify k) ⇒ le (natify m) (natify n))) ≔
begin admit end;

opaque symbol mult_le_cancel1 (k m n : τ ι) :
  π (le (mult k m) (mult k n) ⇔ (lt empty (natify k) ⇒ le (natify m) (natify n))) ≔
begin admit end;

opaque symbol mult_le_cancel_le1 (k m : τ ι) :
  π (k ∈ omega) →
  π (le (mult k m) k ⇔ (lt empty k ⇒ le (natify m) (succ empty))) ≔
begin admit end;

opaque symbol Ord_eq_iff_le (m n : τ ι) :
  π (Ord m) → π (Ord n) → π (m = n ⇔ (le m n ∧ le n m)) ≔
begin admit end;

opaque symbol mult_cancel2_lemma (k m n : τ ι) :
  π (k ∈ omega) → π (m ∈ omega) → π (n ∈ omega) →
  π (mult m k = mult n k ⇔ (m = n ∨ k = empty)) ≔
begin admit end;

opaque symbol mult_cancel2 (m k n : τ ι) :
  π (mult m k = mult n k ⇔ (natify m = natify n ∨ natify k = empty)) ≔
begin admit end;

opaque symbol mult_cancel1 (k m n : τ ι) :
  π (mult k m = mult k n ⇔ (natify m = natify n ∨ natify k = empty)) ≔
begin admit end;

// ** Cancellation law for division **

opaque symbol div_cancel_raw (n k m : τ ι) :
  π (lt empty n) → π (lt empty k) → π (k ∈ omega) → π (m ∈ omega) → π (n ∈ omega) →
  π (div (mult k m) (mult k n) = div m n) ≔
begin admit end;

opaque symbol div_cancel (n k m : τ ι) :
  π (lt empty (natify n)) → π (lt empty (natify k)) →
  π (div (mult k m) (mult k n) = div m n) ≔
begin admit end;

// ===========================================================================
// More Lemmas about Remainder
// ===========================================================================

opaque symbol mult_mod_distrib_raw (k m n : τ ι) :
  π (k ∈ omega) → π (m ∈ omega) → π (n ∈ omega) →
  π (mod (mult k m) (mult k n) = mult k (mod m n)) ≔
begin admit end;

opaque symbol mod_mult_distrib2 (k m n : τ ι) :
  π (mult k (mod m n) = mod (mult k m) (mult k n)) ≔
begin admit end;

opaque symbol mult_mod_distrib (m n k : τ ι) :
  π (mult (mod m n) k = mod (mult m k) (mult n k)) ≔
begin admit end;

opaque symbol mod_add_self2_raw (n m : τ ι) :
  π (n ∈ omega) → π (mod (add m n) n = mod m n) ≔
begin admit end;

opaque symbol mod_add_self2 (m n : τ ι) : π (mod (add m n) n = mod m n) ≔
begin admit end;

opaque symbol mod_add_self1 (n m : τ ι) : π (mod (add n m) n = mod m n) ≔
begin admit end;

opaque symbol mod_mult_self1_raw (k m n : τ ι) :
  π (k ∈ omega) → π (mod (add m (mult k n)) n = mod m n) ≔
begin admit end;

opaque symbol mod_mult_self1 (m k n : τ ι) :
  π (mod (add m (mult k n)) n = mod m n) ≔
begin admit end;

opaque symbol mod_mult_self2 (m n k : τ ι) :
  π (mod (add m (mult n k)) n = mod m n) ≔
begin admit end;

// Lemma for gcd
opaque symbol mult_eq_self_implies_10 (m n : τ ι) :
  π (m = mult m n) → π (natify n = succ empty ∨ m = empty) ≔
begin admit end;

opaque symbol less_imp_succ_add (m n : τ ι) :
  π (lt m n) → π (n ∈ omega) → π (Bex omega (λ k, n = succ (add m k))) ≔
begin admit end;

opaque symbol less_iff_succ_add (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) →
  π (lt m n ⇔ Bex omega (λ k, n = succ (add m k))) ≔
begin admit end;

opaque symbol add_lt_elim2 (a d b c : τ ι) :
  π (add a d = add b c) → π (lt a b) → π (b ∈ omega) → π (c ∈ omega) → π (d ∈ omega) →
  π (lt c d) ≔
begin admit end;

opaque symbol add_le_elim2 (a d b c : τ ι) :
  π (add a d = add b c) → π (le a b) → π (b ∈ omega) → π (c ∈ omega) → π (d ∈ omega) →
  π (le c d) ≔
begin admit end;

// ===========================================================================
// More Lemmas About Difference
// ===========================================================================

opaque symbol diff_is_0_lemma (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (diff m n = empty ⇔ le m n) ≔
begin admit end;

opaque symbol diff_is_0_iff (m n : τ ι) :
  π (diff m n = empty ⇔ le (natify m) (natify n)) ≔
begin admit end;

opaque symbol nat_lt_imp_diff_eq_0 (a b : τ ι) :
  π (a ∈ omega) → π (b ∈ omega) → π (lt a b) → π (diff a b = empty) ≔
begin admit end;

opaque symbol raw_nat_diff_split (a b : τ ι) (P : τ ι → Prop) :
  π (a ∈ omega) → π (b ∈ omega) →
  π (P (diff a b) ⇔ ((lt a b ⇒ P empty) ∧ Ball omega (λ d, a = add b d ⇒ P d))) ≔
begin admit end;

opaque symbol nat_diff_split (a b : τ ι) (P : τ ι → Prop) :
  π (P (diff a b) ⇔
     ((lt (natify a) (natify b) ⇒ P empty) ∧
      Ball omega (λ d, natify a = add b d ⇒ P d))) ≔
begin admit end;

// Difference and less-than
opaque symbol diff_lt_imp_lt (k i j : τ ι) :
  π (lt (diff k i) (diff k j)) → π (i ∈ omega) → π (j ∈ omega) → π (k ∈ omega) →
  π (lt j i) ≔
begin admit end;

opaque symbol lt_imp_diff_lt (j i k : τ ι) :
  π (lt j i) → π (le i k) → π (k ∈ omega) → π (lt (diff k i) (diff k j)) ≔
begin admit end;

opaque symbol diff_lt_iff_lt (i k j : τ ι) :
  π (le i k) → π (j ∈ omega) → π (k ∈ omega) → π (lt (diff k i) (diff k j) ⇔ lt j i) ≔
begin admit end;
