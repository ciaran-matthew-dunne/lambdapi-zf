// ZF.IntDiv — The Division Operators Div and Mod
// Faithful SKELETON port of isabelle-src/IntDiv.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/IntDiv.thy.)
//
// BOOTSTRAP: posDivAlg/negDivAlg are `wfrec` over `measure(int*int, ...)`
// (already available from OrderArith.lp).  Per Arith.lp's established
// precedent for recursors built on an expensive-to-unfold combinator
// (Vrec/transrec/wfrec all eagerly explode through trancl/eclose during
// kernel conversion), they are declared as ABSTRACT symbols with a
// defining *_def AXIOM rather than a `≔` body — the axiom IS the Isabelle
// definition, faithfully.  `quorem`/`adjust`/`negateSnd`/`divAlg`/`zdiv`/
// `zmod` are non-recursive combinators built from those two, so get plain
// `≔` bodies.  Isabelle's pattern-matching lambdas `λ⟨a,b⟩. ...` are
// unfolded directly via `fst`/`snd` (no polymorphic `split` at Prop-return
// type is available in this port, and `posDivAlg`/`negDivAlg`'s recursor
// step functions need it applied to a plain τι argument, not a Prop one).

require open ZF.Bin ZF.OrderArith;

// ===========================================================================
// quorem, adjust
// ===========================================================================

// quorem(<a,b>,<q,r>) ≡
//   a = b$*q $+ r ∧ (#0$<b ∧ #0$≤r ∧ r$<b | ¬(#0$<b) ∧ b$<r ∧ r$≤#0)
symbol quorem (ab qr : τ ι) : Prop ≔
  fst ab = zadd (zmult (snd ab) (fst qr)) (snd qr) ∧
  ((zless Int0 (snd ab) ∧ zle Int0 (snd qr) ∧ zless (snd qr) (snd ab)) ∨
   (¬ (zless Int0 (snd ab)) ∧ zless (snd ab) (snd qr) ∧ zle (snd qr) Int0));

// adjust(b,<q,r>) ≡ if #0 $≤ r$-b then <#2$*q $+ #1,r$-b> else <#2$*q,r>
symbol adjust (b qr : τ ι) : τ ι ≔
  If (zle Int0 (zdiff (snd qr) b))
     (Pair (zadd (zmult Int2 (fst qr)) Int1) (zdiff (snd qr) b))
     (Pair (zmult Int2 (fst qr)) (snd qr));

// ===========================================================================
// The division algorithm
// ===========================================================================

// posDivAlg(ab) ≡  -- for the case a≥0, b>0
//   wfrec(measure(int*int, λ<a,b>. nat_of(a$-b$+#1)), ab,
//         λ<a,b> f. if (a$<b | b$≤#0) then <#0,a> else adjust(b, f`<a,#2$*b>))
symbol posDivAlg : τ ι → τ ι;
opaque symbol posDivAlg_def (ab : τ ι) :
  π (posDivAlg ab =
     wfrec (measure (Sigma int (λ _, int))
              (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
       ab
       (λ ab2 f,
          If (zless (fst ab2) (snd ab2) ∨ zle (snd ab2) Int0)
             (Pair Int0 (fst ab2))
             (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2))))))) ≔
begin admit end;

// negDivAlg(ab) ≡  -- for the case a<0, b>0
//   wfrec(measure(int*int, λ<a,b>. nat_of($-a$-b)), ab,
//         λ<a,b> f. if (#0$≤a$+b | b$≤#0) then <#-1,a$+b> else adjust(b, f`<a,#2$*b>))
symbol negDivAlg : τ ι → τ ι;
opaque symbol negDivAlg_def (ab : τ ι) :
  π (negDivAlg ab =
     wfrec (measure (Sigma int (λ _, int))
              (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
       ab
       (λ ab2 f,
          If (zle Int0 (zadd (fst ab2) (snd ab2)) ∨ zle (snd ab2) Int0)
             (Pair NegInt1 (zadd (fst ab2) (snd ab2)))
             (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2))))))) ≔
begin admit end;

// negateSnd(<q,r>) ≡ <q, $-r>
symbol negateSnd (qr : τ ι) : τ ι ≔ Pair (fst qr) (zminus (snd qr));

// The full division algorithm considers all possible signs for a,b,
// including the special case a=0, b<0, because negDivAlg requires a<0.
symbol divAlg (ab : τ ι) : τ ι ≔
  If (zle Int0 (fst ab))
     (If (zle Int0 (snd ab)) (posDivAlg ab)
        (If (fst ab = Int0) (Pair Int0 Int0)
           (negateSnd (negDivAlg (Pair (zminus (fst ab)) (zminus (snd ab)))))))
     (If (zless Int0 (snd ab)) (negDivAlg ab)
        (negateSnd (posDivAlg (Pair (zminus (fst ab)) (zminus (snd ab))))));

symbol zdiv (a b : τ ι) : τ ι ≔ fst (divAlg (Pair (intify a) (intify b)));
notation zdiv infix left 70;

symbol zmod (a b : τ ι) : τ ι ≔ snd (divAlg (Pair (intify a) (intify b)));
notation zmod infix left 70;

// ===========================================================================
// Some basic laws by Sidi Ehmety (need linear arithmetic!)
// ===========================================================================

opaque symbol zspos_add_zspos_imp_zspos (x y : τ ι) :
  π (zless Int0 x) → π (zless Int0 y) → π (zless Int0 (zadd x y)) ≔
begin admit end;

opaque symbol zpos_add_zpos_imp_zpos (x y : τ ι) :
  π (zle Int0 x) → π (zle Int0 y) → π (zle Int0 (zadd x y)) ≔
begin admit end;

opaque symbol zneg_add_zneg_imp_zneg (x y : τ ι) :
  π (zless x Int0) → π (zless y Int0) → π (zless (zadd x y) Int0) ≔
begin admit end;

// this theorem is used below
opaque symbol zneg_or_0_add_zneg_or_0_imp_zneg_or_0 (x y : τ ι) :
  π (zle x Int0) → π (zle y Int0) → π (zle (zadd x y) Int0) ≔
begin admit end;

opaque symbol zero_lt_zmagnitude (k : τ ι) :
  π (zless Int0 k) → π (k ∈ int) → π (lt empty (zmagnitude k)) ≔
begin admit end;

// ===========================================================================
// Inequality lemmas involving $#succ(m)
// ===========================================================================

opaque symbol zless_add_succ_iff (w z m : τ ι) :
  π (zless w (zadd z (int_of (succ m))) ⇔
     (zless w (zadd z (int_of m)) ∨ intify w = zadd z (int_of m))) ≔
begin admit end;

opaque symbol zadd_succ_lemma (z w m : τ ι) :
  π (z ∈ int) → π (zle (zadd w (int_of (succ m))) z ⇔ zless (zadd w (int_of m)) z) ≔
begin admit end;

opaque symbol zadd_succ_zle_iff (w m z : τ ι) :
  π (zle (zadd w (int_of (succ m))) z ⇔ zless (zadd w (int_of m)) z) ≔
begin admit end;

// ===========================================================================
// Inequality reasoning
// ===========================================================================

opaque symbol zless_add1_iff_zle (w z : τ ι) :
  π (zless w (zadd z Int1) ⇔ zle w z) ≔
begin admit end;

opaque symbol add1_zle_iff (w z : τ ι) :
  π (zle (zadd w Int1) z ⇔ zless w z) ≔
begin admit end;

opaque symbol add1_left_zle_iff (w z : τ ι) :
  π (zle (zadd Int1 w) z ⇔ zless w z) ≔
begin admit end;

// ===========================================================================
// Monotonicity of Multiplication
// ===========================================================================

opaque symbol zmult_mono_lemma (k i j : τ ι) :
  π (k ∈ omega) → π (zle i j) → π (zle (zmult i (int_of k)) (zmult j (int_of k))) ≔
begin admit end;

opaque symbol zmult_zle_mono1 (i j k : τ ι) :
  π (zle i j) → π (zle Int0 k) → π (zle (zmult i k) (zmult j k)) ≔
begin admit end;

opaque symbol zmult_zle_mono1_neg (i j k : τ ι) :
  π (zle i j) → π (zle k Int0) → π (zle (zmult j k) (zmult i k)) ≔
begin admit end;

opaque symbol zmult_zle_mono2 (i j k : τ ι) :
  π (zle i j) → π (zle Int0 k) → π (zle (zmult k i) (zmult k j)) ≔
begin admit end;

opaque symbol zmult_zle_mono2_neg (i j k : τ ι) :
  π (zle i j) → π (zle k Int0) → π (zle (zmult k j) (zmult k i)) ≔
begin admit end;

// ≤ monotonicity, BOTH arguments
opaque symbol zmult_zle_mono (i j k l : τ ι) :
  π (zle i j) → π (zle k l) → π (zle Int0 j) → π (zle Int0 k) →
  π (zle (zmult i k) (zmult j l)) ≔
begin admit end;

// strict, in 1st argument; proof is by induction on k>0
opaque symbol zmult_zless_mono2_lemma (i j k : τ ι) :
  π (zless i j) → π (k ∈ omega) → π (lt empty k) →
  π (zless (zmult (int_of k) i) (zmult (int_of k) j)) ≔
begin admit end;

opaque symbol zmult_zless_mono2 (i j k : τ ι) :
  π (zless i j) → π (zless Int0 k) → π (zless (zmult k i) (zmult k j)) ≔
begin admit end;

opaque symbol zmult_zless_mono1 (i j k : τ ι) :
  π (zless i j) → π (zless Int0 k) → π (zless (zmult i k) (zmult j k)) ≔
begin admit end;

// < monotonicity, BOTH arguments
opaque symbol zmult_zless_mono (i j k l : τ ι) :
  π (zless i j) → π (zless k l) → π (zless Int0 j) → π (zless Int0 k) →
  π (zless (zmult i k) (zmult j l)) ≔
begin admit end;

opaque symbol zmult_zless_mono1_neg (i j k : τ ι) :
  π (zless i j) → π (zless k Int0) → π (zless (zmult j k) (zmult i k)) ≔
begin admit end;

opaque symbol zmult_zless_mono2_neg (i j k : τ ι) :
  π (zless i j) → π (zless k Int0) → π (zless (zmult k j) (zmult k i)) ≔
begin admit end;

// ===========================================================================
// Products of zeroes
// ===========================================================================

opaque symbol zmult_eq_lemma (m n : τ ι) :
  π (m ∈ int) → π (n ∈ int) → π ((m = Int0 ∨ n = Int0) ⇔ zmult m n = Int0) ≔
begin admit end;

opaque symbol zmult_eq_0_iff (m n : τ ι) :
  π (zmult m n = Int0 ⇔ (intify m = Int0 ∨ intify n = Int0)) ≔
begin admit end;

// ===========================================================================
// Cancellation laws for k*m < k*n and m*k < n*k, also for ≤ and =,
// but not (yet?) for k*m < n*k.
// ===========================================================================

opaque symbol zmult_zless_lemma (k m n : τ ι) :
  π (k ∈ int) → π (m ∈ int) → π (n ∈ int) →
  π (zless (zmult m k) (zmult n k) ⇔
     ((zless Int0 k ∧ zless m n) ∨ (zless k Int0 ∧ zless n m))) ≔
begin admit end;

opaque symbol zmult_zless_cancel2 (m k n : τ ι) :
  π (zless (zmult m k) (zmult n k) ⇔
     ((zless Int0 k ∧ zless m n) ∨ (zless k Int0 ∧ zless n m))) ≔
begin admit end;

opaque symbol zmult_zless_cancel1 (k m n : τ ι) :
  π (zless (zmult k m) (zmult k n) ⇔
     ((zless Int0 k ∧ zless m n) ∨ (zless k Int0 ∧ zless n m))) ≔
begin admit end;

opaque symbol zmult_zle_cancel2 (m k n : τ ι) :
  π (zle (zmult m k) (zmult n k) ⇔
     ((zless Int0 k ⇒ zle m n) ∧ (zless k Int0 ⇒ zle n m))) ≔
begin admit end;

opaque symbol zmult_zle_cancel1 (k m n : τ ι) :
  π (zle (zmult k m) (zmult k n) ⇔
     ((zless Int0 k ⇒ zle m n) ∧ (zless k Int0 ⇒ zle n m))) ≔
begin admit end;

opaque symbol int_eq_iff_zle (m n : τ ι) :
  π (m ∈ int) → π (n ∈ int) → π (m = n ⇔ (zle m n ∧ zle n m)) ≔
begin admit end;

opaque symbol zmult_cancel2_lemma (k m n : τ ι) :
  π (k ∈ int) → π (m ∈ int) → π (n ∈ int) →
  π (zmult m k = zmult n k ⇔ (k = Int0 ∨ m = n)) ≔
begin admit end;

opaque symbol zmult_cancel2 (m k n : τ ι) :
  π (zmult m k = zmult n k ⇔ (intify k = Int0 ∨ intify m = intify n)) ≔
begin admit end;

opaque symbol zmult_cancel1 (k m n : τ ι) :
  π (zmult k m = zmult k n ⇔ (intify k = Int0 ∨ intify m = intify n)) ≔
begin admit end;

// ===========================================================================
// Uniqueness and monotonicity of quotients and remainders
// ===========================================================================

opaque symbol unique_quotient_lemma (b q' r' q r : τ ι) :
  π (zle (zadd (zmult b q') r') (zadd (zmult b q) r)) →
  π (zle Int0 r') → π (zless Int0 b) → π (zless r b) →
  π (zle q' q) ≔
begin admit end;

opaque symbol unique_quotient_lemma_neg (b q' r' q r : τ ι) :
  π (zle (zadd (zmult b q') r') (zadd (zmult b q) r)) →
  π (zle r Int0) → π (zless b Int0) → π (zless b r') →
  π (zle q q') ≔
begin admit end;

opaque symbol unique_quotient (a b q r q' r' : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (quorem (Pair a b) (Pair q' r')) →
  π (b ∈ int) → π (b ≠ Int0) → π (q ∈ int) → π (q' ∈ int) →
  π (q = q') ≔
begin admit end;

opaque symbol unique_remainder (a b q r q' r' : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (quorem (Pair a b) (Pair q' r')) →
  π (b ∈ int) → π (b ≠ Int0) → π (q ∈ int) → π (q' ∈ int) →
  π (r ∈ int) → π (r' ∈ int) →
  π (r = r') ≔
begin admit end;

// ===========================================================================
// Correctness of posDivAlg, the Division Algorithm for a≥0 and b>0
// ===========================================================================

opaque symbol adjust_eq (b q r : τ ι) :
  π (adjust b (Pair q r) =
     If (zle Int0 (zdiff r b)) (Pair (zadd (zmult Int2 q) Int1) (zdiff r b))
        (Pair (zmult Int2 q) r)) ≔
begin admit end;

opaque symbol posDivAlg_termination (a b : τ ι) :
  π (zless Int0 b) → π (¬ zless a b) →
  π (lt (nat_of (zadd (zdiff a (zmult Int2 b)) Int1)) (nat_of (zadd (zdiff a b) Int1))) ≔
begin admit end;

// posDivAlg_unfold = def_wfrec [OF posDivAlg_def wf_measure]
opaque symbol posDivAlg_unfold (ab : τ ι) :
  π (posDivAlg ab =
     If (zless (fst ab) (snd ab) ∨ zle (snd ab) Int0)
        (Pair Int0 (fst ab))
        (adjust (snd ab)
           (fapply (Lambda (vimage_singleton
                       (measure (Sigma int (λ _, int))
                          (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))) ab)
                     (λ x, posDivAlg x))
                   (Pair (fst ab) (zmult Int2 (snd ab)))))) ≔
begin admit end;

opaque symbol posDivAlg_eqn (a b : τ ι) :
  π (zless Int0 b) → π (a ∈ int) → π (b ∈ int) →
  π (posDivAlg (Pair a b) =
     If (zless a b) (Pair Int0 a) (adjust b (posDivAlg (Pair a (zmult Int2 b))))) ≔
begin admit end;

opaque symbol posDivAlg_induct_lemma (P : τ ι → Prop) (u v : τ ι) :
  (Π (a b : τ ι), π (a ∈ int) → π (b ∈ int) →
    π (¬ (zless a b ∨ zle b Int0) ⇒ P (Pair a (zmult Int2 b))) →
    π (P (Pair a b))) →
  π (Pair u v ∈ Sigma int (λ _, int)) →
  π (P (Pair u v)) ≔
begin admit end;

opaque symbol posDivAlg_induct (P : τ ι → τ ι → Prop) (u v : τ ι) :
  π (u ∈ int) → π (v ∈ int) →
  (Π (a b : τ ι), π (a ∈ int) → π (b ∈ int) →
    π (¬ (zless a b ∨ zle b Int0) ⇒ P a (zmult Int2 b)) →
    π (P a b)) →
  π (P u v) ≔
begin admit end;

// FIXME: use intify in integ_of so that we always have integ_of(w) ∈ int.
// then this rewrite can work for all constants
opaque symbol intify_eq_0_iff_zle (m : τ ι) :
  π (intify m = Int0 ⇔ (zle m Int0 ∧ zle Int0 m)) ≔
begin admit end;

// ===========================================================================
// Some convenient biconditionals for products of signs
// ===========================================================================

opaque symbol zmult_pos (i j : τ ι) :
  π (zless Int0 i) → π (zless Int0 j) → π (zless Int0 (zmult i j)) ≔
begin admit end;

opaque symbol zmult_neg (i j : τ ι) :
  π (zless i Int0) → π (zless j Int0) → π (zless Int0 (zmult i j)) ≔
begin admit end;

opaque symbol zmult_pos_neg (i j : τ ι) :
  π (zless Int0 i) → π (zless j Int0) → π (zless (zmult i j) Int0) ≔
begin admit end;

// ===========================================================================
// Inequality reasoning
// ===========================================================================

opaque symbol int_0_less_lemma (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) →
  π (zless Int0 (zmult x y) ⇔
     ((zless Int0 x ∧ zless Int0 y) ∨ (zless x Int0 ∧ zless y Int0))) ≔
begin admit end;

opaque symbol int_0_less_mult_iff (x y : τ ι) :
  π (zless Int0 (zmult x y) ⇔
     ((zless Int0 x ∧ zless Int0 y) ∨ (zless x Int0 ∧ zless y Int0))) ≔
begin admit end;

opaque symbol int_0_le_lemma (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) →
  π (zle Int0 (zmult x y) ⇔
     ((zle Int0 x ∧ zle Int0 y) ∨ (zle x Int0 ∧ zle y Int0))) ≔
begin admit end;

opaque symbol int_0_le_mult_iff (x y : τ ι) :
  π (zle Int0 (zmult x y) ⇔
     ((zle Int0 x ∧ zle Int0 y) ∨ (zle x Int0 ∧ zle y Int0))) ≔
begin admit end;

opaque symbol zmult_less_0_iff (x y : τ ι) :
  π (zless (zmult x y) Int0 ⇔
     ((zless Int0 x ∧ zless y Int0) ∨ (zless x Int0 ∧ zless Int0 y))) ≔
begin admit end;

opaque symbol zmult_le_0_iff (x y : τ ι) :
  π (zle (zmult x y) Int0 ⇔
     ((zle Int0 x ∧ zle y Int0) ∨ (zle x Int0 ∧ zle Int0 y))) ≔
begin admit end;

// Typechecking for posDivAlg
opaque symbol posDivAlg_type (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (posDivAlg (Pair a b) ∈ Sigma int (λ _, int)) ≔
begin admit end;

// Correctness of posDivAlg: it computes quotients correctly
opaque symbol posDivAlg_correct (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle Int0 a) → π (zless Int0 b) →
  π (quorem (Pair a b) (posDivAlg (Pair a b))) ≔
begin admit end;

// ===========================================================================
// Correctness of negDivAlg, the division algorithm for a<0 and b>0
// ===========================================================================

opaque symbol negDivAlg_termination (a b : τ ι) :
  π (zless Int0 b) → π (zless (zadd a b) Int0) →
  π (lt (nat_of (zdiff (zminus a) (zmult Int2 b))) (nat_of (zdiff (zminus a) b))) ≔
begin admit end;

// negDivAlg_unfold = def_wfrec [OF negDivAlg_def wf_measure]
opaque symbol negDivAlg_unfold (ab : τ ι) :
  π (negDivAlg ab =
     If (zle Int0 (zadd (fst ab) (snd ab)) ∨ zle (snd ab) Int0)
        (Pair NegInt1 (zadd (fst ab) (snd ab)))
        (adjust (snd ab)
           (fapply (Lambda (vimage_singleton
                       (measure (Sigma int (λ _, int))
                          (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))) ab)
                     (λ x, negDivAlg x))
                   (Pair (fst ab) (zmult Int2 (snd ab)))))) ≔
begin admit end;

opaque symbol negDivAlg_eqn (a b : τ ι) :
  π (zless Int0 b) → π (a ∈ int) → π (b ∈ int) →
  π (negDivAlg (Pair a b) =
     If (zle Int0 (zadd a b)) (Pair NegInt1 (zadd a b))
        (adjust b (negDivAlg (Pair a (zmult Int2 b))))) ≔
begin admit end;

opaque symbol negDivAlg_induct_lemma (P : τ ι → Prop) (u v : τ ι) :
  (Π (a b : τ ι), π (a ∈ int) → π (b ∈ int) →
    π (¬ (zle Int0 (zadd a b) ∨ zle b Int0) ⇒ P (Pair a (zmult Int2 b))) →
    π (P (Pair a b))) →
  π (Pair u v ∈ Sigma int (λ _, int)) →
  π (P (Pair u v)) ≔
begin admit end;

opaque symbol negDivAlg_induct (P : τ ι → τ ι → Prop) (u v : τ ι) :
  π (u ∈ int) → π (v ∈ int) →
  (Π (a b : τ ι), π (a ∈ int) → π (b ∈ int) →
    π (¬ (zle Int0 (zadd a b) ∨ zle b Int0) ⇒ P a (zmult Int2 b)) →
    π (P a b)) →
  π (P u v) ≔
begin admit end;

// Typechecking for negDivAlg
opaque symbol negDivAlg_type (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (negDivAlg (Pair a b) ∈ Sigma int (λ _, int)) ≔
begin admit end;

// Correctness of negDivAlg: it computes quotients correctly.
// It doesn't work if a=0 because 0/b=0 rather than -1
opaque symbol negDivAlg_correct (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zless a Int0) → π (zless Int0 b) →
  π (quorem (Pair a b) (negDivAlg (Pair a b))) ≔
begin admit end;

// ===========================================================================
// Existence shown by proving the division algorithm to be correct
// ===========================================================================

// the case a=0
opaque symbol quorem_0 (b : τ ι) :
  π (b ≠ Int0) → π (b ∈ int) → π (quorem (Pair Int0 b) (Pair Int0 Int0)) ≔
begin admit end;

opaque symbol posDivAlg_zero_divisor (a : τ ι) :
  π (posDivAlg (Pair a Int0) = Pair Int0 a) ≔
begin admit end;

opaque symbol posDivAlg_0 (b : τ ι) :
  π (posDivAlg (Pair Int0 b) = Pair Int0 Int0) ≔
begin admit end;

// Needed below. Actually it's an equivalence.
opaque symbol linear_arith_lemma (b : τ ι) :
  π (¬ zle Int0 (zadd NegInt1 b)) → π (zle b Int0) ≔
begin admit end;

opaque symbol negDivAlg_minus1 (b : τ ι) :
  π (negDivAlg (Pair NegInt1 b) = Pair NegInt1 (zdiff b Int1)) ≔
begin admit end;

opaque symbol negateSnd_eq (q r : τ ι) :
  π (negateSnd (Pair q r) = Pair q (zminus r)) ≔
begin admit end;

opaque symbol negateSnd_type (qr : τ ι) :
  π (qr ∈ Sigma int (λ _, int)) → π (negateSnd qr ∈ Sigma int (λ _, int)) ≔
begin admit end;

opaque symbol quorem_neg (a b qr : τ ι) :
  π (quorem (Pair (zminus a) (zminus b)) qr) → π (a ∈ int) → π (b ∈ int) →
  π (qr ∈ Sigma int (λ _, int)) →
  π (quorem (Pair a b) (negateSnd qr)) ≔
begin admit end;

opaque symbol divAlg_correct (a b : τ ι) :
  π (b ≠ Int0) → π (a ∈ int) → π (b ∈ int) →
  π (quorem (Pair a b) (divAlg (Pair a b))) ≔
begin admit end;

opaque symbol divAlg_type (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (divAlg (Pair a b) ∈ Sigma int (λ _, int)) ≔
begin admit end;

// intify cancellation

opaque symbol zdiv_intify1 (x y : τ ι) : π (zdiv (intify x) y = zdiv x y) ≔
begin admit end;

opaque symbol zdiv_intify2 (x y : τ ι) : π (zdiv x (intify y) = zdiv x y) ≔
begin admit end;

opaque symbol zdiv_type (z w : τ ι) : π (zdiv z w ∈ int) ≔
begin admit end;

opaque symbol zmod_intify1 (x y : τ ι) : π (zmod (intify x) y = zmod x y) ≔
begin admit end;

opaque symbol zmod_intify2 (x y : τ ι) : π (zmod x (intify y) = zmod x y) ≔
begin admit end;

opaque symbol zmod_type (z w : τ ι) : π (zmod z w ∈ int) ≔
begin admit end;

// Arbitrary definitions for division by zero. Useful to simplify certain equations

opaque symbol DIVISION_BY_ZERO_ZDIV (a : τ ι) : π (zdiv a Int0 = Int0) ≔
begin admit end;

opaque symbol DIVISION_BY_ZERO_ZMOD (a : τ ι) : π (zmod a Int0 = intify a) ≔
begin admit end;

// Basic laws about division and remainder

opaque symbol raw_zmod_zdiv_equality (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) →
  π (a = zadd (zmult b (zdiv a b)) (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zdiv_equality (a b : τ ι) :
  π (intify a = zadd (zmult b (zdiv a b)) (zmod a b)) ≔
begin admit end;

opaque symbol pos_mod (a b : τ ι) :
  π (zless Int0 b) → π (zle Int0 (zmod a b) ∧ zless (zmod a b) b) ≔
begin admit end;

// pos_mod_sign = pos_mod [THEN conjunct1]
opaque symbol pos_mod_sign (a b : τ ι) :
  π (zless Int0 b) → π (zle Int0 (zmod a b)) ≔
begin admit end;

// pos_mod_bound = pos_mod [THEN conjunct2]
opaque symbol pos_mod_bound (a b : τ ι) :
  π (zless Int0 b) → π (zless (zmod a b) b) ≔
begin admit end;

opaque symbol neg_mod (a b : τ ι) :
  π (zless b Int0) → π (zle (zmod a b) Int0 ∧ zless b (zmod a b)) ≔
begin admit end;

// neg_mod_sign = neg_mod [THEN conjunct1]
opaque symbol neg_mod_sign (a b : τ ι) :
  π (zless b Int0) → π (zle (zmod a b) Int0) ≔
begin admit end;

// neg_mod_bound = neg_mod [THEN conjunct2]
opaque symbol neg_mod_bound (a b : τ ι) :
  π (zless b Int0) → π (zless b (zmod a b)) ≔
begin admit end;

// proving general properties of zdiv and zmod

opaque symbol quorem_div_mod (a b : τ ι) :
  π (b ≠ Int0) → π (a ∈ int) → π (b ∈ int) →
  π (quorem (Pair a b) (Pair (zdiv a b) (zmod a b))) ≔
begin admit end;

// Surely quorem(⟨a,b⟩,⟨q,r⟩) implies a∈int, but it doesn't matter
opaque symbol quorem_div (a b q r : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (b ≠ Int0) → π (a ∈ int) → π (b ∈ int) →
  π (q ∈ int) → π (zdiv a b = q) ≔
begin admit end;

opaque symbol quorem_mod (a b q r : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (b ≠ Int0) → π (a ∈ int) → π (b ∈ int) →
  π (q ∈ int) → π (r ∈ int) → π (zmod a b = r) ≔
begin admit end;

opaque symbol zdiv_pos_pos_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle Int0 a) → π (zless a b) →
  π (zdiv a b = Int0) ≔
begin admit end;

opaque symbol zdiv_pos_pos_trivial (a b : τ ι) :
  π (zle Int0 a) → π (zless a b) → π (zdiv a b = Int0) ≔
begin admit end;

opaque symbol zdiv_neg_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle a Int0) → π (zless b a) →
  π (zdiv a b = Int0) ≔
begin admit end;

opaque symbol zdiv_neg_neg_trivial (a b : τ ι) :
  π (zle a Int0) → π (zless b a) → π (zdiv a b = Int0) ≔
begin admit end;

opaque symbol zadd_le_0_lemma (a b : τ ι) :
  π (zle (zadd a b) Int0) → π (zless Int0 a) → π (zless Int0 b) → π ⊥ ≔
begin admit end;

opaque symbol zdiv_pos_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zless Int0 a) → π (zle (zadd a b) Int0) →
  π (zdiv a b = NegInt1) ≔
begin admit end;

opaque symbol zdiv_pos_neg_trivial (a b : τ ι) :
  π (zless Int0 a) → π (zle (zadd a b) Int0) → π (zdiv a b = NegInt1) ≔
begin admit end;

// There is no zdiv_neg_pos_trivial because 0 zdiv b = 0 would supersede it

opaque symbol zmod_pos_pos_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle Int0 a) → π (zless a b) →
  π (zmod a b = a) ≔
begin admit end;

opaque symbol zmod_pos_pos_trivial (a b : τ ι) :
  π (zle Int0 a) → π (zless a b) → π (zmod a b = intify a) ≔
begin admit end;

opaque symbol zmod_neg_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle a Int0) → π (zless b a) →
  π (zmod a b = a) ≔
begin admit end;

opaque symbol zmod_neg_neg_trivial (a b : τ ι) :
  π (zle a Int0) → π (zless b a) → π (zmod a b = intify a) ≔
begin admit end;

opaque symbol zmod_pos_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zless Int0 a) → π (zle (zadd a b) Int0) →
  π (zmod a b = zadd a b) ≔
begin admit end;

opaque symbol zmod_pos_neg_trivial (a b : τ ι) :
  π (zless Int0 a) → π (zle (zadd a b) Int0) → π (zmod a b = zadd a b) ≔
begin admit end;

// There is no zmod_neg_pos_trivial...

// Simpler laws such as -a zdiv b = -(a zdiv b) FAIL

opaque symbol zdiv_zminus_zminus_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zdiv (zminus a) (zminus b) = zdiv a b) ≔
begin admit end;

opaque symbol zdiv_zminus_zminus (a b : τ ι) :
  π (zdiv (zminus a) (zminus b) = zdiv a b) ≔
begin admit end;

// Simpler laws such as -a zmod b = -(a zmod b) FAIL
opaque symbol zmod_zminus_zminus_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zmod (zminus a) (zminus b) = zminus (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zminus_zminus (a b : τ ι) :
  π (zmod (zminus a) (zminus b) = zminus (zmod a b)) ≔
begin admit end;

// ===========================================================================
// division of a number by itself
// ===========================================================================

opaque symbol self_quotient_aux1 (a r q : τ ι) :
  π (zless Int0 a) → π (a = zadd r (zmult a q)) → π (zless r a) →
  π (zle Int1 q) ≔
begin admit end;

opaque symbol self_quotient_aux2 (a r q : τ ι) :
  π (zless Int0 a) → π (a = zadd r (zmult a q)) → π (zle Int0 r) →
  π (zle q Int1) ≔
begin admit end;

opaque symbol self_quotient (a q r : τ ι) :
  π (quorem (Pair a a) (Pair q r)) → π (a ∈ int) → π (q ∈ int) → π (a ≠ Int0) →
  π (q = Int1) ≔
begin admit end;

opaque symbol self_remainder (a q r : τ ι) :
  π (quorem (Pair a a) (Pair q r)) → π (a ∈ int) → π (q ∈ int) → π (r ∈ int) →
  π (a ≠ Int0) → π (r = Int0) ≔
begin admit end;

opaque symbol zdiv_self_raw (a : τ ι) :
  π (a ≠ Int0) → π (a ∈ int) → π (zdiv a a = Int1) ≔
begin admit end;

opaque symbol zdiv_self (a : τ ι) :
  π (intify a ≠ Int0) → π (zdiv a a = Int1) ≔
begin admit end;

// Here we have 0 zmod 0 = 0, also assumed by Knuth (who puts m zmod 0 = 0)
opaque symbol zmod_self_raw (a : τ ι) :
  π (a ∈ int) → π (zmod a a = Int0) ≔
begin admit end;

opaque symbol zmod_self (a : τ ι) : π (zmod a a = Int0) ≔
begin admit end;

// ===========================================================================
// Computation of division and remainder
// ===========================================================================

opaque symbol zdiv_zero (b : τ ι) : π (zdiv Int0 b = Int0) ≔
begin admit end;

opaque symbol zdiv_eq_minus1 (b : τ ι) :
  π (zless Int0 b) → π (zdiv NegInt1 b = NegInt1) ≔
begin admit end;

opaque symbol zmod_zero (b : τ ι) : π (zmod Int0 b = Int0) ≔
begin admit end;

opaque symbol zdiv_minus1 (b : τ ι) :
  π (zless Int0 b) → π (zdiv NegInt1 b = NegInt1) ≔
begin admit end;

opaque symbol zmod_minus1 (b : τ ι) :
  π (zless Int0 b) → π (zmod NegInt1 b = zdiff b Int1) ≔
begin admit end;

// a positive, b positive

opaque symbol zdiv_pos_pos (a b : τ ι) :
  π (zless Int0 a) → π (zle Int0 b) →
  π (zdiv a b = fst (posDivAlg (Pair (intify a) (intify b)))) ≔
begin admit end;

opaque symbol zmod_pos_pos (a b : τ ι) :
  π (zless Int0 a) → π (zle Int0 b) →
  π (zmod a b = snd (posDivAlg (Pair (intify a) (intify b)))) ≔
begin admit end;

// a negative, b positive

opaque symbol zdiv_neg_pos (a b : τ ι) :
  π (zless a Int0) → π (zless Int0 b) →
  π (zdiv a b = fst (negDivAlg (Pair (intify a) (intify b)))) ≔
begin admit end;

opaque symbol zmod_neg_pos (a b : τ ι) :
  π (zless a Int0) → π (zless Int0 b) →
  π (zmod a b = snd (negDivAlg (Pair (intify a) (intify b)))) ≔
begin admit end;

// a positive, b negative

opaque symbol zdiv_pos_neg (a b : τ ι) :
  π (zless Int0 a) → π (zless b Int0) →
  π (zdiv a b = fst (negateSnd (negDivAlg (Pair (zminus a) (zminus b))))) ≔
begin admit end;

opaque symbol zmod_pos_neg (a b : τ ι) :
  π (zless Int0 a) → π (zless b Int0) →
  π (zmod a b = snd (negateSnd (negDivAlg (Pair (zminus a) (zminus b))))) ≔
begin admit end;

// a negative, b negative

opaque symbol zdiv_neg_neg (a b : τ ι) :
  π (zless a Int0) → π (zle b Int0) →
  π (zdiv a b = fst (negateSnd (posDivAlg (Pair (zminus a) (zminus b))))) ≔
begin admit end;

opaque symbol zmod_neg_neg (a b : τ ι) :
  π (zless a Int0) → π (zle b Int0) →
  π (zmod a b = snd (negateSnd (posDivAlg (Pair (zminus a) (zminus b))))) ≔
begin admit end;

// (`declare zdiv_pos_pos [of "integ_of (v)" "integ_of (w)", simp] for v w` and
// the seven similar `declare` lines that follow in the .thy just re-target
// the EXISTING lemmas above as simp rules for `integ_of` literals — no new
// statement, skipped.)

// Special-case simplification

opaque symbol zmod_1 (a : τ ι) : π (zmod a Int1 = Int0) ≔
begin admit end;

opaque symbol zdiv_1 (a : τ ι) : π (zdiv a Int1 = intify a) ≔
begin admit end;

opaque symbol zmod_minus1_right (a : τ ι) : π (zmod a NegInt1 = Int0) ≔
begin admit end;

opaque symbol zdiv_minus1_right_raw (a : τ ι) :
  π (a ∈ int) → π (zdiv a NegInt1 = zminus a) ≔
begin admit end;

opaque symbol zdiv_minus1_right (a : τ ι) : π (zdiv a NegInt1 = zminus a) ≔
begin admit end;

// ===========================================================================
// Monotonicity in the first argument (divisor)
// ===========================================================================

opaque symbol zdiv_mono1 (a a' b : τ ι) :
  π (zle a a') → π (zless Int0 b) → π (zle (zdiv a b) (zdiv a' b)) ≔
begin admit end;

opaque symbol zdiv_mono1_neg (a a' b : τ ι) :
  π (zle a a') → π (zless b Int0) → π (zle (zdiv a' b) (zdiv a b)) ≔
begin admit end;

// ===========================================================================
// Monotonicity in the second argument (dividend)
// ===========================================================================

opaque symbol q_pos_lemma (b' q' r' : τ ι) :
  π (zle Int0 (zadd (zmult b' q') r')) → π (zless r' b') → π (zless Int0 b') →
  π (zle Int0 q') ≔
begin admit end;

opaque symbol zdiv_mono2_lemma (b q r b' q' r' : τ ι) :
  π (zadd (zmult b q) r = zadd (zmult b' q') r') →
  π (zle Int0 (zadd (zmult b' q') r')) →
  π (zless r' b') → π (zle Int0 r) → π (zless Int0 b') → π (zle b' b) →
  π (zle q q') ≔
begin admit end;

opaque symbol zdiv_mono2_raw (a b b' : τ ι) :
  π (zle Int0 a) → π (zless Int0 b') → π (zle b' b) → π (a ∈ int) →
  π (zle (zdiv a b) (zdiv a b')) ≔
begin admit end;

opaque symbol zdiv_mono2 (a b b' : τ ι) :
  π (zle Int0 a) → π (zless Int0 b') → π (zle b' b) →
  π (zle (zdiv a b) (zdiv a b')) ≔
begin admit end;

opaque symbol q_neg_lemma (b' q' r' : τ ι) :
  π (zless (zadd (zmult b' q') r') Int0) → π (zle Int0 r') → π (zless Int0 b') →
  π (zless q' Int0) ≔
begin admit end;

opaque symbol zdiv_mono2_neg_lemma (b q r b' q' r' : τ ι) :
  π (zadd (zmult b q) r = zadd (zmult b' q') r') →
  π (zless (zadd (zmult b' q') r') Int0) →
  π (zless r b) → π (zle Int0 r') → π (zless Int0 b') → π (zle b' b) →
  π (zle q' q) ≔
begin admit end;

opaque symbol zdiv_mono2_neg_raw (a b b' : τ ι) :
  π (zless a Int0) → π (zless Int0 b') → π (zle b' b) → π (a ∈ int) →
  π (zle (zdiv a b') (zdiv a b)) ≔
begin admit end;

opaque symbol zdiv_mono2_neg (a b b' : τ ι) :
  π (zless a Int0) → π (zless Int0 b') → π (zle b' b) →
  π (zle (zdiv a b') (zdiv a b)) ≔
begin admit end;

// ===========================================================================
// More algebraic laws for zdiv and zmod
// ===========================================================================

// proving (a*b) zdiv c = a $* (b zdiv c) $+ a * (b zmod c)

opaque symbol zmult1_lemma (b c q r a : τ ι) :
  π (quorem (Pair b c) (Pair q r)) → π (c ∈ int) → π (c ≠ Int0) →
  π (quorem (Pair (zmult a b) c)
       (Pair (zadd (zmult a q) (zdiv (zmult a r) c)) (zmod (zmult a r) c))) ≔
begin admit end;

opaque symbol zdiv_zmult1_eq_raw (a b c : τ ι) :
  π (b ∈ int) → π (c ∈ int) →
  π (zdiv (zmult a b) c = zadd (zmult a (zdiv b c)) (zdiv (zmult a (zmod b c)) c)) ≔
begin admit end;

opaque symbol zdiv_zmult1_eq (a b c : τ ι) :
  π (zdiv (zmult a b) c = zadd (zmult a (zdiv b c)) (zdiv (zmult a (zmod b c)) c)) ≔
begin admit end;

opaque symbol zmod_zmult1_eq_raw (a b c : τ ι) :
  π (b ∈ int) → π (c ∈ int) →
  π (zmod (zmult a b) c = zmod (zmult a (zmod b c)) c) ≔
begin admit end;

opaque symbol zmod_zmult1_eq (a b c : τ ι) :
  π (zmod (zmult a b) c = zmod (zmult a (zmod b c)) c) ≔
begin admit end;

opaque symbol zmod_zmult1_eq' (a b c : τ ι) :
  π (zmod (zmult a b) c = zmod (zmult (zmod a c) b) c) ≔
begin admit end;

opaque symbol zmod_zmult_distrib (a b c : τ ι) :
  π (zmod (zmult a b) c = zmod (zmult (zmod a c) (zmod b c)) c) ≔
begin admit end;

opaque symbol zdiv_zmult_self1 (a b : τ ι) :
  π (intify b ≠ Int0) → π (zdiv (zmult a b) b = intify a) ≔
begin admit end;

opaque symbol zdiv_zmult_self2 (a b : τ ι) :
  π (intify b ≠ Int0) → π (zdiv (zmult b a) b = intify a) ≔
begin admit end;

opaque symbol zmod_zmult_self1 (a b : τ ι) : π (zmod (zmult a b) b = Int0) ≔
begin admit end;

opaque symbol zmod_zmult_self2 (a b : τ ι) : π (zmod (zmult b a) b = Int0) ≔
begin admit end;

// proving (a+b) zdiv c = a zdiv c + b zdiv c + ((a zmod c + b zmod c) zdiv c)

opaque symbol zadd1_lemma (a c aq ar b bq br : τ ι) :
  π (quorem (Pair a c) (Pair aq ar)) → π (quorem (Pair b c) (Pair bq br)) →
  π (c ∈ int) → π (c ≠ Int0) →
  π (quorem (Pair (zadd a b) c)
       (Pair (zadd (zadd aq bq) (zdiv (zadd ar br) c)) (zmod (zadd ar br) c))) ≔
begin admit end;

// NOT suitable for rewriting: the RHS has an instance of the LHS
opaque symbol zdiv_zadd1_eq_raw (a b c : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (c ∈ int) →
  π (zdiv (zadd a b) c =
     zadd (zadd (zdiv a c) (zdiv b c)) (zdiv (zadd (zmod a c) (zmod b c)) c)) ≔
begin admit end;

opaque symbol zdiv_zadd1_eq (a b c : τ ι) :
  π (zdiv (zadd a b) c =
     zadd (zadd (zdiv a c) (zdiv b c)) (zdiv (zadd (zmod a c) (zmod b c)) c)) ≔
begin admit end;

opaque symbol zmod_zadd1_eq_raw (a b c : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (c ∈ int) →
  π (zmod (zadd a b) c = zmod (zadd (zmod a c) (zmod b c)) c) ≔
begin admit end;

opaque symbol zmod_zadd1_eq (a b c : τ ι) :
  π (zmod (zadd a b) c = zmod (zadd (zmod a c) (zmod b c)) c) ≔
begin admit end;

opaque symbol zmod_div_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zdiv (zmod a b) b = Int0) ≔
begin admit end;

opaque symbol zmod_div_trivial (a b : τ ι) : π (zdiv (zmod a b) b = Int0) ≔
begin admit end;

opaque symbol zmod_mod_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zmod (zmod a b) b = zmod a b) ≔
begin admit end;

opaque symbol zmod_mod_trivial (a b : τ ι) : π (zmod (zmod a b) b = zmod a b) ≔
begin admit end;

opaque symbol zmod_zadd_left_eq (a b c : τ ι) :
  π (zmod (zadd a b) c = zmod (zadd (zmod a c) b) c) ≔
begin admit end;

opaque symbol zmod_zadd_right_eq (a b c : τ ι) :
  π (zmod (zadd a b) c = zmod (zadd a (zmod b c)) c) ≔
begin admit end;

opaque symbol zdiv_zadd_self1 (a b : τ ι) :
  π (intify a ≠ Int0) → π (zdiv (zadd a b) a = zadd (zdiv b a) Int1) ≔
begin admit end;

opaque symbol zdiv_zadd_self2 (a b : τ ι) :
  π (intify a ≠ Int0) → π (zdiv (zadd b a) a = zadd (zdiv b a) Int1) ≔
begin admit end;

opaque symbol zmod_zadd_self1 (a b : τ ι) : π (zmod (zadd a b) a = zmod b a) ≔
begin admit end;

opaque symbol zmod_zadd_self2 (a b : τ ι) : π (zmod (zadd b a) a = zmod b a) ≔
begin admit end;

// ===========================================================================
// proving a zdiv (b*c) = (a zdiv b) zdiv c
// ===========================================================================

// The condition c>0 seems necessary. Consider that 7 zdiv -6 = -2 but
// 7 zdiv 2 zdiv -3 = 3 zdiv -3 = -1. The subcase (a zdiv b) zmod c = 0 seems
// to cause particular problems.

// first, four lemmas to bound the remainder for the cases b<0 and b>0

opaque symbol zdiv_zmult2_aux1 (c b r q : τ ι) :
  π (zless Int0 c) → π (zless b r) → π (zle r Int0) →
  π (zless (zmult b c) (zadd (zmult b (zmod q c)) r)) ≔
begin admit end;

opaque symbol zdiv_zmult2_aux2 (c b r q : τ ι) :
  π (zless Int0 c) → π (zless b r) → π (zle r Int0) →
  π (zle (zadd (zmult b (zmod q c)) r) Int0) ≔
begin admit end;

opaque symbol zdiv_zmult2_aux3 (c r b q : τ ι) :
  π (zless Int0 c) → π (zle Int0 r) → π (zless r b) →
  π (zle Int0 (zadd (zmult b (zmod q c)) r)) ≔
begin admit end;

opaque symbol zdiv_zmult2_aux4 (c r b q : τ ι) :
  π (zless Int0 c) → π (zle Int0 r) → π (zless r b) →
  π (zless (zadd (zmult b (zmod q c)) r) (zmult b c)) ≔
begin admit end;

opaque symbol zdiv_zmult2_lemma (a b q r c : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (a ∈ int) → π (b ∈ int) → π (b ≠ Int0) →
  π (zless Int0 c) →
  π (quorem (Pair a (zmult b c)) (Pair (zdiv q c) (zadd (zmult b (zmod q c)) r))) ≔
begin admit end;

opaque symbol zdiv_zmult2_eq_raw (a b c : τ ι) :
  π (zless Int0 c) → π (a ∈ int) → π (b ∈ int) →
  π (zdiv a (zmult b c) = zdiv (zdiv a b) c) ≔
begin admit end;

opaque symbol zdiv_zmult2_eq (a b c : τ ι) :
  π (zless Int0 c) → π (zdiv a (zmult b c) = zdiv (zdiv a b) c) ≔
begin admit end;

opaque symbol zmod_zmult2_eq_raw (a b c : τ ι) :
  π (zless Int0 c) → π (a ∈ int) → π (b ∈ int) →
  π (zmod a (zmult b c) = zadd (zmult b (zmod (zdiv a b) c)) (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zmult2_eq (a b c : τ ι) :
  π (zless Int0 c) →
  π (zmod a (zmult b c) = zadd (zmult b (zmod (zdiv a b) c)) (zmod a b)) ≔
begin admit end;

// ===========================================================================
// Cancellation of common factors in "zdiv"
// ===========================================================================

opaque symbol zdiv_zmult_zmult1_aux1 (b c a : τ ι) :
  π (zless Int0 b) → π (intify c ≠ Int0) →
  π (zdiv (zmult c a) (zmult c b) = zdiv a b) ≔
begin admit end;

opaque symbol zdiv_zmult_zmult1_aux2 (b c a : τ ι) :
  π (zless b Int0) → π (intify c ≠ Int0) →
  π (zdiv (zmult c a) (zmult c b) = zdiv a b) ≔
begin admit end;

opaque symbol zdiv_zmult_zmult1_raw (c a b : τ ι) :
  π (intify c ≠ Int0) → π (b ∈ int) →
  π (zdiv (zmult c a) (zmult c b) = zdiv a b) ≔
begin admit end;

opaque symbol zdiv_zmult_zmult1 (c a b : τ ι) :
  π (intify c ≠ Int0) → π (zdiv (zmult c a) (zmult c b) = zdiv a b) ≔
begin admit end;

opaque symbol zdiv_zmult_zmult2 (c a b : τ ι) :
  π (intify c ≠ Int0) → π (zdiv (zmult a c) (zmult b c) = zdiv a b) ≔
begin admit end;

// ===========================================================================
// Distribution of factors over "zmod"
// ===========================================================================

opaque symbol zmod_zmult_zmult1_aux1 (b c a : τ ι) :
  π (zless Int0 b) → π (intify c ≠ Int0) →
  π (zmod (zmult c a) (zmult c b) = zmult c (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zmult_zmult1_aux2 (b c a : τ ι) :
  π (zless b Int0) → π (intify c ≠ Int0) →
  π (zmod (zmult c a) (zmult c b) = zmult c (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zmult_zmult1_raw (b c a : τ ι) :
  π (b ∈ int) → π (c ∈ int) →
  π (zmod (zmult c a) (zmult c b) = zmult c (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zmult_zmult1 (c a b : τ ι) :
  π (zmod (zmult c a) (zmult c b) = zmult c (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zmult_zmult2 (a c b : τ ι) :
  π (zmod (zmult a c) (zmult b c) = zmult (zmod a b) c) ≔
begin admit end;

// Quotients of signs

opaque symbol zdiv_neg_pos_less0 (a b : τ ι) :
  π (zless a Int0) → π (zless Int0 b) → π (zless (zdiv a b) Int0) ≔
begin admit end;

opaque symbol zdiv_nonneg_neg_le0 (a b : τ ι) :
  π (zle Int0 a) → π (zless b Int0) → π (zle (zdiv a b) Int0) ≔
begin admit end;

opaque symbol pos_imp_zdiv_nonneg_iff (a b : τ ι) :
  π (zless Int0 b) → π (zle Int0 (zdiv a b) ⇔ zle Int0 a) ≔
begin admit end;

opaque symbol neg_imp_zdiv_nonneg_iff (a b : τ ι) :
  π (zless b Int0) → π (zle Int0 (zdiv a b) ⇔ zle a Int0) ≔
begin admit end;

// But not (a zdiv b ≤ 0 iff a≤0); consider a=1, b=2 when a zdiv b = 0.
opaque symbol pos_imp_zdiv_neg_iff (a b : τ ι) :
  π (zless Int0 b) → π (zless (zdiv a b) Int0 ⇔ zless a Int0) ≔
begin admit end;

// Again the law fails for ≤: consider a = -1, b = -2 when a zdiv b = 0
opaque symbol neg_imp_zdiv_neg_iff (a b : τ ι) :
  π (zless b Int0) → π (zless (zdiv a b) Int0 ⇔ zless Int0 a) ≔
begin admit end;

// The remainder of IntDiv.thy (shifting-based speedups for zdiv/zmod, from
// "Speeding up the division algorithm with shifting" onward) is wrapped in
// the .thy's own literal comment "THESE REMAIN TO BE CONVERTED -- but aren't
// that useful!" — i.e. the ORIGINAL Isabelle author marked it dead/unconverted
// and Isabelle itself never parsed it. Zero provable content; skipped entirely
// per task instructions.
