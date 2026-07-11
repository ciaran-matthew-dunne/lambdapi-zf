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
constant symbol quorem (ab qr : τ ι) : Prop;
constant symbol quorem_def (ab qr : τ ι) :
  π (quorem ab qr =
     (fst ab = zadd (zmult (snd ab) (fst qr)) (snd qr) ∧
      ((zless Int0 (snd ab) ∧ zle Int0 (snd qr) ∧ zless (snd qr) (snd ab)) ∨
       (¬ (zless Int0 (snd ab)) ∧ zless (snd ab) (snd qr) ∧ zle (snd qr) Int0))));

// adjust(b,<q,r>) ≡ if #0 $≤ r$-b then <#2$*q $+ #1,r$-b> else <#2$*q,r>
constant symbol adjust (b qr : τ ι) : τ ι;
constant symbol adjust_def (b qr : τ ι) :
  π (adjust b qr =
     If (zle Int0 (zdiff (snd qr) b))
        (Pair (zadd (zmult Int2 (fst qr)) Int1) (zdiff (snd qr) b))
        (Pair (zmult Int2 (fst qr)) (snd qr)));

// ===========================================================================
// The division algorithm
// ===========================================================================

// posDivAlg(ab) ≡  -- for the case a≥0, b>0
//   wfrec(measure(int*int, λ<a,b>. nat_of(a$-b$+#1)), ab,
//         λ<a,b> f. if (a$<b | b$≤#0) then <#0,a> else adjust(b, f`<a,#2$*b>))
symbol posDivAlg : τ ι → τ ι;
// posDivAlg is a declared abstract symbol (no body), so this wfrec-unfolding
// equation IS its Isabelle definition — a declared `_def` axiom per Arith.lp's
// raw_div_def / Bin.lp's bin_rec_def precedent, not a provable lemma.
symbol posDivAlg_def (ab : τ ι) :
  π (posDivAlg ab =
     wfrec (measure (Sigma int (λ _, int))
              (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
       ab
       (λ ab2 f,
          If (zless (fst ab2) (snd ab2) ∨ zle (snd ab2) Int0)
             (Pair Int0 (fst ab2))
             (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2)))))));

// negDivAlg(ab) ≡  -- for the case a<0, b>0
//   wfrec(measure(int*int, λ<a,b>. nat_of($-a$-b)), ab,
//         λ<a,b> f. if (#0$≤a$+b | b$≤#0) then <#-1,a$+b> else adjust(b, f`<a,#2$*b>))
symbol negDivAlg : τ ι → τ ι;
// negDivAlg is a declared abstract symbol (no body); this wfrec-unfolding
// equation IS its Isabelle definition — a declared `_def` axiom, as posDivAlg_def.
symbol negDivAlg_def (ab : τ ι) :
  π (negDivAlg ab =
     wfrec (measure (Sigma int (λ _, int))
              (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
       ab
       (λ ab2 f,
          If (zle Int0 (zadd (fst ab2) (snd ab2)) ∨ zle (snd ab2) Int0)
             (Pair NegInt1 (zadd (fst ab2) (snd ab2)))
             (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2)))))));

// negateSnd(<q,r>) ≡ <q, $-r>
constant symbol negateSnd (qr : τ ι) : τ ι;
constant symbol negateSnd_def (qr : τ ι) :
  π (negateSnd qr = Pair (fst qr) (zminus (snd qr)));

// The full division algorithm considers all possible signs for a,b,
// including the special case a=0, b<0, because negDivAlg requires a<0.
constant symbol divAlg (ab : τ ι) : τ ι;
constant symbol divAlg_def (ab : τ ι) :
  π (divAlg ab =
     If (zle Int0 (fst ab))
        (If (zle Int0 (snd ab)) (posDivAlg ab)
           (If (fst ab = Int0) (Pair Int0 Int0)
              (negateSnd (negDivAlg (Pair (zminus (fst ab)) (zminus (snd ab)))))))
        (If (zless Int0 (snd ab)) (negDivAlg ab)
           (negateSnd (posDivAlg (Pair (zminus (fst ab)) (zminus (snd ab)))))));

constant symbol zdiv (a b : τ ι) : τ ι;
constant symbol zdiv_def (a b : τ ι) :
  π (zdiv a b = fst (divAlg (Pair (intify a) (intify b))));
notation zdiv infix left 70;

constant symbol zmod (a b : τ ι) : τ ι;
constant symbol zmod_def (a b : τ ι) :
  π (zmod a b = snd (divAlg (Pair (intify a) (intify b))));
notation zmod infix left 70;

// ===========================================================================
// port-internal helpers: intify book-keeping (used throughout below)
// ===========================================================================

// push intify through both args of zless
private opaque symbol zless_in (a b : τ ι) :
  π (zless a b) → π (zless (intify a) (intify b)) ≔
begin
  assume a b h;
  refine ∧ₑ₂ (zless_intify2 (intify a) b) (∧ₑ₂ (zless_intify1 a b) h)
end;

// strip intify from both args of zless
private opaque symbol zless_out (a b : τ ι) :
  π (zless (intify a) (intify b)) → π (zless a b) ≔
begin
  assume a b h;
  refine ∧ₑ₁ (zless_intify1 a b) (∧ₑ₁ (zless_intify2 (intify a) b) h)
end;

// push intify through both args of zle
private opaque symbol zle_in (a b : τ ι) :
  π (zle a b) → π (zle (intify a) (intify b)) ≔
begin
  assume a b h;
  refine ∧ₑ₂ (zle_intify2 (intify a) b) (∧ₑ₂ (zle_intify1 a b) h)
end;

// strip intify from both args of zle
private opaque symbol zle_out (a b : τ ι) :
  π (zle (intify a) (intify b)) → π (zle a b) ≔
begin
  assume a b h;
  refine ∧ₑ₁ (zle_intify1 a b) (∧ₑ₁ (zle_intify2 (intify a) b) h)
end;

// intify cancels on both args of zadd
private opaque symbol zadd_deintify (a b : τ ι) :
  π (zadd (intify a) (intify b) = zadd a b) ≔
begin
  assume a b;
  rewrite (zadd_intify1 a (intify b));
  rewrite (zadd_intify2 a b);
  reflexivity
end;

// intify cancels on both args of zmult
private opaque symbol zmult_deintify (a b : τ ι) :
  π (zmult (intify a) (intify b) = zmult a b) ≔
begin
  assume a b;
  rewrite (zmult_intify1 a (intify b));
  rewrite (zmult_intify2 a b);
  reflexivity
end;

// Int0 is an integer
private opaque symbol Int0_in_int : π (Int0 ∈ int) ≔
begin
  refine ind_eq (eq_sym int_of_0) (λ v, v ∈ int) (int_of_type empty)
end;

// ===========================================================================
// Some basic laws by Sidi Ehmety (need linear arithmetic!)
// ===========================================================================

opaque symbol zspos_add_zspos_imp_zspos (x y : τ ι) :
  π (zless Int0 x) → π (zless Int0 y) → π (zless Int0 (zadd x y)) ≔
begin
  assume x y hx hy;
  have h1 : π (zless (zadd Int0 y) (zadd x y))
    { refine zadd_zless_mono1 Int0 x y hx };
  have h2 : π (zless (intify y) (zadd x y))
    { refine ind_eq (eq_sym (zadd_0_intify y)) (λ v, zless v (zadd x y)) h1 };
  have hy2 : π (zless Int0 (intify y))
    { refine ∧ₑ₂ (zless_intify2 Int0 y) hy };
  refine zless_trans Int0 (intify y) (zadd x y) hy2 h2
end;

opaque symbol zpos_add_zpos_imp_zpos (x y : τ ι) :
  π (zle Int0 x) → π (zle Int0 y) → π (zle Int0 (zadd x y)) ≔
begin
  assume x y hx hy;
  have h1 : π (zle (zadd Int0 y) (zadd x y))
    { refine zadd_zle_mono1 Int0 x y hx };
  have h2 : π (zle (intify y) (zadd x y))
    { refine ind_eq (eq_sym (zadd_0_intify y)) (λ v, zle v (zadd x y)) h1 };
  have hy2 : π (zle Int0 (intify y))
    { refine ∧ₑ₂ (zle_intify2 Int0 y) hy };
  refine zle_trans Int0 (intify y) (zadd x y) hy2 h2
end;

opaque symbol zneg_add_zneg_imp_zneg (x y : τ ι) :
  π (zless x Int0) → π (zless y Int0) → π (zless (zadd x y) Int0) ≔
begin
  assume x y hx hy;
  have h1 : π (zless (zadd x y) (zadd Int0 y))
    { refine zadd_zless_mono1 x Int0 y hx };
  have h2 : π (zless (zadd x y) (intify y))
    { refine ind_eq (eq_sym (zadd_0_intify y)) (λ v, zless (zadd x y) v) h1 };
  have hy2 : π (zless (intify y) Int0)
    { refine ∧ₑ₂ (zless_intify1 y Int0) hy };
  refine zless_trans (zadd x y) (intify y) Int0 h2 hy2
end;

// this theorem is used below
opaque symbol zneg_or_0_add_zneg_or_0_imp_zneg_or_0 (x y : τ ι) :
  π (zle x Int0) → π (zle y Int0) → π (zle (zadd x y) Int0) ≔
begin
  assume x y hx hy;
  have h1 : π (zle (zadd x y) (zadd Int0 y))
    { refine zadd_zle_mono1 x Int0 y hx };
  have h2 : π (zle (zadd x y) (intify y))
    { refine ind_eq (eq_sym (zadd_0_intify y)) (λ v, zle (zadd x y) v) h1 };
  have hy2 : π (zle (intify y) Int0)
    { refine ∧ₑ₂ (zle_intify1 y Int0) hy };
  refine zle_trans (zadd x y) (intify y) Int0 h2 hy2
end;

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
begin
  assume w m z;
  have hlem : π (zle (zadd w (int_of (succ m))) (intify z) ⇔
                 zless (zadd w (int_of m)) (intify z))
    { refine zadd_succ_lemma (intify z) w m (intify_in_int z) };
  apply ∧ᵢ
  { assume h;
    refine ∧ₑ₁ (zless_intify2 (zadd w (int_of m)) z)
      (∧ₑ₁ hlem (∧ₑ₂ (zle_intify2 (zadd w (int_of (succ m))) z) h)) }
  { assume h;
    refine ∧ₑ₁ (zle_intify2 (zadd w (int_of (succ m))) z)
      (∧ₑ₂ hlem (∧ₑ₂ (zless_intify2 (zadd w (int_of m)) z) h)) }
end;

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
begin
  assume w z;
  rewrite (zadd_commute Int1 w);
  refine add1_zle_iff w z
end;

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
begin
  assume i j k h1 h2;
  rewrite (zmult_commute k i);
  rewrite (zmult_commute k j);
  refine zmult_zle_mono1 i j k h1 h2
end;

opaque symbol zmult_zle_mono2_neg (i j k : τ ι) :
  π (zle i j) → π (zle k Int0) → π (zle (zmult k j) (zmult k i)) ≔
begin
  assume i j k h1 h2;
  rewrite (zmult_commute k j);
  rewrite (zmult_commute k i);
  refine zmult_zle_mono1_neg i j k h1 h2
end;

// ≤ monotonicity, BOTH arguments
opaque symbol zmult_zle_mono (i j k l : τ ι) :
  π (zle i j) → π (zle k l) → π (zle Int0 j) → π (zle Int0 k) →
  π (zle (zmult i k) (zmult j l)) ≔
begin
  assume i j k l h1 h2 h3 h4;
  refine zle_trans (zmult i k) (zmult j k) (zmult j l)
    (zmult_zle_mono1 i j k h1 h4)
    (zmult_zle_mono2 k l j h2 h3)
end;

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
begin
  assume i j k h1 h2;
  rewrite (zmult_commute i k);
  rewrite (zmult_commute j k);
  refine zmult_zless_mono2 i j k h1 h2
end;

// < monotonicity, BOTH arguments
opaque symbol zmult_zless_mono (i j k l : τ ι) :
  π (zless i j) → π (zless k l) → π (zless Int0 j) → π (zless Int0 k) →
  π (zless (zmult i k) (zmult j l)) ≔
begin
  assume i j k l h1 h2 h3 h4;
  refine zless_trans (zmult i k) (zmult j k) (zmult j l)
    (zmult_zless_mono1 i j k h1 h4)
    (zmult_zless_mono2 k l j h2 h3)
end;

opaque symbol zmult_zless_mono1_neg (i j k : τ ι) :
  π (zless i j) → π (zless k Int0) → π (zless (zmult j k) (zmult i k)) ≔
begin admit end;

opaque symbol zmult_zless_mono2_neg (i j k : τ ι) :
  π (zless i j) → π (zless k Int0) → π (zless (zmult k j) (zmult k i)) ≔
begin
  assume i j k h1 h2;
  rewrite (zmult_commute k j);
  rewrite (zmult_commute k i);
  refine zmult_zless_mono1_neg i j k h1 h2
end;

// ===========================================================================
// Products of zeroes
// ===========================================================================

opaque symbol zmult_eq_lemma (m n : τ ι) :
  π (m ∈ int) → π (n ∈ int) → π ((m = Int0 ∨ n = Int0) ⇔ zmult m n = Int0) ≔
begin admit end;

opaque symbol zmult_eq_0_iff (m n : τ ι) :
  π (zmult m n = Int0 ⇔ (intify m = Int0 ∨ intify n = Int0)) ≔
begin
  assume m n;
  rewrite left (zmult_deintify m n);
  have hlem : π ((intify m = Int0 ∨ intify n = Int0) ⇔ (zmult (intify m) (intify n) = Int0))
    { refine zmult_eq_lemma (intify m) (intify n) (intify_in_int m) (intify_in_int n) };
  apply ∧ᵢ
  { assume h; refine ∧ₑ₂ hlem h }
  { assume h; refine ∧ₑ₁ hlem h }
end;

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
begin
  assume k m n;
  rewrite (zmult_commute k m);
  rewrite (zmult_commute k n);
  refine zmult_zless_cancel2 m k n
end;

opaque symbol zmult_zle_cancel2 (m k n : τ ι) :
  π (zle (zmult m k) (zmult n k) ⇔
     ((zless Int0 k ⇒ zle m n) ∧ (zless k Int0 ⇒ zle n m))) ≔
begin admit end;

opaque symbol zmult_zle_cancel1 (k m n : τ ι) :
  π (zle (zmult k m) (zmult k n) ⇔
     ((zless Int0 k ⇒ zle m n) ∧ (zless k Int0 ⇒ zle n m))) ≔
begin
  assume k m n;
  rewrite (zmult_commute k m);
  rewrite (zmult_commute k n);
  refine zmult_zle_cancel2 m k n
end;

opaque symbol int_eq_iff_zle (m n : τ ι) :
  π (m ∈ int) → π (n ∈ int) → π (m = n ⇔ (zle m n ∧ zle n m)) ≔
begin
  assume m n hm hn;
  apply ∧ᵢ
  { assume h; refine ∧ᵢ (zle_eq_refl m n h) (zle_eq_refl n m (eq_sym h)) }
  { assume h; refine zle_anti_sym m n (∧ₑ₁ h) (∧ₑ₂ h) hm hn }
end;

opaque symbol zmult_cancel2_lemma (k m n : τ ι) :
  π (k ∈ int) → π (m ∈ int) → π (n ∈ int) →
  π (zmult m k = zmult n k ⇔ (k = Int0 ∨ m = n)) ≔
begin admit end;

opaque symbol zmult_cancel2 (m k n : τ ι) :
  π (zmult m k = zmult n k ⇔ (intify k = Int0 ∨ intify m = intify n)) ≔
begin
  assume m k n;
  rewrite left (zmult_deintify m k);
  rewrite left (zmult_deintify n k);
  refine zmult_cancel2_lemma (intify k) (intify m) (intify n)
    (intify_in_int k) (intify_in_int m) (intify_in_int n)
end;

opaque symbol zmult_cancel1 (k m n : τ ι) :
  π (zmult k m = zmult k n ⇔ (intify k = Int0 ∨ intify m = intify n)) ≔
begin
  assume k m n;
  rewrite (zmult_commute k m);
  rewrite (zmult_commute k n);
  refine zmult_cancel2 m k n
end;

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
begin
  assume b q r;
  rewrite adjust_def;
  rewrite fst_conv;
  rewrite snd_conv;
  reflexivity
end;

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
begin
  assume m;
  have hInt0 : π (Int0 ∈ int)
    { refine ind_eq (eq_sym int_of_0) (λ v, v ∈ int) (int_of_type empty) };
  have hbase : π (intify m = Int0 ⇔ (zle (intify m) Int0 ∧ zle Int0 (intify m)))
    { refine int_eq_iff_zle (intify m) Int0 (intify_in_int m) hInt0 };
  apply ∧ᵢ
  { assume h;
    have hc : π (zle (intify m) Int0 ∧ zle Int0 (intify m)) { refine ∧ₑ₁ hbase h };
    refine ∧ᵢ (∧ₑ₁ (zle_intify1 m Int0) (∧ₑ₁ hc)) (∧ₑ₁ (zle_intify2 Int0 m) (∧ₑ₂ hc)) }
  { assume h;
    refine ∧ₑ₂ hbase
      (∧ᵢ (∧ₑ₂ (zle_intify1 m Int0) (∧ₑ₁ h)) (∧ₑ₂ (zle_intify2 Int0 m) (∧ₑ₂ h))) }
end;

// ===========================================================================
// Some convenient biconditionals for products of signs
// ===========================================================================

opaque symbol zmult_pos (i j : τ ι) :
  π (zless Int0 i) → π (zless Int0 j) → π (zless Int0 (zmult i j)) ≔
begin
  assume i j hi hj;
  have h1 : π (zless (zmult Int0 j) (zmult i j))
    { refine zmult_zless_mono1 Int0 i j hi hj };
  refine ind_eq (eq_sym (zmult_0 j)) (λ v, zless v (zmult i j)) h1
end;

opaque symbol zmult_neg (i j : τ ι) :
  π (zless i Int0) → π (zless j Int0) → π (zless Int0 (zmult i j)) ≔
begin
  assume i j hi hj;
  have h1 : π (zless (zmult Int0 j) (zmult i j))
    { refine zmult_zless_mono1_neg i Int0 j hi hj };
  refine ind_eq (eq_sym (zmult_0 j)) (λ v, zless v (zmult i j)) h1
end;

opaque symbol zmult_pos_neg (i j : τ ι) :
  π (zless Int0 i) → π (zless j Int0) → π (zless (zmult i j) Int0) ≔
begin
  assume i j hi hj;
  have h1 : π (zless (zmult i j) (zmult Int0 j))
    { refine zmult_zless_mono1_neg Int0 i j hi hj };
  refine ind_eq (eq_sym (zmult_0 j)) (λ v, zless (zmult i j) v) h1
end;

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
begin
  assume b hb0 hb;
  rewrite quorem_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∧ᵢ _ _
  { rewrite (zmult_0_right b);
    rewrite (zadd_0_right_intify Int0);
    refine eq_sym (intify_ident Int0 Int0_in_int) }
  { refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) _ _
    { assume hlt;
      refine ∨ᵢ₂ (∧ᵢ (zless_not_sym b Int0 hlt) (∧ᵢ hlt (zle_refl Int0))) }
    { assume hgt;
      refine ∨ᵢ₁ (∧ᵢ hgt (∧ᵢ (zle_refl Int0) hgt)) } }
end;

opaque symbol posDivAlg_zero_divisor (a : τ ι) :
  π (posDivAlg (Pair a Int0) = Pair Int0 a) ≔
begin
  assume a;
  rewrite posDivAlg_unfold;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_P (zless a Int0 ∨ zle Int0 Int0) _ _ (∨ᵢ₂ (zle_refl Int0)));
  reflexivity
end;

opaque symbol posDivAlg_0 (b : τ ι) :
  π (posDivAlg (Pair Int0 b) = Pair Int0 Int0) ≔
begin
  assume b;
  rewrite posDivAlg_unfold;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  have hcond : π (zless Int0 b ∨ zle b Int0)
    { refine ∨ₑ (zless_linear Int0 b) _ _
      { assume h; refine ∨ᵢ₁ h }
      { assume h;
        refine ∨ₑ h _ _
        { assume heq; refine ∨ᵢ₂ (ind_eq (zle_def b Int0) (λ p, p) (∨ᵢ₂ (eq_sym heq))) }
        { assume hlt; refine ∨ᵢ₂ (zless_imp_zle b Int0 hlt) } } };
  rewrite (If_P (zless Int0 b ∨ zle b Int0) _ _ hcond);
  reflexivity
end;

// Needed below. Actually it's an equivalence.
opaque symbol linear_arith_lemma (b : τ ι) :
  π (¬ zle Int0 (zadd NegInt1 b)) → π (zle b Int0) ≔
begin admit end;

opaque symbol negDivAlg_minus1 (b : τ ι) :
  π (negDivAlg (Pair NegInt1 b) = Pair NegInt1 (zdiff b Int1)) ≔
begin admit end;

opaque symbol negateSnd_eq (q r : τ ι) :
  π (negateSnd (Pair q r) = Pair q (zminus r)) ≔
begin
  assume q r;
  rewrite negateSnd_def;
  rewrite fst_conv;
  rewrite snd_conv;
  reflexivity
end;

opaque symbol negateSnd_type (qr : τ ι) :
  π (qr ∈ Sigma int (λ _, int)) → π (negateSnd qr ∈ Sigma int (λ _, int)) ≔
begin
  assume qr hqr;
  rewrite negateSnd_def;
  refine SigmaI (fst qr) (zminus (snd qr)) int (λ _, int)
    (SigmaD1 qr int (λ _, int) hqr)
    (zminus_type (snd qr))
end;

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
begin
  assume a b ha hb;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∨ₑ (em (zle Int0 a)) _ _
  { assume h1;
    rewrite (If_P (zle Int0 a) _ _ h1);
    refine ∨ₑ (em (zle Int0 b)) _ _
    { assume h2;
      rewrite (If_P (zle Int0 b) _ _ h2);
      refine posDivAlg_type a b ha hb }
    { assume h2;
      rewrite (If_not_P (zle Int0 b) _ _ h2);
      refine ∨ₑ (em (a = Int0)) _ _
      { assume h3;
        rewrite (If_P (a = Int0) _ _ h3);
        refine SigmaI Int0 Int0 int (λ _, int) Int0_in_int Int0_in_int }
      { assume h3;
        rewrite (If_not_P (a = Int0) _ _ h3);
        refine negateSnd_type (negDivAlg (Pair (zminus a) (zminus b)))
          (negDivAlg_type (zminus a) (zminus b) (zminus_type a) (zminus_type b)) } } }
  { assume h1;
    rewrite (If_not_P (zle Int0 a) _ _ h1);
    refine ∨ₑ (em (zless Int0 b)) _ _
    { assume h2;
      rewrite (If_P (zless Int0 b) _ _ h2);
      refine negDivAlg_type a b ha hb }
    { assume h2;
      rewrite (If_not_P (zless Int0 b) _ _ h2);
      refine negateSnd_type (posDivAlg (Pair (zminus a) (zminus b)))
        (posDivAlg_type (zminus a) (zminus b) (zminus_type a) (zminus_type b)) } }
end;

// intify cancellation

opaque symbol zdiv_intify1 (x y : τ ι) : π (zdiv (intify x) y = zdiv x y) ≔
begin
  assume x y;
  rewrite zdiv_def; rewrite zdiv_def; rewrite intify_idem; reflexivity
end;

opaque symbol zdiv_intify2 (x y : τ ι) : π (zdiv x (intify y) = zdiv x y) ≔
begin
  assume x y;
  rewrite zdiv_def; rewrite zdiv_def; rewrite intify_idem; reflexivity
end;

opaque symbol zdiv_type (z w : τ ι) : π (zdiv z w ∈ int) ≔
begin
  assume z w;
  rewrite zdiv_def;
  refine SigmaD1 (divAlg (Pair (intify z) (intify w))) int (λ _, int)
    (divAlg_type (intify z) (intify w) (intify_in_int z) (intify_in_int w))
end;

opaque symbol zmod_intify1 (x y : τ ι) : π (zmod (intify x) y = zmod x y) ≔
begin
  assume x y;
  rewrite zmod_def; rewrite zmod_def; rewrite intify_idem; reflexivity
end;

opaque symbol zmod_intify2 (x y : τ ι) : π (zmod x (intify y) = zmod x y) ≔
begin
  assume x y;
  rewrite zmod_def; rewrite zmod_def; rewrite intify_idem; reflexivity
end;

opaque symbol zmod_type (z w : τ ι) : π (zmod z w ∈ int) ≔
begin
  assume z w;
  rewrite zmod_def;
  refine SigmaD2 (divAlg (Pair (intify z) (intify w))) int (λ _, int)
    (divAlg_type (intify z) (intify w) (intify_in_int z) (intify_in_int w))
end;

// port-internal helper: intify cancels on both args of zdiv
private opaque symbol zdiv_deintify (a b : τ ι) :
  π (zdiv (intify a) (intify b) = zdiv a b) ≔
begin
  assume a b;
  rewrite (zdiv_intify1 a (intify b));
  rewrite (zdiv_intify2 a b);
  reflexivity
end;

// port-internal helper: intify cancels on both args of zmod
private opaque symbol zmod_deintify (a b : τ ι) :
  π (zmod (intify a) (intify b) = zmod a b) ≔
begin
  assume a b;
  rewrite (zmod_intify1 a (intify b));
  rewrite (zmod_intify2 a b);
  reflexivity
end;

// Arbitrary definitions for division by zero. Useful to simplify certain equations

opaque symbol DIVISION_BY_ZERO_ZDIV (a : τ ι) : π (zdiv a Int0 = Int0) ≔
begin
  assume a;
  have hnn : π (¬ zless Int0 Int0) { assume hx; refine zless_not_sym Int0 Int0 hx hx };
  rewrite zdiv_def;
  rewrite (intify_ident Int0 Int0_in_int);
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∨ₑ (em (zle Int0 (intify a))) _ _
  { assume h;
    rewrite (If_P (zle Int0 (intify a)) _ _ h);
    rewrite (If_P (zle Int0 Int0) _ _ (zle_refl Int0));
    rewrite (posDivAlg_zero_divisor (intify a));
    rewrite fst_conv;
    reflexivity }
  { assume h;
    rewrite (If_not_P (zle Int0 (intify a)) _ _ h);
    rewrite (If_not_P (zless Int0 Int0) _ _ hnn);
    rewrite zminus_0;
    rewrite (posDivAlg_zero_divisor (zminus (intify a)));
    rewrite (negateSnd_eq Int0 (zminus (intify a)));
    rewrite fst_conv;
    reflexivity }
end;

opaque symbol DIVISION_BY_ZERO_ZMOD (a : τ ι) : π (zmod a Int0 = intify a) ≔
begin
  assume a;
  have hnn : π (¬ zless Int0 Int0) { assume hx; refine zless_not_sym Int0 Int0 hx hx };
  rewrite zmod_def;
  rewrite (intify_ident Int0 Int0_in_int);
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∨ₑ (em (zle Int0 (intify a))) _ _
  { assume h;
    rewrite (If_P (zle Int0 (intify a)) _ _ h);
    rewrite (If_P (zle Int0 Int0) _ _ (zle_refl Int0));
    rewrite (posDivAlg_zero_divisor (intify a));
    rewrite snd_conv;
    reflexivity }
  { assume h;
    rewrite (If_not_P (zle Int0 (intify a)) _ _ h);
    rewrite (If_not_P (zless Int0 Int0) _ _ hnn);
    rewrite zminus_0;
    rewrite (posDivAlg_zero_divisor (zminus (intify a)));
    rewrite (negateSnd_eq Int0 (zminus (intify a)));
    rewrite snd_conv;
    rewrite (zminus_zminus_intify (intify a));
    rewrite intify_idem;
    reflexivity }
end;

// Basic laws about division and remainder

opaque symbol raw_zmod_zdiv_equality (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) →
  π (a = zadd (zmult b (zdiv a b)) (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zdiv_equality (a b : τ ι) :
  π (intify a = zadd (zmult b (zdiv a b)) (zmod a b)) ≔
begin
  assume a b;
  rewrite left (zdiv_deintify a b);
  rewrite left (zmod_deintify a b);
  rewrite left (zmult_intify1 b (zdiv (intify a) (intify b)));
  refine raw_zmod_zdiv_equality (intify a) (intify b) (intify_in_int a) (intify_in_int b)
end;

opaque symbol pos_mod (a b : τ ι) :
  π (zless Int0 b) → π (zle Int0 (zmod a b) ∧ zless (zmod a b) b) ≔
begin admit end;

// pos_mod_sign = pos_mod [THEN conjunct1]
opaque symbol pos_mod_sign (a b : τ ι) :
  π (zless Int0 b) → π (zle Int0 (zmod a b)) ≔
begin
  assume a b h; refine ∧ₑ₁ (pos_mod a b h)
end;

// pos_mod_bound = pos_mod [THEN conjunct2]
opaque symbol pos_mod_bound (a b : τ ι) :
  π (zless Int0 b) → π (zless (zmod a b) b) ≔
begin
  assume a b h; refine ∧ₑ₂ (pos_mod a b h)
end;

opaque symbol neg_mod (a b : τ ι) :
  π (zless b Int0) → π (zle (zmod a b) Int0 ∧ zless b (zmod a b)) ≔
begin admit end;

// neg_mod_sign = neg_mod [THEN conjunct1]
opaque symbol neg_mod_sign (a b : τ ι) :
  π (zless b Int0) → π (zle (zmod a b) Int0) ≔
begin
  assume a b h; refine ∧ₑ₁ (neg_mod a b h)
end;

// neg_mod_bound = neg_mod [THEN conjunct2]
opaque symbol neg_mod_bound (a b : τ ι) :
  π (zless b Int0) → π (zless b (zmod a b)) ≔
begin
  assume a b h; refine ∧ₑ₂ (neg_mod a b h)
end;

// proving general properties of zdiv and zmod

opaque symbol quorem_div_mod (a b : τ ι) :
  π (b ≠ Int0) → π (a ∈ int) → π (b ∈ int) →
  π (quorem (Pair a b) (Pair (zdiv a b) (zmod a b))) ≔
begin admit end;

// Surely quorem(⟨a,b⟩,⟨q,r⟩) implies a∈int, but it doesn't matter
opaque symbol quorem_div (a b q r : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (b ≠ Int0) → π (a ∈ int) → π (b ∈ int) →
  π (q ∈ int) → π (zdiv a b = q) ≔
begin
  assume a b q r hq hb0 ha hb hqint;
  refine unique_quotient a b (zdiv a b) (zmod a b) q r
    (quorem_div_mod a b hb0 ha hb)
    hq hb hb0 (zdiv_type a b) hqint
end;

opaque symbol quorem_mod (a b q r : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (b ≠ Int0) → π (a ∈ int) → π (b ∈ int) →
  π (q ∈ int) → π (r ∈ int) → π (zmod a b = r) ≔
begin
  assume a b q r hq hb0 ha hb hqint hrint;
  refine unique_remainder a b (zdiv a b) (zmod a b) q r
    (quorem_div_mod a b hb0 ha hb)
    hq hb hb0 (zdiv_type a b) hqint (zmod_type a b) hrint
end;

opaque symbol zdiv_pos_pos_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle Int0 a) → π (zless a b) →
  π (zdiv a b = Int0) ≔
begin admit end;

opaque symbol zdiv_pos_pos_trivial (a b : τ ι) :
  π (zle Int0 a) → π (zless a b) → π (zdiv a b = Int0) ≔
begin
  assume a b h1 h2;
  rewrite left (zdiv_deintify a b);
  refine zdiv_pos_pos_trivial_raw (intify a) (intify b)
    (intify_in_int a) (intify_in_int b)
    (∧ₑ₂ (zle_intify2 Int0 a) h1)
    (zless_in a b h2)
end;

opaque symbol zdiv_neg_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle a Int0) → π (zless b a) →
  π (zdiv a b = Int0) ≔
begin admit end;

opaque symbol zdiv_neg_neg_trivial (a b : τ ι) :
  π (zle a Int0) → π (zless b a) → π (zdiv a b = Int0) ≔
begin
  assume a b h1 h2;
  rewrite left (zdiv_deintify a b);
  refine zdiv_neg_neg_trivial_raw (intify a) (intify b)
    (intify_in_int a) (intify_in_int b)
    (∧ₑ₂ (zle_intify1 a Int0) h1)
    (zless_in b a h2)
end;

opaque symbol zadd_le_0_lemma (a b : τ ι) :
  π (zle (zadd a b) Int0) → π (zless Int0 a) → π (zless Int0 b) → π ⊥ ≔
begin admit end;

opaque symbol zdiv_pos_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zless Int0 a) → π (zle (zadd a b) Int0) →
  π (zdiv a b = NegInt1) ≔
begin admit end;

opaque symbol zdiv_pos_neg_trivial (a b : τ ι) :
  π (zless Int0 a) → π (zle (zadd a b) Int0) → π (zdiv a b = NegInt1) ≔
begin
  assume a b h1 h2;
  rewrite left (zdiv_deintify a b);
  refine zdiv_pos_neg_trivial_raw (intify a) (intify b)
    (intify_in_int a) (intify_in_int b)
    (∧ₑ₂ (zless_intify2 Int0 a) h1)
    (ind_eq (zadd_deintify a b) (λ v, zle v Int0) h2)
end;

// There is no zdiv_neg_pos_trivial because 0 zdiv b = 0 would supersede it

opaque symbol zmod_pos_pos_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle Int0 a) → π (zless a b) →
  π (zmod a b = a) ≔
begin admit end;

opaque symbol zmod_pos_pos_trivial (a b : τ ι) :
  π (zle Int0 a) → π (zless a b) → π (zmod a b = intify a) ≔
begin
  assume a b h1 h2;
  rewrite left (zmod_deintify a b);
  refine zmod_pos_pos_trivial_raw (intify a) (intify b)
    (intify_in_int a) (intify_in_int b)
    (∧ₑ₂ (zle_intify2 Int0 a) h1)
    (zless_in a b h2)
end;

opaque symbol zmod_neg_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle a Int0) → π (zless b a) →
  π (zmod a b = a) ≔
begin admit end;

opaque symbol zmod_neg_neg_trivial (a b : τ ι) :
  π (zle a Int0) → π (zless b a) → π (zmod a b = intify a) ≔
begin
  assume a b h1 h2;
  rewrite left (zmod_deintify a b);
  refine zmod_neg_neg_trivial_raw (intify a) (intify b)
    (intify_in_int a) (intify_in_int b)
    (∧ₑ₂ (zle_intify1 a Int0) h1)
    (zless_in b a h2)
end;

opaque symbol zmod_pos_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zless Int0 a) → π (zle (zadd a b) Int0) →
  π (zmod a b = zadd a b) ≔
begin admit end;

opaque symbol zmod_pos_neg_trivial (a b : τ ι) :
  π (zless Int0 a) → π (zle (zadd a b) Int0) → π (zmod a b = zadd a b) ≔
begin
  assume a b h1 h2;
  rewrite left (zmod_deintify a b);
  rewrite left (zadd_deintify a b);
  refine zmod_pos_neg_trivial_raw (intify a) (intify b)
    (intify_in_int a) (intify_in_int b)
    (∧ₑ₂ (zless_intify2 Int0 a) h1)
    (ind_eq (zadd_deintify a b) (λ v, zle v Int0) h2)
end;

// There is no zmod_neg_pos_trivial...

// Simpler laws such as -a zdiv b = -(a zdiv b) FAIL

opaque symbol zdiv_zminus_zminus_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zdiv (zminus a) (zminus b) = zdiv a b) ≔
begin admit end;

opaque symbol zdiv_zminus_zminus (a b : τ ι) :
  π (zdiv (zminus a) (zminus b) = zdiv a b) ≔
begin
  assume a b;
  rewrite left (zminus_intify a);
  rewrite left (zminus_intify b);
  rewrite left (zdiv_deintify a b);
  refine zdiv_zminus_zminus_raw (intify a) (intify b) (intify_in_int a) (intify_in_int b)
end;

// Simpler laws such as -a zmod b = -(a zmod b) FAIL
opaque symbol zmod_zminus_zminus_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zmod (zminus a) (zminus b) = zminus (zmod a b)) ≔
begin admit end;

opaque symbol zmod_zminus_zminus (a b : τ ι) :
  π (zmod (zminus a) (zminus b) = zminus (zmod a b)) ≔
begin
  assume a b;
  rewrite left (zminus_intify a);
  rewrite left (zminus_intify b);
  rewrite left (zmod_deintify a b);
  refine zmod_zminus_zminus_raw (intify a) (intify b) (intify_in_int a) (intify_in_int b)
end;

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
begin
  assume a h0 ha;
  refine self_quotient a (zdiv a a) (zmod a a)
    (quorem_div_mod a a h0 ha ha) ha (zdiv_type a a) h0
end;

opaque symbol zdiv_self (a : τ ι) :
  π (intify a ≠ Int0) → π (zdiv a a = Int1) ≔
begin
  assume a h;
  rewrite left (zdiv_deintify a a);
  refine zdiv_self_raw (intify a) h (intify_in_int a)
end;

// Here we have 0 zmod 0 = 0, also assumed by Knuth (who puts m zmod 0 = 0)
opaque symbol zmod_self_raw (a : τ ι) :
  π (a ∈ int) → π (zmod a a = Int0) ≔
begin
  assume a ha;
  refine ∨ₑ (em (a = Int0)) _ _
  { assume h0;
    rewrite h0;
    rewrite (DIVISION_BY_ZERO_ZMOD Int0);
    refine intify_ident Int0 Int0_in_int }
  { assume h0;
    refine self_remainder a (zdiv a a) (zmod a a)
      (quorem_div_mod a a h0 ha ha) ha (zdiv_type a a) (zmod_type a a) h0 }
end;

opaque symbol zmod_self (a : τ ι) : π (zmod a a = Int0) ≔
begin
  assume a;
  rewrite left (zmod_deintify a a);
  refine zmod_self_raw (intify a) (intify_in_int a)
end;

// ===========================================================================
// Computation of division and remainder
// ===========================================================================

opaque symbol zdiv_zero (b : τ ι) : π (zdiv Int0 b = Int0) ≔
begin
  assume b;
  rewrite zdiv_def;
  rewrite (intify_ident Int0 Int0_in_int);
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_P (zle Int0 Int0) _ _ (zle_refl Int0));
  refine ∨ₑ (em (zle Int0 (intify b))) _ _
  { assume hle;
    rewrite (If_P (zle Int0 (intify b)) _ _ hle);
    rewrite (posDivAlg_0 (intify b));
    rewrite fst_conv;
    reflexivity }
  { assume hnle;
    rewrite (If_not_P (zle Int0 (intify b)) _ _ hnle);
    rewrite (If_P (Int0 = Int0) _ _ (eq_refl Int0));
    rewrite fst_conv;
    reflexivity }
end;

opaque symbol zdiv_eq_minus1 (b : τ ι) :
  π (zless Int0 b) → π (zdiv NegInt1 b = NegInt1) ≔
begin admit end;

opaque symbol zmod_zero (b : τ ι) : π (zmod Int0 b = Int0) ≔
begin
  assume b;
  rewrite zmod_def;
  rewrite (intify_ident Int0 Int0_in_int);
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_P (zle Int0 Int0) _ _ (zle_refl Int0));
  refine ∨ₑ (em (zle Int0 (intify b))) _ _
  { assume hle;
    rewrite (If_P (zle Int0 (intify b)) _ _ hle);
    rewrite (posDivAlg_0 (intify b));
    rewrite snd_conv;
    reflexivity }
  { assume hnle;
    rewrite (If_not_P (zle Int0 (intify b)) _ _ hnle);
    rewrite (If_P (Int0 = Int0) _ _ (eq_refl Int0));
    rewrite snd_conv;
    reflexivity }
end;

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
begin
  assume a b h1 h2;
  rewrite zdiv_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_P (zle Int0 (intify a)) _ _ (∧ₑ₂ (zle_intify2 Int0 a) (zless_imp_zle Int0 a h1)));
  rewrite (If_P (zle Int0 (intify b)) _ _ (∧ₑ₂ (zle_intify2 Int0 b) h2));
  reflexivity
end;

opaque symbol zmod_pos_pos (a b : τ ι) :
  π (zless Int0 a) → π (zle Int0 b) →
  π (zmod a b = snd (posDivAlg (Pair (intify a) (intify b)))) ≔
begin
  assume a b h1 h2;
  rewrite zmod_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_P (zle Int0 (intify a)) _ _ (∧ₑ₂ (zle_intify2 Int0 a) (zless_imp_zle Int0 a h1)));
  rewrite (If_P (zle Int0 (intify b)) _ _ (∧ₑ₂ (zle_intify2 Int0 b) h2));
  reflexivity
end;

// a negative, b positive

opaque symbol zdiv_neg_pos (a b : τ ι) :
  π (zless a Int0) → π (zless Int0 b) →
  π (zdiv a b = fst (negDivAlg (Pair (intify a) (intify b)))) ≔
begin
  assume a b h1 h2;
  rewrite zdiv_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_not_P (zle Int0 (intify a)) _ _
    (∧ₑ₂ (not_zle_iff_zless Int0 (intify a)) (∧ₑ₂ (zless_intify1 a Int0) h1)));
  rewrite (If_P (zless Int0 (intify b)) _ _ (∧ₑ₂ (zless_intify2 Int0 b) h2));
  reflexivity
end;

opaque symbol zmod_neg_pos (a b : τ ι) :
  π (zless a Int0) → π (zless Int0 b) →
  π (zmod a b = snd (negDivAlg (Pair (intify a) (intify b)))) ≔
begin
  assume a b h1 h2;
  rewrite zmod_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_not_P (zle Int0 (intify a)) _ _
    (∧ₑ₂ (not_zle_iff_zless Int0 (intify a)) (∧ₑ₂ (zless_intify1 a Int0) h1)));
  rewrite (If_P (zless Int0 (intify b)) _ _ (∧ₑ₂ (zless_intify2 Int0 b) h2));
  reflexivity
end;

// a positive, b negative

opaque symbol zdiv_pos_neg (a b : τ ι) :
  π (zless Int0 a) → π (zless b Int0) →
  π (zdiv a b = fst (negateSnd (negDivAlg (Pair (zminus a) (zminus b))))) ≔
begin
  assume a b h1 h2;
  rewrite zdiv_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_P (zle Int0 (intify a)) _ _ (∧ₑ₂ (zle_intify2 Int0 a) (zless_imp_zle Int0 a h1)));
  rewrite (If_not_P (zle Int0 (intify b)) _ _
    (∧ₑ₂ (not_zle_iff_zless Int0 (intify b)) (∧ₑ₂ (zless_intify1 b Int0) h2)));
  have hna : π (¬ (intify a = Int0))
    { assume heq;
      have hlt : π (zless Int0 (intify a)) { refine ∧ₑ₂ (zless_intify2 Int0 a) h1 };
      have hlt0 : π (zless Int0 Int0) { refine ind_eq (eq_sym heq) (λ v, zless Int0 v) hlt };
      refine zless_not_sym Int0 Int0 hlt0 hlt0 };
  rewrite (If_not_P (intify a = Int0) _ _ hna);
  rewrite (zminus_intify a);
  rewrite (zminus_intify b);
  reflexivity
end;

opaque symbol zmod_pos_neg (a b : τ ι) :
  π (zless Int0 a) → π (zless b Int0) →
  π (zmod a b = snd (negateSnd (negDivAlg (Pair (zminus a) (zminus b))))) ≔
begin
  assume a b h1 h2;
  rewrite zmod_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_P (zle Int0 (intify a)) _ _ (∧ₑ₂ (zle_intify2 Int0 a) (zless_imp_zle Int0 a h1)));
  rewrite (If_not_P (zle Int0 (intify b)) _ _
    (∧ₑ₂ (not_zle_iff_zless Int0 (intify b)) (∧ₑ₂ (zless_intify1 b Int0) h2)));
  have hna : π (¬ (intify a = Int0))
    { assume heq;
      have hlt : π (zless Int0 (intify a)) { refine ∧ₑ₂ (zless_intify2 Int0 a) h1 };
      have hlt0 : π (zless Int0 Int0) { refine ind_eq (eq_sym heq) (λ v, zless Int0 v) hlt };
      refine zless_not_sym Int0 Int0 hlt0 hlt0 };
  rewrite (If_not_P (intify a = Int0) _ _ hna);
  rewrite (zminus_intify a);
  rewrite (zminus_intify b);
  reflexivity
end;

// a negative, b negative

opaque symbol zdiv_neg_neg (a b : τ ι) :
  π (zless a Int0) → π (zle b Int0) →
  π (zdiv a b = fst (negateSnd (posDivAlg (Pair (zminus a) (zminus b))))) ≔
begin
  assume a b h1 h2;
  rewrite zdiv_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_not_P (zle Int0 (intify a)) _ _
    (∧ₑ₂ (not_zle_iff_zless Int0 (intify a)) (∧ₑ₂ (zless_intify1 a Int0) h1)));
  rewrite (If_not_P (zless Int0 (intify b)) _ _
    (∧ₑ₂ (not_zless_iff_zle Int0 (intify b)) (∧ₑ₂ (zle_intify1 b Int0) h2)));
  rewrite (zminus_intify a);
  rewrite (zminus_intify b);
  reflexivity
end;

opaque symbol zmod_neg_neg (a b : τ ι) :
  π (zless a Int0) → π (zle b Int0) →
  π (zmod a b = snd (negateSnd (posDivAlg (Pair (zminus a) (zminus b))))) ≔
begin
  assume a b h1 h2;
  rewrite zmod_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  rewrite (If_not_P (zle Int0 (intify a)) _ _
    (∧ₑ₂ (not_zle_iff_zless Int0 (intify a)) (∧ₑ₂ (zless_intify1 a Int0) h1)));
  rewrite (If_not_P (zless Int0 (intify b)) _ _
    (∧ₑ₂ (not_zless_iff_zle Int0 (intify b)) (∧ₑ₂ (zle_intify1 b Int0) h2)));
  rewrite (zminus_intify a);
  rewrite (zminus_intify b);
  reflexivity
end;

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
begin
  assume a;
  rewrite left (zdiv_intify1 a NegInt1);
  rewrite left (zminus_intify a);
  refine zdiv_minus1_right_raw (intify a) (intify_in_int a)
end;

// ===========================================================================
// Monotonicity in the first argument (divisor)
// ===========================================================================

opaque symbol zdiv_mono1 (a a' b : τ ι) :
  π (zle a a') → π (zless Int0 b) → π (zle (zdiv a b) (zdiv a' b)) ≔
begin
  assume a a' b hle hb;
  have h1 : π (intify a = zadd (zmult b (zdiv a b)) (zmod a b))
    { refine zmod_zdiv_equality a b };
  have h2 : π (intify a' = zadd (zmult b (zdiv a' b)) (zmod a' b))
    { refine zmod_zdiv_equality a' b };
  have harg : π (zle (zadd (zmult b (zdiv a b)) (zmod a b))
                     (zadd (zmult b (zdiv a' b)) (zmod a' b)))
    { refine ind_eq (eq_sym h2) (λ v, zle (zadd (zmult b (zdiv a b)) (zmod a b)) v)
        (ind_eq (eq_sym h1) (λ w, zle w (intify a')) (zle_in a a' hle)) };
  refine unique_quotient_lemma b (zdiv a b) (zmod a b) (zdiv a' b) (zmod a' b)
    harg (pos_mod_sign a b hb) hb (pos_mod_bound a' b hb)
end;

opaque symbol zdiv_mono1_neg (a a' b : τ ι) :
  π (zle a a') → π (zless b Int0) → π (zle (zdiv a' b) (zdiv a b)) ≔
begin
  assume a a' b hle hb;
  have h1 : π (intify a = zadd (zmult b (zdiv a b)) (zmod a b))
    { refine zmod_zdiv_equality a b };
  have h2 : π (intify a' = zadd (zmult b (zdiv a' b)) (zmod a' b))
    { refine zmod_zdiv_equality a' b };
  have harg : π (zle (zadd (zmult b (zdiv a b)) (zmod a b))
                     (zadd (zmult b (zdiv a' b)) (zmod a' b)))
    { refine ind_eq (eq_sym h2) (λ v, zle (zadd (zmult b (zdiv a b)) (zmod a b)) v)
        (ind_eq (eq_sym h1) (λ w, zle w (intify a')) (zle_in a a' hle)) };
  refine unique_quotient_lemma_neg b (zdiv a b) (zmod a b) (zdiv a' b) (zmod a' b)
    harg (neg_mod_sign a' b hb) hb (neg_mod_bound a b hb)
end;

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
begin
  assume a b b' h1 h2 h3;
  rewrite left (zdiv_intify1 a b);
  rewrite left (zdiv_intify1 a b');
  refine zdiv_mono2_raw (intify a) b b'
    (∧ₑ₂ (zle_intify2 Int0 a) h1) h2 h3 (intify_in_int a)
end;

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
begin
  assume a b b' h1 h2 h3;
  rewrite left (zdiv_intify1 a b');
  rewrite left (zdiv_intify1 a b);
  refine zdiv_mono2_neg_raw (intify a) b b'
    (∧ₑ₂ (zless_intify1 a Int0) h1) h2 h3 (intify_in_int a)
end;

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
begin
  assume a b c hb hc;
  refine ∨ₑ (em (c = Int0)) _ _
  { assume hc0;
    rewrite hc0;
    rewrite (DIVISION_BY_ZERO_ZDIV (zmult a b));
    rewrite (DIVISION_BY_ZERO_ZDIV b);
    rewrite (DIVISION_BY_ZERO_ZMOD b);
    rewrite (DIVISION_BY_ZERO_ZDIV (zmult a (intify b)));
    rewrite (zmult_0_right a);
    rewrite (zadd_0_right_intify Int0);
    refine eq_sym (intify_ident Int0 Int0_in_int) }
  { assume hc0;
    refine quorem_div (zmult a b) c
      (zadd (zmult a (zdiv b c)) (zdiv (zmult a (zmod b c)) c))
      (zmod (zmult a (zmod b c)) c)
      (zmult1_lemma b c (zdiv b c) (zmod b c) a (quorem_div_mod b c hc0 hb hc) hc hc0)
      hc0
      (zmult_type a b)
      hc
      (zadd_type (zmult a (zdiv b c)) (zdiv (zmult a (zmod b c)) c)) }
end;

opaque symbol zdiv_zmult1_eq (a b c : τ ι) :
  π (zdiv (zmult a b) c = zadd (zmult a (zdiv b c)) (zdiv (zmult a (zmod b c)) c)) ≔
begin
  assume a b c;
  rewrite left (zmod_deintify b c);
  rewrite left (zdiv_deintify b c);
  rewrite left (zmult_intify2 a b);
  rewrite left (zdiv_intify2 (zmult a (intify b)) c);
  rewrite left (zdiv_intify2 (zmult a (zmod (intify b) (intify c))) c);
  refine zdiv_zmult1_eq_raw a (intify b) (intify c) (intify_in_int b) (intify_in_int c)
end;

opaque symbol zmod_zmult1_eq_raw (a b c : τ ι) :
  π (b ∈ int) → π (c ∈ int) →
  π (zmod (zmult a b) c = zmod (zmult a (zmod b c)) c) ≔
begin
  assume a b c hb hc;
  refine ∨ₑ (em (c = Int0)) _ _
  { assume hc0;
    rewrite hc0;
    rewrite (DIVISION_BY_ZERO_ZMOD (zmult a b));
    rewrite (DIVISION_BY_ZERO_ZMOD b);
    rewrite (DIVISION_BY_ZERO_ZMOD (zmult a (intify b)));
    rewrite (zmult_intify2 a b);
    reflexivity }
  { assume hc0;
    refine quorem_mod (zmult a b) c
      (zadd (zmult a (zdiv b c)) (zdiv (zmult a (zmod b c)) c))
      (zmod (zmult a (zmod b c)) c)
      (zmult1_lemma b c (zdiv b c) (zmod b c) a (quorem_div_mod b c hc0 hb hc) hc hc0)
      hc0
      (zmult_type a b)
      hc
      (zadd_type (zmult a (zdiv b c)) (zdiv (zmult a (zmod b c)) c))
      (zmod_type (zmult a (zmod b c)) c) }
end;

opaque symbol zmod_zmult1_eq (a b c : τ ι) :
  π (zmod (zmult a b) c = zmod (zmult a (zmod b c)) c) ≔
begin
  assume a b c;
  rewrite left (zmod_deintify b c);
  rewrite left (zmult_intify2 a b);
  rewrite left (zmod_intify2 (zmult a (intify b)) c);
  rewrite left (zmod_intify2 (zmult a (zmod (intify b) (intify c))) c);
  refine zmod_zmult1_eq_raw a (intify b) (intify c) (intify_in_int b) (intify_in_int c)
end;

opaque symbol zmod_zmult1_eq' (a b c : τ ι) :
  π (zmod (zmult a b) c = zmod (zmult (zmod a c) b) c) ≔
begin
  assume a b c;
  rewrite (zmult_commute a b);
  rewrite (zmod_zmult1_eq b a c);
  rewrite (zmult_commute b (zmod a c));
  reflexivity
end;

opaque symbol zmod_zmult_distrib (a b c : τ ι) :
  π (zmod (zmult a b) c = zmod (zmult (zmod a c) (zmod b c)) c) ≔
begin
  assume a b c;
  rewrite (zmod_zmult1_eq' a b c);
  rewrite (zmod_zmult1_eq (zmod a c) b c);
  reflexivity
end;

opaque symbol zdiv_zmult_self1 (a b : τ ι) :
  π (intify b ≠ Int0) → π (zdiv (zmult a b) b = intify a) ≔
begin
  assume a b h;
  rewrite (zdiv_zmult1_eq a b b);
  rewrite (zdiv_self b h);
  rewrite (zmod_self b);
  rewrite (zmult_0_right a);
  rewrite (zdiv_zero b);
  rewrite (zmult_1_right_intify a);
  rewrite (zadd_0_right_intify (intify a));
  rewrite intify_idem;
  reflexivity
end;

opaque symbol zdiv_zmult_self2 (a b : τ ι) :
  π (intify b ≠ Int0) → π (zdiv (zmult b a) b = intify a) ≔
begin
  assume a b h;
  rewrite (zmult_commute b a);
  refine zdiv_zmult_self1 a b h
end;

opaque symbol zmod_zmult_self1 (a b : τ ι) : π (zmod (zmult a b) b = Int0) ≔
begin
  assume a b;
  rewrite (zmod_zmult1_eq a b b);
  rewrite (zmod_self b);
  rewrite (zmult_0_right a);
  rewrite (zmod_zero b);
  reflexivity
end;

opaque symbol zmod_zmult_self2 (a b : τ ι) : π (zmod (zmult b a) b = Int0) ≔
begin
  assume a b;
  rewrite (zmult_commute b a);
  refine zmod_zmult_self1 a b
end;

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
begin
  assume a b c ha hb hc;
  refine ∨ₑ (em (c = Int0)) _ _
  { assume hc0;
    rewrite hc0;
    rewrite (DIVISION_BY_ZERO_ZDIV (zadd a b));
    rewrite (DIVISION_BY_ZERO_ZDIV a);
    rewrite (DIVISION_BY_ZERO_ZDIV b);
    rewrite (DIVISION_BY_ZERO_ZMOD a);
    rewrite (DIVISION_BY_ZERO_ZMOD b);
    rewrite (DIVISION_BY_ZERO_ZDIV (zadd (intify a) (intify b)));
    rewrite (zadd_0_right_intify Int0);
    rewrite (intify_ident Int0 Int0_in_int);
    rewrite (zadd_0_right_intify Int0);
    refine eq_sym (intify_ident Int0 Int0_in_int) }
  { assume hc0;
    refine quorem_div (zadd a b) c
      (zadd (zadd (zdiv a c) (zdiv b c)) (zdiv (zadd (zmod a c) (zmod b c)) c))
      (zmod (zadd (zmod a c) (zmod b c)) c)
      (zadd1_lemma a c (zdiv a c) (zmod a c) b (zdiv b c) (zmod b c)
         (quorem_div_mod a c hc0 ha hc) (quorem_div_mod b c hc0 hb hc) hc hc0)
      hc0
      (zadd_type a b)
      hc
      (zadd_type (zadd (zdiv a c) (zdiv b c)) (zdiv (zadd (zmod a c) (zmod b c)) c)) }
end;

opaque symbol zdiv_zadd1_eq (a b c : τ ι) :
  π (zdiv (zadd a b) c =
     zadd (zadd (zdiv a c) (zdiv b c)) (zdiv (zadd (zmod a c) (zmod b c)) c)) ≔
begin
  assume a b c;
  rewrite left (zdiv_deintify a c);
  rewrite left (zdiv_deintify b c);
  rewrite left (zmod_deintify a c);
  rewrite left (zmod_deintify b c);
  rewrite left (zadd_deintify a b);
  rewrite left (zdiv_intify2 (zadd (intify a) (intify b)) c);
  rewrite left (zdiv_intify2 (zadd (zmod (intify a) (intify c)) (zmod (intify b) (intify c))) c);
  refine zdiv_zadd1_eq_raw (intify a) (intify b) (intify c)
    (intify_in_int a) (intify_in_int b) (intify_in_int c)
end;

opaque symbol zmod_zadd1_eq_raw (a b c : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (c ∈ int) →
  π (zmod (zadd a b) c = zmod (zadd (zmod a c) (zmod b c)) c) ≔
begin
  assume a b c ha hb hc;
  refine ∨ₑ (em (c = Int0)) _ _
  { assume hc0;
    rewrite hc0;
    rewrite (DIVISION_BY_ZERO_ZMOD (zadd a b));
    rewrite (DIVISION_BY_ZERO_ZMOD a);
    rewrite (DIVISION_BY_ZERO_ZMOD b);
    rewrite (DIVISION_BY_ZERO_ZMOD (zadd (intify a) (intify b)));
    rewrite (zadd_deintify a b);
    reflexivity }
  { assume hc0;
    refine quorem_mod (zadd a b) c
      (zadd (zadd (zdiv a c) (zdiv b c)) (zdiv (zadd (zmod a c) (zmod b c)) c))
      (zmod (zadd (zmod a c) (zmod b c)) c)
      (zadd1_lemma a c (zdiv a c) (zmod a c) b (zdiv b c) (zmod b c)
         (quorem_div_mod a c hc0 ha hc) (quorem_div_mod b c hc0 hb hc) hc hc0)
      hc0
      (zadd_type a b)
      hc
      (zadd_type (zadd (zdiv a c) (zdiv b c)) (zdiv (zadd (zmod a c) (zmod b c)) c))
      (zmod_type (zadd (zmod a c) (zmod b c)) c) }
end;

opaque symbol zmod_zadd1_eq (a b c : τ ι) :
  π (zmod (zadd a b) c = zmod (zadd (zmod a c) (zmod b c)) c) ≔
begin
  assume a b c;
  rewrite left (zmod_deintify a c);
  rewrite left (zmod_deintify b c);
  rewrite left (zadd_deintify a b);
  rewrite left (zmod_intify2 (zadd (intify a) (intify b)) c);
  rewrite left (zmod_intify2 (zadd (zmod (intify a) (intify c)) (zmod (intify b) (intify c))) c);
  refine zmod_zadd1_eq_raw (intify a) (intify b) (intify c)
    (intify_in_int a) (intify_in_int b) (intify_in_int c)
end;

opaque symbol zmod_div_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zdiv (zmod a b) b = Int0) ≔
begin admit end;

opaque symbol zmod_div_trivial (a b : τ ι) : π (zdiv (zmod a b) b = Int0) ≔
begin
  assume a b;
  rewrite left (zmod_deintify a b);
  rewrite left (zdiv_intify2 (zmod (intify a) (intify b)) b);
  refine zmod_div_trivial_raw (intify a) (intify b) (intify_in_int a) (intify_in_int b)
end;

opaque symbol zmod_mod_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zmod (zmod a b) b = zmod a b) ≔
begin admit end;

opaque symbol zmod_mod_trivial (a b : τ ι) : π (zmod (zmod a b) b = zmod a b) ≔
begin
  assume a b;
  rewrite left (zmod_deintify a b);
  rewrite left (zmod_intify2 (zmod (intify a) (intify b)) b);
  refine zmod_mod_trivial_raw (intify a) (intify b) (intify_in_int a) (intify_in_int b)
end;

opaque symbol zmod_zadd_left_eq (a b c : τ ι) :
  π (zmod (zadd a b) c = zmod (zadd (zmod a c) b) c) ≔
begin
  assume a b c;
  rewrite (zmod_zadd1_eq a b c);
  rewrite (zmod_zadd1_eq (zmod a c) b c);
  rewrite (zmod_mod_trivial a c);
  reflexivity
end;

opaque symbol zmod_zadd_right_eq (a b c : τ ι) :
  π (zmod (zadd a b) c = zmod (zadd a (zmod b c)) c) ≔
begin
  assume a b c;
  rewrite (zmod_zadd1_eq a b c);
  rewrite (zmod_zadd1_eq a (zmod b c) c);
  rewrite (zmod_mod_trivial b c);
  reflexivity
end;

opaque symbol zdiv_zadd_self1 (a b : τ ι) :
  π (intify a ≠ Int0) → π (zdiv (zadd a b) a = zadd (zdiv b a) Int1) ≔
begin
  assume a b h;
  rewrite (zdiv_zadd1_eq a b a);
  rewrite (zdiv_self a h);
  rewrite (zmod_self a);
  rewrite (zadd_0_intify (zmod b a));
  rewrite (zdiv_intify1 (zmod b a) a);
  rewrite (zmod_div_trivial b a);
  rewrite (zadd_commute Int1 (zdiv b a));
  rewrite (zadd_0_right_intify (zadd (zdiv b a) Int1));
  refine intify_ident (zadd (zdiv b a) Int1) (zadd_type (zdiv b a) Int1)
end;

opaque symbol zdiv_zadd_self2 (a b : τ ι) :
  π (intify a ≠ Int0) → π (zdiv (zadd b a) a = zadd (zdiv b a) Int1) ≔
begin
  assume a b h;
  rewrite (zadd_commute b a);
  refine zdiv_zadd_self1 a b h
end;

opaque symbol zmod_zadd_self1 (a b : τ ι) : π (zmod (zadd a b) a = zmod b a) ≔
begin
  assume a b;
  rewrite (zmod_zadd1_eq a b a);
  rewrite (zmod_self a);
  rewrite (zadd_0_intify (zmod b a));
  rewrite (zmod_intify1 (zmod b a) a);
  rewrite (zmod_mod_trivial b a);
  reflexivity
end;

opaque symbol zmod_zadd_self2 (a b : τ ι) : π (zmod (zadd b a) a = zmod b a) ≔
begin
  assume a b;
  rewrite (zadd_commute b a);
  refine zmod_zadd_self1 a b
end;

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
begin
  assume a b c hc ha hb;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0;
    rewrite hb0;
    rewrite (zmult_0 c);
    rewrite (DIVISION_BY_ZERO_ZDIV a);
    rewrite (zdiv_zero c);
    reflexivity }
  { assume hb0;
    have hbc0 : π (zmult b c ≠ Int0)
      { assume heq;
        refine ∨ₑ (∧ₑ₁ (zmult_eq_0_iff b c) heq) _ _
        { assume hbz; refine hb0 (eq_trans (eq_sym (intify_ident b hb)) hbz) }
        { assume hcz;
          have hlt : π (zless Int0 (intify c)) { refine ∧ₑ₂ (zless_intify2 Int0 c) hc };
          have hlt0 : π (zless Int0 Int0)
            { refine ind_eq (eq_sym hcz) (λ v, zless Int0 v) hlt };
          refine zless_not_sym Int0 Int0 hlt0 hlt0 } };
    refine quorem_div a (zmult b c)
      (zdiv (zdiv a b) c)
      (zadd (zmult b (zmod (zdiv a b) c)) (zmod a b))
      (zdiv_zmult2_lemma a b (zdiv a b) (zmod a b) c
         (quorem_div_mod a b hb0 ha hb) ha hb hb0 hc)
      hbc0 ha (zmult_type b c) (zdiv_type (zdiv a b) c) }
end;

opaque symbol zdiv_zmult2_eq (a b c : τ ι) :
  π (zless Int0 c) → π (zdiv a (zmult b c) = zdiv (zdiv a b) c) ≔
begin
  assume a b c hc;
  rewrite left (zdiv_deintify a b);
  rewrite left (zmult_intify1 b c);
  rewrite left (zdiv_intify1 a (zmult (intify b) c));
  refine zdiv_zmult2_eq_raw (intify a) (intify b) c hc (intify_in_int a) (intify_in_int b)
end;

opaque symbol zmod_zmult2_eq_raw (a b c : τ ι) :
  π (zless Int0 c) → π (a ∈ int) → π (b ∈ int) →
  π (zmod a (zmult b c) = zadd (zmult b (zmod (zdiv a b) c)) (zmod a b)) ≔
begin
  assume a b c hc ha hb;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0;
    rewrite hb0;
    rewrite (zmult_0 c);
    rewrite (zmult_0 (zmod (zdiv a Int0) c));
    rewrite (DIVISION_BY_ZERO_ZMOD a);
    rewrite (zadd_0_intify (intify a));
    rewrite intify_idem;
    reflexivity }
  { assume hb0;
    have hbc0 : π (zmult b c ≠ Int0)
      { assume heq;
        refine ∨ₑ (∧ₑ₁ (zmult_eq_0_iff b c) heq) _ _
        { assume hbz; refine hb0 (eq_trans (eq_sym (intify_ident b hb)) hbz) }
        { assume hcz;
          have hlt : π (zless Int0 (intify c)) { refine ∧ₑ₂ (zless_intify2 Int0 c) hc };
          have hlt0 : π (zless Int0 Int0)
            { refine ind_eq (eq_sym hcz) (λ v, zless Int0 v) hlt };
          refine zless_not_sym Int0 Int0 hlt0 hlt0 } };
    refine quorem_mod a (zmult b c)
      (zdiv (zdiv a b) c)
      (zadd (zmult b (zmod (zdiv a b) c)) (zmod a b))
      (zdiv_zmult2_lemma a b (zdiv a b) (zmod a b) c
         (quorem_div_mod a b hb0 ha hb) ha hb hb0 hc)
      hbc0 ha (zmult_type b c) (zdiv_type (zdiv a b) c)
      (zadd_type (zmult b (zmod (zdiv a b) c)) (zmod a b)) }
end;

opaque symbol zmod_zmult2_eq (a b c : τ ι) :
  π (zless Int0 c) →
  π (zmod a (zmult b c) = zadd (zmult b (zmod (zdiv a b) c)) (zmod a b)) ≔
begin
  assume a b c hc;
  rewrite left (zmod_deintify a b);
  rewrite left (zdiv_deintify a b);
  rewrite left (zmult_intify1 b (zmod (zdiv (intify a) (intify b)) c));
  rewrite left (zmult_intify1 b c);
  rewrite left (zmod_intify1 a (zmult (intify b) c));
  refine zmod_zmult2_eq_raw (intify a) (intify b) c hc (intify_in_int a) (intify_in_int b)
end;

// ===========================================================================
// Cancellation of common factors in "zdiv"
// ===========================================================================

opaque symbol zdiv_zmult_zmult1_aux1 (b c a : τ ι) :
  π (zless Int0 b) → π (intify c ≠ Int0) →
  π (zdiv (zmult c a) (zmult c b) = zdiv a b) ≔
begin
  assume b c a hb hc;
  rewrite (zdiv_zmult2_eq (zmult c a) c b hb);
  rewrite (zdiv_zmult_self2 a c hc);
  rewrite (zdiv_intify1 a b);
  reflexivity
end;

opaque symbol zdiv_zmult_zmult1_aux2 (b c a : τ ι) :
  π (zless b Int0) → π (intify c ≠ Int0) →
  π (zdiv (zmult c a) (zmult c b) = zdiv a b) ≔
begin
  assume b c a hb hc;
  have hmb : π (zless Int0 (zminus b))
    { have h1 : π (zless b (zminus Int0)) { rewrite zminus_0; refine hb };
      refine ∧ₑ₂ (zless_zminus Int0 b) h1 };
  rewrite left (zdiv_zminus_zminus (zmult c a) (zmult c b));
  rewrite left (zdiv_zminus_zminus a b);
  rewrite left (zmult_zminus_right c a);
  rewrite left (zmult_zminus_right c b);
  refine zdiv_zmult_zmult1_aux1 (zminus b) c (zminus a) hmb hc
end;

opaque symbol zdiv_zmult_zmult1_raw (c a b : τ ι) :
  π (intify c ≠ Int0) → π (b ∈ int) →
  π (zdiv (zmult c a) (zmult c b) = zdiv a b) ≔
begin
  assume c a b hc hb;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0;
    rewrite hb0;
    rewrite (zmult_0_right c);
    rewrite (DIVISION_BY_ZERO_ZDIV (zmult c a));
    rewrite (DIVISION_BY_ZERO_ZDIV a);
    reflexivity }
  { assume hb0;
    refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) _ _
    { assume hlt; refine zdiv_zmult_zmult1_aux2 b c a hlt hc }
    { assume hgt; refine zdiv_zmult_zmult1_aux1 b c a hgt hc } }
end;

opaque symbol zdiv_zmult_zmult1 (c a b : τ ι) :
  π (intify c ≠ Int0) → π (zdiv (zmult c a) (zmult c b) = zdiv a b) ≔
begin
  assume c a b h;
  rewrite left (zmult_intify2 c b);
  rewrite left (zdiv_intify2 a b);
  refine zdiv_zmult_zmult1_raw c a (intify b) h (intify_in_int b)
end;

opaque symbol zdiv_zmult_zmult2 (c a b : τ ι) :
  π (intify c ≠ Int0) → π (zdiv (zmult a c) (zmult b c) = zdiv a b) ≔
begin
  assume c a b h;
  rewrite (zmult_commute a c);
  rewrite (zmult_commute b c);
  refine zdiv_zmult_zmult1 c a b h
end;

// ===========================================================================
// Distribution of factors over "zmod"
// ===========================================================================

opaque symbol zmod_zmult_zmult1_aux1 (b c a : τ ι) :
  π (zless Int0 b) → π (intify c ≠ Int0) →
  π (zmod (zmult c a) (zmult c b) = zmult c (zmod a b)) ≔
begin
  assume b c a hb hc;
  rewrite (zmod_zmult2_eq (zmult c a) c b hb);
  rewrite (zdiv_zmult_self2 a c hc);
  rewrite (zmod_zmult_self2 a c);
  rewrite (zmod_intify1 a b);
  rewrite (zadd_0_right_intify (zmult c (zmod a b)));
  refine intify_ident (zmult c (zmod a b)) (zmult_type c (zmod a b))
end;

opaque symbol zmod_zmult_zmult1_aux2 (b c a : τ ι) :
  π (zless b Int0) → π (intify c ≠ Int0) →
  π (zmod (zmult c a) (zmult c b) = zmult c (zmod a b)) ≔
begin
  assume b c a hb hc;
  have hmb : π (zless Int0 (zminus b))
    { have h1 : π (zless b (zminus Int0)) { rewrite zminus_0; refine hb };
      refine ∧ₑ₂ (zless_zminus Int0 b) h1 };
  have hS : π (zmod (zmult c (zminus a)) (zmult c (zminus b)) =
               zmult c (zmod (zminus a) (zminus b)))
    { refine zmod_zmult_zmult1_aux1 (zminus b) c (zminus a) hmb hc };
  have hminus : π (zminus (zmod (zmult c a) (zmult c b)) =
                   zminus (zmult c (zmod a b)))
    { rewrite left (zmod_zminus_zminus (zmult c a) (zmult c b));
      rewrite left (zmult_zminus_right c a);
      rewrite left (zmult_zminus_right c b);
      rewrite left (zmult_zminus_right c (zmod a b));
      rewrite left (zmod_zminus_zminus a b);
      refine hS };
  refine zminus_inject (zmod (zmult c a) (zmult c b)) (zmult c (zmod a b))
    hminus (zmod_type (zmult c a) (zmult c b)) (zmult_type c (zmod a b))
end;

opaque symbol zmod_zmult_zmult1_raw (b c a : τ ι) :
  π (b ∈ int) → π (c ∈ int) →
  π (zmod (zmult c a) (zmult c b) = zmult c (zmod a b)) ≔
begin
  assume b c a hb hc;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0;
    rewrite hb0;
    rewrite (zmult_0_right c);
    rewrite (DIVISION_BY_ZERO_ZMOD (zmult c a));
    rewrite (DIVISION_BY_ZERO_ZMOD a);
    rewrite (zmult_intify2 c a);
    rewrite (intify_ident (zmult c a) (zmult_type c a));
    reflexivity }
  { assume hb0;
    refine ∨ₑ (em (c = Int0)) _ _
    { assume hc0;
      rewrite hc0;
      rewrite (zmult_0 a);
      rewrite (zmult_0 b);
      rewrite (zmult_0 (zmod a b));
      rewrite (DIVISION_BY_ZERO_ZMOD Int0);
      rewrite (intify_ident Int0 Int0_in_int);
      reflexivity }
    { assume hc0;
      have hic : π (intify c ≠ Int0)
        { assume heq; refine hc0 (eq_trans (eq_sym (intify_ident c hc)) heq) };
      refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) _ _
      { assume hlt; refine zmod_zmult_zmult1_aux2 b c a hlt hic }
      { assume hgt; refine zmod_zmult_zmult1_aux1 b c a hgt hic } } }
end;

opaque symbol zmod_zmult_zmult1 (c a b : τ ι) :
  π (zmod (zmult c a) (zmult c b) = zmult c (zmod a b)) ≔
begin
  assume c a b;
  rewrite left (zmult_intify1 c a);
  rewrite left (zmult_deintify c b);
  rewrite left (zmod_intify2 a b);
  rewrite left (zmult_intify1 c (zmod a (intify b)));
  refine zmod_zmult_zmult1_raw (intify b) (intify c) a (intify_in_int b) (intify_in_int c)
end;

opaque symbol zmod_zmult_zmult2 (a c b : τ ι) :
  π (zmod (zmult a c) (zmult b c) = zmult (zmod a b) c) ≔
begin
  assume a c b;
  rewrite (zmult_commute a c);
  rewrite (zmult_commute b c);
  rewrite (zmult_commute (zmod a b) c);
  refine zmod_zmult_zmult1 c a b
end;

// Quotients of signs

opaque symbol zdiv_neg_pos_less0 (a b : τ ι) :
  π (zless a Int0) → π (zless Int0 b) → π (zless (zdiv a b) Int0) ≔
begin admit end;

opaque symbol zdiv_nonneg_neg_le0 (a b : τ ι) :
  π (zle Int0 a) → π (zless b Int0) → π (zle (zdiv a b) Int0) ≔
begin
  assume a b h1 h2;
  have hm : π (zle (zdiv a b) (zdiv Int0 b)) { refine zdiv_mono1_neg Int0 a b h1 h2 };
  refine ind_eq (eq_sym (zdiv_zero b)) (λ v, zle (zdiv a b) v) hm
end;

opaque symbol pos_imp_zdiv_nonneg_iff (a b : τ ι) :
  π (zless Int0 b) → π (zle Int0 (zdiv a b) ⇔ zle Int0 a) ≔
begin
  assume a b hb;
  apply ∧ᵢ
  { assume h;
    refine ∧ₑ₁ (not_zless_iff_zle a Int0) _;
    assume hlt;
    have hq : π (zless (zdiv a b) Int0) { refine zdiv_neg_pos_less0 a b hlt hb };
    have hxx : π (zless (zdiv a b) (zdiv a b))
      { refine zless_zle_trans (zdiv a b) Int0 (zdiv a b) hq h };
    refine zless_not_sym (zdiv a b) (zdiv a b) hxx hxx }
  { assume h;
    have hm : π (zle (zdiv Int0 b) (zdiv a b)) { refine zdiv_mono1 Int0 a b h hb };
    refine ind_eq (eq_sym (zdiv_zero b)) (λ v, zle v (zdiv a b)) hm }
end;

opaque symbol neg_imp_zdiv_nonneg_iff (a b : τ ι) :
  π (zless b Int0) → π (zle Int0 (zdiv a b) ⇔ zle a Int0) ≔
begin admit end;

// But not (a zdiv b ≤ 0 iff a≤0); consider a=1, b=2 when a zdiv b = 0.
opaque symbol pos_imp_zdiv_neg_iff (a b : τ ι) :
  π (zless Int0 b) → π (zless (zdiv a b) Int0 ⇔ zless a Int0) ≔
begin
  assume a b hb;
  have hiff : π (zle Int0 (zdiv a b) ⇔ zle Int0 a) { refine pos_imp_zdiv_nonneg_iff a b hb };
  apply ∧ᵢ
  { assume h;
    have hn : π (¬ zle Int0 a)
      { assume ha; refine ∧ₑ₂ (not_zle_iff_zless Int0 (zdiv a b)) h (∧ₑ₂ hiff ha) };
    refine ∧ₑ₁ (not_zle_iff_zless Int0 a) hn }
  { assume h;
    have hn : π (¬ zle Int0 (zdiv a b))
      { assume hq; refine ∧ₑ₂ (not_zle_iff_zless Int0 a) h (∧ₑ₁ hiff hq) };
    refine ∧ₑ₁ (not_zle_iff_zless Int0 (zdiv a b)) hn }
end;

// Again the law fails for ≤: consider a = -1, b = -2 when a zdiv b = 0
opaque symbol neg_imp_zdiv_neg_iff (a b : τ ι) :
  π (zless b Int0) → π (zless (zdiv a b) Int0 ⇔ zless Int0 a) ≔
begin
  assume a b hb;
  have hiff : π (zle Int0 (zdiv a b) ⇔ zle a Int0) { refine neg_imp_zdiv_nonneg_iff a b hb };
  apply ∧ᵢ
  { assume h;
    have hn : π (¬ zle a Int0)
      { assume ha; refine ∧ₑ₂ (not_zle_iff_zless Int0 (zdiv a b)) h (∧ₑ₂ hiff ha) };
    refine ∧ₑ₁ (not_zle_iff_zless a Int0) hn }
  { assume h;
    have hn : π (¬ zle Int0 (zdiv a b))
      { assume hq; refine ∧ₑ₂ (not_zle_iff_zless a Int0) h (∧ₑ₁ hiff hq) };
    refine ∧ₑ₁ (not_zle_iff_zless Int0 (zdiv a b)) hn }
end;

// The remainder of IntDiv.thy (shifting-based speedups for zdiv/zmod, from
// "Speeding up the division algorithm with shifting" onward) is wrapped in
// the .thy's own literal comment "THESE REMAIN TO BE CONVERTED -- but aren't
// that useful!" — i.e. the ORIGINAL Isabelle author marked it dead/unconverted
// and Isabelle itself never parsed it. Zero provable content; skipped entirely
// per task instructions.
