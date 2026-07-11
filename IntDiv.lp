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
begin
  assume k hpos hk;
  have hnneg : π (¬ znegative k)
    { assume hneg;
      have hlt : π (zless k Int0) { refine ∧ₑ₁ (znegative_iff_zless_0 k hk) hneg };
      refine zless_not_sym Int0 k hpos hlt };
  refine ∃ₑ (not_zneg_int_of k hk hnneg) _;
  assume n hn_and;
  have hnω : π (n ∈ omega) { refine ∧ₑ₁ hn_and };
  have hkeq : π (k = int_of n) { refine ∧ₑ₂ hn_and };
  have hmag : π (zmagnitude k = natify n)
    { rewrite hkeq; refine zmagnitude_int_of n };
  rewrite hmag;
  rewrite (natify_ident n hnω);
  refine ∧ₑ₁ (zless_int_of empty n zero_in_omega hnω)
    (ind_eq int_of_0 (λ w, zless w (int_of n))
      (ind_eq (eq_sym hkeq) (λ w, zless Int0 w) hpos))
end;

// ===========================================================================
// Inequality lemmas involving $#succ(m)
// ===========================================================================

// port-internal helper: w $+ $#(succ k) = (w $+ $#k) $+ #1
private opaque symbol zadd_int_of_succ (w k : τ ι) :
  π (zadd w (int_of (succ k)) = zadd (zadd w (int_of k)) Int1) ≔
begin
  assume w k;
  rewrite (int_of_succ k);
  rewrite (zadd_commute Int1 (int_of k));
  rewrite left (zadd_assoc w (int_of k) Int1);
  reflexivity
end;

opaque symbol zless_add_succ_iff (w z m : τ ι) :
  π (zless w (zadd z (int_of (succ m))) ⇔
     (zless w (zadd z (int_of m)) ∨ intify w = zadd z (int_of m))) ≔
begin
  assume w z m;
  have hZ : π (zadd z (int_of m) ∈ int) { refine zadd_type z (int_of m) };
  have hZSshift : π (zadd z (int_of (succ m)) = zadd (zadd z (int_of m)) Int1)
    { refine zadd_int_of_succ z m };
  have hZSint : π (intify (zadd z (int_of (succ m))) = zadd z (int_of (succ m)))
    { refine intify_ident (zadd z (int_of (succ m))) (zadd_type z (int_of (succ m))) };
  apply ∧ᵢ
  { assume hlt;
    have hex : π (Bex omega (λ n, zadd w (int_of (succ n)) = intify (zadd z (int_of (succ m)))))
      { refine zless_imp_succ_zadd w (zadd z (int_of (succ m))) hlt };
    refine ∃ₑ hex _;
    assume n hn_and;
    have hnω : π (n ∈ omega) { refine ∧ₑ₁ hn_and };
    have heq2 : π (zadd w (int_of (succ n)) = zadd z (int_of (succ m)))
      { refine ind_eq (eq_sym hZSint) (λ v, zadd w (int_of (succ n)) = v) (∧ₑ₂ hn_and) };
    refine natE n (zless w (zadd z (int_of m)) ∨ intify w = zadd z (int_of m)) hnω _ _
    { assume hn0;
      // n = empty: zadd w (int_of (succ empty)) = ZS
      have he : π (zadd w (int_of (succ empty)) = zadd z (int_of (succ m)))
        { refine ind_eq (eq_sym hn0) (λ v, zadd w (int_of (succ v)) = zadd z (int_of (succ m))) heq2 };
      have he2 : π (zadd (zadd w (int_of empty)) Int1 = zadd (zadd z (int_of m)) Int1)
        { rewrite left (zadd_int_of_succ w empty);
          rewrite left hZSshift;
          refine he };
      have he3 : π (zadd (intify w) Int1 = zadd (zadd z (int_of m)) Int1)
        { refine ind_eq (eq_sym (zadd_int0_right_intify w))
            (λ v, zadd v Int1 = zadd (zadd z (int_of m)) Int1) he2 };
      refine ∨ᵢ₂ (∧ₑ₁ (zadd_right_cancel (zadd z (int_of m)) (intify w) Int1
        hZ (intify_in_int w)) he3) }
    { assume k hk hnsk;
      // n = succ k: zadd w (int_of (succ (succ k))) = ZS
      have he : π (zadd w (int_of (succ (succ k))) = zadd z (int_of (succ m)))
        { refine ind_eq (eq_sym hnsk) (λ v, zadd w (int_of (succ v)) = zadd z (int_of (succ m))) heq2 };
      have he2 : π (zadd (zadd w (int_of (succ k))) Int1 = zadd (zadd z (int_of m)) Int1)
        { rewrite left (zadd_int_of_succ w (succ k));
          rewrite left hZSshift;
          refine he };
      have hkeq : π (zadd w (int_of (succ k)) = zadd z (int_of m))
        { refine ∧ₑ₁ (zadd_right_cancel (zadd z (int_of m)) (zadd w (int_of (succ k))) Int1
            hZ (zadd_type w (int_of (succ k)))) he2 };
      refine ∨ᵢ₁ (∧ₑ₂ (zless_iff_succ_zadd w (zadd z (int_of m)))
        (∃ᵢ k (∧ᵢ hk
          (ind_eq (intify_ident (zadd z (int_of m)) hZ)
            (λ v, zadd w (int_of (succ k)) = v) hkeq)))) } }
  { assume hor;
    refine ∨ₑ hor _ _
    { assume hr1;
      have hex : π (Bex omega (λ n, zadd w (int_of (succ n)) = intify (zadd z (int_of m))))
        { refine zless_imp_succ_zadd w (zadd z (int_of m)) hr1 };
      refine ∃ₑ hex _;
      assume k hk_and;
      have hk : π (k ∈ omega) { refine ∧ₑ₁ hk_and };
      have hkeq : π (zadd w (int_of (succ k)) = zadd z (int_of m))
        { refine ind_eq (eq_sym (intify_ident (zadd z (int_of m)) hZ))
            (λ v, zadd w (int_of (succ k)) = v) (∧ₑ₂ hk_and) };
      refine ∧ₑ₂ (zless_iff_succ_zadd w (zadd z (int_of (succ m))))
        (∃ᵢ (succ k) (∧ᵢ (succ_in_omega k hk) _));
      // zadd w (int_of (succ (succ k))) = intify ZS
      rewrite hZSint;
      rewrite hZSshift;
      rewrite (zadd_int_of_succ w (succ k));
      rewrite hkeq;
      reflexivity }
    { assume hr2;
      refine ∧ₑ₂ (zless_iff_succ_zadd w (zadd z (int_of (succ m))))
        (∃ᵢ empty (∧ᵢ zero_in_omega _));
      // zadd w (int_of (succ empty)) = intify ZS
      rewrite hZSint;
      rewrite hZSshift;
      rewrite (zadd_int_of_succ w empty);
      rewrite (zadd_int0_right_intify w);
      rewrite hr2;
      reflexivity } }
end;

opaque symbol zadd_succ_lemma (z w m : τ ι) :
  π (z ∈ int) → π (zle (zadd w (int_of (succ m))) z ⇔ zless (zadd w (int_of m)) z) ≔
begin
  assume z w m hz;
  have hB : π (zadd w (int_of m) ∈ int) { refine zadd_type w (int_of m) };
  have hsucc : π (zless z (zadd w (int_of (succ m))) ⇔
                  (zless z (zadd w (int_of m)) ∨ intify z = zadd w (int_of m)))
    { refine zless_add_succ_iff z w m };
  have hzleB : π (zle z (zadd w (int_of m)) ⇔
                  (zless z (zadd w (int_of m)) ∨ intify z = zadd w (int_of m)))
    { rewrite zle_def; rewrite (intify_ident (zadd w (int_of m)) hB); refine ⇔_refl };
  apply ∧ᵢ
  { assume h;
    have hnzA : π (¬ zless z (zadd w (int_of (succ m))))
      { refine ∧ₑ₂ (not_zless_iff_zle z (zadd w (int_of (succ m)))) h };
    have hnleB : π (¬ zle z (zadd w (int_of m)))
      { assume hle; refine hnzA (∧ₑ₂ hsucc (∧ₑ₁ hzleB hle)) };
    refine ∧ₑ₁ (not_zle_iff_zless z (zadd w (int_of m))) hnleB }
  { assume h;
    have hnleB : π (¬ zle z (zadd w (int_of m)))
      { refine ∧ₑ₂ (not_zle_iff_zless z (zadd w (int_of m))) h };
    have hnzA : π (¬ zless z (zadd w (int_of (succ m))))
      { assume hlt; refine hnleB (∧ₑ₂ hzleB (∧ₑ₁ hsucc hlt)) };
    refine ∧ₑ₁ (not_zless_iff_zle z (zadd w (int_of (succ m)))) hnzA }
end;

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

// port-internal helper: Int1 is an integer
private opaque symbol Int1_in_int : π (Int1 ∈ int) ≔
begin
  refine integ_of_type (Bit Pls one) (bin_BitI Pls one bin_PlsI one_in_bool)
end;

// port-internal helper: NegInt1 (= $-#1) is an integer
private opaque symbol NegInt1_in_int : π (NegInt1 ∈ int) ≔
begin
  refine ind_eq NegInt1_eq_zminus_Int1 (λ v, v ∈ int) (zminus_type Int1)
end;

// port-internal helper: $#(succ 0) = #1
private opaque symbol int_of_succ_empty : π (int_of (succ empty) = Int1) ≔
begin
  rewrite (int_of_succ empty);
  rewrite (zadd_int0_right_intify Int1);
  refine intify_ident Int1 Int1_in_int
end;

// port-internal helper: #0 $< #1
private opaque symbol zless_Int0_Int1 : π (zless Int0 Int1) ≔
begin
  rewrite left int_of_0;
  rewrite left int_of_succ_empty;
  refine ∧ₑ₂ (zless_int_of empty (succ empty) zero_in_omega
                (succ_in_omega empty zero_in_omega)) _;
  refine ltI empty (succ empty) (succI1 empty) (Ord_succ empty Ord_0)
end;

// port-internal helper: #-1 $< #0
private opaque symbol zless_NegInt1_Int0 : π (zless NegInt1 Int0) ≔
begin
  rewrite NegInt1_eq_zminus_Int1;
  refine ∧ₑ₂ (zminus_zless Int1 Int0) _;
  rewrite zminus_0;
  refine zless_Int0_Int1
end;

opaque symbol zless_add1_iff_zle (w z : τ ι) :
  π (zless w (zadd z Int1) ⇔ zle w z) ≔
begin
  assume w z;
  have he : π (zadd z (int_of empty) = intify z) { refine zadd_int0_right_intify z };
  have hs : π (zless w (zadd z (int_of (succ empty))) ⇔
               (zless w (zadd z (int_of empty)) ∨ intify w = zadd z (int_of empty)))
    { refine zless_add_succ_iff w z empty };
  rewrite left int_of_succ_empty;
  apply ∧ᵢ
  { assume hl;
    have hd : π (zless w (zadd z (int_of empty)) ∨ intify w = zadd z (int_of empty))
      { refine ∧ₑ₁ hs hl };
    refine ∨ₑ hd _ _
    { assume h1;
      have h1' : π (zless w (intify z)) { refine ind_eq (eq_sym he) (λ v, zless w v) h1 };
      refine zless_imp_zle w z (∧ₑ₁ (zless_intify2 w z) h1') }
    { assume h2;
      have h2' : π (intify w = intify z) { refine ind_eq (eq_sym he) (λ v, intify w = v) h2 };
      refine ind_eq (zle_def w z) (λ p, p) (∨ᵢ₂ h2') } }
  { assume hle;
    have hd : π (zless w z ∨ intify w = intify z)
      { refine ind_eq (eq_sym (zle_def w z)) (λ p, p) hle };
    refine ∧ₑ₂ hs _;
    refine ∨ₑ hd _ _
    { assume h1;
      have h1' : π (zless w (intify z)) { refine ∧ₑ₂ (zless_intify2 w z) h1 };
      refine ∨ᵢ₁ (ind_eq he (λ v, zless w v) h1') }
    { assume h2;
      refine ∨ᵢ₂ (ind_eq he (λ v, intify w = v) h2) } }
end;

opaque symbol add1_zle_iff (w z : τ ι) :
  π (zle (zadd w Int1) z ⇔ zless w z) ≔
begin
  assume w z;
  apply ∧ᵢ
  { assume h;
    have hn : π (¬ zless z (zadd w Int1))
      { refine ∧ₑ₂ (not_zless_iff_zle z (zadd w Int1)) h };
    have hnle : π (¬ zle z w)
      { assume hle; refine hn (∧ₑ₂ (zless_add1_iff_zle z w) hle) };
    refine ∧ₑ₁ (not_zle_iff_zless z w) hnle }
  { assume h;
    have hnle : π (¬ zle z w) { refine ∧ₑ₂ (not_zle_iff_zless z w) h };
    have hn : π (¬ zless z (zadd w Int1))
      { assume hlt; refine hnle (∧ₑ₁ (zless_add1_iff_zle z w) hlt) };
    refine ∧ₑ₁ (not_zless_iff_zle z (zadd w Int1)) hn }
end;

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
begin
  assume k i j hk hij;
  refine nat_induct (λ n, zle (zmult i (int_of n)) (zmult j (int_of n))) _ _ k hk
  { simplify rule off;
    rewrite int_of_0;
    rewrite (zmult_0_right i);
    rewrite (zmult_0_right j);
    refine zle_refl Int0 }
  { assume n hn hIH;
    rewrite (int_succ_int_1 n);
    rewrite (zadd_zmult_distrib2 i (int_of (succ empty)) (int_of n));
    rewrite (zadd_zmult_distrib2 j (int_of (succ empty)) (int_of n));
    have hbase : π (zle (zmult i (int_of (succ empty))) (zmult j (int_of (succ empty))))
      { rewrite int_of_succ_empty;
        rewrite (zmult_1_right_intify i);
        rewrite (zmult_1_right_intify j);
        refine ∧ₑ₂ (zle_intify1 i (intify j)) (∧ₑ₂ (zle_intify2 i j) hij) };
    refine zadd_zle_mono (zmult j (int_of (succ empty))) (zmult i (int_of (succ empty)))
                          (zmult j (int_of n)) (zmult i (int_of n)) hbase hIH }
end;

opaque symbol zmult_zle_mono1 (i j k : τ ι) :
  π (zle i j) → π (zle Int0 k) → π (zle (zmult i k) (zmult j k)) ≔
begin
  assume i j k hij hk;
  have hki : π (zle Int0 (intify k)) { refine ∧ₑ₂ (zle_intify2 Int0 k) hk };
  have hnneg : π (¬ znegative (intify k))
    { assume hneg;
      have hlt : π (zless (intify k) Int0)
        { refine ∧ₑ₁ (znegative_iff_zless_0 (intify k) (intify_in_int k)) hneg };
      have hlt0 : π (zless Int0 Int0)
        { refine zle_zless_trans Int0 (intify k) Int0 hki hlt };
      refine zless_not_sym Int0 Int0 hlt0 hlt0 };
  have hm : π (int_of (nat_of (intify k)) = intify k)
    { refine not_zneg_nat_of (intify k) hnneg (intify_in_int k) };
  rewrite left (zmult_intify2 i k);
  rewrite left (zmult_intify2 j k);
  rewrite left hm;
  refine zmult_mono_lemma (nat_of (intify k)) i j (nat_of_type (intify k)) hij
end;

opaque symbol zmult_zle_mono1_neg (i j k : τ ι) :
  π (zle i j) → π (zle k Int0) → π (zle (zmult j k) (zmult i k)) ≔
begin
  assume i j k hij hk;
  refine ∧ₑ₁ (zminus_zle_zminus (zmult i k) (zmult j k)) _;
  rewrite left (zmult_zminus_right i k);
  rewrite left (zmult_zminus_right j k);
  have hkneg : π (zle Int0 (zminus k))
    { refine ind_eq (eq_sym zminus_0) (λ v, zle v (zminus k))
        (∧ₑ₂ (zminus_zle_zminus Int0 k) hk) };
  refine zmult_zle_mono1 i j (zminus k) hij hkneg
end;

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
begin
  assume i j k hij hk hpos;
  refine natE k (zless (zmult (int_of k) i) (zmult (int_of k) j)) hk _ _
  { assume h0;
    have hbad : π (empty ∈ empty)
      { refine ind_eq (eq_sym h0) (λ v, empty ∈ v) (ltD empty k hpos) };
    refine ⊥ₑ (emptyE empty hbad) }
  { assume x hx hkx;
    rewrite hkx;
    rewrite (int_succ_int_1 x);
    rewrite (zadd_zmult_distrib (int_of (succ empty)) (int_of x) i);
    rewrite (zadd_zmult_distrib (int_of (succ empty)) (int_of x) j);
    rewrite int_of_succ_empty;
    rewrite (zmult_1_intify i);
    rewrite (zmult_1_intify j);
    have hle0 : π (zle Int0 (int_of x))
      { refine ∧ₑ₁ (not_zless_iff_zle (int_of x) Int0) _;
        assume hlt;
        refine not_znegative_int_of x
          (∧ₑ₂ (znegative_iff_zless_0 (int_of x) (int_of_type x)) hlt) };
    refine zadd_zless_mono (intify j) (intify i)
      (zmult (int_of x) j) (zmult (int_of x) i) _ _
    { refine ∧ₑ₂ (zless_intify1 i (intify j)) (∧ₑ₂ (zless_intify2 i j) hij) }
    { refine zmult_zle_mono2 i j (int_of x) (zless_imp_zle i j hij) hle0 } }
end;

opaque symbol zmult_zless_mono2 (i j k : τ ι) :
  π (zless i j) → π (zless Int0 k) → π (zless (zmult k i) (zmult k j)) ≔
begin
  assume i j k hij hk;
  have hki : π (zless Int0 (intify k)) { refine ∧ₑ₂ (zless_intify2 Int0 k) hk };
  have hnneg : π (¬ znegative (intify k))
    { assume hneg;
      have hlt : π (zless (intify k) Int0)
        { refine ∧ₑ₁ (znegative_iff_zless_0 (intify k) (intify_in_int k)) hneg };
      have hlt0 : π (zless Int0 Int0)
        { refine zless_trans Int0 (intify k) Int0 hki hlt };
      refine zless_not_sym Int0 Int0 hlt0 hlt0 };
  have hm : π (int_of (nat_of (intify k)) = intify k)
    { refine not_zneg_nat_of (intify k) hnneg (intify_in_int k) };
  have hpos : π (lt empty (nat_of (intify k)))
    { refine ∧ₑ₂ (zless_nat_iff_int_zless empty (intify k) zero_in_omega (intify_in_int k))
        (ind_eq int_of_0 (λ v, zless v (intify k)) hki) };
  rewrite left (zmult_intify1 k i);
  rewrite left (zmult_intify1 k j);
  rewrite left hm;
  refine zmult_zless_mono2_lemma i j (nat_of (intify k)) hij (nat_of_type (intify k)) hpos
end;

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
begin
  assume i j k hij hk;
  refine ∧ₑ₁ (zminus_zless_zminus (zmult i k) (zmult j k)) _;
  rewrite left (zmult_zminus_right i k);
  rewrite left (zmult_zminus_right j k);
  have hkneg : π (zless Int0 (zminus k))
    { refine ind_eq (eq_sym zminus_0) (λ v, zless v (zminus k))
        (∧ₑ₂ (zminus_zless_zminus Int0 k) hk) };
  refine zmult_zless_mono1 i j (zminus k) hij hkneg
end;

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
begin
  assume m n hm hn;
  apply ∧ᵢ
  { assume h;
    refine ∨ₑ h _ _
    { assume hm0; rewrite hm0; refine zmult_0 n }
    { assume hn0; rewrite hn0; refine zmult_0_right m } }
  { assume hmn;
    refine ∨ₑ (em (m = Int0)) _ _
    { assume h; refine ∨ᵢ₁ h }
    { assume hmne;
      refine ∨ᵢ₂ _;
      refine ∨ₑ (em (n = Int0)) _ _
      { assume h; refine h }
      { assume hnne;
        refine ⊥ₑ _;
        have hmc : π (zless m Int0 ∨ zless Int0 m)
          { refine ∧ₑ₁ (neq_iff_zless m Int0 hm Int0_in_int) hmne };
        have hnc : π (zless n Int0 ∨ zless Int0 n)
          { refine ∧ₑ₁ (neq_iff_zless n Int0 hn Int0_in_int) hnne };
        refine ∨ₑ hmc _ _
        { assume hmneg;
          refine ∨ₑ hnc _ _
          { assume hnneg;
            have h1 : π (zless (zmult Int0 n) (zmult m n))
              { refine zmult_zless_mono1_neg m Int0 n hmneg hnneg };
            have hp : π (zless Int0 (zmult m n))
              { refine ind_eq (eq_sym (zmult_0 n)) (λ v, zless v (zmult m n)) h1 };
            have h00 : π (zless Int0 Int0)
              { refine ind_eq (eq_sym hmn) (λ v, zless Int0 v) hp };
            refine zless_not_sym Int0 Int0 h00 h00 }
          { assume hnpos;
            have h1 : π (zless (zmult n m) (zmult Int0 m))
              { refine zmult_zless_mono1_neg Int0 n m hnpos hmneg };
            have hq : π (zless (zmult n m) Int0)
              { refine ind_eq (eq_sym (zmult_0 m)) (λ v, zless (zmult n m) v) h1 };
            have hq2 : π (zless (zmult m n) Int0)
              { refine ind_eq (zmult_commute m n) (λ v, zless v Int0) hq };
            have h00 : π (zless Int0 Int0)
              { refine ind_eq (eq_sym hmn) (λ v, zless v Int0) hq2 };
            refine zless_not_sym Int0 Int0 h00 h00 } }
        { assume hmpos;
          refine ∨ₑ hnc _ _
          { assume hnneg;
            have h1 : π (zless (zmult m n) (zmult Int0 n))
              { refine zmult_zless_mono1_neg Int0 m n hmpos hnneg };
            have hq : π (zless (zmult m n) Int0)
              { refine ind_eq (eq_sym (zmult_0 n)) (λ v, zless (zmult m n) v) h1 };
            have h00 : π (zless Int0 Int0)
              { refine ind_eq (eq_sym hmn) (λ v, zless v Int0) hq };
            refine zless_not_sym Int0 Int0 h00 h00 }
          { assume hnpos;
            have h1 : π (zless (zmult Int0 n) (zmult m n))
              { refine zmult_zless_mono1 Int0 m n hmpos hnpos };
            have hp : π (zless Int0 (zmult m n))
              { refine ind_eq (eq_sym (zmult_0 n)) (λ v, zless v (zmult m n)) h1 };
            have h00 : π (zless Int0 Int0)
              { refine ind_eq (eq_sym hmn) (λ v, zless Int0 v) hp };
            refine zless_not_sym Int0 Int0 h00 h00 } } } } }
end;

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
begin
  assume k m n hk hm hn;
  apply ∧ᵢ
  { assume h;
    have hkne : π (k ≠ Int0)
      { assume hk0;
        have h1 : π (zless (zmult m Int0) (zmult n Int0))
          { refine ind_eq (eq_sym hk0) (λ v, zless (zmult m v) (zmult n v)) h };
        have h2a : π (zless Int0 (zmult n Int0))
          { refine ind_eq (eq_sym (zmult_0_right m)) (λ v, zless v (zmult n Int0)) h1 };
        have h2 : π (zless Int0 Int0)
          { refine ind_eq (eq_sym (zmult_0_right n)) (λ v, zless Int0 v) h2a };
        refine zless_not_sym Int0 Int0 h2 h2 };
    have hkc : π (zless k Int0 ∨ zless Int0 k)
      { refine ∧ₑ₁ (neq_iff_zless k Int0 hk Int0_in_int) hkne };
    refine ∨ₑ hkc _ _
    { assume hkneg;
      refine ∨ᵢ₂ (∧ᵢ hkneg _);
      refine ∨ₑ (em (zless n m)) (λ x, x) _;
      assume hnm;
      have hmn : π (zle m n) { refine ∧ₑ₁ (not_zless_iff_zle n m) hnm };
      have hle : π (zle (zmult n k) (zmult m k))
        { refine zmult_zle_mono1_neg m n k hmn (zless_imp_zle k Int0 hkneg) };
      have hbad : π (zless (zmult m k) (zmult m k))
        { refine zless_zle_trans (zmult m k) (zmult n k) (zmult m k) h hle };
      refine ⊥ₑ (zless_not_sym (zmult m k) (zmult m k) hbad hbad) }
    { assume hkpos;
      refine ∨ᵢ₁ (∧ᵢ hkpos _);
      refine ∨ₑ (em (zless m n)) (λ x, x) _;
      assume hmn0;
      have hnm : π (zle n m) { refine ∧ₑ₁ (not_zless_iff_zle m n) hmn0 };
      have hle : π (zle (zmult n k) (zmult m k))
        { refine zmult_zle_mono1 n m k hnm (zless_imp_zle Int0 k hkpos) };
      have hbad : π (zless (zmult m k) (zmult m k))
        { refine zless_zle_trans (zmult m k) (zmult n k) (zmult m k) h hle };
      refine ⊥ₑ (zless_not_sym (zmult m k) (zmult m k) hbad hbad) } }
  { assume h;
    refine ∨ₑ h _ _
    { assume hc; refine zmult_zless_mono1 m n k (∧ₑ₂ hc) (∧ₑ₁ hc) }
    { assume hc; refine zmult_zless_mono1_neg n m k (∧ₑ₂ hc) (∧ₑ₁ hc) } }
end;

opaque symbol zmult_zless_cancel2 (m k n : τ ι) :
  π (zless (zmult m k) (zmult n k) ⇔
     ((zless Int0 k ∧ zless m n) ∨ (zless k Int0 ∧ zless n m))) ≔
begin
  assume m k n;
  have hlem : π (zless (zmult (intify m) (intify k)) (zmult (intify n) (intify k)) ⇔
                 ((zless Int0 (intify k) ∧ zless (intify m) (intify n)) ∨
                  (zless (intify k) Int0 ∧ zless (intify n) (intify m))))
    { refine zmult_zless_lemma (intify k) (intify m) (intify n)
        (intify_in_int k) (intify_in_int m) (intify_in_int n) };
  apply ∧ᵢ
  { assume h;
    have h' : π (zless (zmult (intify m) (intify k)) (zmult (intify n) (intify k)))
      { refine ind_eq (zmult_deintify n k) (λ v, zless (zmult (intify m) (intify k)) v)
          (ind_eq (zmult_deintify m k) (λ v, zless v (zmult n k)) h) };
    refine ∨ₑ (∧ₑ₁ hlem h') _ _
    { assume hc;
      refine ∨ᵢ₁ (∧ᵢ (∧ₑ₁ (zless_intify2 Int0 k) (∧ₑ₁ hc)) (zless_out m n (∧ₑ₂ hc))) }
    { assume hc;
      refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ (zless_intify1 k Int0) (∧ₑ₁ hc)) (zless_out n m (∧ₑ₂ hc))) } }
  { assume h;
    have h' : π ((zless Int0 (intify k) ∧ zless (intify m) (intify n)) ∨
                 (zless (intify k) Int0 ∧ zless (intify n) (intify m)))
      { refine ∨ₑ h _ _
        { assume hc;
          refine ∨ᵢ₁ (∧ᵢ (∧ₑ₂ (zless_intify2 Int0 k) (∧ₑ₁ hc)) (zless_in m n (∧ₑ₂ hc))) }
        { assume hc;
          refine ∨ᵢ₂ (∧ᵢ (∧ₑ₂ (zless_intify1 k Int0) (∧ₑ₁ hc)) (zless_in n m (∧ₑ₂ hc))) } };
    have hr : π (zless (zmult (intify m) (intify k)) (zmult (intify n) (intify k)))
      { refine ∧ₑ₂ hlem h' };
    refine ind_eq (eq_sym (zmult_deintify m k)) (λ v, zless v (zmult n k))
      (ind_eq (eq_sym (zmult_deintify n k)) (λ v, zless (zmult (intify m) (intify k)) v) hr) }
end;

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
begin
  assume m k n;
  apply ∧ᵢ
  { assume h;
    refine ∧ᵢ _ _
    { assume hkpos;
      refine ∧ₑ₁ (not_zless_iff_zle n m) _;
      assume hnm;
      have hz : π (zless (zmult n k) (zmult m k))
        { refine ∧ₑ₂ (zmult_zless_cancel2 n k m) (∨ᵢ₁ (∧ᵢ hkpos hnm)) };
      have hbad : π (zless (zmult n k) (zmult n k))
        { refine zless_zle_trans (zmult n k) (zmult m k) (zmult n k) hz h };
      refine zless_not_sym (zmult n k) (zmult n k) hbad hbad }
    { assume hkneg;
      refine ∧ₑ₁ (not_zless_iff_zle m n) _;
      assume hmn;
      have hz : π (zless (zmult n k) (zmult m k))
        { refine ∧ₑ₂ (zmult_zless_cancel2 n k m) (∨ᵢ₂ (∧ᵢ hkneg hmn)) };
      have hbad : π (zless (zmult n k) (zmult n k))
        { refine zless_zle_trans (zmult n k) (zmult m k) (zmult n k) hz h };
      refine zless_not_sym (zmult n k) (zmult n k) hbad hbad } }
  { assume h;
    refine ∧ₑ₁ (not_zless_iff_zle (zmult n k) (zmult m k)) _;
    assume hz;
    refine ∨ₑ (∧ₑ₁ (zmult_zless_cancel2 n k m) hz) _ _
    { assume hc;
      have hle : π (zle m n) { refine ∧ₑ₁ h (∧ₑ₁ hc) };
      have hbad : π (zless n n)
        { refine zless_zle_trans n m n (∧ₑ₂ hc) hle };
      refine zless_not_sym n n hbad hbad }
    { assume hc;
      have hle : π (zle n m) { refine ∧ₑ₂ h (∧ₑ₁ hc) };
      have hbad : π (zless m m)
        { refine zless_zle_trans m n m (∧ₑ₂ hc) hle };
      refine zless_not_sym m m hbad hbad } }
end;

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
begin
  assume k m n hk hm hn;
  apply ∧ᵢ
  { assume heq;
    refine ∨ₑ (em (k = Int0)) _ _
    { assume h; refine ∨ᵢ₁ h }
    { assume hkne;
      refine ∨ᵢ₂ _;
      have h1 : π ((zless Int0 k ⇒ zle m n) ∧ (zless k Int0 ⇒ zle n m))
        { refine ∧ₑ₁ (zmult_zle_cancel2 m k n) (zle_eq_refl (zmult m k) (zmult n k) heq) };
      have h2 : π ((zless Int0 k ⇒ zle n m) ∧ (zless k Int0 ⇒ zle m n))
        { refine ∧ₑ₁ (zmult_zle_cancel2 n k m)
            (zle_eq_refl (zmult n k) (zmult m k) (eq_sym heq)) };
      refine ∨ₑ (∧ₑ₁ (neq_iff_zless k Int0 hk Int0_in_int) hkne) _ _
      { assume hkneg;
        refine zle_anti_sym m n (∧ₑ₂ h2 hkneg) (∧ₑ₂ h1 hkneg) hm hn }
      { assume hkpos;
        refine zle_anti_sym m n (∧ₑ₁ h1 hkpos) (∧ₑ₁ h2 hkpos) hm hn } } }
  { assume h;
    refine ∨ₑ h _ _
    { assume hk0;
      rewrite hk0;
      rewrite (zmult_0_right m);
      rewrite (zmult_0_right n);
      reflexivity }
    { assume hmn; rewrite hmn; reflexivity } }
end;

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
begin
  assume b q' r' q r H1 H2 H3 H4;
  have hstep_a : π (zle (zmult b q') (zadd (zmult b q') r'))
    { refine ∧ₑ₁ (zle_intify1 (zmult b q') (zadd (zmult b q') r'))
        (ind_eq (eq_sym (zadd_0_right_intify (zmult b q')))
          (λ w, zle w (zadd (zmult b q') r'))
          (zadd_zle_mono2 Int0 r' (zmult b q') H2)) };
  have hb_q' : π (zle (zmult b q') (zadd (zmult b q) r))
    { refine zle_trans (zmult b q') (zadd (zmult b q') r') (zadd (zmult b q) r) hstep_a H1 };
  have hb_q'_lt : π (zless (zmult b q') (zadd (zmult b q) b))
    { refine zle_zless_trans (zmult b q') (zadd (zmult b q) r) (zadd (zmult b q) b) hb_q'
        (zadd_zless_mono2 r b (zmult b q) H4) };
  have hbqp1 : π (zmult b (zadd q Int1) = zadd (zmult b q) b)
    { rewrite (zadd_zmult_distrib2 b q Int1); rewrite (zmult_1_right_intify b);
      refine zadd_intify2 (zmult b q) b };
  have hb_q'_lt2 : π (zless (zmult b q') (zmult b (zadd q Int1)))
    { refine ind_eq hbqp1 (λ w, zless (zmult b q') w) hb_q'_lt };
  refine ∨ₑ (∧ₑ₁ (zmult_zless_cancel1 b q' (zadd q Int1)) hb_q'_lt2) _ _
  { assume hc; refine ∧ₑ₁ (zless_add1_iff_zle q' q) (∧ₑ₂ hc) }
  { assume hc; refine ⊥ₑ (zless_not_sym Int0 b H3 (∧ₑ₁ hc)) }
end;

opaque symbol unique_quotient_lemma_neg (b q' r' q r : τ ι) :
  π (zle (zadd (zmult b q') r') (zadd (zmult b q) r)) →
  π (zle r Int0) → π (zless b Int0) → π (zless b r') →
  π (zle q q') ≔
begin
  assume b q' r' q r H1 H2 H3 H4;
  have hP1a : π (zadd (zmult (zminus b) q) (zminus r) = zminus (zadd (zmult b q) r))
    { rewrite (zmult_zminus b q); rewrite left (zminus_zadd_distrib (zmult b q) r); reflexivity };
  have hP1b : π (zadd (zmult (zminus b) q') (zminus r') = zminus (zadd (zmult b q') r'))
    { rewrite (zmult_zminus b q'); rewrite left (zminus_zadd_distrib (zmult b q') r'); reflexivity };
  refine unique_quotient_lemma (zminus b) q (zminus r) q' (zminus r') _ _ _ _
  { rewrite hP1a; rewrite hP1b;
    refine ∧ₑ₂ (zminus_zle_zminus (zadd (zmult b q) r) (zadd (zmult b q') r')) H1 }
  { refine ∧ₑ₂ (zle_zminus Int0 r) (ind_eq zminus_0 (λ w, zle r w) H2) }
  { refine ∧ₑ₂ (zless_zminus Int0 b) (ind_eq zminus_0 (λ w, zless b w) H3) }
  { refine ∧ₑ₂ (zminus_zless_zminus r' b) H4 }
end;

// port-internal helper: general quorem extraction (no sign assumption on b).
private opaque symbol quoremE (a b qr : τ ι) :
  π (quorem (Pair a b) qr) →
  π (a = zadd (zmult b (fst qr)) (snd qr)
     ∧ ((zless Int0 b ∧ zle Int0 (snd qr) ∧ zless (snd qr) b)
        ∨ (¬ (zless Int0 b) ∧ zless b (snd qr) ∧ zle (snd qr) Int0))) ≔
begin
  assume a b qr hq;
  have hu : π (fst (Pair a b) = zadd (zmult (snd (Pair a b)) (fst qr)) (snd qr) ∧
    ((zless Int0 (snd (Pair a b)) ∧ zle Int0 (snd qr) ∧ zless (snd qr) (snd (Pair a b))) ∨
     (¬ (zless Int0 (snd (Pair a b))) ∧ zless (snd (Pair a b)) (snd qr) ∧ zle (snd qr) Int0)))
    { refine ind_eq (eq_sym (quorem_def (Pair a b) qr)) (λ p, p) hq };
  have hu_s : π (fst (Pair a b) = zadd (zmult b (fst qr)) (snd qr) ∧
    ((zless Int0 b ∧ zle Int0 (snd qr) ∧ zless (snd qr) b) ∨
     (¬ (zless Int0 b) ∧ zless b (snd qr) ∧ zle (snd qr) Int0)))
    { refine ind_eq (eq_sym (snd_conv a b))
        (λ w, fst (Pair a b) = zadd (zmult w (fst qr)) (snd qr) ∧
          ((zless Int0 w ∧ zle Int0 (snd qr) ∧ zless (snd qr) w) ∨
           (¬ (zless Int0 w) ∧ zless w (snd qr) ∧ zle (snd qr) Int0))) hu };
  refine ind_eq (eq_sym (fst_conv a b))
    (λ w, w = zadd (zmult b (fst qr)) (snd qr) ∧
      ((zless Int0 b ∧ zle Int0 (snd qr) ∧ zless (snd qr) b) ∨
       (¬ (zless Int0 b) ∧ zless b (snd qr) ∧ zle (snd qr) Int0))) hu_s
end;

// port-internal helper: general quorem builder.
private opaque symbol quoremI (a b q r : τ ι) :
  π (a = zadd (zmult b q) r) →
  π ((zless Int0 b ∧ zle Int0 r ∧ zless r b)
     ∨ (¬ (zless Int0 b) ∧ zless b r ∧ zle r Int0)) →
  π (quorem (Pair a b) (Pair q r)) ≔
begin
  assume a b q r heq hdisj;
  rewrite quorem_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∧ᵢ heq hdisj
end;

// port-internal helper: quorem extraction with a concrete quotient pair.
private opaque symbol quoremE_pair (a b q r : τ ι) :
  π (quorem (Pair a b) (Pair q r)) →
  π (a = zadd (zmult b q) r
     ∧ ((zless Int0 b ∧ zle Int0 r ∧ zless r b)
        ∨ (¬ (zless Int0 b) ∧ zless b r ∧ zle r Int0))) ≔
begin
  assume a b q r hq;
  have hE : π (a = zadd (zmult b (fst (Pair q r))) (snd (Pair q r))
     ∧ ((zless Int0 b ∧ zle Int0 (snd (Pair q r)) ∧ zless (snd (Pair q r)) b)
        ∨ (¬ (zless Int0 b) ∧ zless b (snd (Pair q r)) ∧ zle (snd (Pair q r)) Int0)))
    { refine quoremE a b (Pair q r) hq };
  have hE_s : π (a = zadd (zmult b (fst (Pair q r))) r
     ∧ ((zless Int0 b ∧ zle Int0 r ∧ zless r b)
        ∨ (¬ (zless Int0 b) ∧ zless b r ∧ zle r Int0)))
    { refine ind_eq (eq_sym (snd_conv q r))
        (λ w, a = zadd (zmult b (fst (Pair q r))) w
           ∧ ((zless Int0 b ∧ zle Int0 w ∧ zless w b)
              ∨ (¬ (zless Int0 b) ∧ zless b w ∧ zle w Int0))) hE };
  refine ind_eq (eq_sym (fst_conv q r))
    (λ w, a = zadd (zmult b w) r
       ∧ ((zless Int0 b ∧ zle Int0 r ∧ zless r b)
          ∨ (¬ (zless Int0 b) ∧ zless b r ∧ zle r Int0))) hE_s
end;

opaque symbol unique_quotient (a b q r q' r' : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (quorem (Pair a b) (Pair q' r')) →
  π (b ∈ int) → π (b ≠ Int0) → π (q ∈ int) → π (q' ∈ int) →
  π (q = q') ≔
begin
  assume a b q r q' r' hq1 hq2 hb hb0 hqi hqi';
  have hE1 : π (a = zadd (zmult b q) r
     ∧ ((zless Int0 b ∧ zle Int0 r ∧ zless r b)
        ∨ (¬ (zless Int0 b) ∧ zless b r ∧ zle r Int0)))
    { refine quoremE_pair a b q r hq1 };
  have hE2 : π (a = zadd (zmult b q') r'
     ∧ ((zless Int0 b ∧ zle Int0 r' ∧ zless r' b)
        ∨ (¬ (zless Int0 b) ∧ zless b r' ∧ zle r' Int0)))
    { refine quoremE_pair a b q' r' hq2 };
  have hle12 : π (zle (zadd (zmult b q') r') (zadd (zmult b q) r))
    { refine zle_eq_refl (zadd (zmult b q') r') (zadd (zmult b q) r)
        (eq_trans (eq_sym (∧ₑ₁ hE2)) (∧ₑ₁ hE1)) };
  have hle21 : π (zle (zadd (zmult b q) r) (zadd (zmult b q') r'))
    { refine zle_eq_refl (zadd (zmult b q) r) (zadd (zmult b q') r')
        (eq_trans (eq_sym (∧ₑ₁ hE1)) (∧ₑ₁ hE2)) };
  refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) _ _
  { assume hbneg;
    have hd1 : π (zless b r ∧ zle r Int0)
      { refine ∨ₑ (∧ₑ₂ hE1) _ _
        { assume hc; refine ⊥ₑ (zless_not_sym b Int0 hbneg (∧ₑ₁ hc)) }
        { assume hc; refine ∧ᵢ (∧ₑ₁ (∧ₑ₂ hc)) (∧ₑ₂ (∧ₑ₂ hc)) } };
    have hd2 : π (zless b r' ∧ zle r' Int0)
      { refine ∨ₑ (∧ₑ₂ hE2) _ _
        { assume hc; refine ⊥ₑ (zless_not_sym b Int0 hbneg (∧ₑ₁ hc)) }
        { assume hc; refine ∧ᵢ (∧ₑ₁ (∧ₑ₂ hc)) (∧ₑ₂ (∧ₑ₂ hc)) } };
    refine zle_anti_sym q q'
      (unique_quotient_lemma_neg b q' r' q r hle12 (∧ₑ₂ hd1) hbneg (∧ₑ₁ hd2))
      (unique_quotient_lemma_neg b q r q' r' hle21 (∧ₑ₂ hd2) hbneg (∧ₑ₁ hd1))
      hqi hqi' }
  { assume hbpos;
    have hd1 : π (zle Int0 r ∧ zless r b)
      { refine ∨ₑ (∧ₑ₂ hE1) _ _
        { assume hc; refine ∧ᵢ (∧ₑ₁ (∧ₑ₂ hc)) (∧ₑ₂ (∧ₑ₂ hc)) }
        { assume hc; refine ⊥ₑ (∧ₑ₁ hc hbpos) } };
    have hd2 : π (zle Int0 r' ∧ zless r' b)
      { refine ∨ₑ (∧ₑ₂ hE2) _ _
        { assume hc; refine ∧ᵢ (∧ₑ₁ (∧ₑ₂ hc)) (∧ₑ₂ (∧ₑ₂ hc)) }
        { assume hc; refine ⊥ₑ (∧ₑ₁ hc hbpos) } };
    refine zle_anti_sym q q'
      (unique_quotient_lemma b q r q' r' hle21 (∧ₑ₁ hd1) hbpos (∧ₑ₂ hd2))
      (unique_quotient_lemma b q' r' q r hle12 (∧ₑ₁ hd2) hbpos (∧ₑ₂ hd1))
      hqi hqi' }
end;

opaque symbol unique_remainder (a b q r q' r' : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (quorem (Pair a b) (Pair q' r')) →
  π (b ∈ int) → π (b ≠ Int0) → π (q ∈ int) → π (q' ∈ int) →
  π (r ∈ int) → π (r' ∈ int) →
  π (r = r') ≔
begin
  assume a b q r q' r' hq1 hq2 hb hb0 hqi hqi' hri hri';
  have hqq : π (q = q') { refine unique_quotient a b q r q' r' hq1 hq2 hb hb0 hqi hqi' };
  have heq1 : π (a = zadd (zmult b q) r) { refine ∧ₑ₁ (quoremE_pair a b q r hq1) };
  have heq2 : π (a = zadd (zmult b q') r') { refine ∧ₑ₁ (quoremE_pair a b q' r' hq2) };
  have heq2' : π (a = zadd (zmult b q) r')
    { refine ind_eq hqq (λ w, a = zadd (zmult b w) r') heq2 };
  refine ∧ₑ₁ (zadd_left_cancel r' r (zmult b q) hri' hri)
    (eq_trans (eq_sym heq1) heq2')
end;

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

// port-internal helper: adjust preserves the int*int type (both If branches
// are pairs of integers).  Used by posDivAlg_type / negDivAlg_type.
private opaque symbol adjust_type (b qr : τ ι) :
  π (qr ∈ Sigma int (λ _, int)) → π (adjust b qr ∈ Sigma int (λ _, int)) ≔
begin
  assume b qr hqr;
  rewrite adjust_def;
  refine ∨ₑ (em (zle Int0 (zdiff (snd qr) b))) _ _
  { assume h;
    rewrite (If_P (zle Int0 (zdiff (snd qr) b)) _ _ h);
    refine SigmaI (zadd (zmult Int2 (fst qr)) Int1) (zdiff (snd qr) b) int (λ _, int)
      (zadd_type (zmult Int2 (fst qr)) Int1) (zdiff_type (snd qr) b) }
  { assume h;
    rewrite (If_not_P (zle Int0 (zdiff (snd qr) b)) _ _ h);
    refine SigmaI (zmult Int2 (fst qr)) (snd qr) int (λ _, int)
      (zmult_type Int2 (fst qr)) (SigmaD2 qr int (λ _, int) hqr) }
end;

opaque symbol posDivAlg_termination (a b : τ ι) :
  π (zless Int0 b) → π (¬ zless a b) →
  π (lt (nat_of (zadd (zdiff a (zmult Int2 b)) Int1)) (nat_of (zadd (zdiff a b) Int1))) ≔
begin
  assume a b hb hab;
  have hb2 : π (zless b (zmult Int2 b))
    { refine ∧ₑ₁ (zless_intify1 b (zmult Int2 b)) _;
      rewrite Int2_eq_add;
      rewrite (zadd_zmult_distrib Int1 Int1 b);
      rewrite zmult_1_intify;
      have hbi : π (zless Int0 (intify b)) { refine ∧ₑ₂ (zless_intify2 Int0 b) hb };
      have hstep : π (zless (zadd (intify b) Int0) (zadd (intify b) (intify b)))
        { refine zadd_zless_mono2 Int0 (intify b) (intify b) hbi };
      have heq : π (zadd (intify b) Int0 = intify b)
        { rewrite (zadd_0_right_intify (intify b)); refine intify_idem b };
      refine ind_eq (eq_sym heq) (λ v, zless v (zadd (intify b) (intify b))) hstep };
  refine ∧ₑ₂ (zless_nat_conj (zadd (zdiff a (zmult Int2 b)) Int1) (zadd (zdiff a b) Int1)) _;
  refine ∧ᵢ _ _
  { refine ind_eq int_of_0 (λ u, zless u (zadd (zdiff a b) Int1)) _;
    refine ∧ₑ₂ (zless_add1_iff_zle Int0 (zdiff a b)) _;
    refine ∧ₑ₂ (zle_zdiff_iff Int0 b a) _;
    refine ind_eq (zadd_0_intify b) (λ v, zle v a) (∧ₑ₂ (zle_intify1 b a) _);
    refine ∧ₑ₁ (not_zless_iff_zle a b) hab }
  { refine zadd_zless_mono1 (zdiff a (zmult Int2 b)) (zdiff a b) Int1 _;
    rewrite (zdiff_def a (zmult Int2 b));
    rewrite (zdiff_def a b);
    refine zadd_zless_mono2 (zminus (zmult Int2 b)) (zminus b) a _;
    refine ∧ₑ₂ (zminus_zless_zminus (zmult Int2 b) b) hb2 }
end;

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
begin
  assume ab;
  rewrite posDivAlg_def;
  rewrite (wfrec_eq
    (measure (Sigma int (λ _, int))
       (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
    ab
    (λ ab2 f,
       If (zless (fst ab2) (snd ab2) ∨ zle (snd ab2) Int0)
          (Pair Int0 (fst ab2))
          (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2))))))
    (wf_measure (Sigma int (λ _, int))
       (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))));
  simplify rule off;
  have hlam :
    π (Lambda (vimage_singleton
                 (measure (Sigma int (λ _, int))
                    (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))) ab)
         (λ x, wfrec
                 (measure (Sigma int (λ _, int))
                    (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
                 x
                 (λ ab2 f,
                    If (zless (fst ab2) (snd ab2) ∨ zle (snd ab2) Int0)
                       (Pair Int0 (fst ab2))
                       (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2)))))))
       = Lambda (vimage_singleton
                   (measure (Sigma int (λ _, int))
                      (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))) ab)
           (λ x, posDivAlg x))
    { refine lam_cong
        (vimage_singleton
           (measure (Sigma int (λ _, int))
              (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))) ab)
        (vimage_singleton
           (measure (Sigma int (λ _, int))
              (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))) ab)
        (λ x, wfrec
                (measure (Sigma int (λ _, int))
                   (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
                x
                (λ ab2 f,
                   If (zless (fst ab2) (snd ab2) ∨ zle (snd ab2) Int0)
                      (Pair Int0 (fst ab2))
                      (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2)))))))
        (λ x, posDivAlg x)
        (eq_refl _) _;
      assume x hx;
      rewrite posDivAlg_def;
      reflexivity };
  rewrite hlam;
  reflexivity
end;

opaque symbol posDivAlg_eqn (a b : τ ι) :
  π (zless Int0 b) → π (a ∈ int) → π (b ∈ int) →
  π (posDivAlg (Pair a b) =
     If (zless a b) (Pair Int0 a) (adjust b (posDivAlg (Pair a (zmult Int2 b))))) ≔
begin
  assume a b hb ha hb_int;
  rewrite posDivAlg_unfold;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∨ₑ (em (zless a b)) _ _
  { assume h1;
    rewrite (If_P (zless a b ∨ zle b Int0) _ _ (∨ᵢ₁ h1));
    rewrite (If_P (zless a b) _ _ h1);
    reflexivity }
  { assume h2;
    have hncond : π (¬ (zless a b ∨ zle b Int0))
      { assume hd; refine ∨ₑ hd _ _
        { assume hh; refine h2 hh }
        { assume hh; refine (∧ₑ₂ (not_zle_iff_zless b Int0) hb) hh } };
    rewrite (If_not_P (zless a b ∨ zle b Int0) _ _ hncond);
    rewrite (If_not_P (zless a b) _ _ h2);
    have hmem : π (Pair a (zmult Int2 b) ∈
        vimage_singleton
          (measure (Sigma int (λ _, int)) (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
          (Pair a b))
      { refine vimage_singletonI (Pair a (zmult Int2 b)) (Pair a b)
          (measure (Sigma int (λ _, int)) (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))) _;
        refine ∧ₑ₂ (measure_iff (Sigma int (λ _, int))
          (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))
          (Pair a (zmult Int2 b)) (Pair a b)) _;
        refine ∧ᵢ (SigmaI a (zmult Int2 b) int (λ _, int) ha (zmult_type Int2 b))
              (∧ᵢ (SigmaI a b int (λ _, int) ha hb_int) _);
        repeat orelse rewrite fst_conv rewrite snd_conv;
        refine posDivAlg_termination a b hb h2 };
    have hbeta : π (fapply (Lambda
          (vimage_singleton
            (measure (Sigma int (λ _, int)) (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
            (Pair a b))
          (λ x, posDivAlg x)) (Pair a (zmult Int2 b))
        = posDivAlg (Pair a (zmult Int2 b)))
      { refine beta
          (vimage_singleton
            (measure (Sigma int (λ _, int)) (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
            (Pair a b))
          (λ x, posDivAlg x) (Pair a (zmult Int2 b)) hmem };
    rewrite hbeta;
    reflexivity }
end;

opaque symbol posDivAlg_induct_lemma (P : τ ι → Prop) (u v : τ ι) :
  (Π (a b : τ ι), π (a ∈ int) → π (b ∈ int) →
    π (¬ (zless a b ∨ zle b Int0) ⇒ P (Pair a (zmult Int2 b))) →
    π (P (Pair a b))) →
  π (Pair u v ∈ Sigma int (λ _, int)) →
  π (P (Pair u v)) ≔
begin
  assume P u v prem huv;
  refine wf_global_induct
    (measure (Sigma int (λ _, int)) (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
    (λ z, z ∈ Sigma int (λ _, int) ⇒ P z)
    (Pair u v)
    (wf_measure (Sigma int (λ _, int)) (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
    _
    huv;
  assume x hpred hxA;
  have hfx : π (fst x ∈ int) { refine SigmaD1 x int (λ _, int) hxA };
  have hsx : π (snd x ∈ int) { refine SigmaD2 x int (λ _, int) hxA };
  have hxeq : π (Pair (fst x) (snd x) = x) { refine Pair_fst_snd x int (λ _, int) hxA };
  refine ind_eq (eq_sym hxeq) (λ w, P w) _;
  refine prem (fst x) (snd x) hfx hsx _;
  assume hcond;
  have hnlt : π (¬ zless (fst x) (snd x)) { assume h; refine hcond (∨ᵢ₁ h) };
  have hnle : π (¬ zle (snd x) Int0) { assume h; refine hcond (∨ᵢ₂ h) };
  have hb' : π (zless Int0 (snd x)) { refine ∧ₑ₁ (not_zle_iff_zless (snd x) Int0) hnle };
  have hyA : π (Pair (fst x) (zmult Int2 (snd x)) ∈ Sigma int (λ _, int))
    { refine SigmaI (fst x) (zmult Int2 (snd x)) int (λ _, int) hfx (zmult_type Int2 (snd x)) };
  have hyr : π (Pair (Pair (fst x) (zmult Int2 (snd x))) x ∈
      measure (Sigma int (λ _, int)) (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1)))
    { refine ∧ₑ₂ (measure_iff (Sigma int (λ _, int))
        (λ p, nat_of (zadd (zdiff (fst p) (snd p)) Int1))
        (Pair (fst x) (zmult Int2 (snd x))) x) _;
      refine ∧ᵢ hyA (∧ᵢ hxA _);
      repeat orelse rewrite fst_conv rewrite snd_conv;
      refine posDivAlg_termination (fst x) (snd x) hb' hnlt };
  refine hpred (Pair (fst x) (zmult Int2 (snd x))) hyr hyA
end;

opaque symbol posDivAlg_induct (P : τ ι → τ ι → Prop) (u v : τ ι) :
  π (u ∈ int) → π (v ∈ int) →
  (Π (a b : τ ι), π (a ∈ int) → π (b ∈ int) →
    π (¬ (zless a b ∨ zle b Int0) ⇒ P a (zmult Int2 b)) →
    π (P a b)) →
  π (P u v) ≔
begin
  assume P u v hu hv ih;
  have huv : π (Pair u v ∈ Sigma int (λ _, int))
    { refine SigmaI u v int (λ _, int) hu hv };
  have hmain : π (P (fst (Pair u v)) (snd (Pair u v)))
    { refine posDivAlg_induct_lemma (λ z, P (fst z) (snd z)) u v _ huv;
      assume a b ha hb himp;
      have hres : π (P a b)
        { refine ih a b ha hb _;
          assume hcond;
          have hh : π (P (fst (Pair a (zmult Int2 b))) (snd (Pair a (zmult Int2 b))))
            { refine himp hcond };
          have h1 : π (P a (snd (Pair a (zmult Int2 b))))
            { refine ind_eq (eq_sym (fst_conv a (zmult Int2 b)))
                (λ w, P w (snd (Pair a (zmult Int2 b)))) hh };
          refine ind_eq (eq_sym (snd_conv a (zmult Int2 b))) (λ w, P a w) h1 };
      have hf : π (P (fst (Pair a b)) b)
        { refine ind_eq (fst_conv a b) (λ w, P w b) hres };
      refine ind_eq (snd_conv a b) (λ w, P (fst (Pair a b)) w) hf };
  have hm1 : π (P u (snd (Pair u v)))
    { refine ind_eq (eq_sym (fst_conv u v)) (λ w, P w (snd (Pair u v))) hmain };
  refine ind_eq (eq_sym (snd_conv u v)) (λ w, P u w) hm1
end;

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
begin
  assume x y hx hy;
  apply ∧ᵢ
  { assume h;
    have hxne : π (x ≠ Int0)
      { assume hx0;
        have hc : π (zless Int0 (zmult Int0 y))
          { refine ind_eq (eq_sym hx0) (λ v, zless Int0 (zmult v y)) h };
        have hc2 : π (zless Int0 Int0)
          { refine ind_eq (eq_sym (zmult_0 y)) (λ v, zless Int0 v) hc };
        refine zless_not_sym Int0 Int0 hc2 hc2 };
    have hyne : π (y ≠ Int0)
      { assume hy0;
        have hc : π (zless Int0 (zmult x Int0))
          { refine ind_eq (eq_sym hy0) (λ v, zless Int0 (zmult x v)) h };
        have hc2 : π (zless Int0 Int0)
          { refine ind_eq (eq_sym (zmult_0_right x)) (λ v, zless Int0 v) hc };
        refine zless_not_sym Int0 Int0 hc2 hc2 };
    have hxc : π (zless x Int0 ∨ zless Int0 x)
      { refine ∧ₑ₁ (neq_iff_zless x Int0 hx Int0_in_int) hxne };
    have hyc : π (zless y Int0 ∨ zless Int0 y)
      { refine ∧ₑ₁ (neq_iff_zless y Int0 hy Int0_in_int) hyne };
    refine ∨ₑ hxc _ _
    { assume hxneg;
      refine ∨ₑ hyc _ _
      { assume hyneg; refine ∨ᵢ₂ (∧ᵢ hxneg hyneg) }
      { assume hypos;
        have hq : π (zless (zmult y x) Int0) { refine zmult_pos_neg y x hypos hxneg };
        have hq2 : π (zless (zmult x y) Int0)
          { refine ind_eq (zmult_commute x y) (λ v, zless v Int0) hq };
        have h00 : π (zless Int0 Int0)
          { refine zless_trans Int0 (zmult x y) Int0 h hq2 };
        refine ⊥ₑ (zless_not_sym Int0 Int0 h00 h00) } }
    { assume hxpos;
      refine ∨ₑ hyc _ _
      { assume hyneg;
        have hq : π (zless (zmult x y) Int0) { refine zmult_pos_neg x y hxpos hyneg };
        have h00 : π (zless Int0 Int0)
          { refine zless_trans Int0 (zmult x y) Int0 h hq };
        refine ⊥ₑ (zless_not_sym Int0 Int0 h00 h00) }
      { assume hypos; refine ∨ᵢ₁ (∧ᵢ hxpos hypos) } } }
  { assume h;
    refine ∨ₑ h _ _
    { assume hc; refine zmult_pos x y (∧ₑ₁ hc) (∧ₑ₂ hc) }
    { assume hc; refine zmult_neg x y (∧ₑ₁ hc) (∧ₑ₂ hc) } }
end;

opaque symbol int_0_less_mult_iff (x y : τ ι) :
  π (zless Int0 (zmult x y) ⇔
     ((zless Int0 x ∧ zless Int0 y) ∨ (zless x Int0 ∧ zless y Int0))) ≔
begin
  assume x y;
  have hlem : π (zless Int0 (zmult (intify x) (intify y)) ⇔
                 ((zless Int0 (intify x) ∧ zless Int0 (intify y)) ∨
                  (zless (intify x) Int0 ∧ zless (intify y) Int0)))
    { refine int_0_less_lemma (intify x) (intify y) (intify_in_int x) (intify_in_int y) };
  apply ∧ᵢ
  { assume h;
    have h' : π (zless Int0 (zmult (intify x) (intify y)))
      { refine ind_eq (zmult_deintify x y) (λ v, zless Int0 v) h };
    refine ∨ₑ (∧ₑ₁ hlem h') _ _
    { assume hc;
      refine ∨ᵢ₁ (∧ᵢ (∧ₑ₁ (zless_intify2 Int0 x) (∧ₑ₁ hc))
                       (∧ₑ₁ (zless_intify2 Int0 y) (∧ₑ₂ hc))) }
    { assume hc;
      refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ (zless_intify1 x Int0) (∧ₑ₁ hc))
                       (∧ₑ₁ (zless_intify1 y Int0) (∧ₑ₂ hc))) } }
  { assume h;
    have h' : π ((zless Int0 (intify x) ∧ zless Int0 (intify y)) ∨
                 (zless (intify x) Int0 ∧ zless (intify y) Int0))
      { refine ∨ₑ h _ _
        { assume hc;
          refine ∨ᵢ₁ (∧ᵢ (∧ₑ₂ (zless_intify2 Int0 x) (∧ₑ₁ hc))
                           (∧ₑ₂ (zless_intify2 Int0 y) (∧ₑ₂ hc))) }
        { assume hc;
          refine ∨ᵢ₂ (∧ᵢ (∧ₑ₂ (zless_intify1 x Int0) (∧ₑ₁ hc))
                           (∧ₑ₂ (zless_intify1 y Int0) (∧ₑ₂ hc))) } };
    refine ind_eq (eq_sym (zmult_deintify x y)) (λ v, zless Int0 v) (∧ₑ₂ hlem h') }
end;

opaque symbol int_0_le_lemma (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) →
  π (zle Int0 (zmult x y) ⇔
     ((zle Int0 x ∧ zle Int0 y) ∨ (zle x Int0 ∧ zle y Int0))) ≔
begin
  assume x y hx hy;
  apply ∧ᵢ
  { assume h;
    have hdisj : π (zless Int0 (zmult x y) ∨ intify Int0 = intify (zmult x y))
      { refine ind_eq (eq_sym (zle_def Int0 (zmult x y))) (λ p, p) h };
    refine ∨ₑ hdisj _ _
    { assume hlt;
      refine ∨ₑ (∧ₑ₁ (int_0_less_mult_iff x y) hlt) _ _
      { assume hc; refine ∨ᵢ₁ (∧ᵢ (zless_imp_zle Int0 x (∧ₑ₁ hc)) (zless_imp_zle Int0 y (∧ₑ₂ hc))) }
      { assume hc; refine ∨ᵢ₂ (∧ᵢ (zless_imp_zle x Int0 (∧ₑ₁ hc)) (zless_imp_zle y Int0 (∧ₑ₂ hc))) } }
    { assume heq;
      have hmn0 : π (zmult x y = Int0)
        { rewrite left (intify_ident (zmult x y) (zmult_type x y));
          rewrite left (intify_ident Int0 Int0_in_int);
          refine eq_sym heq };
      refine ∨ₑ (∧ₑ₂ (zmult_eq_lemma x y hx hy) hmn0) _ _
      { assume hx0;
        have hle0x : π (zle Int0 x) { refine ind_eq hx0 (λ v, zle Int0 v) (zle_refl Int0) };
        have hlex0 : π (zle x Int0) { refine ind_eq hx0 (λ v, zle v Int0) (zle_refl Int0) };
        refine ∨ₑ (em (zle Int0 y)) _ _
        { assume hyle; refine ∨ᵢ₁ (∧ᵢ hle0x hyle) }
        { assume hyn;
          refine ∨ᵢ₂ (∧ᵢ hlex0 (zless_imp_zle y Int0 (∧ₑ₁ (not_zle_iff_zless Int0 y) hyn))) } }
      { assume hy0;
        have hle0y : π (zle Int0 y) { refine ind_eq hy0 (λ v, zle Int0 v) (zle_refl Int0) };
        have hley0 : π (zle y Int0) { refine ind_eq hy0 (λ v, zle v Int0) (zle_refl Int0) };
        refine ∨ₑ (em (zle Int0 x)) _ _
        { assume hxle; refine ∨ᵢ₁ (∧ᵢ hxle hle0y) }
        { assume hxn;
          refine ∨ᵢ₂ (∧ᵢ (zless_imp_zle x Int0 (∧ₑ₁ (not_zle_iff_zless Int0 x) hxn)) hley0) } } } }
  { assume h;
    refine ∨ₑ h _ _
    { assume hc;
      have hm : π (zle (zmult Int0 y) (zmult x y))
        { refine zmult_zle_mono1 Int0 x y (∧ₑ₁ hc) (∧ₑ₂ hc) };
      refine ind_eq (eq_sym (zmult_0 y)) (λ v, zle v (zmult x y)) hm }
    { assume hc;
      have hm : π (zle (zmult Int0 y) (zmult x y))
        { refine zmult_zle_mono1_neg x Int0 y (∧ₑ₁ hc) (∧ₑ₂ hc) };
      refine ind_eq (eq_sym (zmult_0 y)) (λ v, zle v (zmult x y)) hm } }
end;

opaque symbol int_0_le_mult_iff (x y : τ ι) :
  π (zle Int0 (zmult x y) ⇔
     ((zle Int0 x ∧ zle Int0 y) ∨ (zle x Int0 ∧ zle y Int0))) ≔
begin
  assume x y;
  have hlem : π (zle Int0 (zmult (intify x) (intify y)) ⇔
                 ((zle Int0 (intify x) ∧ zle Int0 (intify y)) ∨
                  (zle (intify x) Int0 ∧ zle (intify y) Int0)))
    { refine int_0_le_lemma (intify x) (intify y) (intify_in_int x) (intify_in_int y) };
  apply ∧ᵢ
  { assume h;
    have h' : π (zle Int0 (zmult (intify x) (intify y)))
      { refine ind_eq (zmult_deintify x y) (λ v, zle Int0 v) h };
    refine ∨ₑ (∧ₑ₁ hlem h') _ _
    { assume hc;
      refine ∨ᵢ₁ (∧ᵢ (∧ₑ₁ (zle_intify2 Int0 x) (∧ₑ₁ hc))
                       (∧ₑ₁ (zle_intify2 Int0 y) (∧ₑ₂ hc))) }
    { assume hc;
      refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ (zle_intify1 x Int0) (∧ₑ₁ hc))
                       (∧ₑ₁ (zle_intify1 y Int0) (∧ₑ₂ hc))) } }
  { assume h;
    have h' : π ((zle Int0 (intify x) ∧ zle Int0 (intify y)) ∨
                 (zle (intify x) Int0 ∧ zle (intify y) Int0))
      { refine ∨ₑ h _ _
        { assume hc;
          refine ∨ᵢ₁ (∧ᵢ (∧ₑ₂ (zle_intify2 Int0 x) (∧ₑ₁ hc))
                           (∧ₑ₂ (zle_intify2 Int0 y) (∧ₑ₂ hc))) }
        { assume hc;
          refine ∨ᵢ₂ (∧ᵢ (∧ₑ₂ (zle_intify1 x Int0) (∧ₑ₁ hc))
                           (∧ₑ₂ (zle_intify1 y Int0) (∧ₑ₂ hc))) } };
    refine ind_eq (eq_sym (zmult_deintify x y)) (λ v, zle Int0 v) (∧ₑ₂ hlem h') }
end;

opaque symbol zmult_less_0_iff (x y : τ ι) :
  π (zless (zmult x y) Int0 ⇔
     ((zless Int0 x ∧ zless y Int0) ∨ (zless x Int0 ∧ zless Int0 y))) ≔
begin
  assume x y;
  have hbridge : π (zless (zmult x y) Int0 ⇔ zless Int0 (zmult x (zminus y)))
    { rewrite (zmult_zminus_right x y);
      apply ∧ᵢ
      { assume h;
        refine ∧ₑ₂ (zless_zminus Int0 (zmult x y))
          (ind_eq zminus_0 (λ v, zless (zmult x y) v) h) }
      { assume h;
        refine ind_eq (eq_sym zminus_0) (λ v, zless (zmult x y) v)
          (∧ₑ₁ (zless_zminus Int0 (zmult x y)) h) } };
  have hmul : π (zless Int0 (zmult x (zminus y)) ⇔
                 ((zless Int0 x ∧ zless Int0 (zminus y)) ∨
                  (zless x Int0 ∧ zless (zminus y) Int0)))
    { refine int_0_less_mult_iff x (zminus y) };
  have hCy : π (zless Int0 (zminus y) ⇔ zless y Int0)
    { apply ∧ᵢ
      { assume h; refine ind_eq (eq_sym zminus_0) (λ v, zless y v)
          (∧ₑ₁ (zless_zminus Int0 y) h) }
      { assume h; refine ∧ₑ₂ (zless_zminus Int0 y)
          (ind_eq zminus_0 (λ v, zless y v) h) } };
  have hDy : π (zless (zminus y) Int0 ⇔ zless Int0 y)
    { apply ∧ᵢ
      { assume h; refine ind_eq (eq_sym zminus_0) (λ v, zless v y)
          (∧ₑ₁ (zminus_zless y Int0) h) }
      { assume h; refine ∧ₑ₂ (zminus_zless y Int0)
          (ind_eq zminus_0 (λ v, zless v y) h) } };
  apply ∧ᵢ
  { assume h;
    refine ∨ₑ (∧ₑ₁ hmul (∧ₑ₁ hbridge h)) _ _
    { assume hc; refine ∨ᵢ₁ (∧ᵢ (∧ₑ₁ hc) (∧ₑ₁ hCy (∧ₑ₂ hc))) }
    { assume hc; refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ hc) (∧ₑ₁ hDy (∧ₑ₂ hc))) } }
  { assume h;
    refine ∧ₑ₂ hbridge (∧ₑ₂ hmul _);
    refine ∨ₑ h _ _
    { assume hc; refine ∨ᵢ₁ (∧ᵢ (∧ₑ₁ hc) (∧ₑ₂ hCy (∧ₑ₂ hc))) }
    { assume hc; refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ hc) (∧ₑ₂ hDy (∧ₑ₂ hc))) } }
end;

opaque symbol zmult_le_0_iff (x y : τ ι) :
  π (zle (zmult x y) Int0 ⇔
     ((zle Int0 x ∧ zle y Int0) ∨ (zle x Int0 ∧ zle Int0 y))) ≔
begin
  assume x y;
  have hbridge : π (zle (zmult x y) Int0 ⇔ zle Int0 (zmult x (zminus y)))
    { rewrite (zmult_zminus_right x y);
      apply ∧ᵢ
      { assume h;
        refine ∧ₑ₂ (zle_zminus Int0 (zmult x y))
          (ind_eq zminus_0 (λ v, zle (zmult x y) v) h) }
      { assume h;
        refine ind_eq (eq_sym zminus_0) (λ v, zle (zmult x y) v)
          (∧ₑ₁ (zle_zminus Int0 (zmult x y)) h) } };
  have hmul : π (zle Int0 (zmult x (zminus y)) ⇔
                 ((zle Int0 x ∧ zle Int0 (zminus y)) ∨
                  (zle x Int0 ∧ zle (zminus y) Int0)))
    { refine int_0_le_mult_iff x (zminus y) };
  have hCy : π (zle Int0 (zminus y) ⇔ zle y Int0)
    { apply ∧ᵢ
      { assume h; refine ind_eq (eq_sym zminus_0) (λ v, zle y v)
          (∧ₑ₁ (zle_zminus Int0 y) h) }
      { assume h; refine ∧ₑ₂ (zle_zminus Int0 y)
          (ind_eq zminus_0 (λ v, zle y v) h) } };
  have hDy : π (zle (zminus y) Int0 ⇔ zle Int0 y)
    { apply ∧ᵢ
      { assume h;
        have h2 : π (zle (zminus y) (zminus Int0))
          { refine ind_eq zminus_0 (λ v, zle (zminus y) v) h };
        refine ∧ₑ₁ (zminus_zle_zminus y Int0) h2 }
      { assume h;
        have h2 : π (zle (zminus y) (zminus Int0))
          { refine ∧ₑ₂ (zminus_zle_zminus y Int0) h };
        refine ind_eq (eq_sym zminus_0) (λ v, zle (zminus y) v) h2 } };
  apply ∧ᵢ
  { assume h;
    refine ∨ₑ (∧ₑ₁ hmul (∧ₑ₁ hbridge h)) _ _
    { assume hc; refine ∨ᵢ₁ (∧ᵢ (∧ₑ₁ hc) (∧ₑ₁ hCy (∧ₑ₂ hc))) }
    { assume hc; refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ hc) (∧ₑ₁ hDy (∧ₑ₂ hc))) } }
  { assume h;
    refine ∧ₑ₂ hbridge (∧ₑ₂ hmul _);
    refine ∨ₑ h _ _
    { assume hc; refine ∨ᵢ₁ (∧ᵢ (∧ₑ₁ hc) (∧ₑ₂ hCy (∧ₑ₂ hc))) }
    { assume hc; refine ∨ᵢ₂ (∧ᵢ (∧ₑ₁ hc) (∧ₑ₂ hDy (∧ₑ₂ hc))) } }
end;

// Typechecking for posDivAlg
opaque symbol posDivAlg_type (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (posDivAlg (Pair a b) ∈ Sigma int (λ _, int)) ≔
begin
  assume a b ha hb;
  refine posDivAlg_induct (λ a b, posDivAlg (Pair a b) ∈ Sigma int (λ _, int)) a b ha hb _;
  assume a2 b2 ha2 hb2 ih;
  refine ∨ₑ (em (zless Int0 b2)) _ _
  { assume hpos;
    rewrite (posDivAlg_eqn a2 b2 hpos ha2 hb2);
    refine ∨ₑ (em (zless a2 b2)) _ _
    { assume hlt;
      rewrite (If_P (zless a2 b2) _ _ hlt);
      refine SigmaI Int0 a2 int (λ _, int) Int0_in_int ha2 }
    { assume hnlt;
      rewrite (If_not_P (zless a2 b2) _ _ hnlt);
      have hncond : π (¬ (zless a2 b2 ∨ zle b2 Int0))
        { assume hd; refine ∨ₑ hd _ _
          { assume h; refine hnlt h }
          { assume h; refine (∧ₑ₂ (not_zle_iff_zless b2 Int0) hpos) h } };
      refine adjust_type b2 (posDivAlg (Pair a2 (zmult Int2 b2))) (ih hncond) } }
  { assume hnpos;
    have hble : π (zle b2 Int0) { refine ∧ₑ₁ (not_zless_iff_zle Int0 b2) hnpos };
    rewrite posDivAlg_unfold;
    repeat orelse rewrite fst_conv rewrite snd_conv;
    rewrite (If_P (zless a2 b2 ∨ zle b2 Int0) _ _ (∨ᵢ₂ hble));
    refine SigmaI Int0 a2 int (λ _, int) Int0_in_int ha2 }
end;

// port-internal helper: b < 2b, given 0 < b  (measure/positivity arithmetic)
private opaque symbol b_zless_2b (b : τ ι) :
  π (zless Int0 b) → π (zless b (zmult Int2 b)) ≔
begin
  assume b hb;
  refine ∧ₑ₁ (zless_intify1 b (zmult Int2 b)) _;
  rewrite Int2_eq_add;
  rewrite (zadd_zmult_distrib Int1 Int1 b);
  rewrite zmult_1_intify;
  have hbi : π (zless Int0 (intify b)) { refine ∧ₑ₂ (zless_intify2 Int0 b) hb };
  have hstep : π (zless (zadd (intify b) Int0) (zadd (intify b) (intify b)))
    { refine zadd_zless_mono2 Int0 (intify b) (intify b) hbi };
  have heq : π (zadd (intify b) Int0 = intify b)
    { rewrite (zadd_0_right_intify (intify b)); refine intify_idem b };
  refine ind_eq (eq_sym heq) (λ v, zless v (zadd (intify b) (intify b))) hstep
end;

// port-internal helper: b $* (#2 $* q) = (#2 $* b) $* q
private opaque symbol zmult_2_shift (b q : τ ι) :
  π (zmult b (zmult Int2 q) = zmult (zmult Int2 b) q) ≔
begin
  assume b q;
  rewrite (zmult_assoc Int2 b q);
  rewrite (zmult_commute Int2 q);
  rewrite left (zmult_assoc b q Int2);
  refine zmult_commute (zmult b q) Int2
end;

// port-internal helper: #2 $* b = b $+ b, for b ∈ int
private opaque symbol two_b_eq (b : τ ι) :
  π (b ∈ int) → π (zmult Int2 b = zadd b b) ≔
begin
  assume b hb;
  rewrite Int2_eq_add;
  rewrite (zadd_zmult_distrib Int1 Int1 b);
  rewrite zmult_1_intify;
  rewrite (intify_ident b hb);
  reflexivity
end;

// port-internal helper: (mval $+ b) $+ (r $+ ($-b)) = mval $+ intify(r)
private opaque symbol adjust_arith1 (mval b r : τ ι) :
  π (zadd (zadd mval b) (zadd r (zminus b)) = zadd mval (intify r)) ≔
begin
  assume mval b r;
  rewrite (zadd_assoc mval b (zadd r (zminus b)));
  rewrite left (zadd_assoc b r (zminus b));
  rewrite (zadd_commute b r);
  rewrite (zadd_assoc r b (zminus b));
  rewrite (zadd_zminus_inverse b);
  rewrite (zadd_int0_right_intify r);
  reflexivity
end;

// port-internal helper: ($-b) $+ (a $+ b) = intify(a)  (negDivAlg base case)
private opaque symbol neg_then_arith (a b : τ ι) :
  π (zadd (zminus b) (zadd a b) = intify a) ≔
begin
  assume a b;
  rewrite (zadd_commute (zminus b) (zadd a b));
  rewrite (zadd_assoc a b (zminus b));
  rewrite (zadd_zminus_inverse b);
  rewrite (zadd_int0_right_intify a);
  reflexivity
end;

// port-internal helper: build quorem for b>0 from the three facts.
private opaque symbol quorem_posI (a b q r : τ ι) :
  π (a = zadd (zmult b q) r) → π (zless Int0 b) →
  π (zle Int0 r) → π (zless r b) →
  π (quorem (Pair a b) (Pair q r)) ≔
begin
  assume a b q r heq hpos hr0 hrb;
  rewrite quorem_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∧ᵢ heq (∨ᵢ₁ (∧ᵢ hpos (∧ᵢ hr0 hrb)))
end;

// port-internal helper: extract the three facts from quorem for b>0.
private opaque symbol quorem_posE (a b qr : τ ι) :
  π (quorem (Pair a b) qr) → π (zless Int0 b) →
  π (a = zadd (zmult b (fst qr)) (snd qr)
     ∧ zle Int0 (snd qr) ∧ zless (snd qr) b) ≔
begin
  assume a b qr hq hpos;
  have hu : π (fst (Pair a b) = zadd (zmult (snd (Pair a b)) (fst qr)) (snd qr) ∧
    ((zless Int0 (snd (Pair a b)) ∧ zle Int0 (snd qr) ∧ zless (snd qr) (snd (Pair a b))) ∨
     (¬ (zless Int0 (snd (Pair a b))) ∧ zless (snd (Pair a b)) (snd qr) ∧ zle (snd qr) Int0)))
    { refine ind_eq (eq_sym (quorem_def (Pair a b) qr)) (λ p, p) hq };
  have hu_s : π (fst (Pair a b) = zadd (zmult b (fst qr)) (snd qr) ∧
    ((zless Int0 b ∧ zle Int0 (snd qr) ∧ zless (snd qr) b) ∨
     (¬ (zless Int0 b) ∧ zless b (snd qr) ∧ zle (snd qr) Int0)))
    { refine ind_eq (eq_sym (snd_conv a b))
        (λ w, fst (Pair a b) = zadd (zmult w (fst qr)) (snd qr) ∧
          ((zless Int0 w ∧ zle Int0 (snd qr) ∧ zless (snd qr) w) ∨
           (¬ (zless Int0 w) ∧ zless w (snd qr) ∧ zle (snd qr) Int0))) hu };
  have hu2 : π (a = zadd (zmult b (fst qr)) (snd qr) ∧
    ((zless Int0 b ∧ zle Int0 (snd qr) ∧ zless (snd qr) b) ∨
     (¬ (zless Int0 b) ∧ zless b (snd qr) ∧ zle (snd qr) Int0)))
    { refine ind_eq (eq_sym (fst_conv a b))
        (λ w, w = zadd (zmult b (fst qr)) (snd qr) ∧
          ((zless Int0 b ∧ zle Int0 (snd qr) ∧ zless (snd qr) b) ∨
           (¬ (zless Int0 b) ∧ zless b (snd qr) ∧ zle (snd qr) Int0))) hu_s };
  refine ∨ₑ (∧ₑ₂ hu2) _ _
  { assume hc; refine ∧ᵢ (∧ₑ₁ hu2) (∧ᵢ (∧ₑ₁ (∧ₑ₂ hc)) (∧ₑ₂ (∧ₑ₂ hc))) }
  { assume hc; refine ⊥ₑ (∧ₑ₁ hc hpos) }
end;

// Correctness of posDivAlg: it computes quotients correctly
opaque symbol posDivAlg_correct (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle Int0 a) → π (zless Int0 b) →
  π (quorem (Pair a b) (posDivAlg (Pair a b))) ≔
begin
  assume a b ha hb hle hlt;
  refine posDivAlg_induct
    (λ a b, zle Int0 a ⇒ zless Int0 b ⇒ quorem (Pair a b) (posDivAlg (Pair a b)))
    a b ha hb _ hle hlt;
  assume a2 b2 ha2 hb2 ih hle2 hlt2;
  rewrite (posDivAlg_eqn a2 b2 hlt2 ha2 hb2);
  refine ∨ₑ (em (zless a2 b2)) _ _
  { assume hlt_ab;
    rewrite (If_P (zless a2 b2) _ _ hlt_ab);
    refine quorem_posI a2 b2 Int0 a2 _ hlt2 hle2 hlt_ab;
    rewrite (zmult_0_right b2);
    rewrite (zadd_0_intify a2);
    refine eq_sym (intify_ident a2 ha2) }
  { assume hnlt_ab;
    rewrite (If_not_P (zless a2 b2) _ _ hnlt_ab);
    have hncond : π (¬ (zless a2 b2 ∨ zle b2 Int0))
      { assume hd; refine ∨ₑ hd _ _
        { assume h; refine hnlt_ab h }
        { assume h; refine (∧ₑ₂ (not_zle_iff_zless b2 Int0) hlt2) h } };
    have h2b2 : π (zless Int0 (zmult Int2 b2))
      { refine zless_trans Int0 b2 (zmult Int2 b2) hlt2 (b_zless_2b b2 hlt2) };
    have hqr : π (quorem (Pair a2 (zmult Int2 b2)) (posDivAlg (Pair a2 (zmult Int2 b2))))
      { refine ih hncond hle2 h2b2 };
    have htype : π (posDivAlg (Pair a2 (zmult Int2 b2)) ∈ Sigma int (λ _, int))
      { refine posDivAlg_type a2 (zmult Int2 b2) ha2 (zmult_type Int2 b2) };
    have hsnd : π (snd (posDivAlg (Pair a2 (zmult Int2 b2))) ∈ int)
      { refine SigmaD2 (posDivAlg (Pair a2 (zmult Int2 b2))) int (λ _, int) htype };
    have hqrE : π (a2 = zadd (zmult (zmult Int2 b2)
          (fst (posDivAlg (Pair a2 (zmult Int2 b2)))))
          (snd (posDivAlg (Pair a2 (zmult Int2 b2))))
        ∧ zle Int0 (snd (posDivAlg (Pair a2 (zmult Int2 b2))))
        ∧ zless (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) (zmult Int2 b2))
      { refine quorem_posE a2 (zmult Int2 b2) (posDivAlg (Pair a2 (zmult Int2 b2))) hqr h2b2 };
    have heqa : π (a2 = zadd (zmult (zmult Int2 b2)
          (fst (posDivAlg (Pair a2 (zmult Int2 b2)))))
          (snd (posDivAlg (Pair a2 (zmult Int2 b2))))) { refine ∧ₑ₁ hqrE };
    have hr0 : π (zle Int0 (snd (posDivAlg (Pair a2 (zmult Int2 b2))))) { refine ∧ₑ₁ (∧ₑ₂ hqrE) };
    have hrb2 : π (zless (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) (zmult Int2 b2))
      { refine ∧ₑ₂ (∧ₑ₂ hqrE) };
    rewrite (adjust_def b2 (posDivAlg (Pair a2 (zmult Int2 b2))));
    refine ∨ₑ (em (zle Int0 (zdiff (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2))) _ _
    { assume hle_rb;
      rewrite (If_P (zle Int0 (zdiff (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2)) _ _ hle_rb);
      refine quorem_posI a2 b2
        (zadd (zmult Int2 (fst (posDivAlg (Pair a2 (zmult Int2 b2))))) Int1)
        (zdiff (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2) _ hlt2 hle_rb _
      { rewrite (zadd_zmult_distrib2 b2 (zmult Int2 (fst (posDivAlg (Pair a2 (zmult Int2 b2))))) Int1);
        rewrite (zmult_1_right_intify b2);
        rewrite (intify_ident b2 hb2);
        rewrite (zmult_2_shift b2 (fst (posDivAlg (Pair a2 (zmult Int2 b2)))));
        rewrite (zdiff_def (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2);
        rewrite (adjust_arith1 (zmult (zmult Int2 b2) (fst (posDivAlg (Pair a2 (zmult Int2 b2)))))
                   b2 (snd (posDivAlg (Pair a2 (zmult Int2 b2)))));
        rewrite (intify_ident (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) hsnd);
        refine heqa }
      { refine ∧ₑ₂ (zdiff_zless_iff (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2 b2)
          (ind_eq (eq_sym (two_b_eq b2 hb2))
            (λ w, zless (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) w) hrb2) } }
    { assume hnle_rb;
      rewrite (If_not_P (zle Int0 (zdiff (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2)) _ _ hnle_rb);
      refine quorem_posI a2 b2
        (zmult Int2 (fst (posDivAlg (Pair a2 (zmult Int2 b2)))))
        (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) _ hlt2 hr0 _
      { rewrite (zmult_2_shift b2 (fst (posDivAlg (Pair a2 (zmult Int2 b2)))));
        refine heqa }
      { have hlt_rb : π (zless (zdiff (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2) Int0)
          { refine ∧ₑ₁ (not_zle_iff_zless Int0
              (zdiff (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2)) hnle_rb };
        have hstep : π (zless (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) (zadd Int0 b2))
          { refine ∧ₑ₁ (zdiff_zless_iff (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2 Int0) hlt_rb };
        refine ∧ₑ₁ (zless_intify2 (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) b2)
          (ind_eq (eq_sym (zadd_0_intify b2))
            (λ w, zless (snd (posDivAlg (Pair a2 (zmult Int2 b2)))) w) hstep) } } }
end;

// ===========================================================================
// Correctness of negDivAlg, the division algorithm for a<0 and b>0
// ===========================================================================

opaque symbol negDivAlg_termination (a b : τ ι) :
  π (zless Int0 b) → π (zless (zadd a b) Int0) →
  π (lt (nat_of (zdiff (zminus a) (zmult Int2 b))) (nat_of (zdiff (zminus a) b))) ≔
begin
  assume a b hb hab;
  have hb2 : π (zless b (zmult Int2 b))
    { refine ∧ₑ₁ (zless_intify1 b (zmult Int2 b)) _;
      rewrite Int2_eq_add;
      rewrite (zadd_zmult_distrib Int1 Int1 b);
      rewrite zmult_1_intify;
      have hbi : π (zless Int0 (intify b)) { refine ∧ₑ₂ (zless_intify2 Int0 b) hb };
      have hstep : π (zless (zadd (intify b) Int0) (zadd (intify b) (intify b)))
        { refine zadd_zless_mono2 Int0 (intify b) (intify b) hbi };
      have heq : π (zadd (intify b) Int0 = intify b)
        { rewrite (zadd_0_right_intify (intify b)); refine intify_idem b };
      refine ind_eq (eq_sym heq) (λ v, zless v (zadd (intify b) (intify b))) hstep };
  refine ∧ₑ₂ (zless_nat_conj (zdiff (zminus a) (zmult Int2 b)) (zdiff (zminus a) b)) _;
  refine ∧ᵢ _ _
  { refine ind_eq int_of_0 (λ u, zless u (zdiff (zminus a) b)) _;
    rewrite (zdiff_def (zminus a) b);
    rewrite left (zminus_zadd_distrib a b);
    refine ∧ₑ₂ (zless_zminus Int0 (zadd a b)) _;
    rewrite zminus_0;
    refine hab }
  { rewrite (zdiff_def (zminus a) (zmult Int2 b));
    rewrite (zdiff_def (zminus a) b);
    refine zadd_zless_mono2 (zminus (zmult Int2 b)) (zminus b) (zminus a) _;
    refine ∧ₑ₂ (zminus_zless_zminus (zmult Int2 b) b) hb2 }
end;

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
begin
  assume ab;
  rewrite negDivAlg_def;
  rewrite (wfrec_eq
    (measure (Sigma int (λ _, int))
       (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
    ab
    (λ ab2 f,
       If (zle Int0 (zadd (fst ab2) (snd ab2)) ∨ zle (snd ab2) Int0)
          (Pair NegInt1 (zadd (fst ab2) (snd ab2)))
          (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2))))))
    (wf_measure (Sigma int (λ _, int))
       (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))));
  simplify rule off;
  have hlam :
    π (Lambda (vimage_singleton
                 (measure (Sigma int (λ _, int))
                    (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))) ab)
         (λ x, wfrec
                 (measure (Sigma int (λ _, int))
                    (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
                 x
                 (λ ab2 f,
                    If (zle Int0 (zadd (fst ab2) (snd ab2)) ∨ zle (snd ab2) Int0)
                       (Pair NegInt1 (zadd (fst ab2) (snd ab2)))
                       (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2)))))))
       = Lambda (vimage_singleton
                   (measure (Sigma int (λ _, int))
                      (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))) ab)
           (λ x, negDivAlg x))
    { refine lam_cong
        (vimage_singleton
           (measure (Sigma int (λ _, int))
              (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))) ab)
        (vimage_singleton
           (measure (Sigma int (λ _, int))
              (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))) ab)
        (λ x, wfrec
                (measure (Sigma int (λ _, int))
                   (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
                x
                (λ ab2 f,
                   If (zle Int0 (zadd (fst ab2) (snd ab2)) ∨ zle (snd ab2) Int0)
                      (Pair NegInt1 (zadd (fst ab2) (snd ab2)))
                      (adjust (snd ab2) (fapply f (Pair (fst ab2) (zmult Int2 (snd ab2)))))))
        (λ x, negDivAlg x)
        (eq_refl _) _;
      assume x hx;
      rewrite negDivAlg_def;
      reflexivity };
  rewrite hlam;
  reflexivity
end;

opaque symbol negDivAlg_eqn (a b : τ ι) :
  π (zless Int0 b) → π (a ∈ int) → π (b ∈ int) →
  π (negDivAlg (Pair a b) =
     If (zle Int0 (zadd a b)) (Pair NegInt1 (zadd a b))
        (adjust b (negDivAlg (Pair a (zmult Int2 b))))) ≔
begin
  assume a b hb ha hb_int;
  rewrite negDivAlg_unfold;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∨ₑ (em (zle Int0 (zadd a b))) _ _
  { assume h1;
    rewrite (If_P (zle Int0 (zadd a b) ∨ zle b Int0) _ _ (∨ᵢ₁ h1));
    rewrite (If_P (zle Int0 (zadd a b)) _ _ h1);
    reflexivity }
  { assume h2;
    have hncond : π (¬ (zle Int0 (zadd a b) ∨ zle b Int0))
      { assume hd; refine ∨ₑ hd _ _
        { assume hh; refine h2 hh }
        { assume hh; refine (∧ₑ₂ (not_zle_iff_zless b Int0) hb) hh } };
    rewrite (If_not_P (zle Int0 (zadd a b) ∨ zle b Int0) _ _ hncond);
    rewrite (If_not_P (zle Int0 (zadd a b)) _ _ h2);
    have hmem : π (Pair a (zmult Int2 b) ∈
        vimage_singleton
          (measure (Sigma int (λ _, int)) (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
          (Pair a b))
      { refine vimage_singletonI (Pair a (zmult Int2 b)) (Pair a b)
          (measure (Sigma int (λ _, int)) (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))) _;
        refine ∧ₑ₂ (measure_iff (Sigma int (λ _, int))
          (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))
          (Pair a (zmult Int2 b)) (Pair a b)) _;
        refine ∧ᵢ (SigmaI a (zmult Int2 b) int (λ _, int) ha (zmult_type Int2 b))
              (∧ᵢ (SigmaI a b int (λ _, int) ha hb_int) _);
        repeat orelse rewrite fst_conv rewrite snd_conv;
        refine negDivAlg_termination a b hb
          (∧ₑ₁ (not_zle_iff_zless Int0 (zadd a b)) h2) };
    have hbeta : π (fapply (Lambda
          (vimage_singleton
            (measure (Sigma int (λ _, int)) (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
            (Pair a b))
          (λ x, negDivAlg x)) (Pair a (zmult Int2 b))
        = negDivAlg (Pair a (zmult Int2 b)))
      { refine beta
          (vimage_singleton
            (measure (Sigma int (λ _, int)) (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
            (Pair a b))
          (λ x, negDivAlg x) (Pair a (zmult Int2 b)) hmem };
    rewrite hbeta;
    reflexivity }
end;

opaque symbol negDivAlg_induct_lemma (P : τ ι → Prop) (u v : τ ι) :
  (Π (a b : τ ι), π (a ∈ int) → π (b ∈ int) →
    π (¬ (zle Int0 (zadd a b) ∨ zle b Int0) ⇒ P (Pair a (zmult Int2 b))) →
    π (P (Pair a b))) →
  π (Pair u v ∈ Sigma int (λ _, int)) →
  π (P (Pair u v)) ≔
begin
  assume P u v prem huv;
  refine wf_global_induct
    (measure (Sigma int (λ _, int)) (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
    (λ z, z ∈ Sigma int (λ _, int) ⇒ P z)
    (Pair u v)
    (wf_measure (Sigma int (λ _, int)) (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
    _
    huv;
  assume x hpred hxA;
  have hfx : π (fst x ∈ int) { refine SigmaD1 x int (λ _, int) hxA };
  have hsx : π (snd x ∈ int) { refine SigmaD2 x int (λ _, int) hxA };
  have hxeq : π (Pair (fst x) (snd x) = x) { refine Pair_fst_snd x int (λ _, int) hxA };
  refine ind_eq (eq_sym hxeq) (λ w, P w) _;
  refine prem (fst x) (snd x) hfx hsx _;
  assume hcond;
  have hnle_add : π (¬ zle Int0 (zadd (fst x) (snd x)))
    { assume h; refine hcond (∨ᵢ₁ h) };
  have hnle_b : π (¬ zle (snd x) Int0) { assume h; refine hcond (∨ᵢ₂ h) };
  have hab' : π (zless (zadd (fst x) (snd x)) Int0)
    { refine ∧ₑ₁ (not_zle_iff_zless Int0 (zadd (fst x) (snd x))) hnle_add };
  have hb' : π (zless Int0 (snd x)) { refine ∧ₑ₁ (not_zle_iff_zless (snd x) Int0) hnle_b };
  have hyA : π (Pair (fst x) (zmult Int2 (snd x)) ∈ Sigma int (λ _, int))
    { refine SigmaI (fst x) (zmult Int2 (snd x)) int (λ _, int) hfx (zmult_type Int2 (snd x)) };
  have hyr : π (Pair (Pair (fst x) (zmult Int2 (snd x))) x ∈
      measure (Sigma int (λ _, int)) (λ p, nat_of (zdiff (zminus (fst p)) (snd p))))
    { refine ∧ₑ₂ (measure_iff (Sigma int (λ _, int))
        (λ p, nat_of (zdiff (zminus (fst p)) (snd p)))
        (Pair (fst x) (zmult Int2 (snd x))) x) _;
      refine ∧ᵢ hyA (∧ᵢ hxA _);
      repeat orelse rewrite fst_conv rewrite snd_conv;
      refine negDivAlg_termination (fst x) (snd x) hb' hab' };
  refine hpred (Pair (fst x) (zmult Int2 (snd x))) hyr hyA
end;

opaque symbol negDivAlg_induct (P : τ ι → τ ι → Prop) (u v : τ ι) :
  π (u ∈ int) → π (v ∈ int) →
  (Π (a b : τ ι), π (a ∈ int) → π (b ∈ int) →
    π (¬ (zle Int0 (zadd a b) ∨ zle b Int0) ⇒ P a (zmult Int2 b)) →
    π (P a b)) →
  π (P u v) ≔
begin
  assume P u v hu hv ih;
  have huv : π (Pair u v ∈ Sigma int (λ _, int))
    { refine SigmaI u v int (λ _, int) hu hv };
  have hmain : π (P (fst (Pair u v)) (snd (Pair u v)))
    { refine negDivAlg_induct_lemma (λ z, P (fst z) (snd z)) u v _ huv;
      assume a b ha hb himp;
      have hres : π (P a b)
        { refine ih a b ha hb _;
          assume hcond;
          have hh : π (P (fst (Pair a (zmult Int2 b))) (snd (Pair a (zmult Int2 b))))
            { refine himp hcond };
          have h1 : π (P a (snd (Pair a (zmult Int2 b))))
            { refine ind_eq (eq_sym (fst_conv a (zmult Int2 b)))
                (λ w, P w (snd (Pair a (zmult Int2 b)))) hh };
          refine ind_eq (eq_sym (snd_conv a (zmult Int2 b))) (λ w, P a w) h1 };
      have hf : π (P (fst (Pair a b)) b)
        { refine ind_eq (fst_conv a b) (λ w, P w b) hres };
      refine ind_eq (snd_conv a b) (λ w, P (fst (Pair a b)) w) hf };
  have hm1 : π (P u (snd (Pair u v)))
    { refine ind_eq (eq_sym (fst_conv u v)) (λ w, P w (snd (Pair u v))) hmain };
  refine ind_eq (eq_sym (snd_conv u v)) (λ w, P u w) hm1
end;

// Typechecking for negDivAlg
opaque symbol negDivAlg_type (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (negDivAlg (Pair a b) ∈ Sigma int (λ _, int)) ≔
begin
  assume a b ha hb;
  refine negDivAlg_induct (λ a b, negDivAlg (Pair a b) ∈ Sigma int (λ _, int)) a b ha hb _;
  assume a2 b2 ha2 hb2 ih;
  refine ∨ₑ (em (zless Int0 b2)) _ _
  { assume hpos;
    rewrite (negDivAlg_eqn a2 b2 hpos ha2 hb2);
    refine ∨ₑ (em (zle Int0 (zadd a2 b2))) _ _
    { assume hle;
      rewrite (If_P (zle Int0 (zadd a2 b2)) _ _ hle);
      refine SigmaI NegInt1 (zadd a2 b2) int (λ _, int) NegInt1_in_int (zadd_type a2 b2) }
    { assume hnle;
      rewrite (If_not_P (zle Int0 (zadd a2 b2)) _ _ hnle);
      have hncond : π (¬ (zle Int0 (zadd a2 b2) ∨ zle b2 Int0))
        { assume hd; refine ∨ₑ hd _ _
          { assume h; refine hnle h }
          { assume h; refine (∧ₑ₂ (not_zle_iff_zless b2 Int0) hpos) h } };
      refine adjust_type b2 (negDivAlg (Pair a2 (zmult Int2 b2))) (ih hncond) } }
  { assume hnpos;
    have hble : π (zle b2 Int0) { refine ∧ₑ₁ (not_zless_iff_zle Int0 b2) hnpos };
    rewrite negDivAlg_unfold;
    repeat orelse rewrite fst_conv rewrite snd_conv;
    rewrite (If_P (zle Int0 (zadd a2 b2) ∨ zle b2 Int0) _ _ (∨ᵢ₂ hble));
    refine SigmaI NegInt1 (zadd a2 b2) int (λ _, int) NegInt1_in_int (zadd_type a2 b2) }
end;

// Correctness of negDivAlg: it computes quotients correctly.
// It doesn't work if a=0 because 0/b=0 rather than -1
opaque symbol negDivAlg_correct (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zless a Int0) → π (zless Int0 b) →
  π (quorem (Pair a b) (negDivAlg (Pair a b))) ≔
begin
  assume a b ha hb hlta hlt;
  refine negDivAlg_induct
    (λ a b, zless a Int0 ⇒ zless Int0 b ⇒ quorem (Pair a b) (negDivAlg (Pair a b)))
    a b ha hb _ hlta hlt;
  assume a2 b2 ha2 hb2 ih hlta2 hlt2;
  rewrite (negDivAlg_eqn a2 b2 hlt2 ha2 hb2);
  refine ∨ₑ (em (zle Int0 (zadd a2 b2))) _ _
  { assume hle_ab;
    rewrite (If_P (zle Int0 (zadd a2 b2)) _ _ hle_ab);
    refine quorem_posI a2 b2 NegInt1 (zadd a2 b2) _ hlt2 hle_ab _
    { rewrite (zmult_minus1_right b2);
      rewrite (neg_then_arith a2 b2);
      refine eq_sym (intify_ident a2 ha2) }
    { have hstep : π (zless (zadd a2 b2) (zadd Int0 b2))
        { refine zadd_zless_mono1 a2 Int0 b2 hlta2 };
      refine ∧ₑ₁ (zless_intify2 (zadd a2 b2) b2)
        (ind_eq (eq_sym (zadd_0_intify b2)) (λ w, zless (zadd a2 b2) w) hstep) } }
  { assume hnle_ab;
    rewrite (If_not_P (zle Int0 (zadd a2 b2)) _ _ hnle_ab);
    have hncond : π (¬ (zle Int0 (zadd a2 b2) ∨ zle b2 Int0))
      { assume hd; refine ∨ₑ hd _ _
        { assume h; refine hnle_ab h }
        { assume h; refine (∧ₑ₂ (not_zle_iff_zless b2 Int0) hlt2) h } };
    have h2b2 : π (zless Int0 (zmult Int2 b2))
      { refine zless_trans Int0 b2 (zmult Int2 b2) hlt2 (b_zless_2b b2 hlt2) };
    have hqr : π (quorem (Pair a2 (zmult Int2 b2)) (negDivAlg (Pair a2 (zmult Int2 b2))))
      { refine ih hncond hlta2 h2b2 };
    have htype : π (negDivAlg (Pair a2 (zmult Int2 b2)) ∈ Sigma int (λ _, int))
      { refine negDivAlg_type a2 (zmult Int2 b2) ha2 (zmult_type Int2 b2) };
    have hsnd : π (snd (negDivAlg (Pair a2 (zmult Int2 b2))) ∈ int)
      { refine SigmaD2 (negDivAlg (Pair a2 (zmult Int2 b2))) int (λ _, int) htype };
    have hqrE : π (a2 = zadd (zmult (zmult Int2 b2)
          (fst (negDivAlg (Pair a2 (zmult Int2 b2)))))
          (snd (negDivAlg (Pair a2 (zmult Int2 b2))))
        ∧ zle Int0 (snd (negDivAlg (Pair a2 (zmult Int2 b2))))
        ∧ zless (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) (zmult Int2 b2))
      { refine quorem_posE a2 (zmult Int2 b2) (negDivAlg (Pair a2 (zmult Int2 b2))) hqr h2b2 };
    have heqa : π (a2 = zadd (zmult (zmult Int2 b2)
          (fst (negDivAlg (Pair a2 (zmult Int2 b2)))))
          (snd (negDivAlg (Pair a2 (zmult Int2 b2))))) { refine ∧ₑ₁ hqrE };
    have hr0 : π (zle Int0 (snd (negDivAlg (Pair a2 (zmult Int2 b2))))) { refine ∧ₑ₁ (∧ₑ₂ hqrE) };
    have hrb2 : π (zless (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) (zmult Int2 b2))
      { refine ∧ₑ₂ (∧ₑ₂ hqrE) };
    rewrite (adjust_def b2 (negDivAlg (Pair a2 (zmult Int2 b2))));
    refine ∨ₑ (em (zle Int0 (zdiff (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2))) _ _
    { assume hle_rb;
      rewrite (If_P (zle Int0 (zdiff (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2)) _ _ hle_rb);
      refine quorem_posI a2 b2
        (zadd (zmult Int2 (fst (negDivAlg (Pair a2 (zmult Int2 b2))))) Int1)
        (zdiff (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2) _ hlt2 hle_rb _
      { rewrite (zadd_zmult_distrib2 b2 (zmult Int2 (fst (negDivAlg (Pair a2 (zmult Int2 b2))))) Int1);
        rewrite (zmult_1_right_intify b2);
        rewrite (intify_ident b2 hb2);
        rewrite (zmult_2_shift b2 (fst (negDivAlg (Pair a2 (zmult Int2 b2)))));
        rewrite (zdiff_def (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2);
        rewrite (adjust_arith1 (zmult (zmult Int2 b2) (fst (negDivAlg (Pair a2 (zmult Int2 b2)))))
                   b2 (snd (negDivAlg (Pair a2 (zmult Int2 b2)))));
        rewrite (intify_ident (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) hsnd);
        refine heqa }
      { refine ∧ₑ₂ (zdiff_zless_iff (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2 b2)
          (ind_eq (eq_sym (two_b_eq b2 hb2))
            (λ w, zless (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) w) hrb2) } }
    { assume hnle_rb;
      rewrite (If_not_P (zle Int0 (zdiff (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2)) _ _ hnle_rb);
      refine quorem_posI a2 b2
        (zmult Int2 (fst (negDivAlg (Pair a2 (zmult Int2 b2)))))
        (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) _ hlt2 hr0 _
      { rewrite (zmult_2_shift b2 (fst (negDivAlg (Pair a2 (zmult Int2 b2)))));
        refine heqa }
      { have hlt_rb : π (zless (zdiff (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2) Int0)
          { refine ∧ₑ₁ (not_zle_iff_zless Int0
              (zdiff (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2)) hnle_rb };
        have hstep : π (zless (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) (zadd Int0 b2))
          { refine ∧ₑ₁ (zdiff_zless_iff (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2 Int0) hlt_rb };
        refine ∧ₑ₁ (zless_intify2 (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) b2)
          (ind_eq (eq_sym (zadd_0_intify b2))
            (λ w, zless (snd (negDivAlg (Pair a2 (zmult Int2 b2)))) w) hstep) } } }
end;

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
begin
  assume b h;
  have h1 : π (zless (zadd NegInt1 b) Int0)
    { refine ∧ₑ₁ (not_zle_iff_zless Int0 (zadd NegInt1 b)) h };
  have h2 : π (zless (zadd b NegInt1) Int0)
    { refine ind_eq (eq_sym (zadd_commute NegInt1 b)) (λ v, zless v Int0) h1 };
  have h3 : π (zless (zdiff b Int1) Int0)
    { rewrite (zdiff_def b Int1);
      rewrite left NegInt1_eq_zminus_Int1;
      refine h2 };
  have h4 : π (zless b (zadd Int0 Int1))
    { refine ∧ₑ₁ (zdiff_zless_iff b Int1 Int0) h3 };
  refine ∧ₑ₁ (zless_add1_iff_zle b Int0) h4
end;

opaque symbol negDivAlg_minus1 (b : τ ι) :
  π (negDivAlg (Pair NegInt1 b) = Pair NegInt1 (zdiff b Int1)) ≔
begin
  assume b;
  rewrite negDivAlg_unfold;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  have hcond : π (zle Int0 (zadd NegInt1 b) ∨ zle b Int0)
    { refine ∨ₑ (em (zle Int0 (zadd NegInt1 b))) _ _
      { assume h; refine ∨ᵢ₁ h }
      { assume h; refine ∨ᵢ₂ (linear_arith_lemma b h) } };
  rewrite (If_P (zle Int0 (zadd NegInt1 b) ∨ zle b Int0) _ _ hcond);
  have heq : π (zadd NegInt1 b = zdiff b Int1)
    { rewrite NegInt1_eq_zminus_Int1;
      rewrite (zdiff_def b Int1);
      refine zadd_commute (zminus Int1) b };
  rewrite heq;
  reflexivity
end;

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

// port-internal helper: negate the quorem equation.
private opaque symbol quorem_neg_eq (a b q r : τ ι) :
  π (a ∈ int) →
  π (zminus a = zadd (zmult (zminus b) q) r) →
  π (a = zadd (zmult b q) (zminus r)) ≔
begin
  assume a b q r ha heq;
  have h1 : π (zminus (zminus a) = zminus (zadd (zmult (zminus b) q) r))
    { rewrite heq; reflexivity };
  have h2 : π (a = zminus (zadd (zmult (zminus b) q) r))
    { rewrite left (zminus_zminus a ha); refine h1 };
  rewrite h2;
  rewrite (zminus_zadd_distrib (zmult (zminus b) q) r);
  rewrite (zmult_zminus b q);
  rewrite (zminus_zminus_intify (zmult b q));
  rewrite (intify_ident (zmult b q) (zmult_type b q));
  reflexivity
end;

opaque symbol quorem_neg (a b qr : τ ι) :
  π (quorem (Pair (zminus a) (zminus b)) qr) → π (a ∈ int) → π (b ∈ int) →
  π (qr ∈ Sigma int (λ _, int)) →
  π (quorem (Pair a b) (negateSnd qr)) ≔
begin
  assume a b qr hq ha hb hqr;
  have hE : π (zminus a = zadd (zmult (zminus b) (fst qr)) (snd qr)
     ∧ ((zless Int0 (zminus b) ∧ zle Int0 (snd qr) ∧ zless (snd qr) (zminus b))
        ∨ (¬ (zless Int0 (zminus b)) ∧ zless (zminus b) (snd qr) ∧ zle (snd qr) Int0)))
    { refine quoremE (zminus a) (zminus b) qr hq };
  rewrite (negateSnd_def qr);
  refine quoremI a b (fst qr) (zminus (snd qr)) _ _
  { refine quorem_neg_eq a b (fst qr) (snd qr) ha (∧ₑ₁ hE) }
  { refine ∨ₑ (∧ₑ₂ hE) _ _
    { assume hc;
      have hc1 : π (zless Int0 (zminus b)) { refine ∧ₑ₁ hc };
      have hc2 : π (zle Int0 (snd qr)) { refine ∧ₑ₁ (∧ₑ₂ hc) };
      have hc3 : π (zless (snd qr) (zminus b)) { refine ∧ₑ₂ (∧ₑ₂ hc) };
      have hbneg : π (zless b Int0)
        { refine ind_eq (eq_sym zminus_0) (λ w, zless b w)
            (∧ₑ₁ (zless_zminus Int0 b) hc1) };
      refine ∨ᵢ₂ (∧ᵢ (zless_not_sym b Int0 hbneg)
        (∧ᵢ (∧ₑ₂ (zless_zminus b (snd qr)) hc3)
            (∧ₑ₂ (zminus_zle (snd qr) Int0)
              (ind_eq zminus_0 (λ w, zle w (snd qr)) hc2)))) }
    { assume hc;
      have hc2 : π (zless (zminus b) (snd qr)) { refine ∧ₑ₁ (∧ₑ₂ hc) };
      have hc3 : π (zle (snd qr) Int0) { refine ∧ₑ₂ (∧ₑ₂ hc) };
      have hbpos : π (zless Int0 b)
        { refine ind_eq (eq_sym zminus_0) (λ w, zless w b)
            (∧ₑ₁ (zminus_zless b Int0)
              (zless_zle_trans (zminus b) (snd qr) Int0 hc2 hc3)) };
      refine ∨ᵢ₁ (∧ᵢ hbpos
        (∧ᵢ (∧ₑ₂ (zle_zminus Int0 (snd qr))
              (ind_eq zminus_0 (λ w, zle (snd qr) w) hc3))
            (∧ₑ₂ (zminus_zless (snd qr) b) hc2))) } }
end;

// port-internal helper: 0≤b and b≠0 imply 0<b
private opaque symbol pos_of_zle_neq (b : τ ι) :
  π (b ∈ int) → π (b ≠ Int0) → π (zle Int0 b) → π (zless Int0 b) ≔
begin
  assume b hb hne hle;
  refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hne) _ _
  { assume hlt;
    have hbad : π (zless Int0 Int0) { refine zle_zless_trans Int0 b Int0 hle hlt };
    refine ⊥ₑ (zless_not_sym Int0 Int0 hbad hbad) }
  { assume h; refine h }
end;

opaque symbol divAlg_correct (a b : τ ι) :
  π (b ≠ Int0) → π (a ∈ int) → π (b ∈ int) →
  π (quorem (Pair a b) (divAlg (Pair a b))) ≔
begin
  assume a b hb0 ha hb;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  refine ∨ₑ (em (zle Int0 a)) _ _
  { assume h1;
    rewrite (If_P (zle Int0 a) _ _ h1);
    refine ∨ₑ (em (zle Int0 b)) _ _
    { assume h2;
      rewrite (If_P (zle Int0 b) _ _ h2);
      refine posDivAlg_correct a b ha hb h1 (pos_of_zle_neq b hb hb0 h2) }
    { assume h2;
      rewrite (If_not_P (zle Int0 b) _ _ h2);
      have hnegb : π (zless b Int0) { refine ∧ₑ₁ (not_zle_iff_zless Int0 b) h2 };
      refine ∨ₑ (em (a = Int0)) _ _
      { assume h3;
        rewrite (If_P (a = Int0) _ _ h3);
        rewrite h3;
        refine quorem_0 b hb0 hb }
      { assume h3;
        rewrite (If_not_P (a = Int0) _ _ h3);
        have hposa : π (zless Int0 a) { refine pos_of_zle_neq a ha h3 h1 };
        have hma : π (zless (zminus a) Int0)
          { refine ∧ₑ₂ (zminus_zless a Int0)
              (ind_eq zminus_0 (λ w, zless w a) hposa) };
        have hmb : π (zless Int0 (zminus b))
          { refine ∧ₑ₂ (zless_zminus Int0 b)
              (ind_eq zminus_0 (λ w, zless b w) hnegb) };
        refine quorem_neg a b (negDivAlg (Pair (zminus a) (zminus b)))
          (negDivAlg_correct (zminus a) (zminus b) (zminus_type a) (zminus_type b) hma hmb)
          ha hb
          (negDivAlg_type (zminus a) (zminus b) (zminus_type a) (zminus_type b)) } } }
  { assume h1;
    rewrite (If_not_P (zle Int0 a) _ _ h1);
    have hlta : π (zless a Int0) { refine ∧ₑ₁ (not_zle_iff_zless Int0 a) h1 };
    refine ∨ₑ (em (zless Int0 b)) _ _
    { assume h2;
      rewrite (If_P (zless Int0 b) _ _ h2);
      refine negDivAlg_correct a b ha hb hlta h2 }
    { assume h2;
      rewrite (If_not_P (zless Int0 b) _ _ h2);
      have hnegb : π (zless b Int0)
        { refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) (λ x, x)
            (λ h, ⊥ₑ (h2 h)) };
      have hma : π (zle Int0 (zminus a))
        { refine ∧ₑ₂ (zle_zminus Int0 a)
            (ind_eq zminus_0 (λ w, zle a w) (zless_imp_zle a Int0 hlta)) };
      have hmb : π (zless Int0 (zminus b))
        { refine ∧ₑ₂ (zless_zminus Int0 b)
            (ind_eq zminus_0 (λ w, zless b w) hnegb) };
      refine quorem_neg a b (posDivAlg (Pair (zminus a) (zminus b)))
        (posDivAlg_correct (zminus a) (zminus b) (zminus_type a) (zminus_type b) hma hmb)
        ha hb
        (posDivAlg_type (zminus a) (zminus b) (zminus_type a) (zminus_type b)) } }
end;

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
begin
  assume a b ha hb;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0;
    rewrite hb0;
    rewrite (DIVISION_BY_ZERO_ZDIV a);
    rewrite (DIVISION_BY_ZERO_ZMOD a);
    rewrite (zmult_0_right Int0);
    rewrite (zadd_0_intify (intify a));
    rewrite (intify_idem a);
    refine eq_sym (intify_ident a ha) }
  { assume hb0;
    have hquo : π (a = zadd (zmult b (fst (divAlg (Pair a b)))) (snd (divAlg (Pair a b))))
      { refine ∧ₑ₁ (quoremE a b (divAlg (Pair a b)) (divAlg_correct a b hb0 ha hb)) };
    rewrite zdiv_def;
    rewrite zmod_def;
    rewrite (intify_ident a ha);
    rewrite (intify_ident b hb);
    refine hquo }
end;

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
begin
  assume a b hposb;
  have hposbi : π (zless Int0 (intify b)) { refine ∧ₑ₂ (zless_intify2 Int0 b) hposb };
  have hbne : π (intify b ≠ Int0)
    { assume heq;
      have h0 : π (zless Int0 Int0) { refine ind_eq (eq_sym heq) (λ w, zless Int0 w) hposbi };
      refine zless_not_sym Int0 Int0 h0 h0 };
  have hE : π (intify a = zadd (zmult (intify b) (fst (divAlg (Pair (intify a) (intify b)))))
       (snd (divAlg (Pair (intify a) (intify b))))
     ∧ zle Int0 (snd (divAlg (Pair (intify a) (intify b))))
     ∧ zless (snd (divAlg (Pair (intify a) (intify b)))) (intify b))
    { refine quorem_posE (intify a) (intify b) (divAlg (Pair (intify a) (intify b)))
        (divAlg_correct (intify a) (intify b) hbne (intify_in_int a) (intify_in_int b)) hposbi };
  rewrite zmod_def;
  refine ∧ᵢ (∧ₑ₁ (∧ₑ₂ hE))
    (∧ₑ₁ (zless_intify2 (snd (divAlg (Pair (intify a) (intify b)))) b) (∧ₑ₂ (∧ₑ₂ hE)))
end;

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
begin
  assume a b hnegb;
  have hnegbi : π (zless (intify b) Int0) { refine ∧ₑ₂ (zless_intify1 b Int0) hnegb };
  have hbne : π (intify b ≠ Int0)
    { assume heq;
      have h0 : π (zless Int0 Int0) { refine ind_eq (eq_sym heq) (λ w, zless w Int0) hnegbi };
      refine zless_not_sym Int0 Int0 h0 h0 };
  have hE : π (intify a = zadd (zmult (intify b) (fst (divAlg (Pair (intify a) (intify b)))))
       (snd (divAlg (Pair (intify a) (intify b))))
     ∧ ((zless Int0 (intify b)
          ∧ zle Int0 (snd (divAlg (Pair (intify a) (intify b))))
          ∧ zless (snd (divAlg (Pair (intify a) (intify b)))) (intify b))
        ∨ (¬ (zless Int0 (intify b))
          ∧ zless (intify b) (snd (divAlg (Pair (intify a) (intify b))))
          ∧ zle (snd (divAlg (Pair (intify a) (intify b)))) Int0)))
    { refine quoremE (intify a) (intify b) (divAlg (Pair (intify a) (intify b)))
        (divAlg_correct (intify a) (intify b) hbne (intify_in_int a) (intify_in_int b)) };
  rewrite zmod_def;
  refine ∨ₑ (∧ₑ₂ hE) _ _
  { assume hc;
    refine ⊥ₑ (zless_not_sym (intify b) Int0 hnegbi (∧ₑ₁ hc)) }
  { assume hc;
    refine ∧ᵢ (∧ₑ₂ (∧ₑ₂ hc))
      (∧ₑ₁ (zless_intify1 b (snd (divAlg (Pair (intify a) (intify b))))) (∧ₑ₁ (∧ₑ₂ hc))) }
end;

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
begin
  assume a b hb0 ha hb;
  refine quoremI a b (zdiv a b) (zmod a b) (raw_zmod_zdiv_equality a b ha hb) _;
  refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) _ _
  { assume hlt;
    refine ∨ᵢ₂ (∧ᵢ (zless_not_sym b Int0 hlt)
      (∧ᵢ (neg_mod_bound a b hlt) (neg_mod_sign a b hlt))) }
  { assume hgt;
    refine ∨ᵢ₁ (∧ᵢ hgt (∧ᵢ (pos_mod_sign a b hgt) (pos_mod_bound a b hgt))) }
end;

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

// port-internal helpers: strict sign implies ≠ 0
private opaque symbol neq0_of_zless_pos (b : τ ι) : π (zless Int0 b) → π (b ≠ Int0) ≔
begin
  assume b h heq;
  have h0 : π (zless Int0 Int0) { refine ind_eq (eq_sym heq) (λ w, zless Int0 w) h };
  refine zless_not_sym Int0 Int0 h0 h0
end;

private opaque symbol neq0_of_zless_neg (b : τ ι) : π (zless b Int0) → π (b ≠ Int0) ≔
begin
  assume b h heq;
  have h0 : π (zless Int0 Int0) { refine ind_eq (eq_sym heq) (λ w, zless w Int0) h };
  refine zless_not_sym Int0 Int0 h0 h0
end;

opaque symbol zdiv_pos_pos_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zle Int0 a) → π (zless a b) →
  π (zdiv a b = Int0) ≔
begin
  assume a b ha hb hle hlt;
  have hposb : π (zless Int0 b) { refine zle_zless_trans Int0 a b hle hlt };
  refine quorem_div a b Int0 a _ (neq0_of_zless_pos b hposb) ha hb Int0_in_int;
  refine quorem_posI a b Int0 a _ hposb hle hlt;
  rewrite (zmult_0_right b);
  rewrite (zadd_0_intify a);
  refine eq_sym (intify_ident a ha)
end;

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
begin
  assume a b ha hb hle hlt;
  have hnegb : π (zless b Int0) { refine zless_zle_trans b a Int0 hlt hle };
  refine quorem_div a b Int0 a _ (neq0_of_zless_neg b hnegb) ha hb Int0_in_int;
  refine quoremI a b Int0 a _ _
  { rewrite (zmult_0_right b); rewrite (zadd_0_intify a); refine eq_sym (intify_ident a ha) }
  { refine ∨ᵢ₂ (∧ᵢ (zless_not_sym b Int0 hnegb) (∧ᵢ hlt hle)) }
end;

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
begin
  assume a b hle ha hb;
  have hpos : π (zless Int0 (zadd a b)) { refine zspos_add_zspos_imp_zspos a b ha hb };
  have h00 : π (zless Int0 Int0) { refine zless_zle_trans Int0 (zadd a b) Int0 hpos hle };
  refine zless_not_sym Int0 Int0 h00 h00
end;

opaque symbol zdiv_pos_neg_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zless Int0 a) → π (zle (zadd a b) Int0) →
  π (zdiv a b = NegInt1) ≔
begin
  assume a b ha hb hposa hle2;
  have hb_lt : π (zless b (zadd a b))
    { refine ∧ₑ₁ (zless_intify1 b (zadd a b))
        (ind_eq (eq_sym (zadd_0_intify b)) (λ w, zless w (zadd a b))
          (zadd_zless_mono1 Int0 a b hposa)) };
  have hnegb : π (zless b Int0) { refine zless_zle_trans b (zadd a b) Int0 hb_lt hle2 };
  refine quorem_div a b NegInt1 (zadd a b) _ (neq0_of_zless_neg b hnegb) ha hb NegInt1_in_int;
  refine quoremI a b NegInt1 (zadd a b) _ _
  { rewrite (zmult_minus1_right b); rewrite (neg_then_arith a b); refine eq_sym (intify_ident a ha) }
  { refine ∨ᵢ₂ (∧ᵢ (zless_not_sym b Int0 hnegb) (∧ᵢ hb_lt hle2)) }
end;

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
begin
  assume a b ha hb hle hlt;
  have hposb : π (zless Int0 b) { refine zle_zless_trans Int0 a b hle hlt };
  refine quorem_mod a b Int0 a _ (neq0_of_zless_pos b hposb) ha hb Int0_in_int ha;
  refine quorem_posI a b Int0 a _ hposb hle hlt;
  rewrite (zmult_0_right b); rewrite (zadd_0_intify a); refine eq_sym (intify_ident a ha)
end;

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
begin
  assume a b ha hb hle hlt;
  have hnegb : π (zless b Int0) { refine zless_zle_trans b a Int0 hlt hle };
  refine quorem_mod a b Int0 a _ (neq0_of_zless_neg b hnegb) ha hb Int0_in_int ha;
  refine quoremI a b Int0 a _ _
  { rewrite (zmult_0_right b); rewrite (zadd_0_intify a); refine eq_sym (intify_ident a ha) }
  { refine ∨ᵢ₂ (∧ᵢ (zless_not_sym b Int0 hnegb) (∧ᵢ hlt hle)) }
end;

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
begin
  assume a b ha hb hposa hle2;
  have hb_lt : π (zless b (zadd a b))
    { refine ∧ₑ₁ (zless_intify1 b (zadd a b))
        (ind_eq (eq_sym (zadd_0_intify b)) (λ w, zless w (zadd a b))
          (zadd_zless_mono1 Int0 a b hposa)) };
  have hnegb : π (zless b Int0) { refine zless_zle_trans b (zadd a b) Int0 hb_lt hle2 };
  refine quorem_mod a b NegInt1 (zadd a b) _ (neq0_of_zless_neg b hnegb) ha hb NegInt1_in_int
    (zadd_type a b);
  refine quoremI a b NegInt1 (zadd a b) _ _
  { rewrite (zmult_minus1_right b); rewrite (neg_then_arith a b); refine eq_sym (intify_ident a ha) }
  { refine ∨ᵢ₂ (∧ᵢ (zless_not_sym b Int0 hnegb) (∧ᵢ hb_lt hle2)) }
end;

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
begin
  assume a b ha hb;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0;
    rewrite hb0;
    rewrite zminus_0;
    rewrite (DIVISION_BY_ZERO_ZDIV (zminus a));
    rewrite (DIVISION_BY_ZERO_ZDIV a);
    reflexivity }
  { assume hb0;
    have hpre : π (quorem (Pair (zminus (zminus a)) (zminus (zminus b)))
        (Pair (zdiv a b) (zmod a b)))
      { rewrite (zminus_zminus a ha); rewrite (zminus_zminus b hb);
        refine quorem_div_mod a b hb0 ha hb };
    have hqn : π (quorem (Pair (zminus a) (zminus b)) (negateSnd (Pair (zdiv a b) (zmod a b))))
      { refine quorem_neg (zminus a) (zminus b) (Pair (zdiv a b) (zmod a b)) hpre
          (zminus_type a) (zminus_type b)
          (SigmaI (zdiv a b) (zmod a b) int (λ _, int) (zdiv_type a b) (zmod_type a b)) };
    have hbne_neg : π (zminus b ≠ Int0)
      { assume heq;
        refine hb0 _;
        rewrite left (zminus_zminus b hb); rewrite heq; refine zminus_0 };
    refine quorem_div (zminus a) (zminus b) (zdiv a b) (zminus (zmod a b))
      _ hbne_neg (zminus_type a) (zminus_type b) (zdiv_type a b);
    rewrite left (negateSnd_eq (zdiv a b) (zmod a b));
    refine hqn }
end;

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
begin
  assume a b ha hb;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0;
    rewrite hb0;
    rewrite zminus_0;
    rewrite (DIVISION_BY_ZERO_ZMOD (zminus a));
    rewrite (DIVISION_BY_ZERO_ZMOD a);
    rewrite (intify_ident (zminus a) (zminus_type a));
    rewrite (zminus_intify a);
    reflexivity }
  { assume hb0;
    have hpre : π (quorem (Pair (zminus (zminus a)) (zminus (zminus b)))
        (Pair (zdiv a b) (zmod a b)))
      { rewrite (zminus_zminus a ha); rewrite (zminus_zminus b hb);
        refine quorem_div_mod a b hb0 ha hb };
    have hqn : π (quorem (Pair (zminus a) (zminus b)) (negateSnd (Pair (zdiv a b) (zmod a b))))
      { refine quorem_neg (zminus a) (zminus b) (Pair (zdiv a b) (zmod a b)) hpre
          (zminus_type a) (zminus_type b)
          (SigmaI (zdiv a b) (zmod a b) int (λ _, int) (zdiv_type a b) (zmod_type a b)) };
    have hbne_neg : π (zminus b ≠ Int0)
      { assume heq;
        refine hb0 _;
        rewrite left (zminus_zminus b hb); rewrite heq; refine zminus_0 };
    refine quorem_mod (zminus a) (zminus b) (zdiv a b) (zminus (zmod a b))
      _ hbne_neg (zminus_type a) (zminus_type b) (zdiv_type a b) (zminus_type (zmod a b));
    rewrite left (negateSnd_eq (zdiv a b) (zmod a b));
    refine hqn }
end;

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
begin
  assume a r q hpos heq hlt;
  have haq_eq : π (zadd a (zminus r) = intify (zmult a q))
    { have hstep : π (zadd (zadd r (zmult a q)) (zminus r) = intify (zmult a q))
        { rewrite (zadd_commute r (zmult a q));
          rewrite (zadd_assoc (zmult a q) r (zminus r));
          rewrite (zadd_zminus_inverse r);
          refine zadd_int0_right_intify (zmult a q) };
      refine ind_eq heq (λ w, zadd w (zminus r) = intify (zmult a q)) hstep };
  have hzr : π (zadd r (zminus r) = Int0) { refine eq_trans (zadd_zminus_inverse r) int_of_0 };
  have hmono : π (zless (zadd r (zminus r)) (zadd a (zminus r)))
    { refine zadd_zless_mono1 r a (zminus r) hlt };
  have haq : π (zless Int0 (zmult a q))
    { refine ∧ₑ₁ (zless_intify2 Int0 (zmult a q))
        (ind_eq (eq_sym haq_eq) (λ w, zless Int0 w)
          (ind_eq (eq_sym hzr) (λ w, zless w (zadd a (zminus r))) hmono)) };
  have hposq : π (zless Int0 q)
    { refine ∨ₑ (∧ₑ₁ (int_0_less_mult_iff a q) haq) _ _
      { assume hc; refine ∧ₑ₂ hc }
      { assume hc; refine ⊥ₑ (zless_not_sym Int0 a hpos (∧ₑ₁ hc)) } };
  have hI1 : π (zadd Int0 Int1 = Int1)
    { rewrite (zadd_0_intify Int1); refine intify_ident Int1 Int1_in_int };
  refine ind_eq (eq_sym hI1) (λ w, zle w q) (∧ₑ₂ (add1_zle_iff Int0 q) hposq)
end;

opaque symbol self_quotient_aux2 (a r q : τ ι) :
  π (zless Int0 a) → π (a = zadd r (zmult a q)) → π (zle Int0 r) →
  π (zle q Int1) ≔
begin
  assume a r q hpos heq hle;
  have hia : π (intify a = zadd r (zmult a q))
    { refine ind_eq heq (λ w, intify w = zadd r (zmult a q))
        (intify_ident (zadd r (zmult a q)) (zadd_type r (zmult a q))) };
  have haq_eq : π (zmult a (zdiff Int1 q) = intify r)
    { rewrite (zdiff_zmult_distrib2 a Int1 q);
      rewrite (zmult_1_right_intify a);
      rewrite hia;
      rewrite (zdiff_def (zadd r (zmult a q)) (zmult a q));
      rewrite (zadd_assoc r (zmult a q) (zminus (zmult a q)));
      rewrite (zadd_zminus_inverse (zmult a q));
      refine zadd_int0_right_intify r };
  have hler : π (zle Int0 (zmult a (zdiff Int1 q)))
    { refine ind_eq haq_eq (λ w, zle Int0 w) (∧ₑ₂ (zle_intify2 Int0 r) hle) };
  have hle1q : π (zle Int0 (zdiff Int1 q))
    { refine ∨ₑ (∧ₑ₁ (int_0_le_mult_iff a (zdiff Int1 q)) hler) _ _
      { assume hc; refine ∧ₑ₂ hc }
      { assume hc;
        have h00 : π (zless Int0 Int0) { refine zless_zle_trans Int0 a Int0 hpos (∧ₑ₁ hc) };
        refine ⊥ₑ (zless_not_sym Int0 Int0 h00 h00) } };
  refine ∧ₑ₁ (zle_intify1 q Int1)
    (ind_eq (eq_sym (zadd_0_intify q)) (λ w, zle w Int1)
      (∧ₑ₁ (zle_zdiff_iff Int0 q Int1) hle1q))
end;

opaque symbol self_quotient (a q r : τ ι) :
  π (quorem (Pair a a) (Pair q r)) → π (a ∈ int) → π (q ∈ int) → π (a ≠ Int0) →
  π (q = Int1) ≔
begin
  assume a q r hq ha hqi hne;
  have hE : π (a = zadd (zmult a q) r
     ∧ ((zless Int0 a ∧ zle Int0 r ∧ zless r a)
        ∨ (¬ (zless Int0 a) ∧ zless a r ∧ zle r Int0)))
    { refine quoremE_pair a a q r hq };
  have heq_r : π (a = zadd r (zmult a q))
    { refine eq_trans (∧ₑ₁ hE) (zadd_commute (zmult a q) r) };
  refine ∨ₑ (∧ₑ₂ hE) _ _
  { assume hc;
    have hposa : π (zless Int0 a) { refine ∧ₑ₁ hc };
    refine zle_anti_sym q Int1
      (self_quotient_aux2 a r q hposa heq_r (∧ₑ₁ (∧ₑ₂ hc)))
      (self_quotient_aux1 a r q hposa heq_r (∧ₑ₂ (∧ₑ₂ hc)))
      hqi Int1_in_int }
  { assume hc;
    have har : π (zless a r) { refine ∧ₑ₁ (∧ₑ₂ hc) };
    have hr0 : π (zle r Int0) { refine ∧ₑ₂ (∧ₑ₂ hc) };
    have hlta : π (zless a Int0) { refine zless_zle_trans a r Int0 har hr0 };
    have hposma : π (zless Int0 (zminus a))
      { refine ∧ₑ₂ (zless_zminus Int0 a) (ind_eq zminus_0 (λ w, zless a w) hlta) };
    have heq' : π (zminus a = zadd (zminus r) (zmult (zminus a) q))
      { rewrite (zmult_zminus a q);
        rewrite (zadd_commute (zminus r) (zminus (zmult a q)));
        refine ind_eq (∧ₑ₁ hE) (λ w, zminus w = zadd (zminus (zmult a q)) (zminus r))
          (zminus_zadd_distrib (zmult a q) r) };
    have hrma : π (zless (zminus r) (zminus a))
      { refine ∧ₑ₂ (zminus_zless_zminus r a) har };
    have h0mr : π (zle Int0 (zminus r))
      { refine ∧ₑ₂ (zle_zminus Int0 r) (ind_eq zminus_0 (λ w, zle r w) hr0) };
    refine zle_anti_sym q Int1
      (self_quotient_aux2 (zminus a) (zminus r) q hposma heq' h0mr)
      (self_quotient_aux1 (zminus a) (zminus r) q hposma heq' hrma)
      hqi Int1_in_int }
end;

opaque symbol self_remainder (a q r : τ ι) :
  π (quorem (Pair a a) (Pair q r)) → π (a ∈ int) → π (q ∈ int) → π (r ∈ int) →
  π (a ≠ Int0) → π (r = Int0) ≔
begin
  assume a q r hq ha hqi hri hne;
  have hq1 : π (q = Int1) { refine self_quotient a q r hq ha hqi hne };
  have heq_qr : π (a = zadd (zmult a q) r) { refine ∧ₑ₁ (quoremE_pair a a q r hq) };
  have heq2 : π (a = zadd (zmult a Int1) r)
    { refine ind_eq (eq_sym hq1) (λ w, a = zadd (zmult a w) r) heq_qr };
  have hz1 : π (zmult a Int1 = a)
    { rewrite (zmult_1_right_intify a); refine intify_ident a ha };
  have heq3 : π (a = zadd a r)
    { refine ind_eq (eq_sym hz1) (λ w, a = zadd w r) heq2 };
  have ha0 : π (a = zadd a Int0)
    { refine eq_sym (eq_trans (zadd_0_right_intify a) (intify_ident a ha)) };
  refine ∧ₑ₁ (zadd_left_cancel Int0 r a Int0_in_int hri) (eq_trans (eq_sym heq3) ha0)
end;

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
begin
  assume b hb;
  rewrite zdiv_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  have hnle : π (¬ zle Int0 (intify NegInt1))
    { refine ∧ₑ₂ (not_zle_iff_zless Int0 (intify NegInt1))
        (∧ₑ₂ (zless_intify1 NegInt1 Int0) zless_NegInt1_Int0) };
  rewrite (If_not_P (zle Int0 (intify NegInt1)) _ _ hnle);
  have hposb : π (zless Int0 (intify b)) { refine ∧ₑ₂ (zless_intify2 Int0 b) hb };
  rewrite (If_P (zless Int0 (intify b)) _ _ hposb);
  rewrite (intify_ident NegInt1 NegInt1_in_int);
  rewrite (negDivAlg_minus1 (intify b));
  rewrite fst_conv;
  reflexivity
end;

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
begin
  assume b hb;
  rewrite zdiv_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  have hnle : π (¬ zle Int0 (intify NegInt1))
    { refine ∧ₑ₂ (not_zle_iff_zless Int0 (intify NegInt1))
        (∧ₑ₂ (zless_intify1 NegInt1 Int0) zless_NegInt1_Int0) };
  rewrite (If_not_P (zle Int0 (intify NegInt1)) _ _ hnle);
  have hposb : π (zless Int0 (intify b)) { refine ∧ₑ₂ (zless_intify2 Int0 b) hb };
  rewrite (If_P (zless Int0 (intify b)) _ _ hposb);
  rewrite (intify_ident NegInt1 NegInt1_in_int);
  rewrite (negDivAlg_minus1 (intify b));
  rewrite fst_conv;
  reflexivity
end;

opaque symbol zmod_minus1 (b : τ ι) :
  π (zless Int0 b) → π (zmod NegInt1 b = zdiff b Int1) ≔
begin
  assume b hb;
  rewrite zmod_def;
  rewrite divAlg_def;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  have hnle : π (¬ zle Int0 (intify NegInt1))
    { refine ∧ₑ₂ (not_zle_iff_zless Int0 (intify NegInt1))
        (∧ₑ₂ (zless_intify1 NegInt1 Int0) zless_NegInt1_Int0) };
  rewrite (If_not_P (zle Int0 (intify NegInt1)) _ _ hnle);
  have hposb : π (zless Int0 (intify b)) { refine ∧ₑ₂ (zless_intify2 Int0 b) hb };
  rewrite (If_P (zless Int0 (intify b)) _ _ hposb);
  rewrite (intify_ident NegInt1 NegInt1_in_int);
  rewrite (negDivAlg_minus1 (intify b));
  rewrite snd_conv;
  refine zdiff_intify1 b Int1
end;

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
begin
  assume a;
  have hposb : π (zless Int0 Int1) { refine zless_Int0_Int1 };
  have hsign : π (zle Int0 (zmod a Int1)) { refine pos_mod_sign a Int1 hposb };
  have hbound : π (zless (zmod a Int1) Int1) { refine pos_mod_bound a Int1 hposb };
  have hI1 : π (zadd Int0 Int1 = Int1)
    { rewrite (zadd_0_intify Int1); refine intify_ident Int1 Int1_in_int };
  have hle0 : π (zle (zmod a Int1) Int0)
    { refine ∧ₑ₁ (zless_add1_iff_zle (zmod a Int1) Int0)
        (ind_eq hI1 (λ w, zless (zmod a Int1) w) hbound) };
  refine zle_anti_sym (zmod a Int1) Int0 hle0 hsign (zmod_type a Int1) Int0_in_int
end;

opaque symbol zdiv_1 (a : τ ι) : π (zdiv a Int1 = intify a) ≔
begin
  assume a;
  have heq : π (intify a = zadd (zmult Int1 (zdiv a Int1)) (zmod a Int1))
    { refine zmod_zdiv_equality a Int1 };
  have hrhs : π (zadd (zmult Int1 (zdiv a Int1)) (zmod a Int1) = intify (zdiv a Int1))
    { rewrite (zmod_1 a); rewrite (zmult_1_intify (zdiv a Int1));
      rewrite (zadd_0_right_intify (intify (zdiv a Int1))); refine intify_idem (zdiv a Int1) };
  refine eq_trans (eq_sym (intify_ident (zdiv a Int1) (zdiv_type a Int1)))
    (eq_sym (eq_trans heq hrhs))
end;

opaque symbol zmod_minus1_right (a : τ ι) : π (zmod a NegInt1 = Int0) ≔
begin
  assume a;
  have hnegb : π (zless NegInt1 Int0) { refine zless_NegInt1_Int0 };
  have hsign : π (zle (zmod a NegInt1) Int0) { refine neg_mod_sign a NegInt1 hnegb };
  have hbound : π (zless NegInt1 (zmod a NegInt1)) { refine neg_mod_bound a NegInt1 hnegb };
  have hI : π (zadd NegInt1 Int1 = Int0)
    { rewrite NegInt1_eq_zminus_Int1; rewrite (zadd_zminus_inverse2 Int1); refine int_of_0 };
  have hge0 : π (zle Int0 (zmod a NegInt1))
    { refine ind_eq (eq_sym hI) (λ w, zle w (zmod a NegInt1))
        (∧ₑ₂ (add1_zle_iff NegInt1 (zmod a NegInt1)) hbound) };
  refine zle_anti_sym (zmod a NegInt1) Int0 hsign hge0 (zmod_type a NegInt1) Int0_in_int
end;

opaque symbol zdiv_minus1_right_raw (a : τ ι) :
  π (a ∈ int) → π (zdiv a NegInt1 = zminus a) ≔
begin
  assume a ha;
  have heq : π (intify a = zadd (zmult NegInt1 (zdiv a NegInt1)) (zmod a NegInt1))
    { refine zmod_zdiv_equality a NegInt1 };
  have hrhs : π (zadd (zmult NegInt1 (zdiv a NegInt1)) (zmod a NegInt1)
      = zminus (zdiv a NegInt1))
    { rewrite (zmod_minus1_right a); rewrite (zmult_minus1 (zdiv a NegInt1));
      rewrite (zadd_0_right_intify (zminus (zdiv a NegInt1)));
      refine intify_ident (zminus (zdiv a NegInt1)) (zminus_type (zdiv a NegInt1)) };
  have heqA : π (a = zminus (zdiv a NegInt1))
    { refine eq_trans (eq_sym (intify_ident a ha)) (eq_trans heq hrhs) };
  refine eq_sym (ind_eq heqA (λ w, zminus w = zdiv a NegInt1)
    (zminus_zminus (zdiv a NegInt1) (zdiv_type a NegInt1)))
end;

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
begin
  assume b' q' r' h hr hb;
  have hrb : π (zless r' (intify b')) { refine ∧ₑ₂ (zless_intify2 r' b') hr };
  have hstep : π (zless (zadd (zmult b' q') r') (zadd (zmult b' q') (intify b')))
    { refine zadd_zless_mono2 r' (intify b') (zmult b' q') hrb };
  have hpos : π (zless Int0 (zadd (zmult b' q') (intify b')))
    { refine zle_zless_trans Int0 (zadd (zmult b' q') r')
        (zadd (zmult b' q') (intify b')) h hstep };
  have heq4 : π (zmult b' (zadd q' Int1) = zadd (zmult b' q') (intify b'))
    { rewrite (zadd_zmult_distrib2 b' q' Int1);
      rewrite (zmult_1_right_intify b');
      reflexivity };
  have h4 : π (zless Int0 (zmult b' (zadd q' Int1)))
    { refine ind_eq heq4 (λ v, zless Int0 v) hpos };
  refine ∨ₑ (∧ₑ₁ (int_0_less_mult_iff b' (zadd q' Int1)) h4) _ _
  { assume hc; refine ∧ₑ₁ (zless_add1_iff_zle Int0 q') (∧ₑ₂ hc) }
  { assume hc;
    have h00 : π (zless Int0 Int0) { refine zless_trans Int0 b' Int0 hb (∧ₑ₁ hc) };
    refine ⊥ₑ (zless_not_sym Int0 Int0 h00 h00) }
end;

opaque symbol zdiv_mono2_lemma (b q r b' q' r' : τ ι) :
  π (zadd (zmult b q) r = zadd (zmult b' q') r') →
  π (zle Int0 (zadd (zmult b' q') r')) →
  π (zless r' b') → π (zle Int0 r) → π (zless Int0 b') → π (zle b' b) →
  π (zle q q') ≔
begin
  assume b q r b' q' r' heq hpos hr'b' hr0 hb'pos hb'b;
  have hbpos : π (zless Int0 b) { refine zless_zle_trans Int0 b' b hb'pos hb'b };
  have hq'0 : π (zle Int0 q') { refine q_pos_lemma b' q' r' hpos hr'b' hb'pos };
  have hbq' : π (zle (zmult b' q') (zmult b q')) { refine zmult_zle_mono1 b' b q' hb'b hq'0 };
  have hr'b : π (zless r' b) { refine zless_zle_trans r' b' b hr'b' hb'b };
  have hr'lt0 : π (zless (zadd r' Int0) (zadd b r))
    { refine zadd_zless_mono b r' r Int0 hr'b hr0 };
  have hr'lt : π (zless r' (zadd b r))
    { refine ∧ₑ₁ (zless_intify1 r' (zadd b r)) _;
      rewrite left (zadd_0_right_intify r');
      refine hr'lt0 };
  have hdiff : π (zless (zdiff r' r) b)
    { refine ∧ₑ₂ (zdiff_zless_iff r' r b) hr'lt };
  have hmono : π (zless (zadd (zdiff r' r) (zmult b' q')) (zadd b (zmult b q')))
    { refine zadd_zless_mono b (zdiff r' r) (zmult b q') (zmult b' q') hdiff hbq' };
  have hE : π (zadd (zadd (zdiff r' r) (zmult b' q')) r = zadd (zmult b' q') r')
    { rewrite (zadd_commute (zdiff r' r) (zmult b' q'));
      rewrite (zadd_assoc (zmult b' q') (zdiff r' r) r);
      rewrite zdiff_def;
      rewrite (zadd_assoc r' (zminus r) r);
      rewrite (zadd_zminus_inverse2 r);
      rewrite (zadd_int0_right_intify r');
      rewrite (zadd_intify2 (zmult b' q') r');
      reflexivity };
  have heq2 : π (zadd (zmult b q) r = zadd (zadd (zdiff r' r) (zmult b' q')) r)
    { refine eq_trans heq (eq_sym hE) };
  have hbq_eq : π (zmult b q = zadd (zdiff r' r) (zmult b' q'))
    { refine ∧ₑ₁ (zadd_right_cancel (zadd (zdiff r' r) (zmult b' q')) (zmult b q) r
        (zadd_type (zdiff r' r) (zmult b' q')) (zmult_type b q)) heq2 };
  have hrhs2 : π (zadd b (zmult b q') = zmult b (zadd q' Int1))
    { rewrite (zadd_zmult_distrib2 b q' Int1);
      rewrite (zmult_1_right_intify b);
      rewrite (zadd_commute b (zmult b q'));
      rewrite left (zadd_intify2 (zmult b q') b);
      reflexivity };
  have hkey : π (zless (zmult b q) (zmult b (zadd q' Int1)))
    { rewrite hbq_eq;
      rewrite left hrhs2;
      refine hmono };
  refine ∨ₑ (∧ₑ₁ (zmult_zless_cancel1 b q (zadd q' Int1)) hkey) _ _
  { assume hc; refine ∧ₑ₁ (zless_add1_iff_zle q q') (∧ₑ₂ hc) }
  { assume hc; refine ⊥ₑ (zless_not_sym Int0 b hbpos (∧ₑ₁ hc)) }
end;

opaque symbol zdiv_mono2_raw (a b b' : τ ι) :
  π (zle Int0 a) → π (zless Int0 b') → π (zle b' b) → π (a ∈ int) →
  π (zle (zdiv a b) (zdiv a b')) ≔
begin
  assume a b b' h1 h2 h3 ha;
  have hbpos : π (zless Int0 b) { refine zless_zle_trans Int0 b' b h2 h3 };
  have heq : π (zadd (zmult b (zdiv a b)) (zmod a b) = zadd (zmult b' (zdiv a b')) (zmod a b'))
    { refine eq_trans (eq_sym (zmod_zdiv_equality a b)) (zmod_zdiv_equality a b') };
  have hpos : π (zle Int0 (zadd (zmult b' (zdiv a b')) (zmod a b')))
    { refine ind_eq (eq_sym (zmod_zdiv_equality a b')) (λ v, zle Int0 v)
        (∧ₑ₂ (zle_intify2 Int0 a) h1) };
  refine zdiv_mono2_lemma b (zdiv a b) (zmod a b) b' (zdiv a b') (zmod a b')
    heq hpos (pos_mod_bound a b' h2) (pos_mod_sign a b hbpos) h2 h3
end;

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
begin
  assume b' q' r' h hr hb;
  have hz : π (zle (zadd (zmult b' q') Int0) (zadd (zmult b' q') r'))
    { refine zadd_zle_mono2 Int0 r' (zmult b' q') hr };
  have hz2 : π (zle (intify (zmult b' q')) (zadd (zmult b' q') r'))
    { refine ind_eq (eq_sym (zadd_0_right_intify (zmult b' q')))
        (λ v, zle v (zadd (zmult b' q') r')) hz };
  have h1 : π (zle (zmult b' q') (zadd (zmult b' q') r'))
    { refine ∧ₑ₁ (zle_intify1 (zmult b' q') (zadd (zmult b' q') r')) hz2 };
  have hlt : π (zless (zmult b' q') Int0)
    { refine zle_zless_trans (zmult b' q') (zadd (zmult b' q') r') Int0 h1 h };
  refine ∨ₑ (∧ₑ₁ (zmult_less_0_iff b' q') hlt) _ _
  { assume hc; refine ∧ₑ₂ hc }
  { assume hc;
    have h00 : π (zless Int0 Int0) { refine zless_trans Int0 b' Int0 hb (∧ₑ₁ hc) };
    refine ⊥ₑ (zless_not_sym Int0 Int0 h00 h00) }
end;

opaque symbol zdiv_mono2_neg_lemma (b q r b' q' r' : τ ι) :
  π (zadd (zmult b q) r = zadd (zmult b' q') r') →
  π (zless (zadd (zmult b' q') r') Int0) →
  π (zless r b) → π (zle Int0 r') → π (zless Int0 b') → π (zle b' b) →
  π (zle q' q) ≔
begin
  assume b q r b' q' r' heq hneg hrb hr'0 hb'pos hb'b;
  have hbpos : π (zless Int0 b) { refine zless_zle_trans Int0 b' b hb'pos hb'b };
  have hq'neg : π (zless q' Int0) { refine q_neg_lemma b' q' r' hneg hr'0 hb'pos };
  have hbq' : π (zle (zmult b q') (zmult b' q'))
    { refine ∧ₑ₂ (zmult_zle_cancel2 b q' b') _;
      refine ∧ᵢ _ _
      { assume h0; refine ⊥ₑ (zless_not_sym Int0 q' h0 hq'neg) }
      { assume h1; refine hb'b } };
  have hrr'0 : π (zless (zadd r Int0) (zadd b r'))
    { refine zadd_zless_mono b r r' Int0 hrb hr'0 };
  have hrr' : π (zless r (zadd b r'))
    { refine ∧ₑ₁ (zless_intify1 r (zadd b r')) _;
      rewrite left (zadd_0_right_intify r);
      refine hrr'0 };
  have hstep1 : π (zless (zadd (zmult b' q') r) (zadd (zmult b' q') (zadd b r')))
    { refine zadd_zless_mono2 r (zadd b r') (zmult b' q') hrr' };
  have hstep2 : π (zadd (zmult b' q') (zadd b r') = zadd b (zadd (zmult b q) r))
    { rewrite (zadd_left_commute (zmult b' q') b r');
      rewrite left heq;
      reflexivity };
  have hlt3 : π (zless (zadd (zmult b' q') r) (zadd b (zadd (zmult b q) r)))
    { rewrite left hstep2; refine hstep1 };
  have hlt2 : π (zless (zmult b' q') (zadd b (zmult b q)))
    { refine ∧ₑ₁ (zadd_right_cancel_zless (zadd b (zmult b q)) (zmult b' q') r) _;
      rewrite (zadd_assoc b (zmult b q) r);
      refine hlt3 };
  have hlt_final : π (zless (zmult b q') (zadd b (zmult b q)))
    { refine zle_zless_trans (zmult b q') (zmult b' q') (zadd b (zmult b q)) hbq' hlt2 };
  have hrhs2 : π (zadd b (zmult b q) = zmult b (zadd q Int1))
    { rewrite (zadd_zmult_distrib2 b q Int1);
      rewrite (zmult_1_right_intify b);
      rewrite (zadd_commute b (zmult b q));
      rewrite left (zadd_intify2 (zmult b q) b);
      reflexivity };
  have hkey : π (zless (zmult b q') (zmult b (zadd q Int1)))
    { rewrite left hrhs2; refine hlt_final };
  refine ∨ₑ (∧ₑ₁ (zmult_zless_cancel1 b q' (zadd q Int1)) hkey) _ _
  { assume hc; refine ∧ₑ₁ (zless_add1_iff_zle q' q) (∧ₑ₂ hc) }
  { assume hc; refine ⊥ₑ (zless_not_sym Int0 b hbpos (∧ₑ₁ hc)) }
end;

opaque symbol zdiv_mono2_neg_raw (a b b' : τ ι) :
  π (zless a Int0) → π (zless Int0 b') → π (zle b' b) → π (a ∈ int) →
  π (zle (zdiv a b') (zdiv a b)) ≔
begin
  assume a b b' h1 h2 h3 ha;
  have hbpos : π (zless Int0 b) { refine zless_zle_trans Int0 b' b h2 h3 };
  have heq : π (zadd (zmult b (zdiv a b)) (zmod a b) = zadd (zmult b' (zdiv a b')) (zmod a b'))
    { refine eq_trans (eq_sym (zmod_zdiv_equality a b)) (zmod_zdiv_equality a b') };
  have hneg : π (zless (zadd (zmult b' (zdiv a b')) (zmod a b')) Int0)
    { refine ind_eq (eq_sym (zmod_zdiv_equality a b')) (λ v, zless v Int0)
        (∧ₑ₂ (zless_intify1 a Int0) h1) };
  refine zdiv_mono2_neg_lemma b (zdiv a b) (zmod a b) b' (zdiv a b') (zmod a b')
    heq hneg (pos_mod_bound a b hbpos) (pos_mod_sign a b' h2) h2 h3
end;

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
begin
  assume b c q r a hq hc hc0;
  have heq : π (b = zadd (zmult c q) r) { refine ∧ₑ₁ (quoremE_pair b c q r hq) };
  have hmar : π (zmult a r ∈ int) { refine zmult_type a r };
  refine quoremI (zmult a b) c
    (zadd (zmult a q) (zdiv (zmult a r) c)) (zmod (zmult a r) c) _ _
  { rewrite heq;
    rewrite (zadd_zmult_distrib2 a (zmult c q) r);
    rewrite (zadd_zmult_distrib2 c (zmult a q) (zdiv (zmult a r) c));
    rewrite (zadd_assoc (zmult c (zmult a q)) (zmult c (zdiv (zmult a r) c)) (zmod (zmult a r) c));
    rewrite left (raw_zmod_zdiv_equality (zmult a r) c hmar hc);
    rewrite (zmult_left_commute a c q);
    reflexivity }
  { refine ∨ₑ (∧ₑ₁ (neq_iff_zless c Int0 hc Int0_in_int) hc0) _ _
    { assume hlt;
      refine ∨ᵢ₂ (∧ᵢ (zless_not_sym c Int0 hlt)
        (∧ᵢ (neg_mod_bound (zmult a r) c hlt) (neg_mod_sign (zmult a r) c hlt))) }
    { assume hgt;
      refine ∨ᵢ₁ (∧ᵢ hgt (∧ᵢ (pos_mod_sign (zmult a r) c hgt) (pos_mod_bound (zmult a r) c hgt))) } }
end;

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
begin
  assume a c aq ar b bq br hqa hqb hc hc0;
  have ha : π (a = zadd (zmult c aq) ar) { refine ∧ₑ₁ (quoremE_pair a c aq ar hqa) };
  have hb : π (b = zadd (zmult c bq) br) { refine ∧ₑ₁ (quoremE_pair b c bq br hqb) };
  have hs : π (zadd ar br ∈ int) { refine zadd_type ar br };
  refine quoremI (zadd a b) c
    (zadd (zadd aq bq) (zdiv (zadd ar br) c)) (zmod (zadd ar br) c) _ _
  { rewrite ha; rewrite hb;
    rewrite (zadd_zmult_distrib2 c (zadd aq bq) (zdiv (zadd ar br) c));
    rewrite (zadd_zmult_distrib2 c aq bq);
    rewrite (zadd_assoc (zadd (zmult c aq) (zmult c bq))
                        (zmult c (zdiv (zadd ar br) c)) (zmod (zadd ar br) c));
    rewrite left (raw_zmod_zdiv_equality (zadd ar br) c hs hc);
    rewrite (zadd_assoc (zmult c aq) ar (zadd (zmult c bq) br));
    rewrite (zadd_left_commute ar (zmult c bq) br);
    rewrite (zadd_assoc (zmult c aq) (zmult c bq) (zadd ar br));
    reflexivity }
  { refine ∨ₑ (∧ₑ₁ (neq_iff_zless c Int0 hc Int0_in_int) hc0) _ _
    { assume hlt;
      refine ∨ᵢ₂ (∧ᵢ (zless_not_sym c Int0 hlt)
        (∧ᵢ (neg_mod_bound (zadd ar br) c hlt) (neg_mod_sign (zadd ar br) c hlt))) }
    { assume hgt;
      refine ∨ᵢ₁ (∧ᵢ hgt (∧ᵢ (pos_mod_sign (zadd ar br) c hgt) (pos_mod_bound (zadd ar br) c hgt))) } }
end;

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
begin
  assume a b ha hb;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0; rewrite hb0; rewrite (DIVISION_BY_ZERO_ZMOD a);
    refine DIVISION_BY_ZERO_ZDIV (intify a) }
  { assume hb0;
    refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) _ _
    { assume hbneg;
      refine zdiv_neg_neg_trivial (zmod a b) b (neg_mod_sign a b hbneg) (neg_mod_bound a b hbneg) }
    { assume hbpos;
      refine zdiv_pos_pos_trivial (zmod a b) b (pos_mod_sign a b hbpos) (pos_mod_bound a b hbpos) } }
end;

opaque symbol zmod_div_trivial (a b : τ ι) : π (zdiv (zmod a b) b = Int0) ≔
begin
  assume a b;
  rewrite left (zmod_deintify a b);
  rewrite left (zdiv_intify2 (zmod (intify a) (intify b)) b);
  refine zmod_div_trivial_raw (intify a) (intify b) (intify_in_int a) (intify_in_int b)
end;

opaque symbol zmod_mod_trivial_raw (a b : τ ι) :
  π (a ∈ int) → π (b ∈ int) → π (zmod (zmod a b) b = zmod a b) ≔
begin
  assume a b ha hb;
  refine ∨ₑ (em (b = Int0)) _ _
  { assume hb0; rewrite hb0; rewrite (DIVISION_BY_ZERO_ZMOD a);
    rewrite (DIVISION_BY_ZERO_ZMOD (intify a)); rewrite intify_idem; reflexivity }
  { assume hb0;
    refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) _ _
    { assume hbneg;
      rewrite (zmod_neg_neg_trivial (zmod a b) b (neg_mod_sign a b hbneg) (neg_mod_bound a b hbneg));
      refine intify_ident (zmod a b) (zmod_type a b) }
    { assume hbpos;
      rewrite (zmod_pos_pos_trivial (zmod a b) b (pos_mod_sign a b hbpos) (pos_mod_bound a b hbpos));
      refine intify_ident (zmod a b) (zmod_type a b) } }
end;

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
begin
  assume c b r q hc hbr hr0;
  have hbneg : π (zless b Int0) { refine zless_zle_trans b r Int0 hbr hr0 };
  have hble0 : π (zle b Int0) { refine zless_imp_zle b Int0 hbneg };
  have hone : π (zle Int1 (zdiff c (zmod q c)))
    { refine ∧ₑ₂ (zle_zdiff_iff Int1 (zmod q c) c) _;
      rewrite (zadd_commute Int1 (zmod q c));
      refine ∧ₑ₂ (add1_zle_iff (zmod q c) c) (pos_mod_bound q c hc) };
  have hmono : π (zle (zmult b (zdiff c (zmod q c))) (zmult b Int1))
    { refine zmult_zle_mono2_neg Int1 (zdiff c (zmod q c)) b hone hble0 };
  have hb1 : π (zless (zmult b Int1) r)
    { rewrite (zmult_1_right_intify b);
      refine ∧ₑ₂ (zless_intify1 b r) hbr };
  have hkey' : π (zless (zmult b (zdiff c (zmod q c))) r)
    { refine zle_zless_trans (zmult b (zdiff c (zmod q c))) (zmult b Int1) r hmono hb1 };
  have hkey : π (zless (zdiff (zmult b c) (zmult b (zmod q c))) r)
    { rewrite left (zdiff_zmult_distrib2 b c (zmod q c));
      refine hkey' };
  rewrite (zadd_commute (zmult b (zmod q c)) r);
  refine ∧ₑ₁ (zdiff_zless_iff (zmult b c) (zmult b (zmod q c)) r) hkey
end;

opaque symbol zdiv_zmult2_aux2 (c b r q : τ ι) :
  π (zless Int0 c) → π (zless b r) → π (zle r Int0) →
  π (zle (zadd (zmult b (zmod q c)) r) Int0) ≔
begin
  assume c b r q hc hbr hr0;
  have hbneg : π (zless b Int0) { refine zless_zle_trans b r Int0 hbr hr0 };
  have hble0 : π (zle b Int0) { refine zless_imp_zle b Int0 hbneg };
  have hmul : π (zle (zmult b (zmod q c)) Int0)
    { refine ∧ₑ₂ (zmult_le_0_iff b (zmod q c)) (∨ᵢ₂ (∧ᵢ hble0 (pos_mod_sign q c hc))) };
  have hz00 : π (zadd Int0 Int0 = Int0)
    { rewrite (zadd_0_right_intify Int0); refine intify_ident Int0 Int0_in_int };
  have hsum : π (zle (zadd (zmult b (zmod q c)) r) (zadd Int0 Int0))
    { refine zadd_zle_mono Int0 (zmult b (zmod q c)) Int0 r hmul hr0 };
  refine zle_trans (zadd (zmult b (zmod q c)) r) (zadd Int0 Int0) Int0 hsum
    (zle_eq_refl (zadd Int0 Int0) Int0 hz00)
end;

opaque symbol zdiv_zmult2_aux3 (c r b q : τ ι) :
  π (zless Int0 c) → π (zle Int0 r) → π (zless r b) →
  π (zle Int0 (zadd (zmult b (zmod q c)) r)) ≔
begin
  assume c r b q hc hr0 hrb;
  have hbpos : π (zless Int0 b) { refine zle_zless_trans Int0 r b hr0 hrb };
  have hb0 : π (zle Int0 b) { refine zless_imp_zle Int0 b hbpos };
  have hmul : π (zle Int0 (zmult b (zmod q c)))
    { refine ∧ₑ₂ (int_0_le_mult_iff b (zmod q c)) (∨ᵢ₁ (∧ᵢ hb0 (pos_mod_sign q c hc))) };
  have hz00 : π (zadd Int0 Int0 = Int0)
    { rewrite (zadd_0_right_intify Int0); refine intify_ident Int0 Int0_in_int };
  have hsum : π (zle (zadd Int0 Int0) (zadd (zmult b (zmod q c)) r))
    { refine zadd_zle_mono (zmult b (zmod q c)) Int0 r Int0 hmul hr0 };
  refine zle_trans Int0 (zadd Int0 Int0) (zadd (zmult b (zmod q c)) r)
    (zle_eq_refl Int0 (zadd Int0 Int0) (eq_sym hz00)) hsum
end;

opaque symbol zdiv_zmult2_aux4 (c r b q : τ ι) :
  π (zless Int0 c) → π (zle Int0 r) → π (zless r b) →
  π (zless (zadd (zmult b (zmod q c)) r) (zmult b c)) ≔
begin
  assume c r b q hc hr0 hrb;
  have hbpos : π (zless Int0 b) { refine zle_zless_trans Int0 r b hr0 hrb };
  have hb0 : π (zle Int0 b) { refine zless_imp_zle Int0 b hbpos };
  have hone : π (zle Int1 (zdiff c (zmod q c)))
    { refine ∧ₑ₂ (zle_zdiff_iff Int1 (zmod q c) c) _;
      rewrite (zadd_commute Int1 (zmod q c));
      refine ∧ₑ₂ (add1_zle_iff (zmod q c) c) (pos_mod_bound q c hc) };
  have hmono : π (zle (zmult b Int1) (zmult b (zdiff c (zmod q c))))
    { refine zmult_zle_mono2 Int1 (zdiff c (zmod q c)) b hone hb0 };
  have hb1 : π (zless r (zmult b Int1))
    { rewrite (zmult_1_right_intify b);
      refine ∧ₑ₂ (zless_intify2 r b) hrb };
  have hkey' : π (zless r (zmult b (zdiff c (zmod q c))))
    { refine zless_zle_trans r (zmult b Int1) (zmult b (zdiff c (zmod q c))) hb1 hmono };
  have hkey : π (zless r (zdiff (zmult b c) (zmult b (zmod q c))))
    { rewrite left (zdiff_zmult_distrib2 b c (zmod q c));
      refine hkey' };
  rewrite (zadd_commute (zmult b (zmod q c)) r);
  refine ∧ₑ₁ (zless_zdiff_iff r (zmult b (zmod q c)) (zmult b c)) hkey
end;

opaque symbol zdiv_zmult2_lemma (a b q r c : τ ι) :
  π (quorem (Pair a b) (Pair q r)) → π (a ∈ int) → π (b ∈ int) → π (b ≠ Int0) →
  π (zless Int0 c) →
  π (quorem (Pair a (zmult b c)) (Pair (zdiv q c) (zadd (zmult b (zmod q c)) r))) ≔
begin
  assume a b q r c hq ha hb hb0 hc;
  have heq : π (a = zadd (zmult b q) r) { refine ∧ₑ₁ (quoremE_pair a b q r hq) };
  refine quoremI a (zmult b c) (zdiv q c) (zadd (zmult b (zmod q c)) r) _ _
  { rewrite heq;
    rewrite left (zmult_intify2 b q);
    rewrite (zmod_zdiv_equality q c);
    rewrite (zadd_zmult_distrib2 b (zmult c (zdiv q c)) (zmod q c));
    rewrite (zmult_assoc b c (zdiv q c));
    rewrite (zadd_assoc (zmult b (zmult c (zdiv q c))) (zmult b (zmod q c)) r);
    reflexivity }
  { have hdisj : π ((zless Int0 b ∧ zle Int0 r ∧ zless r b)
                    ∨ (¬ (zless Int0 b) ∧ zless b r ∧ zle r Int0))
      { refine ∧ₑ₂ (quoremE_pair a b q r hq) };
    refine ∨ₑ (∧ₑ₁ (neq_iff_zless b Int0 hb Int0_in_int) hb0) _ _
    { assume hbneg;
      have hbcneg : π (zless (zmult b c) Int0)
        { refine ∧ₑ₂ (zmult_less_0_iff b c) (∨ᵢ₂ (∧ᵢ hbneg hc)) };
      have hnbc : π (¬ (zless Int0 (zmult b c)))
        { refine zless_not_sym (zmult b c) Int0 hbcneg };
      have hneg_r : π (zless b r ∧ zle r Int0)
        { refine ∨ₑ hdisj _ _
          { assume hc'; refine ⊥ₑ (zless_not_sym b Int0 hbneg (∧ₑ₁ hc')) }
          { assume hc'; refine ∧ᵢ (∧ₑ₁ (∧ₑ₂ hc')) (∧ₑ₂ (∧ₑ₂ hc')) } };
      refine ∨ᵢ₂ (∧ᵢ hnbc (∧ᵢ
        (zdiv_zmult2_aux1 c b r q hc (∧ₑ₁ hneg_r) (∧ₑ₂ hneg_r))
        (zdiv_zmult2_aux2 c b r q hc (∧ₑ₁ hneg_r) (∧ₑ₂ hneg_r)))) }
    { assume hbpos;
      have hbcpos : π (zless Int0 (zmult b c))
        { refine ∧ₑ₂ (int_0_less_mult_iff b c) (∨ᵢ₁ (∧ᵢ hbpos hc)) };
      have hpos_r : π (zle Int0 r ∧ zless r b)
        { refine ∨ₑ hdisj _ _
          { assume hc'; refine ∧ᵢ (∧ₑ₁ (∧ₑ₂ hc')) (∧ₑ₂ (∧ₑ₂ hc')) }
          { assume hc'; refine ⊥ₑ (∧ₑ₁ hc' hbpos) } };
      refine ∨ᵢ₁ (∧ᵢ hbcpos (∧ᵢ
        (zdiv_zmult2_aux3 c r b q hc (∧ₑ₁ hpos_r) (∧ₑ₂ hpos_r))
        (zdiv_zmult2_aux4 c r b q hc (∧ₑ₁ hpos_r) (∧ₑ₂ hpos_r)))) } }
end;

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
begin
  assume a b hlta hposb;
  have hI : π (zadd NegInt1 Int1 = Int0)
    { rewrite NegInt1_eq_zminus_Int1; rewrite (zadd_zminus_inverse2 Int1); refine int_of_0 };
  have hle_a : π (zle a NegInt1)
    { refine ∧ₑ₁ (zless_add1_iff_zle a NegInt1)
        (ind_eq hI (λ w, zless a w) hlta) };
  have hmono : π (zle (zdiv a b) (zdiv NegInt1 b)) { refine zdiv_mono1 a NegInt1 b hle_a hposb };
  have hm1 : π (zle (zdiv a b) NegInt1)
    { refine ind_eq (eq_sym (zdiv_minus1 b hposb)) (λ w, zle (zdiv a b) w) hmono };
  refine zle_zless_trans (zdiv a b) NegInt1 Int0 hm1 zless_NegInt1_Int0
end;

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
begin
  assume a b hnegb;
  have hposmb : π (zless Int0 (zminus b))
    { refine ∧ₑ₂ (zless_zminus Int0 b) (ind_eq zminus_0 (λ w, zless b w) hnegb) };
  have hiff1 : π (zle Int0 (zdiv (zminus a) (zminus b)) ⇔ zle Int0 (zminus a))
    { refine pos_imp_zdiv_nonneg_iff (zminus a) (zminus b) hposmb };
  apply ∧ᵢ
  { assume h;
    have h2 : π (zle Int0 (zdiv (zminus a) (zminus b)))
      { refine ind_eq (zdiv_zminus_zminus a b) (λ w, zle Int0 w) h };
    refine ind_eq (eq_sym zminus_0) (λ w, zle a w)
      (∧ₑ₁ (zle_zminus Int0 a) (∧ₑ₁ hiff1 h2)) }
  { assume h;
    have h3 : π (zle Int0 (zminus a))
      { refine ∧ₑ₂ (zle_zminus Int0 a) (ind_eq zminus_0 (λ w, zle a w) h) };
    refine ind_eq (eq_sym (zdiv_zminus_zminus a b)) (λ w, zle Int0 w) (∧ₑ₂ hiff1 h3) }
end;

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
