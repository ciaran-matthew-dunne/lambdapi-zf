// ZF.Bin — Arithmetic on Binary Integers
// Faithful SKELETON port of isabelle-src/Bin.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
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
opaque symbol bin_rec_def (fPls fMin : τ ι) (fBit : τ ι → τ ι → τ ι → τ ι) (z : τ ι) :
  π (bin_rec fPls fMin fBit z =
     Vrec z (λ z2 g, bin_case fPls fMin (λ w b, fBit w b (fapply g w)) z2)) ≔
begin admit end;

// ===========================================================================
// Basic freeness / typing
// ===========================================================================

opaque symbol bin_PlsI : π (Pls ∈ bin) ≔
begin admit end;

opaque symbol bin_MinI : π (Min ∈ bin) ≔
begin admit end;

opaque symbol bin_BitI (w b : τ ι) :
  π (w ∈ bin) → π (b ∈ bool_set) → π (Bit w b ∈ bin) ≔
begin admit end;

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
// NCons_simps (`declare bin.intros [simp,TC]`, plus the immediate NCons
// simplification lemmas)
// ===========================================================================

opaque symbol NCons_Pls_0 : π (NCons Pls empty = Pls) ≔
begin admit end;

opaque symbol NCons_Pls_1 : π (NCons Pls one = Bit Pls one) ≔
begin admit end;

opaque symbol NCons_Min_0 : π (NCons Min empty = Bit Min empty) ≔
begin admit end;

opaque symbol NCons_Min_1 : π (NCons Min one = Min) ≔
begin admit end;

opaque symbol NCons_BIT (w x b : τ ι) : π (NCons (Bit w x) b = Bit (Bit w x) b) ≔
begin admit end;

// ===========================================================================
// Type checking
// ===========================================================================

opaque symbol integ_of_type (w : τ ι) : π (w ∈ bin) → π (integ_of w ∈ int) ≔
begin admit end;

opaque symbol NCons_type (w b : τ ι) :
  π (w ∈ bin) → π (b ∈ bool_set) → π (NCons w b ∈ bin) ≔
begin admit end;

opaque symbol bin_succ_type (w : τ ι) : π (w ∈ bin) → π (bin_succ w ∈ bin) ≔
begin admit end;

opaque symbol bin_pred_type (w : τ ι) : π (w ∈ bin) → π (bin_pred w ∈ bin) ≔
begin admit end;

opaque symbol bin_minus_type (w : τ ι) : π (w ∈ bin) → π (bin_minus w ∈ bin) ≔
begin admit end;

// This proof is complicated by the mutual recursion
opaque symbol bin_add_type (v : τ ι) :
  π (v ∈ bin) → π (Ball bin (λ w, bin_add v w ∈ bin)) ≔
begin admit end;

opaque symbol bin_mult_type (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) → π (bin_mult v w ∈ bin) ≔
begin admit end;

// ===========================================================================
// The Carry and Borrow Functions: bin_succ and bin_pred
// ===========================================================================

// NCons preserves the integer value of its argument
opaque symbol integ_of_NCons (w b : τ ι) :
  π (w ∈ bin) → π (b ∈ bool_set) → π (integ_of (NCons w b) = integ_of (Bit w b)) ≔
begin admit end;

opaque symbol integ_of_succ (w : τ ι) :
  π (w ∈ bin) → π (integ_of (bin_succ w) = zadd (int_of one) (integ_of w)) ≔
begin admit end;

opaque symbol integ_of_pred (w : τ ι) :
  π (w ∈ bin) → π (integ_of (bin_pred w) = zadd (zminus (int_of one)) (integ_of w)) ≔
begin admit end;

// ===========================================================================
// bin_minus: Unary Negation of Binary Integers
// ===========================================================================

opaque symbol integ_of_minus (w : τ ι) :
  π (w ∈ bin) → π (integ_of (bin_minus w) = zminus (integ_of w)) ≔
begin admit end;

// ===========================================================================
// bin_add: Binary Addition
// ===========================================================================

opaque symbol bin_add_Pls (w : τ ι) : π (w ∈ bin) → π (bin_add Pls w = w) ≔
begin admit end;

opaque symbol bin_add_Pls_right (w : τ ι) : π (w ∈ bin) → π (bin_add w Pls = w) ≔
begin admit end;

opaque symbol bin_add_Min (w : τ ι) : π (w ∈ bin) → π (bin_add Min w = bin_pred w) ≔
begin admit end;

opaque symbol bin_add_Min_right (w : τ ι) :
  π (w ∈ bin) → π (bin_add w Min = bin_pred w) ≔
begin admit end;

opaque symbol bin_add_BIT_Pls (v x : τ ι) : π (bin_add (Bit v x) Pls = Bit v x) ≔
begin admit end;

opaque symbol bin_add_BIT_Min (v x : τ ι) :
  π (bin_add (Bit v x) Min = bin_pred (Bit v x)) ≔
begin admit end;

opaque symbol bin_add_BIT_BIT (v x w y : τ ι) :
  π (w ∈ bin) → π (y ∈ bool_set) →
  π (bin_add (Bit v x) (Bit w y) =
     NCons (bin_add v (cond (and x y) (bin_succ w) w)) (xor x y)) ≔
begin admit end;

opaque symbol integ_of_add (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (integ_of (bin_add v w) = zadd (integ_of v) (integ_of w)) ≔
begin admit end;

// Subtraction
opaque symbol diff_integ_of_eq (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zdiff (integ_of v) (integ_of w) = integ_of (bin_add v (bin_minus w))) ≔
begin admit end;

// ===========================================================================
// bin_mult: Binary Multiplication
// ===========================================================================

opaque symbol integ_of_mult (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (integ_of (bin_mult v w) = zmult (integ_of v) (integ_of w)) ≔
begin admit end;

// ===========================================================================
// Computations
// ===========================================================================

// extra rules for bin_succ, bin_pred
opaque symbol bin_succ_1 (w : τ ι) : π (bin_succ (Bit w one) = Bit (bin_succ w) empty) ≔
begin admit end;

opaque symbol bin_succ_0 (w : τ ι) : π (bin_succ (Bit w empty) = NCons w one) ≔
begin admit end;

opaque symbol bin_pred_1 (w : τ ι) : π (bin_pred (Bit w one) = NCons w empty) ≔
begin admit end;

opaque symbol bin_pred_0 (w : τ ι) : π (bin_pred (Bit w empty) = Bit (bin_pred w) one) ≔
begin admit end;

// extra rules for bin_minus
opaque symbol bin_minus_1 (w : τ ι) :
  π (bin_minus (Bit w one) = bin_pred (NCons (bin_minus w) empty)) ≔
begin admit end;

opaque symbol bin_minus_0 (w : τ ι) :
  π (bin_minus (Bit w empty) = Bit (bin_minus w) empty) ≔
begin admit end;

// extra rules for bin_add
opaque symbol bin_add_BIT_11 (v w : τ ι) :
  π (w ∈ bin) →
  π (bin_add (Bit v one) (Bit w one) = NCons (bin_add v (bin_succ w)) empty) ≔
begin admit end;

opaque symbol bin_add_BIT_10 (v w : τ ι) :
  π (w ∈ bin) →
  π (bin_add (Bit v one) (Bit w empty) = NCons (bin_add v w) one) ≔
begin admit end;

opaque symbol bin_add_BIT_0 (v w y : τ ι) :
  π (w ∈ bin) → π (y ∈ bool_set) →
  π (bin_add (Bit v empty) (Bit w y) = NCons (bin_add v w) y) ≔
begin admit end;

// extra rules for bin_mult
opaque symbol bin_mult_1 (v w : τ ι) :
  π (bin_mult (Bit v one) w = bin_add (NCons (bin_mult v w) empty) w) ≔
begin admit end;

opaque symbol bin_mult_0 (v w : τ ι) :
  π (bin_mult (Bit v empty) w = NCons (bin_mult v w) empty) ≔
begin admit end;

// ===========================================================================
// Simplification rules with integer constants
// ===========================================================================

opaque symbol int_of_0 : π (int_of empty = Int0) ≔
begin admit end;

opaque symbol int_of_succ (n : τ ι) : π (int_of (succ n) = zadd Int1 (int_of n)) ≔
begin admit end;

opaque symbol zminus_0 : π (zminus Int0 = Int0) ≔
begin admit end;

opaque symbol zadd_0_intify (z : τ ι) : π (zadd Int0 z = intify z) ≔
begin admit end;

opaque symbol zadd_0_right_intify (z : τ ι) : π (zadd z Int0 = intify z) ≔
begin admit end;

opaque symbol zmult_1_intify (z : τ ι) : π (zmult Int1 z = intify z) ≔
begin admit end;

opaque symbol zmult_1_right_intify (z : τ ι) : π (zmult z Int1 = intify z) ≔
begin admit end;

opaque symbol zmult_0 (z : τ ι) : π (zmult Int0 z = Int0) ≔
begin admit end;

opaque symbol zmult_0_right (z : τ ι) : π (zmult z Int0 = Int0) ≔
begin admit end;

opaque symbol zmult_minus1 (z : τ ι) : π (zmult NegInt1 z = zminus z) ≔
begin admit end;

opaque symbol zmult_minus1_right (z : τ ι) : π (zmult z NegInt1 = zminus z) ≔
begin admit end;

// ===========================================================================
// Simplification Rules for Comparison of Binary Numbers (Thanks to Norbert Voelker)
// ===========================================================================

// Equals (=)

opaque symbol eq_integ_of_eq (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (integ_of v = integ_of w ⇔ iszero (integ_of (bin_add v (bin_minus w)))) ≔
begin admit end;

opaque symbol iszero_integ_of_Pls : π (iszero (integ_of Pls)) ≔
begin admit end;

opaque symbol nonzero_integ_of_Min : π (¬ iszero (integ_of Min)) ≔
begin admit end;

opaque symbol iszero_integ_of_BIT (w x : τ ι) :
  π (w ∈ bin) → π (x ∈ bool_set) →
  π (iszero (integ_of (Bit w x)) ⇔ (x = empty ∧ iszero (integ_of w))) ≔
begin admit end;

opaque symbol iszero_integ_of_0 (w : τ ι) :
  π (w ∈ bin) → π (iszero (integ_of (Bit w empty)) ⇔ iszero (integ_of w)) ≔
begin admit end;

opaque symbol iszero_integ_of_1 (w : τ ι) :
  π (w ∈ bin) → π (¬ iszero (integ_of (Bit w one))) ≔
begin admit end;

// Less-than (<)

opaque symbol less_integ_of_eq_neg (v w : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zless (integ_of v) (integ_of w) ⇔
     znegative (integ_of (bin_add v (bin_minus w)))) ≔
begin admit end;

opaque symbol not_neg_integ_of_Pls : π (¬ znegative (integ_of Pls)) ≔
begin admit end;

opaque symbol neg_integ_of_Min : π (znegative (integ_of Min)) ≔
begin admit end;

opaque symbol neg_integ_of_BIT (w x : τ ι) :
  π (w ∈ bin) → π (x ∈ bool_set) →
  π (znegative (integ_of (Bit w x)) ⇔ znegative (integ_of w)) ≔
begin admit end;

// Less-than-or-equals (<=)

opaque symbol le_integ_of_eq_not_less (x w : τ ι) :
  π (zle (integ_of x) (integ_of w) ⇔ ¬ zless (integ_of w) (integ_of x)) ≔
begin admit end;

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
begin admit end;

opaque symbol mult_integ_of_left (v w z : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zmult (integ_of v) (zmult (integ_of w) z) = zmult (integ_of (bin_mult v w)) z) ≔
begin admit end;

opaque symbol add_integ_of_diff1 (v w c : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zadd (integ_of v) (zdiff (integ_of w) c) = zdiff (integ_of (bin_add v w)) c) ≔
begin admit end;

opaque symbol add_integ_of_diff2 (v w c : τ ι) :
  π (v ∈ bin) → π (w ∈ bin) →
  π (zadd (integ_of v) (zdiff c (integ_of w)) =
     zadd (integ_of (bin_add v (bin_minus w))) c) ≔
begin admit end;

// ===========================================================================
// More for integer constants
// ===========================================================================

// SKIPPED: `declare int_of_0 [simp] int_of_succ [simp]` — simp-attribute
// toggle on the two facts already stated above (int_of_0, int_of_succ), no
// new content.

opaque symbol zdiff0 (x : τ ι) : π (zdiff Int0 x = zminus x) ≔
begin admit end;

opaque symbol zdiff0_right (x : τ ι) : π (zdiff x Int0 = intify x) ≔
begin admit end;

opaque symbol zdiff_self (x : τ ι) : π (zdiff x x = Int0) ≔
begin admit end;

opaque symbol znegative_iff_zless_0 (k : τ ι) :
  π (k ∈ int) → π (znegative k ⇔ zless k Int0) ≔
begin admit end;

opaque symbol zero_zless_imp_znegative_zminus (k : τ ι) :
  π (zless Int0 k) → π (k ∈ int) → π (znegative (zminus k)) ≔
begin admit end;

opaque symbol zero_zle_int_of (n : τ ι) : π (zle Int0 (int_of n)) ≔
begin admit end;

opaque symbol nat_of_0 : π (nat_of Int0 = empty) ≔
begin admit end;

opaque symbol nat_le_int0_lemma (z : τ ι) :
  π (zle z (int_of empty)) → π (z ∈ int) → π (nat_of z = empty) ≔
begin admit end;

opaque symbol nat_le_int0 (z : τ ι) :
  π (zle z (int_of empty)) → π (nat_of z = empty) ≔
begin admit end;

opaque symbol int_of_eq_0_imp_natify_eq_0 (n : τ ι) :
  π (int_of n = Int0) → π (natify n = empty) ≔
begin admit end;

opaque symbol nat_of_zminus_int_of (n : τ ι) : π (nat_of (zminus (int_of n)) = empty) ≔
begin admit end;

opaque symbol int_of_nat_of (z : τ ι) :
  π (zle Int0 z) → π (int_of (nat_of z) = intify z) ≔
begin admit end;

// SKIPPED: `declare int_of_nat_of [simp] nat_of_zminus_int_of [simp]` —
// simp-attribute toggle on the two facts just stated, no new content.

opaque symbol int_of_nat_of_if (z : τ ι) :
  π (int_of (nat_of z) = If (zle Int0 z) (intify z) Int0) ≔
begin admit end;

opaque symbol zless_nat_iff_int_zless (m z : τ ι) :
  π (m ∈ omega) → π (z ∈ int) → π (lt m (nat_of z) ⇔ zless (int_of m) z) ≔
begin admit end;

// ===========================================================================
// nat_of and zless
// ===========================================================================

// An alternative condition is $#0 ⊆ w
opaque symbol zless_nat_conj_lemma (w z : τ ι) :
  π (zless (int_of empty) z) → π (lt (nat_of w) (nat_of z) ⇔ zless w z) ≔
begin admit end;

opaque symbol zless_nat_conj (w z : τ ι) :
  π (lt (nat_of w) (nat_of z) ⇔ (zless (int_of empty) z ∧ zless w z)) ≔
begin admit end;

// SKIPPED: the commented-out `integ_of_reorient` lemma (the .thy's own
// `(* ... *)` block) — an abandoned draft with no live content ("The
// condition True is a hack to prevent looping" — the author's note
// explains why it was never enabled).

opaque symbol integ_of_minus_reorient (w x : τ ι) :
  π (integ_of w = zminus x ⇔ zminus x = integ_of w) ≔
begin admit end;

opaque symbol integ_of_add_reorient (w x y : τ ι) :
  π (integ_of w = zadd x y ⇔ zadd x y = integ_of w) ≔
begin admit end;

opaque symbol integ_of_diff_reorient (w x y : τ ι) :
  π (integ_of w = zdiff x y ⇔ zdiff x y = integ_of w) ≔
begin admit end;

opaque symbol integ_of_mult_reorient (w x y : τ ι) :
  π (integ_of w = zmult x y ⇔ zmult x y = integ_of w) ≔
begin admit end;

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
begin admit end;

opaque symbol eq_iff_zdiff_eq_0 (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (x = y ⇔ zdiff x y = Int0) ≔
begin admit end;

opaque symbol zle_iff_zdiff_zle_0 (x y : τ ι) :
  π (zle x y ⇔ zle (zdiff x y) Int0) ≔
begin admit end;

// For combine_numerals

opaque symbol left_zadd_zmult_distrib (i u j k : τ ι) :
  π (zadd (zmult i u) (zadd (zmult j u) k) = zadd (zmult (zadd i j) u) k) ≔
begin admit end;

// For cancel_numerals

opaque symbol eq_add_iff1 (i u m j n : τ ι) :
  π (zadd (zmult i u) m = zadd (zmult j u) n ⇔
     zadd (zmult (zdiff i j) u) m = intify n) ≔
begin admit end;

opaque symbol eq_add_iff2 (i u m j n : τ ι) :
  π (zadd (zmult i u) m = zadd (zmult j u) n ⇔
     intify m = zadd (zmult (zdiff j i) u) n) ≔
begin admit end;

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
begin admit end;

opaque symbol less_add_iff2 (i u m j n : τ ι) :
  π (zless (zadd (zmult i u) m) (zadd (zmult j u) n) ⇔
     zless m (zadd (zmult (zdiff j i) u) n)) ≔
begin admit end;

opaque symbol le_add_iff1 (i u m j n : τ ι) :
  π (zle (zadd (zmult i u) m) (zadd (zmult j u) n) ⇔
     zle (zadd (zmult (zdiff i j) u) m) n) ≔
begin admit end;

opaque symbol le_add_iff2 (i u m j n : τ ι) :
  π (zle (zadd (zmult i u) m) (zadd (zmult j u) n) ⇔
     zle m (zadd (zmult (zdiff j i) u) n)) ≔
begin admit end;

// SKIPPED FROM HERE ON: `ML_file "int_arith.ML"` (the numeral-literal
// cancel/combine simplification procedures, implemented in ML) and the
// trailing `simproc_setup` blocks plus the long run of
// `lemma "..." apply simp oops` demo goals at the end of Bin.thy — pure ML
// infrastructure / abandoned example goals with zero provable ZF content.
