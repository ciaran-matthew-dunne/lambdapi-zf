// ZF.Int — The Integers as Equivalence Classes Over Pairs of Natural Numbers
// Faithful SKELETON port of isabelle-src/Int.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/Int.thy.)
//
// int = (nat*nat)//intrel, built with the EquivClass quotient/congruent(2)
// machinery: raw_zminus/raw_zadd/raw_zmult are UN-lifts (Union o RepFun) of a
// per-representative-pair operation to the whole equivalence class, exactly
// as UN_equiv_class(2) in EquivClass.lp expects; zminus/zadd/zmult then
// `intify` both arguments so the operations are total on ALL sets, not just
// `int`.  Isabelle infix notation ($#, $-, $+, $*, $<, $\<le>) is rendered
// here as the plain names int_of/zminus/zadd/zmult/zless/zle per the task's
// naming convention.
//
// SKIPPED (no portable propositional content):
//   - `declare quotientE [elim!]`, `declare equiv_intrel [THEN
//     eq_equiv_class_iff, simp]`, `declare conj_cong [cong]` — these are
//     simp/elim-set attribute declarations on ALREADY-existing facts
//     (quotientE lives in EquivClass.lp; conj_cong is a generic HOL fact),
//     not new statements.
//   - `lemmas zadd_ac = zadd_assoc zadd_commute zadd_left_commute` and
//     `lemmas zmult_ac = zmult_assoc zmult_commute zmult_left_commute`: named
//     BUNDLES of pre-existing facts (AC-rewriting hint lists for `simp`), not
//     single Prop-typed statements — same precedent as `div_rls` in
//     ArithSimp.lp.
//   - `lemmas int_typechecks = int_of_type zminus_type zmagnitude_type
//     zadd_type zmult_type`: likewise a hint-list bundle, not a fact.
//   - `lemmas zcompare_rls = zdiff_def[symmetric] zadd_zdiff_eq ...`:
//     likewise a hint-list bundle ("Use with zadd_ac").
//
// GENUINE derived facts (Isabelle `lemmas foo = bar [THEN baz]`, a single
// composed fact under a fresh name — ported as fresh statements per
// CLAUDE.md, computed by chasing the combinator types):
//   - eq_intrelD = eq_equiv_class [OF _ equiv_intrel]
//   - zless_asym = zless_not_sym [THEN swap]   (the .thy's own comment gives
//     the resulting statement literally: "z $< w; ¬P ⟹ w $< z ⟹ P")
//   - zadd_zless_mono1/2, zadd_zle_mono1/2 = zadd_{right,left}_cancel_{zless,
//     zle} [THEN iffD2]  (NOTE: the .thy's inline comments for these four all
//     say "v $\<le> w ⟹ ..." even for the two $< versions — apparently a
//     copy/paste artifact in the source; the statements below follow the
//     mechanical [THEN iffD2] derivation from the named lemma, not the
//     comment text — flagged for human double-check.)
//
// NAME COLLISIONS: Isabelle allows a lemma computing a defined constant's
// value on a representative pair to share that constant's own name (e.g.
// `lemma raw_zminus: ... raw_zminus(intrel``{x,y}) = ...`, alongside
// `definition raw_zminus`).  Lambdapi symbols live in one namespace, so each
// such lemma is suffixed `_eq` here: raw_zminus_eq, zminus_eq, znegative_eq,
// raw_nat_of_eq, raw_zadd_eq, zadd_eq, raw_zmult_eq, zmult_eq.  (Flagged:
// check.py's --missing name-matching will see the *definition* symbol of the
// same base name and count these as "present" even though the lemma content
// lives under the `_eq`-suffixed name — a tooling blind spot, not a gap.)

require open ZF.ZF_Base ZF.upair ZF.pair ZF.Ordinal ZF.Nat_ZF ZF.Arith
             ZF.EquivClass;

// ===========================================================================
// Definitions
// ===========================================================================

// intrel ≡ {p ∈ (nat*nat)*(nat*nat). ∃x1 y1 x2 y2. p=⟨⟨x1,y1⟩,⟨x2,y2⟩⟩ ∧ x1+y2=x2+y1}
symbol intrel : τ ι ≔
  Collect (Sigma (Sigma omega (λ _, omega)) (λ _, Sigma omega (λ _, omega)))
    (λ p, `∃ (x1 : τ ι), `∃ (y1 : τ ι), `∃ (x2 : τ ι), `∃ (y2 : τ ι),
      p = Pair (Pair x1 y1) (Pair x2 y2) ∧ add x1 y2 = add x2 y1);

// int ≡ (nat*nat)//intrel
symbol int : τ ι ≔ quotient (Sigma omega (λ _, omega)) intrel;

// $# m ≡ intrel``{⟨natify(m),0⟩}   (coercion from nat to int)
symbol int_of (m : τ ι) : τ ι ≔ rel_image_sing intrel (Pair (natify m) empty);

// intify(m) ≡ if m ∈ int then m else $#0   (coercion from ANYTHING to int)
symbol intify (m : τ ι) : τ ι ≔ If (m ∈ int) m (int_of empty);

// raw_zminus(z) ≡ ⋃⟨x,y⟩∈z. intrel``{⟨y,x⟩}
symbol raw_zminus (z : τ ι) : τ ι ≔
  Union (RepFun z (λ p, rel_image_sing intrel (Pair (snd p) (fst p))));

// $- z ≡ raw_zminus(intify(z))
symbol zminus (z : τ ι) : τ ι ≔ raw_zminus (intify z);

// znegative(z) ≡ ∃x y. x<y ∧ y∈nat ∧ ⟨x,y⟩∈z
symbol znegative (z : τ ι) : Prop ≔
  `∃ (x : τ ι), `∃ (y : τ ι), lt x y ∧ y ∈ omega ∧ Pair x y ∈ z;

// iszero(z) ≡ z = $#0
symbol iszero (z : τ ι) : Prop ≔ z = int_of empty;

// raw_nat_of(z) ≡ natify(⋃⟨x,y⟩∈z. x#-y)
symbol raw_nat_of (z : τ ι) : τ ι ≔
  natify (Union (RepFun z (λ p, diff (fst p) (snd p))));

// nat_of(z) ≡ raw_nat_of(intify(z))
symbol nat_of (z : τ ι) : τ ι ≔ raw_nat_of (intify z);

// zmagnitude(z) ≡ THE m. m∈nat ∧ ((¬znegative(z) ∧ z=$#m) | (znegative(z) ∧ $-z=$#m))
symbol zmagnitude (z : τ ι) : τ ι ≔
  The (λ m, m ∈ omega ∧
    ((¬ znegative z ∧ z = int_of m) ∨ (znegative z ∧ zminus z = int_of m)));

// raw_zmult(z1,z2) ≡ ⋃p1∈z1. ⋃p2∈z2.
//   split(λx1 y1. split(λx2 y2. intrel``{⟨x1*x2+y1*y2, x1*y2+y1*x2⟩}, p2), p1)
symbol raw_zmult (z1 z2 : τ ι) : τ ι ≔
  Union (RepFun z1 (λ p1, Union (RepFun z2 (λ p2,
    rel_image_sing intrel (Pair
      (add (mult (fst p1) (fst p2)) (mult (snd p1) (snd p2)))
      (add (mult (fst p1) (snd p2)) (mult (snd p1) (fst p2))))))));

// z1 $* z2 ≡ raw_zmult(intify(z1),intify(z2))
symbol zmult (z1 z2 : τ ι) : τ ι ≔ raw_zmult (intify z1) (intify z2);

// raw_zadd(z1,z2) ≡ ⋃z1∈z1. ⋃z2∈z2. let ⟨x1,y1⟩=z1;⟨x2,y2⟩=z2 in intrel``{⟨x1+x2,y1+y2⟩}
symbol raw_zadd (z1 z2 : τ ι) : τ ι ≔
  Union (RepFun z1 (λ p1, Union (RepFun z2 (λ p2,
    rel_image_sing intrel (Pair (add (fst p1) (fst p2)) (add (snd p1) (snd p2)))))));

// z1 $+ z2 ≡ raw_zadd(intify(z1),intify(z2))
symbol zadd (z1 z2 : τ ι) : τ ι ≔ raw_zadd (intify z1) (intify z2);

// z1 $- z2 ≡ z1 $+ zminus(z2)
symbol zdiff (z1 z2 : τ ι) : τ ι ≔ zadd z1 (zminus z2);

// z1 $< z2 ≡ znegative(z1 $- z2)
symbol zless (z1 z2 : τ ι) : Prop ≔ znegative (zdiff z1 z2);

// z1 $≤ z2 ≡ z1 $< z2 | intify(z1)=intify(z2)
symbol zle (z1 z2 : τ ι) : Prop ≔ zless z1 z2 ∨ intify z1 = intify z2;

// ===========================================================================
// Proving that intrel is an equivalence relation
// ===========================================================================

opaque symbol intrel_iff (x1 y1 x2 y2 : τ ι) :
  π (Pair (Pair x1 y1) (Pair x2 y2) ∈ intrel ⇔
     (x1 ∈ omega ∧ y1 ∈ omega ∧ x2 ∈ omega ∧ y2 ∈ omega ∧ add x1 y2 = add x2 y1)) ≔
begin admit end;

opaque symbol intrelI (x1 y1 x2 y2 : τ ι) :
  π (add x1 y2 = add x2 y1) → π (x1 ∈ omega) → π (y1 ∈ omega) →
  π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (Pair (Pair x1 y1) (Pair x2 y2) ∈ intrel) ≔
begin admit end;

opaque symbol intrelE (p : τ ι) (Q : Prop) :
  π (p ∈ intrel) →
  (Π (x1 y1 x2 y2 : τ ι), π (p = Pair (Pair x1 y1) (Pair x2 y2)) →
    π (add x1 y2 = add x2 y1) → π (x1 ∈ omega) → π (y1 ∈ omega) →
    π (x2 ∈ omega) → π (y2 ∈ omega) → π Q) →
  π Q ≔
begin admit end;

opaque symbol int_trans_lemma (x1 y1 x2 y2 x3 y3 : τ ι) :
  π (add x1 y2 = add x2 y1) → π (add x2 y3 = add x3 y2) →
  π (add x1 y3 = add x3 y1) ≔
begin admit end;

opaque symbol equiv_intrel :
  π (equiv (Sigma omega (λ _, omega)) intrel) ≔
begin admit end;

opaque symbol image_intrel_int (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (rel_image_sing intrel (Pair m n) ∈ int) ≔
begin admit end;

// eq_intrelD = eq_equiv_class [OF _ equiv_intrel]
opaque symbol eq_intrelD (a b : τ ι) :
  π (rel_image_sing intrel a = rel_image_sing intrel b) →
  π (b ∈ Sigma omega (λ _, omega)) →
  π (Pair a b ∈ intrel) ≔
begin admit end;

// ===========================================================================
// int_of: the injection from nat to int
// ===========================================================================

opaque symbol int_of_type (m : τ ι) : π (int_of m ∈ int) ≔
begin admit end;

opaque symbol int_of_eq (m n : τ ι) :
  π (int_of m = int_of n ⇔ natify m = natify n) ≔
begin admit end;

opaque symbol int_of_inject (m n : τ ι) :
  π (int_of m = int_of n) → π (m ∈ omega) → π (n ∈ omega) → π (m = n) ≔
begin admit end;

// ===========================================================================
// intify: coercion from anything to int
// ===========================================================================

opaque symbol intify_in_int (x : τ ι) : π (intify x ∈ int) ≔
begin admit end;

opaque symbol intify_ident (n : τ ι) : π (n ∈ int) → π (intify n = n) ≔
begin admit end;

// ===========================================================================
// Collapsing rules: to remove intify from arithmetic expressions
// ===========================================================================

opaque symbol intify_idem (x : τ ι) : π (intify (intify x) = intify x) ≔
begin admit end;

opaque symbol int_of_natify (m : τ ι) : π (int_of (natify m) = int_of m) ≔
begin admit end;

opaque symbol zminus_intify (m : τ ι) : π (zminus (intify m) = zminus m) ≔
begin admit end;

// Addition
opaque symbol zadd_intify1 (x y : τ ι) : π (zadd (intify x) y = zadd x y) ≔
begin admit end;

opaque symbol zadd_intify2 (x y : τ ι) : π (zadd x (intify y) = zadd x y) ≔
begin admit end;

// Subtraction
opaque symbol zdiff_intify1 (x y : τ ι) : π (zdiff (intify x) y = zdiff x y) ≔
begin admit end;

opaque symbol zdiff_intify2 (x y : τ ι) : π (zdiff x (intify y) = zdiff x y) ≔
begin admit end;

// Multiplication
opaque symbol zmult_intify1 (x y : τ ι) : π (zmult (intify x) y = zmult x y) ≔
begin admit end;

opaque symbol zmult_intify2 (x y : τ ι) : π (zmult x (intify y) = zmult x y) ≔
begin admit end;

// Orderings
opaque symbol zless_intify1 (x y : τ ι) : π (zless (intify x) y ⇔ zless x y) ≔
begin admit end;

opaque symbol zless_intify2 (x y : τ ι) : π (zless x (intify y) ⇔ zless x y) ≔
begin admit end;

opaque symbol zle_intify1 (x y : τ ι) : π (zle (intify x) y ⇔ zle x y) ≔
begin admit end;

opaque symbol zle_intify2 (x y : τ ι) : π (zle x (intify y) ⇔ zle x y) ≔
begin admit end;

// ===========================================================================
// zminus: unary negation on int
// ===========================================================================

opaque symbol zminus_congruent :
  π (congruent intrel (λ p, rel_image_sing intrel (Pair (snd p) (fst p)))) ≔
begin admit end;

opaque symbol raw_zminus_type (z : τ ι) : π (z ∈ int) → π (raw_zminus z ∈ int) ≔
begin admit end;

opaque symbol zminus_type (z : τ ι) : π (zminus z ∈ int) ≔
begin admit end;

opaque symbol raw_zminus_inject (z w : τ ι) :
  π (raw_zminus z = raw_zminus w) → π (z ∈ int) → π (w ∈ int) → π (z = w) ≔
begin admit end;

opaque symbol zminus_inject_intify (z w : τ ι) :
  π (zminus z = zminus w) → π (intify z = intify w) ≔
begin admit end;

opaque symbol zminus_inject (z w : τ ι) :
  π (zminus z = zminus w) → π (z ∈ int) → π (w ∈ int) → π (z = w) ≔
begin admit end;

// raw_zminus (name collision with the `raw_zminus` definition; see header)
opaque symbol raw_zminus_eq (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) →
  π (raw_zminus (rel_image_sing intrel (Pair x y)) = rel_image_sing intrel (Pair y x)) ≔
begin admit end;

// zminus (name collision with the `zminus` definition; see header)
opaque symbol zminus_eq (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) →
  π (zminus (rel_image_sing intrel (Pair x y)) = rel_image_sing intrel (Pair y x)) ≔
begin admit end;

opaque symbol raw_zminus_zminus (z : τ ι) :
  π (z ∈ int) → π (raw_zminus (raw_zminus z) = z) ≔
begin admit end;

opaque symbol zminus_zminus_intify (z : τ ι) :
  π (zminus (zminus z) = intify z) ≔
begin admit end;

opaque symbol zminus_int0 : π (zminus (int_of empty) = int_of empty) ≔
begin admit end;

opaque symbol zminus_zminus (z : τ ι) : π (z ∈ int) → π (zminus (zminus z) = z) ≔
begin admit end;

// ===========================================================================
// znegative: the test for negative integers
// ===========================================================================

// znegative (name collision with the `znegative` definition; see header)
opaque symbol znegative_eq (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) →
  π (znegative (rel_image_sing intrel (Pair x y)) ⇔ lt x y) ≔
begin admit end;

// No natural number is negative!
opaque symbol not_znegative_int_of (n : τ ι) : π (¬ znegative (int_of n)) ≔
begin admit end;

opaque symbol znegative_zminus_int_of (n : τ ι) :
  π (znegative (zminus (int_of (succ n)))) ≔
begin admit end;

opaque symbol not_znegative_imp_zero (n : τ ι) :
  π (¬ znegative (zminus (int_of n))) → π (natify n = empty) ≔
begin admit end;

// ===========================================================================
// nat_of: Coercion of an Integer to a Natural Number
// ===========================================================================

opaque symbol nat_of_intify (z : τ ι) : π (nat_of (intify z) = nat_of z) ≔
begin admit end;

opaque symbol nat_of_congruent :
  π (congruent intrel (λ p, diff (fst p) (snd p))) ≔
begin admit end;

// raw_nat_of (name collision with the `raw_nat_of` definition; see header)
opaque symbol raw_nat_of_eq (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) →
  π (raw_nat_of (rel_image_sing intrel (Pair x y)) = diff x y) ≔
begin admit end;

opaque symbol raw_nat_of_int_of (n : τ ι) : π (raw_nat_of (int_of n) = natify n) ≔
begin admit end;

opaque symbol nat_of_int_of (n : τ ι) : π (nat_of (int_of n) = natify n) ≔
begin admit end;

opaque symbol raw_nat_of_type (z : τ ι) : π (raw_nat_of z ∈ omega) ≔
begin admit end;

opaque symbol nat_of_type (z : τ ι) : π (nat_of z ∈ omega) ≔
begin admit end;

// ===========================================================================
// zmagnitude: magnitude of an integer, as a natural number
// ===========================================================================

opaque symbol zmagnitude_int_of (n : τ ι) : π (zmagnitude (int_of n) = natify n) ≔
begin admit end;

opaque symbol natify_int_of_eq (x n : τ ι) :
  π (natify x = n) → π (int_of x = int_of n) ≔
begin admit end;

opaque symbol zmagnitude_zminus_int_of (n : τ ι) :
  π (zmagnitude (zminus (int_of n)) = natify n) ≔
begin admit end;

opaque symbol zmagnitude_type (z : τ ι) : π (zmagnitude z ∈ omega) ≔
begin admit end;

opaque symbol not_zneg_int_of (z : τ ι) :
  π (z ∈ int) → π (¬ znegative z) → π (Bex omega (λ n, z = int_of n)) ≔
begin admit end;

opaque symbol not_zneg_mag (z : τ ι) :
  π (z ∈ int) → π (¬ znegative z) → π (int_of (zmagnitude z) = z) ≔
begin admit end;

opaque symbol zneg_int_of (z : τ ι) :
  π (znegative z) → π (z ∈ int) → π (Bex omega (λ n, z = zminus (int_of (succ n)))) ≔
begin admit end;

opaque symbol zneg_mag (z : τ ι) :
  π (znegative z) → π (z ∈ int) → π (int_of (zmagnitude z) = zminus z) ≔
begin admit end;

opaque symbol int_cases (z : τ ι) :
  π (z ∈ int) → π (Bex omega (λ n, z = int_of n ∨ z = zminus (int_of (succ n)))) ≔
begin admit end;

opaque symbol not_zneg_raw_nat_of (z : τ ι) :
  π (¬ znegative z) → π (z ∈ int) → π (int_of (raw_nat_of z) = z) ≔
begin admit end;

opaque symbol not_zneg_nat_of_intify (z : τ ι) :
  π (¬ znegative (intify z)) → π (int_of (nat_of z) = intify z) ≔
begin admit end;

opaque symbol not_zneg_nat_of (z : τ ι) :
  π (¬ znegative z) → π (z ∈ int) → π (int_of (nat_of z) = z) ≔
begin admit end;

opaque symbol zneg_nat_of (z : τ ι) :
  π (znegative (intify z)) → π (nat_of z = empty) ≔
begin admit end;

// ===========================================================================
// zadd: addition on int
// ===========================================================================

// Congruence Property for Addition
opaque symbol zadd_congruent2 :
  π (congruent2 intrel intrel (λ z1 z2,
    rel_image_sing intrel (Pair (add (fst z1) (fst z2)) (add (snd z1) (snd z2))))) ≔
begin admit end;

opaque symbol raw_zadd_type (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (raw_zadd z w ∈ int) ≔
begin admit end;

opaque symbol zadd_type (z w : τ ι) : π (zadd z w ∈ int) ≔
begin admit end;

// raw_zadd (name collision with the `raw_zadd` definition; see header)
opaque symbol raw_zadd_eq (x1 y1 x2 y2 : τ ι) :
  π (x1 ∈ omega) → π (y1 ∈ omega) → π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (raw_zadd (rel_image_sing intrel (Pair x1 y1)) (rel_image_sing intrel (Pair x2 y2))
     = rel_image_sing intrel (Pair (add x1 x2) (add y1 y2))) ≔
begin admit end;

// zadd (name collision with the `zadd` definition; see header)
opaque symbol zadd_eq (x1 y1 x2 y2 : τ ι) :
  π (x1 ∈ omega) → π (y1 ∈ omega) → π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (zadd (rel_image_sing intrel (Pair x1 y1)) (rel_image_sing intrel (Pair x2 y2))
     = rel_image_sing intrel (Pair (add x1 x2) (add y1 y2))) ≔
begin admit end;

opaque symbol raw_zadd_int0 (z : τ ι) :
  π (z ∈ int) → π (raw_zadd (int_of empty) z = z) ≔
begin admit end;

opaque symbol zadd_int0_intify (z : τ ι) :
  π (zadd (int_of empty) z = intify z) ≔
begin admit end;

opaque symbol zadd_int0 (z : τ ι) : π (z ∈ int) → π (zadd (int_of empty) z = z) ≔
begin admit end;

opaque symbol raw_zminus_zadd_distrib (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) →
  π (zminus (raw_zadd z w) = raw_zadd (zminus z) (zminus w)) ≔
begin admit end;

opaque symbol zminus_zadd_distrib (z w : τ ι) :
  π (zminus (zadd z w) = zadd (zminus z) (zminus w)) ≔
begin admit end;

opaque symbol raw_zadd_commute (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (raw_zadd z w = raw_zadd w z) ≔
begin admit end;

opaque symbol zadd_commute (z w : τ ι) : π (zadd z w = zadd w z) ≔
begin admit end;

opaque symbol raw_zadd_assoc (z1 z2 z3 : τ ι) :
  π (z1 ∈ int) → π (z2 ∈ int) → π (z3 ∈ int) →
  π (raw_zadd (raw_zadd z1 z2) z3 = raw_zadd z1 (raw_zadd z2 z3)) ≔
begin admit end;

opaque symbol zadd_assoc (z1 z2 z3 : τ ι) :
  π (zadd (zadd z1 z2) z3 = zadd z1 (zadd z2 z3)) ≔
begin admit end;

// For AC rewriting
opaque symbol zadd_left_commute (z1 z2 z3 : τ ι) :
  π (zadd z1 (zadd z2 z3) = zadd z2 (zadd z1 z3)) ≔
begin admit end;

// (Integer addition is an AC operator: `lemmas zadd_ac = zadd_assoc
// zadd_commute zadd_left_commute` — a hint-list bundle, skipped; see header.)

opaque symbol int_of_add (m n : τ ι) :
  π (int_of (add m n) = zadd (int_of m) (int_of n)) ≔
begin admit end;

opaque symbol int_succ_int_1 (m : τ ι) :
  π (int_of (succ m) = zadd (int_of (succ empty)) (int_of m)) ≔
begin admit end;

opaque symbol int_of_diff (m n : τ ι) :
  π (m ∈ omega) → π (le n m) → π (int_of (diff m n) = zdiff (int_of m) (int_of n)) ≔
begin admit end;

opaque symbol raw_zadd_zminus_inverse (z : τ ι) :
  π (z ∈ int) → π (raw_zadd z (zminus z) = int_of empty) ≔
begin admit end;

opaque symbol zadd_zminus_inverse (z : τ ι) :
  π (zadd z (zminus z) = int_of empty) ≔
begin admit end;

opaque symbol zadd_zminus_inverse2 (z : τ ι) :
  π (zadd (zminus z) z = int_of empty) ≔
begin admit end;

opaque symbol zadd_int0_right_intify (z : τ ι) :
  π (zadd z (int_of empty) = intify z) ≔
begin admit end;

opaque symbol zadd_int0_right (z : τ ι) :
  π (z ∈ int) → π (zadd z (int_of empty) = z) ≔
begin admit end;

// ===========================================================================
// zmult: Integer Multiplication
// ===========================================================================

// Congruence property for multiplication
opaque symbol zmult_congruent2 :
  π (congruent2 intrel intrel (λ p1 p2,
    rel_image_sing intrel (Pair
      (add (mult (fst p1) (fst p2)) (mult (snd p1) (snd p2)))
      (add (mult (fst p1) (snd p2)) (mult (snd p1) (fst p2)))))) ≔
begin admit end;

opaque symbol raw_zmult_type (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (raw_zmult z w ∈ int) ≔
begin admit end;

opaque symbol zmult_type (z w : τ ι) : π (zmult z w ∈ int) ≔
begin admit end;

// raw_zmult (name collision with the `raw_zmult` definition; see header)
opaque symbol raw_zmult_eq (x1 y1 x2 y2 : τ ι) :
  π (x1 ∈ omega) → π (y1 ∈ omega) → π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (raw_zmult (rel_image_sing intrel (Pair x1 y1)) (rel_image_sing intrel (Pair x2 y2))
     = rel_image_sing intrel
         (Pair (add (mult x1 x2) (mult y1 y2)) (add (mult x1 y2) (mult y1 x2)))) ≔
begin admit end;

// zmult (name collision with the `zmult` definition; see header)
opaque symbol zmult_eq (x1 y1 x2 y2 : τ ι) :
  π (x1 ∈ omega) → π (y1 ∈ omega) → π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (zmult (rel_image_sing intrel (Pair x1 y1)) (rel_image_sing intrel (Pair x2 y2))
     = rel_image_sing intrel
         (Pair (add (mult x1 x2) (mult y1 y2)) (add (mult x1 y2) (mult y1 x2)))) ≔
begin admit end;

opaque symbol raw_zmult_int0 (z : τ ι) :
  π (z ∈ int) → π (raw_zmult (int_of empty) z = int_of empty) ≔
begin admit end;

opaque symbol zmult_int0 (z : τ ι) : π (zmult (int_of empty) z = int_of empty) ≔
begin admit end;

opaque symbol raw_zmult_int1 (z : τ ι) :
  π (z ∈ int) → π (raw_zmult (int_of (succ empty)) z = z) ≔
begin admit end;

opaque symbol zmult_int1_intify (z : τ ι) :
  π (zmult (int_of (succ empty)) z = intify z) ≔
begin admit end;

opaque symbol zmult_int1 (z : τ ι) :
  π (z ∈ int) → π (zmult (int_of (succ empty)) z = z) ≔
begin admit end;

opaque symbol raw_zmult_commute (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (raw_zmult z w = raw_zmult w z) ≔
begin admit end;

opaque symbol zmult_commute (z w : τ ι) : π (zmult z w = zmult w z) ≔
begin admit end;

opaque symbol raw_zmult_zminus (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) →
  π (raw_zmult (zminus z) w = zminus (raw_zmult z w)) ≔
begin admit end;

opaque symbol zmult_zminus (z w : τ ι) :
  π (zmult (zminus z) w = zminus (zmult z w)) ≔
begin admit end;

opaque symbol zmult_zminus_right (w z : τ ι) :
  π (zmult w (zminus z) = zminus (zmult w z)) ≔
begin admit end;

opaque symbol raw_zmult_assoc (z1 z2 z3 : τ ι) :
  π (z1 ∈ int) → π (z2 ∈ int) → π (z3 ∈ int) →
  π (raw_zmult (raw_zmult z1 z2) z3 = raw_zmult z1 (raw_zmult z2 z3)) ≔
begin admit end;

opaque symbol zmult_assoc (z1 z2 z3 : τ ι) :
  π (zmult (zmult z1 z2) z3 = zmult z1 (zmult z2 z3)) ≔
begin admit end;

// For AC rewriting
opaque symbol zmult_left_commute (z1 z2 z3 : τ ι) :
  π (zmult z1 (zmult z2 z3) = zmult z2 (zmult z1 z3)) ≔
begin admit end;

// (Integer multiplication is an AC operator: `lemmas zmult_ac = zmult_assoc
// zmult_commute zmult_left_commute` — a hint-list bundle, skipped.)

opaque symbol raw_zadd_zmult_distrib (z1 z2 w : τ ι) :
  π (z1 ∈ int) → π (z2 ∈ int) → π (w ∈ int) →
  π (raw_zmult (raw_zadd z1 z2) w = raw_zadd (raw_zmult z1 w) (raw_zmult z2 w)) ≔
begin admit end;

opaque symbol zadd_zmult_distrib (z1 z2 w : τ ι) :
  π (zmult (zadd z1 z2) w = zadd (zmult z1 w) (zmult z2 w)) ≔
begin admit end;

opaque symbol zadd_zmult_distrib2 (w z1 z2 : τ ι) :
  π (zmult w (zadd z1 z2) = zadd (zmult w z1) (zmult w z2)) ≔
begin admit end;

// (`lemmas int_typechecks = int_of_type zminus_type zmagnitude_type
// zadd_type zmult_type` — a hint-list bundle, skipped; see header.)

// ===========================================================================
// Subtraction laws
// ===========================================================================

opaque symbol zdiff_type (z w : τ ι) : π (zdiff z w ∈ int) ≔
begin admit end;

opaque symbol zminus_zdiff_eq (z y : τ ι) : π (zminus (zdiff z y) = zdiff y z) ≔
begin admit end;

opaque symbol zdiff_zmult_distrib (z1 z2 w : τ ι) :
  π (zmult (zdiff z1 z2) w = zdiff (zmult z1 w) (zmult z2 w)) ≔
begin admit end;

opaque symbol zdiff_zmult_distrib2 (w z1 z2 : τ ι) :
  π (zmult w (zdiff z1 z2) = zdiff (zmult w z1) (zmult w z2)) ≔
begin admit end;

opaque symbol zadd_zdiff_eq (x y z : τ ι) :
  π (zadd x (zdiff y z) = zdiff (zadd x y) z) ≔
begin admit end;

opaque symbol zdiff_zadd_eq (x y z : τ ι) :
  π (zadd (zdiff x y) z = zdiff (zadd x z) y) ≔
begin admit end;

// ===========================================================================
// The "Less Than" Relation
// ===========================================================================

// "Less than" is a linear ordering
opaque symbol zless_linear_lemma (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (zless z w ∨ z = w ∨ zless w z) ≔
begin admit end;

opaque symbol zless_linear (z w : τ ι) :
  π (zless z w ∨ intify z = intify w ∨ zless w z) ≔
begin admit end;

opaque symbol zless_not_refl (z : τ ι) : π (¬ zless z z) ≔
begin admit end;

opaque symbol neq_iff_zless (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (x ≠ y ⇔ (zless x y ∨ zless y x)) ≔
begin admit end;

opaque symbol zless_imp_intify_neq (w z : τ ι) :
  π (zless w z) → π (intify w ≠ intify z) ≔
begin admit end;

// This lemma allows direct proofs of other <-properties
opaque symbol zless_imp_succ_zadd_lemma (w z : τ ι) :
  π (zless w z) → π (w ∈ int) → π (z ∈ int) →
  π (Bex omega (λ n, z = zadd w (int_of (succ n)))) ≔
begin admit end;

opaque symbol zless_imp_succ_zadd (w z : τ ι) :
  π (zless w z) → π (Bex omega (λ n, zadd w (int_of (succ n)) = intify z)) ≔
begin admit end;

opaque symbol zless_succ_zadd_lemma (w n : τ ι) :
  π (w ∈ int) → π (zless w (zadd w (int_of (succ n)))) ≔
begin admit end;

opaque symbol zless_succ_zadd (w n : τ ι) :
  π (zless w (zadd w (int_of (succ n)))) ≔
begin admit end;

opaque symbol zless_iff_succ_zadd (w z : τ ι) :
  π (zless w z ⇔ Bex omega (λ n, zadd w (int_of (succ n)) = intify z)) ≔
begin admit end;

opaque symbol zless_int_of (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (zless (int_of m) (int_of n) ⇔ lt m n) ≔
begin admit end;

opaque symbol zless_trans_lemma (x y z : τ ι) :
  π (zless x y) → π (zless y z) → π (x ∈ int) → π (y ∈ int) → π (z ∈ int) →
  π (zless x z) ≔
begin admit end;

opaque symbol zless_trans (x y z : τ ι) :
  π (zless x y) → π (zless y z) → π (zless x z) ≔
begin admit end;

opaque symbol zless_not_sym (z w : τ ι) : π (zless z w) → π (¬ zless w z) ≔
begin admit end;

// zless_asym = zless_not_sym [THEN swap] : ⟦z $< w; ¬P ⟹ w $< z⟧ ⟹ P
opaque symbol zless_asym (z w : τ ι) (P : Prop) :
  π (zless z w) → (π (¬ P) → π (zless w z)) → π P ≔
begin admit end;

opaque symbol zless_imp_zle (z w : τ ι) : π (zless z w) → π (zle z w) ≔
begin admit end;

opaque symbol zle_linear (z w : τ ι) : π (zle z w ∨ zle w z) ≔
begin admit end;

// ===========================================================================
// Less Than or Equals
// ===========================================================================

opaque symbol zle_refl (z : τ ι) : π (zle z z) ≔
begin admit end;

opaque symbol zle_eq_refl (x y : τ ι) : π (x = y) → π (zle x y) ≔
begin admit end;

opaque symbol zle_anti_sym_intify (x y : τ ι) :
  π (zle x y) → π (zle y x) → π (intify x = intify y) ≔
begin admit end;

opaque symbol zle_anti_sym (x y : τ ι) :
  π (zle x y) → π (zle y x) → π (x ∈ int) → π (y ∈ int) → π (x = y) ≔
begin admit end;

opaque symbol zle_trans_lemma (x y z : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (z ∈ int) → π (zle x y) → π (zle y z) →
  π (zle x z) ≔
begin admit end;

opaque symbol zle_trans (x y z : τ ι) :
  π (zle x y) → π (zle y z) → π (zle x z) ≔
begin admit end;

opaque symbol zle_zless_trans (i j k : τ ι) :
  π (zle i j) → π (zless j k) → π (zless i k) ≔
begin admit end;

opaque symbol zless_zle_trans (i j k : τ ι) :
  π (zless i j) → π (zle j k) → π (zless i k) ≔
begin admit end;

opaque symbol not_zless_iff_zle (z w : τ ι) : π (¬ zless z w ⇔ zle w z) ≔
begin admit end;

opaque symbol not_zle_iff_zless (z w : τ ι) : π (¬ zle z w ⇔ zless w z) ≔
begin admit end;

// ===========================================================================
// More subtraction laws (for zcompare_rls)
// ===========================================================================

opaque symbol zdiff_zdiff_eq (x y z : τ ι) :
  π (zdiff (zdiff x y) z = zdiff x (zadd y z)) ≔
begin admit end;

opaque symbol zdiff_zdiff_eq2 (x y z : τ ι) :
  π (zdiff x (zdiff y z) = zdiff (zadd x z) y) ≔
begin admit end;

opaque symbol zdiff_zless_iff (x y z : τ ι) :
  π (zless (zdiff x y) z ⇔ zless x (zadd z y)) ≔
begin admit end;

opaque symbol zless_zdiff_iff (x y z : τ ι) :
  π (zless x (zdiff z y) ⇔ zless (zadd x y) z) ≔
begin admit end;

opaque symbol zdiff_eq_iff (x y z : τ ι) :
  π (x ∈ int) → π (z ∈ int) → π (zdiff x y = z ⇔ x = zadd z y) ≔
begin admit end;

opaque symbol eq_zdiff_iff (x y z : τ ι) :
  π (x ∈ int) → π (z ∈ int) → π (x = zdiff z y ⇔ zadd x y = z) ≔
begin admit end;

opaque symbol zdiff_zle_iff_lemma (x y z : τ ι) :
  π (x ∈ int) → π (z ∈ int) → π (zle (zdiff x y) z ⇔ zle x (zadd z y)) ≔
begin admit end;

opaque symbol zdiff_zle_iff (x y z : τ ι) :
  π (zle (zdiff x y) z ⇔ zle x (zadd z y)) ≔
begin admit end;

opaque symbol zle_zdiff_iff_lemma (x y z : τ ι) :
  π (x ∈ int) → π (z ∈ int) → π (zle x (zdiff z y) ⇔ zle (zadd x y) z) ≔
begin admit end;

opaque symbol zle_zdiff_iff (x y z : τ ι) :
  π (zle x (zdiff z y) ⇔ zle (zadd x y) z) ≔
begin admit end;

// (`lemmas zcompare_rls = zdiff_def[symmetric] zadd_zdiff_eq zdiff_zadd_eq
// zdiff_zdiff_eq zdiff_zdiff_eq2 zdiff_zless_iff zless_zdiff_iff
// zdiff_zle_iff zle_zdiff_iff zdiff_eq_iff eq_zdiff_iff` — a hint-list
// bundle ("Use with zadd_ac"), skipped; see header.)

// ===========================================================================
// Monotonicity and Cancellation Results for Instantiation of the
// CancelNumerals Simprocs
// ===========================================================================

opaque symbol zadd_left_cancel (w w' z : τ ι) :
  π (w ∈ int) → π (w' ∈ int) → π (zadd z w' = zadd z w ⇔ w' = w) ≔
begin admit end;

opaque symbol zadd_left_cancel_intify (w w' z : τ ι) :
  π (zadd z w' = zadd z w ⇔ intify w' = intify w) ≔
begin admit end;

opaque symbol zadd_right_cancel (w w' z : τ ι) :
  π (w ∈ int) → π (w' ∈ int) → π (zadd w' z = zadd w z ⇔ w' = w) ≔
begin admit end;

opaque symbol zadd_right_cancel_intify (w w' z : τ ι) :
  π (zadd w' z = zadd w z ⇔ intify w' = intify w) ≔
begin admit end;

opaque symbol zadd_right_cancel_zless (w w' z : τ ι) :
  π (zless (zadd w' z) (zadd w z) ⇔ zless w' w) ≔
begin admit end;

opaque symbol zadd_left_cancel_zless (w w' z : τ ι) :
  π (zless (zadd z w') (zadd z w) ⇔ zless w' w) ≔
begin admit end;

opaque symbol zadd_right_cancel_zle (w w' z : τ ι) :
  π (zle (zadd w' z) (zadd w z) ⇔ zle w' w) ≔
begin admit end;

opaque symbol zadd_left_cancel_zle (w w' z : τ ι) :
  π (zle (zadd z w') (zadd z w) ⇔ zle w' w) ≔
begin admit end;

// zadd_zless_mono1 = zadd_right_cancel_zless [THEN iffD2] : v $< w ⟹ v$+z $< w$+z
opaque symbol zadd_zless_mono1 (v w z : τ ι) :
  π (zless v w) → π (zless (zadd v z) (zadd w z)) ≔
begin admit end;

// zadd_zless_mono2 = zadd_left_cancel_zless [THEN iffD2] : v $< w ⟹ z$+v $< z$+w
opaque symbol zadd_zless_mono2 (v w z : τ ι) :
  π (zless v w) → π (zless (zadd z v) (zadd z w)) ≔
begin admit end;

// zadd_zle_mono1 = zadd_right_cancel_zle [THEN iffD2] : v $≤ w ⟹ v$+z $≤ w$+z
opaque symbol zadd_zle_mono1 (v w z : τ ι) :
  π (zle v w) → π (zle (zadd v z) (zadd w z)) ≔
begin admit end;

// zadd_zle_mono2 = zadd_left_cancel_zle [THEN iffD2] : v $≤ w ⟹ z$+v $≤ z$+w
opaque symbol zadd_zle_mono2 (v w z : τ ι) :
  π (zle v w) → π (zle (zadd z v) (zadd z w)) ≔
begin admit end;

opaque symbol zadd_zle_mono (w w' z z' : τ ι) :
  π (zle w' w) → π (zle z' z) → π (zle (zadd w' z') (zadd w z)) ≔
begin admit end;

opaque symbol zadd_zless_mono (w w' z z' : τ ι) :
  π (zless w' w) → π (zle z' z) → π (zless (zadd w' z') (zadd w z)) ≔
begin admit end;

// ===========================================================================
// Comparison laws
// ===========================================================================

opaque symbol zminus_zless_zminus (x y : τ ι) :
  π (zless (zminus x) (zminus y) ⇔ zless y x) ≔
begin admit end;

opaque symbol zminus_zle_zminus (x y : τ ι) :
  π (zle (zminus x) (zminus y) ⇔ zle y x) ≔
begin admit end;

// More inequality lemmas

opaque symbol equation_zminus (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (x = zminus y ⇔ y = zminus x) ≔
begin admit end;

opaque symbol zminus_equation (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (zminus x = y ⇔ zminus y = x) ≔
begin admit end;

opaque symbol equation_zminus_intify (x y : τ ι) :
  π (intify x = zminus y ⇔ intify y = zminus x) ≔
begin admit end;

opaque symbol zminus_equation_intify (x y : τ ι) :
  π (zminus x = intify y ⇔ zminus y = intify x) ≔
begin admit end;

// The next several equations are permutative: watch out!

opaque symbol zless_zminus (x y : τ ι) :
  π (zless x (zminus y) ⇔ zless y (zminus x)) ≔
begin admit end;

opaque symbol zminus_zless (x y : τ ι) :
  π (zless (zminus x) y ⇔ zless (zminus y) x) ≔
begin admit end;

opaque symbol zle_zminus (x y : τ ι) :
  π (zle x (zminus y) ⇔ zle y (zminus x)) ≔
begin admit end;

opaque symbol zminus_zle (x y : τ ι) :
  π (zle (zminus x) y ⇔ zle (zminus y) x) ≔
begin admit end;
