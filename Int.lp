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

require open ZF.EquivClass ZF.ArithSimp;

// ===========================================================================
// Definitions
// ===========================================================================

// intrel ≡ {p ∈ (nat*nat)*(nat*nat). ∃x1 y1 x2 y2. p=⟨⟨x1,y1⟩,⟨x2,y2⟩⟩ ∧ x1+y2=x2+y1}
constant symbol intrel : τ ι;
constant symbol intrel_def :
  π (intrel =
     Collect (Sigma (Sigma omega (λ _, omega)) (λ _, Sigma omega (λ _, omega)))
       (λ p, `∃ (x1 : τ ι), `∃ (y1 : τ ι), `∃ (x2 : τ ι), `∃ (y2 : τ ι),
         p = Pair (Pair x1 y1) (Pair x2 y2) ∧ add x1 y2 = add x2 y1));

// int ≡ (nat*nat)//intrel
constant symbol int : τ ι;
constant symbol int_def :
  π (int = quotient (Sigma omega (λ _, omega)) intrel);

// $# m ≡ intrel``{⟨natify(m),0⟩}   (coercion from nat to int)
constant symbol int_of (m : τ ι) : τ ι;
constant symbol int_of_def (m : τ ι) :
  π (int_of m = rel_image_sing intrel (Pair (natify m) empty));

// intify(m) ≡ if m ∈ int then m else $#0   (coercion from ANYTHING to int)
constant symbol intify (m : τ ι) : τ ι;
constant symbol intify_def (m : τ ι) :
  π (intify m = If (m ∈ int) m (int_of empty));

// raw_zminus(z) ≡ ⋃⟨x,y⟩∈z. intrel``{⟨y,x⟩}
constant symbol raw_zminus (z : τ ι) : τ ι;
constant symbol raw_zminus_def (z : τ ι) :
  π (raw_zminus z =
     Union (RepFun z (λ p, rel_image_sing intrel (Pair (snd p) (fst p)))));

// $- z ≡ raw_zminus(intify(z))
constant symbol zminus (z : τ ι) : τ ι;
constant symbol zminus_def (z : τ ι) :
  π (zminus z = raw_zminus (intify z));

// znegative(z) ≡ ∃x y. x<y ∧ y∈nat ∧ ⟨x,y⟩∈z
constant symbol znegative (z : τ ι) : Prop;
constant symbol znegative_def (z : τ ι) :
  π (znegative z =
     (`∃ (x : τ ι), `∃ (y : τ ι), lt x y ∧ y ∈ omega ∧ Pair x y ∈ z));

// iszero(z) ≡ z = $#0
constant symbol iszero (z : τ ι) : Prop;
constant symbol iszero_def (z : τ ι) :
  π (iszero z = (z = int_of empty));

// raw_nat_of(z) ≡ natify(⋃⟨x,y⟩∈z. x#-y)
constant symbol raw_nat_of (z : τ ι) : τ ι;
constant symbol raw_nat_of_def (z : τ ι) :
  π (raw_nat_of z = natify (Union (RepFun z (λ p, diff (fst p) (snd p)))));

// nat_of(z) ≡ raw_nat_of(intify(z))
constant symbol nat_of (z : τ ι) : τ ι;
constant symbol nat_of_def (z : τ ι) :
  π (nat_of z = raw_nat_of (intify z));

// zmagnitude(z) ≡ THE m. m∈nat ∧ ((¬znegative(z) ∧ z=$#m) | (znegative(z) ∧ $-z=$#m))
constant symbol zmagnitude (z : τ ι) : τ ι;
constant symbol zmagnitude_def (z : τ ι) :
  π (zmagnitude z =
     The (λ m, m ∈ omega ∧
       ((¬ znegative z ∧ z = int_of m) ∨ (znegative z ∧ zminus z = int_of m))));

// raw_zmult(z1,z2) ≡ ⋃p1∈z1. ⋃p2∈z2.
//   split(λx1 y1. split(λx2 y2. intrel``{⟨x1*x2+y1*y2, x1*y2+y1*x2⟩}, p2), p1)
constant symbol raw_zmult (z1 z2 : τ ι) : τ ι;
constant symbol raw_zmult_def (z1 z2 : τ ι) :
  π (raw_zmult z1 z2 =
     Union (RepFun z1 (λ p1, Union (RepFun z2 (λ p2,
       rel_image_sing intrel (Pair
         (add (mult (fst p1) (fst p2)) (mult (snd p1) (snd p2)))
         (add (mult (fst p1) (snd p2)) (mult (snd p1) (fst p2)))))))));

// z1 $* z2 ≡ raw_zmult(intify(z1),intify(z2))
constant symbol zmult (z1 z2 : τ ι) : τ ι;
constant symbol zmult_def (z1 z2 : τ ι) :
  π (zmult z1 z2 = raw_zmult (intify z1) (intify z2));

// raw_zadd(z1,z2) ≡ ⋃z1∈z1. ⋃z2∈z2. let ⟨x1,y1⟩=z1;⟨x2,y2⟩=z2 in intrel``{⟨x1+x2,y1+y2⟩}
constant symbol raw_zadd (z1 z2 : τ ι) : τ ι;
constant symbol raw_zadd_def (z1 z2 : τ ι) :
  π (raw_zadd z1 z2 =
     Union (RepFun z1 (λ p1, Union (RepFun z2 (λ p2,
       rel_image_sing intrel (Pair (add (fst p1) (fst p2)) (add (snd p1) (snd p2))))))));

// z1 $+ z2 ≡ raw_zadd(intify(z1),intify(z2))
constant symbol zadd (z1 z2 : τ ι) : τ ι;
constant symbol zadd_def (z1 z2 : τ ι) :
  π (zadd z1 z2 = raw_zadd (intify z1) (intify z2));

// z1 $- z2 ≡ z1 $+ zminus(z2)
constant symbol zdiff (z1 z2 : τ ι) : τ ι;
constant symbol zdiff_def (z1 z2 : τ ι) :
  π (zdiff z1 z2 = zadd z1 (zminus z2));

// z1 $< z2 ≡ znegative(z1 $- z2)
constant symbol zless (z1 z2 : τ ι) : Prop;
constant symbol zless_def (z1 z2 : τ ι) :
  π (zless z1 z2 = znegative (zdiff z1 z2));

// z1 $≤ z2 ≡ z1 $< z2 | intify(z1)=intify(z2)
constant symbol zle (z1 z2 : τ ι) : Prop;
constant symbol zle_def (z1 z2 : τ ι) :
  π (zle z1 z2 = (zless z1 z2 ∨ intify z1 = intify z2));

// ===========================================================================
// Proving that intrel is an equivalence relation
// ===========================================================================

// Private helpers (port-internal): iff-reflexivity, and the add-AC
// "interchange" law (a+b)+(c+d) = (a+c)+(b+d) used throughout the
// congruence/algebra proofs below.
private opaque symbol iff_refl (P : Prop) : π (P ⇔ P) ≔
begin
  assume P;
  apply ∧ᵢ { assume h; apply h } { assume h; apply h }
end;

private opaque symbol add_interchange (a b c d : τ ι) :
  π (add (add a b) (add c d) = add (add a c) (add b d)) ≔
begin
  assume a b c d;
  rewrite (add_assoc a b (add c d));
  rewrite (add_assoc a c (add b d));
  rewrite (add_left_commute b c d);
  reflexivity
end;

opaque symbol intrel_iff (x1 y1 x2 y2 : τ ι) :
  π (Pair (Pair x1 y1) (Pair x2 y2) ∈ intrel ⇔
     (x1 ∈ omega ∧ y1 ∈ omega ∧ x2 ∈ omega ∧ y2 ∈ omega ∧ add x1 y2 = add x2 y1)) ≔
begin
  assume x1 y1 x2 y2;
  rewrite intrel_def;
  apply ∧ᵢ
  { assume h;
    have hSig : π (Pair (Pair x1 y1) (Pair x2 y2) ∈
                   Sigma (Sigma omega (λ _, omega)) (λ _, Sigma omega (λ _, omega)))
      { refine CollectD1 _ _ _ h };
    have h1S : π (Pair x1 y1 ∈ Sigma omega (λ _, omega))
      { refine ind_eq (eq_sym (fst_conv (Pair x1 y1) (Pair x2 y2)))
          (λ t, t ∈ Sigma omega (λ _, omega)) (SigmaD1 _ _ _ hSig) };
    have h2S : π (Pair x2 y2 ∈ Sigma omega (λ _, omega))
      { refine ind_eq (eq_sym (snd_conv (Pair x1 y1) (Pair x2 y2)))
          (λ t, t ∈ Sigma omega (λ _, omega)) (SigmaD2 _ _ _ hSig) };
    have hx1 : π (x1 ∈ omega)
      { refine ind_eq (eq_sym (fst_conv x1 y1)) (λ t, t ∈ omega) (SigmaD1 _ _ _ h1S) };
    have hy1 : π (y1 ∈ omega)
      { refine ind_eq (eq_sym (snd_conv x1 y1)) (λ t, t ∈ omega) (SigmaD2 _ _ _ h1S) };
    have hx2 : π (x2 ∈ omega)
      { refine ind_eq (eq_sym (fst_conv x2 y2)) (λ t, t ∈ omega) (SigmaD1 _ _ _ h2S) };
    have hy2 : π (y2 ∈ omega)
      { refine ind_eq (eq_sym (snd_conv x2 y2)) (λ t, t ∈ omega) (SigmaD2 _ _ _ h2S) };
    have hP : π (`∃ (a1 : τ ι), `∃ (b1 : τ ι), `∃ (a2 : τ ι), `∃ (b2 : τ ι),
                 Pair (Pair x1 y1) (Pair x2 y2) = Pair (Pair a1 b1) (Pair a2 b2) ∧
                 add a1 b2 = add a2 b1)
      { refine CollectD2 _ _ _ h };
    refine ∃ₑ hP _; assume a1 hP1;
    refine ∃ₑ hP1 _; assume b1 hP2;
    refine ∃ₑ hP2 _; assume a2 hP3;
    refine ∃ₑ hP3 _; assume b2 hP4;
    have hpeq : π (Pair (Pair x1 y1) (Pair x2 y2) = Pair (Pair a1 b1) (Pair a2 b2))
      { refine ∧ₑ₁ hP4 };
    have haeq : π (add a1 b2 = add a2 b1) { refine ∧ₑ₂ hP4 };
    have e1 : π (Pair x1 y1 = Pair a1 b1) { refine Pair_inject1 _ _ _ _ hpeq };
    have e2 : π (Pair x2 y2 = Pair a2 b2) { refine Pair_inject2 _ _ _ _ hpeq };
    have ex1 : π (x1 = a1) { refine Pair_inject1 _ _ _ _ e1 };
    have ey1 : π (y1 = b1) { refine Pair_inject2 _ _ _ _ e1 };
    have ex2 : π (x2 = a2) { refine Pair_inject1 _ _ _ _ e2 };
    have ey2 : π (y2 = b2) { refine Pair_inject2 _ _ _ _ e2 };
    refine ∧ᵢ hx1 (∧ᵢ hy1 (∧ᵢ hx2 (∧ᵢ hy2 _)));
    rewrite ex1; rewrite ey2; rewrite ex2; rewrite ey1;
    refine haeq }
  { assume h;
    have hx1 : π (x1 ∈ omega) { refine ∧ₑ₁ h };
    have hy1 : π (y1 ∈ omega) { refine ∧ₑ₁ (∧ₑ₂ h) };
    have hx2 : π (x2 ∈ omega) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ h)) };
    have hy2 : π (y2 ∈ omega) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h))) };
    have heq : π (add x1 y2 = add x2 y1) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h))) };
    refine CollectI _ _ _ _ _
    { refine SigmaI (Pair x1 y1) (Pair x2 y2) (Sigma omega (λ _, omega))
        (λ _, Sigma omega (λ _, omega))
        (SigmaI x1 y1 omega (λ _, omega) hx1 hy1)
        (SigmaI x2 y2 omega (λ _, omega) hx2 hy2) }
    { refine ∃ᵢ x1 _; refine ∃ᵢ y1 _; refine ∃ᵢ x2 _; refine ∃ᵢ y2 _;
      refine ∧ᵢ (eq_refl _) heq } }
end;

opaque symbol intrelI (x1 y1 x2 y2 : τ ι) :
  π (add x1 y2 = add x2 y1) → π (x1 ∈ omega) → π (y1 ∈ omega) →
  π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (Pair (Pair x1 y1) (Pair x2 y2) ∈ intrel) ≔
begin
  assume x1 y1 x2 y2 heq hx1 hy1 hx2 hy2;
  refine ∧ₑ₂ (intrel_iff x1 y1 x2 y2) _;
  refine ∧ᵢ hx1 (∧ᵢ hy1 (∧ᵢ hx2 (∧ᵢ hy2 heq)))
end;

opaque symbol intrelE (p : τ ι) (Q : Prop) :
  π (p ∈ intrel) →
  (Π (x1 y1 x2 y2 : τ ι), π (p = Pair (Pair x1 y1) (Pair x2 y2)) →
    π (add x1 y2 = add x2 y1) → π (x1 ∈ omega) → π (y1 ∈ omega) →
    π (x2 ∈ omega) → π (y2 ∈ omega) → π Q) →
  π Q ≔
begin
  assume p Q hp hcont;
  have hp' : π (p ∈ Collect
       (Sigma (Sigma omega (λ _, omega)) (λ _, Sigma omega (λ _, omega)))
       (λ q, `∃ (x1 : τ ι), `∃ (y1 : τ ι), `∃ (x2 : τ ι), `∃ (y2 : τ ι),
         q = Pair (Pair x1 y1) (Pair x2 y2) ∧ add x1 y2 = add x2 y1))
    { refine ind_eq (eq_sym intrel_def) (λ w, p ∈ w) hp };
  have hP : π (`∃ (a1 : τ ι), `∃ (b1 : τ ι), `∃ (a2 : τ ι), `∃ (b2 : τ ι),
               p = Pair (Pair a1 b1) (Pair a2 b2) ∧ add a1 b2 = add a2 b1)
    { refine CollectD2 _ _ _ hp' };
  refine ∃ₑ hP _; assume a1 h1;
  refine ∃ₑ h1 _; assume b1 h2;
  refine ∃ₑ h2 _; assume a2 h3;
  refine ∃ₑ h3 _; assume b2 h4;
  have hpeq : π (p = Pair (Pair a1 b1) (Pair a2 b2)) { refine ∧ₑ₁ h4 };
  have haeq : π (add a1 b2 = add a2 b1) { refine ∧ₑ₂ h4 };
  have hmem : π (Pair (Pair a1 b1) (Pair a2 b2) ∈ intrel)
    { refine ind_eq (eq_sym hpeq) (λ w, w ∈ intrel) hp };
  have hiff : π (a1 ∈ omega ∧ b1 ∈ omega ∧ a2 ∈ omega ∧ b2 ∈ omega ∧
                 add a1 b2 = add a2 b1)
    { refine ∧ₑ₁ (intrel_iff a1 b1 a2 b2) hmem };
  refine hcont a1 b1 a2 b2 hpeq haeq (∧ₑ₁ hiff) (∧ₑ₁ (∧ₑ₂ hiff))
    (∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hiff))) (∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hiff))))
end;

opaque symbol int_trans_lemma (x1 y1 x2 y2 x3 y3 : τ ι) :
  π (add x1 y2 = add x2 y1) → π (add x2 y3 = add x3 y2) →
  π (add x1 y3 = add x3 y1) ≔
begin
  assume x1 y1 x2 y2 x3 y3 h1 h2;
  have hstep : π (add x2 (add x1 y3) = add x2 (add x3 y1))
    { rewrite (add_left_commute x2 x1 y3);
      rewrite h2;
      rewrite (add_left_commute x1 x3 y2);
      rewrite h1;
      rewrite (add_left_commute x3 x2 y1);
      reflexivity };
  have hnat : π (natify (add x1 y3) = natify (add x3 y1))
    { refine add_left_cancel_natify x2 (add x1 y3) (add x3 y1) hstep };
  refine eq_trans (eq_sym (natify_ident (add x1 y3) (add_type x1 y3)))
    (eq_trans hnat (natify_ident (add x3 y1) (add_type x3 y1)))
end;

opaque symbol equiv_intrel :
  π (equiv (Sigma omega (λ _, omega)) intrel) ≔
begin
  rewrite equiv_def;
  refine ∧ᵢ _ (∧ᵢ _ (∧ᵢ _ _))
  { // intrel ⊆ (nat*nat)*(nat*nat)
    assume p hp;
    refine CollectD1 _ _ _ (ind_eq (eq_sym intrel_def) (λ w, p ∈ w) hp) }
  { // refl_on
    refine refl_onI _ _ _;
    assume x hx;
    refine ∃ₑ (SigmaE x omega (λ _, omega) hx) _; assume a ha;
    refine ∃ₑ (∧ₑ₂ ha) _; assume b hb;
    have hxeq : π (x = Pair a b) { refine ∧ₑ₂ hb };
    rewrite hxeq;
    refine intrelI a b a b (eq_refl (add a b)) (∧ₑ₁ ha) (∧ₑ₁ hb) (∧ₑ₁ ha) (∧ₑ₁ hb) }
  { // sym
    refine symI _ _;
    assume x y hxy;
    refine intrelE (Pair x y) _ hxy _;
    assume a1 b1 a2 b2 hpeq heq ha1 hb1 ha2 hb2;
    have hx : π (x = Pair a1 b1) { refine Pair_inject1 _ _ _ _ hpeq };
    have hy : π (y = Pair a2 b2) { refine Pair_inject2 _ _ _ _ hpeq };
    rewrite hx; rewrite hy;
    refine intrelI a2 b2 a1 b1 (eq_sym heq) ha2 hb2 ha1 hb1 }
  { // trans
    refine transI _ _;
    assume x y z hxy hyz;
    refine intrelE (Pair x y) _ hxy _;
    assume a1 b1 a2 b2 hp1 he1 ha1 hb1 ha2 hb2;
    refine intrelE (Pair y z) _ hyz _;
    assume c1 d1 c2 d2 hp2 he2 hc1 hd1 hc2 hd2;
    have hx : π (x = Pair a1 b1) { refine Pair_inject1 _ _ _ _ hp1 };
    have hy : π (y = Pair a2 b2) { refine Pair_inject2 _ _ _ _ hp1 };
    have hy2 : π (y = Pair c1 d1) { refine Pair_inject1 _ _ _ _ hp2 };
    have hz : π (z = Pair c2 d2) { refine Pair_inject2 _ _ _ _ hp2 };
    have hyy : π (Pair a2 b2 = Pair c1 d1) { refine eq_trans (eq_sym hy) hy2 };
    have ec : π (a2 = c1) { refine Pair_inject1 _ _ _ _ hyy };
    have ed : π (b2 = d1) { refine Pair_inject2 _ _ _ _ hyy };
    have he2' : π (add a2 d2 = add c2 b2)
      { rewrite ec; rewrite ed; refine he2 };
    rewrite hx; rewrite hz;
    refine intrelI a1 b1 c2 d2
      (int_trans_lemma a1 b1 a2 b2 c2 d2 he1 he2') ha1 hb1 hc2 hd2 }
end;

opaque symbol image_intrel_int (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (rel_image_sing intrel (Pair m n) ∈ int) ≔
begin
  assume m n hm hn;
  rewrite int_def;
  refine quotientI (Pair m n) _ _ (SigmaI m n omega (λ _, omega) hm hn)
end;

// eq_intrelD = eq_equiv_class [OF _ equiv_intrel]
opaque symbol eq_intrelD (a b : τ ι) :
  π (rel_image_sing intrel a = rel_image_sing intrel b) →
  π (b ∈ Sigma omega (λ _, omega)) →
  π (Pair a b ∈ intrel) ≔
begin
  assume a b heq hb;
  refine eq_equiv_class (Sigma omega (λ _, omega)) a b intrel heq equiv_intrel hb
end;

// ===========================================================================
// int_of: the injection from nat to int
// ===========================================================================

opaque symbol int_of_type (m : τ ι) : π (int_of m ∈ int) ≔
begin
  assume m;
  rewrite int_of_def;
  refine image_intrel_int (natify m) empty (natify_in_nat m) zero_in_omega
end;

opaque symbol int_of_eq (m n : τ ι) :
  π (int_of m = int_of n ⇔ natify m = natify n) ≔
begin
  assume m n;
  apply ∧ᵢ
  { assume h;
    have h' : π (rel_image_sing intrel (Pair (natify m) empty)
               = rel_image_sing intrel (Pair (natify n) empty))
      { rewrite left int_of_def; rewrite left int_of_def; refine h };
    have hmem : π (Pair (Pair (natify m) empty) (Pair (natify n) empty) ∈ intrel)
      { refine eq_intrelD (Pair (natify m) empty) (Pair (natify n) empty) h'
          (SigmaI (natify n) empty omega (λ _, omega) (natify_in_nat n) zero_in_omega) };
    have hadd : π (add (natify m) empty = add (natify n) empty)
      { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂
          (∧ₑ₁ (intrel_iff (natify m) empty (natify n) empty) hmem)))) };
    refine eq_trans
      (eq_sym (eq_trans (add_0_right_natify (natify m)) (natify_idem m)))
      (eq_trans hadd (eq_trans (add_0_right_natify (natify n)) (natify_idem n))) }
  { assume h;
    rewrite int_of_def; rewrite int_of_def;
    rewrite h; reflexivity }
end;

opaque symbol int_of_inject (m n : τ ι) :
  π (int_of m = int_of n) → π (m ∈ omega) → π (n ∈ omega) → π (m = n) ≔
begin
  assume m n h hm hn;
  have hnat : π (natify m = natify n) { refine ∧ₑ₁ (int_of_eq m n) h };
  refine eq_trans (eq_sym (natify_ident m hm)) (eq_trans hnat (natify_ident n hn))
end;

// ===========================================================================
// intify: coercion from anything to int
// ===========================================================================

opaque symbol intify_in_int (x : τ ι) : π (intify x ∈ int) ≔
begin
  assume x;
  rewrite intify_def;
  refine ∨ₑ (em (x ∈ int)) _ _
  { assume h; rewrite (If_P (x ∈ int) x (int_of empty) h); refine h }
  { assume h; rewrite (If_not_P (x ∈ int) x (int_of empty) h);
    refine int_of_type empty }
end;

opaque symbol intify_ident (n : τ ι) : π (n ∈ int) → π (intify n = n) ≔
begin
  assume n h;
  rewrite intify_def;
  refine If_P (n ∈ int) n (int_of empty) h
end;

// ===========================================================================
// Collapsing rules: to remove intify from arithmetic expressions
// ===========================================================================

opaque symbol intify_idem (x : τ ι) : π (intify (intify x) = intify x) ≔
begin
  assume x;
  refine intify_ident (intify x) (intify_in_int x)
end;

opaque symbol int_of_natify (m : τ ι) : π (int_of (natify m) = int_of m) ≔
begin
  assume m;
  rewrite int_of_def; rewrite int_of_def;
  rewrite natify_idem; reflexivity
end;

opaque symbol zminus_intify (m : τ ι) : π (zminus (intify m) = zminus m) ≔
begin
  assume m;
  rewrite zminus_def; rewrite zminus_def;
  rewrite intify_idem; reflexivity
end;

// Addition
opaque symbol zadd_intify1 (x y : τ ι) : π (zadd (intify x) y = zadd x y) ≔
begin
  assume x y;
  rewrite zadd_def; rewrite zadd_def;
  rewrite intify_idem; reflexivity
end;

opaque symbol zadd_intify2 (x y : τ ι) : π (zadd x (intify y) = zadd x y) ≔
begin
  assume x y;
  rewrite zadd_def; rewrite zadd_def;
  rewrite intify_idem; reflexivity
end;

// Subtraction
opaque symbol zdiff_intify1 (x y : τ ι) : π (zdiff (intify x) y = zdiff x y) ≔
begin
  assume x y;
  rewrite zdiff_def; rewrite zdiff_def;
  refine zadd_intify1 x (zminus y)
end;

opaque symbol zdiff_intify2 (x y : τ ι) : π (zdiff x (intify y) = zdiff x y) ≔
begin
  assume x y;
  rewrite zdiff_def; rewrite zdiff_def;
  rewrite zminus_intify; reflexivity
end;

// Multiplication
opaque symbol zmult_intify1 (x y : τ ι) : π (zmult (intify x) y = zmult x y) ≔
begin
  assume x y;
  rewrite zmult_def; rewrite zmult_def;
  rewrite intify_idem; reflexivity
end;

opaque symbol zmult_intify2 (x y : τ ι) : π (zmult x (intify y) = zmult x y) ≔
begin
  assume x y;
  rewrite zmult_def; rewrite zmult_def;
  rewrite intify_idem; reflexivity
end;

// Orderings
opaque symbol zless_intify1 (x y : τ ι) : π (zless (intify x) y ⇔ zless x y) ≔
begin
  assume x y;
  rewrite zless_def; rewrite zless_def;
  rewrite zdiff_intify1;
  refine iff_refl _
end;

opaque symbol zless_intify2 (x y : τ ι) : π (zless x (intify y) ⇔ zless x y) ≔
begin
  assume x y;
  rewrite zless_def; rewrite zless_def;
  rewrite zdiff_intify2;
  refine iff_refl _
end;

opaque symbol zle_intify1 (x y : τ ι) : π (zle (intify x) y ⇔ zle x y) ≔
begin
  assume x y;
  rewrite zle_def; rewrite zle_def;
  rewrite intify_idem;
  apply ∧ᵢ
  { assume h; refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₁ (zless_intify1 x y) h1) }
    { assume h2; refine ∨ᵢ₂ h2 } }
  { assume h; refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₂ (zless_intify1 x y) h1) }
    { assume h2; refine ∨ᵢ₂ h2 } }
end;

opaque symbol zle_intify2 (x y : τ ι) : π (zle x (intify y) ⇔ zle x y) ≔
begin
  assume x y;
  rewrite zle_def; rewrite zle_def;
  rewrite intify_idem;
  apply ∧ᵢ
  { assume h; refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₁ (zless_intify2 x y) h1) }
    { assume h2; refine ∨ᵢ₂ h2 } }
  { assume h; refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₂ (zless_intify2 x y) h1) }
    { assume h2; refine ∨ᵢ₂ h2 } }
end;

// ===========================================================================
// zminus: unary negation on int
// ===========================================================================

opaque symbol zminus_congruent :
  π (congruent intrel (λ p, rel_image_sing intrel (Pair (snd p) (fst p)))) ≔
begin
  refine congruentI intrel (λ p, rel_image_sing intrel (Pair (snd p) (fst p))) _;
  assume y z hyz;
  refine intrelE (Pair y z) _ hyz _;
  assume x1 y1 x2 y2 hpeq heq hx1 hy1 hx2 hy2;
  have hy : π (y = Pair x1 y1) { refine Pair_inject1 _ _ _ _ hpeq };
  have hz : π (z = Pair x2 y2) { refine Pair_inject2 _ _ _ _ hpeq };
  rewrite hy; rewrite hz;
  rewrite fst_conv; rewrite snd_conv; rewrite fst_conv; rewrite snd_conv;
  refine equiv_class_eq (Sigma omega (λ _, omega)) (Pair y1 x1) (Pair y2 x2)
    intrel equiv_intrel _;
  refine intrelI y1 x1 y2 x2 _ hy1 hx1 hy2 hx2;
  rewrite (add_commute y1 x2); rewrite (add_commute y2 x1);
  refine eq_sym heq
end;

opaque symbol raw_zminus_type (z : τ ι) : π (z ∈ int) → π (raw_zminus z ∈ int) ≔
begin
  assume z hz;
  have hzq : π (z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ w, z ∈ w) hz };
  rewrite raw_zminus_def;
  rewrite int_def;
  refine UN_equiv_class_type (Sigma omega (λ _, omega)) intrel
    (quotient (Sigma omega (λ _, omega)) intrel)
    (λ p, rel_image_sing intrel (Pair (snd p) (fst p))) z
    equiv_intrel zminus_congruent hzq _;
  assume x hx;
  refine quotientI (Pair (snd x) (fst x)) (Sigma omega (λ _, omega)) intrel
    (SigmaI (snd x) (fst x) omega (λ _, omega)
      (SigmaD2 x omega (λ _, omega) hx) (SigmaD1 x omega (λ _, omega) hx))
end;

opaque symbol zminus_type (z : τ ι) : π (zminus z ∈ int) ≔
begin
  assume z;
  rewrite zminus_def;
  refine raw_zminus_type (intify z) (intify_in_int z)
end;

opaque symbol raw_zminus_inject (z w : τ ι) :
  π (raw_zminus z = raw_zminus w) → π (z ∈ int) → π (w ∈ int) → π (z = w) ≔
begin
  assume z w h hz hw;
  have hU : π (Union (RepFun z (λ p, rel_image_sing intrel (Pair (snd p) (fst p))))
             = Union (RepFun w (λ p, rel_image_sing intrel (Pair (snd p) (fst p)))))
    { rewrite left raw_zminus_def; rewrite left raw_zminus_def; refine h };
  have hzq : π (z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ v, z ∈ v) hz };
  have hwq : π (w ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ v, w ∈ v) hw };
  refine UN_equiv_class_inject (Sigma omega (λ _, omega)) intrel
    (λ p, rel_image_sing intrel (Pair (snd p) (fst p))) z w
    equiv_intrel zminus_congruent hU hzq hwq _;
  assume x y hxS hyS hbeq;
  have hfx : π (fst x ∈ omega) { refine SigmaD1 x omega (λ _, omega) hxS };
  have hsx : π (snd x ∈ omega) { refine SigmaD2 x omega (λ _, omega) hxS };
  have hfy : π (fst y ∈ omega) { refine SigmaD1 y omega (λ _, omega) hyS };
  have hsy : π (snd y ∈ omega) { refine SigmaD2 y omega (λ _, omega) hyS };
  have hmem : π (Pair (Pair (snd x) (fst x)) (Pair (snd y) (fst y)) ∈ intrel)
    { refine eq_intrelD (Pair (snd x) (fst x)) (Pair (snd y) (fst y)) hbeq
        (SigmaI (snd y) (fst y) omega (λ _, omega) hsy hfy) };
  have hadd : π (add (snd x) (fst y) = add (snd y) (fst x))
    { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂
        (∧ₑ₁ (intrel_iff (snd x) (fst x) (snd y) (fst y)) hmem)))) };
  have hxpair : π (Pair (fst x) (snd x) = x)
    { refine Pair_fst_snd x omega (λ _, omega) hxS };
  have hypair : π (Pair (fst y) (snd y) = y)
    { refine Pair_fst_snd y omega (λ _, omega) hyS };
  rewrite left hxpair; rewrite left hypair;
  refine intrelI (fst x) (snd x) (fst y) (snd y) _ hfx hsx hfy hsy;
  rewrite (add_commute (fst x) (snd y)); rewrite (add_commute (fst y) (snd x));
  refine eq_sym hadd
end;

opaque symbol zminus_inject_intify (z w : τ ι) :
  π (zminus z = zminus w) → π (intify z = intify w) ≔
begin
  assume z w h;
  have h' : π (raw_zminus (intify z) = raw_zminus (intify w))
    { rewrite left zminus_def; rewrite left zminus_def; refine h };
  refine raw_zminus_inject (intify z) (intify w) h'
    (intify_in_int z) (intify_in_int w)
end;

opaque symbol zminus_inject (z w : τ ι) :
  π (zminus z = zminus w) → π (z ∈ int) → π (w ∈ int) → π (z = w) ≔
begin
  assume z w h hz hw;
  have h' : π (intify z = intify w) { refine zminus_inject_intify z w h };
  refine eq_trans (eq_sym (intify_ident z hz)) (eq_trans h' (intify_ident w hw))
end;

// raw_zminus (name collision with the `raw_zminus` definition; see header)
opaque symbol raw_zminus_eq (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) →
  π (raw_zminus (rel_image_sing intrel (Pair x y)) = rel_image_sing intrel (Pair y x)) ≔
begin
  assume x y hx hy;
  rewrite raw_zminus_def;
  rewrite (UN_equiv_class (Sigma omega (λ _, omega)) intrel
    (λ p, rel_image_sing intrel (Pair (snd p) (fst p))) (Pair x y)
    equiv_intrel zminus_congruent (SigmaI x y omega (λ _, omega) hx hy));
  simplify rule off;
  rewrite fst_conv; rewrite snd_conv;
  reflexivity
end;

// zminus (name collision with the `zminus` definition; see header)
opaque symbol zminus_eq (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) →
  π (zminus (rel_image_sing intrel (Pair x y)) = rel_image_sing intrel (Pair y x)) ≔
begin
  assume x y hx hy;
  rewrite zminus_def;
  rewrite (intify_ident (rel_image_sing intrel (Pair x y))
    (image_intrel_int x y hx hy));
  refine raw_zminus_eq x y hx hy
end;

opaque symbol raw_zminus_zminus (z : τ ι) :
  π (z ∈ int) → π (raw_zminus (raw_zminus z) = z) ≔
begin
  assume z hz;
  have hzq : π (z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ w, z ∈ w) hz };
  refine ∃ₑ (quotientE z (Sigma omega (λ _, omega)) intrel hzq) _; assume x hxz;
  have hxS : π (x ∈ Sigma omega (λ _, omega)) { refine ∧ₑ₁ hxz };
  have hzeq : π (z = rel_image_sing intrel x) { refine ∧ₑ₂ hxz };
  have hfst : π (fst x ∈ omega) { refine SigmaD1 x omega (λ _, omega) hxS };
  have hsnd : π (snd x ∈ omega) { refine SigmaD2 x omega (λ _, omega) hxS };
  have hxpair : π (Pair (fst x) (snd x) = x)
    { refine Pair_fst_snd x omega (λ _, omega) hxS };
  rewrite hzeq;
  rewrite left hxpair;
  rewrite (raw_zminus_eq (fst x) (snd x) hfst hsnd);
  rewrite (raw_zminus_eq (snd x) (fst x) hsnd hfst);
  reflexivity
end;

opaque symbol zminus_zminus_intify (z : τ ι) :
  π (zminus (zminus z) = intify z) ≔
begin
  assume z;
  rewrite zminus_def;
  rewrite (intify_ident (zminus z) (zminus_type z));
  rewrite zminus_def;
  refine raw_zminus_zminus (intify z) (intify_in_int z)
end;

opaque symbol zminus_int0 : π (zminus (int_of empty) = int_of empty) ≔
begin
  rewrite int_of_def;
  rewrite natify_0;
  rewrite (zminus_eq empty empty zero_in_omega zero_in_omega);
  reflexivity
end;

opaque symbol zminus_zminus (z : τ ι) : π (z ∈ int) → π (zminus (zminus z) = z) ≔
begin
  assume z hz;
  rewrite zminus_zminus_intify;
  refine intify_ident z hz
end;

// ===========================================================================
// znegative: the test for negative integers
// ===========================================================================

// znegative (name collision with the `znegative` definition; see header)
opaque symbol znegative_eq (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) →
  π (znegative (rel_image_sing intrel (Pair x y)) ⇔ lt x y) ≔
begin
  assume x y hx hy;
  apply ∧ᵢ
  { assume h;
    have h' : π (`∃ (a : τ ι), `∃ (b : τ ι),
                 lt a b ∧ b ∈ omega ∧ Pair a b ∈ rel_image_sing intrel (Pair x y))
      { refine ind_eq (eq_sym (znegative_def (rel_image_sing intrel (Pair x y))))
          (λ p, p) h };
    refine ∃ₑ h' _; assume a ha;
    refine ∃ₑ ha _; assume b hb;
    have hab : π (lt a b) { refine ∧ₑ₁ hb };
    have hmem : π (Pair a b ∈ rel_image_sing intrel (Pair x y))
      { refine ∧ₑ₂ (∧ₑ₂ hb) };
    have hrel : π (Pair (Pair x y) (Pair a b) ∈ intrel)
      { refine rel_image_singD (Pair x y) (Pair a b) intrel hmem };
    have hiff : π (x ∈ omega ∧ y ∈ omega ∧ a ∈ omega ∧ b ∈ omega ∧
                   add x b = add a y)
      { refine ∧ₑ₁ (intrel_iff x y a b) hrel };
    have hbn : π (b ∈ omega) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hiff))) };
    have heq : π (add x b = add a y) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hiff))) };
    have h1 : π (lt (add a y) (add b y)) { refine add_lt_mono1 a b y hab hbn };
    have h2 : π (lt (add x b) (add b y))
      { refine ind_eq heq (λ w, lt w (add b y)) h1 };
    have h3 : π (lt (add b x) (add b y))
      { rewrite (add_commute b x); refine h2 };
    refine add_lt_elim1 b x y h3 hx hy }
  { assume hlt;
    rewrite znegative_def;
    refine ∃ᵢ x _; refine ∃ᵢ y _;
    refine ∧ᵢ hlt (∧ᵢ hy (rel_image_singI (Pair x y) (Pair x y) intrel
      (intrelI x y x y (eq_refl (add x y)) hx hy hx hy))) }
end;

// No natural number is negative!
opaque symbol not_znegative_int_of (n : τ ι) : π (¬ znegative (int_of n)) ≔
begin
  assume n hneg;
  have hneg' : π (znegative (rel_image_sing intrel (Pair (natify n) empty)))
    { refine ind_eq (eq_sym (int_of_def n)) (λ w, znegative w) hneg };
  have hlt : π (lt (natify n) empty)
    { refine ∧ₑ₁ (znegative_eq (natify n) empty (natify_in_nat n) zero_in_omega)
        hneg' };
  refine emptyE (natify n) (ltD (natify n) empty hlt)
end;

opaque symbol znegative_zminus_int_of (n : τ ι) :
  π (znegative (zminus (int_of (succ n)))) ≔
begin
  assume n;
  have hsn : π (succ (natify n) ∈ omega)
    { refine succ_in_omega (natify n) (natify_in_nat n) };
  rewrite int_of_def;
  rewrite natify_succ;
  rewrite (zminus_eq (succ (natify n)) empty hsn zero_in_omega);
  refine ∧ₑ₂ (znegative_eq empty (succ (natify n)) zero_in_omega hsn) _;
  refine Ord_0_lt (succ (natify n))
    (Ord_succ (natify n) (nat_into_Ord (natify n) (natify_in_nat n)))
    (succ_neq_0 (natify n))
end;

opaque symbol not_znegative_imp_zero (n : τ ι) :
  π (¬ znegative (zminus (int_of n))) → π (natify n = empty) ≔
begin
  assume n hn;
  have hcls : π (zminus (int_of n) = rel_image_sing intrel (Pair empty (natify n)))
    { rewrite int_of_def;
      refine zminus_eq (natify n) empty (natify_in_nat n) zero_in_omega };
  refine ∨ₑ (em (natify n = empty)) _ _
  { assume h; refine h }
  { assume hne;
    have hlt : π (lt empty (natify n))
      { refine Ord_0_lt (natify n) (nat_into_Ord (natify n) (natify_in_nat n)) hne };
    have hzneg : π (znegative (zminus (int_of n)))
      { rewrite hcls;
        refine ∧ₑ₂ (znegative_eq empty (natify n) zero_in_omega (natify_in_nat n))
          hlt };
    refine ⊥ₑ (hn hzneg) }
end;

// ===========================================================================
// nat_of: Coercion of an Integer to a Natural Number
// ===========================================================================

opaque symbol nat_of_intify (z : τ ι) : π (nat_of (intify z) = nat_of z) ≔
begin
  assume z;
  rewrite nat_of_def; rewrite nat_of_def;
  rewrite intify_idem; reflexivity
end;

opaque symbol nat_of_congruent :
  π (congruent intrel (λ p, diff (fst p) (snd p))) ≔
begin
  refine congruentI intrel (λ p, diff (fst p) (snd p)) _;
  assume y z hyz;
  refine intrelE (Pair y z) _ hyz _;
  assume x1 y1 x2 y2 hpeq heq hx1 hy1 hx2 hy2;
  have hy : π (y = Pair x1 y1) { refine Pair_inject1 _ _ _ _ hpeq };
  have hz : π (z = Pair x2 y2) { refine Pair_inject2 _ _ _ _ hpeq };
  rewrite hy; rewrite hz;
  rewrite fst_conv; rewrite snd_conv; rewrite fst_conv; rewrite snd_conv;
  rewrite left (diff_cancel2 x1 y1 y2);
  rewrite heq;
  rewrite (add_commute y1 y2);
  refine diff_cancel2 x2 y2 y1
end;

// raw_nat_of (name collision with the `raw_nat_of` definition; see header)
opaque symbol raw_nat_of_eq (x y : τ ι) :
  π (x ∈ omega) → π (y ∈ omega) →
  π (raw_nat_of (rel_image_sing intrel (Pair x y)) = diff x y) ≔
begin
  assume x y hx hy;
  rewrite raw_nat_of_def;
  rewrite (UN_equiv_class (Sigma omega (λ _, omega)) intrel
    (λ p, diff (fst p) (snd p)) (Pair x y)
    equiv_intrel nat_of_congruent (SigmaI x y omega (λ _, omega) hx hy));
  simplify rule off;
  rewrite fst_conv; rewrite snd_conv;
  refine natify_ident (diff x y) (diff_type x y)
end;

opaque symbol raw_nat_of_int_of (n : τ ι) : π (raw_nat_of (int_of n) = natify n) ≔
begin
  assume n;
  rewrite int_of_def;
  rewrite (raw_nat_of_eq (natify n) empty (natify_in_nat n) zero_in_omega);
  rewrite diff_0;
  refine natify_idem n
end;

opaque symbol nat_of_int_of (n : τ ι) : π (nat_of (int_of n) = natify n) ≔
begin
  assume n;
  rewrite nat_of_def;
  rewrite (intify_ident (int_of n) (int_of_type n));
  refine raw_nat_of_int_of n
end;

opaque symbol raw_nat_of_type (z : τ ι) : π (raw_nat_of z ∈ omega) ≔
begin
  assume z;
  rewrite raw_nat_of_def;
  refine natify_in_nat (Union (RepFun z (λ p, diff (fst p) (snd p))))
end;

opaque symbol nat_of_type (z : τ ι) : π (nat_of z ∈ omega) ≔
begin
  assume z;
  rewrite nat_of_def;
  refine raw_nat_of_type (intify z)
end;

// ===========================================================================
// zmagnitude: magnitude of an integer, as a natural number
// ===========================================================================

opaque symbol zmagnitude_int_of (n : τ ι) : π (zmagnitude (int_of n) = natify n) ≔
begin
  assume n;
  rewrite zmagnitude_def;
  refine the_equality (λ m, m ∈ omega ∧
      ((¬ znegative (int_of n) ∧ int_of n = int_of m) ∨
       (znegative (int_of n) ∧ zminus (int_of n) = int_of m))) (natify n) _ _
  { refine ∧ᵢ (natify_in_nat n)
      (∨ᵢ₁ (∧ᵢ (not_znegative_int_of n) (eq_sym (int_of_natify n)))) }
  { assume m hm;
    have hmn : π (m ∈ omega) { refine ∧ₑ₁ hm };
    refine ∨ₑ (∧ₑ₂ hm) _ _
    { assume h1;
      have hnat : π (natify n = natify m) { refine ∧ₑ₁ (int_of_eq n m) (∧ₑ₂ h1) };
      refine eq_trans (eq_sym (natify_ident m hmn)) (eq_sym hnat) }
    { assume h2; refine ⊥ₑ (not_znegative_int_of n (∧ₑ₁ h2)) } }
end;

opaque symbol natify_int_of_eq (x n : τ ι) :
  π (natify x = n) → π (int_of x = int_of n) ≔
begin
  assume x n h;
  refine ∧ₑ₂ (int_of_eq x n) _;
  rewrite left h;
  refine eq_sym (natify_idem x)
end;

opaque symbol zmagnitude_zminus_int_of (n : τ ι) :
  π (zmagnitude (zminus (int_of n)) = natify n) ≔
begin
  assume n;
  have hzz : π (zminus (zminus (int_of n)) = int_of n)
    { rewrite zminus_zminus_intify; refine intify_ident (int_of n) (int_of_type n) };
  rewrite zmagnitude_def;
  refine the_equality (λ m, m ∈ omega ∧
      ((¬ znegative (zminus (int_of n)) ∧ zminus (int_of n) = int_of m) ∨
       (znegative (zminus (int_of n)) ∧ zminus (zminus (int_of n)) = int_of m)))
    (natify n) _ _
  { refine ∧ᵢ (natify_in_nat n) _;
    refine ∨ₑ (em (znegative (zminus (int_of n)))) _ _
    { assume hneg;
      refine ∨ᵢ₂ (∧ᵢ hneg (eq_trans hzz (eq_sym (int_of_natify n)))) }
    { assume hnneg;
      have h0 : π (natify n = empty) { refine not_znegative_imp_zero n hnneg };
      refine ∨ᵢ₁ (∧ᵢ hnneg _);
      // zminus (int_of n) = int_of (natify n): both sides are int_of 0
      have hn0 : π (int_of n = int_of empty)
        { refine natify_int_of_eq n empty h0 };
      rewrite hn0;
      rewrite zminus_int0;
      rewrite h0;
      reflexivity } }
  { assume m hm;
    have hmn : π (m ∈ omega) { refine ∧ₑ₁ hm };
    refine ∨ₑ (∧ₑ₂ hm) _ _
    { assume h1;
      have hnneg : π (¬ znegative (zminus (int_of n))) { refine ∧ₑ₁ h1 };
      have h0 : π (natify n = empty) { refine not_znegative_imp_zero n hnneg };
      // zminus (int_of m) = zminus (zminus (int_of n)) = int_of n, so
      // ¬znegative (zminus (int_of m)), so natify m = 0
      have hzm : π (zminus (int_of m) = int_of n)
        { rewrite left (∧ₑ₂ h1); refine hzz };
      have hnnegm : π (¬ znegative (zminus (int_of m)))
        { assume habs;
          refine not_znegative_int_of n
            (ind_eq (eq_sym hzm) (λ w, znegative w) habs) };
      have hm0 : π (natify m = empty) { refine not_znegative_imp_zero m hnnegm };
      refine eq_trans (eq_sym (natify_ident m hmn)) (eq_trans hm0 (eq_sym h0)) }
    { assume h2;
      have heqm : π (int_of n = int_of m)
        { rewrite left hzz; refine ∧ₑ₂ h2 };
      have hnat : π (natify n = natify m) { refine ∧ₑ₁ (int_of_eq n m) heqm };
      refine eq_trans (eq_sym (natify_ident m hmn)) (eq_sym hnat) } }
end;

opaque symbol zmagnitude_type (z : τ ι) : π (zmagnitude z ∈ omega) ≔
begin
  assume z;
  rewrite zmagnitude_def;
  refine ∨ₑ (em (`∃ (x : τ ι),
      (x ∈ omega ∧ ((¬ znegative z ∧ z = int_of x) ∨
                    (znegative z ∧ zminus z = int_of x))) ∧
      (`∀ (w : τ ι), (w ∈ omega ∧ ((¬ znegative z ∧ z = int_of w) ∨
                    (znegative z ∧ zminus z = int_of w))) ⇒ w = x))) _ _
  { assume hex;
    refine ∧ₑ₁ (theI (λ m, m ∈ omega ∧
      ((¬ znegative z ∧ z = int_of m) ∨
       (znegative z ∧ zminus z = int_of m))) hex) }
  { assume hno;
    rewrite (the_0 (λ m, m ∈ omega ∧
      ((¬ znegative z ∧ z = int_of m) ∨
       (znegative z ∧ zminus z = int_of m))) hno);
    refine zero_in_omega }
end;

opaque symbol not_zneg_int_of (z : τ ι) :
  π (z ∈ int) → π (¬ znegative z) → π (Bex omega (λ n, z = int_of n)) ≔
begin
  assume z hz hnneg;
  have hzq : π (z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ w, z ∈ w) hz };
  refine ∃ₑ (quotientE z (Sigma omega (λ _, omega)) intrel hzq) _; assume p hp;
  have hpS : π (p ∈ Sigma omega (λ _, omega)) { refine ∧ₑ₁ hp };
  have hzeq : π (z = rel_image_sing intrel p) { refine ∧ₑ₂ hp };
  have hx : π (fst p ∈ omega) { refine SigmaD1 p omega (λ _, omega) hpS };
  have hy : π (snd p ∈ omega) { refine SigmaD2 p omega (λ _, omega) hpS };
  have hppair : π (Pair (fst p) (snd p) = p)
    { refine Pair_fst_snd p omega (λ _, omega) hpS };
  have hzeq2 : π (z = rel_image_sing intrel (Pair (fst p) (snd p)))
    { rewrite hzeq; rewrite hppair; reflexivity };
  have hnlt : π (¬ lt (fst p) (snd p))
    { assume hltxy;
      refine hnneg (ind_eq hzeq2 (λ w, znegative w)
        (∧ₑ₂ (znegative_eq (fst p) (snd p) hx hy) hltxy)) };
  have hle : π (le (snd p) (fst p))
    { refine not_lt_imp_le (fst p) (snd p)
        (nat_into_Ord (fst p) hx) (nat_into_Ord (snd p) hy) hnlt };
  refine ∃ᵢ (diff (fst p) (snd p)) (∧ᵢ (diff_type (fst p) (snd p)) _);
  rewrite int_of_def;
  rewrite (natify_ident (diff (fst p) (snd p)) (diff_type (fst p) (snd p)));
  rewrite hzeq2;
  refine equiv_class_eq (Sigma omega (λ _, omega)) (Pair (fst p) (snd p))
    (Pair (diff (fst p) (snd p)) empty) intrel equiv_intrel _;
  refine intrelI (fst p) (snd p) (diff (fst p) (snd p)) empty _
    hx hy (diff_type (fst p) (snd p)) zero_in_omega;
  rewrite (add_0_right_natify (fst p));
  rewrite (natify_ident (fst p) hx);
  refine eq_sym (add_diff_inverse2 (snd p) (fst p) hle hx)
end;

opaque symbol not_zneg_mag (z : τ ι) :
  π (z ∈ int) → π (¬ znegative z) → π (int_of (zmagnitude z) = z) ≔
begin
  assume z hz hnneg;
  refine ∃ₑ (not_zneg_int_of z hz hnneg) _; assume n hn;
  rewrite (∧ₑ₂ hn);
  rewrite zmagnitude_int_of;
  refine int_of_natify n
end;

opaque symbol zneg_int_of (z : τ ι) :
  π (znegative z) → π (z ∈ int) → π (Bex omega (λ n, z = zminus (int_of (succ n)))) ≔
begin
  assume z hneg hz;
  have hzq : π (z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ w, z ∈ w) hz };
  refine ∃ₑ (quotientE z (Sigma omega (λ _, omega)) intrel hzq) _; assume p hp;
  have hpS : π (p ∈ Sigma omega (λ _, omega)) { refine ∧ₑ₁ hp };
  have hzeq : π (z = rel_image_sing intrel p) { refine ∧ₑ₂ hp };
  have hx : π (fst p ∈ omega) { refine SigmaD1 p omega (λ _, omega) hpS };
  have hy : π (snd p ∈ omega) { refine SigmaD2 p omega (λ _, omega) hpS };
  have hppair : π (Pair (fst p) (snd p) = p)
    { refine Pair_fst_snd p omega (λ _, omega) hpS };
  have hzeq2 : π (z = rel_image_sing intrel (Pair (fst p) (snd p)))
    { rewrite hzeq; rewrite hppair; reflexivity };
  have hltxy : π (lt (fst p) (snd p))
    { refine ∧ₑ₁ (znegative_eq (fst p) (snd p) hx hy)
        (ind_eq (eq_sym hzeq2) (λ w, znegative w) hneg) };
  refine ∃ₑ (less_imp_succ_add (fst p) (snd p) hltxy hy) _; assume k hk;
  have hkw : π (k ∈ omega) { refine ∧ₑ₁ hk };
  have hsnd : π (snd p = succ (add (fst p) k)) { refine ∧ₑ₂ hk };
  refine ∃ᵢ k (∧ᵢ hkw _);
  rewrite int_of_def;
  rewrite natify_succ;
  rewrite (natify_ident k hkw);
  rewrite (zminus_eq (succ k) empty (succ_in_omega k hkw) zero_in_omega);
  rewrite hzeq2;
  refine equiv_class_eq (Sigma omega (λ _, omega)) (Pair (fst p) (snd p))
    (Pair empty (succ k)) intrel equiv_intrel _;
  refine intrelI (fst p) (snd p) empty (succ k) _
    hx hy zero_in_omega (succ_in_omega k hkw);
  rewrite (add_succ_right (fst p) k);
  rewrite (add_0_natify (snd p));
  rewrite (natify_ident (snd p) hy);
  rewrite hsnd;
  reflexivity
end;

opaque symbol zneg_mag (z : τ ι) :
  π (znegative z) → π (z ∈ int) → π (int_of (zmagnitude z) = zminus z) ≔
begin
  assume z hneg hz;
  refine ∃ₑ (zneg_int_of z hneg hz) _; assume n hn;
  rewrite (∧ₑ₂ hn);
  rewrite zmagnitude_zminus_int_of;
  rewrite int_of_natify;
  rewrite zminus_zminus_intify;
  refine eq_sym (intify_ident (int_of (succ n)) (int_of_type (succ n)))
end;

opaque symbol int_cases (z : τ ι) :
  π (z ∈ int) → π (Bex omega (λ n, z = int_of n ∨ z = zminus (int_of (succ n)))) ≔
begin
  assume z hz;
  refine ∨ₑ (em (znegative z)) _ _
  { assume hneg;
    refine ∃ₑ (zneg_int_of z hneg hz) _; assume n hn;
    refine ∃ᵢ n (∧ᵢ (∧ₑ₁ hn) (∨ᵢ₂ (∧ₑ₂ hn))) }
  { assume hnneg;
    refine ∃ₑ (not_zneg_int_of z hz hnneg) _; assume n hn;
    refine ∃ᵢ n (∧ᵢ (∧ₑ₁ hn) (∨ᵢ₁ (∧ₑ₂ hn))) }
end;

opaque symbol not_zneg_raw_nat_of (z : τ ι) :
  π (¬ znegative z) → π (z ∈ int) → π (int_of (raw_nat_of z) = z) ≔
begin
  assume z hnneg hz;
  refine ∃ₑ (not_zneg_int_of z hz hnneg) _; assume n hn;
  rewrite (∧ₑ₂ hn);
  rewrite raw_nat_of_int_of;
  refine int_of_natify n
end;

opaque symbol not_zneg_nat_of_intify (z : τ ι) :
  π (¬ znegative (intify z)) → π (int_of (nat_of z) = intify z) ≔
begin
  assume z h;
  rewrite nat_of_def;
  refine not_zneg_raw_nat_of (intify z) h (intify_in_int z)
end;

opaque symbol not_zneg_nat_of (z : τ ι) :
  π (¬ znegative z) → π (z ∈ int) → π (int_of (nat_of z) = z) ≔
begin
  assume z hnneg hz;
  have h1 : π (¬ znegative (intify z))
    { rewrite (intify_ident z hz); refine hnneg };
  refine eq_trans (not_zneg_nat_of_intify z h1) (intify_ident z hz)
end;

opaque symbol zneg_nat_of (z : τ ι) :
  π (znegative (intify z)) → π (nat_of z = empty) ≔
begin
  assume z hneg;
  have hzq : π (intify z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ w, intify z ∈ w) (intify_in_int z) };
  refine ∃ₑ (quotientE (intify z) (Sigma omega (λ _, omega)) intrel hzq) _;
  assume p hp;
  have hpS : π (p ∈ Sigma omega (λ _, omega)) { refine ∧ₑ₁ hp };
  have hzeq : π (intify z = rel_image_sing intrel p) { refine ∧ₑ₂ hp };
  have hx : π (fst p ∈ omega) { refine SigmaD1 p omega (λ _, omega) hpS };
  have hy : π (snd p ∈ omega) { refine SigmaD2 p omega (λ _, omega) hpS };
  have hppair : π (Pair (fst p) (snd p) = p)
    { refine Pair_fst_snd p omega (λ _, omega) hpS };
  have hzeq2 : π (intify z = rel_image_sing intrel (Pair (fst p) (snd p)))
    { rewrite hzeq; rewrite hppair; reflexivity };
  have hlt : π (lt (fst p) (snd p))
    { refine ∧ₑ₁ (znegative_eq (fst p) (snd p) hx hy)
        (ind_eq (eq_sym hzeq2) (λ w, znegative w) hneg) };
  rewrite nat_of_def;
  rewrite hzeq2;
  rewrite (raw_nat_of_eq (fst p) (snd p) hx hy);
  refine nat_lt_imp_diff_eq_0 (fst p) (snd p) hx hy hlt
end;

// ===========================================================================
// zadd: addition on int
// ===========================================================================

// port-internal helper: every z ∈ int is the intrel-class of a pair of
// naturals (quotientE + surjective pairing, packaged as an eliminator).
private opaque symbol intE (z : τ ι) (Q : Prop) :
  π (z ∈ int) →
  (Π (x y : τ ι), π (x ∈ omega) → π (y ∈ omega) →
     π (z = rel_image_sing intrel (Pair x y)) → π Q) → π Q ≔
begin
  assume z Q hz hcont;
  have hzq : π (z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ w, z ∈ w) hz };
  refine ∃ₑ (quotientE z (Sigma omega (λ _, omega)) intrel hzq) _; assume p hp;
  have hpS : π (p ∈ Sigma omega (λ _, omega)) { refine ∧ₑ₁ hp };
  have hppair : π (Pair (fst p) (snd p) = p)
    { refine Pair_fst_snd p omega (λ _, omega) hpS };
  refine hcont (fst p) (snd p) (SigmaD1 p omega (λ _, omega) hpS)
    (SigmaD2 p omega (λ _, omega) hpS) _;
  rewrite (∧ₑ₂ hp); rewrite hppair; reflexivity
end;

// Congruence Property for Addition
opaque symbol zadd_congruent2 :
  π (congruent2 intrel intrel (λ z1 z2,
    rel_image_sing intrel (Pair (add (fst z1) (fst z2)) (add (snd z1) (snd z2))))) ≔
begin
  refine congruent2I (Sigma omega (λ _, omega)) (Sigma omega (λ _, omega))
    intrel intrel
    (λ z1 z2, rel_image_sing intrel (Pair (add (fst z1) (fst z2)) (add (snd z1) (snd z2))))
    equiv_intrel equiv_intrel _ _
  { // left congruence
    assume w hw y z hyz;
    refine intrelE (Pair y z) _ hyz _;
    assume x1 y1 x2 y2 hpeq heq hx1 hy1 hx2 hy2;
    have hyp : π (y = Pair x1 y1) { refine Pair_inject1 _ _ _ _ hpeq };
    have hzp : π (z = Pair x2 y2) { refine Pair_inject2 _ _ _ _ hpeq };
    rewrite hyp; rewrite hzp;
    rewrite fst_conv; rewrite snd_conv; rewrite fst_conv; rewrite snd_conv;
    refine equiv_class_eq (Sigma omega (λ _, omega))
      (Pair (add x1 (fst w)) (add y1 (snd w)))
      (Pair (add x2 (fst w)) (add y2 (snd w))) intrel equiv_intrel _;
    refine intrelI (add x1 (fst w)) (add y1 (snd w))
      (add x2 (fst w)) (add y2 (snd w)) _
      (add_type x1 (fst w)) (add_type y1 (snd w))
      (add_type x2 (fst w)) (add_type y2 (snd w));
    rewrite (add_interchange x1 (fst w) y2 (snd w));
    rewrite (add_interchange x2 (fst w) y1 (snd w));
    rewrite heq;
    reflexivity }
  { // right congruence
    assume w hw y z hyz;
    refine intrelE (Pair y z) _ hyz _;
    assume x1 y1 x2 y2 hpeq heq hx1 hy1 hx2 hy2;
    have hyp : π (y = Pair x1 y1) { refine Pair_inject1 _ _ _ _ hpeq };
    have hzp : π (z = Pair x2 y2) { refine Pair_inject2 _ _ _ _ hpeq };
    rewrite hyp; rewrite hzp;
    rewrite fst_conv; rewrite snd_conv; rewrite fst_conv; rewrite snd_conv;
    refine equiv_class_eq (Sigma omega (λ _, omega))
      (Pair (add (fst w) x1) (add (snd w) y1))
      (Pair (add (fst w) x2) (add (snd w) y2)) intrel equiv_intrel _;
    refine intrelI (add (fst w) x1) (add (snd w) y1)
      (add (fst w) x2) (add (snd w) y2) _
      (add_type (fst w) x1) (add_type (snd w) y1)
      (add_type (fst w) x2) (add_type (snd w) y2);
    rewrite (add_interchange (fst w) x1 (snd w) y2);
    rewrite (add_interchange (fst w) x2 (snd w) y1);
    rewrite heq;
    reflexivity }
end;

opaque symbol raw_zadd_type (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (raw_zadd z w ∈ int) ≔
begin
  assume z w hz hw;
  have hzq : π (z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ v, z ∈ v) hz };
  have hwq : π (w ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ v, w ∈ v) hw };
  rewrite raw_zadd_def;
  rewrite int_def;
  refine UN_equiv_class_type2 (Sigma omega (λ _, omega)) intrel
    (quotient (Sigma omega (λ _, omega)) intrel) z w
    (λ p1 p2, rel_image_sing intrel
      (Pair (add (fst p1) (fst p2)) (add (snd p1) (snd p2))))
    equiv_intrel zadd_congruent2 hzq hwq _;
  assume x1 x2 h1 h2;
  refine quotientI (Pair (add (fst x1) (fst x2)) (add (snd x1) (snd x2)))
    (Sigma omega (λ _, omega)) intrel
    (SigmaI (add (fst x1) (fst x2)) (add (snd x1) (snd x2)) omega (λ _, omega)
      (add_type (fst x1) (fst x2)) (add_type (snd x1) (snd x2)))
end;

opaque symbol zadd_type (z w : τ ι) : π (zadd z w ∈ int) ≔
begin
  assume z w;
  rewrite zadd_def;
  refine raw_zadd_type (intify z) (intify w) (intify_in_int z) (intify_in_int w)
end;

// raw_zadd (name collision with the `raw_zadd` definition; see header)
opaque symbol raw_zadd_eq (x1 y1 x2 y2 : τ ι) :
  π (x1 ∈ omega) → π (y1 ∈ omega) → π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (raw_zadd (rel_image_sing intrel (Pair x1 y1)) (rel_image_sing intrel (Pair x2 y2))
     = rel_image_sing intrel (Pair (add x1 x2) (add y1 y2))) ≔
begin
  assume x1 y1 x2 y2 h1 h2 h3 h4;
  rewrite raw_zadd_def;
  refine eq_trans (UN_equiv_class2 (Sigma omega (λ _, omega))
    (Sigma omega (λ _, omega)) intrel intrel
    (λ p1 p2, rel_image_sing intrel
      (Pair (add (fst p1) (fst p2)) (add (snd p1) (snd p2))))
    (Pair x1 y1) (Pair x2 y2) equiv_intrel equiv_intrel zadd_congruent2
    (SigmaI x1 y1 omega (λ _, omega) h1 h2)
    (SigmaI x2 y2 omega (λ _, omega) h3 h4)) _;
  rewrite fst_conv; rewrite snd_conv; rewrite fst_conv; rewrite snd_conv;
  reflexivity
end;

// zadd (name collision with the `zadd` definition; see header)
opaque symbol zadd_eq (x1 y1 x2 y2 : τ ι) :
  π (x1 ∈ omega) → π (y1 ∈ omega) → π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (zadd (rel_image_sing intrel (Pair x1 y1)) (rel_image_sing intrel (Pair x2 y2))
     = rel_image_sing intrel (Pair (add x1 x2) (add y1 y2))) ≔
begin
  assume x1 y1 x2 y2 h1 h2 h3 h4;
  rewrite zadd_def;
  rewrite (intify_ident (rel_image_sing intrel (Pair x1 y1))
    (image_intrel_int x1 y1 h1 h2));
  rewrite (intify_ident (rel_image_sing intrel (Pair x2 y2))
    (image_intrel_int x2 y2 h3 h4));
  refine raw_zadd_eq x1 y1 x2 y2 h1 h2 h3 h4
end;

opaque symbol raw_zadd_int0 (z : τ ι) :
  π (z ∈ int) → π (raw_zadd (int_of empty) z = z) ≔
begin
  assume z hz;
  refine intE z _ hz _;
  assume x y hx hy hzeq;
  rewrite hzeq;
  rewrite int_of_def; rewrite natify_0;
  rewrite (raw_zadd_eq empty empty x y zero_in_omega zero_in_omega hx hy);
  rewrite (add_0 x hx); rewrite (add_0 y hy);
  reflexivity
end;

opaque symbol zadd_int0_intify (z : τ ι) :
  π (zadd (int_of empty) z = intify z) ≔
begin
  assume z;
  rewrite zadd_def;
  rewrite (intify_ident (int_of empty) (int_of_type empty));
  refine raw_zadd_int0 (intify z) (intify_in_int z)
end;

opaque symbol zadd_int0 (z : τ ι) : π (z ∈ int) → π (zadd (int_of empty) z = z) ≔
begin
  assume z hz;
  rewrite zadd_int0_intify;
  refine intify_ident z hz
end;

opaque symbol raw_zminus_zadd_distrib (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) →
  π (zminus (raw_zadd z w) = raw_zadd (zminus z) (zminus w)) ≔
begin
  assume z w hz hw;
  refine intE z _ hz _; assume x1 y1 hx1 hy1 hzeq;
  refine intE w _ hw _; assume x2 y2 hx2 hy2 hweq;
  rewrite hzeq; rewrite hweq;
  rewrite (raw_zadd_eq x1 y1 x2 y2 hx1 hy1 hx2 hy2);
  rewrite (zminus_eq (add x1 x2) (add y1 y2)
    (add_type x1 x2) (add_type y1 y2));
  rewrite (zminus_eq x1 y1 hx1 hy1);
  rewrite (zminus_eq x2 y2 hx2 hy2);
  rewrite (raw_zadd_eq y1 x1 y2 x2 hy1 hx1 hy2 hx2);
  reflexivity
end;

opaque symbol zminus_zadd_distrib (z w : τ ι) :
  π (zminus (zadd z w) = zadd (zminus z) (zminus w)) ≔
begin
  assume z w;
  rewrite zadd_def;
  rewrite zadd_def;
  rewrite (intify_ident (zminus z) (zminus_type z));
  rewrite (intify_ident (zminus w) (zminus_type w));
  rewrite left (zminus_intify z);
  rewrite left (zminus_intify w);
  refine raw_zminus_zadd_distrib (intify z) (intify w)
    (intify_in_int z) (intify_in_int w)
end;

opaque symbol raw_zadd_commute (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (raw_zadd z w = raw_zadd w z) ≔
begin
  assume z w hz hw;
  refine intE z _ hz _; assume x1 y1 hx1 hy1 hzeq;
  refine intE w _ hw _; assume x2 y2 hx2 hy2 hweq;
  rewrite hzeq; rewrite hweq;
  rewrite (raw_zadd_eq x1 y1 x2 y2 hx1 hy1 hx2 hy2);
  rewrite (raw_zadd_eq x2 y2 x1 y1 hx2 hy2 hx1 hy1);
  rewrite (add_commute x1 x2);
  rewrite (add_commute y1 y2);
  reflexivity
end;

opaque symbol zadd_commute (z w : τ ι) : π (zadd z w = zadd w z) ≔
begin
  assume z w;
  rewrite zadd_def; rewrite zadd_def;
  refine raw_zadd_commute (intify z) (intify w)
    (intify_in_int z) (intify_in_int w)
end;

opaque symbol raw_zadd_assoc (z1 z2 z3 : τ ι) :
  π (z1 ∈ int) → π (z2 ∈ int) → π (z3 ∈ int) →
  π (raw_zadd (raw_zadd z1 z2) z3 = raw_zadd z1 (raw_zadd z2 z3)) ≔
begin
  assume z1 z2 z3 h1 h2 h3;
  refine intE z1 _ h1 _; assume x1 y1 hx1 hy1 he1;
  refine intE z2 _ h2 _; assume x2 y2 hx2 hy2 he2;
  refine intE z3 _ h3 _; assume x3 y3 hx3 hy3 he3;
  rewrite he1; rewrite he2; rewrite he3;
  rewrite (raw_zadd_eq x1 y1 x2 y2 hx1 hy1 hx2 hy2);
  rewrite (raw_zadd_eq (add x1 x2) (add y1 y2) x3 y3
    (add_type x1 x2) (add_type y1 y2) hx3 hy3);
  rewrite (raw_zadd_eq x2 y2 x3 y3 hx2 hy2 hx3 hy3);
  rewrite (raw_zadd_eq x1 y1 (add x2 x3) (add y2 y3)
    hx1 hy1 (add_type x2 x3) (add_type y2 y3));
  rewrite add_assoc; rewrite add_assoc;
  reflexivity
end;

opaque symbol zadd_assoc (z1 z2 z3 : τ ι) :
  π (zadd (zadd z1 z2) z3 = zadd z1 (zadd z2 z3)) ≔
begin
  assume z1 z2 z3;
  rewrite zadd_def; rewrite zadd_def; rewrite zadd_def; rewrite zadd_def;
  rewrite (intify_ident (raw_zadd (intify z1) (intify z2))
    (raw_zadd_type (intify z1) (intify z2) (intify_in_int z1) (intify_in_int z2)));
  rewrite (intify_ident (raw_zadd (intify z2) (intify z3))
    (raw_zadd_type (intify z2) (intify z3) (intify_in_int z2) (intify_in_int z3)));
  refine raw_zadd_assoc (intify z1) (intify z2) (intify z3)
    (intify_in_int z1) (intify_in_int z2) (intify_in_int z3)
end;

// For AC rewriting
opaque symbol zadd_left_commute (z1 z2 z3 : τ ι) :
  π (zadd z1 (zadd z2 z3) = zadd z2 (zadd z1 z3)) ≔
begin
  assume z1 z2 z3;
  rewrite left (zadd_assoc z1 z2 z3);
  rewrite left (zadd_assoc z2 z1 z3);
  rewrite (zadd_commute z1 z2);
  reflexivity
end;

// (Integer addition is an AC operator: `lemmas zadd_ac = zadd_assoc
// zadd_commute zadd_left_commute` — a hint-list bundle, skipped; see header.)

opaque symbol int_of_add (m n : τ ι) :
  π (int_of (add m n) = zadd (int_of m) (int_of n)) ≔
begin
  assume m n;
  rewrite int_of_def; rewrite int_of_def; rewrite int_of_def;
  rewrite (zadd_eq (natify m) empty (natify n) empty
    (natify_in_nat m) zero_in_omega (natify_in_nat n) zero_in_omega);
  rewrite (natify_ident (add m n) (add_type m n));
  rewrite (add_natify1 m (natify n));
  rewrite (add_natify2 m n);
  rewrite (add_0 empty zero_in_omega);
  reflexivity
end;

opaque symbol int_succ_int_1 (m : τ ι) :
  π (int_of (succ m) = zadd (int_of (succ empty)) (int_of m)) ≔
begin
  assume m;
  rewrite left (int_of_add (succ empty) m);
  refine ∧ₑ₂ (int_of_eq (succ m) (add (succ empty) m)) _;
  rewrite natify_succ;
  rewrite (natify_ident (add (succ empty) m) (add_type (succ empty) m));
  rewrite (add_succ empty m);
  rewrite (add_0_natify m);
  reflexivity
end;

opaque symbol int_of_diff (m n : τ ι) :
  π (m ∈ omega) → π (le n m) → π (int_of (diff m n) = zdiff (int_of m) (int_of n)) ≔
begin
  assume m n hm hle;
  have hn : π (n ∈ omega) { refine le_in_nat n m hle hm };
  rewrite zdiff_def;
  rewrite int_of_def;
  rewrite (natify_ident (diff m n) (diff_type m n));
  rewrite int_of_def;
  rewrite (natify_ident m hm);
  rewrite int_of_def;
  rewrite (natify_ident n hn);
  rewrite (zminus_eq n empty hn zero_in_omega);
  rewrite (zadd_eq m empty empty n hm zero_in_omega zero_in_omega hn);
  rewrite (add_0_right m hm);
  rewrite (add_0 n hn);
  refine equiv_class_eq (Sigma omega (λ _, omega)) (Pair (diff m n) empty)
    (Pair m n) intrel equiv_intrel _;
  refine intrelI (diff m n) empty m n _ (diff_type m n) zero_in_omega hm hn;
  rewrite (add_0_right m hm);
  refine add_diff_inverse2 n m hle hm
end;

opaque symbol raw_zadd_zminus_inverse (z : τ ι) :
  π (z ∈ int) → π (raw_zadd z (zminus z) = int_of empty) ≔
begin
  assume z hz;
  refine intE z _ hz _; assume x y hx hy hzeq;
  rewrite hzeq;
  rewrite (zminus_eq x y hx hy);
  rewrite (raw_zadd_eq x y y x hx hy hy hx);
  rewrite int_of_def; rewrite natify_0;
  refine equiv_class_eq (Sigma omega (λ _, omega))
    (Pair (add x y) (add y x)) (Pair empty empty) intrel equiv_intrel _;
  refine intrelI (add x y) (add y x) empty empty _
    (add_type x y) (add_type y x) zero_in_omega zero_in_omega;
  rewrite (add_0_right (add x y) (add_type x y));
  rewrite (add_0 (add y x) (add_type y x));
  refine add_commute x y
end;

opaque symbol zadd_zminus_inverse (z : τ ι) :
  π (zadd z (zminus z) = int_of empty) ≔
begin
  assume z;
  rewrite zadd_def;
  rewrite (intify_ident (zminus z) (zminus_type z));
  rewrite left (zminus_intify z);
  refine raw_zadd_zminus_inverse (intify z) (intify_in_int z)
end;

opaque symbol zadd_zminus_inverse2 (z : τ ι) :
  π (zadd (zminus z) z = int_of empty) ≔
begin
  assume z;
  rewrite (zadd_commute (zminus z) z);
  refine zadd_zminus_inverse z
end;

opaque symbol zadd_int0_right_intify (z : τ ι) :
  π (zadd z (int_of empty) = intify z) ≔
begin
  assume z;
  rewrite (zadd_commute z (int_of empty));
  refine zadd_int0_intify z
end;

opaque symbol zadd_int0_right (z : τ ι) :
  π (z ∈ int) → π (zadd z (int_of empty) = z) ≔
begin
  assume z hz;
  rewrite zadd_int0_right_intify;
  refine intify_ident z hz
end;

// ===========================================================================
// zmult: Integer Multiplication
// ===========================================================================

// Congruence property for multiplication
opaque symbol zmult_congruent2 :
  π (congruent2 intrel intrel (λ p1 p2,
    rel_image_sing intrel (Pair
      (add (mult (fst p1) (fst p2)) (mult (snd p1) (snd p2)))
      (add (mult (fst p1) (snd p2)) (mult (snd p1) (fst p2)))))) ≔
begin
  refine congruent2_commuteI (Sigma omega (λ _, omega)) intrel
    (λ p1 p2, rel_image_sing intrel (Pair
      (add (mult (fst p1) (fst p2)) (mult (snd p1) (snd p2)))
      (add (mult (fst p1) (snd p2)) (mult (snd p1) (fst p2)))))
    equiv_intrel _ _
  { // commutativity
    assume y z hyA hzA;
    rewrite (mult_commute (fst z) (fst y));
    rewrite (mult_commute (snd z) (snd y));
    rewrite (mult_commute (fst z) (snd y));
    rewrite (mult_commute (snd z) (fst y));
    rewrite (add_commute (mult (snd y) (fst z)) (mult (fst y) (snd z)));
    reflexivity }
  { // congruence in the second argument
    assume w y z hwA hyz;
    refine intrelE (Pair y z) _ hyz _;
    assume x1 y1 x2 y2 hpeq heq hx1 hy1 hx2 hy2;
    have hyp : π (y = Pair x1 y1) { refine Pair_inject1 _ _ _ _ hpeq };
    have hzp : π (z = Pair x2 y2) { refine Pair_inject2 _ _ _ _ hpeq };
    rewrite hyp; rewrite hzp;
    rewrite fst_conv; rewrite snd_conv; rewrite fst_conv; rewrite snd_conv;
    refine equiv_class_eq (Sigma omega (λ _, omega))
      (Pair (add (mult (fst w) x1) (mult (snd w) y1))
            (add (mult (fst w) y1) (mult (snd w) x1)))
      (Pair (add (mult (fst w) x2) (mult (snd w) y2))
            (add (mult (fst w) y2) (mult (snd w) x2))) intrel equiv_intrel _;
    have hyx : π (add y1 x2 = add y2 x1)
      { rewrite (add_commute y1 x2); rewrite (add_commute y2 x1);
        refine eq_sym heq };
    refine intrelI (add (mult (fst w) x1) (mult (snd w) y1))
      (add (mult (fst w) y1) (mult (snd w) x1))
      (add (mult (fst w) x2) (mult (snd w) y2))
      (add (mult (fst w) y2) (mult (snd w) x2)) _
      (add_type (mult (fst w) x1) (mult (snd w) y1))
      (add_type (mult (fst w) y1) (mult (snd w) x1))
      (add_type (mult (fst w) x2) (mult (snd w) y2))
      (add_type (mult (fst w) y2) (mult (snd w) x2));
    rewrite (add_interchange (mult (fst w) x1) (mult (snd w) y1)
      (mult (fst w) y2) (mult (snd w) x2));
    rewrite (add_interchange (mult (fst w) x2) (mult (snd w) y2)
      (mult (fst w) y1) (mult (snd w) x1));
    rewrite left (add_mult_distrib_left (fst w) x1 y2);
    rewrite left (add_mult_distrib_left (snd w) y1 x2);
    rewrite left (add_mult_distrib_left (fst w) x2 y1);
    rewrite left (add_mult_distrib_left (snd w) y2 x1);
    rewrite heq;
    rewrite hyx;
    reflexivity }
end;

opaque symbol raw_zmult_type (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (raw_zmult z w ∈ int) ≔
begin
  assume z w hz hw;
  have hzq : π (z ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ v, z ∈ v) hz };
  have hwq : π (w ∈ quotient (Sigma omega (λ _, omega)) intrel)
    { refine ind_eq (eq_sym int_def) (λ v, w ∈ v) hw };
  rewrite raw_zmult_def;
  rewrite int_def;
  refine UN_equiv_class_type2 (Sigma omega (λ _, omega)) intrel
    (quotient (Sigma omega (λ _, omega)) intrel) z w
    (λ p1 p2, rel_image_sing intrel (Pair
      (add (mult (fst p1) (fst p2)) (mult (snd p1) (snd p2)))
      (add (mult (fst p1) (snd p2)) (mult (snd p1) (fst p2)))))
    equiv_intrel zmult_congruent2 hzq hwq _;
  assume x1 x2 h1 h2;
  refine quotientI (Pair
      (add (mult (fst x1) (fst x2)) (mult (snd x1) (snd x2)))
      (add (mult (fst x1) (snd x2)) (mult (snd x1) (fst x2))))
    (Sigma omega (λ _, omega)) intrel
    (SigmaI (add (mult (fst x1) (fst x2)) (mult (snd x1) (snd x2)))
      (add (mult (fst x1) (snd x2)) (mult (snd x1) (fst x2))) omega (λ _, omega)
      (add_type (mult (fst x1) (fst x2)) (mult (snd x1) (snd x2)))
      (add_type (mult (fst x1) (snd x2)) (mult (snd x1) (fst x2))))
end;

opaque symbol zmult_type (z w : τ ι) : π (zmult z w ∈ int) ≔
begin
  assume z w;
  rewrite zmult_def;
  refine raw_zmult_type (intify z) (intify w) (intify_in_int z) (intify_in_int w)
end;

// raw_zmult (name collision with the `raw_zmult` definition; see header)
opaque symbol raw_zmult_eq (x1 y1 x2 y2 : τ ι) :
  π (x1 ∈ omega) → π (y1 ∈ omega) → π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (raw_zmult (rel_image_sing intrel (Pair x1 y1)) (rel_image_sing intrel (Pair x2 y2))
     = rel_image_sing intrel
         (Pair (add (mult x1 x2) (mult y1 y2)) (add (mult x1 y2) (mult y1 x2)))) ≔
begin
  assume x1 y1 x2 y2 h1 h2 h3 h4;
  rewrite raw_zmult_def;
  refine eq_trans (UN_equiv_class2 (Sigma omega (λ _, omega))
    (Sigma omega (λ _, omega)) intrel intrel
    (λ p1 p2, rel_image_sing intrel (Pair
      (add (mult (fst p1) (fst p2)) (mult (snd p1) (snd p2)))
      (add (mult (fst p1) (snd p2)) (mult (snd p1) (fst p2)))))
    (Pair x1 y1) (Pair x2 y2) equiv_intrel equiv_intrel zmult_congruent2
    (SigmaI x1 y1 omega (λ _, omega) h1 h2)
    (SigmaI x2 y2 omega (λ _, omega) h3 h4)) _;
  rewrite fst_conv; rewrite snd_conv; rewrite fst_conv; rewrite snd_conv;
  reflexivity
end;

// zmult (name collision with the `zmult` definition; see header)
opaque symbol zmult_eq (x1 y1 x2 y2 : τ ι) :
  π (x1 ∈ omega) → π (y1 ∈ omega) → π (x2 ∈ omega) → π (y2 ∈ omega) →
  π (zmult (rel_image_sing intrel (Pair x1 y1)) (rel_image_sing intrel (Pair x2 y2))
     = rel_image_sing intrel
         (Pair (add (mult x1 x2) (mult y1 y2)) (add (mult x1 y2) (mult y1 x2)))) ≔
begin
  assume x1 y1 x2 y2 h1 h2 h3 h4;
  rewrite zmult_def;
  rewrite (intify_ident (rel_image_sing intrel (Pair x1 y1))
    (image_intrel_int x1 y1 h1 h2));
  rewrite (intify_ident (rel_image_sing intrel (Pair x2 y2))
    (image_intrel_int x2 y2 h3 h4));
  refine raw_zmult_eq x1 y1 x2 y2 h1 h2 h3 h4
end;

opaque symbol raw_zmult_int0 (z : τ ι) :
  π (z ∈ int) → π (raw_zmult (int_of empty) z = int_of empty) ≔
begin
  assume z hz;
  refine intE z _ hz _; assume x y hx hy hzeq;
  rewrite hzeq;
  rewrite int_of_def; rewrite natify_0;
  rewrite (raw_zmult_eq empty empty x y zero_in_omega zero_in_omega hx hy);
  rewrite (mult_0 x); rewrite (mult_0 y);
  rewrite (add_0 empty zero_in_omega);
  reflexivity
end;

opaque symbol zmult_int0 (z : τ ι) : π (zmult (int_of empty) z = int_of empty) ≔
begin
  assume z;
  rewrite zmult_def;
  rewrite (intify_ident (int_of empty) (int_of_type empty));
  refine raw_zmult_int0 (intify z) (intify_in_int z)
end;

opaque symbol raw_zmult_int1 (z : τ ι) :
  π (z ∈ int) → π (raw_zmult (int_of (succ empty)) z = z) ≔
begin
  assume z hz;
  refine intE z _ hz _; assume x y hx hy hzeq;
  rewrite hzeq;
  rewrite int_of_def;
  rewrite natify_succ; rewrite natify_0;
  rewrite (raw_zmult_eq (succ empty) empty x y nat_1I zero_in_omega hx hy);
  rewrite (mult_1 x hx); rewrite (mult_1 y hy);
  rewrite (mult_0 x); rewrite (mult_0 y);
  rewrite (add_0_right x hx); rewrite (add_0_right y hy);
  reflexivity
end;

opaque symbol zmult_int1_intify (z : τ ι) :
  π (zmult (int_of (succ empty)) z = intify z) ≔
begin
  assume z;
  rewrite zmult_def;
  rewrite (intify_ident (int_of (succ empty)) (int_of_type (succ empty)));
  refine raw_zmult_int1 (intify z) (intify_in_int z)
end;

opaque symbol zmult_int1 (z : τ ι) :
  π (z ∈ int) → π (zmult (int_of (succ empty)) z = z) ≔
begin
  assume z hz;
  rewrite zmult_int1_intify;
  refine intify_ident z hz
end;

opaque symbol raw_zmult_commute (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (raw_zmult z w = raw_zmult w z) ≔
begin
  assume z w hz hw;
  refine intE z _ hz _; assume x1 y1 hx1 hy1 hzeq;
  refine intE w _ hw _; assume x2 y2 hx2 hy2 hweq;
  rewrite hzeq; rewrite hweq;
  rewrite (raw_zmult_eq x1 y1 x2 y2 hx1 hy1 hx2 hy2);
  rewrite (raw_zmult_eq x2 y2 x1 y1 hx2 hy2 hx1 hy1);
  rewrite (mult_commute x2 x1);
  rewrite (mult_commute y2 y1);
  rewrite (mult_commute x2 y1);
  rewrite (mult_commute y2 x1);
  rewrite (add_commute (mult y1 x2) (mult x1 y2));
  reflexivity
end;

opaque symbol zmult_commute (z w : τ ι) : π (zmult z w = zmult w z) ≔
begin
  assume z w;
  rewrite zmult_def; rewrite zmult_def;
  refine raw_zmult_commute (intify z) (intify w)
    (intify_in_int z) (intify_in_int w)
end;

opaque symbol raw_zmult_zminus (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) →
  π (raw_zmult (zminus z) w = zminus (raw_zmult z w)) ≔
begin
  assume z w hz hw;
  refine intE z _ hz _; assume x1 y1 hx1 hy1 hzeq;
  refine intE w _ hw _; assume x2 y2 hx2 hy2 hweq;
  rewrite hzeq; rewrite hweq;
  rewrite (zminus_eq x1 y1 hx1 hy1);
  rewrite (raw_zmult_eq y1 x1 x2 y2 hy1 hx1 hx2 hy2);
  rewrite (raw_zmult_eq x1 y1 x2 y2 hx1 hy1 hx2 hy2);
  rewrite (zminus_eq (add (mult x1 x2) (mult y1 y2))
    (add (mult x1 y2) (mult y1 x2))
    (add_type (mult x1 x2) (mult y1 y2))
    (add_type (mult x1 y2) (mult y1 x2)));
  rewrite (add_commute (mult y1 x2) (mult x1 y2));
  rewrite (add_commute (mult y1 y2) (mult x1 x2));
  reflexivity
end;

opaque symbol zmult_zminus (z w : τ ι) :
  π (zmult (zminus z) w = zminus (zmult z w)) ≔
begin
  assume z w;
  rewrite zmult_def; rewrite zmult_def;
  rewrite (intify_ident (zminus z) (zminus_type z));
  rewrite left (zminus_intify z);
  refine raw_zmult_zminus (intify z) (intify w)
    (intify_in_int z) (intify_in_int w)
end;

opaque symbol zmult_zminus_right (w z : τ ι) :
  π (zmult w (zminus z) = zminus (zmult w z)) ≔
begin
  assume w z;
  rewrite (zmult_commute w (zminus z));
  rewrite (zmult_commute w z);
  refine zmult_zminus z w
end;

opaque symbol raw_zmult_assoc (z1 z2 z3 : τ ι) :
  π (z1 ∈ int) → π (z2 ∈ int) → π (z3 ∈ int) →
  π (raw_zmult (raw_zmult z1 z2) z3 = raw_zmult z1 (raw_zmult z2 z3)) ≔
begin
  assume z1 z2 z3 h1 h2 h3;
  refine intE z1 _ h1 _; assume a b ha hb he1;
  refine intE z2 _ h2 _; assume c d hc hd he2;
  refine intE z3 _ h3 _; assume e f he hf he3;
  rewrite he1; rewrite he2; rewrite he3;
  rewrite (raw_zmult_eq a b c d ha hb hc hd);
  rewrite (raw_zmult_eq (add (mult a c) (mult b d)) (add (mult a d) (mult b c)) e f
    (add_type (mult a c) (mult b d)) (add_type (mult a d) (mult b c)) he hf);
  rewrite (raw_zmult_eq c d e f hc hd he hf);
  rewrite (raw_zmult_eq a b (add (mult c e) (mult d f)) (add (mult c f) (mult d e))
    ha hb (add_type (mult c e) (mult d f)) (add_type (mult c f) (mult d e)));
  rewrite add_mult_distrib; rewrite add_mult_distrib;
  rewrite add_mult_distrib; rewrite add_mult_distrib;
  rewrite mult_assoc; rewrite mult_assoc; rewrite mult_assoc; rewrite mult_assoc;
  rewrite mult_assoc; rewrite mult_assoc; rewrite mult_assoc; rewrite mult_assoc;
  rewrite (add_interchange (mult a (mult c e)) (mult b (mult d e))
    (mult a (mult d f)) (mult b (mult c f)));
  rewrite (add_interchange (mult a (mult c f)) (mult b (mult d f))
    (mult a (mult d e)) (mult b (mult c e)));
  rewrite left (add_mult_distrib_left a (mult c e) (mult d f));
  rewrite left (add_mult_distrib_left b (mult d e) (mult c f));
  rewrite left (add_mult_distrib_left a (mult c f) (mult d e));
  rewrite left (add_mult_distrib_left b (mult d f) (mult c e));
  rewrite (add_commute (mult d e) (mult c f));
  rewrite (add_commute (mult d f) (mult c e));
  reflexivity
end;

opaque symbol zmult_assoc (z1 z2 z3 : τ ι) :
  π (zmult (zmult z1 z2) z3 = zmult z1 (zmult z2 z3)) ≔
begin
  assume z1 z2 z3;
  rewrite zmult_def; rewrite zmult_def; rewrite zmult_def; rewrite zmult_def;
  rewrite (intify_ident (raw_zmult (intify z1) (intify z2))
    (raw_zmult_type (intify z1) (intify z2) (intify_in_int z1) (intify_in_int z2)));
  rewrite (intify_ident (raw_zmult (intify z2) (intify z3))
    (raw_zmult_type (intify z2) (intify z3) (intify_in_int z2) (intify_in_int z3)));
  refine raw_zmult_assoc (intify z1) (intify z2) (intify z3)
    (intify_in_int z1) (intify_in_int z2) (intify_in_int z3)
end;

// For AC rewriting
opaque symbol zmult_left_commute (z1 z2 z3 : τ ι) :
  π (zmult z1 (zmult z2 z3) = zmult z2 (zmult z1 z3)) ≔
begin
  assume z1 z2 z3;
  rewrite left (zmult_assoc z1 z2 z3);
  rewrite left (zmult_assoc z2 z1 z3);
  rewrite (zmult_commute z1 z2);
  reflexivity
end;

// (Integer multiplication is an AC operator: `lemmas zmult_ac = zmult_assoc
// zmult_commute zmult_left_commute` — a hint-list bundle, skipped.)

opaque symbol raw_zadd_zmult_distrib (z1 z2 w : τ ι) :
  π (z1 ∈ int) → π (z2 ∈ int) → π (w ∈ int) →
  π (raw_zmult (raw_zadd z1 z2) w = raw_zadd (raw_zmult z1 w) (raw_zmult z2 w)) ≔
begin
  assume z1 z2 w h1 h2 hw;
  refine intE z1 _ h1 _; assume a b ha hb he1;
  refine intE z2 _ h2 _; assume c d hc hd he2;
  refine intE w _ hw _; assume e f he hf hew;
  rewrite he1; rewrite he2; rewrite hew;
  rewrite (raw_zadd_eq a b c d ha hb hc hd);
  rewrite (raw_zmult_eq (add a c) (add b d) e f
    (add_type a c) (add_type b d) he hf);
  rewrite (raw_zmult_eq a b e f ha hb he hf);
  rewrite (raw_zmult_eq c d e f hc hd he hf);
  rewrite (raw_zadd_eq (add (mult a e) (mult b f)) (add (mult a f) (mult b e))
    (add (mult c e) (mult d f)) (add (mult c f) (mult d e))
    (add_type (mult a e) (mult b f)) (add_type (mult a f) (mult b e))
    (add_type (mult c e) (mult d f)) (add_type (mult c f) (mult d e)));
  rewrite add_mult_distrib; rewrite add_mult_distrib;
  rewrite add_mult_distrib; rewrite add_mult_distrib;
  rewrite (add_interchange (mult a e) (mult c e) (mult b f) (mult d f));
  rewrite (add_interchange (mult a f) (mult c f) (mult b e) (mult d e));
  reflexivity
end;

opaque symbol zadd_zmult_distrib (z1 z2 w : τ ι) :
  π (zmult (zadd z1 z2) w = zadd (zmult z1 w) (zmult z2 w)) ≔
begin
  assume z1 z2 w;
  rewrite zmult_def;
  rewrite zadd_def;
  rewrite (intify_ident (raw_zadd (intify z1) (intify z2))
    (raw_zadd_type (intify z1) (intify z2) (intify_in_int z1) (intify_in_int z2)));
  rewrite zadd_def;
  rewrite zmult_def; rewrite zmult_def;
  rewrite (intify_ident (raw_zmult (intify z1) (intify w))
    (raw_zmult_type (intify z1) (intify w) (intify_in_int z1) (intify_in_int w)));
  rewrite (intify_ident (raw_zmult (intify z2) (intify w))
    (raw_zmult_type (intify z2) (intify w) (intify_in_int z2) (intify_in_int w)));
  refine raw_zadd_zmult_distrib (intify z1) (intify z2) (intify w)
    (intify_in_int z1) (intify_in_int z2) (intify_in_int w)
end;

opaque symbol zadd_zmult_distrib2 (w z1 z2 : τ ι) :
  π (zmult w (zadd z1 z2) = zadd (zmult w z1) (zmult w z2)) ≔
begin
  assume w z1 z2;
  rewrite (zmult_commute w (zadd z1 z2));
  rewrite (zmult_commute w z1);
  rewrite (zmult_commute w z2);
  refine zadd_zmult_distrib z1 z2 w
end;

// (`lemmas int_typechecks = int_of_type zminus_type zmagnitude_type
// zadd_type zmult_type` — a hint-list bundle, skipped; see header.)

// ===========================================================================
// Subtraction laws
// ===========================================================================

opaque symbol zdiff_type (z w : τ ι) : π (zdiff z w ∈ int) ≔
begin
  assume z w;
  rewrite zdiff_def;
  refine zadd_type z (zminus w)
end;

opaque symbol zminus_zdiff_eq (z y : τ ι) : π (zminus (zdiff z y) = zdiff y z) ≔
begin
  assume z y;
  rewrite zdiff_def; rewrite zdiff_def;
  rewrite zminus_zadd_distrib;
  rewrite zminus_zminus_intify;
  rewrite (zadd_intify2 (zminus z) y);
  refine zadd_commute (zminus z) y
end;

opaque symbol zdiff_zmult_distrib (z1 z2 w : τ ι) :
  π (zmult (zdiff z1 z2) w = zdiff (zmult z1 w) (zmult z2 w)) ≔
begin
  assume z1 z2 w;
  rewrite zdiff_def; rewrite zdiff_def;
  rewrite (zadd_zmult_distrib z1 (zminus z2) w);
  rewrite (zmult_zminus z2 w);
  reflexivity
end;

opaque symbol zdiff_zmult_distrib2 (w z1 z2 : τ ι) :
  π (zmult w (zdiff z1 z2) = zdiff (zmult w z1) (zmult w z2)) ≔
begin
  assume w z1 z2;
  rewrite (zmult_commute w (zdiff z1 z2));
  rewrite (zmult_commute w z1);
  rewrite (zmult_commute w z2);
  refine zdiff_zmult_distrib z1 z2 w
end;

opaque symbol zadd_zdiff_eq (x y z : τ ι) :
  π (zadd x (zdiff y z) = zdiff (zadd x y) z) ≔
begin
  assume x y z;
  rewrite zdiff_def; rewrite zdiff_def;
  refine eq_sym (zadd_assoc x y (zminus z))
end;

opaque symbol zdiff_zadd_eq (x y z : τ ι) :
  π (zadd (zdiff x y) z = zdiff (zadd x z) y) ≔
begin
  assume x y z;
  rewrite zdiff_def; rewrite zdiff_def;
  rewrite (zadd_assoc x (zminus y) z);
  rewrite (zadd_assoc x z (zminus y));
  rewrite (zadd_commute (zminus y) z);
  reflexivity
end;

// ===========================================================================
// The "Less Than" Relation
// ===========================================================================

// "Less than" is a linear ordering
opaque symbol zless_linear_lemma (z w : τ ι) :
  π (z ∈ int) → π (w ∈ int) → π (zless z w ∨ z = w ∨ zless w z) ≔
begin
  assume z w hz hw;
  refine intE z _ hz _; assume x1 y1 hx1 hy1 he1;
  refine intE w _ hw _; assume x2 y2 hx2 hy2 he2;
  have hzw : π (zdiff z w = rel_image_sing intrel (Pair (add x1 y2) (add y1 x2)))
    { rewrite zdiff_def; rewrite he1; rewrite he2;
      rewrite (zminus_eq x2 y2 hx2 hy2);
      rewrite (zadd_eq x1 y1 y2 x2 hx1 hy1 hy2 hx2);
      reflexivity };
  have hwz : π (zdiff w z = rel_image_sing intrel (Pair (add x2 y1) (add y2 x1)))
    { rewrite zdiff_def; rewrite he1; rewrite he2;
      rewrite (zminus_eq x1 y1 hx1 hy1);
      rewrite (zadd_eq x2 y2 y1 x1 hx2 hy2 hy1 hx1);
      reflexivity };
  have hOa : π (Ord (add x1 y2)) { refine nat_into_Ord (add x1 y2) (add_type x1 y2) };
  have hOb : π (Ord (add y1 x2)) { refine nat_into_Ord (add y1 x2) (add_type y1 x2) };
  refine ∨ₑ (Ord_linear (add x1 y2) (add y1 x2) hOa hOb) _ _
  { assume hmem;
    refine ∨ᵢ₁ _;
    rewrite zless_def;
    rewrite hzw;
    refine ∧ₑ₂ (znegative_eq (add x1 y2) (add y1 x2)
        (add_type x1 y2) (add_type y1 x2))
      (ltI (add x1 y2) (add y1 x2) hmem hOb) }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume heq;
      refine ∨ᵢ₂ (∨ᵢ₁ _);
      rewrite he1; rewrite he2;
      refine equiv_class_eq (Sigma omega (λ _, omega)) (Pair x1 y1) (Pair x2 y2)
        intrel equiv_intrel _;
      refine intrelI x1 y1 x2 y2 _ hx1 hy1 hx2 hy2;
      rewrite heq;
      refine add_commute y1 x2 }
    { assume hmem2;
      refine ∨ᵢ₂ (∨ᵢ₂ _);
      rewrite zless_def;
      rewrite hwz;
      refine ∧ₑ₂ (znegative_eq (add x2 y1) (add y2 x1)
          (add_type x2 y1) (add_type y2 x1)) _;
      rewrite (add_commute x2 y1); rewrite (add_commute y2 x1);
      refine ltI (add y1 x2) (add x1 y2) hmem2 hOa } }
end;

opaque symbol zless_linear (z w : τ ι) :
  π (zless z w ∨ intify z = intify w ∨ zless w z) ≔
begin
  assume z w;
  refine ∨ₑ (zless_linear_lemma (intify z) (intify w)
    (intify_in_int z) (intify_in_int w)) _ _
  { assume h;
    refine ∨ᵢ₁ (∧ₑ₁ (zless_intify2 z w) (∧ₑ₁ (zless_intify1 z (intify w)) h)) }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume heq; refine ∨ᵢ₂ (∨ᵢ₁ heq) }
    { assume h;
      refine ∨ᵢ₂ (∨ᵢ₂ (∧ₑ₁ (zless_intify2 w z)
        (∧ₑ₁ (zless_intify1 w (intify z)) h))) } }
end;

opaque symbol zless_not_refl (z : τ ι) : π (¬ zless z z) ≔
begin
  assume z hlt;
  have h1 : π (znegative (zdiff z z))
    { refine ind_eq (eq_sym (zless_def z z)) (λ p, p) hlt };
  have h2 : π (zdiff z z = int_of empty)
    { rewrite zdiff_def; refine zadd_zminus_inverse z };
  refine not_znegative_int_of empty (ind_eq (eq_sym h2) (λ v, znegative v) h1)
end;

opaque symbol neq_iff_zless (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (x ≠ y ⇔ (zless x y ∨ zless y x)) ≔
begin
  assume x y hx hy;
  apply ∧ᵢ
  { assume hne;
    refine ∨ₑ (zless_linear_lemma x y hx hy) _ _
    { assume h; refine ∨ᵢ₁ h }
    { assume hrest;
      refine ∨ₑ hrest _ _
      { assume heq; refine ⊥ₑ (hne heq) }
      { assume h; refine ∨ᵢ₂ h } } }
  { assume hd heq;
    refine ∨ₑ hd _ _
    { assume h;
      refine zless_not_refl y (ind_eq (eq_sym heq) (λ v, zless v y) h) }
    { assume h;
      refine zless_not_refl y (ind_eq (eq_sym heq) (λ v, zless y v) h) } }
end;

opaque symbol zless_imp_intify_neq (w z : τ ι) :
  π (zless w z) → π (intify w ≠ intify z) ≔
begin
  assume w z hlt heq;
  have h1 : π (zless (intify w) (intify z))
    { refine ∧ₑ₂ (zless_intify1 w (intify z)) (∧ₑ₂ (zless_intify2 w z) hlt) };
  refine zless_not_refl (intify z)
    (ind_eq (eq_sym heq) (λ v, zless v (intify z)) h1)
end;

// This lemma allows direct proofs of other <-properties
opaque symbol zless_imp_succ_zadd_lemma (w z : τ ι) :
  π (zless w z) → π (w ∈ int) → π (z ∈ int) →
  π (Bex omega (λ n, z = zadd w (int_of (succ n)))) ≔
begin
  assume w z hlt hw hz;
  refine intE w _ hw _; assume x1 y1 hx1 hy1 he1;
  refine intE z _ hz _; assume x2 y2 hx2 hy2 he2;
  have hd : π (zdiff w z = rel_image_sing intrel (Pair (add x1 y2) (add y1 x2)))
    { rewrite zdiff_def; rewrite he1; rewrite he2;
      rewrite (zminus_eq x2 y2 hx2 hy2);
      rewrite (zadd_eq x1 y1 y2 x2 hx1 hy1 hy2 hx2);
      reflexivity };
  have hzneg : π (znegative (zdiff w z))
    { refine ind_eq (eq_sym (zless_def w z)) (λ p, p) hlt };
  have hltn : π (lt (add x1 y2) (add y1 x2))
    { refine ∧ₑ₁ (znegative_eq (add x1 y2) (add y1 x2)
        (add_type x1 y2) (add_type y1 x2))
        (ind_eq (eq_sym hd) (λ v, znegative v) hzneg) };
  refine ∃ₑ (less_imp_succ_add (add x1 y2) (add y1 x2) hltn (add_type y1 x2)) _;
  assume k hkk;
  have hkw : π (k ∈ omega) { refine ∧ₑ₁ hkk };
  have hk : π (add y1 x2 = succ (add (add x1 y2) k)) { refine ∧ₑ₂ hkk };
  refine ∃ᵢ k (∧ᵢ hkw _);
  rewrite he1; rewrite he2;
  rewrite int_of_def;
  rewrite natify_succ; rewrite (natify_ident k hkw);
  rewrite (zadd_eq x1 y1 (succ k) empty hx1 hy1
    (succ_in_omega k hkw) zero_in_omega);
  refine equiv_class_eq (Sigma omega (λ _, omega)) (Pair x2 y2)
    (Pair (add x1 (succ k)) (add y1 empty)) intrel equiv_intrel _;
  refine intrelI x2 y2 (add x1 (succ k)) (add y1 empty) _ hx2 hy2
    (add_type x1 (succ k)) (add_type y1 empty);
  rewrite (add_0_right y1 hy1);
  rewrite (add_commute x2 y1);
  rewrite hk;
  rewrite (add_succ_right x1 k);
  rewrite (add_succ (add x1 k) y2);
  rewrite (add_assoc x1 y2 k);
  rewrite (add_assoc x1 k y2);
  rewrite (add_commute k y2);
  reflexivity
end;

opaque symbol zless_imp_succ_zadd (w z : τ ι) :
  π (zless w z) → π (Bex omega (λ n, zadd w (int_of (succ n)) = intify z)) ≔
begin
  assume w z hlt;
  have h1 : π (zless (intify w) (intify z))
    { refine ∧ₑ₂ (zless_intify1 w (intify z)) (∧ₑ₂ (zless_intify2 w z) hlt) };
  refine ∃ₑ (zless_imp_succ_zadd_lemma (intify w) (intify z) h1
    (intify_in_int w) (intify_in_int z)) _;
  assume n hn;
  refine ∃ᵢ n (∧ᵢ (∧ₑ₁ hn) _);
  rewrite left (zadd_intify1 w (int_of (succ n)));
  refine eq_sym (∧ₑ₂ hn)
end;

opaque symbol zless_succ_zadd_lemma (w n : τ ι) :
  π (w ∈ int) → π (zless w (zadd w (int_of (succ n)))) ≔
begin
  assume w n hw;
  refine intE w _ hw _; assume x y hx hy hweq;
  rewrite zless_def;
  rewrite zdiff_def;
  rewrite hweq;
  rewrite int_of_def; rewrite natify_succ;
  rewrite (zadd_eq x y (succ (natify n)) empty hx hy
    (succ_in_omega (natify n) (natify_in_nat n)) zero_in_omega);
  rewrite (zminus_eq (add x (succ (natify n))) (add y empty)
    (add_type x (succ (natify n))) (add_type y empty));
  rewrite (zadd_eq x y (add y empty) (add x (succ (natify n)))
    hx hy (add_type y empty) (add_type x (succ (natify n))));
  refine ∧ₑ₂ (znegative_eq (add x (add y empty))
    (add y (add x (succ (natify n))))
    (add_type x (add y empty))
    (add_type y (add x (succ (natify n))))) _;
  rewrite (add_0_right y hy);
  rewrite (add_succ_right x (natify n));
  rewrite (add_succ_right y (add x (natify n)));
  rewrite (add_left_commute y x (natify n));
  rewrite left (add_assoc x y (natify n));
  refine add_le_self (add x y) (natify n) (add_type x y)
end;

opaque symbol zless_succ_zadd (w n : τ ι) :
  π (zless w (zadd w (int_of (succ n)))) ≔
begin
  assume w n;
  have h1 : π (zless (intify w) (zadd (intify w) (int_of (succ n))))
    { refine zless_succ_zadd_lemma (intify w) n (intify_in_int w) };
  have h2 : π (zless (intify w) (zadd w (int_of (succ n))))
    { rewrite left (zadd_intify1 w (int_of (succ n))); refine h1 };
  refine ∧ₑ₁ (zless_intify1 w (zadd w (int_of (succ n)))) h2
end;

opaque symbol zless_iff_succ_zadd (w z : τ ι) :
  π (zless w z ⇔ Bex omega (λ n, zadd w (int_of (succ n)) = intify z)) ≔
begin
  assume w z;
  apply ∧ᵢ
  { assume h; refine zless_imp_succ_zadd w z h }
  { assume h;
    refine ∃ₑ h _; assume n hn;
    have h1 : π (zless w (zadd w (int_of (succ n))))
      { refine zless_succ_zadd w n };
    have h2 : π (zless w (intify z))
      { refine ind_eq (eq_sym (∧ₑ₂ hn)) (λ v, zless w v) h1 };
    refine ∧ₑ₁ (zless_intify2 w z) h2 }
end;

opaque symbol zless_int_of (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (zless (int_of m) (int_of n) ⇔ lt m n) ≔
begin
  assume m n hm hn;
  have hd : π (zdiff (int_of m) (int_of n) = rel_image_sing intrel (Pair m n))
    { rewrite zdiff_def;
      rewrite int_of_def; rewrite (natify_ident m hm);
      rewrite int_of_def; rewrite (natify_ident n hn);
      rewrite (zminus_eq n empty hn zero_in_omega);
      rewrite (zadd_eq m empty empty n hm zero_in_omega zero_in_omega hn);
      rewrite (add_0_right m hm);
      rewrite (add_0 n hn);
      reflexivity };
  apply ∧ᵢ
  { assume h;
    have h1 : π (znegative (zdiff (int_of m) (int_of n)))
      { refine ind_eq (eq_sym (zless_def (int_of m) (int_of n))) (λ p, p) h };
    refine ∧ₑ₁ (znegative_eq m n hm hn)
      (ind_eq (eq_sym hd) (λ v, znegative v) h1) }
  { assume h;
    rewrite zless_def;
    rewrite hd;
    refine ∧ₑ₂ (znegative_eq m n hm hn) h }
end;

opaque symbol zless_trans_lemma (x y z : τ ι) :
  π (zless x y) → π (zless y z) → π (x ∈ int) → π (y ∈ int) → π (z ∈ int) →
  π (zless x z) ≔
begin
  assume x y z hxy hyz hx hy hz;
  refine ∃ₑ (zless_imp_succ_zadd_lemma x y hxy hx hy) _; assume m hm;
  refine ∃ₑ (zless_imp_succ_zadd_lemma y z hyz hy hz) _; assume n hn;
  have hz2 : π (z = zadd x (int_of (succ (add m (succ n)))))
    { rewrite (∧ₑ₂ hn); rewrite (∧ₑ₂ hm);
      rewrite (zadd_assoc x (int_of (succ m)) (int_of (succ n)));
      rewrite left (int_of_add (succ m) (succ n));
      rewrite (add_succ m (succ n));
      reflexivity };
  have hless : π (zless x (zadd x (int_of (succ (add m (succ n))))))
    { refine zless_succ_zadd_lemma x (add m (succ n)) hx };
  refine ind_eq hz2 (λ v, zless x v) hless
end;

opaque symbol zless_trans (x y z : τ ι) :
  π (zless x y) → π (zless y z) → π (zless x z) ≔
begin
  assume x y z hxy hyz;
  have h1 : π (zless (intify x) (intify y))
    { refine ∧ₑ₂ (zless_intify1 x (intify y)) (∧ₑ₂ (zless_intify2 x y) hxy) };
  have h2 : π (zless (intify y) (intify z))
    { refine ∧ₑ₂ (zless_intify1 y (intify z)) (∧ₑ₂ (zless_intify2 y z) hyz) };
  have h3 : π (zless (intify x) (intify z))
    { refine zless_trans_lemma (intify x) (intify y) (intify z) h1 h2
        (intify_in_int x) (intify_in_int y) (intify_in_int z) };
  refine ∧ₑ₁ (zless_intify2 x z) (∧ₑ₁ (zless_intify1 x (intify z)) h3)
end;

opaque symbol zless_not_sym (z w : τ ι) : π (zless z w) → π (¬ zless w z) ≔
begin
  assume z w hzw hwz;
  refine zless_not_refl z (zless_trans z w z hzw hwz)
end;

// zless_asym = zless_not_sym [THEN swap] : ⟦z $< w; ¬P ⟹ w $< z⟧ ⟹ P
opaque symbol zless_asym (z w : τ ι) (P : Prop) :
  π (zless z w) → (π (¬ P) → π (zless w z)) → π P ≔
begin
  assume z w P hzw hcontra;
  refine ∨ₑ (em P) _ _
  { assume hP; refine hP }
  { assume hnP; refine ⊥ₑ (zless_not_sym z w hzw (hcontra hnP)) }
end;

opaque symbol zless_imp_zle (z w : τ ι) : π (zless z w) → π (zle z w) ≔
begin
  assume z w h;
  rewrite zle_def;
  refine ∨ᵢ₁ h
end;

opaque symbol zle_linear (z w : τ ι) : π (zle z w ∨ zle w z) ≔
begin
  assume z w;
  refine ∨ₑ (zless_linear z w) _ _
  { assume h; refine ∨ᵢ₁ _; rewrite zle_def; refine ∨ᵢ₁ h }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume heq; refine ∨ᵢ₁ _; rewrite zle_def; refine ∨ᵢ₂ heq }
    { assume h; refine ∨ᵢ₂ _; rewrite zle_def; refine ∨ᵢ₁ h } }
end;

// ===========================================================================
// Less Than or Equals
// ===========================================================================

opaque symbol zle_refl (z : τ ι) : π (zle z z) ≔
begin
  assume z;
  rewrite zle_def;
  refine ∨ᵢ₂ (eq_refl (intify z))
end;

opaque symbol zle_eq_refl (x y : τ ι) : π (x = y) → π (zle x y) ≔
begin
  assume x y h;
  rewrite h;
  refine zle_refl y
end;

opaque symbol zle_anti_sym_intify (x y : τ ι) :
  π (zle x y) → π (zle y x) → π (intify x = intify y) ≔
begin
  assume x y hxy hyx;
  have h1 : π (zless x y ∨ intify x = intify y)
    { refine ind_eq (eq_sym (zle_def x y)) (λ p, p) hxy };
  have h2 : π (zless y x ∨ intify y = intify x)
    { refine ind_eq (eq_sym (zle_def y x)) (λ p, p) hyx };
  refine ∨ₑ h1 _ _
  { assume hlt1;
    refine ∨ₑ h2 _ _
    { assume hlt2; refine ⊥ₑ (zless_not_sym x y hlt1 hlt2) }
    { assume heq; refine eq_sym heq } }
  { assume heq; refine heq }
end;

opaque symbol zle_anti_sym (x y : τ ι) :
  π (zle x y) → π (zle y x) → π (x ∈ int) → π (y ∈ int) → π (x = y) ≔
begin
  assume x y hxy hyx hx hy;
  have h : π (intify x = intify y) { refine zle_anti_sym_intify x y hxy hyx };
  refine eq_trans (eq_sym (intify_ident x hx)) (eq_trans h (intify_ident y hy))
end;

opaque symbol zle_trans_lemma (x y z : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (z ∈ int) → π (zle x y) → π (zle y z) →
  π (zle x z) ≔
begin
  assume x y z hx hy hz hxy hyz;
  have h1 : π (zless x y ∨ intify x = intify y)
    { refine ind_eq (eq_sym (zle_def x y)) (λ p, p) hxy };
  have h2 : π (zless y z ∨ intify y = intify z)
    { refine ind_eq (eq_sym (zle_def y z)) (λ p, p) hyz };
  rewrite zle_def;
  refine ∨ₑ h1 _ _
  { assume hlt1;
    refine ∨ₑ h2 _ _
    { assume hlt2; refine ∨ᵢ₁ (zless_trans x y z hlt1 hlt2) }
    { assume heq2;
      have hyz_eq : π (y = z)
        { refine eq_trans (eq_sym (intify_ident y hy))
            (eq_trans heq2 (intify_ident z hz)) };
      refine ∨ᵢ₁ (ind_eq (eq_sym hyz_eq) (λ v, zless x v) hlt1) } }
  { assume heq1;
    have hxy_eq : π (x = y)
      { refine eq_trans (eq_sym (intify_ident x hx))
          (eq_trans heq1 (intify_ident y hy)) };
    refine ∨ₑ h2 _ _
    { assume hlt2; refine ∨ᵢ₁ (ind_eq hxy_eq (λ v, zless v z) hlt2) }
    { assume heq2; refine ∨ᵢ₂ (eq_trans heq1 heq2) } }
end;

opaque symbol zle_trans (x y z : τ ι) :
  π (zle x y) → π (zle y z) → π (zle x z) ≔
begin
  assume x y z hxy hyz;
  have h1 : π (zle (intify x) (intify y))
    { refine ∧ₑ₂ (zle_intify1 x (intify y)) (∧ₑ₂ (zle_intify2 x y) hxy) };
  have h2 : π (zle (intify y) (intify z))
    { refine ∧ₑ₂ (zle_intify1 y (intify z)) (∧ₑ₂ (zle_intify2 y z) hyz) };
  have h3 : π (zle (intify x) (intify z))
    { refine zle_trans_lemma (intify x) (intify y) (intify z)
        (intify_in_int x) (intify_in_int y) (intify_in_int z) h1 h2 };
  refine ∧ₑ₁ (zle_intify2 x z) (∧ₑ₁ (zle_intify1 x (intify z)) h3)
end;

opaque symbol zle_zless_trans (i j k : τ ι) :
  π (zle i j) → π (zless j k) → π (zless i k) ≔
begin
  assume i j k hij hjk;
  have h1 : π (zless i j ∨ intify i = intify j)
    { refine ind_eq (eq_sym (zle_def i j)) (λ p, p) hij };
  refine ∨ₑ h1 _ _
  { assume hlt; refine zless_trans i j k hlt hjk }
  { assume heq;
    have h2 : π (zless (intify j) k) { refine ∧ₑ₂ (zless_intify1 j k) hjk };
    have h3 : π (zless (intify i) k)
      { refine ind_eq heq (λ v, zless v k) h2 };
    refine ∧ₑ₁ (zless_intify1 i k) h3 }
end;

opaque symbol zless_zle_trans (i j k : τ ι) :
  π (zless i j) → π (zle j k) → π (zless i k) ≔
begin
  assume i j k hij hjk;
  have h1 : π (zless j k ∨ intify j = intify k)
    { refine ind_eq (eq_sym (zle_def j k)) (λ p, p) hjk };
  refine ∨ₑ h1 _ _
  { assume hlt; refine zless_trans i j k hij hlt }
  { assume heq;
    have h2 : π (zless i (intify j)) { refine ∧ₑ₂ (zless_intify2 i j) hij };
    have h3 : π (zless i (intify k))
      { refine ind_eq (eq_sym heq) (λ v, zless i v) h2 };
    refine ∧ₑ₁ (zless_intify2 i k) h3 }
end;

opaque symbol not_zless_iff_zle (z w : τ ι) : π (¬ zless z w ⇔ zle w z) ≔
begin
  assume z w;
  apply ∧ᵢ
  { assume hn;
    rewrite zle_def;
    refine ∨ₑ (zless_linear z w) _ _
    { assume h; refine ⊥ₑ (hn h) }
    { assume hrest;
      refine ∨ₑ hrest _ _
      { assume heq; refine ∨ᵢ₂ (eq_sym heq) }
      { assume h; refine ∨ᵢ₁ h } } }
  { assume hle hlt;
    have h1 : π (zless w z ∨ intify w = intify z)
      { refine ind_eq (eq_sym (zle_def w z)) (λ p, p) hle };
    refine ∨ₑ h1 _ _
    { assume h2; refine zless_not_sym z w hlt h2 }
    { assume heq; refine zless_imp_intify_neq z w hlt (eq_sym heq) } }
end;

opaque symbol not_zle_iff_zless (z w : τ ι) : π (¬ zle z w ⇔ zless w z) ≔
begin
  assume z w;
  apply ∧ᵢ
  { assume hn;
    refine ∨ₑ (em (zless w z)) _ _
    { assume h; refine h }
    { assume hnn; refine ⊥ₑ (hn (∧ₑ₁ (not_zless_iff_zle w z) hnn)) } }
  { assume hlt hle;
    refine ∧ₑ₂ (not_zless_iff_zle w z) hle hlt }
end;

// ===========================================================================
// More subtraction laws (for zcompare_rls)
// ===========================================================================

opaque symbol zdiff_zdiff_eq (x y z : τ ι) :
  π (zdiff (zdiff x y) z = zdiff x (zadd y z)) ≔
begin
  assume x y z;
  rewrite zdiff_def; rewrite zdiff_def; rewrite zdiff_def;
  rewrite zminus_zadd_distrib;
  refine zadd_assoc x (zminus y) (zminus z)
end;

opaque symbol zdiff_zdiff_eq2 (x y z : τ ι) :
  π (zdiff x (zdiff y z) = zdiff (zadd x z) y) ≔
begin
  assume x y z;
  rewrite zdiff_def; rewrite zdiff_def; rewrite zdiff_def;
  rewrite zminus_zadd_distrib;
  rewrite zminus_zminus_intify;
  rewrite (zadd_intify2 (zminus y) z);
  rewrite (zadd_assoc x z (zminus y));
  rewrite (zadd_commute (zminus y) z);
  reflexivity
end;

opaque symbol zdiff_zless_iff (x y z : τ ι) :
  π (zless (zdiff x y) z ⇔ zless x (zadd z y)) ≔
begin
  assume x y z;
  rewrite zless_def; rewrite zless_def;
  rewrite (zdiff_zdiff_eq x y z);
  rewrite (zadd_commute y z);
  refine iff_refl _
end;

opaque symbol zless_zdiff_iff (x y z : τ ι) :
  π (zless x (zdiff z y) ⇔ zless (zadd x y) z) ≔
begin
  assume x y z;
  rewrite zless_def; rewrite zless_def;
  rewrite (zdiff_zdiff_eq2 x z y);
  refine iff_refl _
end;

opaque symbol zdiff_eq_iff (x y z : τ ι) :
  π (x ∈ int) → π (z ∈ int) → π (zdiff x y = z ⇔ x = zadd z y) ≔
begin
  assume x y z hx hz;
  apply ∧ᵢ
  { assume h;
    rewrite left h;
    rewrite zdiff_def;
    rewrite (zadd_assoc x (zminus y) y);
    rewrite (zadd_zminus_inverse2 y);
    rewrite zadd_int0_right_intify;
    refine eq_sym (intify_ident x hx) }
  { assume h;
    rewrite zdiff_def;
    rewrite h;
    rewrite (zadd_assoc z y (zminus y));
    rewrite (zadd_zminus_inverse y);
    rewrite zadd_int0_right_intify;
    refine intify_ident z hz }
end;

opaque symbol eq_zdiff_iff (x y z : τ ι) :
  π (x ∈ int) → π (z ∈ int) → π (x = zdiff z y ⇔ zadd x y = z) ≔
begin
  assume x y z hx hz;
  apply ∧ᵢ
  { assume h;
    rewrite h;
    rewrite zdiff_def;
    rewrite (zadd_assoc z (zminus y) y);
    rewrite (zadd_zminus_inverse2 y);
    rewrite zadd_int0_right_intify;
    refine intify_ident z hz }
  { assume h;
    rewrite left h;
    rewrite zdiff_def;
    rewrite (zadd_assoc x y (zminus y));
    rewrite (zadd_zminus_inverse y);
    rewrite zadd_int0_right_intify;
    refine eq_sym (intify_ident x hx) }
end;

opaque symbol zdiff_zle_iff_lemma (x y z : τ ι) :
  π (x ∈ int) → π (z ∈ int) → π (zle (zdiff x y) z ⇔ zle x (zadd z y)) ≔
begin
  assume x y z hx hz;
  rewrite zle_def; rewrite zle_def;
  rewrite (intify_ident (zdiff x y) (zdiff_type x y));
  rewrite (intify_ident z hz);
  rewrite (intify_ident x hx);
  rewrite (intify_ident (zadd z y) (zadd_type z y));
  apply ∧ᵢ
  { assume h;
    refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₁ (zdiff_zless_iff x y z) h1) }
    { assume h2; refine ∨ᵢ₂ (∧ₑ₁ (zdiff_eq_iff x y z hx hz) h2) } }
  { assume h;
    refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₂ (zdiff_zless_iff x y z) h1) }
    { assume h2; refine ∨ᵢ₂ (∧ₑ₂ (zdiff_eq_iff x y z hx hz) h2) } }
end;

opaque symbol zdiff_zle_iff (x y z : τ ι) :
  π (zle (zdiff x y) z ⇔ zle x (zadd z y)) ≔
begin
  assume x y z;
  have hlem : π (zle (zdiff (intify x) y) (intify z) ⇔
                 zle (intify x) (zadd (intify z) y))
    { refine zdiff_zle_iff_lemma (intify x) y (intify z)
        (intify_in_int x) (intify_in_int z) };
  apply ∧ᵢ
  { assume h;
    have h1 : π (zle (zdiff x y) (intify z))
      { refine ∧ₑ₂ (zle_intify2 (zdiff x y) z) h };
    have h2 : π (zle (zdiff (intify x) y) (intify z))
      { refine ind_eq (zdiff_intify1 x y) (λ v, zle v (intify z)) h1 };
    have h3 : π (zle (intify x) (zadd (intify z) y)) { refine ∧ₑ₁ hlem h2 };
    have h4 : π (zle x (zadd (intify z) y))
      { refine ∧ₑ₁ (zle_intify1 x (zadd (intify z) y)) h3 };
    refine ind_eq (eq_sym (zadd_intify1 z y)) (λ v, zle x v) h4 }
  { assume h;
    have h1 : π (zle x (zadd (intify z) y))
      { refine ind_eq (zadd_intify1 z y) (λ v, zle x v) h };
    have h2 : π (zle (intify x) (zadd (intify z) y))
      { refine ∧ₑ₂ (zle_intify1 x (zadd (intify z) y)) h1 };
    have h3 : π (zle (zdiff (intify x) y) (intify z)) { refine ∧ₑ₂ hlem h2 };
    have h4 : π (zle (zdiff x y) (intify z))
      { refine ind_eq (eq_sym (zdiff_intify1 x y)) (λ v, zle v (intify z)) h3 };
    refine ∧ₑ₁ (zle_intify2 (zdiff x y) z) h4 }
end;

opaque symbol zle_zdiff_iff_lemma (x y z : τ ι) :
  π (x ∈ int) → π (z ∈ int) → π (zle x (zdiff z y) ⇔ zle (zadd x y) z) ≔
begin
  assume x y z hx hz;
  rewrite zle_def; rewrite zle_def;
  rewrite (intify_ident x hx);
  rewrite (intify_ident (zdiff z y) (zdiff_type z y));
  rewrite (intify_ident (zadd x y) (zadd_type x y));
  rewrite (intify_ident z hz);
  apply ∧ᵢ
  { assume h;
    refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₁ (zless_zdiff_iff x y z) h1) }
    { assume h2; refine ∨ᵢ₂ (∧ₑ₁ (eq_zdiff_iff x y z hx hz) h2) } }
  { assume h;
    refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₂ (zless_zdiff_iff x y z) h1) }
    { assume h2; refine ∨ᵢ₂ (∧ₑ₂ (eq_zdiff_iff x y z hx hz) h2) } }
end;

opaque symbol zle_zdiff_iff (x y z : τ ι) :
  π (zle x (zdiff z y) ⇔ zle (zadd x y) z) ≔
begin
  assume x y z;
  have hlem : π (zle (intify x) (zdiff (intify z) y) ⇔
                 zle (zadd (intify x) y) (intify z))
    { refine zle_zdiff_iff_lemma (intify x) y (intify z)
        (intify_in_int x) (intify_in_int z) };
  apply ∧ᵢ
  { assume h;
    have h1 : π (zle (intify x) (zdiff z y))
      { refine ∧ₑ₂ (zle_intify1 x (zdiff z y)) h };
    have h2 : π (zle (intify x) (zdiff (intify z) y))
      { refine ind_eq (zdiff_intify1 z y) (λ v, zle (intify x) v) h1 };
    have h3 : π (zle (zadd (intify x) y) (intify z)) { refine ∧ₑ₁ hlem h2 };
    have h4 : π (zle (zadd (intify x) y) z)
      { refine ∧ₑ₁ (zle_intify2 (zadd (intify x) y) z) h3 };
    refine ind_eq (eq_sym (zadd_intify1 x y)) (λ v, zle v z) h4 }
  { assume h;
    have h1 : π (zle (zadd (intify x) y) z)
      { refine ind_eq (zadd_intify1 x y) (λ v, zle v z) h };
    have h2 : π (zle (zadd (intify x) y) (intify z))
      { refine ∧ₑ₂ (zle_intify2 (zadd (intify x) y) z) h1 };
    have h3 : π (zle (intify x) (zdiff (intify z) y)) { refine ∧ₑ₂ hlem h2 };
    have h4 : π (zle (intify x) (zdiff z y))
      { refine ind_eq (eq_sym (zdiff_intify1 z y)) (λ v, zle (intify x) v) h3 };
    refine ∧ₑ₁ (zle_intify1 x (zdiff z y)) h4 }
end;

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
begin
  assume w w' z hw hw';
  apply ∧ᵢ
  { assume h;
    have hc1 : π (zadd (zminus z) (zadd z w') = w')
      { rewrite left (zadd_assoc (zminus z) z w');
        rewrite (zadd_zminus_inverse2 z);
        rewrite zadd_int0_intify;
        refine intify_ident w' hw' };
    have hc2 : π (zadd (zminus z) (zadd z w) = w)
      { rewrite left (zadd_assoc (zminus z) z w);
        rewrite (zadd_zminus_inverse2 z);
        rewrite zadd_int0_intify;
        refine intify_ident w hw };
    refine eq_trans (eq_sym hc1)
      (eq_trans (feq (λ v, zadd (zminus z) v) h) hc2) }
  { assume h; rewrite h; reflexivity }
end;

opaque symbol zadd_left_cancel_intify (w w' z : τ ι) :
  π (zadd z w' = zadd z w ⇔ intify w' = intify w) ≔
begin
  assume w w' z;
  rewrite left (zadd_intify2 z w');
  rewrite left (zadd_intify2 z w);
  refine zadd_left_cancel (intify w) (intify w') z
    (intify_in_int w) (intify_in_int w')
end;

opaque symbol zadd_right_cancel (w w' z : τ ι) :
  π (w ∈ int) → π (w' ∈ int) → π (zadd w' z = zadd w z ⇔ w' = w) ≔
begin
  assume w w' z hw hw';
  rewrite (zadd_commute w' z); rewrite (zadd_commute w z);
  refine zadd_left_cancel w w' z hw hw'
end;

opaque symbol zadd_right_cancel_intify (w w' z : τ ι) :
  π (zadd w' z = zadd w z ⇔ intify w' = intify w) ≔
begin
  assume w w' z;
  rewrite (zadd_commute w' z); rewrite (zadd_commute w z);
  refine zadd_left_cancel_intify w w' z
end;

opaque symbol zadd_right_cancel_zless (w w' z : τ ι) :
  π (zless (zadd w' z) (zadd w z) ⇔ zless w' w) ≔
begin
  assume w w' z;
  have hE : π (zdiff (zadd w' z) (zadd w z) = zdiff w' w)
    { rewrite zdiff_def; rewrite zdiff_def;
      rewrite zminus_zadd_distrib;
      rewrite (zadd_assoc w' z (zadd (zminus w) (zminus z)));
      rewrite (zadd_left_commute z (zminus w) (zminus z));
      rewrite (zadd_zminus_inverse z);
      rewrite zadd_int0_right_intify;
      rewrite (intify_ident (zminus w) (zminus_type w));
      reflexivity };
  rewrite zless_def; rewrite zless_def;
  rewrite hE;
  refine iff_refl _
end;

opaque symbol zadd_left_cancel_zless (w w' z : τ ι) :
  π (zless (zadd z w') (zadd z w) ⇔ zless w' w) ≔
begin
  assume w w' z;
  rewrite (zadd_commute z w'); rewrite (zadd_commute z w);
  refine zadd_right_cancel_zless w w' z
end;

opaque symbol zadd_right_cancel_zle (w w' z : τ ι) :
  π (zle (zadd w' z) (zadd w z) ⇔ zle w' w) ≔
begin
  assume w w' z;
  rewrite zle_def; rewrite zle_def;
  rewrite (intify_ident (zadd w' z) (zadd_type w' z));
  rewrite (intify_ident (zadd w z) (zadd_type w z));
  apply ∧ᵢ
  { assume h;
    refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₁ (zadd_right_cancel_zless w w' z) h1) }
    { assume h2; refine ∨ᵢ₂ (∧ₑ₁ (zadd_right_cancel_intify w w' z) h2) } }
  { assume h;
    refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₂ (zadd_right_cancel_zless w w' z) h1) }
    { assume h2; refine ∨ᵢ₂ (∧ₑ₂ (zadd_right_cancel_intify w w' z) h2) } }
end;

opaque symbol zadd_left_cancel_zle (w w' z : τ ι) :
  π (zle (zadd z w') (zadd z w) ⇔ zle w' w) ≔
begin
  assume w w' z;
  rewrite (zadd_commute z w'); rewrite (zadd_commute z w);
  refine zadd_right_cancel_zle w w' z
end;

// zadd_zless_mono1 = zadd_right_cancel_zless [THEN iffD2] : v $< w ⟹ v$+z $< w$+z
opaque symbol zadd_zless_mono1 (v w z : τ ι) :
  π (zless v w) → π (zless (zadd v z) (zadd w z)) ≔
begin
  assume v w z h;
  refine ∧ₑ₂ (zadd_right_cancel_zless w v z) h
end;

// zadd_zless_mono2 = zadd_left_cancel_zless [THEN iffD2] : v $< w ⟹ z$+v $< z$+w
opaque symbol zadd_zless_mono2 (v w z : τ ι) :
  π (zless v w) → π (zless (zadd z v) (zadd z w)) ≔
begin
  assume v w z h;
  refine ∧ₑ₂ (zadd_left_cancel_zless w v z) h
end;

// zadd_zle_mono1 = zadd_right_cancel_zle [THEN iffD2] : v $≤ w ⟹ v$+z $≤ w$+z
opaque symbol zadd_zle_mono1 (v w z : τ ι) :
  π (zle v w) → π (zle (zadd v z) (zadd w z)) ≔
begin
  assume v w z h;
  refine ∧ₑ₂ (zadd_right_cancel_zle w v z) h
end;

// zadd_zle_mono2 = zadd_left_cancel_zle [THEN iffD2] : v $≤ w ⟹ z$+v $≤ z$+w
opaque symbol zadd_zle_mono2 (v w z : τ ι) :
  π (zle v w) → π (zle (zadd z v) (zadd z w)) ≔
begin
  assume v w z h;
  refine ∧ₑ₂ (zadd_left_cancel_zle w v z) h
end;

opaque symbol zadd_zle_mono (w w' z z' : τ ι) :
  π (zle w' w) → π (zle z' z) → π (zle (zadd w' z') (zadd w z)) ≔
begin
  assume w w' z z' h1 h2;
  refine zle_trans (zadd w' z') (zadd w z') (zadd w z)
    (zadd_zle_mono1 w' w z' h1) (zadd_zle_mono2 z' z w h2)
end;

opaque symbol zadd_zless_mono (w w' z z' : τ ι) :
  π (zless w' w) → π (zle z' z) → π (zless (zadd w' z') (zadd w z)) ≔
begin
  assume w w' z z' h1 h2;
  refine zless_zle_trans (zadd w' z') (zadd w z') (zadd w z)
    (zadd_zless_mono1 w' w z' h1) (zadd_zle_mono2 z' z w h2)
end;

// ===========================================================================
// Comparison laws
// ===========================================================================

opaque symbol zminus_zless_zminus (x y : τ ι) :
  π (zless (zminus x) (zminus y) ⇔ zless y x) ≔
begin
  assume x y;
  rewrite zless_def; rewrite zless_def;
  rewrite zdiff_def; rewrite zdiff_def;
  rewrite zminus_zminus_intify;
  rewrite (zadd_intify2 (zminus x) y);
  rewrite (zadd_commute (zminus x) y);
  refine iff_refl _
end;

opaque symbol zminus_zle_zminus (x y : τ ι) :
  π (zle (zminus x) (zminus y) ⇔ zle y x) ≔
begin
  assume x y;
  rewrite zle_def; rewrite zle_def;
  rewrite (intify_ident (zminus x) (zminus_type x));
  rewrite (intify_ident (zminus y) (zminus_type y));
  apply ∧ᵢ
  { assume h;
    refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₁ (zminus_zless_zminus x y) h1) }
    { assume h2; refine ∨ᵢ₂ (eq_sym (zminus_inject_intify x y h2)) } }
  { assume h;
    refine ∨ₑ h _ _
    { assume h1; refine ∨ᵢ₁ (∧ₑ₂ (zminus_zless_zminus x y) h1) }
    { assume h2;
      refine ∨ᵢ₂ _;
      rewrite left (zminus_intify x);
      rewrite left (zminus_intify y);
      rewrite left h2;
      reflexivity } }
end;

// More inequality lemmas

opaque symbol equation_zminus (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (x = zminus y ⇔ y = zminus x) ≔
begin
  assume x y hx hy;
  apply ∧ᵢ
  { assume h;
    refine eq_sym _;
    rewrite h;
    rewrite zminus_zminus_intify;
    refine intify_ident y hy }
  { assume h;
    refine eq_sym _;
    rewrite h;
    rewrite zminus_zminus_intify;
    refine intify_ident x hx }
end;

opaque symbol zminus_equation (x y : τ ι) :
  π (x ∈ int) → π (y ∈ int) → π (zminus x = y ⇔ zminus y = x) ≔
begin
  assume x y hx hy;
  apply ∧ᵢ
  { assume h;
    rewrite left h;
    rewrite zminus_zminus_intify;
    refine intify_ident x hx }
  { assume h;
    rewrite left h;
    rewrite zminus_zminus_intify;
    refine intify_ident y hy }
end;

opaque symbol equation_zminus_intify (x y : τ ι) :
  π (intify x = zminus y ⇔ intify y = zminus x) ≔
begin
  assume x y;
  rewrite left (zminus_intify y);
  rewrite left (zminus_intify x);
  refine equation_zminus (intify x) (intify y)
    (intify_in_int x) (intify_in_int y)
end;

opaque symbol zminus_equation_intify (x y : τ ι) :
  π (zminus x = intify y ⇔ zminus y = intify x) ≔
begin
  assume x y;
  rewrite left (zminus_intify x);
  rewrite left (zminus_intify y);
  refine zminus_equation (intify x) (intify y)
    (intify_in_int x) (intify_in_int y)
end;

// The next several equations are permutative: watch out!

opaque symbol zless_zminus (x y : τ ι) :
  π (zless x (zminus y) ⇔ zless y (zminus x)) ≔
begin
  assume x y;
  rewrite zless_def; rewrite zless_def;
  rewrite zdiff_def; rewrite zdiff_def;
  rewrite zminus_zminus_intify; rewrite zminus_zminus_intify;
  rewrite (zadd_intify2 x y);
  rewrite (zadd_intify2 y x);
  rewrite (zadd_commute y x);
  refine iff_refl _
end;

opaque symbol zminus_zless (x y : τ ι) :
  π (zless (zminus x) y ⇔ zless (zminus y) x) ≔
begin
  assume x y;
  rewrite zless_def; rewrite zless_def;
  rewrite zdiff_def; rewrite zdiff_def;
  rewrite (zadd_commute (zminus x) (zminus y));
  refine iff_refl _
end;

opaque symbol zle_zminus (x y : τ ι) :
  π (zle x (zminus y) ⇔ zle y (zminus x)) ≔
begin
  assume x y;
  apply ∧ᵢ
  { assume h;
    refine ∧ₑ₁ (not_zless_iff_zle (zminus x) y) _;
    assume hlt;
    have hlt2 : π (zless (zminus y) x) { refine ∧ₑ₁ (zminus_zless x y) hlt };
    refine ∧ₑ₂ (not_zless_iff_zle (zminus y) x) h hlt2 }
  { assume h;
    refine ∧ₑ₁ (not_zless_iff_zle (zminus y) x) _;
    assume hlt;
    have hlt2 : π (zless (zminus x) y) { refine ∧ₑ₂ (zminus_zless x y) hlt };
    refine ∧ₑ₂ (not_zless_iff_zle (zminus x) y) h hlt2 }
end;

opaque symbol zminus_zle (x y : τ ι) :
  π (zle (zminus x) y ⇔ zle (zminus y) x) ≔
begin
  assume x y;
  apply ∧ᵢ
  { assume h;
    refine ∧ₑ₁ (not_zless_iff_zle x (zminus y)) _;
    assume hlt;
    have hlt2 : π (zless y (zminus x)) { refine ∧ₑ₁ (zless_zminus x y) hlt };
    refine ∧ₑ₂ (not_zless_iff_zle y (zminus x)) h hlt2 }
  { assume h;
    refine ∧ₑ₁ (not_zless_iff_zle y (zminus x)) _;
    assume hlt;
    have hlt2 : π (zless x (zminus y)) { refine ∧ₑ₂ (zless_zminus x y) hlt };
    refine ∧ₑ₂ (not_zless_iff_zle x (zminus y)) h hlt2 }
end;
