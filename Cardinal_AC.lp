// ZF.Cardinal_AC — Cardinal Arithmetic Using AC
// Faithful SKELETON port of isabelle-src/Cardinal_AC.thy.
// Every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/Cardinal_AC.thy — "these results help justify
// infinite-branching datatypes".)
//
// Several lemmas here (cardinal_UN_le, cardinal_UN_lt_csucc,
// cardinal_UN_Ord_lt_csucc, inj_UN_subset, le_UN_Ord_lt_csucc) are stated in
// Isabelle with SCHEMATIC FUNCTION VARIABLES (`X`, `j`, `C` : i⇒i, e.g.
// "⋀i. i∈K ⟹ |X(i)| ≤ K"); these become Π-bound `τ ι → τ ι` parameters here,
// exactly as CardinalArith.lp's own function-valued lemmas already do.
// Isar `assumes ... shows ...` blocks are flattened to ordinary curried
// hypotheses in declaration order, per CLAUDE.md's standard treatment.

require open ZF.CardinalArith ZF.Zorn ZF.AC;

// ===========================================================================
// Strengthened Forms of Existing Theorems on Cardinals
// ===========================================================================

opaque symbol cardinal_eqpoll (A : τ ι) : π (eqpoll (cardinal A) A) ≔
begin
  assume A;
  refine ∃ₑ (AC_well_ord A) _;
  assume r hr;
  refine well_ord_cardinal_eqpoll A r hr
end;

// The theorem ||A|| = |A|
opaque symbol cardinal_idem (A : τ ι) : π (cardinal (cardinal A) = cardinal A) ≔
begin
  assume A;
  refine cardinal_cong (cardinal A) A (cardinal_eqpoll A)
end;

opaque symbol cardinal_eqE (X Y : τ ι) :
  π (cardinal X = cardinal Y) → π (eqpoll X Y) ≔
begin
  assume X Y heq;
  refine ∃ₑ (AC_well_ord X) _;
  assume r hr;
  refine ∃ₑ (AC_well_ord Y) _;
  assume s hs;
  refine well_ord_cardinal_eqE X r Y s hr hs heq
end;

opaque symbol cardinal_eqpoll_iff (X Y : τ ι) :
  π (cardinal X = cardinal Y ⇔ eqpoll X Y) ≔
begin
  assume X Y;
  apply ∧ᵢ
  { assume h; refine cardinal_eqE X Y h }
  { assume h; refine cardinal_cong X Y h }
end;

opaque symbol cardinal_disjoint_Un (A B C D : τ ι) :
  π (cardinal A = cardinal B) → π (cardinal C = cardinal D) →
  π (Int A C = empty) → π (Int B D = empty) →
  π (cardinal (Un A C) = cardinal (Un B D)) ≔
begin
  assume A B C D hAB hCD hAC hBD;
  refine cardinal_cong (Un A C) (Un B D) _;
  refine eqpoll_disjoint_Un A B C D (cardinal_eqE A B hAB) (cardinal_eqE C D hCD) hAC hBD
end;

opaque symbol lepoll_imp_cardinal_le (A B : τ ι) :
  π (lepoll A B) → π (le (cardinal A) (cardinal B)) ≔
begin
  assume A B h;
  refine ∃ₑ (AC_well_ord B) _;
  assume r hr;
  refine well_ord_lepoll_imp_cardinal_le B r A hr h
end;

opaque symbol cadd_assoc (i j k : τ ι) :
  π (cadd (cadd i j) k = cadd i (cadd j k)) ≔
begin
  assume i j k;
  refine ∃ₑ (AC_well_ord i) _;
  assume ri hri;
  refine ∃ₑ (AC_well_ord j) _;
  assume rj hrj;
  refine ∃ₑ (AC_well_ord k) _;
  assume rk hrk;
  refine well_ord_cadd_assoc i ri j rj k rk hri hrj hrk
end;

opaque symbol cmult_assoc (i j k : τ ι) :
  π (cmult (cmult i j) k = cmult i (cmult j k)) ≔
begin
  assume i j k;
  refine ∃ₑ (AC_well_ord i) _;
  assume ri hri;
  refine ∃ₑ (AC_well_ord j) _;
  assume rj hrj;
  refine ∃ₑ (AC_well_ord k) _;
  assume rk hrk;
  refine well_ord_cmult_assoc i ri j rj k rk hri hrj hrk
end;

opaque symbol cadd_cmult_distrib (i j k : τ ι) :
  π (cmult (cadd i j) k = cadd (cmult i k) (cmult j k)) ≔
begin
  assume i j k;
  refine ∃ₑ (AC_well_ord i) _;
  assume ri hri;
  refine ∃ₑ (AC_well_ord j) _;
  assume rj hrj;
  refine ∃ₑ (AC_well_ord k) _;
  assume rk hrk;
  refine well_ord_cadd_cmult_distrib i ri j rj k rk hri hrj hrk
end;

opaque symbol InfCard_square_eq (A : τ ι) :
  π (InfCard (cardinal A)) → π (eqpoll (Sigma A (λ _, A)) A) ≔
begin
  assume A hInf;
  refine ∃ₑ (AC_well_ord A) _;
  assume r hr;
  refine well_ord_InfCard_square_eq A r hr hInf
end;

// ===========================================================================
// The relationship between cardinality and le-pollence
// ===========================================================================

opaque symbol Card_le_imp_lepoll (A B : τ ι) :
  π (le (cardinal A) (cardinal B)) → π (lepoll A B) ≔
begin
  assume A B h;
  // A ≈ |A| ≼ |B| ≈ B
  refine eq_lepoll_trans A (cardinal A) B (eqpoll_sym (cardinal A) A (cardinal_eqpoll A)) _;
  refine lepoll_eq_trans (cardinal A) (cardinal B) B (le_imp_lepoll (cardinal A) (cardinal B) h) (cardinal_eqpoll B)
end;

opaque symbol le_Card_iff (K A : τ ι) :
  π (Card K) → π (le (cardinal A) K ⇔ lepoll A K) ≔
begin
  assume K A hK;
  have hKeq : π (cardinal K = K) { refine Card_cardinal_eq K hK };
  apply ∧ᵢ
  { assume h;
    have h2 : π (le (cardinal A) (cardinal K)) { rewrite hKeq; refine h };
    refine Card_le_imp_lepoll A K h2 }
  { assume h;
    have h2 : π (le (cardinal A) (cardinal K)) { refine lepoll_imp_cardinal_le A K h };
    refine ind_eq (eq_sym hKeq) (λ w, le (cardinal A) w) h2 }
end;

opaque symbol cardinal_0_iff_0 (A : τ ι) : π (cardinal A = empty ⇔ A = empty) ≔
begin
  assume A;
  apply ∧ᵢ
  { assume h;
    have he : π (eqpoll empty A)
      { refine ind_eq (eq_sym h) (λ w, eqpoll w A) (cardinal_eqpoll A) };
    refine ∧ₑ₁ (eqpoll_0_iff A) (eqpoll_sym empty A he) }
  { assume h; rewrite h; refine cardinal_0 }
end;

opaque symbol cardinal_lt_iff_lesspoll (i A : τ ι) :
  π (Ord i) → π (lt i (cardinal A) ⇔ lesspoll i A) ≔
begin
  assume i A hOi;
  apply ∧ᵢ
  { assume h;
    have h1 : π (lesspoll i (cardinal A))
      { refine lt_Card_imp_lesspoll (cardinal A) i (Card_cardinal A) h };
    refine lesspoll_eq_trans i (cardinal A) A h1 (cardinal_eqpoll A) }
  { assume h;
    have h1 : π (lesspoll i (cardinal A))
      { refine lesspoll_eq_trans i A (cardinal A) h (eqpoll_sym (cardinal A) A (cardinal_eqpoll A)) };
    have h2 : π (lt (cardinal i) (cardinal A))
      { refine lesspoll_cardinal_lt i (cardinal A) h1 (Ord_cardinal A) };
    refine Card_lt_imp_lt i (cardinal A) h2 hOi (Card_cardinal A) }
end;

opaque symbol cardinal_le_imp_lepoll (i A : τ ι) :
  π (le i (cardinal A)) → π (lesspoll i A ∨ eqpoll i A) ≔
begin
  assume i A hle;
  // Ord i from le (le i j is lt i (succ j))
  have hOi : π (Ord i) { refine lt_Ord i (succ (cardinal A)) hle };
  have hle2 : π (le (cardinal i) (cardinal A))
    { refine le_trans (cardinal i) i (cardinal A) (Ord_cardinal_le i hOi) hle };
  refine ∧ₑ₁ (lepoll_iff_leqpoll i A) (Card_le_imp_lepoll i A hle2)
end;

// ===========================================================================
// Other Applications of AC
// ===========================================================================

opaque symbol surj_implies_inj (f X Y : τ ι) :
  π (f ∈ surj X Y) → π (`∃ (g : τ ι), g ∈ inj Y X) ≔
begin
  assume f X Y hf;
  have hfun : π (f ∈ Pi X (λ _, Y)) { refine surj_is_fun f X Y hf };
  // each fibre f-``{y} is nonempty
  have hne : Π (y : τ ι), π (y ∈ Y) → π (`∃ (x : τ ι), x ∈ vimage_singleton f y)
    { assume y hy;
      refine ∃ₑ (surj_memD f X Y hf y hy) _;
      assume x hx;
      have hpair : π (Pair x (fapply f x) ∈ f)
        { refine Pi_apply_Pair f x X (λ _, Y) hfun (∧ₑ₁ hx) };
      have hpair2 : π (Pair x y ∈ f)
        { refine ind_eq (eq_sym (∧ₑ₂ hx)) (λ w, Pair x w ∈ f) hpair };
      refine ∃ᵢ x (vimage_singletonI x y f hpair2) };
  // choice function z ∈ Pi(Y, λy. f-``{y})
  refine ∃ₑ (AC_Pi Y (λ y, vimage_singleton f y) hne) _;
  assume z hz;
  have hzX : π (z ∈ Pi Y (λ _, X))
    { refine Pi_type z Y (λ y, vimage_singleton f y) (λ _, X) hz _;
      assume y hy x hx;
      refine domain_type x y f X (λ _, Y) (vimage_singletonD x y f hx) hfun };
  have hleft : π (Ball Y (λ y, fapply f (fapply z y) = y))
    { assume y hy;
      have hzy : π (fapply z y ∈ vimage_singleton f y)
        { refine fapply_type z y Y (λ y, vimage_singleton f y) hz hy };
      refine apply_equality (fapply z y) y f X (λ _, Y)
        (vimage_singletonD (fapply z y) y f hzy) hfun };
  refine ∃ᵢ z (f_imp_injective z Y X (λ w, fapply f w) hzX hleft)
end;

// Kunen's Lemma 10.20
opaque symbol surj_implies_cardinal_le (f X Y : τ ι) :
  π (f ∈ surj X Y) → π (le (cardinal Y) (cardinal X)) ≔
begin
  assume f X Y hf;
  refine ∃ₑ (surj_implies_inj f X Y hf) _;
  assume g hg;
  refine lepoll_imp_cardinal_le Y X _;
  rewrite lepoll_def;
  refine ∃ᵢ g hg
end;

// Kunen's Lemma 10.21
opaque symbol cardinal_UN_le (K : τ ι) (X : τ ι → τ ι) :
  π (InfCard K) → (Π (i : τ ι), π (i ∈ K) → π (le (cardinal (X i)) K)) →
  π (le (cardinal (Union (RepFun K X))) K) ≔
begin
  assume K X hInf hle;
  have hCK : π (Card K) { refine InfCard_is_Card K hInf };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  // each X(i) ≲ K, i.e. the inj-spaces inj(X(i),K) are nonempty
  have hinjex : Π (i : τ ι), π (i ∈ K) → π (`∃ (g : τ ι), g ∈ inj (X i) K)
    { assume i hi;
      have hlep : π (lepoll (X i) K)
        { refine ∧ₑ₁ (le_Card_iff K (X i) hCK) (hle i hi) };
      refine ind_eq (eq_sym (lepoll_def (X i) K)) (λ p, p) hlep };
  // choose f ∈ (∏i∈K. inj(X(i),K)) by AC
  refine ∃ₑ (AC_Pi K (λ i, inj (X i) K) hinjex) _;
  assume f hf;
  // for z in the union, (μ i. z ∈ X(i)) ∈ K and z ∈ X(μ i. z ∈ X(i))
  have hmem : Π (z : τ ι), π (z ∈ Union (RepFun K X)) →
      π (Least (λ i, z ∈ X i) ∈ K ∧ z ∈ X (Least (λ i, z ∈ X i)))
    { assume z hz;
      refine ∃ₑ (UnionE z (RepFun K X) hz) _;
      assume B hB;
      refine ∃ₑ (∧ₑ₁ (RepFun_iff B K X) (∧ₑ₁ hB)) _;
      assume i hi;
      have hiK : π (i ∈ K) { refine ∧ₑ₁ hi };
      have hzXi : π (z ∈ X i)
        { refine ind_eq (eq_sym (∧ₑ₂ hi)) (λ w, z ∈ w) (∧ₑ₂ hB) };
      have hOi : π (Ord i) { refine Ord_in_Ord K i hOK hiK };
      have hLlt : π (lt (Least (λ j, z ∈ X j)) K)
        { refine lt_trans1 (Least (λ j, z ∈ X j)) i K
            (Least_le (λ j, z ∈ X j) i hzXi hOi) (ltI i K hiK hOK) };
      refine ∧ᵢ (ltD (Least (λ j, z ∈ X j)) K hLlt)
                (LeastI (λ j, z ∈ X j) i hzXi hOi) };
  // (⋃i∈K. X(i)) ≲ K × K via z ↦ ⟨μ i. z∈X(i), f`(μ i. z∈X(i))`z⟩
  have hlepSq : π (lepoll (Union (RepFun K X)) (Sigma K (λ _, K)))
    { rewrite lepoll_def;
      refine ∃ᵢ (Lambda (Union (RepFun K X))
        (λ z, Pair (Least (λ i, z ∈ X i)) (fapply (fapply f (Least (λ i, z ∈ X i))) z))) _;
      refine lam_injective (Union (RepFun K X)) (Sigma K (λ _, K))
        (λ z, Pair (Least (λ i, z ∈ X i)) (fapply (fapply f (Least (λ i, z ∈ X i))) z))
        (λ p, fapply (converse (fapply f (fst p))) (snd p)) _ _
      { assume z hz;
        have hm : π (Least (λ i, z ∈ X i) ∈ K ∧ z ∈ X (Least (λ i, z ∈ X i)))
          { refine hmem z hz };
        have hfL : π (fapply f (Least (λ i, z ∈ X i)) ∈ inj (X (Least (λ i, z ∈ X i))) K)
          { refine fapply_type f (Least (λ i, z ∈ X i)) K (λ i, inj (X i) K) hf (∧ₑ₁ hm) };
        have hfz : π (fapply (fapply f (Least (λ i, z ∈ X i))) z ∈ K)
          { refine fapply_type (fapply f (Least (λ i, z ∈ X i))) z
              (X (Least (λ i, z ∈ X i))) (λ _, K)
              (inj_is_fun (fapply f (Least (λ i, z ∈ X i))) (X (Least (λ i, z ∈ X i))) K hfL)
              (∧ₑ₂ hm) };
        refine SigmaI (Least (λ i, z ∈ X i)) (fapply (fapply f (Least (λ i, z ∈ X i))) z)
          K (λ _, K) (∧ₑ₁ hm) hfz }
      { assume z hz;
        rewrite fst_conv;
        rewrite snd_conv;
        have hm : π (Least (λ i, z ∈ X i) ∈ K ∧ z ∈ X (Least (λ i, z ∈ X i)))
          { refine hmem z hz };
        have hfL : π (fapply f (Least (λ i, z ∈ X i)) ∈ inj (X (Least (λ i, z ∈ X i))) K)
          { refine fapply_type f (Least (λ i, z ∈ X i)) K (λ i, inj (X i) K) hf (∧ₑ₁ hm) };
        refine left_inverse (fapply f (Least (λ i, z ∈ X i)))
          (X (Least (λ i, z ∈ X i))) K z hfL (∧ₑ₂ hm) } };
  // K × K ≈ K, hence the union ≲ K, hence |union| ≤ K
  have hlepK : π (lepoll (Union (RepFun K X)) K)
    { refine lepoll_eq_trans (Union (RepFun K X)) (Sigma K (λ _, K)) K hlepSq
        (InfCard_square_eqpoll K hInf) };
  refine ∧ₑ₂ (le_Card_iff K (Union (RepFun K X)) hCK) hlepK
end;

// The same again, using csucc
opaque symbol cardinal_UN_lt_csucc (K : τ ι) (X : τ ι → τ ι) :
  π (InfCard K) → (Π (i : τ ι), π (i ∈ K) → π (lt (cardinal (X i)) (csucc K))) →
  π (lt (cardinal (Union (RepFun K X))) (csucc K)) ≔
begin
  assume K X hInf hlt;
  have hCK : π (Card K) { refine InfCard_is_Card K hInf };
  have hle : Π (i : τ ι), π (i ∈ K) → π (le (cardinal (X i)) K)
    { assume i hi;
      refine ∧ₑ₁ (Card_lt_csucc_iff (cardinal (X i)) K (Card_cardinal (X i)) hCK)
        (hlt i hi) };
  refine ∧ₑ₂ (Card_lt_csucc_iff (cardinal (Union (RepFun K X))) K
      (Card_cardinal (Union (RepFun K X))) hCK)
    (cardinal_UN_le K X hInf hle)
end;

// The same again, for a union of ordinals. In use, j(i) is a bit like
// rank(i), the least ordinal j such that i:Vfrom(A,j).
opaque symbol cardinal_UN_Ord_lt_csucc (K : τ ι) (j : τ ι → τ ι) :
  π (InfCard K) → (Π (i : τ ι), π (i ∈ K) → π (lt (j i) (csucc K))) →
  π (lt (Union (RepFun K j)) (csucc K)) ≔
begin
  assume K j hInf hlt;
  have hCK : π (Card K) { refine InfCard_is_Card K hInf };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  // |⋃i∈K. j(i)| < csucc(K), via |j(i)| ≤ j(i) < csucc(K)
  have hlt2 : Π (i : τ ι), π (i ∈ K) → π (lt (cardinal (j i)) (csucc K))
    { assume i hi;
      have hOji : π (Ord (j i)) { refine lt_Ord (j i) (csucc K) (hlt i hi) };
      refine lt_trans1 (cardinal (j i)) (j i) (csucc K)
        (Ord_cardinal_le (j i) hOji) (hlt i hi) };
  // Ord(⋃i∈K. j(i))
  have hOUN : π (Ord (Union (RepFun K j)))
    { refine Ord_Union (RepFun K j) _;
      assume B hB;
      refine ∃ₑ (∧ₑ₁ (RepFun_iff B K j) hB) _;
      assume i hi;
      rewrite (∧ₑ₂ hi);
      refine lt_Ord (j i) (csucc K) (hlt i (∧ₑ₁ hi)) };
  refine Card_lt_imp_lt (Union (RepFun K j)) (csucc K)
    (cardinal_UN_lt_csucc K j hInf hlt2) hOUN (Card_csucc K hOK)
end;

// ===========================================================================
// The Main Result for Infinite-Branching Datatypes
// ===========================================================================

// As above, but the index set need not be a cardinal. Work backwards along
// the injection from W into K, given that W≠0.
opaque symbol inj_UN_subset (f A B a : τ ι) (C : τ ι → τ ι) :
  π (f ∈ inj A B) → π (a ∈ A) →
  π (Union (RepFun A C) ⊆
     Union (RepFun B (λ y, C (If (y ∈ range f) (fapply (converse f) y) a)))) ≔
begin
  assume f A B a C hinj ha z hz;
  refine ∃ₑ (UnionE z (RepFun A C) hz) _;
  assume w hw;
  refine ∃ₑ (∧ₑ₁ (RepFun_iff w A C) (∧ₑ₁ hw)) _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hzCx : π (z ∈ C x)
    { refine ind_eq (eq_sym (∧ₑ₂ hx)) (λ v, z ∈ v) (∧ₑ₂ hw) };
  have hfun : π (f ∈ Pi A (λ _, B)) { refine inj_is_fun f A B hinj };
  have hfxB : π (fapply f x ∈ B) { refine fapply_type f x A (λ _, B) hfun hxA };
  have hrange : π (fapply f x ∈ range f)
    { refine rangeI x (fapply f x) f (Pi_apply_Pair f x A (λ _, B) hfun hxA) };
  refine UnionI z (C (If (fapply f x ∈ range f) (fapply (converse f) (fapply f x)) a))
    (RepFun B (λ y, C (If (y ∈ range f) (fapply (converse f) y) a))) _ _
  { // z ∈ C(if f`x ∈ range f then converse(f)`(f`x) else a) — reduce the if
    rewrite If_P (fapply f x ∈ range f) (fapply (converse f) (fapply f x)) a hrange;
    rewrite left_inverse f A B x hinj hxA;
    refine hzCx }
  { refine RepFunI (fapply f x) B (λ y, C (If (y ∈ range f) (fapply (converse f) y) a)) hfxB }
end;

opaque symbol le_UN_Ord_lt_csucc (K W : τ ι) (j : τ ι → τ ι) :
  π (InfCard K) → π (le (cardinal W) K) →
  (Π (w : τ ι), π (w ∈ W) → π (lt (j w) (csucc K))) →
  π (lt (Union (RepFun W j)) (csucc K)) ≔
begin
  assume K W j hInf hWK hj;
  have hCK : π (Card K) { refine InfCard_is_Card K hInf };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  // OU: Ord(⋃w∈W. j(w))
  have hOU : π (Ord (Union (RepFun W j)))
    { refine Ord_Union (RepFun W j) _;
      assume B hB;
      refine ∃ₑ (∧ₑ₁ (RepFun_iff B W j) hB) _;
      assume w hw;
      rewrite (∧ₑ₂ hw);
      refine lt_Ord (j w) (csucc K) (hj w (∧ₑ₁ hw)) };
  // f ∈ inj(W,K) from |W| ≤ K
  have hexf : π (`∃ (g : τ ι), g ∈ inj W K)
    { refine ind_eq (eq_sym (lepoll_def W K)) (λ p, p)
        (∧ₑ₁ (le_Card_iff K W hCK) hWK) };
  refine ∃ₑ hexf _;
  assume f hf;
  refine ∨ₑ (em (W = empty)) _ _
  { // the easy W = 0 case: the union is 0 and 0 < csucc(K)
    assume hW0;
    rewrite hW0;
    have hU0 : π (Union (RepFun empty j) = empty)
      { refine equals0I (Union (RepFun empty j)) _;
        assume y hy;
        refine ∃ₑ (UnionE y (RepFun empty j) hy) _;
        assume B hB;
        refine ∃ₑ (∧ₑ₁ (RepFun_iff B empty j) (∧ₑ₁ hB)) _;
        assume x hx;
        refine emptyE x (∧ₑ₁ hx) };
    rewrite hU0;
    refine Ord_0_lt_csucc K hOK }
  { // W ≠ 0: pick x ∈ W and work backwards along the injection f
    assume hWne;
    refine not_emptyE W (lt (Union (RepFun W j)) (csucc K)) hWne _;
    assume x hx;
    // (⋃w∈W. j(w)) ⊆ (⋃k∈K. j(if k ∈ range f then converse(f)`k else x))
    have hsub : π (Union (RepFun W j) ⊆
        Union (RepFun K (λ y, j (If (y ∈ range f) (fapply (converse f) y) x))))
      { refine inj_UN_subset f W K x j hf hx };
    // the right-hand union is < csucc(K)
    have hUK : π (lt (Union (RepFun K (λ y, j (If (y ∈ range f) (fapply (converse f) y) x))))
        (csucc K))
      { refine cardinal_UN_Ord_lt_csucc K
          (λ y, j (If (y ∈ range f) (fapply (converse f) y) x)) hInf _;
        assume k hk;
        refine ∨ₑ (em (k ∈ range f)) _ _
        { assume hkr;
          rewrite If_P (k ∈ range f) (fapply (converse f) k) x hkr;
          refine hj (fapply (converse f) k)
            (fapply_type (converse f) k (range f) (λ _, W)
              (inj_converse_fun f W K hf) hkr) }
        { assume hknr;
          rewrite If_not_P (k ∈ range f) (fapply (converse f) k) x hknr;
          refine hj x hx } };
    // conclude by lt_subset_trans: subset gives ≤, then < by transitivity
    have hle2 : π (le (Union (RepFun W j))
        (Union (RepFun K (λ y, j (If (y ∈ range f) (fapply (converse f) y) x)))))
      { refine subset_imp_le
          (Union (RepFun K (λ y, j (If (y ∈ range f) (fapply (converse f) y) x))))
          (Union (RepFun W j)) hsub
          (lt_Ord (Union (RepFun K (λ y, j (If (y ∈ range f) (fapply (converse f) y) x))))
            (csucc K) hUK)
          hOU };
    refine lt_trans1 (Union (RepFun W j))
      (Union (RepFun K (λ y, j (If (y ∈ range f) (fapply (converse f) y) x))))
      (csucc K) hle2 hUK }
end;
