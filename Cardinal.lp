// ZF.Cardinal — Cardinal Numbers Without the Axiom of Choice
// Faithful SKELETON port of isabelle-src/Cardinal.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/Cardinal.thy.)
//
// Isabelle infix/binder notation is rendered with the plain function names:
//   |A|   = cardinal A      A ≈ B = eqpoll A B     A ≼ B = lepoll A B
//   A ≺ B = lesspoll A B    μ i. P i = Least (λ i, P i)
// nat (ω) = omega ;  A*B = Sigma A (λ _, B) ;  A+B = sum A B ;  A-B = Diff A B.

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum ZF.Ordinal ZF.OrdQuant ZF.Nat_ZF ZF.QPair ZF.Epsilon ZF.Inductive ZF.Order ZF.OrderArith ZF.OrderType ZF.Finite;

// ===========================================================================
// Definitions
// ===========================================================================

// Least(P) ≡ THE i. Ord(i) ∧ P(i) ∧ (∀j. j<i ⟶ ¬P(j))     (least ordinal operator, binder μ)
constant symbol Least (P : τ ι → Prop) : τ ι;
constant symbol Least_def (P : τ ι → Prop) :
  π (Least P = The (λ i, Ord i ∧ P i ∧ (`∀ (j : τ ι), lt j i ⇒ ¬ P j)));

// A ≈ B ≡ ∃f. f ∈ bij(A,B)
constant symbol eqpoll (A B : τ ι) : Prop;
constant symbol eqpoll_def (A B : τ ι) :
  π (eqpoll A B = (`∃ (f : τ ι), f ∈ bij A B));

// A ≼ B ≡ ∃f. f ∈ inj(A,B)
constant symbol lepoll (A B : τ ι) : Prop;
constant symbol lepoll_def (A B : τ ι) :
  π (lepoll A B = (`∃ (f : τ ι), f ∈ inj A B));

// A ≺ B ≡ A ≼ B ∧ ¬(A ≈ B)
constant symbol lesspoll (A B : τ ι) : Prop;
constant symbol lesspoll_def (A B : τ ι) :
  π (lesspoll A B = (lepoll A B ∧ ¬ eqpoll A B));

// |A| ≡ (μ i. i ≈ A)
constant symbol cardinal (A : τ ι) : τ ι;
constant symbol cardinal_def (A : τ ι) :
  π (cardinal A = Least (λ i, eqpoll i A));

// Finite(A) ≡ ∃n∈nat. A ≈ n      (defined HERE, not in ZF.Finite)
constant symbol Finite (A : τ ι) : Prop;
constant symbol Finite_def (A : τ ι) :
  π (Finite A = Bex omega (λ n, eqpoll A n));

// Card(i) ≡ (i = |i|)
constant symbol Card (i : τ ι) : Prop;
constant symbol Card_def (i : τ ι) :
  π (Card i = (i = cardinal i));

// ===========================================================================
// The Schroeder-Bernstein Theorem
// ===========================================================================

opaque symbol decomp_bnd_mono (X g Y f : τ ι) :
  π (bnd_mono X (λ W, Diff X (Image g (Diff Y (Image f W))))) ≔
begin
  assume X g Y f;
  refine bnd_monoI X (λ W, Diff X (Image g (Diff Y (Image f W)))) _ _
  { assume z hz; refine DiffD1 z X (Image g (Diff Y (Image f X))) hz }
  { assume W1 W2 hW12 hW2X z hz;
    have hzX : π (z ∈ X) { refine DiffD1 z X (Image g (Diff Y (Image f W1))) hz };
    have hzn : π (z ∉ Image g (Diff Y (Image f W1)))
      { refine DiffD2 z X (Image g (Diff Y (Image f W1))) hz };
    refine DiffI z X (Image g (Diff Y (Image f W2))) hzX _;
    assume hzIm;
    refine hzn (Image_mono g (Diff Y (Image f W2)) (Diff Y (Image f W1))
      (Diff_mono Y (Image f W2) Y (Image f W1) (subset_refl Y)
        (Image_mono f W1 W2 hW12)) z hzIm) }
end;

opaque symbol Banach_last_equation (g Y X f : τ ι) :
  π (g ∈ Pi Y (λ _, X)) →
  π (Image g (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))))
     = Diff X (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))) ≔
begin
  assume g Y X f hg;
  have hbm : π (bnd_mono X (λ W, Diff X (Image g (Diff Y (Image f W)))))
    { refine decomp_bnd_mono X g Y f };
  have hunf : π (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))
      = Diff X (Image g (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))))))
    { refine lfp_unfold X (λ W, Diff X (Image g (Diff Y (Image f W)))) hbm };
  have hSX : π (Image g (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))))) ⊆ X)
    { refine Image_fun_subset g Y X
        (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))))) hg };
  have hdc : π (Diff X (Diff X (Image g (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))))))
      = Image g (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))))))
    { refine double_complement
        (Image g (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))))))
        X X hSX (subset_refl X) };
  have h1 : π (Diff X (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))
      = Image g (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))))))
    { refine eq_trans (feq (Diff X) hunf) hdc };
  refine eq_sym h1
end;

// Helpers for the decomposition witnesses: A and B−A partition B when A ⊆ B.
private opaque symbol Int_Diff_disjoint (A B : τ ι) :
  π (Int A (Diff B A) = empty) ≔
begin
  assume A B;
  refine equals0I (Int A (Diff B A)) _;
  assume z hz;
  refine DiffD2 z B A (IntD2 z A (Diff B A) hz) (IntD1 z A (Diff B A) hz)
end;

private opaque symbol Un_Diff_eq (A B : τ ι) :
  π (A ⊆ B) → π (Un A (Diff B A) = B) ≔
begin
  assume A B hAB;
  refine equality_iffI (Un A (Diff B A)) B _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∨ₑ (UnE z A (Diff B A) hz) _ _
    { assume h; refine hAB z h }
    { assume h; refine DiffD1 z B A h } }
  { assume hzB;
    refine ∨ₑ (em (z ∈ A)) _ _
    { assume h; refine UnI1 z A (Diff B A) h }
    { assume h; refine UnI2 z A (Diff B A) (DiffI z B A hzB h) } }
end;

opaque symbol decomposition (f X Y g : τ ι) :
  π (f ∈ Pi X (λ _, Y)) → π (g ∈ Pi Y (λ _, X)) →
  π (`∃ (XA : τ ι), `∃ (XB : τ ι), `∃ (YA : τ ι), `∃ (YB : τ ι),
       (Int XA XB = empty) ∧ (Un XA XB = X) ∧ (Int YA YB = empty) ∧ (Un YA YB = Y)
       ∧ (Image f XA = YA) ∧ (Image g YB = XB)) ≔
begin
  assume f X Y g hf hg;
  refine ∃ᵢ (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))) _;
  refine ∃ᵢ (Diff X (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))) _;
  refine ∃ᵢ (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))) _;
  refine ∃ᵢ (Diff Y (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))))) _;
  have hWX : π (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))) ⊆ X)
    { refine lfp_subset X (λ W, Diff X (Image g (Diff Y (Image f W)))) };
  have hfWY : π (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))) ⊆ Y)
    { refine Image_fun_subset f X Y
        (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))) hf };
  refine ∧ᵢ (Int_Diff_disjoint (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))) X) _;
  refine ∧ᵢ (Un_Diff_eq (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))) X hWX) _;
  refine ∧ᵢ (Int_Diff_disjoint (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))) Y) _;
  refine ∧ᵢ (Un_Diff_eq (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W)))))) Y hfWY) _;
  refine ∧ᵢ (eq_refl (Image f (lfp X (λ W, Diff X (Image g (Diff Y (Image f W))))))) _;
  refine Banach_last_equation g Y X f hg
end;

opaque symbol schroeder_bernstein (f X Y g : τ ι) :
  π (f ∈ inj X Y) → π (g ∈ inj Y X) → π (`∃ (h : τ ι), h ∈ bij X Y) ≔
begin
  assume f X Y g hf hg;
  refine ∃ₑ (decomposition f X Y g (inj_is_fun f X Y hf) (inj_is_fun g Y X hg)) _;
  assume XA h1;
  refine ∃ₑ h1 _;
  assume XB h2;
  refine ∃ₑ h2 _;
  assume YA h3;
  refine ∃ₑ h3 _;
  assume YB h4;
  have hIntX : π (Int XA XB = empty) { refine ∧ₑ₁ h4 };
  have hUnX : π (Un XA XB = X) { refine ∧ₑ₁ (∧ₑ₂ h4) };
  have hIntY : π (Int YA YB = empty) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ h4)) };
  have hUnY : π (Un YA YB = Y) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h4))) };
  have hImf : π (Image f XA = YA) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h4)))) };
  have hImg : π (Image g YB = XB) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ (∧ₑ₂ h4)))) };
  have hXAX : π (XA ⊆ X)
    { assume z hz; refine ind_eq (eq_sym hUnX) (λ w, z ∈ w) (UnI1 z XA XB hz) };
  have hYBY : π (YB ⊆ Y)
    { assume z hz; refine ind_eq (eq_sym hUnY) (λ w, z ∈ w) (UnI2 z YA YB hz) };
  have hbij1 : π (restrict f XA ∈ bij XA YA)
    { refine ind_eq (eq_sym hImf) (λ w, restrict f XA ∈ bij XA w)
        (restrict_bij f X Y XA hf hXAX) };
  have hbij2 : π (restrict g YB ∈ bij YB XB)
    { refine ind_eq (eq_sym hImg) (λ w, restrict g YB ∈ bij YB w)
        (restrict_bij g Y X YB hg hYBY) };
  have hbij2c : π (converse (restrict g YB) ∈ bij XB YB)
    { refine bij_converse_bij (restrict g YB) YB XB hbij2 };
  have hglue : π (Un (restrict f XA) (converse (restrict g YB)) ∈ bij (Un XA XB) (Un YA YB))
    { refine bij_disjoint_Un (restrict f XA) (converse (restrict g YB))
        XA YA XB YB hbij1 hbij2c hIntX hIntY };
  have hglue2 : π (Un (restrict f XA) (converse (restrict g YB)) ∈ bij X (Un YA YB))
    { refine ind_eq (eq_sym hUnX)
        (λ w, Un (restrict f XA) (converse (restrict g YB)) ∈ bij w (Un YA YB)) hglue };
  refine ∃ᵢ (Un (restrict f XA) (converse (restrict g YB))) _;
  refine ind_eq (eq_sym hUnY)
    (λ w, Un (restrict f XA) (converse (restrict g YB)) ∈ bij X w) hglue2
end;

// ===========================================================================
// Equipollence is an equivalence relation
// ===========================================================================

opaque symbol bij_imp_eqpoll (f A B : τ ι) :
  π (f ∈ bij A B) → π (eqpoll A B) ≔
begin
  assume f A B hf;
  rewrite eqpoll_def;
  refine ∃ᵢ f hf
end;

// eqpoll_refl = id_bij [THEN bij_imp_eqpoll] : A ≈ A
opaque symbol eqpoll_refl (A : τ ι) :
  π (eqpoll A A) ≔
begin
  assume A; refine bij_imp_eqpoll (id_fun A) A A (id_bij A)
end;

opaque symbol eqpoll_sym (X Y : τ ι) :
  π (eqpoll X Y) → π (eqpoll Y X) ≔
begin
  assume X Y h;
  have h' : π (`∃ (f : τ ι), f ∈ bij X Y)
    { refine ind_eq (eq_sym (eqpoll_def X Y)) (λ p, p) h };
  rewrite eqpoll_def;
  refine ∃ₑ h' _; assume f hf;
  refine ∃ᵢ (converse f) (bij_converse_bij f X Y hf)
end;

opaque symbol eqpoll_trans (X Y Z : τ ι) :
  π (eqpoll X Y) → π (eqpoll Y Z) → π (eqpoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  have hXY' : π (`∃ (f : τ ι), f ∈ bij X Y)
    { refine ind_eq (eq_sym (eqpoll_def X Y)) (λ p, p) hXY };
  have hYZ' : π (`∃ (f : τ ι), f ∈ bij Y Z)
    { refine ind_eq (eq_sym (eqpoll_def Y Z)) (λ p, p) hYZ };
  rewrite eqpoll_def;
  refine ∃ₑ hXY' _; assume f hf;
  refine ∃ₑ hYZ' _; assume g hg;
  refine ∃ᵢ (rcomp g f) (comp_bij g f X Y Z hf hg)
end;

// ===========================================================================
// Le-pollence is a partial ordering
// ===========================================================================

opaque symbol subset_imp_lepoll (X Y : τ ι) :
  π (X ⊆ Y) → π (lepoll X Y) ≔
begin
  assume X Y hsub;
  rewrite lepoll_def;
  refine ∃ᵢ (id_fun X) _;
  rewrite id_fun_def;
  refine lam_injective X Y (λ x, x) (λ x, x) _ _
  { assume x hx; refine hsub x hx }
  { assume x hx; refine eq_refl x }
end;

// lepoll_refl = subset_refl [THEN subset_imp_lepoll] : A ≼ A
opaque symbol lepoll_refl (A : τ ι) :
  π (lepoll A A) ≔
begin
  assume A; refine subset_imp_lepoll A A (subset_refl A)
end;

// le_imp_lepoll = le_imp_subset [THEN subset_imp_lepoll] : i ≤ j ⟹ i ≼ j
opaque symbol le_imp_lepoll (i j : τ ι) :
  π (le i j) → π (lepoll i j) ≔
begin
  assume i j hle; refine subset_imp_lepoll i j (le_imp_subset i j hle)
end;

opaque symbol eqpoll_imp_lepoll (X Y : τ ι) :
  π (eqpoll X Y) → π (lepoll X Y) ≔
begin
  assume X Y h;
  have h' : π (`∃ (f : τ ι), f ∈ bij X Y)
    { refine ind_eq (eq_sym (eqpoll_def X Y)) (λ p, p) h };
  rewrite lepoll_def;
  refine ∃ₑ h' _; assume f hf;
  refine ∃ᵢ f (bij_is_inj f X Y hf)
end;

opaque symbol lepoll_trans (X Y Z : τ ι) :
  π (lepoll X Y) → π (lepoll Y Z) → π (lepoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  have hXY' : π (`∃ (f : τ ι), f ∈ inj X Y)
    { refine ind_eq (eq_sym (lepoll_def X Y)) (λ p, p) hXY };
  have hYZ' : π (`∃ (f : τ ι), f ∈ inj Y Z)
    { refine ind_eq (eq_sym (lepoll_def Y Z)) (λ p, p) hYZ };
  rewrite lepoll_def;
  refine ∃ₑ hXY' _; assume f hf;
  refine ∃ₑ hYZ' _; assume g hg;
  refine ∃ᵢ (rcomp g f) (comp_inj g f X Y Z hf hg)
end;

opaque symbol eq_lepoll_trans (X Y Z : τ ι) :
  π (eqpoll X Y) → π (lepoll Y Z) → π (lepoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  refine lepoll_trans X Y Z (eqpoll_imp_lepoll X Y hXY) hYZ
end;

opaque symbol lepoll_eq_trans (X Y Z : τ ι) :
  π (lepoll X Y) → π (eqpoll Y Z) → π (lepoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  refine lepoll_trans X Y Z hXY (eqpoll_imp_lepoll Y Z hYZ)
end;

// Asymmetry law
opaque symbol eqpollI (X Y : τ ι) :
  π (lepoll X Y) → π (lepoll Y X) → π (eqpoll X Y) ≔
begin
  assume X Y hXY hYX;
  have hXY' : π (`∃ (f : τ ι), f ∈ inj X Y)
    { refine ind_eq (eq_sym (lepoll_def X Y)) (λ p, p) hXY };
  have hYX' : π (`∃ (f : τ ι), f ∈ inj Y X)
    { refine ind_eq (eq_sym (lepoll_def Y X)) (λ p, p) hYX };
  rewrite eqpoll_def;
  refine ∃ₑ hXY' _;
  assume f hf;
  refine ∃ₑ hYX' _;
  assume g hg;
  refine schroeder_bernstein f X Y g hf hg
end;

// schematic conclusion P
opaque symbol eqpollE (X Y : τ ι) (P : Prop) :
  π (eqpoll X Y) → (π (lepoll X Y) → π (lepoll Y X) → π P) → π P ≔
begin
  assume X Y P he hk;
  have he' : π (`∃ (f : τ ι), f ∈ bij X Y)
    { refine ind_eq (eq_sym (eqpoll_def X Y)) (λ p, p) he };
  refine ∃ₑ he' _;
  assume f hf;
  refine hk _ _
  { rewrite lepoll_def; refine ∃ᵢ f (bij_is_inj f X Y hf) }
  { rewrite lepoll_def;
    refine ∃ᵢ (converse f) (bij_is_inj (converse f) Y X (bij_converse_bij f X Y hf)) }
end;

opaque symbol eqpoll_iff (X Y : τ ι) :
  π (eqpoll X Y ⇔ (lepoll X Y ∧ lepoll Y X)) ≔
begin
  assume X Y;
  apply ∧ᵢ
  { assume he;
    refine eqpollE X Y (lepoll X Y ∧ lepoll Y X) he _;
    assume h1 h2; refine ∧ᵢ h1 h2 }
  { assume h; refine eqpollI X Y (∧ₑ₁ h) (∧ₑ₂ h) }
end;

opaque symbol lepoll_0_is_0 (A : τ ι) :
  π (lepoll A empty) → π (A = empty) ≔
begin
  assume A h;
  have h' : π (`∃ (f : τ ι), f ∈ inj A empty)
    { refine ind_eq (eq_sym (lepoll_def A empty)) (λ p, p) h };
  refine ∃ₑ h' _; assume f hf;
  refine equals0I A _; assume y hy;
  refine emptyE (fapply f y)
    (fapply_type f y A (λ _, empty) (inj_is_fun f A empty hf) hy)
end;

// empty_lepollI = empty_subsetI [THEN subset_imp_lepoll] : 0 ≼ A
opaque symbol empty_lepollI (A : τ ι) :
  π (lepoll empty A) ≔
begin
  assume A; refine subset_imp_lepoll empty A (empty_subset A)
end;

opaque symbol lepoll_0_iff (A : τ ι) :
  π (lepoll A empty ⇔ (A = empty)) ≔
begin
  assume A;
  refine ∧ᵢ _ _
  { assume h; refine lepoll_0_is_0 A h }
  { assume heq; rewrite heq; refine lepoll_refl empty }
end;

opaque symbol Un_lepoll_Un (A B C D : τ ι) :
  π (lepoll A B) → π (lepoll C D) → π (Int B D = empty) →
  π (lepoll (Un A C) (Un B D)) ≔
begin
  admit
end;

// eqpoll_0_is_0 = eqpoll_imp_lepoll [THEN lepoll_0_is_0] : A ≈ 0 ⟹ A=0
opaque symbol eqpoll_0_is_0 (A : τ ι) :
  π (eqpoll A empty) → π (A = empty) ≔
begin
  assume A h; refine lepoll_0_is_0 A (eqpoll_imp_lepoll A empty h)
end;

opaque symbol eqpoll_0_iff (A : τ ι) :
  π (eqpoll A empty ⇔ (A = empty)) ≔
begin
  assume A;
  refine ∧ᵢ _ _
  { assume h; refine eqpoll_0_is_0 A h }
  { assume heq; rewrite heq; refine eqpoll_refl empty }
end;

opaque symbol eqpoll_disjoint_Un (A B C D : τ ι) :
  π (eqpoll A B) → π (eqpoll C D) → π (Int A C = empty) → π (Int B D = empty) →
  π (eqpoll (Un A C) (Un B D)) ≔
begin
  admit
end;

// ===========================================================================
// lesspoll: contributions by Krzysztof Grabczewski
// ===========================================================================

opaque symbol lesspoll_not_refl (i : τ ι) :
  π (¬ (lesspoll i i)) ≔
begin
  assume i h;
  have h' : π (lepoll i i ∧ ¬ eqpoll i i)
    { refine ind_eq (eq_sym (lesspoll_def i i)) (λ p, p) h };
  refine (∧ₑ₂ h') (eqpoll_refl i)
end;

// schematic conclusion P
opaque symbol lesspoll_irrefl (i : τ ι) (P : Prop) :
  π (lesspoll i i) → π P ≔
begin
  assume i P h;
  have h' : π (lepoll i i ∧ ¬ eqpoll i i)
    { refine ind_eq (eq_sym (lesspoll_def i i)) (λ p, p) h };
  refine ⊥ₑ ((∧ₑ₂ h') (eqpoll_refl i))
end;

opaque symbol lesspoll_imp_lepoll (A B : τ ι) :
  π (lesspoll A B) → π (lepoll A B) ≔
begin
  assume A B h;
  have h' : π (lepoll A B ∧ ¬ eqpoll A B)
    { refine ind_eq (eq_sym (lesspoll_def A B)) (λ p, p) h };
  refine ∧ₑ₁ h'
end;

opaque symbol lepoll_well_ord (A B r : τ ι) :
  π (lepoll A B) → π (well_ord B r) → π (`∃ (s : τ ι), well_ord A s) ≔
begin
  admit
end;

opaque symbol lepoll_iff_leqpoll (A B : τ ι) :
  π (lepoll A B ⇔ (lesspoll A B ∨ eqpoll A B)) ≔
begin
  assume A B;
  apply ∧ᵢ
  { assume hlep;
    refine ∨ₑ (em (eqpoll A B)) _ _
    { assume he; refine ∨ᵢ₂ he }
    { assume hne;
      refine ∨ᵢ₁ _;
      rewrite lesspoll_def;
      refine ∧ᵢ hlep hne } }
  { assume h;
    refine ∨ₑ h _ _
    { assume hl; refine lesspoll_imp_lepoll A B hl }
    { assume he; refine eqpoll_imp_lepoll A B he } }
end;

opaque symbol inj_not_surj_succ (f A m : τ ι) :
  π (f ∈ inj A (succ m)) → π (f ∉ surj A (succ m)) →
  π (`∃ (g : τ ι), g ∈ inj A m) ≔
begin
  admit
end;

// Variations on transitivity
opaque symbol lesspoll_trans1 (X Y Z : τ ι) :
  π (lepoll X Y) → π (lesspoll Y Z) → π (lesspoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  have hYZ' : π (lepoll Y Z ∧ ¬ eqpoll Y Z)
    { refine ind_eq (eq_sym (lesspoll_def Y Z)) (λ p, p) hYZ };
  rewrite lesspoll_def;
  refine ∧ᵢ (lepoll_trans X Y Z hXY (∧ₑ₁ hYZ')) _;
  assume heXZ;
  refine (∧ₑ₂ hYZ') _;
  refine eqpollE X Z (eqpoll Y Z) heXZ _;
  assume h1 h2;
  refine eqpollI Y Z (∧ₑ₁ hYZ') (lepoll_trans Z X Y h2 hXY)
end;

opaque symbol lesspoll_trans2 (X Y Z : τ ι) :
  π (lesspoll X Y) → π (lepoll Y Z) → π (lesspoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  have hXY' : π (lepoll X Y ∧ ¬ eqpoll X Y)
    { refine ind_eq (eq_sym (lesspoll_def X Y)) (λ p, p) hXY };
  rewrite lesspoll_def;
  refine ∧ᵢ (lepoll_trans X Y Z (∧ₑ₁ hXY') hYZ) _;
  assume heXZ;
  refine (∧ₑ₂ hXY') _;
  refine eqpollE X Z (eqpoll X Y) heXZ _;
  assume h1 h2;
  refine eqpollI X Y (∧ₑ₁ hXY') (lepoll_trans Y Z X hYZ h2)
end;

opaque symbol lesspoll_trans (X Y Z : τ ι) :
  π (lesspoll X Y) → π (lesspoll Y Z) → π (lesspoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  refine lesspoll_trans1 X Y Z (lesspoll_imp_lepoll X Y hXY) hYZ
end;

opaque symbol eq_lesspoll_trans (X Y Z : τ ι) :
  π (eqpoll X Y) → π (lesspoll Y Z) → π (lesspoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  refine lesspoll_trans1 X Y Z (eqpoll_imp_lepoll X Y hXY) hYZ
end;

opaque symbol lesspoll_eq_trans (X Y Z : τ ι) :
  π (lesspoll X Y) → π (eqpoll Y Z) → π (lesspoll X Z) ≔
begin
  assume X Y Z hXY hYZ;
  refine lesspoll_trans2 X Y Z hXY (eqpoll_imp_lepoll Y Z hYZ)
end;

// ===========================================================================
// μ -- the least number operator
// ===========================================================================

opaque symbol Least_equality (P : τ ι → Prop) (i : τ ι) :
  π (P i) → π (Ord i) → (Π (x : τ ι), π (lt x i) → π (¬ (P x))) →
  π (Least (λ x, P x) = i) ≔
begin
  assume P i hPi hOi hmin;
  rewrite Least_def;
  refine the_equality (λ k, Ord k ∧ P k ∧ (`∀ (j : τ ι), lt j k ⇒ ¬ P j)) i _ _
  { refine ∧ᵢ hOi (∧ᵢ hPi _);
    assume j hj; refine hmin j hj }
  { assume k hk;
    have hOk : π (Ord k) { refine ∧ₑ₁ hk };
    have hPk : π (P k) { refine ∧ₑ₁ (∧ₑ₂ hk) };
    have hmink : π (`∀ (j : τ ι), lt j k ⇒ ¬ P j) { refine ∧ₑ₂ (∧ₑ₂ hk) };
    refine ∨ₑ (Ord_linear i k hOi hOk) _ _
    { assume hik; refine ⊥ₑ (hmink i (ltI i k hik hOk) hPi) }
    { assume hd; refine ∨ₑ hd _ _
      { assume hik; refine eq_sym hik }
      { assume hki; refine ⊥ₑ (hmin k (ltI k i hki hOi) hPk) } } }
end;

opaque symbol LeastI (P : τ ι → Prop) (i : τ ι) :
  π (P i) → π (Ord i) → π (P (Least (λ x, P x))) ≔
begin
  assume P i hPi hOi;
  have hind : π (P i ⇒ P (Least (λ x, P x)))
    { refine trans_induct i (λ i, P i ⇒ P (Least (λ x, P x))) hOi _;
      assume x hOx hIH hPx;
      refine ∨ₑ (em (P (Least (λ x, P x)))) _ _
      { assume hyes; refine hyes }
      { assume hno;
        have hmin : Π (z : τ ι), π (lt z x) → π (¬ P z)
          { assume z hzx hPz; refine hno (hIH z (ltD z x hzx) hPz) };
        have hLeq : π (Least (λ x, P x) = x) { refine Least_equality P x hPx hOx hmin };
        refine ind_eq hLeq (λ w, P w) hPx } };
  refine hind hPi
end;

// Helper: Least P either satisfies the full guard predicate, or equals 0.
// (The guard has a unique witness — the least ordinal with P — or none.)
private opaque symbol Least_dichotomy (P : τ ι → Prop) :
  π ((Ord (Least (λ x, P x)) ∧ (P (Least (λ x, P x))
       ∧ (`∀ (j : τ ι), lt j (Least (λ x, P x)) ⇒ ¬ P j)))
     ∨ (Least (λ x, P x) = empty)) ≔
begin
  assume P;
  refine ∨ₑ (em (`∃ (x : τ ι),
      (Ord x ∧ (P x ∧ (`∀ (j : τ ι), lt j x ⇒ ¬ P j)))
      ∧ (`∀ (z : τ ι),
           (Ord z ∧ (P z ∧ (`∀ (j : τ ι), lt j z ⇒ ¬ P j))) ⇒ z = x))) _ _
  { assume hexu; refine ∃ₑ hexu _; assume w hw;
    have hThe : π (Least (λ x, P x) = w)
      { rewrite Least_def;
        refine the_equality (λ k, Ord k ∧ (P k ∧ (`∀ (j : τ ι), lt j k ⇒ ¬ P j)))
          w (∧ₑ₁ hw) (∧ₑ₂ hw) };
    refine ∨ᵢ₁ _; rewrite hThe; refine ∧ₑ₁ hw }
  { assume hnou;
    refine ∨ᵢ₂ _;
    rewrite Least_def;
    refine the_0 (λ k, Ord k ∧ (P k ∧ (`∀ (j : τ ι), lt j k ⇒ ¬ P j))) hnou }
end;

opaque symbol Least_le (P : τ ι → Prop) (i : τ ι) :
  π (P i) → π (Ord i) → π (le (Least (λ x, P x)) i) ≔
begin
  assume P i hPi hOi;
  refine ∨ₑ (Least_dichotomy P) _ _
  { assume hg;
    have hOL : π (Ord (Least (λ x, P x))) { refine ∧ₑ₁ hg };
    have hmin : π (`∀ (j : τ ι), lt j (Least (λ x, P x)) ⇒ ¬ P j) { refine ∧ₑ₂ (∧ₑ₂ hg) };
    // trichotomy Least P vs i: if i < Least P then ¬P i (min), contra; else Least P ≤ i
    refine ∨ₑ (Ord_linear (Least (λ x, P x)) i hOL hOi) _ _
    { assume hLi; refine leI (Least (λ x, P x)) i hLi hOi }
    { assume hd; refine ∨ₑ hd _ _
      { assume heq; refine le_eqI (Least (λ x, P x)) i heq hOi }
      { assume hiL; refine ⊥ₑ (hmin i (ltI i (Least (λ x, P x)) hiL hOL) hPi) } } }
  { assume he; rewrite he; refine Ord_0_le i hOi }
end;

// schematic conclusion Q
opaque symbol less_LeastE (P : τ ι → Prop) (i : τ ι) (Q : Prop) :
  π (P i) → π (lt i (Least (λ x, P x))) → π Q ≔
begin
  assume P i Q hPi hlt;
  refine ∨ₑ (Least_dichotomy P) _ _
  { assume hg; refine ⊥ₑ ((∧ₑ₂ (∧ₑ₂ hg)) i hlt hPi) }
  { assume he; refine ⊥ₑ (not_lt0 i (ind_eq (eq_sym he) (λ z, lt i z) hlt)) }
end;

opaque symbol LeastI2 (P Q : τ ι → Prop) (i : τ ι) :
  π (P i) → π (Ord i) → (Π (j : τ ι), π (P j) → π (Q j)) →
  π (Q (Least (λ j, P j))) ≔
begin
  assume P Q i hPi hOi hPQ;
  refine hPQ (Least (λ x, P x)) (LeastI P i hPi hOi)
end;

opaque symbol Least_0 (P : τ ι → Prop) :
  π (¬ (`∃ (i : τ ι), Ord i ∧ P i)) → π (Least (λ x, P x) = empty) ≔
begin
  assume P hno;
  rewrite Least_def;
  refine the_0 (λ k, Ord k ∧ P k ∧ (`∀ (j : τ ι), lt j k ⇒ ¬ P j)) _;
  assume hex;
  refine ∃ₑ hex _; assume x hx;
  have hg : π (Ord x ∧ P x ∧ (`∀ (j : τ ι), lt j x ⇒ ¬ P j)) { refine ∧ₑ₁ hx };
  refine hno (∃ᵢ x (∧ᵢ (∧ₑ₁ hg) (∧ₑ₁ (∧ₑ₂ hg))))
end;

opaque symbol Ord_Least (P : τ ι → Prop) :
  π (Ord (Least (λ x, P x))) ≔
begin
  assume P;
  refine ∨ₑ (Least_dichotomy P) _ _
  { assume hg; refine ∧ₑ₁ hg }
  { assume he; rewrite he; refine Ord_0 }
end;


// ===========================================================================
// Basic Properties of Cardinals
// ===========================================================================

// The_cong: pointwise-equivalent descriptions describe the same object.
// Choice-free: either both have the same unique witness (the_equality twice)
// or neither has one (the_0 twice).
private opaque symbol The_cong (P Q : τ ι → Prop) :
  (Π (y : τ ι), π (P y ⇔ Q y)) → π (The P = The Q) ≔
begin
  assume P Q hiff;
  refine ∨ₑ (em (`∃ (x : τ ι), P x ∧ (`∀ (z : τ ι), P z ⇒ z = x))) _ _
  { assume hex;
    refine ∃ₑ hex _;
    assume x hx;
    have hTP : π (The P = x)
      { refine the_equality P x (∧ₑ₁ hx) _;
        assume z hz; refine (∧ₑ₂ hx) z hz };
    have hTQ : π (The Q = x)
      { refine the_equality Q x (∧ₑ₁ (hiff x) (∧ₑ₁ hx)) _;
        assume z hz; refine (∧ₑ₂ hx) z (∧ₑ₂ (hiff z) hz) };
    rewrite hTP; refine eq_sym hTQ }
  { assume hno;
    have hnoQ : π (¬ (`∃ (x : τ ι), Q x ∧ (`∀ (z : τ ι), Q z ⇒ z = x)))
      { assume hexQ;
        refine hno _;
        refine ∃ₑ hexQ _;
        assume x hx;
        refine ∃ᵢ x (∧ᵢ (∧ₑ₂ (hiff x) (∧ₑ₁ hx)) _);
        assume z hz; refine (∧ₑ₂ hx) z (∧ₑ₁ (hiff z) hz) };
    have hTP : π (The P = empty) { refine the_0 P hno };
    have hTQ : π (The Q = empty) { refine the_0 Q hnoQ };
    rewrite hTP; refine eq_sym hTQ }
end;

opaque symbol Least_cong (P Q : τ ι → Prop) :
  (Π (y : τ ι), π (P y ⇔ Q y)) → π (Least (λ x, P x) = Least (λ x, Q x)) ≔
begin
  assume P Q hiff;
  rewrite Least_def;
  rewrite Least_def;
  refine The_cong
    (λ i, Ord i ∧ P i ∧ (`∀ (j : τ ι), lt j i ⇒ ¬ P j))
    (λ i, Ord i ∧ Q i ∧ (`∀ (j : τ ι), lt j i ⇒ ¬ Q j)) _;
  assume y;
  apply ∧ᵢ
  { assume h;
    refine ∧ᵢ (∧ₑ₁ h) (∧ᵢ (∧ₑ₁ (hiff y) (∧ₑ₁ (∧ₑ₂ h))) _);
    assume j hj hQj;
    refine (∧ₑ₂ (∧ₑ₂ h)) j hj (∧ₑ₂ (hiff j) hQj) }
  { assume h;
    refine ∧ᵢ (∧ₑ₁ h) (∧ᵢ (∧ₑ₂ (hiff y) (∧ₑ₁ (∧ₑ₂ h))) _);
    assume j hj hPj;
    refine (∧ₑ₂ (∧ₑ₂ h)) j hj (∧ₑ₁ (hiff j) hPj) }
end;

opaque symbol cardinal_cong (X Y : τ ι) :
  π (eqpoll X Y) → π (cardinal X = cardinal Y) ≔
begin
  assume X Y he;
  rewrite cardinal_def;
  rewrite cardinal_def;
  refine Least_cong (λ i, eqpoll i X) (λ i, eqpoll i Y) _;
  assume i;
  apply ∧ᵢ
  { assume h; refine eqpoll_trans i X Y h he }
  { assume h; refine eqpoll_trans i Y X h (eqpoll_sym X Y he) }
end;

opaque symbol well_ord_cardinal_eqpoll (A r : τ ι) :
  π (well_ord A r) → π (eqpoll (cardinal A) A) ≔
begin
  admit
end;

// Ord_cardinal_eqpoll = well_ord_Memrel [THEN well_ord_cardinal_eqpoll] : Ord(A) ⟹ |A| ≈ A
opaque symbol Ord_cardinal_eqpoll (A : τ ι) :
  π (Ord A) → π (eqpoll (cardinal A) A) ≔
begin
  admit
end;

opaque symbol Ord_cardinal_idem (A : τ ι) :
  π (Ord A) → π (cardinal (cardinal A) = cardinal A) ≔
begin
  admit
end;

opaque symbol well_ord_cardinal_eqE (X r Y s : τ ι) :
  π (well_ord X r) → π (well_ord Y s) → π (cardinal X = cardinal Y) →
  π (eqpoll X Y) ≔
begin
  admit
end;

opaque symbol well_ord_cardinal_eqpoll_iff (X r Y s : τ ι) :
  π (well_ord X r) → π (well_ord Y s) →
  π ((cardinal X = cardinal Y) ⇔ eqpoll X Y) ≔
begin
  admit
end;

opaque symbol Ord_cardinal_le (i : τ ι) :
  π (Ord i) → π (le (cardinal i) i) ≔
begin
  assume i hOi;
  rewrite cardinal_def;
  refine Least_le (λ k, eqpoll k i) i (eqpoll_refl i) hOi
end;

opaque symbol Card_cardinal_eq (K : τ ι) :
  π (Card K) → π (cardinal K = K) ≔
begin
  assume K h;
  have h' : π (K = cardinal K)
    { refine ind_eq (eq_sym (Card_def K)) (λ p, p) h };
  refine eq_sym h'
end;

opaque symbol CardI (i : τ ι) :
  π (Ord i) → (Π (j : τ ι), π (lt j i) → π (¬ (eqpoll j i))) → π (Card i) ≔
begin
  assume i hOi hmin;
  rewrite Card_def;
  rewrite cardinal_def;
  refine eq_sym (Least_equality (λ k, eqpoll k i) i (eqpoll_refl i) hOi hmin)
end;

opaque symbol Card_is_Ord (i : τ ι) :
  π (Card i) → π (Ord i) ≔
begin
  assume i h;
  have h' : π (i = cardinal i)
    { refine ind_eq (eq_sym (Card_def i)) (λ p, p) h };
  rewrite h';
  rewrite cardinal_def;
  refine Ord_Least (λ k, eqpoll k i)
end;

opaque symbol Card_cardinal_le (K : τ ι) :
  π (Card K) → π (le K (cardinal K)) ≔
begin
  assume K h;
  have h' : π (K = cardinal K)
    { refine ind_eq (eq_sym (Card_def K)) (λ p, p) h };
  rewrite left h';
  refine le_refl K (Card_is_Ord K h)
end;

opaque symbol Ord_cardinal (A : τ ι) :
  π (Ord (cardinal A)) ≔
begin
  assume A;
  rewrite cardinal_def;
  refine Ord_Least (λ i, eqpoll i A)
end;

opaque symbol Card_iff_initial (K : τ ι) :
  π (Card K ⇔ (Ord K ∧ (`∀ (j : τ ι), lt j K ⇒ ¬ (eqpoll j K)))) ≔
begin
  assume K;
  refine ∧ᵢ _ _
  { assume h;
    have h' : π (K = cardinal K)
      { refine ind_eq (eq_sym (Card_def K)) (λ p, p) h };
    refine ∧ᵢ (Card_is_Ord K h) _;
    assume j hj he;
    have hj1 : π (lt j (cardinal K)) { refine ind_eq (eq_sym h') (λ z, lt j z) hj };
    have hj2 : π (lt j (Least (λ i, eqpoll i K)))
      { refine ind_eq (eq_sym (cardinal_def K)) (λ z, lt j z) hj1 };
    refine less_LeastE (λ i, eqpoll i K) j ⊥ he hj2 }
  { assume h; refine CardI K (∧ₑ₁ h) (∧ₑ₂ h) }
end;

opaque symbol lt_Card_imp_lesspoll (a i : τ ι) :
  π (Card a) → π (lt i a) → π (lesspoll i a) ≔
begin
  assume a i hCard hlt;
  have hCard' : π (a = cardinal a)
    { refine ind_eq (eq_sym (Card_def a)) (λ p, p) hCard };
  rewrite lesspoll_def;
  refine ∧ᵢ _ _
  { refine le_imp_lepoll i a (leI i a (ltD i a hlt) (lt_Ord2 i a hlt)) }
  { assume he;
    have hlt1 : π (lt i (cardinal a)) { refine ind_eq (eq_sym hCard') (λ z, lt i z) hlt };
    have hlt2 : π (lt i (Least (λ k, eqpoll k a)))
      { refine ind_eq (eq_sym (cardinal_def a)) (λ z, lt i z) hlt1 };
    refine less_LeastE (λ k, eqpoll k a) i ⊥ he hlt2 }
end;

opaque symbol Card_0 :
  π (Card empty) ≔
begin
  rewrite Card_def;
  rewrite cardinal_def;
  refine eq_sym (Least_equality (λ i, eqpoll i empty) empty (eqpoll_refl empty) Ord_0 _);
  assume x hx; refine ⊥ₑ (not_lt0 x hx)
end;

opaque symbol Card_Un (K L : τ ι) :
  π (Card K) → π (Card L) → π (Card (Un K L)) ≔
begin
  admit
end;

opaque symbol Card_cardinal (A : τ ι) :
  π (Card (cardinal A)) ≔
begin
  admit
end;

opaque symbol cardinal_eq_lemma (i j : τ ι) :
  π (le (cardinal i) j) → π (le j i) → π (cardinal j = cardinal i) ≔
begin
  admit
end;

opaque symbol cardinal_mono (i j : τ ι) :
  π (le i j) → π (le (cardinal i) (cardinal j)) ≔
begin
  admit
end;

opaque symbol cardinal_lt_imp_lt (i j : τ ι) :
  π (lt (cardinal i) (cardinal j)) → π (Ord i) → π (Ord j) → π (lt i j) ≔
begin
  admit
end;

opaque symbol Card_lt_imp_lt (i K : τ ι) :
  π (lt (cardinal i) K) → π (Ord i) → π (Card K) → π (lt i K) ≔
begin
  admit
end;

opaque symbol Card_lt_iff (i K : τ ι) :
  π (Ord i) → π (Card K) → π (lt (cardinal i) K ⇔ lt i K) ≔
begin
  admit
end;

opaque symbol Card_le_iff (i K : τ ι) :
  π (Ord i) → π (Card K) → π (le K (cardinal i) ⇔ le K i) ≔
begin
  admit
end;

opaque symbol well_ord_lepoll_imp_cardinal_le (B r A : τ ι) :
  π (well_ord B r) → π (lepoll A B) → π (le (cardinal A) (cardinal B)) ≔
begin
  admit
end;

opaque symbol lepoll_cardinal_le (A i : τ ι) :
  π (lepoll A i) → π (Ord i) → π (le (cardinal A) i) ≔
begin
  admit
end;

opaque symbol lepoll_Ord_imp_eqpoll (A i : τ ι) :
  π (lepoll A i) → π (Ord i) → π (eqpoll (cardinal A) A) ≔
begin
  admit
end;

opaque symbol lesspoll_imp_eqpoll (A i : τ ι) :
  π (lesspoll A i) → π (Ord i) → π (eqpoll (cardinal A) A) ≔
begin
  admit
end;

opaque symbol cardinal_subset_Ord (A i : τ ι) :
  π (A ⊆ i) → π (Ord i) → π (cardinal A ⊆ i) ≔
begin
  admit
end;

// ===========================================================================
// The finite cardinals
// ===========================================================================

opaque symbol cons_lepoll_consD (u A v B : τ ι) :
  π (lepoll (cons u A) (cons v B)) → π (u ∉ A) → π (v ∉ B) → π (lepoll A B) ≔
begin
  admit
end;

opaque symbol cons_eqpoll_consD (u A v B : τ ι) :
  π (eqpoll (cons u A) (cons v B)) → π (u ∉ A) → π (v ∉ B) → π (eqpoll A B) ≔
begin
  admit
end;

opaque symbol succ_lepoll_succD (m n : τ ι) :
  π (lepoll (succ m) (succ n)) → π (lepoll m n) ≔
begin
  admit
end;

opaque symbol nat_lepoll_imp_le (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (lepoll m n) → π (le m n) ≔
begin
  admit
end;

opaque symbol nat_eqpoll_iff (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (eqpoll m n ⇔ (m = n)) ≔
begin
  admit
end;

opaque symbol nat_into_Card (n : τ ι) :
  π (n ∈ omega) → π (Card n) ≔
begin
  admit
end;

// cardinal_0 = nat_0I [THEN nat_into_Card, THEN Card_cardinal_eq] : |0| = 0
opaque symbol cardinal_0 :
  π (cardinal empty = empty) ≔
begin
  refine Card_cardinal_eq empty Card_0
end;

// cardinal_1 = nat_1I [THEN nat_into_Card, THEN Card_cardinal_eq] : |1| = 1
opaque symbol cardinal_1 :
  π (cardinal (succ empty) = succ empty) ≔
begin
  rewrite cardinal_def;
  refine Least_equality (λ k, eqpoll k (succ empty)) (succ empty)
    (eqpoll_refl (succ empty)) (Ord_succ empty Ord_0) _;
  assume j hj he;
  have hjeq : π (j = empty) {
    refine ∨ₑ (∧ₑ₁ (succ_iff j empty) (ltD j (succ empty) hj)) _ _
    { assume h; refine h }
    { assume h; refine ⊥ₑ (emptyE j h) } };
  refine succ_neq_0 empty
    (eqpoll_0_is_0 (succ empty)
      (eqpoll_sym empty (succ empty)
        (ind_eq (eq_sym hjeq) (λ z, eqpoll z (succ empty)) he)))
end;

// schematic conclusion P
opaque symbol succ_lepoll_natE (n : τ ι) (P : Prop) :
  π (lepoll (succ n) n) → π (n ∈ omega) → π P ≔
begin
  admit
end;

opaque symbol nat_lepoll_imp_ex_eqpoll_n (n X : τ ι) :
  π (n ∈ omega) → π (lepoll omega X) →
  π (`∃ (Y : τ ι), Y ⊆ X ∧ eqpoll n Y) ≔
begin
  admit
end;

// ===========================================================================
// ≼, ≺ and natural numbers
// ===========================================================================

opaque symbol lepoll_succ (i : τ ι) :
  π (lepoll i (succ i)) ≔
begin
  assume i; refine subset_imp_lepoll i (succ i) _;
  assume x hx; refine succI2 x i hx
end;

opaque symbol lepoll_imp_lesspoll_succ (A m : τ ι) :
  π (lepoll A m) → π (m ∈ omega) → π (lesspoll A (succ m)) ≔
begin
  admit
end;

opaque symbol lesspoll_succ_imp_lepoll (A m : τ ι) :
  π (lesspoll A (succ m)) → π (m ∈ omega) → π (lepoll A m) ≔
begin
  admit
end;

opaque symbol lesspoll_succ_iff (m A : τ ι) :
  π (m ∈ omega) → π (lesspoll A (succ m) ⇔ lepoll A m) ≔
begin
  admit
end;

opaque symbol lepoll_succ_disj (A m : τ ι) :
  π (lepoll A (succ m)) → π (m ∈ omega) →
  π (lepoll A m ∨ eqpoll A (succ m)) ≔
begin
  admit
end;

opaque symbol lesspoll_cardinal_lt (A i : τ ι) :
  π (lesspoll A i) → π (Ord i) → π (lt (cardinal A) i) ≔
begin
  admit
end;

// ===========================================================================
// The first infinite cardinal: Omega, or nat
// ===========================================================================

opaque symbol lt_not_lepoll (n i : τ ι) :
  π (lt n i) → π (n ∈ omega) → π (¬ (lepoll i n)) ≔
begin
  admit
end;

opaque symbol Ord_nat_eqpoll_iff (i n : τ ι) :
  π (Ord i) → π (n ∈ omega) → π (eqpoll i n ⇔ (i = n)) ≔
begin
  admit
end;

opaque symbol Card_nat :
  π (Card omega) ≔
begin
  admit
end;

opaque symbol nat_le_cardinal (i : τ ι) :
  π (le omega i) → π (le omega (cardinal i)) ≔
begin
  admit
end;

opaque symbol n_lesspoll_nat (n : τ ι) :
  π (n ∈ omega) → π (lesspoll n omega) ≔
begin
  admit
end;

// ===========================================================================
// Towards Cardinal Arithmetic — congruence laws
// ===========================================================================

opaque symbol cons_lepoll_cong (A B b a : τ ι) :
  π (lepoll A B) → π (b ∉ B) → π (lepoll (cons a A) (cons b B)) ≔
begin
  admit
end;

opaque symbol cons_eqpoll_cong (A B a b : τ ι) :
  π (eqpoll A B) → π (a ∉ A) → π (b ∉ B) → π (eqpoll (cons a A) (cons b B)) ≔
begin
  admit
end;

opaque symbol cons_lepoll_cons_iff (a A b B : τ ι) :
  π (a ∉ A) → π (b ∉ B) → π (lepoll (cons a A) (cons b B) ⇔ lepoll A B) ≔
begin
  admit
end;

opaque symbol cons_eqpoll_cons_iff (a A b B : τ ι) :
  π (a ∉ A) → π (b ∉ B) → π (eqpoll (cons a A) (cons b B) ⇔ eqpoll A B) ≔
begin
  admit
end;

opaque symbol singleton_eqpoll_1 (a : τ ι) :
  π (eqpoll (singleton a) (succ empty)) ≔
begin
  admit
end;

opaque symbol cardinal_singleton (a : τ ι) :
  π (cardinal (singleton a) = succ empty) ≔
begin
  admit
end;

opaque symbol not_0_is_lepoll_1 (A : τ ι) :
  π (A ≠ empty) → π (lepoll (succ empty) A) ≔
begin
  admit
end;

opaque symbol succ_eqpoll_cong (A B : τ ι) :
  π (eqpoll A B) → π (eqpoll (succ A) (succ B)) ≔
begin
  admit
end;

opaque symbol sum_eqpoll_cong (A C B D : τ ι) :
  π (eqpoll A C) → π (eqpoll B D) → π (eqpoll (sum A B) (sum C D)) ≔
begin
  admit
end;

opaque symbol prod_eqpoll_cong (A C B D : τ ι) :
  π (eqpoll A C) → π (eqpoll B D) →
  π (eqpoll (Sigma A (λ _, B)) (Sigma C (λ _, D))) ≔
begin
  admit
end;

opaque symbol inj_disjoint_eqpoll (f A B : τ ι) :
  π (f ∈ inj A B) → π (Int A B = empty) →
  π (eqpoll (Un A (Diff B (range f))) B) ≔
begin
  admit
end;

// ===========================================================================
// Lemmas by Krzysztof Grabczewski
// ===========================================================================

opaque symbol Diff_sing_lepoll (a A n : τ ι) :
  π (a ∈ A) → π (lepoll A (succ n)) → π (lepoll (Diff A (singleton a)) n) ≔
begin
  admit
end;

opaque symbol lepoll_Diff_sing (n A a : τ ι) :
  π (lepoll (succ n) A) → π (lepoll n (Diff A (singleton a))) ≔
begin
  admit
end;

opaque symbol Diff_sing_eqpoll (a A n : τ ι) :
  π (a ∈ A) → π (eqpoll A (succ n)) → π (eqpoll (Diff A (singleton a)) n) ≔
begin
  admit
end;

opaque symbol lepoll_1_is_sing (A a : τ ι) :
  π (lepoll A (succ empty)) → π (a ∈ A) → π (A = singleton a) ≔
begin
  admit
end;

opaque symbol Un_lepoll_sum (A B : τ ι) :
  π (lepoll (Un A B) (sum A B)) ≔
begin
  admit
end;

opaque symbol well_ord_Un (X R Y S : τ ι) :
  π (well_ord X R) → π (well_ord Y S) → π (`∃ (T : τ ι), well_ord (Un X Y) T) ≔
begin
  admit
end;

opaque symbol disj_Un_eqpoll_sum (A B : τ ι) :
  π (Int A B = empty) → π (eqpoll (Un A B) (sum A B)) ≔
begin
  admit
end;

// ===========================================================================
// Finite and infinite sets
// ===========================================================================

opaque symbol eqpoll_imp_Finite_iff (A B : τ ι) :
  π (eqpoll A B) → π (Finite A ⇔ Finite B) ≔
begin
  admit
end;

opaque symbol Finite_0 :
  π (Finite empty) ≔
begin
  admit
end;

opaque symbol Finite_cons (x y : τ ι) :
  π (Finite x) → π (Finite (cons y x)) ≔
begin
  admit
end;

opaque symbol Finite_succ (x : τ ι) :
  π (Finite x) → π (Finite (succ x)) ≔
begin
  admit
end;

opaque symbol lepoll_nat_imp_Finite (A n : τ ι) :
  π (lepoll A n) → π (n ∈ omega) → π (Finite A) ≔
begin
  admit
end;

opaque symbol lesspoll_nat_is_Finite (A : τ ι) :
  π (lesspoll A omega) → π (Finite A) ≔
begin
  admit
end;

opaque symbol lepoll_Finite (Y X : τ ι) :
  π (lepoll Y X) → π (Finite X) → π (Finite Y) ≔
begin
  admit
end;

// subset_Finite = subset_imp_lepoll [THEN lepoll_Finite] : ⟦A ⊆ B; Finite(B)⟧ ⟹ Finite(A)
opaque symbol subset_Finite (A B : τ ι) :
  π (A ⊆ B) → π (Finite B) → π (Finite A) ≔
begin
  admit
end;

opaque symbol Finite_cons_iff (y x : τ ι) :
  π (Finite (cons y x) ⇔ Finite x) ≔
begin
  admit
end;

opaque symbol Finite_succ_iff (x : τ ι) :
  π (Finite (succ x) ⇔ Finite x) ≔
begin
  admit
end;

opaque symbol Finite_Int (A B : τ ι) :
  π (Finite A ∨ Finite B) → π (Finite (Int A B)) ≔
begin
  admit
end;

// Finite_Diff = Diff_subset [THEN subset_Finite] : Finite(A) ⟹ Finite(A - B)
opaque symbol Finite_Diff (A B : τ ι) :
  π (Finite A) → π (Finite (Diff A B)) ≔
begin
  admit
end;

opaque symbol nat_le_infinite_Ord (i : τ ι) :
  π (Ord i) → π (¬ (Finite i)) → π (le omega i) ≔
begin
  admit
end;

opaque symbol Finite_imp_well_ord (A : τ ι) :
  π (Finite A) → π (`∃ (r : τ ι), well_ord A r) ≔
begin
  admit
end;

opaque symbol succ_lepoll_imp_not_empty (x y : τ ι) :
  π (lepoll (succ x) y) → π (y ≠ empty) ≔
begin
  admit
end;

opaque symbol eqpoll_succ_imp_not_empty (x n : τ ι) :
  π (eqpoll x (succ n)) → π (x ≠ empty) ≔
begin
  admit
end;

// Finite_Fin_lemma [rule_format] : n ∈ nat ⟹ ∀A. (A≈n ∧ A ⊆ X) ⟶ A ∈ Fin(X)
opaque symbol Finite_Fin_lemma (n X : τ ι) :
  π (n ∈ omega) → π (`∀ (A : τ ι), (eqpoll A n ∧ A ⊆ X) ⇒ A ∈ Fin X) ≔
begin
  admit
end;

opaque symbol Finite_Fin (A X : τ ι) :
  π (Finite A) → π (A ⊆ X) → π (A ∈ Fin X) ≔
begin
  admit
end;

// Fin_lemma [rule_format] : n ∈ nat ⟹ ∀A. A ≈ n ⟶ A ∈ Fin(A)
opaque symbol Fin_lemma (n : τ ι) :
  π (n ∈ omega) → π (`∀ (A : τ ι), eqpoll A n ⇒ A ∈ Fin A) ≔
begin
  admit
end;

opaque symbol Finite_into_Fin (A : τ ι) :
  π (Finite A) → π (A ∈ Fin A) ≔
begin
  admit
end;

opaque symbol Fin_into_Finite (A U : τ ι) :
  π (A ∈ Fin U) → π (Finite A) ≔
begin
  admit
end;

opaque symbol Finite_Fin_iff (A : τ ι) :
  π (Finite A ⇔ A ∈ Fin A) ≔
begin
  admit
end;

opaque symbol Finite_Un (A B : τ ι) :
  π (Finite A) → π (Finite B) → π (Finite (Un A B)) ≔
begin
  admit
end;

opaque symbol Finite_Un_iff (A B : τ ι) :
  π (Finite (Un A B) ⇔ (Finite A ∧ Finite B)) ≔
begin
  admit
end;

opaque symbol Finite_Union (X : τ ι) :
  π (Ball X (λ y, Finite y)) → π (Finite X) → π (Finite (Union X)) ≔
begin
  admit
end;

// Induction principle for Finite(A)
opaque symbol Finite_induct (A : τ ι) (P : τ ι → Prop) :
  π (Finite A) → π (P empty) →
  (Π (x B : τ ι), π (Finite B) → π (x ∉ B) → π (P B) → π (P (cons x B))) →
  π (P A) ≔
begin
  admit
end;

opaque symbol Diff_sing_Finite (A a : τ ι) :
  π (Finite (Diff A (singleton a))) → π (Finite A) ≔
begin
  admit
end;

// Diff_Finite [rule_format] : Finite(B) ⟹ Finite(A-B) ⟶ Finite(A)
opaque symbol Diff_Finite (B A : τ ι) :
  π (Finite B) → π (Finite (Diff A B) ⇒ Finite A) ≔
begin
  admit
end;

opaque symbol Finite_RepFun (A : τ ι) (f : τ ι → τ ι) :
  π (Finite A) → π (Finite (RepFun A f)) ≔
begin
  admit
end;

// Finite_RepFun_iff_lemma [rule_format]
opaque symbol Finite_RepFun_iff_lemma (x : τ ι) (f : τ ι → τ ι) :
  π (Finite x) → (Π (u v : τ ι), π (f u = f v) → π (u = v)) →
  π (`∀ (A : τ ι), (x = RepFun A f) ⇒ Finite A) ≔
begin
  admit
end;

opaque symbol Finite_RepFun_iff (f : τ ι → τ ι) (A : τ ι) :
  π (`∀ (u : τ ι), `∀ (v : τ ι), (f u = f v) ⇒ (u = v)) →
  π (Finite (RepFun A f) ⇔ Finite A) ≔
begin
  admit
end;

opaque symbol Finite_Pow (A : τ ι) :
  π (Finite A) → π (Finite (Pow A)) ≔
begin
  admit
end;

opaque symbol Finite_Pow_imp_Finite (A : τ ι) :
  π (Finite (Pow A)) → π (Finite A) ≔
begin
  admit
end;

opaque symbol Finite_Pow_iff (A : τ ι) :
  π (Finite (Pow A) ⇔ Finite A) ≔
begin
  admit
end;

opaque symbol Finite_cardinal_iff (i : τ ι) :
  π (Ord i) → π (Finite (cardinal i) ⇔ Finite i) ≔
begin
  admit
end;

opaque symbol nat_wf_on_converse_Memrel (n : τ ι) :
  π (n ∈ omega) → π (wf n (converse (Memrel n))) ≔
begin
  admit
end;

opaque symbol nat_well_ord_converse_Memrel (n : τ ι) :
  π (n ∈ omega) → π (well_ord n (converse (Memrel n))) ≔
begin
  admit
end;

opaque symbol well_ord_converse (A r : τ ι) :
  π (well_ord A r) →
  π (well_ord (ordertype A r) (converse (Memrel (ordertype A r)))) →
  π (well_ord A (converse r)) ≔
begin
  admit
end;

opaque symbol ordertype_eq_n (A r n : τ ι) :
  π (well_ord A r) → π (eqpoll A n) → π (n ∈ omega) →
  π (ordertype A r = n) ≔
begin
  admit
end;

opaque symbol Finite_well_ord_converse (A r : τ ι) :
  π (Finite A) → π (well_ord A r) → π (well_ord A (converse r)) ≔
begin
  admit
end;

opaque symbol nat_into_Finite (n : τ ι) :
  π (n ∈ omega) → π (Finite n) ≔
begin
  admit
end;

opaque symbol nat_not_Finite :
  π (¬ (Finite omega)) ≔
begin
  admit
end;
