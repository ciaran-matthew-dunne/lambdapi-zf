// ZF.CardinalArith — Cardinal Arithmetic Without the Axiom of Choice
// Faithful SKELETON port of isabelle-src/CardinalArith.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/CardinalArith.thy.)
//
// Isabelle infix/binder notation is rendered with the plain function names:
//   i⊕j = cadd i j        i⊗j = cmult i j        |A| = cardinal A
//   A*B = Sigma A (λ_,B)  A+B = sum A B           μL. P(L) = Least (λ L, P L)
//   m#+n = add m n        m#*n = mult m n         nat = omega
// csquare_rel/jump_cardinal/csucc are ordinary combinations of existing
// primitives (rvimage/rmult/Memrel, Union/RepFun/Collect/ordertype, Least) —
// no new inductive-definition machinery is needed for this module.
//
// `ordermap_csquare_le`'s Isar `defines "z ≡ succ(x∪y)"` is inlined directly
// into the statement below (faithful — it is a pure local abbreviation).

require open ZF.Cardinal ZF.OrderArith ZF.ArithSimp ZF.Finite;

// ===========================================================================
// Definitions
// ===========================================================================

// InfCard(i) ≡ Card(i) ∧ nat ≤ i
constant symbol InfCard (i : τ ι) : Prop;
constant symbol InfCard_def (i : τ ι) :
  π (InfCard i = (Card i ∧ le omega i));

// i ⊗ j ≡ |i*j|
constant symbol cmult (i j : τ ι) : τ ι;
constant symbol cmult_def (i j : τ ι) :
  π (cmult i j = cardinal (Sigma i (λ _, j)));

// i ⊕ j ≡ |i+j|
constant symbol cadd (i j : τ ι) : τ ι;
constant symbol cadd_def (i j : τ ι) :
  π (cadd i j = cardinal (sum i j));

// csquare_rel(K) ≡ rvimage(K*K, λ⟨x,y⟩∈K*K. ⟨x∪y,x,y⟩,
//                           rmult(K,Memrel(K), K*K, rmult(K,Memrel(K), K,Memrel(K))))
constant symbol csquare_rel (K : τ ι) : τ ι;
constant symbol csquare_rel_def (K : τ ι) :
  π (csquare_rel K =
     rvimage (Sigma K (λ _, K))
       (Lambda (Sigma K (λ _, K))
          (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p))))
       (rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))));

// jump_cardinal(K) ≡ ⋃X∈Pow(K). {z. r∈Pow(K*K), well_ord(X,r) ∧ z=ordertype(X,r)}
constant symbol jump_cardinal (K : τ ι) : τ ι;
constant symbol jump_cardinal_def (K : τ ι) :
  π (jump_cardinal K =
     Union (RepFun (Pow K) (λ X,
       RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
              (λ r, ordertype X r))));

// csucc(K) ≡ μL. Card(L) ∧ K<L
constant symbol csucc (K : τ ι) : τ ι;
constant symbol csucc_def (K : τ ι) :
  π (csucc K = Least (λ L, Card L ∧ lt K L));

// ===========================================================================

opaque symbol Card_Union (A : τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Card x)) → π (Card (Union A)) ≔
begin
  assume A hA;
  have hOU : π (Ord (Union A))
    { refine Ord_Union A _; assume x hx; refine Card_is_Ord x (hA x hx) };
  refine CardI (Union A) hOU _;
  assume j hj heqp;
  have hjm : π (j ∈ Union A) { refine ltD j (Union A) hj };
  refine ∃ₑ (UnionE j A hjm) _; assume c hc;
  have hcA : π (c ∈ A) { refine ∧ₑ₁ hc };
  have hjc : π (j ∈ c) { refine ∧ₑ₂ hc };
  have hCc : π (Card c) { refine hA c hcA };
  have hjls : π (lesspoll j c)
    { refine lt_Card_imp_lesspoll c j hCc (ltI j c hjc (Card_is_Ord c hCc)) };
  have hclep : π (lepoll c (Union A))
    { refine subset_imp_lepoll c (Union A) _;
      assume x hx; refine UnionI x c A hx hcA };
  have hcj : π (lepoll c j)
    { refine lepoll_eq_trans c (Union A) j hclep
        (eqpoll_sym j (Union A) heqp) };
  refine lesspoll_irrefl c ⊥ (lesspoll_trans1 c j c hcj hjls)
end;

opaque symbol Card_UN (A : τ ι) (f : τ ι → τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Card (f x))) → π (Card (Union (RepFun A f))) ≔
begin
  assume A f hf;
  refine Card_Union (RepFun A f) _;
  assume x hx;
  refine ∃ₑ (∧ₑ₁ (RepFun_iff x A f) hx) _; assume a ha;
  refine ind_eq (∧ₑ₂ ha) (λ w, Card w) (hf a (∧ₑ₁ ha))
end;

opaque symbol Card_OUN (A : τ ι) (f : τ ι → τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Card (f x))) → π (Card (OUnion A f)) ≔
begin
  assume A f hf;
  rewrite OUnion_def;
  refine ∨ₑ (em (Ord A)) _ _
  { assume hOrdA;
    have heq : π (Collect (Union (RepFun A f)) (λ _, Ord A) = Union (RepFun A f))
      { refine equality_iffI (Collect (Union (RepFun A f)) (λ _, Ord A))
          (Union (RepFun A f)) _;
        assume x;
        refine ∧ᵢ _ _
        { assume hx; refine CollectD1 x (Union (RepFun A f)) (λ _, Ord A) hx }
        { assume hx;
          refine CollectI x (Union (RepFun A f)) (λ _, Ord A) hx hOrdA } };
    rewrite heq;
    refine Card_UN A f hf }
  { assume hnOrd;
    have heq : π (Collect (Union (RepFun A f)) (λ _, Ord A) = empty)
      { refine equals0I (Collect (Union (RepFun A f)) (λ _, Ord A)) _;
        assume y hy;
        refine hnOrd (CollectD2 y (Union (RepFun A f)) (λ _, Ord A) hy) };
    rewrite heq;
    refine Card_0 }
end;

opaque symbol in_Card_imp_lesspoll (K b : τ ι) :
  π (Card K) → π (b ∈ K) → π (lesspoll b K) ≔
begin
  assume K b hCK hb;
  refine lt_Card_imp_lesspoll K b hCK (ltI b K hb (Card_is_Ord K hCK))
end;

// ===========================================================================
// Cardinal addition
// ===========================================================================

// Cardinal addition is commutative
opaque symbol sum_commute_eqpoll (A B : τ ι) :
  π (eqpoll (sum A B) (sum B A)) ≔
begin
  assume A B;
  rewrite eqpoll_def;
  refine ∃ᵢ (Lambda (sum A B) (λ z, case_sum Inr Inl z)) _;
  refine lam_bijective (sum A B) (sum B A)
    (λ z, case_sum Inr Inl z) (λ z, case_sum Inr Inl z) _ _ _ _
  { assume z hz;
    refine sumE z A B _ hz _ _
    { assume x hx heq; rewrite heq; rewrite case_Inl; refine InrI x B A hx }
    { assume y hy heq; rewrite heq; rewrite case_Inr; refine InlI y B A hy } }
  { assume z hz;
    refine sumE z B A _ hz _ _
    { assume x hx heq; rewrite heq; rewrite case_Inl; refine InrI x A B hx }
    { assume y hy heq; rewrite heq; rewrite case_Inr; refine InlI y A B hy } }
  { assume z hz;
    refine sumE z A B _ hz _ _
    { assume x hx heq; rewrite heq; rewrite case_Inl; rewrite case_Inr; reflexivity }
    { assume y hy heq; rewrite heq; rewrite case_Inr; rewrite case_Inl; reflexivity } }
  { assume z hz;
    refine sumE z B A _ hz _ _
    { assume x hx heq; rewrite heq; rewrite case_Inl; rewrite case_Inr; reflexivity }
    { assume y hy heq; rewrite heq; rewrite case_Inr; rewrite case_Inl; reflexivity } }
end;

opaque symbol cadd_commute (i j : τ ι) :
  π (cadd i j = cadd j i) ≔
begin
  assume i j;
  rewrite cadd_def; rewrite cadd_def;
  refine cardinal_cong (sum i j) (sum j i) (sum_commute_eqpoll i j)
end;

// Cardinal addition is associative
opaque symbol sum_assoc_eqpoll (A B C : τ ι) :
  π (eqpoll (sum (sum A B) C) (sum A (sum B C))) ≔
begin
  assume A B C;
  rewrite eqpoll_def;
  refine ∃ᵢ _ (sum_assoc_bij A B C)
end;

// Unconditional version requires AC
opaque symbol well_ord_cadd_assoc (i ri j rj k rk : τ ι) :
  π (well_ord i ri) → π (well_ord j rj) → π (well_ord k rk) →
  π (cadd (cadd i j) k = cadd i (cadd j k)) ≔
begin
  assume i ri j rj k rk hi hj hk;
  rewrite cadd_def; rewrite cadd_def; rewrite cadd_def; rewrite cadd_def;
  have hwij : π (well_ord (sum i j) (radd i ri j rj))
    { refine well_ord_radd i ri j rj hi hj };
  have hwjk : π (well_ord (sum j k) (radd j rj k rk))
    { refine well_ord_radd j rj k rk hj hk };
  have e1 : π (eqpoll (sum (cardinal (sum i j)) k) (sum (sum i j) k))
    { refine sum_eqpoll_cong (cardinal (sum i j)) (sum i j) k k
        (well_ord_cardinal_eqpoll (sum i j) (radd i ri j rj) hwij) (eqpoll_refl k) };
  have e2 : π (eqpoll (sum (sum i j) k) (sum i (sum j k)))
    { refine sum_assoc_eqpoll i j k };
  have e3 : π (eqpoll (sum i (sum j k)) (sum i (cardinal (sum j k))))
    { refine sum_eqpoll_cong i i (sum j k) (cardinal (sum j k)) (eqpoll_refl i)
        (eqpoll_sym (cardinal (sum j k)) (sum j k)
          (well_ord_cardinal_eqpoll (sum j k) (radd j rj k rk) hwjk)) };
  refine cardinal_cong (sum (cardinal (sum i j)) k) (sum i (cardinal (sum j k)))
    (eqpoll_trans (sum (cardinal (sum i j)) k) (sum i (sum j k))
       (sum i (cardinal (sum j k)))
       (eqpoll_trans (sum (cardinal (sum i j)) k) (sum (sum i j) k)
          (sum i (sum j k)) e1 e2) e3)
end;

// 0 is the identity for addition
opaque symbol sum_0_eqpoll (A : τ ι) :
  π (eqpoll (sum empty A) A) ≔
begin
  assume A;
  rewrite eqpoll_def;
  refine ∃ᵢ _ (bij_0_sum A)
end;

opaque symbol cadd_0 (K : τ ι) :
  π (Card K) → π (cadd empty K = K) ≔
begin
  assume K hK;
  rewrite cadd_def;
  have h1 : π (cardinal (sum empty K) = cardinal K)
    { refine cardinal_cong (sum empty K) K (sum_0_eqpoll K) };
  rewrite h1;
  refine Card_cardinal_eq K hK
end;

// Addition by another cardinal
opaque symbol sum_lepoll_self (A B : τ ι) :
  π (lepoll A (sum A B)) ≔
begin
  assume A B;
  rewrite lepoll_def;
  refine ∃ᵢ (Lambda A (λ x, Inl x)) _;
  refine lam_injective A (sum A B) (λ x, Inl x) (λ z, case_sum (λ w, w) (λ w, w) z) _ _
  { assume x hx; refine InlI x A B hx }
  { assume x hx; rewrite case_Inl; reflexivity }
end;

// Could probably weaken the premises to well_ord(K,r), or removing using AC
opaque symbol cadd_le_self (K L : τ ι) :
  π (Card K) → π (Ord L) → π (le K (cadd K L)) ≔
begin
  assume K L hK hOL;
  rewrite cadd_def;
  have hOK : π (Ord K) { refine Card_is_Ord K hK };
  have h1 : π (le K (cardinal K)) { refine Card_cardinal_le K hK };
  have hwo : π (well_ord (sum K L) (radd K (Memrel K) L (Memrel L)))
    { refine well_ord_radd K (Memrel K) L (Memrel L)
        (well_ord_Memrel K hOK) (well_ord_Memrel L hOL) };
  have h2 : π (le (cardinal K) (cardinal (sum K L)))
    { refine well_ord_lepoll_imp_cardinal_le (sum K L)
        (radd K (Memrel K) L (Memrel L)) K hwo (sum_lepoll_self K L) };
  refine le_trans K (cardinal K) (cardinal (sum K L)) h1 h2
end;

// Monotonicity of addition
opaque symbol sum_lepoll_mono (A C B D : τ ι) :
  π (lepoll A C) → π (lepoll B D) → π (lepoll (sum A B) (sum C D)) ≔
begin
  assume A C B D hAC hBD;
  have hAC' : π (`∃ (f : τ ι), f ∈ inj A C)
    { refine ind_eq (eq_sym (lepoll_def A C)) (λ p, p) hAC };
  have hBD' : π (`∃ (f : τ ι), f ∈ inj B D)
    { refine ind_eq (eq_sym (lepoll_def B D)) (λ p, p) hBD };
  refine ∃ₑ hAC' _; assume f hf;
  refine ∃ₑ hBD' _; assume g hg;
  rewrite lepoll_def;
  refine ∃ᵢ (Lambda (sum A B)
    (λ z, case_sum (λ w, Inl (fapply f w)) (λ y, Inr (fapply g y)) z)) _;
  refine lam_injective (sum A B) (sum C D)
    (λ z, case_sum (λ w, Inl (fapply f w)) (λ y, Inr (fapply g y)) z)
    (λ z, case_sum (λ w, Inl (fapply (converse f) w))
                   (λ y, Inr (fapply (converse g) y)) z) _ _
  { assume z hz;
    refine sumE z A B _ hz _ _
    { assume x hx heq; rewrite heq; rewrite case_Inl; simplify rule off;
      refine InlI (fapply f x) C D
        (fapply_type f x A (λ _, C) (inj_is_fun f A C hf) hx) }
    { assume y hy heq; rewrite heq; rewrite case_Inr; simplify rule off;
      refine InrI (fapply g y) C D
        (fapply_type g y B (λ _, D) (inj_is_fun g B D hg) hy) } }
  { assume z hz;
    refine sumE z A B _ hz _ _
    { assume x hx heq; rewrite heq; rewrite case_Inl; simplify rule off;
      rewrite case_Inl; simplify rule off;
      rewrite (left_inverse f A C x hf hx); reflexivity }
    { assume y hy heq; rewrite heq; rewrite case_Inr; simplify rule off;
      rewrite case_Inr; simplify rule off;
      rewrite (left_inverse g B D y hg hy); reflexivity } }
end;

opaque symbol cadd_le_mono (K' K L' L : τ ι) :
  π (le K' K) → π (le L' L) → π (le (cadd K' L') (cadd K L)) ≔
begin
  assume K' K L' L hK hL;
  have hOK : π (Ord K) { refine le_Ord2 K' K hK };
  have hOL : π (Ord L) { refine le_Ord2 L' L hL };
  rewrite cadd_def; rewrite cadd_def;
  refine well_ord_lepoll_imp_cardinal_le (sum K L)
    (radd K (Memrel K) L (Memrel L)) (sum K' L')
    (well_ord_radd K (Memrel K) L (Memrel L)
       (well_ord_Memrel K hOK) (well_ord_Memrel L hOL))
    (sum_lepoll_mono K' K L' L (le_imp_lepoll K' K hK) (le_imp_lepoll L' L hL))
end;

// Addition of finite cardinals is "ordinary" addition
opaque symbol sum_succ_eqpoll (A B : τ ι) :
  π (eqpoll (sum (succ A) B) (succ (sum A B))) ≔
begin
  assume A B;
  rewrite eqpoll_def;
  refine ∃ᵢ (Lambda (sum (succ A) B) (λ z, If (z = Inl A) (sum A B) z)) _;
  refine lam_bijective (sum (succ A) B) (succ (sum A B))
    (λ z, If (z = Inl A) (sum A B) z) (λ w, If (w = sum A B) (Inl A) w) _ _ _ _
  { assume z hz;
    refine sumE z (succ A) B _ hz _ _
    { assume x hx heq;
      refine ∨ₑ (∧ₑ₁ (succ_iff x A) hx) _ _
      { assume hxA;
        have hzIA : π (z = Inl A) { rewrite heq; rewrite hxA; reflexivity };
        rewrite (If_P (z = Inl A) (sum A B) z hzIA);
        refine succI1 (sum A B) }
      { assume hxinA;
        have hne : π (¬ (z = Inl A))
          { assume hzeq;
            have hxeqA : π (x = A)
              { refine Inl_inject x A (eq_trans (eq_sym heq) hzeq) };
            refine mem_irrefl A (ind_eq (eq_sym hxeqA) (λ w, w ∈ A) hxinA) };
        rewrite (If_not_P (z = Inl A) (sum A B) z hne);
        rewrite heq;
        refine succI2 (Inl x) (sum A B) (InlI x A B hxinA) } }
    { assume y hy heq;
      have hne : π (¬ (z = Inl A))
        { assume hzeq; refine Inr_neq_Inl A y ⊥ (eq_trans (eq_sym heq) hzeq) };
      rewrite (If_not_P (z = Inl A) (sum A B) z hne);
      rewrite heq;
      refine succI2 (Inr y) (sum A B) (InrI y A B hy) } }
  { assume w hw;
    refine ∨ₑ (∧ₑ₁ (succ_iff w (sum A B)) hw) _ _
    { assume hweq;
      rewrite (If_P (w = sum A B) (Inl A) w hweq);
      refine InlI A (succ A) B (succI1 A) }
    { assume hwin;
      have hne : π (¬ (w = sum A B))
        { assume hweq;
          refine mem_irrefl (sum A B)
            (ind_eq (eq_sym hweq) (λ v, v ∈ sum A B) hwin) };
      rewrite (If_not_P (w = sum A B) (Inl A) w hne);
      refine sumE w A B _ hwin _ _
      { assume x hx heq; rewrite heq; refine InlI x (succ A) B (succI2 x A hx) }
      { assume y hy heq; rewrite heq; refine InrI y (succ A) B hy } } }
  { assume z hz;
    refine sumE z (succ A) B _ hz _ _
    { assume x hx heq;
      refine ∨ₑ (∧ₑ₁ (succ_iff x A) hx) _ _
      { assume hxA;
        have hzIA : π (z = Inl A) { rewrite heq; rewrite hxA; reflexivity };
        rewrite (If_P (z = Inl A) (sum A B) z hzIA);
        rewrite (If_P (sum A B = sum A B) (Inl A) (sum A B) (eq_refl (sum A B)));
        rewrite hzIA; reflexivity }
      { assume hxinA;
        have hne : π (¬ (z = Inl A))
          { assume hzeq;
            have hxeqA : π (x = A)
              { refine Inl_inject x A (eq_trans (eq_sym heq) hzeq) };
            refine mem_irrefl A (ind_eq (eq_sym hxeqA) (λ w, w ∈ A) hxinA) };
        rewrite (If_not_P (z = Inl A) (sum A B) z hne);
        have hzin : π (z ∈ sum A B) { rewrite heq; refine InlI x A B hxinA };
        have hne2 : π (¬ (z = sum A B))
          { assume hzeq;
            refine mem_irrefl (sum A B)
              (ind_eq (eq_sym hzeq) (λ v, v ∈ sum A B) hzin) };
        rewrite (If_not_P (z = sum A B) (Inl A) z hne2);
        reflexivity } }
    { assume y hy heq;
      have hne : π (¬ (z = Inl A))
        { assume hzeq; refine Inr_neq_Inl A y ⊥ (eq_trans (eq_sym heq) hzeq) };
      rewrite (If_not_P (z = Inl A) (sum A B) z hne);
      have hzin : π (z ∈ sum A B) { rewrite heq; refine InrI y A B hy };
      have hne2 : π (¬ (z = sum A B))
        { assume hzeq;
          refine mem_irrefl (sum A B)
            (ind_eq (eq_sym hzeq) (λ v, v ∈ sum A B) hzin) };
      rewrite (If_not_P (z = sum A B) (Inl A) z hne2);
      reflexivity } }
  { assume w hw;
    refine ∨ₑ (∧ₑ₁ (succ_iff w (sum A B)) hw) _ _
    { assume hweq;
      rewrite (If_P (w = sum A B) (Inl A) w hweq);
      rewrite (If_P (Inl A = Inl A) (sum A B) (Inl A) (eq_refl (Inl A)));
      rewrite hweq; reflexivity }
    { assume hwin;
      have hne : π (¬ (w = sum A B))
        { assume hweq;
          refine mem_irrefl (sum A B)
            (ind_eq (eq_sym hweq) (λ v, v ∈ sum A B) hwin) };
      rewrite (If_not_P (w = sum A B) (Inl A) w hne);
      have hne2 : π (¬ (w = Inl A))
        { assume hweq;
          have hIA : π (Inl A ∈ sum A B)
            { refine ind_eq (eq_sym hweq) (λ v, v ∈ sum A B) hwin };
          refine mem_irrefl A (∧ₑ₁ (Inl_in_sum_iff A A B) hIA) };
      rewrite (If_not_P (w = Inl A) (sum A B) w hne2);
      reflexivity } }
end;

// Pulling the succ(...) outside the |...| requires m, n ∈ nat
// Unconditional version requires AC
opaque symbol cadd_succ_lemma (m n : τ ι) :
  π (Ord m) → π (Ord n) → π (cadd (succ m) n = cardinal (succ (cadd m n))) ≔
begin
  assume m n hOm hOn;
  rewrite cadd_def; rewrite cadd_def;
  have hwo : π (well_ord (sum m n) (radd m (Memrel m) n (Memrel n)))
    { refine well_ord_radd m (Memrel m) n (Memrel n)
        (well_ord_Memrel m hOm) (well_ord_Memrel n hOn) };
  have e1 : π (eqpoll (sum (succ m) n) (succ (sum m n)))
    { refine sum_succ_eqpoll m n };
  have e2 : π (eqpoll (sum m n) (cardinal (sum m n)))
    { refine eqpoll_sym (cardinal (sum m n)) (sum m n)
        (well_ord_cardinal_eqpoll (sum m n) (radd m (Memrel m) n (Memrel n)) hwo) };
  have e3 : π (eqpoll (succ (sum m n)) (succ (cardinal (sum m n))))
    { refine succ_eqpoll_cong (sum m n) (cardinal (sum m n)) e2 };
  refine cardinal_cong (sum (succ m) n) (succ (cardinal (sum m n)))
    (eqpoll_trans (sum (succ m) n) (succ (sum m n)) (succ (cardinal (sum m n))) e1 e3)
end;

opaque symbol nat_cadd_eq_add (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (cadd m n = add m n) ≔
begin
  assume m n hm hn;
  refine nat_induct (λ w, cadd w n = add w n) _ _ m hm
  { simplify rule off;
    have h0 : π (cadd empty n = n) { refine cadd_0 n (nat_into_Card n hn) };
    rewrite h0;
    refine eq_sym (add_0 n hn) }
  { assume k hk IH;
    have h1 : π (cadd (succ k) n = cardinal (succ (cadd k n)))
      { refine cadd_succ_lemma k n (nat_into_Ord k hk) (nat_into_Ord n hn) };
    rewrite h1; rewrite IH;
    rewrite add_succ;
    refine Card_cardinal_eq (succ (add k n))
      (nat_into_Card (succ (add k n)) (succ_in_omega (add k n) (add_type k n))) }
end;

// ===========================================================================
// Cardinal multiplication
// ===========================================================================

// Cardinal multiplication is commutative
opaque symbol prod_commute_eqpoll (A B : τ ι) :
  π (eqpoll (Sigma A (λ _, B)) (Sigma B (λ _, A))) ≔
begin
  assume A B;
  rewrite eqpoll_def;
  refine ∃ᵢ (Lambda (Sigma A (λ _, B)) (λ p, Pair (snd p) (fst p))) _;
  refine lam_bijective (Sigma A (λ _, B)) (Sigma B (λ _, A))
    (λ p, Pair (snd p) (fst p)) (λ p, Pair (snd p) (fst p)) _ _ _ _
  { assume p hp;
    refine SigmaI (snd p) (fst p) B (λ _, A)
      (SigmaD2 p A (λ _, B) hp) (SigmaD1 p A (λ _, B) hp) }
  { assume p hp;
    refine SigmaI (snd p) (fst p) A (λ _, B)
      (SigmaD2 p B (λ _, A) hp) (SigmaD1 p B (λ _, A) hp) }
  { assume p hp;
    rewrite fst_conv; rewrite snd_conv;
    refine Pair_fst_snd p A (λ _, B) hp }
  { assume p hp;
    rewrite fst_conv; rewrite snd_conv;
    refine Pair_fst_snd p B (λ _, A) hp }
end;

opaque symbol cmult_commute (i j : τ ι) :
  π (cmult i j = cmult j i) ≔
begin
  assume i j;
  rewrite cmult_def; rewrite cmult_def;
  refine cardinal_cong (Sigma i (λ _, j)) (Sigma j (λ _, i)) (prod_commute_eqpoll i j)
end;

// Cardinal multiplication is associative
opaque symbol prod_assoc_eqpoll (A B C : τ ι) :
  π (eqpoll (Sigma (Sigma A (λ _, B)) (λ _, C)) (Sigma A (λ _, Sigma B (λ _, C)))) ≔
begin
  assume A B C;
  rewrite eqpoll_def;
  refine ∃ᵢ _ (prod_assoc_bij A B C)
end;

// Unconditional version requires AC
opaque symbol well_ord_cmult_assoc (i ri j rj k rk : τ ι) :
  π (well_ord i ri) → π (well_ord j rj) → π (well_ord k rk) →
  π (cmult (cmult i j) k = cmult i (cmult j k)) ≔
begin
  assume i ri j rj k rk hi hj hk;
  rewrite cmult_def; rewrite cmult_def; rewrite cmult_def; rewrite cmult_def;
  have hwij : π (well_ord (Sigma i (λ _, j)) (rmult i ri j rj))
    { refine well_ord_rmult i ri j rj hi hj };
  have hwjk : π (well_ord (Sigma j (λ _, k)) (rmult j rj k rk))
    { refine well_ord_rmult j rj k rk hj hk };
  have e1 : π (eqpoll (Sigma (cardinal (Sigma i (λ _, j))) (λ _, k))
                      (Sigma (Sigma i (λ _, j)) (λ _, k)))
    { refine prod_eqpoll_cong (cardinal (Sigma i (λ _, j))) (Sigma i (λ _, j)) k k
        (well_ord_cardinal_eqpoll (Sigma i (λ _, j)) (rmult i ri j rj) hwij)
        (eqpoll_refl k) };
  have e2 : π (eqpoll (Sigma (Sigma i (λ _, j)) (λ _, k))
                      (Sigma i (λ _, Sigma j (λ _, k))))
    { refine prod_assoc_eqpoll i j k };
  have e3 : π (eqpoll (Sigma i (λ _, Sigma j (λ _, k)))
                      (Sigma i (λ _, cardinal (Sigma j (λ _, k)))))
    { refine prod_eqpoll_cong i i (Sigma j (λ _, k)) (cardinal (Sigma j (λ _, k)))
        (eqpoll_refl i)
        (eqpoll_sym (cardinal (Sigma j (λ _, k))) (Sigma j (λ _, k))
          (well_ord_cardinal_eqpoll (Sigma j (λ _, k)) (rmult j rj k rk) hwjk)) };
  refine cardinal_cong (Sigma (cardinal (Sigma i (λ _, j))) (λ _, k))
    (Sigma i (λ _, cardinal (Sigma j (λ _, k))))
    (eqpoll_trans (Sigma (cardinal (Sigma i (λ _, j))) (λ _, k))
       (Sigma i (λ _, Sigma j (λ _, k)))
       (Sigma i (λ _, cardinal (Sigma j (λ _, k))))
       (eqpoll_trans (Sigma (cardinal (Sigma i (λ _, j))) (λ _, k))
          (Sigma (Sigma i (λ _, j)) (λ _, k))
          (Sigma i (λ _, Sigma j (λ _, k))) e1 e2) e3)
end;

// Cardinal multiplication distributes over addition
opaque symbol sum_prod_distrib_eqpoll (A B C : τ ι) :
  π (eqpoll (Sigma (sum A B) (λ _, C)) (sum (Sigma A (λ _, C)) (Sigma B (λ _, C)))) ≔
begin
  assume A B C;
  rewrite eqpoll_def;
  refine ∃ᵢ _ (sum_prod_distrib_bij A B C)
end;

opaque symbol well_ord_cadd_cmult_distrib (i ri j rj k rk : τ ι) :
  π (well_ord i ri) → π (well_ord j rj) → π (well_ord k rk) →
  π (cmult (cadd i j) k = cadd (cmult i k) (cmult j k)) ≔
begin
  assume i ri j rj k rk hi hj hk;
  rewrite cadd_def; rewrite cmult_def; rewrite cmult_def; rewrite cmult_def;
  rewrite cadd_def;
  have hwij : π (well_ord (sum i j) (radd i ri j rj))
    { refine well_ord_radd i ri j rj hi hj };
  have hwik : π (well_ord (Sigma i (λ _, k)) (rmult i ri k rk))
    { refine well_ord_rmult i ri k rk hi hk };
  have hwjk : π (well_ord (Sigma j (λ _, k)) (rmult j rj k rk))
    { refine well_ord_rmult j rj k rk hj hk };
  have e1 : π (eqpoll (Sigma (cardinal (sum i j)) (λ _, k))
                      (Sigma (sum i j) (λ _, k)))
    { refine prod_eqpoll_cong (cardinal (sum i j)) (sum i j) k k
        (well_ord_cardinal_eqpoll (sum i j) (radd i ri j rj) hwij)
        (eqpoll_refl k) };
  have e2 : π (eqpoll (Sigma (sum i j) (λ _, k))
                      (sum (Sigma i (λ _, k)) (Sigma j (λ _, k))))
    { refine sum_prod_distrib_eqpoll i j k };
  have e3 : π (eqpoll (sum (Sigma i (λ _, k)) (Sigma j (λ _, k)))
                      (sum (cardinal (Sigma i (λ _, k))) (cardinal (Sigma j (λ _, k)))))
    { refine sum_eqpoll_cong (Sigma i (λ _, k)) (cardinal (Sigma i (λ _, k)))
        (Sigma j (λ _, k)) (cardinal (Sigma j (λ _, k)))
        (eqpoll_sym (cardinal (Sigma i (λ _, k))) (Sigma i (λ _, k))
          (well_ord_cardinal_eqpoll (Sigma i (λ _, k)) (rmult i ri k rk) hwik))
        (eqpoll_sym (cardinal (Sigma j (λ _, k))) (Sigma j (λ _, k))
          (well_ord_cardinal_eqpoll (Sigma j (λ _, k)) (rmult j rj k rk) hwjk)) };
  refine cardinal_cong (Sigma (cardinal (sum i j)) (λ _, k))
    (sum (cardinal (Sigma i (λ _, k))) (cardinal (Sigma j (λ _, k))))
    (eqpoll_trans (Sigma (cardinal (sum i j)) (λ _, k))
       (sum (Sigma i (λ _, k)) (Sigma j (λ _, k)))
       (sum (cardinal (Sigma i (λ _, k))) (cardinal (Sigma j (λ _, k))))
       (eqpoll_trans (Sigma (cardinal (sum i j)) (λ _, k))
          (Sigma (sum i j) (λ _, k))
          (sum (Sigma i (λ _, k)) (Sigma j (λ _, k))) e1 e2) e3)
end;

// Multiplication by 0 yields 0
opaque symbol prod_0_eqpoll (A : τ ι) :
  π (eqpoll (Sigma empty (λ _, A)) empty) ≔
begin
  assume A;
  rewrite eqpoll_def;
  refine ∃ᵢ (Lambda (Sigma empty (λ _, A)) (λ z, z)) _;
  refine lam_bijective (Sigma empty (λ _, A)) empty (λ z, z) (λ z, z) _ _ _ _
  { assume z hz; refine ⊥ₑ (emptyE (fst z) (SigmaD1 z empty (λ _, A) hz)) }
  { assume z hz; refine ⊥ₑ (emptyE z hz) }
  { assume z hz; reflexivity }
  { assume z hz; refine ⊥ₑ (emptyE z hz) }
end;

opaque symbol cmult_0 (i : τ ι) :
  π (cmult empty i = empty) ≔
begin
  assume i;
  rewrite cmult_def;
  have h1 : π (cardinal (Sigma empty (λ _, i)) = cardinal empty)
    { refine cardinal_cong (Sigma empty (λ _, i)) empty (prod_0_eqpoll i) };
  rewrite h1;
  refine cardinal_0
end;

// 1 is the identity for multiplication
opaque symbol prod_singleton_eqpoll (x A : τ ι) :
  π (eqpoll (Sigma (singleton x) (λ _, A)) A) ≔
begin
  assume x A;
  refine eqpoll_sym A (Sigma (singleton x) (λ _, A)) _;
  rewrite eqpoll_def;
  refine ∃ᵢ (Lambda A (λ z, Pair x z)) (singleton_prod_bij x A)
end;

opaque symbol cmult_1 (K : τ ι) :
  π (Card K) → π (cmult (succ empty) K = K) ≔
begin
  assume K hK;
  rewrite cmult_def;
  have hse : π (succ empty = singleton empty) { rewrite succ_def; reflexivity };
  rewrite hse;
  have h1 : π (cardinal (Sigma (singleton empty) (λ _, K)) = cardinal K)
    { refine cardinal_cong (Sigma (singleton empty) (λ _, K)) K
        (prod_singleton_eqpoll empty K) };
  rewrite h1;
  refine Card_cardinal_eq K hK
end;

// ===========================================================================
// Some inequalities for multiplication
// ===========================================================================

opaque symbol prod_square_lepoll (A : τ ι) :
  π (lepoll A (Sigma A (λ _, A))) ≔
begin
  assume A;
  rewrite lepoll_def;
  refine ∃ᵢ (Lambda A (λ x, Pair x x)) _;
  refine lam_injective A (Sigma A (λ _, A)) (λ x, Pair x x) (λ p, fst p) _ _
  { assume x hx; refine SigmaI x x A (λ _, A) hx hx }
  { assume x hx; refine fst_conv x x }
end;

// Could probably weaken the premise to well_ord(K,r), or remove using AC
opaque symbol cmult_square_le (K : τ ι) :
  π (Card K) → π (le K (cmult K K)) ≔
begin
  assume K hK;
  have hOK : π (Ord K) { refine Card_is_Ord K hK };
  rewrite cmult_def;
  have hwo : π (well_ord (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K)))
    { refine well_ord_rmult K (Memrel K) K (Memrel K)
        (well_ord_Memrel K hOK) (well_ord_Memrel K hOK) };
  have h2 : π (le (cardinal K) (cardinal (Sigma K (λ _, K))))
    { refine well_ord_lepoll_imp_cardinal_le (Sigma K (λ _, K))
        (rmult K (Memrel K) K (Memrel K)) K hwo (prod_square_lepoll K) };
  have h1 : π (cardinal K = K) { refine Card_cardinal_eq K hK };
  refine ind_eq (eq_sym h1) (λ w, le w (cardinal (Sigma K (λ _, K)))) h2
end;

// Multiplication by a non-zero cardinal
opaque symbol prod_lepoll_self (A B b : τ ι) :
  π (b ∈ B) → π (lepoll A (Sigma A (λ _, B))) ≔
begin
  assume A B b hb;
  rewrite lepoll_def;
  refine ∃ᵢ (Lambda A (λ x, Pair x b)) _;
  refine lam_injective A (Sigma A (λ _, B)) (λ x, Pair x b) (λ p, fst p) _ _
  { assume x hx; refine SigmaI x b A (λ _, B) hx hb }
  { assume x hx; refine fst_conv x b }
end;

// Could probably weaken the premises to well_ord(K,r), or removing using AC
opaque symbol cmult_le_self (K L : τ ι) :
  π (Card K) → π (Ord L) → π (lt empty L) → π (le K (cmult K L)) ≔
begin
  assume K L hK hOL h0L;
  rewrite cmult_def;
  have hOK : π (Ord K) { refine Card_is_Ord K hK };
  have hwo : π (well_ord (Sigma K (λ _, L)) (rmult K (Memrel K) L (Memrel L)))
    { refine well_ord_rmult K (Memrel K) L (Memrel L)
        (well_ord_Memrel K hOK) (well_ord_Memrel L hOL) };
  have hlep : π (lepoll K (Sigma K (λ _, L)))
    { refine prod_lepoll_self K L empty (ltD empty L h0L) };
  have h2 : π (le (cardinal K) (cardinal (Sigma K (λ _, L))))
    { refine well_ord_lepoll_imp_cardinal_le (Sigma K (λ _, L))
        (rmult K (Memrel K) L (Memrel L)) K hwo hlep };
  have h1 : π (le K (cardinal K)) { refine Card_cardinal_le K hK };
  refine le_trans K (cardinal K) (cardinal (Sigma K (λ _, L))) h1 h2
end;

// Monotonicity of multiplication
opaque symbol prod_lepoll_mono (A C B D : τ ι) :
  π (lepoll A C) → π (lepoll B D) → π (lepoll (Sigma A (λ _, B)) (Sigma C (λ _, D))) ≔
begin
  assume A C B D hAC hBD;
  have hAC' : π (`∃ (f : τ ι), f ∈ inj A C)
    { refine ind_eq (eq_sym (lepoll_def A C)) (λ p, p) hAC };
  have hBD' : π (`∃ (f : τ ι), f ∈ inj B D)
    { refine ind_eq (eq_sym (lepoll_def B D)) (λ p, p) hBD };
  refine ∃ₑ hAC' _; assume f hf;
  refine ∃ₑ hBD' _; assume g hg;
  rewrite lepoll_def;
  refine ∃ᵢ (Lambda (Sigma A (λ _, B))
    (λ p, Pair (fapply f (fst p)) (fapply g (snd p)))) _;
  refine lam_injective (Sigma A (λ _, B)) (Sigma C (λ _, D))
    (λ p, Pair (fapply f (fst p)) (fapply g (snd p)))
    (λ p, Pair (fapply (converse f) (fst p)) (fapply (converse g) (snd p))) _ _
  { assume p hp;
    refine SigmaI (fapply f (fst p)) (fapply g (snd p)) C (λ _, D)
      (fapply_type f (fst p) A (λ _, C) (inj_is_fun f A C hf)
         (SigmaD1 p A (λ _, B) hp))
      (fapply_type g (snd p) B (λ _, D) (inj_is_fun g B D hg)
         (SigmaD2 p A (λ _, B) hp)) }
  { assume p hp;
    rewrite fst_conv; rewrite snd_conv;
    rewrite (left_inverse f A C (fst p) hf (SigmaD1 p A (λ _, B) hp));
    rewrite (left_inverse g B D (snd p) hg (SigmaD2 p A (λ _, B) hp));
    refine Pair_fst_snd p A (λ _, B) hp }
end;

opaque symbol cmult_le_mono (K' K L' L : τ ι) :
  π (le K' K) → π (le L' L) → π (le (cmult K' L') (cmult K L)) ≔
begin
  assume K' K L' L hK hL;
  have hOK : π (Ord K) { refine le_Ord2 K' K hK };
  have hOL : π (Ord L) { refine le_Ord2 L' L hL };
  rewrite cmult_def; rewrite cmult_def;
  refine well_ord_lepoll_imp_cardinal_le (Sigma K (λ _, L))
    (rmult K (Memrel K) L (Memrel L)) (Sigma K' (λ _, L'))
    (well_ord_rmult K (Memrel K) L (Memrel L)
       (well_ord_Memrel K hOK) (well_ord_Memrel L hOL))
    (prod_lepoll_mono K' K L' L (le_imp_lepoll K' K hK) (le_imp_lepoll L' L hL))
end;

// ===========================================================================
// Multiplication of finite cardinals is "ordinary" multiplication
// ===========================================================================

opaque symbol prod_succ_eqpoll (A B : τ ι) :
  π (eqpoll (Sigma (succ A) (λ _, B)) (sum B (Sigma A (λ _, B)))) ≔
begin
  assume A B;
  rewrite eqpoll_def;
  refine ∃ᵢ (Lambda (Sigma (succ A) (λ _, B))
    (λ p, If (fst p = A) (Inl (snd p)) (Inr p))) _;
  refine lam_bijective (Sigma (succ A) (λ _, B)) (sum B (Sigma A (λ _, B)))
    (λ p, If (fst p = A) (Inl (snd p)) (Inr p))
    (λ w, case_sum (λ y, Pair A y) (λ z, z) w) _ _ _ _
  { assume p hp;
    have hfp : π (fst p ∈ succ A) { refine SigmaD1 p (succ A) (λ _, B) hp };
    have hsp : π (snd p ∈ B) { refine SigmaD2 p (succ A) (λ _, B) hp };
    refine ∨ₑ (∧ₑ₁ (succ_iff (fst p) A) hfp) _ _
    { assume hfA;
      rewrite (If_P (fst p = A) (Inl (snd p)) (Inr p) hfA);
      refine InlI (snd p) B (Sigma A (λ _, B)) hsp }
    { assume hfinA;
      have hne : π (¬ (fst p = A))
        { assume hfA;
          refine mem_irrefl A (ind_eq (eq_sym hfA) (λ w, w ∈ A) hfinA) };
      rewrite (If_not_P (fst p = A) (Inl (snd p)) (Inr p) hne);
      refine InrI p B (Sigma A (λ _, B))
        (ind_eq (eq_sym (Pair_fst_snd p (succ A) (λ _, B) hp))
           (λ w, w ∈ Sigma A (λ _, B))
           (SigmaI (fst p) (snd p) A (λ _, B) hfinA hsp)) } }
  { assume w hw;
    refine sumE w B (Sigma A (λ _, B)) _ hw _ _
    { assume y hy heq; rewrite heq; rewrite case_Inl; simplify rule off;
      refine SigmaI A y (succ A) (λ _, B) (succI1 A) hy }
    { assume q hq heq; rewrite heq; rewrite case_Inr; simplify rule off;
      refine ind_eq (eq_sym (Pair_fst_snd q A (λ _, B) hq))
        (λ v, v ∈ Sigma (succ A) (λ _, B))
        (SigmaI (fst q) (snd q) (succ A) (λ _, B)
           (succI2 (fst q) A (SigmaD1 q A (λ _, B) hq))
           (SigmaD2 q A (λ _, B) hq)) } }
  { assume p hp;
    have hfp : π (fst p ∈ succ A) { refine SigmaD1 p (succ A) (λ _, B) hp };
    have hsp : π (snd p ∈ B) { refine SigmaD2 p (succ A) (λ _, B) hp };
    refine ∨ₑ (∧ₑ₁ (succ_iff (fst p) A) hfp) _ _
    { assume hfA;
      rewrite (If_P (fst p = A) (Inl (snd p)) (Inr p) hfA);
      rewrite case_Inl; simplify rule off;
      rewrite left hfA;
      refine Pair_fst_snd p (succ A) (λ _, B) hp }
    { assume hfinA;
      have hne : π (¬ (fst p = A))
        { assume hfA;
          refine mem_irrefl A (ind_eq (eq_sym hfA) (λ w, w ∈ A) hfinA) };
      rewrite (If_not_P (fst p = A) (Inl (snd p)) (Inr p) hne);
      rewrite case_Inr; simplify rule off;
      reflexivity } }
  { assume w hw;
    refine sumE w B (Sigma A (λ _, B)) _ hw _ _
    { assume y hy heq; rewrite heq; rewrite case_Inl; simplify rule off;
      rewrite fst_conv; rewrite snd_conv;
      rewrite (If_P (A = A) (Inl y) (Inr (Pair A y)) (eq_refl A));
      reflexivity }
    { assume q hq heq; rewrite heq; rewrite case_Inr; simplify rule off;
      have hne : π (¬ (fst q = A))
        { assume hfA;
          refine mem_irrefl A
            (ind_eq (eq_sym hfA) (λ v, v ∈ A) (SigmaD1 q A (λ _, B) hq)) };
      rewrite (If_not_P (fst q = A) (Inl (snd q)) (Inr q) hne);
      reflexivity } }
end;

// Unconditional version requires AC
opaque symbol cmult_succ_lemma (m n : τ ι) :
  π (Ord m) → π (Ord n) → π (cmult (succ m) n = cadd n (cmult m n)) ≔
begin
  assume m n hOm hOn;
  rewrite cmult_def; rewrite cmult_def; rewrite cadd_def;
  have hwo : π (well_ord (Sigma m (λ _, n)) (rmult m (Memrel m) n (Memrel n)))
    { refine well_ord_rmult m (Memrel m) n (Memrel n)
        (well_ord_Memrel m hOm) (well_ord_Memrel n hOn) };
  have e1 : π (eqpoll (Sigma (succ m) (λ _, n)) (sum n (Sigma m (λ _, n))))
    { refine prod_succ_eqpoll m n };
  have e2 : π (eqpoll (sum n (Sigma m (λ _, n)))
                      (sum n (cardinal (Sigma m (λ _, n)))))
    { refine sum_eqpoll_cong n n (Sigma m (λ _, n)) (cardinal (Sigma m (λ _, n)))
        (eqpoll_refl n)
        (eqpoll_sym (cardinal (Sigma m (λ _, n))) (Sigma m (λ _, n))
          (well_ord_cardinal_eqpoll (Sigma m (λ _, n))
             (rmult m (Memrel m) n (Memrel n)) hwo)) };
  refine cardinal_cong (Sigma (succ m) (λ _, n))
    (sum n (cardinal (Sigma m (λ _, n))))
    (eqpoll_trans (Sigma (succ m) (λ _, n)) (sum n (Sigma m (λ _, n)))
       (sum n (cardinal (Sigma m (λ _, n)))) e1 e2)
end;

opaque symbol nat_cmult_eq_mult (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (cmult m n = mult m n) ≔
begin
  assume m n hm hn;
  refine nat_induct (λ w, cmult w n = mult w n) _ _ m hm
  { simplify rule off;
    rewrite cmult_0; rewrite mult_0; reflexivity }
  { assume k hk IH;
    have h1 : π (cmult (succ k) n = cadd n (cmult k n))
      { refine cmult_succ_lemma k n (nat_into_Ord k hk) (nat_into_Ord n hn) };
    rewrite h1; rewrite IH;
    rewrite mult_succ;
    refine nat_cadd_eq_add n (mult k n) hn (mult_type k n) }
end;

opaque symbol cmult_2 (n : τ ι) :
  π (Card n) → π (cmult (succ (succ empty)) n = cadd n n) ≔
begin
  assume n hn;
  have hOn : π (Ord n) { refine Card_is_Ord n hn };
  have h1 : π (cmult (succ (succ empty)) n = cadd n (cmult (succ empty) n))
    { refine cmult_succ_lemma (succ empty) n (Ord_succ empty Ord_0) hOn };
  have h2 : π (cmult (succ empty) n = cadd n (cmult empty n))
    { refine cmult_succ_lemma empty n Ord_0 hOn };
  rewrite h1; rewrite h2; rewrite cmult_0;
  have h4 : π (cadd n empty = cadd empty n) { refine cadd_commute n empty };
  rewrite h4;
  rewrite (cadd_0 n hn);
  reflexivity
end;

opaque symbol sum_lepoll_prod (C B : τ ι) :
  π (lepoll (succ (succ empty)) C) → π (lepoll (sum B B) (Sigma C (λ _, B))) ≔
begin
  assume C B h2C;
  have h2C' : π (`∃ (f : τ ι), f ∈ inj (succ (succ empty)) C)
    { refine ind_eq (eq_sym (lepoll_def (succ (succ empty)) C)) (λ p, p) h2C };
  refine ∃ₑ h2C' _; assume f hf;
  have hfun : π (f ∈ Pi (succ (succ empty)) (λ _, C))
    { refine inj_is_fun f (succ (succ empty)) C hf };
  have h0 : π (empty ∈ succ (succ empty))
    { refine succI2 empty (succ empty) (succI1 empty) };
  have h1m : π (succ empty ∈ succ (succ empty)) { refine succI1 (succ empty) };
  have hf0 : π (fapply f empty ∈ C)
    { refine fapply_type f empty (succ (succ empty)) (λ _, C) hfun h0 };
  have hf1 : π (fapply f (succ empty) ∈ C)
    { refine fapply_type f (succ empty) (succ (succ empty)) (λ _, C) hfun h1m };
  have hne1 : π (¬ (fapply f (succ empty) = fapply f empty))
    { assume heq;
      have h01 : π (succ empty = empty)
        { refine inj_apply_equality f (succ (succ empty)) C (succ empty) empty
            hf heq h1m h0 };
      refine succ_neq_0 empty h01 };
  rewrite lepoll_def;
  refine ∃ᵢ (Lambda (sum B B)
    (λ z, case_sum (λ y, Pair (fapply f empty) y)
                   (λ y, Pair (fapply f (succ empty)) y) z)) _;
  refine lam_injective (sum B B) (Sigma C (λ _, B))
    (λ z, case_sum (λ y, Pair (fapply f empty) y)
                   (λ y, Pair (fapply f (succ empty)) y) z)
    (λ p, If (fst p = fapply f empty) (Inl (snd p)) (Inr (snd p))) _ _
  { assume z hz;
    refine sumE z B B _ hz _ _
    { assume x hx heq; rewrite heq; rewrite case_Inl; simplify rule off;
      refine SigmaI (fapply f empty) x C (λ _, B) hf0 hx }
    { assume y hy heq; rewrite heq; rewrite case_Inr; simplify rule off;
      refine SigmaI (fapply f (succ empty)) y C (λ _, B) hf1 hy } }
  { assume z hz;
    refine sumE z B B _ hz _ _
    { assume x hx heq; rewrite heq; rewrite case_Inl; simplify rule off;
      rewrite fst_conv; rewrite snd_conv;
      rewrite (If_P (fapply f empty = fapply f empty) (Inl x) (Inr x)
        (eq_refl (fapply f empty)));
      reflexivity }
    { assume y hy heq; rewrite heq; rewrite case_Inr; simplify rule off;
      rewrite fst_conv; rewrite snd_conv;
      rewrite (If_not_P (fapply f (succ empty) = fapply f empty) (Inl y) (Inr y) hne1);
      reflexivity } }
end;

opaque symbol lepoll_imp_sum_lepoll_prod (A B : τ ι) :
  π (lepoll A B) → π (lepoll (succ (succ empty)) A) →
  π (lepoll (sum A B) (Sigma A (λ _, B))) ≔
begin
  assume A B hAB h2A;
  refine lepoll_trans (sum A B) (sum B B) (Sigma A (λ _, B))
    (sum_lepoll_mono A B B B hAB (lepoll_refl B))
    (sum_lepoll_prod A B h2A)
end;

// ===========================================================================
// Infinite Cardinals are Limit Ordinals
// ===========================================================================

// Port-internal helper (Isabelle func.apply_rangeI): f`a ∈ range(f).
private opaque symbol priv_apply_rangeI (f A : τ ι) (B : τ ι → τ ι) (a : τ ι) :
  π (f ∈ Pi A B) → π (a ∈ A) → π (fapply f a ∈ range f) ≔
begin
  assume f A B a hf ha;
  have hfun : π (function f) { refine Pi_function f A B hf };
  have hdom : π (domain f = A) { refine domain_of_fun f A B hf };
  have hadom : π (a ∈ domain f) { refine ind_eq hdom (λ w, a ∈ w) ha };
  refine rangeI a (fapply f a) f (apply_Pair f a hfun hadom)
end;

// This proof is modelled upon one assuming nat⊆A, with injection
// λz∈cons(u,A). if z=u then 0 else if z∈nat then succ(z) else z
// and inverse λy. if y∈nat then nat_case(u, λz.z, y) else y.
// If f∈inj(nat,A) then range(f) behaves like the natural numbers.
opaque symbol nat_cons_lepoll (A u : τ ι) :
  π (lepoll omega A) → π (lepoll (cons u A) A) ≔
begin
  assume A u hle;
  have hle' : π (`∃ (f : τ ι), f ∈ inj omega A)
    { refine ind_eq (eq_sym (lepoll_def omega A)) (λ p, p) hle };
  refine ∃ₑ hle' _; assume f hf;
  have hfun : π (f ∈ Pi omega (λ _, A)) { refine inj_is_fun f omega A hf };
  have hcfun : π (converse f ∈ Pi (range f) (λ _, omega))
    { refine inj_converse_fun f omega A hf };
  rewrite lepoll_def;
  refine ∃ᵢ (Lambda (cons u A)
    (λ z, If (z = u) (fapply f empty)
             (If (z ∈ range f) (fapply f (succ (fapply (converse f) z))) z))) _;
  refine lam_injective (cons u A) A
    (λ z, If (z = u) (fapply f empty)
             (If (z ∈ range f) (fapply f (succ (fapply (converse f) z))) z))
    (λ y, If (y ∈ range f)
             (nat_case u (λ w, fapply f w) (fapply (converse f) y)) y) _ _
  { assume z hz;
    refine ∨ₑ (em (z = u)) _ _
    { assume hzu;
      rewrite (If_P (z = u) (fapply f empty)
        (If (z ∈ range f) (fapply f (succ (fapply (converse f) z))) z) hzu);
      refine fapply_type f empty omega (λ _, A) hfun zero_in_omega }
    { assume hnzu;
      rewrite (If_not_P (z = u) (fapply f empty)
        (If (z ∈ range f) (fapply f (succ (fapply (converse f) z))) z) hnzu);
      refine ∨ₑ (em (z ∈ range f)) _ _
      { assume hzr;
        rewrite (If_P (z ∈ range f)
          (fapply f (succ (fapply (converse f) z))) z hzr);
        refine fapply_type f (succ (fapply (converse f) z)) omega (λ _, A) hfun
          (succ_in_omega (fapply (converse f) z)
             (fapply_type (converse f) z (range f) (λ _, omega) hcfun hzr)) }
      { assume hnzr;
        rewrite (If_not_P (z ∈ range f)
          (fapply f (succ (fapply (converse f) z))) z hnzr);
        refine ∨ₑ (∧ₑ₁ (cons_iff z u A) hz) _ _
        { assume hzu; refine ⊥ₑ (hnzu hzu) }
        { assume hzA; refine hzA } } } }
  { assume z hz;
    refine ∨ₑ (em (z = u)) _ _
    { assume hzu;
      rewrite (If_P (z = u) (fapply f empty)
        (If (z ∈ range f) (fapply f (succ (fapply (converse f) z))) z) hzu);
      have hr0 : π (fapply f empty ∈ range f)
        { refine priv_apply_rangeI f omega (λ _, A) empty hfun zero_in_omega };
      rewrite (If_P (fapply f empty ∈ range f)
        (nat_case u (λ w, fapply f w) (fapply (converse f) (fapply f empty)))
        (fapply f empty) hr0);
      rewrite (left_inverse f omega A empty hf zero_in_omega);
      rewrite nat_case_0;
      refine eq_sym hzu }
    { assume hnzu;
      rewrite (If_not_P (z = u) (fapply f empty)
        (If (z ∈ range f) (fapply f (succ (fapply (converse f) z))) z) hnzu);
      refine ∨ₑ (em (z ∈ range f)) _ _
      { assume hzr;
        rewrite (If_P (z ∈ range f)
          (fapply f (succ (fapply (converse f) z))) z hzr);
        have hcz : π (fapply (converse f) z ∈ omega)
          { refine fapply_type (converse f) z (range f) (λ _, omega) hcfun hzr };
        have hsucc : π (succ (fapply (converse f) z) ∈ omega)
          { refine succ_in_omega (fapply (converse f) z) hcz };
        have hsr : π (fapply f (succ (fapply (converse f) z)) ∈ range f)
          { refine priv_apply_rangeI f omega (λ _, A)
              (succ (fapply (converse f) z)) hfun hsucc };
        rewrite (If_P (fapply f (succ (fapply (converse f) z)) ∈ range f)
          (nat_case u (λ w, fapply f w)
             (fapply (converse f) (fapply f (succ (fapply (converse f) z)))))
          (fapply f (succ (fapply (converse f) z))) hsr);
        rewrite (left_inverse f omega A (succ (fapply (converse f) z)) hf hsucc);
        rewrite nat_case_succ; simplify rule off;
        refine right_inverse f omega A z hf hzr }
      { assume hnzr;
        rewrite (If_not_P (z ∈ range f)
          (fapply f (succ (fapply (converse f) z))) z hnzr);
        rewrite (If_not_P (z ∈ range f)
          (nat_case u (λ w, fapply f w) (fapply (converse f) z)) z hnzr);
        reflexivity } } }
end;

opaque symbol nat_cons_eqpoll (A u : τ ι) :
  π (lepoll omega A) → π (eqpoll (cons u A) A) ≔
begin
  assume A u hle;
  refine eqpollI (cons u A) A (nat_cons_lepoll A u hle) _;
  refine subset_imp_lepoll A (cons u A) _;
  assume x hx; refine consI2 x u A hx
end;

// Specialized version required below
opaque symbol nat_succ_eqpoll (A : τ ι) :
  π (omega ⊆ A) → π (eqpoll (succ A) A) ≔
begin
  assume A hsub;
  rewrite succ_def;
  refine nat_cons_eqpoll A A (subset_imp_lepoll omega A hsub)
end;

opaque symbol InfCard_nat :
  π (InfCard omega) ≔
begin
  rewrite InfCard_def;
  refine ∧ᵢ Card_nat (le_refl omega Ord_omega)
end;

opaque symbol InfCard_is_Card (K : τ ι) :
  π (InfCard K) → π (Card K) ≔
begin
  assume K h;
  have h' : π (Card K ∧ le omega K)
    { refine ind_eq (eq_sym (InfCard_def K)) (λ p, p) h };
  refine ∧ₑ₁ h'
end;

opaque symbol InfCard_Un (K L : τ ι) :
  π (InfCard K) → π (Card L) → π (InfCard (Un K L)) ≔
begin
  assume K L hIK hCL;
  have h' : π (Card K ∧ le omega K)
    { refine ind_eq (eq_sym (InfCard_def K)) (λ p, p) hIK };
  have hCK : π (Card K) { refine ∧ₑ₁ h' };
  have hnK : π (le omega K) { refine ∧ₑ₂ h' };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  have hOL : π (Ord L) { refine Card_is_Ord L hCL };
  rewrite InfCard_def;
  refine ∧ᵢ (Card_Un K L hCK hCL)
    (le_trans omega K (Un K L) hnK (Un_upper1_le K L hOK hOL))
end;

// Kunen's Lemma 10.11
opaque symbol InfCard_is_Limit (K : τ ι) :
  π (InfCard K) → π (Limit K) ≔
begin
  assume K hIK;
  have h' : π (Card K ∧ le omega K)
    { refine ind_eq (eq_sym (InfCard_def K)) (λ p, p) hIK };
  have hCK : π (Card K) { refine ∧ₑ₁ h' };
  have hnK : π (le omega K) { refine ∧ₑ₂ h' };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  refine Ord_cases K (Limit K) hOK _ _ _
  { // K = 0 contradicts nat ≤ K
    assume hK0;
    have hn0 : π (le omega empty)
      { refine ind_eq (eq_sym hK0) (λ w, le omega w) hnK };
    refine ∨ₑ (leE omega empty hn0) _ _
    { assume hmem; refine ⊥ₑ (emptyE omega hmem) }
    { assume heq; refine ⊥ₑ (nat_nonempty heq) } }
  { // K = succ(j) contradicts Card(K) via succ(j) ≈ j
    assume hbex;
    refine ∃ₑ hbex _; assume j hj;
    have hOj : π (Ord j) { refine ∧ₑ₁ (∧ₑ₂ hj) };
    have hKsj : π (K = succ j) { refine ∧ₑ₂ (∧ₑ₂ hj) };
    have hCsj : π (Card (succ j))
      { refine ind_eq (eq_sym hKsj) (λ w, Card w) hCK };
    have hnsj : π (le omega (succ j))
      { refine ind_eq (eq_sym hKsj) (λ w, le omega w) hnK };
    have hnj : π (le omega j) { refine Limit_le_succD omega j Limit_omega hnsj };
    have heqp : π (eqpoll (succ j) j)
      { refine nat_succ_eqpoll j (le_imp_subset omega j hnj) };
    have hcc : π (cardinal (succ j) = cardinal j)
      { refine cardinal_cong (succ j) j heqp };
    have hcs : π (cardinal (succ j) = succ j)
      { refine Card_cardinal_eq (succ j) hCsj };
    have hsj_cj : π (succ j = cardinal j) { refine eq_trans (eq_sym hcs) hcc };
    have hlesj : π (le (succ j) j)
      { refine ind_eq hsj_cj (λ w, le w j) (Ord_cardinal_le j hOj) };
    have hltss : π (lt (succ j) (succ j))
      { refine lt_trans1 (succ j) j (succ j) hlesj
          (ltI j (succ j) (succI1 j) (Ord_succ j hOj)) };
    refine ⊥ₑ (lt_irrefl (succ j) hltss) }
  { assume hLim; refine hLim }
end;

// ===========================================================================
// An infinite cardinal equals its square (Kunen, Thm 10.12, page 29)
// ===========================================================================

// A general fact about ordermap
// (NB: `ZF.Order.pred` qualified — Arith's unary predecessor `pred`, opened
// transitively via ZF.ArithSimp below, shadows Order's ternary `pred`.)
opaque symbol ordermap_eqpoll_pred (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) →
  π (eqpoll (fapply (ordermap A r) x) (ZF.Order.pred A x r)) ≔
begin
  assume A r x hwo hx;
  rewrite eqpoll_def;
  have hinj : π (ordermap A r ∈ inj A (ordertype A r))
    { refine bij_is_inj (ordermap A r) A (ordertype A r) (ordermap_bij A r hwo) };
  have hrb : π (restrict (ordermap A r) (ZF.Order.pred A x r)
                ∈ bij (ZF.Order.pred A x r)
                      (Image (ordermap A r) (ZF.Order.pred A x r)))
    { refine restrict_bij (ordermap A r) A (ordertype A r) (ZF.Order.pred A x r)
        hinj (pred_subset A x r) };
  have hcb : π (converse (restrict (ordermap A r) (ZF.Order.pred A x r))
                ∈ bij (Image (ordermap A r) (ZF.Order.pred A x r))
                      (ZF.Order.pred A x r))
    { refine bij_converse_bij (restrict (ordermap A r) (ZF.Order.pred A x r))
        (ZF.Order.pred A x r) (Image (ordermap A r) (ZF.Order.pred A x r)) hrb };
  have him : π (fapply (ordermap A r) x
                = Image (ordermap A r) (ZF.Order.pred A x r))
    { refine ordermap_eq_image A r x (well_ord_is_wf A r hwo) hx };
  refine ∃ᵢ (converse (restrict (ordermap A r) (ZF.Order.pred A x r))) _;
  refine ind_eq him
    (λ w, converse (restrict (ordermap A r) (ZF.Order.pred A x r))
          ∈ bij w (ZF.Order.pred A x r)) hcb
end;

// Port-internal helper (Isabelle Ordinal.Un_least_lt): i<k → j<k → i∪j<k.
private opaque symbol priv_Un_least_lt (i j k : τ ι) :
  π (lt i k) → π (lt j k) → π (lt (Un i j) k) ≔
begin
  assume i j k hik hjk;
  have hOi : π (Ord i) { refine lt_Ord i k hik };
  have hOj : π (Ord j) { refine lt_Ord j k hjk };
  refine ∨ₑ (Ord_linear i j hOi hOj) _ _
  { assume hij;
    have heq : π (Un i j = j)
      { refine subset_antisym (Un i j) j
          (Un_least i j j (OrdmemD j i hij hOj) (subset_refl j)) (Un_upper2 i j) };
    refine ind_eq heq (λ w, lt w k) hjk }
  { assume hd;
    refine ∨ₑ hd _ _
    { assume heqij;
      have heq : π (Un i j = j)
        { refine ind_eq heqij (λ w, Un w j = j) (Un_absorb j) };
      refine ind_eq heq (λ w, lt w k) hjk }
    { assume hji;
      have heq : π (Un i j = i)
        { refine subset_antisym (Un i j) i
            (Un_least i j i (subset_refl i) (OrdmemD i j hji hOi)) (Un_upper1 i j) };
      refine ind_eq heq (λ w, lt w k) hik } }
end;

// Establishing the well-ordering
opaque symbol well_ord_csquare (K : τ ι) :
  π (Ord K) → π (well_ord (Sigma K (λ _, K)) (csquare_rel K)) ≔
begin
  assume K hOK;
  rewrite csquare_rel_def;
  refine well_ord_rvimage (Sigma K (λ _, K)) (Sigma K (λ _, Sigma K (λ _, K)))
    (Lambda (Sigma K (λ _, K))
       (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p))))
    (rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))) _ _
  { refine lam_injective (Sigma K (λ _, K)) (Sigma K (λ _, Sigma K (λ _, K)))
      (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))
      (λ q, snd q) _ _
    { assume p hp;
      have hf : π (fst p ∈ K) { refine SigmaD1 p K (λ _, K) hp };
      have hs : π (snd p ∈ K) { refine SigmaD2 p K (λ _, K) hp };
      have hUnK : π (Un (fst p) (snd p) ∈ K)
        { refine ltD (Un (fst p) (snd p)) K
            (priv_Un_least_lt (fst p) (snd p) K
               (ltI (fst p) K hf hOK) (ltI (snd p) K hs hOK)) };
      refine SigmaI (Un (fst p) (snd p)) (Pair (fst p) (snd p)) K
        (λ _, Sigma K (λ _, K)) hUnK
        (SigmaI (fst p) (snd p) K (λ _, K) hf hs) }
    { assume p hp;
      rewrite snd_conv;
      refine Pair_fst_snd p K (λ _, K) hp } }
  { refine well_ord_rmult K (Memrel K) (Sigma K (λ _, K))
      (rmult K (Memrel K) K (Memrel K)) (well_ord_Memrel K hOK)
      (well_ord_rmult K (Memrel K) K (Memrel K)
         (well_ord_Memrel K hOK) (well_ord_Memrel K hOK)) }
end;

// Characterising initial segments of the well-ordering

// Port-internal: β-computation of the csquare_rel measure map on a pair.
private opaque symbol priv_csquare_beta (x y K : τ ι) :
  π (Pair x y ∈ Sigma K (λ _, K)) →
  π (fapply (Lambda (Sigma K (λ _, K))
        (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair x y)
     = Pair (Un x y) (Pair x y)) ≔
begin
  assume x y K hmem;
  rewrite (beta (Sigma K (λ _, K))
    (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p))) (Pair x y) hmem);
  simplify rule off;
  repeat orelse rewrite fst_conv rewrite snd_conv;
  reflexivity
end;

// Port-internal: unfold membership in csquare_rel to the underlying rmult.
private opaque symbol priv_csquareD_raw (x y z K : τ ι) :
  π (Pair (Pair x y) (Pair z z) ∈ csquare_rel K) →
  π (Pair (Pair (Un x y) (Pair x y)) (Pair z (Pair z z))
     ∈ rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))) ≔
begin
  assume x y z K h;
  have h0 : π (Pair (Pair x y) (Pair z z)
               ∈ rvimage (Sigma K (λ _, K))
                   (Lambda (Sigma K (λ _, K))
                      (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p))))
                   (rmult K (Memrel K) (Sigma K (λ _, K))
                      (rmult K (Memrel K) K (Memrel K))))
    { refine ind_eq (eq_sym (csquare_rel_def K))
        (λ w, Pair (Pair x y) (Pair z z) ∈ w) h };
  have h1 : π (Pair
      (fapply (Lambda (Sigma K (λ _, K))
         (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair x y))
      (fapply (Lambda (Sigma K (λ _, K))
         (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair z z))
      ∈ rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))
      ∧ Pair x y ∈ Sigma K (λ _, K) ∧ Pair z z ∈ Sigma K (λ _, K))
    { refine ∧ₑ₁ (rvimage_iff (Pair x y) (Pair z z) (Sigma K (λ _, K))
        (Lambda (Sigma K (λ _, K))
           (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p))))
        (rmult K (Memrel K) (Sigma K (λ _, K))
           (rmult K (Memrel K) K (Memrel K)))) h0 };
  have hbeta1 : π (fapply (Lambda (Sigma K (λ _, K))
        (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair x y)
      = Pair (Un x y) (Pair x y))
    { refine priv_csquare_beta x y K (∧ₑ₁ (∧ₑ₂ h1)) };
  have hbeta2 : π (fapply (Lambda (Sigma K (λ _, K))
        (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair z z)
      = Pair z (Pair z z))
    { have hb : π (fapply (Lambda (Sigma K (λ _, K))
          (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair z z)
        = Pair (Un z z) (Pair z z))
        { refine priv_csquare_beta z z K (∧ₑ₂ (∧ₑ₂ h1)) };
      rewrite hb; rewrite Un_absorb; reflexivity };
  have hR1 : π (Pair (Pair (Un x y) (Pair x y))
      (fapply (Lambda (Sigma K (λ _, K))
         (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair z z))
      ∈ rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K)))
    { refine ind_eq (eq_sym hbeta1)
        (λ w, Pair w (fapply (Lambda (Sigma K (λ _, K))
           (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair z z))
           ∈ rmult K (Memrel K) (Sigma K (λ _, K))
               (rmult K (Memrel K) K (Memrel K))) (∧ₑ₁ h1) };
  refine ind_eq (eq_sym hbeta2)
    (λ w, Pair (Pair (Un x y) (Pair x y)) w
          ∈ rmult K (Memrel K) (Sigma K (λ _, K))
              (rmult K (Memrel K) K (Memrel K))) hR1
end;

// Port-internal: build membership in csquare_rel from the underlying rmult.
private opaque symbol priv_csquareI (x y z K : τ ι) :
  π (x ∈ K) → π (y ∈ K) → π (z ∈ K) →
  π (Pair (Pair (Un x y) (Pair x y)) (Pair z (Pair z z))
     ∈ rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))) →
  π (Pair (Pair x y) (Pair z z) ∈ csquare_rel K) ≔
begin
  assume x y z K hx hy hz hR;
  have hmemxy : π (Pair x y ∈ Sigma K (λ _, K))
    { refine SigmaI x y K (λ _, K) hx hy };
  have hmemzz : π (Pair z z ∈ Sigma K (λ _, K))
    { refine SigmaI z z K (λ _, K) hz hz };
  have hbeta1 : π (fapply (Lambda (Sigma K (λ _, K))
        (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair x y)
      = Pair (Un x y) (Pair x y))
    { refine priv_csquare_beta x y K hmemxy };
  have hbeta2 : π (fapply (Lambda (Sigma K (λ _, K))
        (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair z z)
      = Pair z (Pair z z))
    { have hb : π (fapply (Lambda (Sigma K (λ _, K))
          (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair z z)
        = Pair (Un z z) (Pair z z))
        { refine priv_csquare_beta z z K hmemzz };
      rewrite hb; rewrite Un_absorb; reflexivity };
  have hR1 : π (Pair
      (fapply (Lambda (Sigma K (λ _, K))
         (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair x y))
      (Pair z (Pair z z))
      ∈ rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K)))
    { refine ind_eq hbeta1
        (λ w, Pair w (Pair z (Pair z z))
              ∈ rmult K (Memrel K) (Sigma K (λ _, K))
                  (rmult K (Memrel K) K (Memrel K))) hR };
  have hR2 : π (Pair
      (fapply (Lambda (Sigma K (λ _, K))
         (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair x y))
      (fapply (Lambda (Sigma K (λ _, K))
         (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair z z))
      ∈ rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K)))
    { refine ind_eq hbeta2
        (λ w, Pair (fapply (Lambda (Sigma K (λ _, K))
           (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p)))) (Pair x y)) w
           ∈ rmult K (Memrel K) (Sigma K (λ _, K))
               (rmult K (Memrel K) K (Memrel K))) hR1 };
  rewrite csquare_rel_def;
  refine ∧ₑ₂ (rvimage_iff (Pair x y) (Pair z z) (Sigma K (λ _, K))
    (Lambda (Sigma K (λ _, K))
       (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p))))
    (rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))))
    (∧ᵢ hR2 (∧ᵢ hmemxy hmemzz))
end;

opaque symbol csquareD (x y z K : τ ι) :
  π (Pair (Pair x y) (Pair z z) ∈ csquare_rel K) →
  π (lt x K) → π (lt y K) → π (lt z K) →
  π (le x z ∧ le y z) ≔
begin
  assume x y z K h hxK hyK hzK;
  have hOx : π (Ord x) { refine lt_Ord x K hxK };
  have hOy : π (Ord y) { refine lt_Ord y K hyK };
  have hOz : π (Ord z) { refine lt_Ord z K hzK };
  have hR : π (Pair (Pair (Un x y) (Pair x y)) (Pair z (Pair z z))
               ∈ rmult K (Memrel K) (Sigma K (λ _, K))
                   (rmult K (Memrel K) K (Memrel K)))
    { refine priv_csquareD_raw x y z K h };
  refine ∨ₑ (∧ₑ₁ (rmult_iff (Un x y) (Pair x y) z (Pair z z) K (Memrel K)
    (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))) hR) _ _
  { assume hA;
    have hUnz : π (Un x y ∈ z)
      { refine ∧ₑ₂ (∧ₑ₂ (MemrelE (Un x y) z K (∧ₑ₁ hA))) };
    have hltU : π (lt (Un x y) z) { refine ltI (Un x y) z hUnz hOz };
    have hxz : π (lt x z)
      { refine lt_trans1 x (Un x y) z (Un_upper1_le x y hOx hOy) hltU };
    have hyz : π (lt y z)
      { refine lt_trans1 y (Un x y) z (Un_upper2_le x y hOx hOy) hltU };
    refine ∧ᵢ (leI x z (ltD x z hxz) hOz) (leI y z (ltD y z hyz) hOz) }
  { assume hB;
    have hUneq : π (Un x y = z) { refine ∧ₑ₁ (∧ₑ₂ hB) };
    refine ∨ₑ (∧ₑ₁ (rmult_iff x y z z K (Memrel K) K (Memrel K)) (∧ₑ₁ hB)) _ _
    { assume hB1;
      have hxz : π (x ∈ z) { refine ∧ₑ₂ (∧ₑ₂ (MemrelE x z K (∧ₑ₁ hB1))) };
      refine ∧ᵢ (leI x z hxz hOz)
        (ind_eq (eq_sym hUneq) (λ w, le y w) (Un_upper2_le x y hOx hOy)) }
    { assume hB2;
      have hyz : π (y ∈ z) { refine ∧ₑ₂ (∧ₑ₂ (MemrelE y z K (∧ₑ₁ hB2))) };
      have hxeq : π (x = z) { refine ∧ₑ₁ (∧ₑ₂ hB2) };
      refine ∧ᵢ (le_eqI x z hxeq hOz) (leI y z hyz hOz) } }
end;

opaque symbol pred_csquare_subset (z K : τ ι) :
  π (lt z K) →
  π (ZF.Order.pred (Sigma K (λ _, K)) (Pair z z) (csquare_rel K) ⊆
     Sigma (succ z) (λ _, succ z)) ≔
begin
  assume z K hzK;
  have hOK : π (Ord K) { refine lt_Ord2 z K hzK };
  assume w hw;
  have hw' : π (Pair w (Pair z z) ∈ csquare_rel K ∧ w ∈ Sigma K (λ _, K))
    { refine ∧ₑ₁ (pred_iff w (Sigma K (λ _, K)) (Pair z z) (csquare_rel K)) hw };
  have hwS : π (w ∈ Sigma K (λ _, K)) { refine ∧ₑ₂ hw' };
  have hfw : π (fst w ∈ K) { refine SigmaD1 w K (λ _, K) hwS };
  have hsw : π (snd w ∈ K) { refine SigmaD2 w K (λ _, K) hwS };
  have hpair : π (Pair (fst w) (snd w) = w) { refine Pair_fst_snd w K (λ _, K) hwS };
  have hcsq : π (Pair (Pair (fst w) (snd w)) (Pair z z) ∈ csquare_rel K)
    { refine ind_eq hpair (λ v, Pair v (Pair z z) ∈ csquare_rel K) (∧ₑ₁ hw') };
  have hle : π (le (fst w) z ∧ le (snd w) z)
    { refine csquareD (fst w) (snd w) z K hcsq
        (ltI (fst w) K hfw hOK) (ltI (snd w) K hsw hOK) hzK };
  refine ind_eq (eq_sym hpair) (λ v, v ∈ Sigma (succ z) (λ _, succ z)) _;
  refine SigmaI (fst w) (snd w) (succ z) (λ _, succ z)
    (ltD (fst w) (succ z) (∧ₑ₁ hle)) (ltD (snd w) (succ z) (∧ₑ₂ hle))
end;

opaque symbol csquare_ltI (x y z K : τ ι) :
  π (lt x z) → π (lt y z) → π (lt z K) →
  π (Pair (Pair x y) (Pair z z) ∈ csquare_rel K) ≔
begin
  assume x y z K hxz hyz hzK;
  have hxK : π (lt x K) { refine lt_trans x z K hxz hzK };
  have hyK : π (lt y K) { refine lt_trans y z K hyz hzK };
  have hx : π (x ∈ K) { refine ltD x K hxK };
  have hy : π (y ∈ K) { refine ltD y K hyK };
  have hz : π (z ∈ K) { refine ltD z K hzK };
  have hUnz : π (Un x y ∈ z) { refine ltD (Un x y) z (priv_Un_least_lt x y z hxz hyz) };
  have hUnK : π (Un x y ∈ K) { refine ltD (Un x y) K (priv_Un_least_lt x y K hxK hyK) };
  refine priv_csquareI x y z K hx hy hz _;
  refine ∧ₑ₂ (rmult_iff (Un x y) (Pair x y) z (Pair z z) K (Memrel K)
    (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))) _;
  refine ∨ᵢ₁ (∧ᵢ (MemrelI (Un x y) z K hUnz hUnK hz)
    (∧ᵢ hUnK (∧ᵢ hz (∧ᵢ (SigmaI x y K (λ _, K) hx hy)
                        (SigmaI z z K (λ _, K) hz hz)))))
end;

// Part of the traditional proof. UNUSED since it's harder to prove and apply
opaque symbol csquare_or_eqI (x y z K : τ ι) :
  π (le x z) → π (le y z) → π (lt z K) →
  π ((Pair (Pair x y) (Pair z z) ∈ csquare_rel K) ∨ (x = z ∧ y = z)) ≔
begin
  assume x y z K hxz hyz hzK;
  have hOz : π (Ord z) { refine lt_Ord z K hzK };
  have hOK : π (Ord K) { refine lt_Ord2 z K hzK };
  have hz : π (z ∈ K) { refine ltD z K hzK };
  refine ∨ₑ (leE x z hxz) _ _
  { assume hxmem;
    have hx : π (x ∈ K) { refine Ord_trans x z K hxmem hz hOK };
    refine ∨ₑ (leE y z hyz) _ _
    { assume hymem;
      refine ∨ᵢ₁ (csquare_ltI x y z K (ltI x z hxmem hOz) (ltI y z hymem hOz) hzK) }
    { assume hyeq;
      have hy : π (y ∈ K) { refine ind_eq hyeq (λ w, w ∈ K) hz };
      have hUneq : π (Un x y = z)
        { rewrite hyeq;
          refine subset_antisym (Un x z) z
            (Un_least x z z (OrdmemD z x hxmem hOz) (subset_refl z))
            (Un_upper2 x z) };
      refine ∨ᵢ₁ _;
      refine priv_csquareI x y z K hx hy hz _;
      refine ∧ₑ₂ (rmult_iff (Un x y) (Pair x y) z (Pair z z) K (Memrel K)
        (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))) _;
      refine ∨ᵢ₂ (∧ᵢ _ (∧ᵢ hUneq (∧ᵢ hz
        (∧ᵢ (SigmaI x y K (λ _, K) hx hy) (SigmaI z z K (λ _, K) hz hz)))));
      refine ∧ₑ₂ (rmult_iff x y z z K (Memrel K) K (Memrel K)) _;
      refine ∨ᵢ₁ (∧ᵢ (MemrelI x z K hxmem hx hz) (∧ᵢ hx (∧ᵢ hz (∧ᵢ hy hz)))) } }
  { assume hxeq;
    have hx : π (x ∈ K) { refine ind_eq hxeq (λ w, w ∈ K) hz };
    refine ∨ₑ (leE y z hyz) _ _
    { assume hymem;
      have hy : π (y ∈ K) { refine Ord_trans y z K hymem hz hOK };
      have hUneq : π (Un x y = z)
        { rewrite hxeq;
          refine subset_antisym (Un z y) z
            (Un_least z y z (subset_refl z) (OrdmemD z y hymem hOz))
            (Un_upper1 z y) };
      refine ∨ᵢ₁ _;
      refine priv_csquareI x y z K hx hy hz _;
      refine ∧ₑ₂ (rmult_iff (Un x y) (Pair x y) z (Pair z z) K (Memrel K)
        (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K))) _;
      refine ∨ᵢ₂ (∧ᵢ _ (∧ᵢ hUneq (∧ᵢ hz
        (∧ᵢ (SigmaI x y K (λ _, K) hx hy) (SigmaI z z K (λ _, K) hz hz)))));
      refine ∧ₑ₂ (rmult_iff x y z z K (Memrel K) K (Memrel K)) _;
      refine ∨ᵢ₂ (∧ᵢ (MemrelI y z K hymem hy hz) (∧ᵢ hxeq (∧ᵢ hz (∧ᵢ hy hz)))) }
    { assume hyeq; refine ∨ᵢ₂ (∧ᵢ hxeq hyeq) } }
end;

// The cardinality of initial segments

opaque symbol ordermap_z_lt (K x y z : τ ι) :
  π (Limit K) → π (lt x K) → π (lt y K) → π (z = succ (Un x y)) →
  π (lt (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
       (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair z z))) ≔
begin
  assume K x y z hLim hxK hyK heqz;
  have hOK : π (Ord K) { refine Limit_is_Ord K hLim };
  have hOx : π (Ord x) { refine lt_Ord x K hxK };
  have hOy : π (Ord y) { refine lt_Ord y K hyK };
  have hUnK : π (Un x y ∈ K)
    { refine ltD (Un x y) K (priv_Un_least_lt x y K hxK hyK) };
  have hzK : π (lt z K)
    { refine ind_eq heqz (λ w, lt w K)
        (ltI (succ (Un x y)) K (Limit_has_succ K (Un x y) hLim hUnK) hOK) };
  have hxz : π (lt x z)
    { refine ind_eq heqz (λ w, lt x w) (Un_upper1_le x y hOx hOy) };
  have hyz : π (lt y z)
    { refine ind_eq heqz (λ w, lt y w) (Un_upper2_le x y hOx hOy) };
  have hmem : π (Pair (Pair x y) (Pair z z) ∈ csquare_rel K)
    { refine csquare_ltI x y z K hxz hyz hzK };
  have hwo : π (well_ord (Sigma K (λ _, K)) (csquare_rel K))
    { refine well_ord_csquare K hOK };
  have hxyS : π (Pair x y ∈ Sigma K (λ _, K))
    { refine SigmaI x y K (λ _, K) (ltD x K hxK) (ltD y K hyK) };
  have hzzS : π (Pair z z ∈ Sigma K (λ _, K))
    { refine SigmaI z z K (λ _, K) (ltD z K hzK) (ltD z K hzK) };
  refine ltI (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
    (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair z z))
    (ordermap_mono (Pair x y) (Pair z z) (Sigma K (λ _, K)) (csquare_rel K)
       hmem (well_ord_is_wf (Sigma K (λ _, K)) (csquare_rel K) hwo) hxyS hzzS)
    (Ord_ordermap (Sigma K (λ _, K)) (csquare_rel K) (Pair z z) hwo hzzS)
end;

// Kunen: "each ⟨x,y⟩∈K×K has no more than z×z predecessors..." (page 29)
// (z ≡ succ(x∪y), inlined — a pure local abbreviation in the Isar source)
opaque symbol ordermap_csquare_le (K x y : τ ι) :
  π (Limit K) → π (lt x K) → π (lt y K) →
  π (le (cardinal (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y)))
       (cmult (cardinal (succ (succ (Un x y)))) (cardinal (succ (succ (Un x y)))))) ≔
begin
  assume K x y hLim hxK hyK;
  have hOK : π (Ord K) { refine Limit_is_Ord K hLim };
  have hOx : π (Ord x) { refine lt_Ord x K hxK };
  have hOy : π (Ord y) { refine lt_Ord y K hyK };
  have hOu : π (Ord (Un x y)) { refine Ord_Un x y hOx hOy };
  have hOz : π (Ord (succ (Un x y))) { refine Ord_succ (Un x y) hOu };
  have hOsz : π (Ord (succ (succ (Un x y)))) { refine Ord_succ (succ (Un x y)) hOz };
  have hUnK : π (Un x y ∈ K)
    { refine ltD (Un x y) K (priv_Un_least_lt x y K hxK hyK) };
  have hzK : π (lt (succ (Un x y)) K)
    { refine ltI (succ (Un x y)) K (Limit_has_succ K (Un x y) hLim hUnK) hOK };
  have hwo : π (well_ord (Sigma K (λ _, K)) (csquare_rel K))
    { refine well_ord_csquare K hOK };
  rewrite cmult_def;
  refine well_ord_lepoll_imp_cardinal_le
    (Sigma (cardinal (succ (succ (Un x y))))
       (λ _, cardinal (succ (succ (Un x y)))))
    (rmult (cardinal (succ (succ (Un x y))))
       (Memrel (cardinal (succ (succ (Un x y)))))
       (cardinal (succ (succ (Un x y))))
       (Memrel (cardinal (succ (succ (Un x y))))))
    (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y)) _ _
  { refine well_ord_rmult (cardinal (succ (succ (Un x y))))
      (Memrel (cardinal (succ (succ (Un x y)))))
      (cardinal (succ (succ (Un x y))))
      (Memrel (cardinal (succ (succ (Un x y)))))
      (well_ord_Memrel (cardinal (succ (succ (Un x y))))
         (Ord_cardinal (succ (succ (Un x y)))))
      (well_ord_Memrel (cardinal (succ (succ (Un x y))))
         (Ord_cardinal (succ (succ (Un x y))))) }
  { have hlt : π (lt (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
                    (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
                       (Pair (succ (Un x y)) (succ (Un x y)))))
      { refine ordermap_z_lt K x y (succ (Un x y)) hLim hxK hyK
          (eq_refl (succ (Un x y))) };
    have hlep1 : π (lepoll
        (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
        (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
           (Pair (succ (Un x y)) (succ (Un x y)))))
      { refine le_imp_lepoll
          (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
          (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
             (Pair (succ (Un x y)) (succ (Un x y))))
          (leI (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
             (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
                (Pair (succ (Un x y)) (succ (Un x y))))
             (ltD (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
                (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
                   (Pair (succ (Un x y)) (succ (Un x y)))) hlt)
             (lt_Ord2 (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
                (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
                   (Pair (succ (Un x y)) (succ (Un x y)))) hlt)) };
    have hzzS : π (Pair (succ (Un x y)) (succ (Un x y)) ∈ Sigma K (λ _, K))
      { refine SigmaI (succ (Un x y)) (succ (Un x y)) K (λ _, K)
          (ltD (succ (Un x y)) K hzK) (ltD (succ (Un x y)) K hzK) };
    have heqp2 : π (eqpoll
        (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
           (Pair (succ (Un x y)) (succ (Un x y))))
        (ZF.Order.pred (Sigma K (λ _, K))
           (Pair (succ (Un x y)) (succ (Un x y))) (csquare_rel K)))
      { refine ordermap_eqpoll_pred (Sigma K (λ _, K)) (csquare_rel K)
          (Pair (succ (Un x y)) (succ (Un x y))) hwo hzzS };
    have hlep3 : π (lepoll
        (ZF.Order.pred (Sigma K (λ _, K))
           (Pair (succ (Un x y)) (succ (Un x y))) (csquare_rel K))
        (Sigma (succ (succ (Un x y))) (λ _, succ (succ (Un x y)))))
      { refine subset_imp_lepoll
          (ZF.Order.pred (Sigma K (λ _, K))
             (Pair (succ (Un x y)) (succ (Un x y))) (csquare_rel K))
          (Sigma (succ (succ (Un x y))) (λ _, succ (succ (Un x y))))
          (pred_csquare_subset (succ (Un x y)) K hzK) };
    have heqp4 : π (eqpoll
        (Sigma (succ (succ (Un x y))) (λ _, succ (succ (Un x y))))
        (Sigma (cardinal (succ (succ (Un x y))))
           (λ _, cardinal (succ (succ (Un x y))))))
      { refine prod_eqpoll_cong (succ (succ (Un x y)))
          (cardinal (succ (succ (Un x y))))
          (succ (succ (Un x y))) (cardinal (succ (succ (Un x y))))
          (eqpoll_sym (cardinal (succ (succ (Un x y)))) (succ (succ (Un x y)))
             (Ord_cardinal_eqpoll (succ (succ (Un x y))) hOsz))
          (eqpoll_sym (cardinal (succ (succ (Un x y)))) (succ (succ (Un x y)))
             (Ord_cardinal_eqpoll (succ (succ (Un x y))) hOsz)) };
    refine lepoll_eq_trans
      (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
      (Sigma (succ (succ (Un x y))) (λ _, succ (succ (Un x y))))
      (Sigma (cardinal (succ (succ (Un x y))))
         (λ _, cardinal (succ (succ (Un x y)))))
      _ heqp4;
    refine lepoll_trans
      (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
      (ZF.Order.pred (Sigma K (λ _, K))
         (Pair (succ (Un x y)) (succ (Un x y))) (csquare_rel K))
      (Sigma (succ (succ (Un x y))) (λ _, succ (succ (Un x y))))
      (lepoll_eq_trans
         (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
         (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
            (Pair (succ (Un x y)) (succ (Un x y))))
         (ZF.Order.pred (Sigma K (λ _, K))
            (Pair (succ (Un x y)) (succ (Un x y))) (csquare_rel K))
         hlep1 heqp2)
      hlep3 }
end;

// Kunen: "... so the order type is ≤ K"
opaque symbol ordertype_csquare_le (K : τ ι) :
  π (InfCard K) →
  (Π (y : τ ι), π (y ∈ K) → π (InfCard y) → π (cmult y y = y)) →
  π (le (ordertype (Sigma K (λ _, K)) (csquare_rel K)) K) ≔
begin
  assume K hIK heq;
  have hCK : π (Card K) { refine InfCard_is_Card K hIK };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  have hnatK : π (le omega K)
    { refine ∧ₑ₂ (ind_eq (eq_sym (InfCard_def K)) (λ q, q) hIK) };
  have hLim : π (Limit K) { refine InfCard_is_Limit K hIK };
  have hwo : π (well_ord (Sigma K (λ _, K)) (csquare_rel K))
    { refine well_ord_csquare K hOK };
  have hOT : π (Ord (ordertype (Sigma K (λ _, K)) (csquare_rel K)))
    { refine Ord_ordertype (Sigma K (λ _, K)) (csquare_rel K) hwo };
  refine all_lt_imp_le K (ordertype (Sigma K (λ _, K)) (csquare_rel K)) hOK hOT _;
  assume i hi;
  have hiRF : π (i ∈ RepFun (Sigma K (λ _, K))
                   (λ p, fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) p))
    { refine ind_eq (eq_sym (ordertype_unfold (Sigma K (λ _, K)) (csquare_rel K)))
        (λ w, i ∈ w) hi };
  refine ∃ₑ (∧ₑ₁ (RepFun_iff i (Sigma K (λ _, K))
      (λ p, fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) p)) hiRF) _;
  assume p hp;
  have hpS : π (p ∈ Sigma K (λ _, K)) { refine ∧ₑ₁ hp };
  have hieq : π (i = fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K))
                    (Pair (fst p) (snd p)))
    { refine ind_eq (Pair_fst_snd p K (λ _, K) hpS)
        (λ w, i = fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) w)
        (∧ₑ₂ hp) };
  have hfp : π (fst p ∈ K) { refine SigmaD1 p K (λ _, K) hpS };
  have hsp : π (snd p ∈ K) { refine SigmaD2 p K (λ _, K) hpS };
  have hxK : π (lt (fst p) K) { refine ltI (fst p) K hfp hOK };
  have hyK : π (lt (snd p) K) { refine ltI (snd p) K hsp hOK };
  have hOx : π (Ord (fst p)) { refine lt_Ord (fst p) K hxK };
  have hOy : π (Ord (snd p)) { refine lt_Ord (snd p) K hyK };
  have hOu : π (Ord (Un (fst p) (snd p))) { refine Ord_Un (fst p) (snd p) hOx hOy };
  have hOi : π (Ord i)
    { refine Ord_in_Ord (ordertype (Sigma K (λ _, K)) (csquare_rel K)) i hOT hi };
  have hile : π (le (cardinal i)
                   (cmult (cardinal (succ (succ (Un (fst p) (snd p)))))
                          (cardinal (succ (succ (Un (fst p) (snd p)))))))
    { refine ind_eq hieq
        (λ w, le (cardinal w)
                 (cmult (cardinal (succ (succ (Un (fst p) (snd p)))))
                        (cardinal (succ (succ (Un (fst p) (snd p)))))))
        (ordermap_csquare_le K (fst p) (snd p) hLim hxK hyK) };
  have hcmlt : π (lt (cmult (cardinal (succ (succ (Un (fst p) (snd p)))))
                            (cardinal (succ (succ (Un (fst p) (snd p)))))) K)
    { refine ∨ₑ (Ord_linear (Un (fst p) (snd p)) omega hOu Ord_omega) _ _
      { assume humem;
        have hssm : π (succ (succ (Un (fst p) (snd p))) ∈ omega)
          { refine succ_in_omega (succ (Un (fst p) (snd p)))
              (succ_in_omega (Un (fst p) (snd p)) humem) };
        have hcceq : π (cardinal (succ (succ (Un (fst p) (snd p))))
                        = succ (succ (Un (fst p) (snd p))))
          { refine Card_cardinal_eq (succ (succ (Un (fst p) (snd p))))
              (nat_into_Card (succ (succ (Un (fst p) (snd p)))) hssm) };
        have hcm_nat : π (cmult (succ (succ (Un (fst p) (snd p))))
                                (succ (succ (Un (fst p) (snd p)))) ∈ omega)
          { refine ind_eq (nat_cmult_eq_mult (succ (succ (Un (fst p) (snd p))))
                (succ (succ (Un (fst p) (snd p)))) hssm hssm)
              (λ w, w ∈ omega)
              (mult_type (succ (succ (Un (fst p) (snd p))))
                 (succ (succ (Un (fst p) (snd p))))) };
        have hmem : π (cmult (cardinal (succ (succ (Un (fst p) (snd p)))))
                             (cardinal (succ (succ (Un (fst p) (snd p))))) ∈ omega)
          { refine ind_eq hcceq (λ w, cmult w w ∈ omega) hcm_nat };
        refine ltI (cmult (cardinal (succ (succ (Un (fst p) (snd p)))))
                          (cardinal (succ (succ (Un (fst p) (snd p)))))) K
          (le_imp_subset omega K hnatK
             (cmult (cardinal (succ (succ (Un (fst p) (snd p)))))
                    (cardinal (succ (succ (Un (fst p) (snd p)))))) hmem) hOK }
      { assume hd;
        have hnatu : π (le omega (Un (fst p) (snd p)))
          { refine ∨ₑ hd _ _
            { assume hueq;
              refine le_eqI omega (Un (fst p) (snd p)) (eq_sym hueq) hOu }
            { assume homem;
              refine leI omega (Un (fst p) (snd p)) homem hOu } };
        have hsubu : π (omega ⊆ Un (fst p) (snd p))
          { refine le_imp_subset omega (Un (fst p) (snd p)) hnatu };
        have he1 : π (eqpoll (succ (Un (fst p) (snd p))) (Un (fst p) (snd p)))
          { refine nat_succ_eqpoll (Un (fst p) (snd p)) hsubu };
        have hsubsu : π (omega ⊆ succ (Un (fst p) (snd p)))
          { assume w hw;
            refine succI2 w (Un (fst p) (snd p)) (hsubu w hw) };
        have he2 : π (eqpoll (succ (succ (Un (fst p) (snd p))))
                             (succ (Un (fst p) (snd p))))
          { refine nat_succ_eqpoll (succ (Un (fst p) (snd p))) hsubsu };
        have hseq : π (cardinal (succ (succ (Un (fst p) (snd p))))
                       = cardinal (Un (fst p) (snd p)))
          { refine eq_trans
              (cardinal_cong (succ (succ (Un (fst p) (snd p))))
                 (succ (Un (fst p) (snd p))) he2)
              (cardinal_cong (succ (Un (fst p) (snd p))) (Un (fst p) (snd p)) he1) };
        have huK : π (lt (Un (fst p) (snd p)) K)
          { refine priv_Un_least_lt (fst p) (snd p) K hxK hyK };
        have hcuK : π (lt (cardinal (Un (fst p) (snd p))) K)
          { refine lt_trans1 (cardinal (Un (fst p) (snd p))) (Un (fst p) (snd p)) K
              (Ord_cardinal_le (Un (fst p) (snd p)) hOu) huK };
        have hcssK : π (lt (cardinal (succ (succ (Un (fst p) (snd p))))) K)
          { refine ind_eq hseq (λ w, lt w K) hcuK };
        have hIC : π (InfCard (cardinal (succ (succ (Un (fst p) (snd p))))))
          { rewrite InfCard_def;
            refine ∧ᵢ (Card_cardinal (succ (succ (Un (fst p) (snd p))))) _;
            refine ind_eq hseq (λ w, le omega w)
              (nat_le_cardinal (Un (fst p) (snd p)) hnatu) };
        have hsq : π (cmult (cardinal (succ (succ (Un (fst p) (snd p)))))
                            (cardinal (succ (succ (Un (fst p) (snd p)))))
                    = cardinal (succ (succ (Un (fst p) (snd p)))))
          { refine heq (cardinal (succ (succ (Un (fst p) (snd p)))))
              (ltD (cardinal (succ (succ (Un (fst p) (snd p))))) K hcssK) hIC };
        refine ind_eq hsq (λ w, lt w K) hcssK } };
  have hciK : π (lt (cardinal i) K)
    { refine lt_trans1 (cardinal i)
        (cmult (cardinal (succ (succ (Un (fst p) (snd p)))))
               (cardinal (succ (succ (Un (fst p) (snd p)))))) K hile hcmlt };
  refine ltD i K (Card_lt_imp_lt i K hciK hOi hCK)
end;

// Main result: Kunen's Theorem 10.12
opaque symbol InfCard_csquare_eq (K : τ ι) :
  π (InfCard K) → π (cmult K K = K) ≔
begin
  assume K hIK;
  have hOK : π (Ord K)
    { refine Card_is_Ord K (InfCard_is_Card K hIK) };
  refine trans_induct K (λ w, InfCard w ⇒ cmult w w = w) hOK _ hIK;
  assume j hOj IH hICj;
  have hCj : π (Card j) { refine InfCard_is_Card j hICj };
  have hwoj : π (well_ord (Sigma j (λ _, j)) (csquare_rel j))
    { refine well_ord_csquare j hOj };
  have hOT : π (Ord (ordertype (Sigma j (λ _, j)) (csquare_rel j)))
    { refine Ord_ordertype (Sigma j (λ _, j)) (csquare_rel j) hwoj };
  have hc : π (cardinal (Sigma j (λ _, j))
               = cardinal (ordertype (Sigma j (λ _, j)) (csquare_rel j)))
    { refine cardinal_cong (Sigma j (λ _, j))
        (ordertype (Sigma j (λ _, j)) (csquare_rel j))
        (bij_imp_eqpoll (ordermap (Sigma j (λ _, j)) (csquare_rel j))
           (Sigma j (λ _, j)) (ordertype (Sigma j (λ _, j)) (csquare_rel j))
           (ordermap_bij (Sigma j (λ _, j)) (csquare_rel j) hwoj)) };
  have hle_ot : π (le (ordertype (Sigma j (λ _, j)) (csquare_rel j)) j)
    { refine ordertype_csquare_le j hICj _;
      assume y hy hICy; refine IH y hy hICy };
  have h1 : π (le (cmult j j) j)
    { rewrite cmult_def; rewrite hc;
      refine le_trans (cardinal (ordertype (Sigma j (λ _, j)) (csquare_rel j)))
        (ordertype (Sigma j (λ _, j)) (csquare_rel j)) j
        (Ord_cardinal_le (ordertype (Sigma j (λ _, j)) (csquare_rel j)) hOT)
        hle_ot };
  refine le_anti_sym (cmult j j) j h1 (cmult_square_le j hCj)
end;

// Corollary for arbitrary well-ordered sets (all sets, assuming AC)
opaque symbol well_ord_InfCard_square_eq (A r : τ ι) :
  π (well_ord A r) → π (InfCard (cardinal A)) → π (eqpoll (Sigma A (λ _, A)) A) ≔
begin
  assume A r hwo hI;
  have he : π (eqpoll A (cardinal A))
    { refine eqpoll_sym (cardinal A) A (well_ord_cardinal_eqpoll A r hwo) };
  have he2 : π (eqpoll (Sigma A (λ _, A))
                       (Sigma (cardinal A) (λ _, cardinal A)))
    { refine prod_eqpoll_cong A (cardinal A) A (cardinal A) he he };
  have hwoc : π (well_ord (Sigma (cardinal A) (λ _, cardinal A))
                   (rmult (cardinal A) (Memrel (cardinal A))
                          (cardinal A) (Memrel (cardinal A))))
    { refine well_ord_rmult (cardinal A) (Memrel (cardinal A))
        (cardinal A) (Memrel (cardinal A))
        (well_ord_Memrel (cardinal A) (Ord_cardinal A))
        (well_ord_Memrel (cardinal A) (Ord_cardinal A)) };
  have hcc : π (cardinal (Sigma (cardinal A) (λ _, cardinal A)) = cardinal A)
    { refine eq_trans (eq_sym (cmult_def (cardinal A) (cardinal A)))
        (InfCard_csquare_eq (cardinal A) hI) };
  have he3 : π (eqpoll (Sigma (cardinal A) (λ _, cardinal A)) A)
    { refine well_ord_cardinal_eqE (Sigma (cardinal A) (λ _, cardinal A))
        (rmult (cardinal A) (Memrel (cardinal A))
               (cardinal A) (Memrel (cardinal A))) A r hwoc hwo hcc };
  refine eqpoll_trans (Sigma A (λ _, A))
    (Sigma (cardinal A) (λ _, cardinal A)) A he2 he3
end;

opaque symbol InfCard_square_eqpoll (K : τ ι) :
  π (InfCard K) → π (eqpoll (Sigma K (λ _, K)) K) ≔
begin
  assume K hIK;
  have hCK : π (Card K) { refine InfCard_is_Card K hIK };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  refine well_ord_InfCard_square_eq K (Memrel K) (well_ord_Memrel K hOK) _;
  refine ind_eq (Card_cardinal_eq K hCK) (λ w, InfCard w) hIK
end;

opaque symbol Inf_Card_is_InfCard (i : τ ι) :
  π (Card i) → π (¬ (Finite i)) → π (InfCard i) ≔
begin
  assume i hCi hnF;
  rewrite InfCard_def;
  refine ∧ᵢ hCi (nat_le_infinite_Ord i (Card_is_Ord i hCi) hnF)
end;

// Toward's Kunen's Corollary 10.13 (1)

opaque symbol InfCard_le_cmult_eq (K L : τ ι) :
  π (InfCard K) → π (le L K) → π (lt empty L) → π (cmult K L = K) ≔
begin
  assume K L hIK hLK h0L;
  have hCK : π (Card K) { refine InfCard_is_Card K hIK };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  have hOL : π (Ord L) { refine lt_Ord L (succ K) hLK };
  have h1 : π (le (cmult K L) (cmult K K))
    { refine cmult_le_mono K K L K (le_refl K hOK) hLK };
  have h2 : π (le (cmult K L) K)
    { refine ind_eq (eq_sym (InfCard_csquare_eq K hIK))
        (λ w, le (cmult K L) w) h1 };
  refine le_anti_sym (cmult K L) K h2 (cmult_le_self K L hCK hOL h0L)
end;

// Corollary 10.13 (1), for cardinal multiplication
opaque symbol InfCard_cmult_eq (K L : τ ι) :
  π (InfCard K) → π (InfCard L) → π (cmult K L = Un K L) ≔
begin
  assume K L hIK hIL;
  have hOK : π (Ord K) { refine Card_is_Ord K (InfCard_is_Card K hIK) };
  have hOL : π (Ord L) { refine Card_is_Ord L (InfCard_is_Card L hIL) };
  have h0K : π (lt empty K) { refine Limit_has_0 K (InfCard_is_Limit K hIK) };
  have h0L : π (lt empty L) { refine Limit_has_0 L (InfCard_is_Limit L hIL) };
  refine ∨ₑ (Ord_linear K L hOK hOL) _ _
  { assume hKL;
    have hleKL : π (le K L) { refine leI K L hKL hOL };
    have hcm : π (cmult L K = L) { refine InfCard_le_cmult_eq L K hIL hleKL h0K };
    have hUn : π (Un K L = L)
      { refine subset_antisym (Un K L) L
          (Un_least K L L (le_imp_subset K L hleKL) (subset_refl L))
          (Un_upper2 K L) };
    rewrite (cmult_commute K L); rewrite hcm; rewrite hUn; reflexivity }
  { assume hd;
    refine ∨ₑ hd _ _
    { assume heqKL;
      rewrite left heqKL;
      rewrite (InfCard_csquare_eq K hIK);
      rewrite Un_absorb; reflexivity }
    { assume hLK;
      have hleLK : π (le L K) { refine leI L K hLK hOK };
      have hcm : π (cmult K L = K)
        { refine InfCard_le_cmult_eq K L hIK hleLK h0L };
      have hUn : π (Un K L = K)
        { refine subset_antisym (Un K L) K
            (Un_least K L K (subset_refl K) (le_imp_subset L K hleLK))
            (Un_upper1 K L) };
      rewrite hcm; rewrite hUn; reflexivity } }
end;

opaque symbol InfCard_cdouble_eq (K : τ ι) :
  π (InfCard K) → π (cadd K K = K) ≔
begin
  assume K hIK;
  have hCK : π (Card K) { refine InfCard_is_Card K hIK };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  have hnatK : π (le omega K)
    { refine ∧ₑ₂ (ind_eq (eq_sym (InfCard_def K)) (λ q, q) hIK) };
  have h2m : π (cmult (succ (succ empty)) K = cadd K K) { refine cmult_2 K hCK };
  have h2K : π (le (succ (succ empty)) K)
    { have hlt : π (lt (succ (succ empty)) K)
        { refine lt_trans2 (succ (succ empty)) omega K
            (ltI (succ (succ empty)) omega nat_2I Ord_omega) hnatK };
      refine leI (succ (succ empty)) K (ltD (succ (succ empty)) K hlt) hOK };
  have h02 : π (lt empty (succ (succ empty)))
    { refine ltI empty (succ (succ empty))
        (succI2 empty (succ empty) (succI1 empty))
        (Ord_succ (succ empty) (Ord_succ empty Ord_0)) };
  have hKcomm : π (cmult K (succ (succ empty)) = cmult (succ (succ empty)) K)
    { refine cmult_commute K (succ (succ empty)) };
  have hcm : π (cmult K (succ (succ empty)) = K)
    { refine InfCard_le_cmult_eq K (succ (succ empty)) hIK h2K h02 };
  refine eq_trans (eq_sym h2m) (eq_trans (eq_sym hKcomm) hcm)
end;

// Corollary 10.13 (1), for cardinal addition
opaque symbol InfCard_le_cadd_eq (K L : τ ι) :
  π (InfCard K) → π (le L K) → π (cadd K L = K) ≔
begin
  assume K L hIK hLK;
  have hCK : π (Card K) { refine InfCard_is_Card K hIK };
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  have hOL : π (Ord L) { refine lt_Ord L (succ K) hLK };
  have h1 : π (le (cadd K L) (cadd K K))
    { refine cadd_le_mono K K L K (le_refl K hOK) hLK };
  have h2 : π (le (cadd K L) K)
    { refine ind_eq (eq_sym (InfCard_cdouble_eq K hIK))
        (λ w, le (cadd K L) w) h1 };
  refine le_anti_sym (cadd K L) K h2 (cadd_le_self K L hCK hOL)
end;

opaque symbol InfCard_cadd_eq (K L : τ ι) :
  π (InfCard K) → π (InfCard L) → π (cadd K L = Un K L) ≔
begin
  assume K L hIK hIL;
  have hOK : π (Ord K) { refine Card_is_Ord K (InfCard_is_Card K hIK) };
  have hOL : π (Ord L) { refine Card_is_Ord L (InfCard_is_Card L hIL) };
  refine ∨ₑ (Ord_linear K L hOK hOL) _ _
  { assume hKL;
    have hleKL : π (le K L) { refine leI K L hKL hOL };
    have hcm : π (cadd L K = L) { refine InfCard_le_cadd_eq L K hIL hleKL };
    have hUn : π (Un K L = L)
      { refine subset_antisym (Un K L) L
          (Un_least K L L (le_imp_subset K L hleKL) (subset_refl L))
          (Un_upper2 K L) };
    rewrite (cadd_commute K L); rewrite hcm; rewrite hUn; reflexivity }
  { assume hd;
    refine ∨ₑ hd _ _
    { assume heqKL;
      rewrite left heqKL;
      rewrite (InfCard_cdouble_eq K hIK);
      rewrite Un_absorb; reflexivity }
    { assume hLK;
      have hleLK : π (le L K) { refine leI L K hLK hOK };
      have hcm : π (cadd K L = K)
        { refine InfCard_le_cadd_eq K L hIK hleLK };
      have hUn : π (Un K L = K)
        { refine subset_antisym (Un K L) K
            (Un_least K L K (subset_refl K) (le_imp_subset L K hleLK))
            (Un_upper1 K L) };
      rewrite hcm; rewrite hUn; reflexivity } }
end;

// The other part, Corollary 10.13 (2), refers to the cardinality of the set
// of all n-tuples of elements of K. A better version for the Isabelle theory
// might be InfCard(K) ⟹ |list(K)| = K.  (No statement to port — remark only.)

// ===========================================================================
// For Every Cardinal Number There Exists A Greater One
// ===========================================================================

// This result is Kunen's Theorem 10.16, which would be trivial using AC

// Private copy of jump_cardinal_iff, needed already for Ord_jump_cardinal
// (Isabelle proves Ord_jump_cardinal by direct unfolding; we factor the
// unfolding once and reuse it — the public lemma below just cites this).
private opaque symbol priv_jump_cardinal_iff (i K : τ ι) :
  π (i ∈ jump_cardinal K ⇔
     (`∃ (r : τ ι), `∃ (X : τ ι),
        r ⊆ Sigma K (λ _, K) ∧ X ⊆ K ∧ well_ord X r ∧ i = ordertype X r)) ≔
begin
  assume i K;
  rewrite jump_cardinal_def;
  apply ∧ᵢ
  { assume hmem;
    refine ∃ₑ (UnionE i (RepFun (Pow K) (λ X,
      RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
             (λ r, ordertype X r))) hmem) _;
    assume S hS;
    have hSm : π (S ∈ RepFun (Pow K) (λ X,
      RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
             (λ r, ordertype X r))) { refine ∧ₑ₁ hS };
    have hiS : π (i ∈ S) { refine ∧ₑ₂ hS };
    refine ∃ₑ (∧ₑ₁ (RepFun_iff S (Pow K) (λ X,
      RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
             (λ r, ordertype X r))) hSm) _;
    assume X hX;
    have hXP : π (X ∈ Pow K) { refine ∧ₑ₁ hX };
    have hSeq : π (S = RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
                       (λ r, ordertype X r)) { refine ∧ₑ₂ hX };
    have hiF : π (i ∈ RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
                      (λ r, ordertype X r))
      { refine ind_eq (eq_sym hSeq) (λ w, i ∈ w) hiS };
    refine ∃ₑ (∧ₑ₁ (RepFun_iff i
      (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
      (λ r, ordertype X r)) hiF) _;
    assume r hr;
    have hrC : π (r ∈ Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
      { refine ∧ₑ₁ hr };
    refine ∃ᵢ r (∃ᵢ X (∧ᵢ
      (PowD r (Sigma K (λ _, K))
         (CollectD1 r (Pow (Sigma K (λ _, K))) (λ r, well_ord X r) hrC))
      (∧ᵢ (PowD X K hXP)
          (∧ᵢ (CollectD2 r (Pow (Sigma K (λ _, K))) (λ r, well_ord X r) hrC)
              (∧ₑ₂ hr))))) }
  { assume hex;
    refine ∃ₑ hex _; assume r hr1;
    refine ∃ₑ hr1 _; assume X hX1;
    have hrsub : π (r ⊆ Sigma K (λ _, K)) { refine ∧ₑ₁ hX1 };
    have hXsub : π (X ⊆ K) { refine ∧ₑ₁ (∧ₑ₂ hX1) };
    have hwo : π (well_ord X r) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hX1)) };
    have hieq : π (i = ordertype X r) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hX1)) };
    have hoF : π (ordertype X r ∈
        RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
               (λ r, ordertype X r))
      { refine RepFunI r (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
          (λ r, ordertype X r)
          (CollectI r (Pow (Sigma K (λ _, K))) (λ r, well_ord X r)
             (PowI r (Sigma K (λ _, K)) hrsub) hwo) };
    have hiF : π (i ∈ RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
                      (λ r, ordertype X r))
      { refine ind_eq hieq (λ w, w ∈
          RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
                 (λ r, ordertype X r)) hoF };
    refine UnionI i
      (RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
              (λ r, ordertype X r))
      (RepFun (Pow K) (λ X,
         RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
                (λ r, ordertype X r)))
      hiF
      (RepFunI X (Pow K) (λ X,
         RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
                (λ r, ordertype X r)) (PowI X K hXsub)) }
end;

opaque symbol Ord_jump_cardinal (K : τ ι) :
  π (Ord (jump_cardinal K)) ≔
begin
  assume K;
  refine OrdI (jump_cardinal K) _ _
  { refine TranssetI (jump_cardinal K) _;
    assume i hi;
    assume j hj;
    refine ∃ₑ (∧ₑ₁ (priv_jump_cardinal_iff i K) hi) _; assume r hr1;
    refine ∃ₑ hr1 _; assume X hX1;
    have hrsub : π (r ⊆ Sigma K (λ _, K)) { refine ∧ₑ₁ hX1 };
    have hXsub : π (X ⊆ K) { refine ∧ₑ₁ (∧ₑ₂ hX1) };
    have hwoXr : π (well_ord X r) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hX1)) };
    have hieq : π (i = ordertype X r) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hX1)) };
    have hjot : π (j ∈ ordertype X r)
      { refine ind_eq (eq_sym hieq) (λ w, j ∈ w) hj };
    have hunf : π (ordertype X r = RepFun X (λ x, ordertype (ZF.Order.pred X x r) r))
      { refine ordertype_pred_unfold X r hwoXr };
    have hjRF : π (j ∈ RepFun X (λ x, ordertype (ZF.Order.pred X x r) r))
      { refine ind_eq (eq_sym hunf) (λ w, j ∈ w) hjot };
    refine ∃ₑ (∧ₑ₁ (RepFun_iff j X (λ x, ordertype (ZF.Order.pred X x r) r)) hjRF) _;
    assume x hx;
    refine ∧ₑ₂ (priv_jump_cardinal_iff j K) _;
    refine ∃ᵢ r (∃ᵢ (ZF.Order.pred X x r) (∧ᵢ hrsub (∧ᵢ _ (∧ᵢ _ (∧ₑ₂ hx)))))
    { refine subset_trans (ZF.Order.pred X x r) X K (pred_subset X x r) hXsub }
    { refine well_ord_subset X (ZF.Order.pred X x r) r hwoXr (pred_subset X x r) } }
  { assume x hx;
    refine ∃ₑ (∧ₑ₁ (priv_jump_cardinal_iff x K) hx) _; assume r hr1;
    refine ∃ₑ hr1 _; assume X hX1;
    have hwoXr : π (well_ord X r) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hX1)) };
    have hxeq : π (x = ordertype X r) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hX1)) };
    refine Ord_is_Transset x
      (ind_eq hxeq (λ w, Ord w) (Ord_ordertype X r hwoXr)) }
end;

// Allows selective unfolding. Less work than deriving intro/elim rules
opaque symbol jump_cardinal_iff (i K : τ ι) :
  π (i ∈ jump_cardinal K ⇔
     (`∃ (r : τ ι), `∃ (X : τ ι),
        r ⊆ Sigma K (λ _, K) ∧ X ⊆ K ∧ well_ord X r ∧ i = ordertype X r)) ≔
begin
  assume i K;
  refine priv_jump_cardinal_iff i K
end;

// The easy part of Theorem 10.16: jump_cardinal(K) exceeds K
opaque symbol K_lt_jump_cardinal (K : τ ι) :
  π (Ord K) → π (lt K (jump_cardinal K)) ≔
begin
  assume K hOK;
  refine ltI K (jump_cardinal K) _ (Ord_jump_cardinal K);
  refine ∧ₑ₂ (jump_cardinal_iff K K) _;
  refine ∃ᵢ (Memrel K) (∃ᵢ K (∧ᵢ (Memrel_type K)
    (∧ᵢ (subset_refl K)
        (∧ᵢ (well_ord_Memrel K hOK) (eq_sym (ordertype_Memrel K hOK))))))
end;

// The proof by contradiction: the bijection f yields a wellordering of X
// whose ordertype is jump_cardinal(K).
// (Isabelle composes f with ordermap(X,r); we avoid composition machinery by
// pulling Memrel(jump_cardinal K) back twice, through f and then ordermap.)
opaque symbol Card_jump_cardinal_lemma (X r K f : τ ι) :
  π (well_ord X r) → π (r ⊆ Sigma K (λ _, K)) → π (X ⊆ K) →
  π (f ∈ bij (ordertype X r) (jump_cardinal K)) →
  π (jump_cardinal K ∈ jump_cardinal K) ≔
begin
  assume X r K f hwo hrsub hXsub hbij;
  have hOjc : π (Ord (jump_cardinal K)) { refine Ord_jump_cardinal K };
  have hwoM : π (well_ord (jump_cardinal K) (Memrel (jump_cardinal K)))
    { refine well_ord_Memrel (jump_cardinal K) hOjc };
  have hfinj : π (f ∈ inj (ordertype X r) (jump_cardinal K))
    { refine bij_is_inj f (ordertype X r) (jump_cardinal K) hbij };
  have hwo1 : π (well_ord (ordertype X r)
                   (rvimage (ordertype X r) f (Memrel (jump_cardinal K))))
    { refine well_ord_rvimage (ordertype X r) (jump_cardinal K) f
        (Memrel (jump_cardinal K)) hfinj hwoM };
  have hot1 : π (ordertype (ordertype X r)
                   (rvimage (ordertype X r) f (Memrel (jump_cardinal K)))
                 = ordertype (jump_cardinal K) (Memrel (jump_cardinal K)))
    { refine bij_ordertype_vimage f (ordertype X r) (jump_cardinal K)
        (Memrel (jump_cardinal K)) hbij hwoM };
  have hotM : π (ordertype (jump_cardinal K) (Memrel (jump_cardinal K))
                 = jump_cardinal K)
    { refine ordertype_Memrel (jump_cardinal K) hOjc };
  have hgbij : π (ordermap X r ∈ bij X (ordertype X r))
    { refine ordermap_bij X r hwo };
  have hginj : π (ordermap X r ∈ inj X (ordertype X r))
    { refine bij_is_inj (ordermap X r) X (ordertype X r) hgbij };
  have hwo2 : π (well_ord X (rvimage X (ordermap X r)
                   (rvimage (ordertype X r) f (Memrel (jump_cardinal K)))))
    { refine well_ord_rvimage X (ordertype X r) (ordermap X r)
        (rvimage (ordertype X r) f (Memrel (jump_cardinal K))) hginj hwo1 };
  have hot2 : π (ordertype X (rvimage X (ordermap X r)
                   (rvimage (ordertype X r) f (Memrel (jump_cardinal K))))
                 = ordertype (ordertype X r)
                     (rvimage (ordertype X r) f (Memrel (jump_cardinal K))))
    { refine bij_ordertype_vimage (ordermap X r) X (ordertype X r)
        (rvimage (ordertype X r) f (Memrel (jump_cardinal K))) hgbij hwo1 };
  have hr2sub : π (rvimage X (ordermap X r)
                     (rvimage (ordertype X r) f (Memrel (jump_cardinal K)))
                   ⊆ Sigma K (λ _, K))
    { refine subset_trans
        (rvimage X (ordermap X r)
           (rvimage (ordertype X r) f (Memrel (jump_cardinal K))))
        (Sigma X (λ _, X)) (Sigma K (λ _, K))
        (rvimage_type X (ordermap X r)
           (rvimage (ordertype X r) f (Memrel (jump_cardinal K)))) _;
      assume p hp;
      refine ind_eq (eq_sym (Pair_fst_snd p X (λ _, X) hp))
        (λ w, w ∈ Sigma K (λ _, K))
        (SigmaI (fst p) (snd p) K (λ _, K)
           (hXsub (fst p) (SigmaD1 p X (λ _, X) hp))
           (hXsub (snd p) (SigmaD2 p X (λ _, X) hp))) };
  refine ∧ₑ₂ (jump_cardinal_iff (jump_cardinal K) K) _;
  refine ∃ᵢ (rvimage X (ordermap X r)
              (rvimage (ordertype X r) f (Memrel (jump_cardinal K))))
    (∃ᵢ X (∧ᵢ hr2sub (∧ᵢ hXsub (∧ᵢ hwo2
      (eq_sym (eq_trans hot2 (eq_trans hot1 hotM)))))))
end;

// The hard part of Theorem 10.16: jump_cardinal(K) is itself a cardinal
opaque symbol Card_jump_cardinal (K : τ ι) :
  π (Card (jump_cardinal K)) ≔
begin
  assume K;
  refine CardI (jump_cardinal K) (Ord_jump_cardinal K) _;
  assume j hj heqp;
  have hjm : π (j ∈ jump_cardinal K) { refine ltD j (jump_cardinal K) hj };
  refine ∃ₑ (∧ₑ₁ (jump_cardinal_iff j K) hjm) _; assume r hr1;
  refine ∃ₑ hr1 _; assume X hX1;
  have hrsub : π (r ⊆ Sigma K (λ _, K)) { refine ∧ₑ₁ hX1 };
  have hXsub : π (X ⊆ K) { refine ∧ₑ₁ (∧ₑ₂ hX1) };
  have hwoXr : π (well_ord X r) { refine ∧ₑ₁ (∧ₑ₂ (∧ₑ₂ hX1)) };
  have hjeq : π (j = ordertype X r) { refine ∧ₑ₂ (∧ₑ₂ (∧ₑ₂ hX1)) };
  have heqp' : π (`∃ (f : τ ι), f ∈ bij j (jump_cardinal K))
    { refine ind_eq (eq_sym (eqpoll_def j (jump_cardinal K))) (λ p, p) heqp };
  refine ∃ₑ heqp' _; assume f hf;
  have hf' : π (f ∈ bij (ordertype X r) (jump_cardinal K))
    { refine ind_eq (eq_sym hjeq) (λ w, f ∈ bij w (jump_cardinal K)) hf };
  refine mem_irrefl (jump_cardinal K)
    (Card_jump_cardinal_lemma X r K f hwoXr hrsub hXsub hf')
end;

// ===========================================================================
// Basic Properties of Successor Cardinals
// ===========================================================================

opaque symbol csucc_basic (K : τ ι) :
  π (Ord K) → π (Card (csucc K) ∧ lt K (csucc K)) ≔
begin
  assume K hOK;
  rewrite csucc_def;
  refine LeastI (λ L, Card L ∧ lt K L) (jump_cardinal K)
    (∧ᵢ (Card_jump_cardinal K) (K_lt_jump_cardinal K hOK)) (Ord_jump_cardinal K)
end;

// Card_csucc = csucc_basic [THEN conjunct1] : Ord(K) ⟹ Card(csucc(K))
opaque symbol Card_csucc (K : τ ι) :
  π (Ord K) → π (Card (csucc K)) ≔
begin
  assume K hOK; refine ∧ₑ₁ (csucc_basic K hOK)
end;

// lt_csucc = csucc_basic [THEN conjunct2] : Ord(K) ⟹ K < csucc(K)
opaque symbol lt_csucc (K : τ ι) :
  π (Ord K) → π (lt K (csucc K)) ≔
begin
  assume K hOK; refine ∧ₑ₂ (csucc_basic K hOK)
end;

opaque symbol Ord_0_lt_csucc (K : τ ι) :
  π (Ord K) → π (lt empty (csucc K)) ≔
begin
  assume K hOK;
  refine lt_trans1 empty K (csucc K) (Ord_0_le K hOK) (lt_csucc K hOK)
end;

opaque symbol csucc_le (K L : τ ι) :
  π (Card L) → π (lt K L) → π (le (csucc K) L) ≔
begin
  assume K L hCL hKL;
  rewrite csucc_def;
  refine Least_le (λ L', Card L' ∧ lt K L') L (∧ᵢ hCL hKL) (Card_is_Ord L hCL)
end;

opaque symbol lt_csucc_iff (i K : τ ι) :
  π (Ord i) → π (Card K) → π (lt i (csucc K) ⇔ le (cardinal i) K) ≔
begin
  assume i K hOi hCK;
  have hOK : π (Ord K) { refine Card_is_Ord K hCK };
  apply ∧ᵢ
  { assume hi;
    have hnot : π (¬ (lt K (cardinal i)))
      { assume hKlt;
        have hcs : π (le (csucc K) (cardinal i))
          { refine csucc_le K (cardinal i) (Card_cardinal i) hKlt };
        have hci : π (le (cardinal i) i) { refine Ord_cardinal_le i hOi };
        have h1 : π (le (csucc K) i)
          { refine le_trans (csucc K) (cardinal i) i hcs hci };
        refine lt_irrefl i (lt_trans2 i (csucc K) i hi h1) };
    refine not_lt_imp_le K (cardinal i) hOK (Ord_cardinal i) hnot }
  { assume hle;
    refine Card_lt_imp_lt i (csucc K)
      (lt_trans1 (cardinal i) K (csucc K) hle (lt_csucc K hOK))
      hOi (Card_csucc K hOK) }
end;

opaque symbol Card_lt_csucc_iff (K' K : τ ι) :
  π (Card K') → π (Card K) → π (lt K' (csucc K) ⇔ le K' K) ≔
begin
  assume K' K hCK' hCK;
  have hiff : π (lt K' (csucc K) ⇔ le (cardinal K') K)
    { refine lt_csucc_iff K' K (Card_is_Ord K' hCK') hCK };
  refine ind_eq (eq_sym (Card_cardinal_eq K' hCK'))
    (λ w, lt K' (csucc K) ⇔ le w K) hiff
end;

opaque symbol InfCard_csucc (K : τ ι) :
  π (InfCard K) → π (InfCard (csucc K)) ≔
begin
  assume K hIK;
  have h' : π (Card K ∧ le omega K)
    { refine ind_eq (eq_sym (InfCard_def K)) (λ p, p) hIK };
  have hOK : π (Ord K) { refine Card_is_Ord K (∧ₑ₁ h') };
  rewrite InfCard_def;
  refine ∧ᵢ (Card_csucc K hOK) _;
  have hlt : π (lt K (csucc K)) { refine lt_csucc K hOK };
  have hKcs : π (le K (csucc K))
    { refine leI K (csucc K) (ltD K (csucc K) hlt) (lt_Ord2 K (csucc K) hlt) };
  refine le_trans omega K (csucc K) (∧ₑ₂ h') hKcs
end;

// ===========================================================================
// Removing elements from a finite set decreases its cardinality
// ===========================================================================

// Port-internal helper (Isabelle upair.cons_commute).
private opaque symbol priv_cons_commute (a b A : τ ι) :
  π (cons a (cons b A) = cons b (cons a A)) ≔
begin
  assume a b A;
  refine equality_iffI (cons a (cons b A)) (cons b (cons a A)) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z a (cons b A)) hz) _ _
    { assume hza;
      refine consI2 z b (cons a A)
        (ind_eq hza (λ w, w ∈ cons a A) (consI1 a A)) }
    { assume hzbA;
      refine ∨ₑ (∧ₑ₁ (cons_iff z b A) hzbA) _ _
      { assume hzb;
        refine ind_eq hzb (λ w, w ∈ cons b (cons a A)) (consI1 b (cons a A)) }
      { assume hzA; refine consI2 z b (cons a A) (consI2 z a A hzA) } } }
  { assume hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z b (cons a A)) hz) _ _
    { assume hzb;
      refine consI2 z a (cons b A)
        (ind_eq hzb (λ w, w ∈ cons b A) (consI1 b A)) }
    { assume hzaA;
      refine ∨ₑ (∧ₑ₁ (cons_iff z a A) hzaA) _ _
      { assume hza;
        refine ind_eq hza (λ w, w ∈ cons a (cons b A)) (consI1 a (cons b A)) }
      { assume hzA; refine consI2 z a (cons b A) (consI2 z b A hzA) } } }
end;

// Port-internal: the inner induction of Isabelle's Finite_imp_cardinal_cons —
// a finite set cannot absorb a fresh element: Finite(X) → a∉X → cons(a,X)≲X → ⊥.
private opaque symbol priv_cons_lepoll_False (a X : τ ι) :
  π (Finite X) → π (a ∉ X) → π (lepoll (cons a X) X) → π ⊥ ≔
begin
  assume a X hFX;
  refine Finite_induct X (λ Y, (a ∉ Y) ⇒ (lepoll (cons a Y) Y ⇒ ⊥)) hFX _ _
  { assume hna hlep;
    have h0 : π (cons a empty = empty)
      { refine lepoll_0_is_0 (cons a empty) hlep };
    refine emptyE a (ind_eq (eq_sym h0) (λ w, a ∈ w) (consI1 a empty)) }
  { assume x B hFB hnxB IH;
    assume hna hlep;
    have hnaB : π (a ∉ B) { assume haB; refine hna (consI2 a x B haB) };
    have hax : π (¬ (a = x))
      { assume hax;
        refine hna (ind_eq hax (λ w, w ∈ cons x B) (consI1 x B)) };
    have hlep2 : π (lepoll (cons x (cons a B)) (cons x B))
      { refine ind_eq (eq_sym (priv_cons_commute a x B))
          (λ w, lepoll w (cons x B)) hlep };
    have hxnaB : π (x ∉ cons a B)
      { assume hx;
        refine ∨ₑ (∧ₑ₁ (cons_iff x a B) hx) _ _
        { assume hxa; refine hax (eq_sym hxa) }
        { assume hxB; refine hnxB hxB } };
    refine IH hnaB (cons_lepoll_consD x (cons a B) x B hlep2 hxnaB hnxB) }
end;

opaque symbol Finite_imp_cardinal_cons (A a : τ ι) :
  π (Finite A) → π (a ∉ A) → π (cardinal (cons a A) = succ (cardinal A)) ≔
begin
  assume A a hFA hna;
  have hAeq : π (eqpoll (cardinal A) A)
    { refine ∃ₑ (Finite_imp_well_ord A hFA) _; assume r hr;
      refine well_ord_cardinal_eqpoll A r hr };
  have hLeast : π (Least (λ i, eqpoll i (cons a A)) = succ (cardinal A))
    { refine Least_equality (λ i, eqpoll i (cons a A)) (succ (cardinal A)) _ _ _
      { rewrite succ_def;
        refine cons_eqpoll_cong (cardinal A) A (cardinal A) a hAeq
          (mem_irrefl (cardinal A)) hna }
      { refine Ord_succ (cardinal A) (Ord_cardinal A) }
      { assume j hj heqj;
        have hlep : π (lepoll (cons a A) A)
          { refine lepoll_eq_trans (cons a A) (cardinal A) A _ hAeq;
            refine eq_lepoll_trans (cons a A) j (cardinal A)
              (eqpoll_sym j (cons a A) heqj)
              (le_imp_lepoll j (cardinal A) hj) };
        refine priv_cons_lepoll_False a A hFA hna hlep } };
  refine eq_trans (cardinal_def (cons a A)) hLeast
end;

// Port-internal helper (Isabelle upair.cons_Diff): a∈A → cons(a, A-{a}) = A.
private opaque symbol priv_cons_Diff (a A : τ ι) :
  π (a ∈ A) → π (cons a (Diff A (singleton a)) = A) ≔
begin
  assume a A ha;
  refine equality_iffI (cons a (Diff A (singleton a))) A _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z a (Diff A (singleton a))) hz) _ _
    { assume hza; refine ind_eq hza (λ w, w ∈ A) ha }
    { assume hzD; refine DiffD1 z A (singleton a) hzD } }
  { assume hzA;
    refine ∨ₑ (em (z = a)) _ _
    { assume hza;
      refine ind_eq hza (λ w, w ∈ cons a (Diff A (singleton a)))
        (consI1 a (Diff A (singleton a))) }
    { assume hnza;
      refine consI2 z a (Diff A (singleton a)) (DiffI z A (singleton a) hzA _);
      assume hzs; refine hnza (∧ₑ₁ (singleton_iff z a) hzs) } }
end;

opaque symbol Finite_imp_succ_cardinal_Diff (A a : τ ι) :
  π (Finite A) → π (a ∈ A) →
  π (succ (cardinal (Diff A (singleton a))) = cardinal A) ≔
begin
  assume A a hFA ha;
  have hFD : π (Finite (Diff A (singleton a)))
    { refine subset_Finite (Diff A (singleton a)) A _ hFA;
      assume z hz; refine DiffD1 z A (singleton a) hz };
  have hnaD : π (a ∉ Diff A (singleton a))
    { assume haD; refine DiffD2 a A (singleton a) haD (singletonI a) };
  have hcc : π (cardinal (cons a (Diff A (singleton a)))
                = succ (cardinal (Diff A (singleton a))))
    { refine Finite_imp_cardinal_cons (Diff A (singleton a)) a hFD hnaD };
  refine eq_trans (eq_sym hcc) (feq cardinal (priv_cons_Diff a A ha))
end;

opaque symbol Finite_imp_cardinal_Diff (A a : τ ι) :
  π (Finite A) → π (a ∈ A) → π (lt (cardinal (Diff A (singleton a))) (cardinal A)) ≔
begin
  assume A a hFA ha;
  have hsc : π (succ (cardinal (Diff A (singleton a))) = cardinal A)
    { refine Finite_imp_succ_cardinal_Diff A a hFA ha };
  refine ltI (cardinal (Diff A (singleton a))) (cardinal A) _ (Ord_cardinal A);
  refine ind_eq (eq_sym hsc) (λ w, cardinal (Diff A (singleton a)) ∈ w)
    (succI1 (cardinal (Diff A (singleton a))))
end;

opaque symbol Finite_cardinal_in_nat (A : τ ι) :
  π (Finite A) → π (cardinal A ∈ omega) ≔
begin
  assume A hFA;
  refine Finite_induct A (λ B, cardinal B ∈ omega) hFA _ _
  { refine ind_eq cardinal_0 (λ w, w ∈ omega) zero_in_omega }
  { assume x B hFB hnxB IH;
    refine ind_eq (Finite_imp_cardinal_cons B x hFB hnxB) (λ w, w ∈ omega)
      (succ_in_omega (cardinal B) IH) }
end;

// Port-internal helpers (Isabelle equalities: Un_cons, cons_absorb,
// Int_cons_left — the latter split into its two cases).
private opaque symbol priv_Un_cons (x A B : τ ι) :
  π (Un (cons x A) B = cons x (Un A B)) ≔
begin
  assume x A B;
  refine equality_iffI (Un (cons x A) B) (cons x (Un A B)) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∨ₑ (UnE z (cons x A) B hz) _ _
    { assume hzc;
      refine ∨ₑ (∧ₑ₁ (cons_iff z x A) hzc) _ _
      { assume hzx;
        refine ind_eq hzx (λ w, w ∈ cons x (Un A B)) (consI1 x (Un A B)) }
      { assume hzA; refine consI2 z x (Un A B) (UnI1 z A B hzA) } }
    { assume hzB; refine consI2 z x (Un A B) (UnI2 z A B hzB) } }
  { assume hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z x (Un A B)) hz) _ _
    { assume hzx;
      refine UnI1 z (cons x A) B
        (ind_eq hzx (λ w, w ∈ cons x A) (consI1 x A)) }
    { assume hzU;
      refine ∨ₑ (UnE z A B hzU) _ _
      { assume hzA; refine UnI1 z (cons x A) B (consI2 z x A hzA) }
      { assume hzB; refine UnI2 z (cons x A) B hzB } } }
end;

private opaque symbol priv_cons_absorb (x B : τ ι) :
  π (x ∈ B) → π (cons x B = B) ≔
begin
  assume x B hx;
  refine equality_iffI (cons x B) B _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z x B) hz) _ _
    { assume hzx; refine ind_eq hzx (λ w, w ∈ B) hx }
    { assume hzB; refine hzB } }
  { assume hzB; refine consI2 z x B hzB }
end;

private opaque symbol priv_Int_cons_in (x A B : τ ι) :
  π (x ∈ B) → π (Int (cons x A) B = cons x (Int A B)) ≔
begin
  assume x A B hxB;
  refine equality_iffI (Int (cons x A) B) (cons x (Int A B)) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z x A) (IntD1 z (cons x A) B hz)) _ _
    { assume hzx;
      refine ind_eq hzx (λ w, w ∈ cons x (Int A B)) (consI1 x (Int A B)) }
    { assume hzA;
      refine consI2 z x (Int A B) (IntI z A B hzA (IntD2 z (cons x A) B hz)) } }
  { assume hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z x (Int A B)) hz) _ _
    { assume hzx;
      refine ind_eq hzx (λ w, w ∈ Int (cons x A) B)
        (IntI x (cons x A) B (consI1 x A) hxB) }
    { assume hzI;
      refine IntI z (cons x A) B (consI2 z x A (IntD1 z A B hzI))
        (IntD2 z A B hzI) } }
end;

private opaque symbol priv_Int_cons_out (x A B : τ ι) :
  π (x ∉ B) → π (Int (cons x A) B = Int A B) ≔
begin
  assume x A B hxnB;
  refine equality_iffI (Int (cons x A) B) (Int A B) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∨ₑ (∧ₑ₁ (cons_iff z x A) (IntD1 z (cons x A) B hz)) _ _
    { assume hzx;
      refine ⊥ₑ (hxnB (ind_eq (eq_sym hzx) (λ w, w ∈ B)
        (IntD2 z (cons x A) B hz))) }
    { assume hzA; refine IntI z A B hzA (IntD2 z (cons x A) B hz) } }
  { assume hz;
    refine IntI z (cons x A) B (consI2 z x A (IntD1 z A B hz)) (IntD2 z A B hz) }
end;

opaque symbol card_Un_Int (A B : τ ι) :
  π (Finite A) → π (Finite B) →
  π (add (cardinal A) (cardinal B) = add (cardinal (Un A B)) (cardinal (Int A B))) ≔
begin
  assume A B hFA hFB;
  refine Finite_induct A
    (λ C, add (cardinal C) (cardinal B) = add (cardinal (Un C B)) (cardinal (Int C B)))
    hFA _ _
  { try simplify rule off;
    have hUn0 : π (Un empty B = B) { refine Un_empty_left B };
    have hInt0 : π (Int empty B = empty)
      { refine equals0I (Int empty B) _;
        assume z hz; refine emptyE z (IntD1 z empty B hz) };
    rewrite hUn0; rewrite hInt0; rewrite cardinal_0;
    rewrite (add_0 (cardinal B) (Finite_cardinal_in_nat B hFB));
    rewrite (add_0_right (cardinal B) (Finite_cardinal_in_nat B hFB));
    reflexivity }
  { assume x C hFC hnxC IH;
    try simplify rule off;
    have hcc : π (cardinal (cons x C) = succ (cardinal C))
      { refine Finite_imp_cardinal_cons C x hFC hnxC };
    rewrite hcc;
    rewrite (priv_Un_cons x C B);
    refine ∨ₑ (em (x ∈ B)) _ _
    { assume hxB;
      rewrite (priv_Int_cons_in x C B hxB);
      rewrite (priv_cons_absorb x (Un C B) (UnI2 x C B hxB));
      have hxnI : π (x ∉ Int C B) { assume hxI; refine hnxC (IntD1 x C B hxI) };
      have hFI : π (Finite (Int C B)) { refine Finite_Int C B (∨ᵢ₁ hFC) };
      rewrite (Finite_imp_cardinal_cons (Int C B) x hFI hxnI);
      rewrite add_succ; rewrite add_succ_right;
      rewrite IH; reflexivity }
    { assume hxnB;
      rewrite (priv_Int_cons_out x C B hxnB);
      have hxnU : π (x ∉ Un C B)
        { assume hxU;
          refine ∨ₑ (UnE x C B hxU) _ _
          { assume h; refine hnxC h }
          { assume h; refine hxnB h } };
      have hFU : π (Finite (Un C B)) { refine Finite_Un C B hFC hFB };
      rewrite (Finite_imp_cardinal_cons (Un C B) x hFU hxnU);
      rewrite add_succ; rewrite add_succ;
      rewrite IH; reflexivity } }
end;

opaque symbol card_Un_disjoint (A B : τ ι) :
  π (Finite A) → π (Finite B) → π (Int A B = empty) →
  π (cardinal (Un A B) = add (cardinal A) (cardinal B)) ≔
begin
  assume A B hFA hFB hdis;
  have h1 : π (add (cardinal A) (cardinal B)
               = add (cardinal (Un A B)) (cardinal (Int A B)))
    { refine card_Un_Int A B hFA hFB };
  have h2 : π (add (cardinal A) (cardinal B)
               = add (cardinal (Un A B)) (cardinal empty))
    { refine ind_eq (eq_sym hdis)
        (λ w, add (cardinal A) (cardinal B) = add (cardinal (Un A B)) (cardinal w))
        h1 };
  have h4 : π (add (cardinal (Un A B)) (cardinal empty) = cardinal (Un A B))
    { rewrite cardinal_0;
      refine add_0_right (cardinal (Un A B))
        (Finite_cardinal_in_nat (Un A B) (Finite_Un A B hFA hFB)) };
  refine eq_sym (eq_trans h2 h4)
end;

// Port-internal helpers: ⋃0 = 0 and ⋃cons(x,C) = x ∪ ⋃C.
private opaque symbol priv_Union_0 :
  π (Union empty = empty) ≔
begin
  refine equals0I (Union empty) _;
  assume z hz;
  refine ∃ₑ (UnionE z empty hz) _; assume B hB;
  refine emptyE B (∧ₑ₁ hB)
end;

private opaque symbol priv_Union_cons (x C : τ ι) :
  π (Union (cons x C) = Un x (Union C)) ≔
begin
  assume x C;
  refine equality_iffI (Union (cons x C)) (Un x (Union C)) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine ∃ₑ (UnionE z (cons x C) hz) _; assume B hB;
    refine ∨ₑ (∧ₑ₁ (cons_iff B x C) (∧ₑ₁ hB)) _ _
    { assume hBx;
      refine UnI1 z x (Union C)
        (ind_eq (eq_sym hBx) (λ w, z ∈ w) (∧ₑ₂ hB)) }
    { assume hBC; refine UnI2 z x (Union C) (UnionI z B C (∧ₑ₂ hB) hBC) } }
  { assume hz;
    refine ∨ₑ (UnE z x (Union C) hz) _ _
    { assume hzx; refine UnionI z x (cons x C) hzx (consI1 x C) }
    { assume hzU;
      refine ∃ₑ (UnionE z C hzU) _; assume B hB;
      refine UnionI z B (cons x C) (∧ₑ₂ hB) (consI2 B x C (∧ₑ₁ hB)) } }
end;

opaque symbol card_partition (C k : τ ι) :
  π (Finite C) → π (Finite (Union C)) →
  π (Ball C (λ c, cardinal c = k)) →
  π (Ball C (λ c1, Ball C (λ c2, c1 ≠ c2 ⇒ Int c1 c2 = empty))) →
  π (mult k (cardinal C) = cardinal (Union C)) ≔
begin
  assume C k hFC;
  refine Finite_induct C
    (λ D, Finite (Union D) ⇒
          (Ball D (λ c, cardinal c = k) ⇒
           (Ball D (λ c1, Ball D (λ c2, c1 ≠ c2 ⇒ Int c1 c2 = empty)) ⇒
            mult k (cardinal D) = cardinal (Union D))))
    hFC _ _
  { assume hFU hall hdisj;
    try simplify rule off;
    rewrite priv_Union_0; rewrite cardinal_0;
    refine mult_0_right k }
  { assume x D hFD hnxD IH;
    assume hFU hall hdisj;
    try simplify rule off;
    have hUc : π (Union (cons x D) = Un x (Union D)) { refine priv_Union_cons x D };
    have hFx : π (Finite x)
      { refine subset_Finite x (Union (cons x D)) _ hFU;
        assume z hz; refine UnionI z x (cons x D) hz (consI1 x D) };
    have hFUD : π (Finite (Union D))
      { refine subset_Finite (Union D) (Union (cons x D)) _ hFU;
        assume z hz;
        refine ∃ₑ (UnionE z D hz) _; assume B hB;
        refine UnionI z B (cons x D) (∧ₑ₂ hB) (consI2 B x D (∧ₑ₁ hB)) };
    have hxdisj : π (Int x (Union D) = empty)
      { refine equals0I (Int x (Union D)) _;
        assume z hz;
        have hzx : π (z ∈ x) { refine IntD1 z x (Union D) hz };
        refine ∃ₑ (UnionE z D (IntD2 z x (Union D) hz)) _;
        assume B hB;
        have hBD : π (B ∈ D) { refine ∧ₑ₁ hB };
        have hne : π (¬ (x = B))
          { assume hxB; refine hnxD (ind_eq hxB (λ w, w ∈ D) hBD) };
        have hIempty : π (Int x B = empty)
          { refine hdisj x (consI1 x D) B (consI2 B x D hBD) hne };
        refine emptyE z (ind_eq (eq_sym hIempty) (λ w, z ∈ w)
          (IntI z x B hzx (∧ₑ₂ hB))) };
    have hallD : π (Ball D (λ c, cardinal c = k))
      { assume c hc; refine hall c (consI2 c x D hc) };
    have hdisjD : π (Ball D (λ c1, Ball D (λ c2, c1 ≠ c2 ⇒ Int c1 c2 = empty)))
      { assume c1 hc1 c2 hc2 hne;
        refine hdisj c1 (consI2 c1 x D hc1) c2 (consI2 c2 x D hc2) hne };
    have hIH : π (mult k (cardinal D) = cardinal (Union D))
      { refine IH hFUD hallD hdisjD };
    have hcards : π (cardinal (cons x D) = succ (cardinal D))
      { refine Finite_imp_cardinal_cons D x hFD hnxD };
    have hUn : π (cardinal (Un x (Union D))
                  = add (cardinal x) (cardinal (Union D)))
      { refine card_Un_disjoint x (Union D) hFx hFUD hxdisj };
    have hcardx : π (cardinal x = k) { refine hall x (consI1 x D) };
    rewrite hcards; rewrite mult_succ_right; rewrite hIH;
    rewrite hUc; rewrite hUn; rewrite hcardx;
    reflexivity }
end;

// ===========================================================================
// Theorems by Krzysztof Grabczewski, proofs by lcp
// ===========================================================================

// nat_implies_well_ord = nat_into_Ord [THEN well_ord_Memrel] :
//   n ∈ nat ⟹ well_ord(n, Memrel(n))
opaque symbol nat_implies_well_ord (n : τ ι) :
  π (n ∈ omega) → π (well_ord n (Memrel n)) ≔
begin
  assume n hn; refine well_ord_Memrel n (nat_into_Ord n hn)
end;

opaque symbol nat_sum_eqpoll_sum (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (eqpoll (sum m n) (add m n)) ≔
begin
  assume m n hm hn;
  have hwo : π (well_ord (sum m n) (radd m (Memrel m) n (Memrel n)))
    { refine well_ord_radd m (Memrel m) n (Memrel n)
        (nat_implies_well_ord m hm) (nat_implies_well_ord n hn) };
  have e1 : π (eqpoll (sum m n) (cardinal (sum m n)))
    { refine eqpoll_sym (cardinal (sum m n)) (sum m n)
        (well_ord_cardinal_eqpoll (sum m n) (radd m (Memrel m) n (Memrel n)) hwo) };
  have h3 : π (cardinal (sum m n) = add m n)
    { refine eq_trans (eq_sym (cadd_def m n)) (nat_cadd_eq_add m n hm hn) };
  refine ind_eq (eq_sym h3) (λ w, eqpoll (sum m n) w) e1
end;

opaque symbol Ord_subset_natD (i : τ ι) :
  π (Ord i) → π (i ⊆ omega) → π (i ∈ omega ∨ i = omega) ≔
begin
  assume i hOi hsub;
  refine Ord_cases i (i ∈ omega ∨ i = omega) hOi _ _ _
  { assume h0; refine ∨ᵢ₁ (ind_eq h0 (λ w, w ∈ omega) zero_in_omega) }
  { assume hbex;
    refine ∃ₑ hbex _; assume j hj;
    have hisj : π (i = succ j) { refine ∧ₑ₂ (∧ₑ₂ hj) };
    have hjo : π (j ∈ omega) { refine hsub j (∧ₑ₁ hj) };
    refine ∨ᵢ₁ (ind_eq hisj (λ w, w ∈ omega) (succ_in_omega j hjo)) }
  { assume hLim;
    have hni : π (le omega i) { refine nat_le_Limit i hLim };
    refine ∨ᵢ₂ (subset_antisym i omega hsub (le_imp_subset omega i hni)) }
end;

opaque symbol Ord_nat_subset_into_Card (i : τ ι) :
  π (Ord i) → π (i ⊆ omega) → π (Card i) ≔
begin
  assume i hOi hsub;
  refine ∨ₑ (Ord_subset_natD i hOi hsub) _ _
  { assume hin; refine nat_into_Card i hin }
  { assume heq; refine ind_eq heq (λ w, Card w) Card_nat }
end;
