// Epsilon.lp — Epsilon induction and recursion.
// Translated from Isabelle/ZF Epsilon.thy (Paulson).
//
// Key definitions: eclose, transrec, rank
// Key results: eps_induct, transrec unfolding, rank properties

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities
            ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Ordinal ZF.Nat_ZF ZF.OrdQuant;

// ===========================================================================
// eclose(A): the epsilon closure — least transitive set containing A.
// eclose(A) = ⋃_{n ∈ nat} nat_rec(n, A, λ m r. ⋃(r))
// ===========================================================================

constant symbol eclose (A : τ ι) : τ ι;
constant symbol eclose_def (A : τ ι) :
  π (eclose A = Union (RepFun omega (λ n, nat_rec n A (λ m r, Union r))));

// A ⊆ eclose(A):  A = nat_rec(0,A,b) is the 0th stage, and 0 ∈ ω.
opaque symbol arg_subset_eclose (A : τ ι) : π (A ⊆ eclose A) ≔
begin
  assume A x hx;
  rewrite eclose_def;
  have hxnr : π (x ∈ nat_rec empty A (λ m r, Union r))
    { rewrite (nat_rec_0 A (λ m r, Union r)); apply hx };
  have hmem : π (nat_rec empty A (λ m r, Union r)
                 ∈ RepFun omega (λ n, nat_rec n A (λ m r, Union r)))
    { refine RepFunI empty omega (λ n, nat_rec n A (λ m r, Union r)) zero_in_omega };
  refine UnionI x (nat_rec empty A (λ m r, Union r))
    (RepFun omega (λ n, nat_rec n A (λ m r, Union r))) hxnr hmem
end;

// eclose(A) is transitive:  if x ∈ stage n and z ∈ x, then z ∈ ⋃(stage n) =
// stage (n+1), so z ∈ eclose(A).
opaque symbol Transset_eclose (A : τ ι) : π (Transset (eclose A)) ≔
begin
  assume A;
  rewrite Transset_def;
  assume x hx z hzx;
  rewrite eclose_def;
  have hx' : π (x ∈ Union (RepFun omega (λ n, nat_rec n A (λ m r, Union r))))
    { refine ind_eq (eq_sym (eclose_def A)) (λ w, x ∈ w) hx };
  // x ∈ eclose A → ∃ S ∈ RepFun ω (λ n. stage n). x ∈ S
  have hbex1 : π (Bex (RepFun omega (λ n, nat_rec n A (λ m r, Union r))) (λ S, x ∈ S))
    { refine UnionE x (RepFun omega (λ n, nat_rec n A (λ m r, Union r))) hx' };
  refine ∃ₑ hbex1 _;
  assume S hS;
  have hSrep : π (S ∈ RepFun omega (λ n, nat_rec n A (λ m r, Union r))) { refine ∧ₑ₁ hS };
  have hxS : π (x ∈ S) { refine ∧ₑ₂ hS };
  have hbex2 : π (Bex omega (λ n, S = nat_rec n A (λ m r, Union r)))
    { refine ∧ₑ₁ (RepFun_iff S omega (λ n, nat_rec n A (λ m r, Union r))) hSrep };
  refine ∃ₑ hbex2 _;
  assume n hn;
  have hnω : π (n ∈ omega) { refine ∧ₑ₁ hn };
  have hSeq : π (S = nat_rec n A (λ m r, Union r)) { refine ∧ₑ₂ hn };
  have hxnr : π (x ∈ nat_rec n A (λ m r, Union r)) { rewrite (eq_sym hSeq); apply hxS };
  // z ∈ ⋃(stage n) = stage (n+1)
  have hzU : π (z ∈ Union (nat_rec n A (λ m r, Union r)))
    { refine UnionI z x (nat_rec n A (λ m r, Union r)) hzx hxnr };
  have hznr : π (z ∈ nat_rec (succ n) A (λ m r, Union r))
    { rewrite (nat_rec_succ n A (λ m r, Union r) hnω); apply hzU };
  have hmem : π (nat_rec (succ n) A (λ m r, Union r)
                 ∈ RepFun omega (λ k, nat_rec k A (λ m r, Union r)))
    { refine RepFunI (succ n) omega (λ k, nat_rec k A (λ m r, Union r))
        (succ_in_omega n hnω) };
  refine UnionI z (nat_rec (succ n) A (λ m r, Union r))
    (RepFun omega (λ k, nat_rec k A (λ m r, Union r))) hznr hmem
end;

// x ∈ eclose(A) → x ⊆ eclose(A)
symbol eclose_subset (A x : τ ι) :
  π (x ∈ eclose A) → π (x ⊆ eclose A) ≔
  λ h, TranssetD (eclose A) x (Transset_eclose A) h;

// A ∈ eclose(B) ∧ c ∈ A → c ∈ eclose(B)
symbol ecloseD (A B c : τ ι) :
  π (A ∈ eclose B) → π (c ∈ A) → π (c ∈ eclose B) ≔
  λ hA hc, eclose_subset B A hA c hc;

// Each stage nat_rec(n,A,b) is contained in any transitive X ⊇ A (by induction).
opaque symbol eclose_least_lemma (X A : τ ι) :
  π (Transset X) → π (A ⊆ X) →
  π (Ball omega (λ n, nat_rec n A (λ m r, Union r) ⊆ X)) ≔
begin
  assume X A hTX hAX;
  // nat_induct leaves each goal as a β-redex (λ n. …) k; `refine ind_eq …`
  // matches up to conversion, so no `rewrite`/`change` on the redex is needed.
  refine nat_induct (λ n, nat_rec n A (λ m r, Union r) ⊆ X) _ _
  { // stage 0 = A ⊆ X
    refine ind_eq (nat_rec_0 A (λ m r, Union r)) (λ w, w ⊆ X) hAX }
  { // stage (n+1) = ⋃(stage n) ⊆ X
    assume n hn IH;
    have hUsub : π (Union (nat_rec n A (λ m r, Union r)) ⊆ X) {
      assume z hz;
      have hbex : π (Bex (nat_rec n A (λ m r, Union r)) (λ y, z ∈ y))
        { refine UnionE z (nat_rec n A (λ m r, Union r)) hz };
      refine ∃ₑ hbex _;
      assume y hy;
      have hynr : π (y ∈ nat_rec n A (λ m r, Union r)) { refine ∧ₑ₁ hy };
      have hzy : π (z ∈ y) { refine ∧ₑ₂ hy };
      have hyX : π (y ∈ X) { refine IH y hynr };
      refine TranssetD X y hTX hyX z hzy
    };
    refine ind_eq (nat_rec_succ n A (λ m r, Union r) hn) (λ w, w ⊆ X) hUsub }
end;

// eclose is the least transitive superset.
opaque symbol eclose_least (X A : τ ι) :
  π (Transset X) → π (A ⊆ X) → π (eclose A ⊆ X) ≔
begin
  assume X A hTX hAX z hz;
  have hz' : π (z ∈ Union (RepFun omega (λ n, nat_rec n A (λ m r, Union r))))
    { refine ind_eq (eq_sym (eclose_def A)) (λ w, z ∈ w) hz };
  have hbex : π (Bex (RepFun omega (λ n, nat_rec n A (λ m r, Union r))) (λ S, z ∈ S))
    { refine UnionE z (RepFun omega (λ n, nat_rec n A (λ m r, Union r))) hz' };
  refine ∃ₑ hbex _;
  assume S hS;
  have hSrep : π (S ∈ RepFun omega (λ n, nat_rec n A (λ m r, Union r))) { refine ∧ₑ₁ hS };
  have hzS : π (z ∈ S) { refine ∧ₑ₂ hS };
  have hbex2 : π (Bex omega (λ n, S = nat_rec n A (λ m r, Union r)))
    { refine ∧ₑ₁ (RepFun_iff S omega (λ n, nat_rec n A (λ m r, Union r))) hSrep };
  refine ∃ₑ hbex2 _;
  assume n hn;
  have hnω : π (n ∈ omega) { refine ∧ₑ₁ hn };
  have hSeq : π (S = nat_rec n A (λ m r, Union r)) { refine ∧ₑ₂ hn };
  have hzNR : π (z ∈ nat_rec n A (λ m r, Union r)) { rewrite (eq_sym hSeq); apply hzS };
  refine eclose_least_lemma X A hTX hAX n hnω z hzNR
end;

// Epsilon induction for eclose: P holds at a if it propagates up ∈ within
// eclose(A). Proved by Memrel(eclose A)-induction with P'(x) = (x∈eclose A ⇒ P x).
opaque symbol eclose_induct (A a : τ ι) (P : τ ι → Prop) :
  π (a ∈ eclose A) →
  (Π x : τ ι, π (x ∈ eclose A) → (Π y : τ ι, π (y ∈ x) → π (P y)) → π (P x)) →
  π (P a) ≔
begin
  assume A a P ha Hstep;
  have hTK : π (Transset (eclose A)) { refine Transset_eclose A };
  have hwf : π (wf_global (Memrel (eclose A))) { refine wf_Memrel (eclose A) };
  have hPa : π (a ∈ eclose A ⇒ P a) {
    refine wf_global_induct (Memrel (eclose A)) (λ x, x ∈ eclose A ⇒ P x) a hwf _;
    assume x IH hxK;
    refine Hstep x hxK _;
    assume y hyx;
    have hyK : π (y ∈ eclose A) { refine TranssetD (eclose A) x hTK hxK y hyx };
    refine IH y (MemrelI y x (eclose A) hyx hyK hxK) hyK
  };
  refine hPa ha
end;

// Epsilon induction: (∀y ∈ x. P(y)) → P(x) implies P(a) for all a.
opaque symbol eps_induct (P : τ ι → Prop) (a : τ ι) :
  (Π x : τ ι, (Π y : τ ι, π (y ∈ x) → π (P y)) → π (P x)) →
  π (P a) ≔
begin
  assume P a H;
  have ha : π (a ∈ eclose (singleton a))
    { refine arg_subset_eclose (singleton a) a (singletonI a) };
  refine eclose_induct (singleton a) a P ha _;
  assume x hx hAll;
  refine H x hAll
end;

// eclose is monotone
opaque symbol eclose_mono (A B : τ ι) :
  π (A ⊆ B) → π (eclose A ⊆ eclose B) ≔
begin
  assume A B hAB;
  refine eclose_least (eclose B) A (Transset_eclose B) _;
  refine subset_trans A B (eclose B) hAB (arg_subset_eclose B)
end;

// eclose is idempotent
opaque symbol eclose_idem (A : τ ι) :
  π (eclose (eclose A) = eclose A) ≔
begin
  assume A;
  refine subset_antisym (eclose (eclose A)) (eclose A) _ _
  { refine eclose_least (eclose A) (eclose A) (Transset_eclose A) (subset_refl (eclose A)) }
  { refine arg_subset_eclose (eclose A) }
end;

// Transset(X) → eclose(X) = X
opaque symbol Transset_eclose_eq_arg (X : τ ι) :
  π (Transset X) → π (eclose X = X) ≔
begin
  assume X hTX;
  refine subset_antisym (eclose X) X _ _
  { refine eclose_least X X hTX (subset_refl X) }
  { refine arg_subset_eclose X }
end;

// ===========================================================================
// Helper lemmas for transrec / rank
// ===========================================================================

// eq_trans and RepFun_cong now live in ZF.equalities (required above); they are
// equalities-level helpers reused by OrderArith/wfrank as well as rank below.

// UN_upper: a ∈ A → B(a) ⊆ ⋃_{x∈A} B(x)
opaque symbol UN_upper (a A : τ ι) (B : τ ι → τ ι) :
  π (a ∈ A) → π (B a ⊆ Union (RepFun A B)) ≔
begin
  assume a A B ha z hz;
  refine UnionI z (B a) (RepFun A B) hz (RepFunI a A B ha)
end;

// UN_least: (∀x∈A. B(x) ⊆ C) → ⋃_{x∈A} B(x) ⊆ C
opaque symbol UN_least (A C : τ ι) (B : τ ι → τ ι) :
  (Π x : τ ι, π (x ∈ A) → π (B x ⊆ C)) → π (Union (RepFun A B) ⊆ C) ≔
begin
  assume A C B hsub z hz;
  have hbex : π (Bex (RepFun A B) (λ S, z ∈ S)) { refine UnionE z (RepFun A B) hz };
  refine ∃ₑ hbex _;
  assume S hS;
  have hSR : π (S ∈ RepFun A B) { refine ∧ₑ₁ hS };
  have hzS : π (z ∈ S) { refine ∧ₑ₂ hS };
  have hbex2 : π (Bex A (λ x, S = B x)) { refine ∧ₑ₁ (RepFun_iff S A B) hSR };
  refine ∃ₑ hbex2 _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hSeq : π (S = B x) { refine ∧ₑ₂ hx };
  have hzBx : π (z ∈ B x) { refine ind_eq (eq_sym hSeq) (λ w, z ∈ w) hzS };
  refine hsub x hxA z hzBx
end;

// Ord_UN: (∀x∈A. Ord(B(x))) → Ord(⋃_{x∈A} B(x))
opaque symbol Ord_UN (A : τ ι) (B : τ ι → τ ι) :
  (Π x : τ ι, π (x ∈ A) → π (Ord (B x))) → π (Ord (Union (RepFun A B))) ≔
begin
  assume A B hB;
  refine Ord_Union (RepFun A B) _;
  assume z hz;
  have hbex : π (Bex A (λ x, z = B x)) { refine ∧ₑ₁ (RepFun_iff z A B) hz };
  refine ∃ₑ hbex _;
  assume x hx;
  have hxA : π (x ∈ A) { refine ∧ₑ₁ hx };
  have hzB : π (z = B x) { refine ∧ₑ₂ hx };
  refine ind_eq hzB (λ w, Ord w) (hB x hxA)
end;

// UN_mono: A ⊆ B → (∀x∈A. C(x) ⊆ D(x)) → ⋃_{x∈A} C(x) ⊆ ⋃_{x∈B} D(x)
// (Isabelle equalities.thy UN_mono)
opaque symbol UN_mono (A B : τ ι) (C D : τ ι → τ ι) :
  π (A ⊆ B) → (Π x : τ ι, π (x ∈ A) → π (C x ⊆ D x)) →
  π (Union (RepFun A C) ⊆ Union (RepFun B D)) ≔
begin
  assume A B C D hAB hCD;
  refine UN_least A (Union (RepFun B D)) C _;
  assume x hxA;
  refine subset_trans (C x) (D x) (Union (RepFun B D))
    (hCD x hxA) (UN_upper x B D (hAB x hxA))
end;

// UN_least_le: Ord(i) → (∀x∈A. b(x) ≤ i) → (⋃_{x∈A} b(x)) ≤ i
// (Isabelle Ordinal.thy:582)
opaque symbol UN_least_le (i A : τ ι) (b : τ ι → τ ι) :
  π (Ord i) → (Π x : τ ι, π (x ∈ A) → π (le (b x) i)) →
  π (le (Union (RepFun A b)) i) ≔
begin
  assume i A b hOi hle;
  have hsub : π (Union (RepFun A b) ⊆ i)
    { refine UN_least A i b _;
      assume x hxA; refine le_imp_subset (b x) i (hle x hxA) };
  have hOU : π (Ord (Union (RepFun A b)))
    { refine Ord_UN A b _;
      assume x hxA; refine lt_Ord (b x) (succ i) (hle x hxA) };
  refine subset_imp_le i (Union (RepFun A b)) hsub hOi hOU
end;

// UN_succ_least_lt: j<i → (∀x∈A. b(x)<j) → (⋃_{x∈A} succ(b(x))) < i
// (Isabelle Ordinal.thy:588)
opaque symbol UN_succ_least_lt (i j A : τ ι) (b : τ ι → τ ι) :
  π (lt j i) → (Π x : τ ι, π (x ∈ A) → π (lt (b x) j)) →
  π (lt (Union (RepFun A (λ x, succ (b x)))) i) ≔
begin
  assume i j A b hji hlt;
  have hOj : π (Ord j) { refine lt_Ord j i hji };
  have hle : π (le (Union (RepFun A (λ x, succ (b x)))) j)
    { refine UN_least_le j A (λ x, succ (b x)) hOj _;
      assume x hxA;
      refine succ_leI (b x) j hOj (ltD (b x) j (hlt x hxA)) };
  refine lt_trans1 (Union (RepFun A (λ x, succ (b x)))) j i hle hji
end;

// succ is monotone w.r.t. ≤ on ordinals.
opaque symbol succ_subset_succ (i j : τ ι) :
  π (Ord j) → π (le i j) → π (succ i ⊆ succ j) ≔
begin
  assume i j hOj hle;
  refine ∨ₑ (leE i j hle) _ _
  { assume hij;
    have hisj : π (i ∈ succ j) { refine ∧ₑ₂ (succ_iff i j) (∨ᵢ₂ hij) };
    refine Ord_succ_subsetI i (succ j) hisj (Ord_succ j hOj) }
  { assume heq;
    have hsij : π (succ i = succ j) { refine feq succ heq };
    refine ind_eq hsij (λ w, w ⊆ succ j) (subset_refl (succ j)) }
end;

// {a} ⊆ B  ←  a ∈ B
opaque symbol singleton_subsetI (a B : τ ι) :
  π (a ∈ B) → π (singleton a ⊆ B) ≔
begin
  assume a B ha x hx;
  have hxa : π (x = a) { refine ∧ₑ₁ (singleton_iff x a) hx };
  refine ind_eq hxa (λ z, z ∈ B) ha
end;

// under_Memrel: Transset(i) → j ∈ i → Memrel(i)⁻¹{j} = j
opaque symbol under_Memrel (i j : τ ι) :
  π (Transset i) → π (j ∈ i) → π (vimage_singleton (Memrel i) j = j) ≔
begin
  assume i j hT hji;
  refine subset_antisym (vimage_singleton (Memrel i) j) j _ _
  { assume x hx;
    have hpair : π (Pair x j ∈ Memrel i) { refine vimage_singletonD x j (Memrel i) hx };
    have hmem : π (x ∈ i ∧ j ∈ i ∧ x ∈ j) { refine MemrelE x j i hpair };
    refine ∧ₑ₂ (∧ₑ₂ hmem) }
  { assume x hxj;
    have hsub : π (j ⊆ i) { refine TranssetD i j hT hji };
    have hxi : π (x ∈ i) { refine hsub x hxj };
    refine vimage_singletonI x j (Memrel i) (MemrelI x j i hxj hxi hji) }
end;

// under_Memrel specialised to eclose (always transitive).
opaque symbol under_Memrel_eclose (A j : τ ι) :
  π (j ∈ eclose A) → π (vimage_singleton (Memrel (eclose A)) j = j) ≔
begin
  assume A j hj;
  refine under_Memrel (eclose A) j (Transset_eclose A) hj
end;

// a ∈ eclose({a})
opaque symbol arg_in_eclose_sing (a : τ ι) : π (a ∈ eclose (singleton a)) ≔
begin
  assume a;
  refine arg_subset_eclose (singleton a) a (singletonI a)
end;

// c ∈ a → c ∈ eclose({a})
opaque symbol arg_into_eclose_sing (a c : τ ι) :
  π (c ∈ a) → π (c ∈ eclose (singleton a)) ≔
begin
  assume a c hc;
  refine ecloseD a (singleton a) c (arg_in_eclose_sing a) hc
end;

// A ∈ eclose({B}) → B ∈ eclose({C}) → A ∈ eclose({C})
opaque symbol mem_eclose_sing_trans (A B C : τ ι) :
  π (A ∈ eclose (singleton B)) → π (B ∈ eclose (singleton C)) →
  π (A ∈ eclose (singleton C)) ≔
begin
  assume A B C hAB hBC;
  have hsub : π (eclose (singleton B) ⊆ eclose (singleton C))
    { refine eclose_least (eclose (singleton C)) (singleton B)
        (Transset_eclose (singleton C)) (singleton_subsetI B (eclose (singleton C)) hBC) };
  refine hsub A hAB
end;

// wfrec_eclose_eq: changing the eclose base for the well-founded recursion does
// not change the result, as long as both bases reach k.  Proved by ∈-induction
// over eclose({j}).
opaque symbol wfrec_eclose_eq (i j k : τ ι) (H : τ ι → τ ι → τ ι) :
  π (k ∈ eclose (singleton j)) → π (j ∈ eclose (singleton i)) →
  π (wfrec (Memrel (eclose (singleton i))) k H = wfrec (Memrel (eclose (singleton j))) k H) ≔
begin
  assume i j k H hk hj;
  refine eclose_induct (singleton j) k
    (λ m, wfrec (Memrel (eclose (singleton i))) m H = wfrec (Memrel (eclose (singleton j))) m H)
    hk _;
  assume x hx IH;
  have hxi : π (x ∈ eclose (singleton i)) { refine mem_eclose_sing_trans x j i hx hj };
  // unfold the left recursion at x
  have hL : π (wfrec (Memrel (eclose (singleton i))) x H =
    H x (Lambda (vimage_singleton (Memrel (eclose (singleton i))) x)
      (λ y, wfrec (Memrel (eclose (singleton i))) y H)))
    { refine wfrec_eq (Memrel (eclose (singleton i))) x H (wf_Memrel (eclose (singleton i))) };
  have hvi : π (vimage_singleton (Memrel (eclose (singleton i))) x = x)
    { refine under_Memrel_eclose (singleton i) x hxi };
  have hLamI : π (Lambda (vimage_singleton (Memrel (eclose (singleton i))) x)
      (λ y, wfrec (Memrel (eclose (singleton i))) y H) =
      Lambda x (λ y, wfrec (Memrel (eclose (singleton i))) y H))
    { refine feq (λ d, Lambda d (λ y, wfrec (Memrel (eclose (singleton i))) y H)) hvi };
  have hL2 : π (wfrec (Memrel (eclose (singleton i))) x H =
      H x (Lambda x (λ y, wfrec (Memrel (eclose (singleton i))) y H)))
    { refine eq_trans hL (feq (H x) hLamI) };
  // unfold the right recursion at x
  have hR : π (wfrec (Memrel (eclose (singleton j))) x H =
    H x (Lambda (vimage_singleton (Memrel (eclose (singleton j))) x)
      (λ y, wfrec (Memrel (eclose (singleton j))) y H)))
    { refine wfrec_eq (Memrel (eclose (singleton j))) x H (wf_Memrel (eclose (singleton j))) };
  have hvj : π (vimage_singleton (Memrel (eclose (singleton j))) x = x)
    { refine under_Memrel_eclose (singleton j) x hx };
  have hLamJ : π (Lambda (vimage_singleton (Memrel (eclose (singleton j))) x)
      (λ y, wfrec (Memrel (eclose (singleton j))) y H) =
      Lambda x (λ y, wfrec (Memrel (eclose (singleton j))) y H))
    { refine feq (λ d, Lambda d (λ y, wfrec (Memrel (eclose (singleton j))) y H)) hvj };
  have hR2 : π (wfrec (Memrel (eclose (singleton j))) x H =
      H x (Lambda x (λ y, wfrec (Memrel (eclose (singleton j))) y H)))
    { refine eq_trans hR (feq (H x) hLamJ) };
  // inner calls agree by the induction hypothesis
  have hbody : π (Lambda x (λ y, wfrec (Memrel (eclose (singleton i))) y H) =
      Lambda x (λ y, wfrec (Memrel (eclose (singleton j))) y H))
    { refine lam_cong x x (λ y, wfrec (Memrel (eclose (singleton i))) y H)
        (λ y, wfrec (Memrel (eclose (singleton j))) y H) (eq_refl x) _;
      assume y hy; refine IH y hy };
  refine eq_trans hL2 (eq_trans (feq (H x) hbody) (eq_sym hR2))
end;

// wfrec_eclose_eq2: specialise the base to {k} for an inner call k ∈ i.
opaque symbol wfrec_eclose_eq2 (i k : τ ι) (H : τ ι → τ ι → τ ι) :
  π (k ∈ i) →
  π (wfrec (Memrel (eclose (singleton i))) k H = wfrec (Memrel (eclose (singleton k))) k H) ≔
begin
  assume i k H hk;
  refine wfrec_eclose_eq i k k H (arg_in_eclose_sing k) (arg_into_eclose_sing i k hk)
end;

// ===========================================================================
// transrec(a, H): transfinite recursion.
// transrec(a, H) = H(a, λx∈a. transrec(x, H))
// ===========================================================================

// transrec(a,H) = wfrec(Memrel(eclose({a})), a, H).
constant symbol transrec (a : τ ι) (H : τ ι → τ ι → τ ι) : τ ι;
constant symbol transrec_def (a : τ ι) (H : τ ι → τ ι → τ ι) :
  π (transrec a H = wfrec (Memrel (eclose (singleton a))) a H);

// The fundamental recursion equation
opaque symbol transrec_eq (a : τ ι) (H : τ ι → τ ι → τ ι) :
  π (transrec a H = H a (Lambda a (λ x, transrec x H))) ≔
begin
  assume a H;
  rewrite transrec_def;
  have h1 : π (wfrec (Memrel (eclose (singleton a))) a H =
    H a (Lambda (vimage_singleton (Memrel (eclose (singleton a))) a)
      (λ x, wfrec (Memrel (eclose (singleton a))) x H)))
    { refine wfrec_eq (Memrel (eclose (singleton a))) a H (wf_Memrel (eclose (singleton a))) };
  have hv : π (vimage_singleton (Memrel (eclose (singleton a))) a = a)
    { refine under_Memrel_eclose (singleton a) a (arg_in_eclose_sing a) };
  have hlam : π (Lambda (vimage_singleton (Memrel (eclose (singleton a))) a)
      (λ x, wfrec (Memrel (eclose (singleton a))) x H) =
      Lambda a (λ x, transrec x H))
    { refine lam_cong (vimage_singleton (Memrel (eclose (singleton a))) a) a
        (λ x, wfrec (Memrel (eclose (singleton a))) x H) (λ x, transrec x H) hv _;
      assume x hx;
      have hxa : π (x ∈ a) { refine ind_eq (eq_sym hv) (λ z, x ∈ z) hx };
      refine eq_trans (wfrec_eclose_eq2 a x H hxa) (eq_sym (transrec_def x H)) };
  refine eq_trans h1 (feq (H a) hlam)
end;

// Helper for definitions via transrec
opaque symbol def_transrec (f : τ ι → τ ι) (H : τ ι → τ ι → τ ι) (a : τ ι) :
  (Π x : τ ι, π (f x = transrec x H)) →
  π (f a = H a (Lambda a (λ x, f x))) ≔
begin
  assume f H a hfdef;
  have e2 : π (transrec a H = H a (Lambda a (λ x, transrec x H))) { refine transrec_eq a H };
  have e3 : π (Lambda a (λ x, transrec x H) = Lambda a (λ x, f x))
    { refine lam_cong a a (λ x, transrec x H) (λ x, f x) (eq_refl a) _;
      assume x hx; symmetry; refine hfdef x };
  refine eq_trans (hfdef a) (eq_trans e2 (feq (H a) e3))
end;

// ===========================================================================
// recursor / rec — primitive recursion on nat.  "recursor is better than
// nat_rec: the succ case has no type requirement" (Epsilon.thy).
//   recursor(a,b,k) = transrec(k, λn f. nat_case(a, λm. b(m, f`m), n))
//   rec(k,a,b)      = recursor(a,b,k)
// ===========================================================================

constant symbol recursor (a : τ ι) (b : τ ι → τ ι → τ ι) (k : τ ι) : τ ι;
constant symbol recursor_def (a : τ ι) (b : τ ι → τ ι → τ ι) (k : τ ι) :
  π (recursor a b k = transrec k (λ n f, nat_case a (λ m, b m (fapply f m)) n));

constant symbol rec (k a : τ ι) (b : τ ι → τ ι → τ ι) : τ ι;
constant symbol rec_def (k a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (rec k a b = recursor a b k);

// recursor(a,b,0) = a
opaque symbol recursor_0 (a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (recursor a b empty = a) ≔
begin
  assume a b;
  rewrite recursor_def;
  rewrite transrec_eq; simplify rule off; refine nat_case_0 a _
end;

// recursor(a,b,succ(m)) = b(m, recursor(a,b,m))   [unconditional in m]
opaque symbol recursor_succ (a : τ ι) (b : τ ι → τ ι → τ ι) (m : τ ι) :
  π (recursor a b (succ m) = b m (recursor a b m)) ≔
begin
  assume a b m;
  rewrite recursor_def;
  // beta step: (Lambda (succ m) (λx. transrec x H)) ` m  =  transrec m H  =  recursor a b m
  have hbeta : π (fapply (Lambda (succ m)
        (λ x, transrec x (λ n f, nat_case a (λ k, b k (fapply f k)) n))) m
      = recursor a b m)
    { refine eq_trans
        (beta (succ m)
          (λ x, transrec x (λ n f, nat_case a (λ k, b k (fapply f k)) n)) m (succI1 m))
        (eq_sym (recursor_def a b m)) };
  rewrite transrec_eq; simplify rule off;
  rewrite nat_case_succ; simplify rule off;
  rewrite hbeta; reflexivity
end;

// rec(0,a,b) = a
opaque symbol rec_0 (a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (rec empty a b = a) ≔
begin
  assume a b;
  rewrite rec_def;
  refine recursor_0 a b
end;

// rec(succ(m),a,b) = b(m, rec(m,a,b))   [unconditional in m]
opaque symbol rec_succ (m a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (rec (succ m) a b = b m (rec m a b)) ≔
begin
  assume m a b;
  rewrite rec_def;
  rewrite .[x in _ = _ x] rec_def;
  refine recursor_succ a b m
end;

// rec_type: ⟦n∈nat; a∈C(0); ⋀m z. ⟦m∈nat; z∈C(m)⟧⟹b(m,z)∈C(succ m)⟧ ⟹ rec(n,a,b)∈C(n)
opaque symbol rec_type (n a : τ ι) (b : τ ι → τ ι → τ ι) (C : τ ι → τ ι)
  (hn : π (n ∈ omega)) (ha : π (a ∈ C empty))
  (hstep : Π m z, π (m ∈ omega) → π (z ∈ C m) → π (b m z ∈ C (succ m))) :
  π (rec n a b ∈ C n) ≔
begin
  assume n a b C hn ha hstep;
  have hall : π (Ball omega (λ k, rec k a b ∈ C k)) {
    refine nat_induct (λ k, rec k a b ∈ C k) _ _
    { simplify rule off; rewrite (rec_0 a b); refine ha }
    { assume k hk hIH;
      rewrite (rec_succ k a b);
      refine hstep k (rec k a b) hk hIH }
  };
  refine bspec omega (λ k, rec k a b ∈ C k) n hall hn
end;

// ===========================================================================
// transrec2 — two-case transfinite recursion with an explicit Limit fallback
// (Epsilon.thy keyword-definition).
// ===========================================================================

// The recursion body, named for proof-side convertibility.
private symbol tr2body (a : τ ι) (b : τ ι → τ ι → τ ι) : τ ι → τ ι → τ ι ≔
  λ i r, If (i = empty) a
    (If (`∃ (j : τ ι), i = succ j)
        (b (The (λ j, i = succ j)) (fapply r (The (λ j, i = succ j))))
        (OUnion i (λ j, fapply r j)));

constant symbol transrec2 (k a : τ ι) (b : τ ι → τ ι → τ ι) : τ ι;
constant symbol transrec2_def (k a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (transrec2 k a b =
     transrec k (λ i r, If (i = empty) a
       (If (`∃ (j : τ ι), i = succ j)
           (b (The (λ j, i = succ j)) (fapply r (The (λ j, i = succ j))))
           (OUnion i (λ j, fapply r j)))));

// transrec2(0,a,b) = a
opaque symbol transrec2_0 (a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (transrec2 empty a b = a) ≔
begin
  assume a b;
  rewrite transrec2_def;
  rewrite transrec_eq;
  simplify rule off;
  refine If_P (empty = empty) a _ (eq_refl empty)
end;

// transrec2(succ(i),a,b) = b(i, transrec2(i,a,b))
opaque symbol transrec2_succ (i a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (transrec2 (succ i) a b = b i (transrec2 i a b)) ≔
begin
  assume i a b;
  rewrite transrec2_def;
  rewrite transrec_eq;
  simplify rule off;
  rewrite If_not_P (succ i = empty) _ _ (succ_neq_0 i);
  rewrite If_P (`∃ (j : τ ι), succ i = succ j) _ _ (∃ᵢ i (eq_refl (succ i)));
  have hthe : π (The (λ j, succ i = succ j) = i)
    { refine the_equality (λ j, succ i = succ j) i (eq_refl (succ i)) _;
      assume z hz; refine eq_sym (succ_inject i z hz) };
  rewrite hthe;
  rewrite (beta (succ i) _ i (succI1 i));
  simplify rule off;
  rewrite left (transrec2_def i a b);
  reflexivity
end;

// Limit(i) → transrec2(i,a,b) = ⋃j<i. transrec2(j,a,b)
opaque symbol transrec2_Limit (i a : τ ι) (b : τ ι → τ ι → τ ι) :
  π (Limit i) →
  π (transrec2 i a b = OUnion i (λ j, transrec2 j a b)) ≔
begin
  assume i a b hLim;
  rewrite transrec2_def;
  rewrite transrec_eq;
  simplify rule off;
  rewrite If_not_P (i = empty) _ _ (Limit_nonzero i hLim);
  have hnsucc : π (¬ (`∃ (j : τ ι), i = succ j))
    { assume hex; refine ∃ₑ hex _; assume j hj;
      refine not_succ_Limit j (ind_eq (eq_sym hj) (λ w, Limit w) hLim) };
  rewrite If_not_P (`∃ (j : τ ι), i = succ j) _ _ hnsucc;
  refine equality_iffI
    (OUnion i (λ j, fapply (Lambda i (λ x, transrec x (tr2body a b))) j))
    (OUnion i (λ j, transrec2 j a b)) _;
  assume z;
  apply ∧ᵢ
  { assume hz;
    refine OUN_E z i (λ j, fapply (Lambda i (λ x, transrec x (tr2body a b))) j)
      (z ∈ OUnion i (λ j, transrec2 j a b)) hz _;
    assume j hzB hji;
    have hjm : π (j ∈ i) { refine ltD j i hji };
    have hbeta : π (fapply (Lambda i (λ x, transrec x (tr2body a b))) j = transrec2 j a b)
      { refine eq_trans (beta i (λ x, transrec x (tr2body a b)) j hjm)
          (eq_sym (transrec2_def j a b)) };
    refine OUN_I j z i (λ j2, transrec2 j2 a b) hji
      (ind_eq (eq_sym hbeta) (λ w, z ∈ w) hzB) }
  { assume hz;
    refine OUN_E z i (λ j, transrec2 j a b)
      (z ∈ OUnion i (λ j, fapply (Lambda i (λ x, transrec x (tr2body a b))) j)) hz _;
    assume j hzB hji;
    have hjm : π (j ∈ i) { refine ltD j i hji };
    have hbeta : π (fapply (Lambda i (λ x, transrec x (tr2body a b))) j = transrec2 j a b)
      { refine eq_trans (beta i (λ x, transrec x (tr2body a b)) j hjm)
          (eq_sym (transrec2_def j a b)) };
    refine OUN_I j z i (λ j2, fapply (Lambda i (λ x, transrec x (tr2body a b))) j2) hji
      (ind_eq hbeta (λ w, z ∈ w) hzB) }
end;

// ===========================================================================
// rank(a) = ⋃_{y ∈ a} succ(rank(y))
// ===========================================================================

constant symbol rank (a : τ ι) : τ ι;
constant symbol rank_def (a : τ ι) :
  π (rank a = transrec a (λ x f, Union (RepFun x (λ y, succ (fapply f y)))));

// rank unfolding:  rank(a) = ⋃_{y∈a} succ(rank(y))
opaque symbol rank_eq (a : τ ι) :
  π (rank a = Union (RepFun a (λ y, succ (rank y)))) ≔
begin
  assume a;
  have hdt : π (rank a =
      Union (RepFun a (λ y, succ (fapply (Lambda a (λ x, rank x)) y))))
    { refine def_transrec rank (λ x g, Union (RepFun x (λ y, succ (fapply g y)))) a _;
      assume x; refine rank_def x };
  have hcong : π (Union (RepFun a (λ y, succ (fapply (Lambda a (λ x, rank x)) y))) =
      Union (RepFun a (λ y, succ (rank y))))
    { refine feq Union _;
      refine RepFun_cong a (λ y, succ (fapply (Lambda a (λ x, rank x)) y)) (λ y, succ (rank y)) _;
      assume y hy;
      refine feq succ (beta a (λ x, rank x) y hy) };
  refine eq_trans hdt hcong
end;

// Ord(rank(a))
opaque symbol Ord_rank (a : τ ι) : π (Ord (rank a)) ≔
begin
  assume a;
  refine eps_induct (λ b, Ord (rank b)) a _;
  assume x IH;
  have ho : π (Ord (Union (RepFun x (λ y, succ (rank y)))))
    { refine Ord_UN x (λ y, succ (rank y)) _;
      assume y hy;
      refine Ord_succ (rank y) (IH y hy) };
  refine ind_eq (rank_eq x) (λ z, Ord z) ho
end;

// Ord(i) → rank(i) = i
opaque symbol rank_of_Ord (i : τ ι) :
  π (Ord i) → π (rank i = i) ≔
begin
  assume i hOi;
  refine trans_induct i (λ b, rank b = b) hOi _;
  assume x hOx IH;
  have h2 : π (Union (RepFun x (λ y, succ (rank y))) = Union (RepFun x (λ y, succ y)))
    { refine feq Union _;
      refine RepFun_cong x (λ y, succ (rank y)) (λ y, succ y) _;
      assume y hy; refine feq succ (IH y hy) };
  refine eq_trans (rank_eq x) (eq_trans h2 (Ord_equality x hOx))
end;

// a ∈ b → rank(a) < rank(b)
opaque symbol rank_lt (a b : τ ι) :
  π (a ∈ b) → π (lt (rank a) (rank b)) ≔
begin
  assume a b hab;
  refine ltI (rank a) (rank b) _ (Ord_rank b);
  have hU : π (rank a ∈ Union (RepFun b (λ y, succ (rank y))))
    { refine UnionI (rank a) (succ (rank a)) (RepFun b (λ y, succ (rank y)))
        (succI1 (rank a)) (RepFunI a b (λ y, succ (rank y)) hab) };
  refine ind_eq (rank_eq b) (λ z, rank a ∈ z) hU
end;

// rank(0) = 0
opaque symbol rank_0 : π (rank empty = empty) ≔
begin
  have hsub : π (Union (RepFun empty (λ y, succ (rank y))) ⊆ empty)
    { assume z hz;
      have hbex : π (Bex (RepFun empty (λ y, succ (rank y))) (λ S, z ∈ S))
        { refine UnionE z (RepFun empty (λ y, succ (rank y))) hz };
      refine ∃ₑ hbex _;
      assume S hS;
      have hbex2 : π (Bex empty (λ y, S = succ (rank y)))
        { refine ∧ₑ₁ (RepFun_iff S empty (λ y, succ (rank y))) (∧ₑ₁ hS) };
      refine ∃ₑ hbex2 _;
      assume y hy;
      refine ⊥ₑ (emptyE y (∧ₑ₁ hy)) };
  refine eq_trans (rank_eq empty)
    (subset_antisym (Union (RepFun empty (λ y, succ (rank y)))) empty hsub
      (empty_subset (Union (RepFun empty (λ y, succ (rank y))))))
end;

// a ⊆ b → rank(a) ≤ rank(b)
opaque symbol rank_mono (a b : τ ι) :
  π (a ⊆ b) → π (le (rank a) (rank b)) ≔
begin
  assume a b hab;
  have hmono : π (Union (RepFun a (λ y, succ (rank y))) ⊆ Union (RepFun b (λ y, succ (rank y))))
    { refine UN_least a (Union (RepFun b (λ y, succ (rank y)))) (λ y, succ (rank y)) _;
      assume y hy;
      refine UN_upper y b (λ y, succ (rank y)) (hab y hy) };
  have hsub : π (rank a ⊆ rank b)
    { refine ind_eq (rank_eq a) (λ z, z ⊆ rank b) _;
      refine ind_eq (rank_eq b) (λ z, Union (RepFun a (λ y, succ (rank y))) ⊆ z) hmono };
  refine subset_imp_le (rank b) (rank a) hsub (Ord_rank b) (Ord_rank a)
end;

// rank(succ(x)) = succ(rank(x))
opaque symbol rank_succ (x : τ ι) :
  π (rank (succ x) = succ (rank x)) ≔
begin
  assume x;
  have hmain : π (Union (RepFun (succ x) (λ y, succ (rank y))) = succ (rank x))
    { refine subset_antisym (Union (RepFun (succ x) (λ y, succ (rank y)))) (succ (rank x)) _ _
      { refine UN_least (succ x) (succ (rank x)) (λ y, succ (rank y)) _;
        assume y hy;
        refine ∨ₑ (∧ₑ₁ (succ_iff y x) hy) _ _
        { assume heq;
          have hseq : π (succ (rank y) = succ (rank x)) { refine feq succ (feq rank heq) };
          refine ind_eq hseq (λ w, w ⊆ succ (rank x)) (subset_refl (succ (rank x))) }
        { assume hyx;
          refine succ_subset_succ (rank y) (rank x) (Ord_rank x)
            (leI (rank y) (rank x) (ltD (rank y) (rank x) (rank_lt y x hyx)) (Ord_rank x)) } }
      { refine UN_upper x (succ x) (λ y, succ (rank y)) (succI1 x) } };
  refine eq_trans (rank_eq (succ x)) hmain
end;

// rank(Pow(a)) = succ(rank(a))
opaque symbol rank_Pow (a : τ ι) :
  π (rank (Pow a) = succ (rank a)) ≔
begin
  assume a;
  have hOu : π (Ord (Union (RepFun (Pow a) (λ y, succ (rank y)))))
    { refine Ord_UN (Pow a) (λ y, succ (rank y)) _;
      assume y hy; refine Ord_succ (rank y) (Ord_rank y) };
  have hOs : π (Ord (succ (rank a))) { refine Ord_succ (rank a) (Ord_rank a) };
  have hle1 : π (le (Union (RepFun (Pow a) (λ y, succ (rank y)))) (succ (rank a)))
    { refine subset_imp_le (succ (rank a)) (Union (RepFun (Pow a) (λ y, succ (rank y)))) _ hOs hOu;
      refine UN_least (Pow a) (succ (rank a)) (λ y, succ (rank y)) _;
      assume y hy;
      refine succ_subset_succ (rank y) (rank a) (Ord_rank a)
        (rank_mono y a (∧ₑ₁ (Pow_iff y a) hy)) };
  have hle2 : π (le (succ (rank a)) (Union (RepFun (Pow a) (λ y, succ (rank y)))))
    { refine subset_imp_le (Union (RepFun (Pow a) (λ y, succ (rank y)))) (succ (rank a)) _ hOu hOs;
      refine UN_upper a (Pow a) (λ y, succ (rank y)) (Pow_top a) };
  refine eq_trans (rank_eq (Pow a))
    (le_anti_sym (Union (RepFun (Pow a) (λ y, succ (rank y)))) (succ (rank a)) hle1 hle2)
end;
