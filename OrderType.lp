// ZF.OrderType — Order Types and Ordinal Arithmetic
// Faithful SKELETON port of isabelle-src/OrderType.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/OrderType.thy.)

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum ZF.Ordinal ZF.OrdQuant ZF.Nat_ZF ZF.Order ZF.OrderArith;

// ===========================================================================
// Lt — defined in Isabelle's Nat.thy (Lt ≡ {⟨x,y⟩ ∈ nat*nat. x<y}) but ABSENT
// from this port's Nat_ZF.lp.  Added here (faithfully, with nat = omega) so the
// *_Lt lemmas at the end of OrderType have a referent.
// ===========================================================================
symbol Lt : τ ι ≔ Collect (Sigma omega (λ _, omega)) (λ z, lt (fst z) (snd z));

// ===========================================================================
// Definitions
// ===========================================================================

symbol ordermap (A r : τ ι) : τ ι ≔
  Lambda A (λ x, wfrec (Int r (Sigma A (λ _, A))) x (λ x2 f, Image f (pred A x2 r)));

symbol ordertype (A r : τ ι) : τ ι ≔ Image (ordermap A r) A;

symbol Ord_alt (X : τ ι) : Prop ≔
  well_ord X (Memrel X) ∧ Ball X (λ u, u = pred X u (Memrel X));

symbol ordify (x : τ ι) : τ ι ≔ If (Ord x) x empty;

symbol omult (i j : τ ι) : τ ι ≔
  ordertype (Sigma j (λ _, i)) (rmult j (Memrel j) i (Memrel i));

symbol raw_oadd (i j : τ ι) : τ ι ≔
  ordertype (sum i j) (radd i (Memrel i) j (Memrel j));

symbol oadd (i j : τ ι) : τ ι ≔ raw_oadd (ordify i) (ordify j);

symbol odiff (i j : τ ι) : τ ι ≔ ordertype (Diff i j) (Memrel i);

// ===========================================================================
// Proofs needing the combination of Ordinal.thy and Order.thy
// ===========================================================================

opaque symbol le_well_ord_Memrel (j i : τ ι) :
  π (le j i) → π (well_ord j (Memrel i)) ≔
begin
  admit
end;

// well_ord_Memrel = le_refl [THEN le_well_ord_Memrel] : Ord(i) ⟹ well_ord(i, Memrel(i))
opaque symbol well_ord_Memrel (i : τ ι) :
  π (Ord i) → π (well_ord i (Memrel i)) ≔
begin
  admit
end;

opaque symbol lt_pred_Memrel (j i : τ ι) :
  π (lt j i) → π (pred i j (Memrel i) = j) ≔
begin
  admit
end;

opaque symbol pred_Memrel (x A : τ ι) :
  π (x ∈ A) → π (pred A x (Memrel A) = Int A x) ≔
begin
  admit
end;

opaque symbol Ord_iso_implies_eq_lemma (j i f : τ ι) (R : Prop) :
  π (lt j i) → π (f ∈ ord_iso i (Memrel i) j (Memrel j)) → π R ≔
begin
  admit
end;

opaque symbol Ord_iso_implies_eq (i j f : τ ι) :
  π (Ord i) → π (Ord j) → π (f ∈ ord_iso i (Memrel i) j (Memrel j)) →
  π (i = j) ≔
begin
  admit
end;

// ===========================================================================
// Ordermap and ordertype
// ===========================================================================

opaque symbol ordermap_type (A r : τ ι) :
  π (ordermap A r ∈ Pi A (λ _, ordertype A r)) ≔
begin
  admit
end;

opaque symbol ordermap_eq_image (A r x : τ ι) :
  π (wf A r) → π (x ∈ A) →
  π (fapply (ordermap A r) x = Image (ordermap A r) (pred A x r)) ≔
begin
  admit
end;

opaque symbol ordermap_pred_unfold (A r x : τ ι) :
  π (wf A r) → π (x ∈ A) →
  π (fapply (ordermap A r) x
     = RepFun (pred A x r) (λ y, fapply (ordermap A r) y)) ≔
begin
  admit
end;

// ordermap_unfold = ordermap_pred_unfold [simplified pred_def] (pred unfolded to Collect)
opaque symbol ordermap_unfold (A r x : τ ι) :
  π (wf A r) → π (x ∈ A) →
  π (fapply (ordermap A r) x
     = RepFun (Collect A (λ y, Pair y x ∈ r)) (λ y, fapply (ordermap A r) y)) ≔
begin
  admit
end;

opaque symbol Ord_ordermap (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) → π (Ord (fapply (ordermap A r) x)) ≔
begin
  admit
end;

opaque symbol Ord_ordertype (A r : τ ι) :
  π (well_ord A r) → π (Ord (ordertype A r)) ≔
begin
  admit
end;

opaque symbol ordermap_mono (w x A r : τ ι) :
  π (Pair w x ∈ r) → π (wf A r) → π (w ∈ A) → π (x ∈ A) →
  π (fapply (ordermap A r) w ∈ fapply (ordermap A r) x) ≔
begin
  admit
end;

opaque symbol converse_ordermap_mono (w x A r : τ ι) :
  π (fapply (ordermap A r) w ∈ fapply (ordermap A r) x) →
  π (well_ord A r) → π (w ∈ A) → π (x ∈ A) → π (Pair w x ∈ r) ≔
begin
  admit
end;

opaque symbol ordermap_surj (A r : τ ι) :
  π (ordermap A r ∈ surj A (ordertype A r)) ≔
begin
  admit
end;

opaque symbol ordermap_bij (A r : τ ι) :
  π (well_ord A r) → π (ordermap A r ∈ bij A (ordertype A r)) ≔
begin
  admit
end;

opaque symbol ordertype_ord_iso (A r : τ ι) :
  π (well_ord A r) →
  π (ordermap A r ∈ ord_iso A r (ordertype A r) (Memrel (ordertype A r))) ≔
begin
  admit
end;

opaque symbol ordertype_eq (f A r B s : τ ι) :
  π (f ∈ ord_iso A r B s) → π (well_ord B s) →
  π (ordertype A r = ordertype B s) ≔
begin
  admit
end;

opaque symbol ordertype_eq_imp_ord_iso (A r B s : τ ι) :
  π (ordertype A r = ordertype B s) → π (well_ord A r) → π (well_ord B s) →
  π (`∃ (f : τ ι), f ∈ ord_iso A r B s) ≔
begin
  admit
end;

opaque symbol le_ordertype_Memrel (j i : τ ι) :
  π (le j i) → π (ordertype j (Memrel i) = j) ≔
begin
  admit
end;

// ordertype_Memrel = le_refl [THEN le_ordertype_Memrel] : Ord(i) ⟹ ordertype(i,Memrel(i)) = i
opaque symbol ordertype_Memrel (i : τ ι) :
  π (Ord i) → π (ordertype i (Memrel i) = i) ≔
begin
  admit
end;

opaque symbol ordertype_0 (r : τ ι) :
  π (ordertype empty r = empty) ≔
begin
  admit
end;

// bij_ordertype_vimage = ord_iso_rvimage [THEN ordertype_eq]
opaque symbol bij_ordertype_vimage (f A B s : τ ι) :
  π (f ∈ bij A B) → π (well_ord B s) →
  π (ordertype A (rvimage A f s) = ordertype B s) ≔
begin
  admit
end;

opaque symbol ordermap_pred_eq_ordermap (A r y z : τ ι) :
  π (well_ord A r) → π (y ∈ A) → π (z ∈ pred A y r) →
  π (fapply (ordermap (pred A y r) r) z = fapply (ordermap A r) z) ≔
begin
  admit
end;

opaque symbol ordertype_unfold (A r : τ ι) :
  π (ordertype A r = RepFun A (λ y, fapply (ordermap A r) y)) ≔
begin
  admit
end;

opaque symbol ordertype_pred_subset (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) →
  π (ordertype (pred A x r) r ⊆ ordertype A r) ≔
begin
  admit
end;

opaque symbol ordertype_pred_lt (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) →
  π (lt (ordertype (pred A x r) r) (ordertype A r)) ≔
begin
  admit
end;

opaque symbol ordertype_pred_unfold (A r : τ ι) :
  π (well_ord A r) →
  π (ordertype A r = RepFun A (λ x, ordertype (pred A x r) r)) ≔
begin
  admit
end;

// ===========================================================================
// Alternative definition of ordinal
// ===========================================================================

opaque symbol Ord_is_Ord_alt (i : τ ι) :
  π (Ord i) → π (Ord_alt i) ≔
begin
  admit
end;

opaque symbol Ord_alt_is_Ord (i : τ ι) :
  π (Ord_alt i) → π (Ord i) ≔
begin
  admit
end;

// ===========================================================================
// Ordinal Addition
// ===========================================================================

opaque symbol bij_sum_0 (A : τ ι) :
  π (Lambda (sum A empty) (λ z, case_sum (λ x, x) (λ y, y) z)
     ∈ bij (sum A empty) A) ≔
begin
  admit
end;

opaque symbol ordertype_sum_0_eq (A r s : τ ι) :
  π (well_ord A r) →
  π (ordertype (sum A empty) (radd A r empty s) = ordertype A r) ≔
begin
  admit
end;

opaque symbol bij_0_sum (A : τ ι) :
  π (Lambda (sum empty A) (λ z, case_sum (λ x, x) (λ y, y) z)
     ∈ bij (sum empty A) A) ≔
begin
  admit
end;

opaque symbol ordertype_0_sum_eq (A r s : τ ι) :
  π (well_ord A r) →
  π (ordertype (sum empty A) (radd empty s A r) = ordertype A r) ≔
begin
  admit
end;

opaque symbol pred_Inl_bij (a A r B s : τ ι) :
  π (a ∈ A) →
  π (Lambda (pred A a r) (λ x, Inl x)
     ∈ bij (pred A a r) (pred (sum A B) (Inl a) (radd A r B s))) ≔
begin
  admit
end;

opaque symbol ordertype_pred_Inl_eq (a A r B s : τ ι) :
  π (a ∈ A) → π (well_ord A r) →
  π (ordertype (pred (sum A B) (Inl a) (radd A r B s)) (radd A r B s)
     = ordertype (pred A a r) r) ≔
begin
  admit
end;

opaque symbol pred_Inr_bij (b B s A r : τ ι) :
  π (b ∈ B) →
  π (id_fun (sum A (pred B b s))
     ∈ bij (sum A (pred B b s)) (pred (sum A B) (Inr b) (radd A r B s))) ≔
begin
  admit
end;

opaque symbol ordertype_pred_Inr_eq (b A r B s : τ ι) :
  π (b ∈ B) → π (well_ord A r) → π (well_ord B s) →
  π (ordertype (pred (sum A B) (Inr b) (radd A r B s)) (radd A r B s)
     = ordertype (sum A (pred B b s)) (radd A r (pred B b s) s)) ≔
begin
  admit
end;

opaque symbol Ord_ordify (x : τ ι) :
  π (Ord (ordify x)) ≔
begin
  admit
end;

opaque symbol ordify_idem (x : τ ι) :
  π (ordify (ordify x) = ordify x) ≔
begin
  admit
end;

opaque symbol Ord_raw_oadd (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (raw_oadd i j)) ≔
begin
  admit
end;

opaque symbol Ord_oadd (i j : τ ι) :
  π (Ord (oadd i j)) ≔
begin
  admit
end;

opaque symbol raw_oadd_0 (i : τ ι) :
  π (Ord i) → π (raw_oadd i empty = i) ≔
begin
  admit
end;

opaque symbol oadd_0 (i : τ ι) :
  π (Ord i) → π (oadd i empty = i) ≔
begin
  admit
end;

opaque symbol raw_oadd_0_left (i : τ ι) :
  π (Ord i) → π (raw_oadd empty i = i) ≔
begin
  admit
end;

opaque symbol oadd_0_left (i : τ ι) :
  π (Ord i) → π (oadd empty i = i) ≔
begin
  admit
end;

opaque symbol oadd_eq_if_raw_oadd (i j : τ ι) :
  π (oadd i j = If (Ord i) (If (Ord j) (raw_oadd i j) i) (If (Ord j) j empty)) ≔
begin
  admit
end;

opaque symbol raw_oadd_eq_oadd (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (raw_oadd i j = oadd i j) ≔
begin
  admit
end;

opaque symbol lt_oadd1 (k i j : τ ι) :
  π (lt k i) → π (lt k (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_le_self (i j : τ ι) :
  π (Ord i) → π (le i (oadd i j)) ≔
begin
  admit
end;

opaque symbol id_ord_iso_Memrel (A B : τ ι) :
  π (A ⊆ B) → π (id_fun A ∈ ord_iso A (Memrel A) A (Memrel B)) ≔
begin
  admit
end;

opaque symbol subset_ord_iso_Memrel (f A B C r : τ ι) :
  π (f ∈ ord_iso A (Memrel B) C r) → π (A ⊆ B) →
  π (f ∈ ord_iso A (Memrel A) C r) ≔
begin
  admit
end;

opaque symbol restrict_ord_iso (f i A a r j : τ ι) :
  π (f ∈ ord_iso i (Memrel i) (pred A a r) r) → π (a ∈ A) → π (lt j i) →
  π (trans_on A r) →
  π (restrict f j ∈ ord_iso j (Memrel j) (pred A (fapply f j) r) r) ≔
begin
  admit
end;

opaque symbol restrict_ord_iso2 (f A a r i j : τ ι) :
  π (f ∈ ord_iso (pred A a r) r i (Memrel i)) → π (a ∈ A) → π (lt j i) →
  π (trans_on A r) →
  π (converse (restrict (converse f) j)
     ∈ ord_iso (pred A (fapply (converse f) j) r) r j (Memrel j)) ≔
begin
  admit
end;

opaque symbol ordertype_sum_Memrel (A r k j : τ ι) :
  π (well_ord A r) → π (lt k j) →
  π (ordertype (sum A k) (radd A r k (Memrel j))
     = ordertype (sum A k) (radd A r k (Memrel k))) ≔
begin
  admit
end;

opaque symbol oadd_lt_mono2 (k j i : τ ι) :
  π (lt k j) → π (lt (oadd i k) (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_lt_cancel2 (i j k : τ ι) :
  π (lt (oadd i j) (oadd i k)) → π (Ord j) → π (lt j k) ≔
begin
  admit
end;

opaque symbol oadd_lt_iff2 (i j k : τ ι) :
  π (Ord j) → π (lt (oadd i j) (oadd i k) ⇔ lt j k) ≔
begin
  admit
end;

opaque symbol oadd_inject (i j k : τ ι) :
  π (oadd i j = oadd i k) → π (Ord j) → π (Ord k) → π (j = k) ≔
begin
  admit
end;

opaque symbol lt_oadd_disj (k i j : τ ι) :
  π (lt k (oadd i j)) → π (lt k i ∨ Bex j (λ l, k = oadd i l)) ≔
begin
  admit
end;

opaque symbol oadd_assoc (i j k : τ ι) :
  π (oadd (oadd i j) k = oadd i (oadd j k)) ≔
begin
  admit
end;

opaque symbol oadd_unfold (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (oadd i j = Un i (Union (RepFun j (λ k, singleton (oadd i k))))) ≔
begin
  admit
end;

opaque symbol oadd_1 (i : τ ι) :
  π (Ord i) → π (oadd i (succ empty) = succ i) ≔
begin
  admit
end;

opaque symbol oadd_succ (i j : τ ι) :
  π (Ord j) → π (oadd i (succ j) = succ (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_UN (A i a : τ ι) (jf : τ ι → τ ι) :
  π (Ball A (λ x, Ord (jf x))) → π (a ∈ A) →
  π (oadd i (Union (RepFun A (λ x, jf x)))
     = Union (RepFun A (λ x, oadd i (jf x)))) ≔
begin
  admit
end;

opaque symbol oadd_Limit (i j : τ ι) :
  π (Limit j) → π (oadd i j = Union (RepFun j (λ k, oadd i k))) ≔
begin
  admit
end;

opaque symbol oadd_eq_0_iff (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π ((oadd i j = empty) ⇔ (i = empty ∧ j = empty)) ≔
begin
  admit
end;

opaque symbol oadd_eq_lt_iff (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (lt empty (oadd i j) ⇔ (lt empty i ∨ lt empty j)) ≔
begin
  admit
end;

opaque symbol oadd_LimitI (i j : τ ι) :
  π (Ord i) → π (Limit j) → π (Limit (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_le_self2 (i j : τ ι) :
  π (Ord i) → π (le i (oadd j i)) ≔
begin
  admit
end;

opaque symbol oadd_le_mono1 (k j i : τ ι) :
  π (le k j) → π (le (oadd k i) (oadd j i)) ≔
begin
  admit
end;

opaque symbol oadd_lt_mono (ip i jp j : τ ι) :
  π (le ip i) → π (lt jp j) → π (lt (oadd ip jp) (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_le_mono (ip i jp j : τ ι) :
  π (le ip i) → π (le jp j) → π (le (oadd ip jp) (oadd i j)) ≔
begin
  admit
end;

opaque symbol oadd_le_iff2 (i j k : τ ι) :
  π (Ord j) → π (Ord k) → π (le (oadd i j) (oadd i k) ⇔ le j k) ≔
begin
  admit
end;

opaque symbol oadd_lt_self (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (lt i (oadd i j)) ≔
begin
  admit
end;

opaque symbol Ord_imp_greater_Limit (i : τ ι) :
  π (Ord i) → π (`∃ (k : τ ι), lt i k ∧ Limit k) ≔
begin
  admit
end;

opaque symbol Ord2_imp_greater_Limit (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (`∃ (k : τ ι), lt i k ∧ lt j k ∧ Limit k) ≔
begin
  admit
end;

// ===========================================================================
// Ordinal Subtraction
// ===========================================================================

opaque symbol bij_sum_Diff (A B : τ ι) :
  π (A ⊆ B) →
  π (Lambda B (λ y, If (y ∈ A) (Inl y) (Inr y)) ∈ bij B (sum A (Diff B A))) ≔
begin
  admit
end;

opaque symbol ordertype_sum_Diff (i j : τ ι) :
  π (le i j) →
  π (ordertype (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j))
     = ordertype j (Memrel j)) ≔
begin
  admit
end;

opaque symbol Ord_odiff (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (odiff i j)) ≔
begin
  admit
end;

opaque symbol raw_oadd_ordertype_Diff (i j : τ ι) :
  π (le i j) →
  π (raw_oadd i (odiff j i)
     = ordertype (sum i (Diff j i)) (radd i (Memrel j) (Diff j i) (Memrel j))) ≔
begin
  admit
end;

opaque symbol oadd_odiff_inverse (i j : τ ι) :
  π (le i j) → π (oadd i (odiff j i) = j) ≔
begin
  admit
end;

opaque symbol odiff_oadd_inverse (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (odiff (oadd i j) i = j) ≔
begin
  admit
end;

opaque symbol odiff_lt_mono2 (i j k : τ ι) :
  π (lt i j) → π (le k i) → π (lt (odiff i k) (odiff j k)) ≔
begin
  admit
end;

// ===========================================================================
// Ordinal Multiplication
// ===========================================================================

opaque symbol Ord_omult (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord (omult i j)) ≔
begin
  admit
end;

opaque symbol pred_Pair_eq (a A b B r s : τ ι) :
  π (a ∈ A) → π (b ∈ B) →
  π (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)
     = Un (Sigma (pred A a r) (λ _, B)) (Sigma (singleton a) (λ _, pred B b s))) ≔
begin
  admit
end;

opaque symbol ordertype_pred_Pair_eq (a A b B r s : τ ι) :
  π (a ∈ A) → π (b ∈ B) → π (well_ord A r) → π (well_ord B s) →
  π (ordertype (pred (Sigma A (λ _, B)) (Pair a b) (rmult A r B s)) (rmult A r B s)
     = ordertype (sum (Sigma (pred A a r) (λ _, B)) (pred B b s))
                 (radd (Sigma A (λ _, B)) (rmult A r B s) B s)) ≔
begin
  admit
end;

opaque symbol ordertype_pred_Pair_lemma (ip i jp j : τ ι) :
  π (lt ip i) → π (lt jp j) →
  π (ordertype
       (pred (Sigma i (λ _, j)) (Pair ip jp) (rmult i (Memrel i) j (Memrel j)))
       (rmult i (Memrel i) j (Memrel j))
     = raw_oadd (omult j ip) jp) ≔
begin
  admit
end;

opaque symbol lt_omult (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (lt k (omult j i)) →
  π (`∃ (jp : τ ι), `∃ (ip : τ ι),
       (k = oadd (omult j ip) jp) ∧ lt jp j ∧ lt ip i) ≔
begin
  admit
end;

opaque symbol omult_oadd_lt (jp j ip i : τ ι) :
  π (lt jp j) → π (lt ip i) →
  π (lt (oadd (omult j ip) jp) (omult j i)) ≔
begin
  admit
end;

opaque symbol omult_unfold (i j : τ ι) :
  π (Ord i) → π (Ord j) →
  π (omult j i
     = Union (RepFun j (λ jp,
         Union (RepFun i (λ ip, singleton (oadd (omult j ip) jp)))))) ≔
begin
  admit
end;

opaque symbol omult_0 (i : τ ι) :
  π (omult i empty = empty) ≔
begin
  admit
end;

opaque symbol omult_0_left (i : τ ι) :
  π (omult empty i = empty) ≔
begin
  admit
end;

opaque symbol omult_1 (i : τ ι) :
  π (Ord i) → π (omult i (succ empty) = i) ≔
begin
  admit
end;

opaque symbol omult_1_left (i : τ ι) :
  π (Ord i) → π (omult (succ empty) i = i) ≔
begin
  admit
end;

opaque symbol oadd_omult_distrib (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord k) →
  π (omult i (oadd j k) = oadd (omult i j) (omult i k)) ≔
begin
  admit
end;

opaque symbol omult_succ (i j : τ ι) :
  π (Ord i) → π (Ord j) → π (omult i (succ j) = oadd (omult i j) i) ≔
begin
  admit
end;

opaque symbol omult_assoc (i j k : τ ι) :
  π (Ord i) → π (Ord j) → π (Ord k) →
  π (omult (omult i j) k = omult i (omult j k)) ≔
begin
  admit
end;

opaque symbol omult_UN (i A : τ ι) (jf : τ ι → τ ι) :
  π (Ord i) → π (Ball A (λ x, Ord (jf x))) →
  π (omult i (Union (RepFun A (λ x, jf x)))
     = Union (RepFun A (λ x, omult i (jf x)))) ≔
begin
  admit
end;

opaque symbol omult_Limit (i j : τ ι) :
  π (Ord i) → π (Limit j) →
  π (omult i j = Union (RepFun j (λ k, omult i k))) ≔
begin
  admit
end;

opaque symbol lt_omult1 (k i j : τ ι) :
  π (lt k i) → π (lt empty j) → π (lt k (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_self (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (le i (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_mono1 (k j i : τ ι) :
  π (le k j) → π (Ord i) → π (le (omult k i) (omult j i)) ≔
begin
  admit
end;

opaque symbol omult_lt_mono2 (k j i : τ ι) :
  π (lt k j) → π (lt empty i) → π (lt (omult i k) (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_mono2 (k j i : τ ι) :
  π (le k j) → π (Ord i) → π (le (omult i k) (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_mono (ip i jp j : τ ι) :
  π (le ip i) → π (le jp j) → π (le (omult ip jp) (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_lt_mono (ip i jp j : τ ι) :
  π (le ip i) → π (lt jp j) → π (lt empty i) →
  π (lt (omult ip jp) (omult i j)) ≔
begin
  admit
end;

opaque symbol omult_le_self2 (i j : τ ι) :
  π (Ord i) → π (lt empty j) → π (le i (omult j i)) ≔
begin
  admit
end;

opaque symbol omult_inject (i j k : τ ι) :
  π (omult i j = omult i k) → π (lt empty i) → π (Ord j) → π (Ord k) →
  π (j = k) ≔
begin
  admit
end;

// ===========================================================================
// The Relation Lt
// ===========================================================================

opaque symbol wf_Lt : π (wf_global Lt) ≔
begin
  admit
end;

opaque symbol irrefl_Lt (A : τ ι) : π (irrefl_on A Lt) ≔
begin
  admit
end;

opaque symbol trans_Lt (A : τ ι) : π (trans_on A Lt) ≔
begin
  admit
end;

opaque symbol part_ord_Lt (A : τ ι) : π (part_ord A Lt) ≔
begin
  admit
end;

opaque symbol linear_Lt : π (linear omega Lt) ≔
begin
  admit
end;

opaque symbol tot_ord_Lt : π (tot_ord omega Lt) ≔
begin
  admit
end;

opaque symbol well_ord_Lt : π (well_ord omega Lt) ≔
begin
  admit
end;
