// ZF.lp — module ZF.ZF.
// Mirrors the "Transfinite Recursion" section of Isabelle/ZF ZF.thy
// (ZF.thy:44-64): transrec3, three-case ordinal recursion.
//
// Prerequisite `pred` is Isabelle's ordinal predecessor (Arith.thy:19-20,
// pred(y) ≡ nat_case(0, λx. x, y)).  Arith.thy is not yet ported, so pred is
// homed here as the direct dependency of transrec3's successor case.
//
// Reuses: transrec/def_transrec (Epsilon.lp), If/If_P/If_not_P (upair.lp),
// nat_case/nat_case_0/nat_case_succ (Nat_ZF.lp), not_succ_Limit/Limit_nonzero
// (Ordinal.lp), beta/lam_cong (func.lp).

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities
            ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Ordinal ZF.Nat_ZF ZF.Epsilon;

// ===========================================================================
// pred — ordinal predecessor (Arith.thy:19-20)
// ===========================================================================

// pred(y) = nat_case(0, λx. x, y)
symbol pred (y : τ ι) : τ ι ≔ nat_case empty (λ x, x) y;

// pred(0) = 0                       (Isabelle Arith.thy:393, pred_0)
opaque symbol pred_0 : π (pred empty = empty) ≔
begin
  refine nat_case_0 empty (λ x, x)
end;

// pred(succ(y)) = y                 (Isabelle Arith.thy:90, pred_succ_eq)
opaque symbol pred_succ_eq (y : τ ι) : π (pred (succ y) = y) ≔
begin
  assume y;
  refine nat_case_succ empty (λ x, x) y
end;

// ===========================================================================
// transrec3(k, a, b, c) — three-case transfinite recursion (ZF.thy:47-54)
//
// transrec3(k, a, b, c) ≡
//   transrec(k, λx r.
//     if x = 0      then a
//     else if Limit(x) then c(x, λy∈x. r`y)
//     else             b(pred(x), r`pred(x)))
// ===========================================================================

constant symbol transrec3 (k a : τ ι) (b c : τ ι → τ ι → τ ι) : τ ι;
constant symbol transrec3_def (k a : τ ι) (b c : τ ι → τ ι → τ ι) :
  π (transrec3 k a b c =
     transrec k (λ x r,
       If (x = empty) a
         (If (Limit x)
           (c x (Lambda x (λ y, fapply r y)))
           (b (pred x) (fapply r (pred x))))));

// Unfolding equation (via def_transrec).  Mirrors Isabelle's
// `transrec3_def [THEN def_transrec]`.
opaque symbol transrec3_unfold (k a : τ ι) (b c : τ ι → τ ι → τ ι) :
  π (transrec3 k a b c =
     If (k = empty) a
       (If (Limit k)
         (c k (Lambda k (λ y, fapply (Lambda k (λ x, transrec3 x a b c)) y)))
         (b (pred k) (fapply (Lambda k (λ x, transrec3 x a b c)) (pred k))))) ≔
begin
  assume k a b c;
  refine def_transrec (λ z, transrec3 z a b c)
    (λ x r, If (x = empty) a
      (If (Limit x)
        (c x (Lambda x (λ y, fapply r y)))
        (b (pred x) (fapply r (pred x))))) k _;
  assume x; refine transrec3_def x a b c
end;

// transrec3(0, a, b, c) = a                              (ZF.thy:56, simp)
opaque symbol transrec3_0 (a : τ ι) (b c : τ ι → τ ι → τ ι) :
  π (transrec3 empty a b c = a) ≔
begin
  assume a b c;
  rewrite transrec3_unfold empty a b c;
  refine If_P (empty = empty) a _ (eq_refl empty)
end;

// transrec3(succ(i), a, b, c) = b(i, transrec3(i, a, b, c))   (ZF.thy:59, simp)
opaque symbol transrec3_succ (i a : τ ι) (b c : τ ι → τ ι → τ ι) :
  π (transrec3 (succ i) a b c = b i (transrec3 i a b c)) ≔
begin
  assume i a b c;
  rewrite transrec3_unfold (succ i) a b c;
  rewrite If_not_P (succ i = empty) _ _ (succ_neq_0 i);
  rewrite If_not_P (Limit (succ i)) _ _ (not_succ_Limit i);
  rewrite pred_succ_eq i;
  rewrite beta (succ i) (λ x, transrec3 x a b c) i (succI1 i);
  reflexivity
end;

// Limit(i) → transrec3(i, a, b, c) = c(i, λj∈i. transrec3(j, a, b, c))
//                                                        (ZF.thy:62, force)
opaque symbol transrec3_Limit (i a : τ ι) (b c : τ ι → τ ι → τ ι) :
  π (Limit i) →
  π (transrec3 i a b c = c i (Lambda i (λ j, transrec3 j a b c))) ≔
begin
  assume i a b c hLim;
  rewrite transrec3_unfold i a b c;
  rewrite If_not_P (i = empty) _ _ (Limit_nonzero i hLim);
  rewrite If_P (Limit i) _ _ hLim;
  refine feq (c i) _;
  refine lam_cong i i (λ y, fapply (Lambda i (λ x, transrec3 x a b c)) y)
    (λ j, transrec3 j a b c) (eq_refl i) _;
  assume y hy;
  refine beta i (λ x, transrec3 x a b c) y hy
end;

// ===========================================================================
// iterates — F^n(x) (ZF.thy consts+primrec; transparent per the primrec
// exception) and iterates_omega — F^ω(x) (ZF.thy keyword-definition).
// ===========================================================================

symbol iterates (F : τ ι → τ ι) (n x : τ ι) : τ ι ≔ rec n x (λ _ r, F r);

// F^0(x) = x
opaque symbol iterates_0 (F : τ ι → τ ι) (x : τ ι) :
  π (iterates F empty x = x) ≔
begin
  assume F x;
  refine rec_0 x (λ _ r, F r)
end;

// F^succ(n)(x) = F(F^n(x))
opaque symbol iterates_succ (F : τ ι → τ ι) (n x : τ ι) :
  π (iterates F (succ n) x = F (iterates F n x)) ≔
begin
  assume F n x;
  refine rec_succ n x (λ _ r, F r)
end;

// F^ω(x) = ⋃n∈nat. F^n(x)
constant symbol iterates_omega (F : τ ι → τ ι) (x : τ ι) : τ ι;
constant symbol iterates_omega_def (F : τ ι → τ ι) (x : τ ι) :
  π (iterates_omega F x = Union (RepFun omega (λ n, iterates F n x)));
