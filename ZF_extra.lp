// ZF_extra.lp — transrec3: three-case transfinite recursion.
// Translated from Isabelle/ZF ZF.thy (lines 47-65).
//
// transrec3(k, a, b, c):
//   k = 0       → a
//   k = succ(j) → b(j, transrec3(j, a, b, c))
//   Limit(k)    → c(k, λj∈k. transrec3(j, a, b, c))

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
            Stdlib.Classic Stdlib.Impred Stdlib.HOL
            Stdlib.PropExt Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities
            ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Ordinal ZF.Epsilon;

// ===========================================================================
// transrec3(k, a, b, c) — ordinal recursion with three cases
// ===========================================================================

// Definition via transrec:
// transrec3(k, a, b, c) ≡
//   transrec(k, λx r.
//     if x = 0 then a
//     else if Limit(x) then c(x, λy∈x. r`y)
//     else b(pred(x), r`pred(x)))
//
// where pred is the ordinal predecessor (from Ordinal.lp or Nat_ZF).
// We axiomatize the three computation rules directly.

constant symbol transrec3 :
  τ ι →                          // k: the ordinal
  τ ι →                          // a: value at 0
  (τ ι → τ ι → τ ι) →           // b: successor case b(j, rec(j))
  (τ ι → τ ι → τ ι) →           // c: limit case c(k, λj∈k. rec(j))
  τ ι;

// transrec3(0, a, b, c) = a
constant symbol transrec3_0 (a : τ ι) (b c : τ ι → τ ι → τ ι) :
  π (transrec3 empty a b c = a);

// transrec3(succ(i), a, b, c) = b(i, transrec3(i, a, b, c))
constant symbol transrec3_succ (i a : τ ι) (b c : τ ι → τ ι → τ ι) :
  π (transrec3 (succ i) a b c = b i (transrec3 i a b c));

// Limit(i) → transrec3(i, a, b, c) = c(i, λj∈i. transrec3(j, a, b, c))
constant symbol transrec3_Limit (i a : τ ι) (b c : τ ι → τ ι → τ ι) :
  π (Limit i) →
  π (transrec3 i a b c = c i (Lambda i (λ j, transrec3 j a b c)));

// ===========================================================================
// Pair is not an ordinal (from Kuratowski structure + Foundation)
// ===========================================================================

// Ord(x) → Transset(x), and Pair_not_Transset gives ¬ Transset(Pair(a,b)).
opaque symbol Pair_not_Ord (a b : τ ι) :
  π (¬ Ord (Pair a b)) ≔
begin
  assume a b hO;
  have hT : π (Transset (Pair a b)) { refine ∧ₑ₁ hO };
  refine Pair_not_Transset a b hT
end;

// Note: no AC/well-ordering axiom needed. The model uses Vset(α) as node
// space in sys_on, so every pointed graph fits in some sys_on directly.

// ===========================================================================
// ZF definite description (no ε)
// ===========================================================================
// The(A, P) = ⋃(Collect(A, P))
// If ∃!x ∈ A. P(x), then Collect(A, P) = {x₀} and ⋃{x₀} = x₀.
// This is a pure ZF operation — no choice principle needed.
// singleton elimination: z ∈ {x} → z = x
opaque symbol singletonE (z a : τ ι) :
  π (z ∈ singleton a) → π (z = a) ≔
begin
  assume z a hz;
  have hdisj : π (z = a ∨ z ∈ empty)
    { refine ∧ₑ₁ (cons_iff z a empty) hz };
  refine ∨ₑ hdisj (λ h, h) (λ h, ⊥ₑ (empty_ax z h))
end;

// ⋃{x} = x: Union of a singleton set
opaque symbol Union_singleton (x : τ ι) :
  π (Union (singleton x) = x) ≔
begin
  assume x;
  refine extension (Union (singleton x)) x _;
  assume z; refine ∧ᵢ _ _
  { assume hz;
    // z ∈ ⋃{x} → ∃B ∈ {x}. z ∈ B → z ∈ x
    have hbex : π (Bex (singleton x) (λ B, z ∈ B))
      { refine UnionE z (singleton x) hz };
    refine ∃ₑ hbex _;
    assume B hB;
    have hBx : π (B = x)
      { refine singletonE B x (∧ₑ₁ hB) };
    rewrite left hBx; refine ∧ₑ₂ hB }
  { assume hz;
    // z ∈ x → z ∈ ⋃{x}
    refine UnionI z x (singleton x) hz (singletonI x) }
end;

// ZF definite description (no ε): ZThe(A, P) = ⋃(Collect(A, P))
// If P has a unique solution x ∈ A, then ZThe = x.
symbol ZThe (A : τ ι) (P : τ ι → Prop) : τ ι ≔ Union (Collect A P);

opaque symbol ZThe_eq (A : τ ι) (P : τ ι → Prop) (x : τ ι) :
  π (x ∈ A) → π (P x) → π (Ball A (λ y, P y ⇒ y = x)) →
  π (ZThe A P = x) ≔
begin
  assume A P x hxA hPx huniq;
  // Collect(A, P) = singleton(x)
  have hCeq : π (Collect A P = singleton x)
    { refine extension (Collect A P) (singleton x) _;
      assume y; refine ∧ᵢ _ _
      { assume hy;
        have hyeq : π (y = x) { refine huniq y (CollectD1 y A P hy) (CollectD2 y A P hy) };
        rewrite hyeq; refine singletonI x }
      { assume hy;
        have hyeq : π (y = x) { refine singletonE y x hy };
        rewrite hyeq; refine CollectI x A P hxA hPx } };
  // ZThe = Union(Collect(A, P)) = Union(singleton(x)) = x
  have hgoal : π (Union (Collect A P) = x)
    { rewrite hCeq; refine Union_singleton x };
  refine hgoal
end;
