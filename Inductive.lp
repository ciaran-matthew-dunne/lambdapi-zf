// Inductive: glue lemmas for the inductive-definition package.
//
// Isabelle source: Inductive.thy.  That theory is almost entirely the ML
// `inductive`/`coinductive`/`primrec` PACKAGE (ind_syntax.ML, inductive_package.ML,
// …) which has no object-level content to port.  It contributes exactly three
// tiny "glue" lemmas, used by the package's definition-unfolding tactics.  They
// are meta-level (`≡`) in Isabelle; rendered here object-level.
//
// SKELETON: statements faithful, proofs admitted (per request).

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func
             ZF.Fixedpt ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum
             ZF.Ordinal ZF.OrdQuant ZF.Nat_ZF ZF.QPair;

// def_swap_iff: a ≡ b ⟹ (a = c ⟷ c = b)   [≡ rendered as object equality]
opaque symbol def_swap_iff (a b c : τ ι) :
  π (a = b) → π ((a = c) ⇔ (c = b)) ≔
begin
  admit
end;

// def_trans: f ≡ g ⟹ g(a) = b ⟹ f(a) = b   [f ≡ g rendered pointwise]
opaque symbol def_trans (f g : τ ι → τ ι) (a b : τ ι) :
  (Π (x : τ ι), π (f x = g x)) → π (g a = b) → π (f a = b) ≔
begin
  admit
end;

// refl_thin: ⋀P. a = a ⟹ P ⟹ P
opaque symbol refl_thin (P : Prop) (a : τ ι) :
  π (a = a) → π P → π P ≔
begin
  admit
end;
