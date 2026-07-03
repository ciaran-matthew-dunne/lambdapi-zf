// Inductive: glue lemmas for the inductive-definition package.
//
// Isabelle source: Inductive.thy.  That theory is almost entirely the ML
// `inductive`/`coinductive`/`primrec` PACKAGE (ind_syntax.ML, inductive_package.ML,
// …) which has no object-level content to port.  It contributes exactly three
// tiny "glue" lemmas, used by the package's definition-unfolding tactics.  They
// are meta-level (`≡`) in Isabelle; rendered here object-level.
//
// All three glue lemmas are fully proved (no admits).

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
             Stdlib.Classic Stdlib.Impred Stdlib.HOL Stdlib.PropExt;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func
             ZF.Fixedpt ZF.Trancl ZF.WF ZF.Perm ZF.Bool_ZF ZF.Sum
             ZF.Ordinal ZF.OrdQuant ZF.Nat_ZF ZF.QPair;

// def_swap_iff: a ≡ b ⟹ (a = c ⟷ c = b)   [≡ rendered as object equality]
opaque symbol def_swap_iff (a b c : τ ι) :
  π (a = b) → π ((a = c) ⇔ (c = b)) ≔
begin
  assume a b c h;
  rewrite h;                        // goal: (b = c) ⇔ (c = b)
  apply ∧ᵢ
  { assume h1; refine eq_sym h1 }
  { assume h1; refine eq_sym h1 }
end;

// def_trans: f ≡ g ⟹ g(a) = b ⟹ f(a) = b   [f ≡ g rendered pointwise]
opaque symbol def_trans (f g : τ ι → τ ι) (a b : τ ι) :
  (Π (x : τ ι), π (f x = g x)) → π (g a = b) → π (f a = b) ≔
begin
  assume f g a b hfg hgab;
  rewrite (hfg a);                  // goal: g a = b
  refine hgab
end;

// refl_thin: ⋀P. a = a ⟹ P ⟹ P
opaque symbol refl_thin (P : Prop) (a : τ ι) :
  π (a = a) → π P → π P ≔
begin
  assume P a h hP;
  refine hP
end;
