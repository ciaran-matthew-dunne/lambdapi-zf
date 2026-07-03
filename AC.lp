// AC: Axiom of Choice
//
// Isabelle source: AC.thy
// The AC states: for every set A of nonempty sets,
// there exists a choice function picking one element from each

require open ZF.ZF_Base ZF.upair ZF.pair;

// ===========================================================================
// Axiom of Choice
// ===========================================================================

// AC: for every set of nonempty sets, there is a choice function
// ∀A. (∀x∈A. x ≠ 0) → ∃f. ∀x∈A. f`x ∈ x
// We state it in the simpler "every set can be well-ordered" form:

// For every set A, there exists a well-ordering on A
// (equivalently: every surjection has a right inverse)

// Simple form: for every family of nonempty sets, we can choose one element from each
constant symbol AC :
  π (`∀ (A : τ ι), Ball A (λ x, x ≠ empty) ⇒
     `∃ (f : τ ι), Ball A (λ x, `∃ (y : τ ι), y ∈ x ∧ Pair x y ∈ f));
