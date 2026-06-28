// Univ.lp — The cumulative hierarchy Vfrom/Vset.
// Translated from Isabelle/ZF Univ.thy (Paulson).
//
// Key definitions: Vfrom(A,i), Vset(i) = Vfrom(0,i)
// Key results: unfolding, monotonicity, 0/succ/limit cases,
//   rank characterization of membership.

require open Stdlib.Set Stdlib.Prop Stdlib.FOL Stdlib.Eq
            Stdlib.Classic Stdlib.Impred Stdlib.HOL
            Stdlib.PropExt Stdlib.Epsilon;
require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities
            ZF.func ZF.Fixedpt ZF.Trancl ZF.WF ZF.Ordinal ZF.Epsilon;

// ===========================================================================
// Vfrom(A, i) = A ∪ ⋃_{j ∈ i} Pow(Vfrom(A, j))
// Defined via transrec: Vfrom(A,i) = transrec(i, λx f. A ∪ ⋃_{y∈x} Pow(f`y))
// ===========================================================================

symbol Vfrom (A i : τ ι) : τ ι ≔
  transrec i (λ x f, Un A (Union (RepFun x (λ y, Pow (fapply f y)))));

// Vset(i) = Vfrom(∅, i)
symbol Vset (i : τ ι) : τ ι ≔ Vfrom empty i;

// ---------------------------------------------------------------------------
// Unfolding
// ---------------------------------------------------------------------------

// Vfrom(A, i) = A ∪ ⋃_{j ∈ i} Pow(Vfrom(A, j))
constant symbol Vfrom_eq (A i : τ ι) :
  π (Vfrom A i = Un A (Union (RepFun i (λ j, Pow (Vfrom A j)))));

// Vset(i) = ⋃_{j ∈ i} Pow(Vset(j))
// (Since A = ∅, the A ∪ ... simplifies to just the union)
constant symbol Vset_eq (i : τ ι) :
  π (Vset i = Union (RepFun i (λ j, Pow (Vset j))));

// ---------------------------------------------------------------------------
// Base cases
// ---------------------------------------------------------------------------

// Vfrom(A, 0) = A
constant symbol Vfrom_0 (A : τ ι) :
  π (Vfrom A empty = A);

// Vset(0) = ∅
constant symbol Vset_0 : π (Vset empty = empty);

// ---------------------------------------------------------------------------
// Successor
// ---------------------------------------------------------------------------

// Vfrom(A, succ(i)) = A ∪ Pow(Vfrom(A, i))
constant symbol Vfrom_succ (A i : τ ι) :
  π (Vfrom A (succ i) = Un A (Pow (Vfrom A i)));

// Vset(succ(i)) = Pow(Vset(i))
constant symbol Vset_succ (i : τ ι) :
  π (Vset (succ i) = Pow (Vset i));

// Transset(A) → Vfrom(A, succ(i)) = Pow(Vfrom(A, i))
// (A is absorbed into Pow since A ⊆ Vfrom(A,i))
constant symbol Vfrom_succ_Transset (A i : τ ι) :
  π (Transset A) → π (Vfrom A (succ i) = Pow (Vfrom A i));

// ---------------------------------------------------------------------------
// Limit
// ---------------------------------------------------------------------------

// Limit(i) → Vfrom(A, i) = ⋃_{j ∈ i} Vfrom(A, j)
constant symbol Limit_Vfrom_eq (A i : τ ι) :
  π (Limit i) → π (Vfrom A i = Union (RepFun i (λ j, Vfrom A j)));

// Limit(i) → Vset(i) = ⋃_{j ∈ i} Vset(j)
constant symbol Limit_Vset_eq (i : τ ι) :
  π (Limit i) → π (Vset i = Union (RepFun i (λ j, Vset j)));

// ---------------------------------------------------------------------------
// Monotonicity
// ---------------------------------------------------------------------------

// A ⊆ B → i ⊆ j → Vfrom(A, i) ⊆ Vfrom(B, j)
constant symbol Vfrom_mono (A B i j : τ ι) :
  π (A ⊆ B) → π (i ⊆ j) → π (Vfrom A i ⊆ Vfrom B j);

// Vfrom(A, rank(x)) = Vfrom(A, x)
constant symbol Vfrom_rank_eq (A x : τ ι) :
  π (Vfrom A (rank x) = Vfrom A x);

// ---------------------------------------------------------------------------
// Inclusion properties
// ---------------------------------------------------------------------------

// A ⊆ Vfrom(A, i)
constant symbol A_subset_Vfrom (A i : τ ι) :
  π (A ⊆ Vfrom A i);

// i ⊆ Vfrom(A, i)
constant symbol i_subset_Vfrom (A i : τ ι) :
  π (i ⊆ Vfrom A i);

// Transset(A) → Transset(Vfrom(A, i))
constant symbol Transset_Vfrom (A i : τ ι) :
  π (Transset A) → π (Transset (Vfrom A i));

// Transset(Vset(i))
constant symbol Transset_Vset (i : τ ι) :
  π (Transset (Vset i));

// ---------------------------------------------------------------------------
// Rank characterization of Vset membership
// ---------------------------------------------------------------------------

// Ord(i) → b ∈ Vset(i) → rank(b) < i
constant symbol VsetD (i b : τ ι) :
  π (Ord i) → π (b ∈ Vset i) → π (lt (rank b) i);

// rank(x) < i → x ∈ Vset(i)
constant symbol VsetI (x i : τ ι) :
  π (lt (rank x) i) → π (x ∈ Vset i);

// b ∈ Vset(a) ↔ rank(b) < rank(a)
constant symbol Vset_rank_iff (a b : τ ι) :
  π (b ∈ Vset a ⇔ lt (rank b) (rank a));

// Ord(i) → rank(Vset(i)) = i
constant symbol rank_Vset (i : τ ι) :
  π (Ord i) → π (rank (Vset i) = i);

// Every set belongs to some Vset
constant symbol Vset_rank_exists (x : τ ι) :
  π (`∃ i : τ ι, Ord i ∧ x ∈ Vset i);
