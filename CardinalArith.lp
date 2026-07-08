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
symbol InfCard (i : τ ι) : Prop ≔ Card i ∧ le omega i;

// i ⊗ j ≡ |i*j|
symbol cmult (i j : τ ι) : τ ι ≔ cardinal (Sigma i (λ _, j));

// i ⊕ j ≡ |i+j|
symbol cadd (i j : τ ι) : τ ι ≔ cardinal (sum i j);

// csquare_rel(K) ≡ rvimage(K*K, λ⟨x,y⟩∈K*K. ⟨x∪y,x,y⟩,
//                           rmult(K,Memrel(K), K*K, rmult(K,Memrel(K), K,Memrel(K))))
symbol csquare_rel (K : τ ι) : τ ι ≔
  rvimage (Sigma K (λ _, K))
    (Lambda (Sigma K (λ _, K))
       (λ p, Pair (Un (fst p) (snd p)) (Pair (fst p) (snd p))))
    (rmult K (Memrel K) (Sigma K (λ _, K)) (rmult K (Memrel K) K (Memrel K)));

// jump_cardinal(K) ≡ ⋃X∈Pow(K). {z. r∈Pow(K*K), well_ord(X,r) ∧ z=ordertype(X,r)}
symbol jump_cardinal (K : τ ι) : τ ι ≔
  Union (RepFun (Pow K) (λ X,
    RepFun (Collect (Pow (Sigma K (λ _, K))) (λ r, well_ord X r))
           (λ r, ordertype X r)));

// csucc(K) ≡ μL. Card(L) ∧ K<L
symbol csucc (K : τ ι) : τ ι ≔ Least (λ L, Card L ∧ lt K L);

// ===========================================================================

opaque symbol Card_Union (A : τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Card x)) → π (Card (Union A)) ≔
begin admit end;

opaque symbol Card_UN (A : τ ι) (f : τ ι → τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Card (f x))) → π (Card (Union (RepFun A f))) ≔
begin admit end;

opaque symbol Card_OUN (A : τ ι) (f : τ ι → τ ι) :
  (Π (x : τ ι), π (x ∈ A) → π (Card (f x))) → π (Card (OUnion A f)) ≔
begin admit end;

opaque symbol in_Card_imp_lesspoll (K b : τ ι) :
  π (Card K) → π (b ∈ K) → π (lesspoll b K) ≔
begin admit end;

// ===========================================================================
// Cardinal addition
// ===========================================================================

// Cardinal addition is commutative
opaque symbol sum_commute_eqpoll (A B : τ ι) :
  π (eqpoll (sum A B) (sum B A)) ≔
begin admit end;

opaque symbol cadd_commute (i j : τ ι) :
  π (cadd i j = cadd j i) ≔
begin admit end;

// Cardinal addition is associative
opaque symbol sum_assoc_eqpoll (A B C : τ ι) :
  π (eqpoll (sum (sum A B) C) (sum A (sum B C))) ≔
begin admit end;

// Unconditional version requires AC
opaque symbol well_ord_cadd_assoc (i ri j rj k rk : τ ι) :
  π (well_ord i ri) → π (well_ord j rj) → π (well_ord k rk) →
  π (cadd (cadd i j) k = cadd i (cadd j k)) ≔
begin admit end;

// 0 is the identity for addition
opaque symbol sum_0_eqpoll (A : τ ι) :
  π (eqpoll (sum empty A) A) ≔
begin admit end;

opaque symbol cadd_0 (K : τ ι) :
  π (Card K) → π (cadd empty K = K) ≔
begin admit end;

// Addition by another cardinal
opaque symbol sum_lepoll_self (A B : τ ι) :
  π (lepoll A (sum A B)) ≔
begin admit end;

// Could probably weaken the premises to well_ord(K,r), or removing using AC
opaque symbol cadd_le_self (K L : τ ι) :
  π (Card K) → π (Ord L) → π (le K (cadd K L)) ≔
begin admit end;

// Monotonicity of addition
opaque symbol sum_lepoll_mono (A C B D : τ ι) :
  π (lepoll A C) → π (lepoll B D) → π (lepoll (sum A B) (sum C D)) ≔
begin admit end;

opaque symbol cadd_le_mono (K' K L' L : τ ι) :
  π (le K' K) → π (le L' L) → π (le (cadd K' L') (cadd K L)) ≔
begin admit end;

// Addition of finite cardinals is "ordinary" addition
opaque symbol sum_succ_eqpoll (A B : τ ι) :
  π (eqpoll (sum (succ A) B) (succ (sum A B))) ≔
begin admit end;

// Pulling the succ(...) outside the |...| requires m, n ∈ nat
// Unconditional version requires AC
opaque symbol cadd_succ_lemma (m n : τ ι) :
  π (Ord m) → π (Ord n) → π (cadd (succ m) n = cardinal (succ (cadd m n))) ≔
begin admit end;

opaque symbol nat_cadd_eq_add (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (cadd m n = add m n) ≔
begin admit end;

// ===========================================================================
// Cardinal multiplication
// ===========================================================================

// Cardinal multiplication is commutative
opaque symbol prod_commute_eqpoll (A B : τ ι) :
  π (eqpoll (Sigma A (λ _, B)) (Sigma B (λ _, A))) ≔
begin admit end;

opaque symbol cmult_commute (i j : τ ι) :
  π (cmult i j = cmult j i) ≔
begin admit end;

// Cardinal multiplication is associative
opaque symbol prod_assoc_eqpoll (A B C : τ ι) :
  π (eqpoll (Sigma (Sigma A (λ _, B)) (λ _, C)) (Sigma A (λ _, Sigma B (λ _, C)))) ≔
begin admit end;

// Unconditional version requires AC
opaque symbol well_ord_cmult_assoc (i ri j rj k rk : τ ι) :
  π (well_ord i ri) → π (well_ord j rj) → π (well_ord k rk) →
  π (cmult (cmult i j) k = cmult i (cmult j k)) ≔
begin admit end;

// Cardinal multiplication distributes over addition
opaque symbol sum_prod_distrib_eqpoll (A B C : τ ι) :
  π (eqpoll (Sigma (sum A B) (λ _, C)) (sum (Sigma A (λ _, C)) (Sigma B (λ _, C)))) ≔
begin admit end;

opaque symbol well_ord_cadd_cmult_distrib (i ri j rj k rk : τ ι) :
  π (well_ord i ri) → π (well_ord j rj) → π (well_ord k rk) →
  π (cmult (cadd i j) k = cadd (cmult i k) (cmult j k)) ≔
begin admit end;

// Multiplication by 0 yields 0
opaque symbol prod_0_eqpoll (A : τ ι) :
  π (eqpoll (Sigma empty (λ _, A)) empty) ≔
begin admit end;

opaque symbol cmult_0 (i : τ ι) :
  π (cmult empty i = empty) ≔
begin admit end;

// 1 is the identity for multiplication
opaque symbol prod_singleton_eqpoll (x A : τ ι) :
  π (eqpoll (Sigma (singleton x) (λ _, A)) A) ≔
begin admit end;

opaque symbol cmult_1 (K : τ ι) :
  π (Card K) → π (cmult (succ empty) K = K) ≔
begin admit end;

// ===========================================================================
// Some inequalities for multiplication
// ===========================================================================

opaque symbol prod_square_lepoll (A : τ ι) :
  π (lepoll A (Sigma A (λ _, A))) ≔
begin admit end;

// Could probably weaken the premise to well_ord(K,r), or remove using AC
opaque symbol cmult_square_le (K : τ ι) :
  π (Card K) → π (le K (cmult K K)) ≔
begin admit end;

// Multiplication by a non-zero cardinal
opaque symbol prod_lepoll_self (A B b : τ ι) :
  π (b ∈ B) → π (lepoll A (Sigma A (λ _, B))) ≔
begin admit end;

// Could probably weaken the premises to well_ord(K,r), or removing using AC
opaque symbol cmult_le_self (K L : τ ι) :
  π (Card K) → π (Ord L) → π (lt empty L) → π (le K (cmult K L)) ≔
begin admit end;

// Monotonicity of multiplication
opaque symbol prod_lepoll_mono (A C B D : τ ι) :
  π (lepoll A C) → π (lepoll B D) → π (lepoll (Sigma A (λ _, B)) (Sigma C (λ _, D))) ≔
begin admit end;

opaque symbol cmult_le_mono (K' K L' L : τ ι) :
  π (le K' K) → π (le L' L) → π (le (cmult K' L') (cmult K L)) ≔
begin admit end;

// ===========================================================================
// Multiplication of finite cardinals is "ordinary" multiplication
// ===========================================================================

opaque symbol prod_succ_eqpoll (A B : τ ι) :
  π (eqpoll (Sigma (succ A) (λ _, B)) (sum B (Sigma A (λ _, B)))) ≔
begin admit end;

// Unconditional version requires AC
opaque symbol cmult_succ_lemma (m n : τ ι) :
  π (Ord m) → π (Ord n) → π (cmult (succ m) n = cadd n (cmult m n)) ≔
begin admit end;

opaque symbol nat_cmult_eq_mult (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (cmult m n = mult m n) ≔
begin admit end;

opaque symbol cmult_2 (n : τ ι) :
  π (Card n) → π (cmult (succ (succ empty)) n = cadd n n) ≔
begin admit end;

opaque symbol sum_lepoll_prod (C B : τ ι) :
  π (lepoll (succ (succ empty)) C) → π (lepoll (sum B B) (Sigma C (λ _, B))) ≔
begin admit end;

opaque symbol lepoll_imp_sum_lepoll_prod (A B : τ ι) :
  π (lepoll A B) → π (lepoll (succ (succ empty)) A) →
  π (lepoll (sum A B) (Sigma A (λ _, B))) ≔
begin admit end;

// ===========================================================================
// Infinite Cardinals are Limit Ordinals
// ===========================================================================

// This proof is modelled upon one assuming nat⊆A, with injection
// λz∈cons(u,A). if z=u then 0 else if z∈nat then succ(z) else z
// and inverse λy. if y∈nat then nat_case(u, λz.z, y) else y.
// If f∈inj(nat,A) then range(f) behaves like the natural numbers.
opaque symbol nat_cons_lepoll (A u : τ ι) :
  π (lepoll omega A) → π (lepoll (cons u A) A) ≔
begin admit end;

opaque symbol nat_cons_eqpoll (A u : τ ι) :
  π (lepoll omega A) → π (eqpoll (cons u A) A) ≔
begin admit end;

// Specialized version required below
opaque symbol nat_succ_eqpoll (A : τ ι) :
  π (omega ⊆ A) → π (eqpoll (succ A) A) ≔
begin admit end;

opaque symbol InfCard_nat :
  π (InfCard omega) ≔
begin admit end;

opaque symbol InfCard_is_Card (K : τ ι) :
  π (InfCard K) → π (Card K) ≔
begin admit end;

opaque symbol InfCard_Un (K L : τ ι) :
  π (InfCard K) → π (Card L) → π (InfCard (Un K L)) ≔
begin admit end;

// Kunen's Lemma 10.11
opaque symbol InfCard_is_Limit (K : τ ι) :
  π (InfCard K) → π (Limit K) ≔
begin admit end;

// ===========================================================================
// An infinite cardinal equals its square (Kunen, Thm 10.12, page 29)
// ===========================================================================

// A general fact about ordermap
// (NB: `ZF.Order.pred` qualified — Arith's unary predecessor `pred`, opened
// transitively via ZF.ArithSimp below, shadows Order's ternary `pred`.)
opaque symbol ordermap_eqpoll_pred (A r x : τ ι) :
  π (well_ord A r) → π (x ∈ A) →
  π (eqpoll (fapply (ordermap A r) x) (ZF.Order.pred A x r)) ≔
begin admit end;

// Establishing the well-ordering
opaque symbol well_ord_csquare (K : τ ι) :
  π (Ord K) → π (well_ord (Sigma K (λ _, K)) (csquare_rel K)) ≔
begin admit end;

// Characterising initial segments of the well-ordering

opaque symbol csquareD (x y z K : τ ι) :
  π (Pair (Pair x y) (Pair z z) ∈ csquare_rel K) →
  π (lt x K) → π (lt y K) → π (lt z K) →
  π (le x z ∧ le y z) ≔
begin admit end;

opaque symbol pred_csquare_subset (z K : τ ι) :
  π (lt z K) →
  π (ZF.Order.pred (Sigma K (λ _, K)) (Pair z z) (csquare_rel K) ⊆
     Sigma (succ z) (λ _, succ z)) ≔
begin admit end;

opaque symbol csquare_ltI (x y z K : τ ι) :
  π (lt x z) → π (lt y z) → π (lt z K) →
  π (Pair (Pair x y) (Pair z z) ∈ csquare_rel K) ≔
begin admit end;

// Part of the traditional proof. UNUSED since it's harder to prove and apply
opaque symbol csquare_or_eqI (x y z K : τ ι) :
  π (le x z) → π (le y z) → π (lt z K) →
  π ((Pair (Pair x y) (Pair z z) ∈ csquare_rel K) ∨ (x = z ∧ y = z)) ≔
begin admit end;

// The cardinality of initial segments

opaque symbol ordermap_z_lt (K x y z : τ ι) :
  π (Limit K) → π (lt x K) → π (lt y K) → π (z = succ (Un x y)) →
  π (lt (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y))
       (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair z z))) ≔
begin admit end;

// Kunen: "each ⟨x,y⟩∈K×K has no more than z×z predecessors..." (page 29)
// (z ≡ succ(x∪y), inlined — a pure local abbreviation in the Isar source)
opaque symbol ordermap_csquare_le (K x y : τ ι) :
  π (Limit K) → π (lt x K) → π (lt y K) →
  π (le (cardinal (fapply (ordermap (Sigma K (λ _, K)) (csquare_rel K)) (Pair x y)))
       (cmult (cardinal (succ (succ (Un x y)))) (cardinal (succ (succ (Un x y)))))) ≔
begin admit end;

// Kunen: "... so the order type is ≤ K"
opaque symbol ordertype_csquare_le (K : τ ι) :
  π (InfCard K) →
  (Π (y : τ ι), π (y ∈ K) → π (InfCard y) → π (cmult y y = y)) →
  π (le (ordertype (Sigma K (λ _, K)) (csquare_rel K)) K) ≔
begin admit end;

// Main result: Kunen's Theorem 10.12
opaque symbol InfCard_csquare_eq (K : τ ι) :
  π (InfCard K) → π (cmult K K = K) ≔
begin admit end;

// Corollary for arbitrary well-ordered sets (all sets, assuming AC)
opaque symbol well_ord_InfCard_square_eq (A r : τ ι) :
  π (well_ord A r) → π (InfCard (cardinal A)) → π (eqpoll (Sigma A (λ _, A)) A) ≔
begin admit end;

opaque symbol InfCard_square_eqpoll (K : τ ι) :
  π (InfCard K) → π (eqpoll (Sigma K (λ _, K)) K) ≔
begin admit end;

opaque symbol Inf_Card_is_InfCard (i : τ ι) :
  π (Card i) → π (¬ (Finite i)) → π (InfCard i) ≔
begin admit end;

// Toward's Kunen's Corollary 10.13 (1)

opaque symbol InfCard_le_cmult_eq (K L : τ ι) :
  π (InfCard K) → π (le L K) → π (lt empty L) → π (cmult K L = K) ≔
begin admit end;

// Corollary 10.13 (1), for cardinal multiplication
opaque symbol InfCard_cmult_eq (K L : τ ι) :
  π (InfCard K) → π (InfCard L) → π (cmult K L = Un K L) ≔
begin admit end;

opaque symbol InfCard_cdouble_eq (K : τ ι) :
  π (InfCard K) → π (cadd K K = K) ≔
begin admit end;

// Corollary 10.13 (1), for cardinal addition
opaque symbol InfCard_le_cadd_eq (K L : τ ι) :
  π (InfCard K) → π (le L K) → π (cadd K L = K) ≔
begin admit end;

opaque symbol InfCard_cadd_eq (K L : τ ι) :
  π (InfCard K) → π (InfCard L) → π (cadd K L = Un K L) ≔
begin admit end;

// The other part, Corollary 10.13 (2), refers to the cardinality of the set
// of all n-tuples of elements of K. A better version for the Isabelle theory
// might be InfCard(K) ⟹ |list(K)| = K.  (No statement to port — remark only.)

// ===========================================================================
// For Every Cardinal Number There Exists A Greater One
// ===========================================================================

// This result is Kunen's Theorem 10.16, which would be trivial using AC

opaque symbol Ord_jump_cardinal (K : τ ι) :
  π (Ord (jump_cardinal K)) ≔
begin admit end;

// Allows selective unfolding. Less work than deriving intro/elim rules
opaque symbol jump_cardinal_iff (i K : τ ι) :
  π (i ∈ jump_cardinal K ⇔
     (`∃ (r : τ ι), `∃ (X : τ ι),
        r ⊆ Sigma K (λ _, K) ∧ X ⊆ K ∧ well_ord X r ∧ i = ordertype X r)) ≔
begin admit end;

// The easy part of Theorem 10.16: jump_cardinal(K) exceeds K
opaque symbol K_lt_jump_cardinal (K : τ ι) :
  π (Ord K) → π (lt K (jump_cardinal K)) ≔
begin admit end;

// The proof by contradiction: the bijection f yields a wellordering of X
// whose ordertype is jump_cardinal(K).
opaque symbol Card_jump_cardinal_lemma (X r K f : τ ι) :
  π (well_ord X r) → π (r ⊆ Sigma K (λ _, K)) → π (X ⊆ K) →
  π (f ∈ bij (ordertype X r) (jump_cardinal K)) →
  π (jump_cardinal K ∈ jump_cardinal K) ≔
begin admit end;

// The hard part of Theorem 10.16: jump_cardinal(K) is itself a cardinal
opaque symbol Card_jump_cardinal (K : τ ι) :
  π (Card (jump_cardinal K)) ≔
begin admit end;

// ===========================================================================
// Basic Properties of Successor Cardinals
// ===========================================================================

opaque symbol csucc_basic (K : τ ι) :
  π (Ord K) → π (Card (csucc K) ∧ lt K (csucc K)) ≔
begin admit end;

// Card_csucc = csucc_basic [THEN conjunct1] : Ord(K) ⟹ Card(csucc(K))
opaque symbol Card_csucc (K : τ ι) :
  π (Ord K) → π (Card (csucc K)) ≔
begin admit end;

// lt_csucc = csucc_basic [THEN conjunct2] : Ord(K) ⟹ K < csucc(K)
opaque symbol lt_csucc (K : τ ι) :
  π (Ord K) → π (lt K (csucc K)) ≔
begin admit end;

opaque symbol Ord_0_lt_csucc (K : τ ι) :
  π (Ord K) → π (lt empty (csucc K)) ≔
begin admit end;

opaque symbol csucc_le (K L : τ ι) :
  π (Card L) → π (lt K L) → π (le (csucc K) L) ≔
begin admit end;

opaque symbol lt_csucc_iff (i K : τ ι) :
  π (Ord i) → π (Card K) → π (lt i (csucc K) ⇔ le (cardinal i) K) ≔
begin admit end;

opaque symbol Card_lt_csucc_iff (K' K : τ ι) :
  π (Card K') → π (Card K) → π (lt K' (csucc K) ⇔ le K' K) ≔
begin admit end;

opaque symbol InfCard_csucc (K : τ ι) :
  π (InfCard K) → π (InfCard (csucc K)) ≔
begin admit end;

// ===========================================================================
// Removing elements from a finite set decreases its cardinality
// ===========================================================================

opaque symbol Finite_imp_cardinal_cons (A a : τ ι) :
  π (Finite A) → π (a ∉ A) → π (cardinal (cons a A) = succ (cardinal A)) ≔
begin admit end;

opaque symbol Finite_imp_succ_cardinal_Diff (A a : τ ι) :
  π (Finite A) → π (a ∈ A) →
  π (succ (cardinal (Diff A (singleton a))) = cardinal A) ≔
begin admit end;

opaque symbol Finite_imp_cardinal_Diff (A a : τ ι) :
  π (Finite A) → π (a ∈ A) → π (lt (cardinal (Diff A (singleton a))) (cardinal A)) ≔
begin admit end;

opaque symbol Finite_cardinal_in_nat (A : τ ι) :
  π (Finite A) → π (cardinal A ∈ omega) ≔
begin admit end;

opaque symbol card_Un_Int (A B : τ ι) :
  π (Finite A) → π (Finite B) →
  π (add (cardinal A) (cardinal B) = add (cardinal (Un A B)) (cardinal (Int A B))) ≔
begin admit end;

opaque symbol card_Un_disjoint (A B : τ ι) :
  π (Finite A) → π (Finite B) → π (Int A B = empty) →
  π (cardinal (Un A B) = add (cardinal A) (cardinal B)) ≔
begin admit end;

opaque symbol card_partition (C k : τ ι) :
  π (Finite C) → π (Finite (Union C)) →
  π (Ball C (λ c, cardinal c = k)) →
  π (Ball C (λ c1, Ball C (λ c2, c1 ≠ c2 ⇒ Int c1 c2 = empty))) →
  π (mult k (cardinal C) = cardinal (Union C)) ≔
begin admit end;

// ===========================================================================
// Theorems by Krzysztof Grabczewski, proofs by lcp
// ===========================================================================

// nat_implies_well_ord = nat_into_Ord [THEN well_ord_Memrel] :
//   n ∈ nat ⟹ well_ord(n, Memrel(n))
opaque symbol nat_implies_well_ord (n : τ ι) :
  π (n ∈ omega) → π (well_ord n (Memrel n)) ≔
begin admit end;

opaque symbol nat_sum_eqpoll_sum (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (eqpoll (sum m n) (add m n)) ≔
begin admit end;

opaque symbol Ord_subset_natD (i : τ ι) :
  π (Ord i) → π (i ⊆ omega) → π (i ∈ omega ∨ i = omega) ≔
begin admit end;

opaque symbol Ord_nat_subset_into_Card (i : τ ι) :
  π (Ord i) → π (i ⊆ omega) → π (Card i) ≔
begin admit end;
