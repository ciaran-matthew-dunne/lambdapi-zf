// ZF.List — Lists in Zermelo-Fraenkel Set Theory
// Faithful SKELETON port of isabelle-src/List.thy.
// Every definition is given; every lemma/theorem is stated and `admit`ted.
// (Source: L. C. Paulson, ZF/List.thy.)
//
// BOOTSTRAP (hand-built, no proofs — analogous to Finite.lp's Fin/FiniteFun
// and Zorn.lp's TFin, which likewise reconstruct what Isabelle's `datatype`/
// `inductive` package generates):
//
//   list(A) is the package-generated datatype "list(A) = Nil | Cons(a∈A,l∈list(A))".
//   Its ACTUAL Isabelle encoding (Datatype.thy's Standard_Sum instantiation) is
//   the least fixed point, domain univ(A), of X ↦ {0} + (A*X):
//     Nil      = Inl(0)
//     Cons a l = Inr(⟨a,l⟩)
//   freeness (Nil≠Cons(..), Cons injective) follows from Inl/Inr already being
//   proved disjoint+injective in Sum.lp — this is exactly why the package
//   itself picks a disjoint-sum encoding, and why we do too.
//
//   list_case/list_rec are the package-generated case-analysis/recursor.
//   list_case is a direct (non-recursive) combinator, `≔`-defined.  list_rec
//   is recursive (built on Vrec, i.e. Vset-rank recursion) — per Arith.lp's
//   established precedent (see that file's header) recursive definitions here
//   are ABSTRACT symbols with a defining *_def AXIOM rather than a `≔` body,
//   to keep the kernel from eagerly unfolding Vrec/transrec/rank during
//   conversion checking.  `list_rec_def` IS the Isabelle definition, faithfully.
//
//   Every other primrec'd function in List.thy (length, hd, tl, map, app,
//   rev, flat, list_add, drop, filter, upt, zip_aux, repeat) is a direct
//   instance of list_rec — e.g. length ≔ list_rec(0, λx xs r. succ(r)).
//   `take`/`nth`/`list_update` are defined via list_rec directly in the .thy
//   too (not `primrec`), same treatment.

require open ZF.Datatype ZF.ArithSimp;

// ===========================================================================
// The datatype list(A), its constructors, case analysis and recursor
// ===========================================================================

symbol list (A : τ ι) : τ ι ≔
  lfp (univ A) (λ X, sum (singleton empty) (Sigma A (λ _, X)));

symbol Nil : τ ι ≔ Inl empty;
symbol Cons (a l : τ ι) : τ ι ≔ Inr (Pair a l);

symbol list_case (c : τ ι) (h : τ ι → τ ι → τ ι) (l : τ ι) : τ ι ≔
  case_sum (λ _, c) (split h) l;

// list_rec(c,h,l) ≡ Vrec(l, λl2 g. list_case(c, λx xs. h(x,xs,g`xs), l2))
symbol list_rec : τ ι → (τ ι → τ ι → τ ι → τ ι) → τ ι → τ ι;
opaque symbol list_rec_def (c : τ ι) (h : τ ι → τ ι → τ ι → τ ι) (l : τ ι) :
  π (list_rec c h l =
     Vrec l (λ l2 g, list_case c (λ x xs, h x xs (fapply g xs)) l2)) ≔
begin admit end;

// ===========================================================================
// Basic freeness / typing (`declare list.intros [simp,TC]`,
// `inductive_cases ConsE`, and the immediate freeness lemmas)
// ===========================================================================

opaque symbol list_0I (A : τ ι) : π (Nil ∈ list A) ≔
begin admit end;

opaque symbol list_consI (a l A : τ ι) :
  π (a ∈ A) → π (l ∈ list A) → π (Cons a l ∈ list A) ≔
begin admit end;

// inductive_cases ConsE: elimination rule for Cons(a,l) ∈ list(A)
opaque symbol ConsE (a l A : τ ι) (P : Prop) :
  π (Cons a l ∈ list A) → (π (a ∈ A) → π (l ∈ list A) → π P) → π P ≔
begin admit end;

opaque symbol Cons_type_iff (a l A : τ ι) :
  π (Cons a l ∈ list A ⇔ (a ∈ A ∧ l ∈ list A)) ≔
begin admit end;

// Proving freeness results
opaque symbol Cons_iff (a l a' l' : τ ι) :
  π (Cons a l = Cons a' l' ⇔ (a = a' ∧ l = l')) ≔
begin admit end;

opaque symbol Nil_Cons_iff (a l : τ ι) : π (¬ (Nil = Cons a l)) ≔
begin admit end;

opaque symbol list_unfold (A : τ ι) :
  π (list A = sum (singleton empty) (Sigma A (λ _, list A))) ≔
begin admit end;

// ===========================================================================
// Lemmas to justify using "list" in other recursive type definitions
// ===========================================================================

opaque symbol list_mono (A B : τ ι) : π (A ⊆ B) → π (list A ⊆ list B) ≔
begin admit end;

// There is a similar proof by list induction.
opaque symbol list_univ (A : τ ι) : π (list (univ A) ⊆ univ A) ≔
begin admit end;

// These two theorems justify datatypes involving list(nat), list(A), ...
opaque symbol list_subset_univ (A B : τ ι) : π (A ⊆ univ B) → π (list A ⊆ univ B) ≔
begin admit end;

opaque symbol list_into_univ (l A B : τ ι) :
  π (l ∈ list A) → π (A ⊆ univ B) → π (l ∈ univ B) ≔
begin admit end;

opaque symbol list_case_type (l A c : τ ι) (h : τ ι → τ ι → τ ι) (C : τ ι → τ ι) :
  π (l ∈ list A) → π (c ∈ C Nil) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ list A) → π (h x y ∈ C (Cons x y))) →
  π (list_case c h l ∈ C l) ≔
begin admit end;

opaque symbol list_0_triv : π (list empty = singleton Nil) ≔
begin admit end;

// ===========================================================================
// List functions
// ===========================================================================

symbol length (l : τ ι) : τ ι ≔ list_rec empty (λ a l2 r, succ r) l;
symbol hd (l : τ ι) : τ ι ≔ list_rec empty (λ a l2 r, a) l;
symbol tl (l : τ ι) : τ ι ≔ list_rec Nil (λ a l2 r, l2) l;

opaque symbol tl_type (l A : τ ι) : π (l ∈ list A) → π (tl l ∈ list A) ≔
begin admit end;

// ===========================================================================
// map, set_of_list, app
// ===========================================================================

symbol map (f : τ ι → τ ι) (l : τ ι) : τ ι ≔
  list_rec Nil (λ a l2 r, Cons (f a) r) l;

symbol set_of_list (l : τ ι) : τ ι ≔ list_rec empty (λ a l2 r, cons a r) l;

symbol app (xs ys : τ ι) : τ ι ≔ list_rec ys (λ a l2 r, Cons a r) xs;
notation app infix right 60;

symbol rev (l : τ ι) : τ ι ≔ list_rec Nil (λ a l2 r, app r (Cons a Nil)) l;

symbol flat (l : τ ι) : τ ι ≔ list_rec Nil (λ a l2 r, app a r) l;

symbol list_add (l : τ ι) : τ ι ≔ list_rec empty (λ a l2 r, add a r) l;

symbol drop (i l : τ ι) : τ ι ≔ nat_rec i l (λ i2 r, tl r);

// ===========================================================================
// (** Type checking -- proved by induction, as usual **))
// ===========================================================================

opaque symbol list_rec_type (l A c : τ ι) (h : τ ι → τ ι → τ ι → τ ι) (C : τ ι → τ ι) :
  π (l ∈ list A) → π (c ∈ C Nil) →
  (Π (x y r : τ ι), π (x ∈ A) → π (y ∈ list A) → π (r ∈ C y) →
    π (h x y r ∈ C (Cons x y))) →
  π (list_rec c h l ∈ C l) ≔
begin admit end;

// ===========================================================================
// map
// ===========================================================================

opaque symbol map_type (l A B : τ ι) (h : τ ι → τ ι) :
  π (l ∈ list A) → (Π (x : τ ι), π (x ∈ A) → π (h x ∈ B)) →
  π (map h l ∈ list B) ≔
begin admit end;

opaque symbol map_type2 (l A : τ ι) (h : τ ι → τ ι) :
  π (l ∈ list A) → π (map h l ∈ list (RepFun A h)) ≔
begin admit end;

// ===========================================================================
// length
// ===========================================================================

opaque symbol length_type (l A : τ ι) : π (l ∈ list A) → π (length l ∈ omega) ≔
begin admit end;

opaque symbol lt_length_in_nat (x l A : τ ι) :
  π (lt x (length l)) → π (l ∈ list A) → π (x ∈ omega) ≔
begin admit end;

// ===========================================================================
// app
// ===========================================================================

opaque symbol app_type (xs ys A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (app xs ys ∈ list A) ≔
begin admit end;

// ===========================================================================
// rev
// ===========================================================================

opaque symbol rev_type (xs A : τ ι) : π (xs ∈ list A) → π (rev xs ∈ list A) ≔
begin admit end;

// ===========================================================================
// flat
// ===========================================================================

opaque symbol flat_type (ls A : τ ι) : π (ls ∈ list (list A)) → π (flat ls ∈ list A) ≔
begin admit end;

// ===========================================================================
// set_of_list
// ===========================================================================

opaque symbol set_of_list_type (l A : τ ι) :
  π (l ∈ list A) → π (set_of_list l ∈ Pow A) ≔
begin admit end;

opaque symbol set_of_list_append (xs ys A : τ ι) :
  π (xs ∈ list A) →
  π (set_of_list (app xs ys) = Un (set_of_list xs) (set_of_list ys)) ≔
begin admit end;

// ===========================================================================
// list_add
// ===========================================================================

opaque symbol list_add_type (xs : τ ι) : π (xs ∈ list omega) → π (list_add xs ∈ omega) ≔
begin admit end;

// ===========================================================================
// More list functions: take, nth, list_update, filter, upt, min, max,
// zip_aux, zip, sublist, repeat
// (Grouped here, right after the base list functions/typing lemmas above,
//  because Lambdapi requires define-before-use.  The .thy itself scatters
//  these definitions earlier, interleaved with "drop" near the top of the
//  file (isabelle-src/List.thy lines 90-127), well before the "Aspects of
//  the datatype definition" section that the bootstrap already ported.)
// ===========================================================================

symbol take (n xs : τ ι) : τ ι ≔
  fapply (list_rec (Lambda omega (λ _, Nil))
    (λ a l r, Lambda omega (λ n2, nat_case Nil (λ m, Cons a (fapply r m)) n2)) xs) n;

symbol nth (n xs : τ ι) : τ ι ≔
  fapply (list_rec (Lambda omega (λ _, empty))
    (λ a l r, Lambda omega (λ n2, nat_case a (λ m, fapply r m) n2)) xs) n;

symbol list_update (xs i v : τ ι) : τ ι ≔
  fapply (list_rec (Lambda omega (λ _, Nil))
    (λ u us vs, Lambda omega
      (λ n2, nat_case (Cons v us) (λ m, Cons u (fapply vs m)) n2)) xs) i;

symbol filter (P : τ ι → Prop) (l : τ ι) : τ ι ≔
  list_rec Nil (λ x xs r, If (P x) (Cons x r) r) l;

symbol upt (i j : τ ι) : τ ι ≔
  nat_rec j Nil (λ j2 r, If (le i j2) (app r (Cons j2 Nil)) Nil);

symbol min (x y : τ ι) : τ ι ≔ If (le x y) x y;
symbol max (x y : τ ι) : τ ι ≔ If (le x y) y x;

// zip_aux(B,l) recurses on l, closing over B; used to give zip(xs,ys) its
// type without needing ys's element type as an extra explicit argument.
symbol zip_aux (B l : τ ι) : τ ι ≔
  list_rec
    (Lambda (list B) (λ ys, list_case Nil (λ y l2, Nil) ys))
    (λ x l2 r,
       Lambda (list B) (λ ys, list_case Nil (λ y zs, Cons (Pair x y) (fapply r zs)) ys))
    l;

symbol zip (xs ys : τ ι) : τ ι ≔ fapply (zip_aux (set_of_list ys) xs) ys;

symbol sublist (xs A : τ ι) : τ ι ≔
  map fst (filter (λ p, snd p ∈ A) (zip xs (upt empty (length xs))));

// Named `list_repeat`, not `repeat` (Isabelle's name): `repeat` is a
// reserved tactical keyword in Lambdapi (the `repeat` tactic combinator).
symbol list_repeat (a n : τ ι) : τ ι ≔ nat_rec n Nil (λ n2 r, Cons a r);

// ===========================================================================
// (** drop **)
// ===========================================================================

opaque symbol drop_Nil (i : τ ι) : π (i ∈ omega) → π (drop i Nil = Nil) ≔
begin admit end;

opaque symbol drop_succ_Cons (i a l : τ ι) :
  π (i ∈ omega) → π (drop (succ i) (Cons a l) = drop i l) ≔
begin admit end;

opaque symbol drop_type (i l A : τ ι) :
  π (i ∈ omega) → π (l ∈ list A) → π (drop i l ∈ list A) ≔
begin admit end;

// declare drop_succ [simp del]: an attribute toggle on the primrec equation
// already captured by `drop`'s definition above — no new content.

// ===========================================================================
// theorems about map
// ===========================================================================

opaque symbol map_ident (l A : τ ι) : π (l ∈ list A) → π (map (λ u, u) l = l) ≔
begin admit end;

opaque symbol map_compose (l A : τ ι) (h j : τ ι → τ ι) :
  π (l ∈ list A) → π (map h (map j l) = map (λ u, h (j u)) l) ≔
begin admit end;

opaque symbol map_app_distrib (xs A ys : τ ι) (h : τ ι → τ ι) :
  π (xs ∈ list A) → π (map h (app xs ys) = app (map h xs) (map h ys)) ≔
begin admit end;

opaque symbol map_flat (ls A : τ ι) (h : τ ι → τ ι) :
  π (ls ∈ list (list A)) → π (map h (flat ls) = flat (map (map h) ls)) ≔
begin admit end;

opaque symbol list_rec_map (l A c : τ ι) (d : τ ι → τ ι → τ ι → τ ι) (h : τ ι → τ ι) :
  π (l ∈ list A) →
  π (list_rec c d (map h l) = list_rec c (λ x xs r, d (h x) (map h xs) r) l) ≔
begin admit end;

// list_CollectD = Collect_subset [THEN list_mono, THEN subsetD]
opaque symbol list_CollectD (A : τ ι) (P : τ ι → Prop) (c : τ ι) :
  π (c ∈ list (Collect A P)) → π (c ∈ list A) ≔
begin admit end;

opaque symbol map_list_Collect (l A : τ ι) (h j : τ ι → τ ι) :
  π (l ∈ list (Collect A (λ x, h x = j x))) → π (map h l = map j l) ≔
begin admit end;

// ===========================================================================
// theorems about length
// ===========================================================================

opaque symbol length_map (xs A : τ ι) (h : τ ι → τ ι) :
  π (xs ∈ list A) → π (length (map h xs) = length xs) ≔
begin admit end;

opaque symbol length_app (xs ys A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) →
  π (length (app xs ys) = add (length xs) (length ys)) ≔
begin admit end;

opaque symbol length_rev (xs A : τ ι) : π (xs ∈ list A) → π (length (rev xs) = length xs) ≔
begin admit end;

opaque symbol length_flat (ls A : τ ι) :
  π (ls ∈ list (list A)) → π (length (flat ls) = list_add (map length ls)) ≔
begin admit end;

// ===========================================================================
// Length and drop
// ===========================================================================

// Lemma for the inductive step of drop_length
opaque symbol drop_length_Cons (xs A x : τ ι) :
  π (xs ∈ list A) →
  π (`∃ (z : τ ι), `∃ (zs : τ ι), drop (length xs) (Cons x xs) = Cons z zs) ≔
begin admit end;

opaque symbol drop_length (l A i : τ ι) :
  π (l ∈ list A) → π (i ∈ length l) →
  π (`∃ (z : τ ι), `∃ (zs : τ ι), drop i l = Cons z zs) ≔
begin admit end;

// ===========================================================================
// theorems about app
// ===========================================================================

opaque symbol app_right_Nil (xs A : τ ι) : π (xs ∈ list A) → π (app xs Nil = xs) ≔
begin admit end;

opaque symbol app_assoc (xs A ys zs : τ ι) :
  π (xs ∈ list A) → π (app (app xs ys) zs = app xs (app ys zs)) ≔
begin admit end;

opaque symbol flat_app_distrib (ls A ms : τ ι) :
  π (ls ∈ list (list A)) → π (flat (app ls ms) = app (flat ls) (flat ms)) ≔
begin admit end;

// ===========================================================================
// theorems about rev
// ===========================================================================

opaque symbol rev_map_distrib (l A : τ ι) (h : τ ι → τ ι) :
  π (l ∈ list A) → π (rev (map h l) = map h (rev l)) ≔
begin admit end;

// Simplifier needs the premises as assumptions because rewriting will not
// instantiate the variable ?A in the rules' typing conditions; note that
// rev_type does not instantiate ?A.  Only the premises do.
opaque symbol rev_app_distrib (xs ys A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (rev (app xs ys) = app (rev ys) (rev xs)) ≔
begin admit end;

opaque symbol rev_rev_ident (l A : τ ι) : π (l ∈ list A) → π (rev (rev l) = l) ≔
begin admit end;

opaque symbol rev_flat (ls A : τ ι) :
  π (ls ∈ list (list A)) → π (rev (flat ls) = flat (map rev (rev ls))) ≔
begin admit end;

// ===========================================================================
// theorems about list_add
// ===========================================================================

opaque symbol list_add_app (xs ys : τ ι) :
  π (xs ∈ list omega) → π (ys ∈ list omega) →
  π (list_add (app xs ys) = add (list_add ys) (list_add xs)) ≔
begin admit end;

opaque symbol list_add_rev (l : τ ι) :
  π (l ∈ list omega) → π (list_add (rev l) = list_add l) ≔
begin admit end;

opaque symbol list_add_flat (ls : τ ι) :
  π (ls ∈ list (list omega)) → π (list_add (flat ls) = list_add (map list_add ls)) ≔
begin admit end;

// ===========================================================================
// New induction rules
// ===========================================================================

opaque symbol list_append_induct (l A : τ ι) (P : τ ι → Prop) :
  π (l ∈ list A) → π (P Nil) →
  (Π (x y : τ ι), π (x ∈ A) → π (y ∈ list A) → π (P y) → π (P (app y (Cons x Nil)))) →
  π (P l) ≔
begin admit end;

opaque symbol list_complete_induct_lemma (A : τ ι) (P : τ ι → Prop)
  (ih : Π (l : τ ι), π (l ∈ list A) →
        π (Ball (list A) (λ l', lt (length l') (length l) ⇒ P l')) → π (P l))
  (n l : τ ι) :
  π (n ∈ omega) → π (l ∈ list A) → π (lt (length l) n) → π (P l) ≔
begin admit end;

opaque symbol list_complete_induct (l A : τ ι) (P : τ ι → Prop) :
  π (l ∈ list A) →
  (Π (l2 : τ ι), π (l2 ∈ list A) →
    π (Ball (list A) (λ l', lt (length l') (length l2) ⇒ P l')) → π (P l2)) →
  π (P l) ≔
begin admit end;

// ===========================================================================
// (** min FIXME: replace by Int! **)
// Min theorems are also true for i, j ordinals
// ===========================================================================

opaque symbol min_sym (i j : τ ι) : π (i ∈ omega) → π (j ∈ omega) → π (min i j = min j i) ≔
begin admit end;

opaque symbol min_type (i j : τ ι) : π (i ∈ omega) → π (j ∈ omega) → π (min i j ∈ omega) ≔
begin admit end;

opaque symbol min_0 (i : τ ι) : π (i ∈ omega) → π (min empty i = empty) ≔
begin admit end;

opaque symbol min_02 (i : τ ι) : π (i ∈ omega) → π (min i empty = empty) ≔
begin admit end;

opaque symbol lt_min_iff (i j k : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (k ∈ omega) →
  π (lt i (min j k) ⇔ (lt i j ∧ lt i k)) ≔
begin admit end;

opaque symbol min_succ_succ (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (min (succ i) (succ j) = succ (min i j)) ≔
begin admit end;

// ===========================================================================
// more theorems about lists
// ===========================================================================

// (** filter **)

opaque symbol filter_append (xs A ys : τ ι) (P : τ ι → Prop) :
  π (xs ∈ list A) → π (filter P (app xs ys) = app (filter P xs) (filter P ys)) ≔
begin admit end;

opaque symbol filter_type (xs A : τ ι) (P : τ ι → Prop) :
  π (xs ∈ list A) → π (filter P xs ∈ list A) ≔
begin admit end;

opaque symbol length_filter (xs A : τ ι) (P : τ ι → Prop) :
  π (xs ∈ list A) → π (le (length (filter P xs)) (length xs)) ≔
begin admit end;

opaque symbol filter_is_subset (xs A : τ ι) (P : τ ι → Prop) :
  π (xs ∈ list A) → π (set_of_list (filter P xs) ⊆ set_of_list xs) ≔
begin admit end;

opaque symbol filter_False (xs A : τ ι) : π (xs ∈ list A) → π (filter (λ p, ⊥) xs = Nil) ≔
begin admit end;

opaque symbol filter_True (xs A : τ ι) : π (xs ∈ list A) → π (filter (λ p, ⊤) xs = xs) ≔
begin admit end;

// (** length **)

opaque symbol length_is_0_iff (xs A : τ ι) :
  π (xs ∈ list A) → π (length xs = empty ⇔ xs = Nil) ≔
begin admit end;

opaque symbol length_is_0_iff2 (xs A : τ ι) :
  π (xs ∈ list A) → π (empty = length xs ⇔ xs = Nil) ≔
begin admit end;

opaque symbol length_tl (xs A : τ ι) :
  π (xs ∈ list A) → π (length (tl xs) = diff (length xs) (succ empty)) ≔
begin admit end;

opaque symbol length_greater_0_iff (xs A : τ ι) :
  π (xs ∈ list A) → π (lt empty (length xs) ⇔ xs ≠ Nil) ≔
begin admit end;

opaque symbol length_succ_iff (xs A n : τ ι) :
  π (xs ∈ list A) →
  π (length xs = succ n ⇔ (`∃ (y : τ ι), `∃ (ys : τ ι), xs = Cons y ys ∧ length ys = n)) ≔
begin admit end;

// (** more theorems about append **)

opaque symbol append_is_Nil_iff (xs A ys : τ ι) :
  π (xs ∈ list A) → π (app xs ys = Nil ⇔ (xs = Nil ∧ ys = Nil)) ≔
begin admit end;

opaque symbol append_is_Nil_iff2 (xs A ys : τ ι) :
  π (xs ∈ list A) → π (Nil = app xs ys ⇔ (xs = Nil ∧ ys = Nil)) ≔
begin admit end;

opaque symbol append_left_is_self_iff (xs A ys : τ ι) :
  π (xs ∈ list A) → π (app xs ys = xs ⇔ ys = Nil) ≔
begin admit end;

opaque symbol append_left_is_self_iff2 (xs A ys : τ ι) :
  π (xs ∈ list A) → π (xs = app xs ys ⇔ ys = Nil) ≔
begin admit end;

// TOO SLOW as a default simprule!
opaque symbol append_left_is_Nil_iff (xs ys zs A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (zs ∈ list A) →
  π (length ys = length zs) →
  π (app xs ys = zs ⇔ (xs = Nil ∧ ys = zs)) ≔
begin admit end;

// TOO SLOW as a default simprule!
opaque symbol append_left_is_Nil_iff2 (xs ys zs A : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (zs ∈ list A) →
  π (length ys = length zs) →
  π (zs = app ys xs ⇔ (xs = Nil ∧ ys = zs)) ≔
begin admit end;

opaque symbol append_eq_append_iff (xs A ys us vs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (length xs = length ys) →
  π (app xs us = app ys vs ⇔ (xs = ys ∧ us = vs)) ≔
begin admit end;

opaque symbol append_eq_append (xs A ys us vs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (us ∈ list A) → π (vs ∈ list A) →
  π (length us = length vs) → π (app xs us = app ys vs) →
  π (xs = ys ∧ us = vs) ≔
begin admit end;

opaque symbol append_eq_append_iff2 (xs A ys us vs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (us ∈ list A) → π (vs ∈ list A) →
  π (length us = length vs) →
  π (app xs us = app ys vs ⇔ (xs = ys ∧ us = vs)) ≔
begin admit end;

opaque symbol append_self_iff (xs A ys zs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (zs ∈ list A) →
  π (app xs ys = app xs zs ⇔ ys = zs) ≔
begin admit end;

opaque symbol append_self_iff2 (xs A ys zs : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (zs ∈ list A) →
  π (app ys xs = app zs xs ⇔ ys = zs) ≔
begin admit end;

// Can also be proved from append_eq_append_iff2, but the proof requires two
// more hypotheses: x \<in> A and y \<in> A
opaque symbol append1_eq_iff (xs A ys x y : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) →
  π (app xs (Cons x Nil) = app ys (Cons y Nil) ⇔ (xs = ys ∧ x = y)) ≔
begin admit end;

opaque symbol append_right_is_self_iff (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (app xs ys = ys ⇔ xs = Nil) ≔
begin admit end;

opaque symbol append_right_is_self_iff2 (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (ys = app xs ys ⇔ xs = Nil) ≔
begin admit end;

opaque symbol hd_append (xs A ys : τ ι) :
  π (xs ∈ list A) → π (xs ≠ Nil) → π (hd (app xs ys) = hd xs) ≔
begin admit end;

opaque symbol tl_append (xs A ys : τ ι) :
  π (xs ∈ list A) → π (xs ≠ Nil) → π (tl (app xs ys) = app (tl xs) ys) ≔
begin admit end;

// (** rev **)

opaque symbol rev_is_Nil_iff (xs A : τ ι) : π (xs ∈ list A) → π (rev xs = Nil ⇔ xs = Nil) ≔
begin admit end;

opaque symbol Nil_is_rev_iff (xs A : τ ι) : π (xs ∈ list A) → π (Nil = rev xs ⇔ xs = Nil) ≔
begin admit end;

opaque symbol rev_is_rev_iff (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (rev xs = rev ys ⇔ xs = ys) ≔
begin admit end;

opaque symbol rev_list_elim (xs A : τ ι) (P : Prop) :
  π (xs ∈ list A) →
  π (xs = Nil ⇒ P) →
  π (Ball (list A) (λ ys, Ball A (λ y, (xs = app ys (Cons y Nil)) ⇒ P))) →
  π P ≔
begin admit end;

// (** more theorems about drop **)

opaque symbol length_drop (n A xs : τ ι) :
  π (n ∈ omega) → π (xs ∈ list A) → π (length (drop n xs) = diff (length xs) n) ≔
begin admit end;

opaque symbol drop_all (n A xs : τ ι) :
  π (n ∈ omega) → π (xs ∈ list A) → π (le (length xs) n) → π (drop n xs = Nil) ≔
begin admit end;

opaque symbol drop_append (n A xs ys : τ ι) :
  π (n ∈ omega) → π (xs ∈ list A) →
  π (drop n (app xs ys) = app (drop n xs) (drop (diff n (length xs)) ys)) ≔
begin admit end;

opaque symbol drop_drop (m A : τ ι) :
  π (m ∈ omega) →
  π (Ball (list A) (λ xs, Ball omega (λ n, drop n (drop m xs) = drop (add n m) xs))) ≔
begin admit end;

// ===========================================================================
// (** take **)
// ===========================================================================

opaque symbol take_0 (xs A : τ ι) : π (xs ∈ list A) → π (take empty xs = Nil) ≔
begin admit end;

opaque symbol take_succ_Cons (n a xs : τ ι) :
  π (n ∈ omega) → π (take (succ n) (Cons a xs) = Cons a (take n xs)) ≔
begin admit end;

// Needed for proving take_all
opaque symbol take_Nil (n : τ ι) : π (n ∈ omega) → π (take n Nil = Nil) ≔
begin admit end;

opaque symbol take_all (n A xs : τ ι) :
  π (n ∈ omega) → π (xs ∈ list A) → π (le (length xs) n) → π (take n xs = xs) ≔
begin admit end;

opaque symbol take_type (xs A n : τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) → π (take n xs ∈ list A) ≔
begin admit end;

opaque symbol take_append (xs A ys n : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (n ∈ omega) →
  π (take n (app xs ys) = app (take n xs) (take (diff n (length xs)) ys)) ≔
begin admit end;

opaque symbol take_take (m A xs n : τ ι) :
  π (m ∈ omega) → π (xs ∈ list A) → π (n ∈ omega) →
  π (take n (take m xs) = take (min n m) xs) ≔
begin admit end;

// ===========================================================================
// (** nth **)
// ===========================================================================

opaque symbol nth_0 (a l : τ ι) : π (nth empty (Cons a l) = a) ≔
begin admit end;

opaque symbol nth_Cons (n a l : τ ι) :
  π (n ∈ omega) → π (nth (succ n) (Cons a l) = nth n l) ≔
begin admit end;

opaque symbol nth_empty (n : τ ι) : π (nth n Nil = empty) ≔
begin admit end;

opaque symbol nth_type (xs A n : τ ι) :
  π (xs ∈ list A) → π (lt n (length xs)) → π (nth n xs ∈ A) ≔
begin admit end;

opaque symbol nth_eq_0 (xs A n : τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) → π (le (length xs) n) → π (nth n xs = empty) ≔
begin admit end;

opaque symbol nth_append (xs A ys n : τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) →
  π (nth n (app xs ys) = If (lt n (length xs)) (nth n xs) (nth (diff n (length xs)) ys)) ≔
begin admit end;

opaque symbol set_of_list_conv_nth (xs A : τ ι) :
  π (xs ∈ list A) →
  π (set_of_list xs = Collect A (λ x, Bex omega (λ i, lt i (length xs) ∧ x = nth i xs))) ≔
begin admit end;

// ===========================================================================
// Other theorems about lists
// ===========================================================================

opaque symbol nth_take_lemma (k A xs ys : τ ι) :
  π (k ∈ omega) → π (xs ∈ list A) → π (ys ∈ list A) →
  π (le k (length xs)) → π (le k (length ys)) →
  π (Ball omega (λ i, lt i k ⇒ nth i xs = nth i ys)) →
  π (take k xs = take k ys) ≔
begin admit end;

opaque symbol nth_equalityI (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) → π (length xs = length ys) →
  π (Ball omega (λ i, lt i (length xs) ⇒ nth i xs = nth i ys)) →
  π (xs = ys) ≔
begin admit end;

// The famous take-lemma
opaque symbol take_equalityI (xs A ys : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list A) →
  π (Ball omega (λ i, take i xs = take i ys)) →
  π (xs = ys) ≔
begin admit end;

opaque symbol nth_drop (n i A xs : τ ι) :
  π (n ∈ omega) → π (i ∈ omega) → π (xs ∈ list A) →
  π (nth i (drop n xs) = nth (add n i) xs) ≔
begin admit end;

opaque symbol take_succ (xs A i : τ ι) :
  π (xs ∈ list A) → π (lt i (length xs)) →
  π (take (succ i) xs = app (take i xs) (Cons (nth i xs) Nil)) ≔
begin admit end;

opaque symbol take_add (xs A j i : τ ι) :
  π (xs ∈ list A) → π (j ∈ omega) → π (i ∈ omega) →
  π (take (add i j) xs = app (take i xs) (take j (drop i xs))) ≔
begin admit end;

opaque symbol length_take (l A : τ ι) :
  π (l ∈ list A) → π (Ball omega (λ n, length (take n l) = min n (length l))) ≔
begin admit end;

// ===========================================================================
// The function zip
// ===========================================================================

opaque symbol list_on_set_of_list (xs A : τ ι) :
  π (xs ∈ list A) → π (xs ∈ list (set_of_list xs)) ≔
begin admit end;

opaque symbol zip_Nil (ys A : τ ι) : π (ys ∈ list A) → π (zip Nil ys = Nil) ≔
begin admit end;

opaque symbol zip_Nil2 (xs A : τ ι) : π (xs ∈ list A) → π (zip xs Nil = Nil) ≔
begin admit end;

opaque symbol zip_aux_unique (B C xs A ys : τ ι) :
  π (B ⊆ C) → π (xs ∈ list A) → π (ys ∈ list B) →
  π (fapply (zip_aux C xs) ys = fapply (zip_aux B xs) ys) ≔
begin admit end;

opaque symbol zip_Cons_Cons (xs A ys B x y : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list B) → π (x ∈ A) → π (y ∈ B) →
  π (zip (Cons x xs) (Cons y ys) = Cons (Pair x y) (zip xs ys)) ≔
begin admit end;

opaque symbol zip_type (xs A ys B : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list B) → π (zip xs ys ∈ list (Sigma A (λ _, B))) ≔
begin admit end;

// zip length
opaque symbol length_zip (xs A ys B : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list B) →
  π (length (zip xs ys) = min (length xs) (length ys)) ≔
begin admit end;

opaque symbol zip_append1 (ys A zs B xs : τ ι) :
  π (ys ∈ list A) → π (zs ∈ list B) → π (xs ∈ list A) →
  π (zip (app xs ys) zs
     = app (zip xs (take (length xs) zs)) (zip ys (drop (length xs) zs))) ≔
begin admit end;

opaque symbol zip_append2 (xs A zs B ys : τ ι) :
  π (xs ∈ list A) → π (zs ∈ list B) → π (ys ∈ list B) →
  π (zip xs (app ys zs)
     = app (zip (take (length ys) xs) ys) (zip (drop (length ys) xs) zs)) ≔
begin admit end;

opaque symbol zip_append (xs us ys vs A B : τ ι) :
  π (length xs = length us) → π (length ys = length vs) →
  π (xs ∈ list A) → π (us ∈ list B) → π (ys ∈ list A) → π (vs ∈ list B) →
  π (zip (app xs ys) (app us vs) = app (zip xs us) (zip ys vs)) ≔
begin admit end;

opaque symbol zip_rev (ys B xs A : τ ι) :
  π (ys ∈ list B) → π (xs ∈ list A) → π (length xs = length ys) →
  π (zip (rev xs) (rev ys) = rev (zip xs ys)) ≔
begin admit end;

opaque symbol nth_zip (ys B i A xs : τ ι) :
  π (ys ∈ list B) → π (i ∈ omega) → π (xs ∈ list A) →
  π (lt i (length xs)) → π (lt i (length ys)) →
  π (nth i (zip xs ys) = Pair (nth i xs) (nth i ys)) ≔
begin admit end;

// NOTE: the .thy's hypothesis list literally includes `i \<in> nat` even
// though the `i` bound inside the ∃ in the conclusion shadows it (so the
// hypothesis is, as stated, unused) — ported literally per CLAUDE.md's
// faithfulness requirement, not "fixed".
opaque symbol set_of_list_zip (xs A ys B i : τ ι) :
  π (xs ∈ list A) → π (ys ∈ list B) → π (i ∈ omega) →
  π (set_of_list (zip xs ys)
     = Collect (Sigma A (λ _, B))
         (λ p, Bex omega (λ i2, lt i2 (min (length xs) (length ys))
                ∧ fst p = nth i2 xs ∧ snd p = nth i2 ys))) ≔
begin admit end;

// ===========================================================================
// (** list_update **)
// ===========================================================================

opaque symbol list_update_Nil (i v : τ ι) :
  π (i ∈ omega) → π (list_update Nil i v = Nil) ≔
begin admit end;

opaque symbol list_update_Cons_0 (x xs v : τ ι) :
  π (list_update (Cons x xs) empty v = Cons v xs) ≔
begin admit end;

opaque symbol list_update_Cons_succ (n x xs v : τ ι) :
  π (n ∈ omega) →
  π (list_update (Cons x xs) (succ n) v = Cons x (list_update xs n v)) ≔
begin admit end;

opaque symbol list_update_type (xs A v n : τ ι) :
  π (xs ∈ list A) → π (v ∈ A) → π (n ∈ omega) →
  π (list_update xs n v ∈ list A) ≔
begin admit end;

opaque symbol length_list_update (xs A i v : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (length (list_update xs i v) = length xs) ≔
begin admit end;

opaque symbol nth_list_update (xs A i j x : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (j ∈ omega) → π (lt i (length xs)) →
  π (nth j (list_update xs i x) = If (i = j) x (nth j xs)) ≔
begin admit end;

opaque symbol nth_list_update_eq (i xs A x : τ ι) :
  π (lt i (length xs)) → π (xs ∈ list A) → π (nth i (list_update xs i x) = x) ≔
begin admit end;

opaque symbol nth_list_update_neq (xs A i j x : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (j ∈ omega) → π (i ≠ j) →
  π (nth j (list_update xs i x) = nth j xs) ≔
begin admit end;

opaque symbol list_update_overwrite (xs A i x y : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (lt i (length xs)) →
  π (list_update (list_update xs i x) i y = list_update xs i y) ≔
begin admit end;

opaque symbol list_update_same_conv (xs A i x : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) → π (lt i (length xs)) →
  π (list_update xs i x = xs ⇔ nth i xs = x) ≔
begin admit end;

opaque symbol update_zip (ys B i A xy xs : τ ι) :
  π (ys ∈ list B) → π (i ∈ omega) → π (xy ∈ Sigma A (λ _, B)) →
  π (xs ∈ list A) → π (length xs = length ys) →
  π (list_update (zip xs ys) i xy
     = zip (list_update xs i (fst xy)) (list_update ys i (snd xy))) ≔
begin admit end;

opaque symbol set_update_subset_cons (xs A i x : τ ι) :
  π (xs ∈ list A) → π (i ∈ omega) →
  π (set_of_list (list_update xs i x) ⊆ cons x (set_of_list xs)) ≔
begin admit end;

opaque symbol set_of_list_update_subsetI (xs A x i : τ ι) :
  π (set_of_list xs ⊆ A) → π (xs ∈ list A) → π (x ∈ A) → π (i ∈ omega) →
  π (set_of_list (list_update xs i x) ⊆ A) ≔
begin admit end;

// ===========================================================================
// (** upt **)
// ===========================================================================

opaque symbol upt_rec (i j : τ ι) :
  π (j ∈ omega) → π (upt i j = If (lt i j) (Cons i (upt (succ i) j)) Nil) ≔
begin admit end;

opaque symbol upt_conv_Nil (i j : τ ι) :
  π (le j i) → π (j ∈ omega) → π (upt i j = Nil) ≔
begin admit end;

// Only needed if upt_Suc is deleted from the simpset
opaque symbol upt_succ_append (i j : τ ι) :
  π (le i j) → π (j ∈ omega) → π (upt i (succ j) = app (upt i j) (Cons j Nil)) ≔
begin admit end;

opaque symbol upt_conv_Cons (i j : τ ι) :
  π (lt i j) → π (j ∈ omega) → π (upt i j = Cons i (upt (succ i) j)) ≔
begin admit end;

opaque symbol upt_type (i j : τ ι) : π (j ∈ omega) → π (upt i j ∈ list omega) ≔
begin admit end;

// LOOPS as a simprule, since j<=j
opaque symbol upt_add_eq_append (i j k : τ ι) :
  π (le i j) → π (j ∈ omega) → π (k ∈ omega) →
  π (upt i (add j k) = app (upt i j) (upt j (add j k))) ≔
begin admit end;

opaque symbol length_upt (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (length (upt i j) = diff j i) ≔
begin admit end;

opaque symbol nth_upt (i j k : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (k ∈ omega) → π (lt (add i k) j) →
  π (nth k (upt i j) = add i k) ≔
begin admit end;

opaque symbol take_upt (m n i : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (i ∈ omega) → π (le (add i m) n) →
  π (take m (upt i n) = upt i (add i m)) ≔
begin admit end;

opaque symbol map_succ_upt (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (map succ (upt m n) = upt (succ m) (succ n)) ≔
begin admit end;

opaque symbol nth_map (xs A n : τ ι) (f : τ ι → τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) → π (lt n (length xs)) →
  π (nth n (map f xs) = f (nth n xs)) ≔
begin admit end;

opaque symbol nth_map_upt (m n i : τ ι) (f : τ ι → τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (i ∈ omega) → π (lt i (diff n m)) →
  π (nth i (map f (upt m n)) = f (add m i)) ≔
begin admit end;

// ===========================================================================
// (** sublist (a generalization of nth to sets) **)
// ===========================================================================

opaque symbol sublist_0 (xs A : τ ι) : π (xs ∈ list A) → π (sublist xs empty = Nil) ≔
begin admit end;

opaque symbol sublist_Nil (A : τ ι) : π (sublist Nil A = Nil) ≔
begin admit end;

opaque symbol sublist_shift_lemma (xs B i A : τ ι) :
  π (xs ∈ list B) → π (i ∈ omega) →
  π (map fst (filter (λ p, snd p ∈ A) (zip xs (upt i (add i (length xs)))))
     = map fst (filter (λ p, snd p ∈ omega ∧ add (snd p) i ∈ A)
                        (zip xs (upt empty (length xs))))) ≔
begin admit end;

opaque symbol sublist_type (xs B A : τ ι) : π (xs ∈ list B) → π (sublist xs A ∈ list B) ≔
begin admit end;

opaque symbol upt_add_eq_append2 (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) →
  π (upt empty (add i j) = app (upt empty i) (upt i (add i j))) ≔
begin admit end;

opaque symbol sublist_append (xs B ys A : τ ι) :
  π (xs ∈ list B) → π (ys ∈ list B) →
  π (sublist (app xs ys) A
     = app (sublist xs A) (sublist ys (Collect omega (λ j, add j (length xs) ∈ A)))) ≔
begin admit end;

opaque symbol sublist_Cons (xs B x A : τ ι) :
  π (xs ∈ list B) → π (x ∈ B) →
  π (sublist (Cons x xs) A
     = app (If (empty ∈ A) (Cons x Nil) Nil) (sublist xs (Collect omega (λ j, succ j ∈ A)))) ≔
begin admit end;

opaque symbol sublist_singleton (x A : τ ι) :
  π (sublist (Cons x Nil) A = If (empty ∈ A) (Cons x Nil) Nil) ≔
begin admit end;

opaque symbol sublist_upt_eq_take (xs A n : τ ι) :
  π (xs ∈ list A) → π (n ∈ omega) → π (sublist xs n = take n xs) ≔
begin admit end;

opaque symbol sublist_Int_eq (xs B A : τ ι) :
  π (xs ∈ list B) → π (sublist xs (Int A omega) = sublist xs A) ≔
begin admit end;

// ===========================================================================
// Repetition of a List Element
// ===========================================================================

opaque symbol length_repeat (a n : τ ι) : π (n ∈ omega) → π (length (list_repeat a n) = n) ≔
begin admit end;

opaque symbol repeat_succ_app (a n : τ ι) :
  π (n ∈ omega) → π (list_repeat a (succ n) = app (list_repeat a n) (Cons a Nil)) ≔
begin admit end;

opaque symbol repeat_type (a A n : τ ι) :
  π (a ∈ A) → π (n ∈ omega) → π (list_repeat a n ∈ list A) ≔
begin admit end;
