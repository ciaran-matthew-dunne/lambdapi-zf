// Arith.lp — Natural-number arithmetic (Isabelle/ZF Arith.thy, Paulson).
//
// add/diff/mult/div/mod on nat (= omega in this port), plus the natify
// coercion.  raw_* are the primrec/transrec kernels; the public operators
// coerce both arguments through natify first.
//
// Isabelle source: Arith.thy (imports Univ).
//
// ARCHITECTURE: the operators are ABSTRACT symbols with a `*_def` defining
// axiom (= the Isabelle definition), NOT `≔` definitions.  This keeps the
// kernel from eagerly unfolding e.g. `natify (m #+ n)` through
// Vrecursor→transrec→wfrec→eclose during conversion (which blows up); proofs
// unfold on demand with `rewrite *_def`.  Faithful: `op_def` IS the Isabelle def.

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func
            ZF.Ordinal ZF.Nat_ZF ZF.Epsilon ZF.Univ;

// ===========================================================================
// Operators (abstract) + their defining equations (Isabelle definitions)
// ===========================================================================

// pred(y) = nat_case(0, λx. x, y)   — inverse of succ
symbol pred : τ ι → τ ι;
symbol pred_def (y : τ ι) : π (pred y = nat_case empty (λ x, x) y);

// natify ≡ Vrecursor(λf a. if a = succ(pred a) then succ(f`pred a) else 0)
symbol natify : τ ι → τ ι;
symbol natify_def (x : τ ι) :
  π (natify x
     = Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) x);

// raw_add / raw_diff / raw_mult: primrec kernels (Isabelle primrec → rec).
symbol raw_add : τ ι → τ ι → τ ι;
symbol raw_add_def (m n : τ ι) : π (raw_add m n = rec m n (λ x r, succ r));

symbol raw_diff : τ ι → τ ι → τ ι;
symbol raw_diff_def (m n : τ ι) :
  π (raw_diff m n = rec n m (λ y r, nat_case empty (λ x, x) r));

symbol raw_mult : τ ι → τ ι → τ ι;
symbol raw_mult_def (m n : τ ι) : π (raw_mult m n = rec m empty (λ x r, raw_add n r));

// Public operators: coerce both arguments through natify.
symbol add : τ ι → τ ι → τ ι;
symbol add_def (m n : τ ι) : π (add m n = raw_add (natify m) (natify n));

symbol diff : τ ι → τ ι → τ ι;
symbol diff_def (m n : τ ι) : π (diff m n = raw_diff (natify m) (natify n));

symbol mult : τ ι → τ ι → τ ι;
symbol mult_def (m n : τ ι) : π (mult m n = raw_mult (natify m) (natify n));

// raw_div / raw_mod via transfinite recursion.
symbol raw_div : τ ι → τ ι → τ ι;
symbol raw_div_def (m n : τ ι) :
  π (raw_div m n
     = transrec m (λ j f, If (lt j n ∨ (n = empty)) empty (succ (fapply f (diff j n)))));

symbol raw_mod : τ ι → τ ι → τ ι;
symbol raw_mod_def (m n : τ ι) :
  π (raw_mod m n = transrec m (λ j f, If (lt j n ∨ (n = empty)) j (fapply f (diff j n))));

symbol div : τ ι → τ ι → τ ι;
symbol div_def (m n : τ ι) : π (div m n = raw_div (natify m) (natify n));

symbol mod : τ ι → τ ι → τ ι;
symbol mod_def (m n : τ ι) : π (mod m n = raw_mod (natify m) (natify n));

// ===========================================================================
// Primrec defining equations (via rec_0 / rec_succ — unconditional in succ).
// ===========================================================================

opaque symbol raw_add_0 (n : τ ι) : π (raw_add empty n = n) ≔
begin assume n; rewrite raw_add_def; refine rec_0 n (λ x r, succ r) end;

opaque symbol raw_add_succ (m n : τ ι) :
  π (raw_add (succ m) n = succ (raw_add m n)) ≔
begin assume m n; rewrite raw_add_def; rewrite raw_add_def;
  refine rec_succ m n (λ x r, succ r) end;

opaque symbol raw_diff_0 (m : τ ι) : π (raw_diff m empty = m) ≔
begin assume m; rewrite raw_diff_def; refine rec_0 m (λ y r, nat_case empty (λ x, x) r) end;

opaque symbol raw_diff_succ (m n : τ ι) :
  π (raw_diff m (succ n) = nat_case empty (λ x, x) (raw_diff m n)) ≔
begin assume m n; rewrite raw_diff_def; rewrite raw_diff_def;
  refine rec_succ n m (λ y r, nat_case empty (λ x, x) r) end;

opaque symbol raw_mult_0 (n : τ ι) : π (raw_mult empty n = empty) ≔
begin assume n; rewrite raw_mult_def; refine rec_0 empty (λ x r, raw_add n r) end;

opaque symbol raw_mult_succ (m n : τ ι) :
  π (raw_mult (succ m) n = raw_add n (raw_mult m n)) ≔
begin assume m n; rewrite raw_mult_def; rewrite raw_mult_def;
  refine rec_succ m empty (λ x r, raw_add n r) end;

// ===========================================================================
// pred
// ===========================================================================

opaque symbol pred_0 : π (pred empty = empty) ≔
begin rewrite pred_def; refine nat_case_0 empty (λ x, x) end;

opaque symbol pred_succ_eq (y : τ ι) : π (pred (succ y) = y) ≔
begin assume y; rewrite pred_def; refine nat_case_succ empty (λ x, x) y end;

opaque symbol pred_type (m : τ ι) : π (m ∈ omega) → π (pred m ∈ omega) ≔
begin
  assume m hm;
  refine natE m (pred m ∈ omega) hm _ _
  { assume heq; rewrite heq; rewrite pred_0; refine zero_in_omega }
  { assume x hx heq; rewrite heq; rewrite (pred_succ_eq x); refine hx }
end;

// ===========================================================================
// Typing rules — raw_* by induction on the recursion argument.
// ===========================================================================

opaque symbol raw_add_type (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (raw_add m n ∈ omega) ≔
begin
  assume m n hm hn;
  have hall : π (Ball omega (λ k, raw_add k n ∈ omega)) {
    refine nat_induct (λ k, raw_add k n ∈ omega) _ _
    { simplify rule off; rewrite (raw_add_0 n); refine hn }
    { assume k hk hIH; rewrite (raw_add_succ k n);
      refine succ_in_omega (raw_add k n) hIH }
  };
  refine bspec omega (λ k, raw_add k n ∈ omega) m hall hm
end;

opaque symbol raw_mult_type (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (raw_mult m n ∈ omega) ≔
begin
  assume m n hm hn;
  have hall : π (Ball omega (λ k, raw_mult k n ∈ omega)) {
    refine nat_induct (λ k, raw_mult k n ∈ omega) _ _
    { simplify rule off; rewrite (raw_mult_0 n); refine zero_in_omega }
    { assume k hk hIH; rewrite (raw_mult_succ k n);
      refine raw_add_type n (raw_mult k n) hn hIH }
  };
  refine bspec omega (λ k, raw_mult k n ∈ omega) m hall hm
end;

opaque symbol raw_diff_type (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (raw_diff m n ∈ omega) ≔
begin
  assume m n hm hn;
  have hall : π (Ball omega (λ k, raw_diff m k ∈ omega)) {
    refine nat_induct (λ k, raw_diff m k ∈ omega) _ _
    { simplify rule off; rewrite (raw_diff_0 m); refine hm }
    { assume k hk hIH; rewrite (raw_diff_succ m k);
      rewrite left (pred_def (raw_diff m k));
      refine pred_type (raw_diff m k) hIH }
  };
  refine bspec omega (λ k, raw_diff m k ∈ omega) n hall hn
end;

// ===========================================================================
// natify — the coercion to nat.
// ===========================================================================

opaque symbol natify_0 : π (natify empty = empty) ≔
begin
  rewrite natify_def;
  rewrite Vrecursor_eq;
  simplify rule off;
  rewrite pred_0;
  refine If_not_P (empty = succ empty) _ _ _;
  assume heq;
  refine cons_not_empty empty empty (eq_sym heq)
end;

opaque symbol natify_succ (y : τ ι) : π (natify (succ y) = succ (natify y)) ≔
begin
  assume y;
  have hy_in : π (y ∈ Vset (rank (succ y))) {
    have hrs : π (rank (succ y) = succ (rank y)) { refine rank_succ y };
    refine VsetI y (rank (succ y)) _;
    rewrite hrs;
    refine ltI (rank y) (succ (rank y)) (succI1 (rank y)) (Ord_succ (rank y) (Ord_rank y))
  };
  // key: unfold only the LHS natify (RHS stays `succ (natify y)`)
  have key : π (Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) (succ y)
              = succ (natify y)) {
    rewrite Vrecursor_eq;
    simplify rule off;
    rewrite pred_succ_eq;
    rewrite (If_P (succ y = succ y) _ _ (eq_refl (succ y)));
    have hb : π (fapply (Lambda (Vset (rank (succ y)))
          (λ x, Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) x)) y
        = natify y)
      { rewrite (natify_def y);
        refine beta (Vset (rank (succ y)))
          (λ x, Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) x)
          y hy_in };
    rewrite hb;
    reflexivity
  };
  rewrite (natify_def (succ y));
  refine key
end;

opaque symbol natify_non_succ (x : τ ι) :
  π (`∀ z, x ≠ succ z) → π (natify x = empty) ≔
begin
  assume x hns;
  rewrite natify_def;
  rewrite Vrecursor_eq;
  simplify rule off;
  refine If_not_P (x = succ (pred x)) _ _ (hns (pred x))
end;

opaque symbol natify_ident (n : τ ι) : π (n ∈ omega) → π (natify n = n) ≔
begin
  assume n hn;
  have hall : π (Ball omega (λ k, natify k = k)) {
    refine nat_induct (λ k, natify k = k) _ _
    { simplify rule off; refine natify_0 }
    { assume k hk hIH; rewrite (natify_succ k); rewrite hIH; reflexivity }
  };
  refine bspec omega (λ k, natify k = k) n hall hn
end;

opaque symbol natify_eqE (x y : τ ι) :
  π (natify x = y) → π (x ∈ omega) → π (x = y) ≔
begin
  assume x y hxy hx;
  refine eq_trans (eq_sym (natify_ident x hx)) hxy
end;

opaque symbol natify_in_nat (x : τ ι) : π (natify x ∈ omega) ≔
begin
  assume x;
  refine eps_induct (λ w, natify w ∈ omega) x _;
  assume w IH;
  refine ∨ₑ (em (`∃ z, w = succ z)) _ _
  { assume hex;
    refine ∃ₑ hex _;
    assume z hz;
    have hz_in_w : π (z ∈ w) { rewrite hz; refine succI1 z };
    have hnz : π (natify z ∈ omega) { refine IH z hz_in_w };
    rewrite hz;
    rewrite (natify_succ z);
    refine succ_in_omega (natify z) hnz }
  { assume hnex;
    have hall : π (`∀ z, w ≠ succ z) { assume z heq; refine hnex (∃ᵢ z heq) };
    rewrite (natify_non_succ w hall);
    refine zero_in_omega }
end;

opaque symbol natify_idem (x : τ ι) : π (natify (natify x) = natify x) ≔
begin assume x; refine natify_ident (natify x) (natify_in_nat x) end;

// ===========================================================================
// Collapsing rules: natify(_) inside an operator arg is redundant.
// ===========================================================================

opaque symbol add_natify1 (m n : τ ι) : π (add (natify m) n = add m n) ≔
begin assume m n; rewrite (add_def (natify m) n); rewrite (add_def m n);
  rewrite (natify_idem m); reflexivity end;

opaque symbol add_natify2 (m n : τ ι) : π (add m (natify n) = add m n) ≔
begin assume m n; rewrite (add_def m (natify n)); rewrite (add_def m n);
  rewrite (natify_idem n); reflexivity end;

opaque symbol mult_natify1 (m n : τ ι) : π (mult (natify m) n = mult m n) ≔
begin assume m n; rewrite (mult_def (natify m) n); rewrite (mult_def m n);
  rewrite (natify_idem m); reflexivity end;

opaque symbol mult_natify2 (m n : τ ι) : π (mult m (natify n) = mult m n) ≔
begin assume m n; rewrite (mult_def m (natify n)); rewrite (mult_def m n);
  rewrite (natify_idem n); reflexivity end;

opaque symbol diff_natify1 (m n : τ ι) : π (diff (natify m) n = diff m n) ≔
begin assume m n; rewrite (diff_def (natify m) n); rewrite (diff_def m n);
  rewrite (natify_idem m); reflexivity end;

opaque symbol diff_natify2 (m n : τ ι) : π (diff m (natify n) = diff m n) ≔
begin assume m n; rewrite (diff_def m (natify n)); rewrite (diff_def m n);
  rewrite (natify_idem n); reflexivity end;

opaque symbol mod_natify1 (m n : τ ι) : π (mod (natify m) n = mod m n) ≔
begin assume m n; rewrite (mod_def (natify m) n); rewrite (mod_def m n);
  rewrite (natify_idem m); reflexivity end;

opaque symbol mod_natify2 (m n : τ ι) : π (mod m (natify n) = mod m n) ≔
begin assume m n; rewrite (mod_def m (natify n)); rewrite (mod_def m n);
  rewrite (natify_idem n); reflexivity end;

opaque symbol div_natify1 (m n : τ ι) : π (div (natify m) n = div m n) ≔
begin assume m n; rewrite (div_def (natify m) n); rewrite (div_def m n);
  rewrite (natify_idem m); reflexivity end;

opaque symbol div_natify2 (m n : τ ι) : π (div m (natify n) = div m n) ≔
begin assume m n; rewrite (div_def m (natify n)); rewrite (div_def m n);
  rewrite (natify_idem n); reflexivity end;

// ===========================================================================
// Public typing rules (natify coerces, so no nat hypotheses needed).
// ===========================================================================

opaque symbol add_type (m n : τ ι) : π (add m n ∈ omega) ≔
begin assume m n; rewrite add_def;
  refine raw_add_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n) end;

opaque symbol mult_type (m n : τ ι) : π (mult m n ∈ omega) ≔
begin assume m n; rewrite mult_def;
  refine raw_mult_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n) end;

opaque symbol diff_type (m n : τ ι) : π (diff m n ∈ omega) ≔
begin assume m n; rewrite diff_def;
  refine raw_diff_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n) end;

// ===========================================================================
// Addition
// ===========================================================================

// 0 #+ m = natify(m)
opaque symbol add_0_natify (m : τ ι) : π (add empty m = natify m) ≔
begin assume m; rewrite add_def; rewrite natify_0; refine raw_add_0 (natify m) end;

// succ(m) #+ n = succ(m #+ n)
opaque symbol add_succ (m n : τ ι) : π (add (succ m) n = succ (add m n)) ≔
begin assume m n;
  rewrite (add_def (succ m) n); rewrite (add_def m n);
  rewrite (natify_succ m);
  refine raw_add_succ (natify m) (natify n) end;

// m ∈ nat ⟹ 0 #+ m = m
opaque symbol add_0 (m : τ ι) : π (m ∈ omega) → π (add empty m = m) ≔
begin assume m hm; refine eq_trans (add_0_natify m) (natify_ident m hm) end;

// m #+ 0 = natify(m)   (raw_add k 0 = k by induction on k)
opaque symbol add_0_right_natify (m : τ ι) : π (add m empty = natify m) ≔
begin
  assume m;
  have hkey : π (Ball omega (λ k, raw_add k empty = k)) {
    refine nat_induct (λ k, raw_add k empty = k) _ _
    { simplify rule off; refine raw_add_0 empty }
    { assume k hk hIH; rewrite (raw_add_succ k empty); rewrite hIH; reflexivity }
  };
  rewrite add_def; rewrite natify_0;
  refine bspec omega (λ k, raw_add k empty = k) (natify m) hkey (natify_in_nat m)
end;

// m ∈ nat ⟹ m #+ 0 = m
opaque symbol add_0_right (m : τ ι) : π (m ∈ omega) → π (add m empty = m) ≔
begin assume m hm; refine eq_trans (add_0_right_natify m) (natify_ident m hm) end;

// ===========================================================================
// Multiplication
// ===========================================================================

// 0 #* m = 0
opaque symbol mult_0 (m : τ ι) : π (mult empty m = empty) ≔
begin assume m; rewrite mult_def; rewrite natify_0; refine raw_mult_0 (natify m) end;

// succ(m) #* n = n #+ (m #* n)
opaque symbol mult_succ (m n : τ ι) : π (mult (succ m) n = add n (mult m n)) ≔
begin assume m n;
  have hmt : π (raw_mult (natify m) (natify n) ∈ omega)
    { refine raw_mult_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n) };
  rewrite (mult_def (succ m) n);
  rewrite (add_def n (mult m n));
  rewrite (mult_def m n);
  rewrite (natify_succ m);
  rewrite (raw_mult_succ (natify m) (natify n));
  rewrite (natify_ident (raw_mult (natify m) (natify n)) hmt);
  reflexivity
end;

// ===========================================================================
// Difference
// ===========================================================================

// m #- 0 = natify(m)
opaque symbol diff_0 (m : τ ι) : π (diff m empty = natify m) ≔
begin assume m; rewrite diff_def; rewrite natify_0; refine raw_diff_0 (natify m) end;

// m #+ succ(n) = succ(m #+ n)   (raw_add k (succ j) = succ (raw_add k j), induct k)
opaque symbol add_succ_right (m n : τ ι) : π (add m (succ n) = succ (add m n)) ≔
begin
  assume m n;
  have hkey : π (Ball omega (λ k, raw_add k (succ (natify n)) = succ (raw_add k (natify n)))) {
    refine nat_induct (λ k, raw_add k (succ (natify n)) = succ (raw_add k (natify n))) _ _
    { simplify rule off;
      rewrite (raw_add_0 (succ (natify n))); rewrite (raw_add_0 (natify n)); reflexivity }
    { assume k hk hIH;
      rewrite (raw_add_succ k (succ (natify n)));
      rewrite hIH;
      rewrite (raw_add_succ k (natify n)); reflexivity }
  };
  rewrite (add_def m (succ n)); rewrite (add_def m n);
  rewrite (natify_succ n);
  refine bspec omega (λ k, raw_add k (succ (natify n)) = succ (raw_add k (natify n)))
    (natify m) hkey (natify_in_nat m)
end;

// m #* 0 = 0   (raw_mult k 0 = 0, induct k)
opaque symbol mult_0_right (m : τ ι) : π (mult m empty = empty) ≔
begin
  assume m;
  have hkey : π (Ball omega (λ k, raw_mult k empty = empty)) {
    refine nat_induct (λ k, raw_mult k empty = empty) _ _
    { simplify rule off; refine raw_mult_0 empty }
    { assume k hk hIH; rewrite (raw_mult_succ k empty); rewrite hIH; refine raw_add_0 empty }
  };
  rewrite mult_def; rewrite natify_0;
  refine bspec omega (λ k, raw_mult k empty = empty) (natify m) hkey (natify_in_nat m)
end;

// 0 #- n = 0   (raw_diff 0 k = 0, induct k)
opaque symbol diff_0_eq_0 (n : τ ι) : π (diff empty n = empty) ≔
begin
  assume n;
  have hkey : π (Ball omega (λ k, raw_diff empty k = empty)) {
    refine nat_induct (λ k, raw_diff empty k = empty) _ _
    { simplify rule off; refine raw_diff_0 empty }
    { assume k hk hIH;
      rewrite (raw_diff_succ empty k); rewrite hIH; refine nat_case_0 empty (λ x, x) }
  };
  rewrite diff_def; rewrite natify_0;
  refine bspec omega (λ k, raw_diff empty k = empty) (natify n) hkey (natify_in_nat n)
end;

// succ(m) #- succ(n) = m #- n   (raw_diff (succ a)(succ k) = raw_diff a k, induct k)
opaque symbol diff_succ_succ (m n : τ ι) : π (diff (succ m) (succ n) = diff m n) ≔
begin
  assume m n;
  have hkey : π (Ball omega (λ k, raw_diff (succ (natify m)) (succ k) = raw_diff (natify m) k)) {
    refine nat_induct (λ k, raw_diff (succ (natify m)) (succ k) = raw_diff (natify m) k) _ _
    { simplify rule off;
      rewrite (raw_diff_succ (succ (natify m)) empty);
      rewrite (raw_diff_0 (succ (natify m)));
      rewrite (nat_case_succ empty (λ x, x) (natify m));
      rewrite (raw_diff_0 (natify m)); reflexivity }
    { assume k hk hIH;
      rewrite (raw_diff_succ (succ (natify m)) (succ k));
      rewrite hIH;
      rewrite (raw_diff_succ (natify m) k); reflexivity }
  };
  rewrite (diff_def (succ m) (succ n)); rewrite (diff_def m n);
  rewrite (natify_succ m); rewrite (natify_succ n);
  refine bspec omega (λ k, raw_diff (succ (natify m)) (succ k) = raw_diff (natify m) k)
    (natify n) hkey (natify_in_nat n)
end;

// ===========================================================================
// Associativity / commutativity of addition
// ===========================================================================

// (m #+ n) #+ k = m #+ (n #+ k)   (raw associativity by induction on 1st arg)
opaque symbol add_assoc (m n k : τ ι) : π (add (add m n) k = add m (add n k)) ≔
begin
  assume m n k;
  have hmn : π (raw_add (natify m) (natify n) ∈ omega)
    { refine raw_add_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n) };
  have hnk : π (raw_add (natify n) (natify k) ∈ omega)
    { refine raw_add_type (natify n) (natify k) (natify_in_nat n) (natify_in_nat k) };
  have hkey : π (Ball omega (λ a, raw_add (raw_add a (natify n)) (natify k)
                                  = raw_add a (raw_add (natify n) (natify k)))) {
    refine nat_induct (λ a, raw_add (raw_add a (natify n)) (natify k)
                            = raw_add a (raw_add (natify n) (natify k))) _ _
    { simplify rule off;
      rewrite (raw_add_0 (natify n));
      rewrite (raw_add_0 (raw_add (natify n) (natify k)));
      reflexivity }
    { assume a ha hIH;
      rewrite (raw_add_succ a (natify n));
      rewrite (raw_add_succ (raw_add a (natify n)) (natify k));
      rewrite hIH;
      rewrite (raw_add_succ a (raw_add (natify n) (natify k)));
      reflexivity }
  };
  rewrite (add_def (add m n) k); rewrite (add_def m n);
  rewrite (add_def m (add n k)); rewrite (add_def n k);
  rewrite (natify_ident (raw_add (natify m) (natify n)) hmn);
  rewrite (natify_ident (raw_add (natify n) (natify k)) hnk);
  refine bspec omega (λ a, raw_add (raw_add a (natify n)) (natify k)
                          = raw_add a (raw_add (natify n) (natify k)))
    (natify m) hkey (natify_in_nat m)
end;

// raw_add helpers (recursion is on the 1st arg; these lift to the 2nd, k ∈ nat)
opaque symbol raw_add_0_right (k : τ ι) : π (k ∈ omega) → π (raw_add k empty = k) ≔
begin
  assume k hk;
  have hall : π (Ball omega (λ a, raw_add a empty = a)) {
    refine nat_induct (λ a, raw_add a empty = a) _ _
    { simplify rule off; refine raw_add_0 empty }
    { assume a ha hIH; rewrite (raw_add_succ a empty); rewrite hIH; reflexivity }
  };
  refine bspec omega (λ a, raw_add a empty = a) k hall hk
end;

opaque symbol raw_add_succ_right (k j : τ ι) :
  π (k ∈ omega) → π (raw_add k (succ j) = succ (raw_add k j)) ≔
begin
  assume k j hk;
  have hall : π (Ball omega (λ a, raw_add a (succ j) = succ (raw_add a j))) {
    refine nat_induct (λ a, raw_add a (succ j) = succ (raw_add a j)) _ _
    { simplify rule off; rewrite (raw_add_0 (succ j)); rewrite (raw_add_0 j); reflexivity }
    { assume a ha hIH; rewrite (raw_add_succ a (succ j)); rewrite hIH;
      rewrite (raw_add_succ a j); reflexivity }
  };
  refine bspec omega (λ a, raw_add a (succ j) = succ (raw_add a j)) k hall hk
end;

// m #+ n = n #+ m
opaque symbol add_commute (m n : τ ι) : π (add m n = add n m) ≔
begin
  assume m n;
  have hkey : π (Ball omega (λ a, raw_add a (natify n) = raw_add (natify n) a)) {
    refine nat_induct (λ a, raw_add a (natify n) = raw_add (natify n) a) _ _
    { simplify rule off;
      rewrite (raw_add_0 (natify n));
      rewrite (raw_add_0_right (natify n) (natify_in_nat n));
      reflexivity }
    { assume a ha hIH;
      rewrite (raw_add_succ a (natify n));
      rewrite hIH;
      rewrite (raw_add_succ_right (natify n) a (natify_in_nat n));
      reflexivity }
  };
  rewrite (add_def m n); rewrite (add_def n m);
  refine bspec omega (λ a, raw_add a (natify n) = raw_add (natify n) a)
    (natify m) hkey (natify_in_nat m)
end;

// m #+ (n #+ k) = n #+ (m #+ k)   (from assoc + commute)
opaque symbol add_left_commute (m n k : τ ι) : π (add m (add n k) = add n (add m k)) ≔
begin
  assume m n k;
  refine eq_trans (eq_sym (add_assoc m n k))
    (eq_trans (feq (λ z, add z k) (add_commute m n)) (add_assoc n m k))
end;

// ===========================================================================
// raw_add / raw_mult a-c infrastructure (nat-level, for the mult laws)
// ===========================================================================

opaque symbol raw_add_assoc (a b c : τ ι) :
  π (a ∈ omega) → π (raw_add (raw_add a b) c = raw_add a (raw_add b c)) ≔
begin
  assume a b c ha;
  have hall : π (Ball omega (λ x, raw_add (raw_add x b) c = raw_add x (raw_add b c))) {
    refine nat_induct (λ x, raw_add (raw_add x b) c = raw_add x (raw_add b c)) _ _
    { simplify rule off; rewrite (raw_add_0 b); rewrite (raw_add_0 (raw_add b c)); reflexivity }
    { assume x hx hIH;
      rewrite (raw_add_succ x b);
      rewrite (raw_add_succ (raw_add x b) c);
      rewrite hIH;
      rewrite (raw_add_succ x (raw_add b c)); reflexivity }
  };
  refine bspec omega (λ x, raw_add (raw_add x b) c = raw_add x (raw_add b c)) a hall ha
end;

opaque symbol raw_add_commute (a b : τ ι) :
  π (a ∈ omega) → π (b ∈ omega) → π (raw_add a b = raw_add b a) ≔
begin
  assume a b ha hb;
  have hall : π (Ball omega (λ x, raw_add x b = raw_add b x)) {
    refine nat_induct (λ x, raw_add x b = raw_add b x) _ _
    { simplify rule off; rewrite (raw_add_0 b); rewrite (raw_add_0_right b hb); reflexivity }
    { assume x hx hIH;
      rewrite (raw_add_succ x b); rewrite hIH;
      rewrite (raw_add_succ_right b x hb); reflexivity }
  };
  refine bspec omega (λ x, raw_add x b = raw_add b x) a hall ha
end;

opaque symbol raw_add_left_commute (a b c : τ ι) :
  π (a ∈ omega) → π (b ∈ omega) → π (raw_add a (raw_add b c) = raw_add b (raw_add a c)) ≔
begin
  assume a b c ha hb;
  refine eq_trans (eq_sym (raw_add_assoc a b c ha))
    (eq_trans (feq (λ z, raw_add z c) (raw_add_commute a b ha hb)) (raw_add_assoc b a c hb))
end;

opaque symbol raw_mult_0_right (k : τ ι) : π (k ∈ omega) → π (raw_mult k empty = empty) ≔
begin
  assume k hk;
  have hall : π (Ball omega (λ x, raw_mult x empty = empty)) {
    refine nat_induct (λ x, raw_mult x empty = empty) _ _
    { simplify rule off; refine raw_mult_0 empty }
    { assume x hx hIH; rewrite (raw_mult_succ x empty); rewrite hIH; refine raw_add_0 empty }
  };
  refine bspec omega (λ x, raw_mult x empty = empty) k hall hk
end;

// raw_mult k (succ j) = raw_add k (raw_mult k j)   (induct k; step uses raw_add a/c)
opaque symbol raw_mult_succ_right (k j : τ ι) :
  π (k ∈ omega) → π (j ∈ omega) → π (raw_mult k (succ j) = raw_add k (raw_mult k j)) ≔
begin
  assume k j hk hj;
  have hall : π (Ball omega (λ x, raw_mult x (succ j) = raw_add x (raw_mult x j))) {
    refine nat_induct (λ x, raw_mult x (succ j) = raw_add x (raw_mult x j)) _ _
    { simplify rule off;
      rewrite (raw_mult_0 (succ j)); rewrite (raw_mult_0 j); rewrite (raw_add_0 empty);
      reflexivity }
    { assume x hx hIH;
      rewrite (raw_mult_succ x (succ j));
      rewrite hIH;
      rewrite (raw_mult_succ x j);
      rewrite (raw_add_succ j (raw_add x (raw_mult x j)));
      rewrite (raw_add_succ x (raw_add j (raw_mult x j)));
      rewrite (raw_add_left_commute j x (raw_mult x j) hj hx);
      reflexivity }
  };
  refine bspec omega (λ x, raw_mult x (succ j) = raw_add x (raw_mult x j)) k hall hk
end;

// ===========================================================================
// Multiplication laws
// ===========================================================================

// m #* n = n #* m
opaque symbol mult_commute (m n : τ ι) : π (mult m n = mult n m) ≔
begin
  assume m n;
  have hbn : π (natify n ∈ omega) { refine natify_in_nat n };
  have hkey : π (Ball omega (λ a, raw_mult a (natify n) = raw_mult (natify n) a)) {
    refine nat_induct (λ a, raw_mult a (natify n) = raw_mult (natify n) a) _ _
    { simplify rule off;
      rewrite (raw_mult_0 (natify n));
      rewrite (raw_mult_0_right (natify n) hbn);
      reflexivity }
    { assume a ha hIH;
      rewrite (raw_mult_succ a (natify n));
      rewrite hIH;
      rewrite (raw_mult_succ_right (natify n) a hbn ha);
      reflexivity }
  };
  rewrite (mult_def m n); rewrite (mult_def n m);
  refine bspec omega (λ a, raw_mult a (natify n) = raw_mult (natify n) a)
    (natify m) hkey (natify_in_nat m)
end;

// m #* succ(n) = m #+ (m #* n)
opaque symbol mult_succ_right (m n : τ ι) : π (mult m (succ n) = add m (mult m n)) ≔
begin
  assume m n;
  have hmn : π (raw_mult (natify m) (natify n) ∈ omega)
    { refine raw_mult_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n) };
  rewrite (mult_def m (succ n));
  rewrite (add_def m (mult m n));
  rewrite (mult_def m n);
  rewrite (natify_succ n);
  rewrite (raw_mult_succ_right (natify m) (natify n) (natify_in_nat m) (natify_in_nat n));
  rewrite (natify_ident (raw_mult (natify m) (natify n)) hmn);
  reflexivity
end;

// raw distributivity: raw_mult (raw_add a b) c = raw_add (raw_mult a c) (raw_mult b c)
opaque symbol raw_add_mult_distrib (a b c : τ ι) :
  π (a ∈ omega) → π (c ∈ omega) →
  π (raw_mult (raw_add a b) c = raw_add (raw_mult a c) (raw_mult b c)) ≔
begin
  assume a b c ha hc;
  have hall : π (Ball omega (λ x, raw_mult (raw_add x b) c
                                  = raw_add (raw_mult x c) (raw_mult b c))) {
    refine nat_induct (λ x, raw_mult (raw_add x b) c = raw_add (raw_mult x c) (raw_mult b c)) _ _
    { simplify rule off;
      rewrite (raw_add_0 b); rewrite (raw_mult_0 c); rewrite (raw_add_0 (raw_mult b c));
      reflexivity }
    { assume x hx hIH;
      rewrite (raw_add_succ x b);
      rewrite (raw_mult_succ (raw_add x b) c);
      rewrite hIH;
      rewrite (raw_mult_succ x c);
      rewrite (raw_add_assoc c (raw_mult x c) (raw_mult b c) hc);
      reflexivity }
  };
  refine bspec omega (λ x, raw_mult (raw_add x b) c = raw_add (raw_mult x c) (raw_mult b c)) a hall ha
end;

// (m #+ n) #* k = (m #* k) #+ (n #* k)
opaque symbol add_mult_distrib (m n k : τ ι) :
  π (mult (add m n) k = add (mult m k) (mult n k)) ≔
begin
  assume m n k;
  have hmn : π (raw_add (natify m) (natify n) ∈ omega)
    { refine raw_add_type (natify m) (natify n) (natify_in_nat m) (natify_in_nat n) };
  have hmk : π (raw_mult (natify m) (natify k) ∈ omega)
    { refine raw_mult_type (natify m) (natify k) (natify_in_nat m) (natify_in_nat k) };
  have hnk : π (raw_mult (natify n) (natify k) ∈ omega)
    { refine raw_mult_type (natify n) (natify k) (natify_in_nat n) (natify_in_nat k) };
  rewrite (mult_def (add m n) k);
  rewrite (add_def m n);
  rewrite (add_def (mult m k) (mult n k));
  rewrite (mult_def m k);
  rewrite (mult_def n k);
  rewrite (natify_ident (raw_add (natify m) (natify n)) hmn);
  rewrite (natify_ident (raw_mult (natify m) (natify k)) hmk);
  rewrite (natify_ident (raw_mult (natify n) (natify k)) hnk);
  refine raw_add_mult_distrib (natify m) (natify n) (natify k) (natify_in_nat m) (natify_in_nat k)
end;

// k #* (m #+ n) = (k #* m) #+ (k #* n)   (from commute + distrib)
opaque symbol add_mult_distrib_left (k m n : τ ι) :
  π (mult k (add m n) = add (mult k m) (mult k n)) ≔
begin
  assume k m n;
  refine eq_trans (mult_commute k (add m n))
    (eq_trans (add_mult_distrib m n k)
      (eq_trans (feq (λ z, add z (mult n k)) (mult_commute m k))
        (feq (λ z, add (mult k m) z) (mult_commute n k))))
end;

// (m #* n) #* k = m #* (n #* k)
opaque symbol mult_assoc (m n k : τ ι) : π (mult (mult m n) k = mult m (mult n k)) ≔
begin
  assume m n k;
  have hbn : π (natify n ∈ omega) { refine natify_in_nat n };
  have hbk : π (natify k ∈ omega) { refine natify_in_nat k };
  have hmn : π (raw_mult (natify m) (natify n) ∈ omega)
    { refine raw_mult_type (natify m) (natify n) (natify_in_nat m) hbn };
  have hnk : π (raw_mult (natify n) (natify k) ∈ omega)
    { refine raw_mult_type (natify n) (natify k) hbn hbk };
  have hkey : π (Ball omega (λ a, raw_mult (raw_mult a (natify n)) (natify k)
                        = raw_mult a (raw_mult (natify n) (natify k)))) {
    refine nat_induct (λ a, raw_mult (raw_mult a (natify n)) (natify k)
                        = raw_mult a (raw_mult (natify n) (natify k))) _ _
    { simplify rule off;
      rewrite (raw_mult_0 (natify n));
      rewrite (raw_mult_0 (natify k));
      rewrite (raw_mult_0 (raw_mult (natify n) (natify k)));
      reflexivity }
    { assume a ha hIH;
      rewrite (raw_mult_succ a (natify n));
      rewrite (raw_add_mult_distrib (natify n) (raw_mult a (natify n)) (natify k) hbn hbk);
      rewrite hIH;
      rewrite (raw_mult_succ a (raw_mult (natify n) (natify k)));
      reflexivity }
  };
  rewrite (mult_def (mult m n) k);
  rewrite (mult_def m n);
  rewrite (mult_def m (mult n k));
  rewrite (mult_def n k);
  rewrite (natify_ident (raw_mult (natify m) (natify n)) hmn);
  rewrite (natify_ident (raw_mult (natify n) (natify k)) hnk);
  refine bspec omega (λ a, raw_mult (raw_mult a (natify n)) (natify k)
                    = raw_mult a (raw_mult (natify n) (natify k)))
    (natify m) hkey (natify_in_nat m)
end;

// m #* (n #* k) = n #* (m #* k)   (from assoc + commute)
opaque symbol mult_left_commute (m n k : τ ι) :
  π (mult m (mult n k) = mult n (mult m k)) ≔
begin
  assume m n k;
  refine eq_trans (eq_sym (mult_assoc m n k))
    (eq_trans (feq (λ z, mult z k) (mult_commute m n)) (mult_assoc n m k))
end;

// units (1 = succ 0)
// 1 #* n = natify(n)
opaque symbol mult_1_natify (n : τ ι) : π (mult (succ empty) n = natify n) ≔
begin
  assume n;
  refine eq_trans (mult_succ empty n)
    (eq_trans (feq (λ z, add n z) (mult_0 n)) (add_0_right_natify n))
end;

// n #* 1 = natify(n)
opaque symbol mult_1_right_natify (n : τ ι) : π (mult n (succ empty) = natify n) ≔
begin
  assume n;
  refine eq_trans (mult_succ_right n empty)
    (eq_trans (feq (λ z, add n z) (mult_0_right n)) (add_0_right_natify n))
end;

// n ∈ nat ⟹ 1 #* n = n
opaque symbol mult_1 (n : τ ι) : π (n ∈ omega) → π (mult (succ empty) n = n) ≔
begin assume n hn; refine eq_trans (mult_1_natify n) (natify_ident n hn) end;

// n ∈ nat ⟹ n #* 1 = n
opaque symbol mult_1_right (n : τ ι) : π (n ∈ omega) → π (mult n (succ empty) = n) ≔
begin assume n hn; refine eq_trans (mult_1_right_natify n) (natify_ident n hn) end;

// ===========================================================================
// Cancellation
// ===========================================================================

// ⟦raw_add(k,m) = raw_add(k,n); k∈nat⟧ ⟹ m = n   (induct k)
opaque symbol raw_add_left_cancel (k m n : τ ι) :
  π (raw_add k m = raw_add k n) → π (k ∈ omega) → π (m = n) ≔
begin
  assume k m n heq hk;
  have hall : π (Ball omega (λ x, raw_add x m = raw_add x n ⇒ m = n)) {
    refine nat_induct (λ x, raw_add x m = raw_add x n ⇒ m = n) _ _
    { simplify rule off; assume h0;
      refine eq_trans (eq_sym (raw_add_0 m)) (eq_trans h0 (raw_add_0 n)) }
    { assume x hx hIH h;
      have h2 : π (succ (raw_add x m) = succ (raw_add x n)) {
        rewrite left (raw_add_succ x m); rewrite left (raw_add_succ x n); refine h };
      refine hIH (succ_inject (raw_add x m) (raw_add x n) h2) }
  };
  have hkP : π (raw_add k m = raw_add k n ⇒ m = n)
    { refine bspec omega (λ x, raw_add x m = raw_add x n ⇒ m = n) k hall hk };
  refine hkP heq
end;

// k #+ m = k #+ n ⟹ natify(m) = natify(n)
opaque symbol add_left_cancel_natify (k m n : τ ι) :
  π (add k m = add k n) → π (natify m = natify n) ≔
begin
  assume k m n heq;
  have hraw : π (raw_add (natify k) (natify m) = raw_add (natify k) (natify n)) {
    rewrite left (add_def k m); rewrite left (add_def k n); refine heq };
  refine raw_add_left_cancel (natify k) (natify m) (natify n) hraw (natify_in_nat k)
end;

// ⟦i = j; i #+ m = j #+ n; m∈nat; n∈nat⟧ ⟹ m = n
opaque symbol add_left_cancel (i j m n : τ ι) :
  π (i = j) → π (add i m = add j n) → π (m ∈ omega) → π (n ∈ omega) → π (m = n) ≔
begin
  assume i j m n hij haddeq hm hn;
  have haddeq2 : π (add j m = add j n)
    { refine eq_trans (feq (λ z, add z m) (eq_sym hij)) haddeq };
  have hnat : π (natify m = natify n) { refine add_left_cancel_natify j m n haddeq2 };
  refine eq_trans (eq_sym (natify_ident m hm)) (eq_trans hnat (natify_ident n hn))
end;

// ===========================================================================
// Subtraction is the inverse of addition
// ===========================================================================

// raw_diff (succ a) (succ b) = raw_diff a b   (induct b)
opaque symbol raw_diff_succ_succ (a b : τ ι) :
  π (b ∈ omega) → π (raw_diff (succ a) (succ b) = raw_diff a b) ≔
begin
  assume a b hb;
  have hall : π (Ball omega (λ x, raw_diff (succ a) (succ x) = raw_diff a x)) {
    refine nat_induct (λ x, raw_diff (succ a) (succ x) = raw_diff a x) _ _
    { simplify rule off;
      rewrite (raw_diff_succ (succ a) empty);
      rewrite (raw_diff_0 (succ a));
      rewrite (nat_case_succ empty (λ y, y) a);
      rewrite (raw_diff_0 a); reflexivity }
    { assume x hx hIH;
      rewrite (raw_diff_succ (succ a) (succ x)); rewrite hIH;
      rewrite (raw_diff_succ a x); reflexivity }
  };
  refine bspec omega (λ x, raw_diff (succ a) (succ x) = raw_diff a x) b hall hb
end;

// raw_diff 0 k = 0   (induct k)
opaque symbol raw_diff_0_left (k : τ ι) : π (k ∈ omega) → π (raw_diff empty k = empty) ≔
begin
  assume k hk;
  have hall : π (Ball omega (λ x, raw_diff empty x = empty)) {
    refine nat_induct (λ x, raw_diff empty x = empty) _ _
    { simplify rule off; refine raw_diff_0 empty }
    { assume x hx hIH; rewrite (raw_diff_succ empty x); rewrite hIH; refine nat_case_0 empty (λ y, y) }
  };
  refine bspec omega (λ x, raw_diff empty x = empty) k hall hk
end;

// (n #+ m) #- n = natify(m)   (raw_diff (raw_add a bm) a = bm, induct a)
opaque symbol diff_add_inverse (n m : τ ι) : π (diff (add n m) n = natify m) ≔
begin
  assume n m;
  have hkey : π (Ball omega (λ a, raw_diff (raw_add a (natify m)) a = natify m)) {
    refine nat_induct (λ a, raw_diff (raw_add a (natify m)) a = natify m) _ _
    { simplify rule off; rewrite (raw_add_0 (natify m)); rewrite (raw_diff_0 (natify m)); reflexivity }
    { assume a ha hIH;
      rewrite (raw_add_succ a (natify m));
      rewrite (raw_diff_succ_succ (raw_add a (natify m)) a ha);
      refine hIH }
  };
  have hnm : π (raw_add (natify n) (natify m) ∈ omega)
    { refine raw_add_type (natify n) (natify m) (natify_in_nat n) (natify_in_nat m) };
  rewrite (diff_def (add n m) n);
  rewrite (add_def n m);
  rewrite (natify_ident (raw_add (natify n) (natify m)) hnm);
  refine bspec omega (λ a, raw_diff (raw_add a (natify m)) a = natify m)
    (natify n) hkey (natify_in_nat n)
end;

// (m #+ n) #- n = natify(m)   (from diff_add_inverse + add_commute)
opaque symbol diff_add_inverse2 (m n : τ ι) : π (diff (add m n) n = natify m) ≔
begin
  assume m n;
  refine eq_trans (feq (λ z, diff z n) (add_commute m n)) (diff_add_inverse n m)
end;

// n #- (n #+ m) = 0   (raw_diff a (raw_add a bm) = 0, induct a)
opaque symbol diff_add_0 (n m : τ ι) : π (diff n (add n m) = empty) ≔
begin
  assume n m;
  have hbm : π (natify m ∈ omega) { refine natify_in_nat m };
  have hkey : π (Ball omega (λ a, raw_diff a (raw_add a (natify m)) = empty)) {
    refine nat_induct (λ a, raw_diff a (raw_add a (natify m)) = empty) _ _
    { simplify rule off; rewrite (raw_add_0 (natify m)); refine raw_diff_0_left (natify m) hbm }
    { assume a ha hIH;
      rewrite (raw_add_succ a (natify m));
      have hram : π (raw_add a (natify m) ∈ omega) { refine raw_add_type a (natify m) ha hbm };
      rewrite (raw_diff_succ_succ a (raw_add a (natify m)) hram);
      refine hIH }
  };
  have hnm : π (raw_add (natify n) (natify m) ∈ omega)
    { refine raw_add_type (natify n) (natify m) (natify_in_nat n) hbm };
  rewrite (diff_def n (add n m));
  rewrite (add_def n m);
  rewrite (natify_ident (raw_add (natify n) (natify m)) hnm);
  refine bspec omega (λ a, raw_diff a (raw_add a (natify m)) = empty)
    (natify n) hkey (natify_in_nat n)
end;

// (k #+ m) #- (k #+ n) = m #- n
opaque symbol diff_cancel (k m n : τ ι) : π (diff (add k m) (add k n) = diff m n) ≔
begin
  assume k m n;
  have hbm : π (natify m ∈ omega) { refine natify_in_nat m };
  have hbn : π (natify n ∈ omega) { refine natify_in_nat n };
  have hkey : π (Ball omega (λ a, raw_diff (raw_add a (natify m)) (raw_add a (natify n))
                                  = raw_diff (natify m) (natify n))) {
    refine nat_induct (λ a, raw_diff (raw_add a (natify m)) (raw_add a (natify n))
                            = raw_diff (natify m) (natify n)) _ _
    { simplify rule off; rewrite (raw_add_0 (natify m)); rewrite (raw_add_0 (natify n)); reflexivity }
    { assume a ha hIH;
      rewrite (raw_add_succ a (natify m));
      rewrite (raw_add_succ a (natify n));
      have hran : π (raw_add a (natify n) ∈ omega) { refine raw_add_type a (natify n) ha hbn };
      rewrite (raw_diff_succ_succ (raw_add a (natify m)) (raw_add a (natify n)) hran);
      refine hIH }
  };
  have hkm : π (raw_add (natify k) (natify m) ∈ omega)
    { refine raw_add_type (natify k) (natify m) (natify_in_nat k) hbm };
  have hkn : π (raw_add (natify k) (natify n) ∈ omega)
    { refine raw_add_type (natify k) (natify n) (natify_in_nat k) hbn };
  rewrite (diff_def (add k m) (add k n));
  rewrite (add_def k m);
  rewrite (add_def k n);
  rewrite (diff_def m n);
  rewrite (natify_ident (raw_add (natify k) (natify m)) hkm);
  rewrite (natify_ident (raw_add (natify k) (natify n)) hkn);
  refine bspec omega (λ a, raw_diff (raw_add a (natify m)) (raw_add a (natify n))
                          = raw_diff (natify m) (natify n))
    (natify k) hkey (natify_in_nat k)
end;

// (m #+ k) #- (n #+ k) = m #- n   (from diff_cancel + add_commute)
opaque symbol diff_cancel2 (m n k : τ ι) : π (diff (add m k) (add n k) = diff m n) ≔
begin
  assume m n k;
  refine eq_trans (feq (λ z, diff z (add n k)) (add_commute m k))
    (eq_trans (feq (λ z, diff (add k m) z) (add_commute n k)) (diff_cancel k m n))
end;

// i #- succ(j) = pred(i #- j)   (both = nat_case 0 (λx.x) (raw_diff (natify i)(natify j)))
opaque symbol diff_succ_eq_pred (i j : τ ι) : π (diff i (succ j) = pred (diff i j)) ≔
begin
  assume i j;
  rewrite (diff_def i (succ j));
  rewrite (natify_succ j);
  rewrite (raw_diff_succ (natify i) (natify j));
  rewrite (diff_def i j);
  rewrite (pred_def (raw_diff (natify i) (natify j)));
  reflexivity
end;

// ⟦i∈nat; j∈nat⟧ ⟹ i #- succ(j) = pred(i #- j)
opaque symbol nat_diff_pred (i j : τ ι) :
  π (i ∈ omega) → π (j ∈ omega) → π (diff i (succ j) = pred (diff i j)) ≔
begin assume i j hi hj; refine diff_succ_eq_pred i j end;

// ⟦i = succ(j); i∈nat⟧ ⟹ j = i #- 1 ∧ j ∈ nat   (1 = succ 0)
opaque symbol eq_succ_imp_eq_m1 (i j : τ ι) :
  π (i = succ j) → π (i ∈ omega) → π ((j = diff i (succ empty)) ∧ (j ∈ omega)) ≔
begin
  assume i j hij hi;
  have hsj : π (succ j ∈ omega) { rewrite left hij; refine hi };
  have hj : π (j ∈ omega) { refine succ_natD j hsj };
  have hm1 : π (diff i (succ empty) = j) {
    rewrite hij;
    rewrite (diff_succ_succ j empty);
    rewrite (diff_0 j);
    refine natify_ident j hj };
  refine ∧ᵢ (eq_sym hm1) hj
end;

// ===========================================================================
// Monotonicity of addition  (induct on the added quantity, succ-< monotone —
// simpler than Isabelle's succ_lt_induct)
// ===========================================================================

// lt x y ⟹ lt (succ x) (succ y)
opaque symbol succ_lt_mono (x y : τ ι) : π (lt x y) → π (lt (succ x) (succ y)) ≔
begin
  assume x y hlt;
  have hOy : π (Ord y) { refine ∧ₑ₂ hlt };
  refine ltI (succ x) (succ y)
    (Ord_succ_mem_iff_bwd x y hOy (ltD x y hlt)) (Ord_succ y hOy)
end;

// ⟦i<j; j∈nat⟧ ⟹ i #+ k < j #+ k
opaque symbol add_lt_mono1 (i j k : τ ι) :
  π (lt i j) → π (j ∈ omega) → π (lt (add i k) (add j k)) ≔
begin
  assume i j k hlt hj;
  have hi : π (i ∈ omega) { refine lt_nat_in_nat i j hlt hj };
  have hkey : π (Ball omega (λ c, lt (raw_add i c) (raw_add j c))) {
    refine nat_induct (λ c, lt (raw_add i c) (raw_add j c)) _ _
    { simplify rule off;
      rewrite (raw_add_0_right i hi); rewrite (raw_add_0_right j hj); refine hlt }
    { assume c hc hIH;
      rewrite (raw_add_succ_right i c hi); rewrite (raw_add_succ_right j c hj);
      refine succ_lt_mono (raw_add i c) (raw_add j c) hIH }
  };
  rewrite (add_def i k); rewrite (add_def j k);
  rewrite (natify_ident i hi); rewrite (natify_ident j hj);
  refine bspec omega (λ c, lt (raw_add i c) (raw_add j c)) (natify k) hkey (natify_in_nat k)
end;

// ⟦i<j; j∈nat⟧ ⟹ k #+ i < k #+ j
opaque symbol add_lt_mono2 (i j k : τ ι) :
  π (lt i j) → π (j ∈ omega) → π (lt (add k i) (add k j)) ≔
begin
  assume i j k hlt hj;
  rewrite (add_commute k i); rewrite (add_commute k j);
  refine add_lt_mono1 i j k hlt hj
end;

// ⟦i≤j; j∈nat⟧ ⟹ i #+ k ≤ j #+ k
opaque symbol add_le_mono1 (i j k : τ ι) :
  π (le i j) → π (j ∈ omega) → π (le (add i k) (add j k)) ≔
begin
  assume i j k hle hj;
  have hOaddj : π (Ord (add j k)) { refine nat_into_Ord (add j k) (add_type j k) };
  refine ∨ₑ (leE i j hle) _ _
  { assume hij;
    have hlt : π (lt (add i k) (add j k))
      { refine add_lt_mono1 i j k (ltI i j hij (nat_into_Ord j hj)) hj };
    refine leI (add i k) (add j k) (ltD (add i k) (add j k) hlt) hOaddj }
  { assume heq; refine le_eqI (add i k) (add j k) (feq (λ z, add z k) heq) hOaddj }
end;

// ⟦i≤j; j∈nat⟧ ⟹ k #+ i ≤ k #+ j
opaque symbol add_le_mono2 (i j k : τ ι) :
  π (le i j) → π (j ∈ omega) → π (le (add k i) (add k j)) ≔
begin
  assume i j k hle hj;
  rewrite (add_commute k i); rewrite (add_commute k j);
  refine add_le_mono1 i j k hle hj
end;

// ⟦i≤j; k≤l; j∈nat; l∈nat⟧ ⟹ i #+ k ≤ j #+ l
opaque symbol add_le_mono (i j k l : τ ι) :
  π (le i j) → π (le k l) → π (j ∈ omega) → π (l ∈ omega) → π (le (add i k) (add j l)) ≔
begin
  assume i j k l hij hkl hj hl;
  refine le_trans (add i k) (add j k) (add j l)
    (add_le_mono1 i j k hij hj) (add_le_mono2 k l j hkl hl)
end;

// ⟦i<j; k≤l; j∈nat; l∈nat⟧ ⟹ i #+ k < j #+ l
opaque symbol add_lt_le_mono (i j k l : τ ι) :
  π (lt i j) → π (le k l) → π (j ∈ omega) → π (l ∈ omega) → π (lt (add i k) (add j l)) ≔
begin
  assume i j k l hij hkl hj hl;
  refine lt_trans2 (add i k) (add j k) (add j l)
    (add_lt_mono1 i j k hij hj) (add_le_mono2 k l j hkl hl)
end;

// ⟦i≤j; k<l; j∈nat; l∈nat⟧ ⟹ i #+ k < j #+ l
opaque symbol add_le_lt_mono (i j k l : τ ι) :
  π (le i j) → π (lt k l) → π (j ∈ omega) → π (l ∈ omega) → π (lt (add i k) (add j l)) ≔
begin
  assume i j k l hij hkl hj hl;
  refine lt_trans1 (add i k) (add j k) (add j l)
    (add_le_mono1 i j k hij hj) (add_lt_mono2 k l j hkl hl)
end;

// ⟦i<j; k<l; j∈nat; l∈nat⟧ ⟹ i #+ k < j #+ l
opaque symbol add_lt_mono (i j k l : τ ι) :
  π (lt i j) → π (lt k l) → π (j ∈ omega) → π (l ∈ omega) → π (lt (add i k) (add j l)) ≔
begin
  assume i j k l hij hkl hj hl;
  refine add_lt_le_mono i j k l hij (leI k l (ltD k l hkl) (∧ₑ₂ hkl)) hj hl
end;

// ⟦k#+m ≤ k#+n; m∈nat; n∈nat⟧ ⟹ m ≤ n   (trichotomy: else n<m gives k#+n<k#+m≤k#+n)
opaque symbol add_le_elim1 (k m n : τ ι) :
  π (le (add k m) (add k n)) → π (m ∈ omega) → π (n ∈ omega) → π (le m n) ≔
begin
  assume k m n hle hm hn;
  refine ∨ₑ (Ord_linear m n (nat_into_Ord m hm) (nat_into_Ord n hn)) _ _
  { assume hmn; refine leI m n hmn (nat_into_Ord n hn) }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume heq; refine le_eqI m n heq (nat_into_Ord n hn) }
    { assume hnm;
      have hltadd : π (lt (add k n) (add k m))
        { refine add_lt_mono2 n m k (ltI n m hnm (nat_into_Ord m hm)) hm };
      refine ⊥ₑ (lt_not_refl (add k n)
        (lt_trans2 (add k n) (add k m) (add k n) hltadd hle)) } }
end;

// k#+m ≤ k#+n ⟹ natify(m) ≤ natify(n)
opaque symbol add_le_elim1_natify (k m n : τ ι) :
  π (le (add k m) (add k n)) → π (le (natify m) (natify n)) ≔
begin
  assume k m n hle;
  have hle2 : π (le (add k (natify m)) (add k (natify n)))
    { rewrite (add_natify2 k m); rewrite (add_natify2 k n); refine hle };
  refine add_le_elim1 k (natify m) (natify n) hle2 (natify_in_nat m) (natify_in_nat n)
end;

// ⟦k#+m < k#+n; m∈nat; n∈nat⟧ ⟹ m < n
opaque symbol add_lt_elim1 (k m n : τ ι) :
  π (lt (add k m) (add k n)) → π (m ∈ omega) → π (n ∈ omega) → π (lt m n) ≔
begin
  assume k m n hlt hm hn;
  refine ∨ₑ (Ord_linear m n (nat_into_Ord m hm) (nat_into_Ord n hn)) _ _
  { assume hmn; refine ltI m n hmn (nat_into_Ord n hn) }
  { assume hrest;
    refine ∨ₑ hrest _ _
    { assume heq;
      refine ⊥ₑ (lt_not_refl (add k m)
        (ind_eq (feq (λ z, add k z) heq) (λ w, lt (add k m) w) hlt)) }
    { assume hnm;
      have hltadd : π (lt (add k n) (add k m))
        { refine add_lt_mono2 n m k (ltI n m hnm (nat_into_Ord m hm)) hm };
      refine ⊥ₑ (lt_not_refl (add k n)
        (lt_trans (add k n) (add k m) (add k n) hltadd hlt)) } }
end;

// k#+m < k#+n ⟹ natify(m) < natify(n)
opaque symbol add_lt_elim1_natify (k m n : τ ι) :
  π (lt (add k m) (add k n)) → π (lt (natify m) (natify n)) ≔
begin
  assume k m n hlt;
  have hlt2 : π (lt (add k (natify m)) (add k (natify n)))
    { rewrite (add_natify2 k m); rewrite (add_natify2 k n); refine hlt };
  refine add_lt_elim1 k (natify m) (natify n) hlt2 (natify_in_nat m) (natify_in_nat n)
end;

// lift strict-monotone f (on k) to weak-monotone:  i≤j, j:k ⟹ f i ≤ f j
opaque symbol Ord_lt_mono_imp_le_mono (f : τ ι → τ ι) (k i j : τ ι)
  (lt_mono : Π a b, π (lt a b) → π (b ∈ k) → π (lt (f a) (f b)))
  (ford : Π a, π (a ∈ k) → π (Ord (f a)))
  (leij : π (le i j)) (jink : π (j ∈ k)) :
  π (le (f i) (f j)) ≔
begin
  assume f k i j lt_mono ford leij jink;
  have hOj : π (Ord j) { refine le_Ord2 i j leij };
  refine ∨ₑ (leE i j leij) _ _
  { assume hij;
    refine leI (f i) (f j)
      (ltD (f i) (f j) (lt_mono i j (ltI i j hij hOj) jink)) (ford j jink) }
  { assume heq; refine le_eqI (f i) (f j) (feq f heq) (ford j jink) }
end;

// pred(x) ≤ x  (x∈nat)
opaque symbol pred_le (x : τ ι) : π (x ∈ omega) → π (le (pred x) x) ≔
begin
  assume x hx;
  refine natE x (le (pred x) x) hx _ _
  { assume heq; rewrite heq; rewrite pred_0;
    refine le_refl empty (nat_into_Ord empty zero_in_omega) }
  { assume y hy heq; rewrite heq; rewrite (pred_succ_eq y);
    refine leI y (succ y) (succI1 y) (Ord_succ y (nat_into_Ord y hy)) }
end;

// m∈nat ⟹ (m #- n) ≤ m   (raw_diff m b ≤ m, induct b; step = pred_le + le_trans)
opaque symbol diff_le_self (m n : τ ι) : π (m ∈ omega) → π (le (diff m n) m) ≔
begin
  assume m n hm;
  have hkey : π (Ball omega (λ b, le (raw_diff m b) m)) {
    refine nat_induct (λ b, le (raw_diff m b) m) _ _
    { simplify rule off; rewrite (raw_diff_0 m); refine le_refl m (nat_into_Ord m hm) }
    { assume b hb hIH;
      rewrite (raw_diff_succ m b);
      rewrite left (pred_def (raw_diff m b));
      have hrt : π (raw_diff m b ∈ omega) { refine raw_diff_type m b hm hb };
      refine le_trans (pred (raw_diff m b)) (raw_diff m b) m
        (pred_le (raw_diff m b) hrt) hIH }
  };
  rewrite (diff_def m n);
  rewrite (natify_ident m hm);
  refine bspec omega (λ b, le (raw_diff m b) m) (natify n) hkey (natify_in_nat n)
end;

// ⟦0<k; k∈nat⟧ ⟹ ∃j∈nat. k = succ(j)
opaque symbol zero_lt_lemma (k : τ ι) :
  π (lt empty k) → π (k ∈ omega) → π (Bex omega (λ j, k = succ j)) ≔
begin
  assume k hlt hk;
  refine natE k (Bex omega (λ j, k = succ j)) hk _ _
  { assume heq;
    refine ⊥ₑ (emptyE empty (ind_eq (eq_sym heq) (λ w, empty ∈ w) (ltD empty k hlt))) }
  { assume x hx heq; refine ∃ᵢ x (∧ᵢ hx heq) }
end;
