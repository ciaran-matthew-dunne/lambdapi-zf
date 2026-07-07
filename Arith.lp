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
