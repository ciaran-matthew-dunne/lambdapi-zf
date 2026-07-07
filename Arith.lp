// Arith.lp — Natural-number arithmetic (Isabelle/ZF Arith.thy, Paulson).
//
// add/diff/mult/div/mod on nat (= omega in this port), plus the natify
// coercion.  raw_* are the primrec/transrec kernels; the public operators
// coerce both arguments through natify first.
//
// Isabelle source: Arith.thy (imports Univ).

require open ZF.ZF_Base ZF.upair ZF.pair ZF.equalities ZF.func
            ZF.Ordinal ZF.Nat_ZF ZF.Epsilon ZF.Univ;

// ===========================================================================
// Definitions
// ===========================================================================

// pred(y) = nat_case(0, λx. x, y)   — inverse of succ
symbol pred (y : τ ι) : τ ι ≔ nat_case empty (λ x, x) y;

// natify: coerces non-nats to nats, identity on nat.
// natify ≡ Vrecursor(λf a. if a = succ(pred a) then succ(f`pred a) else 0)
symbol natify (x : τ ι) : τ ι ≔
  Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) x;

// raw_add / raw_diff / raw_mult: primitive-recursion kernels (Isabelle primrec).
//   raw_add(0,n)=n,       raw_add(succ m,n)=succ(raw_add(m,n))
//   raw_diff(m,0)=m,      raw_diff(m,succ n)=nat_case(0,λx.x, raw_diff(m,n))
//   raw_mult(0,n)=0,      raw_mult(succ m,n)=raw_add(n, raw_mult(m,n))
symbol raw_add (m n : τ ι) : τ ι ≔ rec m n (λ x r, succ r);
symbol raw_diff (m n : τ ι) : τ ι ≔ rec n m (λ y r, nat_case empty (λ x, x) r);
symbol raw_mult (m n : τ ι) : τ ι ≔ rec m empty (λ x r, raw_add n r);

// Public operators: coerce both arguments through natify.
symbol add (m n : τ ι) : τ ι ≔ raw_add (natify m) (natify n);
symbol diff (m n : τ ι) : τ ι ≔ raw_diff (natify m) (natify n);
symbol mult (m n : τ ι) : τ ι ≔ raw_mult (natify m) (natify n);

// raw_div / raw_mod via transfinite recursion.
//   raw_div(m,n) = transrec(m, λj f. if j<n ∨ n=0 then 0 else succ(f`(j #- n)))
//   raw_mod(m,n) = transrec(m, λj f. if j<n ∨ n=0 then j else f`(j #- n))
symbol raw_div (m n : τ ι) : τ ι ≔
  transrec m (λ j f, If (lt j n ∨ (n = empty)) empty (succ (fapply f (diff j n))));
symbol raw_mod (m n : τ ι) : τ ι ≔
  transrec m (λ j f, If (lt j n ∨ (n = empty)) j (fapply f (diff j n)));

symbol div (m n : τ ι) : τ ι ≔ raw_div (natify m) (natify n);
symbol mod (m n : τ ι) : τ ι ≔ raw_mod (natify m) (natify n);

// ===========================================================================
// Primrec defining equations (via rec_0 / rec_succ — unconditional in succ).
// ===========================================================================

opaque symbol raw_add_0 (n : τ ι) : π (raw_add empty n = n) ≔
begin assume n; refine rec_0 n (λ x r, succ r) end;

opaque symbol raw_add_succ (m n : τ ι) :
  π (raw_add (succ m) n = succ (raw_add m n)) ≔
begin assume m n; refine rec_succ m n (λ x r, succ r) end;

opaque symbol raw_diff_0 (m : τ ι) : π (raw_diff m empty = m) ≔
begin assume m; refine rec_0 m (λ y r, nat_case empty (λ x, x) r) end;

opaque symbol raw_diff_succ (m n : τ ι) :
  π (raw_diff m (succ n) = nat_case empty (λ x, x) (raw_diff m n)) ≔
begin assume m n; refine rec_succ n m (λ y r, nat_case empty (λ x, x) r) end;

opaque symbol raw_mult_0 (n : τ ι) : π (raw_mult empty n = empty) ≔
begin assume n; refine rec_0 empty (λ x r, raw_add n r) end;

opaque symbol raw_mult_succ (m n : τ ι) :
  π (raw_mult (succ m) n = raw_add n (raw_mult m n)) ≔
begin assume m n; refine rec_succ m empty (λ x r, raw_add n r) end;

// ===========================================================================
// pred
// ===========================================================================

opaque symbol pred_0 : π (pred empty = empty) ≔
begin refine nat_case_0 empty (λ x, x) end;

opaque symbol pred_succ_eq (y : τ ι) : π (pred (succ y) = y) ≔
begin assume y; refine nat_case_succ empty (λ x, x) y end;

opaque symbol pred_type (m : τ ι) : π (m ∈ omega) → π (pred m ∈ omega) ≔
begin
  assume m hm;
  refine natE m (pred m ∈ omega) hm _ _
  { assume heq; rewrite heq; rewrite pred_0; refine zero_in_omega }
  { assume x hx heq; rewrite heq; rewrite (pred_succ_eq x); refine hx }
end;

// ===========================================================================
// Typing rules (Arith.thy §"Typing rules").  raw_* by induction on the
// recursion argument; via the unconditional primrec equations above.
// ===========================================================================

opaque symbol raw_add_type (m n : τ ι) :
  π (m ∈ omega) → π (n ∈ omega) → π (raw_add m n ∈ omega) ≔
begin
  assume m n hm hn;
  have hall : π (Ball omega (λ k, raw_add k n ∈ omega)) {
    refine nat_induct (λ k, raw_add k n ∈ omega) _ _
    { simplify rule off; rewrite (raw_add_0 n); refine hn }
    { assume k hk hIH;
      rewrite (raw_add_succ k n);
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
    { assume k hk hIH;
      rewrite (raw_mult_succ k n);
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
    { assume k hk hIH;
      rewrite (raw_diff_succ m k);
      refine pred_type (raw_diff m k) hIH }
  };
  refine bspec omega (λ k, raw_diff m k ∈ omega) n hall hn
end;

// ===========================================================================
// natify — the coercion to nat.  natify(succ x)=succ(natify x), natify(0)=0.
// Proved via def/Vrecursor_eq: natify a = Hn (λx∈Vset(rank a). natify x) a.
// ===========================================================================

opaque symbol natify_0 : π (natify empty = empty) ≔
begin
  have h1 : π (Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) empty
              = empty) {
    rewrite Vrecursor_eq;
    simplify rule off;
    rewrite pred_0;
    refine If_not_P (empty = succ empty) _ _ _;
    assume heq;
    refine cons_not_empty empty empty (eq_sym heq)
  };
  refine h1
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
  have h1 : π (Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) (succ y)
              = succ (natify y)) {
    rewrite Vrecursor_eq;
    simplify rule off;
    rewrite pred_succ_eq;
    rewrite (If_P (succ y = succ y) _ _ (eq_refl (succ y)));
    have hb : π (fapply (Lambda (Vset (rank (succ y)))
          (λ x, Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) x)) y
        = natify y)
      { refine beta (Vset (rank (succ y)))
          (λ x, Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) x)
          y hy_in };
    rewrite hb;
    reflexivity
  };
  refine h1
end;

// (∀z. x ≠ succ z) ⟹ natify(x) = 0
opaque symbol natify_non_succ (x : τ ι) :
  π (`∀ z, x ≠ succ z) → π (natify x = empty) ≔
begin
  assume x hns;
  have h1 : π (Vrecursor (λ f a, If (a = succ (pred a)) (succ (fapply f (pred a))) empty) x
              = empty) {
    rewrite Vrecursor_eq;
    simplify rule off;
    refine If_not_P (x = succ (pred x)) _ _ (hns (pred x))
  };
  refine h1
end;

// n ∈ nat ⟹ natify(n) = n
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

// ⟦natify(x) = y; x ∈ nat⟧ ⟹ x = y
opaque symbol natify_eqE (x y : τ ι) :
  π (natify x = y) → π (x ∈ omega) → π (x = y) ≔
begin
  assume x y hxy hx;
  refine eq_trans (eq_sym (natify_ident x hx)) hxy
end;
