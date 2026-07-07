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
