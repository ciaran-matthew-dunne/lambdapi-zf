// OrdLeast.lp — least-ordinal operator (μ), ε-FREE.
//
// Provides `Least P` = the least ordinal satisfying P, defined via ZF.The
// (guarded definite description — NO Hilbert ε, hence no choice), plus the two
// lemmas the hyperset development needs: `Least_equality` and `LeastI`.
//
// Kept deliberately minimal and fully proved (0 admits) so downstream code can
// import it without pulling in the heavily-admitted `Cardinal` skeleton (which
// is where Isabelle/ZF puts `Least`). Faithful to `isabelle-src/Cardinal.thy`.

require open ZF.ZF_Base ZF.upair ZF.Ordinal;

// Least(P) ≡ THE i. Ord(i) ∧ P(i) ∧ (∀ j. j < i → ¬ P(j))
symbol Least (P : τ ι → Prop) : τ ι ≔
  The (λ i, Ord i ∧ P i ∧ (`∀ (j : τ ι), lt j i ⇒ ¬ P j));

// Least_equality: if i witnesses P, is an ordinal, and nothing below it does,
// then the least such is exactly i. (Cardinal.thy Least_equality.)
opaque symbol Least_equality (P : τ ι → Prop) (i : τ ι) :
  π (P i) → π (Ord i) → (Π (x : τ ι), π (lt x i) → π (¬ P x)) →
  π (Least P = i) ≔
begin
  assume P i hPi hOi hmin;
  refine the_equality (λ k, Ord k ∧ P k ∧ (`∀ (j : τ ι), lt j k ⇒ ¬ P j)) i _ _
  { // i satisfies the guard predicate
    refine ∧ᵢ hOi (∧ᵢ hPi _);
    assume j hj; refine hmin j hj }
  { // uniqueness: any k satisfying the predicate equals i (ordinal trichotomy)
    assume k hk;
    have hOk : π (Ord k) { refine ∧ₑ₁ hk };
    have hPk : π (P k) { refine ∧ₑ₁ (∧ₑ₂ hk) };
    have hmink : π (`∀ (j : τ ι), lt j k ⇒ ¬ P j) { refine ∧ₑ₂ (∧ₑ₂ hk) };
    refine ∨ₑ (Ord_linear i k hOi hOk) _ _
    { // i ∈ k ⇒ lt i k ⇒ ¬ P i, contradicting P i
      assume hik; refine ⊥ₑ (hmink i (ltI i k hik hOk) hPi) }
    { assume hd; refine ∨ₑ hd _ _
      { assume hik; refine eq_sym hik }
      { // k ∈ i ⇒ lt k i ⇒ ¬ P k, contradicting P k
        assume hki; refine ⊥ₑ (hmin k (ltI k i hki hOi) hPk) } } }
end;

// LeastI: if some ordinal i satisfies P, then Least P satisfies P.
// (Cardinal.thy LeastI, by transfinite induction.)
opaque symbol LeastI (P : τ ι → Prop) (i : τ ι) :
  π (P i) → π (Ord i) → π (P (Least P)) ≔
begin
  assume P i hPi hOi;
  have hind : π (P i ⇒ P (Least P))
    { refine trans_induct i (λ i, P i ⇒ P (Least P)) hOi _;
      assume x hOx hIH hPx;
      refine ∨ₑ (em (P (Least P))) _ _
      { assume hyes; refine hyes }
      { assume hno;
        // Nothing below x satisfies P: else the IH would give P(Least P).
        have hmin : Π (z : τ ι), π (lt z x) → π (¬ P z)
          { assume z hzx hPz; refine hno (hIH z (ltD z x hzx) hPz) };
        have hLeq : π (Least P = x) { refine Least_equality P x hPx hOx hmin };
        refine ind_eq hLeq (λ w, P w) hPx } };
  refine hind hPi
end;
