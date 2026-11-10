import Mathlib.NumberTheory.LSeries.Injectivity
import ModularFormsKB.Citation
/-!
# Miyake §3.2: uniqueness of the coefficients of a Dirichlet series

Miyake, *Modular Forms* (Springer 1989), §3.2, p. 85, Lemma 3.2.1.

Miyake's series `Σ_{n ≥ 1} a_n n^{-s}` is Mathlib's `LSeries a s` (the value `a 0` is ignored);
"absolutely convergent at `s = σ₀`" is `LSeriesSummable a σ₀`. The proof is Mathlib's
`LSeries.eq_of_LSeries_eventually_eq` (the same idea as Miyake's: let `σ → ∞` along the reals).
-/

open Filter

namespace ModularFormsKB.Miyake

/-- **Miyake, Lemma 3.2.1.** If `Σ a_n n^{-s}` and `Σ b_n n^{-s}` converge absolutely at
`s = σ₀ > 0` and agree on `Re(s) ≥ σ₀`, then `a_n = b_n` for all `n ≥ 1`. -/
@[kb "miyake1989" "Lemma 3.2.1, p. 85"]
theorem eq_of_LSeries_eq {a b : ℕ → ℂ} {σ₀ : ℝ} (_hσ₀ : 0 < σ₀)
    (ha : LSeriesSummable a σ₀) (hb : LSeriesSummable b σ₀)
    (hab : ∀ s : ℂ, σ₀ ≤ s.re → LSeries a s = LSeries b s) {n : ℕ} (hn : 1 ≤ n) :
    a n = b n := by
  refine LSeries.eq_of_LSeries_eventually_eq
    (ha.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
    (hb.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)) ?_ (by omega)
  filter_upwards [eventually_ge_atTop σ₀] with x hx
  exact hab x (by simpa using hx)

end ModularFormsKB.Miyake
