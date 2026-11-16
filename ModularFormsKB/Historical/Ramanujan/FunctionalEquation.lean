import Mathlib.NumberTheory.LSeries.RiemannZeta
import ModularFormsKB.Citation
/-!
# The functional equation of `ζ` in Ramanujan's form

Ramanujan, *Collected Papers*, No. 9 (*Sum of the square roots of the first `n` natural numbers*), § 3, (9), p. 48,
quotes as well known: for `Re r > 1` the constant in the approximate summation of `1^{r-1} + 2^{r-1} + 3^{r-1} + ⋯`,
that is `ζ(1 - r)`, equals `2 Γ(r) cos(πr/2) (2π)^{-r} (1^{-r} + 2^{-r} + 3^{-r} + ⋯)`.

Thin wrapper of Mathlib's `riemannZeta_one_sub` (Riemann 1859) and `zeta_eq_tsum_one_div_nat_add_one_cpow`.
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Ramanujan

/-- **Ramanujan, No. 9, § 3, (9)** (p. 48): for `Re r > 1`,
`ζ(1 - r) = 2 Γ(r) cos(πr/2) / (2π)^r · ∑_{n ≥ 1} n^{-r}`. -/
@[kb "ramanujan1927" "No. 9, § 3, (9), p. 48"]
def RamanujanZetaFunctionalEquation : Prop :=
  ∀ r : ℂ, 1 < r.re →
    riemannZeta (1 - r) =
      2 * Gamma r * cos (π * r / 2) / (2 * π) ^ r * ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ r

/-- **Ramanujan, No. 9, § 3, (9)**. Wrapper of `riemannZeta_one_sub`. -/
@[kb "ramanujan1927" "No. 9, § 3, (9), p. 48"]
theorem ramanujanZetaFunctionalEquation : RamanujanZetaFunctionalEquation := by
  intro r hr
  have hs : ∀ n : ℕ, r ≠ -n := by
    intro n h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs' : r ≠ 1 := by
    intro h
    rw [h, one_re] at hr
    exact lt_irrefl _ hr
  rw [riemannZeta_one_sub hs hs', ← zeta_eq_tsum_one_div_nat_add_one_cpow hr, cpow_neg]
  ring

end ModularFormsKB.Historical.Ramanujan
