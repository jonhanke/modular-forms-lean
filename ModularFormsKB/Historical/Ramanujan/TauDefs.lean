import ModularFormsKB.Historical.Ramanujan.PartitionDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ModularFormsKB.Citation
/-!
# Ramanujan's `τ`: congruences, recurrences, and Question 387 (statements)

Ramanujan, *On certain arithmetical functions* (1916; *Collected Papers* 1927, No. 18), *Congruence properties
of partitions* (1919; No. 28) and the posthumous manuscript of the same title (No. 30); Question 387
(J. Indian Math. Soc. 4, p. 120; *Collected Papers*, p. 326).

`tau n` is Ramanujan's `τ(n)`, defined (No. 18, (92)) by `∑ τ(n) xⁿ = x ∏_{n ≥ 1} (1 - xⁿ)²⁴`, here as the
coefficients of the integer power series `X · eulerSeries ^ 24`. The proofs are in `Tau.lean` and
`Question387.lean`.
-/

noncomputable section

open PowerSeries Finset
open scoped ArithmeticFunction.sigma Real

namespace ModularFormsKB.Historical.Ramanujan

/-- Ramanujan's `τ(n)` (No. 18, (92), p. 151): the coefficient of `xⁿ` in `x ∏_{n ≥ 1} (1 - xⁿ)²⁴`. -/
def tau (n : ℕ) : ℤ := (X * eulerSeries ^ 24 : ℤ⟦X⟧).coeff n

/-- **Ramanujan's congruence `τ(5n) ≡ 0 (mod 5)`** (No. 28, p. 230; proof in the manuscript No. 30;
see also the editors' note in App. I, p. 346). -/
@[kb "ramanujan1927" "No. 28, p. 230"]
def TauModFive : Prop := ∀ n : ℕ, (5 : ℤ) ∣ tau (5 * n)

/-- **Ramanujan's congruence modulo 7** (No. 28, p. 230):
`τ(7n), τ(7n + 3), τ(7n + 5), τ(7n + 6) ≡ 0 (mod 7)`. -/
@[kb "ramanujan1927" "No. 28, p. 230"]
def TauModSeven : Prop := ∀ n : ℕ, n % 7 = 0 ∨ n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6 → (7 : ℤ) ∣ tau n

/-- **Ramanujan's congruence modulo 23** (No. 28, p. 230): `τ(23n + ν) ≡ 0
(mod 23)` for `ν` a quadratic non-residue modulo `23`, i.e. `τ(n) ≡ 0 (mod 23)` whenever `n` is not a square
modulo `23` (`0` counts as a square). Stated, not proved: see loose end LE-MF-0281. -/
@[kb "ramanujan1927" "No. 28, p. 230"]
def TauModTwentyThree : Prop := ∀ n : ℕ, ¬ IsSquare (n : ZMod 23) → (23 : ℤ) ∣ tau n

/-- **Ramanujan's first recurrence for `τ`** (No. 18, § 17, (99), p. 152, first
part): `(n - 1) τ(n) = -24 ∑_{k=1}^{n-1} σ₁(k) τ(n - k)`. -/
@[kb "ramanujan1927" "No. 18, § 17, (99), p. 152"]
def TauRecurrenceSigma : Prop :=
  ∀ n : ℕ, ((n : ℤ) - 1) * tau n = -24 * ∑ k ∈ Ico 1 n, (σ 1 k : ℤ) * tau (n - k)

/-- **Ramanujan's second recurrence for `τ`** (No. 18, § 17, (100), p. 153,
second part): with `t_r = r(r-1)/2`,
`∑_{r ≥ 1} (-1)^{r-1} (2r - 1) (n - 1 - 9 t_r) τ(n - t_r) = 0`, i.e.
`(n-1) τ(n) - 3(n-10) τ(n-1) + 5(n-28) τ(n-3) - 7(n-55) τ(n-6) + ⋯ = 0`.
Written with `r = j + 1`, `t_r = j(j+1)/2`, the sum over `j` with `j(j+1)/2 < n`. -/
@[kb "ramanujan1927" "No. 18, § 17, (100), p. 153"]
def TauRecurrenceJacobi : Prop :=
  ∀ n : ℕ, ∑ j ∈ (range n).filter (fun j ↦ j * (j + 1) / 2 < n),
    (-1 : ℤ) ^ j * (2 * j + 1) * ((n : ℤ) - 1 - 9 * (j * (j + 1) / 2 : ℕ)) * tau (n - j * (j + 1) / 2) = 0

/-- **Ramanujan's Question 387** (J. Indian Math. Soc. 4 (1912), p. 120; *Collected Papers*, p. 326):
`∑_{n ≥ 1} n / (e^{2πn} - 1) = 1/24 - 1/(8π)`, equivalently `E₂(i) = 3/π`
(index shifted to start at `0`). -/
@[kb "ramanujan1927" "Question 387, p. 326"]
def Question387 : Prop :=
  HasSum (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / (Real.exp (2 * π * (n + 1 : ℕ)) - 1)) (1 / 24 - 1 / (8 * π))

end ModularFormsKB.Historical.Ramanujan
