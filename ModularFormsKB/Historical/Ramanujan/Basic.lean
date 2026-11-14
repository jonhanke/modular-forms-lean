import Mathlib.NumberTheory.ModularForms.RamanujanFormula
import ModularFormsKB.Citation
/-!
# Ramanujan's `P`, `Q`, `R` and his differential equations

Ramanujan, *On certain arithmetical functions* (1916; *Collected Papers* 1927, No. 18), works with the
power series in a complex variable `x`, `|x| < 1`,

* `P(x) = 1 - 24 ∑ σ₁(n) xⁿ`, `Q(x) = 1 + 240 ∑ σ₃(n) xⁿ`, `R(x) = 1 - 504 ∑ σ₅(n) xⁿ`,

and with `Φ_{r,s}(x) = ∑_{m,n ≥ 1} m^r n^s x^{mn} = ∑_{N ≥ 1} N^r σ_{s-r}(N) x^N` (here in the second, divisor-sum form,
for `r ≤ s`). He proves (No. 18, § 7, (30), p. 142)

  `x dP/dx = (P² - Q)/12`, `x dQ/dx = (PQ - R)/3`, `x dR/dx = (PR - Q²)/2`,

and tabulates the consequences (No. 18, Table III; No. 30, § 1, (1.71)–(1.74), p. 233)

  `Q - P² = 288 Φ_{1,2}`, `PQ - R = 720 Φ_{1,4}`, `Q² - PR = 1008 Φ_{1,6}`, `Q(PQ - R) = 720 Φ_{1,8}`.

## Relation to Mathlib

With `x = e^{2πiτ}`, `P`, `Q`, `R` are Mathlib's `EisensteinSeries.E2`, `ModularForm.E₄`, `ModularForm.E₆`
(`ramanujanP_qParam` etc. below), and Mathlib proves the differential equations in the variable `τ`
(`Derivative.normalizedDerivOfComplex_E₂`, `_E₄`, `_E₆`, by Seewoo Lee, via the dimension formula). The
theorems here restate them in Ramanujan's variable `x` and derive the table; the proofs are new only in
the change of variable `x = e^{2πiτ}` and the termwise differentiation of the series.
-/

noncomputable section

open Complex ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Ramanujan

/-- Ramanujan's `P(x) = 1 - 24 ∑_{n ≥ 1} σ₁(n) xⁿ` (Ramanujan 1916, No. 18; the series appear in the
differential equations (30), p. 142); the normalized Eisenstein series `E₂` in `x = e^{2πiτ}`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
def P (x : ℂ) : ℂ := 1 - 24 * ∑' n : ℕ+, (σ 1 n : ℂ) * x ^ (n : ℕ)

/-- Ramanujan's `Q(x) = 1 + 240 ∑_{n ≥ 1} σ₃(n) xⁿ`, i.e. `E₄`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
def Q (x : ℂ) : ℂ := 1 + 240 * ∑' n : ℕ+, (σ 3 n : ℂ) * x ^ (n : ℕ)

/-- Ramanujan's `R(x) = 1 - 504 ∑_{n ≥ 1} σ₅(n) xⁿ`, i.e. `E₆`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
def R (x : ℂ) : ℂ := 1 - 504 * ∑' n : ℕ+, (σ 5 n : ℂ) * x ^ (n : ℕ)

/-- Ramanujan's `Φ_{r,s}(x) = ∑_{m, n ≥ 1} m^r n^s x^{mn}`, in its divisor-sum form
`∑_{N ≥ 1} N^r σ_{s-r}(N) x^N` (valid for `r ≤ s`, the only case used). -/
@[kb "ramanujan1927" "No. 18, § 7, Φ_{r,s} in (30)–(31), p. 142"]
def Phi (r s : ℕ) (x : ℂ) : ℂ := ∑' N : ℕ+, (N : ℂ) ^ r * (σ (s - r) N : ℂ) * x ^ (N : ℕ)

end ModularFormsKB.Historical.Ramanujan
