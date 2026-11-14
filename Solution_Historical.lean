/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Historical.Jacobi
import ModularFormsKB.Historical.Ramanujan
import ModularFormsKB.Historical.Weber
import ModularFormsKB.Historical.Kronecker

/-!
# Headline statements of modular-forms-lean 0.3.1: historical theorems of Jacobi, Ramanujan, Weber and Kronecker, proved

A topic, not a book: theorems read in the original papers (Jacobi, *Fundamenta nova*, 1829; Ramanujan, *On certain
arithmetical functions*, 1916, paper 18 of his *Collected Papers*, 1927; Weber, *Elliptische Functionen und
algebraische Zahlen*, 1891; Kronecker, *Zur Theorie der elliptischen Functionen*, Werke 5).

The statements of `Challenge_Historical.lean`, each proved by appeal to the library theorem. `lake comparator`
(configured by `comparator/Historical.json`) checks that each statement here is exactly the one in
`Challenge_Historical.lean` and that its proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

Each statement is the library's statement, copied, except that a named statement in the conclusion is unfolded. The
statements were not yet reviewed by a human (see the README). These libraries import Mathlib modules only.

One theorem is **conditional**: `weber_theta_eta` assumes the Jacobi triple product identity as the named input
`ModularFormsKB.Historical.Weber.JacobiTripleProduct` (a hypothesis of the theorem, a `Prop` structure, not an
axiom; neither Mathlib nor Tau Ceti proves the identity). The others are unconditional.

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `ModularFormsKB.Historical.Jacobi.IsLegendreSolution` (a `C³` solution on `(0, 1)` of Legendre's equation
  `(k - k³) y'' + (1 - 3k²) y' - k y = 0`), `ModularFormsKB.Historical.Jacobi.jacobiR` (`(1 + k²)/(k - k³)`),
  `ModularFormsKB.Historical.Jacobi.jacobiΘ`, `ModularFormsKB.Historical.Jacobi.jacobiH` (Jacobi's `Θ` and `H` as
  values of Mathlib's `jacobiTheta₂`)
* `ModularFormsKB.Historical.Ramanujan.P`, `.Q`, `.R` (Ramanujan's `1 - 24 Σ σ₁(n) xⁿ`, `1 + 240 Σ σ₃(n) xⁿ`,
  `1 - 504 Σ σ₅(n) xⁿ`)
* `ModularFormsKB.Historical.Weber.weberTheta00`, `.weberTheta01`, `.weberTheta10` (Weber's theta functions, values
  of `jacobiTheta₂`), `ModularFormsKB.Historical.Weber.weberF₁`, `ModularFormsKB.WeberHeegnerStark.weberF`,
  `ModularFormsKB.WeberHeegnerStark.weberF₂` (Weber's functions `f`, `f₁`, `f₂`, quotients of Dedekind's `η`)
* `ModularFormsKB.Historical.Kronecker.ser` (Kronecker's series `Ser_ρ`, the limit of the square partial sums)
-/

namespace ModularFormsKB.Headlines

section Jacobi

open Set Complex ModularFormsKB.Historical.Jacobi
open scoped Real

/-- **Jacobi's differential equation of the modular equations** (Jacobi, *Fundamenta nova*, § 33, (7)–(8)). Let
`A`, `B` be solutions of Legendre's equation on `(0, 1)` (Jacobi's `K` and `K'`) with `A ≠ 0` and nonvanishing
Wronskian, and let `λ` be a `C³` function on an open `I ⊆ (0, 1)` with values in `(0, 1)` related to `k` by a
modular equation `B(λ)/A(λ) = (a B(k)/A(k) + b)/(c B(k)/A(k) + d)` with `ad - bc ≠ 0` (for a transformation of order
`n`: `Λ'/Λ = n K'/K`). Then on `I`: `3 λ''² - 2 λ' λ''' + λ'² [((1 + k²)/(k - k³))² - ((1 + λ²)/(λ - λ³))² λ'²] = 0`. -/
theorem jacobi_modular_equation_ode {A B lam : ℝ → ℝ} {I : Set ℝ} {a b c d : ℝ}
    (hA : IsLegendreSolution A) (hB : IsLegendreSolution B)
    (hA0 : ∀ k ∈ Ioo (0 : ℝ) 1, A k ≠ 0)
    (hW : ∀ k ∈ Ioo (0 : ℝ) 1, A k * deriv B k - deriv A k * B k ≠ 0)
    (hI : IsOpen I) (hI01 : I ⊆ Ioo 0 1) (hlam : ContDiffOn ℝ 3 lam I)
    (hlam01 : MapsTo lam I (Ioo 0 1)) (hM : a * d - b * c ≠ 0)
    (hden : ∀ k ∈ I, c * (B k / A k) + d ≠ 0)
    (hmod : ∀ k ∈ I, B (lam k) / A (lam k) = (a * (B k / A k) + b) / (c * (B k / A k) + d)) :
    ∀ k ∈ I,
      3 * iteratedDeriv 2 lam k ^ 2 - 2 * deriv lam k * iteratedDeriv 3 lam k +
        deriv lam k ^ 2 * (jacobiR k ^ 2 - jacobiR (lam k) ^ 2 * deriv lam k ^ 2) = 0 := by
  exact ModularFormsKB.Historical.Jacobi.jacobi_modular_equation_ode hA hB hA0 hW hI hI01 hlam hlam01 hM hden hmod

/-- **The Fourier series of Jacobi's `Θ` and `H`** (Jacobi, *Fundamenta nova*, § 62). With `q^{n²} = e^{πin²τ}`
(`Im τ > 0`): `Θ(x) = 1 + 2 Σ_{n ≥ 1} (-1)ⁿ q^{n²} cos 2nx` and
`H(x) = 2 Σ_{n ≥ 0} (-1)ⁿ q^{(n + 1/2)²} sin (2n + 1)x`. -/
theorem jacobi_theta_fourier (x : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiΘ x τ = 1 + 2 * ∑' n : ℕ+,
      (-1 : ℂ) ^ (n : ℕ) * cexp (π * I * (n : ℂ) ^ 2 * τ) * Complex.cos (2 * n * x) ∧
    jacobiH x τ = 2 * ∑' n : ℕ,
      (-1 : ℂ) ^ n * cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ) * Complex.sin ((2 * n + 1) * x) := by
  exact ⟨ModularFormsKB.Historical.Jacobi.jacobiΘ_eq_cos_series x hτ, ModularFormsKB.Historical.Jacobi.jacobiH_eq_sin_series x hτ⟩

end Jacobi

section Ramanujan

open ModularFormsKB.Historical.Ramanujan

/-- **Ramanujan's differential equations** (Ramanujan 1916, (30)), in his variable `x` (`|x| < 1`):
`x dP/dx = (P² - Q)/12`, `x dQ/dx = (PQ - R)/3`, `x dR/dx = (PR - Q²)/2`. Mathlib proves them in the variable `τ`
(`x = e^{2πiτ}`) for the normalized Eisenstein series; the library derives the form in `x` on the whole unit disc. -/
theorem ramanujan_differential_equations {x : ℂ} (hx : ‖x‖ < 1) :
    x * deriv P x = (P x ^ 2 - Q x) / 12 ∧ x * deriv Q x = (P x * Q x - R x) / 3 ∧
      x * deriv R x = (P x * R x - Q x ^ 2) / 2 := by
  exact ⟨ModularFormsKB.Historical.Ramanujan.x_deriv_P hx, ModularFormsKB.Historical.Ramanujan.x_deriv_Q hx, ModularFormsKB.Historical.Ramanujan.x_deriv_R hx⟩

end Ramanujan

section Weber

open Complex ModularFormsKB.Historical.Weber ModularFormsKB.WeberHeegnerStark
open scoped Real

/-- **Weber's theta functions as products of `η` and his functions `f`** (Weber 1891, § 21, (9)),
**conditional on the Jacobi triple product identity** (the named input `JacobiTripleProduct`): for `Im ω > 0`,
`ϑ₀₀(ω) = η(ω) f(ω)²`, `ϑ₀₁(ω) = η(ω) f₁(ω)²` and `ϑ₁₀(ω) = η(ω) f₂(ω)²`. -/
theorem weber_theta_eta (hJ : JacobiTripleProduct) {ω : ℂ} (hω : 0 < ω.im) :
    weberTheta00 ω = ModularForm.eta ω * weberF ω ^ 2 ∧
      weberTheta01 ω = ModularForm.eta ω * weberF₁ ω ^ 2 ∧
      weberTheta10 ω = ModularForm.eta ω * weberF₂ ω ^ 2 := by
  exact ⟨ModularFormsKB.Historical.Weber.weberTheta00_eq hJ hω, ModularFormsKB.Historical.Weber.weberTheta01_eq hJ hω, ModularFormsKB.Historical.Weber.weberTheta10_eq hJ hω⟩

end Weber

section Kronecker

open Complex ModularFormsKB.Historical.Kronecker
open scoped Real

/-- **Kronecker's transformation law for `Ser_ρ`** (Kronecker, Werke 5, I, art. XXI, § 7, (E)), for `ρ ≥ 2`, where
the series converges absolutely. For integers `α, α', β, β', γ, γ', γ₀, γ₀'` with `αβ' - α'β = 1`, `v/w ∉ ℝ`, none of
`σ₀, τ₀, σ₀' = ασ₀ + βτ₀ + γ₀, τ₀' = α'σ₀ + β'τ₀ + γ₀'` an integer and `u = σv + τw` off the lattice:
`Ser_ρ(u₀, u, v, w) = e^{((αγ' - α'γ)σ₀ + (βγ' - β'γ)τ₀)2πi} Ser_ρ(u₀', u', v', w')` with `v' = β'v - α'w`,
`w' = -βv + αw` and `u' = (ασ + βτ + γ)v' + (α'σ + β'τ + γ')w'`. (In this range the law is a rearrangement of an
absolutely convergent series; the cases `ρ = 0, 1` are not proved.) -/
theorem kronecker_ser_transformation {ρ : ℕ} (hρ : 2 ≤ ρ) :
    ∀ (σ₀ τ₀ σ τ : ℝ) (v w : ℂ) (α α' β β' γ γ' γ₀ γ₀' : ℤ),
      (v / w).im ≠ 0 → α * β' - α' * β = 1 →
      (∀ k : ℤ, σ₀ ≠ k ∧ τ₀ ≠ k ∧ α * σ₀ + β * τ₀ + γ₀ ≠ k ∧ α' * σ₀ + β' * τ₀ + γ₀' ≠ k) →
      (∀ m n : ℤ, (σ * v + τ * w) + m * v + n * w ≠ 0) →
      ser ρ σ₀ τ₀ (σ * v + τ * w) v w =
        cexp (((α * γ' - α' * γ : ℤ) * σ₀ + (β * γ' - β' * γ : ℤ) * τ₀ : ℝ) * (2 * π * I)) *
          ser ρ (α * σ₀ + β * τ₀ + γ₀) (α' * σ₀ + β' * τ₀ + γ₀')
            ((α * σ + β * τ + γ : ℝ) * (β' * v - α' * w) + (α' * σ + β' * τ + γ' : ℝ) * (-β * v + α * w))
            (β' * v - α' * w) (-β * v + α * w) := by
  exact ModularFormsKB.Historical.Kronecker.ser_transformation_of_two_le hρ

end Kronecker

end ModularFormsKB.Headlines
