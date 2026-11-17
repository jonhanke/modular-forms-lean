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
# Headline statements of modular-forms-lean 0.5.1: historical theorems of Jacobi, Ramanujan, Weber and Kronecker, proved

A topic, not a book: theorems read in the original papers (Jacobi, *Fundamenta nova*, 1829; Ramanujan, *On certain
arithmetical functions*, 1916, *Some properties of p(n)*, 1919, *Congruence properties of partitions*, and
Question 387, 1912: papers 18, 25 and 28 and a question of his *Collected Papers*, 1927; Weber, *Elliptische Functionen
und algebraische Zahlen*, 1891; Kronecker, *Zur Theorie der elliptischen Functionen*, Werke 5). New in 0.5.0:
`jacobi_cube`, `ramanujan_partition_congruences`, `ramanujan_tau_congruences`, `ramanujan_question387`,
`jacobi_quartic_weber_eighth_powers` and `kronecker_theta_E2`. New in 0.5.1: `jacobi_theta_constants`.

The statements of `Challenge_Historical.lean`, each proved by appeal to the library theorem. `lake comparator`
(configured by `comparator/Historical.json`) checks that each statement here is exactly the one in
`Challenge_Historical.lean` and that its proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

Each statement is the library's statement, copied, except that a named statement in the conclusion is unfolded. The
statements were not yet reviewed by a human (see the README). These libraries import Mathlib, a few Tau Ceti modules
and a few other modules of this library.

All theorems are unconditional. (In 0.3.1 `weber_theta_eta` assumed the Jacobi triple product identity as a named
input; the identity is now proved, `jacobi_triple_product`, and the hypothesis is gone.)

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
* (0.5.0) `ModularFormsKB.Historical.Ramanujan.partitionCount` (`p(n)`, the cardinality of Mathlib's
  `Nat.Partition n`), `ModularFormsKB.Historical.Ramanujan.tau` (the coefficient of `xⁿ` in the formal power series
  `x ∏_{n ≥ 1} (1 - xⁿ)²⁴` over `ℤ`), `ModularFormsKB.Historical.Kronecker.kroneckerTheta` (Kronecker's odd theta
  function `ϑ(ζ, w) = ∑_{n ∈ ℤ} e^{((2n+1)² w + 4(2n+1)ζ - 2(2n+1)) πi/4}`)
* (0.5.1) `ModularFormsKB.Historical.Jacobi.thetaNull3`, `.thetaNull2`, `.thetaNull4` (the theta constants
  `ϑ₃(y) = ∑_{n ∈ ℤ} e^{-πn²y}`, `ϑ₂(y) = ∑_{n ∈ ℤ} e^{-π(n + 1/2)²y}`, `ϑ₄(y) = ∑_{n ∈ ℤ} (-1)ⁿ e^{-πn²y}`, real
  functions of `y > 0`, the nome being `q = e^{-πy}`), `ModularFormsKB.Historical.Jacobi.jacobiModulusOf`
  (`y ↦ ϑ₂(y)²/ϑ₃(y)²`), `ModularFormsKB.Historical.Jacobi.legendreK'` (`K'(k) = K(√(1 - k²))`), and Tau Ceti's
  `TauCeti.Real.legendreK` (the complete elliptic integral `K(k) = ∫₀^{π/2} (1 - k² sin² φ)^{-1/2} dφ`)
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

/-- **Jacobi's triple product identity** (Jacobi, *Fundamenta nova*, § 64), in Jacobi's variables: for `|q| < 1`
and `z ≠ 0`, `∑_{n ∈ ℤ} q^{n²} zⁿ = ∏_{n ≥ 1} (1 - q^{2n})(1 + q^{2n-1} z)(1 + q^{2n-1}/z)` (the product indexed
from `0`). Neither Mathlib nor Tau Ceti proves it. -/
theorem jacobi_triple_product {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    HasSum (fun n : ℤ ↦ q ^ (n.natAbs ^ 2) * z ^ n)
      (∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1) * z) * (1 + q ^ (2 * n + 1) / z)) := by
  exact ModularFormsKB.Historical.Jacobi.triple_product hq hz

/-- **Jacobi's identity for the cube of Euler's product** (Jacobi, *Fundamenta nova*, § 66, 5); new in 0.5.0): for
`|q| < 1`, `∏_{n ≥ 1} (1 - qⁿ)³ = ∑_{n ≥ 0} (-1)ⁿ (2n + 1) q^{n(n+1)/2}` (the product indexed from `0`). The
library derives it from the triple product identity. -/
theorem jacobi_cube {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ n * (2 * n + 1) * q ^ (n * (n + 1) / 2))
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ 3) := by
  exact ModularFormsKB.Historical.Jacobi.jacobi_cube hq

/-- **Jacobi's theta constants through the complete integral** (Jacobi, *Fundamenta nova*, § 63, p. 180 and § 65,
p. 184; new in 0.5.1): for a modulus `0 < k < 1`, at the nome `q = e^{-πK'/K}` (that is `y = K'/K`),
`ϑ₃ = √(2K/π)`, `ϑ₂ = √(2kK/π)` and `ϑ₄ = √(2k'K/π)` with `k' = √(1 - k²)`, and `k = ϑ₂²/ϑ₃²`. The library proves it
by Gauss's route: Weber's duplication formulas make `(ϑ₃(q^{2ⁿ})², ϑ₄(q^{2ⁿ})²)` the arithmetic–geometric sequence
of `(ϑ₃², ϑ₄²)`, Tau Ceti's theorem of Gauss gives `K = πϑ₃²/2`, and the theta transformation formula gives
`K'/K = y`. -/
theorem jacobi_theta_constants {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    jacobiModulusOf (legendreK' k / TauCeti.Real.legendreK k) = k ∧
      thetaNull3 (legendreK' k / TauCeti.Real.legendreK k) = √(2 * TauCeti.Real.legendreK k / π) ∧
      thetaNull2 (legendreK' k / TauCeti.Real.legendreK k) = √(2 * k * TauCeti.Real.legendreK k / π) ∧
      thetaNull4 (legendreK' k / TauCeti.Real.legendreK k) =
        √(2 * √(1 - k ^ 2) * TauCeti.Real.legendreK k / π) := by
  exact ModularFormsKB.Historical.Jacobi.jacobiThetaConstantsOfModulus hk0 hk1

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

/-- **Ramanujan's partition congruences** (Ramanujan, *Some properties of p(n), the number of partitions of n*,
1919, paper 25 of his *Collected Papers*, (1)–(3), proofs §§ 2–3; new in 0.5.0): `p(5m + 4) ≡ 0 (mod 5)`,
`p(7m + 5) ≡ 0 (mod 7)` and `p(35m + 19) ≡ 0 (mod 35)`, for `p(n)` the number of partitions of `n`. The library
follows Ramanujan's proofs, from Jacobi's cube identity. -/
theorem ramanujan_partition_congruences :
    (∀ m : ℕ, 5 ∣ partitionCount (5 * m + 4)) ∧ (∀ m : ℕ, 7 ∣ partitionCount (7 * m + 5)) ∧
      ∀ m : ℕ, 35 ∣ partitionCount (35 * m + 19) := by
  exact ⟨ModularFormsKB.Historical.Ramanujan.ramanujanModFive, ModularFormsKB.Historical.Ramanujan.ramanujanModSeven, ModularFormsKB.Historical.Ramanujan.ramanujanModThirtyFive⟩

/-- **Ramanujan's congruences for `τ(n)` modulo 5 and 7** (Ramanujan, *Congruence properties of partitions*, paper 28
of his *Collected Papers*, p. 230; new in 0.5.0): `τ(5n) ≡ 0 (mod 5)`, and `τ(n) ≡ 0 (mod 7)` for
`n ≡ 0, 3, 5, 6 (mod 7)`, where `Σ τ(n) xⁿ = x ∏_{n ≥ 1} (1 - xⁿ)²⁴` as formal power series. -/
theorem ramanujan_tau_congruences :
    (∀ n : ℕ, (5 : ℤ) ∣ tau (5 * n)) ∧
      ∀ n : ℕ, n % 7 = 0 ∨ n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6 → (7 : ℤ) ∣ tau n := by
  exact ⟨ModularFormsKB.Historical.Ramanujan.tauModFive, ModularFormsKB.Historical.Ramanujan.tauModSeven⟩

open scoped Real in
/-- **Ramanujan's Question 387** (J. Indian Math. Soc. 4 (1912), p. 120; *Collected Papers*, p. 326; new in 0.5.0):
`∑_{n ≥ 1} n / (e^{2πn} - 1) = 1/24 - 1/(8π)` (the sum indexed from `0`), equivalently `E₂(i) = 3/π`. -/
theorem ramanujan_question387 :
    HasSum (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) / (Real.exp (2 * π * (n + 1 : ℕ)) - 1)) (1 / 24 - 1 / (8 * π)) := by
  exact ModularFormsKB.Historical.Ramanujan.question387

end Ramanujan

section Weber

open Complex ModularFormsKB.Historical.Weber ModularFormsKB.WeberHeegnerStark
open scoped Real

/-- **Weber's theta functions as products of `η` and his functions `f`** (Weber 1891, § 21, (9)): for `Im ω > 0`,
`ϑ₀₀(ω) = η(ω) f(ω)²`, `ϑ₀₁(ω) = η(ω) f₁(ω)²` and `ϑ₁₀(ω) = η(ω) f₂(ω)²`. Unconditional since 0.4.0: in 0.3.1 it
assumed the Jacobi triple product identity as a named input, which the library now proves
(`jacobi_triple_product` above). -/
theorem weber_theta_eta {ω : ℂ} (hω : 0 < ω.im) :
    weberTheta00 ω = ModularForm.eta ω * weberF ω ^ 2 ∧
      weberTheta01 ω = ModularForm.eta ω * weberF₁ ω ^ 2 ∧
      weberTheta10 ω = ModularForm.eta ω * weberF₂ ω ^ 2 := by
  exact ⟨ModularFormsKB.Historical.Weber.weberTheta00_eq hω, ModularFormsKB.Historical.Weber.weberTheta01_eq hω, ModularFormsKB.Historical.Weber.weberTheta10_eq hω⟩

/-- **Jacobi's quartic identity and Weber's `f⁸ = f₁⁸ + f₂⁸`** (Jacobi, *Fundamenta nova*, § 36; Weber 1891, § 34;
new in 0.5.0): for `Im ω > 0`, `ϑ₀₀(ω)⁴ = ϑ₀₁(ω)⁴ + ϑ₁₀(ω)⁴`, and `f(ω)⁸ = f₁(ω)⁸ + f₂(ω)⁸`. The library proves the
duplication formulas of the theta constants and derives both. -/
theorem jacobi_quartic_weber_eighth_powers :
    (∀ ω : ℂ, 0 < ω.im → weberTheta00 ω ^ 4 = weberTheta01 ω ^ 4 + weberTheta10 ω ^ 4) ∧
      ∀ ω : ℂ, 0 < ω.im → weberF ω ^ 8 = weberF₁ ω ^ 8 + weberF₂ ω ^ 8 := by
  exact ⟨ModularFormsKB.Historical.Weber.jacobiQuartic, ModularFormsKB.Historical.Weber.weberEighthPowers⟩

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

open scoped UpperHalfPlane in
/-- **Kronecker's `ϑ'''(0, w) = -π² E₂(w) ϑ'(0, w)`** (Kronecker, Werke 5, II, art. IV, pp. 146–147; new in 0.5.0),
for his odd theta function `ϑ(ζ, w) = ∑_{ν odd} e^{(ν² w + 4νζ - 2ν) πi/4}`, derivatives in `ζ`, with Mathlib's
weight-2 Eisenstein series `E₂`. -/
theorem kronecker_theta_E2 :
    ∀ w : ℍ, iteratedDeriv 3 (fun ζ ↦ kroneckerTheta ζ w) 0 =
      -(π : ℂ) ^ 2 * EisensteinSeries.E2 w * deriv (fun ζ ↦ kroneckerTheta ζ w) 0 := by
  exact ModularFormsKB.Historical.Kronecker.kroneckerThetaE2

end Kronecker

end ModularFormsKB.Headlines
