import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import ModularFormsKB.Citation
/-!
# Kronecker's analytic invariant `A` of an arithmetic equivalence

Kronecker, *Zur Theorie der elliptischen Functionen* (Werke 4, ed. Hensel, 1929, XXXI).

* § I, p. 347: `ϑ(ζ, ω) = ∑_{ν odd} e^{(ν²ω + 4νζ - 2ν)πi/4}`; p. 348: `ϑ'(0, ω) = 2π e^{ωπi/4} ∏ (1 - e^{2nωπi})³`,
  i.e. `ϑ'(0, ω) = 2π η(ω)³`.
* § I, p. 348: `A(σ, τ, w₁, w₂) = (4π²)^{1/3} e^{τ²(w₁+w₂)πi} ϑ(σ + τw₁, w₁) ϑ(σ - τw₂, w₂) / (ϑ'(0,w₁) ϑ'(0,w₂))^{1/3}`,
  the cube root fixed by Kronecker's product form (p. 348): `(2π/ϑ'(0, ω))^{1/3} = 1/η(ω)`. Hence
  `A = e^{τ²(w₁+w₂)πi} ϑ(σ + τw₁, w₁) ϑ(σ - τw₂, w₂) / (η(w₁) η(w₂))` (`kroneckerA`).
* § II, (𝔅), p. 353: for integers with `αβ' - α'β = 1`,
  `A(σ, τ, w₁, w₂) = A(ασ + α'τ + α'', βσ + β'τ + β'', (αw₁ - α')/(-βw₁ + β'), (αw₂ + α')/(βw₂ + β'))`.
  With `w₁ = (-b₀ + i)/(2c₀)`, `w₂ = (b₀ + i)/(2c₀)`, `4a₀c₀ - b₀² = 1`, the value depends only on the
  equivalence class of the system `(σ, τ, a₀, b₀, c₀)` (pp. 353–354): Kronecker's *analytic invariant of an
  arithmetic equivalence*.
* § V, pp. 361–362: correspondingly, the lattice sums `∑' e^{2(mσ+nτ)πi} f(m, n)^{-1-ρ}`, `ρ > 0`, of
  equivalent systems agree term by term.

## What is formalized

* `latticeSum_equiv`: the invariance of the lattice sums under arithmetic equivalence (§ V). **Proved.**
* `KroneckerAInvariance`: relation (𝔅) for `A`, and `KroneckerAFormInvariance`, its form version, as
  named propositions. Kronecker derives (𝔅) from the elementary substitutions (𝔅') and (𝔅'') (the
  transformations of `ϑ` under `ω ↦ ω + 1` and `ω ↦ -1/ω`) and the generation of `SL₂(ℤ)` by them; not yet
  formalized (loose end). A numerical check of (𝔅) with the `η` branch above, for complex `σ` and four
  substitutions including both generators, agrees to `4·10⁻¹⁵`.
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Kronecker

/-- Kronecker's odd theta function `ϑ(ζ, ω) = ∑_{ν odd} e^{(ν²ω + 4νζ - 2ν)πi/4}` (Werke 4, XXXI, § I,
p. 347), summed as `ν = 2n + 1`, `n ∈ ℤ`. -/
@[kb "kronecker1929" "XXXI, § I, p. 347"]
def kroneckerTheta (ζ ω : ℂ) : ℂ :=
  ∑' n : ℤ, cexp ((((2 * n + 1 : ℤ) : ℂ) ^ 2 * ω + 4 * ((2 * n + 1 : ℤ) : ℂ) * ζ -
    2 * ((2 * n + 1 : ℤ) : ℂ)) * π * I / 4)

/-- **Kronecker's function `A`** (Werke 4, XXXI, § I, p. 348), with the cube root
`(2π / ϑ'(0, ω))^{1/3} = 1/η(ω)` of Kronecker's product form:
`A(σ, τ, w₁, w₂) = e^{τ²(w₁+w₂)πi} ϑ(σ + τw₁, w₁) ϑ(σ - τw₂, w₂) / (η(w₁) η(w₂))`. -/
@[kb "kronecker1929" "XXXI, § I, p. 348"]
def kroneckerA (σ τ w₁ w₂ : ℂ) : ℂ :=
  cexp (τ ^ 2 * (w₁ + w₂) * π * I) * kroneckerTheta (σ + τ * w₁) w₁ * kroneckerTheta (σ - τ * w₂) w₂ /
    (ModularForm.eta w₁ * ModularForm.eta w₂)

/-- **Kronecker's relation (𝔅)** (Werke 4, XXXI, § II, p. 353), as a proposition: for `w₁, w₂` in the upper
half-plane and integers with `αβ' - α'β = 1`, `A(σ, τ, w₁, w₂) =
A(ασ + α'τ + α'', βσ + β'τ + β'', (αw₁ - α')/(-βw₁ + β'), (αw₂ + α')/(βw₂ + β'))`. -/
def KroneckerAInvariance : Prop :=
  ∀ (σ τ w₁ w₂ : ℂ) (α α' α'' β β' β'' : ℤ), 0 < w₁.im → 0 < w₂.im → α * β' - α' * β = 1 →
    kroneckerA σ τ w₁ w₂ =
      kroneckerA (α * σ + α' * τ + α'') (β * σ + β' * τ + β'')
        ((α * w₁ - α') / (-β * w₁ + β')) ((α * w₂ + α') / (β * w₂ + β'))

/-- The form `a₀x² + b₀xy + c₀y²` after the substitution `x = αx' + βy'`, `y = α'x' + β'y'`. -/
def substForm (a₀ b₀ c₀ : ℝ) (α α' β β' : ℤ) : ℝ × ℝ × ℝ :=
  (a₀ * α ^ 2 + b₀ * α * α' + c₀ * α' ^ 2,
   2 * a₀ * α * β + b₀ * (α * β' + α' * β) + 2 * c₀ * α' * β',
   a₀ * β ^ 2 + b₀ * β * β' + c₀ * β' ^ 2)

/-- **The analytic invariant** (Werke 4, XXXI, § II, pp. 353–354), as a proposition: for a real form with
`a₀, c₀ > 0` and `4a₀c₀ - b₀² = 1`, `A(σ, τ, (-b₀ + i)/(2c₀), (b₀ + i)/(2c₀))` takes the same value on the
equivalent system `(σ', τ', a₀', b₀', c₀')`, `σ' = ασ + α'τ + α''`, `τ' = βσ + β'τ + β''`, `(a₀', b₀', c₀')`
obtained by `x = αx' + βy'`, `y = α'x' + β'y'`, `αβ' - α'β = 1`. -/
def KroneckerAFormInvariance : Prop :=
  ∀ (σ τ : ℂ) (a₀ b₀ c₀ : ℝ) (α α' α'' β β' β'' : ℤ), 0 < a₀ → 0 < c₀ → 4 * a₀ * c₀ - b₀ ^ 2 = 1 →
    α * β' - α' * β = 1 →
    let f' := substForm a₀ b₀ c₀ α α' β β'
    kroneckerA σ τ ((-b₀ + I) / (2 * c₀)) ((b₀ + I) / (2 * c₀)) =
      kroneckerA (α * σ + α' * τ + α'') (β * σ + β' * τ + β'')
        ((-f'.2.1 + I) / (2 * f'.2.2)) ((f'.2.1 + I) / (2 * f'.2.2))

/-- Kronecker's lattice sum `∑'_{(m,n) ≠ 0} e^{2(mσ + nτ)πi} (a₀m² + b₀mn + c₀n²)^{-1-ρ}`
(Werke 4, XXXI, § IV, (T₀), p. 360; the origin is omitted). -/
@[kb "kronecker1929" "XXXI, § IV, (T₀), p. 360"]
def latticeSum (σ τ : ℝ) (a₀ b₀ c₀ ρ : ℝ) : ℂ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else
    cexp ((p.1 * σ + p.2 * τ : ℝ) * (2 * π * I)) *
      ((a₀ * p.1 ^ 2 + b₀ * p.1 * p.2 + c₀ * p.2 ^ 2) ^ (-1 - ρ) : ℝ)

/-- **Invariance of the lattice sums under arithmetic equivalence** (Kronecker, Werke 4, XXXI, § V,
pp. 361–362): under `m = αm' + βn'`, `n = α'm' + β'n'`, `αβ' - α'β = 1`, the form
`f` goes to the equivalent form `f'` and `(σ, τ)` to `(ασ + α'τ + α'', βσ + β'τ + β'')`, and the sums agree.
(No convergence hypothesis is needed: the identity is a reindexing; Kronecker's `ρ > 0` and positive
definiteness make both sides absolutely convergent.) -/
@[kb "kronecker1929" "XXXI, § V, pp. 361–362"]
theorem latticeSum_equiv (σ τ a₀ b₀ c₀ ρ : ℝ) (α α' α'' β β' β'' : ℤ) (hdet : α * β' - α' * β = 1) :
    let f' := substForm a₀ b₀ c₀ α α' β β'
    latticeSum σ τ a₀ b₀ c₀ ρ =
      latticeSum (α * σ + α' * τ + α'') (β * σ + β' * τ + β'') f'.1 f'.2.1 f'.2.2 ρ := by
  intro f'
  -- the substitution `(m', n') ↦ (αm' + βn', α'm' + β'n')` as a permutation of `ℤ × ℤ`
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p ↦ (α * p.1 + β * p.2, α' * p.1 + β' * p.2)
      invFun := fun p ↦ (β' * p.1 - β * p.2, -α' * p.1 + α * p.2)
      left_inv := fun p ↦ by
        ext
        · simp only; linear_combination (p.1 : ℤ) * hdet
        · simp only; linear_combination (p.2 : ℤ) * hdet
      right_inv := fun p ↦ by
        ext
        · simp only; linear_combination (p.1 : ℤ) * hdet
        · simp only; linear_combination (p.2 : ℤ) * hdet }
  unfold latticeSum
  rw [← e.tsum_eq]
  refine tsum_congr fun p ↦ ?_
  have he0 : e p = 0 ↔ p = 0 := by
    constructor
    · intro h
      have := congrArg e.symm h
      rw [Equiv.symm_apply_apply] at this
      rw [this]; simp [e]
    · rintro rfl; simp [e]
  by_cases hp : p = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (he0.mpr hp)), ite_eq_left_of_eq_true _ _ (eq_true hp)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h ↦ hp (he0.mp h))), ite_eq_right_of_eq_false _ _ (eq_false hp)]
    congr 1
    · -- the characters agree: the exponents differ by the integer `α'' m' + β'' n'`
      have hk : ((((α * p.1 + β * p.2 : ℤ) : ℝ) * σ + ((α' * p.1 + β' * p.2 : ℤ) : ℝ) * τ : ℝ) : ℂ) *
          (2 * π * I) =
          ((((p.1 : ℝ) * (α * σ + α' * τ + α'') + (p.2 : ℝ) * (β * σ + β' * τ + β'') : ℝ) : ℂ) *
            (2 * π * I)) - ((α'' * p.1 + β'' * p.2 : ℤ) : ℂ) * (2 * π * I) := by
        push_cast; ring
      simp only [e, Equiv.coe_fn_mk]
      rw [hk, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
    · simp only [e, Equiv.coe_fn_mk, f', substForm]
      congr 2
      push_cast
      ring

end ModularFormsKB.Historical.Kronecker
