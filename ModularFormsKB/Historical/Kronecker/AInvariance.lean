import ModularFormsKB.Historical.Kronecker.AnalyticInvariant
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import ModularFormsKB.Citation
/-!
# Kronecker's relation (𝔅) for the function `A`

Kronecker, *Zur Theorie der elliptischen Functionen* (Werke 4, ed. Hensel, 1929, XXXI, § II, (𝔅), pp. 352–354).
We prove `KroneckerAInvariance` and `KroneckerAFormInvariance`.

Plan (Kronecker's): the transformation laws of `ϑ(ζ, ω)` (shifts of `ζ` by `1` and `ω`, oddness, `ω ↦ ω + 1`,
and the inversion `ω ↦ -1/ω`) together with those of `η` give the invariance of `A` under the shifts
`σ ↦ σ + 1`, `τ ↦ τ + 1` and under the generators `S`, `T` of `SL₂(ℤ)`; the general substitution follows from
the generation of `SL₂(ℤ)` by `S` and `T` (Mathlib `SpecialLinearGroup.SL2Z_generators`).
The inversion law is derived from Mathlib's `jacobiTheta₂_functional_equation` via
`ϑ(ζ, ω) = e^{πi(ω/4 + ζ - 1/2)} jacobiTheta₂ (ζ + ω/2 - 1/2) ω`.
-/

noncomputable section

open Complex
open scoped Real MatrixGroups

namespace ModularFormsKB.Historical.Kronecker

/-! ### Transformation laws of `ϑ` -/

/-- `ϑ(ζ, ω) = e^{πi(ω/4 + ζ - 1/2)} · jacobiTheta₂ (ζ + ω/2 - 1/2) ω`, termwise. -/
lemma kroneckerTheta_eq_jacobi (ζ ω : ℂ) :
    kroneckerTheta ζ ω = cexp (π * I * (ω / 4 + ζ - 1 / 2)) * jacobiTheta₂ (ζ + ω / 2 - 1 / 2) ω := by
  unfold kroneckerTheta jacobiTheta₂
  rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma kroneckerTheta_add_one (ζ ω : ℂ) : kroneckerTheta (ζ + 1) ω = -kroneckerTheta ζ ω := by
  unfold kroneckerTheta
  rw [← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  have h : cexp (π * I + n * (2 * π * I)) = -1 := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I]; ring
  have h2 : cexp ((((2 * n + 1 : ℤ) : ℂ) ^ 2 * ω + 4 * ((2 * n + 1 : ℤ) : ℂ) * (ζ + 1) -
      2 * ((2 * n + 1 : ℤ) : ℂ)) * π * I / 4) =
      cexp ((((2 * n + 1 : ℤ) : ℂ) ^ 2 * ω + 4 * ((2 * n + 1 : ℤ) : ℂ) * ζ -
      2 * ((2 * n + 1 : ℤ) : ℂ)) * π * I / 4) * cexp (π * I + n * (2 * π * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h2, h]; ring

lemma kroneckerTheta_add_period (ζ ω : ℂ) :
    kroneckerTheta (ζ + ω) ω = -cexp (-(π * I * (ω + 2 * ζ))) * kroneckerTheta ζ ω := by
  unfold kroneckerTheta
  rw [← tsum_mul_left]
  conv_rhs => rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  have : -cexp (-(π * I * (ω + 2 * ζ))) * cexp ((((2 * ((Equiv.addRight (1 : ℤ)) n) + 1 : ℤ) : ℂ) ^ 2 * ω +
      4 * (((2 * ((Equiv.addRight (1 : ℤ)) n) + 1 : ℤ) : ℂ)) * ζ -
      2 * (((2 * ((Equiv.addRight (1 : ℤ)) n) + 1 : ℤ) : ℂ))) * π * I / 4) =
      cexp (π * I + (-(π * I * (ω + 2 * ζ))) + ((((2 * ((Equiv.addRight (1 : ℤ)) n) + 1 : ℤ) : ℂ) ^ 2 * ω +
      4 * (((2 * ((Equiv.addRight (1 : ℤ)) n) + 1 : ℤ) : ℂ)) * ζ -
      2 * (((2 * ((Equiv.addRight (1 : ℤ)) n) + 1 : ℤ) : ℂ))) * π * I / 4)) := by
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  rw [this]
  congr 1
  simp only [Equiv.coe_addRight]
  push_cast
  ring

lemma kroneckerTheta_sub_period (ζ ω : ℂ) :
    kroneckerTheta (ζ - ω) ω = -cexp (π * I * (2 * ζ - ω)) * kroneckerTheta ζ ω := by
  unfold kroneckerTheta
  rw [← tsum_mul_left]
  conv_rhs => rw [← (Equiv.subRight (1 : ℤ)).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  have : -cexp (π * I * (2 * ζ - ω)) * cexp ((((2 * ((Equiv.subRight (1 : ℤ)) n) + 1 : ℤ) : ℂ) ^ 2 * ω +
      4 * (((2 * ((Equiv.subRight (1 : ℤ)) n) + 1 : ℤ) : ℂ)) * ζ -
      2 * (((2 * ((Equiv.subRight (1 : ℤ)) n) + 1 : ℤ) : ℂ))) * π * I / 4) =
      cexp (-(π * I) + (π * I * (2 * ζ - ω)) + ((((2 * ((Equiv.subRight (1 : ℤ)) n) + 1 : ℤ) : ℂ) ^ 2 * ω +
      4 * (((2 * ((Equiv.subRight (1 : ℤ)) n) + 1 : ℤ) : ℂ)) * ζ -
      2 * (((2 * ((Equiv.subRight (1 : ℤ)) n) + 1 : ℤ) : ℂ))) * π * I / 4)) := by
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]; ring
  rw [this]
  congr 1
  simp only [Equiv.subRight_apply]
  push_cast
  ring

lemma kroneckerTheta_neg (ζ ω : ℂ) : kroneckerTheta (-ζ) ω = -kroneckerTheta ζ ω := by
  unfold kroneckerTheta
  rw [← tsum_neg]
  conv_rhs => rw [← ((Equiv.neg ℤ).trans (Equiv.subRight (1 : ℤ))).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  have h : cexp (-(π * I + n * (2 * π * I))) = -1 := by
    rw [Complex.exp_neg, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I]; ring
  have h2 : cexp ((((2 * n + 1 : ℤ) : ℂ) ^ 2 * ω + 4 * ((2 * n + 1 : ℤ) : ℂ) * (-ζ) -
      2 * ((2 * n + 1 : ℤ) : ℂ)) * π * I / 4) =
      cexp ((((2 * (((Equiv.neg ℤ).trans (Equiv.subRight (1 : ℤ))) n) + 1 : ℤ) : ℂ) ^ 2 * ω +
        4 * ((2 * (((Equiv.neg ℤ).trans (Equiv.subRight (1 : ℤ))) n) + 1 : ℤ) : ℂ) * ζ -
      2 * ((2 * (((Equiv.neg ℤ).trans (Equiv.subRight (1 : ℤ))) n) + 1 : ℤ) : ℂ)) * π * I / 4) *
      cexp (-(π * I + n * (2 * π * I))) := by
    rw [← Complex.exp_add]; congr 1
    simp only [Equiv.trans_apply, Equiv.neg_apply, Equiv.subRight_apply]
    push_cast; ring
  rw [h2, h]; ring

lemma kroneckerTheta_add_one_right (ζ ω : ℂ) :
    kroneckerTheta ζ (ω + 1) = cexp (π * I / 4) * kroneckerTheta ζ ω := by
  unfold kroneckerTheta
  rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  obtain ⟨m, hm⟩ := Int.even_mul_succ_self n
  have hm' : ((n : ℂ) * (n + 1)) = m + m := by exact_mod_cast hm
  rw [← Complex.exp_add]
  calc _ = cexp ((π * I / 4 + (((2 * n + 1 : ℤ) : ℂ) ^ 2 * ω + 4 * ((2 * n + 1 : ℤ) : ℂ) * ζ -
        2 * ((2 * n + 1 : ℤ) : ℂ)) * π * I / 4) + m * (2 * π * I)) := by
        congr 1; push_cast; linear_combination (π * I) * hm'
    _ = _ := by rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Inversion law for `ϑ`: `ϑ(ζ/ω, -1/ω) = -i (-iω)^{1/2} e^{πiζ²/ω} ϑ(ζ, ω)`, from Mathlib's functional
equation of `jacobiTheta₂`. -/
lemma kroneckerTheta_inv (ζ ω : ℂ) (hω : ω ≠ 0) :
    kroneckerTheta (ζ / ω) (-1 / ω) =
      -I * (-I * ω) ^ (1 / 2 : ℂ) * cexp (π * I * ζ ^ 2 / ω) * kroneckerTheta ζ ω := by
  rw [kroneckerTheta_eq_jacobi ζ ω, kroneckerTheta_eq_jacobi (ζ / ω) (-1 / ω)]
  have hper : jacobiTheta₂ (ζ / ω + -1 / ω / 2 - 1 / 2) (-1 / ω) =
      jacobiTheta₂ ((ζ + ω / 2 - 1 / 2) / ω) (-1 / ω) := by
    have : ζ / ω + -1 / ω / 2 - 1 / 2 = (ζ + ω / 2 - 1 / 2) / ω - 1 := by
      field_simp; ring
    rw [this, ← jacobiTheta₂_add_left ((ζ + ω / 2 - 1 / 2) / ω - 1) (-1 / ω)]
    congr 1; ring
  have hfe := jacobiTheta₂_functional_equation (ζ + ω / 2 - 1 / 2) ω
  have hX : (-I * ω) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [hω]
  have hfe' : jacobiTheta₂ ((ζ + ω / 2 - 1 / 2) / ω) (-1 / ω) =
      (-I * ω) ^ (1 / 2 : ℂ) * cexp (π * I * (ζ + ω / 2 - 1 / 2) ^ 2 / ω) *
        jacobiTheta₂ (ζ + ω / 2 - 1 / 2) ω := by
    have h1 : cexp (-π * I * (ζ + ω / 2 - 1 / 2) ^ 2 / ω) * cexp (π * I * (ζ + ω / 2 - 1 / 2) ^ 2 / ω) = 1 := by
      rw [← Complex.exp_add]; convert Complex.exp_zero using 2; ring
    rw [hfe]
    calc _ = ((-I * ω) ^ (1 / 2 : ℂ) * (1 / (-I * ω) ^ (1 / 2 : ℂ))) *
          ((cexp (-π * I * (ζ + ω / 2 - 1 / 2) ^ 2 / ω) * cexp (π * I * (ζ + ω / 2 - 1 / 2) ^ 2 / ω)) *
          jacobiTheta₂ ((ζ + ω / 2 - 1 / 2) / ω) (-1 / ω)) := by
          rw [mul_one_div_cancel hX, h1]; ring
      _ = _ := by ring
  have hm : cexp (π * I * (-1 / 2)) = -I := by
    rw [show π * I * (-1 / 2 : ℂ) = -(π / 2 * I) by ring, Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
    simp
  rw [hper, hfe']
  have hc : cexp (π * I * (-1 / ω / 4 + ζ / ω - 1 / 2)) * cexp (π * I * (ζ + ω / 2 - 1 / 2) ^ 2 / ω) =
      -I * cexp (π * I * ζ ^ 2 / ω) * cexp (π * I * (ω / 4 + ζ - 1 / 2)) := by
    rw [← hm, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp
    ring
  linear_combination ((-I * ω) ^ (1 / 2 : ℂ) * jacobiTheta₂ (ζ + ω / 2 - 1 / 2) ω) * hc

/-! ### Transformation laws of `η` -/

lemma eta_eq_cexp' (z : ℂ) :
    ModularForm.eta z = cexp (2 * π * I * z / 24) * ∏' n : ℕ, (1 - cexp (2 * π * I * z) ^ (n + 1)) := by
  have h : ∏' n : ℕ, (1 - ModularForm.eta_q n z) = ∏' n : ℕ, (1 - cexp (2 * π * I * z) ^ (n + 1)) :=
    tprod_congr fun n ↦ by rw [ModularForm.eta_q_eq_pow]
  unfold ModularForm.eta
  rw [h]
  simp [Function.Periodic.qParam]

lemma eta_add_one (w : ℂ) : ModularForm.eta (w + 1) = cexp (2 * π * I / 24) * ModularForm.eta w := by
  rw [eta_eq_cexp', eta_eq_cexp' w]
  have h : cexp (2 * π * I * (w + 1)) = cexp (2 * π * I * w) := by
    rw [mul_add, Complex.exp_add, mul_one, Complex.exp_two_pi_mul_I, mul_one]
  have h2 : cexp (2 * π * I * (w + 1) / 24) = cexp (2 * π * I / 24) * cexp (2 * π * I * w / 24) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [h, h2]; ring

lemma sqrt_I_mul (w : ℂ) (hw : 0 < w.im) :
    Complex.sqrt I * (-I * w) ^ (1 / 2 : ℂ) = Complex.sqrt w := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have h1 : -I * w ≠ 0 := by simp [hw0]
  have hre : 0 < (-I * w).re := by simpa using hw
  have harg : |(-I * w).arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
  have hlog : Complex.log (I * (-I * w)) = Complex.log I + Complex.log (-I * w) := by
    rw [Complex.log_mul_eq_add_log_iff I_ne_zero h1, Complex.arg_I]
    have := abs_lt.1 harg
    constructor <;> linarith [Real.pi_pos]
  have h2 : I * (-I * w) = w := by
    calc I * (-I * w) = -(I * I) * w := by ring
      _ = w := by rw [I_mul_I]; ring
  rw [h2] at hlog
  rw [_root_.sqrt_eq_exp hw0, _root_.sqrt_eq_exp I_ne_zero, Complex.cpow_def_of_ne_zero h1,
    ← Complex.exp_add, hlog]
  congr 1; ring

lemma eta_inv (w : ℂ) (hw : 0 < w.im) :
    ModularForm.eta (-1 / w) = (Complex.sqrt I)⁻¹ * (Complex.sqrt w * ModularForm.eta w) := by
  have := ModularForm.eta_comp_eq_csqrt_I_inv hw
  simpa using this

lemma theta_div_eta_inv (ζ w : ℂ) (hw : 0 < w.im) :
    kroneckerTheta (ζ / w) (-1 / w) / ModularForm.eta (-1 / w) =
      -I * cexp (π * I * ζ ^ 2 / w) * (kroneckerTheta ζ w / ModularForm.eta w) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hη := ModularForm.eta_ne_zero hw
  have hX := sqrt_I_mul w hw
  have hsI : Complex.sqrt I ≠ 0 := by
    unfold Complex.sqrt; rw [Ne, Complex.cpow_eq_zero_iff]; simp
  have hX0 : (-I * w) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp [hw0]
  rw [kroneckerTheta_inv ζ w hw0, eta_inv w hw, ← hX]
  field_simp

/-! ### The one-sided factor `F` and the elementary substitutions -/

/-- `F(σ, τ, w) = e^{τ²wπi} ϑ(σ + τw, w) / η(w)`, so that `A(σ, τ, w₁, w₂) = F(σ, τ, w₁) F(σ, -τ, w₂)`. -/
def kF (σ τ w : ℂ) : ℂ :=
  cexp (τ ^ 2 * w * π * I) * kroneckerTheta (σ + τ * w) w / ModularForm.eta w

lemma kroneckerA_eq_kF (σ τ w₁ w₂ : ℂ) :
    kroneckerA σ τ w₁ w₂ = kF σ τ w₁ * kF σ (-τ) w₂ := by
  unfold kroneckerA kF
  have : cexp (τ ^ 2 * (w₁ + w₂) * π * I) = cexp (τ ^ 2 * w₁ * π * I) * cexp (τ ^ 2 * w₂ * π * I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this, neg_sq, neg_mul, ← sub_eq_add_neg]
  ring

lemma exp_mul_exp (a b c d : ℂ) (h : a + b = c + d) : cexp a * cexp b = cexp c * cexp d := by
  rw [← Complex.exp_add, ← Complex.exp_add, h]

lemma kF_sigma_add_one (σ τ w : ℂ) : kF (σ + 1) τ w = -kF σ τ w := by
  unfold kF
  rw [show σ + 1 + τ * w = (σ + τ * w) + 1 by ring, kroneckerTheta_add_one]
  ring

lemma kF_tau_add_one (σ τ w : ℂ) : kF σ (τ + 1) w = -cexp (-(2 * π * I * σ)) * kF σ τ w := by
  unfold kF
  rw [show σ + (τ + 1) * w = (σ + τ * w) + w by ring, kroneckerTheta_add_period]
  have h := exp_mul_exp ((τ + 1) ^ 2 * w * π * I) (-(π * I * (w + 2 * (σ + τ * w))))
    (τ ^ 2 * w * π * I) (-(2 * π * I * σ)) (by ring)
  linear_combination (-(kroneckerTheta (σ + τ * w) w) / ModularForm.eta w) * h

lemma kF_tau_neg_add_one (σ τ w : ℂ) :
    kF σ (-(τ + 1)) w = -cexp (2 * π * I * σ) * kF σ (-τ) w := by
  unfold kF
  rw [show σ + -(τ + 1) * w = (σ + -τ * w) - w by ring, kroneckerTheta_sub_period]
  have h := exp_mul_exp ((-(τ + 1)) ^ 2 * w * π * I) (π * I * (2 * (σ + -τ * w) - w))
    ((-τ) ^ 2 * w * π * I) (2 * π * I * σ) (by ring)
  linear_combination (-(kroneckerTheta (σ + -τ * w) w) / ModularForm.eta w) * h

lemma kF_T_plus (σ τ w : ℂ) :
    kF (σ + τ) (-τ) (w + 1) =
      cexp (τ ^ 2 * π * I) * cexp (π * I / 4) / cexp (2 * π * I / 24) * kF σ (-τ) w := by
  unfold kF
  rw [show σ + τ + -τ * (w + 1) = σ + -τ * w by ring, kroneckerTheta_add_one_right, eta_add_one]
  have h := exp_mul_exp ((-τ) ^ 2 * (w + 1) * π * I) 0 ((-τ) ^ 2 * w * π * I) (τ ^ 2 * π * I)
    (by ring)
  simp only [Complex.exp_zero, mul_one] at h
  rw [h]
  have := Complex.exp_ne_zero (2 * π * I / 24)
  field_simp

lemma kF_T_minus (σ τ w : ℂ) :
    kF (σ + τ) τ (w - 1) =
      cexp (2 * π * I / 24) / (cexp (τ ^ 2 * π * I) * cexp (π * I / 4)) * kF σ τ w := by
  unfold kF
  have h1 : kroneckerTheta (σ + τ + τ * (w - 1)) (w - 1) =
      kroneckerTheta (σ + τ * w) w / cexp (π * I / 4) := by
    have := kroneckerTheta_add_one_right (σ + τ * w) (w - 1)
    rw [sub_add_cancel] at this
    rw [show σ + τ + τ * (w - 1) = σ + τ * w by ring, this]
    have := Complex.exp_ne_zero (π * I / 4)
    field_simp
  have h2 : ModularForm.eta (w - 1) = ModularForm.eta w / cexp (2 * π * I / 24) := by
    have := eta_add_one (w - 1)
    rw [sub_add_cancel] at this
    rw [this]
    have := Complex.exp_ne_zero (2 * π * I / 24)
    field_simp
  have h := exp_mul_exp (τ ^ 2 * (w - 1) * π * I) (τ ^ 2 * π * I) (τ ^ 2 * w * π * I) 0 (by ring)
  simp only [Complex.exp_zero, mul_one] at h
  rw [h1, h2]
  have := Complex.exp_ne_zero (2 * π * I / 24)
  have := Complex.exp_ne_zero (τ ^ 2 * π * I)
  have := Complex.exp_ne_zero (π * I / 4)
  by_cases hη : ModularForm.eta w = 0
  · simp [hη]
  · field_simp
    linear_combination (kroneckerTheta (σ + τ * w) w) * h

lemma kF_S_pos (σ τ w : ℂ) (hw : 0 < w.im) :
    kF (-τ) σ (-1 / w) = I * cexp (2 * π * I * σ * τ) * kF σ τ w := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  unfold kF
  have harg : -τ + σ * (-1 / w) = -((σ + τ * w) / w) := by field_simp; ring
  rw [harg, kroneckerTheta_neg]
  have ht := theta_div_eta_inv (σ + τ * w) w hw
  have h := exp_mul_exp (σ ^ 2 * (-1 / w) * π * I) (π * I * (σ + τ * w) ^ 2 / w)
    (2 * π * I * σ * τ) (τ ^ 2 * w * π * I) (by field_simp; ring)
  linear_combination (-cexp (σ ^ 2 * (-1 / w) * π * I)) * ht +
    (I * kroneckerTheta (σ + τ * w) w / ModularForm.eta w) * h

lemma kF_S_neg (σ τ w : ℂ) (hw : 0 < w.im) :
    kF (-τ) (-σ) (-1 / w) = -I * cexp (-(2 * π * I * σ * τ)) * kF σ (-τ) w := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  unfold kF
  have harg : -τ + -σ * (-1 / w) = (σ + -τ * w) / w := by field_simp; ring
  rw [harg]
  have ht := theta_div_eta_inv (σ + -τ * w) w hw
  have h := exp_mul_exp ((-σ) ^ 2 * (-1 / w) * π * I) (π * I * (σ + -τ * w) ^ 2 / w)
    (-(2 * π * I * σ * τ)) ((-τ) ^ 2 * w * π * I) (by field_simp; ring)
  linear_combination cexp ((-σ) ^ 2 * (-1 / w) * π * I) * ht +
    (-I * kroneckerTheta (σ + -τ * w) w / ModularForm.eta w) * h

/-- Invariance of `A` under `T`: `(σ, τ, w₁, w₂) ↦ (σ + τ, τ, w₁ - 1, w₂ + 1)`. -/
lemma kroneckerA_T (σ τ w₁ w₂ : ℂ) :
    kroneckerA (σ + τ) τ (w₁ - 1) (w₂ + 1) = kroneckerA σ τ w₁ w₂ := by
  rw [kroneckerA_eq_kF, kroneckerA_eq_kF, kF_T_minus, kF_T_plus]
  have := Complex.exp_ne_zero (2 * π * I / 24)
  have := Complex.exp_ne_zero (τ ^ 2 * π * I)
  have := Complex.exp_ne_zero (π * I / 4)
  field_simp

/-- Invariance of `A` under `S`: `(σ, τ, w₁, w₂) ↦ (-τ, σ, -1/w₁, -1/w₂)`; this is where `c² = -1` is used. -/
lemma kroneckerA_S (σ τ w₁ w₂ : ℂ) (h₁ : 0 < w₁.im) (h₂ : 0 < w₂.im) :
    kroneckerA (-τ) σ (-1 / w₁) (-1 / w₂) = kroneckerA σ τ w₁ w₂ := by
  rw [kroneckerA_eq_kF, kroneckerA_eq_kF, kF_S_pos σ τ w₁ h₁, kF_S_neg σ τ w₂ h₂]
  have h : cexp (2 * π * I * σ * τ) * cexp (-(2 * π * I * σ * τ)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (-(cexp (2 * π * I * σ * τ) * cexp (-(2 * π * I * σ * τ))) *
    (kF σ τ w₁ * kF σ (-τ) w₂)) * Complex.I_sq + (kF σ τ w₁ * kF σ (-τ) w₂) * h

lemma kroneckerA_sigma_add_one (σ τ w₁ w₂ : ℂ) :
    kroneckerA (σ + 1) τ w₁ w₂ = kroneckerA σ τ w₁ w₂ := by
  rw [kroneckerA_eq_kF, kroneckerA_eq_kF, kF_sigma_add_one, kF_sigma_add_one]; ring

lemma kroneckerA_tau_add_one (σ τ w₁ w₂ : ℂ) :
    kroneckerA σ (τ + 1) w₁ w₂ = kroneckerA σ τ w₁ w₂ := by
  rw [kroneckerA_eq_kF, kroneckerA_eq_kF, kF_tau_add_one, kF_tau_neg_add_one]
  have h : cexp (-(2 * π * I * σ)) * cexp (2 * π * I * σ) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (kF σ τ w₁ * kF σ (-τ) w₂) * h

lemma kroneckerA_sigma_int (σ τ w₁ w₂ : ℂ) (k : ℤ) :
    kroneckerA (σ + k) τ w₁ w₂ = kroneckerA σ τ w₁ w₂ := by
  have hp : Function.Periodic (fun x => kroneckerA x τ w₁ w₂) 1 :=
    fun x => kroneckerA_sigma_add_one x τ w₁ w₂
  simpa using hp.int_mul k σ

lemma kroneckerA_tau_int (σ τ w₁ w₂ : ℂ) (k : ℤ) :
    kroneckerA σ (τ + k) w₁ w₂ = kroneckerA σ τ w₁ w₂ := by
  have hp : Function.Periodic (fun x => kroneckerA σ x w₁ w₂) 1 :=
    fun x => kroneckerA_tau_add_one σ x w₁ w₂
  simpa using hp.int_mul k τ

/-! ### The action of `SL₂(ℤ)` and generation by `S`, `T` -/

lemma denom_ne_zero (c d : ℤ) (w : ℂ) (hw : 0 < w.im) (hcd : c ≠ 0 ∨ d ≠ 0) :
    (c : ℂ) * w + d ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im, add_re, mul_re,
    sub_zero, zero_re] at him hre
  have hc : (c : ℝ) = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · exact absurd h hw.ne'
  have hd : (d : ℝ) = 0 := by rw [hc] at hre; linarith
  have hc' : c = 0 := by exact_mod_cast hc
  have hd' : d = 0 := by exact_mod_cast hd
  rcases hcd with h | h
  · exact h hc'
  · exact h hd'

lemma SL_det (M : SL(2, ℤ)) : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
  have := M.det_coe
  rw [Matrix.det_fin_two] at this
  exact this

lemma SL_row_ne (M : SL(2, ℤ)) : M 1 0 ≠ 0 ∨ M 1 1 ≠ 0 := by
  by_contra h
  push Not at h
  have := SL_det M
  rw [h.1, h.2] at this
  simp at this

lemma im_mob (a b c d : ℤ) (hdet : a * d - b * c = 1) (w : ℂ) (hw : 0 < w.im) :
    0 < (((a : ℂ) * w + b) / (c * w + d)).im := by
  have hne : (c : ℂ) * w + d ≠ 0 := denom_ne_zero c d w hw (by
    by_contra h; push Not at h; rw [h.1, h.2] at hdet; simp at hdet)
  have hN : 0 < Complex.normSq ((c : ℂ) * w + d) := Complex.normSq_pos.2 hne
  rw [Complex.div_im, ← sub_div]
  apply div_pos _ hN
  have hd : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
  have : ((a : ℂ) * w + b).im * ((c : ℂ) * w + d).re - ((a : ℂ) * w + b).re * ((c : ℂ) * w + d).im =
      w.im := by
    simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, add_re, mul_re, sub_zero]
    linear_combination w.im * hd
  rw [this]; exact hw

lemma mob_comp (a b c d a' b' c' d' w : ℂ) (h : c' * w + d' ≠ 0) :
    (a * ((a' * w + b') / (c' * w + d')) + b) / (c * ((a' * w + b') / (c' * w + d')) + d) =
      ((a * a' + b * c') * w + (a * b' + b * d')) / ((c * a' + d * c') * w + (c * b' + d * d')) := by
  have e1 : a * ((a' * w + b') / (c' * w + d')) + b = (a * (a' * w + b') + b * (c' * w + d')) / (c' * w + d') := by
    rw [← mul_div_assoc, div_add' _ _ _ h]
  have e2 : c * ((a' * w + b') / (c' * w + d')) + d = (c * (a' * w + b') + d * (c' * w + d')) / (c' * w + d') := by
    rw [← mul_div_assoc, div_add' _ _ _ h]
  rw [e1, e2, div_div_div_cancel_right₀ h]
  congr 1 <;> ring

/-- The substitution `(σ, τ, w₁, w₂) ↦ (ασ + α'τ, βσ + β'τ, (αw₁ - α')/(-βw₁ + β'), (αw₂ + α')/(βw₂ + β'))`
attached to `M = [[α, α'], [β, β']]`. It is a left action: `Φ_{gh} = Φ_g ∘ Φ_h`. -/
def Phi (M : SL(2, ℤ)) (x : ℂ × ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (M 0 0 * x.1 + M 0 1 * x.2.1, M 1 0 * x.1 + M 1 1 * x.2.1,
    (M 0 0 * x.2.2.1 - M 0 1) / (-M 1 0 * x.2.2.1 + M 1 1),
    (M 0 0 * x.2.2.2 + M 0 1) / (M 1 0 * x.2.2.2 + M 1 1))

/-- The domain: both `w`'s in the upper half-plane. -/
def Dom (x : ℂ × ℂ × ℂ × ℂ) : Prop := 0 < x.2.2.1.im ∧ 0 < x.2.2.2.im

lemma Phi_dom (M : SL(2, ℤ)) (x : ℂ × ℂ × ℂ × ℂ) (hx : Dom x) : Dom (Phi M x) := by
  have hdet := SL_det M
  refine ⟨?_, ?_⟩
  · have := im_mob (M 0 0) (-M 0 1) (-M 1 0) (M 1 1) (by linarith) x.2.2.1 hx.1
    simpa [Phi, sub_eq_add_neg] using this
  · exact im_mob (M 0 0) (M 0 1) (M 1 0) (M 1 1) hdet x.2.2.2 hx.2

lemma Phi_one (x : ℂ × ℂ × ℂ × ℂ) : Phi 1 x = x := by
  simp [Phi]

lemma Phi_mul (g h : SL(2, ℤ)) (x : ℂ × ℂ × ℂ × ℂ) (hx : Dom x) :
    Phi (g * h) x = Phi g (Phi h x) := by
  obtain ⟨σ, τ, w₁, w₂⟩ := x
  have hx1 := hx.1
  have hx2 := hx.2
  simp only [Phi, Prod.mk.injEq]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨by push_cast; ring, by push_cast; ring, ?_, ?_⟩
  · have hne : (-(h 1 0 : ℂ)) * w₁ + h 1 1 ≠ 0 := by
      have := denom_ne_zero (-h 1 0) (h 1 1) w₁ hx1 (by
        rcases SL_row_ne h with h' | h'
        · left; simpa using h'
        · right; exact h')
      simpa using this
    have := mob_comp (g 0 0) (-g 0 1) (-g 1 0) (g 1 1) (h 0 0) (-h 0 1) (-h 1 0) (h 1 1) w₁ hne
    push_cast
    simp only [sub_eq_add_neg, neg_mul] at this ⊢
    rw [this]
    congr 1 <;> ring
  · have hne : (h 1 0 : ℂ) * w₂ + h 1 1 ≠ 0 := denom_ne_zero (h 1 0) (h 1 1) w₂ hx2 (SL_row_ne h)
    have := mob_comp (g 0 0) (g 0 1) (g 1 0) (g 1 1) (h 0 0) (h 0 1) (h 1 0) (h 1 1) w₂ hne
    push_cast
    rw [this]

/-- `A` evaluated on a 4-tuple. -/
def Ak (x : ℂ × ℂ × ℂ × ℂ) : ℂ := kroneckerA x.1 x.2.1 x.2.2.1 x.2.2.2

/-- `A` is invariant under `Φ_M`. -/
def AInv (M : SL(2, ℤ)) : Prop := ∀ x, Dom x → Ak x = Ak (Phi M x)

lemma AInv_mul {g h : SL(2, ℤ)} (hg : AInv g) (hh : AInv h) : AInv (g * h) := by
  intro x hx
  rw [Phi_mul g h x hx, ← hg _ (Phi_dom h x hx)]
  exact hh x hx

lemma AInv_one : AInv 1 := fun x _ => by rw [Phi_one]

lemma AInv_inv {g : SL(2, ℤ)} (hg : AInv g) : AInv g⁻¹ := by
  intro x hx
  have hy := Phi_dom g⁻¹ x hx
  have h1 := hg _ hy
  have h2 : Phi g (Phi g⁻¹ x) = x := by
    rw [← Phi_mul g g⁻¹ x hx, mul_inv_cancel, Phi_one]
  rw [h2] at h1
  exact h1.symm

lemma AInv_T : AInv ModularGroup.T := by
  rintro ⟨σ, τ, w₁, w₂⟩ _
  have e : Phi ModularGroup.T (σ, τ, w₁, w₂) = (σ + τ, τ, w₁ - 1, w₂ + 1) := by
    simp [Phi, ModularGroup.T]
  rw [e]
  exact (kroneckerA_T σ τ w₁ w₂).symm

lemma AInv_S : AInv ModularGroup.S := by
  rintro ⟨σ, τ, w₁, w₂⟩ hx
  have e : Phi ModularGroup.S (σ, τ, w₁, w₂) = (-τ, σ, -1 / w₁, -1 / w₂) := by
    simp [Phi, ModularGroup.S, neg_div]
  rw [e]
  exact (kroneckerA_S σ τ w₁ w₂ hx.1 hx.2).symm

lemma AInv_all (M : SL(2, ℤ)) : AInv M := by
  have hM : M ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hM using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact AInv_S
    · exact AInv_T
  | one => exact AInv_one
  | mul g h _ _ ihg ihh => exact AInv_mul ihg ihh
  | inv g _ ihg => exact AInv_inv ihg

/-- **Kronecker's relation (𝔅) for `A`** (Werke 4, XXXI, § II, (𝔅), pp. 352–354), from the
transformation laws of `ϑ` and `η` and the generation of `SL₂(ℤ)` by `S`, `T`. -/
@[kb "kronecker1929" "XXXI, § II, (𝔅), pp. 352–354"]
theorem kroneckerA_invariance : KroneckerAInvariance := by
  intro σ τ w₁ w₂ α α' α'' β β' β'' h₁ h₂ hdet
  let M : SL(2, ℤ) := ⟨!![α, α'; β, β'], by rw [Matrix.det_fin_two_of]; linarith⟩
  have h := AInv_all M (σ, τ, w₁, w₂) ⟨h₁, h₂⟩
  have e : Phi M (σ, τ, w₁, w₂) = (α * σ + α' * τ, β * σ + β' * τ,
      (α * w₁ - α') / (-β * w₁ + β'), (α * w₂ + α') / (β * w₂ + β')) := by
    simp [Phi, M]
  rw [e] at h
  refine h.trans ?_
  simp only [Ak]
  rw [kroneckerA_sigma_int, kroneckerA_tau_int]

/-! ### The form version -/

lemma im_form_point (b₀ c₀ : ℝ) (hc : 0 < c₀) (sgn : ℝ) :
    0 < (((sgn * b₀ : ℝ) + I : ℂ) / (2 * c₀)).im := by
  have h2 : (2 * (c₀ : ℂ)) = ((2 * c₀ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.div_ofReal_im]
  simp
  positivity

lemma form_c'_ne (a₀ b₀ c₀ c' : ℝ) (α α' β β' : ℤ) (hc₀ : 0 < c₀) (hD : 4 * a₀ * c₀ - b₀ ^ 2 = 1)
    (hdet : α * β' - α' * β = 1) (hcc : c' = a₀ * β ^ 2 + b₀ * β * β' + c₀ * β' ^ 2) : c' ≠ 0 := by
  intro h0
  have h4 : 4 * c₀ * c' = (2 * c₀ * β' + b₀ * β) ^ 2 + (β : ℝ) ^ 2 := by
    rw [hcc]; linear_combination (β : ℝ) ^ 2 * hD
  rw [h0] at h4
  have hβ2 : (β : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * c₀ * β' + b₀ * β), sq_nonneg (β : ℝ)]
  have hβ : (β : ℝ) = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hβ2
  have hβ' : (β' : ℝ) = 0 := by
    rw [hβ] at h4
    have : (2 * c₀ * β') ^ 2 = 0 := by nlinarith [sq_nonneg (2 * c₀ * β')]
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by positivity)
    · exact h
  have hβi : β = 0 := by exact_mod_cast hβ
  have hβ'i : β' = 0 := by exact_mod_cast hβ'
  rw [hβi, hβ'i] at hdet
  simp at hdet

lemma form_point₂ (a₀ b₀ c₀ b' c' : ℝ) (α α' β β' : ℤ) (hc₀ : 0 < c₀)
    (hD : 4 * a₀ * c₀ - b₀ ^ 2 = 1) (hdet : α * β' - α' * β = 1)
    (hb : b' = 2 * a₀ * α * β + b₀ * (α * β' + α' * β) + 2 * c₀ * α' * β')
    (hcc : c' = a₀ * β ^ 2 + b₀ * β * β' + c₀ * β' ^ 2) :
    ((α : ℂ) * ((b₀ + I) / (2 * c₀)) + α') / ((β : ℂ) * ((b₀ + I) / (2 * c₀)) + β') =
      (b' + I) / (2 * c') := by
  have hc'0 := form_c'_ne a₀ b₀ c₀ c' α α' β β' hc₀ hD hdet hcc
  have hw2 : 0 < (((b₀ + I) / (2 * c₀) : ℂ)).im := by
    have := im_form_point b₀ c₀ hc₀ 1
    simpa using this
  have hden : (β : ℂ) * ((b₀ + I) / (2 * c₀)) + β' ≠ 0 := by
    refine denom_ne_zero β β' _ hw2 ?_
    by_contra hh
    push Not at hh
    rw [hh.1, hh.2] at hdet
    simp at hdet
  have hc0 : (2 * (c₀ : ℂ)) ≠ 0 := by
    have : c₀ ≠ 0 := hc₀.ne'
    simp [this]
  have hc'0' : (2 * (c' : ℂ)) ≠ 0 := by simp [hc'0]
  have hbC : (b' : ℂ) = 2 * a₀ * α * β + b₀ * (α * β' + α' * β) + 2 * c₀ * α' * β' := by
    rw [hb]; push_cast; ring
  have hcC : (c' : ℂ) = a₀ * β ^ 2 + b₀ * β * β' + c₀ * β' ^ 2 := by
    rw [hcc]; push_cast; ring
  have hDC : (4 * a₀ * c₀ - b₀ ^ 2 : ℂ) = 1 := by exact_mod_cast hD
  have hdetC : (α * β' - α' * β : ℂ) = 1 := by exact_mod_cast hdet
  have hc₀' : (c₀ : ℂ) ≠ 0 := by simp [hc₀.ne']
  have hw' : (2 * (c₀ : ℂ)) * ((b₀ + I) / (2 * c₀)) = b₀ + I := by field_simp
  rw [div_eq_div_iff hden hc'0']
  refine mul_left_cancel₀ hc0 ?_
  generalize ((b₀ + I) / (2 * c₀) : ℂ) = w at hw' ⊢
  rw [hbC, hcC]
  linear_combination (2 * (a₀ * β ^ 2 + b₀ * β * β' + c₀ * β' ^ 2 : ℂ) * α - ((2 * a₀ * α * β + b₀ * (α * β' + α' * β) + 2 * c₀ * α' * β' : ℂ) + I) * β) * hw' + (-(β : ℂ) * (α * β' - α' * β)) * hDC +
    (-(β : ℂ) + I * (b₀ * β + 2 * c₀ * β')) * hdetC + (-(β : ℂ)) * Complex.I_sq

lemma form_point₁ (a₀ b₀ c₀ b' c' : ℝ) (α α' β β' : ℤ) (hc₀ : 0 < c₀)
    (hD : 4 * a₀ * c₀ - b₀ ^ 2 = 1) (hdet : α * β' - α' * β = 1)
    (hb : b' = 2 * a₀ * α * β + b₀ * (α * β' + α' * β) + 2 * c₀ * α' * β')
    (hcc : c' = a₀ * β ^ 2 + b₀ * β * β' + c₀ * β' ^ 2) :
    ((α : ℂ) * ((-b₀ + I) / (2 * c₀)) - α') / (-(β : ℂ) * ((-b₀ + I) / (2 * c₀)) + β') =
      (-b' + I) / (2 * c') := by
  have hc'0 := form_c'_ne a₀ b₀ c₀ c' α α' β β' hc₀ hD hdet hcc
  have hw2 : 0 < (((-b₀ + I) / (2 * c₀) : ℂ)).im := by
    have := im_form_point b₀ c₀ hc₀ (-1)
    simpa using this
  have hden : -(β : ℂ) * ((-b₀ + I) / (2 * c₀)) + β' ≠ 0 := by
    have := denom_ne_zero (-β) β' _ hw2 (by
      by_contra hh
      push Not at hh
      have hβ0 : β = 0 := by omega
      rw [hβ0, hh.2] at hdet
      simp at hdet)
    simpa using this
  have hc0 : (2 * (c₀ : ℂ)) ≠ 0 := by
    have : c₀ ≠ 0 := hc₀.ne'
    simp [this]
  have hc'0' : (2 * (c' : ℂ)) ≠ 0 := by simp [hc'0]
  have hbC : (b' : ℂ) = 2 * a₀ * α * β + b₀ * (α * β' + α' * β) + 2 * c₀ * α' * β' := by
    rw [hb]; push_cast; ring
  have hcC : (c' : ℂ) = a₀ * β ^ 2 + b₀ * β * β' + c₀ * β' ^ 2 := by
    rw [hcc]; push_cast; ring
  have hDC : (4 * a₀ * c₀ - b₀ ^ 2 : ℂ) = 1 := by exact_mod_cast hD
  have hdetC : (α * β' - α' * β : ℂ) = 1 := by exact_mod_cast hdet
  have hc₀' : (c₀ : ℂ) ≠ 0 := by simp [hc₀.ne']
  have hw' : (2 * (c₀ : ℂ)) * ((-b₀ + I) / (2 * c₀)) = -b₀ + I := by field_simp
  rw [div_eq_div_iff hden hc'0']
  refine mul_left_cancel₀ hc0 ?_
  generalize ((-b₀ + I) / (2 * c₀) : ℂ) = w at hw' ⊢
  rw [hbC, hcC]
  linear_combination (2 * (a₀ * β ^ 2 + b₀ * β * β' + c₀ * β' ^ 2 : ℂ) * α + (-(2 * a₀ * α * β + b₀ * (α * β' + α' * β) + 2 * c₀ * α' * β' : ℂ) + I) * β) * hw' + ((β : ℂ) * (α * β' - α' * β)) * hDC +
    ((β : ℂ) + I * (b₀ * β + 2 * c₀ * β')) * hdetC + (β : ℂ) * Complex.I_sq

/-- **The analytic invariant** (Werke 4, XXXI, § II, pp. 353–354): `A` takes the
same value on equivalent systems, the points `w₁ = (-b₀ + i)/(2c₀)`, `w₂ = (b₀ + i)/(2c₀)` being carried
to `(-b' + i)/(2c')`, `(b' + i)/(2c')` by the substitution. -/
@[kb "kronecker1929" "XXXI, § II, (𝔅), pp. 352–354"]
theorem kroneckerA_form_invariance : KroneckerAFormInvariance := by
  intro σ τ a₀ b₀ c₀ α α' α'' β β' β'' ha hc hD hdet f'
  have hw₁ := im_form_point b₀ c₀ hc (-1)
  have hw₂ := im_form_point b₀ c₀ hc 1
  simp only [neg_mul, one_mul, Complex.ofReal_neg] at hw₁ hw₂
  rw [kroneckerA_invariance σ τ _ _ α α' α'' β β' β'' hw₁ hw₂ hdet]
  have e₁ := form_point₁ a₀ b₀ c₀ f'.2.1 f'.2.2 α α' β β' hc hD hdet rfl rfl
  have e₂ := form_point₂ a₀ b₀ c₀ f'.2.1 f'.2.2 α α' β β' hc hD hdet rfl rfl
  rw [e₁, e₂]

end ModularFormsKB.Historical.Kronecker
