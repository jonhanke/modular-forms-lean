import ModularFormsKB.Historical.Ramanujan.TauDefs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import ModularFormsKB.Citation
/-!
# Ramanujan's Question 387

`∑_{n ≥ 1} n / (e^{2πn} - 1) = 1/24 - 1/(8π)`, from Mathlib's transformation law of `G2` at `z = i`
(`G2 i = π`, so `E₂(i) = 3/π`), the `q`-expansion `E₂ = 1 - 24 ∑ σ₁(n) qⁿ` and the Lambert series
`∑ σ₁(n) xⁿ = ∑ n xⁿ/(1 - xⁿ)`.
-/

noncomputable section

open UpperHalfPlane hiding I σ
open Complex
open scoped Real ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Ramanujan

lemma S_smul_I : ModularGroup.S • UpperHalfPlane.I = UpperHalfPlane.I := by
  rw [modular_S_smul]
  ext
  simp [UpperHalfPlane.coe_I]

lemma G2_I : EisensteinSeries.G2 UpperHalfPlane.I = π := by
  have h := EisensteinSeries.G2_S_transform UpperHalfPlane.I
  rw [S_smul_I] at h
  simp only [UpperHalfPlane.coe_I] at h
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : -2 * (π : ℂ) * Complex.I / Complex.I = -2 * π := by field_simp
  rw [h2] at h
  have : (Complex.I ^ 2 : ℂ)⁻¹ = -1 := by rw [Complex.I_sq]; norm_num
  rw [this] at h
  linear_combination h / 2

lemma E2_I : EisensteinSeries.E2 UpperHalfPlane.I = 3 / π := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [EisensteinSeries.E2, Pi.smul_apply, G2_I, riemannZeta_two]
  simp only [smul_eq_mul]
  field_simp
  norm_num

lemma term_real (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * Real.exp (-(2 * π)) ^ m / (1 - Real.exp (-(2 * π)) ^ m) =
      (m : ℝ) / (Real.exp (2 * π * m) - 1) := by
  have h1 : 1 < Real.exp (2 * π * m) := by
    rw [Real.one_lt_exp_iff]; have := Real.pi_pos; positivity
  have hx : Real.exp (-(2 * π)) ^ m = (Real.exp (2 * π * m))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring
  rw [hx]
  have h2 : Real.exp (2 * π * m) - 1 ≠ 0 := by linarith
  have h3 : Real.exp (2 * π * m) ≠ 0 := by positivity
  field_simp

lemma term_complex (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) ^ 1 * (((Real.exp (-(2 * π)) : ℝ) : ℂ)) ^ (n + 1) /
        (1 - (((Real.exp (-(2 * π)) : ℝ) : ℂ)) ^ (n + 1)) =
      ((((n + 1 : ℕ) : ℝ) / (Real.exp (2 * π * (n + 1 : ℕ)) - 1) : ℝ) : ℂ) := by
  rw [← term_real (n + 1) (Nat.succ_pos n)]
  push_cast
  ring

/-- **Ramanujan's Question 387** (J. Indian Math. Soc. 4 (1912), p. 120; *Collected Papers*, p. 326):
`∑_{n ≥ 1} n / (e^{2πn} - 1) = 1/24 - 1/(8π)`. -/
@[kb "ramanujan1927" "Question 387, p. 326"]
theorem question387 : Question387 := by
  have hrv : cexp (2 * π * Complex.I * (UpperHalfPlane.I : ℂ)) = ((Real.exp (-(2 * π)) : ℝ) : ℂ) := by
    rw [UpperHalfPlane.coe_I, Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]; ring
  have hE := EisensteinSeries.E2_eq_tsum_cexp UpperHalfPlane.I
  rw [E2_I, hrv] at hE
  have hr1 : ‖((Real.exp (-(2 * π)) : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; linarith)
  rw [← tsum_pow_div_one_sub_eq_tsum_sigma hr1 1,
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ (n : ℂ) ^ 1 * ((Real.exp (-(2 * π)) : ℝ) : ℂ) ^ n /
      (1 - ((Real.exp (-(2 * π)) : ℝ) : ℂ) ^ n))] at hE
  have hsum : Summable fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ) ^ 1 *
      ((Real.exp (-(2 * π)) : ℝ) : ℂ) ^ (n + 1) / (1 - ((Real.exp (-(2 * π)) : ℝ) : ℂ) ^ (n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℂ) ^ 1 * ((Real.exp (-(2 * π)) : ℝ) : ℂ) ^ n /
      (1 - ((Real.exp (-(2 * π)) : ℝ) : ℂ) ^ n)) 1).mpr
      (summable_norm_pow_mul_geometric_div_one_sub (𝕜 := ℂ) 1 hr1)
  simp_rw [term_complex] at hsum hE
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hS : (∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) / (Real.exp (2 * π * (n + 1 : ℕ)) - 1) : ℝ) : ℂ)) =
      ((1 / 24 - 1 / (8 * π) : ℝ) : ℂ) := by
    generalize (∑' n : ℕ, ((((n + 1 : ℕ) : ℝ) / (Real.exp (2 * π * (n + 1 : ℕ)) - 1) : ℝ) : ℂ)) = S
      at hE ⊢
    have h2 : S = (1 - 3 / π) / 24 := by linear_combination (1 / 24 : ℂ) * hE
    rw [h2]
    push_cast
    field_simp
    ring
  have := hsum.hasSum
  rw [hS] at this
  exact Complex.hasSum_ofReal.mp this

end ModularFormsKB.Historical.Ramanujan
