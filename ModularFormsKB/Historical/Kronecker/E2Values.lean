import ModularFormsKB.Historical.Kronecker.AnalyticInvariant
import ModularFormsKB.Historical.Ramanujan.Question387
import ModularFormsKB.Historical.Ramanujan.JacobiCube
import ModularFormsKB.Citation
/-!
# Kronecker's values of `ϑ'''(0)/ϑ'(0)` at `i` and `e^{2πi/3}`; Jacobi's cube identity

Kronecker, *Werke* 5 (1930), II (*Die Legendre'sche Relation*), art. IV, pp. 146–147:
`ϑ'''(0, i)/ϑ'(0, i) = -3π` and `ϑ'''(0, e^{2πi/3})/ϑ'(0, e^{2πi/3}) = -2√3 π`. Since `ϑ'''(0, w)/ϑ'(0, w) = -π² E₂(w)` (heat equation and
`ϑ'(0, w) = 2π η(w)³`), these are the values `E₂(i) = 3/π` and `E₂(e^{2πi/3}) = 2√3/π` of the
quasimodular Eisenstein series `E₂ = 1 - 24 ∑ σ₁(n) qⁿ` (Mathlib's `EisensteinSeries.E2`).

* `kronecker_E2_I`, `kronecker_E2_rho`: the two values of `E₂`, from Mathlib's transformation law of `G₂`
  (`G2_S_transform`, `G2_T_transform`).
* `KroneckerThetaE2`: the identity `ϑ'''(0, w) = -π² E₂(w) ϑ'(0, w)` for Kronecker's `ϑ`
  (`kroneckerTheta`), stated as a named proposition (proved in `ThetaE2.lean` as `kroneckerThetaE2`);
  `kronecker_theta_ratio_I`, `kronecker_theta_ratio_rho` derive Kronecker's two printed values from it.
* `kronecker_jacobi_cube` (Werke 5, I art. XVII, (14), p. 18): Jacobi's identity
  `∏ (1 - qⁿ)³ = ∑ (-1)ⁿ (2n+1) q^{n(n+1)/2}`, a wrapper of `Ramanujan.jacobi_cube_hasSum`.
-/

noncomputable section

open Complex UpperHalfPlane
open scoped Real

namespace ModularFormsKB.Historical.Kronecker

/-- The point `ρ = e^{2πi/3} = -1/2 + (√3/2) i` of the upper half plane. -/
def rhoPoint : ℍ := ⟨-1 / 2 + ((√3 / 2 : ℝ) : ℂ) * Complex.I, by simp⟩

theorem rhoPoint_coe : (rhoPoint : ℂ) = -1 / 2 + ((√3 / 2 : ℝ) : ℂ) * Complex.I := rfl

/-- **Kronecker, Werke 5, II art. IV, pp. 146–147**, in modern form: `E₂(i) = 3/π`.
Wrapper of `Ramanujan.E2_I`. -/
@[kb "kronecker1930" "Werke 5, II art. IV, pp. 146-147"]
theorem kronecker_E2_I : EisensteinSeries.E2 UpperHalfPlane.I = 3 / π :=
  Ramanujan.E2_I

/-- **Kronecker, Werke 5, II art. IV, pp. 146–147**, in modern form:
`E₂(e^{2πi/3}) = 2√3/π`. -/
@[kb "kronecker1930" "Werke 5, II art. IV, pp. 146-147"]
def KroneckerE2Rho : Prop :=
  EisensteinSeries.E2 rhoPoint = 2 * (√3 : ℝ) / π

/-- The identity `ϑ'''(0, w) = -π² E₂(w) ϑ'(0, w)` for Kronecker's odd theta function
`ϑ(ζ, w) = ∑_{ν odd} e^{(ν² w + 4νζ - 2ν) πi/4}` (`kroneckerTheta`), derivatives in `ζ`. It follows from the heat
equation `∂_w ϑ = (4πi)⁻¹ ∂_ζ² ϑ`, Jacobi's `ϑ'(0, w) = 2π η(w)³` and `η'/η = (πi/12) E₂`; stated as a named
proposition, proved in `ThetaE2.lean` (`kroneckerThetaE2`). -/
def KroneckerThetaE2 : Prop :=
  ∀ w : ℍ, iteratedDeriv 3 (fun ζ ↦ kroneckerTheta ζ w) 0 =
    -(π : ℂ) ^ 2 * EisensteinSeries.E2 w * deriv (fun ζ ↦ kroneckerTheta ζ w) 0

/-- **Jacobi's cube identity** as used by Kronecker (Werke 5, I art. XVII, (14), p. 18): for
`‖q‖ < 1`, `∏_{n ≥ 1} (1 - qⁿ)³ = ∑_{n ≥ 0} (-1)ⁿ (2n+1) q^{n(n+1)/2}`. Wrapper of
`Ramanujan.jacobi_cube_hasSum`. -/
@[kb "kronecker1930" "Werke 5, I art. XVII, (14), p. 18"]
theorem kronecker_jacobi_cube {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ n * (2 * n + 1) * q ^ (n * (n + 1) / 2))
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ 3) :=
  Ramanujan.jacobi_cube_hasSum hq

lemma G2_T_apply (z : ℍ) : EisensteinSeries.G2 (ModularGroup.T • z) = EisensteinSeries.G2 z := by
  have := congrFun EisensteinSeries.G2_T_transform z
  simpa [ModularForm.SL_slash_def, ModularGroup.denom_apply, ModularGroup.coe_T, ← ModularGroup.sl_moeb] using this

lemma S_smul_rho : ModularGroup.S • rhoPoint = ModularGroup.T • rhoPoint := by
  have hs : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow]; simp
  have h0 : (rhoPoint : ℂ) ≠ 0 := rhoPoint.ne_zero
  have hρ : (rhoPoint : ℂ) ^ 2 + rhoPoint + 1 = 0 := by
    rw [rhoPoint_coe]
    push_cast
    ring_nf
    rw [Complex.I_sq, hs]
    ring
  ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_T_smul]
  rw [UpperHalfPlane.coe_vadd]
  change (-(rhoPoint : ℂ))⁻¹ =((1 : ℝ) : ℂ) + rhoPoint
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * hρ

lemma G2_rho : EisensteinSeries.G2 rhoPoint = 2 * π / (√3 : ℝ) := by
  have hs : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow]; simp
  have hs0 : ((√3 : ℝ) : ℂ) ≠ 0 := by
    simp
  have h0 : (rhoPoint : ℂ) ≠ 0 := rhoPoint.ne_zero
  have hρ : (rhoPoint : ℂ) ^ 2 + rhoPoint + 1 = 0 := by
    rw [rhoPoint_coe]
    push_cast
    ring_nf
    rw [Complex.I_sq, hs]
    ring
  have hρ' : (rhoPoint : ℂ) ^ 2 - 1 = ((√3 : ℝ) : ℂ) * Complex.I * rhoPoint := by
    have : (rhoPoint : ℂ) ^ 2 = -rhoPoint - 1 := by linear_combination hρ
    rw [this]
    rw [rhoPoint_coe]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    linear_combination (1 / 2 : ℂ) * hs
  have h :=EisensteinSeries.G2_S_transform rhoPoint
  rw [S_smul_rho, G2_T_apply] at h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : EisensteinSeries.G2 rhoPoint * ((√3 : ℝ) : ℂ) = 2 * π := by
    have h1 : EisensteinSeries.G2 rhoPoint * ((rhoPoint : ℂ) ^ 2 - 1) =
        2 * π * Complex.I * rhoPoint := by
      field_simp at h
      linear_combination h
    rw [hρ'] at h1
    have : (Complex.I * rhoPoint) * (EisensteinSeries.G2 rhoPoint * ((√3 : ℝ) : ℂ) - 2 * π) = 0 := by
      linear_combination h1
    rcases mul_eq_zero.mp this with h2 | h2
    · exact absurd h2 (mul_ne_zero Complex.I_ne_zero h0)
    · linear_combination h2
  field_simp
  exact key

/-- **Kronecker, Werke 5, II art. IV, pp. 146–147**: `E₂(e^{2πi/3}) = 2√3/π`.
From `G₂(ρ) = 2π/√3`, obtained by applying `G2_S_transform` at `ρ` together with `S • ρ = T • ρ` and
`T`-invariance of `G₂`. -/
@[kb "kronecker1930" "Werke 5, II art. IV, pp. 146-147"]
theorem kronecker_E2_rho : KroneckerE2Rho := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow]; simp
  have hs0 : ((√3 : ℝ) : ℂ) ≠ 0 := by simp
  unfold KroneckerE2Rho
  rw [EisensteinSeries.E2, Pi.smul_apply, G2_rho, riemannZeta_two]
  simp only [smul_eq_mul]
  field_simp
  linear_combination (-2 : ℂ) * hs

/-- Kronecker's value `ϑ'''(0, i)/ϑ'(0, i) = -3π`, from `KroneckerThetaE2` and
`E₂(i) = 3/π`. -/
theorem kronecker_theta_ratio_I (h : KroneckerThetaE2) :
    iteratedDeriv 3 (fun ζ ↦ kroneckerTheta ζ UpperHalfPlane.I) 0 =
      -3 * π * deriv (fun ζ ↦ kroneckerTheta ζ UpperHalfPlane.I) 0 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [h UpperHalfPlane.I, kronecker_E2_I]
  field_simp

/-- Kronecker's value `ϑ'''(0, ρ)/ϑ'(0, ρ) = -2√3 π`, from `KroneckerThetaE2` and
`E₂(ρ) = 2√3/π`. -/
theorem kronecker_theta_ratio_rho (h : KroneckerThetaE2) :
    iteratedDeriv 3 (fun ζ ↦ kroneckerTheta ζ rhoPoint) 0 =
      -2 * (√3 : ℝ) * π * deriv (fun ζ ↦ kroneckerTheta ζ rhoPoint) 0 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [h rhoPoint, kronecker_E2_rho]
  field_simp

end ModularFormsKB.Historical.Kronecker
