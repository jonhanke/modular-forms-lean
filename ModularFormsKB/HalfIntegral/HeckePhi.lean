/-
# Hecke's function $\varphi(\tau) = (\operatorname{Im}\tau)^{(2k+1)/4}|f(\tau)|$

For $f$ with the weight $k+\tfrac12$ law on $\Gamma_0(4N)$ over an abstract
multiplier system, $\varphi$ is $\Gamma_0(4N)$-invariant (`HeckeBound.phi_smul`), because
$\operatorname{Im}(\gamma\tau) = \operatorname{Im}\tau/|c\tau+d|^2$ and $|j(\gamma,\tau)|^2 = |c\tau+d|$. At $g\tau$ it is
$(\operatorname{Im}\tau)^{(2k+1)/4}$ times the cusp quantity (`HeckeBound.phi_smul_eq_cuspNorm`).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Multiplier
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

namespace HeckeBound

/-- The exponent $w/2 = (2k+1)/4$. -/
noncomputable def ex (k : ℕ) : ℝ := ((2 * k + 1 : ℕ) : ℝ) / 4

/-- **Hecke's function** $\varphi(\tau) = (\operatorname{Im}\tau)^{(2k+1)/4}\,|f(\tau)|$. -/
noncomputable def phi (k : ℕ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℝ := τ.im ^ ex k * ‖f τ‖

/-- Hecke's function at $g\tau$ is $(\operatorname{Im}\tau)^{(2k+1)/4}$ times the cusp quantity. -/
private lemma two_ex (k : ℕ) : 2 * ex k = (k : ℝ) + 1 / 2 := by
  unfold ex; push_cast; ring

private lemma denom_pos (g : SL(2, ℤ)) (τ : UpperHalfPlane) : 0 < ‖(g 1 0 : ℂ) * τ + g 1 1‖ := by
  apply norm_pos_iff.mpr
  simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) τ

private lemma im_smul' (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    (g • τ).im = τ.im / ‖(g 1 0 : ℂ) * τ + g 1 1‖ ^ 2 := by
  have := ModularGroup.im_smul_eq_div_normSq g τ
  rw [Complex.normSq_eq_norm_sq] at this
  simpa [ModularGroup.denom_apply] using this

private lemma im_rpow (k : ℕ) (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    (g • τ).im ^ ex k = τ.im ^ ex k * ‖(g 1 0 : ℂ) * τ + g 1 1‖ ^ (-((k : ℝ) + 1 / 2)) := by
  have hD := denom_pos g τ
  rw [im_smul', Real.div_rpow τ.im_pos.le (by positivity), ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul hD.le, ← two_ex, Nat.cast_ofNat, Real.rpow_neg hD.le, div_eq_mul_inv]

/-- Hecke's function at $g\tau$ is $(\operatorname{Im}\tau)^{(2k+1)/4}$ times the cusp quantity. -/
theorem phi_smul_eq_cuspNorm (k : ℕ) (f : UpperHalfPlane → ℂ) (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    phi k f (g • τ) = τ.im ^ ex k * Abstract.cuspNorm k f g τ := by
  unfold phi Abstract.cuspNorm
  rw [im_rpow]; ring

/-- **Invariance of Hecke's function** under $\Gamma_0(4N)$. -/
theorem phi_smul (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} {f : UpperHalfPlane → ℂ}
    (hf : M.Transforms k N χ f) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * N)) (τ : UpperHalfPlane) :
    phi k f (γ • τ) = phi k f τ := by
  have h4 : γ ∈ Gamma0 4 := by
    rw [Gamma0_mem] at *
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at *
    exact dvd_trans (by push_cast; exact dvd_mul_right (4 : ℤ) N) hγ
  have hc : ((γ 1 0 : ℤ) : ZMod (4 * N)) = 0 := by rwa [Gamma0_mem] at hγ
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h1 : ((γ 0 0 : ℤ) : ZMod (4 * N)) * (γ 1 1 : ℤ) = 1 := by
    have := congrArg (fun x : ℤ ↦ (x : ZMod (4 * N))) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hc] at this
    simpa using this
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (4 * N)) :=
    IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod (4 * N)) (by rw [← h1]; ring)
  have hχ : ‖χ (γ 1 1 : ZMod (4 * N))‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one χ hu.unit
    simpa using this
  have hD := denom_pos γ τ
  rw [phi_smul_eq_cuspNorm]
  unfold Abstract.cuspNorm phi
  rw [hf γ hγ τ, norm_mul, norm_mul, hχ, one_mul, norm_pow]
  have hj : ‖M.j γ τ‖ = ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 : ℝ) := by
    have := M.norm_sq γ h4 τ
    rw [← this, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [hj, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
  have : ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) *
      ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 * ((2 * k + 1 : ℕ) : ℝ)) = 1 := by
    rw [← Real.rpow_add hD]
    push_cast
    have : -((k : ℝ) + 1 / 2) + 1 / 2 * (2 * k + 1) = 0 := by ring
    rw [this, Real.rpow_zero]
  calc _ = (‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2)) *
      ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (1 / 2 * ((2 * k + 1 : ℕ) : ℝ))) * (τ.im ^ ex k * ‖f τ‖) := by ring
    _ = _ := by rw [this, one_mul]

end HeckeBound

end ModularFormsKB.HalfIntegral
