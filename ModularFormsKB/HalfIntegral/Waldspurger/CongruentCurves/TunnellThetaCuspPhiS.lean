/-
# Decay of $\varphi$ at the cusp $0$

By the functional equation of `jacobiTheta₂`,
$\varphi(-1/w) = (2i/w)^{-1/2}\,e^{\pi i w/8}\,\vartheta_2(-w/4, w/2)$, and $\vartheta_2(-w/4,w/2)$ is bounded for
$\operatorname{Im} w \ge 1$. Hence $|w|^{-1/2}|\varphi(-1/w)| \le C e^{-\pi \operatorname{Im} w/8} \to 0$
(`tendsto_W_phiH_S`).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellThetaCuspPhi

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex MatrixGroups CongruenceSubgroup Filter
open scoped Real Manifold

local notation "ℍ" => UpperHalfPlane

theorem exists_bound_theta₂ : ∃ C : ℝ, ∀ w : ℂ, 1 ≤ w.im → ‖jacobiTheta₂ (-w / 4) (w / 2)‖ ≤ C := by
  have hsum : Summable fun n : ℤ ↦ ‖jacobiTheta₂_term n (-I / 4) (I / 2)‖ :=
    summable_norm_iff.mpr ((summable_jacobiTheta₂_term_iff _ _).mpr (by simp))
  refine ⟨∑' n : ℤ, ‖jacobiTheta₂_term n (-I / 4) (I / 2)‖, fun w hw ↦ ?_⟩
  have hw0 : 0 < (w / 2).im := by simp; linarith
  have hs : Summable fun n : ℤ ↦ jacobiTheta₂_term n (-w / 4) (w / 2) :=
    (summable_jacobiTheta₂_term_iff _ _).mpr hw0
  have hsn : Summable fun n : ℤ ↦ ‖jacobiTheta₂_term n (-w / 4) (w / 2)‖ := summable_norm_iff.mpr hs
  refine (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum (fun n ↦ ?_) hsum)
  rw [norm_jacobiTheta₂_term, norm_jacobiTheta₂_term, Real.exp_le_exp]
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 - n := by
    have : (0 : ℤ) ≤ n ^ 2 - n := by
      rcases le_or_gt n 0 with h | h <;> nlinarith
    exact_mod_cast this
  have h1 : (w / 2).im = w.im / 2 := by simp
  have h2 : (-w / 4).im = -(w.im / 4) := by simp [neg_div]
  have h3 : (I / 2 : ℂ).im = 1 / 2 := by simp
  have h4 : (-I / 4 : ℂ).im = -(1 / 4) := by simp [neg_div]
  rw [h1, h2, h3, h4]
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hw), Real.pi_pos,
    mul_nonneg (mul_nonneg hn (sub_nonneg.mpr hw)) Real.pi_pos.le]

theorem W_phiH_S_eq (w : ℍ) :
    W phiH ModularGroup.S w = ‖(w : ℂ)‖ ^ (-(1 / 2 : ℝ)) * ‖phi (-(w : ℂ))⁻¹‖ := by
  rw [W_def]
  have h1 : HalfIntegral.cuspDenom ModularGroup.S w = w := by
    simp [HalfIntegral.cuspDenom, ModularGroup.S]
  rw [h1, UpperHalfPlane.modular_S_smul]
  rfl

theorem norm_phi_inv_eq (w : ℍ) :
    ‖(w : ℂ)‖ ^ (-(1 / 2 : ℝ)) * ‖phi (-(w : ℂ))⁻¹‖ =
      ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ * rexp (-π * w.im / 8) * ‖jacobiTheta₂ (-(w : ℂ) / 4) ((w : ℂ) / 2)‖ := by
  have hw : (w : ℂ) ≠ 0 := w.ne_zero
  have hN : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr hw
  unfold phi
  rw [jacobiTheta₂_functional_equation]
  have hz1 : (1 / 2 : ℂ) / (2 * (-(w : ℂ))⁻¹) = -w / 4 := by field_simp <;> norm_num
  have hz2 : -1 / (2 * (-(w : ℂ))⁻¹) = w / 2 := by field_simp
  have hz3 : -π * I * (1 / 2 : ℂ) ^ 2 / (2 * (-(w : ℂ))⁻¹) = π * I * w / 8 := by
    field_simp; ring
  have hz4 : -I * (2 * (-(w : ℂ))⁻¹) = 2 * I / w := by field_simp
  rw [hz1, hz2, hz3, hz4, norm_mul, norm_mul, norm_div, norm_one]
  have hn1 : ‖(2 * I / (w : ℂ)) ^ (1 / 2 : ℂ)‖ = (2 / ‖(w : ℂ)‖) ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by push_cast; rfl, Complex.norm_cpow_real, norm_div,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have hn2 : ‖cexp (π * I * w / 8)‖ = rexp (-π * w.im / 8) := by
    rw [Complex.norm_exp]
    congr 1
    simp [mul_assoc]
  rw [hn1, hn2, Real.div_rpow (by norm_num) hN.le, Real.rpow_neg hN.le]
  have ha : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hb : 0 < ‖(w : ℂ)‖ ^ (1 / 2 : ℝ) := by positivity
  field_simp

theorem tendsto_W_phiH_S : Tendsto (W phiH ModularGroup.S) UpperHalfPlane.atImInfty (nhds 0) := by
  obtain ⟨C, hC⟩ := exists_bound_theta₂
  have hlim : Tendsto (fun w : ℍ ↦ ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ * rexp (-π / 8 * w.im) * |C|)
      UpperHalfPlane.atImInfty (nhds 0) := by
    have h1 : Tendsto (fun w : ℍ ↦ -π / 8 * w.im) UpperHalfPlane.atImInfty atBot :=
      tendsto_im_atImInfty.const_mul_atTop_of_neg (by linarith [Real.pi_pos])
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := (h2.const_mul (((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹)).mul_const |C|
    simpa [mul_assoc] using h3
  refine squeeze_zero' (Eventually.of_forall fun w ↦ W_nonneg _ _ _) ?_ hlim
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
  refine ⟨1, fun w hw ↦ ?_⟩
  show W phiH ModularGroup.S w ≤ _
  rw [W_phiH_S_eq, norm_phi_inv_eq]
  have hb := (hC w hw)
  have hb' : ‖jacobiTheta₂ (-(w : ℂ) / 4) ((w : ℂ) / 2)‖ ≤ |C| := hb.trans (le_abs_self C)
  have e : rexp (-π * w.im / 8) = rexp (-π / 8 * w.im) := by congr 1; ring
  rw [e]
  have : 0 ≤ ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ * rexp (-π / 8 * w.im) := by positivity
  exact mul_le_mul_of_nonneg_left hb' this

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
