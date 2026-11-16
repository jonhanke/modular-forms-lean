/-
# The sign-twisted theta series $\varphi(z) = \sum_n (-1)^n e^{2\pi i n^2 z}$

$\varphi(z) = $ `jacobiTheta₂ (1/2) (2 z)`. Facts:
* $\varphi(z) = 2\theta(4z) - \theta(z) = \theta(z + 1/2)$ (`phi_eq_two_theta`, `phi_eq_theta_add_half`);
* $|\varphi|$ is invariant under $\Gamma_0(4)$ up to the factor $|c z + d|^{1/2}$ (`norm_phi_smul_of_mem`), by
  conjugating by the translation $z \mapsto z + 1/2$;
* for the absolute slash, $W(\varphi, M B) = W(\varphi, B)$ for $M \in \Gamma_0(4)$ (`W_phi_mul_left`).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellThetaCuspAux

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex MatrixGroups CongruenceSubgroup Filter
open scoped Real Manifold

local notation "ℍ" => UpperHalfPlane

/-- $\varphi(z) = \sum_n (-1)^n e^{2\pi i n^2 z}$. -/
noncomputable def phi (z : ℂ) : ℂ := jacobiTheta₂ (1 / 2) (2 * z)

/-- $\varphi$ as a function on the upper half plane. -/
noncomputable def phiH (z : ℍ) : ℂ := phi z

theorem term_half (n : ℤ) (z : ℂ) : jacobiTheta₂_term n (1 / 2) (2 * z) =
    (if Even n then 1 else -1) * jacobiTheta₂_term n 0 (2 * z) := by
  have h1 : jacobiTheta₂_term n (1 / 2) (2 * z) =
      cexp (π * I * n) * jacobiTheta₂_term n 0 (2 * z) := by
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : cexp (π * I * n) = (-1) ^ n := by
    rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [h1, h2]
  by_cases h : Even n
  · simp [h, h.neg_one_zpow]
  · have : Odd n := Int.not_even_iff_odd.mp h
    simp [h, this.neg_one_zpow]

theorem phi_eq_theta_add_half (z : ℂ) : phi z = HalfIntegral.theta (z + 1 / 2) := by
  rw [HalfIntegral.theta_eq_tsum]
  unfold phi jacobiTheta₂
  refine tsum_congr fun n ↦ ?_
  unfold jacobiTheta₂_term
  rw [Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self n
  have hk' : (n : ℂ) * (n - 1) = k + k := by exact_mod_cast hk
  refine ⟨-k, ?_⟩
  push_cast
  linear_combination (-π * I) * hk'

theorem phi_eq_two_theta {z : ℂ} (hz : 0 < z.im) :
    phi z = 2 * HalfIntegral.theta (4 * z) - HalfIntegral.theta z := by
  have him : 0 < (2 * z).im := by simp; linarith
  have hg : Summable fun n : ℤ ↦ jacobiTheta₂_term n 0 (2 * z) :=
    (summable_jacobiTheta₂_term_iff 0 (2 * z)).mpr him
  have hs : Summable fun n : ℤ ↦ jacobiTheta₂_term n (1 / 2) (2 * z) :=
    (summable_jacobiTheta₂_term_iff (1 / 2) (2 * z)).mpr him
  set g : ℤ → ℂ := fun n ↦ jacobiTheta₂_term n 0 (2 * z) with hgdef
  set F : ℤ → ℂ := fun n ↦ if Even n then g n else 0 with hFdef
  have hFeq : ∀ n, F n = (1 / 2) * (g n + jacobiTheta₂_term n (1 / 2) (2 * z)) := by
    intro n
    rw [term_half]
    by_cases h : Even n <;> simp [F, h, g] <;> ring
  have hFs : HasSum F ((1 / 2) * (∑' n, g n + ∑' n, jacobiTheta₂_term n (1 / 2) (2 * z))) := by
    have := (hg.hasSum.add hs.hasSum).mul_left (1 / 2)
    have e : F = fun n ↦ (1 / 2) * (g n + jacobiTheta₂_term n (1 / 2) (2 * z)) := funext hFeq
    rw [e]; exact this
  have hinj : Function.Injective fun m : ℤ ↦ 2 * m := fun a b h ↦ by simpa using h
  have hsupp : Function.support F ⊆ Set.range fun m : ℤ ↦ 2 * m := by
    intro n hn
    have : Even n := by
      by_contra h; exact hn (by simp [F, h])
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by simp [hr]; ring⟩
  have h4 : HalfIntegral.theta (4 * z) = ∑' n, F n := by
    rw [← hinj.tsum_eq hsupp]
    rw [HalfIntegral.theta, jacobiTheta_eq_jacobiTheta₂]
    unfold jacobiTheta₂
    refine tsum_congr fun m ↦ ?_
    simp only [F, g, jacobiTheta₂_term, even_two_mul, ite_true]
    congr 1
    push_cast; ring
  have h1 : HalfIntegral.theta z = ∑' n, g n := by
    rw [HalfIntegral.theta, jacobiTheta_eq_jacobiTheta₂]
    simp only [g]
    unfold jacobiTheta₂
    rfl
  rw [h4, hFs.tsum_eq, h1]
  show jacobiTheta₂ (1 / 2) (2 * z) = _
  unfold jacobiTheta₂
  ring

theorem coe_smul_SL (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- Conjugation of $\Gamma_0(4)$ by the half translation. -/
theorem exists_half_conj (M : SL(2, ℤ)) (hM : M ∈ Gamma0 4) :
    ∃ M' : SL(2, ℤ), M' ∈ Gamma0 4 ∧ ∀ z : ℍ,
      ((M • z : ℍ) : ℂ) + 1 / 2 = ((M' • ((1 / 2 : ℝ) +ᵥ z) : ℍ) : ℂ) ∧
      HalfIntegral.cuspDenom M' ((1 / 2 : ℝ) +ᵥ z) = HalfIntegral.cuspDenom M z := by
  have hdvd : (4 : ℤ) ∣ M 1 0 := by
    have := (mem_Gamma0_iff_dvd).mp hM; exact_mod_cast this
  obtain ⟨c', hc'⟩ := hdvd
  have hd : Odd (M 1 1) := HalfIntegral.Gamma0_four_odd hM
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := M.det_coe
    rwa [Matrix.det_fin_two] at h
  have ha : Odd (M 0 0) := by
    have h1 : Odd (M 0 0 * M 1 1) := ⟨2 * M 0 1 * c', by rw [hc'] at hdet; linarith⟩
    exact (Int.odd_mul.mp h1).1
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hd
  have hdet' : (M 0 0 + 2 * c') * (M 1 1 - 2 * c') - (M 0 1 + (q - p) - c') * (4 * c') = 1 := by
    rw [hc'] at hdet
    rw [hp, hq] at hdet ⊢
    linear_combination hdet
  obtain ⟨M', h00, h01, h10, h11⟩ : ∃ M' : SL(2, ℤ), M' 0 0 = M 0 0 + 2 * c' ∧
      M' 0 1 = M 0 1 + (q - p) - c' ∧ M' 1 0 = 4 * c' ∧ M' 1 1 = M 1 1 - 2 * c' :=
    ⟨⟨!![M 0 0 + 2 * c', M 0 1 + (q - p) - c'; 4 * c', M 1 1 - 2 * c'], by
      rw [Matrix.det_fin_two]; simpa using hdet'⟩, rfl, rfl, rfl, rfl⟩
  refine ⟨M', ?_, fun z ↦ ?_⟩
  · rw [mem_Gamma0_iff_dvd, h10]
    exact ⟨c', by push_cast; ring⟩
  · have hD : HalfIntegral.cuspDenom M z ≠ 0 := HalfIntegral.cuspDenom_ne_zero M z
    have hcC : (M 1 0 : ℂ) = 4 * c' := by exact_mod_cast hc'
    have hdC : (M 1 1 : ℂ) = M 0 0 + 2 * (q - p) := by
      have : M 1 1 = M 0 0 + 2 * (q - p) := by rw [hp, hq]; ring
      exact_mod_cast this
    have hden : ((4 : ℂ) * c') * (1 / 2 + (z : ℂ)) + ((M 1 1 : ℂ) - 2 * c') =
        (M 1 0 : ℂ) * z + M 1 1 := by
      rw [hcC]; ring
    have hb : HalfIntegral.cuspDenom M' ((1 / 2 : ℝ) +ᵥ z) = HalfIntegral.cuspDenom M z := by
      simp only [HalfIntegral.cuspDenom, UpperHalfPlane.coe_vadd, h10, h11]
      push_cast
      exact hden
    refine ⟨?_, hb⟩
    have hD' : (M 1 0 : ℂ) * z + M 1 1 ≠ 0 := hD
    have goal' : ((M 0 0 : ℂ) * z + M 0 1) / ((M 1 0 : ℂ) * z + M 1 1) + 1 / 2 =
        (((M 0 0 : ℂ) + 2 * c') * (1 / 2 + (z : ℂ)) + ((M 0 1 : ℂ) + (q - p) - c')) /
          ((4 : ℂ) * c' * (1 / 2 + (z : ℂ)) + ((M 1 1 : ℂ) - 2 * c')) := by
      rw [hden, div_add' _ _ _ hD']
      congr 1
      rw [hdC, hcC]
      ring
    rw [coe_smul_SL, coe_smul_SL, h00, h01, h10, h11]
    simp only [UpperHalfPlane.coe_vadd]
    push_cast
    exact goal'

/-- $|\varphi(Mz)| = |cz + d|^{1/2}\,|\varphi(z)|$ for $M \in \Gamma_0(4)$. -/
theorem norm_phi_smul_of_mem {M : SL(2, ℤ)} (hM : M ∈ Gamma0 4) (z : ℍ) :
    ‖phi ((M • z : ℍ) : ℂ)‖ = ‖HalfIntegral.cuspDenom M z‖ ^ (1 / 2 : ℝ) * ‖phi z‖ := by
  obtain ⟨M', hM', h⟩ := exists_half_conj M hM
  obtain ⟨h1, h2⟩ := h z
  have e : phi ((M • z : ℍ) : ℂ) = HalfIntegral.thetaMult M' ((1 / 2 : ℝ) +ᵥ z) * phi z := by
    rw [phi_eq_theta_add_half, h1, HalfIntegral.theta_transformationLaw M' hM', phi_eq_theta_add_half]
    simp only [UpperHalfPlane.coe_vadd]
    push_cast
    ring_nf
  rw [e, norm_mul, HalfIntegral.norm_thetaMult hM']
  have : ‖((M' 1 0 : ℤ) : ℂ) * (((1 / 2 : ℝ) +ᵥ z : ℍ) : ℂ) + (M' 1 1 : ℤ)‖ =
      ‖HalfIntegral.cuspDenom M' ((1 / 2 : ℝ) +ᵥ z)‖ := rfl
  rw [this, h2]

/-- Left invariance of the absolute slash of $\varphi$ under $\Gamma_0(4)$. -/
theorem W_phiH_mul_left {M : SL(2, ℤ)} (hM : M ∈ Gamma0 4) (B : SL(2, ℤ)) (τ : ℍ) :
    W phiH (M * B) τ = W phiH B τ := by
  rw [W_def, W_def, mul_smul, HalfIntegral.cuspDenom_mul]
  have hx : 0 < ‖HalfIntegral.cuspDenom M (B • τ)‖ :=
    norm_pos_iff.mpr (HalfIntegral.cuspDenom_ne_zero M _)
  have hy : 0 < ‖HalfIntegral.cuspDenom B τ‖ := norm_pos_iff.mpr (HalfIntegral.cuspDenom_ne_zero B τ)
  have h := norm_phi_smul_of_mem hM (B • τ)
  simp only [phiH]
  rw [h, norm_mul, Real.mul_rpow hx.le hy.le]
  have : ‖HalfIntegral.cuspDenom M (B • τ)‖ ^ (-(1 / 2 : ℝ)) *
      ‖HalfIntegral.cuspDenom M (B • τ)‖ ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx]; norm_num
  calc _ = (‖HalfIntegral.cuspDenom M (B • τ)‖ ^ (-(1 / 2 : ℝ)) *
        ‖HalfIntegral.cuspDenom M (B • τ)‖ ^ (1 / 2 : ℝ)) *
        (‖HalfIntegral.cuspDenom B τ‖ ^ (-(1 / 2 : ℝ)) * ‖phi ((B • τ : ℍ) : ℂ)‖) := by ring
    _ = _ := by rw [this, one_mul]

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
