/-
# $\varphi$ decays at every cusp with odd denominator

Every $B \in \mathrm{SL}_2(\mathbb Z)$ with odd lower left entry is $M\,S\,T^j$ with $M \in \Gamma_0(4)$
(`exists_decomp_odd`); since $W(\varphi, M B') = W(\varphi, B')$ (`W_phiH_mul_left`), the absolute slash of
$\varphi$ at $B$ is that at $S$ evaluated at $\tau + j$, which tends to $0$ (`tendsto_W_phiH_of_odd`).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellThetaCuspPhiS

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex MatrixGroups CongruenceSubgroup Filter
open scoped Real Manifold

local notation "ℍ" => UpperHalfPlane

theorem exists_decomp_odd (B : SL(2, ℤ)) (hB : Odd (B 1 0)) :
    ∃ (M : SL(2, ℤ)) (j : ℤ), M ∈ Gamma0 4 ∧ B = M * (ModularGroup.S * ModularGroup.T ^ j) := by
  set j : ℤ := B 1 1 * B 1 0 with hj
  refine ⟨B * (ModularGroup.S * ModularGroup.T ^ j)⁻¹, j, ?_, (inv_mul_cancel_right B _).symm⟩
  rw [mem_Gamma0_iff_dvd]
  obtain ⟨k, hk⟩ := hB
  have h10 : (B * (ModularGroup.S * ModularGroup.T ^ j)⁻¹) 1 0 = B 1 0 * j - B 1 1 := by
    have hC : (((ModularGroup.S * ModularGroup.T ^ j : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![0, -1; 1, j] := by
      ext i k
      fin_cases i <;> fin_cases k <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, ModularGroup.coe_T_zpow,
          Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hC,
      Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h10, hj]
  exact ⟨B 1 1 * k * (k + 1), by push_cast; rw [hk]; ring⟩

theorem tendsto_vadd_atImInfty (x : ℝ) :
    Tendsto (fun τ : ℍ ↦ x +ᵥ τ) UpperHalfPlane.atImInfty UpperHalfPlane.atImInfty := by
  show Tendsto _ _ (comap UpperHalfPlane.im atTop)
  rw [tendsto_comap_iff]
  simpa [Function.comp_def, UpperHalfPlane.vadd_im] using tendsto_im_atImInfty

theorem W_phiH_S_mul_T_zpow (j : ℤ) (τ : ℍ) :
    W phiH (ModularGroup.S * ModularGroup.T ^ j) τ = W phiH ModularGroup.S ((j : ℝ) +ᵥ τ) := by
  rw [W_def, W_def, HalfIntegral.cuspDenom_mul, mul_smul, UpperHalfPlane.modular_T_zpow_smul]
  have hD : HalfIntegral.cuspDenom (ModularGroup.T ^ j) τ = 1 := by
    simp [HalfIntegral.cuspDenom, ModularGroup.coe_T_zpow]
  rw [hD, mul_one]

theorem tendsto_W_phiH_of_odd (B : SL(2, ℤ)) (hB : Odd (B 1 0)) :
    Tendsto (W phiH B) UpperHalfPlane.atImInfty (nhds 0) := by
  obtain ⟨M, j, hM, rfl⟩ := exists_decomp_odd B hB
  have e : W phiH (M * (ModularGroup.S * ModularGroup.T ^ j)) =
      fun τ ↦ W phiH ModularGroup.S ((j : ℝ) +ᵥ τ) :=
    funext fun τ ↦ (W_phiH_mul_left hM _ τ).trans (W_phiH_S_mul_T_zpow j τ)
  rw [e]
  exact tendsto_W_phiH_S.comp (tendsto_vadd_atImInfty _)

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
