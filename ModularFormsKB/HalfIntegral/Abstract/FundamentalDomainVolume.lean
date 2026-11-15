/-
# The fundamental domain of SL₂(ℤ) has finite invariant volume

Mathlib's invariant measure on the upper half-plane is dx dy / y² (`UpperHalfPlane.volume_def`).
-/
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace ModularFormsKB.HalfIntegral

open MeasureTheory Set

/-- `ModularGroup.fd` is a measurable subset of the upper half-plane. -/
theorem measurableSet_fd : MeasurableSet ModularGroup.fd :=
  ModularGroup.isClosed_fd.measurableSet

/-- **Finite volume:** `ModularGroup.fd` has finite measure for `dx dy / y²`. -/
theorem volume_fd_lt_top : (volume : Measure UpperHalfPlane) ModularGroup.fd < ⊤ := by
  set e := Complex.measurableEquivRealProd with he
  set T : Set (ℝ × ℝ) := Icc (-1/2 : ℝ) (1/2) ×ˢ Ici (1/2 : ℝ) with hT
  have hTm : MeasurableSet T := measurableSet_Icc.prod measurableSet_Ici
  set g : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal (p.2 ^ (-2 : ℝ)) with hg
  have hgm : Measurable g := by
    simp only [hg]; fun_prop
  have hsub : ((↑) : UpperHalfPlane → ℂ) '' ModularGroup.fd ⊆ e ⁻¹' T := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h1, h2⟩ := hz
    have h3 : -(1/2) ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1/2 := abs_le.mp h2
    have hn : 1 ≤ (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 := by
      have := h1
      simp only [Complex.normSq_apply] at this
      nlinarith
    have hre : |(z : ℂ).re| ≤ 1/2 := h2
    have him : 1/2 ≤ (z : ℂ).im := by
      have hp : 0 < (z : ℂ).im := z.im_pos
      have := abs_le.mp hre
      nlinarith
    simp only [hT, he, mem_preimage, mem_prod, mem_Icc, mem_Ici,
      Complex.measurableEquivRealProd]
    exact ⟨⟨by show -1/2 ≤ (z : ℂ).re; linarith [h3.1], by show (z : ℂ).re ≤ 1/2; linarith [h3.2]⟩, him⟩
  have hcongr : ∫⁻ z : ℂ in e ⁻¹' T, ((1 / ‖z.im‖₊) ^ 2 : NNReal)
      = ∫⁻ z : ℂ in e ⁻¹' T, g (e z) := by
    refine setLIntegral_congr_fun (hTm.preimage e.measurable) ?_
    intro z hz
    have hz' : 1/2 ≤ z.im := by
      simp only [hT, he, mem_preimage, mem_prod, mem_Ici,
        Complex.measurableEquivRealProd] at hz
      exact hz.2
    have hp : 0 < z.im := by linarith
    simp only [hg, he, Complex.measurableEquivRealProd]
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    show _ = z.im ^ (-2 : ℝ)
    rw [Real.rpow_neg hp.le, Real.rpow_two]
    simp [Real.norm_of_nonneg hp.le, one_div]
  calc (volume : Measure UpperHalfPlane) ModularGroup.fd
      = ∫⁻ z : ℂ in (↑) '' ModularGroup.fd, ((1 / ‖z.im‖₊) ^ 2 : NNReal) :=
        UpperHalfPlane.volume_eq_lintegral _
    _ ≤ ∫⁻ z : ℂ in e ⁻¹' T, ((1 / ‖z.im‖₊) ^ 2 : NNReal) := lintegral_mono_set hsub
    _ = ∫⁻ z : ℂ in e ⁻¹' T, g (e z) := hcongr
    _ = ∫⁻ p in T, g p := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage hTm hgm
    _ < ⊤ := by
      rw [hT, Measure.volume_eq_prod, ← Measure.prod_restrict,
        lintegral_prod _ (hgm.aemeasurable)]
      simp only [hg, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
      have hint : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ici (1/2)) := by
        have h := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (c := 1/2) (by norm_num)
        exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr h
      have h2 := hint.lintegral_lt_top
      exact ENNReal.mul_lt_top h2 (by simp)
end ModularFormsKB.HalfIntegral
