/-
# Holomorphic parametric integrals over a set of finite measure

If $h(\tau, s)$ is entire in $s$ for every
$\tau \in \mathbb H$, continuous in $\tau$ for every $s$, and bounded on $S \times \{\sigma_1 \le \operatorname{Re}s \le \sigma_2\}$ for
every vertical strip, then $s \mapsto \int_S h(\tau,s)\,d\mu(\tau)$ is entire (`differentiable_setIntegral_of_strip_bound`;
dominated differentiation, the derivative bounded by Cauchy's estimate on circles of radius $1$) and bounded on vertical
strips (`bddVStrips_setIntegral_of_strip_bound`).
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace ModularFormsKB.HalfIntegral

open Complex MeasureTheory Set
open scoped Real

local notation "ℍ" => UpperHalfPlane

theorem differentiable_setIntegral_of_strip_bound {S : Set ℍ} (hS : MeasurableSet S)
    (hμ : (volume : Measure ℍ) S < ⊤) {h : ℍ → ℂ → ℂ} (hd : ∀ τ, Differentiable ℂ (h τ))
    (hc : ∀ s, Continuous fun τ ↦ h τ s)
    (hb : ∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ τ ∈ S, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖h τ s‖ ≤ C) :
    Differentiable ℂ (fun s ↦ ∫ τ in S, h τ s) := by
  intro s₀
  have : IsFiniteMeasure ((volume : Measure ℍ).restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμ⟩
  obtain ⟨C, hC⟩ := hb (s₀.re - 1) (s₀.re + 1)
  have hmeas : ∀ s, AEStronglyMeasurable (fun τ ↦ h τ s) ((volume : Measure ℍ).restrict S) :=
    fun s ↦ (hc s).aestronglyMeasurable
  have hbd : ∀ᵐ τ ∂((volume : Measure ℍ).restrict S), ∀ s ∈ Metric.ball s₀ (1/2 : ℝ),
      ‖deriv (h τ) s‖ ≤ C / (1/2 : ℝ) := by
    refine ae_restrict_of_forall_mem hS fun τ hτ s hs ↦ ?_
    apply norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
    · exact (hd τ).diffContOnCl
    · intro z hz
      have h1 : ‖z - s‖ = 1/2 := by simpa [Complex.dist_eq] using hz
      have h2 : ‖s - s₀‖ < 1/2 := by simpa [Complex.dist_eq] using hs
      have h3 : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
      have h4 : ‖z - s₀‖ ≤ ‖z - s‖ + ‖s - s₀‖ := by
        simpa using norm_add_le (z - s) (s - s₀)
      have h5 := abs_le.mp h3
      simp only [Complex.sub_re] at h5
      exact hC τ hτ z (by linarith [h5.1]) (by linarith [h5.2])
  have hderiv : AEStronglyMeasurable (fun τ ↦ deriv (h τ) s₀) ((volume : Measure ℍ).restrict S) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun (n : ℕ) τ ↦ ((n + 1 : ℂ))⁻¹⁻¹ • (h τ (s₀ + ((n + 1 : ℂ))⁻¹) - h τ s₀)) ?_ ?_
    · intro n
      exact (Continuous.aestronglyMeasurable (μ := (volume : Measure ℍ).restrict S)
        (f := fun τ ↦ ((n + 1 : ℂ))⁻¹⁻¹ • (h τ (s₀ + ((n + 1 : ℂ))⁻¹) - h τ s₀))
        (by
          have h1 := hc (s₀ + ((n + 1 : ℂ))⁻¹)
          have h2 := hc s₀
          fun_prop))
    · refine Filter.Eventually.of_forall fun τ ↦ ?_
      have h0 : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℂ))⁻¹) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n ↦ ?_⟩
        · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
          simpa using this
        · simp only [mem_compl_iff, mem_singleton_iff, inv_eq_zero]
          exact_mod_cast Nat.succ_ne_zero n
      exact ((hd τ s₀).hasDerivAt.tendsto_slope_zero).comp h0
  have hbound := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℍ).restrict S)
    (F := fun s τ ↦ h τ s) (F' := fun s τ ↦ deriv (h τ) s) (x₀ := s₀) (bound := fun _ ↦ C / (1/2 : ℝ))
    (Metric.ball_mem_nhds s₀ (by norm_num : (0:ℝ) < 1/2)) (Filter.Eventually.of_forall hmeas)
    (Integrable.of_bound (hmeas s₀) (C := C) (ae_restrict_of_forall_mem hS fun τ hτ ↦
      hC τ hτ s₀ (by linarith) (by linarith))) hderiv hbd (integrable_const _)
    (Filter.Eventually.of_forall fun τ s _ ↦ (hd τ s).hasDerivAt)
  exact hbound.2.differentiableAt

theorem bddVStrips_setIntegral_of_strip_bound {S : Set ℍ} (hμ : (volume : Measure ℍ) S < ⊤) {h : ℍ → ℂ → ℂ}
    (hb : ∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ τ ∈ S, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖h τ s‖ ≤ C) :
    BddVStrips (fun s ↦ ∫ τ in S, h τ s) := by
  intro σ₁ σ₂
  have : IsFiniteMeasure ((volume : Measure ℍ).restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμ⟩
  obtain ⟨C, hC⟩ := hb σ₁ σ₂
  refine ⟨max C 0 * (volume S).toReal, fun s h1 h2 ↦ ?_⟩
  by_cases hf : AEStronglyMeasurable (fun τ ↦ h τ s) ((volume : Measure ℍ).restrict S)
  · have hae : ∀ᵐ τ ∂((volume : Measure ℍ).restrict S), ‖h τ s‖ ≤ max C 0 := by
      set g := hf.mk _ with hg
      have hfg : (fun τ ↦ h τ s) =ᵐ[(volume : Measure ℍ).restrict S] g := hf.ae_eq_mk
      have hne : (volume : Measure ℍ).restrict S {τ | h τ s ≠ g τ} = 0 := hfg
      have hBm : MeasurableSet {τ | max C 0 < ‖g τ‖} :=
        measurableSet_lt measurable_const hf.stronglyMeasurable_mk.measurable.norm
      have hB : (volume : Measure ℍ).restrict S {τ | max C 0 < ‖g τ‖} = 0 := by
        rw [Measure.restrict_apply hBm]
        have hsub : {τ | max C 0 < ‖g τ‖} ∩ S ⊆ {τ | h τ s ≠ g τ} ∩ S := by
          rintro τ ⟨hτ1, hτ2⟩
          refine ⟨fun hh ↦ ?_, hτ2⟩
          have := hC τ hτ2 s h1 h2
          have h3 : ‖g τ‖ = ‖h τ s‖ := by rw [← hh]
          have h4 := le_max_left C 0
          simp only [mem_setOf_eq] at hτ1
          linarith
        exact le_antisymm
          ((measure_mono hsub).trans ((Measure.le_restrict_apply S _).trans hne.le)) bot_le
      rw [ae_iff]
      refine measure_mono_null ?_ (measure_union_null hne hB)
      intro τ hτ
      by_contra hcon
      simp only [mem_union, mem_setOf_eq, not_or, not_not, not_lt] at hcon
      simp only [mem_setOf_eq, not_le] at hτ
      linarith [hcon.1 ▸ hcon.2]
    have := norm_integral_le_of_norm_le_const hae
    simpa [Measure.real, Measure.restrict_apply_univ] using this
  · show ‖∫ τ in S, h τ s‖ ≤ _
    rw [integral_non_aestronglyMeasurable hf]
    simp only [norm_zero]
    positivity

end ModularFormsKB.HalfIntegral
