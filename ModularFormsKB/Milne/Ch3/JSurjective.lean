import Mathlib
import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs

/-!
# Surjectivity of the modular invariant `j : ℍ → ℂ`

Open-and-closed image argument: the image is open (open mapping theorem), and closed
(reduction to the fundamental domain, growth of `j` at the cusp, compactness).
-/

namespace ModularFormsKB.Milne
open UpperHalfPlane TauCeti.ModularForm Filter Topology Set

local notation "𝕢" => Function.Periodic.qParam

/-- `j` is large near the cusp. -/
theorem j_norm_large (B : ℝ) : ∃ M : ℝ, ∀ τ : ℍ, M ≤ τ.im → B ≤ ‖j τ‖ := by
  have h := tendsto_qParam_mul_j_atImInfty
  have hm : {τ : ℍ | ‖𝕢 1 τ * j τ - 1‖ < 1 / 2} ∈ atImInfty :=
    Eventually.mono (h.eventually (Metric.ball_mem_nhds _ (by norm_num : (0:ℝ) < 1 / 2)))
      fun τ hτ => by simpa [dist_eq_norm] using hτ
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 hm
  refine ⟨max A (max B 1), fun τ hτ => ?_⟩
  have h1 : ‖𝕢 1 τ * j τ - 1‖ < 1 / 2 := hA τ (le_trans (le_max_left _ _) hτ)
  have h2 : 1 / 2 ≤ ‖𝕢 1 τ * j τ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (𝕢 1 τ * j τ)
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hq : ‖𝕢 1 τ‖ = Real.exp (-2 * Real.pi * τ.im) := by
    rw [Function.Periodic.norm_qParam]; simp
  rw [norm_mul, hq] at h2
  have hpos := Real.exp_pos (-2 * Real.pi * τ.im)
  have hB : max B 1 ≤ τ.im := le_trans (le_max_right _ _) hτ
  have hexp : Real.exp (2 * Real.pi * τ.im) = (Real.exp (-2 * Real.pi * τ.im))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have h3 : 2 * Real.pi * τ.im + 1 ≤ Real.exp (2 * Real.pi * τ.im) := by
    linarith [Real.add_one_le_exp (2 * Real.pi * τ.im)]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have him : 1 ≤ τ.im := le_trans (le_max_right _ _) hB
  have h4 : 1 / 2 * Real.exp (2 * Real.pi * τ.im) ≤ ‖j τ‖ := by
    rw [hexp]
    calc 1 / 2 * (Real.exp (-2 * Real.pi * τ.im))⁻¹
        ≤ (Real.exp (-2 * Real.pi * τ.im) * ‖j τ‖) * (Real.exp (-2 * Real.pi * τ.im))⁻¹ := by
          gcongr
      _ = ‖j τ‖ := by field_simp
  nlinarith [le_trans (le_max_left _ _) hB, mul_pos Real.pi_pos (by linarith : (0:ℝ) < τ.im)]

/-- `j ∘ ofComplex` is analytic on the upper half plane. -/
theorem j_analyticOnNhd :
    AnalyticOnNhd ℂ (j ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp j_mdifferentiable).analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet

theorem isOpen_range_j : IsOpen (range j) := by
  have hU : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hnc : ¬ ∃ w, ∀ z ∈ {z : ℂ | 0 < z.im}, (j ∘ ofComplex) z = w := by
    rintro ⟨w, hw⟩
    have h1 := hw (I : ℂ) I.2
    have h2 := hw (ρ : ℂ) ρ.2
    simp only [Function.comp_apply, ofComplex_apply] at h1 h2
    rw [j_I] at h1
    rw [j_ρ] at h2
    rw [← h1] at h2
    norm_num at h2
  have hopen := (j_analyticOnNhd.is_constant_or_isOpen hU).resolve_left hnc
  have himg : range j = (j ∘ ofComplex) '' {z : ℂ | 0 < z.im} := by
    ext c
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨τ, τ.2, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, by simp [ofComplex_apply_of_im_pos hz]⟩
  rw [himg]
  exact hopen _ subset_rfl UpperHalfPlane.isOpen_upperHalfPlaneSet

theorem isClosed_range_j : IsClosed (range j) := by
  rw [← closure_subset_iff_isClosed]
  intro c hc
  obtain ⟨M, hM⟩ := j_norm_large (‖c‖ + 1)
  set K : Set ℂ := {z | |z.re| ≤ 1 / 2 ∧ Real.sqrt 3 / 2 ≤ z.im ∧ z.im ≤ max M 1} with hK
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have : K = {z : ℂ | |z.re| ≤ 1 / 2} ∩ {z | Real.sqrt 3 / 2 ≤ z.im} ∩ {z | z.im ≤ max M 1} := by
        ext z; simp [hK, and_assoc]
      rw [this]
      refine ((isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) (by fun_prop))).inter (isClosed_le (by fun_prop) (by fun_prop))
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1 / 2 + max M 1 + Real.sqrt 3 / 2 + 1, ?_⟩
      intro z hz
      obtain ⟨h1, h2, h3⟩ := hz
      have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
      have : ‖z‖ ≤ |z.re| + |z.im| := by
        have := Complex.norm_le_abs_re_add_abs_im z
        simpa using this
      rw [mem_closedBall_zero_iff]
      rw [abs_of_nonneg (by linarith : 0 ≤ z.im)] at this
      have := le_max_right M 1
      linarith
  have hKsub : K ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    show 0 < z.im; linarith [hz.2.1]
  have hcont : ContinuousOn (j ∘ ofComplex) K :=
    (UpperHalfPlane.mdifferentiable_iff.mp j_mdifferentiable).continuousOn.mono hKsub
  have hT : IsClosed ((j ∘ ofComplex) '' K) := (hKc.image_of_continuousOn hcont).isClosed
  have hsub : range j ∩ Metric.ball c 1 ⊆ (j ∘ ofComplex) '' K := by
    rintro _ ⟨⟨τ, rfl⟩, hb⟩
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    set σ := (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) • τ with hσ
    have hσfd : σ ∈ ModularGroup.fd := by
      simpa [hσ] using hg
    have hj : j σ = j τ := j_smul g τ
    have hnorm : ‖j σ‖ < ‖c‖ + 1 := by
      rw [hj]
      have h1 := Metric.mem_ball.1 hb
      rw [dist_eq_norm] at h1
      have := norm_sub_norm_le (j τ) c
      linarith
    have him : σ.im ≤ max M 1 := by
      by_contra hcon
      have := hM σ (by linarith [le_max_left M 1, not_le.1 hcon])
      linarith
    refine ⟨(σ : ℂ), ⟨?_, ?_, ?_⟩, by simp [hj]⟩
    · have := hσfd.2; simpa using this
    · have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσfd
      have hs : Real.sqrt 3 / 2 ≤ σ.im := by
        rw [div_le_iff₀ (by norm_num)]
        apply Real.sqrt_le_iff.2
        refine ⟨by linarith [σ.im_pos], ?_⟩
        nlinarith
      simpa using hs
    · simpa using him
  have hcl : c ∈ closure (range j ∩ Metric.ball c 1) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
    have : Metric.ball c (min ε 1) ∈ 𝓝 c := Metric.ball_mem_nhds _ (by positivity)
    obtain ⟨s, hs1, hs2⟩ := mem_closure_iff_nhds.1 hc _ this
    exact ⟨s, hεt (Metric.ball_subset_ball (min_le_left _ _) hs1),
      hs2, Metric.ball_subset_ball (min_le_right _ _) hs1⟩
  have hc' := (closure_minimal hsub hT) hcl
  obtain ⟨z, hz, hzc⟩ := hc'
  exact ⟨⟨z, hKsub hz⟩, by simpa [ofComplex_apply_of_im_pos (hKsub hz)] using hzc⟩

theorem j_surjective : Function.Surjective TauCeti.ModularForm.j := by
  have h : range j = univ :=
    (isClopen_iff.1 ⟨isClosed_range_j, isOpen_range_j⟩).resolve_left
      (nonempty_iff_ne_empty.1 ⟨_, I, rfl⟩)
  intro c
  have : c ∈ range j := h ▸ mem_univ c
  exact this

end ModularFormsKB.Milne
