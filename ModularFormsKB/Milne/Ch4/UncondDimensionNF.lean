import ModularFormsKB.Milne.Ch4.UncondValence

/-!
# Removable singularities for functions on the upper half-plane

Helpers for Milne, Theorem 4.9 (`ModularFormsKB.Milne.Ch4.UncondDimension`): a function on $\mathbb H$ that is
meromorphic with nonnegative order everywhere agrees, off a discrete set, with a holomorphic function (Mathlib's
meromorphic normal form `toMeromorphicNFOn`); slash invariance and boundedness at $i\infty$ pass to it.
-/

open UpperHalfPlane Complex Filter Topology ModularForm
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.UncondDimNF

/-- Two functions continuous at `z` that agree on a punctured neighbourhood of `z` agree at `z`. -/
theorem eq_of_eventuallyEq_nhdsNE {a b : ℂ → ℂ} {z : ℂ} (ha : ContinuousAt a z) (hb : ContinuousAt b z)
    (h : a =ᶠ[𝓝[≠] z] b) : a z = b z := by
  exact tendsto_nhds_unique (ha.tendsto.mono_left nhdsWithin_le_nhds)
    ((hb.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- Eventual equality on punctured neighbourhoods of every point passes to slashes. -/
theorem slash_eventuallyEq {u v : ℍ → ℂ} (huv : ∀ z : ℍ, u ∘ ofComplex =ᶠ[𝓝[≠] (z : ℂ)] v ∘ ofComplex)
    (k : ℤ) (γ : SL(2, ℤ)) (z : ℍ) :
    (u ∣[k] γ) ∘ ofComplex =ᶠ[𝓝[≠] (z : ℂ)] (v ∣[k] γ) ∘ ofComplex := by
  have hcont : ContinuousAt (fun w : ℂ ↦ ((γ • ofComplex w : ℍ) : ℂ)) (z : ℂ) := by
    have h1 : ContinuousAt ofComplex (z : ℂ) :=
      (UpperHalfPlane.mdifferentiableAt_ofComplex z.im_pos).continuousAt
    have h2 : ContinuousAt (fun τ : ℍ ↦ ((γ • τ : ℍ) : ℂ)) (ofComplex (z : ℂ)) :=
      (continuous_coe.comp (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ γ) :
        Continuous fun τ : ℍ ↦ (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ)).continuousAt
    exact h2.comp h1
  have hm : Tendsto (fun w : ℂ ↦ ((γ • ofComplex w : ℍ) : ℂ)) (𝓝[≠] (z : ℂ))
      (𝓝[≠] ((γ • z : ℍ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa [ofComplex_apply] using hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)] with w hw hwim
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    have h3 : γ • ofComplex w = γ • z := UpperHalfPlane.ext heq
    have h4 : ofComplex w = z := smul_left_cancel γ h3
    apply hw
    have := congrArg (fun τ : ℍ ↦ (τ : ℂ)) h4
    simpa [ofComplex_apply_of_im_pos hwim] using this
  have := hm.eventually (huv (γ • z))
  filter_upwards [this] with w hw
  simp only [Function.comp_apply, ofComplex_apply] at hw
  simp only [Function.comp_apply, SL_slash_apply, hw]

/-- The holomorphic function equal to `g` off a discrete set (the meromorphic normal form on $\mathbb H$). -/
def nf (g : ℍ → ℂ) : ℍ → ℂ := fun z ↦ toMeromorphicNFOn (g ∘ ofComplex) {w : ℂ | 0 < w.im} (z : ℂ)

variable {g : ℍ → ℂ}

theorem nf_eventuallyEq (hm : ∀ z : ℍ, MeromorphicAt (g ∘ ofComplex) (z : ℂ)) (z : ℍ) :
    nf g ∘ ofComplex =ᶠ[𝓝[≠] (z : ℂ)] g ∘ ofComplex := by
  have hU : MeromorphicOn (g ∘ ofComplex) {w : ℂ | 0 < w.im} := fun w hw ↦ hm ⟨w, hw⟩
  have h1 := hU.toMeromorphicNFOn_eq_self_on_nhdsNE (x := (z : ℂ)) z.im_pos
  filter_upwards [h1, eventually_nhdsWithin_of_eventually_nhds
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)] with w hw hwim
  simp only [Function.comp_apply, nf, ofComplex_apply_of_im_pos (show 0 < w.im from hwim)]
  simpa [ofComplex_apply_of_im_pos (show 0 < w.im from hwim)] using hw

private theorem nf_analyticAt (hm : ∀ z : ℍ, MeromorphicAt (g ∘ ofComplex) (z : ℂ))
    (ho : ∀ z : ℍ, 0 ≤ meromorphicOrderAt (g ∘ ofComplex) (z : ℂ)) (z : ℍ) :
    AnalyticAt ℂ (nf g ∘ ofComplex) (z : ℂ) := by
  have hU : MeromorphicOn (g ∘ ofComplex) {w : ℂ | 0 < w.im} := fun w hw ↦ hm ⟨w, hw⟩
  have hNF := meromorphicNFOn_toMeromorphicNFOn (g ∘ ofComplex) {w : ℂ | 0 < w.im} z.im_pos
  have hord : meromorphicOrderAt (toMeromorphicNFOn (g ∘ ofComplex) {w : ℂ | 0 < w.im}) (z : ℂ)
      = meromorphicOrderAt (g ∘ ofComplex) (z : ℂ) :=
    meromorphicOrderAt_congr (hU.toMeromorphicNFOn_eq_self_on_nhdsNE z.im_pos)
  have han := hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 (hord ▸ ho z)
  refine han.congr ?_
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp [nf, ofComplex_apply_of_im_pos (show 0 < w.im from hw)]

theorem nf_mdifferentiable (hm : ∀ z : ℍ, MeromorphicAt (g ∘ ofComplex) (z : ℂ))
    (ho : ∀ z : ℍ, 0 ≤ meromorphicOrderAt (g ∘ ofComplex) (z : ℂ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (nf g) := fun z ↦
  UpperHalfPlane.mdifferentiableAt_iff.2 (nf_analyticAt hm ho z).differentiableAt

private theorem nf_slash_differentiableAt (hm : ∀ z : ℍ, MeromorphicAt (g ∘ ofComplex) (z : ℂ))
    (ho : ∀ z : ℍ, 0 ≤ meromorphicOrderAt (g ∘ ofComplex) (z : ℂ)) (k : ℤ) (γ : SL(2, ℤ)) (z : ℍ) :
    DifferentiableAt ℂ ((nf g ∣[k] γ) ∘ ofComplex) (z : ℂ) := by
  have h := MDifferentiable.slash (nf_mdifferentiable hm ho) k (γ : GL (Fin 2) ℝ)
  rw [← ModularForm.SL_slash] at h
  exact UpperHalfPlane.mdifferentiableAt_iff.1 (h z)

/-- Slash invariance passes to the normal form. -/
theorem nf_slash (hm : ∀ z : ℍ, MeromorphicAt (g ∘ ofComplex) (z : ℂ))
    (ho : ∀ z : ℍ, 0 ≤ meromorphicOrderAt (g ∘ ofComplex) (z : ℂ)) {k : ℤ} {γ : SL(2, ℤ)}
    (hγ : g ∣[k] γ = g) : nf g ∣[k] γ = nf g := by
  funext z
  have key := eq_of_eventuallyEq_nhdsNE (nf_slash_differentiableAt hm ho k γ z).continuousAt
    (nf_analyticAt hm ho z).continuousAt (a := (nf g ∣[k] γ) ∘ ofComplex) (b := nf g ∘ ofComplex) (by
      have h1 := slash_eventuallyEq (u := nf g) (v := g) (nf_eventuallyEq hm) k γ z
      rw [hγ] at h1
      exact h1.trans (nf_eventuallyEq hm z).symm)
  simpa [ofComplex_apply] using key

/-- Boundedness at $i\infty$: if `g ∣[k] γ` is `h`-periodic and its cusp function has nonnegative order at `0`,
then `nf g ∣[k] γ` is bounded at $i\infty$. -/
theorem nf_isBoundedAtImInfty (hm : ∀ z : ℍ, MeromorphicAt (g ∘ ofComplex) (z : ℂ))
    (ho : ∀ z : ℍ, 0 ≤ meromorphicOrderAt (g ∘ ofComplex) (z : ℂ)) {k : ℤ} {γ : SL(2, ℤ)} {h : ℝ} (hh : 0 < h)
    (hper : Function.Periodic ((g ∣[k] γ) ∘ ofComplex) h)
    (hc : MeromorphicAt (Function.Periodic.cuspFunction h ((g ∣[k] γ) ∘ ofComplex)) 0)
    (hc0 : 0 ≤ meromorphicOrderAt (Function.Periodic.cuspFunction h ((g ∣[k] γ) ∘ ofComplex)) 0) :
    IsBoundedAtImInfty (nf g ∣[k] γ) := by
  set Q := Function.Periodic.cuspFunction h ((g ∣[k] γ) ∘ ofComplex) with hQ
  obtain ⟨c, hlim⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hc hc0
  have hb : ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖Q q‖ ≤ ‖c‖ + 1 := by
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds c one_pos)] with q hq
    have : ‖Q q - c‖ < 1 := by simpa [dist_eq_norm] using hq
    calc ‖Q q‖ = ‖c + (Q q - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖Q q - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + 1 := by linarith
  have hboth := hb.and hc.eventually_analyticAt
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hboth
  obtain ⟨r, hr, hrr⟩ := hboth
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hqc : Continuous (Function.Periodic.qParam h) := by
    unfold Function.Periodic.qParam; fun_prop
  refine ⟨‖c‖ + 1, -(h * Real.log r) / (2 * Real.pi) + 1, fun τ hτ ↦ ?_⟩
  have hA : -(h * Real.log r) / (2 * Real.pi) < τ.im := by linarith
  have hlt : ‖Function.Periodic.qParam h (τ : ℂ)‖ < r := by
    have h1 := (Function.Periodic.norm_qParam_lt_iff hh (-(h * Real.log r) / (2 * Real.pi)) (τ : ℂ)).2 hA
    have h2 : -2 * Real.pi * (-(h * Real.log r) / (2 * Real.pi)) / h = Real.log r := by
      field_simp
    rw [h2, Real.exp_log hr] at h1
    exact h1
  have hq0 : Function.Periodic.qParam h (τ : ℂ) ≠ 0 := Complex.exp_ne_zero _
  obtain ⟨hbd, hana⟩ := hrr (by simpa [dist_eq_norm] using hlt) hq0
  have hG : ((g ∣[k] γ) ∘ ofComplex) = Q ∘ Function.Periodic.qParam h := by
    funext w
    exact (Function.Periodic.eq_cuspFunction hh.ne' hper w).symm
  have hcont : ContinuousAt ((g ∣[k] γ) ∘ ofComplex) (τ : ℂ) := by
    rw [hG]
    exact hana.continuousAt.comp (hqc.continuousAt)
  have hev : (nf g ∣[k] γ) ∘ ofComplex =ᶠ[𝓝[≠] (τ : ℂ)] (g ∣[k] γ) ∘ ofComplex := by
    have h1 := slash_eventuallyEq (u := nf g) (v := g) (nf_eventuallyEq hm) k γ τ
    exact h1
  have key := eq_of_eventuallyEq_nhdsNE (nf_slash_differentiableAt hm ho k γ τ).continuousAt
    hcont hev
  have e : (nf g ∣[k] γ) τ = Q (Function.Periodic.qParam h (τ : ℂ)) := by
    have e2 : Q (Function.Periodic.qParam h (τ : ℂ)) = (g ∣[k] γ) τ := by
      simpa [ofComplex_apply] using Function.Periodic.eq_cuspFunction hh.ne' hper (τ : ℂ)
    rw [e2]
    simpa [ofComplex_apply] using key
  rw [e]
  exact hbd

end ModularFormsKB.Milne.UncondDimNF
