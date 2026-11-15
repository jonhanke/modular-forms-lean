import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphy of locally normally convergent series in several variables

This is the several-variable Weierstrass theorem for series, proved by Cauchy estimates.
Mathlib only has the one-variable case (`differentiableOn_tsum_of_summable_norm`).

If each `f i` is complex differentiable on an open set `U` of a complex normed space and the series
is locally dominated by a summable sequence, then `∑' i, f i` is complex differentiable on `U`.

The proof: a bound `‖f i‖ ≤ C` on `closedBall y r` gives `‖fderiv ℂ (f i) y‖ ≤ C / r` by applying
the one-variable Cauchy estimate to `w ↦ f i (y + w • v)`; then Mathlib's
`hasFDerivAt_tsum_of_isPreconnected` applies on a small ball.
-/

open Metric Set Filter
open scoped Topology

namespace ModularFormsKB.Miyake.HeckeTrick

/-- Cauchy estimate for the Fréchet derivative of a complex differentiable function. -/
lemma norm_fderiv_le_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {S : Set E} (hS : IsOpen S) {f : E → ℂ} (hf : DifferentiableOn ℂ f S)
    {y : E} {r C : ℝ} (hr : 0 < r) (hsub : closedBall y r ⊆ S)
    (hC : ∀ z ∈ closedBall y r, ‖f z‖ ≤ C) :
    ‖fderiv ℂ f y‖ ≤ C / r := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC y (mem_closedBall_self hr.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set R : ℝ := r / ‖v‖ with hR
  have hRpos : 0 < R := by positivity
  have hmem : ∀ w : ℂ, w ∈ closedBall (0 : ℂ) R → y + w • v ∈ closedBall y r := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    rw [mem_closedBall_iff_norm]
    simp only [add_sub_cancel_left, norm_smul]
    calc ‖w‖ * ‖v‖ ≤ R * ‖v‖ := by gcongr
      _ = r := by rw [hR]; field_simp
  set g : ℂ → ℂ := fun w => f (y + w • v) with hg
  have hline : ∀ w : ℂ, HasDerivAt (fun w : ℂ => y + w • v) v w := by
    intro w
    simpa using ((hasDerivAt_id w).smul_const v).const_add y
  have hgd : ∀ w ∈ closedBall (0 : ℂ) R, DifferentiableAt ℂ g w := by
    intro w hw
    have hfa : DifferentiableAt ℂ f (y + w • v) :=
      (hf _ (hsub (hmem w hw))).differentiableAt (hS.mem_nhds (hsub (hmem w hw)))
    exact hfa.comp w (hline w).differentiableAt
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hRpos.ne']
    exact fun w hw => (hgd w hw).differentiableWithinAt
  have hsph : ∀ w ∈ sphere (0 : ℂ) R, ‖g w‖ ≤ C := fun w hw =>
    hC _ (hmem w (sphere_subset_closedBall hw))
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdc hsph
  have hder : deriv g 0 = fderiv ℂ f y v := by
    have hy : y ∈ S := hsub (mem_closedBall_self hr.le)
    have h0 : HasFDerivAt f (fderiv ℂ f y) ((fun w : ℂ => y + w • v) 0) := by
      have : (fun w : ℂ => y + w • v) 0 = y := by simp
      rw [this]
      exact ((hf y hy).differentiableAt (hS.mem_nhds hy)).hasFDerivAt
    have h1 : HasDerivAt (f ∘ fun w : ℂ => y + w • v) (fderiv ℂ f y v) 0 :=
      h0.comp_hasDerivAt (0 : ℂ) (hline 0)
    exact h1.deriv
  rw [hder] at key
  calc ‖fderiv ℂ f y v‖ ≤ C / R := key
    _ = C / r * ‖v‖ := by rw [hR]; field_simp

/-- Several-variable Weierstrass theorem for series. -/
theorem differentiableOn_tsum_of_locally_bounded {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} (hU : IsOpen U) {f : ι → E → ℂ}
    (hf : ∀ i, DifferentiableOn ℂ (f i) U)
    (hloc : ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ y ∈ V, ‖f i y‖ ≤ u i) :
    DifferentiableOn ℂ (fun x ↦ ∑' i, f i x) U := by
  intro x hx
  obtain ⟨V, hV, u, hu, hbd⟩ := hloc x hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hx))
  set r : ℝ := ε / 3 with hr
  have hrpos : 0 < r := by positivity
  have hsub : ∀ y ∈ ball x r, closedBall y r ⊆ ball x ε := by
    intro y hy z hz
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    have := dist_triangle z y x
    linarith
  have hderiv : ∀ i, ∀ y ∈ ball x r, ‖fderiv ℂ (f i) y‖ ≤ u i / r := by
    intro i y hy
    refine norm_fderiv_le_of_bound hU (hf i) hrpos
      (fun z hz => (hball (hsub y hy hz)).2) (fun z hz => hbd i z (hball (hsub y hy hz)).1)
  have hxs : x ∈ ball x r := mem_ball_self hrpos
  have hsum0 : Summable fun i => f i x :=
    Summable.of_norm_bounded hu (fun i => hbd i x (mem_of_mem_nhds hV))
  have := hasFDerivAt_tsum_of_isPreconnected (u := fun i => u i / r) (hu.div_const r)
    isOpen_ball (convex_ball x r).isPreconnected
    (fun i y hy => ((hf i).differentiableAt
      (hU.mem_nhds (hball ((hsub y hy) (mem_closedBall_self hrpos.le))).2)).hasFDerivAt)
    hderiv hxs hsum0 hxs
  exact this.differentiableAt.differentiableWithinAt

/-- Several-variable Weierstrass theorem for series, on the whole space. -/
theorem differentiable_tsum_of_locally_bounded {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ι → E → ℂ} (hf : ∀ i, Differentiable ℂ (f i))
    (hloc : ∀ x : E, ∃ V ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ y ∈ V, ‖f i y‖ ≤ u i) :
    Differentiable ℂ (fun x ↦ ∑' i, f i x) := by
  rw [← differentiableOn_univ]
  exact differentiableOn_tsum_of_locally_bounded isOpen_univ
    (fun i => (hf i).differentiableOn) (fun x _ => hloc x)

end ModularFormsKB.Miyake.HeckeTrick
