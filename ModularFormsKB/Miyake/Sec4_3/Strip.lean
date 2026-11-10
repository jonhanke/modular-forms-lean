import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Vertical strips: Phragmén–Lindelöf decay and shifting vertical contours

Tools for the proof of Hecke's converse theorem (Miyake Theorem 4.3.5, (B) ⇒ (A)).

* `Miyake.strip_decay`: a function holomorphic and bounded on a closed vertical strip, which decays
  like $1/(1+t^2)$ on both edges, decays like $1/(1+t^2)$ uniformly in the strip (Phragmén–Lindelöf,
  Mathlib's `PhragmenLindelof.vertical_strip`; compare Miyake Lemma 4.3.4).
* `Miyake.integral_vertical_eq_of_decay`: for such a function, the integrals over the two edges
  agree (Cauchy's theorem on rectangles, Mathlib's
  `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, and a limit).
-/

open Complex Filter Set MeasureTheory
open scoped Real Topology

noncomputable section

namespace Miyake

/-- **Phragmén–Lindelöf decay in a strip.** If $\Phi$ is holomorphic on the closed strip
$\beta \le \operatorname{Re} s \le \alpha$, bounded there, and $\|\Phi(\sigma + it)\| \le A/(1+t^2)$ on the
two edges $\sigma = \alpha, \beta$, then $\|\Phi(s)\| \le A'/(1 + (\operatorname{Im} s)^2)$ on the
whole strip. (Proof idea: apply `PhragmenLindelof.vertical_strip` to $(s - w)^2\Phi(s)$ with
$w = \beta - 1$, using $|s - w|^2 \ge 1 + (\operatorname{Im} s)^2$ in the strip.) -/
lemma strip_decay {Φ : ℂ → ℂ} {β α : ℝ} (hβα : β < α)
    (hd : DifferentiableOn ℂ Φ {s : ℂ | β ≤ s.re ∧ s.re ≤ α})
    {B : ℝ} (hB : ∀ s : ℂ, β ≤ s.re → s.re ≤ α → ‖Φ s‖ ≤ B)
    {A : ℝ} (hα : ∀ t : ℝ, ‖Φ (α + t * I)‖ ≤ A / (1 + t ^ 2))
    (hβ : ∀ t : ℝ, ‖Φ (β + t * I)‖ ≤ A / (1 + t ^ 2)) :
    ∃ A' : ℝ, ∀ s : ℂ, β ≤ s.re → s.re ≤ α → ‖Φ s‖ ≤ A' / (1 + s.im ^ 2) := by
  set w : ℝ := β - 1 with hw
  set M : ℝ := (α - w) ^ 2 with hM
  have hαw : 1 ≤ α - w := by rw [hw]; linarith
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith
  have hA0 : 0 ≤ A := by
    have := le_trans (norm_nonneg _) (hα 0)
    simpa using this
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB (β : ℂ) (by simp) (by simpa using hβα.le))
  have hN : ∀ z : ℂ, ‖z - (w : ℂ)‖ ^ 2 = (z.re - w) ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    ring
  set ψ : ℂ → ℂ := fun s => (s - (w : ℂ)) ^ 2 * Φ s with hψ
  have hnψ : ∀ z, ‖ψ z‖ = ((z.re - w) ^ 2 + z.im ^ 2) * ‖Φ z‖ := by
    intro z
    simp only [hψ, norm_mul, norm_pow, ← hN z]
  have hclosed : IsClosed {s : ℂ | β ≤ s.re ∧ s.re ≤ α} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)
  have hψd : DifferentiableOn ℂ ψ {s : ℂ | β ≤ s.re ∧ s.re ≤ α} :=
    (((differentiable_id.sub_const (w : ℂ)).pow 2).differentiableOn).mul hd
  have hsub : (Complex.re ⁻¹' Set.Ioo β α) ⊆ {s : ℂ | β ≤ s.re ∧ s.re ≤ α} :=
    fun s hs => ⟨hs.1.le, hs.2.le⟩
  have hcl : closure (Complex.re ⁻¹' Set.Ioo β α) ⊆ {s : ℂ | β ≤ s.re ∧ s.re ≤ α} :=
    closure_minimal hsub hclosed
  have hfd : DiffContOnCl ℂ ψ (Complex.re ⁻¹' Set.Ioo β α) :=
    ⟨hψd.mono hsub, hψd.continuousOn.mono hcl⟩
  -- boundary bound
  have hbd : ∀ σ : ℝ, β ≤ σ → σ ≤ α → ∀ z : ℂ, z.re = σ →
      ‖Φ z‖ ≤ A / (1 + z.im ^ 2) → ‖ψ z‖ ≤ M * A := by
    intro σ h1 h2 z hz hΦ
    rw [hnψ]
    have h3 : (z.re - w) ^ 2 + z.im ^ 2 ≤ M * (1 + z.im ^ 2) := by
      rw [hM, hz]
      have : (σ - w) ^ 2 ≤ (α - w) ^ 2 := by
        have : 0 ≤ σ - w := by rw [hw]; linarith
        nlinarith
      nlinarith [sq_nonneg z.im]
    have hpos : 0 < 1 + z.im ^ 2 := by positivity
    calc ((z.re - w) ^ 2 + z.im ^ 2) * ‖Φ z‖
        ≤ (M * (1 + z.im ^ 2)) * (A / (1 + z.im ^ 2)) :=
          mul_le_mul h3 hΦ (norm_nonneg _) (by positivity)
      _ = M * A := by field_simp
  have hbα : ∀ z : ℂ, z.re = α → ‖ψ z‖ ≤ M * A := by
    intro z hz
    refine hbd α hβα.le le_rfl z hz ?_
    have := hα z.im
    have e : (α : ℂ) + z.im * I = z := by rw [← hz]; exact Complex.re_add_im z
    rwa [e] at this
  have hbβ : ∀ z : ℂ, z.re = β → ‖ψ z‖ ≤ M * A := by
    intro z hz
    refine hbd β le_rfl hβα.le z hz ?_
    have := hβ z.im
    have e : (β : ℂ) + z.im * I = z := by rw [← hz]; exact Complex.re_add_im z
    rwa [e] at this
  -- growth
  have hab : 0 < α - β := by linarith
  set c : ℝ := π / (2 * (α - β)) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hclt : c < π / (α - β) := by
    rw [hc]
    have : π / (2 * (α - β)) = (π / (α - β)) / 2 := by field_simp
    rw [this]
    have : 0 < π / (α - β) := by positivity
    linarith
  have hgrow : ψ =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo β α)]
      fun z => Real.exp (B * (M + 2 / c ^ 2) * Real.exp (c * |z.im|)) := by
    refine Asymptotics.IsBigO.of_bound 1 (eventually_inf_principal.2 (Eventually.of_forall ?_))
    intro z hz
    set e := Real.exp (c * |z.im|) with he
    have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
    have hq := Real.quadratic_le_exp_of_nonneg (x := c * |z.im|) (by positivity)
    have ht : z.im ^ 2 ≤ 2 / c ^ 2 * e := by
      have hc2 : 0 < c ^ 2 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
      have : (c * |z.im|) ^ 2 = c ^ 2 * z.im ^ 2 := by rw [mul_pow, sq_abs]
      have hq' : (c * |z.im|) ^ 2 / 2 ≤ e := by
        rw [he]; linarith [hq, mul_nonneg hcpos.le (abs_nonneg z.im)]
      nlinarith
    have hre : (z.re - w) ^ 2 ≤ M := by
      have h1 : 0 ≤ z.re - w := by rw [hw]; linarith [hz.1]
      have h2 : z.re - w ≤ α - w := by linarith [hz.2]
      rw [hM]; nlinarith
    have hΦ := hB z hz.1.le hz.2.le
    have hX : ‖ψ z‖ ≤ B * (M + 2 / c ^ 2) * e := by
      rw [hnψ]
      calc ((z.re - w) ^ 2 + z.im ^ 2) * ‖Φ z‖
          ≤ ((z.re - w) ^ 2 + z.im ^ 2) * B :=
            mul_le_mul_of_nonneg_left hΦ (by positivity)
        _ ≤ (M * e + 2 / c ^ 2 * e) * B := by
            apply mul_le_mul_of_nonneg_right _ hB0
            nlinarith
        _ = B * (M + 2 / c ^ 2) * e := by ring
    have hexp := Real.add_one_le_exp (B * (M + 2 / c ^ 2) * e)
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    linarith
  have hmain : ∀ z : ℂ, β ≤ z.re → z.re ≤ α → ‖ψ z‖ ≤ M * A := fun z h1 h2 =>
    PhragmenLindelof.vertical_strip hfd ⟨c, hclt, B * (M + 2 / c ^ 2), hgrow⟩ hbβ hbα h1 h2
  refine ⟨M * A, fun s h1 h2 => ?_⟩
  have hm := hmain s h1 h2
  rw [hnψ] at hm
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  rw [le_div_iff₀ hpos, mul_comm]
  refine le_trans ?_ hm
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have : 1 ≤ (s.re - w) ^ 2 := by
    have : 1 ≤ s.re - w := by rw [hw]; linarith
    nlinarith
  linarith

/-- **Shifting a vertical contour.** If $h$ is holomorphic on the closed strip
$\beta \le \operatorname{Re} s \le \alpha$ and $\|h(s)\| \le A/(1 + (\operatorname{Im} s)^2)$ there, then
$$\int_{\mathbb R} h(\alpha + it)\,dt = \int_{\mathbb R} h(\beta + it)\,dt.$$ -/
lemma integral_vertical_eq_of_decay {h : ℂ → ℂ} {β α : ℝ} (hβα : β ≤ α)
    (hd : DifferentiableOn ℂ h {s : ℂ | β ≤ s.re ∧ s.re ≤ α})
    {A : ℝ} (hA : ∀ s : ℂ, β ≤ s.re → s.re ≤ α → ‖h s‖ ≤ A / (1 + s.im ^ 2)) :
    ∫ t : ℝ, h (α + t * I) = ∫ t : ℝ, h (β + t * I) := by
  have hA0 : 0 ≤ A := by
    have := le_trans (norm_nonneg _) (hA (β : ℂ) (by simp) (by simpa using hβα))
    simpa using this
  have hint : ∀ σ : ℝ, β ≤ σ → σ ≤ α → Integrable (fun t : ℝ => h (σ + t * I)) := by
    intro σ h1 h2
    have hc : Continuous (fun t : ℝ => h (σ + t * I)) :=
      hd.continuousOn.comp_continuous (by fun_prop) (fun t => ⟨by simpa using h1, by simpa using h2⟩)
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul A) hc.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have := hA (σ + t * I) (by simpa using h1) (by simpa using h2)
    simpa [div_eq_mul_inv] using this
  have hhor : ∀ c : ℝ, ‖∫ x : ℝ in β..α, h (x + c * I)‖ ≤ A / (1 + c ^ 2) * |α - β| := by
    intro c
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hβα] at hx
    have := hA (x + c * I) (by simpa using hx.1.le) (by simpa using hx.2)
    simpa using this
  have hrect : ∀ T : ℝ, (∫ x : ℝ in β..α, h (x + (-T : ℝ) * I)) - (∫ x : ℝ in β..α, h (x + T * I))
      + I • (∫ y : ℝ in (-T)..T, h (α + y * I)) - I • (∫ y : ℝ in (-T)..T, h (β + y * I)) = 0 := by
    intro T
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn h (β + (-T : ℝ) * I)
      (α + T * I) (hd.mono (by
        intro s hs
        rw [Complex.mem_reProdIm] at hs
        have h1 := hs.1
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at h1
        rw [Set.uIcc_of_le hβα] at h1
        exact h1))
    simpa using this
  have hv : ∀ σ : ℝ, β ≤ σ → σ ≤ α →
      Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, h (σ + y * I)) atTop
        (𝓝 (∫ t : ℝ, h (σ + t * I))) := fun σ h1 h2 =>
    intervalIntegral_tendsto_integral (hint σ h1 h2) tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => I • (∫ y : ℝ in (-T)..T, h (α + y * I))
      - I • (∫ y : ℝ in (-T)..T, h (β + y * I))) atTop
      (𝓝 (I • (∫ t : ℝ, h (α + t * I)) - I • (∫ t : ℝ, h (β + t * I)))) :=
    ((hv α hβα le_rfl).const_smul I).sub ((hv β le_rfl hβα).const_smul I)
  have hsq : Tendsto (fun T : ℝ => 1 + T ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have hg : Tendsto (fun T : ℝ => 2 * (A / (1 + T ^ 2) * |α - β|)) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := A)).div_atTop hsq).mul_const |α - β|
    simpa using this.const_mul 2
  have hzero : Tendsto (fun T : ℝ => I • (∫ y : ℝ in (-T)..T, h (α + y * I))
      - I • (∫ y : ℝ in (-T)..T, h (β + y * I))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_) hg
    have h0 := hrect T
    have e : I • (∫ y : ℝ in (-T)..T, h (α + y * I)) - I • (∫ y : ℝ in (-T)..T, h (β + y * I))
        = (∫ x : ℝ in β..α, h (x + T * I)) - (∫ x : ℝ in β..α, h (x + (-T : ℝ) * I)) := by
      linear_combination h0
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have a1 := hhor T
    have a2 := hhor (-T)
    simp only [neg_sq] at a2
    linarith
  have := tendsto_nhds_unique hlim hzero
  have h3 : I • (∫ t : ℝ, h (α + t * I)) = I • (∫ t : ℝ, h (β + t * I)) := sub_eq_zero.1 this
  simpa using h3

end Miyake
