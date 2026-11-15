/-
# The cocycle property of the theta multiplier on $\Gamma_0(4)$

For $\gamma_1, \gamma_2 \in \Gamma_0(4)$ and $\tau \in \mathbb H$,
$$j(\gamma_1\gamma_2, \tau) = j(\gamma_1, \gamma_2\tau)\, j(\gamma_2, \tau)$$
(`thetaMult_mul`), where $j$ is `thetaMult`.

**Route.** The transformation law (`theta_transformationLaw`) applied to $\gamma_1\gamma_2$, and to $\gamma_2$ then $\gamma_1$,
gives $j(\gamma_1\gamma_2,\tau)\,\theta(\tau) = j(\gamma_1,\gamma_2\tau)\,j(\gamma_2,\tau)\,\theta(\tau)$. Since $\theta$ does not
vanish on $\{\operatorname{Im} z > 1\}$ (`theta_ne_zero_of_one_lt_im`, from $\|\vartheta - 1\| < 1$), the two sides agree there.
Both sides are holomorphic on $\mathbb H$ (`thetaMult_differentiableOn`), hence analytic, and $\mathbb H$ is connected, so the
identity theorem extends the equality to all of $\mathbb H$.
-/
import ModularFormsKB.HalfIntegral.ThetaForms

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane
open scoped Real

/-- $\theta(z) \ne 0$ for $\operatorname{Im} z > 1$: indeed $\|\vartheta(2z) - 1\| < 1$ there. -/
theorem theta_ne_zero_of_one_lt_im {z : ℂ} (hz : 1 < z.im) : theta z ≠ 0 := by
  intro h0
  have him : 0 < (2 * z).im := by simp; linarith
  have hb := norm_jacobiTheta_sub_one_le him
  have hx : (2 * z).im = 2 * z.im := by simp
  have hpi := Real.pi_gt_three
  set x := Real.exp (-π * (2 * z).im) with hxdef
  have hx6 : x < 1 / 6 := by
    have h1 : 6 < π * (2 * z).im := by rw [hx]; nlinarith
    have h2 : (π * (2 * z).im) + 1 ≤ Real.exp (π * (2 * z).im) := Real.add_one_le_exp _
    have h3 : x = (Real.exp (π * (2 * z).im))⁻¹ := by
      rw [hxdef, ← Real.exp_neg]; ring_nf
    rw [h3, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hx0 : 0 < x := Real.exp_pos _
  have h1 : theta z = jacobiTheta (2 * z) := rfl
  rw [h1] at h0
  rw [h0, zero_sub, norm_neg, norm_one] at hb
  have h2 : 2 / (1 - x) * x < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one (by linarith)]
    linarith
  linarith

/-- The multiplier $z \mapsto j(\gamma, z)$ is holomorphic on $\mathbb H$. -/
theorem thetaMult_differentiableOn (γ : SL(2, ℤ)) :
    DifferentiableOn ℂ (thetaMult γ) {z : ℂ | 0 < z.im} := by
  intro z hz
  unfold thetaMult thetaMultCD
  by_cases hc : γ 1 0 = 0
  · simp only [hc, Int.cast_zero, zero_mul, zero_add]
    exact (differentiableAt_const _).differentiableWithinAt
  · apply DifferentiableAt.differentiableWithinAt
    have hs : ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ∈ Complex.slitPlane := by
      right
      simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero]
      have : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast hc
      exact mul_ne_zero this (ne_of_gt hz)
    have h1 : DifferentiableAt ℂ (fun w : ℂ => (γ 1 0 : ℂ) * w + (γ 1 1 : ℂ)) z := by fun_prop
    exact (differentiableAt_const _).mul
      (h1.cpow (differentiableAt_const _) hs)

/-- **The cocycle property of the theta multiplier:** $j(\gamma_1\gamma_2,\tau) = j(\gamma_1,\gamma_2\tau)\,j(\gamma_2,\tau)$
for $\gamma_1,\gamma_2\in\Gamma_0(4)$, $\tau\in\mathbb H$. -/
theorem thetaMult_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 4) (h₂ : γ₂ ∈ Gamma0 4) (τ : ℍ) :
    thetaMult (γ₁ * γ₂) τ = thetaMult γ₁ ↑(γ₂ • τ) * thetaMult γ₂ τ := by
  set S : Set ℂ := {z : ℂ | 0 < z.im} with hS
  have hSo : IsOpen S := isOpen_lt continuous_const Complex.continuous_im
  -- the Möbius map of `γ₂` on `ℂ`
  set M : ℂ → ℂ := fun z => ((γ₂ 0 0 : ℂ) * z + (γ₂ 0 1 : ℂ)) / ((γ₂ 1 0 : ℂ) * z + (γ₂ 1 1 : ℂ)) with hM
  have hMτ : ∀ σ : ℍ, ((γ₂ • σ : ℍ) : ℂ) = M σ := by
    intro σ
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [hM]
  have hden : ∀ z ∈ S, (γ₂ 1 0 : ℂ) * z + (γ₂ 1 1 : ℂ) ≠ 0 := by
    intro z hz h0
    have him := congrArg Complex.im h0
    simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im] at him
    have hc : γ₂ 1 0 = 0 := by
      have : (γ₂ 1 0 : ℝ) = 0 := by
        rcases mul_eq_zero.mp him with h | h
        · exact h
        · exact absurd h (ne_of_gt hz)
      exact_mod_cast this
    have hre := congrArg Complex.re h0
    simp only [hc, Int.cast_zero, zero_mul, zero_add, intCast_re, zero_re] at hre
    have hd : γ₂ 1 1 = 0 := by exact_mod_cast hre
    have := det_entries γ₂
    rw [hc, hd] at this
    simp at this
  have hMS : ∀ z ∈ S, M z ∈ S := by
    intro z hz
    have := (γ₂ • (⟨z, hz⟩ : ℍ)).im_pos
    rw [← coe_im] at this
    rw [hMτ] at this
    simpa [hS] using this
  have hMd : DifferentiableOn ℂ M S := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have := hden z hz
    simp only [hM]
    fun_prop (disch := assumption)
  set F : ℂ → ℂ := thetaMult (γ₁ * γ₂) with hF
  set G : ℂ → ℂ := fun z => thetaMult γ₁ (M z) * thetaMult γ₂ z with hG
  have hFd : DifferentiableOn ℂ F S := thetaMult_differentiableOn _
  have hGd : DifferentiableOn ℂ G S :=
    ((thetaMult_differentiableOn γ₁).comp hMd hMS).mul (thetaMult_differentiableOn γ₂)
  have hFa : AnalyticOnNhd ℂ F S := hFd.analyticOnNhd hSo
  have hGa : AnalyticOnNhd ℂ G S := hGd.analyticOnNhd hSo
  -- equality for `Im > 1`
  have hbig : ∀ z : ℂ, 1 < z.im → F z = G z := by
    intro z hz
    have hz0 : 0 < z.im := by linarith
    set σ : ℍ := ⟨z, hz0⟩ with hσ
    have e1 := theta_transformationLaw (γ₁ * γ₂) (mul_mem h₁ h₂) σ
    have e2 := theta_transformationLaw γ₁ h₁ (γ₂ • σ)
    have e3 := theta_transformationLaw γ₂ h₂ σ
    have hne : theta σ ≠ 0 := theta_ne_zero_of_one_lt_im hz
    have key : thetaMult (γ₁ * γ₂) σ * theta σ
        = thetaMult γ₁ ↑(γ₂ • σ) * thetaMult γ₂ σ * theta σ := by
      rw [← e1, mul_smul, e2, e3]; ring
    have := mul_right_cancel₀ hne key
    simp only [hF, hG]
    rw [← hMτ σ]
    exact this
  have hev : F =ᶠ[nhds (2 * Complex.I : ℂ)] G := by
    have : {z : ℂ | 1 < z.im} ∈ nhds (2 * Complex.I : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp)
    filter_upwards [this] with z hz using hbig z hz
  have hconn : IsPreconnected S := (convex_halfSpace_im_gt 0).isPreconnected
  have heq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa hconn (by simp [hS]) hev
  have := heq (show (τ : ℂ) ∈ S from τ.im_pos)
  simp only [hF, hG] at this
  rw [hMτ]; exact this

end ModularFormsKB.HalfIntegral
