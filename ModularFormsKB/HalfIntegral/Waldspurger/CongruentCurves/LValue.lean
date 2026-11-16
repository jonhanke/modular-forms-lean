/-
# The value $L(E_n, 1)$ of the true $L$-function, and vanishing from a functional equation

`LValueAtOne` and its two basic lemmas were in `Criterion.lean`; they were moved here so that the root-number file
(`RootNumber.lean`) can use them.

`LValueAtOne n v`: every continuation of the $L$-series of Mathlib's $E_n$ to a connected open set containing $1$
takes the value $v$ at $1$ (the form of Tau Ceti's `WeierstrassCurve.BirchSwinnertonDyer`).

`lValueAtOne_zero_of_functionalEquation`: if
$\Lambda(s) = (2\pi/\sqrt N)^{-s}\Gamma(s) L(s)$ (Miyake's `completedL`) for $\operatorname{Re} s$ large continues
to an entire function with $\Lambda(2 - s) = -\Lambda(s)$, then $L(E_n, 1) = 0$.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.CongruentL
import ModularFormsKB.Miyake.Sec4_3.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex
open scoped Real

/-- **$L(E_n, 1) = v$**: every continuation of the $L$-series of Mathlib's $E_n$ to a connected open set containing
$1$ takes the value $v$ at $1$ (the form of Tau Ceti's `WeierstrassCurve.BirchSwinnertonDyer`). -/
def LValueAtOne (n : ℕ) (v : ℂ) : Prop :=
  ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄, LSeries.IsContinuationOn (lCoeff n) F U → 1 ∈ U → F 1 = v

/-- The value at $1$ of an entire continuation is $L(E_n, 1)$. -/
theorem lValueAtOne_of_univ {n : ℕ} {G : ℂ → ℂ} (hG : LSeries.IsContinuationOn (lCoeff n) G Set.univ) :
    LValueAtOne n (G 1) := fun _ U hF h1 ↦ hF.eqOn_of_subset hG (Set.subset_univ U) h1

theorem LValueAtOne.eq_of_univ {n : ℕ} {v : ℂ} (h : LValueAtOne n v) {G : ℂ → ℂ}
    (hG : LSeries.IsContinuationOn (lCoeff n) G Set.univ) : G 1 = v :=
  h hG (Set.mem_univ 1)

/-- **The functional equation of $L(E_n, s)$ with sign $w$** (in Miyake's normalization, conductor $N$):
$\Lambda(s) = (2\pi/\sqrt N)^{-s}\Gamma(s)L(E_n, s)$ for $\operatorname{Re} s$ large continues to an entire function
with $\Lambda(2 - s) = w\,\Lambda(s)$. -/
def CongruentFE (n : ℕ) (N : ℝ) (w : ℂ) : Prop :=
  ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → Λ s = Miyake.completedL N (lCoeff n) s) ∧
    ∀ s : ℂ, Λ (2 - s) = w * Λ s

/-- An entire function agreeing with `LSeries a` on some half-plane `Re s > c` is an entire continuation (the
identity principle; the argument of Tau Ceti's `LSeries.HasEntireExtension.of_extension_of_eq_on_lt_re`). -/
theorem isContinuationOn_univ_of_eq_on_lt_re {a : ℕ → ℂ} {F : ℂ → ℂ} {c : ℝ}
    (h_finite : LSeries.abscissaOfAbsConv a < ⊤) (hF : Differentiable ℂ F)
    (hFa : ∀ {s : ℂ}, c < s.re → F s = LSeries a s) : LSeries.IsContinuationOn a F Set.univ := by
  refine ⟨isOpen_univ, isPreconnected_univ, Complex.analyticOnNhd_univ_iff_differentiable.mpr hF, ?_,
    fun s _ hs ↦ ?_⟩
  · obtain ⟨σ, hσ, -⟩ := EReal.exists_between_coe_real h_finite
    exact ⟨((σ + 1 : ℝ) : ℂ), Set.mem_univ _, lt_of_lt_of_le hσ (by simp; exact_mod_cast (le_add_of_nonneg_right zero_le_one : σ ≤ σ + 1))⟩
  obtain ⟨σ, hσ_abs, hσ_s⟩ := EReal.exists_between_coe_real hs
  have hσ_s' : (σ : ℝ) < s.re := by exact_mod_cast hσ_s
  set W : Set ℂ := {z : ℂ | (σ : ℝ) < z.re} with hW_def
  have hW_sub : ∀ z ∈ W, LSeries.abscissaOfAbsConv a < (z.re : EReal) := fun z hz ↦
    lt_of_lt_of_le hσ_abs (by exact_mod_cast (hz : (σ : ℝ) < z.re).le)
  have hL : AnalyticOnNhd ℂ (LSeries a) W := (LSeries_analyticOnNhd a).mono hW_sub
  have hFW : AnalyticOnNhd ℂ F W :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).mono (Set.subset_univ W)
  set z₀ : ℂ := ((max σ c + 1 : ℝ) : ℂ) with hz₀_def
  have hz₀W : z₀ ∈ W := by
    simp only [hW_def, Set.mem_ofPred_eq, hz₀_def, Complex.ofReal_re]
    have := le_max_left σ c
    linarith
  have hfg : F =ᶠ[nhds z₀] LSeries a := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{z : ℂ | (max σ c : ℝ) < z.re},
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_, fun z hz ↦ ?_⟩
    · simp only [Set.mem_ofPred_eq, hz₀_def, Complex.ofReal_re]
      linarith
    · exact hFa (lt_of_le_of_lt (le_max_right σ c) hz)
  have hconn : IsPreconnected W := (convex_halfSpace_re_gt σ).isPreconnected
  exact hFW.eqOn_of_preconnected_of_eventuallyEq hL hconn hz₀W hfg hσ_s'

/-- **Sign $-1$ forces $L(E_n, 1) = 0$**: $\Lambda(1) = -\Lambda(1)$, and
$L = \Lambda\,(2\pi/\sqrt N)^{s}/\Gamma(s)$ is an entire continuation of the $L$-series. -/
theorem lValueAtOne_zero_of_congruentFE {n : ℕ} [NeZero n] (hsq : Squarefree n) {N : ℝ} (hN : 0 < N)
    (hfe : CongruentFE n N (-1)) : LValueAtOne n 0 := by
  obtain ⟨Λ, hΛ, ⟨σ₀, hσ⟩, hsym⟩ := hfe
  set c : ℂ := ((2 * π / √N : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, ofReal_ne_zero]; have := Real.pi_pos; have := Real.sqrt_pos.mpr hN; positivity
  set G : ℂ → ℂ := fun s ↦ Λ s * c ^ s * (Gamma s)⁻¹ with hG
  have hGd : Differentiable ℂ G :=
    (hΛ.mul fun s ↦ (differentiableAt_id.const_cpow (Or.inl hc0))).mul
      Complex.differentiable_one_div_Gamma
  have habs : LSeries.abscissaOfAbsConv (lCoeff n) < ⊤ :=
    lt_of_le_of_lt (abscissaOfAbsConv_lCoeff_le hsq) (EReal.coe_lt_top 2)
  have hcont : LSeries.IsContinuationOn (lCoeff n) G Set.univ := by
    refine isContinuationOn_univ_of_eq_on_lt_re (c := max σ₀ 0) habs hGd fun {s} hs ↦ ?_
    have hs0 : 0 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    have hΓ : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
    rw [hG]
    simp only
    rw [hσ s (lt_of_le_of_lt (le_max_left _ _) hs), Miyake.completedL, ← hc, cpow_neg]
    have hcs : c ^ s ≠ 0 := (cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h; rw [h] at hs0; simp at hs0)).mpr hc0
    field_simp
  have h1 : Λ 1 = 0 := by
    have := hsym 1
    norm_num at this
    linear_combination this / 2
  have := lValueAtOne_of_univ hcont
  simpa [G, h1] using this

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
