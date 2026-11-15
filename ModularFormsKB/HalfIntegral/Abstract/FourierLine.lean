/-
# Fourier coefficients on a horizontal line

Groundwork for unfolding Petersson products against Poincaré series. If
$g(\tau) = \sum_{n\ge0} c(n)e^{2\pi i n\tau}$ on $\mathbb H$, the series converges absolutely on every horizontal line
(`summable_of_hasQExp`), and $\int_0^1 \overline{g(u+iv)}\,e^{2\pi i m(u+iv)}\,du = \overline{c(m)}\,e^{-4\pi m v}$
(`integral_conj_mul_exp_of_hasQExp`).
-/
import ModularFormsKB.HalfIntegral.Abstract.Multiplier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

/-- On the line $\operatorname{Im}\tau = v > 0$ the $q$-series converges absolutely. -/
theorem summable_of_hasQExp {g : UpperHalfPlane → ℂ} {c : ℕ → ℂ} (hg : Abstract.HasQExp g c) {v : ℝ} (hv : 0 < v) :
    Summable fun n : ℕ ↦ ‖c n‖ * Real.exp (-2 * π * n * v) := by
  have hpos : 0 < (((v / 2 : ℝ) : ℂ) * I).im := by simpa using half_pos hv
  have h := (hg ⟨((v / 2 : ℝ) : ℂ) * I, hpos⟩).summable.tendsto_atTop_zero
  have hnorm : ∀ n : ℕ, ‖c n * cexp (2 * π * I * n * (⟨((v / 2 : ℝ) : ℂ) * I, hpos⟩ : UpperHalfPlane))‖
      = ‖c n‖ * Real.exp (-π * n * v) := by
    intro n
    rw [norm_mul, Complex.norm_exp]
    congr 2
    have : (2 * π * I * n * (((v / 2 : ℝ) : ℂ) * I) : ℂ) = ((-π * n * v : ℝ) : ℂ) := by
      push_cast
      have : I * I = -1 := I_mul_I
      linear_combination (π * n * (v / 2)) * 2 * this
    rw [this, Complex.ofReal_re]
  have hb := h.norm.bddAbove_range
  obtain ⟨C, hC⟩ := hb
  have hC' : ∀ n : ℕ, ‖c n‖ * Real.exp (-π * n * v) ≤ C := by
    intro n
    calc _ = _ := (hnorm n).symm
      _ ≤ C := hC ⟨n, rfl⟩
  have hr : Summable fun n : ℕ ↦ C * (Real.exp (-π * v)) ^ n := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one (Real.exp_pos _).le
    refine lt_of_lt_of_eq (Real.exp_lt_exp.2 ?_) Real.exp_zero
    have := Real.pi_pos
    nlinarith
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hr
  have e1 : Real.exp (-2 * π * n * v) = Real.exp (-π * n * v) * Real.exp (-π * n * v) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : (Real.exp (-π * v)) ^ n = Real.exp (-π * n * v) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [e2, e1, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC' n) (Real.exp_pos _).le

/-- **The $m$-th Fourier coefficient on a horizontal line.** -/
theorem integral_conj_mul_exp_of_hasQExp {g : UpperHalfPlane → ℂ} {c : ℕ → ℂ} (hg : Abstract.HasQExp g c)
    {v : ℝ} (hv : 0 < v) (m : ℕ) :
    ∫ u in (0 : ℝ)..1, (starRingEnd ℂ) (g ⟨u + v * I, by simpa using hv⟩) * cexp (2 * π * I * m * (u + v * I)) =
      (starRingEnd ℂ) (c m) * Real.exp (-4 * π * m * v) := by
  set F : ℕ → ℝ → ℂ := fun n u ↦ (starRingEnd ℂ) (c n) * (Real.exp (-2 * π * (n + m) * v) : ℝ) *
    cexp (2 * π * I * ((m : ℂ) - n) * u) with hF
  have hFeq : ∀ n : ℕ, ∀ u : ℝ, (starRingEnd ℂ) (c n * cexp (2 * π * I * n * ((u : ℂ) + v * I))) *
      cexp (2 * π * I * m * (u + v * I)) = F n u := by
    intro n u
    simp only [hF]
    have key : (starRingEnd ℂ) (2 * π * I * n * ((u : ℂ) + v * I)) + 2 * π * I * m * (u + v * I)
        = ((-2 * π * (n + m) * v : ℝ) : ℂ) + 2 * π * I * ((m : ℂ) - n) * u := by
      simp only [map_mul, map_add, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
      push_cast
      linear_combination (2 * π * (n + m) * v) * I_sq
    rw [map_mul, ← Complex.exp_conj, mul_assoc, ← Complex.exp_add, key, Complex.exp_add,
      Complex.ofReal_exp]
    ring
  have hsum : ∀ u : ℝ, HasSum (fun n => F n u)
      ((starRingEnd ℂ) (g ⟨u + v * I, by simpa using hv⟩) * cexp (2 * π * I * m * (u + v * I))) := by
    intro u
    have := ((Complex.hasSum_conj'.mpr (hg ⟨u + v * I, by simpa using hv⟩)).mul_right
      (cexp (2 * π * I * m * (u + v * I))))
    convert this using 1
    funext n
    exact (hFeq n u).symm
  have hnormF : ∀ n u, ‖F n u‖ = ‖c n‖ * Real.exp (-2 * π * (n + m) * v) := by
    intro n u
    simp only [hF, norm_mul, Complex.norm_real, RCLike.norm_conj, Complex.norm_exp]
    have : (2 * π * I * ((m : ℂ) - n) * u).re = 0 := by simp
    rw [this, Real.exp_zero, mul_one, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hbs : Summable fun n : ℕ ↦ ‖c n‖ * Real.exp (-2 * π * (n + m) * v) := by
    have := (summable_of_hasQExp hg hv).mul_right (Real.exp (-2 * π * m * v))
    refine this.congr fun n ↦ ?_
    rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := 1) (F := F)
    (fun n _ ↦ ‖c n‖ * Real.exp (-2 * π * (n + m) * v))
    (fun n ↦ (by simp only [hF]; fun_prop : Continuous (F n)).aestronglyMeasurable)
    (fun n ↦ Filter.Eventually.of_forall fun t _ ↦ (hnormF n t).le)
    (Filter.Eventually.of_forall fun t _ ↦ hbs)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ ↦ hsum t)
  have hint : ∀ n : ℕ, ∫ u in (0:ℝ)..1, F n u =
      if n = m then (starRingEnd ℂ) (c m) * Real.exp (-4 * π * m * v) else 0 := by
    intro n
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    by_cases h : n = m
    · subst h
      simp only [ite_true, sub_self, mul_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
      simp only [sub_zero, one_smul, mul_one]
      have : Real.exp (-2 * π * (n + n) * v) = Real.exp (-4 * π * n * v) := by ring_nf
      rw [this]
    · rw [if_neg h]
      have hk : (2 * π * I * ((m : ℂ) - n)) ≠ 0 := by
        have : (m : ℂ) - n ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast Ne.symm h
        simp [Real.pi_ne_zero, this]
      have := integral_exp_mul_complex (a := (0:ℝ)) (b := 1) hk
      have h1 : cexp (2 * π * I * ((m : ℂ) - n)) = 1 := by
        have := Complex.exp_int_mul_two_pi_mul_I ((m : ℤ) - n)
        convert this using 2
        push_cast; ring
      rw [this]
      simp [h1]
  rw [show (fun n : ℕ ↦ ∫ u in (0:ℝ)..1, F n u) = fun n : ℕ ↦
    (if n = m then (starRingEnd ℂ) (c m) * Real.exp (-4 * π * m * v) else 0) from funext hint] at hdom
  exact hdom.unique (hasSum_ite_eq m _)

end ModularFormsKB.HalfIntegral
