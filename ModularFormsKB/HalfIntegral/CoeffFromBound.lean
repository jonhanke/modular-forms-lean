/-
# Coefficient bounds from a bound on the function

If $f(\tau) = \sum_{n\ge0}a(n)e^{2\pi in\tau}$ on $\mathbb H$ and
$|f(\tau)| \le B(\operatorname{Im}\tau)^{-e}$, then $|a(n)| \le e^{2\pi}Bn^e$ for $n \ge 1$: the coefficient is
$a(n) = \int_0^1 f(x+iy)e^{-2\pi in(x+iy)}\,dx$, taken at height $y = 1/n$ (Mathlib's
`UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral` with period $1$, and `UpperHalfPlane.qExpansion_coeff_unique` to
identify $a$ with Mathlib's $q$-expansion).
-/
import ModularFormsKB.HalfIntegral.Abstract.Multiplier
import Mathlib.NumberTheory.ModularForms.Bounds

namespace ModularFormsKB.HalfIntegral

open Complex Asymptotics Filter UpperHalfPlane
open scoped Real Manifold

/-- **Coefficients from a bound on the function** (the last step of Hecke's argument, Iwaniec 1997 `iwaniec1997`, §5
[unverified]): if $f = \sum a(n)q^n$ on $\mathbb H$ and $|f(\tau)| \le B(\operatorname{Im}\tau)^{-e}$, then
$|a(n)| \le e^{2\pi}Bn^e$ for every $n \ge 1$. -/
theorem norm_coeff_le_of_norm_le {f : UpperHalfPlane → ℂ} {a : ℕ → ℂ} (hf : MDiff f) (ha : Abstract.HasQExp f a) {e B : ℝ}
    (hB : ∀ τ : UpperHalfPlane, ‖f τ‖ ≤ B * τ.im ^ (-e)) {n : ℕ} (hn : 1 ≤ n) :
    ‖a n‖ ≤ Real.exp (2 * π) * B * (n : ℝ) ^ e := by
  have hq : ∀ τ : UpperHalfPlane,
      HasSum (fun m ↦ a m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
    intro τ
    convert ha τ using 2 with m
    rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1 := by
    intro z
    rcases le_or_gt z.im 0 with hz | hz
    · simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hz,
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (by simpa using hz : (z + 1).im ≤ 0)]
    · have h1 : 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz,
        UpperHalfPlane.ofComplex_apply_of_im_pos h1]
      refine (ha ⟨z + 1, h1⟩).unique ?_
      convert ha ⟨z, hz⟩ using 2 with m
      simp only [mul_add, Complex.exp_add]
      have : Complex.exp (2 * π * Complex.I * m) = 1 := by
        rw [show (2 * π * Complex.I * m : ℂ) = (m : ℂ) * (2 * π * Complex.I) by ring]
        exact Complex.exp_nat_mul_two_pi_mul_I m
      rw [mul_one, this, mul_one]
  have hbdd := UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion one_pos hq
  have hcoef : a n = (UpperHalfPlane.qExpansion 1 f).coeff n :=
    let _ : FunLike (ℍ → ℂ) ℍ ℂ := ⟨id, fun _ _ h ↦ h⟩
    UpperHalfPlane.qExpansion_coeff_unique f one_pos
      (UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hper hf hbdd) hq n
  have hB0 : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hB UpperHalfPlane.I)
    simpa using h1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [hcoef, UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral one_pos hper hf hbdd n
    (t := 1 / n) (by positivity)]
  have key : ∀ u : ℝ, ‖1 / Function.Periodic.qParam 1 ((u : ℂ) + (1 / n : ℝ) * Complex.I) ^ n *
      f ⟨(u : ℂ) + (1 / n : ℝ) * Complex.I, by simpa using hnpos⟩‖ ≤
      Real.exp (2 * π) * B * (n : ℝ) ^ e := by
    intro u
    rw [norm_mul, norm_div, norm_one, norm_pow, Function.Periodic.norm_qParam]
    have him : (⟨(u : ℂ) + (1 / n : ℝ) * Complex.I, by simpa using hnpos⟩ :
        UpperHalfPlane).im = 1 / n := by simp
    have h2 := hB ⟨(u : ℂ) + (1 / n : ℝ) * Complex.I, by simpa using hnpos⟩
    rw [him] at h2
    have h3 : ((1 : ℝ) / n) ^ (-e) = (n : ℝ) ^ e := by
      rw [Real.rpow_neg (by positivity), one_div, Real.inv_rpow hnpos.le, inv_inv]
    rw [h3] at h2
    have him' : ((u : ℂ) + (1 / n : ℝ) * Complex.I).im = 1 / n := by simp
    have h4 : 1 / Real.exp (-2 * π * ((u : ℂ) + (1 / n : ℝ) * Complex.I).im / 1) ^ n =
        Real.exp (2 * π) := by
      rw [him', ← Real.exp_nat_mul, one_div, ← Real.exp_neg]
      congr 1
      field_simp
    rw [h4, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  rw [norm_mul]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun u : ℝ ↦ 1 / Function.Periodic.qParam 1 ((u : ℂ) + (1 / n : ℝ) * Complex.I) ^ n *
      f ⟨(u : ℂ) + (1 / n : ℝ) * Complex.I, by simpa using hnpos⟩)
    (C := Real.exp (2 * π) * B * (n : ℝ) ^ e) (fun u _ ↦ key u)
  simpa using this

end ModularFormsKB.HalfIntegral
