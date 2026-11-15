/-
# A growth bound for $\theta$ near the real axis

For $w \in \mathbb H$ we show $|\theta(w)| \le C\,(1 + 1/\sqrt{\operatorname{Im} w})$ with an absolute constant $C$
(here $C = 3$). With $b = 2\pi\operatorname{Im} w$ and $s = \sqrt b$, the proof uses
$\|\theta(w)\| \le 1 + 2\sum_{n\ge1} e^{-b n^2}$, the elementary inequality $-b n^2 \le 1 - 2sn$
(from $(sn-1)^2\ge0$), so that $e^{-bn^2} \le e\,x^n$ with $x = e^{-2s}$, and then
$\sum_{n\ge1} x^n = x/(1-x) \le 1/(2s)$ (from $1 + 2s \le e^{2s}$).
-/
import ModularFormsKB.HalfIntegral.Theta
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

/-- Termwise bound $e^{-b k^2} \le e\,(e^{-2\sqrt b})^k$ for $b > 0$. -/
theorem exp_neg_mul_sq_le (b : ℝ) (hb : 0 ≤ b) (k : ℕ) :
    Real.exp (-b * (k : ℝ) ^ 2) ≤ Real.exp 1 * (Real.exp (-2 * Real.sqrt b)) ^ k := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [sq_nonneg (Real.sqrt b * k - 1)]

/-- For $s > 0$ and $x = e^{-2s}$, $x/(1-x) \le 1/(2s)$. -/
theorem geom_le_inv (s : ℝ) (hs : 0 < s) :
    Real.exp (-2 * s) / (1 - Real.exp (-2 * s)) ≤ 1 / (2 * s) := by
  have hx : Real.exp (-2 * s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1 : 0 < 1 - Real.exp (-2 * s) := by linarith
  rw [div_le_div_iff₀ h1 (by linarith)]
  have h2 : 2 * s + 1 ≤ Real.exp (2 * s) := Real.add_one_le_exp _
  have h3 : Real.exp (-2 * s) * Real.exp (2 * s) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-2 * s) := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left h2 h4.le]

/-- **Growth bound** $\|\theta(w)\| \le C\,(1 + 1/\sqrt{\operatorname{Im} w})$ on $\mathbb H$ (one can take $C = 3$). -/
theorem norm_theta_le :
    ∃ C : ℝ, ∀ w : ℂ, 0 < w.im → ‖theta w‖ ≤ C * (1 + 1 / Real.sqrt w.im) := by
  refine ⟨3, fun w hw => ?_⟩
  have hτ : 0 < (2 * w).im := by simpa using hw
  set b : ℝ := π * (2 * w).im with hbdef
  have hb : 0 < b := by positivity
  set s : ℝ := Real.sqrt b with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hb
  set x : ℝ := Real.exp (-2 * s) with hxdef
  have hx1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hx0 : 0 < x := Real.exp_pos _
  have hterm : ∀ n : ℕ, ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * w))‖ ≤ Real.exp 1 * x ^ (n + 1) := by
    intro n
    refine le_trans ?_ (exp_neg_mul_sq_le b hb.le (n + 1))
    rw [Complex.norm_exp]
    apply le_of_eq
    congr 1
    have : (π * I * ((n : ℂ) + 1) ^ 2 * (2 * w) : ℂ)
        = ((π * ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) * ((2 * w) * I) := by push_cast; ring
    rw [this, re_ofReal_mul, mul_I_re]
    push_cast
    rw [hbdef]
    ring
  have hsum : HasSum (fun n : ℕ => Real.exp 1 * x ^ (n + 1)) (Real.exp 1 * (x / (1 - x))) := by
    have : HasSum (fun n : ℕ => x ^ (n + 1)) (x / (1 - x)) := by
      simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff hx0.ne']
      exact hasSum_geometric_of_lt_one hx0.le hx1
    exact this.mul_left _
  have aux : Summable fun n : ℕ => ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * w))‖ :=
    .of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum.summable
  have htail : ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * w))‖
      ≤ Real.exp 1 * (x / (1 - x)) :=
    (norm_tsum_le_tsum_norm aux).trans ((aux.tsum_mono hsum.summable hterm).trans_eq hsum.tsum_eq)
  have hgeom : x / (1 - x) ≤ 1 / (2 * s) := geom_le_inv s hs
  have hexp : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_three
    linarith
  -- 1/s ≤ 1/√(Im w)
  have hsq : Real.sqrt w.im ≤ s := by
    rw [hsdef]
    apply Real.sqrt_le_sqrt
    rw [hbdef]
    have : (2 * w).im = 2 * w.im := by simp
    rw [this]
    nlinarith [Real.pi_gt_three, hw]
  have hsy : 0 < Real.sqrt w.im := Real.sqrt_pos.mpr hw
  have hinv : 1 / s ≤ 1 / Real.sqrt w.im := one_div_le_one_div_of_le hsy hsq
  have hmain : ‖theta w‖ ≤ 1 + 2 * (Real.exp 1 * (1 / (2 * s))) := by
    have e : theta w = 1 + 2 * ∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * w)) :=
      jacobiTheta_eq_tsum_nat hτ
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, Complex.norm_two]
    have : 2 * ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * (2 * w))‖
        ≤ 2 * (Real.exp 1 * (1 / (2 * s))) := by
      gcongr
      exact htail.trans (by gcongr)
    linarith
  have h5 : 2 * (Real.exp 1 * (1 / (2 * s))) = Real.exp 1 * (1 / s) := by
    field_simp
  rw [h5] at hmain
  have h6 : Real.exp 1 * (1 / s) ≤ 3 * (1 / Real.sqrt w.im) := by
    have : 0 < 1 / s := by positivity
    calc Real.exp 1 * (1 / s) ≤ 3 * (1 / s) := by gcongr
      _ ≤ 3 * (1 / Real.sqrt w.im) := by gcongr
  linarith

end ModularFormsKB.HalfIntegral
