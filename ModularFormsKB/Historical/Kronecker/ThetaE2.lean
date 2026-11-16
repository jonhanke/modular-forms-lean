import ModularFormsKB.Historical.Ramanujan.JacobiCube
import ModularFormsKB.Historical.Kronecker.AInvariance
import ModularFormsKB.Historical.Kronecker.E2Values
import Mathlib.Analysis.Calculus.SmoothSeries
import ModularFormsKB.Citation
/-!
# `ϑ'(0, w) = 2π η(w)³` and `ϑ'''(0, w) = -π² E₂(w) ϑ'(0, w)` for Kronecker's theta function

Kronecker, *Werke* 5 (1930), II, art. IV, pp. 146-147.  Termwise differentiation of
`ϑ(ζ, w) = ∑_{ν odd} e^{(ν² w + 4νζ - 2ν)πi/4}` in `ζ` and in `w`, Jacobi's cube identity
(`Ramanujan.jacobi_cube_hasSum`), and `η' = (πi/12) E₂ η` (Mathlib's `deriv_eta_eq_E2_mul_eta`).
-/

noncomputable section

open Complex
open scoped UpperHalfPlane
open scoped Real

namespace ModularFormsKB.Historical.Kronecker

/-- The `n`-th term of `kroneckerTheta`. -/
def thetaTerm (n : ℤ) (ζ w : ℂ) : ℂ :=
  cexp ((((2 * n + 1 : ℤ) : ℂ) ^ 2 * w + 4 * ((2 * n + 1 : ℤ) : ℂ) * ζ -
    2 * ((2 * n + 1 : ℤ) : ℂ)) * π * I / 4)

/-- `ν = 2n + 1` as a complex number. -/
def nuC (n : ℤ) : ℂ := ((2 * n + 1 : ℤ) : ℂ)

lemma kroneckerTheta_eq_tsum (ζ w : ℂ) : kroneckerTheta ζ w = ∑' n, thetaTerm n ζ w := rfl

lemma norm_thetaTerm (n : ℤ) (ζ w : ℂ) :
    ‖thetaTerm n ζ w‖ =
      Real.exp (-π * (((2 * n + 1 : ℤ) : ℝ) ^ 2 * w.im / 4 + ((2 * n + 1 : ℤ) : ℝ) * ζ.im)) := by
  unfold thetaTerm
  rw [Complex.norm_exp]
  congr 1
  have h : (((2 * n + 1 : ℤ) : ℂ)) = ((((2 * n + 1 : ℤ) : ℝ)) : ℂ) := by push_cast; ring
  rw [h]
  generalize ((2 * n + 1 : ℤ) : ℝ) = m
  simp [Complex.mul_re, Complex.mul_im, pow_two]
  ring

lemma norm_thetaTerm_le {S T : ℝ} {ζ w : ℂ} (hT : T ≤ w.im / 4) (hz : |ζ.im| ≤ 2 * S) (n : ℤ) :
    ‖thetaTerm n ζ w‖ ≤ Real.exp (-π * (T * ((2 * n + 1 : ℤ) : ℝ) ^ 2 - 2 * S * |((2 * n + 1 : ℤ) : ℝ)|)) := by
  rw [norm_thetaTerm, Real.exp_le_exp]
  generalize ((2 * n + 1 : ℤ) : ℝ) = m
  have h1 : T * m ^ 2 ≤ m ^ 2 * w.im / 4 := by nlinarith [sq_nonneg m]
  have h2 : -(|m| * |ζ.im|) ≤ m * ζ.im := by rw [← abs_mul]; exact neg_abs_le _
  have h3 : |m| * |ζ.im| ≤ |m| * (2 * S) := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have key : T * m ^ 2 - 2 * S * |m| ≤ m ^ 2 * w.im / 4 + m * ζ.im := by
    have : |m| * (2 * S) = 2 * S * |m| := by ring
    linarith
  have := mul_le_mul_of_nonneg_left key Real.pi_pos.le
  linarith

lemma summable_bound (S : ℝ) {T : ℝ} (hT : 0 < T) (k : ℕ) :
    Summable (fun n : ℤ ↦ (|((2 * n + 1 : ℤ) : ℝ)| ^ k : ℝ) *
      Real.exp (-π * (T * ((2 * n + 1 : ℤ) : ℝ) ^ 2 - 2 * S * |((2 * n + 1 : ℤ) : ℝ)|))) := by
  have hinj : Function.Injective (fun n : ℤ ↦ 2 * n + 1) := fun a b hab ↦ by
    have : 2 * a + 1 = 2 * b + 1 := hab
    omega
  have h := summable_pow_mul_jacobiTheta₂_term_bound S hT k
  have h2 := h.comp_injective hinj
  simpa only [Function.comp_def, Int.cast_abs] using h2

/-- The `k`-th `ζ`-derivative of the `n`-th term. -/
def gTerm (k : ℕ) (n : ℤ) (ζ w : ℂ) : ℂ := (π * I * nuC n) ^ k * thetaTerm n ζ w

lemma norm_nuC_term (n : ℤ) : ‖(π : ℂ) * I * nuC n‖ = π * |((2 * n + 1 : ℤ) : ℝ)| := by
  have h : nuC n = ((((2 * n + 1 : ℤ) : ℝ)) : ℂ) := by unfold nuC; push_cast; ring
  rw [h, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]

lemma norm_gTerm_le (k : ℕ) {S T : ℝ} {ζ w : ℂ} (hT : T ≤ w.im / 4) (hz : |ζ.im| ≤ 2 * S) (n : ℤ) :
    ‖gTerm k n ζ w‖ ≤ π ^ k * ((|((2 * n + 1 : ℤ) : ℝ)| ^ k : ℝ) *
      Real.exp (-π * (T * ((2 * n + 1 : ℤ) : ℝ) ^ 2 - 2 * S * |((2 * n + 1 : ℤ) : ℝ)|))) := by
  unfold gTerm
  rw [norm_mul, norm_pow, norm_nuC_term, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_thetaTerm_le hT hz n |> fun h ↦
    by exact mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)

lemma summable_gTerm (k : ℕ) (ζ : ℂ) {w : ℂ} (hw : 0 < w.im) : Summable fun n : ℤ ↦ gTerm k n ζ w :=
  Summable.of_norm_bounded
    ((summable_bound (|ζ.im| / 2) (T := w.im / 4) (by positivity) k).mul_left (π ^ k))
    (fun n ↦ norm_gTerm_le k (le_refl _) (by linarith) n)

lemma hasDerivAt_gTerm (k : ℕ) (n : ℤ) (ζ w : ℂ) :
    HasDerivAt (fun ζ ↦ gTerm k n ζ w) (gTerm (k + 1) n ζ w) ζ := by
  have hg : HasDerivAt (fun ζ : ℂ ↦ (nuC n ^ 2 * w + 4 * nuC n * ζ - 2 * nuC n) * ((π : ℂ) * I) / 4)
      (4 * nuC n * ((π : ℂ) * I) / 4) ζ := by
    have := ((((hasDerivAt_id ζ).const_mul (4 * nuC n)).const_add (nuC n ^ 2 * w)).sub_const
      (2 * nuC n)).mul_const ((π : ℂ) * I) |>.div_const 4
    refine this.congr_deriv ?_
    ring
  have h2 := (hg.cexp.const_mul ((π * I * nuC n) ^ k))
  have hf : (fun ζ ↦ gTerm k n ζ w) = fun ζ ↦ (π * I * nuC n) ^ k *
      cexp ((nuC n ^ 2 * w + 4 * nuC n * ζ - 2 * nuC n) * ((π : ℂ) * I) / 4) := by
    funext ζ
    unfold gTerm thetaTerm
    simp only [nuC]
    ring_nf
  rw [hf]
  refine h2.congr_deriv ?_
  unfold gTerm thetaTerm
  simp only [nuC]
  ring_nf

lemma iteratedDeriv_kroneckerTheta (w : ℂ) (hw : 0 < w.im) (k : ℕ) :
    iteratedDeriv k (fun ζ ↦ kroneckerTheta ζ w) = fun ζ ↦ ∑' n : ℤ, gTerm k n ζ w := by
  induction k with
  | zero =>
    funext ζ
    simp [gTerm, kroneckerTheta, thetaTerm]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext ζ
    refine HasDerivAt.deriv ?_
    have hS : Summable fun n : ℤ ↦ π ^ (k + 1) * ((|((2 * n + 1 : ℤ) : ℝ)| ^ (k + 1) : ℝ) *
        Real.exp (-π * ((w.im / 4) * ((2 * n + 1 : ℤ) : ℝ) ^ 2 -
          2 * ((|ζ.im| + 1) / 2) * |((2 * n + 1 : ℤ) : ℝ)|))) :=
      (summable_bound ((|ζ.im| + 1) / 2) (T := w.im / 4) (by positivity) (k + 1)).mul_left _
    refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball ζ 1) hS Metric.isOpen_ball
      (convex_ball ζ 1).isPreconnected (fun n y _ ↦ hasDerivAt_gTerm k n y w) ?_
      (Metric.mem_ball_self one_pos) (summable_gTerm k ζ hw) (Metric.mem_ball_self one_pos)
    intro n y hy
    refine norm_gTerm_le (k + 1) (le_refl _) ?_ n
    have h1 : |y.im - ζ.im| ≤ ‖y - ζ‖ := by
      simpa using Complex.abs_im_le_norm (y - ζ)
    have h2 : ‖y - ζ‖ < 1 := by simpa [dist_eq_norm] using hy
    have h3 : |y.im| ≤ |ζ.im| + |y.im - ζ.im| := by
      calc |y.im| = |ζ.im + (y.im - ζ.im)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith

lemma hasDerivAt_gTerm_w (n : ℤ) (w : ℂ) :
    HasDerivAt (fun w ↦ 4 * π * I * gTerm 1 n 0 w) (gTerm 3 n 0 w) w := by
  have hg : HasDerivAt (fun w : ℂ ↦ (nuC n ^ 2 * w + 4 * nuC n * 0 - 2 * nuC n) * ((π : ℂ) * I) / 4)
      (nuC n ^ 2 * ((π : ℂ) * I) / 4) w := by
    have := ((((hasDerivAt_id w).const_mul (nuC n ^ 2)).add_const (4 * nuC n * 0)).sub_const
      (2 * nuC n)).mul_const ((π : ℂ) * I) |>.div_const 4
    refine this.congr_deriv ?_
    ring
  have h2 := hg.cexp.const_mul (4 * π * I * (π * I * nuC n) ^ 1)
  have hf : (fun w ↦ 4 * π * I * gTerm 1 n 0 w) = fun w ↦ 4 * π * I * (π * I * nuC n) ^ 1 *
      cexp ((nuC n ^ 2 * w + 4 * nuC n * 0 - 2 * nuC n) * ((π : ℂ) * I) / 4) := by
    funext w
    unfold gTerm thetaTerm
    simp only [nuC]
    ring_nf
  rw [hf]
  refine h2.congr_deriv ?_
  unfold gTerm thetaTerm
  simp only [nuC]
  ring_nf

lemma hasDerivAt_tsum_gTerm_w {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun w ↦ ∑' n : ℤ, 4 * π * I * gTerm 1 n 0 w) (∑' n : ℤ, gTerm 3 n 0 w) w := by
  have hS : Summable fun n : ℤ ↦ π ^ 3 * ((|((2 * n + 1 : ℤ) : ℝ)| ^ 3 : ℝ) *
      Real.exp (-π * ((w.im / 2 / 4) * ((2 * n + 1 : ℤ) : ℝ) ^ 2 -
        2 * 0 * |((2 * n + 1 : ℤ) : ℝ)|))) :=
    (summable_bound 0 (T := w.im / 2 / 4) (by positivity) 3).mul_left _
  have hmem : w ∈ {z : ℂ | w.im / 2 < z.im} := by
    show w.im / 2 < w.im
    linarith
  refine hasDerivAt_tsum_of_isPreconnected (t := {z : ℂ | w.im / 2 < z.im}) hS
    (isOpen_lt continuous_const Complex.continuous_im)
    (convex_halfSpace_im_gt (w.im / 2)).isPreconnected (fun n y _ ↦ hasDerivAt_gTerm_w n y) ?_
    hmem ((summable_gTerm 1 0 hw).mul_left _) hmem
  intro n y hy
  refine norm_gTerm_le 3 (S := 0) (le_of_lt ?_) (by simp) n
  have : w.im / 2 < y.im := hy
  linarith

/-! ### `ϑ'(0, w) = 2π η(w)³` -/

lemma cexp_nat_neg_pi_I (n : ℕ) : cexp ((n : ℂ) * (-((π : ℂ) * I))) = (-1) ^ n := by
  rw [Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  simp

lemma cexp_nat_pi_I (n : ℕ) : cexp ((n : ℂ) * ((π : ℂ) * I)) = (-1) ^ n := by
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]

lemma cexp_neg_half_pi_I : cexp ((π : ℂ) * I * (-1 / 2)) = -I := by
  rw [show (π : ℂ) * I * (-1 / 2) = -(π / 2 * I) by ring, Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
  simp

lemma cexp_half_pi_I : cexp ((π : ℂ) * I * (1 / 2)) = I := by
  rw [show (π : ℂ) * I * (1 / 2) = π / 2 * I by ring]
  exact Complex.exp_pi_div_two_mul_I

lemma gTerm_one_nat (n : ℕ) (w : ℂ) :
    gTerm 1 (n : ℤ) 0 w = π * ((-1) ^ n * (2 * n + 1)) * cexp (π * I * (2 * n + 1) ^ 2 * w / 4) := by
  unfold gTerm thetaTerm nuC
  rw [pow_one]
  push_cast
  have hexp : cexp (((2 * (n : ℂ) + 1) ^ 2 * w + 4 * (2 * n + 1) * 0 - 2 * (2 * n + 1)) * π * I / 4) =
      cexp (π * I * (2 * n + 1) ^ 2 * w / 4) * ((-1) ^ n * (-I)) := by
    rw [← cexp_nat_neg_pi_I, ← cexp_neg_half_pi_I, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  linear_combination (-(π : ℂ) * (2 * n + 1) * cexp (π * I * (2 * n + 1) ^ 2 * w / 4) * (-1) ^ n) *
    Complex.I_mul_I

lemma gTerm_one_neg (n : ℕ) (w : ℂ) :
    gTerm 1 (-((n : ℤ) + 1)) 0 w =
      π * ((-1) ^ n * (2 * n + 1)) * cexp (π * I * (2 * n + 1) ^ 2 * w / 4) := by
  unfold gTerm thetaTerm nuC
  rw [pow_one]
  push_cast
  have hexp : cexp (((2 * (-((n : ℂ) + 1)) + 1) ^ 2 * w + 4 * (2 * (-((n : ℂ) + 1)) + 1) * 0 -
      2 * (2 * (-((n : ℂ) + 1)) + 1)) * π * I / 4) =
      cexp (π * I * (2 * n + 1) ^ 2 * w / 4) * ((-1) ^ n * I) := by
    rw [show ((2 * (-((n : ℂ) + 1)) + 1) ^ 2 * w + 4 * (2 * (-((n : ℂ) + 1)) + 1) * 0 -
      2 * (2 * (-((n : ℂ) + 1)) + 1)) * π * I / 4 = π * I * (2 * n + 1) ^ 2 * w / 4 +
        (n : ℂ) * ((π : ℂ) * I) + (π : ℂ) * I * (1 / 2) by ring,
      Complex.exp_add, Complex.exp_add, cexp_nat_pi_I, cexp_half_pi_I]
    ring
  rw [hexp]
  linear_combination (-(π : ℂ) * (2 * n + 1) * cexp (π * I * (2 * n + 1) ^ 2 * w / 4) * (-1) ^ n) *
    Complex.I_mul_I

lemma norm_cexp_two_pi_I_lt_one {w : ℂ} (hw : 0 < w.im) : ‖cexp (2 * π * I * w)‖ < 1 := by
  rw [Complex.norm_exp]
  have : (2 * (π : ℂ) * I * w).re = -(2 * π * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have := Real.pi_pos
  nlinarith

lemma term_cube_eq (k : ℕ) (w : ℂ) :
    π * ((-1) ^ k * (2 * k + 1)) * cexp (π * I * (2 * k + 1) ^ 2 * w / 4) =
      π * cexp (π * I * w / 4) *
        ((-1) ^ k * (2 * k + 1) * cexp (2 * π * I * w) ^ (k * (k + 1) / 2)) := by
  have hT : ((k * (k + 1) / 2 : ℕ) : ℂ) * 2 = k * (k + 1) := by
    have h := Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
    have h' : ((k * (k + 1) / 2 : ℕ) : ℂ) * 2 = ((k * (k + 1) : ℕ) : ℂ) := by exact_mod_cast h
    rw [h']
    push_cast
    ring
  have hE : cexp (π * I * (2 * k + 1) ^ 2 * w / 4) =
      cexp (π * I * w / 4) * cexp (2 * π * I * w) ^ (k * (k + 1) / 2) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    linear_combination (π * I * w) * (-hT)
  rw [hE]
  ring

lemma hasSum_gTerm_one_nat {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n : ℕ ↦ gTerm 1 (n : ℤ) 0 w)
      (π * cexp (π * I * w / 4) * (∏' n : ℕ, (1 - cexp (2 * π * I * w) ^ (n + 1))) ^ 3) := by
  have h := (Ramanujan.jacobi_cube_hasSum (norm_cexp_two_pi_I_lt_one hw)).mul_left
    ((π : ℂ) * cexp (π * I * w / 4))
  have hf : (fun n : ℕ ↦ gTerm 1 (n : ℤ) 0 w) = fun k : ℕ ↦ π * cexp (π * I * w / 4) *
      ((-1) ^ k * (2 * k + 1) * cexp (2 * π * I * w) ^ (k * (k + 1) / 2)) := by
    funext k
    rw [gTerm_one_nat, term_cube_eq]
  rw [hf]
  exact h

lemma hasSum_gTerm_one_int {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n : ℤ ↦ gTerm 1 n 0 w)
      (π * cexp (π * I * w / 4) * (∏' n : ℕ, (1 - cexp (2 * π * I * w) ^ (n + 1))) ^ 3 +
        π * cexp (π * I * w / 4) * (∏' n : ℕ, (1 - cexp (2 * π * I * w) ^ (n + 1))) ^ 3) := by
  refine HasSum.of_nat_of_neg_add_one (hasSum_gTerm_one_nat hw) ?_
  have hf : (fun n : ℕ ↦ gTerm 1 (-((n : ℤ) + 1)) 0 w) = fun n : ℕ ↦ gTerm 1 (n : ℤ) 0 w := by
    funext n
    rw [gTerm_one_neg, gTerm_one_nat]
  rw [hf]
  exact hasSum_gTerm_one_nat hw

lemma tsum_gTerm_one {w : ℂ} (hw : 0 < w.im) :
    ∑' n : ℤ, gTerm 1 n 0 w = 2 * π * ModularForm.eta w ^ 3 := by
  rw [(hasSum_gTerm_one_int hw).tsum_eq, eta_eq_cexp', mul_pow, ← Complex.exp_nat_mul]
  have : cexp (((3 : ℕ) : ℂ) * (2 * π * I * w / 24)) = cexp (π * I * w / 4) := by
    congr 1
    push_cast
    ring
  rw [this]
  ring

/-! ### `ϑ'''(0, w) = -π² E₂(w) ϑ'(0, w)` -/

/-- **Kronecker's `ϑ'''(0, w) = -π² E₂(w) ϑ'(0, w)`** (Werke 5, II art. IV, pp. 146-147), proved: closes the named proposition `KroneckerThetaE2`. -/
@[kb "kronecker1930" "Werke 5, II art. IV, pp. 146-147"]
theorem kroneckerThetaE2 : KroneckerThetaE2 := by
  intro w
  have hw : 0 < (w : ℂ).im := w.im_pos
  have h3 := congrFun (iteratedDeriv_kroneckerTheta (w : ℂ) hw 3) 0
  have h1 := congrFun (iteratedDeriv_kroneckerTheta (w : ℂ) hw 1) 0
  rw [iteratedDeriv_one] at h1
  rw [h3, h1, tsum_gTerm_one hw, ← (hasDerivAt_tsum_gTerm_w hw).deriv]
  have hev : (fun w' : ℂ ↦ ∑' n : ℤ, 4 * π * I * gTerm 1 n 0 w') =ᶠ[nhds (w : ℂ)]
      fun w' ↦ 4 * π * I * (2 * π * ModularForm.eta w' ^ 3) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds (show (w : ℂ) ∈ {z : ℂ | 0 < z.im} from hw)] with w' hw'
    rw [tsum_mul_left, tsum_gTerm_one hw']
  rw [hev.deriv_eq]
  have hd : DifferentiableAt ℂ ModularForm.eta (w : ℂ) :=
    ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hw
  have hD : HasDerivAt (fun w' : ℂ ↦ 4 * π * I * (2 * π * ModularForm.eta w' ^ 3))
      (4 * π * I * (2 * π * (3 * ModularForm.eta (w : ℂ) ^ 2 * deriv ModularForm.eta (w : ℂ)))) w := by
    have := ((hd.hasDerivAt.pow 3).const_mul (2 * (π : ℂ))).const_mul (4 * (π : ℂ) * I)
    convert this using 1
  rw [hD.deriv, ModularForm.deriv_eta_eq_E2_mul_eta]
  linear_combination (2 * (π : ℂ) ^ 3 * EisensteinSeries.E2 w * ModularForm.eta (w : ℂ) ^ 3) *
    Complex.I_mul_I

/-- Kronecker's value `ϑ'''(0, i) = -3π ϑ'(0, i)`, unconditional. -/
@[kb "kronecker1930" "Werke 5, II art. IV, p. 147"]
theorem kronecker_theta_ratio_I' :
    iteratedDeriv 3 (fun ζ ↦ kroneckerTheta ζ UpperHalfPlane.I) 0 =
      -3 * π * deriv (fun ζ ↦ kroneckerTheta ζ UpperHalfPlane.I) 0 :=
  kronecker_theta_ratio_I kroneckerThetaE2

/-- Kronecker's value `ϑ'''(0, ρ) = -2√3 π ϑ'(0, ρ)` at `ρ = e^{2πi/3}`, unconditional. -/
@[kb "kronecker1930" "Werke 5, II art. IV, p. 147"]
theorem kronecker_theta_ratio_rho' :
    iteratedDeriv 3 (fun ζ ↦ kroneckerTheta ζ rhoPoint) 0 =
      -2 * (√3 : ℝ) * π * deriv (fun ζ ↦ kroneckerTheta ζ rhoPoint) 0 :=
  kronecker_theta_ratio_rho kroneckerThetaE2

end ModularFormsKB.Historical.Kronecker
