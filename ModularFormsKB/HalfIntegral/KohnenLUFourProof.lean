/-
# `KohnenLUFour` for the theta multiplier: the cusp computation

Let $g \in S^+_{k+1/2}(4)$ (theta multiplier) have coefficients $c$, let $W\tau = -1/4\tau$ (`frickePt`),
$x = (-2i\tau)^{1/2}$, and write $(f|L)(\tau) = x^{-(2k+1)}\cdot\tfrac14\sum_{j=0}^{3} f\big((W\tau + j)/4\big)$
(`kohnenL`). The four points $(W\tau + j)/4$ are:
* $j = 1$: $\begin{psmallmatrix}1&0\\4&1\end{psmallmatrix}(\tau - \tfrac14)$, multiplier $(4\tau)^{1/2} = (1+i)x$;
* $j = 3$: $\begin{psmallmatrix}3&-1\\4&-1\end{psmallmatrix}(\tau + \tfrac14)$, multiplier $-i(4\tau)^{1/2}$;
* $j = 0, 2$: on the plus space $f(z/4) + f(z/4 + 1/2) = f((z+1)/4) + f((z+3)/4)$ (`plus_pair`), since the
  coefficients at $n \equiv 2 \bmod 4$ vanish.
Hence (`kohnenL_eq_of_plus`) $Lg = \tfrac12[(1+i)^{2k+1}g(\tau - \tfrac14) + (1-i)^{2k+1}g(\tau+\tfrac14)]$, whose
coefficients are $\alpha\,c(n)$ (`kohnenL_kappa`, from `omega8_kappa`): this is the forward direction of
`KohnenPlusEigen.plus_iff`, $Lg = \alpha g$ on the plus space.

For $h = U(4)g$ the terms $j = 1, 3$ are as above with $h$ in place of $g$. The term $j = 0$ is
$U(4)g(W(4\tau)) = (2x)^{2k+1}(Lg)(4\tau) = (2x)^{2k+1}\alpha g(4\tau)$. The term $j = 2$ is
$\tfrac14\sum_{r = 1,3,5,7} g\big(\begin{psmallmatrix}r&(r^2-1)/8\\8&r\end{psmallmatrix}(\tau - \tfrac r8)\big)$, with
multipliers $\varepsilon_r^{-1}\left(\frac 8r\right)(8\tau)^{1/2} = 2\omega^r x$, $\omega = e^{\pi i/4}$, and the resulting
Gauss sum is `omega8_gauss`. Comparing coefficients gives `KohnenLUFour thetaMultiplierSystem k`
(`kohnenLUFour_theta`), hence `KohnenTPlusFourStable` (`kohnenTPlusFourStable_theta`).
-/
import ModularFormsKB.HalfIntegral.KohnenEighthRoots
import ModularFormsKB.HalfIntegral.KohnenTPlusFourLU
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-! ### Principal square roots -/

lemma cpow_half_eq_of_sq {y z : ℂ} (h : y ^ 2 = z) (hy : 0 < y.re) : z ^ (1 / 2 : ℂ) = y := by
  rw [← h, one_div]
  exact Complex.sq_cpow_two_inv hy

lemma re_cpow_half_nonneg (z : ℂ) : 0 ≤ (z ^ (1 / 2 : ℂ)).re := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [Complex.zero_cpow (by norm_num)]; simp
  have e : (Complex.log z * (1 / 2)).im = z.arg / 2 := by
    rw [Complex.mul_im, Complex.log_im]; simp [div_eq_mul_inv]
  rw [cpow_def_of_ne_zero hz, Complex.exp_re, e]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
  · have := Complex.neg_pi_lt_arg z; linarith
  · have := Complex.arg_le_pi z; linarith

lemma frickeRoot_sq (τ : ℍ) : ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 2 = -2 * I * τ := by
  have := Complex.cpow_nat_inv_pow (-2 * I * (τ : ℂ)) (n := 2) (by norm_num)
  simpa using this

lemma frickeRoot_im_lt (τ : ℍ) :
    ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)).im < ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)).re := by
  set x := (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) with hx
  have h2 := frickeRoot_sq τ
  rw [← hx] at h2
  have hre : x.re * x.re - x.im * x.im = 2 * τ.im := by
    have := congrArg Complex.re h2
    simp only [sq, Complex.mul_re] at this
    rw [this]; simp
  have h0 : 0 ≤ x.re := re_cpow_half_nonneg _
  have hτ := τ.im_pos
  by_contra hc
  push_neg at hc
  nlinarith

lemma frickeRoot_re_pos (τ : ℍ) : 0 < ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)).re := by
  set x := (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) with hx
  have h2 := frickeRoot_sq τ
  rw [← hx] at h2
  have hre : x.re * x.re - x.im * x.im = 2 * τ.im := by
    have := congrArg Complex.re h2
    simp only [sq, Complex.mul_re] at this
    rw [this]; simp
  have h0 : 0 ≤ x.re := re_cpow_half_nonneg _
  have hτ := τ.im_pos
  rcases h0.lt_or_eq with h | h
  · exact h
  · rw [← h] at hre; nlinarith

/-- **Square roots of $m\tau$:** for $\rho$ on the ray $\arg\rho = \pi/4$,
$(\rho^2(-2i)\tau)^{1/2} = \rho\,(-2i\tau)^{1/2}$. -/
lemma cpow_half_mul_frickeRoot (τ : ℍ) (ρ : ℂ) (hρ : 0 < ρ.re) (hρ' : ρ.re = ρ.im) :
    (ρ ^ 2 * (-2 * I) * τ) ^ (1 / 2 : ℂ) = ρ * (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  apply cpow_half_eq_of_sq
  · rw [mul_pow, frickeRoot_sq]; ring
  · have h := frickeRoot_im_lt τ
    rw [Complex.mul_re, ← hρ']
    have : ρ.re * ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)).re - ρ.re * ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)).im =
        ρ.re * (((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)).re - ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)).im) := by ring
    rw [this]
    exact mul_pos hρ (by linarith)

lemma cpow_half_four_mul (τ : ℍ) :
    ((4 : ℂ) * τ) ^ (1 / 2 : ℂ) = (1 + I) * (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  rw [← cpow_half_mul_frickeRoot τ (1 + I) (by simp) (by simp)]
  congr 1
  have : ((1 + I) ^ 2 * (-2 * I) : ℂ) = 4 := by linear_combination (-2 * I - 4) * I_sq
  rw [this]

lemma cpow_half_eight_mul (τ : ℍ) :
    ((8 : ℂ) * τ) ^ (1 / 2 : ℂ) = (2 * omega8) * (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  rw [← cpow_half_mul_frickeRoot τ (2 * omega8) (by simp [omega8_re_pos]) (by simp [omega8_re_eq_im])]
  congr 1
  have : ((2 * omega8) ^ 2 * (-2 * I) : ℂ) = 8 := by
    rw [mul_pow, omega8_sq]; linear_combination (-8) * I_sq
  rw [this]

lemma cpow_half_fricke_four_mul (τ : ℍ) :
    (-2 * I * ((affPt 4 1 0 τ : ℍ) : ℂ)) ^ (1 / 2 : ℂ) = 2 * (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  apply cpow_half_eq_of_sq
  · rw [mul_pow, frickeRoot_sq, coe_affPt]; push_cast; ring
  · have := frickeRoot_re_pos τ
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith

/-! ### The four matrices -/

/-- The matrix $\begin{pmatrix}a&b\\c&d\end{pmatrix}$ of determinant one. -/
def luMat (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

@[simp] lemma luMat_10 (a b c d : ℤ) (h) : luMat a b c d h 1 0 = c := rfl
@[simp] lemma luMat_11 (a b c d : ℤ) (h) : luMat a b c d h 1 1 = d := rfl

lemma coe_luMat_smul (a b c d : ℤ) (h) (z : ℍ) :
    ((luMat a b c d h • z : ℍ) : ℂ) = (a * z + b) / (c * z + d) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [luMat]

lemma luMat_mem (a b c d : ℤ) (h) (hc : (4 : ℤ) ∣ c) : luMat a b c d h ∈ Gamma0 4 := by
  rw [Gamma0_mem, luMat_10]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hc

lemma coe_quarterPt (j : ℕ) (z : ℍ) : ((quarterPt j z : ℍ) : ℂ) = ((z : ℂ) + j) / 4 := rfl

/-! ### The terms $j = 1, 3$ -/

section Law

variable {k : ℕ} {F : ℍ → ℂ}
  (hF : ∀ γ ∈ Gamma0 4, ∀ τ : ℍ, F (γ • τ) = thetaMult γ (τ : ℂ) ^ (2 * k + 1) * F τ)
include hF

lemma term_one (τ : ℍ) :
    F (quarterPt 1 (frickePt τ)) =
      ((1 + I) * (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ (2 * k + 1) * F ((-1 / 4 : ℝ) +ᵥ τ) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hpt : quarterPt 1 (frickePt τ) = luMat 1 0 4 1 (by norm_num) • ((-1 / 4 : ℝ) +ᵥ τ) := by
    ext
    rw [coe_luMat_smul, coe_quarterPt, coe_frickePt, UpperHalfPlane.coe_vadd]
    have hd : ((4 : ℤ) : ℂ) * (((-1 / 4 : ℝ) : ℂ) + τ) + ((1 : ℤ) : ℂ) = 4 * τ := by push_cast; ring
    rw [hd]
    push_cast
    field_simp
    ring
  rw [hpt, hF _ (luMat_mem _ _ _ _ _ (by norm_num))]
  congr 2
  unfold thetaMult thetaMultCD
  rw [luMat_10, luMat_11, UpperHalfPlane.coe_vadd, ← cpow_half_four_mul]
  have e1 : epsD 1 = 1 := by simp [epsD]
  have e2 : shimuraSym 4 1 = 1 := by simp [shimuraSym]
  rw [e1, e2]
  have hd : ((4 : ℤ) : ℂ) * (((-1 / 4 : ℝ) : ℂ) + τ) + ((1 : ℤ) : ℂ) = 4 * τ := by push_cast; ring
  rw [hd]
  simp

lemma term_three (τ : ℍ) :
    F (quarterPt 3 (frickePt τ)) =
      (-I * (1 + I) * (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ (2 * k + 1) * F ((1 / 4 : ℝ) +ᵥ τ) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hpt : quarterPt 3 (frickePt τ) = luMat 3 (-1) 4 (-1) (by norm_num) • ((1 / 4 : ℝ) +ᵥ τ) := by
    ext
    rw [coe_luMat_smul, coe_quarterPt, coe_frickePt, UpperHalfPlane.coe_vadd]
    have hd : ((4 : ℤ) : ℂ) * (((1 / 4 : ℝ) : ℂ) + τ) + ((-1 : ℤ) : ℂ) = 4 * τ := by push_cast; ring
    rw [hd]
    push_cast
    field_simp
    ring
  rw [hpt, hF _ (luMat_mem _ _ _ _ _ (by norm_num))]
  congr 2
  unfold thetaMult thetaMultCD
  rw [luMat_10, luMat_11, UpperHalfPlane.coe_vadd]
  have e1 : epsD (-1) = I := by simp [epsD]
  have e2 : shimuraSym 4 (-1) = 1 := by simp [shimuraSym]
  rw [e1, e2]
  have hd : ((4 : ℤ) : ℂ) * (((1 / 4 : ℝ) : ℂ) + τ) + ((-1 : ℤ) : ℂ) = 4 * τ := by push_cast; ring
  rw [hd, cpow_half_four_mul, Complex.inv_I]
  push_cast
  ring

/-- The point $((W\tau + 2)/4 + i)/4 = \gamma_r(\tau - r/8)$, $r = 2i+1$, $\gamma_r = \begin{psmallmatrix}r&y\\8&r\end{psmallmatrix}$. -/
lemma term_eighth (τ : ℍ) (i : ℕ) (y : ℤ) (hdet : (2 * i + 1 : ℤ) * (2 * i + 1) - y * 8 = 1) :
    F (quarterPt i (quarterPt 2 (frickePt τ))) =
      ((epsD (2 * i + 1))⁻¹ * (shimuraSym 8 (2 * i + 1) : ℂ) * ((8 : ℂ) * τ) ^ (1 / 2 : ℂ)) ^ (2 * k + 1) *
        F ((-(2 * i + 1 : ℝ) / 8) +ᵥ τ) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hdetC : ((2 * i + 1 : ℤ) : ℂ) * ((2 * i + 1 : ℤ) : ℂ) - (y : ℂ) * 8 = 1 := by exact_mod_cast hdet
  have hpt : quarterPt i (quarterPt 2 (frickePt τ)) =
      luMat (2 * i + 1) y 8 (2 * i + 1) hdet • ((-(2 * i + 1 : ℝ) / 8) +ᵥ τ) := by
    ext
    rw [coe_luMat_smul, coe_quarterPt, coe_quarterPt, coe_frickePt, UpperHalfPlane.coe_vadd]
    have hd : ((8 : ℤ) : ℂ) * (((-(2 * i + 1 : ℝ) / 8 : ℝ) : ℂ) + τ) + ((2 * i + 1 : ℤ) : ℂ) = 8 * τ := by
      push_cast; ring
    rw [hd]
    push_cast at hdetC ⊢
    field_simp
    linear_combination 64 * hdetC
  rw [hpt, hF _ (luMat_mem _ _ _ _ _ (by norm_num))]
  congr 2
  unfold thetaMult thetaMultCD
  rw [luMat_10, luMat_11, UpperHalfPlane.coe_vadd]
  have hd : ((8 : ℤ) : ℂ) * (((-(2 * i + 1 : ℝ) / 8 : ℝ) : ℂ) + τ) + ((2 * i + 1 : ℤ) : ℂ) = 8 * τ := by
    push_cast; ring
  rw [hd]

end Law

/-! ### $q$-expansions of the translates -/

lemma hasSum_vadd {F : ℍ → ℂ} {c : ℕ → ℂ} (hc : Abstract.HasQExp F c) (x : ℝ) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ c n * cexp (2 * π * I * n * x) * cexp (2 * π * I * n * τ)) (F (x +ᵥ τ)) := by
  convert hc (x +ᵥ τ) using 2 with n
  rw [UpperHalfPlane.coe_vadd, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

lemma hasSum_vadd_neg_quarter {F : ℍ → ℂ} {c : ℕ → ℂ} (hc : Abstract.HasQExp F c) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ c n * omega8 ^ (6 * n) * cexp (2 * π * I * n * τ)) (F ((-1 / 4 : ℝ) +ᵥ τ)) := by
  convert hasSum_vadd hc (-1 / 4 : ℝ) τ using 3 with n
  rw [← cexp_neg_eighth n 2 (by norm_num)]
  congr 1
  push_cast; ring

lemma hasSum_vadd_quarter {F : ℍ → ℂ} {c : ℕ → ℂ} (hc : Abstract.HasQExp F c) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ c n * omega8 ^ (2 * n) * cexp (2 * π * I * n * τ)) (F ((1 / 4 : ℝ) +ᵥ τ)) := by
  convert hasSum_vadd hc (1 / 4 : ℝ) τ using 3 with n
  rw [← cexp_pos_quarter n]
  congr 1
  push_cast; ring

lemma hasSum_vadd_eighth {F : ℍ → ℂ} {c : ℕ → ℂ} (hc : Abstract.HasQExp F c) (τ : ℍ) (i : ℕ) (hi : i < 4) :
    HasSum (fun n : ℕ ↦ c n * omega8 ^ ((8 - (2 * i + 1)) * n) * cexp (2 * π * I * n * τ))
      (F ((-(2 * i + 1 : ℝ) / 8) +ᵥ τ)) := by
  convert hasSum_vadd hc (-(2 * i + 1 : ℝ) / 8) τ using 3 with n
  rw [← cexp_neg_eighth n (2 * i + 1) (by omega)]
  congr 1
  push_cast; ring

lemma hasSum_affPt_four {F : ℍ → ℂ} {c : ℕ → ℂ} (hc : Abstract.HasQExp F c) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ (if 4 ∣ n then c (n / 4) else 0) * cexp (2 * π * I * n * τ)) (F (affPt 4 1 0 τ)) := by
  have hinj : Function.Injective (fun m : ℕ ↦ 4 * m) := fun x y hxy ↦ by simpa using hxy
  have h0 : ∀ n ∉ Set.range (fun m : ℕ ↦ 4 * m),
      (if 4 ∣ n then c (n / 4) else 0) * cexp (2 * π * I * n * τ) = 0 := by
    intro n hn
    rw [if_neg, zero_mul]
    rintro ⟨m, rfl⟩
    exact hn ⟨m, rfl⟩
  rw [← hinj.hasSum_iff h0]
  convert hc (affPt 4 1 0 τ) using 2 with m
  simp only [Function.comp, dvd_mul_right, if_true, coe_affPt]
  rw [Nat.mul_div_cancel_left m (by norm_num)]
  congr 2
  push_cast
  ring

/-! ### The plus condition at the cusp $1/2$ -/

lemma minusIdx_of_two_mod_four (k n : ℕ) (hn : n % 4 = 2) : MinusIdx k n := by
  unfold MinusIdx
  left
  rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> omega

/-- **On the plus space** $f(z/4) + f(z/4 + 1/2) = f((z+1)/4) + f((z+3)/4)$: both sides are
$\sum c(n)e(nz/4)(1 + (-1)^n)$ resp. $(i^n + i^{3n})$, which agree unless $n \equiv 2 \bmod 4$. -/
lemma plus_pair {k : ℕ} {F : ℍ → ℂ} {c : ℕ → ℂ} (hc : Abstract.HasQExp F c) (hp : PlusCond k c) (z : ℍ) :
    F (quarterPt 0 z) + F (quarterPt 2 z) = F (quarterPt 1 z) + F (quarterPt 3 z) := by
  have hq : ∀ j : ℕ, HasSum (fun n : ℕ ↦ c n * cexp (2 * π * I * n * z / 4) * (I ^ n) ^ j)
      (F (quarterPt j z)) := by
    intro j
    convert hc (quarterPt j z) using 2 with n
    rw [coe_quarterPt, mul_assoc]
    congr 1
    have hI : I = cexp (π / 2 * I) := by
      rw [Complex.exp_mul_I]; simp
    rw [show (I ^ n) ^ j = cexp (2 * π * I * n * j / 4) by
      rw [show 2 * (π : ℂ) * I * n * j / 4 = ((n * j : ℕ) : ℂ) * (π / 2 * I) by push_cast; ring,
        Complex.exp_nat_mul, ← hI, pow_mul], ← Complex.exp_add]
    congr 1
    ring
  have hL := (hq 0).add (hq 2)
  have hR := (hq 1).add (hq 3)
  refine hL.unique ?_
  convert hR using 1
  funext n
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ n = 4 * m + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have h4 : (I ^ 4 : ℂ) = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
  have hp' : (I ^ (4 * m + r) : ℂ) = I ^ r := by rw [pow_add, pow_mul, h4]; simp
  rw [hp']
  interval_cases r
  · simp
  · simp [pow_succ]
  · have : c (4 * m + 2) = 0 := hp _ (minusIdx_of_two_mod_four k _ (by omega))
    simp [this]
  · simp [pow_succ]

/-! ### $L$ on the plus space -/

lemma kohnenL_apply (k : ℕ) (F : ℍ → ℂ) (τ : ℍ) :
    kohnenL k F τ = (((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ (2 * k + 1))⁻¹ * ((1 / 4 : ℂ) *
      (F (quarterPt 0 (frickePt τ)) + F (quarterPt 1 (frickePt τ)) + F (quarterPt 2 (frickePt τ)) +
        F (quarterPt 3 (frickePt τ)))) := by
  simp only [kohnenL, kohnenW4, kohnenU4, cpow_neg_half_pow, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]

/-- The two odd terms of $L$: $x^{-(2k+1)}(F_1 + F_3) = (1+i)^{2k+1}F(\tau - \tfrac14) + (1-i)^{2k+1}F(\tau + \tfrac14)$. -/
lemma odd_terms {k : ℕ} {F : ℍ → ℂ}
    (hF : ∀ γ ∈ Gamma0 4, ∀ τ : ℍ, F (γ • τ) = thetaMult γ (τ : ℂ) ^ (2 * k + 1) * F τ) (τ : ℍ) :
    (((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ (2 * k + 1))⁻¹ *
        (F (quarterPt 1 (frickePt τ)) + F (quarterPt 3 (frickePt τ))) =
      (1 + I) ^ (2 * k + 1) * F ((-1 / 4 : ℝ) +ᵥ τ) + (-I * (1 + I)) ^ (2 * k + 1) * F ((1 / 4 : ℝ) +ᵥ τ) := by
  rw [term_one hF, term_three hF]
  have hx : ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ (2 * k + 1) ≠ 0 :=
    pow_ne_zero _ (cpow_half_fricke_ne_zero τ)
  rw [mul_pow (1 + I), mul_pow (-I * (1 + I))]
  generalize ((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ (2 * k + 1) = X at hx ⊢
  field_simp

lemma hasSum_odd_terms {k : ℕ} {F : ℍ → ℂ} {c : ℕ → ℂ}
    (hF : ∀ γ ∈ Gamma0 4, ∀ τ : ℍ, F (γ • τ) = thetaMult γ (τ : ℂ) ^ (2 * k + 1) * F τ)
    (hc : Abstract.HasQExp F c) (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((1 + I) ^ (2 * k + 1) * omega8 ^ (6 * n) +
        (-I * (1 + I)) ^ (2 * k + 1) * omega8 ^ (2 * n)) * c n * cexp (2 * π * I * n * τ))
      ((((-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ (2 * k + 1))⁻¹ *
        (F (quarterPt 1 (frickePt τ)) + F (quarterPt 3 (frickePt τ)))) := by
  rw [odd_terms hF]
  convert ((hasSum_vadd_neg_quarter hc τ).mul_left ((1 + I) ^ (2 * k + 1))).add
    ((hasSum_vadd_quarter hc τ).mul_left ((-I * (1 + I)) ^ (2 * k + 1))) using 1
  funext n
  ring

/-- **The constant $\kappa(n)$ of $L$:** $\tfrac12[(1+i)^{2k+1}\omega^{6n} + (1-i)^{2k+1}\omega^{2n}] = \pm\alpha$. -/
lemma kohnenL_kappa (k n : ℕ) :
    (1 / 2 : ℂ) * ((1 + I) ^ (2 * k + 1) * omega8 ^ (6 * n) + (-I * (1 + I)) ^ (2 * k + 1) * omega8 ^ (2 * n)) =
      kohnenAlpha k * (if MinusIdx k n then -1 else 1) := by
  have hI : I = omega8 ^ 2 := omega8_sq.symm
  have h1 : (1 + omega8 ^ 2) ^ (2 * k + 1) = (2 * omega8 ^ 2) ^ k * (1 + omega8 ^ 2) := by
    rw [pow_succ, pow_mul]
    congr 2
    linear_combination omega8_four
  have h2 : (-omega8 ^ 2 * (1 + omega8 ^ 2)) ^ (2 * k + 1) =
      (2 * omega8 ^ 6) ^ k * (-omega8 ^ 2 * (1 + omega8 ^ 2)) := by
    rw [pow_succ, pow_mul]
    congr 2
    linear_combination omega8 ^ 4 * omega8_four
  have hk := omega8_kappa k n
  rw [hI, h1, h2]
  unfold kohnenAlpha
  linear_combination (2 ^ k / 2 : ℂ) * hk +
    (2 ^ k / 2 : ℂ) * omega8 ^ (6 * k + 2 * n) * (-(1 + omega8 ^ 2)) * omega8_four

/-- **Forward direction of `KohnenPlusEigen.plus_iff` for the theta multiplier:** on $S^+_{k+1/2}(4)$,
$W(4)U(4)g = \alpha g$, with $q$-expansion $\alpha c$. -/
theorem hasQExp_kohnenL_of_plus {k : ℕ} {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : g ∈ thetaMultiplierSystem.cuspForms k 1 1) (hc : Abstract.HasQExp g c) (hp : PlusCond k c) :
    Abstract.HasQExp (kohnenL k g) (fun n ↦ kohnenAlpha k * c n) := by
  have hF := (transforms_iff_simple k g).1 hg.transforms
  intro τ
  have hsum := plus_pair hc hp (frickePt τ)
  have h4 : g (quarterPt 0 (frickePt τ)) + g (quarterPt 1 (frickePt τ)) + g (quarterPt 2 (frickePt τ)) +
      g (quarterPt 3 (frickePt τ)) = 2 * (g (quarterPt 1 (frickePt τ)) + g (quarterPt 3 (frickePt τ))) := by
    linear_combination hsum
  rw [kohnenL_apply, h4]
  rw [show ∀ X S : ℂ, X * (1 / 4 * (2 * S)) = 1 / 2 * (X * S) from fun X S ↦ by ring]
  convert (hasSum_odd_terms hF hc τ).mul_left (1 / 2 : ℂ) using 1
  funext n
  beta_reduce
  have hκ := kohnenL_kappa k n
  by_cases hn : MinusIdx k n
  · simp [hp n hn]
  · rw [if_neg hn, mul_one] at hκ
    rw [← hκ]; ring

theorem kohnenL_eq_of_plus {k : ℕ} {g : ℍ → ℂ} (hg : g ∈ thetaMultiplierSystem.plusCuspForms k 1 1) :
    kohnenL k g = kohnenAlpha k • g := by
  obtain ⟨hcusp, c, hc, hp⟩ := hg
  have h1 := hasQExp_kohnenL_of_plus hcusp hc hp
  have h2 : Abstract.HasQExp (kohnenAlpha k • g) (fun n ↦ kohnenAlpha k * c n) := fun τ ↦ by
    simpa [mul_assoc] using (hc τ).mul_left (kohnenAlpha k)
  funext τ
  exact (h1 τ).unique (h2 τ)

/-! ### $L(U(4)g)$ -/

lemma eighth_const (i : ℕ) (hi : i < 4) :
    (epsD (2 * (i : ℤ) + 1))⁻¹ * (shimuraSym 8 (2 * (i : ℤ) + 1) : ℂ) = omega8 ^ (2 * i) := by
  have h6 : omega8 ^ 6 = -I := by
    rw [show 6 = 4 + 2 from rfl, pow_add, omega8_four, omega8_sq]; ring
  interval_cases i
  · simp [epsD, shimuraSym]
  · have hj : jacobiSym 8 3 = -1 := by norm_num
    simp [epsD, shimuraSym, hj, omega8_sq]
  · have hj : jacobiSym 8 5 = -1 := by norm_num
    simp [epsD, shimuraSym, hj, omega8_four]
  · have hj : jacobiSym 8 7 = 1 := by norm_num
    simp [epsD, shimuraSym, hj, h6]

/-- **The Gauss constant at the cusp $1/2$:** at plus indices
$\tfrac1{16}\sum_r (2\omega^r)^{2k+1}\omega^{(8-r)n} = \alpha\left(\frac{(-1)^kn}2\right)2^{k-1}$. -/
lemma kohnenLU_gauss (k n : ℕ) (hn : ¬ MinusIdx k n) :
    (1 / 16 : ℂ) * ∑ i ∈ Finset.range 4,
        (2 * omega8 ^ (2 * i + 1)) ^ (2 * k + 1) * omega8 ^ ((8 - (2 * i + 1)) * n) =
      kohnenAlpha k * (kroneckerTwo ((-1) ^ k * (n : ℤ)) : ℂ) * (2 : ℂ) ^ ((k : ℤ) - 1) := by
  have hg := omega8_gauss k n hn
  rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  unfold kohnenAlpha
  linear_combination (2 ^ (2 * k + 1) / 16 : ℂ) * hg

lemma not_four_dvd_of_minusIdx {k n : ℕ} (hn : MinusIdx k n) : ¬ 4 ∣ n := by
  rintro ⟨m, rfl⟩
  unfold MinusIdx at hn
  rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] at hn <;> push_cast at hn <;> omega

/-- **`KohnenLUFour` holds for the theta multiplier** (Kohnen 1980 `kohnen1980`, §2 [unverified]; the cusp computation
of the module docstring). -/
@[kb "kohnen1980" "§2: W(4)U(4)U(4)g = α T⁺(4)g − (α/2) U(4)g on S⁺_{k+1/2}(4), theta multiplier [unverified]"]
theorem kohnenLUFour_theta (k : ℕ) : KohnenLUFour thetaMultiplierSystem k := by
  refine ⟨fun g hg c hc τ ↦ ?_⟩
  obtain ⟨hcusp, a, ha, hp⟩ := hg
  rw [Abstract.hasQExp_unique ha hc] at hp
  have hF := (transforms_iff_simple k g).1 hcusp.transforms
  have hU := kohnenU4_mem_cuspForms k hcusp
  have hH := (transforms_iff_simple k (kohnenU4 g)).1 hU.transforms
  have hcU := hasQExp_kohnenU4 hc
  set x := (-2 * I * (τ : ℂ)) ^ (1 / 2 : ℂ) with hx
  have hX : x ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (cpow_half_fricke_ne_zero τ)
  -- the term `j = 0`: the cusp `0`, through `L g = α g`
  have h0 : kohnenU4 g (quarterPt 0 (frickePt τ)) =
      x ^ (2 * k + 1) * (2 ^ (2 * k + 1) * (kohnenAlpha k * g (affPt 4 1 0 τ))) := by
    have hpt : quarterPt 0 (frickePt τ) = frickePt (affPt 4 1 0 τ) := by
      have := τ.ne_zero
      ext
      rw [coe_quarterPt, coe_frickePt, coe_frickePt, coe_affPt]
      simp
      field_simp
    have hL := congrFun (kohnenL_eq_of_plus ⟨hcusp, c, hc, hp⟩) (affPt 4 1 0 τ)
    simp only [kohnenL, kohnenW4, Pi.smul_apply, smul_eq_mul] at hL
    rw [cpow_neg_half_pow, cpow_half_fricke_four_mul, ← hx] at hL
    have hx2 : (2 * x) ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero (cpow_half_fricke_ne_zero τ))
    have hU0 : kohnenU4 g (frickePt (affPt 4 1 0 τ)) =
        (2 * x) ^ (2 * k + 1) * (kohnenAlpha k * g (affPt 4 1 0 τ)) := by
      rw [← hL, ← mul_assoc, mul_inv_cancel₀ hx2, one_mul]
    rw [hpt, hU0, mul_pow]
    ring
  -- the term `j = 2`: the cusp `1/2`
  have hterm : ∀ i ∈ Finset.range 4, g (quarterPt i (quarterPt 2 (frickePt τ))) =
      (2 * omega8 ^ (2 * i + 1) * x) ^ (2 * k + 1) * g ((-(2 * i + 1 : ℝ) / 8) +ᵥ τ) := by
    intro i hi
    have hi' : i < 4 := Finset.mem_range.1 hi
    have hy : ∃ y : ℤ, (2 * (i : ℤ) + 1) * (2 * i + 1) - y * 8 = 1 := by
      interval_cases i
      · exact ⟨0, by norm_num⟩
      · exact ⟨1, by norm_num⟩
      · exact ⟨3, by norm_num⟩
      · exact ⟨6, by norm_num⟩
    obtain ⟨y, hy⟩ := hy
    rw [term_eighth hF τ i y hy, cpow_half_eight_mul, ← hx, ← mul_assoc, eighth_const i hi']
    congr 2
    ring
  have h2 : kohnenU4 g (quarterPt 2 (frickePt τ)) = x ^ (2 * k + 1) * ((1 / 4 : ℂ) *
      ∑ i ∈ Finset.range 4, (2 * omega8 ^ (2 * i + 1)) ^ (2 * k + 1) * g ((-(2 * i + 1 : ℝ) / 8) +ᵥ τ)) := by
    show (1 / 4 : ℂ) * ∑ j ∈ Finset.range 4, g (quarterPt j (quarterPt 2 (frickePt τ))) = _
    rw [Finset.sum_congr rfl hterm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- the expansion
  have hval : kohnenL k (kohnenU4 g) τ =
      (1 / 4 * 2 ^ (2 * k + 1) * kohnenAlpha k) * g (affPt 4 1 0 τ) +
        1 / 4 * ((x ^ (2 * k + 1))⁻¹ *
          (kohnenU4 g (quarterPt 1 (frickePt τ)) + kohnenU4 g (quarterPt 3 (frickePt τ)))) +
        1 / 16 * ∑ i ∈ Finset.range 4,
          (2 * omega8 ^ (2 * i + 1)) ^ (2 * k + 1) * g ((-(2 * i + 1 : ℝ) / 8) +ᵥ τ) := by
    rw [kohnenL_apply, ← hx, h0, h2]
    field_simp
    ring
  have S0 := (hasSum_affPt_four hc τ).mul_left (1 / 4 * 2 ^ (2 * k + 1) * kohnenAlpha k)
  have S13 := (hasSum_odd_terms hH hcU τ).mul_left (1 / 4 : ℂ)
  have S2 := (hasSum_sum (s := Finset.range 4) fun i hi ↦
    (hasSum_vadd_eighth hc τ i (Finset.mem_range.1 hi)).mul_left
      ((2 * omega8 ^ (2 * i + 1)) ^ (2 * k + 1))).mul_left (1 / 16 : ℂ)
  rw [hval]
  convert (S0.add S13).add S2 using 1
  funext n
  beta_reduce
  set e := cexp (2 * π * I * n * τ)
  have hsum : ∑ i ∈ Finset.range 4, (2 * omega8 ^ (2 * i + 1)) ^ (2 * k + 1) *
      (c n * omega8 ^ ((8 - (2 * i + 1)) * n) * e) =
      (∑ i ∈ Finset.range 4, (2 * omega8 ^ (2 * i + 1)) ^ (2 * k + 1) * omega8 ^ ((8 - (2 * i + 1)) * n)) *
        c n * e := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hsum]
  have hκ := kohnenL_kappa k n
  by_cases hn : MinusIdx k n
  · rw [if_pos hn] at hκ
    rw [heckeTPlusFour_of_minusIdx k c hn, if_neg (not_four_dvd_of_minusIdx hn), hp n hn]
    linear_combination (-(c (4 * n) * e / 2)) * hκ
  · rw [if_neg hn, mul_one] at hκ
    have hG := kohnenLU_gauss k n hn
    rw [heckeTPlusFour_of_not_minusIdx k c hn, heckeTPlusFourFormula]
    have hz : (2 : ℂ) ^ (2 * (k : ℤ) - 1) = 2 ^ (2 * k) / 2 := by
      rw [zpow_sub₀ two_ne_zero, zpow_one, show (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast]
    rw [hz]
    split_ifs
    · linear_combination (-(c (4 * n) * e / 2)) * hκ - (c n * e) * hG
    · linear_combination (-(c (4 * n) * e / 2)) * hκ - (c n * e) * hG

/-- **`KohnenTPlusFourStable` holds for the theta multiplier.** -/
theorem kohnenTPlusFourStable_theta (k : ℕ) : KohnenTPlusFourStable thetaMultiplierSystem k :=
  kohnenTPlusFourStable_of_LUFour (kohnenLUFour_theta k)

/-- **H2 (Kohnen's isomorphism) for the theta multiplier** from `KohnenTraceIdentity` alone. -/
@[kb "kohnen1980" "Thm. 1 for the theta multiplier, from the trace identity [unverified]"]
theorem kohnenIsomorphism_of_trace_theta (k : ℕ) (h : KohnenTraceIdentity k) :
    KohnenIsomorphism thetaMultiplierSystem k :=
  kohnenIsomorphism_of_trace_LUFour k h (kohnenLUFour_theta k)

/-- **H3 (Kohnen–Zagier) for the theta multiplier** from `KohnenTraceIdentity` and `KohnenAdjointCoeff`. -/
@[kb "kohnenzagier1981" "Kohnen–Zagier formula, theta multiplier, from the trace identity and the kernel coefficient [unverified]"]
theorem kohnenZagier_of_trace_theta (k : ℕ) (h : KohnenTraceIdentity k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_of_trace_LUFour k h (kohnenLUFour_theta k) hcoeff

/-- **H3 (Waldspurger's plus-space theorem) for the theta multiplier** from `KohnenTraceIdentity` and
`KohnenAdjointCoeff`. -/
@[kb "kohnenzagier1981" "Waldspurger's theorem on the plus space, theta multiplier, from the trace identity and the kernel coefficient [unverified]"]
theorem waldspurgerPlus_of_trace_theta (k : ℕ) (h : KohnenTraceIdentity k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_of_trace_LUFour k h (kohnenLUFour_theta k) hcoeff

end ModularFormsKB.HalfIntegral
