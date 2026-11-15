/-
# Boundedness of $\theta$ at the cusps, from the growth bound near the real axis

The cusp quantity of `Forms.lean` for $\theta$ is
$|c\tau+d|^{-1/2}\,|\theta(\gamma\tau)|$. Assuming the a priori growth bound
$|\theta(w)| \le C(1 + (\operatorname{Im} w)^{-1/2})$ on $\mathbb H$ (`theta_cusp_bdd_of_bound`), we show that this quantity
is bounded as $\operatorname{Im}\tau \to \infty$ for every $\gamma \in \mathrm{SL}_2(\mathbb Z)$.

**Route.**
1. $|j(\delta, w)| = |c_\delta w + d_\delta|^{1/2}$ for $\delta \in \Gamma_0(4)$ (`norm_thetaMult`), from `thetaMult_sq`.
2. The cusp quantity is invariant under $\gamma \mapsto \delta\gamma$ for $\delta \in \Gamma_0(4)$ (`cuspNorm_mul_left`), using the
   law and the cocycle relation `cuspDenom_mul`.
3. It is $4$-periodic in $\operatorname{Re}\tau$ (`cuspNorm_T_zpow`), since $\gamma T^{m}\gamma^{-1} \in \Gamma_0(4)$ for $4 \mid m$.
4. On the strip $0 \le \operatorname{Re}\tau < 4$, $\operatorname{Im}\tau \ge 1$, one has $1 \le |c\tau+d| \le K\operatorname{Im}\tau$
   and the growth bound gives a uniform bound (`cuspNorm_strip_le`).

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Law
import ModularFormsKB.HalfIntegral.Forms

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularGroup

local notation "ℍ" => UpperHalfPlane

/-- The automorphy denominator $c\tau + d$ of $\gamma \in \mathrm{SL}_2(\mathbb Z)$ at $\tau \in \mathbb H$. -/
noncomputable def cuspDenom (γ : SL(2, ℤ)) (τ : ℍ) : ℂ := (γ 1 0 : ℂ) * τ + γ 1 1

lemma cuspDenom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : cuspDenom γ τ ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [cuspDenom, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, Complex.zero_im, zero_mul, add_zero,
    Complex.add_re, Complex.mul_re, Complex.zero_re, zero_mul, sub_zero] at him hre
  have hc : γ 1 0 = 0 := by
    have : (γ 1 0 : ℝ) = 0 := by
      rcases mul_eq_zero.mp him with h' | h'
      · exact h'
      · exact absurd h' τ.im_ne_zero
    exact_mod_cast this
  have hd : γ 1 1 = 0 := by
    have : (γ 1 1 : ℝ) = 0 := by
      have hc' : (γ 1 0 : ℝ) = 0 := by exact_mod_cast hc
      rw [hc'] at hre; simpa using hre
    exact_mod_cast this
  have := det_entries γ
  rw [hc, hd] at this
  simp at this

lemma cuspDenom_mul (δ γ : SL(2, ℤ)) (τ : ℍ) : cuspDenom (δ * γ) τ = cuspDenom δ ↑(γ • τ) * cuspDenom γ τ := by
  have hD := cuspDenom_ne_zero γ τ
  unfold cuspDenom at *
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [eq_intCast, algebraMap_int_eq]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

lemma cuspDenom_im_smul (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ).im = τ.im / ‖cuspDenom γ τ‖ ^ 2 := by
  have := ModularGroup.im_smul_eq_div_normSq γ τ
  rw [Complex.normSq_eq_norm_sq] at this
  simpa [cuspDenom, ModularGroup.denom_apply] using this

/-- For $\delta \in \Gamma_0(4)$: $|j(\delta, w)| = |c_\delta w + d_\delta|^{1/2}$. -/
lemma norm_thetaMult {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 4) (w : ℂ) :
    ‖thetaMult δ w‖ = ‖(δ 1 0 : ℂ) * w + δ 1 1‖ ^ (1 / 2 : ℝ) := by
  have h := thetaMult_sq hδ w
  have hχ : ‖(ZMod.χ₄ (δ 1 1 : ZMod 4) : ℂ)‖ = 1 := by
    have ho := Gamma0_four_odd hδ
    rw [ZMod.χ₄_int_eq_if_mod_four]
    have h2 : ¬ δ 1 1 % 2 = 0 := by rcases ho with ⟨t, ht⟩; omega
    by_cases h1 : δ 1 1 % 4 = 1 <;> simp [h1, h2]
  have h2 : ‖thetaMult δ w‖ ^ 2 = ‖(δ 1 0 : ℂ) * w + δ 1 1‖ := by
    rw [← norm_pow, h, norm_mul, hχ, one_mul]
  rw [← Real.sqrt_eq_rpow, ← h2, Real.sqrt_sq (norm_nonneg _)]

/-- Left invariance of the cusp quantity of $\theta$ under $\Gamma_0(4)$. -/
lemma cuspNorm_mul_left {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 4) (hlaw : ThetaTransformationLaw)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    cuspNorm 0 (fun τ : ℍ ↦ theta τ) (δ * γ) τ = cuspNorm 0 (fun τ : ℍ ↦ theta τ) γ τ := by
  unfold cuspNorm
  have e : ((γ 1 0 : ℂ) * τ + γ 1 1) = cuspDenom γ τ := rfl
  have e2 : (((δ * γ) 1 0 : ℂ) * τ + (δ * γ) 1 1) = cuspDenom (δ * γ) τ := rfl
  rw [e, e2, cuspDenom_mul, mul_smul]
  simp only
  rw [hlaw δ hδ, norm_mul (thetaMult δ _), norm_thetaMult hδ]
  have hD1 : 0 < ‖cuspDenom δ ↑(γ • τ)‖ := norm_pos_iff.mpr (cuspDenom_ne_zero δ _)
  have hD2 : 0 < ‖cuspDenom γ τ‖ := norm_pos_iff.mpr (cuspDenom_ne_zero γ τ)
  have hD1' : ‖(δ 1 0 : ℂ) * ((γ • τ : ℍ) : ℂ) + δ 1 1‖ = ‖cuspDenom δ ↑(γ • τ)‖ := rfl
  rw [hD1', norm_mul (cuspDenom δ _), Real.mul_rpow hD1.le hD2.le]
  have : ‖cuspDenom δ ↑(γ • τ)‖ ^ (-((((0 : ℕ) : ℝ)) + 1 / 2)) * ‖cuspDenom δ ↑(γ • τ)‖ ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hD1]; norm_num
  calc _ = (‖cuspDenom δ ↑(γ • τ)‖ ^ (-((((0 : ℕ) : ℝ)) + 1 / 2)) * ‖cuspDenom δ ↑(γ • τ)‖ ^ (1 / 2 : ℝ)) *
        (‖cuspDenom γ τ‖ ^ (-((((0 : ℕ) : ℝ)) + 1 / 2)) * ‖theta ↑(γ • τ)‖) := by ring
    _ = _ := by rw [this, one_mul]

/-- Periodicity of the cusp quantity of $\theta$ under $\tau \mapsto \tau + m$, $4 \mid m$. -/
lemma cuspNorm_T_zpow (hlaw : ThetaTransformationLaw) (γ : SL(2, ℤ)) {m : ℤ} (hm : (4 : ℤ) ∣ m)
    (τ : ℍ) :
    cuspNorm 0 (fun τ : ℍ ↦ theta τ) γ (T ^ m • τ) = cuspNorm 0 (fun τ : ℍ ↦ theta τ) γ τ := by
  set δ : SL(2, ℤ) := γ * T ^ m * γ⁻¹ with hδdef
  have hδ : δ ∈ Gamma0 4 := by
    rw [Gamma0_mem]
    have h10 : δ 1 0 = -(m * γ 1 0 ^ 2) := by
      rw [hδdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T_zpow, Matrix.adjugate_fin_two]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [h10]
    obtain ⟨k, hk⟩ := hm
    rw [hk]
    have : ((-(4 * k * γ 1 0 ^ 2) : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨-(k * γ 1 0 ^ 2), by ring⟩
    exact this
  have hDT : cuspDenom (T ^ m) τ = 1 := by
    simp [cuspDenom, ModularGroup.coe_T_zpow]
  have key : cuspNorm 0 (fun τ : ℍ ↦ theta τ) γ (T ^ m • τ) =
      cuspNorm 0 (fun τ : ℍ ↦ theta τ) (γ * T ^ m) τ := by
    unfold cuspNorm
    have e2 : (((γ * T ^ m) 1 0 : ℂ) * τ + (γ * T ^ m) 1 1) = cuspDenom (γ * T ^ m) τ := rfl
    rw [e2, cuspDenom_mul, hDT, mul_one, mul_smul]
    rfl
  have e : γ * T ^ m = δ * γ := by rw [hδdef]; group
  rw [key, e, cuspNorm_mul_left hδ hlaw]

/-- On the strip $\operatorname{Im}\tau \ge 1$, $\operatorname{Re}\tau \in [0, 4]$ the cusp quantity is bounded. -/
lemma cuspNorm_strip_le {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ w : ℂ, 0 < w.im → ‖theta w‖ ≤ C * (1 + 1 / Real.sqrt w.im))
    (γ : SL(2, ℤ)) (τ : ℍ) (h1 : 1 ≤ τ.im) (h0 : 0 ≤ τ.re) (h4 : τ.re ≤ 4) :
    cuspNorm 0 (fun τ : ℍ ↦ theta τ) γ τ ≤ C * (1 + Real.sqrt (5 * |(γ 1 0 : ℝ)| + |(γ 1 1 : ℝ)|)) := by
  set K : ℝ := 5 * |(γ 1 0 : ℝ)| + |(γ 1 1 : ℝ)| with hK
  set y : ℝ := τ.im with hy
  have hy0 : 0 < y := by linarith
  set n : ℝ := ‖cuspDenom γ τ‖ with hn
  -- bounds on n
  have hn_lo : 1 ≤ n := by
    by_cases hc : γ 1 0 = 0
    · have hd : γ 1 1 ≠ 0 := by
        intro hd
        have := det_entries γ
        rw [hc, hd] at this; simp at this
      have : cuspDenom γ τ = (γ 1 1 : ℂ) := by simp [cuspDenom, hc]
      rw [hn, this, Complex.norm_intCast]
      have : (1 : ℤ) ≤ |γ 1 1| := Int.one_le_abs hd
      exact_mod_cast this
    · have hc1 : (1 : ℝ) ≤ |(γ 1 0 : ℝ)| := by
        have : (1 : ℤ) ≤ |γ 1 0| := Int.one_le_abs hc
        exact_mod_cast this
      have : |(cuspDenom γ τ).im| ≤ ‖cuspDenom γ τ‖ := Complex.abs_im_le_norm _
      have him : (cuspDenom γ τ).im = (γ 1 0 : ℝ) * y := by simp [cuspDenom, hy]
      rw [him, abs_mul, abs_of_pos hy0] at this
      nlinarith
  have hn_hi : n ≤ K * y := by
    have h1' : ‖cuspDenom γ τ‖ ≤ ‖(γ 1 0 : ℂ)‖ * ‖(τ : ℂ)‖ + ‖(γ 1 1 : ℂ)‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
    have hτ : ‖(τ : ℂ)‖ ≤ 4 + y := by
      have := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
      have e1 : |(τ : ℂ).re| ≤ 4 := by
        rw [abs_of_nonneg (by simpa using h0)]; simpa using h4
      have e2 : |(τ : ℂ).im| = y := by rw [abs_of_pos (by simpa using hy0)]; rfl
      linarith
    rw [Complex.norm_intCast, Complex.norm_intCast] at h1'
    have hc0 : 0 ≤ |(γ 1 0 : ℝ)| := abs_nonneg _
    have hd0 : 0 ≤ |(γ 1 1 : ℝ)| := abs_nonneg _
    rw [hK]
    nlinarith [mul_le_mul_of_nonneg_left hτ hc0, mul_nonneg hd0 (sub_nonneg.mpr h1)]
  -- main estimate
  have hw : 0 < ((γ • τ : ℍ) : ℂ).im := (γ • τ).im_pos
  have hbd := hB _ hw
  have him : ((γ • τ : ℍ) : ℂ).im = y / n ^ 2 := cuspDenom_im_smul γ τ
  have hs : Real.sqrt (y / n ^ 2) = Real.sqrt y / n := by
    rw [Real.sqrt_div hy0.le, Real.sqrt_sq (by linarith)]
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  set s : ℝ := Real.sqrt n with hs_def
  have hs1 : 1 ≤ s := by rw [hs_def]; exact Real.one_le_sqrt.mpr hn_lo
  have hss : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hexp : n ^ (-((((0 : ℕ) : ℝ)) + 1 / 2)) = s⁻¹ := by
    rw [hs_def, Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith)]
    norm_num
  have hcn : cuspNorm 0 (fun τ : ℍ ↦ theta τ) γ τ = s⁻¹ * ‖theta ↑(γ • τ)‖ := by
    unfold cuspNorm
    rw [← hexp]; rfl
  rw [hcn]
  rw [him, hs] at hbd
  have e1 : 1 / (Real.sqrt y / n) = n / Real.sqrt y := by field_simp
  rw [e1] at hbd
  have hsK : s ≤ Real.sqrt K * Real.sqrt y := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hn_hi
  have hq : n / Real.sqrt y ≤ s * Real.sqrt K := by
    rw [div_le_iff₀ hsy, ← hss]
    nlinarith [Real.sqrt_nonneg K, Real.sqrt_nonneg y, mul_le_mul_of_nonneg_left hsK (by linarith : (0:ℝ) ≤ s)]
  have hs0 : 0 < s := by linarith
  calc s⁻¹ * ‖theta ↑(γ • τ)‖ ≤ s⁻¹ * (C * (1 + n / Real.sqrt y)) :=
        mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hs0.le)
    _ ≤ s⁻¹ * (C * (1 + s * Real.sqrt K)) := by
        gcongr
    _ = C * (s⁻¹ + Real.sqrt K) := by field_simp
    _ ≤ C * (1 + Real.sqrt K) := by
        gcongr
        exact inv_le_one_of_one_le₀ hs1

/-- **Boundedness of $\theta$ at all cusps, given the growth bound** $|\theta(w)| \le C(1 + (\operatorname{Im} w)^{-1/2})$.
Uses `theta_transformationLaw` (the $\Gamma_0(4)$ law), the norm of the multiplier, and $4$-periodicity. -/
theorem theta_cusp_bdd_of_bound
    (hB : ∃ C : ℝ, ∀ w : ℂ, 0 < w.im → ‖theta w‖ ≤ C * (1 + 1 / Real.sqrt w.im)) :
    ∀ γ : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty (cuspNorm 0 (fun τ : ℍ ↦ theta τ) γ) := by
  obtain ⟨C, hC⟩ := hB
  have hC' : ∀ w : ℂ, 0 < w.im → ‖theta w‖ ≤ |C| * (1 + 1 / Real.sqrt w.im) := fun w hw =>
    (hC w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  intro γ
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨|C| * (1 + Real.sqrt (5 * |(γ 1 0 : ℝ)| + |(γ 1 1 : ℝ)|)), 1, fun τ hτ => ?_⟩
  -- shift into the strip
  set n : ℤ := ⌊τ.re / 4⌋ with hn
  set τ' : ℍ := T ^ (-(4 * n)) • τ with hτ'
  have hcoe : (τ' : ℂ) = τ + ((-(4 * n) : ℤ) : ℂ) := by
    rw [hτ', UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
  have hre : τ'.re = τ.re - 4 * n := by
    have := congrArg Complex.re hcoe
    simp at this; linarith
  have him : τ'.im = τ.im := by
    have := congrArg Complex.im hcoe
    simpa using this
  have hfl1 := Int.floor_le (τ.re / 4)
  have hfl2 := Int.lt_floor_add_one (τ.re / 4)
  rw [← hn] at hfl1 hfl2
  have hper := cuspNorm_T_zpow theta_transformationLaw γ (m := -(4 * n)) ⟨-n, by ring⟩ τ
  rw [← hτ'] at hper
  rw [Real.norm_eq_abs, abs_of_nonneg (cuspNorm_nonneg _ _ _ _), ← hper]
  exact cuspNorm_strip_le (abs_nonneg C) hC' γ τ' (by rw [him]; exact hτ)
    (by rw [hre]; linarith) (by rw [hre]; linarith)

end ModularFormsKB.HalfIntegral
