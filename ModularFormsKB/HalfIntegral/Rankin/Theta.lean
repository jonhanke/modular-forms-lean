/-
# The twisted theta series: parity, convergence, a crude bound, and the line integral against a cusp form

For `thetaTwist ψ t`
$= \sum_{n\in\mathbb Z}\bar\psi(n)n^\nu e(tn^2z)$ ($\nu$ = `charParity ψ`, $t \ge 1$):
- `inv_apply_neg_one_mul_pow_charParity`: $\bar\psi(-1)(-1)^\nu = 1$, so the terms $\pm n$ agree;
- `continuous_thetaTwist`, `norm_thetaTwist_le`: continuity on $\mathbb H$ and $|\theta_{\psi,t}(z)| \le C(1+y^{-2})$;
- `integral_mul_conj_thetaTwist`: for $f = \sum a(n)q^n$ with $a(0) = 0$,
  $\int_0^1 f(x+iy)\overline{\theta_{\psi,t}(x+iy)}\,dx = \sum_{m}2\psi(m)a(tm^2)m^\nu e^{-4\pi tm^2y}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import ModularFormsKB.HalfIntegral.Abstract.FourierLine
import Mathlib.Analysis.Real.Pi.Bounds

namespace ModularFormsKB.HalfIntegral

open Complex MeasureTheory Set
open scoped Real

local notation "ℍ" => UpperHalfPlane

theorem charParity_le_one {r : ℕ} (ψ : DirichletCharacter ℂ r) : charParity ψ ≤ 1 := by
  unfold charParity
  split_ifs <;> simp

/-- $\psi(-1)(-1)^\nu = 1$. -/
theorem apply_neg_one_mul_pow_charParity {r : ℕ} (ψ : DirichletCharacter ℂ r) :
    ψ (-1) * (-1 : ℂ) ^ charParity ψ = 1 := by
  unfold charParity
  by_cases h : ψ (-1) = 1
  · simp [h]
  · have h2 : ψ (-1) * ψ (-1) = 1 := by
      rw [← map_mul]; simp
    have h3 : (ψ (-1) - 1) * (ψ (-1) + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) h
    · have : ψ (-1) = -1 := eq_neg_of_add_eq_zero_left h4
      simp [h, this]

/-- $\bar\psi(-1)(-1)^\nu = 1$. -/
theorem inv_apply_neg_one_mul_pow_charParity {r : ℕ} (ψ : DirichletCharacter ℂ r) :
    ψ⁻¹ (-1) * (-1 : ℂ) ^ charParity ψ = 1 := by
  have h := apply_neg_one_mul_pow_charParity ψ
  have h2 : ψ⁻¹ (-1) = ψ (-1) := by
    have h5 : ψ (-1) * ψ (-1) = 1 := by rw [← map_mul]; simp
    rw [MulChar.inv_apply_eq_inv']
    exact inv_eq_of_mul_eq_one_right h5
  rw [h2]; exact h

theorem stripPt_im {x y : ℝ} (hy : 0 < y) : (stripPt x y).im = y := by
  simp [stripPt, hy]

theorem stripPt_coe {x y : ℝ} (hy : 0 < y) : ((stripPt x y : ℍ) : ℂ) = x + y * I := by
  simp [stripPt, hy]

private noncomputable def thB (y : ℝ) (n : ℤ) : ℝ := ((n.natAbs : ℝ) + 1) * Real.exp (-2 * π * y) ^ n.natAbs

private lemma thB_neg (y : ℝ) (n : ℤ) : thB y (-n) = thB y n := by simp [thB]

private lemma exp_neg_two_pi_lt_one {y : ℝ} (hy : 0 < y) : Real.exp (-2 * π * y) < 1 := by
  rw [Real.exp_lt_one_iff]  
  have := Real.pi_pos
  nlinarith

private lemma thB_anti {y y' : ℝ} (hy : 0 < y) (h : y ≤ y') (n : ℤ) : thB y' n ≤ thB y n := by
  unfold thB
  have hp := Real.pi_pos
  have : Real.exp (-2 * π * y') ≤ Real.exp (-2 * π * y) := Real.exp_le_exp.2 (by nlinarith)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le this _) (by positivity)

private lemma term_norm_le {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) (z : ℍ) (n : ℤ) :
    ‖ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * z)‖ ≤ thB z.im n := by
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have h1 : ‖ψ⁻¹ (n : ZMod r)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖(n : ℂ) ^ charParity ψ‖ ≤ (n.natAbs : ℝ) + 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (charParity_le_one ψ) with h | h <;> rw [h]
    · simp
    · simp
  have hsq : (n.natAbs : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
    have : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
    rw [this, sq_abs]
  have h3 : (2 * π * I * t * (n : ℂ) ^ 2 * z).re = -(2 * π * t * (n.natAbs : ℝ) ^ 2 * z.im) := by
    have : ((n : ℂ)) ^ 2 = (((n.natAbs : ℝ) ^ 2 : ℝ) : ℂ) := by rw [hsq]; push_cast; ring
    rw [this]
    generalize (n.natAbs : ℝ) ^ 2 = m
    simp [Complex.mul_re, Complex.mul_im]
  have h4 : Real.exp (2 * π * I * t * (n : ℂ) ^ 2 * z).re ≤ Real.exp (-2 * π * z.im) ^ n.natAbs := by
    rw [h3, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hp := Real.pi_pos
    have hy := z.im_pos
    have hk : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hn : (n.natAbs : ℝ) ≤ (n.natAbs : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n.natAbs with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n.natAbs := by exact_mod_cast h
        nlinarith
    have : (n.natAbs : ℝ) * (2 * π * z.im) ≤ t * (n.natAbs : ℝ) ^ 2 * (2 * π * z.im) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (n.natAbs : ℝ), Nat.cast_nonneg (α := ℝ) n.natAbs]
    nlinarith
  unfold thB
  calc _ ≤ 1 * (((n.natAbs : ℝ) + 1)) * Real.exp (-2 * π * z.im) ^ n.natAbs := by
        gcongr
    _ = _ := by ring

private lemma summable_thB {y : ℝ} (hy : 0 < y) : Summable (thB y) := by
  set r := Real.exp (-2 * π * y) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := exp_neg_two_pi_lt_one hy
  have hn : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; exact hr1
  have hs : Summable fun n : ℕ ↦ ((n : ℝ) + 1) * r ^ n := by
    have := (hasSum_coe_mul_geometric_of_norm_lt_one hn).summable.add (summable_geometric_of_norm_lt_one hn)
    refine this.congr fun n ↦ ?_
    ring
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hs.congr fun n ↦ ?_
    simp only [thB, Int.natAbs_natCast]
    rfl
  · have := (summable_nat_add_iff 1).2 hs
    refine this.congr fun n ↦ ?_
    have e : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e, thB_neg]
    simp only [thB, Int.natAbs_natCast]
    push_cast
    rfl

private lemma tsum_thB_le {y : ℝ} (hy : 0 < y) : ∑' n, thB y n ≤ 8 * (1 + y ^ (-2 : ℝ)) := by
  set r := Real.exp (-2 * π * y) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := exp_neg_two_pi_lt_one hy
  have hn : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; exact hr1
  have hS : HasSum (fun n : ℕ ↦ ((n : ℝ) + 1) * r ^ n) (r / (1 - r) ^ 2 + (1 - r)⁻¹) := by
    have := (hasSum_coe_mul_geometric_of_norm_lt_one hn).add (hasSum_geometric_of_lt_one hr0 hr1)
    convert this using 2 with n
    ring
  have hb := (summable_thB hy).hasSum
  have hb2 := hb.nat_add_neg
  have hb3 : HasSum (fun n : ℕ ↦ thB y n + thB y (-n)) (2 * (r / (1 - r) ^ 2 + (1 - r)⁻¹)) := by
    have := hS.mul_left 2
    convert this using 2 with n
    rw [thB_neg]
    simp only [thB, Int.natAbs_natCast]
    rw [← hr]; ring
  have hT := hb2.unique hb3
  have h0 : thB y 0 = 1 := by simp [thB]
  have hTle : ∑' n, thB y n ≤ 2 * (r / (1 - r) ^ 2 + (1 - r)⁻¹) := by
    rw [h0] at hT; linarith
  -- estimate 1 - r from below
  have hexp : r ≤ 1 / (1 + y) := by
    have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h2 : r ≤ Real.exp (-y) := by
      rw [hr]; apply Real.exp_le_exp.2
      have := Real.pi_gt_three
      nlinarith
    rw [Real.exp_neg] at h2
    refine h2.trans ?_
    rw [one_div]
    exact inv_anti₀ (by positivity) h1
  have hy1 : y / (1 + y) ≤ 1 - r := by
    have : 1 - 1 / (1 + y) = y / (1 + y) := by field_simp; ring
    linarith
  have hpos : 0 < y / (1 + y) := by positivity
  have hpos' : 0 < 1 - r := by linarith
  have hw : (1 - r)⁻¹ ≤ 1 + 1 / y := by
    have : (1 - r)⁻¹ ≤ (y / (1 + y))⁻¹ := inv_anti₀ hpos hy1
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hw1 : 1 ≤ (1 - r)⁻¹ := by
    rw [one_le_inv₀ hpos']; linarith
  have e1 : r / (1 - r) ^ 2 ≤ ((1 - r)⁻¹) ^ 2 := by
    rw [inv_pow, div_eq_mul_inv]
    have : (0 : ℝ) ≤ ((1 - r) ^ 2)⁻¹ := by positivity
    nlinarith
  have e2 : (1 - r)⁻¹ ≤ ((1 - r)⁻¹) ^ 2 := by nlinarith
  have e3 : ((1 - r)⁻¹) ^ 2 ≤ (1 + 1 / y) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hw 2
  have e4 : (1 + 1 / y) ^ 2 ≤ 2 * (1 + y ^ (-2 : ℝ)) := by
    have : y ^ (-2 : ℝ) = (1 / y) ^ 2 := by
      rw [Real.rpow_neg hy.le, one_div, inv_pow]; norm_cast
    rw [this]
    nlinarith [sq_nonneg (1 - 1 / y)]
  nlinarith

/-- The terms of the twisted theta series are absolutely summable on $\mathbb H$. -/
theorem summable_norm_thetaTwist {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) (z : ℍ) :
    Summable fun n : ℤ ↦
      ‖ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * z)‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (term_norm_le ψ ht z) (summable_thB z.im_pos)

theorem continuous_thetaTwist {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) :
    Continuous fun τ : ℍ ↦ thetaTwist ψ t τ := by
  rw [continuous_iff_continuousAt]
  intro τ0
  have hopen : IsOpen {τ : ℍ | τ0.im / 2 < τ.im} :=
    isOpen_lt continuous_const UpperHalfPlane.continuous_im
  have h0 : 0 < τ0.im / 2 := half_pos τ0.im_pos
  have hon : ContinuousOn (fun τ : ℍ ↦ thetaTwist ψ t τ) {τ : ℍ | τ0.im / 2 < τ.im} := by
    unfold thetaTwist
    refine continuousOn_tsum (u := thB (τ0.im / 2)) (fun n ↦ ?_) (summable_thB h0) (fun n τ hτ ↦ ?_)
    · apply Continuous.continuousOn
      fun_prop
    · refine (term_norm_le ψ ht τ n).trans (thB_anti h0 (le_of_lt hτ) n)
  exact hon.continuousAt (hopen.mem_nhds (by simp; linarith))

/-- **A crude bound:** $|\theta_{\psi,t}(z)| \le C(1 + y^{-2})$ (from $|n|^\nu \le n^2$, $e^{-2\pi tn^2y} \le e^{-2\pi ny}$ and
$\sum_{n\ge1}ne^{-nx} \le x^{-2}$). -/
theorem norm_thetaTwist_le {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, ‖thetaTwist ψ t τ‖ ≤ C * (1 + τ.im ^ (-2 : ℝ)) := by
  refine ⟨8, by norm_num, fun τ ↦ ?_⟩
  unfold thetaTwist
  refine (norm_tsum_le_tsum_norm (summable_norm_thetaTwist ψ ht τ)).trans ?_
  refine le_trans ?_ (tsum_thB_le τ.im_pos)
  exact (summable_norm_thetaTwist ψ ht τ).tsum_le_tsum (term_norm_le ψ ht τ) (summable_thB τ.im_pos)

private lemma stripPt_eq {x y : ℝ} (hy : 0 < y) :
    stripPt x y = ⟨(x : ℂ) + y * I, by simpa using hy⟩ := by
  simp [stripPt, hy]

private lemma natAbs_cast_sq (n : ℤ) : ((n.natAbs : ℂ)) ^ 2 = (n : ℂ) ^ 2 := by
  simp only [Nat.cast_natAbs, Int.cast_abs]
  rcases abs_choice n with h | h <;> simp [h]

private lemma ii_conj (g : ℝ → ℂ) :
    (starRingEnd ℂ) (∫ x in (0 : ℝ)..1, g x) = ∫ x in (0 : ℝ)..1, (starRingEnd ℂ) (g x) := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  exact integral_conj.symm

private lemma integral_term {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a)
    {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} {y : ℝ} (hy : 0 < y) (n : ℤ) :
    ∫ x in (0 : ℝ)..1, f (stripPt x y) * (starRingEnd ℂ)
        (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * (stripPt x y : ℍ))) =
      (starRingEnd ℂ) (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ) *
        (a (t * n.natAbs ^ 2) * ((Real.exp (-4 * π * ((t * n.natAbs ^ 2 : ℕ) : ℝ) * y) : ℝ) : ℂ)) := by
  have key := integral_conj_mul_exp_of_hasQExp hf hy (t * n.natAbs ^ 2)
  have key2 := congrArg (starRingEnd ℂ) key
  rw [ii_conj] at key2
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at key2
  have hcast : ((t * n.natAbs ^ 2 : ℕ) : ℂ) = t * (n : ℂ) ^ 2 := by
    push_cast; rw [natAbs_cast_sq]
  have : ∀ x : ℝ, f (stripPt x y) * (starRingEnd ℂ)
        (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * (stripPt x y : ℍ))) =
      (starRingEnd ℂ) (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ) *
        (f ⟨(x : ℂ) + y * I, by simpa using hy⟩ * (starRingEnd ℂ)
          (cexp (2 * π * I * ((t * n.natAbs ^ 2 : ℕ) : ℂ) * ((x : ℂ) + y * I)))) := by
    intro x
    rw [stripPt_eq hy, hcast]
    simp only [UpperHalfPlane.coe_mk, map_mul]
    ring_nf
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  congr 1

private lemma norm_qterm (c : ℂ) (n : ℕ) (z : ℂ) :
    ‖c * cexp (2 * π * I * n * z)‖ = ‖c‖ * Real.exp (-2 * π * n * z.im) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]

private lemma norm_f_le {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) {y : ℝ} (hy : 0 < y)
    (τ : ℍ) (hτ : τ.im = y) : ‖f τ‖ ≤ ∑' n : ℕ, ‖a n‖ * Real.exp (-2 * π * n * y) := by
  have hs : Summable fun n : ℕ ↦ ‖a n * cexp (2 * π * I * n * (τ : ℂ))‖ := by
    refine (summable_of_hasQExp hf hy).congr fun n ↦ ?_
    rw [norm_qterm]; simp [hτ]
  calc ‖f τ‖ = ‖∑' n : ℕ, a n * cexp (2 * π * I * n * (τ : ℂ))‖ := by rw [(hf τ).tsum_eq]
    _ ≤ ∑' n : ℕ, ‖a n * cexp (2 * π * I * n * (τ : ℂ))‖ := norm_tsum_le_tsum_norm hs
    _ = _ := by
      refine tsum_congr fun n ↦ ?_
      rw [norm_qterm]; simp [hτ]

private lemma continuous_f_line {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ ↦ f (stripPt x y) := by
  have h : (fun x : ℝ ↦ f (stripPt x y)) = fun x : ℝ ↦ ∑' n : ℕ, a n * cexp (2 * π * I * n * ((x : ℂ) + y * I)) := by
    funext x
    rw [← stripPt_coe hy, (hf _).tsum_eq]
  rw [h]
  refine continuous_tsum (u := fun n : ℕ ↦ ‖a n‖ * Real.exp (-2 * π * n * y)) (fun n ↦ by fun_prop)
    (summable_of_hasQExp hf hy) (fun n x ↦ ?_)
  rw [norm_qterm]; simp

private lemma conj_coeff {r : ℕ} (ψ : DirichletCharacter ℂ r) (n : ℤ) :
    (starRingEnd ℂ) (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ) = ψ (n : ZMod r) * (n : ℂ) ^ charParity ψ := by
  have hc : (starRingEnd ℂ) (n : ℂ) = n := by simp
  rw [map_mul, map_pow, hc]
  congr 1
  have := MulChar.star_apply' (ψ⁻¹) (n : ZMod r)
  rw [inv_inv] at this
  exact this

private lemma coeff_neg {r : ℕ} (ψ : DirichletCharacter ℂ r) (m : ℕ) :
    ψ (((-(m : ℤ) : ℤ)) : ZMod r) * (((-(m : ℤ) : ℤ)) : ℂ) ^ charParity ψ =
      ψ ((m : ℤ) : ZMod r) * ((m : ℤ) : ℂ) ^ charParity ψ := by
  have h := apply_neg_one_mul_pow_charParity ψ
  have e1 : (((-(m : ℤ) : ℤ)) : ZMod r) = (-1) * ((m : ℤ) : ZMod r) := by push_cast; ring
  have e2 : (((-(m : ℤ) : ℤ)) : ℂ) = (-1) * ((m : ℤ) : ℂ) := by push_cast; ring
  rw [e1, e2, map_mul, mul_pow]
  linear_combination (ψ ((m : ℤ) : ZMod r) * ((m : ℤ) : ℂ) ^ charParity ψ) * h

/-- **The line integral against a cusp form:** for $f = \sum a(n)q^n$ with $a(0) = 0$ and $y > 0$,
$\int_0^1 f(x+iy)\,\overline{\theta_{\psi,t}(x+iy)}\,dx = \sum_{m\ge0}2\psi(m)a(tm^2)m^\nu e^{-4\pi tm^2y}$. -/
theorem integral_mul_conj_thetaTwist {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) (ha0 : a 0 = 0)
    {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, f (stripPt x y) * (starRingEnd ℂ) (thetaTwist ψ t (stripPt x y)) =
      ∑' m : ℕ, 2 * (twist ψ (fun m ↦ a (t * m ^ 2)) m * (m : ℂ) ^ charParity ψ) *
        ((Real.exp (-4 * π * t * m ^ 2 * y) : ℝ) : ℂ) := by
  set B := ∑' n : ℕ, ‖a n‖ * Real.exp (-2 * π * n * y) with hB
  set G : ℤ → ℂ := fun n ↦ (starRingEnd ℂ) (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ) *
    (a (t * n.natAbs ^ 2) * ((Real.exp (-4 * π * ((t * n.natAbs ^ 2 : ℕ) : ℝ) * y) : ℝ) : ℂ)) with hG
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
    (F := fun (n : ℤ) (x : ℝ) ↦ f (stripPt x y) * (starRingEnd ℂ)
      (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * (stripPt x y : ℍ))))
    (fun n _ ↦ B * thB y n)
    (fun n ↦ by
      refine ((continuous_f_line hf hy).mul ?_).aestronglyMeasurable
      have : (fun x : ℝ ↦ (starRingEnd ℂ)
          (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * (stripPt x y : ℍ)))) =
          fun x : ℝ ↦ (starRingEnd ℂ)
          (ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ * cexp (2 * π * I * t * (n : ℂ) ^ 2 * ((x : ℂ) + y * I))) := by
        funext x; rw [stripPt_coe hy]
      rw [this]
      fun_prop)
    (fun n ↦ Filter.Eventually.of_forall fun x _ ↦ by
      rw [norm_mul, RCLike.norm_conj]
      have h1 := norm_f_le hf hy (stripPt x y) (stripPt_im hy)
      have h2 := term_norm_le ψ ht (stripPt x y) n
      rw [stripPt_im hy] at h2
      exact mul_le_mul h1 h2 (norm_nonneg _) (by
        rw [hB]; exact tsum_nonneg fun k ↦ by positivity))
    (Filter.Eventually.of_forall fun x _ ↦ (summable_thB hy).mul_left B)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun x _ ↦ by
      have h1 : HasSum (fun n : ℤ ↦ ψ⁻¹ (n : ZMod r) * (n : ℂ) ^ charParity ψ *
          cexp (2 * π * I * t * (n : ℂ) ^ 2 * (stripPt x y : ℍ))) (thetaTwist ψ t (stripPt x y)) :=
        (summable_norm_thetaTwist ψ ht (stripPt x y)).of_norm.hasSum
      exact (Complex.hasSum_conj'.mpr h1).mul_left (f (stripPt x y)))
  have hdom2 : HasSum G (∫ x in (0 : ℝ)..1, f (stripPt x y) * (starRingEnd ℂ) (thetaTwist ψ t (stripPt x y))) := by
    convert hdom using 1
    funext n
    exact (integral_term hf ψ hy n).symm
  have hnat := hdom2.nat_add_neg
  have hG0 : G 0 = 0 := by simp [hG, ha0]
  have hGneg : ∀ m : ℕ, G (-(m : ℤ)) = G m := by
    intro m
    simp only [hG, conj_coeff, Int.natAbs_neg, Int.natAbs_natCast]
    rw [coeff_neg]
  rw [hG0, add_zero] at hnat
  rw [← hnat.tsum_eq]
  refine tsum_congr fun m ↦ ?_
  rw [hGneg m]
  simp only [hG, conj_coeff, Int.natAbs_natCast, twist]
  push_cast
  ring_nf

end ModularFormsKB.HalfIntegral
