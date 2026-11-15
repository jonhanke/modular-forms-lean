import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open Complex Filter Topology
open scoped Real Nat

namespace ModularFormsKB.Historical.Eisenstein

local notation "ℂ_ℤ" => Complex.integerComplement

/-- Local summability bound near a point off the integers. -/
lemma differentiableAt_zpowSum {m : ℕ} (hm : 2 ≤ m) {x : ℂ} (hx : x ∈ ℂ_ℤ) :
    DifferentiableAt ℂ (fun z : ℂ ↦ ∑' n : ℤ, 1 / (z + n) ^ m) x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_compl_range_intCast x hx
  have hlow : ∀ n : ℤ, ε ≤ ‖x + n‖ := by
    intro n
    by_contra h
    rw [not_le] at h
    have : (-(n : ℂ)) ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show -(n : ℂ) - x = -(x + n) by ring, norm_neg]
      exact h
    exact hball this ⟨-n, by simp⟩
  have hsum : Summable fun n : ℤ ↦ ‖((x * 1 + n) ^ (m : ℤ))⁻¹‖ := by
    rw [summable_norm_iff]
    simpa using EisensteinSeries.linear_right_summable x 1 (k := m) (by exact_mod_cast hm)
  have hu : Summable fun n : ℤ ↦ (2 : ℝ) ^ m * ‖((x * 1 + n) ^ (m : ℤ))⁻¹‖ := hsum.mul_left _
  have hhalf : ∀ n : ℤ, ∀ z ∈ Metric.ball x (ε / 2), ‖x + n‖ / 2 ≤ ‖z + n‖ := by
    intro n z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : ‖x + n‖ ≤ ‖z + n‖ + ‖z - x‖ := by
      calc ‖x + n‖ = ‖(z + n) - (z - x)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have := hlow n
    linarith
  have hne : ∀ n : ℤ, ∀ z ∈ Metric.ball x (ε / 2), z + n ≠ 0 := by
    intro n z hz h
    have := hhalf n z hz
    rw [h, norm_zero] at this
    have := hlow n
    linarith
  have hD : DifferentiableOn ℂ (fun z : ℂ ↦ ∑' n : ℤ, 1 / (z + n) ^ m) (Metric.ball x (ε / 2)) := by
    refine differentiableOn_tsum_of_summable_norm hu ?_ Metric.isOpen_ball ?_
    · intro n z hz
      have hd : DifferentiableAt ℂ (fun w : ℂ ↦ (w + n) ^ m) z := by fun_prop
      exact ((differentiableAt_const (1 : ℂ)).div hd (pow_ne_zero _ (hne n z hz))).differentiableWithinAt
    · intro n z hz
      have h1 := hhalf n z hz
      have hpos : 0 < ‖x + n‖ := lt_of_lt_of_le hε (hlow n)
      have h2 : ‖(1 : ℂ) / (z + n) ^ m‖ = (‖z + n‖ ^ m)⁻¹ := by simp
      have h3 : ‖((x * 1 + n) ^ (m : ℤ))⁻¹‖ = (‖x + n‖ ^ m)⁻¹ := by simp
      rw [h2, h3]
      have hpos2 : 0 < ‖x + n‖ / 2 := by positivity
      have h4 : (‖x + n‖ / 2) ^ m ≤ ‖z + n‖ ^ m := pow_le_pow_left₀ hpos2.le h1 m
      calc (‖z + n‖ ^ m)⁻¹ ≤ ((‖x + n‖ / 2) ^ m)⁻¹ := inv_anti₀ (by positivity) h4
        _ = 2 ^ m * (‖x + n‖ ^ m)⁻¹ := by rw [div_pow]; field_simp
  exact (hD.differentiableAt (Metric.ball_mem_nhds _ (by linarith)))


lemma analyticOnNhd_zpowSum {m : ℕ} (hm : 2 ≤ m) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' n : ℤ, 1 / (z + n) ^ m) ℂ_ℤ :=
  DifferentiableOn.analyticOnNhd
    (fun x hx ↦ (differentiableAt_zpowSum hm hx).differentiableWithinAt) isOpen_compl_range_intCast

lemma isPreconnected_integerComplement : IsPreconnected ℂ_ℤ := by
  have := (Set.countable_range ((↑) : ℤ → ℂ)).isConnected_compl_of_one_lt_rank
    (by simp [Complex.rank_real_complex])
  exact this.isPreconnected

lemma analyticOnNhd_cot_pi_mul : AnalyticOnNhd ℂ (fun z : ℂ ↦ (π : ℂ) * Complex.cot (π * z)) ℂ_ℤ := by
  refine DifferentiableOn.analyticOnNhd (fun x hx ↦ ?_) isOpen_compl_range_intCast
  have hs : Complex.sin ((π : ℂ) * x) ≠ 0 := sin_pi_mul_ne_zero hx
  have hc : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.cos ((π : ℂ) * z)) x := by fun_prop
  have hsn : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.sin ((π : ℂ) * z)) x := by fun_prop
  have : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.cos ((π : ℂ) * z) / Complex.sin ((π : ℂ) * z)) x :=
    hc.div hsn hs
  simp only [Complex.cot]
  exact (this.const_mul _).differentiableWithinAt

lemma core_cot_series {k : ℕ} (hk : 1 ≤ k) {x : ℂ} (hx : x ∈ ℂ_ℤ) :
    iteratedDeriv k (fun z : ℂ ↦ (π : ℂ) * Complex.cot (π * z)) x =
      (-1) ^ k * k ! * ∑' n : ℤ, 1 / (x + n) ^ (k + 1) := by
  have h1 : AnalyticOnNhd ℂ (iteratedDeriv k (fun z : ℂ ↦ (π : ℂ) * Complex.cot (π * z))) ℂ_ℤ := by
    simpa [iteratedDeriv_eq_iterate] using analyticOnNhd_cot_pi_mul.iterated_deriv k
  have h2 : AnalyticOnNhd ℂ (fun z : ℂ ↦ (-1) ^ k * k ! * ∑' n : ℤ, 1 / (z + n) ^ (k + 1)) ℂ_ℤ :=
    analyticOnNhd_const.mul (analyticOnNhd_zpowSum (m := k + 1) (by omega))
  have hI : (I : ℂ) ∈ ℂ_ℤ := UpperHalfPlane.coe_mem_integerComplement ⟨I, by simp⟩
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_integerComplement hI ?_ hx
  have hmem : (I : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by simp [UpperHalfPlane.upperHalfPlaneSet]
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hmem] with z hz
  rw [← iteratedDerivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz]
  exact iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk hz

lemma isOpen_sin_ne_zero : IsOpen {w : ℂ | Complex.sin w ≠ 0} :=
  isOpen_compl_singleton.preimage Complex.continuous_sin

lemma analyticOnNhd_cot : AnalyticOnNhd ℂ Complex.cot {w : ℂ | Complex.sin w ≠ 0} := by
  refine DifferentiableOn.analyticOnNhd (fun x hx ↦ ?_) isOpen_sin_ne_zero
  have hx' : Complex.sin x ≠ 0 := hx
  have h1 : DifferentiableAt ℂ Complex.cos x := Complex.differentiable_cos x
  have h2 : DifferentiableAt ℂ Complex.sin x := Complex.differentiable_sin x
  have : DifferentiableAt ℂ (fun z : ℂ ↦ Complex.cos z / Complex.sin z) x := h1.div h2 hx'
  have e : Complex.cot = fun z : ℂ ↦ Complex.cos z / Complex.sin z := by
    funext z; rw [Complex.cot]
  rw [e]
  exact this.differentiableWithinAt

lemma analyticOnNhd_cot_comp :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ Complex.cot ((π : ℂ) * z)) ℂ_ℤ :=
  analyticOnNhd_cot.comp (f := fun z : ℂ ↦ (π : ℂ) * z) (analyticOnNhd_const.mul analyticOnNhd_id)
    (fun z hz ↦ sin_pi_mul_ne_zero hz)

lemma iteratedDeriv_cot_comp {k : ℕ} {x : ℂ} (hx : x ∈ ℂ_ℤ) :
    iteratedDeriv k (fun z : ℂ ↦ Complex.cot ((π : ℂ) * z)) x =
      (π : ℂ) ^ k * iteratedDeriv k Complex.cot ((π : ℂ) * x) := by
  have h1 : AnalyticOnNhd ℂ (iteratedDeriv k (fun z : ℂ ↦ Complex.cot ((π : ℂ) * z))) ℂ_ℤ := by
    simpa [iteratedDeriv_eq_iterate] using analyticOnNhd_cot_comp.iterated_deriv k
  have h2 : AnalyticOnNhd ℂ (fun z : ℂ ↦ (π : ℂ) ^ k * iteratedDeriv k Complex.cot ((π : ℂ) * z))
      ℂ_ℤ := by
    have h3 : AnalyticOnNhd ℂ (iteratedDeriv k Complex.cot) {w : ℂ | Complex.sin w ≠ 0} := by
      simpa [iteratedDeriv_eq_iterate] using analyticOnNhd_cot.iterated_deriv k
    exact analyticOnNhd_const.mul (h3.comp (f := fun z : ℂ ↦ (π : ℂ) * z)
      (analyticOnNhd_const.mul analyticOnNhd_id) (fun z hz ↦ sin_pi_mul_ne_zero hz))
  have hI : (I : ℂ) ∈ ℂ_ℤ := UpperHalfPlane.coe_mem_integerComplement ⟨I, by simp⟩
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 isPreconnected_integerComplement hI ?_ hx
  have hmem : (I : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by simp [UpperHalfPlane.upperHalfPlaneSet]
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hmem] with z hz
  have hcd : ContDiffOn ℂ k Complex.cot UpperHalfPlane.upperHalfPlaneSet := by
    refine (analyticOnNhd_cot.contDiffOn (n := k) (isOpen_sin_ne_zero.uniqueDiffOn)).mono ?_
    intro w hw
    have hw' : 0 < w.im := hw
    have hz : w / (π : ℂ) ∈ ℂ_ℤ :=
      UpperHalfPlane.coe_mem_integerComplement ⟨w / (π : ℂ), by
        simp [Complex.div_ofReal_im, hw', Real.pi_pos]⟩
    have := sin_pi_mul_ne_zero hz
    rwa [mul_div_cancel₀ _ (by exact_mod_cast Real.pi_pos.ne')] at this
  have hs : Set.MapsTo (fun x : ℂ ↦ (π : ℂ) * x) UpperHalfPlane.upperHalfPlaneSet
      UpperHalfPlane.upperHalfPlaneSet := by
    intro w hw
    simp only [UpperHalfPlane.upperHalfPlaneSet, Set.mem_setOf_eq] at hw ⊢
    simp [hw, Real.pi_pos]
  have := iteratedDerivWithin_comp_const_smul hz UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
    hcd (π : ℂ) hs
  rw [iteratedDerivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz] at this
  rw [iteratedDerivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet
    (hs hz)] at this
  simpa using this

/-- The `k`-th derivative of the cotangent as a lattice sum, valid on the whole of `ℂ ∖ ℤ`. -/
lemma tsum_inv_pow_eq_iteratedDeriv_cot {k : ℕ} (hk : 1 ≤ k) {x : ℂ} (hx : x ∈ ℂ_ℤ) :
    ∑' n : ℤ, 1 / (x + n) ^ (k + 1) =
      (-1) ^ k / k ! * (π : ℂ) ^ (k + 1) * iteratedDeriv k Complex.cot ((π : ℂ) * x) := by
  have h := core_cot_series hk hx
  rw [iteratedDeriv_const_mul (π : ℂ) (analyticOnNhd_cot_comp x hx).contDiffAt,
    iteratedDeriv_cot_comp hx] at h
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
  have hm : ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; simp
  rw [pow_succ]
  generalize ∑' (n : ℤ), 1 / (x + ↑n) ^ (k + 1) = S at h ⊢
  generalize iteratedDeriv k Complex.cot ((π : ℂ) * x) = D at h ⊢
  have e : S = (-1) ^ k / (k ! : ℂ) * ((-1) ^ k * k ! * S) := by
    field_simp
    linear_combination (-S) * hm
  rw [e, ← h]
  ring

/-! ### Limits of the cotangent along vertical directions -/

lemma cot_eq_exp_ratio_neg (z : ℂ) :
    Complex.cot z = (1 + Complex.exp (-(2 * I * z))) / (I * (Complex.exp (-(2 * I * z)) - 1)) := by
  rw [Complex.cot_eq_exp_ratio, Complex.exp_neg]
  have he : Complex.exp (2 * I * z) ≠ 0 := Complex.exp_ne_zero _
  generalize Complex.exp (2 * I * z) = e at he ⊢
  by_cases h1 : e = 1
  · simp [h1]
  · have h2 : e - 1 ≠ 0 := sub_ne_zero.2 h1
    have h3 : 1 - e ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have h4 : e⁻¹ - 1 ≠ 0 := by
      intro h; apply h1; field_simp at h; linear_combination -h
    field_simp

lemma tendsto_cot_of_im_atTop {z : ℕ → ℂ} (h : Tendsto (fun l ↦ (z l).im) atTop atTop) :
    Tendsto (fun l ↦ Complex.cot (z l)) atTop (𝓝 (-I)) := by
  have he : Tendsto (fun l ↦ Complex.exp (2 * I * z l)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp]
    refine Real.tendsto_exp_atBot.comp ?_
    have : ∀ l, (2 * I * z l).re = -2 * (z l).im := fun l ↦ by simp
    simp_rw [this]
    exact h.const_mul_atTop_of_neg (by norm_num)
  have := (he.add_const 1).div (tendsto_const_nhds.mul (tendsto_const_nhds.sub he))
    (show I * (1 - 0) ≠ (0 : ℂ) by simp)
  have e : ((0 : ℂ) + 1) / (I * (1 - 0)) = -I := by simp
  rw [e] at this
  refine this.congr fun l ↦ ?_
  simp only [Pi.div_apply, Complex.cot_eq_exp_ratio]

lemma tendsto_cot_of_im_atBot {z : ℕ → ℂ} (h : Tendsto (fun l ↦ (z l).im) atTop atBot) :
    Tendsto (fun l ↦ Complex.cot (z l)) atTop (𝓝 I) := by
  have he : Tendsto (fun l ↦ Complex.exp (-(2 * I * z l))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Complex.norm_exp]
    refine Real.tendsto_exp_atBot.comp ?_
    have : ∀ l, (-(2 * I * z l)).re = 2 * (z l).im := fun l ↦ by simp
    simp_rw [this]
    exact h.const_mul_atBot (by norm_num)
  have := ((he.const_add 1)).div (tendsto_const_nhds.mul (he.sub_const 1))
    (show I * (0 - 1) ≠ (0 : ℂ) by simp)
  have e : ((1 : ℂ) + 0) / (I * (0 - 1)) = I := by simp
  rw [e] at this
  refine this.congr fun l ↦ ?_
  simp only [Pi.div_apply, cot_eq_exp_ratio_neg]

/-! ### The weight-two inner sum and its decay -/

lemma inner_tsum_eq_cot {α c : ℂ} (hα : α ≠ 0) (hc : ∀ m : ℤ, α * m + c ≠ 0) {k : ℕ}
    (hk : 1 ≤ k) :
    ∑' m : ℤ, 1 / (α * m + c) ^ (k + 1) =
      (-1) ^ k * (π : ℂ) ^ (k + 1) / (k ! * α ^ (k + 1)) *
        iteratedDeriv k Complex.cot ((π : ℂ) * c / α) := by
  have hx : (c / α) ∈ ℂ_ℤ := by
    rintro ⟨j, hj⟩
    apply hc (-j)
    have : c = α * j := by rw [hj]; field_simp
    push_cast
    linear_combination this
  have h1 := tsum_inv_pow_eq_iteratedDeriv_cot hk hx
  have h2 : ∀ m : ℤ, 1 / (α * m + c) ^ (k + 1) =
      (1 / α ^ (k + 1)) * (1 / (c / α + m) ^ (k + 1)) := by
    intro m
    have : α * m + c = α * (c / α + m) := by field_simp; ring
    rw [this, mul_pow, one_div, one_div, one_div, mul_inv]
  simp_rw [h2]
  rw [tsum_mul_left, h1]
  have e : (π : ℂ) * (c / α) = π * c / α := by ring
  rw [e]
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

lemma deriv_cot_eq {z : ℂ} (hz : Complex.sin z ≠ 0) :
    deriv Complex.cot z = -(1 / Complex.sin z ^ 2) := by
  have h : HasDerivAt (fun z : ℂ ↦ Complex.cos z / Complex.sin z)
      ((-Complex.sin z * Complex.sin z - Complex.cos z * Complex.cos z) / Complex.sin z ^ 2) z :=
    (Complex.hasDerivAt_cos z).div (Complex.hasDerivAt_sin z) hz
  have e : Complex.cot = fun z : ℂ ↦ Complex.cos z / Complex.sin z := by
    funext z; rw [Complex.cot]
  rw [e, h.deriv]
  have := Complex.sin_sq_add_cos_sq z
  field_simp
  linear_combination -this

lemma norm_sin_lower (z : ℂ) (h : 1 ≤ |z.im|) : Real.exp |z.im| / 4 ≤ ‖Complex.sin z‖ := by
  have hs : Complex.sin z = (Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2 := by
    rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by simp [Complex.norm_exp]
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by simp [Complex.norm_exp]
  have h3 : |Real.exp z.im - Real.exp (-z.im)| ≤ ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ := by
    rw [← h1, ← h2]; exact abs_norm_sub_norm_le _ _
  have h4 : ‖Complex.sin z‖ = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
    rw [hs, norm_div, norm_mul, Complex.norm_I]; simp
  have he : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2; linarith
  have key : Real.exp |z.im| / 2 ≤ |Real.exp z.im - Real.exp (-z.im)| := by
    have hpos : 0 < Real.exp |z.im| := Real.exp_pos _
    have hmul : Real.exp |z.im| * Real.exp (-|z.im|) = 1 := by
      rw [← Real.exp_add]; simp
    have hge : Real.exp 2 ≤ Real.exp (2 * |z.im|) := Real.exp_le_exp.2 (by linarith)
    have hsq : Real.exp (2 * |z.im|) = Real.exp |z.im| * Real.exp |z.im| := by
      rw [two_mul, Real.exp_add]
    have hneg : Real.exp (-|z.im|) * 2 ≤ Real.exp |z.im| := by
      have : Real.exp (-|z.im|) * 2 * Real.exp |z.im| ≤ Real.exp |z.im| * Real.exp |z.im| := by
        nlinarith
      exact le_of_mul_le_mul_right (by linarith) hpos
    rcases le_total 0 z.im with hy | hy
    · rw [abs_of_nonneg hy] at hneg hpos ⊢
      rw [abs_of_nonneg (by have := Real.exp_le_exp.2 (show -z.im ≤ z.im by linarith); linarith)]
      linarith
    · rw [abs_of_nonpos hy] at hneg hpos ⊢
      rw [abs_of_nonpos (by have := Real.exp_le_exp.2 (show z.im ≤ -z.im by linarith); linarith)]
      simp only [neg_neg] at hneg
      linarith
  linarith

lemma summable_geom_int {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable fun n : ℤ ↦ r ^ n.natAbs := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩ <;> simpa using summable_geometric_of_lt_one h0 h1

/-! ### Absolute summability of the lattice sum of weight `g ≥ 3` (unshifted) -/

lemma summable_norm_lattice_upper {g : ℕ} (hg : 3 ≤ g) {ω : ℂ} (hω : 0 < ω.im) :
    Summable fun p : ℤ × ℤ ↦ ‖1 / ((π : ℂ) * ω * p.1 + π * p.2) ^ g‖ := by
  have h := EisensteinSeries.summable_norm_eisSummand (k := (g : ℤ)) (by exact_mod_cast hg)
    ⟨ω, hω⟩
  have h2 : Summable fun p : ℤ × ℤ ↦ ‖EisensteinSeries.eisSummand (g : ℤ) ![p.1, p.2] ⟨ω, hω⟩‖ := by
    have := (finTwoArrowEquiv ℤ).summable_iff (f := fun p : ℤ × ℤ ↦
      ‖EisensteinSeries.eisSummand (g : ℤ) ![p.1, p.2] ⟨ω, hω⟩‖)
    rw [← this]
    convert h using 2 with v
    simp only [Function.comp_apply, finTwoArrowEquiv_apply]
    congr 2
    ext i; fin_cases i <;> rfl
  refine (h2.mul_left ((π ^ g)⁻¹)).congr fun p ↦ ?_
  simp only [EisensteinSeries.eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one,
    UpperHalfPlane.coe_mk]
  have : (π : ℂ) * ω * p.1 + π * p.2 = π * (p.1 * ω + p.2) := by ring
  rw [this, mul_pow, one_div, norm_inv, norm_mul, norm_pow, Complex.norm_real, zpow_neg,
    zpow_natCast, norm_inv, norm_pow, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

lemma summable_norm_lattice {g : ℕ} (hg : 3 ≤ g) {ω : ℂ} (hω : ω.im ≠ 0) :
    Summable fun p : ℤ × ℤ ↦ ‖1 / ((π : ℂ) * ω * p.1 + π * p.2) ^ g‖ := by
  rcases lt_or_gt_of_ne hω with h | h
  · have h1 := summable_norm_lattice_upper hg (ω := -ω) (by simpa using h)
    have hinj : Function.Injective fun p : ℤ × ℤ ↦ (-p.1, p.2) := by
      intro p q hpq
      simp only [Prod.mk.injEq, neg_inj] at hpq
      exact Prod.ext hpq.1 hpq.2
    refine (h1.comp_injective hinj).congr fun p ↦ ?_
    simp only [Function.comp_apply]
    push_cast
    congr 3
    ring
  · exact summable_norm_lattice_upper hg h

end ModularFormsKB.Historical.Eisenstein
