import ModularFormsKB.Milne.Ch3.EllipticFunctions
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.Analysis.Contour.Winding.StarConvex
import TauCeti.Analysis.Contour.Winding.SegmentSum
import TauCeti.Analysis.Contour.Winding.Integer
import TauCeti.Analysis.Contour.Curve.Concat
import TauCeti.Analysis.Contour.LogDerivFTC

/-!
# Milne, Chapter 3: contour integration around a fundamental parallelogram

The boundary of the parallelogram `z₀ + [0,1]ω₁ + [0,1]ω₂`, traversed `z₀ → z₀ + ω₁ → z₀ + ω₁ + ω₂ →
z₀ + ω₂ → z₀`, as a closed piecewise-`C¹` curve `pgCurve L z₀` on `[0, 4]`; its winding number about
an interior point is `±1` (the sign of `Im(ω₂ ω̄₁)`); the residue theorem on the parallelogram (from Tau Ceti's
`TauCeti.Contour.classicalResidueTheorem_nullHomologous`); and the cancellation of opposite sides for a
doubly periodic integrand. These give Milne's Proposition 3.1 (`doublyPeriodicSumsStatement`), whose proof in
the book (pdf p. 42) is exactly this contour argument.
-/

open Complex Filter Topology Set PeriodPair MeasureTheory intervalIntegral
open TauCeti TauCeti.Contour

namespace ModularFormsKB.Milne

noncomputable section

variable (L : PeriodPair) (z₀ : ℂ)

/-! ### The boundary curve -/

/-- The four sides of the parallelogram, each parametrised affinely on an interval of length one. -/
def pgSide0 (t : ℝ) : ℂ := z₀ + (t : ℂ) * L.ω₁
/-- Second side. -/
def pgSide1 (t : ℝ) : ℂ := z₀ + L.ω₁ + ((t : ℂ) - 1) * L.ω₂
/-- Third side. -/
def pgSide2 (t : ℝ) : ℂ := z₀ + L.ω₂ + (3 - (t : ℂ)) * L.ω₁
/-- Fourth side. -/
def pgSide3 (t : ℝ) : ℂ := z₀ + (4 - (t : ℂ)) * L.ω₂

/-- The boundary of the parallelogram, a closed curve on `[0, 4]`. -/
def pgCurve (t : ℝ) : ℂ :=
  if t ≤ 1 then pgSide0 L z₀ t else if t ≤ 2 then pgSide1 L z₀ t else if t ≤ 3 then pgSide2 L z₀ t
    else pgSide3 L z₀ t

variable {L z₀}

theorem hasDerivAt_affine (c v : ℂ) (k : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ c + ((t : ℂ) - k) * v) v t := by
  have := ((hasDerivAt_id t).ofReal_comp.sub_const k).mul_const v
  simpa using this.const_add c

theorem hasDerivAt_affine' (c v : ℂ) (k : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ c + (k - (t : ℂ)) * v) (-v) t := by
  have := ((hasDerivAt_id t).ofReal_comp.const_sub k).mul_const v
  simpa using this.const_add c

theorem pgSide0_eq : pgSide0 L z₀ = fun t : ℝ ↦ z₀ + ((t : ℂ) - 0) * L.ω₁ := by
  funext t; simp [pgSide0]

theorem pgSide1_eq : pgSide1 L z₀ = fun t : ℝ ↦ (z₀ + L.ω₁) + ((t : ℂ) - 1) * L.ω₂ := by
  funext t; simp [pgSide1]

theorem pgSide2_eq : pgSide2 L z₀ = fun t : ℝ ↦ (z₀ + L.ω₂) + (3 - (t : ℂ)) * L.ω₁ := by
  funext t; simp [pgSide2]

theorem pgSide3_eq : pgSide3 L z₀ = fun t : ℝ ↦ z₀ + (4 - (t : ℂ)) * L.ω₂ := by
  funext t; simp [pgSide3]

theorem deriv_pgSide0 (t : ℝ) : deriv (pgSide0 L z₀) t = L.ω₁ := by
  rw [pgSide0_eq]; exact (hasDerivAt_affine _ _ _ t).deriv

theorem deriv_pgSide1 (t : ℝ) : deriv (pgSide1 L z₀) t = L.ω₂ := by
  rw [pgSide1_eq]; exact (hasDerivAt_affine _ _ _ t).deriv

theorem deriv_pgSide2 (t : ℝ) : deriv (pgSide2 L z₀) t = -L.ω₁ := by
  rw [pgSide2_eq]; exact (hasDerivAt_affine' _ _ _ t).deriv

theorem deriv_pgSide3 (t : ℝ) : deriv (pgSide3 L z₀) t = -L.ω₂ := by
  rw [pgSide3_eq]; exact (hasDerivAt_affine' _ _ _ t).deriv

@[fun_prop] theorem contDiff_ofReal_one : ContDiff ℝ 1 (fun t : ℝ ↦ (t : ℂ)) := ofRealCLM.contDiff

theorem contDiff_pgSide0 : ContDiff ℝ 1 (pgSide0 L z₀) := by unfold pgSide0; fun_prop
theorem contDiff_pgSide1 : ContDiff ℝ 1 (pgSide1 L z₀) := by unfold pgSide1; fun_prop
theorem contDiff_pgSide2 : ContDiff ℝ 1 (pgSide2 L z₀) := by unfold pgSide2; fun_prop
theorem contDiff_pgSide3 : ContDiff ℝ 1 (pgSide3 L z₀) := by unfold pgSide3; fun_prop

theorem isPiecewiseC1On_pgCurve : IsPiecewiseC1On (pgCurve L z₀) 0 4 := by
  have h3 : IsPiecewiseC1On (fun t ↦ if t ≤ 3 then pgSide2 L z₀ t else pgSide3 L z₀ t) 2 4 :=
    (IsPiecewiseC1On.of_contDiffOn contDiff_pgSide2.contDiffOn).if_le
      (IsPiecewiseC1On.of_contDiffOn contDiff_pgSide3.contDiffOn) (by norm_num) (by norm_num)
      (by simp [pgSide2, pgSide3]; norm_num)
  have h2 : IsPiecewiseC1On (fun t ↦ if t ≤ 2 then pgSide1 L z₀ t else
      if t ≤ 3 then pgSide2 L z₀ t else pgSide3 L z₀ t) 1 4 :=
    (IsPiecewiseC1On.of_contDiffOn contDiff_pgSide1.contDiffOn).if_le h3 (by norm_num) (by norm_num)
      (by simp [pgSide1, pgSide2]; norm_num; ring)
  exact (IsPiecewiseC1On.of_contDiffOn contDiff_pgSide0.contDiffOn).if_le h2 (by norm_num)
    (by norm_num) (by simp [pgSide0, pgSide1])

theorem pgCurve_closed : pgCurve L z₀ 0 = pgCurve L z₀ 4 := by
  simp [pgCurve, pgSide0, pgSide3]; norm_num

theorem pgCurve_eqOn0 : EqOn (pgCurve L z₀) (pgSide0 L z₀) (Icc 0 1) := fun t ht ↦ by
  simp [pgCurve, ht.2]

theorem pgCurve_eqOn1 : EqOn (pgCurve L z₀) (pgSide1 L z₀) (Icc 1 2) := fun t ht ↦ by
  rcases ht.1.eq_or_lt with rfl | h
  · simp [pgCurve, pgSide0, pgSide1]
  · simp [pgCurve, not_le.2 h, ht.2]

theorem pgCurve_eqOn2 : EqOn (pgCurve L z₀) (pgSide2 L z₀) (Icc 2 3) := fun t ht ↦ by
  rcases ht.1.eq_or_lt with rfl | h
  · simp [pgCurve, pgSide1, pgSide2]; norm_num; ring
  · simp [pgCurve, not_le.2 h, not_le.2 (by linarith : (1 : ℝ) < t), ht.2]

theorem pgCurve_eqOn3 : EqOn (pgCurve L z₀) (pgSide3 L z₀) (Icc 3 4) := fun t ht ↦ by
  rcases ht.1.eq_or_lt with rfl | h
  · simp [pgCurve, pgSide2, pgSide3]; norm_num
  · simp [pgCurve, not_le.2 h, not_le.2 (by linarith : (1 : ℝ) < t),
      not_le.2 (by linarith : (2 : ℝ) < t)]

/-- The contour integral around the parallelogram is the sum of the four side integrals. -/
theorem integral_pgCurve (f : ℂ → ℂ) (hf : ContinuousOn f (pgCurve L z₀ '' Icc 0 4)) :
    ∫ t in (0 : ℝ)..4, deriv (pgCurve L z₀) t • f (pgCurve L z₀ t) =
      (∫ t in (0 : ℝ)..1, L.ω₁ * f (pgSide0 L z₀ t)) + (∫ t in (1 : ℝ)..2, L.ω₂ * f (pgSide1 L z₀ t)) +
      (∫ t in (2 : ℝ)..3, -L.ω₁ * f (pgSide2 L z₀ t)) + ∫ t in (3 : ℝ)..4, -L.ω₂ * f (pgSide3 L z₀ t) := by
  have hint : ∀ (e : ℝ → ℂ) (v : ℂ) (a b : ℝ), a ≤ b → (∀ t, deriv e t = v) → Continuous e →
      EqOn (pgCurve L z₀) e (Icc a b) → Icc a b ⊆ Icc 0 4 →
      IntervalIntegrable (fun t ↦ deriv e t • f (e t)) volume a b := by
    intro e v a b hab hd he heq hsub
    simp only [hd, smul_eq_mul]
    refine (ContinuousOn.mul continuousOn_const ?_).intervalIntegrable
    rw [uIcc_of_le hab]
    refine hf.comp he.continuousOn fun t ht ↦ ?_
    exact ⟨t, hsub ht, heq ht⟩
  have hIoo : ∀ a b : ℝ, a ≤ b → uIoo a b ⊆ Icc a b := fun a b hab t ht ↦ by
    rw [uIoo_of_le hab] at ht; exact Ioo_subset_Icc_self ht
  have piece : ∀ (e : ℝ → ℂ) (v : ℂ) (a b : ℝ), a ≤ b → (∀ t, deriv e t = v) → Continuous e →
      EqOn (pgCurve L z₀) e (Icc a b) → Icc a b ⊆ Icc 0 4 →
      IntervalIntegrable (fun t ↦ deriv (pgCurve L z₀) t • f (pgCurve L z₀ t)) volume a b ∧
      ∫ t in a..b, deriv (pgCurve L z₀) t • f (pgCurve L z₀ t) = ∫ t in a..b, v * f (e t) := by
    intro e v a b hab hd he heq hsub
    have hγ : EqOn (pgCurve L z₀) e (uIoo a b) := fun t ht ↦ heq (hIoo a b hab ht)
    refine ⟨(hint e v a b hab hd he heq hsub).congr_uIoo
      ((hγ.deriv isOpen_Ioo).comp_left₂ hγ.comp_left).symm, ?_⟩
    rw [intervalIntegral_deriv_smul_congr hγ]
    simp [hd]
  obtain ⟨i0, j0⟩ := piece _ _ 0 1 (by norm_num) deriv_pgSide0 contDiff_pgSide0.continuous
    pgCurve_eqOn0 (Icc_subset_Icc (by norm_num) (by norm_num))
  obtain ⟨i1, j1⟩ := piece _ _ 1 2 (by norm_num) deriv_pgSide1 contDiff_pgSide1.continuous
    pgCurve_eqOn1 (Icc_subset_Icc (by norm_num) (by norm_num))
  obtain ⟨i2, j2⟩ := piece _ _ 2 3 (by norm_num) deriv_pgSide2 contDiff_pgSide2.continuous
    pgCurve_eqOn2 (Icc_subset_Icc (by norm_num) (by norm_num))
  obtain ⟨i3, j3⟩ := piece _ _ 3 4 (by norm_num) deriv_pgSide3 contDiff_pgSide3.continuous
    pgCurve_eqOn3 (Icc_subset_Icc (by norm_num) (by norm_num))
  rw [← integral_add_adjacent_intervals (i0.trans (i1.trans i2)) i3,
    ← integral_add_adjacent_intervals (i0.trans i1) i2, ← integral_add_adjacent_intervals i0 i1,
    j0, j1, j2, j3]

/-- `u ↦ f(z₀ + u ω₁)` is continuous on `[0, 1]` if `f` is continuous on the boundary. -/
theorem continuousOn_side_ω₁ {f : ℂ → ℂ} (hf : ContinuousOn f (pgCurve L z₀ '' Icc 0 4)) :
    ContinuousOn (fun u : ℝ ↦ f (z₀ + (u : ℂ) * L.ω₁)) (Icc 0 1) := by
  refine hf.comp (contDiff_pgSide0 (L := L) (z₀ := z₀)).continuous.continuousOn fun u hu ↦ ?_
  exact ⟨u, Icc_subset_Icc (by norm_num) (by norm_num) hu, pgCurve_eqOn0 hu⟩

/-- `u ↦ f(z₀ + u ω₂)` is continuous on `[0, 1]` if `f` is continuous on the boundary. -/
theorem continuousOn_side_ω₂ {f : ℂ → ℂ} (hf : ContinuousOn f (pgCurve L z₀ '' Icc 0 4)) :
    ContinuousOn (fun u : ℝ ↦ f (z₀ + (u : ℂ) * L.ω₂)) (Icc 0 1) := by
  have hc : ContinuousOn (fun u : ℝ ↦ f (pgSide3 L z₀ (4 - u))) (Icc 0 1) := by
    refine hf.comp ((contDiff_pgSide3 (L := L) (z₀ := z₀)).continuous.comp
      (continuous_const.sub continuous_id)).continuousOn fun u hu ↦ ?_
    have h4 : 4 - u ∈ Icc (3 : ℝ) 4 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    exact ⟨4 - u, Icc_subset_Icc (by norm_num) (by norm_num) h4, pgCurve_eqOn3 h4⟩
  refine hc.congr fun u _ ↦ ?_
  simp [pgSide3]

/-- **Cancellation of opposite sides.** For `f` doubly periodic and continuous on the boundary, the integral
of `(a z + b) f(z)` around the parallelogram is `a ω₁ ω₂ (∫₀¹ f(z₀ + u ω₂) du - ∫₀¹ f(z₀ + u ω₁) du)`. -/
theorem integral_pgCurve_affine_mul {f : ℂ → ℂ} (hf : ContinuousOn f (pgCurve L z₀ '' Icc 0 4))
    (h₁ : ∀ z, f (z + L.ω₁) = f z) (h₂ : ∀ z, f (z + L.ω₂) = f z) (a b : ℂ) :
    ∫ t in (0 : ℝ)..4, deriv (pgCurve L z₀) t • ((a * pgCurve L z₀ t + b) * f (pgCurve L z₀ t)) =
      a * L.ω₁ * L.ω₂ * ((∫ u in (0 : ℝ)..1, f (z₀ + (u : ℂ) * L.ω₂)) -
        ∫ u in (0 : ℝ)..1, f (z₀ + (u : ℂ) * L.ω₁)) := by
  have hcont : ContinuousOn (fun z ↦ (a * z + b) * f z) (pgCurve L z₀ '' Icc 0 4) :=
    (continuousOn_const.mul continuousOn_id |>.add continuousOn_const).mul hf
  rw [integral_pgCurve _ hcont]
  set F₁ : ℝ → ℂ := fun u ↦ f (z₀ + (u : ℂ) * L.ω₁)
  set F₂ : ℝ → ℂ := fun u ↦ f (z₀ + (u : ℂ) * L.ω₂)
  have e1 : ∫ t in (1 : ℝ)..2, L.ω₂ * ((a * pgSide1 L z₀ t + b) * f (pgSide1 L z₀ t)) =
      ∫ u in (0 : ℝ)..1, L.ω₂ * ((a * (z₀ + L.ω₁ + (u : ℂ) * L.ω₂) + b) * F₂ u) := by
    have := intervalIntegral.integral_comp_add_right
      (fun t ↦ L.ω₂ * ((a * pgSide1 L z₀ t + b) * f (pgSide1 L z₀ t))) (a := 0) (b := 1) (1 : ℝ)
    rw [show (1 : ℝ) + 1 = 2 by norm_num, zero_add] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    have hs : pgSide1 L z₀ (u + 1) = z₀ + (u : ℂ) * L.ω₂ + L.ω₁ := by
      simp [pgSide1]; ring
    simp only [F₂, hs, h₁]
    ring_nf
  have e2 : ∫ t in (2 : ℝ)..3, -L.ω₁ * ((a * pgSide2 L z₀ t + b) * f (pgSide2 L z₀ t)) =
      ∫ u in (0 : ℝ)..1, -L.ω₁ * ((a * (z₀ + L.ω₂ + (u : ℂ) * L.ω₁) + b) * F₁ u) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun t ↦ -L.ω₁ * ((a * (z₀ + L.ω₂ + (t : ℂ) * L.ω₁) + b) * F₁ t)) (a := 2) (b := 3) (3 : ℝ)
    rw [show (3 : ℝ) - 3 = 0 by norm_num, show (3 : ℝ) - 2 = 1 by norm_num] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    have hs : pgSide2 L z₀ u = z₀ + ((3 - u : ℝ) : ℂ) * L.ω₁ + L.ω₂ := by
      simp [pgSide2]; ring
    simp only [F₁, hs, h₂]
    push_cast
    ring_nf
  have e3 : ∫ t in (3 : ℝ)..4, -L.ω₂ * ((a * pgSide3 L z₀ t + b) * f (pgSide3 L z₀ t)) =
      ∫ u in (0 : ℝ)..1, -L.ω₂ * ((a * (z₀ + (u : ℂ) * L.ω₂) + b) * F₂ u) := by
    have := intervalIntegral.integral_comp_sub_left
      (fun t ↦ -L.ω₂ * ((a * (z₀ + (t : ℂ) * L.ω₂) + b) * F₂ t)) (a := 3) (b := 4) (4 : ℝ)
    rw [show (4 : ℝ) - 4 = 0 by norm_num, show (4 : ℝ) - 3 = 1 by norm_num] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    simp only [F₂, pgSide3]
    push_cast
    ring_nf
  have e0 : ∫ t in (0 : ℝ)..1, L.ω₁ * ((a * pgSide0 L z₀ t + b) * f (pgSide0 L z₀ t)) =
      ∫ u in (0 : ℝ)..1, L.ω₁ * ((a * (z₀ + (u : ℂ) * L.ω₁) + b) * F₁ u) := rfl
  rw [e0, e1, e2, e3]
  have hF₁ : ContinuousOn F₁ (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]; exact continuousOn_side_ω₁ hf
  have hF₂ : ContinuousOn F₂ (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]; exact continuousOn_side_ω₂ hf
  have hc : ContinuousOn (fun u : ℝ ↦ (u : ℂ)) (uIcc 0 1) := continuous_ofReal.continuousOn
  have i0 : IntervalIntegrable (fun u : ℝ ↦ L.ω₁ * ((a * (z₀ + (u : ℂ) * L.ω₁) + b) * F₁ u))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul (((continuousOn_const.mul (continuousOn_const.add
      (hc.mul continuousOn_const))).add continuousOn_const).mul hF₁)
  have i1 : IntervalIntegrable (fun u : ℝ ↦ L.ω₂ * ((a * (z₀ + L.ω₁ + (u : ℂ) * L.ω₂) + b) * F₂ u))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul (((continuousOn_const.mul (continuousOn_const.add
      (hc.mul continuousOn_const))).add continuousOn_const).mul hF₂)
  have i2 : IntervalIntegrable (fun u : ℝ ↦ -L.ω₁ * ((a * (z₀ + L.ω₂ + (u : ℂ) * L.ω₁) + b) * F₁ u))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul (((continuousOn_const.mul (continuousOn_const.add
      (hc.mul continuousOn_const))).add continuousOn_const).mul hF₁)
  have i3 : IntervalIntegrable (fun u : ℝ ↦ -L.ω₂ * ((a * (z₀ + (u : ℂ) * L.ω₂) + b) * F₂ u))
      volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    exact continuousOn_const.mul (((continuousOn_const.mul (continuousOn_const.add
      (hc.mul continuousOn_const))).add continuousOn_const).mul hF₂)
  rw [← integral_add i0 i1, ← integral_add (i0.add i1) i2, ← integral_add ((i0.add i1).add i2) i3,
    mul_sub, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun u _ ↦ ?_
    simp only [F₁, F₂]
    ring
  · exact (hF₂.intervalIntegrable).const_mul _
  · exact (hF₁.intervalIntegrable).const_mul _

/-! ### The winding number about an interior point -/

variable (L) in
/-- The orientation number `Im(ω₂ ω̄₁)` of the period pair; nonzero. -/
def pgJ : ℝ := L.ω₂.im * L.ω₁.re - L.ω₂.re * L.ω₁.im

theorem im_div_comb (A B C D : ℝ) :
    (((C : ℂ) * L.ω₁ + (D : ℂ) * L.ω₂) / ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂)).im =
      (D * A - C * B) * pgJ L / normSq ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂) := by
  rw [div_im, ← sub_div]
  congr 1
  simp [pgJ, mul_re, mul_im]
  ring

theorem pgJ_ne_zero : pgJ L ≠ 0 := by
  intro h
  apply L.im_ω₁_div_ω₂_ne_zero
  rw [div_im, ← sub_div]
  have : L.ω₁.im * L.ω₂.re - L.ω₁.re * L.ω₂.im = -pgJ L := by simp only [pgJ]; ring
  rw [this, h, neg_zero, zero_div]

theorem comb_eq_zero {A B : ℝ} (h : (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ = 0) : A = 0 ∧ B = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [add_re, add_im, re_ofReal_mul, im_ofReal_mul, zero_re, zero_im] at h1 h2
  have hJ := pgJ_ne_zero (L := L)
  have hB : B * pgJ L = 0 := by
    simp only [pgJ]; linear_combination L.ω₁.re * h2 - L.ω₁.im * h1
  have hA : A * pgJ L = 0 := by
    simp only [pgJ]; linear_combination L.ω₂.im * h1 - L.ω₂.re * h2
  exact ⟨(mul_eq_zero.1 hA).resolve_right hJ, (mul_eq_zero.1 hB).resolve_right hJ⟩

theorem comb_ne_zero {A B : ℝ} (h : A ≠ 0 ∨ B ≠ 0) : (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ ≠ 0 := by
  intro h0
  have := comb_eq_zero h0
  tauto

/-- A ratio whose imaginary part is a positive multiple of `pgJ L / normSq` lies in the slit plane unless the
multiple vanishes, in which case the ratio is `1`. -/
theorem side_ratio_mem_slitPlane {A B C D : ℝ} (hp : A ≠ 0 ∨ B ≠ 0) (hc : 0 < D * A - C * B) :
    ((C : ℂ) * L.ω₁ + (D : ℂ) * L.ω₂) / ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂) ∈ slitPlane := by
  refine Or.inr ?_
  rw [im_div_comb]
  have hn : 0 < normSq ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂) := normSq_pos.2 (comb_ne_zero hp)
  exact div_ne_zero (mul_ne_zero hc.ne' pgJ_ne_zero) hn.ne'

theorem sign_im_side_ratio {A B C D : ℝ} (hp : A ≠ 0 ∨ B ≠ 0) (hc : 0 < D * A - C * B) :
    (0 < pgJ L → 0 < (((C : ℂ) * L.ω₁ + (D : ℂ) * L.ω₂) / ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂)).im) ∧
    (pgJ L < 0 → (((C : ℂ) * L.ω₁ + (D : ℂ) * L.ω₂) / ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂)).im < 0) := by
  rw [im_div_comb]
  have hn : 0 < normSq ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂) := normSq_pos.2 (comb_ne_zero hp)
  exact ⟨fun h ↦ div_pos (mul_pos hc h) hn, fun h ↦ div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hc h) hn⟩

theorem pgCurve_one : pgCurve L z₀ 1 = z₀ + L.ω₁ := by simp [pgCurve, pgSide0]
theorem pgCurve_two : pgCurve L z₀ 2 = z₀ + L.ω₁ + L.ω₂ := by
  rw [pgCurve_eqOn1 (by norm_num : (2 : ℝ) ∈ Icc 1 2)]; simp [pgSide1]; norm_num
theorem pgCurve_three : pgCurve L z₀ 3 = z₀ + L.ω₂ := by
  rw [pgCurve_eqOn2 (by norm_num : (3 : ℝ) ∈ Icc 2 3)]; simp [pgSide2]
theorem pgCurve_four : pgCurve L z₀ 4 = z₀ := by
  rw [pgCurve_eqOn3 (by norm_num : (4 : ℝ) ∈ Icc 3 4)]; simp [pgSide3]
theorem pgCurve_zero : pgCurve L z₀ 0 = z₀ := by simp [pgCurve, pgSide0]

/-- For an interior point `w = z₀ + s ω₁ + τ ω₂`, each side ratio `(γ t - w)/(γ j - w)` lies in the slit plane,
and its imaginary part at the end of the side has the sign of `pgJ L`. -/
theorem pgCurve_side_ratio {s τ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < τ) (ht1 : τ < 1) (j : ℕ)
    (hj : j < 4) :
    (∀ t ∈ Icc (j : ℝ) (j + 1), (pgCurve L z₀ t - (z₀ + s * L.ω₁ + τ * L.ω₂)) /
        (pgCurve L z₀ j - (z₀ + s * L.ω₁ + τ * L.ω₂)) ∈ slitPlane) ∧
    (0 < pgJ L → 0 < ((pgCurve L z₀ (j + 1) - (z₀ + s * L.ω₁ + τ * L.ω₂)) /
        (pgCurve L z₀ j - (z₀ + s * L.ω₁ + τ * L.ω₂))).im) ∧
    (pgJ L < 0 → ((pgCurve L z₀ (j + 1) - (z₀ + s * L.ω₁ + τ * L.ω₂)) /
        (pgCurve L z₀ j - (z₀ + s * L.ω₁ + τ * L.ω₂))).im < 0) := by
  set w := z₀ + s * L.ω₁ + τ * L.ω₂
  -- the generic statement on a side with coordinates
  have key : ∀ (e : ℝ → ℂ) (a : ℝ) (A B : ℝ) (C D : ℝ → ℝ), (A ≠ 0 ∨ B ≠ 0) →
      EqOn (pgCurve L z₀) e (Icc a (a + 1)) →
      (∀ t, e t - w = (C t : ℂ) * L.ω₁ + (D t : ℂ) * L.ω₂) → C a = A → D a = B →
      (∀ t ∈ Ioc a (a + 1), 0 < D t * A - C t * B) →
      (∀ t ∈ Icc a (a + 1), (pgCurve L z₀ t - w) / (pgCurve L z₀ a - w) ∈ slitPlane) ∧
      (0 < pgJ L → 0 < ((pgCurve L z₀ (a + 1) - w) / (pgCurve L z₀ a - w)).im) ∧
      (pgJ L < 0 → ((pgCurve L z₀ (a + 1) - w) / (pgCurve L z₀ a - w)).im < 0) := by
    intro e a A B C D hp heq hco hCa hDa hpos
    have ha : a ∈ Icc a (a + 1) := ⟨le_rfl, by linarith⟩
    have ha1 : a + 1 ∈ Icc a (a + 1) := ⟨by linarith, le_rfl⟩
    have hden : pgCurve L z₀ a - w = (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ := by
      rw [heq ha, hco, hCa, hDa]
    refine ⟨fun t ht ↦ ?_, ?_⟩
    · rw [hden, heq ht, hco]
      rcases ht.1.eq_or_lt with rfl | hlt
      · rw [hCa, hDa, div_self (comb_ne_zero hp)]; exact one_mem_slitPlane
      · exact side_ratio_mem_slitPlane hp (hpos t ⟨hlt, ht.2⟩)
    · rw [hden, heq ha1, hco]
      exact sign_im_side_ratio hp (hpos _ ⟨by linarith, le_rfl⟩)
  interval_cases j
  · have := key (pgSide0 L z₀) 0 (-s) (-τ) (fun t ↦ t - s) (fun _ ↦ -τ) (Or.inl (by linarith))
      (by simpa using pgCurve_eqOn0) (fun t ↦ by simp [pgSide0, w]; ring) (by simp) rfl
      (fun t ht ↦ by nlinarith [ht.1])
    simpa using this
  · have := key (pgSide1 L z₀) 1 (1 - s) (-τ) (fun _ ↦ 1 - s) (fun t ↦ t - 1 - τ)
      (Or.inl (by linarith)) (by norm_num; exact pgCurve_eqOn1)
      (fun t ↦ by simp [pgSide1, w]; ring) rfl (by simp)
      (fun t ht ↦ by nlinarith [ht.1])
    norm_num at this ⊢; exact this
  · have := key (pgSide2 L z₀) 2 (1 - s) (1 - τ) (fun t ↦ 3 - t - s) (fun _ ↦ 1 - τ)
      (Or.inl (by linarith)) (by norm_num; exact pgCurve_eqOn2)
      (fun t ↦ by simp [pgSide2, w]; ring) (by norm_num) rfl
      (fun t ht ↦ by nlinarith [ht.1])
    norm_num at this ⊢; exact this
  · have := key (pgSide3 L z₀) 3 (-s) (1 - τ) (fun _ ↦ -s) (fun t ↦ 4 - t - τ)
      (Or.inl (by linarith)) (by norm_num; exact pgCurve_eqOn3)
      (fun t ↦ by simp [pgSide3, w]; ring) rfl (by norm_num)
      (fun t ht ↦ by nlinarith [ht.1])
    norm_num at this ⊢; exact this

theorem exists_side (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) : ∃ j : ℕ, j < 4 ∧ t ∈ Icc (j : ℝ) (j + 1) := by
  by_cases h1 : t ≤ 1
  · exact ⟨0, by norm_num, by simpa using ⟨ht.1, h1⟩⟩
  by_cases h2 : t ≤ 2
  · exact ⟨1, by norm_num, by norm_num; exact ⟨by linarith, h2⟩⟩
  by_cases h3 : t ≤ 3
  · exact ⟨2, by norm_num, by norm_num; exact ⟨by linarith, h3⟩⟩
  · exact ⟨3, by norm_num, by norm_num; exact ⟨by linarith, ht.2⟩⟩

/-- The boundary curve avoids every interior point. -/
theorem pgCurve_ne {s τ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < τ) (ht1 : τ < 1) :
    ∀ t ∈ uIcc (0 : ℝ) 4, pgCurve L z₀ t ≠ z₀ + s * L.ω₁ + τ * L.ω₂ := by
  intro t ht heq
  rw [uIcc_of_le (by norm_num)] at ht
  obtain ⟨j, hj, htj⟩ := exists_side t ht
  have := (pgCurve_side_ratio (L := L) (z₀ := z₀) hs0 hs1 ht0 ht1 j hj).1 t htj
  rw [heq, sub_self, zero_div] at this
  exact slitPlane_ne_zero this rfl

/-- **The winding number of the boundary about an interior point** is `1` if `Im(ω₂ ω̄₁) > 0` and `-1`
otherwise. -/
theorem windingNumber_pgCurve {s τ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < τ) (ht1 : τ < 1) :
    windingNumber (pgCurve L z₀) 0 4 (z₀ + s * L.ω₁ + τ * L.ω₂) = if 0 < pgJ L then 1 else -1 := by
  set w := z₀ + s * L.ω₁ + τ * L.ω₂
  have hγ := isPiecewiseC1On_pgCurve (L := L) (z₀ := z₀)
  have hoff := pgCurve_ne (L := L) (z₀ := z₀) hs0 hs1 ht0 ht1
  obtain ⟨m, hm⟩ := hγ.exists_int_windingNumber pgCurve_closed hoff
  have hint := intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn hoff hγ.intervalIntegrable_deriv
  have hW := windingNumber_eq_integral_of_avoidance hγ.continuousOn hoff hint
  obtain ⟨P, hP, hdiff⟩ := hγ.exists_countable_differentiableAt
  have hcont : ContinuousOn (pgCurve L z₀) (Icc 0 4) := by
    rw [← uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4)]; exact hγ.continuousOn
  have hdiff' : ∀ t ∈ Ioo (0 : ℝ) 4 \ P, DifferentiableAt ℝ (pgCurve L z₀) t := by
    simpa using hdiff
  have hsum := integral_inv_sub_mul_deriv_eq_sum_log (w := w) (a := 0) (b := 4) (N := 4)
    (s := fun j : ℕ ↦ (j : ℝ)) hP (by simp) (by norm_num) Nat.mono_cast hcont hdiff'
    (fun j hj t ht ↦ (pgCurve_side_ratio hs0 hs1 ht0 ht1 j hj).1 t (by simpa using ht)) hint
  rw [hsum] at hW
  set r : ℕ → ℂ := fun j ↦ (pgCurve L z₀ ((j + 1 : ℕ) : ℝ) - w) / (pgCurve L z₀ (j : ℝ) - w)
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hS : ∑ j ∈ Finset.range 4, Complex.log (r j) = 2 * Real.pi * I * m := by
    rw [hm] at hW
    rw [hW, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  have hIm := congrArg Complex.im hS
  simp only [im_sum, log_im] at hIm
  have him : (2 * (Real.pi : ℂ) * I * m).im = 2 * Real.pi * m := by simp
  rw [him] at hIm
  have hr : ∀ j < 4, (0 < pgJ L → 0 < (r j).im) ∧ (pgJ L < 0 → (r j).im < 0) := by
    intro j hj
    have := (pgCurve_side_ratio (L := L) (z₀ := z₀) hs0 hs1 ht0 ht1 j hj).2
    simpa [r] using this
  have hpi0 := Real.pi_pos
  rw [hm]
  split_ifs with hJ
  · have hb : ∀ j < 4, 0 < arg (r j) ∧ arg (r j) < Real.pi := fun j hj ↦ by
      have h := (hr j hj).1 hJ
      refine ⟨lt_of_le_of_ne (arg_nonneg_iff.2 h.le) fun h0 ↦ ?_, arg_lt_pi_iff.2 (Or.inr h.ne')⟩
      exact h.ne' (arg_eq_zero_iff.1 h0.symm).2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hIm
    have := hb 0 (by norm_num); have := hb 1 (by norm_num); have := hb 2 (by norm_num)
    have := hb 3 (by norm_num)
    have hm1 : (0 : ℝ) < m := by nlinarith
    have hm2 : (m : ℝ) < 2 := by nlinarith
    have : m = 1 := by
      have h1 : (0 : ℤ) < m := by exact_mod_cast hm1
      have h2 : m < (2 : ℤ) := by exact_mod_cast hm2
      omega
    simp [this]
  · have hJ' : pgJ L < 0 := lt_of_le_of_ne (not_lt.1 hJ) pgJ_ne_zero
    have hb : ∀ j < 4, -Real.pi < arg (r j) ∧ arg (r j) < 0 := fun j hj ↦
      ⟨neg_pi_lt_arg _, arg_neg_iff.2 ((hr j hj).2 hJ')⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hIm
    have := hb 0 (by norm_num); have := hb 1 (by norm_num); have := hb 2 (by norm_num)
    have := hb 3 (by norm_num)
    have hm1 : (m : ℝ) < 0 := by nlinarith
    have hm2 : (-2 : ℝ) < m := by nlinarith
    have : m = -1 := by
      have h1 : m < (0 : ℤ) := by exact_mod_cast hm1
      have h2 : (-2 : ℤ) < m := by exact_mod_cast hm2
      omega
    simp [this]

/-! ### Coordinates and the neighbourhood of the parallelogram -/

theorem repr_comb (A B : ℝ) :
    L.basis.repr ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂) 0 = A ∧
      L.basis.repr ((A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂) 1 = B := by
  have : (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ = A • L.basis 0 + B • L.basis 1 := by
    simp [Complex.real_smul]
  rw [this, map_add, map_smul, map_smul]
  simp only [Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply]
  simp

theorem eq_comb_repr (z : ℂ) :
    z = ((L.basis.repr z 0 : ℝ) : ℂ) * L.ω₁ + ((L.basis.repr z 1 : ℝ) : ℂ) * L.ω₂ := by
  have := L.basis.sum_repr z
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one, Complex.real_smul, Complex.real_smul] at this
  exact this.symm

theorem continuous_repr (i : Fin 2) : Continuous fun z : ℂ ↦ L.basis.repr z i :=
  (L.basis.coord i).continuous_of_finiteDimensional

theorem comb_inj {A B C D : ℝ} (h : z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ = z₀ + C * L.ω₁ + D * L.ω₂) :
    A = C ∧ B = D := by
  have h' : ((A - C : ℝ) : ℂ) * L.ω₁ + ((B - D : ℝ) : ℂ) * L.ω₂ = 0 := by
    push_cast; linear_combination h
  have := comb_eq_zero h'
  constructor <;> linarith [this.1, this.2]

variable (L z₀) in
/-- The open parallelogram `z₀ + (-1, 2) ω₁ + (-1, 2) ω₂`, a convex open neighbourhood of the closed
fundamental parallelogram. -/
def pgU : Set ℂ :=
  {z | L.basis.repr (z - z₀) 0 ∈ Ioo (-1) 2 ∧ L.basis.repr (z - z₀) 1 ∈ Ioo (-1) 2}

theorem isOpen_pgU : IsOpen (pgU L z₀) :=
  (isOpen_Ioo.preimage ((continuous_repr 0).comp (continuous_id.sub continuous_const))).inter
    (isOpen_Ioo.preimage ((continuous_repr 1).comp (continuous_id.sub continuous_const)))

theorem mem_pgU_comb {A B : ℝ} :
    z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ ∈ pgU L z₀ ↔ A ∈ Ioo (-1) 2 ∧ B ∈ Ioo (-1) 2 := by
  have e : z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ - z₀ = (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ := by ring
  simp only [pgU, mem_ofPred_eq, e, (repr_comb A B).1, (repr_comb A B).2]

theorem exists_comb (z : ℂ) : ∃ A B : ℝ, z = z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ :=
  ⟨L.basis.repr (z - z₀) 0, L.basis.repr (z - z₀) 1, by
    have := eq_comb_repr (L := L) (z - z₀); linear_combination this⟩

theorem convex_pgU : Convex ℝ (pgU L z₀) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨A, B, rfl⟩ := exists_comb (L := L) (z₀ := z₀) x
  obtain ⟨C, D, rfl⟩ := exists_comb (L := L) (z₀ := z₀) y
  rw [mem_pgU_comb] at hx hy
  have e : a • (z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂) + b • (z₀ + (C : ℂ) * L.ω₁ + (D : ℂ) * L.ω₂) =
      z₀ + ((a * A + b * C : ℝ) : ℂ) * L.ω₁ + ((a * B + b * D : ℝ) : ℂ) * L.ω₂ := by
    simp only [Complex.real_smul]
    push_cast
    have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
    linear_combination z₀ * hab'
  rw [e, mem_pgU_comb]
  obtain ⟨⟨hA1, hA2⟩, ⟨hB1, hB2⟩⟩ := hx
  obtain ⟨⟨hC1, hC2⟩, ⟨hD1, hD2⟩⟩ := hy
  have k : ∀ x y : ℝ, x ∈ Ioo (-1 : ℝ) 2 → y ∈ Ioo (-1 : ℝ) 2 → a * x + b * y ∈ Ioo (-1 : ℝ) 2 :=
    fun x y hx hy ↦ by simpa [smul_eq_mul] using (convex_Ioo (-1 : ℝ) 2) hx hy ha hb hab
  exact ⟨k A C ⟨hA1, hA2⟩ ⟨hC1, hC2⟩, k B D ⟨hB1, hB2⟩ ⟨hD1, hD2⟩⟩

theorem convex_closedParallelogram : Convex ℝ (closedParallelogram L z₀) := by
  rintro _ ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ _ ⟨C, D, hC0, hC1, hD0, hD1, rfl⟩ a b ha hb hab
  refine ⟨a * A + b * C, a * B + b * D, by positivity, by nlinarith, by positivity, by nlinarith, ?_⟩
  simp only [Complex.real_smul]
  push_cast
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  linear_combination z₀ * hab'

variable (L z₀) in
/-- A compact set containing `pgU L z₀`. -/
def pgK : Set ℂ := parallelogramMap L z₀ '' (Icc (-1) 2 ×ˢ Icc (-1) 2)

theorem isCompact_pgK : IsCompact (pgK L z₀) :=
  (isCompact_Icc.prod isCompact_Icc).image (continuous_parallelogramMap L z₀)

theorem pgU_subset_pgK : pgU L z₀ ⊆ pgK L z₀ := by
  intro z hz
  obtain ⟨A, B, rfl⟩ := exists_comb (L := L) (z₀ := z₀) z
  rw [mem_pgU_comb] at hz
  exact ⟨(A, B), ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩, by simp [parallelogramMap]⟩

/-- Coordinates of the boundary curve: on each side one coordinate is `0` or `1`, both lie in `[0, 1]`. -/
theorem pgCurve_coords (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) : ∃ A B : ℝ,
    pgCurve L z₀ t = z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ ∧ A ∈ Icc 0 1 ∧ B ∈ Icc 0 1 ∧
      (A = 0 ∨ A = 1 ∨ B = 0 ∨ B = 1) := by
  obtain ⟨j, hj, htj⟩ := exists_side t ht
  interval_cases j
  · simp at htj
    exact ⟨t, 0, by rw [pgCurve_eqOn0 htj]; simp [pgSide0], htj, by simp, by simp⟩
  · norm_num at htj
    exact ⟨1, t - 1, by rw [pgCurve_eqOn1 htj]; simp [pgSide1], by simp,
      ⟨by linarith [htj.1], by linarith [htj.2]⟩, by simp⟩
  · norm_num at htj
    exact ⟨3 - t, 1, by rw [pgCurve_eqOn2 htj]; simp [pgSide2]; ring,
      ⟨by linarith [htj.2], by linarith [htj.1]⟩, by simp, by simp⟩
  · norm_num at htj
    exact ⟨0, 4 - t, by rw [pgCurve_eqOn3 htj]; simp [pgSide3], by simp,
      ⟨by linarith [htj.2], by linarith [htj.1]⟩, by simp⟩

theorem pgCurve_mem_closed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    pgCurve L z₀ t ∈ closedParallelogram L z₀ := by
  obtain ⟨A, B, h, hA, hB, -⟩ := pgCurve_coords (L := L) (z₀ := z₀) t ht
  exact ⟨A, B, hA.1, hA.2, hB.1, hB.2, h⟩

theorem pgCurve_notMem_open (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    pgCurve L z₀ t ∉ openParallelogram L z₀ := by
  obtain ⟨A, B, h, -, -, hAB⟩ := pgCurve_coords (L := L) (z₀ := z₀) t ht
  rintro ⟨C, D, hC0, hC1, hD0, hD1, hz⟩
  rw [h] at hz
  obtain ⟨rfl, rfl⟩ := comb_inj hz
  rcases hAB with rfl | rfl | rfl | rfl <;> linarith

theorem pgCurve_mem_frontier (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) :
    pgCurve L z₀ t ∈ frontier (openParallelogram L z₀) :=
  ⟨closedParallelogram_subset_closure L z₀ (pgCurve_mem_closed t ht),
    fun hi ↦ pgCurve_notMem_open t ht (interior_subset hi)⟩

theorem pgCurve_mem_pgU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 4) : pgCurve L z₀ t ∈ pgU L z₀ := by
  obtain ⟨A, B, h, hA, hB, -⟩ := pgCurve_coords (L := L) (z₀ := z₀) t ht
  rw [h, mem_pgU_comb]
  exact ⟨⟨by linarith [hA.1], by linarith [hA.2]⟩, ⟨by linarith [hB.1], by linarith [hB.2]⟩⟩

theorem openParallelogram_subset_pgU : openParallelogram L z₀ ⊆ pgU L z₀ := by
  rintro _ ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩
  rw [mem_pgU_comb]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-! ### The residue theorem on the parallelogram -/

variable (L) in
/-- The orientation sign `±1` of the boundary curve. -/
def pgSign : ℂ := if 0 < pgJ L then 1 else -1

theorem pgSign_ne_zero : pgSign L ≠ 0 := by
  unfold pgSign; split_ifs <;> norm_num

/-- **Residue theorem on the fundamental parallelogram.** Let `h` be meromorphic on `ℂ`, holomorphic at every
point where its order is nonnegative (for instance a function in normal form), and without poles on the
boundary of the parallelogram. Then the integral of `h` around the boundary is `2πi · ε · ∑ Res h`, the sum over
the open parallelogram, with `ε = pgSign L = ±1`. -/
theorem integral_pgCurve_eq_residues {h : ℂ → ℂ} (hmero : MeromorphicOn h univ)
    (han : ∀ z, 0 ≤ meromorphicOrderAt h z → AnalyticAt ℂ h z)
    (hbd : ∀ z ∈ frontier (openParallelogram L z₀), 0 ≤ meromorphicOrderAt h z) :
    ∫ t in (0 : ℝ)..4, deriv (pgCurve L z₀) t • h (pgCurve L z₀ t) =
      2 * Real.pi * I * (pgSign L * ∑ᶠ z ∈ openParallelogram L z₀, TauCeti.Contour.residue h z) := by
  classical
  set K := pgK L z₀
  set U := pgU L z₀
  set D := openParallelogram L z₀
  have hmeroK : MeromorphicOn h K := hmero.mono_set (subset_univ _)
  have hfin := hmeroK.divisor_support_finite_of_subset (isCompact_pgK (L := L) (z₀ := z₀)) le_rfl
  set S : Finset ℂ := hfin.toFinset.filter fun z ↦ meromorphicOrderAt h z < 0
  have hpoleS : ∀ z ∈ U, meromorphicOrderAt h z < 0 → z ∈ S := by
    intro z hz hneg
    refine Finset.mem_filter.2 ⟨?_, hneg⟩
    rw [Set.Finite.mem_toFinset, Function.mem_support,
      MeromorphicOn.divisor_apply hmeroK (pgU_subset_pgK hz)]
    intro h0
    have hne : meromorphicOrderAt h z ≠ ⊤ := fun ht ↦ by rw [ht] at hneg; exact not_top_lt hneg
    rw [← WithTop.coe_untop₀_of_ne_top hne, h0] at hneg
    exact lt_irrefl _ hneg
  have hSneg : ∀ z ∈ S, meromorphicOrderAt h z < 0 := fun z hz ↦ (Finset.mem_filter.1 hz).2
  have hdiff : DifferentiableOn ℂ h (U \ (S : Set ℂ)) := by
    intro z hz
    refine (han z ?_).differentiableAt.differentiableWithinAt
    by_contra hlt
    exact hz.2 (hpoleS z hz.1 (not_le.1 hlt))
  have hγ := isPiecewiseC1On_pgCurve (L := L) (z₀ := z₀)
  have hγU : ∀ t ∈ uIcc (0 : ℝ) 4, pgCurve L z₀ t ∈ U := fun t ht ↦
    pgCurve_mem_pgU t (by rwa [uIcc_of_le (by norm_num)] at ht)
  have hoff : ∀ t ∈ uIcc (0 : ℝ) 4, pgCurve L z₀ t ∉ (S : Set ℂ) := by
    intro t ht hS
    rw [uIcc_of_le (by norm_num)] at ht
    exact not_le.2 (hSneg _ hS) (hbd _ (pgCurve_mem_frontier t ht))
  have hnull : IsNullHomologous (pgCurve L z₀) 0 4 U :=
    isNullHomologous_of_starConvex (convex_pgU.starConvex (hγU 0 (by simp))) hγ pgCurve_closed hγU
  rw [classicalResidueTheorem_nullHomologous isOpen_pgU hdiff (fun s _ _ ↦ hmero s (mem_univ s)) hγ
    hγU pgCurve_closed hoff hnull]
  congr 1
  -- winding numbers: `ε` inside, `0` outside the closed parallelogram
  have hwind : ∀ s ∈ S, windingNumber (pgCurve L z₀) 0 4 s * TauCeti.Contour.residue h s =
      if s ∈ D then pgSign L * TauCeti.Contour.residue h s else 0 := by
    intro s hs
    split_ifs with hsD
    · obtain ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ := hsD
      rw [windingNumber_pgCurve hA0 hA1 hB0 hB1]; rfl
    · have hsP : s ∉ closedParallelogram L z₀ := by
        intro hsP
        have hfr : s ∈ frontier D :=
          ⟨closedParallelogram_subset_closure L z₀ hsP, fun hi ↦ hsD (interior_subset hi)⟩
        exact not_le.2 (hSneg s hs) (hbd s hfr)
      rw [windingNumber_eq_zero_of_starConvex
        (convex_closedParallelogram.starConvex (pgCurve_mem_closed 0 (by simp))) hγ pgCurve_closed
        (fun t ht ↦ pgCurve_mem_closed t (by rwa [uIcc_of_le (by norm_num)] at ht)) hsP, zero_mul]
  rw [Finset.sum_congr rfl hwind, ← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  symm
  apply finsum_mem_eq_sum_of_inter_support_eq
  ext z
  simp only [mem_inter_iff, Function.mem_support, Finset.coe_filter, mem_ofPred_eq]
  constructor
  · rintro ⟨hzD, hres⟩
    refine ⟨⟨?_, hzD⟩, hres⟩
    refine hpoleS z (openParallelogram_subset_pgU hzD) ?_
    by_contra hge
    exact hres (TauCeti.Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg (not_lt.1 hge))
  · rintro ⟨⟨-, hzD⟩, hres⟩
    exact ⟨hzD, hres⟩

/-- Version of the residue theorem for any meromorphic `h` holomorphic on the boundary: pass to the normal form. -/
theorem integral_pgCurve_eq_residues' {h : ℂ → ℂ} (hmero : MeromorphicOn h univ)
    (hbd : ∀ z ∈ frontier (openParallelogram L z₀), AnalyticAt ℂ h z) :
    ∫ t in (0 : ℝ)..4, deriv (pgCurve L z₀) t • h (pgCurve L z₀ t) =
      2 * Real.pi * I * (pgSign L * ∑ᶠ z ∈ openParallelogram L z₀, TauCeti.Contour.residue h z) := by
  set h' := toMeromorphicNFOn h univ
  have hNF : ∀ z, MeromorphicNFAt h' z := fun z ↦ meromorphicNFOn_toMeromorphicNFOn h univ (mem_univ z)
  have hord : ∀ z, meromorphicOrderAt h' z = meromorphicOrderAt h z := fun z ↦
    meromorphicOrderAt_toMeromorphicNFOn hmero (mem_univ z)
  have hgerm0 : h =ᶠ[codiscrete ℂ] h' := toMeromorphicNFOn_eqOn_codiscrete hmero
  have hgerm : ∀ z, h =ᶠ[𝓝[≠] z] h' := eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hgerm0
  have heq : ∀ z ∈ frontier (openParallelogram L z₀), h z = h' z := fun z hz ↦
    (((hbd z hz).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hNF z)).1
      (hgerm z)).eq_of_nhds
  have key := integral_pgCurve_eq_residues (L := L) (z₀ := z₀) (h := h')
    (meromorphicNFOn_toMeromorphicNFOn h univ).meromorphicOn
    (fun z hz ↦ (hNF z).meromorphicOrderAt_nonneg_iff_analyticAt.1 hz)
    (fun z hz ↦ by rw [hord]; exact (hbd z hz).meromorphicOrderAt_nonneg)
  have hres : ∀ z, TauCeti.Contour.residue h' z = TauCeti.Contour.residue h z := fun z ↦
    (TauCeti.Contour.residue_congr_nhdsNE (hgerm z)).symm
  simp only [hres] at key
  rw [← key]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le (by norm_num)] at ht
  simp only [heq _ (pgCurve_mem_frontier t ht)]

/-- The integral of a doubly periodic function, continuous on the boundary, vanishes. -/
theorem integral_pgCurve_periodic {f : ℂ → ℂ} (hf : ContinuousOn f (pgCurve L z₀ '' Icc 0 4))
    (h₁ : ∀ z, f (z + L.ω₁) = f z) (h₂ : ∀ z, f (z + L.ω₂) = f z) :
    ∫ t in (0 : ℝ)..4, deriv (pgCurve L z₀) t • f (pgCurve L z₀ t) = 0 := by
  have := integral_pgCurve_affine_mul hf h₁ h₂ 0 1
  simpa using this

/-- The integral of `z f(z)` for doubly periodic `f`. -/
theorem integral_pgCurve_id_mul {f : ℂ → ℂ} (hf : ContinuousOn f (pgCurve L z₀ '' Icc 0 4))
    (h₁ : ∀ z, f (z + L.ω₁) = f z) (h₂ : ∀ z, f (z + L.ω₂) = f z) :
    ∫ t in (0 : ℝ)..4, deriv (pgCurve L z₀) t • (pgCurve L z₀ t * f (pgCurve L z₀ t)) =
      L.ω₁ * L.ω₂ * ((∫ u in (0 : ℝ)..1, f (z₀ + (u : ℂ) * L.ω₂)) -
        ∫ u in (0 : ℝ)..1, f (z₀ + (u : ℂ) * L.ω₁)) := by
  have := integral_pgCurve_affine_mul hf h₁ h₂ 1 0
  simpa using this

/-! ### Proposition 3.1 -/

theorem IsDoublyPeriodic.toNF {Λ : Submodule ℤ ℂ} {f : ℂ → ℂ} (hf : IsDoublyPeriodic Λ f) :
    IsDoublyPeriodic Λ (toMeromorphicNFOn f univ) := by
  refine ⟨(meromorphicNFOn_toMeromorphicNFOn f univ).meromorphicOn, fun ω hω z ↦ ?_⟩
  set g := toMeromorphicNFOn f univ
  have hfg0 : f =ᶠ[codiscrete ℂ] g := toMeromorphicNFOn_eqOn_codiscrete hf.1
  have hfg : ∀ w, f =ᶠ[𝓝[≠] w] g := eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hfg0
  have hNF : ∀ w, MeromorphicNFAt g w := fun w ↦ meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ w)
  have h1 : MeromorphicNFAt (g ∘ (· + ω)) z :=
    meromorphicNFAt_comp_add_const_iff_meromorphicNFAt.2 (hNF _)
  have hT : Tendsto (fun w : ℂ ↦ w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) :=
    tendsto_nhdsWithin_iff.2 ⟨(by fun_prop : Continuous fun w : ℂ ↦ w + ω).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, by
        filter_upwards [self_mem_nhdsWithin] with w hw
        simpa using hw⟩
  have h2 : (g ∘ (· + ω)) =ᶠ[𝓝[≠] z] g := by
    filter_upwards [hT.eventually (hfg (z + ω)), hfg z] with u hu1 hu2
    simp only [Function.comp_apply]
    rw [← hu1, hf.2 ω hω u, hu2]
  exact ((h1.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hNF z)).1 h2).eq_of_nhds

theorem logDeriv_add_period {g : ℂ → ℂ} {ω : ℂ} (hg : ∀ z, g (z + ω) = g z) (z : ℂ) :
    logDeriv g (z + ω) = logDeriv g z := by
  have e : (fun x ↦ g (x + ω)) = g := funext hg
  have hd : deriv g (z + ω) = deriv g z := by
    rw [← deriv_comp_add_const, e]
  simp only [logDeriv_apply, hd, hg]

theorem residue_id_mul_logDeriv {g : ℂ → ℂ} {z : ℂ} {n : ℤ} (hg : MeromorphicAt g z)
    (hn : meromorphicOrderAt g z = n) :
    TauCeti.Contour.residue (fun w ↦ w * logDeriv g w) z = z * n := by
  obtain ⟨G, hG_an, hG_ne, hgerm⟩ := logDeriv_eventuallyEq_principalPart hg hn
  have hlG : AnalyticAt ℂ (logDeriv G) z := analyticAt_logDeriv_of_analyticAt hG_an hG_ne
  have h2 : (fun w ↦ w * logDeriv g w) =ᶠ[𝓝[≠] z]
      (fun w ↦ (z * n) * (w - z)⁻¹) + (fun w ↦ (n : ℂ) + w * logDeriv G w) := by
    filter_upwards [hgerm, self_mem_nhdsWithin] with w hw hwz
    have hwz' : w - z ≠ 0 := sub_ne_zero.2 hwz
    simp only [hw, Pi.add_apply]
    field_simp
    ring
  have m1 : MeromorphicAt (fun w : ℂ ↦ (z * n) * (w - z)⁻¹) z := by fun_prop
  have a2 : AnalyticAt ℂ (fun w : ℂ ↦ (n : ℂ) + w * logDeriv G w) z := by fun_prop
  rw [TauCeti.Contour.residue_congr_nhdsNE h2, TauCeti.Contour.residue_add m1 a2.meromorphicAt,
    TauCeti.Contour.residue_const_mul_sub_inv, TauCeti.Contour.residue_eq_zero_of_analyticAt a2,
    add_zero]

/-- Along a side `u ↦ z₀ + u v` (`u ∈ [0, 1]`) on which `g` is holomorphic and nonvanishing, with
`g(z₀) = g(z₀ + v)`, the integral of `v · g'/g` is in `2πi ℤ`. -/
theorem exists_int_integral_logDeriv {g : ℂ → ℂ} {v : ℂ}
    (han : ∀ u ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ g (z₀ + (u : ℂ) * v))
    (hne : ∀ u ∈ Icc (0 : ℝ) 1, g (z₀ + (u : ℂ) * v) ≠ 0) (hcl : g z₀ = g (z₀ + v)) :
    ∃ m : ℤ, ∫ u in (0 : ℝ)..1, v * logDeriv g (z₀ + (u : ℂ) * v) = 2 * Real.pi * I * m := by
  set σ : ℝ → ℂ := fun u ↦ z₀ + ((u : ℂ) - 0) * v
  have hσ : ∀ u : ℝ, σ u = z₀ + (u : ℂ) * v := fun u ↦ by simp [σ]
  have hdσ : ∀ u, deriv σ u = v := fun u ↦ (hasDerivAt_affine z₀ v 0 u).deriv
  have hσC : ContDiff ℝ 1 σ := by simp only [σ]; fun_prop
  have hγ : IsPiecewiseC1On σ 0 1 := IsPiecewiseC1On.of_contDiffOn hσC.contDiffOn
  have han' : ∀ t ∈ uIcc (0 : ℝ) 1, AnalyticAt ℂ g (σ t) := fun t ht ↦ by
    rw [hσ]; exact han t (by rwa [uIcc_of_le zero_le_one] at ht)
  have hne' : ∀ t ∈ uIcc (0 : ℝ) 1, g (σ t) ≠ 0 := fun t ht ↦ by
    rw [hσ]; exact hne t (by rwa [uIcc_of_le zero_le_one] at ht)
  have hW := windingNumber_comp_eq_integral_logDeriv hγ han' hne'
  have hgσ : IsPiecewiseC1On (g ∘ σ) 0 1 := by
    refine IsPiecewiseC1On.of_contDiffOn fun t ht ↦ ?_
    have h1 : ContDiffAt ℝ 1 g (σ t) := ((han' t ht).contDiffAt (n := 1)).restrict_scalars ℝ
    exact (h1.comp t (hσC.contDiffAt)).contDiffWithinAt
  have hcl' : (g ∘ σ) 0 = (g ∘ σ) 1 := by simp [hσ, hcl]
  have hav : ∀ t ∈ uIcc (0 : ℝ) 1, (g ∘ σ) t ≠ 0 := hne'
  obtain ⟨m, hm⟩ := hgσ.exists_int_windingNumber hcl' hav
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [hm] at hW
  have : ∫ t in (0 : ℝ)..1, deriv σ t • logDeriv g (σ t) = 2 * Real.pi * I * m := by
    rw [hW, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  rw [← this]
  refine intervalIntegral.integral_congr fun u _ ↦ ?_
  simp [hdσ, hσ]

/-- A finsum of integer casts. -/
theorem finsum_mem_intCast {D : Set ℂ} {a : ℂ → ℤ} (hfin : (D ∩ Function.support a).Finite) :
    ∑ᶠ z ∈ D, ((a z : ℤ) : ℂ) = ((∑ᶠ z ∈ D, a z : ℤ) : ℂ) := by
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := hfin.toFinset),
    finsum_mem_eq_sum_of_inter_support_eq _ (t := hfin.toFinset), Int.cast_sum]
  · ext z; simp only [Set.Finite.coe_toFinset, mem_inter_iff, Function.mem_support]; tauto
  · ext z; simp only [Set.Finite.coe_toFinset, mem_inter_iff, Function.mem_support, ne_eq,
      Int.cast_eq_zero]; tauto

/-- **Milne, Proposition 3.1**, proved by integrating around the fundamental parallelogram as in the book. -/
theorem doublyPeriodicSumsStatement : DoublyPeriodicSumsStatement := by
  refine ⟨fun L f hf hnz z₀ hb ↦ ?_⟩
  set D := openParallelogram L z₀
  set g := toMeromorphicNFOn f univ with hg_def
  have hgper := hf.toNF
  have hmero : MeromorphicOn f univ := hf.1
  have hM : Meromorphic f := meromorphicOn_univ.1 hmero
  have hne : ∀ z, meromorphicOrderAt f z ≠ ⊤ := fun z hz ↦
    hnz ((hM.exists_meromorphicOrderAt_eq_top_iff_eventually_zero).1 ⟨z, hz⟩)
  have hNF : ∀ z, MeromorphicNFAt g z := fun z ↦ meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ z)
  have hord : ∀ z, meromorphicOrderAt g z = meromorphicOrderAt f z := fun z ↦
    meromorphicOrderAt_toMeromorphicNFOn hmero (mem_univ z)
  have hgerm0 : f =ᶠ[codiscrete ℂ] g := toMeromorphicNFOn_eqOn_codiscrete hmero
  have hgerm : ∀ z, f =ᶠ[𝓝[≠] z] g := eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hgerm0
  have hgM : ∀ z, MeromorphicAt g z := fun z ↦ (hNF z).meromorphicAt
  have hbdg : ∀ z ∈ frontier D, AnalyticAt ℂ g z ∧ g z ≠ 0 := fun z hz ↦ by
    have h0 : meromorphicOrderAt g z = 0 := by rw [hord]; exact hb z hz
    exact ⟨(hNF z).meromorphicOrderAt_nonneg_iff_analyticAt.1 h0.ge,
      (hNF z).meromorphicOrderAt_eq_zero_iff.1 h0⟩
  have hg₁ : ∀ z, g (z + L.ω₁) = g z := hgper.2 _ L.ω₁_mem_lattice
  have hg₂ : ∀ z, g (z + L.ω₂) = g z := hgper.2 _ L.ω₂_mem_lattice
  have hγD : ∀ z ∈ pgCurve L z₀ '' Icc 0 4, z ∈ frontier D := by
    rintro _ ⟨t, ht, rfl⟩; exact pgCurve_mem_frontier t ht
  have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  -- the logarithmic derivative
  set φ := logDeriv g
  have hφM : MeromorphicOn φ univ := fun z _ ↦ (hgM z).deriv.div (hgM z)
  have hφbd : ∀ z ∈ frontier D, AnalyticAt ℂ φ z := fun z hz ↦
    analyticAt_logDeriv_of_analyticAt (hbdg z hz).1 (hbdg z hz).2
  have hφ₁ : ∀ z, φ (z + L.ω₁) = φ z := logDeriv_add_period hg₁
  have hφ₂ : ∀ z, φ (z + L.ω₂) = φ z := logDeriv_add_period hg₂
  have hφc : ContinuousOn φ (pgCurve L z₀ '' Icc 0 4) := fun z hz ↦
    (hφbd z (hγD z hz)).continuousAt.continuousWithinAt
  have hresφ : ∀ z, TauCeti.Contour.residue φ z = ((meromorphicOrderAt f z).untop₀ : ℂ) := by
    intro z
    rw [TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt (hgM z)
      (by rw [hord, WithTop.coe_untop₀_of_ne_top (hne z)])]
  -- finiteness of the divisor on the closed parallelogram
  have hfinD : (D ∩ Function.support fun z ↦ (meromorphicOrderAt f z).untop₀).Finite := by
    have hP := (hmero.mono_set (subset_univ (closedParallelogram L z₀))).divisor_support_finite_of_subset
      (isCompact_closedParallelogram L z₀) le_rfl
    refine hP.subset fun z hz ↦ ?_
    rw [Function.mem_support, MeromorphicOn.divisor_apply
      (hmero.mono_set (subset_univ _)) (openParallelogram_subset_closed L z₀ hz.1)]
    exact hz.2
  refine ⟨?_, ?_, ?_⟩
  · -- (a)
    have h0 := integral_pgCurve_periodic hφc hφ₁ hφ₂
    rw [integral_pgCurve_eq_residues' hφM hφbd] at h0
    simp only [hresφ] at h0
    rw [finsum_mem_intCast hfinD] at h0
    have h1 : ((∑ᶠ z ∈ D, (meromorphicOrderAt f z).untop₀ : ℤ) : ℂ) = 0 := by
      have := mul_eq_zero.1 h0
      rcases this with h | h
      · exact absurd h hpi
      · exact (mul_eq_zero.1 h).resolve_left pgSign_ne_zero
    exact_mod_cast h1
  · -- (b)
    have hgc : ContinuousOn g (pgCurve L z₀ '' Icc 0 4) := fun z hz ↦
      (hbdg z (hγD z hz)).1.continuousAt.continuousWithinAt
    have h0 := integral_pgCurve_periodic hgc hg₁ hg₂
    rw [integral_pgCurve_eq_residues' (hgper.1) (fun z hz ↦ (hbdg z hz).1)] at h0
    have hres : ∀ z, TauCeti.Contour.residue g z = TauCeti.Contour.residue f z := fun z ↦
      (TauCeti.Contour.residue_congr_nhdsNE (hgerm z)).symm
    rw [finsum_mem_congr rfl fun z _ ↦ hres z] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hpi
    · exact (mul_eq_zero.1 h).resolve_left pgSign_ne_zero
  · -- (c)
    set ψ : ℂ → ℂ := fun z ↦ z * φ z
    have hψM : MeromorphicOn ψ univ := fun z _ ↦ analyticAt_id.meromorphicAt.mul (hφM z (mem_univ z))
    have hψbd : ∀ z ∈ frontier D, AnalyticAt ℂ ψ z := fun z hz ↦ analyticAt_id.mul (hφbd z hz)
    have hres : ∀ z, TauCeti.Contour.residue ψ z = ((meromorphicOrderAt f z).untop₀ : ℂ) * z := by
      intro z
      rw [residue_id_mul_logDeriv (hgM z) (by rw [hord, WithTop.coe_untop₀_of_ne_top (hne z)]),
        mul_comm]
    have hI := integral_pgCurve_id_mul hφc hφ₁ hφ₂
    have hI' : ∫ t in (0 : ℝ)..4, deriv (pgCurve L z₀) t • ψ (pgCurve L z₀ t) =
        L.ω₁ * L.ω₂ * ((∫ u in (0 : ℝ)..1, φ (z₀ + (u : ℂ) * L.ω₂)) -
          ∫ u in (0 : ℝ)..1, φ (z₀ + (u : ℂ) * L.ω₁)) := hI
    rw [integral_pgCurve_eq_residues' hψM hψbd] at hI'
    simp only [hres] at hI'
    -- the side integrals are in `2πi ℤ`
    have hside1 : ∀ u ∈ Icc (0 : ℝ) 1, z₀ + (u : ℂ) * L.ω₁ ∈ frontier D := fun u hu ↦ by
      have := pgCurve_mem_frontier (L := L) (z₀ := z₀) u (Icc_subset_Icc (by norm_num) (by norm_num) hu)
      rwa [pgCurve_eqOn0 hu] at this
    have hside2 : ∀ u ∈ Icc (0 : ℝ) 1, z₀ + (u : ℂ) * L.ω₂ ∈ frontier D := fun u hu ↦ by
      have h4 : 4 - u ∈ Icc (3 : ℝ) 4 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have := pgCurve_mem_frontier (L := L) (z₀ := z₀) (4 - u)
        (Icc_subset_Icc (by norm_num) (by norm_num) h4)
      rw [pgCurve_eqOn3 h4] at this
      simpa [pgSide3] using this
    obtain ⟨m₁, hm₁⟩ := exists_int_integral_logDeriv (z₀ := z₀) (g := g) (v := L.ω₁)
      (fun u hu ↦ (hbdg _ (hside1 u hu)).1) (fun u hu ↦ (hbdg _ (hside1 u hu)).2)
      (hg₁ z₀).symm
    obtain ⟨m₂, hm₂⟩ := exists_int_integral_logDeriv (z₀ := z₀) (g := g) (v := L.ω₂)
      (fun u hu ↦ (hbdg _ (hside2 u hu)).1) (fun u hu ↦ (hbdg _ (hside2 u hu)).2)
      (hg₂ z₀).symm
    rw [intervalIntegral.integral_const_mul] at hm₁ hm₂
    have hsum : 2 * Real.pi * I * (pgSign L * ∑ᶠ z ∈ D, ((meromorphicOrderAt f z).untop₀ : ℂ) * z) =
        2 * Real.pi * I * (m₂ * L.ω₁ - m₁ * L.ω₂) := by
      rw [hI']
      have e : L.ω₁ * L.ω₂ * ((∫ u in (0 : ℝ)..1, φ (z₀ + (u : ℂ) * L.ω₂)) -
          ∫ u in (0 : ℝ)..1, φ (z₀ + (u : ℂ) * L.ω₁)) =
          L.ω₁ * (L.ω₂ * ∫ u in (0 : ℝ)..1, φ (z₀ + (u : ℂ) * L.ω₂)) -
            L.ω₂ * (L.ω₁ * ∫ u in (0 : ℝ)..1, φ (z₀ + (u : ℂ) * L.ω₁)) := by ring
      rw [e, hm₁, hm₂]
      ring
    have hsum' := mul_left_cancel₀ hpi hsum
    have hmem : (m₂ : ℂ) * L.ω₁ - m₁ * L.ω₂ ∈ L.lattice :=
      sub_mem (L.mem_lattice.2 ⟨m₂, 0, by simp⟩) (L.mem_lattice.2 ⟨0, m₁, by simp⟩)
    unfold pgSign at hsum'
    split_ifs at hsum'
    · rw [one_mul] at hsum'; rw [hsum']; exact hmem
    · have : ∑ᶠ z ∈ D, ((meromorphicOrderAt f z).untop₀ : ℂ) * z = -((m₂ : ℂ) * L.ω₁ - m₁ * L.ω₂) := by
        linear_combination -hsum'
      rw [this]; exact neg_mem hmem

end

end ModularFormsKB.Milne
