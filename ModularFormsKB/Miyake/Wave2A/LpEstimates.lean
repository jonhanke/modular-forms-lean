import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.MeasureTheory.Integral.Circle.LIntegral
import ModularFormsKB.Citation
/-!
# Miyake §2.6: L^p estimates for holomorphic functions on the upper half plane

Miyake, *Modular Forms* (Springer 1989), §2.6, pp. 61–63: Theorem 2.6.1, Corollary 2.6.2,
Theorem 2.6.3, Corollary 2.6.4 and Lemma 2.6.5, the analytic preliminaries for the convergence
of Poincaré series.

## Conventions
* Functions are `ℂ → ℂ`; the upper half plane is the open set `{z : ℂ | 0 < z.im}`.
* `dv(z) = y⁻² dx dy` is the invariant measure (`ModularFormsKB.Miyake.invMeasure`), the
  Lebesgue measure on `ℂ` with density `(z.im ^ 2)⁻¹`.
* For a set `U`, real `k` and `p ≥ 1`, Miyake's
  `‖f‖_U = (∫_U |f(z) Im(z)^{k/2}|^p dv(z))^{1/p}` is `weightedLpNorm U k p f`, an extended
  nonnegative real (it may be `∞`).
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal Real

namespace ModularFormsKB.Miyake

/-- Miyake's invariant measure `dv(z) = y⁻² dx dy` on `ℂ`, `z = x + i y`. -/
noncomputable def invMeasure : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (z.im ^ 2)⁻¹

/-- Miyake's norm `‖f‖_U = (∫_U |f(z) Im(z)^{k/2}|^p dv(z))^{1/p}` (§2.6, p. 63). -/
noncomputable def weightedLpNorm (U : Set ℂ) (k p : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  (∫⁻ z in U, (‖f z‖ₑ * ENNReal.ofReal (z.im ^ (k / 2))) ^ p ∂invMeasure) ^ (1 / p)

/-- The area sub-mean-value inequality for holomorphic functions:
`π δ² |f(c)| ≤ ∫_{|z - c| ≤ δ} |f(z)| dx dy` (Miyake's first step in the proof of
Theorem 2.6.1, from the Taylor expansion of `f` at `c`; here from the circle mean value
property `DiffContOnCl.circleAverage` and Tau Ceti's polar Fubini
`TauCeti.lintegral_circleLIntegral_eq_lintegral`). -/
lemma enorm_mul_le_setLIntegral_closedBall {f : ℂ → ℂ} {c : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (closedBall c δ)) :
    ‖f c‖ₑ * ENNReal.ofReal (π * δ ^ 2) ≤ ∫⁻ z in closedBall c δ, ‖f z‖ₑ := by
  classical
  set g : ℂ → ℝ≥0∞ := (closedBall c δ).indicator fun z => ‖f z‖ₑ with hgdef
  have hg : Measurable g := by
    have : Measurable ((closedBall c δ).piecewise (fun z => ‖f z‖ₑ) 0) :=
      hf.continuousOn.enorm.measurable_piecewise continuousOn_const measurableSet_closedBall
    rwa [Set.piecewise_eq_indicator] at this
  have hcirc : ∀ ρ ∈ Ioo (0 : ℝ) δ, ENNReal.ofReal ρ * (ENNReal.ofReal (2 * π) * ‖f c‖ₑ) ≤
      TauCeti.circleLIntegral g c ρ := by
    rintro ρ ⟨hρ0, hρδ⟩
    rw [TauCeti.circleLIntegral_eq_lintegral_Ioc g c ρ 0, zero_add]
    gcongr
    have hball : closedBall c ρ ⊆ closedBall c δ := closedBall_subset_closedBall hρδ.le
    have hmv : Real.circleAverage f c ρ = f c := by
      apply DiffContOnCl.circleAverage
      rw [abs_of_pos hρ0]
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball c hρ0.ne']
      exact hf.mono hball
    have hon : ∀ θ, circleMap c ρ θ ∈ closedBall c δ := fun θ =>
      hball (sphere_subset_closedBall (circleMap_mem_sphere c hρ0.le θ))
    have hcont : Continuous fun θ => f (circleMap c ρ θ) :=
      hf.continuousOn.comp_continuous (continuous_circleMap c ρ) hon
    have hint : IntegrableOn (fun θ => f (circleMap c ρ θ)) (Ioc 0 (2 * π)) :=
      (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hreal : 2 * π * ‖f c‖ ≤ ∫ θ in Ioc 0 (2 * π), ‖f (circleMap c ρ θ)‖ := by
      rw [← hmv, Real.circleAverage_def, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity),
        ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul,
        intervalIntegral.integral_of_le (by positivity)]
      exact norm_integral_le_integral_norm _
    calc ENNReal.ofReal (2 * π) * ‖f c‖ₑ = ENNReal.ofReal (2 * π * ‖f c‖) := by
          rw [ENNReal.ofReal_mul (q := ‖f c‖) (by positivity : (0 : ℝ) ≤ 2 * π), ofReal_norm]
      _ ≤ ENNReal.ofReal (∫ θ in Ioc 0 (2 * π), ‖f (circleMap c ρ θ)‖) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ∫⁻ θ in Ioc 0 (2 * π), ‖f (circleMap c ρ θ)‖ₑ :=
          ofReal_integral_norm_eq_lintegral_enorm hint
      _ = ∫⁻ θ in Ioc 0 (2 * π), g (circleMap c ρ θ) := by
          refine lintegral_congr fun θ => ?_
          rw [hgdef, Set.indicator_of_mem (hon θ)]
  have hrad : ∫⁻ ρ in Ioo (0 : ℝ) δ, ENNReal.ofReal ρ = ENNReal.ofReal (δ ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hδ.le, integral_id]
      ring_nf
    · exact (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun ρ hρ => hρ.1.le)
  calc ‖f c‖ₑ * ENNReal.ofReal (π * δ ^ 2)
      = (∫⁻ ρ in Ioo (0 : ℝ) δ, ENNReal.ofReal ρ) * (ENNReal.ofReal (2 * π) * ‖f c‖ₑ) := by
        rw [hrad, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm]
        congr 2
        ring
    _ = ∫⁻ ρ in Ioo (0 : ℝ) δ, ENNReal.ofReal ρ * (ENNReal.ofReal (2 * π) * ‖f c‖ₑ) :=
        (lintegral_mul_const _ ENNReal.measurable_ofReal).symm
    _ ≤ ∫⁻ ρ in Ioo (0 : ℝ) δ, TauCeti.circleLIntegral g c ρ := setLIntegral_mono' measurableSet_Ioo hcirc
    _ ≤ ∫⁻ ρ in Ioi (0 : ℝ), TauCeti.circleLIntegral g c ρ := lintegral_mono_set Ioo_subset_Ioi_self
    _ = ∫⁻ z, g z := TauCeti.lintegral_circleLIntegral_eq_lintegral hg c
    _ = ∫⁻ z in closedBall c δ, ‖f z‖ₑ := lintegral_indicator measurableSet_closedBall _

/-- Hölder's inequality against the constant `1`: `∫_s H dμ ≤ μ(s)^{1 - 1/p} (∫_s H^p dμ)^{1/p}`
for `p ≥ 1`. -/
lemma setLIntegral_le_measure_rpow_mul {μ : Measure ℂ} {s : Set ℂ} {H : ℂ → ℝ≥0∞}
    (hH : AEMeasurable H (μ.restrict s)) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ z in s, H z ∂μ ≤ μ s ^ (1 - 1 / p) * (∫⁻ z in s, H z ^ p ∂μ) ^ (1 / p) := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp
  have hpq := Real.HolderConjugate.conjExponent hp1
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s) hpq hH
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    one_mul] at h
  have hq : 1 / p.conjExponent = 1 - 1 / p := by
    have := hpq.inv_add_inv_eq_one
    rw [one_div, one_div]
    linarith
  rw [hq] at h
  rw [mul_comm]
  exact h

/-- **Miyake, Theorem 2.6.1.** Let `z₀ ∈ ℍ` and `δ > 0` with `M = {z : |z - z₀| ≤ 3δ} ⊆ ℍ`.
For real `k` and `p ≥ 1` there is a constant `C` with `|f(z₁)| ≤ C ‖f‖_M` for all `z₁` with
`|z₁ - z₀| ≤ δ` and every `f` continuous on `M` and holomorphic on its interior. -/
@[kb "miyake1989" "Theorem 2.6.1, p. 61"]
theorem exists_norm_le_weightedLpNorm_closedBall (z₀ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hM : closedBall z₀ (3 * δ) ⊆ {z : ℂ | 0 < z.im}) (k : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ℂ → ℂ, ContinuousOn f (closedBall z₀ (3 * δ)) →
      DifferentiableOn ℂ f (ball z₀ (3 * δ)) → ∀ z₁ ∈ closedBall z₀ δ,
        ‖f z₁‖ₑ ≤ C * weightedLpNorm (closedBall z₀ (3 * δ)) k p f := by
  set M := closedBall z₀ (3 * δ) with hMdef
  have hMc : IsCompact M := isCompact_closedBall _ _
  have hMmeas : MeasurableSet M := measurableSet_closedBall
  have hMne : M.Nonempty := ⟨z₀, mem_closedBall_self (by positivity)⟩
  obtain ⟨w, hwM, hwmin⟩ := hMc.exists_isMinOn hMne Complex.continuous_im.continuousOn
  have hm : 0 < w.im := hM hwM
  have hmM : ∀ z ∈ M, w.im ≤ z.im := fun z hz => hwmin hz
  -- Miyake's `C₁ = inf {Im(z)^{k/2 - 2}}`; we bound its reciprocal `Im(z)^{2 - k/2}` by `B`
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z ∈ M, z.im ^ (2 - k / 2) ≤ B := by
    have hco : ContinuousOn (fun z : ℂ => z.im ^ (2 - k / 2)) M :=
      Complex.continuous_im.continuousOn.rpow_const fun z hz => Or.inl (hM hz).ne'
    obtain ⟨B, hB⟩ := hMc.bddAbove_image hco
    exact ⟨B, fun z hz => hB ⟨z, hz, rfl⟩⟩
  have hdens : Measurable fun z : ℂ => ENNReal.ofReal (z.im ^ 2)⁻¹ := by fun_prop
  have hνM : invMeasure M ≠ ⊤ := by
    rw [invMeasure, withDensity_apply _ hMmeas]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in M, ENNReal.ofReal (w.im ^ 2)⁻¹) ?_
      (setLIntegral_mono' hMmeas fun z hz => ?_)
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMc.measure_lt_top.ne
    · apply ENNReal.ofReal_le_ofReal
      have := hmM z hz
      gcongr
  have hπδ : 0 < π * δ ^ 2 := by positivity
  refine ⟨(ENNReal.ofReal (π * δ ^ 2))⁻¹ * (ENNReal.ofReal B * invMeasure M ^ (1 - 1 / p)),
    ?_, ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hπδ).ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ?_ hνM))
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hp
  intro f hfc hfd z₁ hz₁
  have hsub : closedBall z₁ δ ⊆ ball z₀ (3 * δ) := by
    intro z hz
    rw [mem_ball]
    rw [mem_closedBall] at hz hz₁
    linarith [dist_triangle z z₁ z₀]
  have hsubM : closedBall z₁ δ ⊆ M := hsub.trans ball_subset_closedBall
  have hA := enorm_mul_le_setLIntegral_closedBall hδ (hfd.mono hsub)
  set H : ℂ → ℝ≥0∞ := fun z => ‖f z‖ₑ * ENNReal.ofReal (z.im ^ (k / 2)) with hHdef
  have hpt : ∀ z ∈ M, ‖f z‖ₑ ≤ ENNReal.ofReal B * (ENNReal.ofReal (z.im ^ 2)⁻¹ * H z) := by
    intro z hz
    have hy := hM hz
    have key : ENNReal.ofReal (z.im ^ 2)⁻¹ * ENNReal.ofReal (z.im ^ (k / 2)) *
        ENNReal.ofReal (z.im ^ (2 - k / 2)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (Real.rpow_nonneg hy.le _)),
        mul_assoc, ← Real.rpow_add hy, show k / 2 + (2 - k / 2) = (2 : ℝ) by ring,
        Real.rpow_two, inv_mul_cancel₀ (pow_pos hy 2).ne', ENNReal.ofReal_one]
    calc ‖f z‖ₑ = ‖f z‖ₑ * 1 := (mul_one _).symm
      _ = ENNReal.ofReal (z.im ^ (2 - k / 2)) * (ENNReal.ofReal (z.im ^ 2)⁻¹ * H z) := by
          rw [← key, hHdef]; ring
      _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (z.im ^ 2)⁻¹ * H z) := by
          gcongr
          exact hB z hz
  have hHmeas : AEMeasurable H (invMeasure.restrict M) :=
    (hfc.aemeasurable hMmeas).enorm.mul (by fun_prop : Measurable fun z : ℂ =>
      ENNReal.ofReal (z.im ^ (k / 2))).aemeasurable
  have hne0 : ENNReal.ofReal (π * δ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hπδ).ne'
  calc ‖f z₁‖ₑ = (ENNReal.ofReal (π * δ ^ 2))⁻¹ * (‖f z₁‖ₑ * ENNReal.ofReal (π * δ ^ 2)) := by
        rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hne0 ENNReal.ofReal_ne_top, mul_one]
    _ ≤ (ENNReal.ofReal (π * δ ^ 2))⁻¹ * ∫⁻ z in M, ‖f z‖ₑ := by
        gcongr
        exact hA.trans (lintegral_mono_set hsubM)
    _ ≤ (ENNReal.ofReal (π * δ ^ 2))⁻¹ *
          (ENNReal.ofReal B * ∫⁻ z in M, ENNReal.ofReal (z.im ^ 2)⁻¹ * H z) := by
        gcongr
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact setLIntegral_mono' hMmeas hpt
    _ = (ENNReal.ofReal (π * δ ^ 2))⁻¹ * (ENNReal.ofReal B * ∫⁻ z in M, H z ∂invMeasure) := by
        rw [invMeasure, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hdens _
          hMmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        rfl
    _ ≤ (ENNReal.ofReal (π * δ ^ 2))⁻¹ * (ENNReal.ofReal B *
          (invMeasure M ^ (1 - 1 / p) * (∫⁻ z in M, H z ^ p ∂invMeasure) ^ (1 / p))) := by
        gcongr
        exact setLIntegral_le_measure_rpow_mul hHmeas hp
    _ = _ := by
        simp only [weightedLpNorm, hHdef]
        ring

/-- `‖f‖_U` is monotone in `U`. -/
lemma weightedLpNorm_mono {U V : Set ℂ} (hUV : U ⊆ V) (k : ℝ) {p : ℝ} (hp : 0 < p)
    (f : ℂ → ℂ) : weightedLpNorm U k p f ≤ weightedLpNorm V k p f :=
  ENNReal.rpow_le_rpow (lintegral_mono_set hUV) (by positivity)

/-- The local form of Theorem 2.6.1 used for Corollaries 2.6.2 and 2.6.4: about each point of an
open `U ⊆ ℍ` there is a closed disc in `U` on which `|f| ≤ C ‖f‖_U` for every `f` holomorphic
on `U`. -/
lemma exists_closedBall_norm_le_weightedLpNorm (U : Set ℂ) (hU : IsOpen U)
    (hUH : U ⊆ {z : ℂ | 0 < z.im}) {x : ℂ} (hx : x ∈ U) (k : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ δ > 0, closedBall x δ ⊆ U ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∀ z ∈ closedBall x δ, ‖f z‖ₑ ≤ C * weightedLpNorm U k p f := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
  have hδ0 : 0 < ε / 4 := by positivity
  have hMU : closedBall x (3 * (ε / 4)) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_le_weightedLpNorm_closedBall x hδ0 (hMU.trans hUH) k hp
  refine ⟨ε / 4, hδ0, (closedBall_subset_closedBall (by linarith)).trans hMU, C, hC,
    fun f hf z hz => ?_⟩
  refine (hbound f (hf.continuousOn.mono hMU)
    (hf.mono (ball_subset_closedBall.trans hMU)) z hz).trans ?_
  gcongr
  exact weightedLpNorm_mono hMU k (by linarith) f

/-- **Miyake, Corollary 2.6.2.** For an open subset `U` of `ℍ` and `z₀ ∈ U` there is a constant
`C` with `|f(z₀)| ≤ C ‖f‖_U` for every `f` holomorphic on `U`. -/
@[kb "miyake1989" "Corollary 2.6.2, p. 62"]
theorem exists_norm_le_weightedLpNorm (U : Set ℂ) (hU : IsOpen U)
    (hUH : U ⊆ {z : ℂ | 0 < z.im}) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (k : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ‖f z₀‖ₑ ≤ C * weightedLpNorm U k p f := by
  obtain ⟨δ, hδ, -, C, hC, h⟩ := exists_closedBall_norm_le_weightedLpNorm U hU hUH hz₀ k hp
  exact ⟨C, hC, fun f hf => h f hf z₀ (mem_closedBall_self hδ.le)⟩

/-- The estimate of Theorem 2.6.1 on a disc about the point itself, with explicit constant:
if `Im(z)^{2 - k/2} ≤ B` on the closed disc `D` of radius `δ` about `c`, `D ⊆ ℍ`, then
`|f(c)| ≤ (π δ²)⁻¹ B v(D)^{1 - 1/p} ‖f‖_D` (Miyake's inequality (2.6.1)). -/
lemma enorm_le_weightedLpNorm_closedBall_self {f : ℂ → ℂ} {c : ℂ} {δ B : ℝ} (hδ : 0 < δ)
    (hH : closedBall c δ ⊆ {z : ℂ | 0 < z.im}) (k : ℝ)
    (hB : ∀ z ∈ closedBall c δ, z.im ^ (2 - k / 2) ≤ B)
    (hf : DifferentiableOn ℂ f (closedBall c δ)) {p : ℝ} (hp : 1 ≤ p) :
    ‖f c‖ₑ ≤ (ENNReal.ofReal (π * δ ^ 2))⁻¹ * (ENNReal.ofReal B *
      invMeasure (closedBall c δ) ^ (1 - 1 / p)) * weightedLpNorm (closedBall c δ) k p f := by
  set M := closedBall c δ with hMdef
  have hMmeas : MeasurableSet M := measurableSet_closedBall
  have hdens : Measurable fun z : ℂ => ENNReal.ofReal (z.im ^ 2)⁻¹ := by fun_prop
  have hπδ : 0 < π * δ ^ 2 := by positivity
  have hA := enorm_mul_le_setLIntegral_closedBall hδ hf
  set H : ℂ → ℝ≥0∞ := fun z => ‖f z‖ₑ * ENNReal.ofReal (z.im ^ (k / 2)) with hHdef
  have hpt : ∀ z ∈ M, ‖f z‖ₑ ≤ ENNReal.ofReal B * (ENNReal.ofReal (z.im ^ 2)⁻¹ * H z) := by
    intro z hz
    have hy : 0 < z.im := hH hz
    have key : ENNReal.ofReal (z.im ^ 2)⁻¹ * ENNReal.ofReal (z.im ^ (k / 2)) *
        ENNReal.ofReal (z.im ^ (2 - k / 2)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (Real.rpow_nonneg hy.le _)),
        mul_assoc, ← Real.rpow_add hy, show k / 2 + (2 - k / 2) = (2 : ℝ) by ring,
        Real.rpow_two, inv_mul_cancel₀ (pow_pos hy 2).ne', ENNReal.ofReal_one]
    calc ‖f z‖ₑ = ‖f z‖ₑ * 1 := (mul_one _).symm
      _ = ENNReal.ofReal (z.im ^ (2 - k / 2)) * (ENNReal.ofReal (z.im ^ 2)⁻¹ * H z) := by
          rw [← key, hHdef]; ring
      _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (z.im ^ 2)⁻¹ * H z) := by
          gcongr
          exact hB z hz
  have hHmeas : AEMeasurable H (invMeasure.restrict M) :=
    (hf.continuousOn.aemeasurable hMmeas).enorm.mul (by fun_prop : Measurable fun z : ℂ =>
      ENNReal.ofReal (z.im ^ (k / 2))).aemeasurable
  have hne0 : ENNReal.ofReal (π * δ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hπδ).ne'
  calc ‖f c‖ₑ = (ENNReal.ofReal (π * δ ^ 2))⁻¹ * (‖f c‖ₑ * ENNReal.ofReal (π * δ ^ 2)) := by
        rw [mul_comm, mul_assoc, ENNReal.mul_inv_cancel hne0 ENNReal.ofReal_ne_top, mul_one]
    _ ≤ (ENNReal.ofReal (π * δ ^ 2))⁻¹ * ∫⁻ z in M, ‖f z‖ₑ := by gcongr
    _ ≤ (ENNReal.ofReal (π * δ ^ 2))⁻¹ *
          (ENNReal.ofReal B * ∫⁻ z in M, ENNReal.ofReal (z.im ^ 2)⁻¹ * H z) := by
        gcongr
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact setLIntegral_mono' hMmeas hpt
    _ = (ENNReal.ofReal (π * δ ^ 2))⁻¹ * (ENNReal.ofReal B * ∫⁻ z in M, H z ∂invMeasure) := by
        rw [invMeasure, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hdens _
          hMmeas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        rfl
    _ ≤ (ENNReal.ofReal (π * δ ^ 2))⁻¹ * (ENNReal.ofReal B *
          (invMeasure M ^ (1 - 1 / p) * (∫⁻ z in M, H z ^ p ∂invMeasure) ^ (1 / p))) := by
        gcongr
        exact setLIntegral_le_measure_rpow_mul hHmeas hp
    _ = _ := by
        simp only [weightedLpNorm, hHdef]
        ring

/-- On a measurable set where `Im z ≥ m > 0`, `v(s) ≤ m⁻² · area(s)`. -/
lemma invMeasure_le {s : Set ℂ} (hs : MeasurableSet s) {m : ℝ} (hm : 0 < m)
    (hms : ∀ z ∈ s, m ≤ z.im) : invMeasure s ≤ ENNReal.ofReal (m ^ 2)⁻¹ * volume s := by
  rw [invMeasure, withDensity_apply _ hs, ← setLIntegral_const]
  refine setLIntegral_mono' hs fun z hz => ENNReal.ofReal_le_ofReal ?_
  have := hms z hz
  gcongr

/-- **Miyake, Theorem 2.6.3.** If `f` is holomorphic on `ℍ` and `∫_ℍ |f(z) Im(z)^{k/2}|^p dv(z)`
is finite, then `f(x + iy) → 0` as `|x| → ∞`, uniformly for `y` in `[a, b]`, `0 < a < b`. -/
@[kb "miyake1989" "Theorem 2.6.3, p. 62"]
theorem tendsto_zero_of_weightedLpNorm_ne_top {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.im}) (k : ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hfin : weightedLpNorm {z : ℂ | 0 < z.im} k p f ≠ ⊤) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, a ≤ z.im → z.im ≤ b → R ≤ |z.re| → ‖f z‖ ≤ ε := by
  intro ε hε
  set ℍs : Set ℂ := {z : ℂ | 0 < z.im} with hℍs
  -- Miyake's `2δ < a`; here discs of radius `δ = a / 2` about the points of the strip
  set δ := a / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hp0 : 0 < p := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ y ∈ Icc δ (b + δ), y ^ (2 - k / 2) ≤ B := by
    have hco : ContinuousOn (fun y : ℝ => y ^ (2 - k / 2)) (Icc δ (b + δ)) :=
      continuousOn_id.rpow_const fun y hy => Or.inl (hδ.trans_le hy.1).ne'
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hco
    exact ⟨B, fun y hy => hB ⟨y, hy, rfl⟩⟩
  set V : ℝ≥0∞ := ENNReal.ofReal (δ ^ 2)⁻¹ * (ENNReal.ofReal δ ^ 2 * NNReal.pi) with hV
  set K : ℝ≥0∞ := (ENNReal.ofReal (π * δ ^ 2))⁻¹ * (ENNReal.ofReal B * V ^ (1 - 1 / p)) with hK
  have he : 0 ≤ 1 - 1 / p := by
    rw [sub_nonneg, div_le_one hp0]
    exact hp
  have hKtop : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg he ?_))
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.coe_ne_top)
  -- the pointwise estimate on the strip, with a constant independent of the point
  have hstrip : ∀ z : ℂ, a ≤ z.im → z.im ≤ b →
      ‖f z‖ₑ ≤ K * weightedLpNorm (closedBall z δ) k p f := by
    intro z hza hzb
    have him : ∀ w ∈ closedBall z δ, δ ≤ w.im ∧ w.im ≤ b + δ := by
      intro w hw
      have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [Complex.sub_im] at h1
      constructor <;> linarith [abs_le.1 (h1.trans hw)]
    have hH : closedBall z δ ⊆ ℍs := fun w hw => hδ.trans_le (him w hw).1
    have h := enorm_le_weightedLpNorm_closedBall_self hδ hH k
      (fun w hw => hB w.im ⟨(him w hw).1, (him w hw).2⟩) (hf.mono hH) hp
    refine h.trans (mul_le_mul_left ?_ _)
    have hν : invMeasure (closedBall z δ) ≤ V :=
      calc invMeasure (closedBall z δ) ≤ ENNReal.ofReal (δ ^ 2)⁻¹ * volume (closedBall z δ) :=
            invMeasure_le measurableSet_closedBall hδ fun w hw => (him w hw).1
        _ = V := by rw [Complex.volume_closedBall]
    exact mul_le_mul_right (mul_le_mul_right (ENNReal.rpow_le_rpow hν he) _) _
  -- the tails `S n = {z ∈ ℍ | |Re z| ≥ n}` carry less and less of `∫ |f Im^{k/2}|^p dv`
  set H : ℂ → ℝ≥0∞ := fun z => ‖f z‖ₑ * ENNReal.ofReal (z.im ^ (k / 2)) with hHdef
  set μ : Measure ℂ := (invMeasure.restrict ℍs).withDensity fun z => H z ^ p with hμ
  set S : ℕ → Set ℂ := fun n => {z : ℂ | 0 < z.im ∧ (n : ℝ) ≤ |z.re|} with hS
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => by
    show MeasurableSet ({z : ℂ | 0 < z.im} ∩ {z : ℂ | (n : ℝ) ≤ |z.re|})
    exact (isOpen_lt continuous_const Complex.continuous_im).measurableSet.inter
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_re)).measurableSet
  have hμS : ∀ n, μ (S n) = ∫⁻ z in S n, H z ^ p ∂invMeasure := by
    intro n
    rw [hμ, withDensity_apply _ (hSmeas n), Measure.restrict_restrict (hSmeas n)]
    congr 2
    exact inter_eq_left.2 fun z hz => hz.1
  have hI : ∫⁻ z in ℍs, H z ^ p ∂invMeasure ≠ ⊤ := by
    intro htop
    apply hfin
    change (∫⁻ z in ℍs, H z ^ p ∂invMeasure) ^ (1 / p) = ⊤
    rw [htop, ENNReal.top_rpow_of_pos (by positivity)]
  have hanti : Antitone S := fun m n hmn z hz =>
    ⟨hz.1, le_trans (by exact_mod_cast hmn) hz.2⟩
  have hfinS : ∃ n, μ (S n) ≠ ⊤ := ⟨0, by
    rw [hμS]
    exact ne_top_of_le_ne_top hI (lintegral_mono_set fun z hz => hz.1)⟩
  have hinter : (⋂ n, S n) = ∅ := by
    ext z
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨n, hn⟩ := exists_nat_gt |z.re|
    exact ⟨n, fun h => (not_le.2 hn) h.2⟩
  have htend := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hSmeas n).nullMeasurableSet)
    hanti hfinS
  rw [hinter, measure_empty] at htend
  have htend' : Tendsto (fun n => K * μ (S n) ^ (1 / p)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => μ (S n) ^ (1 / p)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto (0 : ℝ≥0∞)).comp htend
      rwa [ENNReal.zero_rpow_of_pos (by positivity)] at this
    have := ENNReal.Tendsto.const_mul h1 (Or.inr hKtop)
    rwa [mul_zero] at this
  obtain ⟨N, hN⟩ := ((tendsto_order.1 htend').2 _ (ENNReal.ofReal_pos.2 hε)).exists
  refine ⟨N + δ, fun z hza hzb hR => ?_⟩
  have hsub : closedBall z δ ⊆ S N := by
    intro w hw
    have h1 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [Complex.sub_re] at h1
    rw [Complex.sub_im] at h2
    refine ⟨by linarith [abs_le.1 (h2.trans hw)], ?_⟩
    have h3 := abs_sub_abs_le_abs_sub z.re w.re
    rw [abs_sub_comm] at h3
    linarith
  have hfz : ‖f z‖ₑ < ENNReal.ofReal ε :=
    calc ‖f z‖ₑ ≤ K * weightedLpNorm (closedBall z δ) k p f := hstrip z hza hzb
      _ ≤ K * weightedLpNorm (S N) k p f := by
          gcongr
          exact weightedLpNorm_mono hsub k hp0 f
      _ = K * μ (S N) ^ (1 / p) := by rw [hμS]; rfl
      _ < ENNReal.ofReal ε := hN
  rw [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hε] at hfz
  exact hfz.le

/-- **Miyake, Corollary 2.6.4.** Let `U` be an open subset of `ℍ`. A sequence of holomorphic
functions on `U` that is Cauchy for `‖·‖_U` converges uniformly on compact subsets of `U` to a
holomorphic function on `U`. -/
@[kb "miyake1989" "Corollary 2.6.4, p. 63"]
theorem exists_tendstoLocallyUniformlyOn_of_cauchy (U : Set ℂ) (hU : IsOpen U)
    (hUH : U ⊆ {z : ℂ | 0 < z.im}) (k : ℝ) {p : ℝ} (hp : 1 ≤ p) (F : ℕ → ℂ → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hcauchy : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      weightedLpNorm U k p (F m - F n) < ε) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ TendstoLocallyUniformlyOn F f atTop U := by
  classical
  -- by Theorem 2.6.1, the sequence is uniformly Cauchy on a closed disc about each point
  have hloc : ∀ x ∈ U, ∃ δ > 0, closedBall x δ ⊆ U ∧
      UniformCauchySeqOn F atTop (closedBall x δ) := by
    intro x hx
    obtain ⟨δ, hδ, hsub, C, hC, h⟩ := exists_closedBall_norm_le_weightedLpNorm U hU hUH hx k hp
    refine ⟨δ, hδ, hsub, Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_⟩
    obtain ⟨η, hη, hηC⟩ := ENNReal.exists_pos_mul_lt hC (ENNReal.ofReal_pos.2 hε).ne'
    obtain ⟨N, hN⟩ := hcauchy η hη
    refine ⟨N, fun m hm n hn z hz => ?_⟩
    have h1 := h (F m - F n) ((hF m).sub (hF n)) z hz
    have h2 : C * weightedLpNorm U k p (F m - F n) < ENNReal.ofReal ε :=
      calc C * weightedLpNorm U k p (F m - F n) ≤ C * η := by
            gcongr
            exact (hN m hm n hn).le
        _ = η * C := mul_comm _ _
        _ < ENNReal.ofReal ε := hηC
    have h3 : ‖F m z - F n z‖ₑ < ENNReal.ofReal ε := lt_of_le_of_lt h1 h2
    rw [dist_eq_norm, ← ENNReal.ofReal_lt_ofReal_iff hε, ofReal_norm]
    exact h3
  have hpt : ∀ x ∈ U, ∃ a, Tendsto (fun n => F n x) atTop (𝓝 a) := fun x hx => by
    obtain ⟨δ, hδ, -, hc⟩ := hloc x hx
    exact cauchySeq_tendsto_of_complete (hc.cauchySeq (mem_closedBall_self hδ.le))
  choose! f hf using hpt
  have hlu : TendstoLocallyUniformlyOn F f atTop U := by
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
    obtain ⟨δ, hδ, hsub, hc⟩ := hloc x hx
    exact ⟨closedBall x δ, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hδ),
      hc.tendstoUniformlyOn_of_tendsto fun z hz => hf z (hsub hz)⟩
  exact ⟨f, hlu.differentiableOn (Eventually.of_forall hF) hU, hlu⟩

/-- **Miyake, Lemma 2.6.5.** Let `(f_n)` be holomorphic on an open set `D ⊆ ℂ` and `z₀ ∈ D`.
If `f_n` converges uniformly on compact subsets of `D - {z₀}`, then it converges uniformly on
compact subsets of `D` (to a limit agreeing with the old one off `z₀`). -/
@[kb "miyake1989" "Lemma 2.6.5, p. 63"]
theorem exists_tendstoLocallyUniformlyOn_of_punctured {D : Set ℂ} (hD : IsOpen D) {z₀ : ℂ}
    (hz₀ : z₀ ∈ D) (F : ℕ → ℂ → ℂ) (hF : ∀ n, DifferentiableOn ℂ (F n) D) (g : ℂ → ℂ)
    (hg : TendstoLocallyUniformlyOn F g atTop (D \ {z₀})) :
    ∃ G : ℂ → ℂ, TendstoLocallyUniformlyOn F G atTop D ∧ EqOn G g (D \ {z₀}) := by
  classical
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD z₀ hz₀
  set ρ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hcl : closedBall z₀ ρ ⊆ D := (closedBall_subset_ball (by linarith)).trans hrD
  have hD' : IsOpen (D \ {z₀}) := hD.sdiff isClosed_singleton
  have hsph : sphere z₀ ρ ⊆ D \ {z₀} := fun z hz => ⟨hcl (sphere_subset_closedBall hz), by
    rintro rfl
    rw [mem_sphere, dist_self] at hz
    exact hρ.ne hz⟩
  have hunif : TendstoUniformlyOn F g atTop (sphere z₀ ρ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hD').1 hg _ hsph (isCompact_sphere _ _)
  -- Miyake uses the Cauchy integral over the circle `|ζ - z₀| = ρ`; we use the maximum modulus
  -- principle, which gives the same uniform Cauchy property on the closed disc.
  have hcauchy : UniformCauchySeqOn F atTop (closedBall z₀ ρ) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      Metric.uniformCauchySeqOn_iff.1 hunif.uniformCauchySeqOn (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn z hz => ?_⟩
    have hdiff : DiffContOnCl ℂ (fun w => F m w - F n w) (ball z₀ ρ) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z₀ hρ.ne']
      exact ((hF m).sub (hF n)).mono hcl
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiff
      (C := ε / 2) (fun w hw => by
        rw [frontier_ball z₀ hρ.ne'] at hw
        have := hN m hm n hn w hw
        rw [dist_eq_norm] at this
        exact this.le) (by rwa [closure_ball z₀ hρ.ne'])
    rw [dist_eq_norm]
    linarith
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hcauchy.cauchySeq (mem_closedBall_self hρ.le))
  refine ⟨Function.update g z₀ a, ?_, fun z hz => Function.update_of_ne hz.2 _ _⟩
  have hpt : ∀ z ∈ D, Tendsto (fun n => F n z) atTop (𝓝 (Function.update g z₀ a z)) := by
    intro z hz
    by_cases h : z = z₀
    · subst h; simpa using ha
    · rw [Function.update_of_ne h]
      exact hg.tendsto_at ⟨hz, h⟩
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
  by_cases hx0 : x = z₀
  · subst hx0
    refine ⟨closedBall x ρ, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hρ), ?_⟩
    exact hcauchy.tendstoUniformlyOn_of_tendsto fun z hz => hpt z (hcl hz)
  · obtain ⟨δ, hδ, hδD⟩ := Metric.isOpen_iff.1 hD' x ⟨hx, hx0⟩
    have hδ2 : 0 < δ / 2 := by positivity
    refine ⟨closedBall x (δ / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x hδ2), ?_⟩
    have hsub : closedBall x (δ / 2) ⊆ D \ {z₀} :=
      (closedBall_subset_ball (by linarith)).trans hδD
    refine ((tendstoLocallyUniformlyOn_iff_forall_isCompact hD').1 hg _ hsub
      (isCompact_closedBall _ _)).congr_right fun z hz => ?_
    exact (Function.update_of_ne (hsub hz).2 _ _).symm

end ModularFormsKB.Miyake
