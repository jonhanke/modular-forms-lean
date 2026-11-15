import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Tools for Miyake §7.2: holomorphic parameter integrals of `exp` of a linear form

Every integrand of Miyake §7.2 (the confluent hypergeometric integral $\sigma(z;\alpha,\beta)$ of
(7.2.16), the integral $\eta(y;\alpha,\beta;t)$ of (7.2.17), the Fourier integral $\xi(y;\alpha,\beta;t)$
of (7.2.11)) has the form $x \mapsto \exp(L_x(p) + c_x)$ where $L_x$ is a $\mathbb C$-linear form in the
parameters $p$ (for instance $(z,\alpha,\beta) \mapsto -uz + \alpha\log(u+1) + \beta\log u$). This file
proves that such parameter integrals are holomorphic (jointly in all parameters) under a local
integrable majorant of $|\exp(L_x(p)+c_x)|(1 + \|L_x\|)$, and supplies the majorant on $(0,\infty)$
used for $\sigma$ and $\eta$.
-/

open MeasureTheory Set Filter Topology Asymptotics

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

/-- **Holomorphy of parameter integrals of $\exp(L_x(p) + c_x)$**: if $|\exp(L_x(p)+c_x)|(1+\|L_x\|)$
has an integrable majorant for $p$ in a ball around $p_0$, then
$p \mapsto \int \exp(L_x(p)+c_x)\,d\mu(x)$ is complex differentiable at $p_0$, with derivative
$\int \exp(L_x(p_0)+c_x)\,L_x\,d\mu(x)$. -/
theorem hasFDerivAt_integral_cexp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : X → V →L[ℂ] ℂ) (c : X → ℂ) (hL : AEStronglyMeasurable L μ)
    (hc : AEStronglyMeasurable c μ) {p₀ : V} {r : ℝ} (hr : 0 < r) {g : X → ℝ}
    (hg : Integrable g μ)
    (hb : ∀ᵐ x ∂μ, ∀ p ∈ Metric.ball p₀ r, ‖Complex.exp (L x p + c x)‖ * (1 + ‖L x‖) ≤ g x) :
    HasFDerivAt (fun p ↦ ∫ x, Complex.exp (L x p + c x) ∂μ)
      (∫ x, Complex.exp (L x p₀ + c x) • L x ∂μ) p₀ := by
  have hmeas : ∀ p : V, AEStronglyMeasurable (fun x ↦ Complex.exp (L x p + c x)) μ := fun p ↦
    Complex.continuous_exp.comp_aestronglyMeasurable
      ((hL.apply_continuousLinearMap p).add hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := g)
    (F' := fun p x ↦ Complex.exp (L x p + c x) • L x) (Metric.ball_mem_nhds p₀ hr)
    (Eventually.of_forall fun p ↦ hmeas p) ?_ ((hmeas p₀).smul hL) ?_ hg ?_
  · refine hg.mono' (hmeas p₀) (hb.mono fun x hx ↦ ?_)
    have := hx p₀ (Metric.mem_ball_self hr)
    nlinarith [norm_nonneg (Complex.exp (L x p₀ + c x)), norm_nonneg (L x)]
  · refine hb.mono fun x hx p hp ↦ ?_
    rw [norm_smul]
    have := hx p hp
    nlinarith [norm_nonneg (Complex.exp (L x p + c x)), norm_nonneg (L x)]
  · refine Eventually.of_forall fun x p _ ↦ ?_
    have h1 : HasFDerivAt (fun q ↦ L x q + c x) (L x) p :=
      (L x).hasFDerivAt.add_const (c x)
    exact (Complex.hasDerivAt_exp _).comp_hasFDerivAt p h1

/-- Differentiability on an open set from local majorants (`hasFDerivAt_integral_cexp`). -/
theorem differentiableOn_integral_cexp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : X → V →L[ℂ] ℂ) (c : X → ℂ) (hL : AEStronglyMeasurable L μ)
    (hc : AEStronglyMeasurable c μ) {U : Set V}
    (hU : ∀ p₀ ∈ U, ∃ r > 0, ∃ g : X → ℝ, Integrable g μ ∧
      ∀ᵐ x ∂μ, ∀ p ∈ Metric.ball p₀ r, ‖Complex.exp (L x p + c x)‖ * (1 + ‖L x‖) ≤ g x) :
    DifferentiableOn ℂ (fun p ↦ ∫ x, Complex.exp (L x p + c x) ∂μ) U := by
  intro p₀ hp₀
  obtain ⟨r, hr, g, hg, hb⟩ := hU p₀ hp₀
  exact (hasFDerivAt_integral_cexp L c hL hc hr hg hb).differentiableAt.differentiableWithinAt

/-! ### The majorant on `(0, ∞)` -/

/-- For $a > 0$, $b > -1$ and any $A$, the function $e^{-au}u^b(1+u)^A(1+|\log u|)$ is integrable on
$(0,\infty)$. -/
theorem integrableOn_majorant {a b : ℝ} (ha : 0 < a) (hb : -1 < b) (A : ℝ) :
    IntegrableOn (fun u : ℝ ↦ Real.exp (-a * u) * u ^ b * (1 + u) ^ A * (1 + |Real.log u|))
      (Ioi 0) := by
  set f : ℝ → ℝ := fun u ↦ Real.exp (-a * u) * u ^ b * (1 + u) ^ A * (1 + |Real.log u|) with hf
  have hcont : ContinuousOn f (Ioi 0) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have h1 : ContinuousAt (fun u : ℝ ↦ u ^ b) u := Real.continuousAt_rpow_const _ _ (Or.inl hu0)
    have h2 : ContinuousAt (fun u : ℝ ↦ (1 + u) ^ A) u :=
      ContinuousAt.rpow_const (f := fun u : ℝ ↦ 1 + u) (by fun_prop)
        (Or.inl (by have := mem_Ioi.mp hu; show 1 + u ≠ 0; linarith))
    have h3 : ContinuousAt (fun u : ℝ ↦ Real.log u) u := Real.continuousAt_log hu0
    have : ContinuousAt f u := by
      simp only [hf]
      fun_prop
    exact this.continuousWithinAt
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hunion]
  refine IntegrableOn.union ?_ ?_
  · -- near zero
    set t : ℝ := (b + 1) / 2 with ht
    have htpos : 0 < t := by rw [ht]; linarith
    have hs : -1 < (b - 1) / 2 := by linarith
    have hint : IntegrableOn (fun u : ℝ ↦ u ^ ((b - 1) / 2)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' hs (a := 0) (b := 1))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine (hint.const_mul (2 ^ |A| * (1 + 1 / t))).mono' ?_ ?_
    · exact hmeas.mono_set Ioc_subset_Ioi_self
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun u hu ↦ ?_)
      obtain ⟨hu0, hu1⟩ := hu
      have hlog := Real.abs_log_mul_self_rpow_lt u t hu0 hu1 htpos
      have e1 : Real.exp (-a * u) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      have e2 : (1 + u) ^ A ≤ 2 ^ |A| := by
        calc (1 + u) ^ A ≤ (1 + u) ^ |A| :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (le_abs_self A)
          _ ≤ 2 ^ |A| := Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg A)
      have e3 : u ^ b ≤ u ^ ((b - 1) / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hu0 hu1 (by linarith)
      have e4 : u ^ b * |Real.log u| ≤ u ^ ((b - 1) / 2) * (1 / t) := by
        have : u ^ b = u ^ ((b - 1) / 2) * u ^ t := by
          rw [← Real.rpow_add hu0]; congr 1; rw [ht]; ring
        rw [this, mul_assoc]
        have hp : 0 ≤ u ^ ((b - 1) / 2) := (Real.rpow_pos_of_pos hu0 _).le
        refine mul_le_mul_of_nonneg_left ?_ hp
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hu0 t)] at hlog
        rw [mul_comm]
        exact hlog.le
      have hpos : 0 ≤ u ^ b := (Real.rpow_pos_of_pos hu0 _).le
      have hB : 0 ≤ (1 + u) ^ A := (Real.rpow_pos_of_pos (by linarith) _).le
      have hE : 0 ≤ Real.exp (-a * u) := (Real.exp_pos _).le
      have key : u ^ b * (1 + |Real.log u|) ≤ u ^ ((b - 1) / 2) * (1 + 1 / t) := by
        nlinarith
      have hfu : f u = Real.exp (-a * u) * (1 + u) ^ A * (u ^ b * (1 + |Real.log u|)) := by
        simp only [hf]; ring
      have h6 : 0 ≤ u ^ b * (1 + |Real.log u|) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hfu]; positivity), hfu]
      have h5 : Real.exp (-a * u) * (1 + u) ^ A ≤ 2 ^ |A| := by
        calc _ ≤ 1 * 2 ^ |A| := mul_le_mul e1 e2 hB (by norm_num)
          _ = _ := one_mul _
      calc Real.exp (-a * u) * (1 + u) ^ A * (u ^ b * (1 + |Real.log u|))
          ≤ 2 ^ |A| * (u ^ ((b - 1) / 2) * (1 + 1 / t)) :=
            mul_le_mul h5 key h6 (by positivity)
        _ = _ := by ring
  · -- at infinity
    set s : ℝ := |b| + |A| + 1 with hsdef
    have hspos : -1 < s := by have := abs_nonneg b; have := abs_nonneg A; linarith
    have hint : IntegrableOn (fun u : ℝ ↦ u ^ s * Real.exp (-a * u ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow hspos one_pos ha
    have hint' : IntegrableOn (fun u : ℝ ↦ u ^ s * Real.exp (-a * u)) (Ioi 1) := by
      refine (hint.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun (fun u _ ↦ ?_)
        measurableSet_Ioi
      simp
    refine ((hint'.const_mul (2 ^ (|A| + 1))).mono' ?_ ?_)
    · exact hmeas.mono_set (Ioi_subset_Ioi zero_le_one)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu ↦ ?_)
      have hu1 : 1 < u := hu
      have hu0 : 0 < u := by linarith
      have hE : 0 ≤ Real.exp (-a * u) := (Real.exp_pos _).le
      have e1 : u ^ b ≤ u ^ |b| := Real.rpow_le_rpow_of_exponent_le hu1.le (le_abs_self b)
      have e2 : (1 + u) ^ A ≤ (2 * u) ^ |A| := by
        calc (1 + u) ^ A ≤ (1 + u) ^ |A| :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (le_abs_self A)
          _ ≤ (2 * u) ^ |A| := Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg A)
      have e3 : 1 + |Real.log u| ≤ 2 * u := by
        have := Real.log_le_sub_one_of_pos hu0
        rw [abs_of_nonneg (Real.log_nonneg hu1.le)]; linarith
      have hpb : 0 ≤ u ^ b := (Real.rpow_pos_of_pos hu0 _).le
      have hpA : 0 ≤ (1 + u) ^ A := (Real.rpow_pos_of_pos (by linarith) _).le
      have hf0 : 0 ≤ f u := by simp only [hf]; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hf0]
      have e2' : (2 * u) ^ |A| = 2 ^ |A| * u ^ |A| := Real.mul_rpow (by norm_num) hu0.le
      have hs' : u ^ s = u ^ |b| * u ^ |A| * u := by
        rw [hsdef, Real.rpow_add hu0, Real.rpow_add hu0, Real.rpow_one]
      have h2A : (2 : ℝ) ^ (|A| + 1) = 2 ^ |A| * 2 := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
      have hu_b : 0 ≤ u ^ |b| := (Real.rpow_pos_of_pos hu0 _).le
      calc f u = Real.exp (-a * u) * (u ^ b * (1 + u) ^ A * (1 + |Real.log u|)) := by
            simp only [hf]; ring
        _ ≤ Real.exp (-a * u) * (u ^ |b| * (2 ^ |A| * u ^ |A|) * (2 * u)) := by
            refine mul_le_mul_of_nonneg_left ?_ hE
            have h3 : u ^ b * (1 + u) ^ A ≤ u ^ |b| * (2 * u) ^ |A| :=
              mul_le_mul e1 e2 hpA hu_b
            calc u ^ b * (1 + u) ^ A * (1 + |Real.log u|)
                ≤ (u ^ |b| * (2 * u) ^ |A|) * (2 * u) :=
                  mul_le_mul h3 e3 (by positivity) (by positivity)
              _ = _ := by rw [e2']
        _ = 2 ^ (|A| + 1) * (u ^ s * Real.exp (-a * u)) := by
            rw [h2A, hs']; ring

end ModularFormsKB.Miyake.HeckeTrick
