import ModularFormsKB.Miyake.HeckeTrick.ExpIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Normed.Operator.Prod
import ModularFormsKB.Citation
/-!
# Miyake §7.2: the confluent hypergeometric integrals $\sigma$ and $\eta$

Miyake, *Modular Forms* (Springer 1989), §7.2, pp. 276–277. With $\mathbf H' = \{\operatorname{Re} z > 0\}$
the right half plane (7.2.15),
$$\sigma(z;\alpha,\beta) = \int_0^\infty e^{-zu}(u+1)^{\alpha-1}u^{\beta-1}\,du \quad (z,\beta \in \mathbf H',
\ \alpha \in \mathbb C) \qquad (7.2.16)$$
$$\eta(y;\alpha,\beta;t) = \int_{|t|}^\infty e^{-yu}(u+t)^{\alpha-1}(u-t)^{\beta-1}\,du
\quad (y > 0,\ t \in \mathbb R). \qquad (7.2.17)$$
The powers have nonnegative real bases, so they are the principal powers. Lean's integral is $0$ when the
integrand is not integrable; every statement below says where the integrals converge.

"Uniformly convergent on every compact subset" (Lemma 7.2.1) is stated in the form the book's proof gives
and later proofs use: on each compact set of parameters the integrand has one integrable majorant.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

/-- The integrand of (7.2.16): $e^{-zu}(u+1)^{\alpha-1}u^{\beta-1}$. -/
def sigmaIntegrand (z α β : ℂ) (u : ℝ) : ℂ :=
  cexp (-z * u) * (((u + 1 : ℝ) : ℂ) ^ (α - 1)) * ((u : ℂ) ^ (β - 1))

/-- **Miyake (7.2.16).** The confluent hypergeometric function
$\sigma(z;\alpha,\beta) = \int_0^\infty e^{-zu}(u+1)^{\alpha-1}u^{\beta-1}\,du$, for $z, \beta \in \mathbf H'$. -/
@[kb "miyake1989" "(7.2.16), p. 276"]
def sigma (z α β : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), sigmaIntegrand z α β u

/-- The integrand of (7.2.17): $e^{-yu}(u+t)^{\alpha-1}(u-t)^{\beta-1}$. -/
def etaIntegrand (y : ℝ) (α β : ℂ) (t u : ℝ) : ℂ :=
  cexp (-(y : ℂ) * u) * (((u + t : ℝ) : ℂ) ^ (α - 1)) * (((u - t : ℝ) : ℂ) ^ (β - 1))

/-- **Miyake (7.2.17).** $\eta(y;\alpha,\beta;t) = \int_{|t|}^\infty e^{-yu}(u+t)^{\alpha-1}(u-t)^{\beta-1}\,du$. -/
@[kb "miyake1989" "(7.2.17), p. 276"]
def eta (y : ℝ) (α β : ℂ) (t : ℝ) : ℂ := ∫ u in Ioi |t|, etaIntegrand y α β t u

/-! ### Auxiliary: the integrand as `exp` of a linear form, and norm bounds -/

/-- The $\mathbb C$-linear form $(z,\alpha,\beta) \mapsto -uz + \log(u+1)\alpha + \log u\,\beta$. -/
def sigmaL (u : ℝ) : ℂ × ℂ × ℂ →L[ℂ] ℂ :=
  (-(u : ℂ)) • ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ) +
    ((Real.log (u + 1) : ℝ) : ℂ) •
      (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ)) +
    ((Real.log u : ℝ) : ℂ) •
      (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))

/-- The constant $-\log(u+1) - \log u$. -/
def sigmaC (u : ℝ) : ℂ := ((-Real.log (u + 1) - Real.log u : ℝ) : ℂ)

theorem sigmaL_apply (u : ℝ) (p : ℂ × ℂ × ℂ) :
    sigmaL u p = -(u : ℂ) * p.1 + ((Real.log (u + 1) : ℝ) : ℂ) * p.2.1
      + ((Real.log u : ℝ) : ℂ) * p.2.2 := by
  simp [sigmaL]

theorem sigmaIntegrand_eq {z α β : ℂ} {u : ℝ} (hu : 0 < u) :
    sigmaIntegrand z α β u = cexp (sigmaL u (z, α, β) + sigmaC u) := by
  have h1 : ((u + 1 : ℝ) : ℂ) ^ (α - 1) = cexp (((Real.log (u + 1) : ℝ) : ℂ) * (α - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by linarith : (u + 1) ≠ 0)),
      Complex.ofReal_log (by linarith)]
  have h2 : ((u : ℝ) : ℂ) ^ (β - 1) = cexp (((Real.log u : ℝ) : ℂ) * (β - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hu.ne'), Complex.ofReal_log hu.le]
  unfold sigmaIntegrand
  rw [h1, h2, sigmaL_apply, sigmaC]
  dsimp only
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_sigmaIntegrand {z α β : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖sigmaIntegrand z α β u‖ =
      Real.exp (-(z.re * u)) * (u + 1) ^ (α.re - 1) * u ^ (β.re - 1) := by
  unfold sigmaIntegrand
  rw [norm_mul, norm_mul, Complex.norm_exp,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < u + 1),
    Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp

theorem rpow_le_rpow_mul_one_add {u b x B : ℝ} (hu : 0 < u) (hb : b ≤ x) (hB : x ≤ B) :
    u ^ x ≤ u ^ b * (1 + u) ^ (B - b) := by
  rcases le_total u 1 with h | h
  · calc u ^ x ≤ u ^ b := Real.rpow_le_rpow_of_exponent_ge hu h hb
      _ = u ^ b * 1 := (mul_one _).symm
      _ ≤ u ^ b * (1 + u) ^ (B - b) :=
        mul_le_mul_of_nonneg_left (Real.one_le_rpow (by linarith) (by linarith))
          (Real.rpow_pos_of_pos hu _).le
  · calc u ^ x ≤ u ^ B := Real.rpow_le_rpow_of_exponent_le h hB
      _ = u ^ b * u ^ (B - b) := by rw [← Real.rpow_add hu]; ring_nf
      _ ≤ u ^ b * (1 + u) ^ (B - b) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu.le (by linarith) (by linarith))
          (Real.rpow_pos_of_pos hu _).le

/-- Pointwise bound of the integrand of (7.2.16) from bounds on the parameters. -/
theorem norm_sigmaIntegrand_le {z α β : ℂ} {a b A B u : ℝ} (hu : 0 < u) (ha : a ≤ z.re)
    (hA : α.re - 1 ≤ A) (hb : b ≤ β.re - 1) (hB : β.re - 1 ≤ B) :
    ‖sigmaIntegrand z α β u‖ ≤ Real.exp (-a * u) * u ^ b * (1 + u) ^ (A + (B - b)) := by
  rw [norm_sigmaIntegrand hu]
  have e1 : Real.exp (-(z.re * u)) ≤ Real.exp (-a * u) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have e2 : (u + 1) ^ (α.re - 1) ≤ (1 + u) ^ A := by
    rw [add_comm u 1]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  have e3 := rpow_le_rpow_mul_one_add hu hb hB
  have p1 : 0 ≤ (u + 1) ^ (α.re - 1) := (Real.rpow_pos_of_pos (by linarith) _).le
  have p2 : 0 ≤ u ^ (β.re - 1) := (Real.rpow_pos_of_pos hu _).le
  have p3 : 0 ≤ Real.exp (-(z.re * u)) := (Real.exp_pos _).le
  have p4 : 0 ≤ (1 + u) ^ A := (Real.rpow_pos_of_pos (by linarith) _).le
  have p5 : 0 ≤ Real.exp (-a * u) := (Real.exp_pos _).le
  have p6 : 0 ≤ u ^ b := (Real.rpow_pos_of_pos hu _).le
  have : Real.exp (-a * u) * u ^ b * (1 + u) ^ (A + (B - b)) =
      Real.exp (-a * u) * (1 + u) ^ A * (u ^ b * (1 + u) ^ (B - b)) := by
    rw [Real.rpow_add (by linarith)]; ring
  rw [this]
  calc Real.exp (-(z.re * u)) * (u + 1) ^ (α.re - 1) * u ^ (β.re - 1)
      ≤ (Real.exp (-a * u) * (1 + u) ^ A) * (u ^ b * (1 + u) ^ (B - b)) := by
        refine mul_le_mul (mul_le_mul e1 e2 p1 p5) e3 p2 (by positivity)
    _ = _ := by ring

theorem one_add_norm_sigmaL_le {u : ℝ} (hu : 0 < u) :
    1 + ‖sigmaL u‖ ≤ 2 * ((1 + u) * (1 + |Real.log u|)) := by
  have h1 : ‖sigmaL u‖ ≤ u + |Real.log (u + 1)| + |Real.log u| := by
    unfold sigmaL
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
      calc u * ‖ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)‖ ≤ u * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_fst_le _ _ _) hu.le
        _ = u := mul_one _
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      calc |Real.log (u + 1)| * ‖(ContinuousLinearMap.fst ℂ ℂ ℂ).comp
              (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))‖ ≤ |Real.log (u + 1)| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            have := ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ
            have := ContinuousLinearMap.norm_snd_le ℂ ℂ (ℂ × ℂ)
            nlinarith [norm_nonneg (ContinuousLinearMap.fst ℂ ℂ ℂ),
              norm_nonneg (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))]
        _ = _ := mul_one _
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      calc |Real.log u| * ‖(ContinuousLinearMap.snd ℂ ℂ ℂ).comp
              (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))‖ ≤ |Real.log u| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            have := ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ
            have := ContinuousLinearMap.norm_snd_le ℂ ℂ (ℂ × ℂ)
            nlinarith [norm_nonneg (ContinuousLinearMap.snd ℂ ℂ ℂ),
              norm_nonneg (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))]
        _ = _ := mul_one _
  have h2 : |Real.log (u + 1)| ≤ u := by
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < u + 1)]
  have h3 := abs_nonneg (Real.log u)
  nlinarith [mul_nonneg hu.le h3]

theorem abs_re_sub_lt {w w' : ℂ} {r : ℝ} (h : dist w w' < r) : |w.re - w'.re| < r := by
  have := Complex.abs_re_le_norm (w - w')
  rw [Complex.sub_re] at this
  rw [dist_eq_norm] at h
  linarith

/-- Local integrable majorant for the integrand of (7.2.16) times `1 + ‖L_u‖`. -/
theorem sigma_local_bound {p₀ : ℂ × ℂ × ℂ} (hz : 0 < p₀.1.re) (hβ : 0 < p₀.2.2.re) :
    ∃ r > 0, ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ u ∈ Ioi (0 : ℝ),
      ∀ p ∈ Metric.ball p₀ r, ‖sigmaIntegrand p.1 p.2.1 p.2.2 u‖ * (1 + ‖sigmaL u‖) ≤ g u := by
  set r : ℝ := min 1 (min (p₀.1.re / 2) (p₀.2.2.re / 2)) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := min_le_left _ _
  have hr2 : r ≤ p₀.1.re / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ p₀.2.2.re / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set a : ℝ := p₀.1.re / 2 with ha
  set b : ℝ := p₀.2.2.re / 2 - 1 with hb
  set A : ℝ := p₀.2.1.re with hA
  set B : ℝ := max (p₀.2.2.re) b with hBdef
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb1 : -1 < b := by rw [hb]; linarith
  refine ⟨r, hr0, fun u ↦ 2 * (Real.exp (-a * u) * u ^ b * (1 + u) ^ (A + (B - b) + 1) *
      (1 + |Real.log u|)), ((integrableOn_majorant ha0 hb1 _).const_mul 2), ?_⟩
  intro u hu p hp
  have hu0 : 0 < u := hu
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Prod.dist_eq, max_lt_iff] at hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have q1 := abs_re_sub_lt hp1
  have q2 := abs_re_sub_lt hp2
  have q3 := abs_re_sub_lt hp3
  rw [abs_lt] at q1 q2 q3
  have hbound := norm_sigmaIntegrand_le (z := p.1) (α := p.2.1) (β := p.2.2) (a := a) (b := b)
    (A := A) (B := B) hu0 (by linarith) (by linarith) (by linarith)
    (by have := le_max_left p₀.2.2.re b; linarith)
  have hL := one_add_norm_sigmaL_le hu0
  have hn : 0 ≤ ‖sigmaIntegrand p.1 p.2.1 p.2.2 u‖ := norm_nonneg _
  have e1 : 0 ≤ Real.exp (-a * u) := (Real.exp_pos _).le
  have e2 : 0 ≤ u ^ b := (Real.rpow_pos_of_pos hu0 _).le
  have e3 : 0 ≤ (1 + u) ^ (A + (B - b)) := (Real.rpow_pos_of_pos (by linarith) _).le
  have e4 : 0 ≤ 1 + |Real.log u| := by positivity
  have e5 : (1 + u) ^ (A + (B - b) + 1) = (1 + u) ^ (A + (B - b)) * (1 + u) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  calc ‖sigmaIntegrand p.1 p.2.1 p.2.2 u‖ * (1 + ‖sigmaL u‖)
      ≤ (Real.exp (-a * u) * u ^ b * (1 + u) ^ (A + (B - b))) *
        (2 * ((1 + u) * (1 + |Real.log u|))) :=
        mul_le_mul hbound hL (by positivity) (by positivity)
    _ = _ := by beta_reduce; rw [e5]; ring

/-- **Miyake (7.2.18).** $\eta(y;\alpha,\beta;t) =\eta(y;\beta,\alpha;-t)$ (for the Lean integrals this holds
whether or not they converge). -/
@[kb "miyake1989" "(7.2.18), p. 276"]
theorem eta_swap (y : ℝ) (α β : ℂ) (t : ℝ) : eta y α β t = eta y β α (-t) := by
  unfold eta
  rw [abs_neg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ ↦ ?_)
  simp only [etaIntegrand]
  rw [show u + -t = u - t by ring, show u - -t = u + t by ring]
  ring

/-- **Miyake (7.2.19).** For $a > 0$, $\eta(ay;\alpha,\beta;t) = a^{1-\alpha-\beta}\eta(y;\alpha,\beta;at)$ (for the
Lean integrals this holds whether or not they converge). -/
@[kb "miyake1989" "(7.2.19), p. 276"]
theorem eta_mul (a : ℝ) (ha : 0 < a) (y : ℝ) (α β : ℂ) (t : ℝ) :
    eta (a * y) α β t = (a : ℂ) ^ (1 - α - β) * eta y α β (a * t) := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpt : ∀ x ∈ Ioi |t|, etaIntegrand y α β (a * t) (a * x) =
      (a : ℂ) ^ (α + β - 2) * etaIntegrand (a * y) α β t x := by
    intro x hx
    have hx' : |t| < x := hx
    have h1 : 0 < x + t := by linarith [neg_abs_le t]
    have h2 : 0 < x - t := by linarith [le_abs_self t]
    unfold etaIntegrand
    have e1 : a * x + a * t = a * (x + t) := by ring
    have e2 : a * x - a * t = a * (x - t) := by ring
    have e3 : cexp (-(y : ℂ) * ((a * x : ℝ) : ℂ)) = cexp (-((a * y : ℝ) : ℂ) * (x : ℂ)) := by
      congr 1; push_cast; ring
    have e4 : (a : ℂ) ^ (α + β - 2) = (a : ℂ) ^ (α - 1) * (a : ℂ) ^ (β - 1) := by
      rw [← Complex.cpow_add _ _ ha0]; ring_nf
    rw [e3, e1, e2, Complex.ofReal_mul a (x + t), Complex.ofReal_mul a (x - t),
      Complex.mul_cpow_ofReal_nonneg ha.le h1.le, Complex.mul_cpow_ofReal_nonneg ha.le h2.le, e4]
    ring
  have hmain := integral_comp_mul_left_Ioi (etaIntegrand y α β (a * t)) |t| ha
  have hL : ∫ x in Ioi |t|, etaIntegrand y α β (a * t) (a * x) =
      (a : ℂ) ^ (α + β - 2) * ∫ x in Ioi |t|, etaIntegrand (a * y) α β t x := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi hpt
  rw [hL, Complex.real_smul, Complex.ofReal_inv] at hmain
  unfold eta
  rw [abs_mul, abs_of_pos ha]
  have hP : (a : ℂ) ^ (α + β - 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp [ha0]
  have hA : (a : ℂ) ^ (α + β - 2) * (a : ℂ) ^ (1 - α - β) = (a : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ ha0, show α + β - 2 + (1 - α - β) = -1 by ring,
      Complex.cpow_neg_one]
  apply mul_left_cancel₀ hP
  rw [hmain, ← mul_assoc, hA]

/-- **Miyake, Lemma 7.2.1 (2).** The integral $\sigma(z;\alpha,\beta)$ converges uniformly on every compact
subset of $\mathbf H' \times \mathbb C \times \mathbf H'$: on such a set the integrand has one integrable
majorant on $(0, \infty)$. -/
@[kb "miyake1989" "Lemma 7.2.1 (2), p. 276"]
theorem sigma_uniform {T : Set (ℂ × ℂ × ℂ)} (hT : IsCompact T)
    (hTz : ∀ p ∈ T, 0 < p.1.re) (hTβ : ∀ p ∈ T, 0 < p.2.2.re) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ p ∈ T, ∀ u ∈ Ioi (0 : ℝ), ‖sigmaIntegrand p.1 p.2.1 p.2.2 u‖ ≤ g u := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, integrableOn_zero, by simp⟩
  have c1 : ContinuousOn (fun p : ℂ × ℂ × ℂ ↦ p.1.re) T :=
    (Complex.continuous_re.comp continuous_fst).continuousOn
  have c2 : ContinuousOn (fun p : ℂ × ℂ × ℂ ↦ p.2.1.re) T :=
    (Complex.continuous_re.comp (continuous_fst.comp continuous_snd)).continuousOn
  have c3 : ContinuousOn (fun p : ℂ × ℂ × ℂ ↦ p.2.2.re) T :=
    (Complex.continuous_re.comp (continuous_snd.comp continuous_snd)).continuousOn
  obtain ⟨p₁, hp₁, hmin1⟩ := hT.exists_isMinOn hne c1
  obtain ⟨p₂, hp₂, hmax2⟩ := hT.exists_isMaxOn hne c2
  obtain ⟨p₃, hp₃, hmin3⟩ := hT.exists_isMinOn hne c3
  obtain ⟨p₄, hp₄, hmax3⟩ := hT.exists_isMaxOn hne c3
  have ha0 : 0 < p₁.1.re := hTz p₁ hp₁
  have hb1 : -1 < p₃.2.2.re - 1 := by linarith [hTβ p₃ hp₃]
  set a : ℝ := p₁.1.re
  set b : ℝ := p₃.2.2.re - 1
  set A : ℝ := p₂.2.1.re - 1
  set B : ℝ := max (p₄.2.2.re - 1) b
  refine ⟨fun u ↦ Real.exp (-a * u) * u ^ b * (1 + u) ^ (A + (B - b)) * (1 + |Real.log u|),
    integrableOn_majorant ha0 hb1 _, ?_⟩
  intro p hp u hu
  have hu0 : 0 < u := hu
  have h1 : a ≤ p.1.re := isMinOn_iff.mp hmin1 p hp
  have h2 : p.2.1.re - 1 ≤ A := by linarith [isMaxOn_iff.mp hmax2 p hp]
  have h3 : b ≤ p.2.2.re - 1 := by linarith [isMinOn_iff.mp hmin3 p hp]
  have h4 : p.2.2.re - 1 ≤ B :=
    (by linarith [isMaxOn_iff.mp hmax3 p hp] : p.2.2.re - 1 ≤ p₄.2.2.re - 1).trans (le_max_left _ _)
  refine (norm_sigmaIntegrand_le hu0 h1 h2 h3 h4).trans ?_
  have e1 : 0 ≤ Real.exp (-a * u) := (Real.exp_pos _).le
  have e2 : 0 ≤ u ^ b := (Real.rpow_pos_of_pos hu0 _).le
  have e3 : 0 ≤ (1 + u) ^ (A + (B - b)) := (Real.rpow_pos_of_pos (by linarith) _).le
  have e4 : 0 ≤ Real.exp (-a * u) * u ^ b * (1 + u) ^ (A + (B - b)) := by positivity
  nlinarith [abs_nonneg (Real.log u)]

theorem continuousAt_ofReal_cpow_pos {u : ℝ} (hu : 0 < u) (s : ℂ) :
    ContinuousAt (fun x : ℝ ↦ ((x : ℝ) : ℂ) ^ s) u :=
  Complex.continuousAt_ofReal_cpow_const u s (Or.inr hu.ne')

theorem continuousOn_sigmaIntegrand (z α β : ℂ) :
    ContinuousOn (sigmaIntegrand z α β) (Ioi 0) := by
  intro u hu
  have hu0 : 0 < u := hu
  have h1 : ContinuousAt (fun x : ℝ ↦ ((x + 1 : ℝ) : ℂ) ^ (α - 1)) u :=
    (continuousAt_ofReal_cpow_pos (by linarith : (0 : ℝ) < u + 1) (α - 1)).comp
      (f := fun x : ℝ ↦ x + 1) (by fun_prop)
  have h2 := continuousAt_ofReal_cpow_pos hu0 (β - 1)
  have : ContinuousAt (sigmaIntegrand z α β) u := by
    unfold sigmaIntegrand
    fun_prop
  exact this.continuousWithinAt

/-- The integrand of (7.2.16) is integrable for $z, \beta \in \mathbf H'$. -/
theorem integrableOn_sigmaIntegrand {z α β : ℂ} (hz : 0 < z.re) (hβ : 0 < β.re) :
    IntegrableOn (sigmaIntegrand z α β) (Ioi 0) := by
  obtain ⟨g, hg, hb⟩ := sigma_uniform (T := {(z, α, β)}) isCompact_singleton
    (by simpa using hz) (by simpa using hβ)
  refine hg.mono' ((continuousOn_sigmaIntegrand z α β).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu ↦ ?_)
  exact hb (z, α, β) rfl u hu

theorem sigmaIntegrand_succ_beta {z α β : ℂ} {u : ℝ} (hu : 0 < u) :
    sigmaIntegrand z α (β + 1) u = (u : ℂ) * sigmaIntegrand z α β u := by
  have hne : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold sigmaIntegrand
  rw [show β + 1 - 1 = (β - 1) + 1 by ring, Complex.cpow_add _ _ hne, Complex.cpow_one]
  ring

theorem sigmaIntegrand_succ_alpha {z α β : ℂ} {u : ℝ} (hu : 0 < u) :
    sigmaIntegrand z (α + 1) β u = ((u + 1 : ℝ) : ℂ) * sigmaIntegrand z α β u := by
  have hne : ((u + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (u + 1) ≠ 0)
  unfold sigmaIntegrand
  rw [show α + 1 - 1 = (α - 1) + 1 by ring, Complex.cpow_add _ _ hne, Complex.cpow_one]
  ring

theorem continuousOn_sigmaL : ContinuousOn sigmaL (Ioi 0) := by
  intro u hu
  have hu0 : 0 < u := hu
  have h1 : ContinuousAt (fun x : ℝ ↦ Real.log (x + 1)) u :=
    ContinuousAt.log (by fun_prop) (by linarith)
  have h2 : ContinuousAt (fun x : ℝ ↦ Real.log x) u := Real.continuousAt_log hu0.ne'
  have : ContinuousAt sigmaL u := by
    unfold sigmaL
    fun_prop
  exact this.continuousWithinAt

theorem continuousOn_sigmaC : ContinuousOn sigmaC (Ioi 0) := by
  intro u hu
  have hu0 : 0 < u := hu
  have h1 : ContinuousAt (fun x : ℝ ↦ Real.log (x + 1)) u :=
    ContinuousAt.log (by fun_prop) (by linarith)
  have h2 : ContinuousAt (fun x : ℝ ↦ Real.log x) u := Real.continuousAt_log hu0.ne'
  have : ContinuousAt sigmaC u := by
    unfold sigmaC
    fun_prop
  exact this.continuousWithinAt

theorem sigmaIntegrand_eq' (p : ℂ × ℂ × ℂ) {u : ℝ} (hu : 0 < u) :
    sigmaIntegrand p.1 p.2.1 p.2.2 u = cexp (sigmaL u p + sigmaC u) :=
  sigmaIntegrand_eq hu

/-- Integrability transfers along the affine change of variable $u = t + 2ts$. -/
theorem integrableOn_Ioi_affine {G : ℝ → ℝ} (hG : IntegrableOn G (Ioi 0)) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ ↦ G ((u - t) / (2 * t))) (Ioi t) := by
  have himg : (fun s : ℝ ↦ t + 2 * t * s) '' Ioi 0 = Ioi t := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      have : (0 : ℝ) < s := hs
      show t < t + 2 * t * s
      nlinarith
    · intro hx
      have : t < x := hx
      refine ⟨(x - t) / (2 * t),
        show (0 : ℝ) < (x - t) / (2 * t) from div_pos (by linarith) (by positivity), ?_⟩
      show t + 2 * t * ((x - t) / (2 * t)) = x
      field_simp
      ring
  have hinj : InjOn (fun s : ℝ ↦ t + 2 * t * s) (Ioi 0) := by
    intro a _ b _ h
    simp only at h
    have : 2 * t * a = 2 * t * b := by linarith
    exact mul_left_cancel₀ (by positivity) this
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s : ℝ ↦ t + 2 * t * s) (2 * t)
      (Ioi 0) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul (2 * t)).const_add t).hasDerivWithinAt (s := Ioi 0)
    simpa using this
  rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  refine IntegrableOn.congr_fun (Integrable.const_mul hG |2 * t|) (fun s _ ↦ ?_)
    measurableSet_Ioi
  have : (t + 2 * t * s - t) / (2 * t) = s := by field_simp; ring
  simp only [smul_eq_mul, this]

/-- **Miyake, Lemma 7.2.1 (1).** For $y > 0$ and $t > 0$ the integral $\eta(y;\alpha,\beta;t)$ converges
uniformly on every compact subset of $\mathbb C \times \mathbf H'$: on such a set the integrand has one
integrable majorant on $(t, \infty)$. -/
@[kb "miyake1989" "Lemma 7.2.1 (1), p. 276"]
theorem eta_uniform {y t : ℝ} (hy : 0 < y) (ht : 0 < t) {T : Set (ℂ × ℂ)} (hT : IsCompact T)
    (hTβ : ∀ p ∈ T, 0 < p.2.re) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi t) ∧
      ∀ p ∈ T, ∀ u ∈ Ioi t, ‖etaIntegrand y p.1 p.2 t u‖ ≤ g u := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, integrableOn_zero, by simp⟩
  set c : ℝ := 2 * t * y with hc
  have hc0 : 0 < c := by positivity
  let φ : ℂ × ℂ → ℂ × ℂ × ℂ := fun p ↦ ((c : ℂ), p.1, p.2)
  have hφ : Continuous φ := by fun_prop
  obtain ⟨G, hG, hGb⟩ := sigma_uniform (T := φ '' T) (hT.image hφ)
    (by rintro _ ⟨p, _, rfl⟩; simpa [φ] using hc0)
    (by rintro _ ⟨p, hp, rfl⟩; exact hTβ p hp)
  have hK : ContinuousOn (fun p : ℂ × ℂ ↦ (2 * t) ^ (p.1.re + p.2.re - 2)) T := by
    refine Continuous.continuousOn ?_
    exact Continuous.rpow continuous_const (by fun_prop) (fun _ ↦ Or.inl (by positivity))
  obtain ⟨p₀, hp₀, hmax⟩ := hT.exists_isMaxOn hne hK
  set K : ℝ := (2 * t) ^ (p₀.1.re + p₀.2.re - 2)
  have hKnn : 0 ≤ K := by positivity
  refine ⟨fun u ↦ Real.exp (-(y * t)) * K * G ((u - t) / (2 * t)),
    ((integrableOn_Ioi_affine hG ht).const_mul (Real.exp (-(y * t)) * K)), ?_⟩
  intro p hp u hu
  have hut : t < u := hu
  set s : ℝ := (u - t) / (2 * t) with hs
  have hs0 : 0 < s := by rw [hs]; apply div_pos <;> linarith
  have hu1 : u = t + 2 * t * s := by rw [hs]; field_simp; ring
  have hGs := hGb (φ p) ⟨p, hp, rfl⟩ s hs0
  have hn : ‖etaIntegrand y p.1 p.2 t u‖ =
      Real.exp (-(y * t)) * (2 * t) ^ (p.1.re + p.2.re - 2) *
        ‖sigmaIntegrand (c : ℂ) p.1 p.2 s‖ := by
    have h1 : 0 < u + t := by linarith
    have h2 : 0 < u - t := by linarith
    have hu2 : u + t = 2 * t * (s + 1) := by rw [hu1]; ring
    have hu3 : u - t = 2 * t * s := by rw [hu1]; ring
    unfold etaIntegrand
    rw [norm_mul, norm_mul, Complex.norm_exp,
      Complex.norm_cpow_eq_rpow_re_of_pos h1, Complex.norm_cpow_eq_rpow_re_of_pos h2]
    show _ = _ * _ * ‖sigmaIntegrand (c : ℂ) p.1 p.2 s‖
    rw [norm_sigmaIntegrand hs0, hu2, hu3, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) hs0.le]
    have : (-(y : ℂ) * (u : ℂ)).re = -(y * t) - c * s := by
      rw [hu1]; simp [hc]; ring
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, this]
    have e : Real.exp (-(y * t) - c * s) = Real.exp (-(y * t)) * Real.exp (-(c * s)) := by
      rw [← Real.exp_add]; ring_nf
    have hrp : (2 * t) ^ (p.1.re + p.2.re - 2) =
        (2 * t) ^ (p.1.re - 1) * (2 * t) ^ (p.2.re - 1) := by
      rw [← Real.rpow_add (by positivity)]; ring_nf
    rw [e, hrp]
    ring
  rw [hn]
  have hKp : (2 * t) ^ (p.1.re + p.2.re - 2) ≤ K := isMaxOn_iff.mp hmax p hp
  have hnn : 0 ≤ ‖sigmaIntegrand (c : ℂ) p.1 p.2 s‖ := norm_nonneg _
  have hE : 0 ≤ Real.exp (-(y * t)) := (Real.exp_pos _).le
  have hP : 0 ≤ (2 * t) ^ (p.1.re + p.2.re - 2) := by positivity
  calc _ ≤ Real.exp (-(y * t)) * K * ‖sigmaIntegrand (c : ℂ) p.1 p.2 s‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKp hE) hnn
    _ ≤ _ := mul_le_mul_of_nonneg_left hGs (by positivity)

/-- The integrand of (7.2.17) is integrable for $y > 0$, $t > 0$ and $\beta \in \mathbf H'$. -/
theorem integrableOn_etaIntegrand {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (α : ℂ) {β : ℂ}
    (hβ : 0 < β.re) : IntegrableOn (etaIntegrand y α β t) (Ioi |t|) := by
  rw [abs_of_pos ht]
  obtain ⟨g, hg, hb⟩ := eta_uniform hy ht (T := {(α, β)}) isCompact_singleton
    (by simpa using hβ)
  have hcont : ContinuousOn (etaIntegrand y α β t) (Ioi t) := by
    intro u hu
    have hut : t < u := hu
    have h1 : ContinuousAt (fun x : ℝ ↦ ((x + t : ℝ) : ℂ) ^ (α - 1)) u :=
      (continuousAt_ofReal_cpow_pos (by linarith : (0 : ℝ) < u + t) (α - 1)).comp
        (f := fun x : ℝ ↦ x + t) (by fun_prop)
    have h2 : ContinuousAt (fun x : ℝ ↦ ((x - t : ℝ) : ℂ) ^ (β - 1)) u :=
      (continuousAt_ofReal_cpow_pos (by linarith : (0 : ℝ) < u - t) (β - 1)).comp
        (f := fun x : ℝ ↦ x - t) (by fun_prop)
    have : ContinuousAt (etaIntegrand y α β t) u := by
      unfold etaIntegrand
      fun_prop
    exact this.continuousWithinAt
  refine hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu ↦ ?_)
  exact hb (α, β) rfl u hu

theorem aesm_sigmaL : AEStronglyMeasurable sigmaL (volume.restrict (Ioi (0 : ℝ))) :=
  continuousOn_sigmaL.aestronglyMeasurable measurableSet_Ioi

theorem aesm_sigmaC : AEStronglyMeasurable sigmaC (volume.restrict (Ioi (0 : ℝ))) :=
  continuousOn_sigmaC.aestronglyMeasurable measurableSet_Ioi

/-- The Fréchet derivative of $\sigma$ at a point of $\mathbf H' \times \mathbb C \times \mathbf H'$. -/
theorem hasFDerivAt_sigma {p₀ : ℂ × ℂ × ℂ} (hz : 0 < p₀.1.re) (hβ : 0 < p₀.2.2.re) :
    HasFDerivAt (fun p : ℂ × ℂ × ℂ ↦ sigma p.1 p.2.1 p.2.2)
      (∫ u in Ioi (0 : ℝ), cexp (sigmaL u p₀ + sigmaC u) • sigmaL u) p₀ := by
  obtain ⟨r, hr, g, hg, hb⟩ := sigma_local_bound hz hβ
  have key := hasFDerivAt_integral_cexp (μ := volume.restrict (Ioi (0 : ℝ))) sigmaL sigmaC
    aesm_sigmaL aesm_sigmaC hr hg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu p hp
      rw [← sigmaIntegrand_eq' p hu]
      exact hb u hu p hp)
  have hfun : (fun p : ℂ × ℂ × ℂ ↦ sigma p.1 p.2.1 p.2.2) =
      fun p ↦ ∫ u in Ioi (0 : ℝ), cexp (sigmaL u p + sigmaC u) := by
    funext p
    exact setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ sigmaIntegrand_eq' p hu)
  rw [hfun]
  exact key

/-- $\sigma(z;\alpha,\beta)$ is holomorphic (jointly in $(z, \alpha, \beta)$) on $\mathbf H' \times \mathbb C
\times \mathbf H'$ (Miyake, p. 279, after (7.2.31)). -/
@[kb "miyake1989" "Lemma 7.2.1 (2) and (7.2.31), p. 279"]
theorem differentiableOn_sigma :
    DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ ↦ sigma p.1 p.2.1 p.2.2)
      {p | 0 < p.1.re ∧ 0 < p.2.2.re} := fun _ hp ↦
  (hasFDerivAt_sigma hp.1 hp.2).differentiableAt.differentiableWithinAt

/-- **Miyake, Lemma 7.2.1 (3).** For $y > 0$ and $\beta \in \mathbf H'$,
$\eta(y;\alpha,\beta;1) = e^{-y}2^{\alpha+\beta-1}\sigma(2y;\alpha,\beta)$. -/
@[kb "miyake1989" "Lemma 7.2.1 (3), p. 277"]
theorem eta_one {y : ℝ} (hy : 0 < y) (α β : ℂ) :
    eta y α β 1 = cexp (-(y : ℂ)) * (2 : ℂ) ^ (α + β - 1) * sigma (2 * y) α β := by
  have himg : (fun s : ℝ ↦ 1 + 2 * s) '' Ioi 0 = Ioi 1 := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      have : (0 : ℝ) < s := hs
      show 1 < 1 + 2 * s
      linarith
    · intro hx
      have : (1 : ℝ) < x := hx
      exact ⟨(x - 1) / 2, by show (0 : ℝ) < (x - 1) / 2; linarith, by ring⟩
  have hinj : InjOn (fun s : ℝ ↦ 1 + 2 * s) (Ioi 0) := by
    intro a _ b _ h
    simp only at h
    linarith
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun s : ℝ ↦ 1 + 2 * s) 2 (Ioi 0) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul 2).const_add 1).hasDerivWithinAt (s := Ioi 0)
    simpa using this
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (etaIntegrand y α β 1)
  rw [himg] at h
  have h2 : (2 : ℂ) ^ (α + β - 1) = (2 : ℂ) ^ (α - 1) * (2 : ℂ) ^ (β - 1) * 2 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    nth_rewrite 3 [← Complex.cpow_one 2]
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    ring_nf
  unfold eta sigma
  rw [abs_one, h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs ↦ ?_)
  have hs' : (0 : ℝ) < s := hs
  simp only [sigmaIntegrand, etaIntegrand]
  have e1 : (1 + 2 * s + 1 : ℝ) = 2 * (s + 1) := by ring
  have e2 : (1 + 2 * s - 1 : ℝ) = 2 * s := by ring
  have e3 : cexp (-(y : ℂ) * ((1 + 2 * s : ℝ) : ℂ)) =
      cexp (-(y : ℂ)) * cexp (-(2 * (y : ℂ)) * (s : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e3, e1, e2, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by norm_num) (by linarith),
    Complex.mul_cpow_ofReal_nonneg (by norm_num) hs'.le, h2]
  simp only [abs_two, Complex.real_smul]
  push_cast
  ring

theorem eta_eq_sigma {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (α β : ℂ) :
    eta y α β t = (t : ℂ) ^ (α + β - 1) *
      (cexp (-((t * y : ℝ) : ℂ)) * (2 : ℂ) ^ (α + β - 1) * sigma (2 * ((t * y : ℝ) : ℂ)) α β) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have h := eta_mul t ht y α β 1
  rw [mul_one] at h
  rw [← eta_one (mul_pos ht hy), h, ← mul_assoc, ← Complex.cpow_add _ _ ht0,
    show α + β - 1 + (1 - α - β) = 0 by ring, Complex.cpow_zero, one_mul]

/-- For $y > 0$, $t > 0$, $\eta(y;\alpha,\beta;t)$ is holomorphic in $(\alpha, \beta)$ on
$\mathbb C \times \mathbf H'$ (Miyake, p. 279, after (7.2.28)). -/
@[kb "miyake1989" "Lemma 7.2.1 (1), p. 276"]
theorem differentiableOn_eta {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ eta y p.1 p.2 t) {p | 0 < p.2.re} := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hcongr : (fun p : ℂ × ℂ ↦ eta y p.1 p.2 t) = fun p ↦ (t : ℂ) ^ (p.1 + p.2 - 1) *
      (cexp (-((t * y : ℝ) : ℂ)) * (2 : ℂ) ^ (p.1 + p.2 - 1) *
        sigma (2 * ((t * y : ℝ) : ℂ)) p.1 p.2) := by
    funext p; exact eta_eq_sigma hy ht p.1 p.2
  rw [hcongr]
  intro p hp
  have hp' : 0 < p.2.re := hp
  have hσ : DifferentiableAt ℂ (fun q : ℂ × ℂ ↦ sigma (2 * ((t * y : ℝ) : ℂ)) q.1 q.2) p := by
    have hz : 0 < (((2 * ((t * y : ℝ) : ℂ)), p.1, p.2) : ℂ × ℂ × ℂ).1.re := by
      simp; positivity
    exact ((hasFDerivAt_sigma (p₀ := ((2 * ((t * y : ℝ) : ℂ)), p.1, p.2)) hz hp').differentiableAt.comp
      p (by fun_prop : DifferentiableAt ℂ
        (fun q : ℂ × ℂ ↦ ((2 * ((t * y : ℝ) : ℂ)), q.1, q.2)) p))
  have hs : DifferentiableAt ℂ (fun q : ℂ × ℂ ↦ q.1 + q.2 - 1) p := by fun_prop
  have h1 : DifferentiableAt ℂ (fun q : ℂ × ℂ ↦ (t : ℂ) ^ (q.1 + q.2 - 1)) p :=
    hs.const_cpow (Or.inl ht0)
  have h2 : DifferentiableAt ℂ (fun q : ℂ × ℂ ↦ (2 : ℂ) ^ (q.1 + q.2 - 1)) p :=
    hs.const_cpow (Or.inl (by norm_num))
  exact (h1.mul ((h2.const_mul _).mul hσ)).differentiableWithinAt

/-- $\partial_z\sigma(z;\alpha,\beta) =-\sigma(z;\alpha,\beta+1)$ on $\mathbf H' \times \mathbb C \times \mathbf H'$
(differentiation under the integral sign, used in (7.2.35)). -/
theorem hasDerivAt_sigma_z {z α β : ℂ} (hz : 0 < z.re) (hβ : 0 < β.re) :
    HasDerivAt (fun w ↦ sigma w α β) (-sigma z α (β + 1)) z := by
  have hF := hasFDerivAt_sigma (p₀ := (z, α, β)) hz hβ
  have hg : HasDerivAt (fun w : ℂ ↦ (w, α, β)) ((1 : ℂ), (0 : ℂ), (0 : ℂ)) z :=
    (hasDerivAt_id z).prodMk ((hasDerivAt_const z α).prodMk (hasDerivAt_const z β))
  refine (hF.comp_hasDerivAt z hg).congr_deriv ?_
  -- integrability of the derivative integrand
  obtain ⟨r, hr, g, hg', hb⟩ := sigma_local_bound (p₀ := (z, α, β)) hz hβ
  have hmeas : AEStronglyMeasurable (fun u : ℝ ↦ cexp (sigmaL u (z, α, β) + sigmaC u) • sigmaL u)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((Complex.continuous_exp.comp_aestronglyMeasurable
      ((aesm_sigmaL.apply_continuousLinearMap (z, α, β)).add aesm_sigmaC))).smul aesm_sigmaL
  have hint : Integrable (fun u : ℝ ↦ cexp (sigmaL u (z, α, β) + sigmaC u) • sigmaL u)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine hg'.mono' hmeas ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu ↦ ?_))
    have := hb u hu (z, α, β) (Metric.mem_ball_self hr)
    rw [sigmaIntegrand_eq hu, norm_smul] at *
    simp only at this
    refine le_trans ?_ this
    nlinarith [norm_nonneg (cexp (sigmaL u (z, α, β) + sigmaC u)), norm_nonneg (sigmaL u)]
  rw [ContinuousLinearMap.integral_apply hint, sigma, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ ?_)
  simp only [smul_apply, smul_eq_mul]
  rw [← sigmaIntegrand_eq hu, sigmaIntegrand_succ_beta hu, sigmaL_apply]
  simp
  ring

theorem hasDerivAt_ofReal_cpow_pos {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun u : ℝ ↦ ((u : ℝ) : ℂ) ^ s) (s * ((x : ℝ) : ℂ) ^ (s - 1)) x := by
  by_cases hs : s = 0
  · subst hs
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hs

/-- The derivative in $u$ of the integrand of (7.2.16). -/
theorem hasDerivAt_sigmaIntegrand (z α β : ℂ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (sigmaIntegrand z α β)
      (-z * sigmaIntegrand z α β u + (α - 1) * sigmaIntegrand z (α - 1) β u
        + (β - 1) * sigmaIntegrand z α (β - 1) u) u := by
  have hx : HasDerivAt (fun x : ℝ ↦ ((x : ℝ) : ℂ)) 1 u := by
    simpa using (hasDerivAt_id (u : ℂ)).comp_ofReal
  have h1 : HasDerivAt (fun x : ℝ ↦ cexp (-z * (x : ℂ))) (cexp (-z * (u : ℂ)) * (-z * 1)) u :=
    (hx.const_mul (-z)).cexp
  have hh : HasDerivAt (fun x : ℝ ↦ x + 1) 1 u := (hasDerivAt_id u).add_const 1
  have h2 := HasDerivAt.scomp u
    (hasDerivAt_ofReal_cpow_pos (by linarith : (0 : ℝ) < u + 1) (α - 1)) hh
  have h3 := hasDerivAt_ofReal_cpow_pos hu (β - 1)
  have key := (h1.mul h2).mul h3
  have hfun : sigmaIntegrand z α β = fun x : ℝ ↦
      cexp (-z * (x : ℂ)) * ((x + 1 : ℝ) : ℂ) ^ (α - 1) * ((x : ℝ) : ℂ) ^ (β - 1) := rfl
  rw [hfun]
  refine key.congr_deriv ?_
  simp only [sigmaIntegrand, one_smul, Pi.mul_apply, Function.comp_apply]
  ring

theorem tendsto_sigmaIntegrand_atTop {z : ℂ} (hz : 0 < z.re) (α β : ℂ) :
    Tendsto (sigmaIntegrand z α β) atTop (𝓝 0) := by
  set p : ℝ := α.re - 1
  set q : ℝ := β.re - 1
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (|p| + |q|) z.re hz).const_mul
    ((2 : ℝ) ^ |p|)
  rw [mul_zero] at hlim
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu1
  have hu0 : 0 < u := by linarith
  rw [norm_sigmaIntegrand hu0]
  have e1 : (u + 1) ^ p ≤ (2 * u) ^ |p| := by
    calc (u + 1) ^ p ≤ (u + 1) ^ |p| :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (le_abs_self p)
      _ ≤ (2 * u) ^ |p| := Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg p)
  have e2 : u ^ q ≤ u ^ |q| := Real.rpow_le_rpow_of_exponent_le hu1 (le_abs_self q)
  have e3 : (2 * u) ^ |p| = 2 ^ |p| * u ^ |p| := Real.mul_rpow (by norm_num) hu0.le
  have e4 : u ^ (|p| + |q|) = u ^ |p| * u ^ |q| := Real.rpow_add hu0 _ _
  have p1 : 0 ≤ (u + 1) ^ p := (Real.rpow_pos_of_pos (by linarith) _).le
  have p2 : 0 ≤ Real.exp (-(z.re * u)) := (Real.exp_pos _).le
  have e5 : Real.exp (-(z.re * u)) = Real.exp (-z.re * u) := by ring_nf
  calc Real.exp (-(z.re * u)) * (u + 1) ^ p * u ^ q
      ≤ Real.exp (-(z.re * u)) * (2 ^ |p| * u ^ |p|) * u ^ |q| := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (e1.trans_eq e3) p2) e2
          (Real.rpow_pos_of_pos hu0 _).le (by positivity)
    _ = 2 ^ |p| * (u ^ (|p| + |q|) * Real.exp (-z.re * u)) := by rw [e4, e5]; ring

/-- $\sigma(z;\alpha,\beta) + \sigma(z;\alpha,\beta+1) =\sigma(z;\alpha+1,\beta)$ (linearity of the integral,
$(u+1)^{\alpha-1}(1 + u) = (u+1)^{\alpha}$). -/
theorem sigma_add_sigma_succ {z α β : ℂ} (hz : 0 < z.re) (hβ : 0 < β.re) :
    sigma z α β + sigma z α (β + 1) = sigma z (α + 1) β := by
  have hβ' : 0 < (β + 1).re := by simp; linarith
  rw [sigma, sigma, sigma, ← integral_add (integrableOn_sigmaIntegrand hz hβ)
    (integrableOn_sigmaIntegrand hz hβ')]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ ?_)
  rw [sigmaIntegrand_succ_beta hu, sigmaIntegrand_succ_alpha hu]
  push_cast
  ring

/-- **Miyake (7.2.38)**, for $z \in \mathbf H'$ (the book takes $z = y > 0$): integration by parts in (7.2.16)
gives $\sigma(z;\alpha,\beta+1) = z^{-1}(\alpha-1)\sigma(z;\alpha-1,\beta+1) + z^{-1}\beta\,\sigma(z;\alpha,\beta)$
for $\beta \in \mathbf H'$. -/
@[kb "miyake1989" "(7.2.38), p. 282"]
theorem sigma_succ {z α β : ℂ} (hz : 0 < z.re) (hβ : 0 < β.re) :
    sigma z α (β + 1) = z⁻¹ * (α - 1) * sigma z (α - 1) (β + 1) + z⁻¹ * β * sigma z α β := by
  have hβ' : 0 < (β + 1).re := by simp; linarith
  have hint1 := integrableOn_sigmaIntegrand (α := α) hz hβ'
  have hint2 := integrableOn_sigmaIntegrand (α := α - 1) hz hβ'
  have hint3 := integrableOn_sigmaIntegrand (α := α) hz hβ
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz
  have hcont : ContinuousWithinAt (sigmaIntegrand z α (β + 1)) (Ici 0) 0 := by
    have h1 : ContinuousAt (fun x : ℝ ↦ ((x + 1 : ℝ) : ℂ) ^ (α - 1)) 0 :=
      (continuousAt_ofReal_cpow_pos (by norm_num : (0 : ℝ) < 0 + 1) (α - 1)).comp
        (f := fun x : ℝ ↦ x + 1) (by fun_prop)
    have h2 : ContinuousAt (fun x : ℝ ↦ ((x : ℝ) : ℂ) ^ (β + 1 - 1)) 0 :=
      Complex.continuousAt_ofReal_cpow_const 0 _ (Or.inl (by simpa using hβ))
    have : ContinuousAt (sigmaIntegrand z α (β + 1)) 0 := by
      unfold sigmaIntegrand
      fun_prop
    exact this.continuousWithinAt
  have hf0 : sigmaIntegrand z α (β + 1) 0 = 0 := by
    have : β ≠ 0 := by
      intro h
      rw [h] at hβ; simp at hβ
    simp [sigmaIntegrand, this]
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (m := 0) hcont
    (f' := fun u ↦ -z * sigmaIntegrand z α (β + 1) u
      + (α - 1) * sigmaIntegrand z (α - 1) (β + 1) u + β * sigmaIntegrand z α β u)
    (fun x hx ↦ by
      simpa only [add_sub_cancel_right] using hasDerivAt_sigmaIntegrand z α (β + 1) hx)
    (((hint1.const_mul (-z)).add (hint2.const_mul (α - 1))).add (hint3.const_mul β))
    (tendsto_sigmaIntegrand_atTop hz α (β + 1))
  rw [hf0, sub_zero, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul] at key
  · have e : z * sigma z α (β + 1) = (α - 1) * sigma z (α - 1) (β + 1) + β * sigma z α β := by
      simp only [sigma]; linear_combination -key
    calc sigma z α (β + 1) = z⁻¹ * (z * sigma z α (β + 1)) := by field_simp
      _ = _ := by rw [e]; ring
  · exact hint1.const_mul (-z)
  · exact hint2.const_mul (α - 1)
  · exact (hint1.const_mul (-z)).add (hint2.const_mul (α - 1))
  · exact hint3.const_mul β

/-- The boundary case $\beta = 0$ of (7.2.38): integrating by parts in $\sigma(z;\alpha,1)$,
$z\,\sigma(z;\alpha,1) = 1 + (\alpha - 1)\sigma(z;\alpha-1,1)$ for $z \in \mathbf H'$ (used for Lemma 7.2.6). -/
theorem mul_sigma_one {z : ℂ} (hz : 0 < z.re) (α : ℂ) :
    z * sigma z α 1 = 1 + (α - 1) * sigma z (α - 1) 1 := by
  have hβ : 0 < (1 : ℂ).re := by simp
  have hint1 := integrableOn_sigmaIntegrand (α := α) hz hβ
  have hint2 := integrableOn_sigmaIntegrand (α := α - 1) hz hβ
  have hfun : sigmaIntegrand z α 1 =
      fun u : ℝ ↦ cexp (-z * (u : ℂ)) * ((u + 1 : ℝ) : ℂ) ^ (α - 1) := by
    funext u; simp [sigmaIntegrand]
  have hcont : ContinuousWithinAt (sigmaIntegrand z α 1) (Ici 0) 0 := by
    have h1 : ContinuousAt (fun x : ℝ ↦ ((x + 1 : ℝ) : ℂ) ^ (α - 1)) 0 :=
      (continuousAt_ofReal_cpow_pos (by norm_num : (0 : ℝ) < 0 + 1) (α - 1)).comp
        (f := fun x : ℝ ↦ x + 1) (by fun_prop)
    have : ContinuousAt (sigmaIntegrand z α 1) 0 := by
      rw [hfun]
      fun_prop
    exact this.continuousWithinAt
  have hf0 : sigmaIntegrand z α 1 0 = 1 := by simp [sigmaIntegrand]
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (m := 0) hcont
    (f' := fun u ↦ -z * sigmaIntegrand z α 1 u + (α - 1) * sigmaIntegrand z (α - 1) 1 u)
    (fun x hx ↦ by
      simpa only [sub_self, zero_mul, add_zero] using hasDerivAt_sigmaIntegrand z α 1 hx)
    ((hint1.const_mul (-z)).add (hint2.const_mul (α - 1)))
    (tendsto_sigmaIntegrand_atTop hz α 1)
  rw [hf0, integral_add (hint1.const_mul (-z)) (hint2.const_mul (α - 1)), integral_const_mul,
    integral_const_mul] at key
  simp only [sigma]
  linear_combination -key

end ModularFormsKB.Miyake.HeckeTrick
