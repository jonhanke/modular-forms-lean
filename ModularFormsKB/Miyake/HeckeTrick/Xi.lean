import ModularFormsKB.Miyake.HeckeTrick.Omega
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Miyake §7.2: the Fourier transform $\xi(y;\alpha,\beta;t)$ (Lemmas 7.2.2, 7.2.3, Theorem 7.2.5)

Miyake, *Modular Forms*, §7.2, pp. 275–281. For $y > 0$ put
$\phi(y;\alpha,\beta;x) = (x+iy)^{-\alpha}(x-iy)^{-\beta}$ (7.2.9) and, for $\operatorname{Re}(\alpha+\beta) > 1$,
$$\xi(y;\alpha,\beta;t) = \int_{\mathbb R}\phi(y;\alpha,\beta;x)e^{-2\pi i t x}\,dx \qquad (7.2.11),$$
the Fourier transform of $\phi$. Powers are principal ($-\pi < \arg \le \pi$); $x \pm iy$ never meets the cut.
$i^{w} = e^{\pi i w/2}$ is the principal power `I ^ w`.

Theorem 7.2.5 expresses $\xi$ through $\omega$ (`omega`); the right-hand side, `xiCont`, is the continuation of
$\xi$ to $\mathbb C \times \mathbb C$: holomorphic for $t \ne 0$, and $\Gamma(\alpha+\beta-1)$ times a holomorphic
function for $t = 0$ ("meromorphic on $\mathbb C \times \mathbb C$" in the book).
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real FourierTransform

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

/-- **Miyake (7.2.9).** $\phi(y;\alpha,\beta;x) = (x+iy)^{-\alpha}(x-iy)^{-\beta}$. -/
@[kb "miyake1989" "(7.2.9), p. 275"]
def phi (y : ℝ) (α β : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) + y * I) ^ (-α) * ((x : ℂ) - y * I) ^ (-β)

/-- **Miyake (7.2.11).** $\xi(y;\alpha,\beta;t) = \int_{\mathbb R}\phi(y;\alpha,\beta;x)e^{-2\pi i t x}\,dx$
(convergent for $\operatorname{Re}(\alpha+\beta) > 1$). -/
@[kb "miyake1989" "(7.2.11), p. 275"]
def xi (y : ℝ) (α β : ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, phi y α β x * cexp (-2 * π * I * t * x)

/-- Identity theorem on the right half plane: holomorphic functions agreeing on the positive reals
agree on $\operatorname{Re} z > 0$. -/
theorem eqOn_halfPlane_of_eq_real {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {w : ℂ | 0 < w.re}) (hg : DifferentiableOn ℂ g {w : ℂ | 0 < w.re})
    (h : ∀ x : ℝ, 0 < x → f x = g x) {z : ℂ} (hz : 0 < z.re) : f z = g z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 1) (by simp) ?_ hz
  rw [Filter.frequently_iff]
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhdsWithin_iff.mp hV
  refine ⟨((1 + ε / 2 : ℝ) : ℂ), hεV ⟨?_, ?_⟩, h _ (by positivity)⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have : (((1 + ε / 2 : ℝ) : ℂ) - 1) = ((ε / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  · intro h
    have h' : (((1 + ε / 2 : ℝ)) : ℂ) = 1 := h
    have := congrArg Complex.re h'
    simp at this
    linarith

/-- The Gamma integral with complex rate: $\sigma(z;1,\beta) = \int_0^\infty e^{-zu}u^{\beta-1}du =
z^{-\beta}\Gamma(\beta)$ for $\operatorname{Re} z, \operatorname{Re}\beta > 0$. -/
theorem sigma_one {z β : ℂ} (hz : 0 < z.re) (hβ : 0 < β.re) :
    sigma z 1 β = z ^ (-β) * Gamma β := by
  have hd1 : DifferentiableOn ℂ (fun w : ℂ ↦ sigma w 1 β) {w : ℂ | 0 < w.re} := by
    intro w hw
    have := (hasFDerivAt_sigma (p₀ := (w, 1, β)) hw hβ).differentiableAt.comp w
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ ↦ ((w, 1, β) : ℂ × ℂ × ℂ)) w)
    exact this.differentiableWithinAt
  have hd2 : DifferentiableOn ℂ (fun w : ℂ ↦ w ^ (-β) * Gamma β) {w : ℂ | 0 < w.re} := by
    intro w hw
    have hs : w ∈ Complex.slitPlane := Or.inl hw
    exact ((differentiableAt_id.cpow (differentiableAt_const _) hs).mul
      (differentiableAt_const _)).differentiableWithinAt
  refine eqOn_halfPlane_of_eq_real hd1 hd2 (fun x hx ↦ ?_) hz
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hβ hx
  have e : ((1 / (x : ℂ))) ^ β = (x : ℂ) ^ (-β) := by
    rw [one_div, Complex.cpow_neg, Complex.inv_cpow _ _
      (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne)]
  rw [e] at h
  rw [← h, sigma]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ ?_)
  simp only [sigmaIntegrand]
  simp [mul_comm]

/-- $\xi(y;\alpha,\beta;\cdot)$ is Mathlib's Fourier transform of $\phi(y;\alpha,\beta;\cdot)$. -/
theorem xi_eq_fourier (y : ℝ) (α β : ℂ) (t : ℝ) : xi y α β t = 𝓕 (phi y α β) t := by
  rw [Real.fourier_real_eq_integral_exp_smul, xi]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- $|w^{-a}| \le e^{\pi|\operatorname{Im} a|}|w|^{-\operatorname{Re} a}$ for $w \ne 0$. -/
theorem norm_cpow_neg_le {w : ℂ} (hw : w ≠ 0) (a : ℂ) :
    ‖w ^ (-a)‖ ≤ Real.exp (π * |a.im|) * ‖w‖ ^ (-a.re) := by
  rw [Complex.norm_cpow_of_ne_zero hw]
  simp only [Complex.neg_re, Complex.neg_im]
  have h1 : |Complex.arg w * a.im| ≤ π * |a.im| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi w) (abs_nonneg _)
  have h2 : ‖w‖ ^ (-a.re) / Real.exp (Complex.arg w * -a.im) =
      Real.exp (Complex.arg w * a.im) * ‖w‖ ^ (-a.re) := by
    rw [show Complex.arg w * -a.im = -(Complex.arg w * a.im) by ring, Real.exp_neg]
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ((le_abs_self _).trans h1))
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem ofReal_add_mul_I_ne_zero {y : ℝ} (hy : 0 < y) (x : ℝ) : ((x : ℂ) + y * I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

theorem ofReal_sub_mul_I_ne_zero {y : ℝ} (hy : 0 < y) (x : ℝ) : ((x : ℂ) - y * I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

/-- $|\phi(y;\alpha,\beta;x)| \le e^{\pi(|\operatorname{Im}\alpha| + |\operatorname{Im}\beta|)}
(x^2+y^2)^{-\operatorname{Re}(\alpha+\beta)/2}$. -/
theorem norm_phi_le {y : ℝ} (hy : 0 < y) (α β : ℂ) (x : ℝ) :
    ‖phi y α β x‖ ≤ Real.exp (π * (|α.im| + |β.im|)) * (x ^ 2 + y ^ 2) ^ (-(α + β).re / 2) := by
  have hn1 : ‖(x : ℂ) + y * I‖ = Real.sqrt (x ^ 2 + y ^ 2) := Complex.norm_add_mul_I x y
  have hn2 : ‖(x : ℂ) - y * I‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.norm_add_mul_I]
    simp
  have hS : 0 < x ^ 2 + y ^ 2 := by positivity
  unfold phi
  rw [norm_mul]
  calc _ ≤ (Real.exp (π * |α.im|) * ‖(x : ℂ) + y * I‖ ^ (-α.re)) *
        (Real.exp (π * |β.im|) * ‖(x : ℂ) - y * I‖ ^ (-β.re)) :=
        mul_le_mul (norm_cpow_neg_le (ofReal_add_mul_I_ne_zero hy x) α)
          (norm_cpow_neg_le (ofReal_sub_mul_I_ne_zero hy x) β) (norm_nonneg _) (by positivity)
    _ = Real.exp (π * (|α.im| + |β.im|)) * (x ^ 2 + y ^ 2) ^ (-(α + β).re / 2) := by
        rw [hn1, hn2, Real.sqrt_eq_rpow, ← Real.rpow_mul hS.le, ← Real.rpow_mul hS.le,
          mul_add, Real.exp_add]
        have : (x ^ 2 + y ^ 2) ^ (1 / 2 * -α.re) * (x ^ 2 + y ^ 2) ^ (1 / 2 * -β.re) =
            (x ^ 2 + y ^ 2) ^ (-(α + β).re / 2) := by
          rw [← Real.rpow_add hS]; congr 1; simp; ring
        rw [← this]; ring

theorem continuous_phi {y : ℝ} (hy : 0 < y) (α β : ℂ) : Continuous (phi y α β) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  unfold phi
  have h1 : (x : ℂ) + y * I ∈ Complex.slitPlane :=
    Or.inr (by simp; exact hy.ne')
  have h2 : (x : ℂ) - y * I ∈ Complex.slitPlane :=
    Or.inr (by simp; exact hy.ne')
  have c1 : ContinuousAt (fun x : ℝ ↦ (x : ℂ) + y * I) x := by fun_prop
  have c2 : ContinuousAt (fun x : ℝ ↦ (x : ℂ) - y * I) x := by fun_prop
  have k1 : ContinuousAt (fun _ : ℝ ↦ -α) x := continuousAt_const
  have k2 : ContinuousAt (fun _ : ℝ ↦ -β) x := continuousAt_const
  exact (c1.cpow k1 h1).mul (c2.cpow k2 h2)

/-- $c(1+x^2) \le x^2 + y^2$ for $c = \min(1,y^2)$. -/
theorem min_mul_le {y : ℝ} (x : ℝ) : min 1 (y ^ 2) * (1 + x ^ 2) ≤ x ^ 2 + y ^ 2 := by
  have h1 := min_le_left 1 (y ^ 2)
  have h2 := min_le_right 1 (y ^ 2)
  have h3 : 0 ≤ min 1 (y ^ 2) := le_min zero_le_one (sq_nonneg _)
  nlinarith [sq_nonneg x]

/-- $\phi(y;\alpha,\beta;\cdot)$ is integrable on $\mathbb R$ for $\operatorname{Re}(\alpha+\beta) > 1$. -/
theorem integrable_phi {y : ℝ} (hy : 0 < y) {α β : ℂ} (h : 1 < (α + β).re) :
    Integrable (phi y α β) := by
  set c : ℝ := min 1 (y ^ 2) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  have hint : Integrable (fun x : ℝ ↦ (1 + ‖x‖ ^ 2) ^ (-(α + β).re / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using h)
  refine ((hint.const_mul (Real.exp (π * (|α.im| + |β.im|)) * c ^ (-(α + β).re / 2))).mono'
    (continuous_phi hy α β).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_))
  refine (norm_phi_le hy α β x).trans ?_
  have hS : c * (1 + x ^ 2) ≤ x ^ 2 + y ^ 2 := min_mul_le x
  have h1 : (x ^ 2 + y ^ 2) ^ (-(α + β).re / 2) ≤ (c * (1 + x ^ 2)) ^ (-(α + β).re / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hS (by linarith)
  rw [Real.mul_rpow hc0.le (by positivity)] at h1
  simp only [Real.norm_eq_abs, sq_abs]
  calc _ ≤ Real.exp (π * (|α.im| + |β.im|)) * (c ^ (-(α + β).re / 2) * (1 + x ^ 2) ^ (-(α + β).re / 2)) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := by ring

/-- Helper: $S^{-a} \le c^{-A}(1+x^2)^{-a_0}$ for $S = x^2+y^2$, $0 \le a_0 \le a \le A$. -/
theorem S_pow_le {y : ℝ} (hy : 0 < y) (x : ℝ) {a₀ a A : ℝ} (h0 : 0 ≤ a₀) (h1 : a₀ ≤ a)
    (h2 : a ≤ A) :
    (x ^ 2 + y ^ 2) ^ (-a) ≤ (min 1 (y ^ 2)) ^ (-A) * (1 + x ^ 2) ^ (-a₀) := by
  set c : ℝ := min 1 (y ^ 2) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hS : c * (1 + x ^ 2) ≤ x ^ 2 + y ^ 2 := min_mul_le x
  have hW : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have h3 : (x ^ 2 + y ^ 2) ^ (-a) ≤ (c * (1 + x ^ 2)) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hS (by linarith)
  rw [Real.mul_rpow hc0.le (by positivity)] at h3
  have h4 : c ^ (-a) ≤ c ^ (-A) := Real.rpow_le_rpow_of_exponent_ge hc0 hc1 (by linarith)
  have h5 : (1 + x ^ 2) ^ (-a) ≤ (1 + x ^ 2) ^ (-a₀) :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  refine h3.trans ?_
  exact mul_le_mul h4 h5 (by positivity) (by positivity)

/-- Majorant for the logarithmic factor. -/
theorem log_majorant {y : ℝ} (hy : 0 < y) {s₁ s₂ s : ℝ} (hs₁ : 1 < s₁) (h1 : s₁ ≤ s) (h2 : s ≤ s₂)
    (x : ℝ) :
    (1 + 2 * π + |Real.log (x ^ 2 + y ^ 2)|) * (x ^ 2 + y ^ 2) ^ (-s / 2) ≤
      (((1 + 2 * π) + 2 / ((s₁ - 1) / 4)) * (min 1 (y ^ 2)) ^ (-(s₂ / 2 + (s₁ - 1) / 4))) *
        (1 + x ^ 2) ^ (-((s₁ + 1) / 4)) := by
  set S : ℝ := x ^ 2 + y ^ 2 with hSdef
  have hS : 0 < S := by positivity
  set ε : ℝ := (s₁ - 1) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set A : ℝ := s₂ / 2 + ε with hA
  set K : ℝ := (min 1 (y ^ 2)) ^ (-A) * (1 + x ^ 2) ^ (-((s₁ + 1) / 4)) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < min 1 (y ^ 2) := lt_min one_pos (by positivity)
    rw [hK]; positivity
  have e0 : S ^ (-s / 2) ≤ K := by
    have := S_pow_le hy x (a₀ := (s₁ + 1) / 4) (a := s / 2) (A := A) (by linarith)
      (by rw [hε] at hA; linarith) (by rw [hA]; linarith)
    rwa [show -(s / 2) = -s / 2 by ring] at this
  have e1 : S ^ (ε + -s / 2) ≤ K := by
    have := S_pow_le hy x (a₀ := (s₁ + 1) / 4) (a := s / 2 - ε) (A := A) (by linarith)
      (by rw [hε]; linarith) (by rw [hA]; linarith)
    rwa [show -(s / 2 - ε) = ε + -s / 2 by ring] at this
  have e2 : S ^ (-ε + -s / 2) ≤ K := by
    have := S_pow_le hy x (a₀ := (s₁ + 1) / 4) (a := s / 2 + ε) (A := A) (by linarith)
      (by rw [hε]; linarith) (by rw [hA]; linarith)
    rwa [show -(s / 2 + ε) = -ε + -s / 2 by ring] at this
  have hlog : |Real.log S| ≤ (S ^ ε + S ^ (-ε)) / ε := by
    have h' : 0 ≤ S ^ ε := (Real.rpow_pos_of_pos hS _).le
    have h'' : 0 ≤ S ^ (-ε) := (Real.rpow_pos_of_pos hS _).le
    rw [abs_le]
    constructor
    · have := Real.neg_rpow_div_le_log hS.le hε0
      have : -((S ^ ε + S ^ (-ε)) / ε) ≤ -S ^ (-ε) / ε := by
        rw [neg_div, neg_le_neg_iff]; gcongr; linarith
      linarith [Real.neg_rpow_div_le_log hS.le hε0]
    · have := Real.log_le_rpow_div hS.le hε0
      refine this.trans ?_
      gcongr; linarith
  have m1 : S ^ ε * S ^ (-s / 2) = S ^ (ε + -s / 2) := (Real.rpow_add hS _ _).symm
  have m2 : S ^ (-ε) * S ^ (-s / 2) = S ^ (-ε + -s / 2) := (Real.rpow_add hS _ _).symm
  have hp : 0 < S ^ (-s / 2) := Real.rpow_pos_of_pos hS _
  calc (1 + 2 * π + |Real.log S|) * S ^ (-s / 2)
      ≤ (1 + 2 * π + (S ^ ε + S ^ (-ε)) / ε) * S ^ (-s / 2) := by gcongr
    _ = (1 + 2 * π) * S ^ (-s / 2) + (S ^ (ε + -s / 2) + S ^ (-ε + -s / 2)) / ε := by
        rw [← m1, ← m2]; field_simp
    _ ≤ (1 + 2 * π) * K + (K + K) / ε := by gcongr
    _ = _ := by rw [hK]; field_simp; ring

/-- The linear form $(\alpha,\beta) \mapsto -\alpha\log(x+iy) - \beta\log(x-iy)$. -/
def xiL (y x : ℝ) : ℂ × ℂ →L[ℂ] ℂ :=
  (-Complex.log ((x : ℂ) + y * I)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (-Complex.log ((x : ℂ) - y * I)) • ContinuousLinearMap.snd ℂ ℂ ℂ

theorem xiL_apply (y x : ℝ) (p : ℂ × ℂ) :
    xiL y x p = -Complex.log ((x : ℂ) + y * I) * p.1 - Complex.log ((x : ℂ) - y * I) * p.2 := by
  simp [xiL]; ring

theorem phi_mul_exp_eq {y : ℝ} (hy : 0 < y) (α β : ℂ) (t x : ℝ) :
    phi y α β x * cexp (-2 * π * I * t * x) =
      cexp (xiL y x (α, β) + (-2 * π * I * t * x : ℂ)) := by
  rw [xiL_apply, Complex.exp_add, phi, Complex.cpow_def_of_ne_zero (ofReal_add_mul_I_ne_zero hy x),
    Complex.cpow_def_of_ne_zero (ofReal_sub_mul_I_ne_zero hy x), ← Complex.exp_add]
  congr 2
  ring

theorem norm_log_le_aux {w : ℂ} : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + π := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.log_re, Complex.log_im]
  linarith [Complex.abs_arg_le_pi w]

theorem norm_xiL_le {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ‖xiL y x‖ ≤ 2 * π + |Real.log (x ^ 2 + y ^ 2)| := by
  have hS : 0 < x ^ 2 + y ^ 2 := by positivity
  have hn1 : ‖(x : ℂ) + y * I‖ = Real.sqrt (x ^ 2 + y ^ 2) := Complex.norm_add_mul_I x y
  have hn2 : ‖(x : ℂ) - y * I‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.norm_add_mul_I]
    simp
  have hl : |Real.log (Real.sqrt (x ^ 2 + y ^ 2))| = |Real.log (x ^ 2 + y ^ 2)| / 2 := by
    rw [Real.log_sqrt hS.le, abs_div, abs_two]
  have b1 := norm_log_le_aux (w := (x : ℂ) + y * I)
  have b2 := norm_log_le_aux (w := (x : ℂ) - y * I)
  rw [hn1, hl] at b1
  rw [hn2, hl] at b2
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun p ↦ ?_)
  rw [xiL_apply]
  calc _ ≤ ‖-Complex.log ((x : ℂ) + y * I) * p.1‖ + ‖Complex.log ((x : ℂ) - y * I) * p.2‖ :=
        norm_sub_le _ _
    _ ≤ ‖Complex.log ((x : ℂ) + y * I)‖ * ‖p‖ + ‖Complex.log ((x : ℂ) - y * I)‖ * ‖p‖ := by
        rw [norm_mul, norm_mul, norm_neg]
        gcongr
        · exact norm_fst_le p
        · exact norm_snd_le p
    _ ≤ _ := by
        have := norm_nonneg p
        nlinarith [abs_nonneg (Real.log (x ^ 2 + y ^ 2))]

theorem continuous_xiL {y : ℝ} (hy : 0 < y) : Continuous (xiL y) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  have h1 : (x : ℂ) + y * I ∈ Complex.slitPlane := Or.inr (by simp; exact hy.ne')
  have h2 : (x : ℂ) - y * I ∈ Complex.slitPlane := Or.inr (by simp; exact hy.ne')
  have c1 : ContinuousAt (fun x : ℝ ↦ Complex.log ((x : ℂ) + y * I)) x :=
    ContinuousAt.clog (by fun_prop) h1
  have c2 : ContinuousAt (fun x : ℝ ↦ Complex.log ((x : ℂ) - y * I)) x :=
    ContinuousAt.clog (by fun_prop) h2
  unfold xiL
  fun_prop

theorem differentiableOn_xi_aux {y : ℝ} (hy : 0 < y) (t : ℝ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ ∫ x : ℝ, cexp (xiL y x p + (-2 * π * I * t * x : ℂ)))
      {p | 1 < (p.1 + p.2).re} := by
  refine differentiableOn_integral_cexp (xiL y) (fun x ↦ (-2 * π * I * t * x : ℂ))
    (continuous_xiL hy).aestronglyMeasurable (by fun_prop : Continuous _).aestronglyMeasurable ?_
  intro p₀ hp₀
  have hp₀' : 1 < (p₀.1 + p₀.2).re := hp₀
  set s₀ := (p₀.1 + p₀.2).re with hs₀
  set r : ℝ := (s₀ - 1) / 4 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set s₁ := s₀ - 2 * r with hs₁
  set s₂ := s₀ + 2 * r with hs₂
  have hs₁1 : 1 < s₁ := by rw [hs₁, hr]; linarith
  set E : ℝ := Real.exp (π * (|p₀.1.im| + |p₀.2.im| + 2 * r)) with hE
  set K : ℝ := (((1 + 2 * π) + 2 / ((s₁ - 1) / 4)) * (min 1 (y ^ 2)) ^ (-(s₂ / 2 + (s₁ - 1) / 4)))
    with hK
  have hint : Integrable (fun x : ℝ ↦ (1 + ‖x‖ ^ 2) ^ (-((s₁ + 1) / 2) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using (by linarith : (1 : ℝ) < (s₁ + 1) / 2))
  refine ⟨r, hr0, fun x ↦ E * K * (1 + ‖x‖ ^ 2) ^ (-((s₁ + 1) / 2) / 2), hint.const_mul _,
    Eventually.of_forall fun x p hp ↦ ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have re1 : |p.1.re - p₀.1.re| < r := (abs_re_le_norm _).trans_lt (by simpa using hp1)
  have re2 : |p.2.re - p₀.2.re| < r := (abs_re_le_norm _).trans_lt (by simpa using hp2)
  have im1 : |p.1.im - p₀.1.im| < r := (abs_im_le_norm _).trans_lt (by simpa using hp1)
  have im2 : |p.2.im - p₀.2.im| < r := (abs_im_le_norm _).trans_lt (by simpa using hp2)
  have a1 : |p.1.im| ≤ |p₀.1.im| + r := by
    have := abs_sub_abs_le_abs_sub p.1.im p₀.1.im
    linarith
  have a2 : |p.2.im| ≤ |p₀.2.im| + r := by
    have := abs_sub_abs_le_abs_sub p.2.im p₀.2.im
    linarith
  rw [abs_lt] at re1 re2
  have hsre : (p.1 + p.2).re = p.1.re + p.2.re := rfl
  have hs₀re : s₀ = p₀.1.re + p₀.2.re := rfl
  have hn : ‖cexp (xiL y x p + (-2 * π * I * t * x : ℂ))‖ = ‖phi y p.1 p.2 x‖ := by
    have := phi_mul_exp_eq hy p.1 p.2 t x
    rw [← Prod.mk.eta (p := p), ← this, norm_mul]
    have : ‖cexp (-2 * π * I * t * x)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [this, mul_one]
  rw [hn]
  have hphi := norm_phi_le hy p.1 p.2 x
  have himE : Real.exp (π * (|p.1.im| + |p.2.im|)) ≤ E := by
    rw [hE]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hlm := log_majorant hy (s₁ := s₁) (s₂ := s₂) (s := (p.1 + p.2).re) hs₁1
    (by rw [hsre]; linarith) (by rw [hsre]; linarith) x
  have hxn : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  show _ ≤ E * K * (1 + ‖x‖ ^ 2) ^ (-((s₁ + 1) / 2) / 2)
  rw [hxn]
  have hLn := norm_xiL_le hy x
  have hSp : 0 ≤ (x ^ 2 + y ^ 2) ^ (-(p.1 + p.2).re / 2) := by positivity
  have hEp : 0 < E := Real.exp_pos _
  calc ‖phi y p.1 p.2 x‖ * (1 + ‖xiL y x‖)
      ≤ (E * (x ^ 2 + y ^ 2) ^ (-(p.1 + p.2).re / 2)) *
          (1 + (2 * π + |Real.log (x ^ 2 + y ^ 2)|)) := by
        gcongr
        exact hphi.trans (by gcongr)
    _ = E * ((1 + 2 * π + |Real.log (x ^ 2 + y ^ 2)|) * (x ^ 2 + y ^ 2) ^ (-(p.1 + p.2).re / 2)) := by
        ring
    _ ≤ E * (K * (1 + x ^ 2) ^ (-((s₁ + 1) / 4))) := by gcongr
    _ = _ := by
        rw [show -((s₁ + 1) / 2) / 2 = -((s₁ + 1) / 4) by ring]; ring

/-- **Miyake, p. 276.** $\xi(y;\alpha,\beta;t)$ is holomorphic in $(\alpha,\beta)$ on
$\{\operatorname{Re}(\alpha+\beta) > 1\}$. -/
@[kb "miyake1989" "(7.2.11), p. 276"]
theorem differentiableOn_xi {y : ℝ} (hy : 0 < y) (t : ℝ) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ xi y p.1 p.2 t) {p | 1 < (p.1 + p.2).re} := by
  refine (differentiableOn_xi_aux hy t).congr (fun p _ ↦ ?_)
  unfold xi
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  have := phi_mul_exp_eq hy p.1 p.2 t x
  rw [Prod.mk.eta] at this
  exact this

/-- Integrability from a bound by $(y^2+(kx)^2)^{-s/2}$, $s > 1$. -/
theorem integrable_of_bound {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {y k : ℝ} (hy : 0 < y)
    (hk : 0 < k) {s : ℝ} (hs : 1 < s) {E : ℝ}
    (h : ∀ x, ‖f x‖ ≤ E * (y ^ 2 + (k * x) ^ 2) ^ (-s / 2)) : Integrable f := by
  set c : ℝ := min (y ^ 2) (k ^ 2) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  have hint : Integrable (fun x : ℝ ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using hs)
  refine ((hint.const_mul (E * c ^ (-s / 2))).mono' hf (Eventually.of_forall fun x ↦ ?_))
  refine (h x).trans ?_
  have h1 := min_le_left (y ^ 2) (k ^ 2)
  have h2 := min_le_right (y ^ 2) (k ^ 2)
  have hS : c * (1 + x ^ 2) ≤ y ^ 2 + (k * x) ^ 2 := by
    rw [mul_pow]; nlinarith [mul_nonneg (sub_nonneg.2 h2) (sq_nonneg x)]
  have h3 : (y ^ 2 + (k * x) ^ 2) ^ (-s / 2) ≤ (c * (1 + x ^ 2)) ^ (-s / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hS (by linarith)
  rw [Real.mul_rpow hc0.le (by positivity)] at h3
  simp only [Real.norm_eq_abs, sq_abs]
  have hE : 0 ≤ E := by
    have := (norm_nonneg (f 0)).trans (h 0)
    by_contra hneg
    rw [not_le] at hneg
    have : 0 < (y ^ 2 + (k * 0) ^ 2) ^ (-s / 2) := by positivity
    nlinarith
  calc E * (y ^ 2 + (k * x) ^ 2) ^ (-s / 2) ≤ E * (c ^ (-s / 2) * (1 + x ^ 2) ^ (-s / 2)) :=
        mul_le_mul_of_nonneg_left h3 hE
    _ = _ := by ring

/-- The function $v \mapsto e^{-yv}v^{\beta-1}$ for $v>0$ and $0$ otherwise (Miyake (7.2.26)). -/
def expGammaFn (y : ℝ) (β : ℂ) (v : ℝ) : ℂ :=
  cexp (-(y : ℂ) * v) * (((max v 0 : ℝ)) : ℂ) ^ (β - 1)

theorem expGammaFn_of_nonpos {y : ℝ} {β : ℂ} (hβ : 1 < β.re) {v : ℝ} (hv : v ≤ 0) :
    expGammaFn y β v = 0 := by
  have : β - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h; simp at this; linarith
  simp [expGammaFn, max_eq_right hv, this]

theorem expGammaFn_of_pos {y : ℝ} {β : ℂ} {v : ℝ} (hv : 0 < v) :
    expGammaFn y β v = cexp (-(y : ℂ) * v) * (v : ℂ) ^ (β - 1) := by
  simp [expGammaFn, max_eq_left hv.le]

theorem continuous_expGammaFn (y : ℝ) {β : ℂ} (hβ : 1 < β.re) : Continuous (expGammaFn y β) := by
  refine continuous_iff_continuousAt.mpr fun v ↦ ?_
  have h1 : ContinuousAt (fun x : ℝ ↦ ((x : ℝ) : ℂ) ^ (β - 1)) (max v 0) :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inl (by simp; linarith))
  have h2 : ContinuousAt (fun v : ℝ ↦ (((max v 0 : ℝ)) : ℂ) ^ (β - 1)) v :=
    h1.comp (f := fun v : ℝ ↦ max v 0) (by fun_prop)
  unfold expGammaFn
  have h3 : ContinuousAt (fun v : ℝ ↦ cexp (-(y : ℂ) * v)) v := by fun_prop
  exact h3.mul h2

theorem integrable_expGammaFn {y : ℝ} (hy : 0 < y) {β : ℂ} (hβ : 1 < β.re) :
    Integrable (expGammaFn y β) := by
  have h := integrableOn_sigmaIntegrand (z := (y : ℂ)) (α := 1) (β := β) (by simpa using hy)
    (by linarith)
  rw [← integrableOn_iff_integrable_of_support_subset (s := Ioi 0)]
  · refine h.congr_fun (fun u hu ↦ ?_) measurableSet_Ioi
    rw [expGammaFn_of_pos hu]
    simp [sigmaIntegrand]
  · intro v hv
    by_contra hv'
    exact hv (expGammaFn_of_nonpos hβ (not_lt.mp hv'))

/-- The Fourier transform of `expGammaFn`: $\Gamma(\beta)(y + 2\pi i\xi)^{-\beta}$. -/
theorem fourier_expGammaFn {y : ℝ} (hy : 0 < y) {β : ℂ} (hβ : 1 < β.re) (ξ : ℝ) :
    𝓕 (expGammaFn y β) ξ = ((y : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I) ^ (-β) * Gamma β := by
  have hz : 0 < ((y : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I).re := by simpa using hy
  rw [Real.fourier_real_eq_integral_exp_smul,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)), ← sigma_one hz (by linarith),
    sigma]
  · refine setIntegral_congr_fun measurableSet_Ioi (fun v hv ↦ ?_)
    rw [expGammaFn_of_pos hv]
    simp only [sigmaIntegrand, smul_eq_mul, sub_self, Complex.cpow_zero, mul_one]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · intro v hv
    have : v ≤ 0 := not_lt.mp hv
    simp [expGammaFn_of_nonpos hβ this]

theorem integrable_fourier_expGammaFn {y : ℝ} (hy : 0 < y) {β : ℂ} (hβ : 1 < β.re) :
    Integrable (𝓕 (expGammaFn y β)) := by
  have hfun : 𝓕 (expGammaFn y β) = fun ξ : ℝ ↦
      ((y : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I) ^ (-β) * Gamma β :=
    funext (fourier_expGammaFn hy hβ)
  rw [hfun]
  have hcont : Continuous (fun ξ : ℝ ↦ ((y : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I) ^ (-β) * Gamma β) := by
    refine Continuous.mul ?_ continuous_const
    refine continuous_iff_continuousAt.mpr fun ξ ↦ ?_
    have h1 : ((y : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I) ∈ Complex.slitPlane := Or.inl (by simpa using hy)
    have c1 : ContinuousAt (fun ξ : ℝ ↦ (y : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I) ξ := by fun_prop
    have k1 : ContinuousAt (fun _ : ℝ ↦ -β) ξ := continuousAt_const
    exact c1.cpow k1 h1
  refine integrable_of_bound hcont.aestronglyMeasurable hy (k := 2 * π) (by positivity)
    (s := β.re) hβ (E := Real.exp (π * |β.im|) * ‖Gamma β‖) (fun ξ ↦ ?_)
  have hw : ((y : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hn : ‖(y : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I‖ = Real.sqrt (y ^ 2 + (2 * π * ξ) ^ 2) :=
    Complex.norm_add_mul_I _ _
  have hS : 0 < y ^ 2 + (2 * π * ξ) ^ 2 := by positivity
  rw [norm_mul]
  have := norm_cpow_neg_le hw β
  rw [hn, Real.sqrt_eq_rpow, ← Real.rpow_mul hS.le] at this
  have e : 1 / 2 * -β.re = -β.re / 2 := by ring
  rw [e] at this
  calc _ ≤ (Real.exp (π * |β.im|) * (y ^ 2 + (2 * π * ξ) ^ 2) ^ (-β.re / 2)) * ‖Gamma β‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := by ring

/-- **Miyake (7.2.27).** For $\operatorname{Re}\beta > 1$ and $y > 0$, the Fourier integral
$\int_{\mathbb R} e^{ix(u-2\pi t)}(y+ix)^{-\beta}\,dx$ equals $2\pi\Gamma(\beta)^{-1}e^{-y(u-2\pi t)}(u-2\pi t)^{\beta-1}$
for $u > 2\pi t$ and $0$ for $u \le 2\pi t$. Stated with $w = u - 2\pi t$. -/
@[kb "miyake1989" "(7.2.27), p. 278"]
theorem integral_exp_mul_cpow {y : ℝ} (hy : 0 < y) {β : ℂ} (hβ : 1 < β.re) (w : ℝ) :
    ∫ x : ℝ, cexp (I * x * w) * ((y : ℂ) + I * x) ^ (-β) =
      if 0 < w then 2 * π * (Gamma β)⁻¹ * cexp (-(y : ℂ) * w) * (w : ℂ) ^ (β - 1) else 0 := by
  have hΓ : Gamma β ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have inv := (continuous_expGammaFn y hβ).fourierInv_fourier_eq (integrable_expGammaFn hy hβ)
    (integrable_fourier_expGammaFn hy hβ)
  have hw := congrFun inv w
  rw [Real.fourierInv_eq'] at hw
  set F : ℝ → ℂ := fun v ↦ Complex.exp (↑(2 * π * inner ℝ v w) * Complex.I) • 𝓕 (expGammaFn y β) v
    with hF
  have hdiv := MeasureTheory.Measure.integral_comp_div F (2 * π)
  have hpt : ∀ x : ℝ, F (x / (2 * π)) = cexp (I * x * w) * ((y : ℂ) + I * x) ^ (-β) * Gamma β := by
    intro x
    simp only [hF, fourier_expGammaFn hy hβ, smul_eq_mul]
    have h1 : 2 * π * (x / (2 * π)) = x := by field_simp
    have e1 : ((2 * π * (x / (2 * π)) : ℝ) : ℂ) = (x : ℂ) := by rw [h1]
    have hin : (inner ℝ (x / (2 * π)) w : ℝ) = x / (2 * π) * w := by
      simp [mul_comm]
    have e3 : ((2 * π * (x / (2 * π) * w) : ℝ) : ℂ) * I = I * x * w := by
      push_cast; field_simp
    rw [hin, e3, e1, ← mul_assoc, mul_comm (x : ℂ) I]
  simp only [hpt] at hdiv
  rw [integral_mul_const, abs_of_pos (by positivity : 0 < 2 * π), Complex.real_smul] at hdiv
  have hFw : ∫ y, F y = expGammaFn y β w := hw
  rw [hFw] at hdiv
  have hmain : ∫ x : ℝ, cexp (I * x * w) * ((y : ℂ) + I * x) ^ (-β) =
      2 * π * (Gamma β)⁻¹ * expGammaFn y β w := by
    field_simp
    have := hdiv
    push_cast at this ⊢
    linear_combination this
  rw [hmain]
  split_ifs with hw0
  · rw [expGammaFn_of_pos hw0]; ring
  · rw [expGammaFn_of_nonpos hβ (not_lt.mp hw0)]; simp

theorem neg_I_cpow (β : ℂ) : (-I) ^ (-β) = I ^ β := by
  rw [Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero),
    Complex.cpow_def_of_ne_zero Complex.I_ne_zero, Complex.log_neg_I, Complex.log_I]
  congr 1; ring

/-- $\phi(y;\alpha,\beta;x) = i^{\beta-\alpha}(y-ix)^{-\alpha}(y+ix)^{-\beta}$ (Miyake p. 277). -/
theorem phi_eq {y : ℝ} (hy : 0 < y) (α β : ℂ) (x : ℝ) :
    phi y α β x = I ^ (β - α) * (((y : ℂ) - I * x) ^ (-α) * ((y : ℂ) + I * x) ^ (-β)) := by
  have h1 : ((x : ℂ) + y * I) = I * ((y : ℂ) - I * x) := by
    linear_combination (x : ℂ) * Complex.I_sq
  have h2 : ((x : ℂ) - y * I) = (-I) * ((y : ℂ) + I * x) := by
    linear_combination (x : ℂ) * Complex.I_sq
  have hb1 : |Complex.arg ((y : ℂ) - I * x)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa using hy))
  have hb2 : |Complex.arg ((y : ℂ) + I * x)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa using hy))
  rw [abs_lt] at hb1 hb2
  unfold phi
  rw [h1, h2, Complex.mul_cpow (by
      rw [Complex.arg_I]; constructor <;> linarith [Real.pi_pos]),
    Complex.mul_cpow (by
      rw [Complex.arg_neg_I]; constructor <;> linarith [Real.pi_pos]), neg_I_cpow,
    show β - α = β + -α by ring, Complex.cpow_add _ _ Complex.I_ne_zero]
  ring

/-- Translation of a half-line integral. -/
theorem setIntegral_Ioi_comp_add (f : ℝ → ℂ) (a c : ℝ) :
    ∫ x in Ioi a, f (x + c) = ∫ x in Ioi (a + c), f x := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun x ↦ (Ioi (a + c)).indicator f x) c]
  congr 1
  funext x
  by_cases h : a < x
  · have h' : a + c < x + c := by linarith
    simp [Set.indicator_of_mem, h, h']
  · have h' : ¬ (a + c < x + c) := by intro h''; exact h (by linarith)
    simp [h, h']

theorem integrable_cpow_add_I {y : ℝ} (hy : 0 < y) {b : ℂ} (hb : 1 < b.re) :
    Integrable (fun x : ℝ ↦ ((y : ℂ) + I * x) ^ (-b)) := by
  have hcont : Continuous (fun x : ℝ ↦ ((y : ℂ) + I * x) ^ (-b)) := by
    refine continuous_iff_continuousAt.mpr fun ξ ↦ ?_
    have h1 : ((y : ℂ) + I * ξ) ∈ Complex.slitPlane := Or.inl (by simpa using hy)
    have c1 : ContinuousAt (fun ξ : ℝ ↦ (y : ℂ) + I * ξ) ξ := by fun_prop
    have k1 : ContinuousAt (fun _ : ℝ ↦ -b) ξ := continuousAt_const
    exact c1.cpow k1 h1
  refine integrable_of_bound hcont.aestronglyMeasurable hy (k := 1) one_pos (s := b.re) hb
    (E := Real.exp (π * |b.im|)) (fun x ↦ ?_)
  have hw : ((y : ℂ) + I * x) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hn : ‖(y : ℂ) + I * x‖ = Real.sqrt (y ^ 2 + x ^ 2) := by
    rw [mul_comm I]; exact Complex.norm_add_mul_I _ _
  have hS : 0 < y ^ 2 + (1 * x) ^ 2 := by positivity
  have := norm_cpow_neg_le hw b
  rw [hn, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)] at this
  have e : 1 / 2 * -b.re = -b.re / 2 := by ring
  rw [e] at this
  simpa using this

/-- **Core of Lemma 7.2.2** (Miyake pp. 277-278). -/
theorem xi_core {y : ℝ} (hy : 0 < y) {a b : ℂ} (ha : 0 < a.re) (hb : 1 < b.re) {s : ℝ}
    (hs : 0 ≤ s) :
    Gamma a * ∫ x : ℝ, (((y : ℂ) - I * x) ^ (-a) * ((y : ℂ) + I * x) ^ (-b)) *
        cexp (-2 * π * I * s * x) =
      2 * π * (Gamma b)⁻¹ * eta (2 * y) a b (π * s) := by
  set H : ℝ → ℝ → ℂ := fun x u ↦ cexp (-((y : ℂ) - I * x) * u) * (u : ℂ) ^ (a - 1) *
    (((y : ℂ) + I * x) ^ (-b) * cexp (-2 * π * I * s * x)) with hH
  have hstep2 : Gamma a * ∫ x : ℝ, (((y : ℂ) - I * x) ^ (-a) * ((y : ℂ) + I * x) ^ (-b)) *
        cexp (-2 * π * I * s * x) = ∫ x : ℝ, ∫ u in Ioi (0 : ℝ), H x u := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    have hz : 0 < ((y : ℂ) - I * x).re := by simpa using hy
    have hs1 : ∫ u in Ioi (0 : ℝ), cexp (-((y : ℂ) - I * x) * u) * (u : ℂ) ^ (a - 1) =
        ((y : ℂ) - I * x) ^ (-a) * Gamma a := by
      rw [← sigma_one hz ha, sigma]
      refine setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ ?_)
      simp [sigmaIntegrand]
    simp only [hH]
    rw [integral_mul_const, hs1]
    ring
  -- Fubini
  have hψ := integrable_cpow_add_I hy hb
  have hI : IntegrableOn (fun u : ℝ ↦ u ^ (a.re - 1) * Real.exp (-(y * u))) (Ioi 0) :=
    integrableOn_rpow_mul_exp hy ha
  have hprod := hψ.norm.mul_prod hI
  have hint : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hvol : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
        (volume.restrict univ).prod (volume.restrict (Ioi (0 : ℝ))) := by
      rw [Measure.restrict_univ]
    rw [hvol, Measure.prod_restrict] at hprod ⊢
    refine hprod.mono' ?_ ((ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioi)).mpr
      (Eventually.of_forall fun q hq ↦ ?_))
    · refine Measurable.aestronglyMeasurable ?_
      unfold Function.uncurry
      simp only [hH]
      fun_prop
    · obtain ⟨-, hu⟩ := hq
      have hu0 : (0 : ℝ) < q.2 := hu
      simp only [Function.uncurry, hH]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
        Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      have e1 : (-((y : ℂ) - I * q.1) * q.2).re = -(y * q.2) := by simp
      have e2 : (-2 * π * I * s * q.1 : ℂ).re = 0 := by simp
      rw [e1, e2]
      simp only [Complex.sub_re, Complex.one_re, Real.exp_zero, mul_one]
      apply le_of_eq
      ring
  rw [hstep2, integral_integral_swap hint]
  have h4 : ∀ u ∈ Ioi (0 : ℝ), ∫ x : ℝ, H x u = (cexp (-(y : ℂ) * u) * (u : ℂ) ^ (a - 1)) *
      (if 0 < u - 2 * π * s then 2 * π * (Gamma b)⁻¹ * cexp (-(y : ℂ) * ((u - 2 * π * s : ℝ) : ℂ)) *
        ((u - 2 * π * s : ℝ) : ℂ) ^ (b - 1) else 0) := by
    intro u _
    have key := integral_exp_mul_cpow hy hb (u - 2 * π * s)
    rw [← key, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [hH]
    have e : cexp (-((y : ℂ) - I * x) * u) * cexp (-2 * π * I * s * x) =
        cexp (-(y : ℂ) * u) * cexp (I * x * ((u - 2 * π * s : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination ((u : ℂ) ^ (a - 1) * ((y : ℂ) + I * x) ^ (-b)) * e
  rw [setIntegral_congr_fun measurableSet_Ioi h4]
  set G : ℝ → ℂ := fun u ↦ (cexp (-(y : ℂ) * u) * (u : ℂ) ^ (a - 1)) *
    (2 * π * (Gamma b)⁻¹ * cexp (-(y : ℂ) * ((u - 2 * π * s : ℝ) : ℂ)) *
      ((u - 2 * π * s : ℝ) : ℂ) ^ (b - 1)) with hG
  have hind : ∀ u ∈ Ioi (0 : ℝ), (cexp (-(y : ℂ) * u) * (u : ℂ) ^ (a - 1)) *
      (if 0 < u - 2 * π * s then 2 * π * (Gamma b)⁻¹ * cexp (-(y : ℂ) * ((u - 2 * π * s : ℝ) : ℂ)) *
        ((u - 2 * π * s : ℝ) : ℂ) ^ (b - 1) else 0) = (Ioi (2 * π * s)).indicator G u := by
    intro u _
    by_cases h : 0 < u - 2 * π * s
    · have h' : u ∈ Ioi (2 * π * s) := by simp only [mem_Ioi]; linarith
      rw [if_pos h, Set.indicator_of_mem h']
    · have h' : u ∉ Ioi (2 * π * s) := by simp only [mem_Ioi]; intro h''; exact h (by linarith)
      rw [if_neg h, Set.indicator_of_notMem h', mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hind, setIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_right (by positivity : (0 : ℝ) ≤ 2 * π * s),
    show 2 * π * s = π * s + π * s by ring, ← setIntegral_Ioi_comp_add G (π * s) (π * s)]
  unfold eta
  rw [abs_of_nonneg (by positivity), ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv ↦ ?_)
  simp only [hG, etaIntegrand]
  have e1 : v + π * s - 2 * π * s = v - π * s := by ring
  have e2 : cexp (-(y : ℂ) * ((v + π * s : ℝ) : ℂ)) * cexp (-(y : ℂ) * ((v - π * s : ℝ) : ℂ)) =
      cexp (-((2 * y : ℝ) : ℂ) * (v : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1]
  linear_combination (2 * π * (Gamma b)⁻¹ * ((v + π * s : ℝ) : ℂ) ^ (a - 1) *
    ((v - π * s : ℝ) : ℂ) ^ (b - 1)) * e2

/-- **Miyake, Lemma 7.2.2.** For $y > 0$: if $\operatorname{Re}\alpha > 0$, $\operatorname{Re}\beta > 1$ and
$t \ge 0$, or $\operatorname{Re}\alpha > 1$, $\operatorname{Re}\beta > 0$ and $t < 0$, then
$\xi(y;\alpha,\beta;t) = i^{\beta-\alpha}(2\pi)\Gamma(\alpha)^{-1}\Gamma(\beta)^{-1}\eta(2y;\alpha,\beta;\pi t)$. -/
@[kb "miyake1989" "Lemma 7.2.2, p. 277"]
theorem xi_eq_eta {y : ℝ} (hy : 0 < y) {α β : ℂ} {t : ℝ}
    (h : (0 < α.re ∧ 1 < β.re ∧ 0 ≤ t) ∨ (1 < α.re ∧ 0 < β.re ∧ t < 0)) :
    xi y α β t = I ^ (β - α) * (2 * π) * (Gamma α)⁻¹ * (Gamma β)⁻¹ * eta (2 * y) α β (π * t) := by
  have hxi : xi y α β t = I ^ (β - α) * ∫ x : ℝ, (((y : ℂ) - I * x) ^ (-α) *
      ((y : ℂ) + I * x) ^ (-β)) * cexp (-2 * π * I * t * x) := by
    rw [xi, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [phi_eq hy]
    ring
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hΓ : Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1
    have hΓb : Gamma β ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hc := xi_core hy h1 h2 h3
    rw [hxi]
    have : ∫ x : ℝ, (((y : ℂ) - I * x) ^ (-α) * ((y : ℂ) + I * x) ^ (-β)) *
        cexp (-2 * π * I * t * x) = 2 * π * (Gamma β)⁻¹ * eta (2 * y) α β (π * t) / Gamma α := by
      rw [eq_div_iff hΓ, mul_comm]; exact hc
    rw [this]
    field_simp
  · have hΓ : Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hΓb : Gamma β ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h2
    have hc := xi_core hy h2 h1 (s := -t) (by linarith)
    have hrefl : ∫ x : ℝ, (((y : ℂ) - I * x) ^ (-α) * ((y : ℂ) + I * x) ^ (-β)) *
        cexp (-2 * π * I * t * x) = ∫ x : ℝ, (((y : ℂ) - I * x) ^ (-β) *
          ((y : ℂ) + I * x) ^ (-α)) * cexp (-2 * π * I * (-t : ℝ) * x) := by
      rw [← integral_neg_eq_self]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [Complex.ofReal_neg]
      push_cast
      have a1 : (y : ℂ) - I * -(x : ℂ) = y + I * x := by ring
      have a2 : (y : ℂ) + I * -(x : ℂ) = y - I * x := by ring
      have a3 : -2 * (π : ℂ) * I * t * -(x : ℂ) = -2 * π * I * -t * x := by ring
      rw [a1, a2, a3]
      ring
    rw [hxi, hrefl]
    have hs : eta (2 * y) β α (π * -t) = eta (2 * y) α β (π * t) := by
      rw [mul_neg]; exact (eta_swap (2 * y) α β (π * t)).symm
    rw [hs] at hc
    have : ∫ x : ℝ, (((y : ℂ) - I * x) ^ (-β) * ((y : ℂ) + I * x) ^ (-α)) *
        cexp (-2 * π * I * (-t : ℝ) * x) = 2 * π * (Gamma α)⁻¹ * eta (2 * y) α β (π * t) / Gamma β := by
      rw [eq_div_iff hΓb, mul_comm]; exact hc
    rw [this]
    field_simp

/-- $\eta(y;\alpha,\beta;0) = y^{1-\alpha-\beta}\Gamma(\alpha+\beta-1)$ for $\operatorname{Re}(\alpha+\beta) > 1$. -/
theorem eta_zero {y : ℝ} (hy : 0 < y) {α β : ℂ} (h : 1 < (α + β).re) :
    eta y α β 0 = (y : ℂ) ^ (1 - α - β) * Gamma (α + β - 1) := by
  have hre : 0 < (α + β - 1).re := by
    have h' : 1 < α.re + β.re := h
    simp; linarith
  have key := Complex.integral_cpow_mul_exp_neg_mul_Ioi hre hy
  have e : (1 / (y : ℂ)) ^ (α + β - 1) = (y : ℂ) ^ (1 - α - β) := by
    rw [one_div, Complex.inv_cpow _ _
      (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne),
      ← Complex.cpow_neg]
    congr 1; ring
  rw [e] at key
  rw [← key, eta, abs_zero]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu ↦ ?_)
  have hu0 : (0 : ℝ) < u := hu
  have hu1 : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  simp only [etaIntegrand, add_zero, sub_zero]
  rw [show α + β - 1 - 1 = (α - 1) + (β - 1) by ring, Complex.cpow_add _ _ hu1]
  simp only [neg_mul]
  ring

/-- One-variable identity theorem for $\xi$ along $\alpha + \beta = s$. -/
theorem xi_one_var {y : ℝ} (hy : 0 < y) (t : ℝ) {s : ℂ} (hs : 1 < s.re) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G) {α₀ : ℂ} (h : ∀ᶠ α in 𝓝 α₀, xi y α (s - α) t = G α) (α : ℂ) :
    xi y α (s - α) t = G α := by
  have hF : Differentiable ℂ (fun α : ℂ ↦ xi y α (s - α) t) := by
    have := (differentiableOn_xi hy t).comp (f := fun α : ℂ ↦ ((α, s - α) : ℂ × ℂ))
      (by fun_prop : Differentiable ℂ _).differentiableOn (s := Set.univ)
      (fun α _ ↦ by simpa using hs)
    exact differentiableOn_univ.mp this
  exact eq_of_eventuallyEq_entire hF hG h α

theorem eventually_strip (s : ℂ) (hs : 1 < s.re) :
    ∀ᶠ α in 𝓝 (((s.re - 1) / 2 : ℝ) : ℂ), 0 < α.re ∧ 1 < (s - α).re := by
  have ho : IsOpen {α : ℂ | 0 < α.re ∧ 1 < (s - α).re} := by
    show IsOpen ({α : ℂ | 0 < α.re} ∩ {α : ℂ | 1 < (s - α).re})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.sub continuous_id)))
  refine ho.mem_nhds ?_
  simp only [Set.mem_setOf_eq, Complex.ofReal_re, Complex.sub_re]
  constructor <;> linarith

/-- **Miyake, Lemma 7.2.3.** For $y > 0$ and $\operatorname{Re}(\alpha+\beta) > 1$,
$\xi(y;\alpha,\beta;0) = i^{\beta-\alpha}(2\pi)\Gamma(\alpha)^{-1}\Gamma(\beta)^{-1}\Gamma(\alpha+\beta-1)(2y)^{1-\alpha-\beta}$;
the right-hand side is meromorphic on $\mathbb C \times \mathbb C$ (it is the continuation). -/
@[kb "miyake1989" "Lemma 7.2.3, p. 279"]
theorem xi_zero {y : ℝ} (hy : 0 < y) {α β : ℂ} (h : 1 < (α + β).re) :
    xi y α β 0 = I ^ (β - α) * (2 * π) * (Gamma α)⁻¹ * (Gamma β)⁻¹ * Gamma (α + β - 1) *
      ((2 * y : ℝ) : ℂ) ^ (1 - α - β) := by
  set s := α + β with hs
  have hG : Differentiable ℂ (fun a : ℂ ↦ I ^ ((s - a) - a) * (2 * π) * (Gamma a)⁻¹ *
      (Gamma (s - a))⁻¹ * Gamma (s - 1) * ((2 * y : ℝ) : ℂ) ^ (1 - s)) := by
    have h1 : Differentiable ℂ (fun a : ℂ ↦ I ^ ((s - a) - a)) :=
      Differentiable.const_cpow (by fun_prop) (Or.inl Complex.I_ne_zero)
    have h2 := differentiable_one_div_Gamma
    have h3 : Differentiable ℂ (fun a : ℂ ↦ (Gamma (s - a))⁻¹) :=
      h2.comp (by fun_prop : Differentiable ℂ (fun a : ℂ ↦ s - a))
    exact ((((h1.mul_const _).mul h2).mul h3).mul_const _).mul_const _
  have hev : ∀ᶠ a in 𝓝 (((s.re - 1) / 2 : ℝ) : ℂ),
      xi y a (s - a) 0 = I ^ ((s - a) - a) * (2 * π) * (Gamma a)⁻¹ *
      (Gamma (s - a))⁻¹ * Gamma (s - 1) * ((2 * y : ℝ) : ℂ) ^ (1 - s) := by
    filter_upwards [eventually_strip s h] with a ha
    rw [xi_eq_eta hy (Or.inl ⟨ha.1, ha.2, le_refl _⟩), mul_zero,
      eta_zero (by positivity) (by simpa using h)]
    ring
  have := xi_one_var hy 0 h hG hev α
  rw [hs, add_sub_cancel_left] at this
  rw [this, show 1 - α - β = 1 - (α + β) by ring]

/-- **Miyake, Theorem 7.2.5 (1)**, the right-hand side: the continuation of $\xi(y;\alpha,\beta;t)$,
$$\begin{cases} i^{\beta-\alpha}(2\pi)^{\alpha}\Gamma(\alpha)^{-1}(2y)^{-\beta}t^{\alpha-1}e^{-2\pi yt}\omega(4\pi yt;\alpha,\beta)
  & (t > 0)\\
i^{\beta-\alpha}(2\pi)^{\alpha+\beta}\Gamma(\alpha)^{-1}\Gamma(\beta)^{-1}\Gamma(\alpha+\beta-1)(4\pi y)^{1-\alpha-\beta}
  & (t = 0)\\
i^{\beta-\alpha}(2\pi)^{\beta}\Gamma(\beta)^{-1}(2y)^{-\alpha}|t|^{\beta-1}e^{-2\pi y|t|}\omega(4\pi y|t|;\beta,\alpha)
  & (t < 0).\end{cases}$$ -/
@[kb "miyake1989" "Theorem 7.2.5 (1), p. 281"]
def xiCont (y : ℝ) (α β : ℂ) (t : ℝ) : ℂ :=
  if 0 < t then
    I ^ (β - α) * ((2 * π : ℝ) : ℂ) ^ α * (Gamma α)⁻¹ * ((2 * y : ℝ) : ℂ) ^ (-β) *
      (t : ℂ) ^ (α - 1) * Real.exp (-2 * π * y * t) * omega (4 * π * y * t : ℝ) α β
  else if t = 0 then
    I ^ (β - α) * ((2 * π : ℝ) : ℂ) ^ (α + β) * (Gamma α)⁻¹ * (Gamma β)⁻¹ * Gamma (α + β - 1) *
      ((4 * π * y : ℝ) : ℂ) ^ (1 - α - β)
  else
    I ^ (β - α) * ((2 * π : ℝ) : ℂ) ^ β * (Gamma β)⁻¹ * ((2 * y : ℝ) : ℂ) ^ (-α) *
      ((|t| : ℝ) : ℂ) ^ (β - 1) * Real.exp (-2 * π * y * |t|) * omega (4 * π * y * |t| : ℝ) β α

theorem cpow_mul_real' {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (w : ℂ) :
    ((c * d : ℝ) : ℂ) ^ w = (c : ℂ) ^ w * (d : ℂ) ^ w := by
  rw [Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg hc hd w

theorem cpow_ofReal_ne_zero {c : ℝ} (hc : 0 < c) (w : ℂ) : (c : ℂ) ^ w ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]; simp [hc.ne']

/-- Algebraic core of Theorem 7.2.5 for $t > 0$. -/
theorem core_pos {y t : ℝ} (hy : 0 < y) (ht : 0 < t) {a b : ℂ} (hb : 0 < b.re) :
    (2 * (π : ℂ)) * (Gamma b)⁻¹ * eta (2 * y) a b (π * t) =
      ((2 * π : ℝ) : ℂ) ^ a * ((2 * y : ℝ) : ℂ) ^ (-b) * (t : ℂ) ^ (a - 1) *
        ((Real.exp (-2 * π * y * t) : ℝ) : ℂ) * omega ((4 * π * y * t : ℝ) : ℂ) a b := by
  have hπ := Real.pi_pos
  have hz : 0 < (((4 * π * y * t : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]; positivity
  rw [omega_eq_omega0 hz hb]
  rw [eta_eq_sigma (by positivity : 0 < 2 * y) (by positivity : 0 < π * t) a b]
  have hz2 : (2 * ((π * t * (2 * y) : ℝ) : ℂ)) = ((4 * π * y * t : ℝ) : ℂ) := by
    push_cast; ring
  rw [hz2]
  have hE : cexp (-(((π * t * (2 * y) : ℝ)) : ℂ)) = ((Real.exp (-2 * π * y * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hE]
  have h4 : (4 * π * y * t : ℝ) = 2 * 2 * π * y * t := by ring
  have h2π : (2 * π : ℝ) = 2 * π := rfl
  have hpow : (2 * (π : ℂ)) * ((((π * t : ℝ)) : ℂ)) ^ (a + b - 1) * (2 : ℂ) ^ (a + b - 1) =
      ((2 * π : ℝ) : ℂ) ^ a * ((2 * y : ℝ) : ℂ) ^ (-b) * (t : ℂ) ^ (a - 1) *
        (((4 * π * y * t : ℝ)) : ℂ) ^ b := by
    rw [h4]
    have n2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have nπ : (π : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
    have nt : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have ny : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp (disch := positivity) only [cpow_mul_real', Complex.ofReal_ofNat, Complex.cpow_neg]
    rw [Complex.cpow_sub _ _ nt, Complex.cpow_one,
      Complex.cpow_sub _ _ nπ, Complex.cpow_sub _ _ n2, Complex.cpow_sub _ _ nt,
      Complex.cpow_add _ _ nπ, Complex.cpow_add _ _ n2, Complex.cpow_add _ _ nt,
      Complex.cpow_one, Complex.cpow_one, Complex.cpow_one]
    have a1 : (2 : ℂ) ^ b ≠ 0 := by
      simpa using cpow_ofReal_ne_zero (c := 2) (by norm_num) b
    have a2 : (y : ℂ) ^ b ≠ 0 := cpow_ofReal_ne_zero hy b
    field_simp
  linear_combination ((Gamma b)⁻¹ * sigma (((4 * π * y * t : ℝ)) : ℂ) a b *
    ((Real.exp (-2 * π * y * t) : ℝ) : ℂ)) * hpow
theorem differentiable_omega_pair {z : ℂ} (hz : 0 < z.re) :
    Differentiable ℂ (fun p : ℂ × ℂ ↦ omega z p.1 p.2) := by
  have := differentiableOn_omega.comp (f := fun p : ℂ × ℂ ↦ ((z, p.1, p.2) : ℂ × ℂ × ℂ))
    (by fun_prop : Differentiable ℂ _).differentiableOn (s := Set.univ) (fun p _ ↦ hz)
  exact differentiableOn_univ.mp this

theorem differentiable_xiCont_pos {y : ℝ} (hy : 0 < y) {t : ℝ} (ht : 0 < t) :
    Differentiable ℂ (fun p : ℂ × ℂ ↦ xiCont y p.1 p.2 t) := by
  have hπ := Real.pi_pos
  have hfun : (fun p : ℂ × ℂ ↦ xiCont y p.1 p.2 t) = fun p ↦
      I ^ (p.2 - p.1) * ((2 * π : ℝ) : ℂ) ^ p.1 * (Gamma p.1)⁻¹ * ((2 * y : ℝ) : ℂ) ^ (-p.2) *
      (t : ℂ) ^ (p.1 - 1) * ((Real.exp (-2 * π * y * t) : ℝ) : ℂ) *
      omega ((4 * π * y * t : ℝ) : ℂ) p.1 p.2 := by
    funext p; simp only [xiCont]; rw [if_pos ht]
  rw [hfun]
  have hz : 0 < (((4 * π * y * t : ℝ)) : ℂ).re := by rw [Complex.ofReal_re]; positivity
  have h1 : Differentiable ℂ (fun p : ℂ × ℂ ↦ I ^ (p.2 - p.1)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl Complex.I_ne_zero)
  have h2 : Differentiable ℂ (fun p : ℂ × ℂ ↦ ((2 * π : ℝ) : ℂ) ^ p.1) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)))
  have h3 : Differentiable ℂ (fun p : ℂ × ℂ ↦ (Gamma p.1)⁻¹) :=
    differentiable_one_div_Gamma.comp differentiable_fst
  have h4 : Differentiable ℂ (fun p : ℂ × ℂ ↦ ((2 * y : ℝ) : ℂ) ^ (-p.2)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (by positivity : (2 * y : ℝ) ≠ 0)))
  have h5 : Differentiable ℂ (fun p : ℂ × ℂ ↦ (t : ℂ) ^ (p.1 - 1)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast ht.ne'))
  exact (((((h1.mul h2).mul h3).mul h4).mul h5).mul_const _).mul (differentiable_omega_pair hz)

theorem differentiable_xiCont_neg {y : ℝ} (hy : 0 < y) {t : ℝ} (ht : t < 0) :
    Differentiable ℂ (fun p : ℂ × ℂ ↦ xiCont y p.1 p.2 t) := by
  have hπ := Real.pi_pos
  have hn : ¬ (0 < t) := not_lt.mpr ht.le
  have hfun : (fun p : ℂ × ℂ ↦ xiCont y p.1 p.2 t) = fun p ↦
      I ^ (p.2 - p.1) * ((2 * π : ℝ) : ℂ) ^ p.2 * (Gamma p.2)⁻¹ * ((2 * y : ℝ) : ℂ) ^ (-p.1) *
      ((|t| : ℝ) : ℂ) ^ (p.2 - 1) * ((Real.exp (-2 * π * y * |t|) : ℝ) : ℂ) *
      omega ((4 * π * y * |t| : ℝ) : ℂ) p.2 p.1 := by
    funext p; simp only [xiCont]; rw [if_neg hn, if_neg ht.ne]
  rw [hfun]
  have habs : 0 < |t| := abs_pos.mpr ht.ne
  have hz : 0 < (((4 * π * y * |t| : ℝ)) : ℂ).re := by rw [Complex.ofReal_re]; positivity
  have h1 : Differentiable ℂ (fun p : ℂ × ℂ ↦ I ^ (p.2 - p.1)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl Complex.I_ne_zero)
  have h2 : Differentiable ℂ (fun p : ℂ × ℂ ↦ ((2 * π : ℝ) : ℂ) ^ p.2) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)))
  have h3 : Differentiable ℂ (fun p : ℂ × ℂ ↦ (Gamma p.2)⁻¹) :=
    differentiable_one_div_Gamma.comp differentiable_snd
  have h4 : Differentiable ℂ (fun p : ℂ × ℂ ↦ ((2 * y : ℝ) : ℂ) ^ (-p.1)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast (by positivity : (2 * y : ℝ) ≠ 0)))
  have h5 : Differentiable ℂ (fun p : ℂ × ℂ ↦ ((|t| : ℝ) : ℂ) ^ (p.2 - 1)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast habs.ne'))
  have h6 : Differentiable ℂ (fun p : ℂ × ℂ ↦ omega ((4 * π * y * |t| : ℝ) : ℂ) p.2 p.1) :=
    (Differentiable.comp (g := fun q : ℂ × ℂ ↦ omega ((4 * π * y * |t| : ℝ) : ℂ) q.1 q.2) (f := fun p : ℂ × ℂ ↦ (p.2, p.1)) (differentiable_omega_pair hz) (differentiable_snd.prodMk differentiable_fst))
  exact (((((h1.mul h2).mul h3).mul h4).mul h5).mul_const _).mul h6

theorem xi_pos_strip {y : ℝ} (hy : 0 < y) {α β : ℂ} {t : ℝ} (ht : 0 < t) (hα : 0 < α.re)
    (hβ : 1 < β.re) : xi y α β t = xiCont y α β t := by
  simp only [xiCont]; rw [if_pos ht]
  rw [xi_eq_eta hy (Or.inl ⟨hα, hβ, ht.le⟩)]
  have := core_pos hy ht (a := α) (b := β) (by linarith)
  push_cast at this ⊢
  linear_combination (I ^ (β - α) * (Gamma α)⁻¹) * this

theorem xi_neg_strip {y : ℝ} (hy : 0 < y) {α β : ℂ} {t : ℝ} (ht : t < 0) (hα : 1 < α.re)
    (hβ : 0 < β.re) : xi y α β t = xiCont y α β t := by
  have hn : ¬ (0 < t) := not_lt.mpr ht.le
  simp only [xiCont]; rw [if_neg hn, if_neg ht.ne]
  rw [xi_eq_eta hy (Or.inr ⟨hα, hβ, ht⟩), eta_swap]
  have habs : 0 < |t| := abs_pos.mpr ht.ne
  have := core_pos hy habs (a := β) (b := α) (by linarith)
  have e : -(π * t) = π * |t| := by rw [abs_of_neg ht]; ring
  rw [e]
  push_cast at this ⊢
  linear_combination (I ^ (β - α) * (Gamma β)⁻¹) * this

theorem eventually_strip2 (s : ℂ) (hs : 1 < s.re) :
    ∀ᶠ α in 𝓝 ((((s.re + 1) / 2 : ℝ)) : ℂ), 1 < α.re ∧ 0 < (s - α).re := by
  have ho : IsOpen {α : ℂ | 1 < α.re ∧ 0 < (s - α).re} := by
    show IsOpen ({α : ℂ | 1 < α.re} ∩ {α : ℂ | 0 < (s - α).re})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.sub continuous_id)))
  refine ho.mem_nhds ?_
  simp only [Set.mem_setOf_eq, Complex.ofReal_re, Complex.sub_re]
  constructor <;> linarith

/-- **Miyake, Theorem 7.2.5 (1).** For $y > 0$ and $\operatorname{Re}(\alpha+\beta) > 1$,
$\xi(y;\alpha,\beta;t)$ is given by `xiCont`. -/
@[kb "miyake1989" "Theorem 7.2.5 (1), p. 281"]
theorem xi_eq_xiCont {y : ℝ} (hy : 0 < y) {α β : ℂ} (h : 1 < (α + β).re) (t : ℝ) :
    xi y α β t = xiCont y α β t := by
  have hs : 1 < (α + β).re := h
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hG : Differentiable ℂ (fun a : ℂ ↦ xiCont y a (α + β - a) t) :=
      Differentiable.comp (g := fun p : ℂ × ℂ ↦ xiCont y p.1 p.2 t)
        (f := fun a : ℂ ↦ ((a, α + β - a) : ℂ × ℂ)) (differentiable_xiCont_neg hy ht)
        (by fun_prop)
    have := xi_one_var hy t hs hG (α₀ := ((((α + β).re + 1) / 2 : ℝ) : ℂ))
      (by filter_upwards [eventually_strip2 (α + β) hs] with a ha
          exact xi_neg_strip hy ht ha.1 ha.2) α
    simpa using this
  · subst ht
    rw [xi_zero hy h]
    simp only [xiCont]
    rw [if_neg (lt_irrefl _)]
    simp only [↓reduceIte]
    have hπ := Real.pi_pos
    have key : (2 * (π : ℂ)) * ((2 * y : ℝ) : ℂ) ^ (1 - α - β) =
        ((2 * π : ℝ) : ℂ) ^ (α + β) * ((4 * π * y : ℝ) : ℂ) ^ (1 - α - β) := by
      have h4 : (4 * π * y : ℝ) = (2 * π) * (2 * y) := by ring
      have hne : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
      rw [h4, cpow_mul_real' (c := 2 * π) (d := 2 * y) (by positivity) (by positivity), ← mul_assoc,
        ← Complex.cpow_add _ _ hne,
        show α + β + (1 - α - β) = 1 by ring, Complex.cpow_one]
      push_cast; ring
    linear_combination (I ^ (β - α) * (Gamma α)⁻¹ * (Gamma β)⁻¹ * Gamma (α + β - 1)) * key
  · have hG : Differentiable ℂ (fun a : ℂ ↦ xiCont y a (α + β - a) t) :=
      Differentiable.comp (g := fun p : ℂ × ℂ ↦ xiCont y p.1 p.2 t)
        (f := fun a : ℂ ↦ ((a, α + β - a) : ℂ × ℂ)) (differentiable_xiCont_pos hy ht)
        (by fun_prop)
    have := xi_one_var hy t hs hG (α₀ := ((((α + β).re - 1) / 2 : ℝ) : ℂ))
      (by filter_upwards [eventually_strip (α + β) hs] with a ha
          exact xi_pos_strip hy ht ha.1 ha.2) α
    simpa using this

/-- **Miyake, Theorem 7.2.5 (2)**, $t \ne 0$: the continuation of $\xi(y;\alpha,\beta;t)$ is holomorphic on
$\mathbb C \times \mathbb C$. -/
@[kb "miyake1989" "Theorem 7.2.5 (2), p. 281"]
theorem differentiable_xiCont {y : ℝ} (hy : 0 < y) {t : ℝ} (ht : t ≠ 0) :
    Differentiable ℂ (fun p : ℂ × ℂ ↦ xiCont y p.1 p.2 t) := by
  rcases lt_or_gt_of_ne ht with h | h
  · exact differentiable_xiCont_neg hy h
  · exact differentiable_xiCont_pos hy h

/-- **Miyake, Theorem 7.2.5 (2)**, $t = 0$: $\Gamma(\alpha+\beta-1)^{-1}\xi(y;\alpha,\beta;0)$ is holomorphic on
$\mathbb C \times \mathbb C$, i.e. the continuation is $\Gamma(\alpha+\beta-1)$ times an entire function. -/
@[kb "miyake1989" "Theorem 7.2.5 (2), p. 281"]
theorem xiCont_zero_eq_Gamma_mul {y : ℝ} (hy : 0 < y) :
    ∃ h : ℂ × ℂ → ℂ, Differentiable ℂ h ∧ ∀ α β : ℂ, xiCont y α β 0 = Gamma (α + β - 1) * h (α, β) := by
  have hπ := Real.pi_pos
  refine ⟨fun p ↦ I ^ (p.2 - p.1) * ((2 * π : ℝ) : ℂ) ^ (p.1 + p.2) * (Gamma p.1)⁻¹ *
    (Gamma p.2)⁻¹ * ((4 * π * y : ℝ) : ℂ) ^ (1 - p.1 - p.2), ?_, fun α β ↦ ?_⟩
  · have h1 : Differentiable ℂ (fun p : ℂ × ℂ ↦ I ^ (p.2 - p.1)) :=
      Differentiable.const_cpow (by fun_prop) (Or.inl Complex.I_ne_zero)
    have h2 : Differentiable ℂ (fun p : ℂ × ℂ ↦ ((2 * π : ℝ) : ℂ) ^ (p.1 + p.2)) :=
      Differentiable.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)))
    have h3 : Differentiable ℂ (fun p : ℂ × ℂ ↦ (Gamma p.1)⁻¹) :=
      differentiable_one_div_Gamma.comp differentiable_fst
    have h4 : Differentiable ℂ (fun p : ℂ × ℂ ↦ (Gamma p.2)⁻¹) :=
      differentiable_one_div_Gamma.comp differentiable_snd
    have h5 : Differentiable ℂ (fun p : ℂ × ℂ ↦ ((4 * π * y : ℝ) : ℂ) ^ (1 - p.1 - p.2)) :=
      Differentiable.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast (by positivity : (4 * π * y : ℝ) ≠ 0)))
    exact ((((h1.mul h2).mul h3).mul h4).mul h5)
  · simp only [xiCont]
    rw [if_neg (lt_irrefl _)]
    simp only [↓reduceIte]
    ring

end ModularFormsKB.Miyake.HeckeTrick
