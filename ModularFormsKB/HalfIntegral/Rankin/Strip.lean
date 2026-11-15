/-
# The strip identity of the Rankin integral

With $G_\psi$ = `rankinKernel k ψ t f`
$= f\,\overline{\theta_{\psi,t}}\,y^{(k+\nu+1)/2}$ and $s = (w-k+1)/2$:
- `stripMellin_rankinKernel`: $\int_0^\infty\!\int_0^1 G_\psi\,y^{s-2}\,dx\,dy =
  2\Gamma(\tfrac{w+\nu}2)(4\pi t)^{-(w+\nu)/2}\sum_m\psi(m)a(tm^2)m^{-w}$ for $\operatorname{Re}w > k+\tfrac32$, given the
  line integral (`integral_mul_conj_thetaTwist`) and Hecke's bound;
- `integrableOn_rankinKernel_strip`: $|G_\psi|y^{\sigma-2}$ is integrable on $[0,1]\times(0,\infty)$ for $\sigma > 4$
  (the hypothesis of `RankinUnfolding`).
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import ModularFormsKB.HalfIntegral.Abstract.FourierLine
import ModularFormsKB.HalfIntegral.ShimuraTwist
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace ModularFormsKB.HalfIntegral

open Complex MeasureTheory Set
open scoped Real

local notation "ℍ" => UpperHalfPlane


private lemma stripPt_im' {x y : ℝ} (hy : 0 < y) : (stripPt x y).im = y := by
  rw [stripPt, dif_pos hy]
  show ((x : ℂ) + y * I).im = y
  simp

private lemma continuousOn_stripPt' :
    ContinuousOn (fun p : ℝ × ℝ ↦ stripPt p.1 p.2) {p : ℝ × ℝ | 0 < p.2} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : Continuous (fun p : {p : ℝ × ℝ | 0 < p.2} ↦
      (⟨((p.1.1 : ℝ) : ℂ) + (p.1.2 : ℝ) * I, by
        have : 0 < p.1.2 := p.2
        simpa using this⟩ : ℍ)) :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (by
      show Continuous fun p : {p : ℝ × ℝ | 0 < p.2} ↦ ((p.1.1 : ℝ) : ℂ) + (p.1.2 : ℝ) * I
      fun_prop)
  convert h using 1
  funext p
  have hp : 0 < p.1.2 := p.2
  simp [Set.domRestrict, stripPt, hp]

/-- Exponential decay of a `q`-series without constant term, on `Im ≥ 1`. -/
private lemma norm_le_of_one_le' {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) (ha0 : a 0 = 0) :
    ∃ S : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ S * Real.exp (-2 * π * τ.im) := by
  have hs := summable_of_hasQExp hf one_pos
  refine ⟨Real.exp (2 * π) * ∑' n : ℕ, ‖a n‖ * Real.exp (-2 * π * n * 1), fun τ hτ ↦ ?_⟩
  have hg := (hs.hasSum.mul_right (Real.exp (-2 * π * (τ.im - 1))))
  have hle := (hf τ).norm_le_of_bounded hg (fun n ↦ ?_)
  · refine hle.trans (le_of_eq ?_)
    rw [← tsum_mul_right]
    have : Real.exp (-2 * π * (τ.im - 1)) = Real.exp (2 * π) * Real.exp (-2 * π * τ.im) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, tsum_mul_right]; ring
  · rw [norm_mul, Complex.norm_exp]
    have hre : (2 * π * I * n * (τ : ℂ)).re = -2 * π * n * τ.im := by
      simp [Complex.mul_re, UpperHalfPlane.coe_im]
    rw [hre]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have := Real.pi_pos
      refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (show -2 * π * n * τ.im ≤ -2 * π * n * 1 + -2 * π * (τ.im - 1) by
          nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hτ)])) (norm_nonneg _)) (le_of_eq ?_)
      rw [Real.exp_add]; ring


private lemma integrableOn_cpow_exp' {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * (y : ℂ)))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := a.re - 1) (p := 1) (b := r)
    (by linarith) one_pos hr
  refine Integrable.mono' h ?_ ?_
  · exact (by fun_prop : Measurable fun y : ℝ ↦ (y : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * (y : ℂ)))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy ↦ ?_)
    have hy : 0 < y := hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_exp]
    simp [Real.rpow_one]

private lemma norm_integral_aux' {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    ∫ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * (y : ℂ)))‖ =
      (1 / r) ^ a.re * Real.Gamma a.re := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy : 0 < y := hy
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_exp]
  simp

private lemma real_aux' (x : ℝ) (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m) (z : ℝ) :
    (1 / (x * (m : ℝ) ^ 2)) ^ z = x ^ (-z) * (m : ℝ) ^ (-(2 * z)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
    Real.mul_rpow hx.le (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hm'.le]
  congr 1
  push_cast; ring

private lemma key_cpow' (x : ℝ) (hx : 0 < x) (m : ℕ) (hm : 1 ≤ m) (w : ℂ) (ν : ℕ) :
    (m : ℂ) ^ ν * (1 / ((x * (m : ℝ) ^ 2 : ℝ) : ℂ)) ^ ((w + ν) / 2) =
      (x : ℂ) ^ (-((w + ν) / 2)) / (m : ℂ) ^ w := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  set z : ℂ := (w + ν) / 2 with hz
  have h1 : (1 / ((x * (m : ℝ) ^ 2 : ℝ) : ℂ)) ^ z = ((x * (m : ℝ) ^ 2 : ℝ) : ℂ) ^ (-z) := by
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_pos.ne), Complex.cpow_neg]
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h2 : ((x * (m : ℝ) ^ 2 : ℝ) : ℂ) ^ (-z) = (x : ℂ) ^ (-z) * (m : ℂ) ^ (-z + -z) := by
    have e : ((x * (m : ℝ) ^ 2 : ℝ) : ℂ) = ((x * (m : ℝ) : ℝ) : ℂ) * ((m : ℝ) : ℂ) := by
      push_cast; ring
    have e1 : ((x * (m : ℝ) : ℝ) : ℂ) ^ (-z) = (x : ℂ) ^ (-z) * ((m : ℝ) : ℂ) ^ (-z) := by
      rw [← Complex.mul_cpow_ofReal_nonneg hx.le hmr, Complex.ofReal_mul]
    rw [e, Complex.mul_cpow_ofReal_nonneg (by positivity) hmr, e1, Complex.ofReal_natCast,
      Complex.cpow_add _ _ hm0, mul_assoc]
  rw [h1, h2, ← mul_assoc, mul_comm ((m : ℂ) ^ ν), mul_assoc, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hm0,
    div_eq_mul_inv, ← Complex.cpow_neg]
  congr 2
  rw [hz]; ring

/-- **The strip identity.** -/
theorem stripMellin_rankinKernel (k : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t)
    (f : ℍ → ℂ) (a : ℕ → ℂ) {C : ℝ} (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4))
    (ha0 : a 0 = 0)
    (hline : ∀ y : ℝ, 0 < y →
      ∫ x in (0 : ℝ)..1, f (stripPt x y) * (starRingEnd ℂ) (thetaTwist ψ t (stripPt x y)) =
        ∑' m : ℕ, 2 * (twist ψ (fun m ↦ a (t * m ^ 2)) m * (m : ℂ) ^ charParity ψ) *
          ((Real.exp (-4 * π * t * m ^ 2 * y) : ℝ) : ℂ))
    {w : ℂ} (hw : (k : ℝ) + 3 / 2 < w.re) :
    stripMellin (rankinKernel k ψ t f) (rankinS k w) =
      2 * Gamma ((w + charParity ψ) / 2) * (((4 * π * t : ℝ) : ℂ) ^ (-((w + charParity ψ) / 2))) *
        LSeries (twist ψ fun m ↦ a (t * m ^ 2)) w := by
  set ν := charParity ψ with hν
  set q : ℝ := 4 * π * t with hq
  have hqpos : 0 < q := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    positivity
  set β : ℝ := ((k + ν + 1 : ℕ) : ℝ) / 2 with hβ
  set s' : ℂ := (w + ν) / 2 with hs'
  have hs're : s'.re = (w.re + ν) / 2 := by simp [hs']
  have hs'pos : 0 < s'.re := by
    rw [hs're]
    have : (0 : ℝ) ≤ ν := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  set c : ℕ → ℂ := fun m ↦ 2 * (twist ψ (fun m ↦ a (t * m ^ 2)) m * (m : ℂ) ^ ν) with hc
  have hc0 : c 0 = 0 := by simp [hc, twist, ha0]
  set F : ℕ → ℝ → ℂ := fun m y ↦
    c m * ((y : ℂ) ^ (s' - 1) * cexp (-(((q * (m : ℝ) ^ 2 : ℝ) : ℂ) * (y : ℂ)))) with hF
  -- Step A: the integrand in y
  have hA : ∀ y : ℝ, 0 < y →
      (∫ x in (0 : ℝ)..1, rankinKernel k ψ t f (stripPt x y)) * (y : ℂ) ^ (rankinS k w - 2) =
        ∑' m : ℕ, F m y := by
    intro y hy
    have e1 : ∀ u : ℝ, rankinKernel k ψ t f (stripPt u y) =
        f (stripPt u y) * (starRingEnd ℂ) (thetaTwist ψ t (stripPt u y)) * ((y ^ β : ℝ) : ℂ) := by
      intro u; unfold rankinKernel; rw [stripPt_im' hy]
    simp only [e1]
    rw [intervalIntegral.integral_mul_const, hline y hy, ← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun m ↦ ?_
    have hyc : ((y ^ β : ℝ) : ℂ) * (y : ℂ) ^ (rankinS k w - 2) = (y : ℂ) ^ (s' - 1) := by
      rw [Complex.ofReal_cpow hy.le, ← Complex.cpow_add _ _ (by exact_mod_cast hy.ne')]
      congr 1
      simp only [rankinS, hs', hβ]; push_cast; ring
    have hexp : ((Real.exp (-4 * π * t * m ^ 2 * y) : ℝ) : ℂ) =
        cexp (-(((q * (m : ℝ) ^ 2 : ℝ) : ℂ) * (y : ℂ))) := by
      rw [Complex.ofReal_exp]; congr 1; simp only [hq]; push_cast; ring
    simp only [hF, hc]
    rw [hexp]
    linear_combination (2 * (twist ψ (fun m ↦ a (t * m ^ 2)) m * (m : ℂ) ^ ν) *
      cexp (-(((q * (m : ℝ) ^ 2 : ℝ) : ℂ) * (y : ℂ)))) * hyc
  -- Step B: integrability
  have hFint : ∀ m, Integrable (F m) (volume.restrict (Ioi (0 : ℝ))) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, hc0]
    · have hr : 0 < q * (m : ℝ) ^ 2 := by
        have : (0 : ℝ) < m := by exact_mod_cast hm
        positivity
      exact (integrableOn_cpow_exp' hs'pos hr).const_mul (c m)
  have hnormF : ∀ m, 1 ≤ m → ∫ y in Ioi (0 : ℝ), ‖F m y‖ =
      ‖c m‖ * ((1 / (q * (m : ℝ) ^ 2)) ^ s'.re * Real.Gamma s'.re) := by
    intro m hm
    have hr : 0 < q * (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    have hn : ∀ y, ‖F m y‖ = ‖c m‖ * ‖(y : ℂ) ^ (s' - 1) * cexp (-(((q * (m : ℝ) ^ 2 : ℝ) : ℂ) * (y : ℂ)))‖ :=
      fun y ↦ norm_mul _ _
    simp only [hn]
    rw [integral_const_mul, norm_integral_aux' hs'pos hr]
  have hnormF0 : ∫ y in Ioi (0 : ℝ), ‖F 0 y‖ = 0 := by simp [hF, hc0]
  have hsum : Summable fun m : ℕ ↦ ∫ y in Ioi (0 : ℝ), ‖F m y‖ := by
    have hC0 : 0 ≤ C := by
      have := ha 1 le_rfl
      simp at this
      exact le_trans (norm_nonneg _) this
    set κ : ℝ := ((2 * k + 1 : ℕ) : ℝ) / 4 with hκ
    set p : ℝ := (k : ℝ) + 1 / 2 - w.re with hp
    have hp1 : p < -1 := by simp only [hp]; linarith
    set K : ℝ := 2 * C * (t : ℝ) ^ κ * q ^ (-s'.re) * Real.Gamma s'.re with hK
    refine Summable.of_nonneg_of_le (fun m ↦ integral_nonneg fun y ↦ norm_nonneg _)
      (fun m ↦ ?_) ((Real.summable_nat_rpow.2 hp1).mul_left K)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [hnormF0]
      have : (0 : ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
      simp [this]
    · have hm1 : 1 ≤ m := hm
      have hmr : (0 : ℝ) < m := by exact_mod_cast hm
      rw [hnormF m hm1, real_aux' q hqpos m hm1 s'.re]
      have hcb : ‖c m‖ ≤ 2 * (C * (t : ℝ) ^ κ * (m : ℝ) ^ (2 * κ)) * (m : ℝ) ^ (ν : ℝ) := by
        have hψ : ‖ψ (m : ZMod r)‖ ≤ 1 := DirichletCharacter.norm_le_one ψ _
        have han := ha (t * m ^ 2) (by
          have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
          nlinarith)
        have h1 : ((t * m ^ 2 : ℕ) : ℝ) ^ κ = (t : ℝ) ^ κ * (m : ℝ) ^ (2 * κ) := by
          push_cast
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hmr.le]
          congr 2
        rw [h1] at han
        have h2 : ‖(m : ℂ) ^ ν‖ = (m : ℝ) ^ (ν : ℝ) := by
          rw [norm_pow, Complex.norm_natCast, Real.rpow_natCast]
        simp only [hc, twist, norm_mul]
        rw [h2]
        have h3 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h3]
        have hG : 0 ≤ (m : ℝ) ^ (ν : ℝ) := by positivity
        calc 2 * (‖ψ (m : ZMod r)‖ * ‖a (t * m ^ 2)‖ * (m : ℝ) ^ (ν : ℝ))
            ≤ 2 * (1 * (C * ((t : ℝ) ^ κ * (m : ℝ) ^ (2 * κ))) * (m : ℝ) ^ (ν : ℝ)) := by
              gcongr
          _ = _ := by ring
      have hΓ : 0 ≤ Real.Gamma s'.re := (Real.Gamma_pos_of_pos hs'pos).le
      calc ‖c m‖ * (q ^ (-s'.re) * (m : ℝ) ^ (-(2 * s'.re)) * Real.Gamma s'.re)
          ≤ (2 * (C * (t : ℝ) ^ κ * (m : ℝ) ^ (2 * κ)) * (m : ℝ) ^ (ν : ℝ)) *
              (q ^ (-s'.re) * (m : ℝ) ^ (-(2 * s'.re)) * Real.Gamma s'.re) := by
            gcongr
        _ = K * (((m : ℝ) ^ (2 * κ) * (m : ℝ) ^ (ν : ℝ)) * (m : ℝ) ^ (-(2 * s'.re))) := by
            rw [hK]; ring
        _ = K * (m : ℝ) ^ p := by
            rw [← Real.rpow_add hmr, ← Real.rpow_add hmr]
            congr 2
            rw [hp, hκ, hs're]; push_cast; ring
  -- Step C: interchange and evaluation
  have hint : stripMellin (rankinKernel k ψ t f) (rankinS k w) = ∑' m : ℕ, ∫ y in Ioi (0 : ℝ), F m y := by
    rw [integral_tsum_of_summable_integral_norm hFint hsum, stripMellin]
    exact setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ hA y hy
  have hval : ∀ m : ℕ, 1 ≤ m → ∫ y in Ioi (0 : ℝ), F m y =
      c m * ((1 / ((q * (m : ℝ) ^ 2 : ℝ) : ℂ)) ^ s' * Gamma s') := by
    intro m hm
    have hr : 0 < q * (m : ℝ) ^ 2 := by
      have : (0 : ℝ) < m := by exact_mod_cast hm
      positivity
    simp only [hF]
    rw [integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi hs'pos hr]
  rw [hint, LSeries, ← tsum_mul_left]
  refine tsum_congr fun m ↦ ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hF, hc0, LSeries.term_zero]
  · rw [hval m hm, LSeries.term_of_ne_zero (by omega)]
    have := key_cpow' q hqpos m hm w ν
    simp only [hc]
    linear_combination (2 * twist ψ (fun m ↦ a (t * m ^ 2)) m * Gamma s') * this

/-- **Integrability on the strip** of $|G_\psi|\,y^{\sigma-2}$, $\sigma > 4$. -/
theorem integrableOn_rankinKernel_strip (k : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t)
    {f : ℍ → ℂ} (hfc : Continuous f) {a : ℕ → ℂ} (hf : Abstract.HasQExp f a) (ha0 : a 0 = 0)
    (hφ : ∃ C : ℝ, ∀ τ : ℍ, τ.im ^ (((2 * k + 1 : ℕ) : ℝ) / 4) * ‖f τ‖ ≤ C)
    (hθc : Continuous fun τ : ℍ ↦ thetaTwist ψ t τ)
    (hθ : ∃ C : ℝ, ∀ τ : ℍ, ‖thetaTwist ψ t τ‖ ≤ C * (1 + τ.im ^ (-2 : ℝ)))
    {σ : ℝ} (hσ : 4 < σ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ‖rankinKernel k ψ t f (stripPt p.1 p.2)‖ * p.2 ^ (σ - 2))
      (Icc 0 1 ×ˢ Ioi 0) := by
  obtain ⟨S, hS⟩ := norm_le_of_one_le' hf ha0
  obtain ⟨C1, hC1⟩ := hφ
  obtain ⟨C2, hC2⟩ := hθ
  set ν := charParity ψ with hν
  set κ : ℝ := ((2 * k + 1 : ℕ) : ℝ) / 4 with hκ
  set β : ℝ := ((k + ν + 1 : ℕ) : ℝ) / 2 with hβ
  have hκ0 : 0 ≤ κ := by positivity
  have hβκ : κ ≤ β := by
    simp only [hκ, hβ]; push_cast
    have : (0 : ℝ) ≤ ν := Nat.cast_nonneg _
    linarith
  set e2 : ℝ := β + (σ - 2) with he2def
  set e1 : ℝ := e2 + (-κ) + (-2) with he1def
  have he1 : -1 < e1 := by simp only [he1def, he2def]; linarith
  have he2 : -1 < e2 := by simp only [he2def]; linarith
  set K1 : ℝ := |C1| * (|C2| * 2) with hK1
  set K2 : ℝ := |S| * (|C2| * 2) with hK2
  set H : ℝ → ℝ := fun y ↦ K1 * (Ioc (0 : ℝ) 1).indicator (fun y ↦ y ^ e1) y +
    K2 * (y ^ e2 * Real.exp (-(2 * π) * y)) with hH
  have hI1 : Integrable ((Ioc (0 : ℝ) 1).indicator (fun y ↦ y ^ e1)) volume := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) he1).1
      |> fun h => by simpa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] using h
  have hI2 : IntegrableOn (fun y : ℝ ↦ y ^ e2 * Real.exp (-(2 * π) * y)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow he2 one_pos (b := 2 * π) (by positivity)
    refine this.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have hHint : Integrable H (volume.restrict (Ioi (0 : ℝ))) :=
    ((hI1.integrableOn.const_mul K1).add (hI2.const_mul K2))
  have hprod : IntegrableOn (fun p : ℝ × ℝ ↦ H p.2) (Icc 0 1 ×ˢ Ioi 0) := by
    have := (integrable_const (1 : ℝ) (μ := volume.restrict (Icc (0 : ℝ) 1))).mul_prod hHint
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa using this
  have hGc : Continuous (rankinKernel k ψ t f) := by
    unfold rankinKernel
    refine (hfc.mul (Complex.continuous_conj.comp hθc)).mul (Complex.continuous_ofReal.comp ?_)
    exact UpperHalfPlane.continuous_im.rpow_const (fun _ ↦ Or.inr (by positivity))
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ‖rankinKernel k ψ t f (stripPt p.1 p.2)‖ * p.2 ^ (σ - 2))
      (volume.restrict (Icc 0 1 ×ˢ Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Icc.prod measurableSet_Ioi)
    refine ContinuousOn.mono (s := {p : ℝ × ℝ | 0 < p.2}) ?_ (fun p hp ↦ ?_)
    · exact ((hGc.comp_continuousOn continuousOn_stripPt').norm).mul
        ((continuous_snd.continuousOn).rpow_const (fun p hp ↦ Or.inl (ne_of_gt hp)))
    · exact hp.2
  refine Integrable.mono' hprod hmeas ?_
  refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Ioi)).2 (Filter.Eventually.of_forall ?_)
  rintro ⟨x, y⟩ ⟨-, hy⟩
  have hy : 0 < y := hy
  set z := stripPt x y with hzdef
  have hz : z.im = y := stripPt_im' hy
  have hfn : ‖f z‖ ≤ |C1| * y ^ (-κ) := by
    have h1 := hC1 z
    rw [hz] at h1
    have hq : 0 < y ^ κ := Real.rpow_pos_of_pos hy _
    rw [Real.rpow_neg hy.le, ← div_eq_mul_inv]
    rw [le_div_iff₀ hq]
    nlinarith [le_abs_self C1, norm_nonneg (f z)]
  have hθn : ‖thetaTwist ψ t z‖ ≤ |C2| * (1 + y ^ (-2 : ℝ)) := by
    have h1 := hC2 z
    rw [hz] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity))
  have hP : y ^ β * y ^ (σ - 2) = y ^ e2 := (Real.rpow_add hy _ _).symm
  have hnorm : ‖rankinKernel k ψ t f z‖ * y ^ (σ - 2) = ‖f z‖ * ‖thetaTwist ψ t z‖ * y ^ e2 := by
    unfold rankinKernel
    rw [norm_mul, norm_mul, Complex.norm_real, RCLike.norm_conj, hz, Real.norm_of_nonneg (by positivity), ← hP]
    ring
  rw [Real.norm_of_nonneg (by positivity), hnorm]
  by_cases hy1 : y ≤ 1
  · have hu : 1 ≤ y ^ (-2 : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1 (by norm_num)
    have hE : y ^ e1 = y ^ e2 * y ^ (-κ) * y ^ (-2 : ℝ) := by
      rw [he1def, Real.rpow_add hy, Real.rpow_add hy]
    have hind : (Ioc (0 : ℝ) 1).indicator (fun y ↦ y ^ e1) y = y ^ e1 :=
      Set.indicator_of_mem (show y ∈ Ioc (0 : ℝ) 1 from ⟨hy, hy1⟩) _
    have hpos : 0 ≤ K2 * (y ^ e2 * Real.exp (-(2 * π) * y)) := by positivity
    simp only [hH]
    rw [hind]
    refine le_trans ?_ (le_add_of_nonneg_right hpos)
    calc ‖f z‖ * ‖thetaTwist ψ t z‖ * y ^ e2
        ≤ (|C1| * y ^ (-κ)) * (|C2| * (2 * y ^ (-2 : ℝ))) * y ^ e2 := by
          gcongr
          exact hθn.trans (by nlinarith [abs_nonneg C2])
      _ = K1 * y ^ e1 := by rw [hE, hK1]; ring
  · rw [not_le] at hy1
    have hu : y ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by norm_num)
    have hind : (Ioc (0 : ℝ) 1).indicator (fun y ↦ y ^ e1) y = 0 :=
      Set.indicator_of_notMem (show y ∉ Ioc (0 : ℝ) 1 from fun h ↦ absurd h.2 (not_le.2 hy1)) _
    have hfS : ‖f z‖ ≤ |S| * Real.exp (-2 * π * y) := by
      have := hS z (by rw [hz]; exact hy1.le)
      rw [hz] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self S) (Real.exp_pos _).le)
    simp only [hH]
    rw [hind, mul_zero, zero_add]
    calc ‖f z‖ * ‖thetaTwist ψ t z‖ * y ^ e2
        ≤ (|S| * Real.exp (-2 * π * y)) * (|C2| * 2) * y ^ e2 := by
          gcongr
          exact hθn.trans (by nlinarith [abs_nonneg C2])
      _ = K2 * (y ^ e2 * Real.exp (-(2 * π) * y)) := by
          rw [hK2, show -(2 * π) * y = -2 * π * y by ring]; ring

end ModularFormsKB.HalfIntegral
