import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import ModularFormsKB.Miyake.Sec4_3.Defs
import ModularFormsKB.Citation
/-!
# Milne, Chapter 9: the Mellin transform (Proposition 9.1, Theorem 9.2)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 9, pdf pp. 101–102.

## Items

- The gamma function (D103, in Mathlib): `Complex.Gamma`, with the properties Milne lists restated in
  `ModularFormsKB.Milne.gamma_properties`.
- **Proposition 9.1** (Mellin inversion for $e^{-x}$): `ModularFormsKB.Milne.exp_neg_eq_contour_integral_Gamma`.
- **Theorem 9.2** (Mellin transform of $\sum a_n e^{-nx}$ and its inversion):
  `ModularFormsKB.Milne.gamma_mul_LSeries_eq_integral` (formula $(*)$) and
  `ModularFormsKB.Milne.expSeries_eq_contour_integral` (formula $(**)$).
- The Mellin transform (D104, in Mathlib): `mellin`, `mellinInv`; "the functions $f(x)$ and $\Gamma(s)\varphi(s)$
  are called the Mellin transforms of each other" is the pair of formulas of Theorem 9.2.
- **Bounded on vertical strips** (D105): `ModularFormsKB.Milne.BoundedOnVerticalStrips`, with the comparison
  `ModularFormsKB.Milne.boundedOnVerticalStrips_iff` with the repository's `Miyake.BoundedOnVerticalStrips` for
  continuous functions.

## Conventions

A vertical line integral $\int_{c-i\infty}^{c+i\infty} g(s)\,ds$ (taken upwards) is written with the parametrization
$s = c + iy$, $ds = i\,dy$, as `I * ∫ y : ℝ, g (c + y * I)`. Mathlib's `mellinInv c F x` is
$\frac{1}{2\pi}\int_{\mathbb R} x^{-(c+iy)}F(c+iy)\,dy$, the same quantity as $\frac{1}{2\pi i}\int_{c-i\infty}^{c+i\infty}
x^{-s}F(s)\,ds$.

Milne's Dirichlet series $\varphi(s) = \sum_{n \ge 1} a_n n^{-s}$ is Mathlib's `LSeries a s` (the value `a 0` is not
used); $f(x) = \sum_{n\ge1} a_n e^{-nx}$ is `expSeries a x`.
-/

open Complex Filter Asymptotics MeasureTheory Set
open scoped Real Topology

noncomputable section

namespace ModularFormsKB.Milne

/-- **The gamma function** (Milne, Section 9, pdf p. 101; D103, in Mathlib as `Complex.Gamma`): the properties Milne
lists after the definition $\Gamma(s) = \int_0^\infty e^{-x}x^{s-1}\,dx$ ($\operatorname{Re} s > 0$):
$\Gamma(s+1) = s\Gamma(s)$ ($s \ne 0$), $\Gamma(1) = 1$, $\Gamma(1/2) = \sqrt\pi$, $\Gamma$ is holomorphic away from
$0, -1, -2, \dots$, and $s\Gamma(s) \to 1$ as $s \to 0$ (the residue at $0$). Mathlib's `Complex.Gamma` is the
meromorphic continuation (with junk value at the poles). -/
@[kb "milne2017mf" "Section 9, the gamma function and its properties (pdf p. 101)"]
theorem gamma_properties :
    (∀ s : ℂ, 0 < s.re → Gamma s = ∫ x in Ioi (0 : ℝ), ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1)) ∧
    (∀ s : ℂ, s ≠ 0 → Gamma (s + 1) = s * Gamma s) ∧ Gamma 1 = 1 ∧
    Gamma (1 / 2) = (√π : ℝ) ∧ (∀ s : ℂ, (∀ m : ℕ, s ≠ -m) → DifferentiableAt ℂ Gamma s) ∧
    Tendsto (fun z : ℂ ↦ z * Gamma z) (𝓝[≠] 0) (𝓝 1) := by
  refine ⟨fun s hs => ?_, fun s hs => Gamma_add_one s hs, Gamma_one, ?_,
    fun s hs => Complex.differentiableAt_Gamma s hs, Complex.tendsto_self_mul_Gamma_nhds_zero⟩
  · exact Gamma_eq_integral hs
  · rw [Gamma_one_half_eq, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num

/-- The Mellin transform of $e^{-t}$ is $\Gamma$ for $\operatorname{Re} s > 0$. -/
private lemma mellin_exp_neg {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s = Gamma s := by
  rw [Gamma_eq_integral hs, GammaIntegral, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul]
  ring

/-- The Mellin integral of $e^{-t}$ converges for $\operatorname{Re} s > 0$. -/
private lemma mellinConvergent_exp_neg {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s := by
  unfold MellinConvergent
  refine (Complex.GammaIntegral_convergent hs).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  ring

/-- $|\Gamma(s)| \le \Gamma(\operatorname{Re} s)$ for $\operatorname{Re} s > 0$. -/
private lemma norm_Gamma_le_real {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, GammaIntegral, Real.Gamma_eq_integral hs]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (setIntegral_congr_fun
    measurableSet_Ioi fun t ht => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
    norm_cpow_eq_rpow_re_of_pos ht]
  simp

/-- $|\Gamma(c+iy)| \le \Gamma(c+2)/(m(1+y^2))$ for $c > 0$, where $m = \min(c^2, 1)$. -/
private lemma norm_Gamma_line_le {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ‖Gamma (c + y * I)‖ ≤ Real.Gamma (c + 2) / (min (c ^ 2) 1 * (1 + y ^ 2)) := by
  set s : ℂ := c + y * I with hsdef
  have hre : s.re = c := by simp [hsdef]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp [hre] at this
    linarith
  have h2 : Gamma (s + 2) = (s + 1) * (s * Gamma s) := by
    have : s + 2 = (s + 1) + 1 := by ring
    rw [this, Gamma_add_one _ hs1, Gamma_add_one _ hs0]
  have hG : ‖Gamma (s + 2)‖ ≤ Real.Gamma (c + 2) := by
    have := norm_Gamma_le_real (s := s + 2) (by simp [hre]; linarith)
    simpa [hre] using this
  have hn1 : ‖s‖ ^ 2 = c ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hsdef]
    ring
  have hn2 : ‖s + 1‖ ^ 2 = (c + 1) ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hsdef]
    ring
  have hle : ‖s‖ ≤ ‖s + 1‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [hn1, hn2]
    nlinarith
  have hmpos : 0 < min (c ^ 2) 1 := lt_min (pow_pos hc 2) one_pos
  have hprod : min (c ^ 2) 1 * (1 + y ^ 2) ≤ ‖s‖ * ‖s + 1‖ := by
    calc min (c ^ 2) 1 * (1 + y ^ 2) ≤ c ^ 2 + y ^ 2 := by
          nlinarith [min_le_left (c ^ 2) 1, mul_le_mul_of_nonneg_right (min_le_right (c ^ 2) 1)
            (sq_nonneg y)]
      _ = ‖s‖ * ‖s‖ := by rw [← hn1, sq]
      _ ≤ ‖s‖ * ‖s + 1‖ := by gcongr
  have hm : 0 < min (c ^ 2) 1 * (1 + y ^ 2) := mul_pos hmpos (by positivity)
  rw [le_div_iff₀ hm]
  calc ‖Gamma s‖ * (min (c ^ 2) 1 * (1 + y ^ 2)) ≤ ‖Gamma s‖ * (‖s‖ * ‖s + 1‖) := by gcongr
    _ = ‖Gamma (s + 2)‖ := by rw [h2, norm_mul, norm_mul]; ring
    _ ≤ _ := hG

/-- $y \mapsto \Gamma(c+iy)g(y)$ is integrable for $c > 0$ and $g$ continuous and bounded. -/
private lemma integrable_Gamma_mul {c : ℝ} (hc : 0 < c) {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ y, ‖g y‖ ≤ B) : Integrable fun y : ℝ => Gamma (c + y * I) * g y := by
  have hcont : Continuous fun y : ℝ => Gamma (c + y * I) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    refine (Complex.differentiableAt_Gamma _ (fun m h => ?_)).continuousAt.comp
      (f := fun y : ℝ => (c : ℂ) + y * I) (by fun_prop)
    have := congrArg Complex.re h
    simp at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hmpos : 0 < min (c ^ 2) 1 := lt_min (pow_pos hc 2) one_pos
  refine (integrable_inv_one_add_sq.const_mul (Real.Gamma (c + 2) / min (c ^ 2) 1 * B)).mono'
    (hcont.mul hg).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  calc ‖Gamma (c + y * I)‖ * ‖g y‖
      ≤ (Real.Gamma (c + 2) / (min (c ^ 2) 1 * (1 + y ^ 2))) * B :=
        mul_le_mul (norm_Gamma_line_le hc y) (hB y) (norm_nonneg _) (by
          have := Real.Gamma_pos_of_pos (show 0 < c + 2 by linarith)
          positivity)
    _ = Real.Gamma (c + 2) / min (c ^ 2) 1 * B * (1 + y ^ 2)⁻¹ := by
        field_simp

/-- **Milne, Proposition 9.1** (Mellin inversion formula): for every real $c > 0$ and $x > 0$,
$$e^{-x} = \frac{1}{2\pi i}\int_{c-i\infty}^{c+i\infty}\Gamma(s)\,x^{-s}\,ds,$$
the integral taken upwards on the vertical line $\operatorname{Re} s = c$ (written with $s = c + iy$, $ds = i\,dy$).
The integral converges absolutely: $|\Gamma(c + iy)| = O(1/(1+y^2))$ from $\Gamma(s) = \Gamma(s+2)/(s(s+1))$. -/
@[kb "milne2017mf" "Section 9, Proposition 9.1 (pdf p. 101)"]
theorem exp_neg_eq_contour_integral_Gamma {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (Real.exp (-x) : ℂ) =
      1 / (2 * π * I) * (I * ∫ y : ℝ, Gamma (c + y * I) * (x : ℂ) ^ (-((c : ℂ) + y * I))) := by
  have hc' : 0 < (c : ℂ).re := by simpa using hc
  have hcont : Continuous fun y : ℝ => (x : ℂ) ^ (-((c : ℂ) + y * I)) := by
    refine Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
  have hnorm : ∀ y : ℝ, ‖(x : ℂ) ^ (-((c : ℂ) + y * I))‖ ≤ x ^ (-c) := by
    intro y
    rw [norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have key := mellinInv_mellin_eq c (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) hx
    (mellinConvergent_exp_neg hc') (by
      unfold VerticalIntegrable
      have : (fun y : ℝ => mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) (c + y * I))
          = fun y : ℝ => Gamma (c + y * I) * 1 := by
        funext y
        rw [mul_one, mellin_exp_neg (by simpa using hc)]
      rw [this]
      exact integrable_Gamma_mul hc continuous_const (B := 1) (fun _ => by simp))
    (by fun_prop)
  rw [mellinInv] at key
  have e : ∀ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) • mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ))
      (c + y * I) = Gamma (c + y * I) * (x : ℂ) ^ (-((c : ℂ) + y * I)) := by
    intro y
    rw [smul_eq_mul, mellin_exp_neg (by simpa using hc), mul_comm]
  simp_rw [e] at key
  rw [← key, Complex.real_smul]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize (∫ y : ℝ, Gamma (c + y * I) * (x : ℂ) ^ (-((c : ℂ) + y * I))) = J
  push_cast
  field_simp

/-- The function $f(x) = \sum_{n \ge 1} a_n e^{-nx}$ of Theorem 9.2 (the term `a 0` is not used). -/
def expSeries (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, (if n = 0 then 0 else a n) * Real.exp (-(n * x))

/-- Polynomial bound on coefficients gives summability of `‖a n‖ e^{-n r}`. -/
private lemma summable_norm_mul_exp {a : ℕ → ℂ} {σ C : ℝ}
    (hC : ∀ n : ℕ, n ≠ 0 → ‖a n‖ ≤ C * (n : ℝ) ^ σ) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => ‖(if n = 0 then 0 else a n)‖ * Real.exp (-(n * r)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_pow_mul_exp_neg_nat_mul ⌈σ⌉₊ hr).mul_left |C|)
  by_cases hn : n = 0
  · subst hn
    simp only [ite_true, norm_zero, zero_mul]
    positivity
  · simp only [hn, ite_false]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hpow : (n : ℝ) ^ σ ≤ (n : ℝ) ^ (⌈σ⌉₊ : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil σ)
    have h1 : ‖a n‖ ≤ |C| * (n : ℝ) ^ (⌈σ⌉₊ : ℕ) :=
      (hC n hn).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hpow (abs_nonneg C)))
    calc ‖a n‖ * Real.exp (-(n * r)) ≤ (|C| * (n : ℝ) ^ (⌈σ⌉₊ : ℕ)) * Real.exp (-(n * r)) := by
          gcongr
      _ = |C| * ((n : ℝ) ^ (⌈σ⌉₊ : ℕ) * Real.exp (-r * n)) := by
          rw [show -r * (n : ℝ) = -((n : ℝ) * r) by ring]; ring

/-- Summability of the terms of `expSeries`. -/
private lemma summable_expTerm {a : ℕ → ℂ} {σ C : ℝ}
    (hC : ∀ n : ℕ, n ≠ 0 → ‖a n‖ ≤ C * (n : ℝ) ^ σ) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ => (if n = 0 then 0 else a n) * ((Real.exp (-(n * r)) : ℝ) : ℂ) := by
  refine Summable.of_norm ?_
  convert summable_norm_mul_exp hC hr using 2 with n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- `expSeries` is continuous on `(0, ∞)`. -/
private lemma continuousAt_expSeries {a : ℕ → ℂ} {σ C : ℝ}
    (hC : ∀ n : ℕ, n ≠ 0 → ‖a n‖ ≤ C * (n : ℝ) ^ σ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (expSeries a) x := by
  have hu := summable_norm_mul_exp hC (half_pos hx)
  have hcont : ContinuousOn (fun y : ℝ => ∑' n : ℕ,
      (if n = 0 then 0 else a n) * ((Real.exp (-(n * y)) : ℝ) : ℂ)) (Ioi (x / 2)) := by
    refine continuousOn_tsum (u := fun n : ℕ =>
      ‖(if n = 0 then 0 else a n)‖ * Real.exp (-(n * (x / 2)))) (fun n => ?_) hu
      (fun n y hy => ?_)
    · exact (by fun_prop : Continuous fun y : ℝ =>
        (if n = 0 then 0 else a n) * ((Real.exp (-(n * y)) : ℝ) : ℂ)).continuousOn
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      gcongr
      have : x / 2 < y := hy
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
  exact hcont.continuousAt (Ioi_mem_nhds (by linarith))

/-- The L-series is summable at `s` given `a = O(n^M)` and `M + 1 < Re s`. -/
private lemma lseriesSummable_of_bigO {a : ℕ → ℂ} {M : ℝ}
    (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ M) {s : ℂ} (hsM : M + 1 < s.re) :
    LSeriesSummable a s :=
  LSeriesSummable_of_isBigO_rpow hsM (by simpa using ha)

/-- Summability of `‖a n‖ / n^σ` from summability of the L-series. -/
private lemma summable_norm_div {a : ℕ → ℂ} {s : ℂ} (hL : LSeriesSummable a s) :
    Summable fun n : ℕ => ‖(if n = 0 then 0 else a n)‖ / (n : ℝ) ^ s.re := by
  refine hL.norm.congr (fun n => ?_)
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.norm_term_eq]
    simp [hn]

/-- The Mellin transform of `expSeries a` is `Γ(s) L(s)` (formula `(*)`). -/
private lemma mellin_expSeries {a : ℕ → ℂ} {s : ℂ} (hs0 : 0 < s.re) (hL : LSeriesSummable a s) :
    mellin (expSeries a) s = Gamma s * LSeries a s := by
  obtain ⟨C, hC⟩ := hL.le_const_mul_rpow
  have h := hasSum_mellin (a := fun n : ℕ => if n = 0 then (0 : ℂ) else a n)
    (p := fun n : ℕ => (n : ℝ)) (F := expSeries a) (s := s)
    (fun n => by
      by_cases hn : n = 0
      · left; simp [hn]
      · right; exact_mod_cast Nat.pos_of_ne_zero hn) hs0
    (fun t ht => by
      have hs := summable_expTerm hC (show 0 < t from ht)
      simp only [neg_mul]
      exact hs.hasSum)
    (summable_norm_div hL)
  rw [← h.tsum_eq, LSeries, ← tsum_mul_left]
  congr 1
  ext n
  by_cases hn : n = 0
  · simp [hn, LSeries.term]
  · simp [hn, mul_div_assoc]

/-- The Mellin integral of `expSeries a` converges. -/
private lemma mellinConvergent_expSeries {a : ℕ → ℂ} {s : ℂ} (hs0 : 0 < s.re)
    (hL : LSeriesSummable a s) : MellinConvergent (expSeries a) s := by
  obtain ⟨C, hC⟩ := hL.le_const_mul_rpow
  by_cases hz : ∀ n : ℕ, (if n = 0 then (0 : ℂ) else a n) = 0
  · have : expSeries a = fun _ => 0 := by
      funext t
      simp [expSeries, hz]
    rw [this]
    unfold MellinConvergent
    simp
  -- the majorant `G t = ∑ ‖a n‖ e^{-n t}`
  obtain ⟨n₀, hn₀⟩ := not_forall.1 hz
  have hn₀' : n₀ ≠ 0 := fun h => hn₀ (by simp [h])
  have hn₀a : a n₀ ≠ 0 := fun h => hn₀ (by simp [h])
  set σ := s.re with hσ
  let G : ℝ → ℝ := fun t => ∑' n : ℕ, ‖(if n = 0 then 0 else a n)‖ * Real.exp (-(n * t))
  have hGsum : ∀ t : ℝ, 0 < t → HasSum (fun n : ℕ =>
      ‖(if n = 0 then 0 else a n)‖ * Real.exp (-(n * t))) (G t) :=
    fun t ht => (summable_norm_mul_exp hC ht).hasSum
  have h := hasSum_mellin (a := fun n : ℕ => (((‖(if n = 0 then 0 else a n)‖ : ℝ)) : ℂ))
    (p := fun n : ℕ => (n : ℝ)) (F := fun t => ((G t : ℝ) : ℂ)) (s := (σ : ℂ))
    (fun n => by
      by_cases hn : n = 0
      · left; simp [hn]
      · right; exact_mod_cast Nat.pos_of_ne_zero hn) (by simpa using hs0)
    (fun t ht => by
      have := Complex.hasSum_ofReal.2 (hGsum t ht)
      simp only [neg_mul]
      convert this using 2 with n
      push_cast
      ring_nf)
    (by simpa using summable_norm_div hL)
  -- the transform of `G` is nonzero
  have hne : mellin (fun t => ((G t : ℝ) : ℂ)) (σ : ℂ) ≠ 0 := by
    intro h0
    have hre := Complex.hasSum_re h
    rw [h0] at hre
    have hr : ∀ n : ℕ, (Gamma (σ : ℂ) * (((‖(if n = 0 then 0 else a n)‖ : ℝ)) : ℂ) /
        ((n : ℝ) : ℂ) ^ (σ : ℂ)).re = Real.Gamma σ * ‖(if n = 0 then 0 else a n)‖ / (n : ℝ) ^ σ := by
      intro n
      rw [← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.Gamma_ofReal,
        ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    simp only [hr, Complex.zero_re] at hre
    have hnn : ∀ n : ℕ, 0 ≤ Real.Gamma σ * ‖(if n = 0 then 0 else a n)‖ / (n : ℝ) ^ σ :=
      fun n => by
        have := Real.Gamma_pos_of_pos (show 0 < σ from hs0)
        positivity
    have h00 := (hasSum_zero_iff_of_nonneg hnn).1 hre
    have := congrFun h00 n₀
    simp only [Pi.zero_apply] at this
    have hpos : 0 < Real.Gamma σ * ‖(if n₀ = 0 then 0 else a n₀)‖ / (n₀ : ℝ) ^ σ := by
      have := Real.Gamma_pos_of_pos (show 0 < σ from hs0)
      have hn1 : (0 : ℝ) < n₀ := by exact_mod_cast Nat.pos_of_ne_zero hn₀'
      simp only [hn₀', ite_false]
      positivity
    linarith
  have hGint : MellinConvergent (fun t => ((G t : ℝ) : ℂ)) (σ : ℂ) := by
    by_contra hcon
    exact hne (integral_undef hcon)
  -- domination
  unfold MellinConvergent at hGint ⊢
  refine hGint.norm.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ContinuousOn.smul (ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
      (fun t ht => Complex.ofReal_mem_slitPlane.2 ht))
      (fun t ht => (continuousAt_expSeries hC ht).continuousWithinAt)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : 0 < t := ht
    rw [norm_smul, norm_smul, norm_cpow_eq_rpow_re_of_pos ht', norm_cpow_eq_rpow_re_of_pos ht']
    simp only [sub_re, one_re, ofReal_re, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    rw [abs_of_nonneg (tsum_nonneg fun n => by positivity)]
    refine (norm_tsum_le_tsum_norm (summable_expTerm hC ht').norm).trans (le_of_eq ?_)
    refine tsum_congr fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- **Milne, Theorem 9.2, formula $(*)$.** Let $a_1, a_2, \dots$ be complex numbers with $a_n = O(n^M)$, and write
$f(x) = \sum_{n\ge1} a_n e^{-nx}$, $\varphi(s) = \sum_{n \ge 1} a_n n^{-s}$. Then
$$\Gamma(s)\varphi(s) = \int_0^\infty f(x)\,x^{s-1}\,dx\qquad(\operatorname{Re} s > \max(0, M+1)).$$
The right side is Mathlib's `mellin (expSeries a) s`. -/
@[kb "milne2017mf" "Section 9, Theorem 9.2, formula (*) (pdf p. 102)"]
theorem gamma_mul_LSeries_eq_integral {a : ℕ → ℂ} {M : ℝ} (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ M)
    {s : ℂ} (hs0 : 0 < s.re) (hsM : M + 1 < s.re) :
    Gamma s * LSeries a s = ∫ x in Ioi (0 : ℝ), expSeries a x * (x : ℂ) ^ (s - 1) := by
  have hL := lseriesSummable_of_bigO ha hsM
  rw [← mellin_expSeries hs0 hL, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul]
  ring

/-- **Milne, Theorem 9.2, formula $(**)$.** With $a_n = O(n^M)$, $f$, $\varphi$ as in
`gamma_mul_LSeries_eq_integral`: for $c > \max(0, M+1)$ and $x > 0$,
$$f(x) = \frac{1}{2\pi i}\int_{c-i\infty}^{c+i\infty}\Gamma(s)\varphi(s)\,x^{-s}\,ds .$$
(Milne writes the side condition as "$\Re(s) > 0$"; the variable is $x$, and the condition is $x > 0$.) -/
@[kb "milne2017mf" "Section 9, Theorem 9.2, formula (**) (pdf p. 102)"]
theorem expSeries_eq_contour_integral {a : ℕ → ℂ} {M : ℝ} (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ M)
    {c x : ℝ} (hc0 : 0 < c) (hcM : M + 1 < c) (hx : 0 < x) :
    expSeries a x = 1 / (2 * π * I) *
      (I * ∫ y : ℝ, Gamma (c + y * I) * LSeries a (c + y * I) * (x : ℂ) ^ (-((c : ℂ) + y * I))) := by
  have hs : ∀ y : ℝ, LSeriesSummable a ((c : ℂ) + y * I) := fun y =>
    lseriesSummable_of_bigO ha (by simpa using hcM)
  have hL : LSeriesSummable a (c : ℂ) := lseriesSummable_of_bigO ha (by simpa using hcM)
  obtain ⟨C, hC⟩ := hL.le_const_mul_rpow
  have hcont : Continuous fun y : ℝ => LSeries a ((c : ℂ) + y * I) := by
    refine continuous_tsum (u := fun n => ‖LSeries.term a (c : ℂ) n‖) (fun n => ?_) hL.norm
      (fun n y => ?_)
    · by_cases hn : n = 0
      · simp only [hn, LSeries.term_zero]
        exact continuous_const
      · simp only [LSeries.term_of_ne_zero hn]
        refine continuous_const.div (Continuous.const_cpow (by fun_prop)
          (Or.inl (by exact_mod_cast hn))) (fun y => ?_)
        simp [Complex.cpow_eq_zero_iff, hn]
    · rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp
  have hbound : ∀ y : ℝ, ‖LSeries a ((c : ℂ) + y * I)‖ ≤ ∑' n, ‖LSeries.term a (c : ℂ) n‖ := by
    intro y
    refine (norm_tsum_le_tsum_norm (hs y).norm).trans (le_of_eq (tsum_congr fun n => ?_))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hconv := mellinConvergent_expSeries (a := a) (s := (c : ℂ)) (by simpa using hc0) hL
  have key := mellinInv_mellin_eq c (expSeries a) hx hconv (by
      unfold VerticalIntegrable
      have : (fun y : ℝ => mellin (expSeries a) ((c : ℂ) + y * I))
          = fun y : ℝ => Gamma (c + y * I) * LSeries a ((c : ℂ) + y * I) := by
        funext y
        exact mellin_expSeries (by simpa using hc0) (hs y)
      rw [this]
      exact integrable_Gamma_mul hc0 hcont hbound)
    (continuousAt_expSeries hC hx)
  rw [mellinInv] at key
  have e : ∀ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) • mellin (expSeries a) ((c : ℂ) + y * I)
      = Gamma (c + y * I) * LSeries a (c + y * I) * (x : ℂ) ^ (-((c : ℂ) + y * I)) := by
    intro y
    rw [smul_eq_mul, mellin_expSeries (by simpa using hc0) (hs y), mul_comm]
  simp_rw [e] at key
  rw [← key, Complex.real_smul]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize (∫ y : ℝ, Gamma (c + y * I) * LSeries a (c + y * I) * (x : ℂ) ^ (-((c : ℂ) + y * I))) = J
  push_cast
  field_simp

/-- **Bounded on vertical strips** (Milne, Section 9, pdf p. 102; D105): a function $\varphi$ on $\mathbb C$ is
bounded on vertical strips if for all real $a < b$, $\varphi(s)$ is bounded on the strip $a \le \operatorname{Re} s \le b$
as $\operatorname{Im}(s) \to \pm\infty$: there are $T$ and $C$ with $|\varphi(s)| \le C$ whenever
$a \le \operatorname{Re} s \le b$ and $|\operatorname{Im} s| \ge T$. -/
@[kb "milne2017mf" "Section 9, bounded on vertical strips (pdf p. 102)"]
def BoundedOnVerticalStrips (φ : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ T C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖φ s‖ ≤ C

/-- For a continuous function, Milne's boundedness on vertical strips (only for large $|\operatorname{Im} s|$) is
the repository's `Miyake.BoundedOnVerticalStrips` (bounded on each whole strip): the rest of a strip is compact. -/
@[kb "milne2017mf" "Section 9, bounded on vertical strips (pdf p. 102)"]
theorem boundedOnVerticalStrips_iff {φ : ℂ → ℂ} (hφ : Continuous φ) :
    BoundedOnVerticalStrips φ ↔ Miyake.BoundedOnVerticalStrips φ := by
  constructor
  · intro h σ₁ σ₂
    obtain ⟨T, C, hC⟩ := h σ₁ (max σ₂ (σ₁ + 1)) (lt_max_of_lt_right (by linarith))
    have hK : IsCompact (Complex.reProdIm (Set.Icc σ₁ (max σ₂ (σ₁ + 1))) (Set.Icc (-T) T)) :=
      isCompact_Icc.reProdIm isCompact_Icc
    obtain ⟨C', hC'⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
    refine ⟨max C C', fun s h1 h2 => ?_⟩
    have h2' : s.re ≤ max σ₂ (σ₁ + 1) := h2.trans (le_max_left _ _)
    by_cases hT : T ≤ |s.im|
    · exact (hC s h1 h2' hT).trans (le_max_left _ _)
    · rw [not_le] at hT
      refine (hC' s ⟨⟨h1, h2'⟩, ?_, ?_⟩).trans (le_max_right _ _)
      · linarith [neg_abs_le s.im]
      · linarith [le_abs_self s.im]
  · intro h a b _
    obtain ⟨C, hC⟩ := h a b
    exact ⟨0, C, fun s h1 h2 _ => hC s h1 h2⟩

end ModularFormsKB.Milne
