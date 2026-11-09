import ModularFormsKB.Miyake.Sec4_3.Defs

/-!
# Decay of completed $L$-series on vertical lines; boundedness of Mellin transforms in strips

* `Miyake.norm_Gamma_le_Gamma_re`: $|\Gamma(s)| \le \Gamma(\operatorname{Re} s)$ for $\operatorname{Re} s > 0$.
* `Miyake.completedL_decay`: where $L(s;f)$ converges absolutely on the line
  $\operatorname{Re} s = \sigma > 0$, $|\Lambda_N(\sigma + it; f)| \le A/(1+t^2)$
  (from $\Gamma(s) = \Gamma(s+2)/(s(s+1))$; no Stirling needed).
* `Miyake.IsStrongFEPair.boundedOnVerticalStrips`, `Miyake.WeakFEPair.boundedOnVerticalStrips_Λ₀`:
  the entire functions produced by Mathlib's FE-pairs are bounded on vertical strips.
-/

open Complex Filter Asymptotics Set MeasureTheory
open scoped Real

noncomputable section

namespace Miyake

/-- $|\Gamma(s)| \le \Gamma(\operatorname{Re} s)$ for $\operatorname{Re} s > 0$ (from the Euler integral). -/
lemma norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- The completed $L$-series decays like $1/(1+t^2)$ on a vertical line $\operatorname{Re} s = \sigma > 0$
on which the Dirichlet series converges absolutely. -/
lemma completedL_decay {N : ℝ} (hN : 0 < N) {a : ℕ → ℂ} {σ : ℝ} (hσ : 0 < σ)
    (hL : LSeriesSummable a σ) :
    ∃ A : ℝ, ∀ t : ℝ, ‖completedL N a (σ + t * I)‖ ≤ A / (1 + t ^ 2) := by
  have hsum : Summable fun n => ‖LSeries.term a (σ : ℂ) n‖ := hL.norm
  set S : ℝ := ∑' n, ‖LSeries.term a (σ : ℂ) n‖ with hS
  set m : ℝ := min σ 1 with hm
  have hm0 : 0 < m := lt_min hσ one_pos
  set B : ℝ := (2 * π / √N) ^ (-σ) with hB
  set G : ℝ := Real.Gamma (σ + 2) with hG
  refine ⟨B * G * S / m, fun t => ?_⟩
  set s : ℂ := σ + t * I with hs
  have hre : s.re = σ := by simp [hs]
  have him : s.im = t := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by simp [h] at hre; linarith
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hre] at this; linarith
  have hL' : ‖LSeries a s‖ ≤ S := by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · simpa [LSeries.norm_term_eq, hre] using hsum
    · refine le_of_eq (tsum_congr fun n => ?_)
      simp [LSeries.norm_term_eq, hre]
  have hΓ2 : ‖Gamma (s + 2)‖ ≤ G := by
    have := norm_Gamma_le_Gamma_re (s := s + 2) (by simp [hre]; linarith)
    simpa [hre, hG] using this
  have hfac : Gamma (s + 2) = (s + 1) * s * Gamma s := by
    have e : s + 2 = (s + 1) + 1 := by ring
    rw [e, Complex.Gamma_add_one _ hs1, Complex.Gamma_add_one _ hs0]; ring
  have hprod : m * (1 + t ^ 2) ≤ ‖s‖ * ‖s + 1‖ := by
    have h1 : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [hre, him]; ring
    have h2 : ‖s + 1‖ ^ 2 = (σ + 1) ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [hre, him]; ring
    have hm1 : m ≤ σ := min_le_left _ _
    have hm2 : m ≤ 1 := min_le_right _ _
    have h3 : (m * (1 + t ^ 2)) ^ 2 ≤ (‖s‖ * ‖s + 1‖) ^ 2 := by
      rw [mul_pow, mul_pow, h1, h2]
      have a1 : m ^ 2 * (1 + t ^ 2) ≤ σ ^ 2 + t ^ 2 := by
        nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (by nlinarith : 0 ≤ 1 - m ^ 2),
          mul_self_le_mul_self hm0.le hm1]
      have a2 : 1 + t ^ 2 ≤ (σ + 1) ^ 2 + t ^ 2 := by nlinarith
      calc m ^ 2 * (1 + t ^ 2) ^ 2 = (m ^ 2 * (1 + t ^ 2)) * (1 + t ^ 2) := by ring
        _ ≤ _ := mul_le_mul a1 a2 (by positivity) (by positivity)
    exact le_of_sq_le_sq h3 (by positivity)
  have hpos : 0 < m * (1 + t ^ 2) := by positivity
  have hΓ : ‖Gamma s‖ ≤ G / (m * (1 + t ^ 2)) := by
    have : ‖Gamma (s + 2)‖ = ‖s‖ * ‖s + 1‖ * ‖Gamma s‖ := by
      rw [hfac, norm_mul, norm_mul, mul_comm ‖s + 1‖]
    rw [le_div_iff₀ hpos]
    calc ‖Gamma s‖ * (m * (1 + t ^ 2)) ≤ ‖Gamma s‖ * (‖s‖ * ‖s + 1‖) :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = ‖Gamma (s + 2)‖ := by rw [this]; ring
      _ ≤ G := hΓ2
  have hc : ‖((2 * π / √N : ℝ) : ℂ) ^ (-s)‖ = B := by
    have hpos' : 0 < 2 * π / √N := by positivity
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos']
    simp [hre, hB]
  unfold completedL
  rw [norm_mul, norm_mul, hc]
  calc B * ‖Gamma s‖ * ‖LSeries a s‖ ≤ B * (G / (m * (1 + t ^ 2))) * S := by
        have hB0 : 0 ≤ B := by positivity
        gcongr
    _ = B * G * S / m / (1 + t ^ 2) := by field_simp

/-- The Mellin transform of the first function of a strong FE-pair (an entire function) is bounded
on every vertical strip. -/
lemma IsStrongFEPair.boundedOnVerticalStrips {P : WeakFEPair ℂ} (hP : IsStrongFEPair P) :
    BoundedOnVerticalStrips (mellin P.f) := by
  intro σ₁ σ₂
  have h1 := (hP.hasMellin (σ₁ : ℂ)).1.norm
  have h2 := (hP.hasMellin (σ₂ : ℂ)).1.norm
  have hint : IntegrableOn (fun t : ℝ => (t ^ (σ₁ - 1) + t ^ (σ₂ - 1)) * ‖P.f t‖) (Ioi 0) := by
    have := MeasureTheory.Integrable.add h1 h2
    refine IntegrableOn.congr_fun this (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0:ℝ) < t := ht
    simp only [Pi.add_apply, norm_smul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_cpow_eq_rpow_re_of_pos ht']
    simp; ring
  refine ⟨∫ t in Ioi (0:ℝ), (t ^ (σ₁ - 1) + t ^ (σ₂ - 1)) * ‖P.f t‖, fun s hs1 hs2 => ?_⟩
  unfold mellin
  refine norm_integral_le_of_norm_le hint ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  have ht : (0:ℝ) < t := ht
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp only [Complex.sub_re, Complex.one_re]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases le_total 1 t with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h (show s.re - 1 ≤ σ₂ - 1 by linarith)
    have := Real.rpow_nonneg ht.le (σ₁ - 1)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge ht h (show σ₁ - 1 ≤ s.re - 1 by linarith)
    have := Real.rpow_nonneg ht.le (σ₂ - 1)
    linarith

/-- The entire function $\Lambda_0$ of a weak FE-pair is bounded on every vertical strip. -/
lemma WeakFEPair.boundedOnVerticalStrips_Λ₀ (P : WeakFEPair ℂ) :
    BoundedOnVerticalStrips P.Λ₀ := by
  have h := Miyake.IsStrongFEPair.boundedOnVerticalStrips P.isStrongFEPair_toStrongFEPair
  have e : mellin P.toStrongFEPair.f = P.Λ₀ := rfl
  rwa [e] at h

end Miyake
