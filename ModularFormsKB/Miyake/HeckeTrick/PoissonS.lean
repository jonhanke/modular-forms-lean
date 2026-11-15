import ModularFormsKB.Miyake.HeckeTrick.Xi
import ModularFormsKB.Miyake.HeckeTrick.TsumHolomorphic
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Miyake §7.2: the series $S(z;\alpha,\beta)$ and its Fourier expansion (Theorem 7.2.8)

Miyake, *Modular Forms*, §7.2, pp. 275 and 282–283. For $z = x + iy \in \mathbf H$,
$$S(z;\alpha,\beta) = \sum_{n=-\infty}^{\infty}(z+n)^{-\alpha}(\bar z+n)^{-\beta} \qquad (7.2.7),$$
absolutely convergent for $\operatorname{Re}(\alpha+\beta) > 1$. Poisson summation (7.2.12) and Theorem 7.2.5 give
$$S(z;\alpha,\beta) = \xi(y;\alpha,\beta;0) + \sum_{m \ne 0} e^{2\pi i m x}\xi(y;\alpha,\beta;m) \qquad (7.2.41),$$
and the right-hand side (`heckeSCont`, built from the continuation `xiCont`) continues $S$ to $\mathbb C \times
\mathbb C$: it is $\Gamma(\alpha+\beta-1)$ times an entire function of $(\alpha,\beta)$, away from the poles of
$\Gamma(\alpha+\beta-1)$ (where Lean's `Gamma` takes the junk value $0$).
-/

open MeasureTheory Set Filter Topology Complex
open scoped Real FourierTransform

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

/-- **Miyake (7.2.7).** $S(z;\alpha,\beta) = \sum_{n}(z+n)^{-\alpha}(\bar z+n)^{-\beta}$. -/
@[kb "miyake1989" "(7.2.7), p. 275"]
def heckeS (z α β : ℂ) : ℂ :=
  ∑' n : ℤ, (z + n) ^ (-α) * ((starRingEnd ℂ) z + n) ^ (-β)

/-- The $m$-th term $e^{2\pi i m x}\xi(y;\alpha,\beta;m)$ of (7.2.41), $m \ne 0$, through the continuation
`xiCont`; $0$ for $m = 0$. -/
def heckeSTerm (z α β : ℂ) (m : ℤ) : ℂ :=
  if m = 0 then 0 else cexp (2 * π * I * m * z.re) * xiCont z.im α β m

/-- **Miyake (7.2.41)**, the right-hand side: $\xi(y;\alpha,\beta;0) + \sum_{m \ne 0}e^{2\pi imx}\xi(y;\alpha,\beta;m)$,
with $\xi$ replaced by its continuation `xiCont`. -/
@[kb "miyake1989" "(7.2.41), Theorem 7.2.8, p. 282"]
def heckeSCont (z α β : ℂ) : ℂ :=
  xiCont z.im α β 0 + ∑' m : ℤ, heckeSTerm z α β m

/-- The $n$-th term of (7.2.7) is $\phi(y;\alpha,\beta;x+n)$. -/
theorem heckeS_term_eq (z α β : ℂ) (n : ℤ) :
    (z + n) ^ (-α) * ((starRingEnd ℂ) z + n) ^ (-β) = phi z.im α β (z.re + n) := by
  unfold phi
  have h1 : (z + n) = (((z.re + n : ℝ)) : ℂ) + z.im * I := by
    apply Complex.ext <;> simp
  have h2 : ((starRingEnd ℂ) z + n) = (((z.re + n : ℝ)) : ℂ) - z.im * I := by
    apply Complex.ext <;> simp
  rw [h1, h2]

/-- **Miyake, p. 275.** The series (7.2.7) converges absolutely for $\operatorname{Re}(\alpha+\beta) > 1$. -/
@[kb "miyake1989" "(7.2.7), p. 275"]
theorem summable_heckeS {z : ℂ} (hz : 0 < z.im) {α β : ℂ} (h : 1 < (α + β).re) :
    Summable fun n : ℤ ↦ ‖(z + n) ^ (-α) * ((starRingEnd ℂ) z + n) ^ (-β)‖ := by
  simp_rw [heckeS_term_eq]
  set E := Real.exp (π * (|α.im| + |β.im|))
  have hs := (Real.summable_one_div_int_add_rpow z.re (α + β).re).mpr h
  refine Summable.of_norm_bounded_eventually (hs.mul_left E) ?_
  have hfin : ∀ᶠ n : ℤ in cofinite, (n : ℝ) + z.re ≠ 0 := by
    have : {n : ℤ | ¬ ((n : ℝ) + z.re ≠ 0)}.Finite := by
      refine Set.Subsingleton.finite ?_
      intro a ha b hb
      simp only [Set.mem_ofPred_eq, not_not] at ha hb
      exact_mod_cast (by linarith : (a : ℝ) = b)
    exact this
  filter_upwards [hfin] with n hn
  rw [norm_norm]
  refine (norm_phi_le hz α β _).trans ?_
  have hpos : 0 < ((z.re + n : ℝ)) ^ 2 := by
    have : z.re + n ≠ 0 := by intro h0; apply hn; linarith
    positivity
  have h1 : (((z.re + n : ℝ)) ^ 2 + z.im ^ 2) ^ (-(α + β).re / 2) ≤
      (((z.re + n : ℝ)) ^ 2) ^ (-(α + β).re / 2) :=
    Real.rpow_le_rpow_of_nonpos hpos (by nlinarith [sq_nonneg z.im]) (by linarith)
  have h2 : (((z.re + n : ℝ)) ^ 2) ^ (-(α + β).re / 2) = 1 / |(n : ℝ) + z.re| ^ (α + β).re := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), one_div,
      ← Real.rpow_neg (abs_nonneg _), add_comm z.re]
    congr 2; push_cast; ring
  rw [← h2]
  exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

/-- Pointwise bound for `xiCont` at $t \ge 1$. -/
theorem norm_xiCont_pos_le {y y0 : ℝ} {α β : ℂ} {t : ℝ} {M A B : ℝ} {N : ℕ}
    (hy0 : 0 < y0) (hyy : y0 ≤ y) (ht : 1 ≤ t) (hN : α.re - 1 ≤ N)
    (hM : ‖I ^ (β - α) * ((2 * π : ℝ) : ℂ) ^ α * (Gamma α)⁻¹ * ((2 * y : ℝ) : ℂ) ^ (-β)‖ ≤ M)
    (hA0 : 0 ≤ A) (hB : 0 ≤ B)
    (hA : ‖omega ((4 * π * y * t : ℝ) : ℂ) α β‖ ≤ A * (1 + (4 * π * y * t) ^ (-B))) :
    ‖xiCont y α β t‖ ≤ M * (A * (1 + (4 * π * y0) ^ (-B))) * t ^ N * Real.exp (-(2 * π * y0) * t) := by
  have htp : 0 < t := by linarith
  unfold xiCont
  rw [if_pos htp]
  set P := I ^ (β - α) * ((2 * π : ℝ) : ℂ) ^ α * (Gamma α)⁻¹ * ((2 * y : ℝ) : ℂ) ^ (-β) with hP
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  simp only [norm_mul]
  have h1 : ‖(t : ℂ) ^ (α - 1)‖ ≤ t ^ N := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.one_re]
    calc t ^ (α.re - 1) ≤ t ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le ht hN
      _ = t ^ N := Real.rpow_natCast _ _
  have h2 : ‖((Real.exp (-2 * π * y * t) : ℝ) : ℂ)‖ ≤ Real.exp (-(2 * π * y0) * t) := by
    rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.2
    have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hyy)) htp.le
    nlinarith
  have h3 : A * (1 + (4 * π * y * t) ^ (-B)) ≤ A * (1 + (4 * π * y0) ^ (-B)) := by
    apply mul_le_mul_of_nonneg_left _ hA0
    have hyt : y0 ≤ y * t := by nlinarith
    have : (4 * π * y0) ^ (-B) ≥ (4 * π * y * t) ^ (-B) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hyt Real.pi_pos.le]) (by linarith)
    linarith
  have h4 := hA.trans h3
  calc _ ≤ M * t ^ N * Real.exp (-(2 * π * y0) * t) * (A * (1 + (4 * π * y0) ^ (-B))) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul hM h1 (norm_nonneg _) hM0) h2 (norm_nonneg _)
          (by positivity)) h4 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Pointwise bound for `xiCont` at $t \le -1$. -/
theorem norm_xiCont_neg_le {y y0 : ℝ} {α β : ℂ} {t : ℝ} {M A B : ℝ} {N : ℕ}
    (hy0 : 0 < y0) (hyy : y0 ≤ y) (ht : 1 ≤ |t|) (htn : t < 0) (hN : β.re - 1 ≤ N)
    (hM : ‖I ^ (β - α) * ((2 * π : ℝ) : ℂ) ^ β * (Gamma β)⁻¹ * ((2 * y : ℝ) : ℂ) ^ (-α)‖ ≤ M)
    (hA0 : 0 ≤ A) (hB : 0 ≤ B)
    (hA : ‖omega ((4 * π * y * |t| : ℝ) : ℂ) β α‖ ≤ A * (1 + (4 * π * y * |t|) ^ (-B))) :
    ‖xiCont y α β t‖ ≤ M * (A * (1 + (4 * π * y0) ^ (-B))) * |t| ^ N *
      Real.exp (-(2 * π * y0) * |t|) := by
  have htp : 0 < |t| := by linarith
  unfold xiCont
  rw [if_neg (by linarith), if_neg (by linarith)]
  set P := I ^ (β - α) * ((2 * π : ℝ) : ℂ) ^ β * (Gamma β)⁻¹ * ((2 * y : ℝ) : ℂ) ^ (-α) with hP
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  simp only [norm_mul]
  have h1 : ‖((|t| : ℝ) : ℂ) ^ (β - 1)‖ ≤ |t| ^ N := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.one_re]
    calc |t| ^ (β.re - 1) ≤ |t| ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le ht hN
      _ = |t| ^ N := Real.rpow_natCast _ _
  have h2 : ‖((Real.exp (-2 * π * y * |t|) : ℝ) : ℂ)‖ ≤ Real.exp (-(2 * π * y0) * |t|) := by
    rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.2
    have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hyy)) htp.le
    nlinarith
  have h3 : A * (1 + (4 * π * y * |t|) ^ (-B)) ≤ A * (1 + (4 * π * y0) ^ (-B)) := by
    apply mul_le_mul_of_nonneg_left _ hA0
    have hyt : y0 ≤ y * |t| := by nlinarith
    have : (4 * π * y0) ^ (-B) ≥ (4 * π * y * |t|) ^ (-B) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hyt Real.pi_pos.le]) (by linarith)
    linarith
  have h4 := hA.trans h3
  calc _ ≤ M * |t| ^ N * Real.exp (-(2 * π * y0) * |t|) * (A * (1 + (4 * π * y0) ^ (-B))) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul hM h1 (norm_nonneg _) hM0) h2 (norm_nonneg _)
          (by positivity)) h4 (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Exponential decay of `xiCont` for $|t| \ge 1$, uniformly on compact sets. -/
theorem xiCont_decay {T : Set (ℂ × ℂ × ℂ)} (hT : IsCompact T) (hTz : ∀ p ∈ T, 0 < p.1.im) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∃ N : ℕ, ∀ p ∈ T, ∀ t : ℝ, 1 ≤ |t| →
      ‖xiCont p.1.im p.2.1 p.2.2 t‖ ≤ C * |t| ^ N * Real.exp (-c * |t|) := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 1, le_rfl, one_pos, 0, by simp⟩
  obtain ⟨p0, hp0, hmin⟩ :=
    hT.exists_isMinOn hne (Complex.continuous_im.comp continuous_fst).continuousOn
  have hy0 : 0 < p0.1.im := hTz p0 hp0
  have hyy : ∀ p ∈ T, p0.1.im ≤ p.1.im := fun p hp ↦ isMinOn_iff.1 hmin p hp
  set y0 := p0.1.im with hy0def
  set T' := ((fun p : ℂ × ℂ × ℂ ↦ (p.2.1, p.2.2)) '' T) ∪
    ((fun p : ℂ × ℂ × ℂ ↦ (p.2.2, p.2.1)) '' T) with hT'
  have hcT' : IsCompact T' := (hT.image (by fun_prop)).union (hT.image (by fun_prop))
  obtain ⟨A, hA, B, hB, hω⟩ := omega_bound hcT'
  obtain ⟨R1, hR1⟩ :=
    (hT.image (Complex.continuous_re.comp (continuous_fst.comp continuous_snd))).bddAbove
  obtain ⟨R2, hR2⟩ :=
    (hT.image (Complex.continuous_re.comp (continuous_snd.comp continuous_snd))).bddAbove
  set N : ℕ := ⌈max R1 R2⌉₊ with hNdef
  have hN1 : ∀ p ∈ T, p.2.1.re - 1 ≤ N := fun p hp ↦ by
    have h1 : p.2.1.re ≤ R1 := hR1 ⟨p, hp, rfl⟩
    have := Nat.le_ceil (max R1 R2)
    have := le_max_left R1 R2
    linarith
  have hN2 : ∀ p ∈ T, p.2.2.re - 1 ≤ N := fun p hp ↦ by
    have h1 : p.2.2.re ≤ R2 := hR2 ⟨p, hp, rfl⟩
    have := Nat.le_ceil (max R1 R2)
    have := le_max_right R1 R2
    linarith
  have hI : (I : ℂ) ∈ Complex.slitPlane := Or.inr (by simp)
  have h2π : ((2 * π : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Or.inl (by simp [Real.pi_pos])
  have hy2 : ∀ p ∈ T, ((2 * p.1.im : ℝ) : ℂ) ∈ Complex.slitPlane := fun p hp ↦
    Or.inl (by simpa using hTz p hp)
  have hG : Continuous fun a : ℂ ↦ (Gamma a)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma.continuous
  have hIc : ∀ f g : ℂ × ℂ × ℂ → ℂ, ContinuousOn f T → ContinuousOn g T →
      (∀ p ∈ T, f p ∈ Complex.slitPlane) → ContinuousOn (fun p ↦ f p ^ g p) T :=
    fun f g hf hg h0 ↦ hf.cpow hg h0
  have hc1 : ContinuousOn (fun p : ℂ × ℂ × ℂ ↦
      ‖I ^ (p.2.2 - p.2.1) * ((2 * π : ℝ) : ℂ) ^ p.2.1 * (Gamma p.2.1)⁻¹ *
        ((2 * p.1.im : ℝ) : ℂ) ^ (-p.2.2)‖) T := by
    have f1 := hIc (fun _ ↦ I) (fun p ↦ p.2.2 - p.2.1) continuousOn_const (by fun_prop)
      (fun _ _ ↦ hI)
    have f2 := hIc (fun _ ↦ ((2 * π : ℝ) : ℂ)) (fun p ↦ p.2.1) continuousOn_const (by fun_prop)
      (fun _ _ ↦ h2π)
    have f3 : ContinuousOn (fun p : ℂ × ℂ × ℂ ↦ (Gamma p.2.1)⁻¹) T :=
      (hG.comp (continuous_fst.comp continuous_snd)).continuousOn
    have f4 := hIc (fun p ↦ ((2 * p.1.im : ℝ) : ℂ)) (fun p ↦ -p.2.2) (by fun_prop)
      (by fun_prop) hy2
    exact (((f1.mul f2).mul f3).mul f4).norm
  have hc2 : ContinuousOn (fun p : ℂ × ℂ × ℂ ↦
      ‖I ^ (p.2.2 - p.2.1) * ((2 * π : ℝ) : ℂ) ^ p.2.2 * (Gamma p.2.2)⁻¹ *
        ((2 * p.1.im : ℝ) : ℂ) ^ (-p.2.1)‖) T := by
    have f1 := hIc (fun _ ↦ I) (fun p ↦ p.2.2 - p.2.1) continuousOn_const (by fun_prop)
      (fun _ _ ↦ hI)
    have f2 := hIc (fun _ ↦ ((2 * π : ℝ) : ℂ)) (fun p ↦ p.2.2) continuousOn_const (by fun_prop)
      (fun _ _ ↦ h2π)
    have f3 : ContinuousOn (fun p : ℂ × ℂ × ℂ ↦ (Gamma p.2.2)⁻¹) T :=
      (hG.comp (continuous_snd.comp continuous_snd)).continuousOn
    have f4 := hIc (fun p ↦ ((2 * p.1.im : ℝ) : ℂ)) (fun p ↦ -p.2.1) (by fun_prop)
      (by fun_prop) hy2
    exact (((f1.mul f2).mul f3).mul f4).norm
  obtain ⟨M1, hM1⟩ := hT.exists_bound_of_continuousOn hc1
  obtain ⟨M2, hM2⟩ := hT.exists_bound_of_continuousOn hc2
  set M : ℝ := max (max M1 M2) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hQ : 0 < A * (1 + (4 * π * y0) ^ (-B)) := by positivity
  refine ⟨M * (A * (1 + (4 * π * y0) ^ (-B))), 2 * π * y0, by positivity, by positivity, N,
    fun p hp t ht ↦ ?_⟩
  have hM1' : ‖I ^ (p.2.2 - p.2.1) * ((2 * π : ℝ) : ℂ) ^ p.2.1 * (Gamma p.2.1)⁻¹ *
        ((2 * p.1.im : ℝ) : ℂ) ^ (-p.2.2)‖ ≤ M := by
    have := hM1 p hp
    rw [norm_norm] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hM2' : ‖I ^ (p.2.2 - p.2.1) * ((2 * π : ℝ) : ℂ) ^ p.2.2 * (Gamma p.2.2)⁻¹ *
        ((2 * p.1.im : ℝ) : ℂ) ^ (-p.2.1)‖ ≤ M := by
    have := hM2 p hp
    rw [norm_norm] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  rcases lt_trichotomy t 0 with htn | rfl | htp
  · have hab : |t| = -t := abs_of_neg htn
    have hmem : (p.2.2, p.2.1) ∈ T' := Or.inr ⟨p, hp, rfl⟩
    have hpos : 0 < 4 * π * p.1.im * |t| := by
      have := hTz p hp
      have : 0 < |t| := by rw [hab]; linarith
      positivity
    have := norm_xiCont_neg_le (y := p.1.im) (y0 := y0) (α := p.2.1) (β := p.2.2) (t := t)
      (M := M) (A := A) (B := B) (N := N) hy0 (hyy p hp) ht htn (hN2 p hp) hM2' hA.le hB.le
      (hω (4 * π * p.1.im * |t|) hpos (p.2.2, p.2.1) hmem)
    refine this.trans ?_
    exact le_of_eq (by ring)
  · rw [abs_zero] at ht; linarith
  · have hab : |t| = t := abs_of_pos htp
    have hmem : (p.2.1, p.2.2) ∈ T' := Or.inl ⟨p, hp, rfl⟩
    have hpos : 0 < 4 * π * p.1.im * t := by
      have := hTz p hp
      positivity
    have ht1 : 1 ≤ t := by rwa [hab] at ht
    have := norm_xiCont_pos_le (y := p.1.im) (y0 := y0) (α := p.2.1) (β := p.2.2) (t := t)
      (M := M) (A := A) (B := B) (N := N) hy0 (hyy p hp) ht1 (hN1 p hp) hM1' hA.le hB.le
      (hω (4 * π * p.1.im * t) hpos (p.2.1, p.2.2) hmem)
    rw [hab]
    refine this.trans (le_of_eq (by ring))

theorem summable_poly_exp (C c : ℝ) (hc : 0 < c) (N : ℕ) :
    Summable fun m : ℤ ↦ C * |(m : ℝ)| ^ N * Real.exp (-c * |(m : ℝ)|) := by
  have hr : ‖Real.exp (-c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := Real.exp_lt_exp.2 (show -c < 0 by linarith)
    simpa using this
  have key := (summable_pow_mul_geometric_of_norm_lt_one N hr).mul_left C
  have e : ∀ n : ℕ, C * ((n : ℝ) ^ N * Real.exp (-c) ^ n) =
      C * |((n : ℤ) : ℝ)| ^ N * Real.exp (-c * |((n : ℤ) : ℝ)|) := fun n ↦ by
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), ← Real.exp_nat_mul]
    ring_nf
  refine Summable.of_nat_of_neg (key.congr e) (key.congr fun n ↦ ?_)
  rw [e n]
  simp

theorem exists_poly_exp_le {c : ℝ} (hc : 0 < c) (N : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    ∃ K : ℝ, ∀ u : ℝ, 1 ≤ u → u ^ N * Real.exp (-c * u) ≤ K * u ^ (-b) := by
  set k : ℕ := ⌈(N : ℝ) + b⌉₊ with hk
  refine ⟨(k.factorial : ℝ) / c ^ k, fun u hu ↦ ?_⟩
  have hu0 : 0 < u := by linarith
  have h1 : u ^ ((N : ℝ) + b) ≤ u ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu (Nat.le_ceil _)
  have h2 := Real.pow_div_factorial_le_exp (c * u) (by positivity) k
  rw [div_le_iff₀ (by positivity)] at h2
  have h3 : (c * u) ^ k * Real.exp (-c * u) ≤ k.factorial := by
    calc (c * u) ^ k * Real.exp (-c * u) ≤ Real.exp (c * u) * k.factorial * Real.exp (-c * u) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = k.factorial := by
          rw [mul_right_comm, ← Real.exp_add]; simp
  have h4 : u ^ k * Real.exp (-c * u) ≤ (k.factorial : ℝ) / c ^ k := by
    rw [le_div_iff₀ (by positivity)]
    calc _ = (c * u) ^ k * Real.exp (-c * u) := by rw [mul_pow]; ring
      _ ≤ _ := h3
  have h5 : u ^ N * Real.exp (-c * u) = (u ^ ((N : ℝ) + b) * Real.exp (-c * u)) * u ^ (-b) := by
    rw [Real.rpow_add hu0, Real.rpow_natCast, mul_right_comm, mul_assoc (u ^ N),
      ← Real.rpow_add hu0]
    simp
  rw [h5]
  have h6 : u ^ ((N : ℝ) + b) * Real.exp (-c * u) ≤ (k.factorial : ℝ) / c ^ k :=
    le_trans (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le) h4
  exact mul_le_mul_of_nonneg_right h6 (by positivity)

/-- **Miyake, Theorem 7.2.8 (convergence).** The series $\sum_{m \ne 0}e^{2\pi imx}\xi(y;\alpha,\beta;m)$ converges
absolutely and uniformly on every compact subset of $\mathbf H \times \mathbb C \times \mathbb C$: on such a set its
terms have one summable majorant. -/
@[kb "miyake1989" "Theorem 7.2.8, p. 282"]
theorem heckeSTerm_uniform {T : Set (ℂ × ℂ × ℂ)} (hT : IsCompact T) (hTz : ∀ p ∈ T, 0 < p.1.im) :
    ∃ u : ℤ → ℝ, Summable u ∧ ∀ p ∈ T, ∀ m : ℤ, ‖heckeSTerm p.1 p.2.1 p.2.2 m‖ ≤ u m := by
  obtain ⟨C, c, hC, hc, N, h⟩ := xiCont_decay hT hTz
  refine ⟨fun m : ℤ ↦ C * |(m : ℝ)| ^ N * Real.exp (-c * |(m : ℝ)|),
    summable_poly_exp C c hc N, fun p hp m ↦ ?_⟩
  by_cases hm : m = 0
  · subst hm
    simp [heckeSTerm]
    positivity
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
    have h2 : ‖cexp (2 * π * I * m * p.1.re)‖ = 1 := by
      have : (2 * π * I * m * p.1.re : ℂ) = ((2 * π * m * p.1.re : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    unfold heckeSTerm
    rw [if_neg hm, norm_mul, h2, one_mul]
    exact h p hp m h1 |> fun h' ↦ by simpa using h'

/-- **Miyake, Theorem 7.2.8 (the Fourier expansion (7.2.41)).** For $z \in \mathbf H$ and
$\operatorname{Re}(\alpha+\beta) > 1$, $S(z;\alpha,\beta) = \xi(y;\alpha,\beta;0) +
\sum_{m \ne 0}e^{2\pi imx}\xi(y;\alpha,\beta;m)$. -/
@[kb "miyake1989" "Theorem 7.2.8, p. 282"]
theorem heckeS_eq_heckeSCont {z : ℂ} (hz : 0 < z.im) {α β : ℂ} (h : 1 < (α + β).re) :
    heckeS z α β = heckeSCont z α β := by
  set b : ℝ := (α + β).re with hbdef
  have hb : 1 < b := h
  have hcpt : IsCompact ({(z, α, β)} : Set (ℂ × ℂ × ℂ)) := isCompact_singleton
  have hTz : ∀ p ∈ ({(z, α, β)} : Set (ℂ × ℂ × ℂ)), 0 < p.1.im := by
    intro p hp; rw [Set.mem_singleton_iff] at hp; rw [hp]; exact hz
  obtain ⟨C, c, hC, hc, N, hdec⟩ := xiCont_decay hcpt hTz
  have hdec' : ∀ t : ℝ, 1 ≤ |t| → ‖xiCont z.im α β t‖ ≤ C * |t| ^ N * Real.exp (-c * |t|) :=
    fun t ht ↦ hdec (z, α, β) rfl t ht
  have hcof : ∀ᶠ t : ℝ in cocompact ℝ, 1 ≤ |t| := by
    filter_upwards [(isCompact_closedBall (0 : ℝ) 1).compl_mem_cocompact] with t ht
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at ht
    exact ht.le
  -- decay of phi
  have hfO : phi z.im α β =O[cocompact ℝ] (fun t : ℝ ↦ |t| ^ (-b)) := by
    refine Asymptotics.IsBigO.of_bound (Real.exp (π * (|α.im| + |β.im|))) ?_
    filter_upwards [hcof] with t ht
    have ht0 : 0 < |t| := by linarith
    refine (norm_phi_le hz α β t).trans ?_
    have h1 : (t ^ 2 + z.im ^ 2) ^ (-(α + β).re / 2) ≤ (t ^ 2) ^ (-(α + β).re / 2) :=
      Real.rpow_le_rpow_of_nonpos (by have : t ≠ 0 := abs_pos.1 ht0; positivity) (by nlinarith [sq_nonneg z.im]) (by linarith)
    have h2 : (t ^ 2) ^ (-(α + β).re / 2) = |t| ^ (-b) := by
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1; push_cast; ring
    rw [h2] at h1
    rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ |t| ^ (-b))]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  -- decay of the Fourier transform
  obtain ⟨K, hK⟩ := exists_poly_exp_le hc N (le_of_lt (by linarith : (0 : ℝ) < b))
  have hFO : (𝓕 (phi z.im α β)) =O[cocompact ℝ] (fun t : ℝ ↦ |t| ^ (-b)) := by
    refine Asymptotics.IsBigO.of_bound (C * K) ?_
    filter_upwards [hcof] with t ht
    rw [← xi_eq_fourier, xi_eq_xiCont hz h, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ |t| ^ (-b))]
    refine (hdec' t ht).trans ?_
    calc C * |t| ^ N * Real.exp (-c * |t|) = C * (|t| ^ N * Real.exp (-c * |t|)) := by ring
      _ ≤ C * (K * |t| ^ (-b)) := mul_le_mul_of_nonneg_left (hK _ ht) hC
      _ = _ := by ring
  have P := Real.tsum_eq_tsum_fourier_of_rpow_decay (continuous_phi hz α β) hb hfO hFO z.re
  -- summability of the terms
  obtain ⟨u, hu, hub⟩ := heckeSTerm_uniform hcpt hTz
  have hsum : Summable fun m : ℤ ↦ heckeSTerm z α β m :=
    Summable.of_norm_bounded hu (fun m ↦ hub (z, α, β) rfl m)
  have hpt : ∀ m : ℤ, 𝓕 (phi z.im α β) m * fourier m (z.re : UnitAddCircle) =
      heckeSTerm z α β m + if m = 0 then xiCont z.im α β 0 else 0 := by
    intro m
    rw [← xi_eq_fourier, xi_eq_xiCont hz h, fourier_coe_apply]
    by_cases hm : m = 0
    · subst hm; simp [heckeSTerm]
    · simp [heckeSTerm, hm, mul_comm]
  have hL : heckeS z α β = ∑' n : ℤ, phi z.im α β (z.re + n) := by
    unfold heckeS
    exact tsum_congr fun n ↦ heckeS_term_eq z α β n
  rw [hL, P]
  simp_rw [hpt]
  rw [Summable.tsum_add hsum (hasSum_ite_eq (0 : ℤ) (xiCont z.im α β 0)).summable,
    tsum_ite_eq, heckeSCont, add_comm]

/-- The entire part: $(\alpha,\beta) \mapsto \sum_{m \ne 0}e^{2\pi imx}\xi(y;\alpha,\beta;m)$ is holomorphic on
$\mathbb C \times \mathbb C$ (Miyake, proof of Theorem 7.2.8). -/
theorem differentiable_tsum_heckeSTerm {z : ℂ} (hz : 0 < z.im) :
    Differentiable ℂ (fun p : ℂ × ℂ ↦ ∑' m : ℤ, heckeSTerm z p.1 p.2 m) := by
  refine differentiable_tsum_of_locally_bounded (fun m ↦ ?_) (fun p ↦ ?_)
  · by_cases hm : m = 0
    · simp only [heckeSTerm, hm, if_true]
      exact differentiable_const _
    · simp only [heckeSTerm, hm, if_false]
      exact (differentiable_const _).mul
        (differentiable_xiCont hz (t := (m : ℝ)) (by exact_mod_cast hm))
  · have hc : Continuous (fun q : ℂ × ℂ ↦ ((z, q.1, q.2) : ℂ × ℂ × ℂ)) :=
      continuous_const.prodMk (continuous_fst.prodMk continuous_snd)
    have hTc : IsCompact ((fun q : ℂ × ℂ ↦ ((z, q.1, q.2) : ℂ × ℂ × ℂ)) '' Metric.closedBall p 1) :=
      (isCompact_closedBall p 1).image hc
    have hTz : ∀ q ∈ (fun q : ℂ × ℂ ↦ ((z, q.1, q.2) : ℂ × ℂ × ℂ)) '' Metric.closedBall p 1,
        0 < q.1.im := by
      rintro _ ⟨q, _, rfl⟩
      exact hz
    obtain ⟨u, hu, hb⟩ := heckeSTerm_uniform hTc hTz
    refine ⟨Metric.closedBall p 1, Metric.closedBall_mem_nhds p one_pos, u, hu, fun m q hq ↦ ?_⟩
    exact hb (z, q.1, q.2) ⟨q, hq, rfl⟩ m

/-- **Miyake, Theorem 7.2.8 (continuation).** For $z \in \mathbf H$, $\Gamma(\alpha+\beta-1)^{-1}S(z;\alpha,\beta)$ is
an entire function of $(\alpha,\beta)$: the continuation `heckeSCont` equals $\Gamma(\alpha+\beta-1)h(\alpha,\beta)$
with $h$ entire, wherever $\alpha + \beta - 1$ is not a pole of $\Gamma$. -/
@[kb "miyake1989" "Theorem 7.2.8, p. 282"]
theorem heckeSCont_eq_Gamma_mul {z : ℂ} (hz : 0 < z.im) :
    ∃ h : ℂ × ℂ → ℂ, Differentiable ℂ h ∧ ∀ α β : ℂ, (∀ n : ℕ, α + β - 1 ≠ -n) →
      heckeSCont z α β = Gamma (α + β - 1) * h (α, β) := by
  obtain ⟨h0, hd0, he0⟩ := xiCont_zero_eq_Gamma_mul hz
  have hlin : Differentiable ℂ (fun p : ℂ × ℂ ↦ p.1 + p.2 - 1) :=
    (differentiable_fst.add differentiable_snd).sub (differentiable_const _)
  have hG : Differentiable ℂ (fun p : ℂ × ℂ ↦ 1 / Gamma (p.1 + p.2 - 1)) :=
    by simpa [one_div, Function.comp_def] using Complex.differentiable_one_div_Gamma.comp hlin
  have hd : Differentiable ℂ (fun p : ℂ × ℂ ↦
      h0 p + 1 / Gamma (p.1 + p.2 - 1) * ∑' m : ℤ, heckeSTerm z p.1 p.2 m) :=
    hd0.add (hG.mul (differentiable_tsum_heckeSTerm hz))
  refine ⟨_, hd, fun α β hαβ ↦ ?_⟩
  have hΓ : Gamma (α + β - 1) ≠ 0 := Complex.Gamma_ne_zero hαβ
  show xiCont z.im α β 0 + ∑' m : ℤ, heckeSTerm z α β m = Gamma (α + β - 1) *
    (h0 (α, β) + 1 / Gamma (α + β - 1) * ∑' m : ℤ, heckeSTerm z α β m)
  rw [he0 α β, mul_add, ← mul_assoc, mul_one_div_cancel hΓ, one_mul]

end ModularFormsKB.Miyake.HeckeTrick
