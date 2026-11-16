/-
# The entire part of $E^*(z,s)$: two Mellin integrals, a bound, continuity in $z$

With the tail $A_z(t) = \theta_z(t) - 1$ for $t > 1$ and
$A_z(t) = 0$ for $t \le 1$ (`thetaTail`), the entire part of the completed Eisenstein series is
$$E^*_0(z,s) = \int_1^\infty(\theta_z(t)-1)\,(t^{s-1} + t^{-s})\,dt = \mathcal M A_z(s) + \mathcal M A_z(1-s)$$
(`eisensteinReg_eq_mellin`), from the self-duality of $\theta_z$. For $\operatorname{Im}z \ge \tfrac12$:
- $|\theta_z(t) - 1| \le Ky\,e^{-b(y)(t-1)}$ for $t \ge 1$, $b(y) = \pi\min(1,y^2)/y$ (`norm_thetaZ_sub_one_le`);
- $|E^*_0(z,s)| \le B\,y^A$ on every vertical strip (`norm_eisensteinReg_le`);
- $z \mapsto E^*_0(z,s)$ is continuous on $\operatorname{Im}z > \tfrac12$ (`continuousOn_eisensteinReg`).
-/
import ModularFormsKB.RankinSelberg.EisensteinZero

open MeasureTheory Set Filter Topology Complex Asymptotics
open scoped UpperHalfPlane Real

noncomputable section

namespace ModularFormsKB.RankinSelberg

open ModularFormsKB.HalfIntegral ModularFormsKB.Miyake.HeckeTrick

/-! ### The tail and the Mellin decomposition -/

/-- The tail $A_z(t) = \theta_z(t) - 1$ for $t > 1$, and $0$ for $t \le 1$. -/
def thetaTail (z : ℍ) : ℝ → ℂ := (Ioi 1).indicator (fun t ↦ thetaZ z t - 1)

theorem locallyIntegrableOn_thetaTail (z : ℍ) : LocallyIntegrableOn (thetaTail z) (Ioi 0) := by
  intro x hx
  obtain ⟨s, hs, hs'⟩ := ((continuousOn_thetaZ z).locallyIntegrableOn measurableSet_Ioi).sub
    (locallyIntegrableOn_const (μ := (volume : Measure ℝ)) (1 : ℂ)) x hx
  exact ⟨s, hs, hs'.indicator measurableSet_Ioi⟩

theorem thetaTail_isBigO_top (z : ℍ) (r : ℝ) : thetaTail z =O[atTop] (· ^ r) := by
  refine (thetaZ_sub_one_isBigO z r).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  simp [thetaTail, Set.indicator_of_mem (show t ∈ Ioi 1 from ht)]

theorem thetaTail_isBigO_bot (z : ℍ) (r : ℝ) : thetaTail z =O[𝓝[>] 0] (· ^ r) := by
  refine (isBigO_zero _ _).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have : t ∉ Ioi (1 : ℝ) := fun h ↦ by
    have : (1 : ℝ) < t := h
    linarith [ht.2]
  simp [thetaTail, Set.indicator_of_notMem this]

theorem mellinConvergent_thetaTail (z : ℍ) (s : ℂ) : MellinConvergent (thetaTail z) s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) (locallyIntegrableOn_thetaTail z)
    (thetaTail_isBigO_top z _) (by linarith) (thetaTail_isBigO_bot z _) (by linarith)

/-- **The modified theta function of the FE-pair** is $A_z(t) + t^{-1}A_z(1/t)$. -/
theorem eisPair_f_modif (z : ℍ) {t : ℝ} (ht : 0 < t) :
    (eisPair z).f_modif t = thetaTail z t + ((t⁻¹ : ℝ) : ℂ) * thetaTail z t⁻¹ := by
  simp only [WeakFEPair.f_modif, Pi.add_apply]
  show (Ioi 1).indicator (fun x ↦ thetaZ z x - 1) t +
      (Ioo 0 1).indicator (fun x ↦ thetaZ z x - ((1 : ℂ) * ((x ^ (-(1 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ)) t =
    thetaTail z t + ((t⁻¹ : ℝ) : ℂ) * thetaTail z t⁻¹
  unfold thetaTail
  rcases lt_trichotomy t 1 with h | h | h
  · have h1 : 1 < t⁻¹ := (one_lt_inv₀ ht).2 h
    have hfe := thetaZ_inv z (inv_pos.2 ht)
    rw [one_div, inv_inv] at hfe
    rw [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h' ↦ by
        have : (1 : ℝ) < t := h'
        linarith),
      Set.indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht, h⟩),
      Set.indicator_of_mem (show t⁻¹ ∈ Ioi (1 : ℝ) from h1), hfe, Real.rpow_neg_one]
    simp only [smul_eq_mul, mul_one, one_mul, zero_add]
    push_cast
    ring
  · subst h
    simp
  · have h1 : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
    rw [Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h),
      Set.indicator_of_notMem (show t ∉ Ioo (0 : ℝ) 1 from fun h' ↦ by linarith [h'.2]),
      Set.indicator_of_notMem (show t⁻¹ ∉ Ioi (1 : ℝ) from fun h' ↦ by
        have : (1 : ℝ) < t⁻¹ := h'
        linarith)]
    simp

/-- **The entire part as two Mellin integrals:** $E^*_0(z,s) = \mathcal MA_z(s) + \mathcal MA_z(1-s)$. -/
theorem eisensteinReg_eq_mellin (z : ℍ) (s : ℂ) :
    eisensteinReg z s = mellin (thetaTail z) s + mellin (thetaTail z) (1 - s) := by
  have hB : mellin (fun t : ℝ ↦ ((t⁻¹ : ℝ) : ℂ) * thetaTail z t⁻¹) s = mellin (thetaTail z) (1 - s) := by
    have e : mellin (fun t : ℝ ↦ ((t⁻¹ : ℝ) : ℂ) * thetaTail z t⁻¹) s =
        mellin (fun t : ℝ ↦ (t : ℂ) ^ (-1 : ℂ) • thetaTail z t⁻¹) s := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht : 0 < t := ht
      simp only [smul_eq_mul]
      rw [Complex.cpow_neg_one, Complex.ofReal_inv]
    rw [e, mellin_cpow_smul, mellin_comp_inv]
    congr 1
    ring
  have hcB : MellinConvergent (fun t : ℝ ↦ ((t⁻¹ : ℝ) : ℂ) * thetaTail z t⁻¹) s := by
    have e : MellinConvergent (fun t : ℝ ↦ ((t⁻¹ : ℝ) : ℂ) * thetaTail z t⁻¹) s ↔
        MellinConvergent (fun t : ℝ ↦ (t : ℂ) ^ (-1 : ℂ) • thetaTail z t⁻¹) s := by
      refine integrableOn_congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
      have ht : 0 < t := ht
      simp only [smul_eq_mul]
      rw [Complex.cpow_neg_one, Complex.ofReal_inv]
    rw [e, MellinConvergent.cpow_smul]
    have h2 : MellinConvergent (fun t : ℝ ↦ thetaTail z (t ^ (-1 : ℝ))) (s + -1) := by
      rw [MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0)]
      exact mellinConvergent_thetaTail z _
    refine (integrableOn_congr_fun (fun t ht ↦ ?_) measurableSet_Ioi).1 h2
    have ht : 0 < t := ht
    simp only [Real.rpow_neg_one]
  have h := (hasMellin_add (mellinConvergent_thetaTail z s) hcB).2
  rw [← hB, ← h]
  unfold eisensteinReg WeakFEPair.Λ₀
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  simp only [eisPair_f_modif z ht]

/-! ### The bound -/

/-- **The tail bound.** There is $K$ with $|\theta_z(t) - 1| \le Ky\,e^{-b(y)(t-1)}$ for $\operatorname{Im}z \ge \tfrac12$,
$t \ge 1$, $b(y) = \pi\min(1,y^2)/y$. -/
theorem norm_thetaZ_sub_one_le : ∃ K > (0 : ℝ), ∀ z : ℍ, 1 / 2 ≤ z.im → ∀ t : ℝ, 1 ≤ t →
    ‖thetaZ z t - 1‖ ≤ K * z.im * Real.exp (-(π * min 1 (z.im ^ 2) / z.im) * (t - 1)) := by
  obtain ⟨B, hB, hbd⟩ := tsum_norm_term_le (a := 1) (lam := 0) (c := cOff) (C := 1) le_rfl norm_cOff_le
  refine ⟨6 * B, by positivity, fun z hz t ht ↦ ?_⟩
  have hy := z.im_pos
  have hu₁ : 0 < 1 / (2 * z.im) := by positivity
  have hu₁1 : 1 / (2 * z.im) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hle : 1 / (2 * z.im) ≤ t / z.im := by
    rw [div_le_div_iff₀ (by positivity) hy]; nlinarith
  rw [thetaZ_sub_one z (by linarith)]
  refine (norm_genTheta_le_shift le_rfl cOff_zero norm_cOff_le z hu₁ hle).trans ?_
  have h1 := hbd z (1 / (2 * z.im)) hu₁ hu₁1
  have h2 : (1 / (2 * z.im)) ^ (-((0 : ℕ) : ℝ) - 1) = 2 * z.im := by
    rw [Nat.cast_zero, neg_zero, zero_sub, Real.rpow_neg_one, one_div, inv_inv]
  rw [h2] at h1
  have h3 : B * (1 + z.im⁻¹) * (2 * z.im) ≤ 6 * B * z.im := by
    have e : B * (1 + z.im⁻¹) * (2 * z.im) = 2 * B * z.im + 2 * B := by
      field_simp
    rw [e]
    nlinarith
  have hm : 0 ≤ min 1 (z.im ^ 2) := by positivity
  have h4 : Real.exp (-π * (t / z.im - 1 / (2 * z.im)) * min 1 (z.im ^ 2)) ≤
      Real.exp (-(π * min 1 (z.im ^ 2) / z.im) * (t - 1)) := by
    apply Real.exp_le_exp.2
    have e1 : -π * (t / z.im - 1 / (2 * z.im)) * min 1 (z.im ^ 2) =
        -(π * min 1 (z.im ^ 2) / z.im) * (t - 1 / 2) := by
      field_simp
    rw [e1]
    have : 0 ≤ π * min 1 (z.im ^ 2) / z.im := by positivity
    nlinarith
  calc _ ≤ Real.exp (-(π * min 1 (z.im ^ 2) / z.im) * (t - 1)) * (6 * B * z.im) :=
        mul_le_mul h4 (h1.trans h3) (tsum_nonneg fun _ ↦ norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- $\int_0^\infty t^{M}e^{-bt}\,dt = \Gamma(M+1)\,b^{-(M+1)}$, as an integrable majorant. -/
theorem integrableOn_rpow_exp (M : ℝ) (hM : 0 ≤ M) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ ↦ t ^ M * Real.exp (-(b * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := M) (b := b) (by linarith) one_pos hb
  refine this.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

theorem integral_rpow_exp (M : ℝ) (hM : 0 ≤ M) {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ M * Real.exp (-(b * t)) = (1 / b) ^ (M + 1) * Real.Gamma (M + 1) := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb]
  simp

/-- **The Mellin bound of the tail:** for $\operatorname{Re}s - 1 \le M$, $M \ge 0$, $\operatorname{Im}z \ge \tfrac12$:
$|\mathcal MA_z(s)| \le Ky\,e^{b}\,\Gamma(M+1)\,b^{-(M+1)}$. -/
theorem norm_mellin_thetaTail_le {K : ℝ} (hK : 0 < K)
    (hKb : ∀ z : ℍ, 1 / 2 ≤ z.im → ∀ t : ℝ, 1 ≤ t →
      ‖thetaZ z t - 1‖ ≤ K * z.im * Real.exp (-(π * min 1 (z.im ^ 2) / z.im) * (t - 1)))
    (z : ℍ) (hz : 1 / 2 ≤ z.im) {M : ℝ} (hM : 0 ≤ M) {s : ℂ} (hs : s.re - 1 ≤ M) :
    ‖mellin (thetaTail z) s‖ ≤ K * z.im * Real.exp (π * min 1 (z.im ^ 2) / z.im) *
      ((1 / (π * min 1 (z.im ^ 2) / z.im)) ^ (M + 1) * Real.Gamma (M + 1)) := by
  have hy := z.im_pos
  set b := π * min 1 (z.im ^ 2) / z.im with hb
  have hb0 : 0 < b := by positivity
  set g : ℝ → ℝ := fun t ↦ K * z.im * Real.exp b * (t ^ M * Real.exp (-(b * t))) with hg
  have hgi : Integrable g (volume.restrict (Ioi 0)) :=
    (integrableOn_rpow_exp M hM hb0).const_mul _
  have hbound : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • thetaTail z t‖ ≤ g t := by
    intro t ht
    have ht : 0 < t := ht
    by_cases h1 : 1 < t
    · rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
      unfold thetaTail
      rw [Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1)]
      have h2 := hKb z hz t h1.le
      have h3 : t ^ (s - 1).re ≤ t ^ M := by
        apply Real.rpow_le_rpow_of_exponent_le h1.le
        simpa using hs
      have h4 : Real.exp (-b * (t - 1)) = Real.exp b * Real.exp (-(b * t)) := by
        rw [← Real.exp_add]; ring_nf
      rw [h4] at h2
      calc t ^ (s - 1).re * ‖thetaZ z t - 1‖ ≤ t ^ M * (K * z.im * (Real.exp b * Real.exp (-(b * t)))) :=
            mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
        _ = g t := by simp only [hg]; ring
    · unfold thetaTail
      rw [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from h1), smul_zero, norm_zero]
      positivity
  have hint : ∫ t in Ioi (0 : ℝ), g t = K * z.im * Real.exp b * ((1 / b) ^ (M + 1) * Real.Gamma (M + 1)) := by
    simp only [hg]
    rw [integral_const_mul, integral_rpow_exp M hM hb0]
  rw [mellin, ← hint]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) hgi ?_
  exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hbound)

/-- **The polynomial bound of the entire part** on vertical strips, for $\operatorname{Im}z \ge \tfrac12$:
$|E^*_0(z,s)| \le B\,y^A$. -/
theorem norm_eisensteinReg_le (σ₁ σ₂ : ℝ) : ∃ A B : ℝ, ∀ z : ℍ, 1 / 2 ≤ z.im → ∀ s : ℂ,
    σ₁ ≤ s.re → s.re ≤ σ₂ → ‖eisensteinReg z s‖ ≤ B * z.im ^ A := by
  obtain ⟨K, hK, hKb⟩ := norm_thetaZ_sub_one_le
  set M : ℝ := max (max (σ₂ - 1) (-σ₁)) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨M + 2, 2 * (K * Real.exp π * ((5 / π) ^ (M + 1) * Real.Gamma (M + 1))),
    fun z hz s h1 h2 ↦ ?_⟩
  have hy := z.im_pos
  set b := π * min 1 (z.im ^ 2) / z.im with hb
  have hb0 : 0 < b := by positivity
  -- `b ≤ π` and `1/b ≤ 5y/π`
  have hbπ : b ≤ π := by
    rw [hb, div_le_iff₀ hy]
    rcases le_total z.im 1 with h | h
    · have : min 1 (z.im ^ 2) ≤ z.im ^ 2 := min_le_right _ _
      calc π * min 1 (z.im ^ 2) ≤ π * z.im ^ 2 := mul_le_mul_of_nonneg_left this Real.pi_pos.le
        _ ≤ π * z.im := mul_le_mul_of_nonneg_left (by nlinarith) Real.pi_pos.le
    · have : min 1 (z.im ^ 2) ≤ 1 := min_le_left _ _
      calc π * min 1 (z.im ^ 2) ≤ π * 1 := mul_le_mul_of_nonneg_left this Real.pi_pos.le
        _ ≤ π * z.im := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  have hbinv : 1 / b ≤ 5 / π * z.im := by
    rw [hb, one_div_div, div_le_iff₀ (by positivity)]
    rcases le_total z.im 1 with h | h
    · rw [min_eq_right (by nlinarith)]
      have : 5 / π * z.im * (π * z.im ^ 2) = 5 * z.im ^ 3 := by field_simp
      rw [this]; nlinarith
    · rw [min_eq_left (by nlinarith)]
      have : 5 / π * z.im * (π * 1) = 5 * z.im := by field_simp
      rw [this]; linarith
  have key : ∀ w : ℂ, w.re - 1 ≤ M → ‖mellin (thetaTail z) w‖ ≤
      K * Real.exp π * ((5 / π) ^ (M + 1) * Real.Gamma (M + 1)) * z.im ^ (M + 2) := by
    intro w hw
    refine (norm_mellin_thetaTail_le hK hKb z hz hM0 hw).trans ?_
    have hG : 0 ≤ Real.Gamma (M + 1) := (Real.Gamma_pos_of_pos (by linarith)).le
    have e1 : Real.exp (π * min 1 (z.im ^ 2) / z.im) ≤ Real.exp π := Real.exp_le_exp.2 hbπ
    have e2 : (1 / (π * min 1 (z.im ^ 2) / z.im)) ^ (M + 1) ≤ (5 / π * z.im) ^ (M + 1) :=
      Real.rpow_le_rpow (by positivity) hbinv (by linarith)
    have e3 : (5 / π * z.im) ^ (M + 1) = (5 / π) ^ (M + 1) * z.im ^ (M + 1) :=
      Real.mul_rpow (by positivity) hy.le
    have e4 : z.im * z.im ^ (M + 1) = z.im ^ (M + 2) := by
      rw [show M + 2 = 1 + (M + 1) by ring, Real.rpow_add hy 1 (M + 1), Real.rpow_one]
    calc K * z.im * Real.exp (π * min 1 (z.im ^ 2) / z.im) *
          ((1 / (π * min 1 (z.im ^ 2) / z.im)) ^ (M + 1) * Real.Gamma (M + 1))
        ≤ K * z.im * Real.exp π * ((5 / π * z.im) ^ (M + 1) * Real.Gamma (M + 1)) := by
          gcongr
      _ = K * Real.exp π * ((5 / π) ^ (M + 1) * Real.Gamma (M + 1)) * (z.im * z.im ^ (M + 1)) := by
          rw [e3]; ring
      _ = _ := by rw [e4]
  rw [eisensteinReg_eq_mellin]
  have k1 := key s (by
    have := le_max_left (max (σ₂ - 1) (-σ₁)) 0
    have := le_max_left (σ₂ - 1) (-σ₁)
    linarith)
  have k2 := key (1 - s) (by
    have := le_max_left (max (σ₂ - 1) (-σ₁)) 0
    have := le_max_right (σ₂ - 1) (-σ₁)
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  calc _ ≤ ‖mellin (thetaTail z) s‖ + ‖mellin (thetaTail z) (1 - s)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ### Continuity in `z` -/

/-- **Joint continuity of the weight-0 theta series** along a continuous positive parameter $u(z)$. -/
theorem continuousAt_genTheta_comp {a : ℕ} (ha : 1 ≤ a) {c : ℤ × ℤ → ℂ} {C : ℝ}
    (hc : ∀ p, ‖c p‖ ≤ C) {u : ℍ → ℝ} (hu : Continuous u) {z₀ : ℍ} (hu₀ : 0 < u z₀) :
    ContinuousAt (fun z ↦ genTheta a 0 c z (u z)) z₀ := by
  set W : Set ℍ := {w | ‖(w : ℂ) - z₀‖ < z₀.im / 4} ∩ {w | u z₀ / 2 < u w} with hW
  have hWo : IsOpen W :=
    (isOpen_lt (UpperHalfPlane.continuous_coe.sub continuous_const).norm continuous_const).inter
      (isOpen_lt continuous_const hu)
  have hz₀ : z₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · show ‖(z₀ : ℂ) - z₀‖ < z₀.im / 4
      rw [sub_self, norm_zero]
      have := z₀.im_pos
      positivity
    · show u z₀ / 2 < u z₀
      linarith
  have hon : ContinuousOn (fun z ↦ genTheta a 0 c z (u z)) W := by
    unfold genTheta
    refine continuousOn_tsum (u := fun p : ℤ × ℤ ↦
      C * Real.exp (-π * (u z₀ / 4) * ‖genVec a z₀ p‖ ^ 2)) (fun p ↦ ?_)
      ((summable_gauss_lattice (a := a) ha z₀ (by positivity : 0 < u z₀ / 4)).mul_left _)
      (fun p w hw ↦ ?_)
    · have hv : Continuous fun w : ℍ ↦ genVec a w p := by
        unfold genVec
        exact (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
      exact (continuous_const.mul (hv.pow 0) |>.mul (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_const.mul hu).mul (hv.norm.pow 2))))).continuousOn
    · rw [term_norm]
      have h2 := normSq_nbhd a z₀ w hw.1 p
      have hu' : u z₀ / 2 < u w := hw.2
      simp only [pow_zero, mul_one]
      have h3 : Real.exp (-π * u w * ‖genVec a w p‖ ^ 2) ≤
          Real.exp (-π * (u z₀ / 4) * ‖genVec a z₀ p‖ ^ 2) := by
        apply Real.exp_le_exp.2
        have hA : 0 ≤ ‖genVec a z₀ p‖ ^ 2 := sq_nonneg _
        have h4 := mul_le_mul hu'.le h2 (by positivity) (by linarith)
        have h5 : u z₀ / 4 * ‖genVec a z₀ p‖ ^ 2 ≤ u w * ‖genVec a w p‖ ^ 2 := by
          nlinarith
        nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left h5 Real.pi_pos.le]
      exact mul_le_mul (hc p) h3 (Real.exp_pos _).le ((norm_nonneg _).trans (hc p))
  exact hon.continuousAt (hWo.mem_nhds hz₀)

theorem continuousAt_thetaZ (t : ℝ) (ht : 0 < t) (z₀ : ℍ) :
    ContinuousAt (fun z ↦ thetaZ z t) z₀ := by
  unfold thetaZ
  exact continuousAt_genTheta_comp (c := fun _ ↦ (1 : ℂ)) le_rfl norm_one_le
    (continuous_const.div UpperHalfPlane.continuous_im fun z ↦ z.im_pos.ne')
    (div_pos ht z₀.im_pos)

/-- **Continuity in $z$** of the Mellin transform of the tail, on $\operatorname{Im}z > \tfrac12$. -/
theorem continuousOn_mellin_thetaTail (s : ℂ) :
    ContinuousOn (fun z : ℍ ↦ mellin (thetaTail z) s) {z | 1 / 2 < z.im} := by
  obtain ⟨K, hK, hKb⟩ := norm_thetaZ_sub_one_le
  intro z₀ hz₀
  have hz₀' : 1 / 2 < z₀.im := hz₀
  set δ := (z₀.im - 1 / 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set V : Set ℍ := {z | z₀.im - δ < z.im} ∩ {z | z.im < z₀.im + δ} with hV
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
      (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
  have hzV : z₀ ∈ V := ⟨by show z₀.im - δ < z₀.im; linarith, by show z₀.im < z₀.im + δ; linarith⟩
  set M : ℝ := max (s.re - 1) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hlow : 1 / 2 < z₀.im - δ := by rw [hδ]; linarith
  set b₀ : ℝ := π * min 1 ((z₀.im - δ) ^ 2) / (z₀.im + δ) with hb₀
  have hb₀0 : 0 < b₀ := by
    have : 0 < z₀.im - δ := by linarith
    have : 0 < z₀.im + δ := by linarith
    positivity
  set g : ℝ → ℝ := fun t ↦ K * (z₀.im + δ) * Real.exp b₀ * (t ^ M * Real.exp (-(b₀ * t))) with hg
  refine ContinuousAt.continuousWithinAt ?_
  unfold mellin
  refine continuousAt_of_dominated (bound := g) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun z ↦ (mellinConvergent_thetaTail z s).aestronglyMeasurable
  · filter_upwards [hVo.mem_nhds hzV] with z hz
    have hz1 : z₀.im - δ < z.im := hz.1
    have hz2 : z.im < z₀.im + δ := hz.2
    have hy := z.im_pos
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_)
    have ht : 0 < t := ht
    by_cases h1 : 1 < t
    · rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
      unfold thetaTail
      rw [Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1)]
      have h2 := hKb z (by linarith) t h1.le
      have h3 : t ^ (s - 1).re ≤ t ^ M := by
        apply Real.rpow_le_rpow_of_exponent_le h1.le
        simp only [Complex.sub_re, Complex.one_re]
        exact le_max_left _ _
      have hbz : b₀ ≤ π * min 1 (z.im ^ 2) / z.im := by
        rw [hb₀]
        have h0 : 0 ≤ z₀.im - δ := by linarith
        gcongr
      have h4 : Real.exp (-(π * min 1 (z.im ^ 2) / z.im) * (t - 1)) ≤
          Real.exp b₀ * Real.exp (-(b₀ * t)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith
      have h5 : K * z.im ≤ K * (z₀.im + δ) := mul_le_mul_of_nonneg_left hz2.le hK.le
      calc t ^ (s - 1).re * ‖thetaZ z t - 1‖
          ≤ t ^ M * (K * (z₀.im + δ) * (Real.exp b₀ * Real.exp (-(b₀ * t)))) := by
            refine mul_le_mul h3 (h2.trans ?_) (norm_nonneg _) (by positivity)
            exact mul_le_mul h5 h4 (Real.exp_pos _).le (by positivity)
        _ = g t := by simp only [hg]; ring
    · unfold thetaTail
      rw [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from h1), smul_zero, norm_zero]
      simp only [hg]
      have : 0 < z₀.im + δ := by linarith
      positivity
  · exact (integrableOn_rpow_exp M hM0 hb₀0).const_mul _
  · refine ae_of_all _ fun t ↦ ?_
    by_cases h1 : 1 < t
    · have e : (fun z : ℍ ↦ (t : ℂ) ^ (s - 1) • thetaTail z t) =
          fun z ↦ (t : ℂ) ^ (s - 1) * (thetaZ z t - 1) := by
        funext z
        unfold thetaTail
        rw [Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1), smul_eq_mul]
      rw [e]
      exact continuousAt_const.mul ((continuousAt_thetaZ t (by linarith) z₀).sub continuousAt_const)
    · have e : (fun z : ℍ ↦ (t : ℂ) ^ (s - 1) • thetaTail z t) = fun _ ↦ 0 := by
        funext z
        unfold thetaTail
        rw [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from h1), smul_zero]
      rw [e]
      exact continuousAt_const

/-- **Continuity of the entire part in $z$** on $\operatorname{Im}z > \tfrac12$ (an open set containing the
fundamental domain). -/
theorem continuousOn_eisensteinReg (s : ℂ) :
    ContinuousOn (fun z : ℍ ↦ eisensteinReg z s) {z | 1 / 2 < z.im} := by
  simp_rw [eisensteinReg_eq_mellin]
  exact (continuousOn_mellin_thetaTail s).add (continuousOn_mellin_thetaTail (1 - s))

end ModularFormsKB.RankinSelberg
