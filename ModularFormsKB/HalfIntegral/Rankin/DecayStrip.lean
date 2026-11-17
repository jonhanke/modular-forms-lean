/-
# Decay of the Rankin kernel at a cusp, on vertical half-strips

`rankinKernel_bound_fd` (`Decay.lean`) bounds $G(\gamma\tau)$ for $\tau$ in the fundamental domain. The unfolding at the
cusps other than $\infty$ (`FrickeCoset.lean`) needs the same decay on vertical half-strips $|\operatorname{Re}\tau| \le X$,
$\operatorname{Im}\tau \ge 1$ (`rankinKernel_bound_strip`): $\|G(\gamma\tau)\| \le C(\operatorname{Im}\tau)^{-A}$ for every
$A$, from the rapid decay of $|c\tau+d|^{-(k+1/2)}|f(\gamma\tau)|$ (`MultiplierSystem.tendsto_cuspNorm_sq_mul`) and
compactness of the part of the strip below the height where that decay takes over.
-/
import ModularFormsKB.HalfIntegral.Rankin.Decay

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane Filter
open scoped Real

theorem stripDecay_isCompact (X Y : ℝ) :
    IsCompact {τ : UpperHalfPlane | |(τ : ℂ).re| ≤ X ∧ 1 ≤ τ.im ∧ τ.im ≤ Y} := by
  have hK : IsCompact ((Set.Icc (-X) X) ×ℂ (Set.Icc (1 : ℝ) Y)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  convert hK using 1
  ext z
  rw [Complex.mem_reProdIm]
  constructor
  · rintro ⟨τ, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨Set.mem_Icc.2 (abs_le.1 h1), Set.mem_Icc.2 ⟨h2, h3⟩⟩
  · rintro ⟨h1, h2⟩
    have h1' := abs_le.2 (Set.mem_Icc.1 h1)
    have h2' := Set.mem_Icc.1 h2
    have hz : 0 < z.im := by linarith [h2'.1]
    exact ⟨⟨z, hz⟩, ⟨h1', h2'.1, h2'.2⟩, rfl⟩

theorem stripDecay_pointwise (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    {f : UpperHalfPlane → ℂ} {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ}
    (hθ : ∃ C : ℝ, ∀ τ : UpperHalfPlane, ‖thetaTwist ψ t τ‖ ≤ C * (1 + τ.im ^ (-2 : ℝ)))
    (γ : SL(2, ℤ)) (X : ℝ) (hf : f ∈ M.cuspForms k N χ) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ τ : UpperHalfPlane, |(τ : ℂ).re| ≤ X → 1 ≤ τ.im →
      ‖rankinKernel k ψ t f (γ • τ)‖ ≤
        K0 * (Abstract.cuspNorm k f γ τ *
          τ.im ^ (((k : ℝ) + 1 / 2) + 2 + ((k + charParity ψ + 1 : ℕ) : ℝ) / 2)) := by
  obtain ⟨C0, hC0⟩ := hθ
  set C : ℝ := |C0| with hCdef
  have hC0n : 0 ≤ C := abs_nonneg _
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ) with hc
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ) with hd
  set w : ℝ := (k : ℝ) + 1 / 2 with hw
  set β : ℝ := ((k + charParity ψ + 1 : ℕ) : ℝ) / 2 with hβ
  have hw0 : 0 ≤ w := by positivity
  have hβ0 : 0 ≤ β := by positivity
  set B0 : ℝ := w + 2 + β with hB0
  have hDne : ∀ τ : ℍ, ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ≠ 0 := by
    intro τ
    rw [← denom_SL_eq]; exact (norm_pos_iff.2 (denom_ne_zero _ τ)).ne'
  have hcd : 1 ≤ c ^ 2 + d ^ 2 := by
    have hz : 1 ≤ (γ 1 0) ^ 2 + (γ 1 1) ^ 2 := by
      by_contra hlt; push_neg at hlt
      have h0 : γ 1 0 = 0 := by nlinarith
      have h1 : γ 1 1 = 0 := by nlinarith
      have := γ.det_coe
      rw [Matrix.det_fin_two, h0, h1] at this
      simp at this
    have : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2 := by exact_mod_cast hz
    exact this
  have hcases : c = 0 ∨ 1 ≤ c ^ 2 := by
    by_cases h0 : γ 1 0 = 0
    · left; simp [hc, h0]
    · right
      have h1 : 0 < (γ 1 0) ^ 2 := by positivity
      have h2 : 1 ≤ (γ 1 0) ^ 2 := h1
      have : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 := by exact_mod_cast h2
      exact this
  set m : ℝ := |c| * (|X| + 1) + |d| + 1 with hm
  have hm1 : 1 ≤ m := by
    have := abs_nonneg c; have := abs_nonneg d
    have := mul_nonneg (abs_nonneg c) (by positivity : (0:ℝ) ≤ |X| + 1)
    linarith
  refine ⟨2 * C * (m ^ 2) ^ B0, by positivity, fun τ hx hy ↦ ?_⟩
  have hu : 0 < τ.im := τ.im_pos
  set u := τ.im with hu_def
  set D := ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ with hD
  have hDpos : 0 < D := lt_of_le_of_ne (norm_nonneg _) (hDne τ).symm
  have hD2eq : D ^ 2 = (c * (τ : ℂ).re + d) ^ 2 + (c * u) ^ 2 := by
    rw [hD, Complex.sq_norm, Complex.normSq_apply]
    simp [hc, hd, hu_def]
    ring
  have hD1 : 1 ≤ D := by
    have h : 1 ≤ D ^ 2 := by
      rw [hD2eq]
      rcases hcases with h0 | h1
      · rw [h0] at hcd ⊢
        nlinarith [sq_nonneg (0 * (τ : ℂ).re + d)]
      · nlinarith [sq_nonneg (c * (τ : ℂ).re + d), mul_le_mul h1 (by nlinarith : 1 ≤ u ^ 2) zero_le_one
          (sq_nonneg c)]
    by_contra hlt; push_neg at hlt; nlinarith
  have hDle : D ≤ m * u := by
    have h1 : D ≤ |c| * ‖(τ : ℂ)‖ + |d| := by
      calc D ≤ ‖(γ 1 0 : ℂ) * τ‖ + ‖(γ 1 1 : ℂ)‖ := norm_add_le _ _
        _ = |c| * ‖(τ : ℂ)‖ + |d| := by
          rw [norm_mul]
          simp [hc, hd, Complex.norm_intCast]
    have h2 : ‖(τ : ℂ)‖ ≤ (|X| + 1) * u := by
      have := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
      have h3 : |(τ : ℂ).im| = u := abs_of_pos hu
      have : |(τ : ℂ).re| ≤ |X| := hx.trans (le_abs_self X)
      nlinarith [mul_le_mul_of_nonneg_left hy (abs_nonneg X)]
    have := abs_nonneg c
    have := abs_nonneg d
    rw [hm]
    nlinarith [mul_le_mul_of_nonneg_left h2 (abs_nonneg c)]
  have hq : (γ • τ).im = u / D ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, normSq_eq_norm_sq, denom_SL_eq]
  have hqpos : 0 < (γ • τ).im := (γ • τ).im_pos
  set q := (γ • τ).im with hq_def
  set U := m ^ 2 * u with hU
  have hUpos : 0 < U := by positivity
  have hum : u ≤ U := by
    rw [hU]; exact le_mul_of_one_le_left hu.le (one_le_pow₀ hm1)
  have hU1 : 1 ≤ U := hy.trans hum
  have hqU : q ≤ U := by
    rw [hq, div_le_iff₀ (by positivity)]
    have hD12 : 1 ≤ D ^ 2 := one_le_pow₀ hD1
    exact hum.trans (le_mul_of_one_le_right hUpos.le hD12)
  have h1U : 1 / U ≤ q := by
    rw [hq, div_le_div_iff₀ hUpos (by positivity)]
    have h3 : D ^ 2 ≤ (m * u) ^ 2 := pow_le_pow_left₀ hDpos.le hDle 2
    have e : u * U = m ^ 2 * u ^ 2 := by rw [hU]; ring
    have e2 : (m * u) ^ 2 = m ^ 2 * u ^ 2 := by ring
    linarith
  have hDU : D ≤ U := by
    calc D ≤ m * u := hDle
      _ ≤ m ^ 2 * u := mul_le_mul_of_nonneg_right (le_self_pow₀ hm1 (by norm_num)) hu.le
  have hker : ‖rankinKernel k ψ t f (γ • τ)‖ =
      ‖f (γ • τ)‖ * ‖thetaTwist ψ t ((γ • τ : ℍ) : ℂ)‖ * q ^ β := by
    unfold rankinKernel
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hqpos.le _)]
  have hfeq : ‖f (γ • τ)‖ = Abstract.cuspNorm k f γ τ * D ^ w := by
    unfold Abstract.cuspNorm
    rw [mul_right_comm, ← Real.rpow_add hDpos]
    simp [hD, hw]
  have hθ1 : ‖thetaTwist ψ t ((γ • τ : ℍ) : ℂ)‖ ≤ C * (1 + q ^ (-2 : ℝ)) :=
    (hC0 (γ • τ)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hq2 : q ^ (-2 : ℝ) ≤ U ^ (2 : ℝ) := by
    have := rpow_le_rpow_abs_aux hqpos h1U hqU (-2)
    simpa using this
  have hU2 : 1 ≤ U ^ (2 : ℝ) := Real.one_le_rpow hU1 (by norm_num)
  have hθ2 : ‖thetaTwist ψ t ((γ • τ : ℍ) : ℂ)‖ ≤ C * (2 * U ^ (2 : ℝ)) :=
    hθ1.trans (mul_le_mul_of_nonneg_left (by linarith) hC0n)
  have hqβ : q ^ β ≤ U ^ β := Real.rpow_le_rpow hqpos.le hqU hβ0
  have hDw : D ^ w ≤ U ^ w := Real.rpow_le_rpow hDpos.le hDU hw0
  have hcn : 0 ≤ Abstract.cuspNorm k f γ τ :=
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  have hUB : U ^ B0 = U ^ w * U ^ (2 : ℝ) * U ^ β := by
    rw [hB0, Real.rpow_add hUpos, Real.rpow_add hUpos]
  have hUu : U ^ B0 = (m ^ 2) ^ B0 * u ^ B0 := Real.mul_rpow (by positivity) hu.le
  have hθn := norm_nonneg (thetaTwist ψ t ((γ • τ : ℍ) : ℂ))
  have hDw0 : 0 ≤ D ^ w := Real.rpow_nonneg hDpos.le _
  calc ‖rankinKernel k ψ t f (γ • τ)‖
      = (Abstract.cuspNorm k f γ τ * D ^ w) * ‖thetaTwist ψ t ((γ • τ : ℍ) : ℂ)‖ * q ^ β := by
        rw [hker, hfeq]
    _ ≤ (Abstract.cuspNorm k f γ τ * U ^ w) * (C * (2 * U ^ (2 : ℝ))) * U ^ β := by
        have hq0 : 0 ≤ q ^ β := Real.rpow_nonneg hqpos.le _
        have hUβ : 0 ≤ U ^ β := Real.rpow_nonneg hUpos.le _
        gcongr
    _ = 2 * C * (Abstract.cuspNorm k f γ τ * U ^ B0) := by rw [hUB]; ring
    _ = _ := by rw [hUu]; ring

theorem rankinKernel_bound_strip (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hN : 0 < N)
    {f : UpperHalfPlane → ℂ} (hf : f ∈ M.cuspForms k N χ) {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ}
    (hθc : Continuous fun τ : UpperHalfPlane ↦ thetaTwist ψ t τ)
    (hθ : ∃ C : ℝ, ∀ τ : UpperHalfPlane, ‖thetaTwist ψ t τ‖ ≤ C * (1 + τ.im ^ (-2 : ℝ)))
    (γ : SL(2, ℤ)) (X A : ℝ) :
    ∃ C : ℝ, ∀ τ : UpperHalfPlane, |(τ : ℂ).re| ≤ X → 1 ≤ τ.im →
      ‖rankinKernel k ψ t f (γ • τ)‖ ≤ C * τ.im ^ (-A) := by
  obtain ⟨K0, hK0, hpt⟩ := stripDecay_pointwise M ψ hθ γ X hf
  set B0 : ℝ := ((k : ℝ) + 1 / 2) + 2 + ((k + charParity ψ + 1 : ℕ) : ℝ) / 2 with hB0
  have hten := MultiplierSystem.tendsto_cuspNorm_sq_mul M k N hN χ hf γ (2 * (B0 + |A|))
  have hev : ∀ᶠ τ : ℍ in atImInfty,
      Abstract.cuspNorm k f γ τ ^ 2 * τ.im ^ (2 * (B0 + |A|)) < 1 :=
    hten.eventually (gt_mem_nhds one_pos)
  obtain ⟨Y0, hY0⟩ := (UpperHalfPlane.atImInfty_mem _).1 hev
  set Y := max Y0 1 with hY
  have hY1 : 1 ≤ Y := le_max_right _ _
  have hcn_nn : ∀ τ : ℍ, 0 ≤ Abstract.cuspNorm k f γ τ := fun τ ↦
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  have hγ : Continuous (fun τ : ℍ ↦ γ • τ) := continuous_const_smul (γ : GL (Fin 2) ℝ)
  have hcont : Continuous fun τ : ℍ ↦ ‖rankinKernel k ψ t f (γ • τ)‖ := by
    have h1 : Continuous fun τ : ℍ ↦ f (γ • τ) := (hf.holo.continuous).comp hγ
    have h2 : Continuous fun τ : ℍ ↦ thetaTwist ψ t ((γ • τ : ℍ) : ℂ) := hθc.comp hγ
    have h3 : Continuous fun τ : ℍ ↦ (((γ • τ).im ^ (((k + charParity ψ + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        (((UpperHalfPlane.continuous_im.comp hγ)).rpow_const fun τ ↦ Or.inl (γ • τ).im_pos.ne')
    have h4 : Continuous fun τ : ℍ ↦ rankinKernel k ψ t f (γ • τ) :=
      (h1.mul (Complex.continuous_conj.comp h2)).mul h3
    exact h4.norm
  obtain ⟨K', hK'⟩ := (stripDecay_isCompact X Y).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max K0 (|K'| * Y ^ |A|), fun τ hx hy ↦ ?_⟩
  have hu : 0 < τ.im := τ.im_pos
  have hypos : 0 < τ.im ^ (-A) := Real.rpow_pos_of_pos hu _
  rcases le_or_gt Y τ.im with hYy | hYy
  · have h1 := hY0 τ (le_trans (le_max_left _ _) hYy)
    have hE : Abstract.cuspNorm k f γ τ * τ.im ^ (B0 + |A|) ≤ 1 := by
      have hsq : (Abstract.cuspNorm k f γ τ * τ.im ^ (B0 + |A|)) ^ 2 < 1 := by
        have : (Abstract.cuspNorm k f γ τ * τ.im ^ (B0 + |A|)) ^ 2 =
            Abstract.cuspNorm k f γ τ ^ 2 * τ.im ^ (2 * (B0 + |A|)) := by
          rw [mul_pow, ← Real.rpow_natCast (τ.im ^ (B0 + |A|)) 2, ← Real.rpow_mul hu.le]
          norm_num; left; rw [mul_comm]
        rw [this]; exact h1
      have hnn : 0 ≤ Abstract.cuspNorm k f γ τ * τ.im ^ (B0 + |A|) :=
        mul_nonneg (hcn_nn τ) (Real.rpow_nonneg hu.le _)
      nlinarith
    have hy1 : 1 ≤ τ.im := hy
    have h2 : Abstract.cuspNorm k f γ τ * τ.im ^ B0 ≤ τ.im ^ (-|A|) := by
      have : τ.im ^ (B0 + |A|) = τ.im ^ B0 * τ.im ^ |A| := Real.rpow_add hu _ _
      rw [this, ← mul_assoc] at hE
      have hp : 0 < τ.im ^ |A| := Real.rpow_pos_of_pos hu _
      rw [Real.rpow_neg hu.le, ← one_div, le_div_iff₀ hp]
      exact hE
    have h3 : τ.im ^ (-|A|) ≤ τ.im ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by linarith [neg_abs_le A, le_abs_self A])
    calc ‖rankinKernel k ψ t f (γ • τ)‖ ≤ K0 * (Abstract.cuspNorm k f γ τ * τ.im ^ B0) := hpt τ hx hy
      _ ≤ K0 * τ.im ^ (-A) := mul_le_mul_of_nonneg_left (h2.trans h3) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hypos.le
  · have hmem : τ ∈ {τ : UpperHalfPlane | |(τ : ℂ).re| ≤ X ∧ 1 ≤ τ.im ∧ τ.im ≤ Y} :=
      ⟨hx, hy, hYy.le⟩
    have h1 := hK' τ hmem
    rw [Real.norm_of_nonneg (norm_nonneg _)] at h1
    have h2 := rpow_le_rpow_abs_aux hu (by
      rw [div_le_iff₀ (by linarith)]; nlinarith) hYy.le A
    have hYp : 0 < Y ^ |A| := Real.rpow_pos_of_pos (by linarith) _
    have h3 : (Y ^ |A|)⁻¹ ≤ τ.im ^ (-A) := by
      rw [Real.rpow_neg hu.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hu _) h2
    have h4 : |K'| ≤ |K'| * Y ^ |A| * τ.im ^ (-A) := by
      have : |K'| = |K'| * Y ^ |A| * (Y ^ |A|)⁻¹ := by field_simp
      calc |K'| = |K'| * Y ^ |A| * (Y ^ |A|)⁻¹ := this
        _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
    calc ‖rankinKernel k ψ t f (γ • τ)‖ ≤ K' := h1
      _ ≤ |K'| := le_abs_self _
      _ ≤ |K'| * Y ^ |A| * τ.im ^ (-A) := h4
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hypos.le

end ModularFormsKB.HalfIntegral
