/-
# The Petersson product is definite on cusp forms

Proves the named input `PeterssonDefinite` of `ModularFormsKB/HalfIntegral/Abstract/KohnenZagierReduction.lean`:
- $\langle g, g\rangle \ne 0$ for $0 \ne g \in S_{k+1/2}(4N, \chi)$, $N \ge 1$, relative to any multiplier system
  (`MultiplierSystem.peterssonNormSqFour_ne_zero`), in particular on Kohnen's plus space;
- $\langle F, F\rangle \ne 0$ for $0 \ne F \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ (`peterssonNormSqOne_ne_zero`), using Mathlib's
  boundedness of $|F|^2 v^{2k}$ (`CuspFormClass.petersson_bounded_left`);
and hence the Kohnen–Zagier formula from the four remaining named inputs (`kohnenZagier_of_four_inputs`).

It also records that `peterssonFour` is additive in each argument on $S_{k+1/2}(4N,\chi)$.

**Proof of definiteness.** The norm is $\tfrac16$ times a sum of six nonnegative integrals; the one for $\gamma = 1$ is
$\int_{\mathcal F}|g|^2 v^{k+1/2}\,d\mu$, so it vanishes. The integrand is continuous, nonnegative and integrable, hence zero
almost everywhere on $\mathcal F$, hence everywhere on the open interior $\mathcal F^\circ$ (open sets have positive measure,
`UpperHalfPlaneOpenPos.lean`). A holomorphic function vanishing on a nonempty open subset of the connected $\mathbb H$ is
zero (identity theorem, `eq_zero_of_setIntegral_fd_eq_zero`).
-/
import ModularFormsKB.HalfIntegral.Abstract.PeterssonConvergence
import ModularFormsKB.HalfIntegral.Abstract.UpperHalfPlaneOpenPos
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierReduction

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane Filter MeasureTheory ModularForm
open scoped Real
open scoped Manifold
open scoped Topology

/-- **A holomorphic function on $\mathbb H$ with $\int_{\mathcal F}|h|^2 v^w\,d\mu = 0$ (integrable) is zero.** -/
theorem eq_zero_of_setIntegral_fd_eq_zero {h : ℍ → ℂ} (hh : MDiff h) (w : ℝ)
    (hint : IntegrableOn (fun τ : ℍ ↦ ‖h τ‖ ^ 2 * τ.im ^ w) ModularGroup.fd)
    (h0 : ∫ τ in ModularGroup.fd, ‖h τ‖ ^ 2 * τ.im ^ w = 0) : h = 0 := by
  set φ : ℍ → ℝ := fun τ ↦ ‖h τ‖ ^ 2 * τ.im ^ w
  have hφ0 : 0 ≤ φ := fun τ ↦ mul_nonneg (sq_nonneg _) (Real.rpow_nonneg τ.im_pos.le _)
  have hφc : Continuous φ :=
    (hh.continuous.norm.pow 2).mul (UpperHalfPlane.continuous_im.rpow_const fun τ ↦ Or.inl τ.im_pos.ne')
  have hae : φ =ᵐ[volume.restrict ModularGroup.fd] 0 := (integral_eq_zero_iff_of_nonneg hφ0 hint).1 h0
  have hae' : φ =ᵐ[volume.restrict ModularGroup.fdo] 0 :=
    ae_restrict_of_ae_restrict_of_subset ModularGroup.fdo_subset_fd hae
  have heq := Measure.eqOn_open_of_ae_eq hae' ModularGroup.isOpen_fdo hφc.continuousOn continuousOn_const
  -- `h` vanishes on the interior of the fundamental domain.
  have hfdo : ∀ τ ∈ ModularGroup.fdo, h τ = 0 := fun τ hτ ↦ by
    have := heq hτ
    simp only [φ, Pi.zero_apply, mul_eq_zero, ne_eq, pow_eq_zero_iff, norm_eq_zero, OfNat.ofNat_ne_zero,
      not_false_eq_true] at this
    rcases this with h1 | h1
    · exact h1
    · exact absurd h1 (Real.rpow_pos_of_pos τ.im_pos w).ne'
  -- Identity theorem on the upper half-plane.
  have han : AnalyticOnNhd ℂ (h ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hh).analyticOnNhd isOpen_upperHalfPlaneSet
  set τ₀ : ℍ := ⟨2 * Complex.I, by simp⟩
  have hτ₀ : τ₀ ∈ ModularGroup.fdo := by
    constructor
    · show 1 < Complex.normSq (2 * Complex.I)
      simp [Complex.normSq_apply]
      norm_num
    · show |(2 * Complex.I).re| < 1 / 2
      simp
  have hev : (h ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    have hopen : IsOpen ((↑) '' ModularGroup.fdo : Set ℂ) :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo
    filter_upwards [hopen.mem_nhds ⟨τ₀, hτ₀, rfl⟩] with z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    simp [ofComplex_apply, hfdo τ hτ]
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected (show 0 < (τ₀ : ℂ).im from τ₀.im_pos) hev
  funext τ
  have := hzero (show 0 < (τ : ℂ).im from τ.im_pos)
  simpa [ofComplex_apply] using this

/-- **Additivity of `peterssonFour` in the second argument** on $S_{k+1/2}(4N,\chi)$. -/
theorem MultiplierSystem.peterssonFour_add_right (M : MultiplierSystem) (k N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ (4 * N)) {f g h : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) (hg : g ∈ M.cuspForms k N χ)
    (hh : h ∈ M.cuspForms k N χ) : peterssonFour k f (g + h) = peterssonFour k f g + peterssonFour k f h := by
  rw [peterssonFour, peterssonFour, peterssonFour, peterssonReps_add_right _ _ _ _ _
    (fun γ _ ↦ M.integrableOn_peterssonIntegrand k N hN χ hf hg γ)
    (fun γ _ ↦ M.integrableOn_peterssonIntegrand k N hN χ hf hh γ), mul_add]

/-- **Additivity of `peterssonFour` in the first argument** on $S_{k+1/2}(4N,\chi)$. -/
theorem MultiplierSystem.peterssonFour_add_left (M : MultiplierSystem) (k N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ (4 * N)) {f g h : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) (hg : g ∈ M.cuspForms k N χ)
    (hh : h ∈ M.cuspForms k N χ) : peterssonFour k (f + g) h = peterssonFour k f h + peterssonFour k g h := by
  rw [peterssonFour, peterssonFour, peterssonFour, peterssonReps_add_left _ _ _ _ _
    (fun γ _ ↦ M.integrableOn_peterssonIntegrand k N hN χ hf hh γ)
    (fun γ _ ↦ M.integrableOn_peterssonIntegrand k N hN χ hg hh γ), mul_add]

private theorem integrableOn_self {γ : SL(2, ℤ)} {w : ℝ} {f : ℍ → ℂ}
    (h : IntegrableOn (peterssonIntegrand γ w f f) ModularGroup.fd) :
    IntegrableOn (fun τ ↦ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ w) ModularGroup.fd := by
  refine IntegrableOn.congr_fun (h.norm : IntegrableOn _ _ _) (fun τ _ ↦ ?_) measurableSet_fd
  rw [peterssonIntegrand_self, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (γ • τ).im_pos.le _))]

/-- **Definiteness on $S_{k+1/2}(4N,\chi)$:** $\langle g, g\rangle \ne 0$ for $g \ne 0$. -/
theorem MultiplierSystem.peterssonNormSqFour_ne_zero (M : MultiplierSystem) (k N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ (4 * N)) {g : ℍ → ℂ} (hg : g ∈ M.cuspForms k N χ) (hg0 : g ≠ 0) :
    peterssonNormSqFour k g ≠ 0 := by
  intro h0
  rw [← peterssonFour_self, peterssonFour, peterssonReps_self_eq_ofReal] at h0
  set t : SL(2, ℤ) → ℝ := fun γ ↦ ∫ τ in ModularGroup.fd, ‖g (γ • τ)‖ ^ 2 * (γ • τ).im ^ ((k : ℝ) + 1 / 2)
  have ht : ∀ γ, 0 ≤ t γ := fun γ ↦
    integral_nonneg fun τ ↦ mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (γ • τ).im_pos.le _)
  have hsum : (gamma0FourReps.map t).sum = 0 := by
    have := (mul_eq_zero.1 h0).resolve_left (by norm_num)
    exact_mod_cast this
  have h1 : t 1 = 0 := by
    simp only [gamma0FourReps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    linarith [ht 1, ht ModularGroup.S, ht (ModularGroup.S * ModularGroup.T),
      ht (ModularGroup.S * ModularGroup.T ^ 2), ht (ModularGroup.S * ModularGroup.T ^ 3),
      ht (ModularGroup.S * ModularGroup.T ^ 2 * ModularGroup.S)]
  have hint := integrableOn_self (M.integrableOn_peterssonIntegrand k N hN χ hg hg 1)
  simp only [one_smul] at hint
  simp only [t, one_smul] at h1
  exact hg0 (eq_zero_of_setIntegral_fd_eq_zero hg.holo _ hint h1)

/-- **Definiteness on $S_{2k}(\mathrm{SL}_2(\mathbb Z))$:** $\langle F, F\rangle \ne 0$ for $F \ne 0$. -/
theorem peterssonNormSqOne_ne_zero (k : ℕ) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (hF : F ≠ 0) :
    peterssonNormSqOne k F ≠ 0 := by
  intro h0
  rw [← peterssonOne_self, peterssonOne, peterssonReps_self_eq_ofReal] at h0
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] at h0
  have h1 : ∫ τ in ModularGroup.fd, ‖F τ‖ ^ 2 * τ.im ^ ((2 * k : ℕ) : ℝ) = 0 := by
    exact_mod_cast h0
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left ((2 * k : ℕ) : ℤ) 𝒮ℒ F F
  have hnorm : ∀ τ : ℍ, ‖F τ‖ ^ 2 * τ.im ^ ((2 * k : ℕ) : ℝ) = ‖petersson ((2 * k : ℕ) : ℤ) F F τ‖ := by
    intro τ
    simp only [petersson, norm_mul, Complex.norm_conj, zpow_natCast, Real.rpow_natCast]
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg τ.im_pos.le _)]
    ring
  have hcont : Continuous (fun τ : ℍ ↦ ‖F τ‖ ^ 2 * τ.im ^ ((2 * k : ℕ) : ℝ)) :=
    ((ModularFormClass.holo F).continuous.norm.pow 2).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ ↦ Or.inl τ.im_pos.ne')
  have hint : IntegrableOn (fun τ : ℍ ↦ ‖F τ‖ ^ 2 * τ.im ^ ((2 * k : ℕ) : ℝ)) ModularGroup.fd := by
    refine Measure.integrableOn_of_bounded (M := C) volume_fd_lt_top.ne hcont.aestronglyMeasurable ?_
    refine Eventually.of_forall fun τ ↦ ?_
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg τ.im_pos.le _)), hnorm]
    exact hC τ
  have := eq_zero_of_setIntegral_fd_eq_zero (ModularFormClass.holo F) _ hint h1
  exact hF (DFunLike.ext F 0 fun τ ↦ by simpa using congrFun this τ)

/-- **Input 5 of the reduction is a theorem.** -/
theorem peterssonDefinite (M : MultiplierSystem) (k : ℕ) : PeterssonDefinite M k where
  four _ hg hg0 := M.peterssonNormSqFour_ne_zero k 1 one_pos 1 (M.plusCuspForms_le k 1 1 hg) hg0
  one F hF := peterssonNormSqOne_ne_zero k F hF

/-- **The Kohnen–Zagier formula from the named inputs 1–4** (`KohnenLiftEigen`, `KohnenAdjointInputs`,
`PlusMultiplicityOne`); definiteness is proved. -/
theorem kohnenZagier_of_four_inputs (M : MultiplierSystem) (k : ℕ) (h1 : KohnenLiftEigen M k)
    (h2 : KohnenAdjointInputs M k) (h4 : PlusMultiplicityOne M k) : KohnenZagier M k :=
  kohnenZagier_of_inputs M k h1 h2 h4 (peterssonDefinite M k)

end ModularFormsKB.HalfIntegral
