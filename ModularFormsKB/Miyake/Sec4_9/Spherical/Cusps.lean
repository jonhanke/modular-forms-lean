import ModularFormsKB.Miyake.Sec4_9.Spherical.CosetSplitting
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Spherical theta series at the cusps (every rank)

Miyake, *Modular Forms* (Springer 1989), Corollary 4.9.4, p. 192: the theta series with a
spherical function is holomorphic at every cusp, and vanishes there when `ν ≥ 1`.

The statement is made with absolute values, so that it applies in every rank, integral or
half-integral weight `w = n/2 + ν`: for every `A ∈ SL(2, ℤ)` the function
`absSlash w f A τ = |cτ + d|^{-w} |f(A τ)|` is bounded at `i∞`, and tends to `0` when `ν ≥ 1`
(`isBoundedAtImInfty_absSlash_thetaSph`, `isZeroAtImInfty_absSlash_thetaSph`). This is the cusp
condition of `HalfIntegral.IsHalfIntModularForm` (`cuspNorm`), and, through
`‖(f ∣[k] A) τ‖ = absSlash k f A τ`, Mathlib's boundedness of the slash at `i∞`.

**Proof.** As in Tau Ceti's `ZLattice.IsEven.isBoundedAtImInfty_thetaCoset_slash`, by Mathlib's
`FixedDetMatrices.induction_on`, carrying the whole family of coset series `θ_{δ+L}(·; P)`,
`δ ∈ L^∨ / L`: the translation `T` preserves `|θ_δ|` (`L` even), and the inversion law with a
spherical weight (`thetaSph_S_smul`, every rank) bounds `|θ_δ(Sσ)|` by
`(covol L)⁻¹ |σ|^w ∑_{δ'} |θ_{δ'}(σ)|`, while `|aτ + b| = |Aτ| |cτ + d|`.
-/

open Complex Module Filter
open scoped Real RealInnerProductSpace UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

/-- The absolute slash `|cτ + d|^{-w} |f(Aτ)|` (Shimura's cusp quantity, `HalfIntegral.cuspNorm`
for `w = k + 1/2`). -/
noncomputable def absSlash (w : ℝ) (f : ℍ → ℂ) (A : SL(2, ℤ)) (τ : ℍ) : ℝ :=
  ‖(A 1 0 : ℂ) * τ + A 1 1‖ ^ (-w) * ‖f (A • τ)‖

theorem absSlash_nonneg (w : ℝ) (f : ℍ → ℂ) (A : SL(2, ℤ)) (τ : ℍ) : 0 ≤ absSlash w f A τ := by
  unfold absSlash; positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The phase-twisted weight `x ↦ ⟪ζ, x⟫^ν e(⟪δ, x⟫)`. -/
noncomputable def phaseWeight (ν : ℕ) (u w δ : E) (x : E) : ℂ :=
  isoForm u w x ^ ν * cexp (2 * π * I * ⟪δ, x⟫)

theorem polyBounded_phaseWeight (ν : ℕ) (u w δ : E) : PolyBounded (phaseWeight ν u w δ) := by
  obtain ⟨C, hC, n, h⟩ := polyBounded_isoForm_pow u w ν
  refine ⟨C, hC, n, fun x ↦ ?_⟩
  rw [phaseWeight, norm_mul, norm_exp_two_pi_mul_I_mul_ofReal, mul_one]
  exact h x

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- For `δ ∈ L^∨` and `x : E`, the phase-twisted theta series over `x + L` is
`e(⟪δ, x⟫) θ_{x+L}(·; P)`. -/
theorem thetaW_phaseWeight (ν : ℕ) (u w : E) {δ : E} (hδ : δ ∈ ZLattice.dual L) (x : E) (τ : ℍ) :
    thetaW L (phaseWeight ν u w δ) x τ = cexp (2 * π * I * ⟪δ, x⟫) * thetaSph L ν u w x τ := by
  rw [thetaSph, thetaW_apply, thetaW_apply, ← tsum_mul_left]
  refine tsum_congr fun ℓ ↦ ?_
  obtain ⟨i, hi⟩ := ZLattice.mem_dual.mp hδ _ ℓ.2
  have he : cexp (2 * π * I * ⟪δ, x + ℓ⟫) = cexp (2 * π * I * ⟪δ, x⟫) := by
    rw [inner_add_right, hi, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨i, by push_cast; ring⟩
  rw [phaseWeight, he]
  ring

variable [MeasurableSpace E] [BorelSpace E]

/-- **The inversion law bounds the coset series at `Sσ`.** For an integral lattice `L`,
`δ ∈ L^∨`: `|θ_{δ+L}(Sσ; P)| ≤ (covol L)⁻¹ |σ|^{ν + n/2} ∑_{y ∈ L^∨/L} |θ_{y+L}(σ; P)|`. -/
theorem norm_thetaSph_S_smul_le (hL : ZLattice.IsIntegral L) [Fintype (ZLattice.DiscriminantGroup L)]
    {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) {δ : E} (hδ : δ ∈ ZLattice.dual L) (σ : ℍ) :
    ‖thetaSph L ν u w δ (ModularGroup.S • σ)‖ ≤ (ZLattice.covolume L)⁻¹ *
      ‖(σ : ℂ)‖ ^ ((ν : ℝ) + finrank ℝ E / 2) *
      ∑ y : ZLattice.DiscriminantGroup L, ‖thetaSph L ν u w (Quotient.out y : ZLattice.dual L) σ‖ := by
  have hLd : L ≤ ZLattice.dual L := ZLattice.isIntegral_iff_le_dual.mp hL
  have hsplit := hasSum_thetaW_add_out (ZLattice.dual L) (polyBounded_phaseWeight ν u w δ)
    (M := L) hLd 0 σ
  rw [thetaSph_S_smul L hsph δ σ]
  have hdual : (∑' m : ZLattice.dual L, isoForm u w m ^ ν * cexp (2 * π * I * ⟪δ, (m : E)⟫) *
      cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ)) = thetaW (ZLattice.dual L) (phaseWeight ν u w δ) 0 σ := by
    rw [thetaW_apply]
    exact tsum_congr fun m ↦ by simp [phaseWeight]
  rw [hdual, ← hsplit.tsum_eq, tsum_fintype]
  simp only [zero_add, thetaW_phaseWeight ν u w hδ]
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  rw [norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hcov, norm_pow, norm_neg]
  have hc : ‖((σ : ℂ) / I) ^ ((finrank ℝ E : ℂ) / 2)‖ = ‖(σ : ℂ)‖ ^ ((finrank ℝ E : ℝ) / 2) := by
    rw [show ((finrank ℝ E : ℂ) / 2) = (((finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_real, norm_div, Complex.norm_I, div_one]
  rw [hc, Real.rpow_add (norm_pos_iff.mpr σ.ne_zero), Real.rpow_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ ↦ ?_))
  rw [norm_mul, norm_exp_two_pi_mul_I_mul_ofReal, one_mul]

/-- For an even lattice and `δ ∈ L^∨`, `|θ_{δ+L}(1 + σ; P)| = |θ_{δ+L}(σ; P)|`. -/
theorem norm_thetaSph_one_vadd (hL : ZLattice.IsEven L) (ν : ℕ) (u w : E) {δ : E}
    (hδ : δ ∈ ZLattice.dual L) (σ : ℍ) :
    ‖thetaSph L ν u w δ ((1 : ℝ) +ᵥ σ)‖ = ‖thetaSph L ν u w δ σ‖ := by
  rw [thetaSph, thetaW_vadd_eq_mul L _ δ (fun v hv ↦ ?_) σ, norm_mul, ← thetaSph]
  · rw [show (π : ℂ) * I * ((‖δ‖ ^ 2 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) =
        2 * π * I * ((‖δ‖ ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring, norm_exp_two_pi_mul_I_mul_ofReal,
      one_mul]
  · obtain ⟨i, hi⟩ := ZLattice.mem_dual.mp hδ _ hv
    obtain ⟨j, hj⟩ := ZLattice.isEven_iff.mp hL _ hv
    refine ⟨i + j, ?_⟩
    rw [norm_add_sq_real, hi, hj]
    push_cast
    ring

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] [MeasurableSpace E]
  [BorelSpace E] in
theorem absSlash_one (w : ℝ) (f : ℍ → ℂ) (τ : ℍ) : absSlash w f 1 τ = ‖f τ‖ := by
  simp [absSlash]

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] [MeasurableSpace E]
  [BorelSpace E] in
theorem absSlash_T_mul (w : ℝ) (f : ℍ → ℂ) (B : SL(2, ℤ)) (τ : ℍ) :
    absSlash w f (ModularGroup.T * B) τ = ‖(B 1 0 : ℂ) * τ + B 1 1‖ ^ (-w) *
      ‖f ((1 : ℝ) +ᵥ (B • τ))‖ := by
  rw [absSlash, mul_smul, UpperHalfPlane.modular_T_smul]
  congr 4 <;> simp [ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]

omit [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L] [MeasurableSpace E]
  [BorelSpace E] in
theorem absSlash_S_mul (w : ℝ) (f : ℍ → ℂ) (B : SL(2, ℤ)) (τ : ℍ) :
    absSlash w f (ModularGroup.S * B) τ = ‖(B 0 0 : ℂ) * τ + B 0 1‖ ^ (-w) *
      ‖f (ModularGroup.S • (B • τ))‖ := by
  rw [absSlash, mul_smul]
  congr 4 <;> simp [ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

/-- `|aτ + b| = |Bτ| |cτ + d|`. -/
theorem norm_top_eq (B : SL(2, ℤ)) (τ : ℍ) :
    ‖(B 0 0 : ℂ) * τ + B 0 1‖ = ‖((B • τ : ℍ) : ℂ)‖ * ‖(B 1 0 : ℂ) * τ + B 1 1‖ := by
  have hden : (B 1 0 : ℂ) * τ + B 1 1 ≠ 0 := by
    simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero B τ
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, ← norm_mul]
  congr 1
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  rw [div_mul_cancel₀ _ (by exact_mod_cast hden)]

/-- **The induction over `SL(2, ℤ)`.** Let `Pr` be a property of real functions on `ℍ`, closed
under domination by a nonnegative multiple of a finite sum. If every `|θ_{δ+L}(·; P)|`, `δ ∈ L^∨`,
has it, then so does every absolute slash `absSlash (ν + n/2) θ_{δ+L}(·; P) A`. -/
theorem absSlash_thetaSph_induction (hL : ZLattice.IsEven L)
    [Fintype (ZLattice.DiscriminantGroup L)] {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w)
    (Pr : (ℍ → ℝ) → Prop)
    (hmono : ∀ f g : ℍ → ℝ, (∀ τ, 0 ≤ f τ) → (∀ τ, f τ ≤ g τ) → Pr g → Pr f)
    (hsum : ∀ g : ZLattice.DiscriminantGroup L → ℍ → ℝ, (∀ y, Pr (g y)) → ∀ c : ℝ,
      Pr (fun τ ↦ c * ∑ y, g y τ))
    (hbase : ∀ δ ∈ ZLattice.dual L, Pr (fun τ ↦ ‖thetaSph L ν u w δ τ‖)) (A : SL(2, ℤ)) :
    ∀ δ ∈ ZLattice.dual L, Pr (absSlash ((ν : ℝ) + finrank ℝ E / 2) (thetaSph L ν u w δ) A) := by
  set wt : ℝ := (ν : ℝ) + finrank ℝ E / 2
  induction A using (FixedDetMatrices.induction_on one_ne_zero) with
  | h0 A ha hc _ hd =>
    rw [FixedDetMatrices.reps_one_id A ha hc hd]
    intro δ hδ
    have : absSlash wt (thetaSph L ν u w δ) (1 : SL(2, ℤ)) = fun τ ↦ ‖thetaSph L ν u w δ τ‖ :=
      funext (absSlash_one wt _)
    change Pr (absSlash wt (thetaSph L ν u w δ) (1 : SL(2, ℤ)))
    rw [this]
    exact hbase δ hδ
  | hS B ih =>
    change SL(2, ℤ) at B
    intro δ hδ
    change Pr (absSlash wt (thetaSph L ν u w δ) (ModularGroup.S * B))
    refine hmono _ _ (absSlash_nonneg _ _ _) (fun τ ↦ ?_)
      (hsum (fun y ↦ absSlash wt (thetaSph L ν u w (Quotient.out y : ZLattice.dual L)) B)
        (fun y ↦ ih _ (Quotient.out y).2) (ZLattice.covolume L)⁻¹)
    rw [absSlash_S_mul]
    have hb := norm_thetaSph_S_smul_le hL.isIntegral hsph hδ (B • τ)
    have hden : 0 < ‖(B 1 0 : ℂ) * τ + B 1 1‖ := norm_pos_iff.mpr (by
      simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero B τ)
    have hσ : 0 < ‖((B • τ : ℍ) : ℂ)‖ := norm_pos_iff.mpr (B • τ).ne_zero
    refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans (le_of_eq ?_)
    simp only [absSlash, ← Finset.mul_sum]
    rw [norm_top_eq, Real.mul_rpow hσ.le hden.le, Real.rpow_neg hσ.le, Real.rpow_neg hden.le]
    field_simp
    congr 3
    simp only [wt]
    ring
  | hT B ih =>
    change SL(2, ℤ) at B
    intro δ hδ
    change Pr (absSlash wt (thetaSph L ν u w δ) (ModularGroup.T * B))
    have : absSlash wt (thetaSph L ν u w δ) (ModularGroup.T * B) =
        absSlash wt (thetaSph L ν u w δ) B := by
      funext τ
      rw [absSlash_T_mul, norm_thetaSph_one_vadd hL ν u w hδ, absSlash]
    rw [this]
    exact ih δ hδ

/-- **Holomorphy at every cusp** (Miyake, Corollary 4.9.4, the cusp condition): for an even full
lattice `L` of any rank `n`, a spherical weight of degree `ν`, `δ ∈ L^∨` and `A ∈ SL(2, ℤ)`,
`|cτ + d|^{-(n/2 + ν)} |θ_{δ+L}(Aτ; P)|` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_absSlash_thetaSph (hL : ZLattice.IsEven L) {ν : ℕ} {u w : E}
    (hsph : IsSphericalDatum ν u w) (A : SL(2, ℤ)) {δ : E} (hδ : δ ∈ ZLattice.dual L) :
    UpperHalfPlane.IsBoundedAtImInfty
      (absSlash ((ν : ℝ) + finrank ℝ E / 2) (thetaSph L ν u w δ) A) := by
  classical
  have := hL.isIntegral.finite_discriminantGroup
  let := Fintype.ofFinite (ZLattice.DiscriminantGroup L)
  refine absSlash_thetaSph_induction hL hsph (fun f ↦ UpperHalfPlane.IsBoundedAtImInfty f)
    (fun f g hf hfg hg ↦ ?_) (fun g hg c ↦ ?_) (fun δ _ ↦ ?_) A δ hδ
  · exact (Asymptotics.isBigO_of_le _ fun τ ↦ by
      rw [Real.norm_of_nonneg (hf τ), Real.norm_of_nonneg ((hf τ).trans (hfg τ))]
      exact hfg τ).trans hg
  · have h : UpperHalfPlane.IsBoundedAtImInfty (fun τ ↦ ∑ y, g y τ) := by
      have := Asymptotics.IsBigO.sum (s := Finset.univ) (fun y _ ↦ hg y)
      have hfun : (fun τ ↦ ∑ y, g y τ) = ∑ y, g y := by funext τ; simp [Finset.sum_apply]
      rw [hfun]
      exact this
    exact h.const_mul_left c
  · exact (isBoundedAtImInfty_thetaW L (polyBounded_isoForm_pow u w ν) δ).norm_left

/-- **Vanishing at every cusp for `ν ≥ 1`** (Miyake, Corollary 4.9.4: a cusp form when `ν ≥ 1`). -/
theorem isZeroAtImInfty_absSlash_thetaSph (hL : ZLattice.IsEven L) {ν : ℕ} (hν : 1 ≤ ν)
    {u w : E} (hsph : IsSphericalDatum ν u w) (A : SL(2, ℤ)) {δ : E} (hδ : δ ∈ ZLattice.dual L) :
    UpperHalfPlane.IsZeroAtImInfty
      (absSlash ((ν : ℝ) + finrank ℝ E / 2) (thetaSph L ν u w δ) A) := by
  classical
  have := hL.isIntegral.finite_discriminantGroup
  let := Fintype.ofFinite (ZLattice.DiscriminantGroup L)
  refine absSlash_thetaSph_induction hL hsph (fun f ↦ UpperHalfPlane.IsZeroAtImInfty f)
    (fun f g hf hfg hg ↦ ?_) (fun g hg c ↦ ?_) (fun δ _ ↦ ?_) A δ hδ
  · exact squeeze_zero hf hfg hg
  · have h : Tendsto (fun τ ↦ ∑ y, g y τ) UpperHalfPlane.atImInfty (nhds 0) := by
      simpa using tendsto_finsetSum Finset.univ fun y _ ↦ (hg y : Tendsto _ _ _)
    have h' := h.const_mul c
    rw [mul_zero] at h'
    exact h'
  · have h0 : isoForm u w 0 ^ ν = 0 := by rw [isoForm_zero]; exact zero_pow (by omega)
    have h' := (isZeroAtImInfty_thetaW L (polyBounded_isoForm_pow u w ν) h0 δ).norm
    rw [norm_zero] at h'
    exact h'

end ModularFormsKB.Miyake.Sec4_9
