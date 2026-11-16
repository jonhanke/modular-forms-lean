import ModularFormsKB.Miyake.Sec4_9.Spherical.Forms

/-!
# The constant term of a theta series at every cusp (even rank)

The analytic half of the statement that theta series of one genus differ by a cusp form.

Let `L` be an even full lattice of rank `2k` in a real inner product space `E`, and
`θ_L(τ) = ∑_{v ∈ L} exp (π i ‖v‖² τ)` (`thetaSph L 0 0 0 0`; with the Gram convention `‖v‖² = 2Q(v)`
this is `∑ q^{Q(v)}`). For `A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`,

`(θ_L ∣[k] A)(τ) → (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c)`  as `im τ → ∞`

(`tendsto_slash_thetaSph_zero`), where `G_L(a, c) = ∑_{y ∈ L/cL} e(a ‖y‖² / (2c))` is Tau Ceti's
`ZLattice.gaussSum`. The proof reads the limit off the coset splitting
`thetaSph_smul_eq_tsum_gaussSumTwisted`: after the slash, `θ_L ∣ A` is a weighted
theta series of the dual lattice whose weight at `m ∈ L^∨` is `G_L(a, c; m) e(d ‖m‖² / (2c))`; such a
series tends to its weight at the origin (`tendsto_thetaW_atImInfty`).

Consequently (`tendsto_slash_sub_of_gaussSum_eq`): if two even lattices `L₁, L₂` of rank `2k` have the
same covolume and the same Gauss sums `G(a, c)` for all `a` and all `c > 0`, then
`(θ_{L₁} - θ_{L₂}) ∣[k] A → 0` at `i∞` for **every** `A ∈ SL(2, ℤ)` (the cases `c = 0` and `c < 0`
reduce to `c > 0` or to `θ → 1`).
-/

open Complex Module Filter Topology
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups Pointwise Classical

set_option linter.unusedSectionVars false

namespace ModularFormsKB.ThetaGenus

open ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### A weighted theta series tends to its weight at the origin -/

theorem polyBounded_ite_zero {p : E → ℂ} (hp : PolyBounded p) :
    PolyBounded fun x ↦ if x = 0 then 0 else p x := by
  obtain ⟨C, hC, n, h⟩ := hp
  refine ⟨C, hC, n, fun x ↦ ?_⟩
  dsimp only
  split_ifs
  · simp only [norm_zero]; positivity
  · exact h x

/-- **A weighted theta series tends to its weight at the origin** as `im τ → ∞`. -/
theorem tendsto_thetaW_atImInfty (M : Submodule ℤ E) [DiscreteTopology M] {p : E → ℂ}
    (hp : PolyBounded p) :
    Tendsto (thetaW M p 0) UpperHalfPlane.atImInfty (𝓝 (p 0)) := by
  have hp' := polyBounded_ite_zero hp
  have h0 := isZeroAtImInfty_thetaW M hp' (by simp) 0
  have hsplit : ∀ τ : ℍ, thetaW M p 0 τ = p 0 + thetaW M (fun x ↦ if x = 0 then 0 else p x) 0 τ := by
    intro τ
    have hs := summable_thetaW M hp 0 τ
    have hs' := summable_thetaW M hp' 0 τ
    rw [thetaW_apply, thetaW_apply]
    have : ∀ v : M, p (0 + v) * cexp (π * I * (‖(0 : E) + (v : E)‖ ^ 2 : ℝ) * τ) -
        (if (0 : E) + v = 0 then 0 else p (0 + v)) * cexp (π * I * (‖(0 : E) + (v : E)‖ ^ 2 : ℝ) * τ) =
        if v = 0 then p 0 else 0 := by
      intro v
      by_cases hv : v = 0
      · subst hv; simp
      · have hv' : (v : E) ≠ 0 := fun h ↦ hv (Subtype.ext h)
        simp [hv, hv']
    have key := hs.tsum_sub hs'
    rw [tsum_congr this, tsum_ite_eq] at key
    linear_combination -key
  have : Tendsto (fun τ ↦ p 0 + thetaW M (fun x ↦ if x = 0 then 0 else p x) 0 τ)
      UpperHalfPlane.atImInfty (𝓝 (p 0 + 0)) := tendsto_const_nhds.add h0
  rw [add_zero] at this
  exact this.congr fun τ ↦ (hsplit τ).symm

/-- The theta series tends to `1` at `i∞`. -/
theorem tendsto_thetaSph_zero_atImInfty (L : Submodule ℤ E) [DiscreteTopology L] :
    Tendsto (thetaSph L 0 0 0 0) UpperHalfPlane.atImInfty (𝓝 1) := by
  have := tendsto_thetaW_atImInfty L (p := fun x ↦ isoForm 0 0 x ^ 0) (polyBounded_isoForm_pow 0 0 0)
  have h2 : isoForm (0 : E) 0 0 ^ 0 = 1 := pow_zero _
  rw [h2] at this
  exact this

/-! ### The constant term at a cusp `a/c`, `c > 0` -/

variable [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- The weight `m ↦ G_L(a, c; m) e(d ‖m‖² / (2c))` on the dual lattice (zero off it). -/
noncomputable def cuspWeight (hL : ZLattice.IsEven L) (a d : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (x : E) : ℂ :=
  if h : x ∈ ZLattice.dual L then
    ZLattice.gaussSumTwisted L hL a c ⟨x, h⟩ * cexp (2 * π * I * ((d * ‖x‖ ^ 2 / (2 * c) : ℝ) : ℂ))
  else 0

theorem polyBounded_cuspWeight (hL : ZLattice.IsEven L) (a d : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] : PolyBounded (cuspWeight hL a d c) := by
  refine ⟨Fintype.card (L ⧸ ((c : ℝ) • L).submoduleOf L), by positivity, 0, fun x ↦ ?_⟩
  simp only [pow_zero, mul_one, cuspWeight]
  split_ifs with h
  · rw [norm_mul, norm_exp_two_pi_mul_I_mul_ofReal, mul_one, ZLattice.gaussSumTwisted_def]
    refine (norm_sum_le _ _).trans ?_
    simp
  · simp

theorem cuspWeight_zero (hL : ZLattice.IsEven L) (a d : ℤ) (c : ℕ)
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] :
    cuspWeight hL a d c 0 = ZLattice.gaussSum L hL a c := by
  simp [cuspWeight, zero_mem, ZLattice.gaussSum_def, ZLattice.gaussSumTwisted_def]
  rfl

/-- After the slash by `A` with `c > 0`, the theta series of `L` is a weighted theta series of the
dual lattice: `(θ_L ∣[k] A)(τ) = (-i)^k c^{-k} (covol L)⁻¹ ∑_{m ∈ L^∨} G_L(a, c; m) e(d‖m‖²/(2c)) q_m(τ)`. -/
theorem slash_thetaSph_zero_eq (hL : ZLattice.IsEven L) {k : ℕ} (hk : finrank ℝ E = 2 * k)
    (A : SL(2, ℤ)) {c : ℕ} [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c)
    (τ : ℍ) :
    (thetaSph L 0 0 0 0 ∣[(k : ℤ)] A) τ =
      (-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (ZLattice.covolume L : ℂ)⁻¹ *
        thetaW (ZLattice.dual L) (cuspWeight hL (A 0 0) (A 1 1) c) 0 τ := by
  have hsph : IsSphericalDatum 0 (0 : E) 0 := Or.inl zero_le_one
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have hden : (c : ℂ) * τ + A 1 1 ≠ 0 := by
    simpa [ModularGroup.denom_apply, hc] using UpperHalfPlane.denom_ne_zero A τ
  have h := IsEvenSph.thetaSph_smul_eq_tsum_gaussSumTwisted hL hk hsph A hc 0 τ
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, hc]
  have hθ : (fun τ ↦ thetaSph L 0 0 0 (((0 : ZLattice.dual L)) : E) τ) = thetaSph L 0 0 0 0 := by
    simp
  rw [show thetaSph L 0 0 0 0 (A • τ) = thetaSph L 0 0 0 ((0 : ZLattice.dual L) : E) (A • τ) by simp,
    h]
  simp only [ZeroMemClass.coe_zero, norm_zero, inner_zero_left, smul_zero, zero_add]
  rw [thetaW_apply]
  rw [tsum_congr (g := fun v : ZLattice.dual L => cuspWeight hL (A 0 0) (A 1 1) c (0 + (v : E)) *
    cexp (π * I * (‖(0 : E) + (v : E)‖ ^ 2 : ℝ) * τ)) (fun m ↦ ?_)]
  · have hI : (I ^ k)⁻¹ = (-I) ^ k := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← mul_pow, neg_mul, I_mul_I, neg_neg, one_pow]
    rw [pow_zero, mul_one, zpow_neg, zpow_natCast, div_pow, mul_pow, div_eq_mul_inv, mul_inv, hI]
    push_cast
    field_simp
  · simp [cuspWeight, m.2]

/-- **The constant term of `θ_L` at the cusp `a/c`** (`c > 0`): `(-i)^k c^{-k} (covol L)⁻¹ G_L(a, c)`. -/
theorem tendsto_slash_thetaSph_zero (hL : ZLattice.IsEven L) {k : ℕ} (hk : finrank ℝ E = 2 * k)
    (A : SL(2, ℤ)) {c : ℕ} [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c) :
    Tendsto (thetaSph L 0 0 0 0 ∣[(k : ℤ)] A) UpperHalfPlane.atImInfty
      (𝓝 ((-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (ZLattice.covolume L : ℂ)⁻¹ * ZLattice.gaussSum L hL (A 0 0) c)) := by
  have h := (tendsto_thetaW_atImInfty (ZLattice.dual L) (polyBounded_cuspWeight hL (A 0 0) (A 1 1) c)).const_mul
    ((-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (ZLattice.covolume L : ℂ)⁻¹)
  rw [cuspWeight_zero] at h
  exact h.congr fun τ ↦ (slash_thetaSph_zero_eq hL hk A hc τ).symm

/-! ### Two lattices with the same covolume and Gauss sums: the difference at every cusp -/

section Difference

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {M : Submodule ℤ F} [DiscreteTopology M] [IsZLattice ℝ M]

/-- In integral weight, slashing by `-A` multiplies by `(-1)^k`. -/
theorem slash_neg_SL (f : ℍ → ℂ) (k : ℕ) (A : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[(k : ℤ)] A) τ = (-1) ^ k * (f ∣[(k : ℤ)] (-A)) τ := by
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul,
    ModularGroup.denom_apply, ModularGroup.denom_apply]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_mul,
    zpow_neg, zpow_natCast]
  rw [show -((A 1 0 : ℂ) * τ) + -(A 1 1 : ℂ) = (-1) * ((A 1 0 : ℂ) * τ + A 1 1) by ring, mul_pow,
    mul_inv]
  have : ((-1 : ℂ) ^ k)⁻¹ = (-1) ^ k := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [this]
  ring_nf
  rw [pow_mul, ← pow_mul, mul_comm k 2, pow_mul, neg_one_sq, one_pow, mul_one]

/-- If `A` fixes `∞` (`c = 0`), it preserves the filter at `i∞`. -/
theorem tendsto_smul_atImInfty_of_c_eq_zero (A : SL(2, ℤ)) (hc : A 1 0 = 0) :
    Tendsto (fun τ : ℍ ↦ A • τ) UpperHalfPlane.atImInfty UpperHalfPlane.atImInfty := by
  have hd : (A 1 1 : ℝ) ^ 2 = 1 := by
    have h := A.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
    have : A 1 1 ^ 2 = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> norm_num
    exact_mod_cast this
  have him : ∀ τ : ℍ, (A • τ).im = τ.im := by
    intro τ
    rw [ModularGroup.sl_moeb, UpperHalfPlane.im_smul_eq_div_normSq, UpperHalfPlane.denom]
    simp [hc, Complex.normSq_apply, ← sq, hd]
  refine tendsto_comap_iff.mpr ?_
  simp only [Function.comp_def, him]
  exact tendsto_comap

/-- For `c = 0`, slashing preserves "tends to `0` at `i∞`". -/
theorem tendsto_slash_of_c_eq_zero {f : ℍ → ℂ} (hf : Tendsto f UpperHalfPlane.atImInfty (𝓝 0))
    (k : ℤ) (A : SL(2, ℤ)) (hc : A 1 0 = 0) :
    Tendsto (f ∣[k] A) UpperHalfPlane.atImInfty (𝓝 0) := by
  have h := (hf.comp (tendsto_smul_atImInfty_of_c_eq_zero A hc)).mul_const
    (((A 1 1 : ℂ)) ^ (-k))
  rw [zero_mul] at h
  refine h.congr fun τ ↦ ?_
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, hc]
  simp

variable (hL : ZLattice.IsEven L) (hM : ZLattice.IsEven M)

theorem tendsto_slash_sub_of_pos {k : ℕ} (hk : finrank ℝ E = 2 * k) (hkM : finrank ℝ F = 2 * k)
    (hcov : ZLattice.covolume L = ZLattice.covolume M)
    (hG : ∀ (a : ℤ) (c : ℕ) [NeZero c], ZLattice.gaussSum L hL a c = ZLattice.gaussSum M hM a c)
    (A : SL(2, ℤ)) (hpos : 0 < A 1 0) :
    Tendsto ((thetaSph L 0 0 0 0 - thetaSph M 0 0 0 0) ∣[(k : ℤ)] A) UpperHalfPlane.atImInfty
      (𝓝 0) := by
  obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le hpos.le
  have : NeZero c := ⟨by rintro rfl; simp at hc; omega⟩
  rw [SlashAction.sub_slash]
  have h := (tendsto_slash_thetaSph_zero hL hk A hc).sub (tendsto_slash_thetaSph_zero hM hkM A hc)
  rwa [hcov, hG, sub_self] at h

/-- **Same covolume and same Gauss sums ⇒ the difference of the theta series vanishes at every
cusp** (even rank `2k`, integral weight `k`). -/
theorem tendsto_slash_sub_of_gaussSum_eq {k : ℕ} (hk : finrank ℝ E = 2 * k)
    (hkM : finrank ℝ F = 2 * k) (hcov : ZLattice.covolume L = ZLattice.covolume M)
    (hG : ∀ (a : ℤ) (c : ℕ) [NeZero c], ZLattice.gaussSum L hL a c = ZLattice.gaussSum M hM a c)
    (A : SL(2, ℤ)) :
    Tendsto ((thetaSph L 0 0 0 0 - thetaSph M 0 0 0 0) ∣[(k : ℤ)] A) UpperHalfPlane.atImInfty
      (𝓝 0) := by
  rcases lt_trichotomy (A 1 0) 0 with hneg | hzero | hpos
  · have hpos' : 0 < (-A) 1 0 := by simp [hneg]
    have h := (tendsto_slash_sub_of_pos hL hM hk hkM hcov hG (-A) hpos').const_mul ((-1 : ℂ) ^ k)
    rw [mul_zero] at h
    exact h.congr fun τ ↦ (slash_neg_SL _ k A τ).symm
  · have h := (tendsto_thetaSph_zero_atImInfty L).sub (tendsto_thetaSph_zero_atImInfty M)
    rw [sub_self] at h
    exact tendsto_slash_of_c_eq_zero h _ A hzero
  · exact tendsto_slash_sub_of_pos hL hM hk hkM hcov hG A hpos

end Difference

end ModularFormsKB.ThetaGenus
