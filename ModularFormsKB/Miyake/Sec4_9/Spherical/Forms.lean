import ModularFormsKB.Miyake.Sec4_9.Spherical.Cusps
import TauCeti.NumberTheory.ModularForms.ThetaSeries.GeneralLevel

/-!
# Miyake, Corollary 4.9.4 in even rank: the spherical theta series as a modular form

Miyake, *Modular Forms* (Springer 1989), Corollary 4.9.4, p. 192.

For an even full lattice `L` of rank `n = 2k` and level `N`, and a spherical weight
`P = ⟪ζ, ·⟫^ν` (`IsSphericalDatum ν u w`), the theta series
`θ_L(τ; P) = ∑_{v ∈ L} P(v) exp (π i ‖v‖² τ)` is a modular form of weight `k + ν` on `Γ₁(N)` in
the character space of the quadratic theta character `χ_L` (that is, on `Γ₀(N)` with character
`χ_L`): `thetaSphForm`, `thetaSphForm_mem_modFormCharSpace`. For `ν ≥ 1` it is a cusp form:
`thetaSphCuspForm`.

In Miyake's normalization `θ(z; 0, A, N, P)` with Gram matrix `A`, the lattice is `ℤ^r` with
`‖m‖² = 2 A[m]`... the series here is `θ(2z)` of Miyake's Corollary 4.9.4 up to the factor `N^ν`
(Miyake sums over `m ≡ 0 mod N` with `P(m)`), at the level of the even lattice of Gram matrix `2A`,
which divides `4N`.
-/

open Complex Module Matrix.SpecialLinearGroup
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

/-- In integral weight, the norm of the slash is the absolute slash. -/
theorem norm_slash_eq_absSlash (m : ℕ) (f : ℍ → ℂ) (A : SL(2, ℤ)) (τ : ℍ) :
    ‖(f ∣[(m : ℤ)] A) τ‖ = absSlash m f A τ := by
  rw [ModularForm.SL_slash_apply, norm_mul, absSlash, mul_comm, norm_zpow, ModularGroup.denom_apply,
    zpow_neg, zpow_natCast, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

theorem isBoundedAtImInfty_slash_thetaSph (hL : ZLattice.IsEven L) (hk : finrank ℝ E = 2 * k)
    {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (thetaSph L ν u w 0 ∣[((k + ν : ℕ) : ℤ)] A) := by
  borelize E
  have h := isBoundedAtImInfty_absSlash_thetaSph hL hsph A (zero_mem (ZLattice.dual L))
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at h ⊢
  obtain ⟨M, B, hMB⟩ := h
  refine ⟨M, B, fun τ hτ ↦ ?_⟩
  rw [norm_slash_eq_absSlash]
  have := hMB τ hτ
  rw [Real.norm_of_nonneg (absSlash_nonneg _ _ _ _)] at this
  convert this using 2
  rw [hk]; push_cast; ring

theorem isZeroAtImInfty_slash_thetaSph (hL : ZLattice.IsEven L) (hk : finrank ℝ E = 2 * k)
    {ν : ℕ} (hν : 1 ≤ ν) {u w : E} (hsph : IsSphericalDatum ν u w) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (thetaSph L ν u w 0 ∣[((k + ν : ℕ) : ℤ)] A) := by
  borelize E
  have h := isZeroAtImInfty_absSlash_thetaSph hL hν hsph A (zero_mem (ZLattice.dual L))
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at h ⊢
  intro ε hε
  obtain ⟨B, hB⟩ := h ε hε
  refine ⟨B, fun τ hτ ↦ ?_⟩
  rw [norm_slash_eq_absSlash]
  have := hB τ hτ
  rw [Real.norm_of_nonneg (absSlash_nonneg _ _ _ _)] at this
  convert this using 2
  rw [hk]; push_cast; ring

/-- **Miyake, Corollary 4.9.4 (even rank, lattice form).** The spherical theta series of an even
full lattice of rank `2k` is a modular form of weight `k + ν` on `Γ₁(N)`, `N` the level. -/
noncomputable def thetaSphForm (hL : ZLattice.IsEven L) (hk : finrank ℝ E = 2 * k) {ν : ℕ}
    {u w : E} (hsph : IsSphericalDatum ν u w) :
    ModularForm ((CongruenceSubgroup.Gamma1 (ZLattice.level L)).map (mapGL ℝ)) (k + ν : ℕ) where
  toFun := thetaSph L ν u w 0
  slash_action_eq' A hA := by
    borelize E
    obtain ⟨A, hA, rfl⟩ := hA
    rw [← TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
      IsEvenSph.thetaSph_slash_of_mem_Gamma0 hL hk hsph
        (CongruenceSubgroup.Gamma1_in_Gamma0 _ hA)]
    have hd := (CongruenceSubgroup.mem_Gamma1_iff.mp hA).2
    rw [hd, map_one, one_smul]
  holo' := mdifferentiable_thetaW L (polyBounded_isoForm_pow u w ν) 0
  bdd_at_cusps' hc := by
    apply (OnePoint.isBoundedAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))).mpr
    intro A _
    exact isBoundedAtImInfty_slash_thetaSph hL hk hsph A

@[simp]
theorem coe_thetaSphForm (hL : ZLattice.IsEven L) (hk : finrank ℝ E = 2 * k) {ν : ℕ}
    {u w : E} (hsph : IsSphericalDatum ν u w) : ⇑(thetaSphForm hL hk hsph) = thetaSph L ν u w 0 :=
  rfl

/-- **Miyake, Theorem 4.9.3 / Corollary 4.9.4: the character.** The spherical theta form lies in the
character space of the quadratic theta character `χ_L` (the nebentypus law on `Γ₀(N)`). -/
@[kb "miyake1989" "Corollary 4.9.4: theta series with a spherical function of an even lattice of even rank lies in M_{r/2+nu}(Gamma0(N), chi) (lattice form)"]
theorem thetaSphForm_mem_modFormCharSpace (hL : ZLattice.IsEven L) (hk : finrank ℝ E = 2 * k)
    {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) :
    thetaSphForm hL hk hsph ∈ TauCeti.modFormCharSpace (k + ν : ℕ)
      (MulChar.equivToUnitHom (hL.thetaCharacter ⟨k, by omega⟩)) := by
  borelize E
  apply (TauCeti.mem_modFormCharSpace_iff_nebentypus _ _ _).mpr
  intro A
  simpa only [coe_thetaSphForm, MulChar.coe_equivToUnitHom,
    MonoidHom.coe_toHomUnits, CongruenceSubgroup.Gamma0Map_apply, ModularForm.SL_slash,
    TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL] using
    IsEvenSph.thetaSph_slash_of_mem_Gamma0 hL hk hsph A.property

/-- **Miyake, Corollary 4.9.4: a cusp form when `ν ≥ 1`** (even rank, lattice form). -/
noncomputable def thetaSphCuspForm (hL : ZLattice.IsEven L) (hk : finrank ℝ E = 2 * k) {ν : ℕ}
    (hν : 1 ≤ ν) {u w : E} (hsph : IsSphericalDatum ν u w) :
    CuspForm ((CongruenceSubgroup.Gamma1 (ZLattice.level L)).map (mapGL ℝ)) (k + ν : ℕ) where
  toSlashInvariantForm := (thetaSphForm hL hk hsph).toSlashInvariantForm
  holo' := (thetaSphForm hL hk hsph).holo'
  zero_at_cusps' hc := by
    apply (OnePoint.isZeroAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))).mpr
    intro A _
    exact isZeroAtImInfty_slash_thetaSph hL hk hν hsph A

@[kb "miyake1989" "Corollary 4.9.4: for nu >= 1 the theta series with a spherical function is a cusp form (lattice form, even rank)"]
theorem coe_thetaSphCuspForm (hL : ZLattice.IsEven L) (hk : finrank ℝ E = 2 * k) {ν : ℕ}
    (hν : 1 ≤ ν) {u w : E} (hsph : IsSphericalDatum ν u w) :
    ⇑(thetaSphCuspForm hL hk hν hsph) = thetaSph L ν u w 0 := rfl

end ModularFormsKB.Miyake.Sec4_9
