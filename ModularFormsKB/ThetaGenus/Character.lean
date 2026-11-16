import ModularFormsKB.ThetaGenus.Cusp

/-!
# Genus theorem, even rank: the law of the difference on `Γ₀(N)` with its character

`sameGenus_thetaSph_sub_cuspForm` gives a cusp form on `Γ₁(N)`.
Lattices in one genus also have the same signed discriminant
(`SameGenus.signedDiscr_eq`), so both theta series have the same nebentypus, and the difference
transforms on `Γ₀(N)` with the Kronecker character `(D_L / d)`, `D_L = (-1)^k |L^∨/L|`
(`sameGenus_thetaSph_sub_slash_of_mem_Gamma0`). With the cusp form on `Γ₁(N)` this is the statement
`θ_L - θ_M ∈ S_k(Γ₀(N), χ_L)`.
-/

open Complex Module Filter Topology
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.ThetaGenus

open ModularFormsKB.Miyake.Sec4_9

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {M : Submodule ℤ F} [DiscreteTopology M] [IsZLattice ℝ M]

theorem SameGenus.signedDiscr_eq (h : SameGenus L M) (hL : ZLattice.IsIntegral L)
    (hM : ZLattice.IsIntegral M) (hEF : finrank ℝ E = finrank ℝ F) :
    ZLattice.signedDiscr L = ZLattice.signedDiscr M := by
  rw [ZLattice.signedDiscr_def, ZLattice.signedDiscr_def, hEF, h.card_discriminantGroup_eq hL hM]

theorem thetaSph_zero_slash_of_mem_Gamma0_kronecker (hL : ZLattice.IsEven L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) {N : ℕ} (hN : ZLattice.level L ∣ N) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    thetaSph L 0 0 0 0 ∣[(k : ℤ)] A =
      (TauCeti.kroneckerSym (ZLattice.signedDiscr L) (A 1 1) : ℂ) • thetaSph L 0 0 0 0 := by
  have hsph : IsSphericalDatum 0 (0 : E) 0 := Or.inl zero_le_one
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 (ZLattice.level L) := by
    rw [CongruenceSubgroup.mem_Gamma0_iff_dvd] at hA ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hN) hA
  have h := IsEvenSph.thetaSph_slash_of_mem_Gamma0 hL hk hsph hA0
  have hco : IsCoprime (A 1 1) (ZLattice.level L : ℤ) := by
    obtain ⟨t, ht⟩ := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hA0
    have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
      have h := A.det_coe
      rwa [Matrix.det_fin_two] at h
    exact ⟨A 0 0, -(A 0 1 * t), by linear_combination hdet + A 0 1 * ht⟩
  rw [hL.thetaCharacter_intCast ⟨k, by omega⟩ hco] at h
  simpa using h

/-- **Headline H5, even rank, with the character**: for `A ∈ Γ₀(N)`,
`(θ_L - θ_M) ∣[k] A = (D_L / d) (θ_L - θ_M)`. -/
@[kb "siegel1935" "theta series of lattices in one genus differ by a cusp form in S_k(Gamma0(N), chi_L) (even rank, the Gamma0 law with the common character)"]
theorem sameGenus_thetaSph_sub_slash_of_mem_Gamma0 (h : SameGenus L M) (hL : ZLattice.IsEven L)
    (hM : ZLattice.IsEven M) {k : ℕ} (hk : finrank ℝ E = 2 * k) (hkM : finrank ℝ F = 2 * k)
    {N : ℕ} (hLN : ZLattice.level L ∣ N) (hMN : ZLattice.level M ∣ N) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) :
    (thetaSph L 0 0 0 0 - thetaSph M 0 0 0 0) ∣[(k : ℤ)] A =
      (TauCeti.kroneckerSym (ZLattice.signedDiscr L) (A 1 1) : ℂ) •
        (thetaSph L 0 0 0 0 - thetaSph M 0 0 0 0) := by
  rw [SlashAction.sub_slash, thetaSph_zero_slash_of_mem_Gamma0_kronecker hL hk hLN hA,
    thetaSph_zero_slash_of_mem_Gamma0_kronecker hM hkM hMN hA,
    h.signedDiscr_eq hL.isIntegral hM.isIntegral (by rw [hk, hkM]), smul_sub]

end ModularFormsKB.ThetaGenus
