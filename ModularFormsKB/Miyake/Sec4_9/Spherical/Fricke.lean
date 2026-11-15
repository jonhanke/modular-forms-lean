import ModularFormsKB.Miyake.Sec4_9.Spherical.Forms

/-!
# The Fricke transform of a spherical theta series (Miyake, Corollary 4.9.5 (3))

Miyake, *Modular Forms* (Springer 1989), Corollary 4.9.5, p. 192.

For a full lattice `L` of any rank `n`, a spherical weight `P` of degree `ν` and `N > 0`:

`θ_L(-1/(Nτ); P) = (covol L)⁻¹ (-Nτ)^ν (Nτ / i)^{n/2} N^{-ν/2} θ_{√N L^∨}(τ; P)`

(`thetaSph_fricke`): the Fricke involution `W_N` carries the theta series of `L` to that of the
rescaled dual lattice `√N L^∨` (for `N` the level, `√N L^∨` is the even lattice of Gram matrix
`N A⁻¹` in Miyake's notation). With `P = 1` and even rank this is Tau Ceti's
`ZLattice.thetaSeries_sqrt_smul_dual_slash_frickeGL`.

Parts (1) and (2) of Corollary 4.9.5 (the level `4N`, `2N` or `N` read off the diagonals of `A`
and `N A⁻¹`) are, in lattice form, statements about Tau Ceti's `ZLattice.level`, at which
`thetaSphForm` and `thetaSph_mem_halfIntModularForms` are stated.
-/

open Complex Module
open scoped Real RealInnerProductSpace UpperHalfPlane Pointwise

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Miyake, Corollary 4.9.5 (3) (lattice form, every rank).** -/
@[kb "miyake1989" "Corollary 4.9.5 (3): the theta series with spherical function under the Fricke involution is that of the rescaled dual lattice (lattice form, every rank)"]
theorem thetaSph_fricke {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) {N : ℝ} (hN : 0 < N)
    (τ : ℍ) :
    thetaSph L ν u w 0 (ModularGroup.S • ((⟨N, hN⟩ : {r : ℝ // 0 < r}) • τ)) =
      (ZLattice.covolume L : ℂ)⁻¹ * ((-(N * τ : ℂ)) ^ ν * ((N * τ : ℂ) / I) ^ ((finrank ℝ E : ℂ) / 2)) *
        ((√N : ℂ) ^ ν)⁻¹ * thetaSph (√N • ZLattice.dual L) ν u w 0 τ := by
  have hs : (√N : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hN
  have hsq : (√N : ℝ) ^ 2 = N := Real.sq_sqrt hN.le
  have hsc := thetaSph_smul (ZLattice.dual L) ν u w hs 0 τ
  rw [smul_zero] at hsc
  have hτ : ((⟨(√N) ^ 2, sq_pos_of_ne_zero hs⟩ : {r : ℝ // 0 < r}) • τ) =
      ((⟨N, hN⟩ : {r : ℝ // 0 < r}) • τ) := by
    congr 1
    exact Subtype.ext hsq
  rw [hτ] at hsc
  rw [hsc, thetaSph_S_smul L hsph 0]
  have key : thetaSph (ZLattice.dual L) ν u w 0 ((⟨N, hN⟩ : {r : ℝ // 0 < r}) • τ) =
      ∑' m : ZLattice.dual L, isoForm u w m ^ ν * cexp (2 * π * I * ⟪(0 : E), (m : E)⟫) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * (((⟨N, hN⟩ : {r : ℝ // 0 < r}) • τ : ℍ) : ℂ)) := by
    rw [thetaSph, thetaW_apply]
    exact tsum_congr fun m ↦ by simp
  have hc : ((√N : ℂ) ^ ν) ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hs)
  rw [key, UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]
  field_simp

end ModularFormsKB.Miyake.Sec4_9
