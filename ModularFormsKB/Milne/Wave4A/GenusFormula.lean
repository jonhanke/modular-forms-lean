import ModularFormsKB.Milne.Wave4A.SphereGenus
import ModularFormsKB.Milne.Ch2.ModularCurves
import TauCeti.Analysis.Complex.Fuchsian.Compactification.RamificationDegree
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Signature
import TauCeti.Analysis.Complex.ModularForms.CongruenceSubgroups.Degree
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Milne, Theorem 2.22: the genus of `X(Γ)`

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, Theorem 2.22 (pdf pp. 37–38).

Let `Γ` be a subgroup of finite index of `SL₂(ℤ)`, `Γ̄` its image in `PSL₂(ℝ)` (`barGamma Γ`), `m` the degree of
`X(Γ) → X(1)` (the index of `Γ̄` in `Γ̄(1)`, Tau Ceti's `Subgroup.degree_compactifiedQuotientMap_map_sl2zToPSL2R`),
`ν₂`, `ν₃` the numbers of inequivalent elliptic points of order `2` and `3`, and `ν∞` the number of inequivalent
cusps. Milne's theorem: the genus of `X(Γ)` is `g = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`.

The book proves it from the Riemann–Hurwitz formula (Theorem 1.27) for `X(Γ) → X(1)` and the ramification count
`∑ (e_{P'} - 1) = (m - ν₂)/2 + 2(m - ν₃)/3 + (m - ν∞)`. Here:

* the ramification count is unconditional (`ramificationDegree_modularCurveX`): it is Tau Ceti's
  `TauCeti.Fuchsian.ramificationDegree_eq_index_mul_cusps_add_elliptic_sub` combined with the level-one signature
  (one cusp; elliptic orbits `i` of order `2` and `ρ` of order `3`) and the classification of elliptic orders of
  subgroups of `Γ̄(1)` (`Subgroup.exists_smul_eq_of_card_stabilizer_ne_one`);
* the genus formula (`genus_modularCurveX`) is conditional on the named input `RiemannHurwitzStatement` (Theorem
  1.27), applied to `j : X(Γ) → X(1) ≅ ℙ¹`; Riemann–Hurwitz on compact Riemann surfaces is not available in Mathlib or
  Tau Ceti (it needs Riemann–Roch, Corollary 1.21). The genus of the target is `genus_onePoint` (proved).

Example 2.23 (the genus of `X(N)`) follows (`genus_modularCurveX_Gamma`).
-/

open Set MulAction UpperHalfPlane
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti TauCeti.RiemannSurface Subgroup.CompactifiedQuotient RiemannSurface

/-! ### The invariants `m`, `ν₂`, `ν₃`, `ν∞` -/

/-- `m`: the degree of `X(Γ) → X(1)`, the index of `Γ̄` in `Γ̄(1) = PSL₂(ℤ)`, i.e. the index of `±Γ` in `SL₂(ℤ)`. -/
def genusIndex (Γ : Subgroup SL(2, ℤ)) : ℕ := Γ.withCenter.index

/-- `ν₂`: the number of inequivalent elliptic points of order `2` (orbits of `Γ̄` on `ℍ` whose stabilizer has
order `2`). -/
def nuTwo (Γ : Subgroup SL(2, ℤ)) : ℕ :=
  {q ∈ (barGamma Γ).ellipticOrbits | cardStabilizerOnOrbit q = 2}.ncard

/-- `ν₃`: the number of inequivalent elliptic points of order `3`. -/
def nuThree (Γ : Subgroup SL(2, ℤ)) : ℕ :=
  {q ∈ (barGamma Γ).ellipticOrbits | cardStabilizerOnOrbit q = 3}.ncard

/-- `ν∞`: the number of inequivalent cusps of `Γ` (cusp orbits of `Γ̄`). -/
def nuInfty (Γ : Subgroup SL(2, ℤ)) : ℕ := Nat.card (barGamma Γ).CuspOrbit

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

omit [Γ.FiniteIndex] in
/-- The right side `1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2` of Theorem 2.22. -/
def genusFormula : ℚ :=
  1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2

omit [Γ.FiniteIndex] in
/-- Every elliptic point of `Γ` has order `2` or `3`. -/
theorem cardStabilizerOnOrbit_eq_two_or_three {q : orbitRel.Quotient (barGamma Γ) ℍ}
    (hq : q ∈ (barGamma Γ).ellipticOrbits) :
    cardStabilizerOnOrbit q = 2 ∨ cardStabilizerOnOrbit q = 3 := by
  induction q using Quotient.inductionOn with
  | h z =>
    rw [Subgroup.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus] at hq
    have hne : Nat.card (stabilizer (Γ.map sl2zToPSL2R) z) ≠ 1 := by
      intro h1
      exact hq (Subgroup.card_eq_one.mp h1)
    have hmk : cardStabilizerOnOrbit (Quotient.mk (orbitRel (barGamma Γ) ℍ) z) =
        Nat.card (stabilizer (Γ.map sl2zToPSL2R) z) := cardStabilizerOnOrbit_mk z
    rw [hmk]
    rcases Γ.exists_smul_eq_of_card_stabilizer_ne_one hne with ⟨_, _, h⟩ | ⟨_, _, h⟩
    · exact Or.inl h
    · exact Or.inr h

theorem finite_ellipticOrbits_barGamma : (barGamma Γ).ellipticOrbits.Finite :=
  Subgroup.finite_ellipticOrbits (barGamma Γ)

/-- The elliptic defect sum: `∑_{elliptic orbits} (1 - 1/e) = ν₂/2 + 2ν₃/3`. -/
theorem finsum_ellipticOrbits_one_sub_inv :
    ∑ᶠ q ∈ (barGamma Γ).ellipticOrbits, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
      (nuTwo Γ : ℝ) / 2 + 2 * (nuThree Γ : ℝ) / 3 := by
  classical
  have hfin := finite_ellipticOrbits_barGamma Γ
  set E := hfin.toFinset with hE
  have h2 : nuTwo Γ = (E.filter fun q ↦ cardStabilizerOnOrbit q = 2).card := by
    rw [nuTwo, ← Set.ncard_coe_finset]
    congr 1
    ext q
    simp [hE]
  have h3 : nuThree Γ = (E.filter fun q ↦ cardStabilizerOnOrbit q = 3).card := by
    rw [nuThree, ← Set.ncard_coe_finset]
    congr 1
    ext q
    simp [hE]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← hE, h2, h3]
  have hpt : ∀ q ∈ E, (1 - (cardStabilizerOnOrbit q : ℝ)⁻¹) =
      (if cardStabilizerOnOrbit q = 2 then (1 / 2 : ℝ) else 0) +
        (if cardStabilizerOnOrbit q = 3 then (2 / 3 : ℝ) else 0) := by
    intro q hq
    rw [hE, Set.Finite.mem_toFinset] at hq
    rcases cardStabilizerOnOrbit_eq_two_or_three Γ hq with h | h <;> rw [h] <;> norm_num
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-! ### The ramification count -/

/-- The map `X(Γ) → X(1)` as a finite holomorphic map (Tau Ceti). -/
abbrev modularCurveXMap : FiniteHolomorphicMap (ModularCurveX Γ) ModularCurveXOne :=
  TauCeti.Fuchsian.compactifiedQuotientFiniteHolomorphicMap Γ.map_sl2zToPSL2R_le_range_psl2zToPSL2R

/-- `m` is the degree of `X(Γ) → X(1)`. -/
theorem degree_modularCurveXMap : degree (modularCurveXMap Γ) = genusIndex Γ :=
  Γ.degree_compactifiedQuotientMap_map_sl2zToPSL2R

/-- **Milne, proof of Theorem 2.22** (the ramification count, unconditional): for `X(Γ) → X(1)`,
`∑ (e_{P'} - 1) = (m - ν₂)/2 + 2(m - ν₃)/3 + (m - ν∞)`. Tau Ceti's total ramification formula for finite-index
inclusions of cofinite Fuchsian groups, specialized to `Γ̄ ≤ Γ̄(1)`. -/
@[kb "milne2017mf" "Theorem 2.22, proof: the ramification of X(Gamma) over X(1), pdf p. 38"]
theorem ramificationDegree_modularCurveX :
    (ramificationDegree (modularCurveXMap Γ) : ℝ) =
      ((genusIndex Γ : ℝ) - nuTwo Γ) / 2 + 2 * ((genusIndex Γ : ℝ) - nuThree Γ) / 3 +
        ((genusIndex Γ : ℝ) - nuInfty Γ) := by
  have h := TauCeti.Fuchsian.ramificationDegree_eq_index_mul_cusps_add_elliptic_sub
    Γ.map_sl2zToPSL2R_le_range_psl2zToPSL2R TauCeti.ModularGroup.isCofinite_psl2zToPSL2RRange
  have hidx : ((Γ.map sl2zToPSL2R).subgroupOf psl2zToPSL2R.range).index = genusIndex Γ := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_map_sl2zToPSL2R]
    rfl
  rw [hidx, Nat.card_unique, TauCeti.ModularGroup.finsum_mem_ellipticOrbits_psl2zToPSL2RRange,
    finsum_ellipticOrbits_one_sub_inv Γ] at h
  rw [show ramificationDegree (modularCurveXMap Γ) =
    ramificationDegree (Subgroup.compactifiedQuotientMap Γ.map_sl2zToPSL2R_le_range_psl2zToPSL2R) from rfl, h, nuInfty]
  push_cast
  ring

/-! ### The map `j : X(Γ) → ℙ¹` -/

/-- `j : X(Γ) → X(1) ≅ ℙ¹`, a finite holomorphic map of degree `m`. -/
abbrev modularCurveXJ : FiniteHolomorphicMap (ModularCurveX Γ) (OnePoint ℂ) :=
  TauCeti.ModularGroup.jFiniteHolomorphicMap.comp (modularCurveXMap Γ)

/-- The isomorphism `j : X(1) → ℙ¹` is unramified. -/
theorem ramificationDegree_jFiniteHolomorphicMap :
    ramificationDegree TauCeti.ModularGroup.jFiniteHolomorphicMap = 0 := by
  rw [ramificationDegree_def]
  have h : ∀ x, localMultiplicity TauCeti.ModularGroup.jFiniteHolomorphicMap x - 1 = 0 := by
    intro x
    have := localMultiplicity_le_degree TauCeti.ModularGroup.jFiniteHolomorphicMap x
    rw [TauCeti.ModularGroup.coe_jFiniteHolomorphicMap, TauCeti.ModularGroup.degree_jSphere] at this
    rw [TauCeti.ModularGroup.coe_jFiniteHolomorphicMap]
    omega
  simp only [h, finsum_zero]

theorem degree_modularCurveXJ : degree (modularCurveXJ Γ) = genusIndex Γ := by
  rw [degree_comp, TauCeti.ModularGroup.coe_jFiniteHolomorphicMap, TauCeti.ModularGroup.degree_jSphere, one_mul]
  exact degree_modularCurveXMap Γ

theorem ramificationDegree_modularCurveXJ :
    ramificationDegree (modularCurveXJ Γ) = ramificationDegree (modularCurveXMap Γ) := by
  rw [ramificationDegree_comp, ramificationDegree_jFiniteHolomorphicMap, mul_zero, add_zero]

/-! ### Theorem 2.22 -/

/-- **Milne, Theorem 2.22** (the genus of `X(Γ)`), conditional on the Riemann–Hurwitz formula (Theorem 1.27, the
named input `RiemannHurwitzStatement`) for `X(Γ)` over the Riemann sphere: for `Γ` of finite index in `SL₂(ℤ)`,
`g(X(Γ)) = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. The book applies Riemann–Hurwitz to `X(Γ) → X(1)`; here it is applied to
the composite with the isomorphism `j : X(1) ≅ ℙ¹` (unramified), and `g(ℙ¹) = 0` is `genus_onePoint`. -/
@[kb "milne2017mf" "Theorem 2.22, pdf p. 37"]
theorem genus_modularCurveX (hRH : RiemannHurwitzStatement (ModularCurveX Γ) (OnePoint ℂ)) :
    (genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 := by
  have h := hRH.out (modularCurveXJ Γ)
  rw [genus_onePoint, degree_modularCurveXJ, ramificationDegree_modularCurveXJ] at h
  have hR := ramificationDegree_modularCurveX Γ
  have hR' : (ramificationDegree (modularCurveXMap Γ) : ℝ) =
      2 * (genus (ModularCurveX Γ) : ℝ) - 2 + 2 * genusIndex Γ := by
    have := congrArg (fun n : ℤ ↦ (n : ℝ)) h
    push_cast at this
    linarith
  have hreal : ((genus (ModularCurveX Γ) : ℚ) : ℝ) =
      ((1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 : ℚ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hreal

end ModularFormsKB.Milne
