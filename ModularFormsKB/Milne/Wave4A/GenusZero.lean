import ModularFormsKB.Milne.Wave4A.CanonicalDegree
import ModularFormsKB.Milne.Wave4A.GenusGammaN

/-!
# Milne, Theorem 2.22 for curves of genus zero, and the valence formula there

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, Theorem 2.22 and Example 2.23 (pdf pp. 37–38), §4,
Proposition 4.12 and Example 4.13 (pdf pp. 53–54).

Every canonical divisor of `X(Γ)` has degree `2g₀ - 2`, `g₀ = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`, unconditionally
(`degree_canonical_modularCurveX` and `RS.degree_divisor_eq_of_not_isZero`). When `g₀ = 0` the canonical degree is
`-2 < 0`, so `g = ℓ(K) = 0`: Theorem 2.22 holds unconditionally (`genus_modularCurveX_of_genusFormula_eq_zero`),
the degree part of Corollary 1.21 holds for `X(Γ)` (`canonicalDegreeStatement_of_genusFormula_eq_zero`), and hence
so does the valence formula, Proposition 4.12 (`valenceFormula_of_genusFormula_eq_zero`, through
`valenceFormula_of_canonicalDegree`).

Instances:
* `Γ(1) = SL₂(ℤ)`: `X(1)` has genus `0`, and Proposition 4.12 for `Γ(1)` (the meromorphic case of Example 4.13)
  holds (`valenceFormula_top`);
* `Γ(N)`, `N = 2, 3, 4, 5`: `g₀ = 0` (Example 2.23's table), so `X(N)` has genus `0` and Proposition 4.12 holds
  (`genus_modularCurveX_Gamma_eq_zero`, `valenceFormula_Gamma`).
-/

open Set CongruenceSubgroup
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti TauCeti.RiemannSurface TauCeti.AlgebraicGeometry RiemannSurface MeromorphicFunction

/-- A compact Riemann surface carrying a nonzero differential form of degree `-2` has genus `0`, and every canonical
divisor has degree `2g - 2 = -2`. -/
theorem canonicalDegreeStatement_of_degree_eq_neg_two {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [ConnectedSpace X] [T2Space X]
    {θ₀ : MeromorphicDifferential X} (hθ₀ : ¬ θ₀.IsZero) (hdeg : WeilDivisor.degree θ₀.divisor = -2) :
    RiemannSurface.genus X = 0 ∧ CanonicalDegreeStatement X := by
  have hg : RiemannSurface.genus X = 0 := by
    rw [← RS.ell_divisor_eq_genus hθ₀]
    exact ell_eq_zero_of_degree_neg (by rw [hdeg]; norm_num)
  refine ⟨hg, ⟨fun θ hθ ↦ ?_⟩⟩
  rw [RS.degree_divisor_eq_of_not_isZero hθ hθ₀, hdeg, hg]
  rfl

/-- **The degree part of Corollary 1.21 for the Riemann sphere.** -/
theorem canonicalDegreeStatement_onePoint : CanonicalDegreeStatement (OnePoint ℂ) :=
  (canonicalDegreeStatement_of_degree_eq_neg_two (RS.differential_not_isZero RS.isNonconstant_coordinate)
    (degree_divisor_sphere (RS.differential_not_isZero RS.isNonconstant_coordinate))).2

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- If `1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2 = 0`, then `X(Γ)` has genus `0` and satisfies the degree part of
Corollary 1.21. -/
theorem genus_and_canonicalDegree_of_genusFormula_eq_zero (h : genusFormula Γ = 0) :
    RiemannSurface.genus (ModularCurveX Γ) = 0 ∧ CanonicalDegreeStatement (ModularCurveX Γ) := by
  refine canonicalDegreeStatement_of_degree_eq_neg_two
    (differential_pullback_coordinate_not_isZero (modularCurveXJ Γ)) ?_
  have h2 := degree_canonical_modularCurveX Γ
  rw [show (1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2) =
    genusFormula Γ from rfl, h] at h2
  exact_mod_cast (by push_cast; linarith : ((WeilDivisor.degree
    (differential (RS.pullbackFun (modularCurveXJ Γ) coordinate)).divisor : ℤ) : ℚ) = ((-2 : ℤ) : ℚ))

/-- **Milne, Theorem 2.22, unconditional when the formula gives genus `0`.** -/
@[kb "milne2017mf" "Theorem 2.22, pdf p. 37"]
theorem genus_modularCurveX_of_genusFormula_eq_zero (h : genusFormula Γ = 0) :
    (RiemannSurface.genus (ModularCurveX Γ) : ℚ) = genusFormula Γ := by
  rw [(genus_and_canonicalDegree_of_genusFormula_eq_zero Γ h).1, h]
  rfl

/-- **Milne, Proposition 4.12 (the valence formula)** for `Γ` with `1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2 = 0`,
unconditional. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53)"]
theorem valenceFormula_of_genusFormula_eq_zero (h : genusFormula Γ = 0) : ValenceFormula Γ :=
  valenceFormula_of_canonicalDegree Γ (genus_and_canonicalDegree_of_genusFormula_eq_zero Γ h).2

/-! ### Level one -/

/-- A finite holomorphic map of degree one is unramified. -/
theorem ramificationDegree_eq_zero_of_degree_eq_one {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [ConnectedSpace X] [T2Space X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [ConnectedSpace Y] [T2Space Y]
    (f : FiniteHolomorphicMap X Y) (hf : degree f = 1) : ramificationDegree f = 0 := by
  rw [ramificationDegree_def]
  have h : ∀ x, localMultiplicity f x - 1 = 0 := by
    intro x
    have := localMultiplicity_le_degree f x
    omega
  simp only [h, finsum_zero]

theorem genusIndex_top : genusIndex ⊤ = 1 := by
  rw [genusIndex, Subgroup.withCenter_def, top_sup_eq, Subgroup.index_top]

/-- **Milne, Proposition 2.21** (genus zero), for `X(Γ(1))` as the curve `X(Γ)` of `Γ = SL₂(ℤ)`, together with the
degree part of Corollary 1.21. -/
theorem genus_and_canonicalDegree_top :
    RiemannSurface.genus (ModularCurveX ⊤) = 0 ∧ CanonicalDegreeStatement (ModularCurveX ⊤) := by
  have hdeg1 : degree (modularCurveXJ ⊤) = 1 := by rw [degree_modularCurveXJ, genusIndex_top]
  refine canonicalDegreeStatement_of_degree_eq_neg_two
    (differential_pullback_coordinate_not_isZero (modularCurveXJ ⊤)) ?_
  rw [degree_divisor_differential_pullback_coordinate, hdeg1,
    ramificationDegree_eq_zero_of_degree_eq_one _ hdeg1]
  rfl

/-- **Milne, Proposition 4.12 for `Γ(1)`** (Example 4.13, meromorphic modular forms), unconditional. -/
@[kb "milne2017mf" "Section 4, Example 4.13 (pdf p. 54)"]
theorem valenceFormula_top : ValenceFormula ⊤ :=
  valenceFormula_of_canonicalDegree ⊤ genus_and_canonicalDegree_top.2

/-! ### `X(N)` for `N = 2, 3, 4, 5` -/

theorem index_adjoinNegOne_Gamma_three : ((Miyake.adjoinNegOne (Gamma 3)).index : ℚ) = 12 := by
  rw [index_adjoinNegOne_Gamma_eq (by norm_num), index_Gamma_eq, Nat.Prime.primeFactors Nat.prime_three]
  norm_num

theorem index_adjoinNegOne_Gamma_four : ((Miyake.adjoinNegOne (Gamma 4)).index : ℚ) = 24 := by
  rw [index_adjoinNegOne_Gamma_eq (by norm_num), index_Gamma_eq,
    show (4 : ℕ) = 2 ^ 2 from rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  norm_num

theorem index_adjoinNegOne_Gamma_five : ((Miyake.adjoinNegOne (Gamma 5)).index : ℚ) = 60 := by
  rw [index_adjoinNegOne_Gamma_eq (by norm_num), index_Gamma_eq, Nat.Prime.primeFactors Nat.prime_five]
  norm_num

theorem genusFormula_Gamma_eq_zero {N : ℕ} [NeZero N] (hN : 2 ≤ N) (hN5 : N ≤ 5) :
    genusFormula (Gamma N) = 0 := by
  rw [genusFormula_Gamma hN]
  interval_cases N
  · rw [show ((Miyake.adjoinNegOne (Gamma 2)).index : ℚ) = 6 by exact_mod_cast index_adjoinNegOne_Gamma_two_eq]
    norm_num
  · rw [index_adjoinNegOne_Gamma_three]; norm_num
  · rw [index_adjoinNegOne_Gamma_four]; norm_num
  · rw [index_adjoinNegOne_Gamma_five]; norm_num

/-- **Milne, Example 2.23** (the table, `g = 0` for `N = 2, …, 5`), unconditional: `X(N)` has genus `0` for
`2 ≤ N ≤ 5`. -/
@[kb "milne2017mf" "Example 2.23: the genus of X(N), pdf p. 38"]
theorem genus_modularCurveX_Gamma_eq_zero {N : ℕ} [NeZero N] (hN : 2 ≤ N) (hN5 : N ≤ 5) :
    RiemannSurface.genus (ModularCurveX (Gamma N)) = 0 :=
  (genus_and_canonicalDegree_of_genusFormula_eq_zero _ (genusFormula_Gamma_eq_zero hN hN5)).1

/-- **Milne, Proposition 4.12** for `Γ(N)`, `2 ≤ N ≤ 5`, unconditional. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53)"]
theorem valenceFormula_Gamma {N : ℕ} [NeZero N] (hN : 2 ≤ N) (hN5 : N ≤ 5) : ValenceFormula (Gamma N) :=
  valenceFormula_of_genusFormula_eq_zero _ (genusFormula_Gamma_eq_zero hN hN5)

end ModularFormsKB.Milne
