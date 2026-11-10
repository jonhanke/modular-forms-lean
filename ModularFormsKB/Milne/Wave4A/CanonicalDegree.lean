import ModularFormsKB.Milne.Wave4A.GenusFormula
import ModularFormsKB.Milne.Wave4A.SphereRiemannRoch
import ModularFormsKB.Milne.RS.HurwitzOrder
import ModularFormsKB.Milne.RS.CanonicalGenus
import ModularFormsKB.Milne.RS.ResidueSphere
import ModularFormsKB.Milne.Ch4.UncondValence
import Mathlib.Algebra.Order.Star.Rat

/-!
# Milne, Proposition 2.21 (genus zero) and Theorem 2.22 from the canonical degree

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, Proposition 2.21 and Theorem 2.22 (pdf pp. 36–37).

For a finite holomorphic map `f : Y → ℙ¹`, the differential `ω = d(z ∘ f)` is nonzero and
`div ω = f^* div(dz) + R_f` (`RS.divisor_differential_pullbackFun`, Milne's proof of 1.27), so
`deg div ω = -2 deg f + R(f)` (`degree_divisor_differential_pullback_coordinate`).

* **Proposition 2.21, genus zero (unconditional).** For `j : X(1) → ℙ¹` (degree one, unramified) the canonical degree
  is `-2 < 0`, so `ℓ(K) = 0`; since `ℓ(K) = g` (`RS.ell_divisor_eq_genus`), `X(1)` has genus `0`
  (`genus_modularCurveXOne`).
* **Theorem 2.22 from Corollary 1.21.** For `j : X(Γ) → ℙ¹` the canonical degree is `-2m + R = 2(1 + m/12 - ν₂/4 -
  ν₃/3 - ν∞/2) - 2` unconditionally (`degree_canonical_modularCurveX`); so the genus formula is equivalent to the
  degree part of Corollary 1.21 for `X(Γ)` (the named input `CanonicalDegreeStatement`), and follows from it
  (`genus_modularCurveX_of_canonicalDegree`). This is a second conditional form of Theorem 2.22, alongside the
  Riemann–Hurwitz form `genus_modularCurveX`.
-/

open Set
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti TauCeti.RiemannSurface TauCeti.AlgebraicGeometry RiemannSurface MeromorphicFunction

section General

variable {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [CompactSpace Y]
  [ConnectedSpace Y] [T2Space Y]

/-- `d(z ∘ f) ≠ 0` for a finite holomorphic map `f : Y → ℙ¹`. -/
theorem differential_pullback_coordinate_not_isZero (f : FiniteHolomorphicMap Y (OnePoint ℂ)) :
    ¬ (differential (RS.pullbackFun f coordinate)).IsZero :=
  RS.differential_not_isZero (RS.isNonconstant_pullbackFun f RS.isNonconstant_coordinate)

/-- `deg div d(z ∘ f) = -2 deg f + R(f)` for a finite holomorphic map `f : Y → ℙ¹`. -/
theorem degree_divisor_differential_pullback_coordinate (f : FiniteHolomorphicMap Y (OnePoint ℂ)) :
    WeilDivisor.degree (differential (RS.pullbackFun f coordinate)).divisor =
      -2 * (degree f : ℤ) + ramificationDegree f := by
  rw [RS.divisor_differential_pullbackFun f RS.isNonconstant_coordinate, map_add, degree_divisorPullback,
    degree_ramificationDivisor, degree_divisor_sphere
      (RS.differential_not_isZero RS.isNonconstant_coordinate)]
  ring

end General

/-- **Milne, Proposition 2.21** (genus zero): the compact Riemann surface `X(1) = Γ(1)\ℍ*` has genus `0`.
Unconditional: the differential `dj` has divisor of degree `-2`, and `ℓ(K) = g`. -/
@[kb "milne2017mf" "Proposition 2.21: X(1) has genus zero, pdf p. 36"]
theorem genus_modularCurveXOne : RiemannSurface.genus ModularCurveXOne = 0 := by
  set f := TauCeti.ModularGroup.jFiniteHolomorphicMap
  have hω := differential_pullback_coordinate_not_isZero f
  have hdeg := degree_divisor_differential_pullback_coordinate f
  rw [ramificationDegree_jFiniteHolomorphicMap, TauCeti.ModularGroup.coe_jFiniteHolomorphicMap,
    TauCeti.ModularGroup.degree_jSphere] at hdeg
  rw [← RS.ell_divisor_eq_genus hω]
  exact ell_eq_zero_of_degree_neg (by rw [hdeg]; norm_num)

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- The canonical degree of `X(Γ)`, unconditionally: the divisor of `dj` on `X(Γ)` has degree
`2(1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2) - 2`. -/
theorem degree_canonical_modularCurveX :
    ((WeilDivisor.degree (differential (RS.pullbackFun (modularCurveXJ Γ) coordinate)).divisor : ℤ) : ℚ) =
      2 * (1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2) - 2 := by
  rw [degree_divisor_differential_pullback_coordinate, degree_modularCurveXJ, ramificationDegree_modularCurveXJ]
  have hR := ramificationDegree_modularCurveX Γ
  have : (((-2 * (genusIndex Γ : ℤ) + ramificationDegree (modularCurveXMap Γ) : ℤ) : ℚ) : ℝ) =
      ((2 * (1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2) - 2 : ℚ) :
        ℝ) := by
    push_cast
    rw [hR]
    ring
  exact_mod_cast this

/-- **Milne, Theorem 2.22**, conditional on the degree part of Corollary 1.21 for `X(Γ)` (the named input
`CanonicalDegreeStatement`): `g(X(Γ)) = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "milne2017mf" "Theorem 2.22, pdf p. 37"]
theorem genus_modularCurveX_of_canonicalDegree (hK : CanonicalDegreeStatement (ModularCurveX Γ)) :
    (RiemannSurface.genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 := by
  have h := hK.out _ (differential_pullback_coordinate_not_isZero (modularCurveXJ Γ))
  have h2 := degree_canonical_modularCurveX Γ
  rw [h] at h2
  push_cast at h2
  linarith

end ModularFormsKB.Milne
