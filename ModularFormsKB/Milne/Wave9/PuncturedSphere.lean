import ModularFormsKB.Milne.Wave4A.GenusEuler
import TauCeti.Geometry.Manifold.Triangulation.Puncture
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.BoundarySphere
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Geometry.Manifold.Instances.Sphere
import ModularFormsKB.Citation
/-!
# The punctured Riemann sphere has finite CW type; Remark 1.28 unconditionally

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Remark 1.28 (pdf p. 23) and Theorem 2.22 (pdf p. 37).

Wave 4A proved Theorem 2.22 in Euler-characteristic form (`eulerChar_puncture_modularCurveX`) conditionally on the
named topological input `PuncturedSphereFiniteCWType`: the Riemann sphere minus finitely many points has finite CW
type. This file proves that input, so the Euler-characteristic form becomes unconditional.

Proof: the Riemann sphere `OnePoint ℂ` is homeomorphic to the unit sphere `S²` of `ℝ³` (Mathlib
`onePointEquivSphereOfFinrankEq`); `S²` is triangulated by the boundary of the 3-simplex (Tau Ceti
`AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere`) and is a compact connected smooth
surface (Mathlib), so deleting finitely many points leaves a space of finite CW type (Tau Ceti
`Set.Finite.finiteCWType_compl_of_isTriangulable`).

## Items

- `puncturedSphereFiniteCWType`: the named input `PuncturedSphereFiniteCWType` holds.
- `eulerChar_puncture_modularCurveX'`: Theorem 2.22 / Remark 1.28 in punctured Euler-characteristic form,
  unconditional.
- `eulerChar_modularCurveX'`: `χ(X(Γ)) = 2 - 2g` for `X(Γ)` of finite CW type (the remaining hypothesis is that
  `X(Γ)` itself has finite CW type).
-/

open Set Metric
open scoped Manifold MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave9

open TauCeti TauCeti.RiemannSurface

/-- The unit sphere of `ℝ³` is triangulable: it is the realization of the boundary of the 3-simplex. -/
theorem isTriangulable_sphere_two :
    IsTriangulable.{0} (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨_, _, ⟨AbstractSimplicialComplex.realizationStandardSuccSimplexBoundaryHomeomorphSphere 2⟩⟩

/-- The unit sphere of `ℝ³` minus a finite set has finite CW type. -/
theorem finiteCWType_sphere_two_compl {S : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ := by
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]; norm_num
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere hdim 0 zero_le_one)
  have hdim2 : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]; norm_num
  exact hS.finiteCWType_compl_of_isTriangulable hdim2 isTriangulable_sphere_two

/-- **The named input `PuncturedSphereFiniteCWType` holds**: the Riemann sphere minus finitely many points has finite
CW type (Hatcher, *Algebraic Topology*, Chapter 0; here through a triangulation of the sphere). -/
@[kb "milne2017mf" "Remark 1.28, pdf p. 23: the punctured sphere is a finite complex (input of the topological proof)"]
theorem puncturedSphereFiniteCWType : PuncturedSphereFiniteCWType := by
  refine ⟨fun S hS => ?_⟩
  let e : OnePoint ℂ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  have := finiteCWType_sphere_two_compl (hS.image e)
  have heq : e ⁻¹' (e '' S)ᶜ = Sᶜ := by
    rw [preimage_compl, e.injective.preimage_image]
  exact (e.sets heq.symm).finiteCWType

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Milne, Theorem 2.22 and Remark 1.28, topological form (punctured), unconditional.** With `F ⊆ X(Γ)` the
preimage of the branch values of `j : X(Γ) → ℙ¹`, `χ(X(Γ) ∖ F) + #F = 2 - 2g` with
`g = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "milne2017mf" "Theorem 2.22 and Remark 1.28, Euler characteristic form, pdf pp. 23, 37"]
theorem eulerChar_puncture_modularCurveX' :
    haveI := puncturedSphereFiniteCWType.out _ (modularCurveXJ Γ).finite_branchValues
    haveI := (modularCurveXJ Γ).finiteCWType_compl_preimage (S := (modularCurveXJ Γ).branchValues) subset_rfl
    ((eulerChar ↥((modularCurveXJ Γ) ⁻¹' (modularCurveXJ Γ).branchValues)ᶜ : ℤ) : ℚ) +
        ((modularCurveXJ Γ) ⁻¹' (modularCurveXJ Γ).branchValues).ncard =
      2 - 2 * genusFormula Γ :=
  eulerChar_puncture_modularCurveX Γ puncturedSphereFiniteCWType

/-- **Milne, Theorem 2.22, topological form.** If `X(Γ)` has finite CW type, `χ(X(Γ)) = 2 - 2g` with
`g = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`; no other input. -/
@[kb "milne2017mf" "Theorem 2.22 and Remark 1.28, Euler characteristic form, pdf pp. 23, 37"]
theorem eulerChar_modularCurveX' [FiniteCWType (ModularCurveX Γ)] :
    (eulerChar (ModularCurveX Γ) : ℚ) = 2 - 2 * genusFormula Γ :=
  eulerChar_modularCurveX Γ puncturedSphereFiniteCWType

end ModularFormsKB.Milne.Wave9
