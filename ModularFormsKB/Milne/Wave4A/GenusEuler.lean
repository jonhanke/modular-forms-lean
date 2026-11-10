import ModularFormsKB.Milne.Wave4A.GenusFormula
import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Puncture
import TauCeti.Topology.CWComplex.Classical.Sphere.Basic

/-!
# Milne, Theorem 2.22 in Euler-characteristic form

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, Theorem 2.22 (pdf p. 37) and Remark 1.28 (pdf
p. 23: the Riemann–Hurwitz formula "also follows by triangulating and counting").

Milne's third proof of Proposition 2.21 and Remark 1.28 use the topological genus, `χ = 2 - 2g`. Tau Ceti proves the
topological Riemann–Hurwitz formula `χ(X) = deg f · χ(Y) - R(f)` for finite holomorphic maps of compact Riemann
surfaces (`TauCeti.RiemannSurface.FiniteHolomorphicMap.eulerChar_compl_preimage_add_ncard_add_ramificationDegree`),
with the Euler characteristic of spaces of finite CW type. Combined with the ramification count of `X(Γ) → X(1)`
(`ramificationDegree_modularCurveX`, unconditional), this gives the genus formula for the topological genus, without
Riemann–Roch:

* `eulerChar_puncture_modularCurveX`: `χ(X(Γ) ∖ F) + #F = 2 - 2(1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2)`, where `F` is the
  preimage of the branch values of `j : X(Γ) → ℙ¹`;
* `eulerChar_modularCurveX`: if `X(Γ)` has finite CW type, `χ(X(Γ)) = 2 - 2(1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2)`.

The one input is topological and is stated as the named structure `PuncturedSphereFiniteCWType`: the Riemann sphere
minus finitely many points has finite CW type (it is homotopy equivalent to a wedge of circles). The missing lemma is
a homotopy equivalence from `ℂ` minus `n` points to Tau Ceti's wedge of `n` circles
(`TauCeti.WedgeSum.circleCWComplex`); Tau Ceti has only the fundamental group of the punctured plane
(`TauCeti.nonempty_fundamentalGroup_compl_mulEquiv_freeGroup`) and the finite-CW type of triangulable manifolds minus
points (`finiteCWType_compl_of_isTriangulable`), not a triangulation of the sphere.
-/

open Set
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti TauCeti.RiemannSurface

/-- **Named input (topology).** The Riemann sphere minus a finite set of points has finite CW type (Hatcher,
*Algebraic Topology*, Chapter 0: the plane minus `n` points deformation retracts onto a wedge of `n` circles). -/
structure PuncturedSphereFiniteCWType : Prop where
  out : ∀ S : Set (OnePoint ℂ), S.Finite → FiniteCWType ↥Sᶜ

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Milne, Theorem 2.22, topological form (punctured).** Let `F ⊆ X(Γ)` be the preimage of the branch values of
`j : X(Γ) → ℙ¹`. Then `χ(X(Γ) ∖ F) + #F = 2 - 2g` with `g = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. Conditional only on the
topological input `PuncturedSphereFiniteCWType`. -/
@[kb "milne2017mf" "Theorem 2.22 and Remark 1.28, Euler characteristic form, pdf pp. 23, 37"]
theorem eulerChar_puncture_modularCurveX (hS : PuncturedSphereFiniteCWType) :
    haveI := hS.out _ (modularCurveXJ Γ).finite_branchValues
    haveI := (modularCurveXJ Γ).finiteCWType_compl_preimage (S := (modularCurveXJ Γ).branchValues) subset_rfl
    ((eulerChar ↥((modularCurveXJ Γ) ⁻¹' (modularCurveXJ Γ).branchValues)ᶜ : ℤ) : ℚ) +
        ((modularCurveXJ Γ) ⁻¹' (modularCurveXJ Γ).branchValues).ncard =
      2 - 2 * genusFormula Γ := by
  set f := modularCurveXJ Γ with hf
  have hfin := f.finite_branchValues
  have := hS.out _ hfin
  have := f.finiteCWType_compl_preimage (S := f.branchValues) subset_rfl
  have h := f.eulerChar_compl_preimage_add_ncard_add_ramificationDegree hfin subset_rfl
  have hY := eulerChar_compl_of_finite (E := ℂ) (X := OnePoint ℂ) hfin
  rw [Complex.finrank_real_complex, eulerChar_onePoint, Complex.finrank_real_complex] at hY
  norm_num at hY
  rw [degree_modularCurveXJ, ramificationDegree_modularCurveXJ] at h
  have hR := ramificationDegree_modularCurveX Γ
  have hYq : ((eulerChar ↥f.branchValuesᶜ : ℤ) : ℝ) + f.branchValues.ncard = 2 := by
    have := congrArg (fun n : ℤ ↦ (n : ℝ)) hY
    push_cast at this
    linarith
  have hreal := congrArg (fun n : ℤ ↦ (n : ℝ)) h
  push_cast at hreal
  rw [hYq] at hreal
  have : ((((eulerChar ↥(f ⁻¹' f.branchValues)ᶜ : ℤ) : ℚ) + (f ⁻¹' f.branchValues).ncard : ℚ) : ℝ) =
      ((2 - 2 * genusFormula Γ : ℚ) : ℝ) := by
    simp only [genusFormula]
    push_cast
    linarith
  exact_mod_cast this

/-- **Milne, Theorem 2.22, topological form.** If `X(Γ)` has finite CW type, its Euler characteristic is `2 - 2g`
with `g = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. Conditional only on the topological input `PuncturedSphereFiniteCWType`. -/
@[kb "milne2017mf" "Theorem 2.22 and Remark 1.28, Euler characteristic form, pdf pp. 23, 37"]
theorem eulerChar_modularCurveX (hS : PuncturedSphereFiniteCWType) [FiniteCWType (ModularCurveX Γ)] :
    (eulerChar (ModularCurveX Γ) : ℚ) = 2 - 2 * genusFormula Γ := by
  set f := modularCurveXJ Γ with hf
  have hfin := f.finite_branchValues
  have := hS.out _ hfin
  have := f.finiteCWType_compl_preimage (S := f.branchValues) subset_rfl
  have hP := eulerChar_puncture_modularCurveX Γ hS
  have hX := eulerChar_compl_of_finite (E := ℂ) (X := ModularCurveX Γ)
    (hfin.preimage' fun y _ ↦ f.finite_fiber y)
  rw [Complex.finrank_real_complex] at hX
  rw [← hP, hX]
  push_cast
  ring

end ModularFormsKB.Milne
