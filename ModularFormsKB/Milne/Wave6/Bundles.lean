import ModularFormsKB.Milne.RiemannSurface.Examples

/-!
# Milne wave 6: full statements of items proved in parts

Earlier waves proved each part of the following items of Milne's notes under separate citations (`Example 1.5: the
transition map`, `Example 1.5: the Riemann sphere`, …). Here each item is stated in full, as one theorem whose
statement is the conjunction of its parts, so that the book map records the item, not only its parts, as proved. No
new mathematics: every conjunct is the earlier theorem named in the docstring.
-/

open Complex
open scoped Manifold Real

namespace ModularFormsKB.Milne.Wave6

/-- **Milne, Example 1.5** (pdf p. 15), in full, with the corrected south chart (erratum: the book's
`(x + iy)/(1 + z)` gives the antiholomorphic transition `w ↦ 1/w̄`, `stereoSouth_book_eq`): the stereographic
projections `σ_N`, `σ_S` from the two poles are charts with holomorphic transition map, `σ_S = 1/σ_N` off the poles
(`stereoSouth_mul_stereoNorth`), and the resulting Riemann surface is the Riemann sphere: a homeomorphism of the unit
sphere onto `OnePoint ℂ` carries the two charts of `OnePoint ℂ` to `σ_N` and `σ_S` (`exists_homeomorph_onePoint`). -/
@[kb "milne2017mf" "Example 1.5, pdf p. 15"]
theorem example_1_5 :
    (∀ p : UnitSphere, p ≠ northPole → p ≠ southPole → stereoSouth p * stereoNorth p = 1) ∧
    ∃ Φ : UnitSphere ≃ₜ OnePoint ℂ, Φ northPole = OnePoint.infty ∧ Φ southPole = ((0 : ℂ) : OnePoint ℂ) ∧
      (∀ p, p ≠ northPole → chartAt ℂ ((0 : ℂ) : OnePoint ℂ) (Φ p) = stereoNorth p) ∧
      (∀ p, p ≠ southPole → chartAt ℂ (OnePoint.infty : OnePoint ℂ) (Φ p) = stereoSouth p) :=
  ⟨fun _ hN hS ↦ stereoSouth_mul_stereoNorth hN hS, exists_homeomorph_onePoint⟩

/-- **Milne, Example 1.10** (pdf p. 17), in full: `ℂ/ℤ` has the complex structure for which a function `f` on an open
`U ⊆ ℂ/ℤ` is holomorphic exactly when `f ∘ p` is holomorphic on `p⁻¹(U)` (`mdifferentiableOn_cylinder_iff`), and
`q = e^{2πiz}` is an isomorphism `ℂ/ℤ ≅ ℂˣ` of Riemann surfaces and of topological groups
(`exists_cylinder_equiv_puncturedPlane`). -/
@[kb "milne2017mf" "Example 1.10, pdf p. 17"]
theorem example_1_10 :
    (∀ (f : Cylinder → ℂ) (U : Set Cylinder), IsOpen U →
      (MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U ↔ DifferentiableOn ℂ (f ∘ Cylinder.mk) (Cylinder.mk ⁻¹' U))) ∧
    ∃ e : Cylinder ≃ₜ puncturedPlane, (∀ z, (e (Cylinder.mk z) : ℂ) = exp (2 * π * I * z)) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm ∧
      ∀ x y, (e (x + y) : ℂ) = e x * e y :=
  ⟨mdifferentiableOn_cylinder_iff, exists_cylinder_equiv_puncturedPlane⟩

end ModularFormsKB.Milne.Wave6
