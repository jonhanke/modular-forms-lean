import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.Algebra.QuadraticAlgebra.Rat
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Quadratic number fields are `ℚ(√m)`

Every quadratic number field `K` contains a square root of a squarefree integer `m ≠ 1`.
The proof goes through Mathlib's classification of quadratic algebras over `ℚ`
(`QuadraticAlgebra.Rat.exists_squarefree_algEquiv`).
-/

namespace ModularFormsKB.WeberHeegnerStark

open QuadraticAlgebra

/-- Every quadratic number field is `ℚ(√m)` for a squarefree integer `m ≠ 1`: there is a squarefree
integer `m ≠ 1` which is a square in `K`. -/
theorem exists_squarefree_isSquare (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    ∃ m : ℤ, Squarefree m ∧ m ≠ 1 ∧ IsSquare (m : K) := by
  have : Algebra.IsQuadraticExtension ℚ K :=
    { finrank_eq_two' := hK }
  obtain ⟨a, b, ⟨e⟩⟩ := Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℚ) (A := K)
  have hfield : IsField (QuadraticAlgebra ℚ a b) :=
    e.symm.toRingEquiv.isField (Field.toIsField K)
  have hdisc : discr a b ≠ 0 := by
    intro h0
    exact not_isField_of_isSquare_discr (by rw [h0]; exact IsSquare.zero) hfield
  obtain ⟨d, hd, ⟨f⟩⟩ := Rat.exists_squarefree_algEquiv hdisc
  let g : K ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0 := e.trans f
  have hsq : (g.symm ω) * (g.symm ω) = (d : K) := by
    rw [← map_mul, omega_mul_omega_eq_add]
    simp
  refine ⟨d, hd, ?_, ⟨g.symm ω, hsq.symm⟩⟩
  rintro rfl
  have h1 : (g.symm ω - 1) * (g.symm ω + 1) = 0 := by
    have : (g.symm ω) * (g.symm ω) = 1 := by simpa using hsq
    linear_combination this
  rcases mul_eq_zero.mp h1 with h | h
  · have : g.symm ω = g.symm 1 := by rw [map_one]; exact sub_eq_zero.mp h
    have := g.symm.injective this
    have := congrArg QuadraticAlgebra.im this
    simp at this
  · have : g.symm ω = g.symm (-1) := by rw [map_neg, map_one]; exact eq_neg_of_add_eq_zero_left h
    have := g.symm.injective this
    have := congrArg QuadraticAlgebra.im this
    simp at this

end ModularFormsKB.WeberHeegnerStark
