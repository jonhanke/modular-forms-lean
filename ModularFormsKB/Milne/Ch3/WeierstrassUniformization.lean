import ModularFormsKB.Milne.Ch3.Uniformization
import ModularFormsKB.Milne.Ch3.JSurjective
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ

/-!
# Milne, Proposition 3.12: every elliptic curve over `ℂ` is `E(Λ)`

The bijection `ℂ/Λ → E(Λ)` is `bijective_weierstrassPoint`. For the last part, an elliptic curve `E` over `ℂ`
has `j(E) = j(τ)` for some `τ ∈ ℍ` (surjectivity of `j`, `j_surjective`), the curve of `ℤτ + ℤ` has
`j`-invariant `j(τ)` (Tau Ceti `UpperHalfPlane.weierstrassCurve_j_periodPair`), and over an algebraically closed
field two elliptic curves with the same `j`-invariant are related by a change of variables (Mathlib
`WeierstrassCurve.exists_variableChange_of_j_eq`). Milne proves the last part in the same way in §4.
-/

open Complex UpperHalfPlane

namespace ModularFormsKB.Milne

/-- Every elliptic curve over `ℂ` is isomorphic to `E(Λ)` for some lattice `Λ`. -/
theorem exists_periodPair_variableChange (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • E = L.weierstrassCurve := by
  obtain ⟨τ, hτ⟩ := j_surjective E.j
  exact ⟨τ.periodPair, WeierstrassCurve.exists_variableChange_of_j_eq E τ.periodPair.weierstrassCurve
    (by rw [weierstrassCurve_j_periodPair, hτ])⟩

/-- **Milne, Proposition 3.12** (second and third parts), proved unconditionally. -/
theorem weierstrassUniformizationStatement : WeierstrassUniformizationStatement :=
  ⟨bijective_weierstrassPoint, fun E hE ↦ by
    have := hE
    exact exists_periodPair_variableChange E⟩

end ModularFormsKB.Milne
