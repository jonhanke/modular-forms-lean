import ModularFormsKB.Milne.Ch4.UncondDimension
import ModularFormsKB.Milne.RS.RiemannHurwitz
import ModularFormsKB.Citation
/-!
# Theorem 4.9 and Proposition 4.12 from the Riemann–Roch theorem on `X(Γ)` alone

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Corollary 1.21 (pdf p. 21), Theorem 4.9 (pdf p. 51),
Proposition 4.12 (pdf p. 53).

The library derives the dimension formula 4.9 from two named inputs on `X(Γ)`, the Riemann–Roch theorem
(`RiemannRochStatement`) and the degree of a canonical divisor `2g - 2` with `g` the genus
(`CanonicalDegreeStatement`, Corollary 1.21), and the valence formula 4.12 from the second
(`dimensionFormula_of_riemannRoch`, `valenceFormula_of_canonicalDegree`). The second input follows from the first, as in
Milne's proof of Corollary 1.21 (`RS.degree_divisor_eq_two_mul_genus_sub_two`, with the integer of the Riemann–Roch
theorem identified with the genus): `canonicalDegreeStatement_of_riemannRoch`. So both results hold for every
finite-index `Γ` from the Riemann–Roch theorem on `X(Γ)` alone.
-/

open scoped Manifold MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave10

open ModularFormsKB.Milne.RiemannSurface

/-- **Milne, Corollary 1.21 (`deg K = 2g - 2`) from the Riemann–Roch theorem**, in the form of the named statement
`CanonicalDegreeStatement` (with `g` the genus, the dimension of the holomorphic differentials). -/
@[kb "milne2017mf" "Corollary 1.21, pdf p. 21, from Theorem 1.20"]
theorem canonicalDegreeStatement_of_riemannRoch {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [ConnectedSpace X] [T2Space X] (hRR : RiemannRochStatement X) :
    CanonicalDegreeStatement X :=
  ⟨fun _ hθ ↦ RS.degree_divisor_eq_two_mul_genus_sub_two hRR hθ⟩

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Milne, Theorem 4.9** (the dimension formula) from the Riemann–Roch theorem on `X(Γ)` alone. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51), from Theorem 1.20 on X(Gamma)"]
theorem dimensionFormula_of_riemannRoch' (hRR : RiemannRochStatement (modularCurve Γ)) : DimensionFormula Γ :=
  dimensionFormula_of_riemannRoch Γ hRR (canonicalDegreeStatement_of_riemannRoch hRR)

/-- **Milne, Proposition 4.12** (the valence formula) from the Riemann–Roch theorem on `X(Γ)` alone. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53), from Theorem 1.20 on X(Gamma)"]
theorem valenceFormula_of_riemannRoch (hRR : RiemannRochStatement (modularCurve Γ)) : ValenceFormula Γ :=
  valenceFormula_of_canonicalDegree Γ (canonicalDegreeStatement_of_riemannRoch hRR)

end ModularFormsKB.Milne.Wave10
