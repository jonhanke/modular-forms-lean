import ModularFormsKB.Milne.Wave15.Existence
import ModularFormsKB.Milne.RS.ResidueTheorem
import ModularFormsKB.Milne.RS.RiemannHurwitz
import ModularFormsKB.Milne.RS.CanonicalGenus
import ModularFormsKB.Milne.Wave10.RiemannRochInputs

/-!
# Milne, Chapter 1 on every compact Riemann surface

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1 (pdf pp. 19–22). With the existence theorem
(`Wave15.existsNonconstantStatement`, `Wave15.separates`) and Riemann–Roch (`Wave15.riemannRochStatement`) proved for
every compact Riemann surface, the library's reductions give, with no hypothesis beyond compactness:

* Proposition 1.12 (b), the residue theorem (`residueTheoremStatement`);
* Theorem 1.17, second statement: `M(X)` is an algebraic function field of one variable (`isFunctionField`);
* Corollary 1.21: `deg K = 2g - 2` (`canonicalDegreeStatement`);
* Corollary 1.22: `ℓ(D) = deg D + 1 - g` when `deg D > 2g - 2` (`ell_eq_of_two_mul_genus_sub_two_lt`);
* Theorem 1.27, Riemann–Hurwitz, for every finite holomorphic map of compact Riemann surfaces
  (`riemannHurwitzStatement`).
-/

open TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface TauCeti.AlgebraicGeometry
open scoped Manifold

universe u v

noncomputable section

namespace ModularFormsKB.Milne.Wave15

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [ConnectedSpace X] [T2Space X]

/-- **Milne, Proposition 1.12 (b)** (the residue theorem) on every compact Riemann surface. -/
@[kb "milne2017mf" "Proposition 1.12 (b), pdf p. 19"]
theorem residueTheoremStatement : ResidueTheoremStatement X :=
  RS.residueTheoremStatement_of_existsNonconstant existsNonconstantStatement

/-- **Milne, Theorem 1.17** (second statement) on every compact Riemann surface: `M(X)` is a finitely generated field
of transcendence degree one over `ℂ`. -/
@[kb "milne2017mf" "Theorem 1.17, pdf p. 20"]
theorem isFunctionField : TauCeti.IsFunctionField ℂ (MeromorphicFunction X) ∧
    (⊤ : IntermediateField ℂ (MeromorphicFunction X)).FG :=
  isFunctionField_of_exists_nonconstant existsNonconstantStatement

/-- **Milne, Corollary 1.21** on every compact Riemann surface: a canonical divisor has degree `2g - 2`. -/
@[kb "milne2017mf" "Corollary 1.21, pdf p. 21"]
theorem canonicalDegreeStatement : CanonicalDegreeStatement X :=
  Wave10.canonicalDegreeStatement_of_riemannRoch riemannRochStatement

/-- **Milne, Corollary 1.22** on every compact Riemann surface: if `deg D > 2g - 2` then `ℓ(D) = deg D + 1 - g`,
`g` the genus. -/
@[kb "milne2017mf" "Corollary 1.22, pdf p. 22"]
theorem ell_eq_of_two_mul_genus_sub_two_lt {D : WeilDivisor X}
    (hD : 2 * (genus X : ℤ) - 2 < WeilDivisor.degree D) :
    (ell X D : ℤ) = WeilDivisor.degree D + 1 - genus X := by
  obtain ⟨g, hg⟩ := (riemannRochStatement (X := X)).exists_genus
  obtain ⟨f, hf⟩ := (existsNonconstantStatement (X := X)).out
  have hω := RS.differential_not_isZero hf
  have e : genus X = g :=
    (RS.ell_divisor_eq_genus hω).symm.trans (degree_canonical_and_ell_canonical hg hω).2
  rw [e] at hD ⊢
  exact ell_eq_of_degree_gt hg ⟨_, hω⟩ hD

/-- **Milne, Theorem 1.27 (Riemann–Hurwitz)** for every finite holomorphic map of compact Riemann surfaces. -/
@[kb "milne2017mf" "Theorem 1.27 (Riemann-Hurwitz), pdf p. 22"]
theorem riemannHurwitzStatement (Y : Type v) [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    [CompactSpace Y] [ConnectedSpace Y] [T2Space Y] : RiemannHurwitzStatement Y X :=
  RS.riemannHurwitzStatement_of_riemannRoch riemannRochStatement riemannRochStatement
    existsNonconstantStatement

end ModularFormsKB.Milne.Wave15
