import ModularFormsKB.Milne.RS.ResidueTheorem
import ModularFormsKB.Milne.RS.RiemannHurwitz
import ModularFormsKB.Milne.Wave4A.GenusFormula
import ModularFormsKB.Milne.Wave4A.SphereRiemannRoch
import ModularFormsKB.Citation
/-!
# Theorem 1.17 and Proposition 1.12 (b) on the modular curves `X(Γ)`; Theorem 2.22 from Riemann–Roch on `X(Γ)`

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.17 (pdf p. 20), Proposition 1.12 (b)
(pdf p. 19), Theorem 1.27 (pdf p. 22), Theorem 2.22 (pdf p. 37).

The library proves Theorem 1.17 (second statement: the meromorphic functions form a function field of one variable,
`RiemannSurface.isFunctionField_of_exists_nonconstant`), the residue theorem 1.12 (b)
(`RS.residueTheoremStatement_of_existsNonconstant`) and Riemann–Hurwitz 1.27 (`RS.riemannHurwitzStatement_of_riemannRoch`)
on a compact Riemann surface from the existence of one nonconstant meromorphic function (the first statement of
Theorem 1.17, the named input `ExistsNonconstantStatement`). On the modular curve `X(Γ)` of a finite-index subgroup
`Γ ≤ SL₂(ℤ)` that input holds: `j : X(Γ) → X(1) ≅ ℙ¹` (`modularCurveXJ`) is a nonconstant meromorphic function. So:

- `jMeromorphic Γ`, `isNonconstant_jMeromorphic`, **`existsNonconstant_modularCurveX`**: Theorem 1.17 (first
  statement) for `X(Γ)`;
- **`isFunctionField_modularCurveX`**: Theorem 1.17 (second statement) for `X(Γ)`, unconditional;
- **`residueTheorem_modularCurveX`**: Proposition 1.12 (b) for `X(Γ)`, unconditional;
- `riemannHurwitz_modularCurveX`: Theorem 1.27 for `j : X(Γ) → ℙ¹` from the Riemann–Roch theorem on `X(Γ)` alone
  (Riemann–Roch on the sphere is proved, `riemannRoch_sphere`);
- `genus_modularCurveX_of_riemannRoch`: Theorem 2.22 (analytic genus) from the Riemann–Roch theorem on `X(Γ)` alone,
  Milne's route (Riemann–Hurwitz for `j`), replacing the hypothesis `RiemannHurwitzStatement` of wave 4A.
-/

open TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface
open scoped Manifold MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave10

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- `j : X(Γ) → ℙ¹` as a meromorphic function on `X(Γ)`. -/
def jMeromorphic : MeromorphicFunction (ModularCurveX Γ) where
  toFun := modularCurveXJ Γ
  mdifferentiable' := (modularCurveXJ Γ).holomorphic
  ne_infty' := fun h ↦ by
    obtain ⟨x, x', hxx'⟩ := (modularCurveXJ Γ).nonconstant
    exact hxx' ((congrFun h x).trans (congrFun h x').symm)

theorem isNonconstant_jMeromorphic : IsNonconstant (jMeromorphic Γ) :=
  (modularCurveXJ Γ).nonconstant

/-- **Milne, Theorem 1.17 (first statement) for `X(Γ)`**: the modular curve has a nonconstant meromorphic function,
namely `j`. -/
@[kb "milne2017mf" "Theorem 1.17, pdf p. 20, for the modular curves X(Gamma)"]
theorem existsNonconstant_modularCurveX : ExistsNonconstantStatement (ModularCurveX Γ) :=
  ⟨⟨jMeromorphic Γ, isNonconstant_jMeromorphic Γ⟩⟩

/-- **Milne, Theorem 1.17 for `X(Γ)`**: the meromorphic functions on `X(Γ)` form a finitely generated field of
transcendence degree one over `ℂ`. -/
@[kb "milne2017mf" "Theorem 1.17, pdf p. 20, for the modular curves X(Gamma)"]
theorem isFunctionField_modularCurveX :
    TauCeti.IsFunctionField ℂ (MeromorphicFunction (ModularCurveX Γ)) ∧
      (⊤ : IntermediateField ℂ (MeromorphicFunction (ModularCurveX Γ))).FG :=
  isFunctionField_of_exists_nonconstant (existsNonconstant_modularCurveX Γ)

/-- **Milne, Proposition 1.12 (b) for `X(Γ)`** (the residue theorem): the residues of a meromorphic differential on
`X(Γ)` sum to zero. -/
@[kb "milne2017mf" "Proposition 1.12 (b), pdf p. 19, for the modular curves X(Gamma)"]
theorem residueTheorem_modularCurveX : ResidueTheoremStatement (ModularCurveX Γ) :=
  RS.residueTheoremStatement_of_existsNonconstant (existsNonconstant_modularCurveX Γ)

/-- **Milne, Theorem 1.27 for `j : X(Γ) → ℙ¹`, from the Riemann–Roch theorem on `X(Γ)`** (Riemann–Roch on the
sphere and the nonconstant coordinate of the sphere are proved). -/
@[kb "milne2017mf" "Theorem 1.27 (Riemann-Hurwitz), pdf p. 22, for X(Gamma) -> P^1, from Theorem 1.20 on X(Gamma)"]
theorem riemannHurwitz_modularCurveX (hRR : RiemannRochStatement (ModularCurveX Γ)) :
    RiemannHurwitzStatement (ModularCurveX Γ) (OnePoint ℂ) :=
  RS.riemannHurwitzStatement_of_riemannRoch hRR riemannRoch_sphere ⟨⟨_, RS.isNonconstant_coordinate⟩⟩

/-- **Milne, Theorem 2.22 from the Riemann–Roch theorem on `X(Γ)`**: Milne's proof (Riemann–Hurwitz for
`j : X(Γ) → ℙ¹`, Theorem 1.27, which follows from Riemann–Roch) gives the genus
`g(X(Γ)) = 1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "milne2017mf" "Theorem 2.22, pdf p. 37, from Theorem 1.20 on X(Gamma)"]
theorem genus_modularCurveX_of_riemannRoch (hRR : RiemannRochStatement (ModularCurveX Γ)) :
    (genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 :=
  genus_modularCurveX Γ (riemannHurwitz_modularCurveX Γ hRR)

end ModularFormsKB.Milne.Wave10
