import ModularFormsKB.Milne.Ch2.Automorphisms
import ModularFormsKB.Milne.Ch2.DiscreteGroups
import ModularFormsKB.Milne.Ch2.ModularGroup
import ModularFormsKB.Milne.Citations

/-!
# Milne wave 5: full statements of items proved in parts

Earlier waves proved each part of the following items of Milne's notes under separate citations (`Proposition 2.1
(a)`, `(b)`, …). Here each item is stated in full, as one theorem whose statement is the conjunction of its parts, so
that the book map records the item, not only its parts, as proved. No new mathematics: every conjunct is the earlier
theorem named in the docstring.
-/

open Matrix MatrixGroups UpperHalfPlane TauCeti

namespace ModularFormsKB.Milne.Wave5

/-- **Milne, Proposition 2.1** (pdf p. 25), all four parts: (a) `SL₂(ℝ)` acts transitively on `ℍ`
(`exists_SL2R_smul_eq`); (b) the action induces `SL₂(ℝ)/{±I} ≅ Aut(ℍ)` (`exists_mulEquiv_autUpperHalfPlane`,
with the center `{±I}`: `mem_center_SL2R_iff`); (c) the stabilizer of `i` is `SO₂(ℝ)` (`stabilizer_I_eq_SO2R`);
(d) `α SO₂(ℝ) ↦ α(i)` is a homeomorphism `SL₂(ℝ)/SO₂(ℝ) ≅ ℍ` (`exists_homeomorph_quotient_SO2R`). -/
@[kb "milne2017mf" "Proposition 2.1, pdf p. 25"]
theorem proposition_2_1 :
    (∀ z w : ℍ, ∃ g : SL(2, ℝ), g • z = w) ∧
    (∀ g : SL(2, ℝ), g ∈ Subgroup.center SL(2, ℝ) ↔ g = 1 ∨ g = -1) ∧
    (∃ φ : SL(2, ℝ) ⧸ Subgroup.center SL(2, ℝ) ≃* autUpperHalfPlane,
      ∀ (g : SL(2, ℝ)) (z : ℍ), (φ (g : SL(2, ℝ) ⧸ Subgroup.center SL(2, ℝ)) : Equiv.Perm ℍ) z = g • z) ∧
    MulAction.stabilizer SL(2, ℝ) UpperHalfPlane.I = SO2R ∧
    (∃ e : SL(2, ℝ) ⧸ SO2R ≃ₜ ℍ, ∀ g : SL(2, ℝ), e (g : SL(2, ℝ) ⧸ SO2R) = g • UpperHalfPlane.I) :=
  ⟨exists_SL2R_smul_eq, mem_center_SL2R_iff, exists_mulEquiv_autUpperHalfPlane, stabilizer_I_eq_SO2R,
    exists_homeomorph_quotient_SO2R⟩

/-- **Milne, Exercise 2.3** (pdf p. 26), all three parts: (a) `SU(1,1)` consists of the matrices
`[[u, v], [v̄, ū]]` with `|u|² - |v|² = 1` (`mem_SU11_iff`); (b) `SU(1,1)/{±I} ≅ Aut(𝔻)` acting by Möbius maps
(`exists_mulEquiv_unitDiscAut`, center `mem_center_SU11_iff`); (c) under the Cayley map the rotation by `θ` becomes
the Möbius map of `diag(e^{iθ}, e^{-iθ})` (`cayley_rotation_smul`). -/
@[kb "milne2017mf" "Exercise 2.3, pdf p. 26"]
theorem exercise_2_3 :
    (∀ α : SL(2, ℂ), α ∈ SU11 ↔ ∃ u v : ℂ, Complex.normSq u - Complex.normSq v = 1 ∧
      (α : Matrix (Fin 2) (Fin 2) ℂ) = !![u, v; (starRingEnd ℂ) v, (starRingEnd ℂ) u]) ∧
    (∀ α : SU11, α ∈ Subgroup.center SU11 ↔ (α : SL(2, ℂ)) = 1 ∨ (α : SL(2, ℂ)) = -1) ∧
    (∃ φ : SU11 ⧸ Subgroup.center SU11 ≃* TauCeti.unitDiscAut,
      ∀ (α : SU11) (z : Complex.UnitDisc),
        ((φ (α : SU11 ⧸ Subgroup.center SU11) : Equiv.Perm Complex.UnitDisc) z : ℂ) =
          ((α : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 0 1) /
            ((α : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * z + (α : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) ∧
    (∀ (θ : ℝ) (z : ℍ),
      (((Matrix.SpecialLinearGroup.rotation θ • z : ℍ) : ℂ) - Complex.I) /
          (((Matrix.SpecialLinearGroup.rotation θ • z : ℍ) : ℂ) + Complex.I) =
        (Complex.exp (θ * Complex.I) * (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) + 0) /
          (0 * (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) + Complex.exp (-(θ * Complex.I)))) :=
  ⟨mem_SU11_iff, mem_center_SU11_iff, exists_mulEquiv_unitDiscAut, cayley_rotation_smul⟩

/-- **Milne, Exercise 2.8** (pdf p. 29), all three parts: (a) commensurability is an equivalence relation; (b) a
subgroup commensurable with a discrete subgroup is discrete (`commensurable_equivalence_and_discrete`); (c) if `Γ`
and `Γ'` are commensurable and `Γ\ℍ` is compact, so is `Γ'\ℍ` (`compactSpace_quotient_of_commensurable`). -/
@[kb "milne2017mf" "Exercise 2.8, pdf p. 29"]
theorem exercise_2_8 :
    Equivalence (@Subgroup.Commensurable SL(2, ℝ) _) ∧
    (∀ {Γ Γ' : Subgroup SL(2, ℝ)}, Subgroup.Commensurable Γ Γ' → (DiscreteTopology Γ ↔ DiscreteTopology Γ')) ∧
    (∀ {Γ Γ' : Subgroup SL(2, ℝ)}, Γ.Commensurable Γ' → CompactSpace (MulAction.orbitRel.Quotient Γ ℍ) →
      CompactSpace (MulAction.orbitRel.Quotient Γ' ℍ)) :=
  ⟨commensurable_equivalence_and_discrete.1, commensurable_equivalence_and_discrete.2,
    fun h _ ↦ compactSpace_quotient_of_commensurable h⟩

/-- **Milne, Aside 2.15** (pdf p. 34), all its claims: every positive definite form is equivalent to a reduced one
(`exists_slZSmul_isReducedForm`); two equivalent reduced forms are equal (`eq_of_slZSmul_eq`); finitely many classes
of integral forms of a given nonzero discriminant (`finite_classes_of_discrim`); the minimum of a form on nonzero
integral vectors is at most `√(disc/3)` (`exists_eval_le_sqrt_disc`), with equality exactly for multiples of
`x² + xy + y²`, the hexagonal lattice (`min_eq_sqrt_disc_iff`). -/
@[kb "milne2017mf" "Aside 2.15, pdf p. 34"]
theorem aside_2_15 :
    (∀ {f : BinaryQuadraticForm ℝ}, IsPosDefForm f → ∃ γ : SL(2, ℤ), IsReducedForm (slZSmul γ f)) ∧
    (∀ {f g : BinaryQuadraticForm ℝ}, IsPosDefForm f → IsReducedForm f → IsReducedForm g →
      ∀ {γ : SL(2, ℤ)}, slZSmul γ f = g → f = g) ∧
    (∀ {D : ℤ}, D ≠ 0 → {Q : MulAction.orbitRel.Quotient SL(2, ℤ) (BinaryQuadraticForm ℤ) |
      ∃ f : BinaryQuadraticForm ℤ, f.discrim = D ∧
        (Quotient.mk _ f : MulAction.orbitRel.Quotient _ _) = Q}.Finite) ∧
    (∀ {f : BinaryQuadraticForm ℝ}, IsPosDefForm f →
      ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ f.eval x y ≤ Real.sqrt ((4 * f.a * f.c - f.b ^ 2) / 3)) ∧
    (∀ {f : BinaryQuadraticForm ℝ}, IsPosDefForm f →
      ((∀ x y : ℤ, (x, y) ≠ (0, 0) → Real.sqrt ((4 * f.a * f.c - f.b ^ 2) / 3) ≤ f.eval x y) ↔
        ∃ (t : ℝ) (γ : SL(2, ℤ)), 0 < t ∧ slZSmul γ f = ⟨t, t, t⟩)) :=
  ⟨exists_slZSmul_isReducedForm, eq_of_slZSmul_eq, finite_classes_of_discrim, exists_eval_le_sqrt_disc,
    min_eq_sqrt_disc_iff⟩

end ModularFormsKB.Milne.Wave5
