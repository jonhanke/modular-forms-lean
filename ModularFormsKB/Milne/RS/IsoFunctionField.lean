import ModularFormsKB.Milne.Ch7.Curves

/-!
# The automorphism of the function field induced by an automorphism of an integral scheme

An automorphism `i` of an integral scheme `C` over `Spec k₀` induces a `k₀`-linear ring endomorphism `ψ` of the
function field `k₀(C)` (the stalk map at the generic point, `ModularFormsKB.Milne.functionFieldMap`), which carries
the image of the local ring at `i c` into the image of the local ring at `c`. This is used for the counterexample to
the named statement `ModularFormsKB.Milne.RiemannSurfaceAlgebraicStructure` (Milne, Theorem 7.5).
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace ModularFormsKB.Milne.RS

variable {k₀ : Type u} [Field k₀]

/-- An automorphism `i` of an integral scheme `C` over `k₀` induces a `k₀`-linear endomorphism `ψ` of `k₀(C)` with
`ψ(𝒪_{C, i c}) ⊆ 𝒪_{C, c}` inside `k₀(C)`. -/
theorem exists_functionField_hom_of_iso {C : Scheme.{u}} [IsIntegral C] (f : C ⟶ Spec (CommRingCat.of k₀))
    (i : C ≅ C) (hi : i.hom ≫ f = f) :
    ∃ ψ : C.functionField →+* C.functionField,
      (∀ a : k₀, ψ (functionFieldAlgebraMap k₀ f a) = functionFieldAlgebraMap k₀ f a) ∧
      ∀ (c : C) (φ : C.functionField), (∃ s, (stalkToFunctionField (i.hom c)).hom s = φ) →
        ∃ s, (stalkToFunctionField c).hom s = ψ φ := by
  have : IsDominant i.hom := inferInstance
  refine ⟨(functionFieldMap i.hom).hom, fun a ↦ ?_, fun c φ ⟨s, hs⟩ ↦ ⟨i.hom.stalkMap c s, ?_⟩⟩
  · have : Nonempty (⊤ : C.Opens) := ⟨⟨genericPoint C, trivial⟩⟩
    simp only [functionFieldAlgebraMap, functionFieldMap]
    conv_rhs => rw [← hi]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [Scheme.germToFunctionField]
    simp only [← CommRingCat.comp_apply, Category.assoc]
    congr 2
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
    rfl
  · subst hs
    simp only [stalkToFunctionField, functionFieldMap, ← CommRingCat.comp_apply]
    rw [TopCat.Presheaf.stalkSpecializes_comp_assoc, Scheme.Hom.stalkSpecializes_stalkMap]

end ModularFormsKB.Milne.RS
