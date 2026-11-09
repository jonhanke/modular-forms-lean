import ModularFormsKB.Milne.Ch12.CMDefs
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
import ModularFormsKB.Citation
/-!
# Milne, Section 12: endomorphism rings under a change of variables

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 123. Milne
works with isomorphism classes of elliptic curves; here an isomorphism is a change of variables `C • W₁ = W₂`, and
conjugation by its isogeny (Tau Ceti `variableChangeIsogeny`) identifies the endomorphism rings. Used in the proofs
of Proposition 12.6 and Theorem 12.8.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields
open scoped WeierstrassCurve

namespace ModularFormsKB.Milne

section VariableChange

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
  {C : WeierstrassCurve.VariableChange F}

/-- Conjugation by the isomorphism of a change of variables $C$ with $C \cdot W_1 = W_2$ is a ring isomorphism
$\mathrm{End}(W_1) \to \mathrm{End}(W_2)$. -/
noncomputable def endRingEquivOfVariableChange (h : C • W₁ = W₂) :
    Hom W₁.toAffine W₁.toAffine ≃+* Hom W₂.toAffine W₂.toAffine :=
  let h' : C⁻¹ • W₂ = W₁ := by rw [← h, inv_smul_smul]
  let φ : Hom W₁.toAffine W₂.toAffine := Hom.ofIsogeny (variableChangeIsogeny C h)
  let ψ : Hom W₂.toAffine W₁.toAffine := Hom.ofIsogeny (variableChangeIsogeny C⁻¹ h')
  have hψφ : ψ.comp φ = Hom.id W₁.toAffine := by
    simp only [φ, ψ, Hom.ofIsogeny_comp_ofIsogeny, variableChangeIsogeny_inv_comp C h h', Hom.id]
  have hφψ : φ.comp ψ = Hom.id W₂.toAffine := by
    have := variableChangeIsogeny_inv_comp (C := C⁻¹) h' (by rw [inv_inv]; exact h)
    simp only [φ, ψ, Hom.ofIsogeny_comp_ofIsogeny, inv_inv] at this ⊢
    rw [this]; rfl
  { toFun := fun f => φ.comp (f.comp ψ)
    invFun := fun g => ψ.comp (g.comp φ)
    left_inv := fun f => by
      simp only [← Hom.comp_assoc, hψφ, Hom.id_comp]
      rw [Hom.comp_assoc, hψφ, Hom.comp_id]
    right_inv := fun g => by
      simp only [← Hom.comp_assoc, hφψ, Hom.id_comp]
      rw [Hom.comp_assoc, hφψ, Hom.comp_id]
    map_add' := fun f g => by
      rw [Hom.add_comp, Hom.comp_add]
    map_mul' := fun f g => by
      simp only [Hom.mul_def]
      calc φ.comp ((f.comp g).comp ψ)
          = φ.comp ((f.comp ((Hom.id _).comp g)).comp ψ) := by rw [Hom.id_comp]
        _ = φ.comp ((f.comp ((ψ.comp φ).comp g)).comp ψ) := by rw [hψφ]
        _ = (φ.comp (f.comp ψ)).comp (φ.comp (g.comp ψ)) := by
          simp only [Hom.comp_assoc] }

/-- Complex multiplication by an order is preserved by a change of variables. -/
@[kb "milne2017mf" "Section 12, Ell(R) consists of isomorphism classes (pdf p. 123)"]
theorem hasCMBy_of_variableChange (h : C • W₁ = W₂) {K : Type*} [Field K] [NumberField K]
    {O : NumberFieldOrder K} (hW : HasCMBy W₁ O) : HasCMBy W₂ O := by
  obtain ⟨h1, h2, ⟨e⟩⟩ := hW
  exact ⟨h1, h2, ⟨e.trans (endRingEquivOfVariableChange h)⟩⟩

/-- Having complex multiplication is preserved by a change of variables. -/
theorem hasComplexMultiplication_of_variableChange (h : C • W₁ = W₂)
    (hW : HasComplexMultiplication W₁) : HasComplexMultiplication W₂ := by
  obtain ⟨f, hf⟩ := hW
  refine ⟨endRingEquivOfVariableChange h f, fun n hn => hf n ?_⟩
  apply (endRingEquivOfVariableChange h).injective
  rw [hn, map_zsmul, map_one]

end VariableChange

end ModularFormsKB.Milne
