import ModularFormsKB.Milne.Ch7.Curves
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.Smooth.Hypersurface

/-!
# Milne, Example 7.4: the affine plane curve $F = 0$

Let $F \in k_0[X, Y]$ be absolutely irreducible and $A = k_0[X, Y]/(F)$.
- $A$ is an affine $k_0$-algebra (`isAffineAlgebra_planeCurve`): it is finitely generated, and
  $\bar k \otimes_{k_0} A \cong \bar k[X, Y]/(F)$ (Mathlib's `Algebra.TensorProduct.tensorQuotientEquiv` and
  `MvPolynomial.algebraTensorAlgEquiv`) is a domain since $F$ is irreducible in the factorial ring $\bar k[X, Y]$.
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ModularFormsKB.Milne

variable (k₀ : Type u) [Field k₀]

/-- $\bar k \otimes_{k_0} k_0[X, Y]/(F) \cong \bar k[X, Y]/(F)$. -/
def planeCurveBaseChangeEquiv (F : MvPolynomial (Fin 2) k₀) :
    TensorProduct k₀ (AlgebraicClosure k₀) (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F}) ≃+*
      MvPolynomial (Fin 2) (AlgebraicClosure k₀) ⧸
        Ideal.span {MvPolynomial.map (algebraMap k₀ (AlgebraicClosure k₀)) F} := by
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k₀) (AlgebraicClosure k₀)
    (MvPolynomial (Fin 2) k₀) (AlgebraicClosure k₀) (Ideal.span {F})).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ (MvPolynomial.algebraTensorAlgEquiv k₀ (AlgebraicClosure k₀)).toRingEquiv ?_)
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  congr 1
  simp

/-- **Milne, Example 7.4, first assertion**: $k_0[X, Y]/(F)$ is an affine $k_0$-algebra when $F$ is absolutely
irreducible. -/
theorem isAffineAlgebra_planeCurve (F : MvPolynomial (Fin 2) k₀)
    (hF : Irreducible (MvPolynomial.map (algebraMap k₀ (AlgebraicClosure k₀)) F)) :
    IsAffineAlgebra k₀ (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F}) := by
  refine ⟨inferInstance, ?_⟩
  have hprime : (Ideal.span {MvPolynomial.map (algebraMap k₀ (AlgebraicClosure k₀)) F}).IsPrime :=
    (Ideal.span_singleton_prime hF.ne_zero).2 hF.prime
  have : IsDomain (MvPolynomial (Fin 2) (AlgebraicClosure k₀) ⧸
      Ideal.span {MvPolynomial.map (algebraMap k₀ (AlgebraicClosure k₀)) F}) :=
    Ideal.Quotient.isDomain _
  exact isReduced_of_injective (planeCurveBaseChangeEquiv k₀ F).toRingHom
    (planeCurveBaseChangeEquiv k₀ F).injective

theorem mem_nonsingularLocus (F : MvPolynomial (Fin 2) k₀)
    (x : Spec (CommRingCat.of (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F}))) :
    x ∈ nonsingularLocus k₀ F ↔
      Ideal.Quotient.mk _ (MvPolynomial.pderiv 0 F) ∉ x.asIdeal ∨
        Ideal.Quotient.mk _ (MvPolynomial.pderiv 1 F) ∉ x.asIdeal := by
  change ¬ (({Ideal.Quotient.mk _ (MvPolynomial.pderiv 0 F), Ideal.Quotient.mk _ (MvPolynomial.pderiv 1 F)} :
    Set (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F})) ⊆ x.asIdeal) ↔ _
  rw [Set.insert_subset_iff, Set.singleton_subset_iff, not_and_or]
  rfl

/-- **Milne, Example 7.4, second assertion**: the nonsingular locus $C^{\mathrm{ns}}$ of $F = 0$ is smooth of relative
dimension one over $k_0$ (the Jacobian criterion). -/
theorem smoothOfRelativeDimension_nonsingularLocus (F : MvPolynomial (Fin 2) k₀) :
    SmoothOfRelativeDimension 1
      ((nonsingularLocus k₀ F).ι ≫ specStructure k₀ (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F})) := by
  set A := MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F} with hA
  set U := nonsingularLocus k₀ F with hU
  let f : Fin 2 → A := fun j ↦ Ideal.Quotient.mk _ (MvPolynomial.pderiv j F)
  let D : Fin 2 → (Spec (CommRingCat.of A)).Opens := fun j ↦ PrimeSpectrum.basicOpen (f j)
  have hDU : ∀ j, D j ≤ U := by
    intro j x hx
    show x ∈ nonsingularLocus k₀ F
    rw [mem_nonsingularLocus]
    have hx' : f j ∉ x.asIdeal := hx
    fin_cases j
    · exact Or.inl hx'
    · exact Or.inr hx'
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun j ↦ U.ι ⁻¹ᵁ D j) ?_ fun j ↦ ?_
  · rw [eq_top_iff]
    intro x _
    have hx : x.1 ∈ nonsingularLocus k₀ F := x.2
    rw [mem_nonsingularLocus] at hx
    simp only [TopologicalSpace.Opens.mem_iSup, Scheme.Hom.mem_preimage]
    rcases hx with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · have e1 : (U.ι ⁻¹ᵁ D j).ι ≫ U.ι = (Scheme.Opens.isoOfLE (hDU j)).hom ≫ (D j).ι :=
      (Scheme.Opens.isoOfLE_hom_ι (hDU j)).symm
    have e2 : (D j).ι = (basicOpenIsoSpecAway (R := CommRingCat.of A) (f j)).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (f j)))) :=
      (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) (f j)).symm
    have e3 : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (f j)))) ≫
        specStructure k₀ A = Spec.map (CommRingCat.ofHom (algebraMap k₀ (Localization.Away (f j)))) := by
      rw [specStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [← Category.assoc, e1, e2, Category.assoc, Category.assoc, e3]
    refine IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1)
      (IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 1) ?_ _) _
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    have h := MvPolynomial.isStandardSmoothOfRelativeDimension_localizationAway_pderiv F j
    rw [Fintype.card_fin] at h
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).2 h

end ModularFormsKB.Milne
