import ModularFormsKB.Milne.Ch7.CurveBridge
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# The function field of a Milne variety is geometrically reduced

For an integral Milne variety $U$ over $k$ (finite affine cover by spectra of affine $k$-algebras, which are
geometrically reduced), $\bar k \otimes_k k(U)$ is reduced (`isReduced_tensor_functionField`): $k(U)$ is the fraction
field of $\Gamma(U, W)$ for a nonempty affine chart $W \cong \operatorname{Spec} A$, $\Gamma(U, W) \cong A$ as
$k$-algebras, and a localization of a reduced ring is reduced (`isReduced_tensor_of_isLocalization`).
-/

universe u

open AlgebraicGeometry CategoryTheory TensorProduct

noncomputable section

namespace ModularFormsKB.Milne.Completion

variable {k : Type u} [Field k]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- $\bar k \otimes_k M^{-1}A$ is reduced when $\bar k \otimes_k A$ is. -/
theorem isReduced_tensor_of_isLocalization {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B] (M : Submonoid A) [IsLocalization M B]
    (h : IsReduced (AlgebraicClosure k ⊗[k] A)) : IsReduced (AlgebraicClosure k ⊗[k] B) := by
  let φ : AlgebraicClosure k ⊗[k] A →ₐ[k] AlgebraicClosure k ⊗[k] B :=
    Algebra.TensorProduct.map (AlgHom.id k _) (IsScalarTower.toAlgHom k A B)
  let _ : Algebra (AlgebraicClosure k ⊗[k] A) (AlgebraicClosure k ⊗[k] B) := φ.toRingHom.toAlgebra
  have : IsScalarTower (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A) (AlgebraicClosure k ⊗[k] B) :=
    .of_algebraMap_eq' (by ext c; simp [φ, RingHom.algebraMap_toAlgebra])
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k (AlgebraicClosure k) M B
    (by ext a; simp [φ, RingHom.algebraMap_toAlgebra])
  exact @isReduced_localizationPreserves _ _ _ (AlgebraicClosure k ⊗[k] B) _ _ hloc h

/-- **The function field of an integral Milne variety is geometrically reduced.** -/
theorem isReduced_tensor_functionField {U : Scheme.{u}} [IsIntegral U] (f : U ⟶ Spec (CommRingCat.of k))
    (hU : IsVariety k f) :
    letI := overOf k f
    IsReduced (AlgebraicClosure k ⊗[k] U.functionField) := by
  letI := overOf k f
  obtain ⟨⟨n, V, hV, hVaff⟩, -⟩ := hU
  obtain ⟨x⟩ : Nonempty U := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, x ∈ V i := by
    have hx : x ∈ (⨆ i, V i : U.Opens) := by rw [hV]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hx
  obtain ⟨A, _, _, hA, e, he⟩ := hVaff i
  generalize V i = W at e he hi
  have : IsAffine W.toScheme := IsAffine.of_isIso e.hom
  have hW : IsAffineOpen W := this
  have : Nonempty W := ⟨⟨x, hi⟩⟩
  let φ : k →+* Γ(U, W) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U ↘ Spec (CommRingCat.of k)).appLE ⊤ W le_top).hom
  let _ : Algebra k Γ(U, W) := φ.toAlgebra
  have htower : IsScalarTower k Γ(U, W) U.functionField :=
    .of_algebraMap_eq' (Scheme.baseRingToFunctionField_eq_comp_appLE k U W)
  have hfrac := functionField_isFractionRing_of_isAffineOpen U W hW
  let g : Spec (CommRingCat.of A) ⟶ U := e.inv ≫ W.ι
  have hrange : Set.range g = Set.range hW.fromSpec := by
    rw [hW.range_fromSpec, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr fun y ↦ ⟨e.hom y, by rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl⟩,
      Set.image_univ, Scheme.Opens.range_ι]
  let ι0 := IsOpenImmersion.isoOfRangeEq g hW.fromSpec hrange
  let ψ : Γ(U, W) ⟶ CommRingCat.of A := Spec.preimage ι0.hom
  let ψ' : CommRingCat.of A ⟶ Γ(U, W) := Spec.preimage ι0.inv
  have hψψ' : ψ ≫ ψ' = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ι0.inv_hom_id, Spec.map_id])
  have h1 : hW.fromSpec ≫ f = Spec.map (CommRingCat.ofHom φ) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of k))) hW le_top, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hk : ψ.hom.comp φ = algebraMap k A := by
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap k A)) = Spec.map (CommRingCat.ofHom φ ≫ ψ) := by
      rw [Spec.map_comp, Spec.map_preimage, ← h1]
      change specStructure k A = _
      rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
      change specStructure k A = (e.inv ≫ W.ι) ≫ f
      rw [Category.assoc, ← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h2)).symm
  let ψa : Γ(U, W) →ₐ[k] A := { ψ.hom with commutes' := fun c ↦ congrFun (congrArg DFunLike.coe hk) c }
  have hinj : Function.Injective ψa := by
    intro a b hab
    have := congrArg ψ'.hom hab
    change (ψ ≫ ψ').hom a = (ψ ≫ ψ').hom b at this
    rwa [hψψ'] at this
  have : Algebra.IsGeometricallyReduced k A := (Algebra.isGeometricallyReduced_field_iff k A).2 hA.2
  have := Algebra.IsGeometricallyReduced.of_injective ψa hinj
  exact isReduced_tensor_of_isLocalization (A := Γ(U, W)) (nonZeroDivisors _)
    ((Algebra.isGeometricallyReduced_field_iff k _).1 this)

end ModularFormsKB.Milne.Completion
