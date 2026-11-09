import ModularFormsKB.Milne.Ch7.ConstantsAlgebra
import ModularFormsKB.Milne.Ch7.CurveEquivalence

/-!
# Geometric irreducibility and the field of constants (Theorem 7.2, last assertion)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 7, Theorem 7.2 (pdf p. 94).

Let $X$ be an integral scheme over a perfect field $k$ with function field $K$. Then $X$ is geometrically irreducible
if and only if $k$ is algebraically closed in $K$ (`geometricallyIrreducible_iff_constants`); in particular the last
field of `CurveFunctionFieldEquivalence` holds over perfect fields, and the corrected Theorem 7.2 is proved
(`curveFunctionFieldEquivalencePerfect`).

For a nonempty affine open $U = \operatorname{Spec} A$ of $X$ and a field $M \supseteq k$, $\operatorname{Spec}(A
\otimes_k M)$ is an open subscheme of $X_M = X \times_k M$ with dense image (the projection $X_M \to X$ is open), so
$X_M$ is irreducible iff $\operatorname{Spec}(A \otimes_k M)$ is (`irreducibleSpace_pullback_iff`). The algebra is in
`ConstantsAlgebra`: $A \otimes_k M \subseteq K \otimes_k M$, $\bar k \otimes_k K$ is a localization of
$\bar k \otimes_k A$, and over a perfect field $\bar k \otimes_k K$ is a domain exactly when $k$ is algebraically closed
in $K$.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

noncomputable section

namespace ModularFormsKB.Milne.GeomConstants

variable {k : Type u} [Field k]

/-- **$X_M$ is irreducible iff $\operatorname{Spec}(A \otimes_k M)$ is**, for a nonempty affine chart
$\operatorname{Spec} A$ of an irreducible $X$. -/
theorem irreducibleSpace_pullback_iff {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k))
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] [Algebra k Γ(X, U)]
    (hfrom : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) (M : Type u) [Field M]
    [Algebra k M] :
    IrreducibleSpace (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k M))) : Scheme.{u}) ↔
      IrreducibleSpace (Spec (CommRingCat.of (Γ(X, U) ⊗[k] M))) := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k M))
  let j₀ := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))) g f g hU.fromSpec (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hfrom]) (by simp)
  let j := (pullbackSpecIso k Γ(X, U) M).inv ≫ j₀
  have hj : IsOpenImmersion j := inferInstance
  have hrange : Set.range j = pullback.fst f g ⁻¹' (U : Set X) := by
    have huniv : Set.range (pullbackSpecIso k Γ(X, U) M).inv = Set.univ :=
      Set.range_eq_univ.mpr fun x ↦ ⟨(pullbackSpecIso k Γ(X, U) M).hom x, by
        rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, huniv, Set.image_univ,
      Scheme.Pullback.range_map, hU.range_fromSpec]
    simp
  have hUd : Dense (U : Set X) := U.isOpen.dense (by obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty U›; exact ⟨x, hx⟩)
  have hdense : Dense (Set.range j) := by
    rw [hrange]
    exact hUd.preimage (pullback.fst f g).isOpenMap
  constructor
  · intro hP
    have hne : (Set.range j).Nonempty := hdense.nonempty
    have hirr : IsIrreducible (Set.range j) :=
      ⟨hne, (IrreducibleSpace.isIrreducible_univ _).isPreirreducible.open_subset
        j.isOpenEmbedding.isOpen_range (Set.subset_univ _)⟩
    have : IrreducibleSpace (Set.range j) := Subtype.irreducibleSpace hirr
    exact (j.isOpenEmbedding.toHomeomorph).irreducibleSpace_iff.mpr this
  · intro hS
    have hirr : IsIrreducible (Set.range j) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image j j.continuous.continuousOn
    have h := hirr.closure
    rw [hdense.closure_eq] at h
    exact (irreducibleSpace_def _).mpr h

/-- **Geometric irreducibility and the field of constants**: an integral scheme $X$ over a perfect field $k$ is
geometrically irreducible iff $k$ is algebraically closed in $k(X)$. -/
theorem geometricallyIrreducible_iff_constants [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) :
    GeometricallyIrreducible f ↔
      letI := (functionFieldAlgebraMap k f).toAlgebra
      fieldOfConstants k X.functionField = ⊥ := by
  letI := overOf k f
  have e : (functionFieldAlgebraMap k f).toAlgebra = Scheme.functionFieldBaseAlgebra k X := by
    rw [functionFieldAlgebraMap_eq]
    rfl
  show _ ↔ @fieldOfConstants k _ X.functionField _ (functionFieldAlgebraMap k f).toAlgebra = ⊥
  rw [e]
  -- an affine chart
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let φ : k →+* Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U le_top).hom
  letI : Algebra k Γ(X, U) := φ.toAlgebra
  have htower : IsScalarTower k Γ(X, U) X.functionField :=
    .of_algebraMap_eq' (Scheme.baseRingToFunctionField_eq_comp_appLE k X U)
  have hfrom : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of k))) hU le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hfrac := functionField_isFractionRing_of_isAffineOpen X U hU
  have hinjA : Function.Injective (algebraMap Γ(X, U) X.functionField) :=
    IsFractionRing.injective Γ(X, U) X.functionField
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro H
    have h1 := H (AlgebraicClosure k)
    rw [irreducibleSpace_pullback_iff f hU hfrom] at h1
    -- `Γ(U) ⊗ k̄` is reduced, hence a domain
    have hredK := isReduced_algebraicClosure_tensor_of_perfectField k X.functionField
    have hredA : IsReduced (AlgebraicClosure k ⊗[k] Γ(X, U)) :=
      isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id k _) (IsScalarTower.toAlgHom k _ _)).toRingHom
        (Module.Flat.lTensor_preserves_injective_linearMap (M := AlgebraicClosure k)
          (IsScalarTower.toAlgHom k Γ(X, U) X.functionField).toLinearMap hinjA)
    have hredA' : IsReduced (Γ(X, U) ⊗[k] AlgebraicClosure k) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k _ _).toRingHom
        (Algebra.TensorProduct.comm k _ _).injective
    have : IsReduced (Spec (CommRingCat.of (Γ(X, U) ⊗[k] AlgebraicClosure k))) :=
      (affine_isReduced_iff _).mpr hredA'
    have : IsIntegral (Spec (CommRingCat.of (Γ(X, U) ⊗[k] AlgebraicClosure k))) :=
      isIntegral_of_irreducibleSpace_of_isReduced _
    have hdom : IsDomain (Γ(X, U) ⊗[k] AlgebraicClosure k) := (affine_isIntegral_iff _).mp this
    have hdom' : IsDomain (AlgebraicClosure k ⊗[k] Γ(X, U)) :=
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) Γ(X, U)).toMulEquiv.isDomain
    have hdomK := Constants.isDomain_tensor_of_isLocalization (B := X.functionField) (nonZeroDivisors Γ(X, U))
      le_rfl hdom'
    exact Constants.algebraicClosure_eq_bot_of_isDomain hdomK
  · intro hL M _ _
    rw [irreducibleSpace_pullback_iff f hU hfrom]
    have h1 : IsDomain (X.functionField ⊗[k] AlgebraicClosure k) :=
      Constants.isDomain_tensor_of_algebraicClosure_eq_bot hL
    have h2 : IsDomain (AlgebraicClosure k ⊗[k] X.functionField) :=
      (Algebra.TensorProduct.comm k (AlgebraicClosure k) X.functionField).toMulEquiv.isDomain
    have h3 : IsDomain (M ⊗[k] X.functionField) := Constants.isDomain_tensor_of_isDomain h2 M
    have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id k M)
        (IsScalarTower.toAlgHom k Γ(X, U) X.functionField)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := M)
        (IsScalarTower.toAlgHom k Γ(X, U) X.functionField).toLinearMap hinjA
    have h4 : IsDomain (M ⊗[k] Γ(X, U)) := hinj.isDomain _
    have h5 : IsDomain (Γ(X, U) ⊗[k] M) := (Algebra.TensorProduct.comm k Γ(X, U) M).toMulEquiv.isDomain
    infer_instance

end ModularFormsKB.Milne.GeomConstants

namespace ModularFormsKB.Milne

variable (k₀ : Type u) [Field k₀]

/-- The last assertion of Theorem 7.2 over a perfect field, unconditionally. -/
theorem geometricallyIrreducibleIffConstants [PerfectField k₀] : GeometricallyIrreducibleIffConstants k₀ :=
  ⟨fun f _ ↦ GeomConstants.geometricallyIrreducible_iff_constants f⟩

/-- **Milne, Theorem 7.2, corrected (perfect $k_0$)**, unconditionally: over a perfect field the function field
functor is an equivalence from complete regular curves to function fields in one variable, and a curve is
geometrically irreducible iff $k_0$ is its field of constants. -/
@[kb "milne2017mf" "Section 7, Theorem 7.2 (pdf p. 94), corrected: k0 perfect"]
theorem curveFunctionFieldEquivalencePerfect [PerfectField k₀] : CurveFunctionFieldEquivalencePerfect k₀ :=
  curveFunctionFieldEquivalencePerfect_of_geometricallyIrreducibleIffConstants k₀
    (geometricallyIrreducibleIffConstants k₀)

end ModularFormsKB.Milne
