import ModularFormsKB.Milne.Ch7.CurveBridge
import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Regular
import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Curve
import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.FiniteChart

/-!
# The two-chart model of a function field is a complete regular curve in Milne's sense

Let $F$ be a function field in one variable over $k$ with $\bar k \otimes_k F$ reduced, and $x \in F$ transcendental.
Tau Ceti's two-chart model $M$ of $F$ (the normalization of $\mathbb P^1_k$ in $F$, glued from
$\operatorname{Spec} \mathcal O_x$ and $\operatorname{Spec} \mathcal O_{x^{-1}}$) is a complete regular curve in
Milne's sense (`isCompleteRegularCurve_twoChartModel`):
- the charts are affine varieties: $\mathcal O_x$ is finite over $k[x]$ (Tau Ceti's `polynomialChartMap_finite`),
  and $\bar k \otimes \mathcal O_x \subseteq \bar k \otimes F$ is reduced (`isAffineAlgebra_holomorphyRing`);
- $M$ is proper (separated, universally closed), of dimension one, with regular local rings.
-/

universe u

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.twoChartModel

noncomputable section

namespace ModularFormsKB.Milne.Completion

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]

/-- The holomorphy ring $\mathcal O_x$ is a finitely generated $k$-algebra. -/
theorem finiteType_holomorphyRing (hF : IsFunctionField k F) {x : F} (hxt : Transcendental k x) :
    Algebra.FiniteType k (holomorphyRing {P : Place k F | x ∈ P.integers}) := by
  have h1 : (algebraMap k (holomorphyRing {P : Place k F | x ∈ P.integers})).FiniteType := by
    have hc : algebraMap k (holomorphyRing {P : Place k F | x ∈ P.integers}) =
        (polynomialChartMap (k := k) x).toRingHom.comp (algebraMap k (Polynomial k)) := by
      ext c
      simp [polynomialChartMap_C]
    rw [hc]
    exact (polynomialChartMap_finite hF hxt).finiteType.comp
      (RingHom.finiteType_algebraMap.2 inferInstance)
  exact RingHom.finiteType_algebraMap.1 h1

/-- $\bar k \otimes_k A$ is reduced for a subalgebra $A \subseteq F$ when $\bar k \otimes_k F$ is. -/
theorem isReduced_tensor_subalgebra (A : Subalgebra k F)
    (hred : IsReduced (TensorProduct k (AlgebraicClosure k) F)) :
    IsReduced (TensorProduct k (AlgebraicClosure k) A) := by
  let φ := Algebra.TensorProduct.map (AlgHom.id k (AlgebraicClosure k)) A.val
  have hinj : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := AlgebraicClosure k) A.val.toLinearMap
      Subtype.val_injective
  exact isReduced_of_injective φ.toRingHom hinj

/-- The chart rings of the two-chart model are affine $k$-algebras. -/
theorem isAffineAlgebra_holomorphyRing (hF : IsFunctionField k F) {x : F} (hxt : Transcendental k x)
    (hred : IsReduced (TensorProduct k (AlgebraicClosure k) F)) :
    IsAffineAlgebra k (holomorphyRing {P : Place k F | x ∈ P.integers}) :=
  ⟨finiteType_holomorphyRing hF hxt, isReduced_tensor_subalgebra _ hred⟩

/-- A chart $j : \operatorname{Spec} A \to M$ (an open immersion) with $j \circ (M \to \operatorname{Spec} k)$ the
structure map of an affine $k$-algebra $A$ is a Milne affine variety. -/
theorem isAffineVariety_opensRange {M : Scheme.{u}} (f : M ⟶ Spec (CommRingCat.of k)) {A : Type u} [CommRing A]
    [Algebra k A] (hA : IsAffineAlgebra k A) (j : Spec (CommRingCat.of A) ⟶ M) [IsOpenImmersion j]
    (hj : j ≫ f = specStructure k A) : IsAffineVariety k (j.opensRange.ι ≫ f) :=
  ⟨A, inferInstance, inferInstance, hA, j.isoOpensRange.symm, by
    rw [Iso.symm_hom, ← hj, ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]⟩

/-- **The two-chart model is a complete regular curve in Milne's sense.** -/
theorem isCompleteRegularCurve_twoChartModel (hF : IsFunctionField k F) {x : F} (hxt : Transcendental k x)
    (hred : IsReduced (TensorProduct k (AlgebraicClosure k) F)) :
    IsCompleteRegularCurve k (twoChartModel hF hxt.ne_zero ↘ Spec (CommRingCat.of k)) := by
  have hP := isProper (hF := hF) (hx := hxt.ne_zero) hxt
  have hxt' : Transcendental k x⁻¹ := fun h ↦ hxt (IsAlgebraic.inv_iff.mp h)
  refine ⟨⟨⟨⟨2, ![(ιFinite hF hxt.ne_zero).opensRange, (ιInfinity hF hxt.ne_zero).opensRange], ?_, ?_⟩,
    inferInstance⟩, ?_⟩, ?_, (show UniversallyClosed _ from inferInstance)⟩
  · apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top,
      ← range_ιFinite_union_range_ιInfinity hF hxt.ne_zero]
    ext p
    simp [Fin.exists_fin_two]
  · intro i
    fin_cases i
    · exact isAffineVariety_opensRange _ (isAffineAlgebra_holomorphyRing hF hxt hred) _
        (ιFinite_over hF hxt.ne_zero)
    · exact isAffineVariety_opensRange _ (isAffineAlgebra_holomorphyRing hF hxt' hred) _
        (ιInfinity_over hF hxt.ne_zero)
  · have h1 := TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField k
      (X := twoChartModel hF hxt.ne_zero)
    rw [TauCeti.AlgebraicGeometry.twoChartModel.topologicalKrullDim_eq_one hxt] at h1
    have h2 : (Algebra.trdeg k (twoChartModel hF hxt.ne_zero).functionField).toNat = 1 := by
      exact_mod_cast h1.symm
    simp only [dimension]
    rw [functionFieldAlgebraMap_eq]
    exact Cardinal.toNat_eq_one.1 h2
  · intro p _
    exact isRegularLocalRing_stalk hxt p

end ModularFormsKB.Milne.Completion
