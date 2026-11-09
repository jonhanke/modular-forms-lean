import ModularFormsKB.Milne.Ch7.Completion
import ModularFormsKB.Milne.Ch7.PlaneCurve
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Milne, Example 7.4: the nonsingular locus of an absolutely irreducible plane curve

`ModularFormsKB.Milne.planeCurveNonsingularLocus : PlaneCurveNonsingularLocus k₀`. The first two assertions are
`isAffineAlgebra_planeCurve` and `smoothOfRelativeDimension_nonsingularLocus`. For the third: $F$ is irreducible over
$k_0$ (units of $k[X, Y]$ are constants), so $A = k_0[X,Y]/(F)$ is a domain and $C^{\mathrm{ns}}$, if nonempty, is an
integral scheme; it is a Milne regular curve (covered by the affine varieties $D(\partial F/\partial X_j) \cong
\operatorname{Spec} A[(\partial F/\partial X_j)^{-1}]$, of dimension one and regular because smooth of relative
dimension one), so Corollary 7.3 (`regularCurveCompletion`) embeds it into a complete regular curve. If $C^{\mathrm{ns}}$
is empty, the empty open immersion into the projective line (Tau Ceti's two-chart model of $k_0(t)$) works.
-/

universe u

open AlgebraicGeometry CategoryTheory TensorProduct TauCeti TauCeti.AlgebraicGeometry

noncomputable section

namespace ModularFormsKB.Milne

variable (k₀ : Type u) [Field k₀]

/-- A polynomial over $k_0$ that becomes a unit over an extension field is a unit. -/
theorem isUnit_of_isUnit_mvPolynomial_map {σ : Type*} {L : Type*} [Field L] (φ : k₀ →+* L)
    {p : MvPolynomial σ k₀} (h : IsUnit (_root_.MvPolynomial.map φ p)) : IsUnit p := by
  classical
  obtain ⟨r, hr, hp⟩ := _root_.MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 h
  have hpc : p = _root_.MvPolynomial.C (p.coeff 0) := by
    ext m
    by_cases hm : m = 0
    · simp [hm]
    · have := congrArg (fun q : _root_.MvPolynomial σ L ↦ q.coeff m) hp
      rw [_root_.MvPolynomial.coeff_map, _root_.MvPolynomial.coeff_C] at this
      rw [_root_.MvPolynomial.coeff_C]
      simp only [Ne.symm hm, ↓reduceIte] at this ⊢
      exact φ.injective (by rw [this, map_zero])
  have h0 : p.coeff 0 ≠ 0 := by
    intro h0
    rw [hpc, h0, map_zero, map_zero] at hp
    exact hr.ne_zero (_root_.MvPolynomial.C_injective σ L (hp.symm.trans (map_zero _).symm))
  rw [hpc]
  exact (Ne.isUnit h0).map _root_.MvPolynomial.C

instance isLocalHom_mvPolynomial_map {σ : Type*} {L : Type*} [Field L] (φ : k₀ →+* L) :
    IsLocalHom (_root_.MvPolynomial.map (σ := σ) φ) :=
  ⟨fun _ h ↦ isUnit_of_isUnit_mvPolynomial_map k₀ φ h⟩

/-- The projective line: a complete regular curve over $k_0$. -/
theorem exists_completeRegularCurve : ∃ (C : Scheme.{u}) (_ : IsIntegral C) (g : C ⟶ Spec (CommRingCat.of k₀)),
    IsCompleteRegularCurve k₀ g := by
  have hred : IsReduced (AlgebraicClosure k₀ ⊗[k₀] RatFunc k₀) := by
    refine Completion.isReduced_tensor_of_isLocalization (A := Polynomial k₀) (nonZeroDivisors _) ?_
    exact isReduced_of_injective (polyEquivTensor k₀ (AlgebraicClosure k₀)).symm.toRingHom
      (polyEquivTensor k₀ (AlgebraicClosure k₀)).symm.injective
  exact ⟨_, inferInstance, _, Completion.isCompleteRegularCurve_twoChartModel (IsFunctionField.ratFunc k₀)
    (RatFunc.transcendental_X) hred⟩

/-- $A[(\partial F/\partial X_j)^{-1}]$ is an affine $k_0$-algebra. -/
theorem isAffineAlgebra_away (F : MvPolynomial (Fin 2) k₀)
    (hF : Irreducible (MvPolynomial.map (algebraMap k₀ (AlgebraicClosure k₀)) F))
    (a : MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F}) : IsAffineAlgebra k₀ (Localization.Away a) := by
  have hA := isAffineAlgebra_planeCurve k₀ F hF
  refine ⟨?_, Completion.isReduced_tensor_of_isLocalization (A := MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F})
    (Submonoid.powers a) hA.2⟩
  have h1 : (algebraMap (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F}) (Localization.Away a)).FiniteType :=
    RingHom.finiteType_holdsForLocalizationAway _ a
  have h2 : (algebraMap k₀ (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F})).FiniteType :=
    RingHom.finiteType_algebraMap.2 hA.1
  rw [← RingHom.finiteType_algebraMap, IsScalarTower.algebraMap_eq k₀ (MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F})]
  exact h1.comp h2

/-- **Milne, Example 7.4, unconditionally.** -/
@[kb "milne2017mf" "Section 7, Example 7.4 (pdf p. 94)"]
theorem planeCurveNonsingularLocus : PlaneCurveNonsingularLocus k₀ := by
  refine ⟨fun F hF ↦ ⟨isAffineAlgebra_planeCurve k₀ F hF, smoothOfRelativeDimension_nonsingularLocus k₀ F, ?_⟩⟩
  set A := MvPolynomial (Fin 2) k₀ ⧸ Ideal.span {F} with hAdef
  set U := nonsingularLocus k₀ F with hU
  rcases isEmpty_or_nonempty U.toScheme with hE | hN
  · obtain ⟨C, hC, g, hg⟩ := exists_completeRegularCurve k₀
    have hinit := isInitialOfIsEmpty (X := U.toScheme)
    have hemb : Topology.IsOpenEmbedding (hinit.to C).base :=
      .of_continuous_injective_isOpenMap (hinit.to C).base.hom.continuous (fun x ↦ isEmptyElim x)
        (fun s _ ↦ by rw [Set.eq_empty_of_isEmpty s, Set.image_empty]; exact isOpen_empty)
    have : ∀ x, IsIso ((hinit.to C).stalkMap x) := fun x ↦ isEmptyElim x
    exact ⟨C, hC, g, hinit.to C, IsOpenImmersion.of_isIso_stalkMap _ hemb, hg, hinit.hom_ext _ _⟩
  · have hFi : Irreducible F :=
      Irreducible.of_map (f := MvPolynomial.map (σ := Fin 2) (algebraMap k₀ (AlgebraicClosure k₀))) hF
    have : (Ideal.span {F}).IsPrime := (Ideal.span_singleton_prime hFi.ne_zero).2 hFi.prime
    have : IsDomain A := Ideal.Quotient.isDomain _
    have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    set f := U.ι ≫ specStructure k₀ A with hf
    have hsm : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_nonsingularLocus k₀ F
    have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    have hregv : IsRegularVariety k₀ f := fun x _ ↦ isRegularLocalRing_stalk_of_smooth f x
    have hdim : dimension k₀ f = 1 := by
      letI := overOf k₀ f
      have : SmoothOfRelativeDimension 1 (U.toScheme ↘ Spec (CommRingCat.of k₀)) := hsm
      have : Smooth (U.toScheme ↘ Spec (CommRingCat.of k₀)) := SmoothOfRelativeDimension.smooth 1 _
      have : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k₀)) := inferInstance
      have h1 := TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField k₀
        (X := U.toScheme)
      rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension (n := 1)
        (U.toScheme ↘ Spec (CommRingCat.of k₀))] at h1
      have h2 : (Algebra.trdeg k₀ U.toScheme.functionField).toNat = 1 := by exact_mod_cast h1.symm
      simp only [dimension]
      rw [functionFieldAlgebraMap_eq]
      exact Cardinal.toNat_eq_one.1 h2
    let fj : Fin 2 → A := fun j ↦ Ideal.Quotient.mk _ (MvPolynomial.pderiv j F)
    let D : Fin 2 → (Spec (CommRingCat.of A)).Opens := fun j ↦ PrimeSpectrum.basicOpen (fj j)
    have hDU : ∀ j, D j ≤ U := by
      intro j x hx
      show x ∈ nonsingularLocus k₀ F
      rw [mem_nonsingularLocus]
      have hx' : fj j ∉ x.asIdeal := hx
      fin_cases j
      · exact Or.inl hx'
      · exact Or.inr hx'
    have hcover : ⨆ j, U.ι ⁻¹ᵁ D j = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x.1 ∈ nonsingularLocus k₀ F := x.2
      rw [mem_nonsingularLocus] at hx
      simp only [TopologicalSpace.Opens.mem_iSup, Scheme.Hom.mem_preimage]
      rcases hx with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hprev : IsPrevariety k₀ f := by
      refine ⟨2, fun j ↦ U.ι ⁻¹ᵁ D j, hcover, fun j ↦ ⟨Localization.Away (fj j), inferInstance,
        inferInstance, isAffineAlgebra_away k₀ F hF (fj j),
        Scheme.Opens.isoOfLE (hDU j) ≪≫ basicOpenIsoSpecAway (R := CommRingCat.of A) (fj j), ?_⟩⟩
      have e3 : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (fj j)))) ≫
          specStructure k₀ A = specStructure k₀ (Localization.Away (fj j)) := by
        rw [specStructure, specStructure, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq]
      rw [Iso.trans_hom, Category.assoc, ← e3, ← Category.assoc (basicOpenIsoSpecAway _).hom,
        basicOpenIsoSpecAway_hom_SpecMap, ← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, Category.assoc]
    have hreg : IsRegularCurve k₀ f := ⟨⟨⟨hprev, inferInstance⟩, hdim⟩, hregv⟩
    obtain ⟨Cbar, hI, g, ι, hι, hC, hcomp, -⟩ := (regularCurveCompletion k₀).completion f hreg
    exact ⟨Cbar, hI, g, ι, hι, hC, hcomp⟩

end ModularFormsKB.Milne
