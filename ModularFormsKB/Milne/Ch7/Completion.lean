import ModularFormsKB.Milne.Ch7.CompletionReduced
import ModularFormsKB.Milne.Ch7.CompletionModel
import ModularFormsKB.Milne.Ch7.CompletionImmersion

/-!
# Milne, Corollary 7.3: completion of a regular curve

`ModularFormsKB.Milne.regularCurveCompletion : RegularCurveCompletion k₀`, for every field $k_0$. For a regular curve
$U$ over $k_0$ with function field $K$:
- every local ring of $U$ is a valuation ring (`valuationRing_stalk`), $K$ is a function field in one variable
  (Tau Ceti's `isFunctionField_functionField_iff`), and $\bar k \otimes K$ is reduced
  (`Completion.isReduced_tensor_functionField`);
- $\bar U$ is Tau Ceti's two-chart model of $K$ (the normalization of $\mathbb P^1$ in $K$), a complete regular curve in
  Milne's sense (`Completion.isCompleteRegularCurve_twoChartModel`);
- $\iota : U \to \bar U$ extends $\operatorname{Spec} K \to \bar U$ from the generic point; it is an open immersion
  (`Completion.isOpenImmersion_ι`) and universal (`Completion.exists_unique_extension`).
-/

universe u

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.twoChartModel

noncomputable section

namespace ModularFormsKB.Milne

variable (k₀ : Type u) [Field k₀]

/-- A Milne complete regular curve is proper. -/
theorem isProper_of_isCompleteRegularCurve {C : Scheme.{u}} [IsIntegral C] (h : C ⟶ Spec (CommRingCat.of k₀))
    (hC : IsCompleteRegularCurve k₀ h) : IsProper h := by
  have := hC.1.1.2
  have : UniversallyClosed h := hC.2.2
  have := hC.1.1.locallyOfFiniteType
  constructor

/-- **Milne, Corollary 7.3, unconditionally**: every regular curve embeds as an open subscheme into a complete regular
curve, universally among maps to complete regular curves. -/
@[kb "milne2017mf" "Section 7, Corollary 7.3 (pdf p. 94)"]
theorem regularCurveCompletion : RegularCurveCompletion k₀ := by
  refine ⟨fun {U} _ f hU ↦ ?_⟩
  letI := overOf k₀ f
  have hvar := hU.1.1
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := hvar.locallyOfFiniteType
  have : IsSeparated (U ↘ Spec (CommRingCat.of k₀)) := hvar.2
  have hval := valuationRing_stalk k₀ f hU
  have hF : IsFunctionField k₀ U.functionField :=
    (TauCeti.AlgebraicGeometry.isFunctionField_functionField_iff k₀).2 (topologicalKrullDim_eq_one k₀ f hU.1)
  obtain ⟨x, hxt⟩ := hF.exists_transcendental
  have hred := Completion.isReduced_tensor_functionField f hvar
  have hM := Completion.isCompleteRegularCurve_twoChartModel hF hxt hred
  have : IsProper (twoChartModel hF hxt.ne_zero ↘ Spec (CommRingCat.of k₀)) := isProper hxt
  have hMval := TauCeti.AlgebraicGeometry.twoChartModel.valuationRing_stalk (hF := hF) (hx := hxt.ne_zero) hxt
  let e : (twoChartModel hF hxt.ne_zero).functionField ≃ₐ[k₀] U.functionField := functionFieldEquiv hxt
  refine ⟨twoChartModel hF hxt.ne_zero, inferInstance, twoChartModel hF hxt.ne_zero ↘ Spec (CommRingCat.of k₀),
    Completion.ι hval e, Completion.isOpenImmersion_ι hval e hMval, hM,
    comp_over (Completion.ι hval e) (Spec (CommRingCat.of k₀)), ?_⟩
  intro C _ h hC φ hφ
  letI := overOf k₀ h
  have : IsProper (C ↘ Spec (CommRingCat.of k₀)) := isProper_of_isCompleteRegularCurve k₀ h hC
  have : φ.IsOver (Spec (CommRingCat.of k₀)) := ⟨hφ⟩
  obtain ⟨φbar, ⟨hover, hι⟩, huniq⟩ := Completion.exists_unique_extension hval hMval e φ
  exact ⟨φbar, ⟨hover.comp_over, hι⟩, fun ψ ⟨h1, h2⟩ ↦ huniq ψ ⟨⟨h1⟩, h2⟩⟩

end ModularFormsKB.Milne
