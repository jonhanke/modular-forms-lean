import ModularFormsKB.Milne.Ch7.Completion
import ModularFormsKB.Milne.Ch7.PerfectReduced
import ModularFormsKB.Milne.Ch7.FunctionFieldCounterexample
import TauCeti.AlgebraicGeometry.Birational.AlgHom

/-!
# Milne, Theorem 7.2 over a perfect field: the equivalence of curves and function fields

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 7, Theorem 7.2 (pdf p. 94).

The four categorical fields of `CurveFunctionFieldEquivalence`, for a perfect field $k_0$ (Theorem 7.2 fails over
imperfect fields, `Ch7Counterexample.not_curveFunctionFieldEquivalence`):

- `functionField_isFunctionFieldIn`: the function field of a complete regular curve is a function field in one
  variable (Tau Ceti: dimension is transcendence degree, `isFunctionField_functionField_iff`);
- `essSurj`: a function field in one variable $K$ is the function field of the two-chart model of $K$ (Tau Ceti's
  `twoChartModel`), a complete regular curve in Milne's sense since $\bar k_0 \otimes K$ is reduced over a perfect field
  (`isReduced_algebraicClosure_tensor_of_perfectField`, `Completion.isCompleteRegularCurve_twoChartModel`);
- `faithful`: a dominant morphism into a separated scheme is determined by its pullback of rational functions (Tau
  Ceti's `ext_of_functionFieldMap_eq`);
- `full`: a $k_0$-embedding of function fields is the pullback along a dominant morphism (Tau Ceti's
  `homOfFunctionFieldAlgHom`; the local rings of a regular curve are valuation rings, `valuationRing_stalk`).

`faithful` and `full` hold over every field; only `essSurj` uses perfectness.
-/

universe u

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry

noncomputable section

namespace ModularFormsKB.Milne.CurveEquivalence

variable (k₀ : Type u) [Field k₀]

/-- **The function field of a complete regular curve is a function field in one variable.** -/
theorem functionField_isFunctionFieldIn {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀))
    (hX : IsCompleteRegularCurve k₀ f) :
    letI := (functionFieldAlgebraMap k₀ f).toAlgebra
    IsFunctionFieldIn k₀ 1 X.functionField := by
  let := overOf k₀ f
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := hX.1.1.locallyOfFiniteType
  have hF : IsFunctionField k₀ X.functionField :=
    (isFunctionField_functionField_iff k₀).mpr (topologicalKrullDim_eq_one k₀ f hX.1)
  have : Algebra.EssFiniteType k₀ X.functionField := hF.essFiniteType
  have e : (functionFieldAlgebraMap k₀ f).toAlgebra = Scheme.functionFieldBaseAlgebra k₀ X := by
    rw [functionFieldAlgebraMap_eq]
    rfl
  show @IsFunctionFieldIn k₀ _ 1 X.functionField _ (functionFieldAlgebraMap k₀ f).toAlgebra
  rw [e]
  exact ⟨IntermediateField.fg_top_iff.mpr inferInstance, hF.trdeg_eq_one⟩

/-- **Every function field in one variable over a perfect field is the function field of a complete regular
curve.** -/
theorem essSurj [PerfectField k₀] (K : Type u) [Field K] [Algebra k₀ K] (hK : IsFunctionFieldIn k₀ 1 K) :
    ∃ (X : Scheme.{u}) (_ : IsIntegral X) (f : X ⟶ Spec (CommRingCat.of k₀)), IsCompleteRegularCurve k₀ f ∧
      ∃ e : K ≃+* X.functionField, ∀ c : k₀, e (algebraMap k₀ K c) = functionFieldAlgebraMap k₀ f c := by
  have : Algebra.EssFiniteType k₀ K := IntermediateField.fg_top_iff.mp hK.1
  have hF : IsFunctionField k₀ K := (isFunctionField_iff_trdeg_eq_one).mpr (by rw [hK.2]; rfl)
  obtain ⟨x, hxt⟩ := hF.exists_transcendental
  have hred := isReduced_algebraicClosure_tensor_of_perfectField k₀ K
  refine ⟨twoChartModel hF hxt.ne_zero, inferInstance, _,
    Completion.isCompleteRegularCurve_twoChartModel hF hxt hred, ?_⟩
  refine ⟨(twoChartModel.functionFieldEquiv hxt).symm.toRingEquiv, fun c ↦ ?_⟩
  rw [functionFieldAlgebraMap_eq]
  exact (twoChartModel.functionFieldEquiv hxt).symm.commutes c

/-- **Dominant morphisms of complete regular curves are determined by their pullbacks of rational functions.** -/
theorem faithful {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Spec (CommRingCat.of k₀))
    (g : Y ⟶ Spec (CommRingCat.of k₀)) (_hX : IsCompleteRegularCurve k₀ f) (hY : IsCompleteRegularCurve k₀ g)
    (φ ψ : X ⟶ Y) [IsDominant φ] [IsDominant ψ] (hφ : φ ≫ g = f) (hψ : ψ ≫ g = f)
    (h : functionFieldMap φ = functionFieldMap ψ) : φ = ψ := by
  let := overOf k₀ f
  let := overOf k₀ g
  have : IsSeparated (Y ↘ Spec (CommRingCat.of k₀)) := hY.1.1.2
  have : φ.IsOver (Spec (CommRingCat.of k₀)) := ⟨hφ⟩
  have : ψ.IsOver (Spec (CommRingCat.of k₀)) := ⟨hψ⟩
  exact Scheme.Hom.ext_of_functionFieldMap_eq (Spec (CommRingCat.of k₀)) h

/-- **Every $k_0$-embedding of function fields is the pullback along a dominant morphism.** -/
theorem full {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Spec (CommRingCat.of k₀))
    (g : Y ⟶ Spec (CommRingCat.of k₀)) (hX : IsCompleteRegularCurve k₀ f) (hY : IsCompleteRegularCurve k₀ g)
    (σ : Y.functionField ⟶ X.functionField)
    (hσ : ∀ c : k₀, σ.hom (functionFieldAlgebraMap k₀ g c) = functionFieldAlgebraMap k₀ f c) :
    ∃ (φ : X ⟶ Y) (_ : IsDominant φ), φ ≫ g = f ∧ functionFieldMap φ = σ := by
  let := overOf k₀ f
  let := overOf k₀ g
  have : IsProper (Y ↘ Spec (CommRingCat.of k₀)) := isProper_of_isCompleteRegularCurve k₀ g hY
  have hval : ∀ x : X, ValuationRing (X.presheaf.stalk x) :=
    valuationRing_stalk k₀ f ⟨hX.1, hX.2.1⟩
  let σ' : Y.functionField →ₐ[k₀] X.functionField :=
    { σ.hom with commutes' := fun c ↦ hσ c }
  refine ⟨Scheme.homOfFunctionFieldAlgHom hval σ', inferInstance,
    (inferInstance : (Scheme.homOfFunctionFieldAlgHom hval σ').IsOver (Spec (CommRingCat.of k₀))).comp_over, ?_⟩
  change Scheme.Hom.functionFieldMap _ = σ
  rw [Scheme.functionFieldMap_homOfFunctionFieldAlgHom]
  rfl

end ModularFormsKB.Milne.CurveEquivalence

namespace ModularFormsKB.Milne

variable (k₀ : Type u) [Field k₀]

/-- **Geometric irreducibility and the field of constants** (the last assertion of Milne's Theorem 7.2, named
statement; Stacks 0G33, 04KS for the two directions): a complete regular curve $X$ over a perfect field $k_0$ is
geometrically irreducible if and only if $k_0$ is algebraically closed in $k_0(X)$. -/
@[kb "milne2017mf" "Section 7, Theorem 7.2 (pdf p. 94), last assertion"]
structure GeometricallyIrreducibleIffConstants [PerfectField k₀] : Prop where
  statement : ∀ {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)),
    IsCompleteRegularCurve k₀ f →
      (GeometricallyIrreducible f ↔
        letI := (functionFieldAlgebraMap k₀ f).toAlgebra
        fieldOfConstants k₀ X.functionField = ⊥)

/-- **Milne, Theorem 7.2, corrected (perfect $k_0$)**, from the named input on geometric irreducibility: the other four
fields are proved (`CurveEquivalence`). -/
theorem curveFunctionFieldEquivalencePerfect_of_geometricallyIrreducibleIffConstants [PerfectField k₀]
    (h : GeometricallyIrreducibleIffConstants k₀) : CurveFunctionFieldEquivalencePerfect k₀ :=
  ⟨⟨fun f hf ↦ CurveEquivalence.functionField_isFunctionFieldIn k₀ f hf,
    fun K _ _ hK ↦ CurveEquivalence.essSurj k₀ K hK,
    fun f g hf hg φ ψ _ _ hφ hψ h ↦ CurveEquivalence.faithful k₀ f g hf hg φ ψ hφ hψ h,
    fun f g hf hg σ hσ ↦ CurveEquivalence.full k₀ f g hf hg σ hσ,
    fun f hf ↦ h.statement f hf⟩⟩

end ModularFormsKB.Milne
