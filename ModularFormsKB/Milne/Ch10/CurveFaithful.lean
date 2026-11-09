import ModularFormsKB.Milne.Ch7.Curves
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Milne, Theorem 7.2: the faithful half

A dominant morphism between integral schemes is determined, among morphisms to a separated scheme over a common base,
by the map it induces on function fields (`functionFieldMap_injective`): both morphisms agree on
$\operatorname{Spec} k(X)$, hence (Mathlib, `PartialMap.equiv_of_fromSpecStalkOfMem_eq`) on a dense open subscheme, hence
everywhere since $X$ is reduced and $Y$ separated (Mathlib, `PartialMap.equiv_iff_of_domain_eq_of_isSeparated`).

In particular the `faithful` field of Milne's Theorem 7.2 (`CurveFunctionFieldEquivalence`) holds for every field
$k_0$ (`curveFunctionField_faithful`); the remaining content of Theorem 7.2 used for Proposition 10.2 is its `full`
field, isolated as the named statement `CurveFunctionFieldFull`.
-/

open CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

namespace ModularFormsKB.Milne

universe u

/-- The composite $\operatorname{Spec} k(X) \to X \to Y$ factors through $\operatorname{Spec}$ of the map of
function fields. -/
theorem fromSpecStalk_genericPoint_comp {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X ⟶ Y) [IsDominant φ] :
    X.fromSpecStalk (genericPoint X) ≫ φ =
      Spec.map (functionFieldMap φ) ≫ Y.fromSpecStalk (genericPoint Y) := by
  rw [functionFieldMap, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- **Morphisms to a separated scheme are determined by their maps of function fields.** -/
theorem eq_of_functionFieldMap_eq {S X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated g] (φ ψ : X ⟶ Y) [IsDominant φ] [IsDominant ψ]
    (hφ : φ ≫ g = f) (hψ : ψ ≫ g = f) (h : functionFieldMap φ = functionFieldMap ψ) : φ = ψ := by
  letI : X.Over S := ⟨f⟩
  letI : Y.Over S := ⟨g⟩
  haveI : φ.IsOver S := ⟨hφ⟩
  haveI : ψ.IsOver S := ⟨hψ⟩
  haveI : IsSeparated (Y ↘ S) := ‹IsSeparated g›
  have hx : genericPoint X ∈ φ.toPartialMap.domain := trivial
  have hstalk : φ.toPartialMap.fromSpecStalkOfMem hx = ψ.toPartialMap.fromSpecStalkOfMem hx := by
    simp only [Scheme.PartialMap.fromSpecStalkOfMem, Scheme.Hom.toPartialMap_hom]
    have hι : ∀ χ : X ⟶ Y, (⊤ : X.Opens).fromSpecStalkOfMem (genericPoint X) hx ≫ X.topIso.hom ≫ χ =
        X.fromSpecStalk (genericPoint X) ≫ χ := by
      intro χ
      rw [← Category.assoc]
      congr 1
      rw [← Scheme.Opens.fromSpecStalkOfMem_ι (⊤ : X.Opens) (genericPoint X) hx]
      congr 1
    refine (hι φ).trans (Eq.trans ?_ (hι ψ).symm)
    rw [fromSpecStalk_genericPoint_comp, fromSpecStalk_genericPoint_comp, h]
  have hequiv := Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq φ.toPartialMap ψ.toPartialMap hx hx hstalk
  have heq := (Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated (S := S) (f := φ.toPartialMap)
    (g := ψ.toPartialMap) rfl).mp hequiv
  obtain ⟨e, he⟩ := (Scheme.PartialMap.ext_iff _ _).mp heq
  have h1 : (X.isoOfEq e).hom = 𝟙 _ := by
    change (X.isoOfEq rfl).hom = 𝟙 _
    simp
  erw [h1, Category.id_comp] at he
  exact (cancel_epi _).mp he

variable (k₀ : Type u) [Field k₀]

/-- **The faithful half of Milne's Theorem 7.2**, proved for every field $k_0$. -/
theorem curveFunctionField_faithful {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (CommRingCat.of k₀)) (g : Y ⟶ Spec (CommRingCat.of k₀)) (_hf : IsCompleteRegularCurve k₀ f)
    (hg : IsCompleteRegularCurve k₀ g) (φ ψ : X ⟶ Y) [IsDominant φ] [IsDominant ψ] (hφ : φ ≫ g = f)
    (hψ : ψ ≫ g = f) (h : functionFieldMap φ = functionFieldMap ψ) : φ = ψ := by
  haveI : IsSeparated g := hg.1.1.2
  exact eq_of_functionFieldMap_eq f g φ ψ hφ hψ h

/-- **The full half of Milne's Theorem 7.2** (named statement): every $k_0$-embedding of function fields
$k_0(Y) \to k_0(X)$ of complete regular curves is induced by a dominant $k_0$-morphism $X \to Y$. This is the
`full` field of `CurveFunctionFieldEquivalence` (equivalently of its corrected form for perfect $k_0$); with
`curveFunctionField_faithful` it is the part of Theorem 7.2 that Proposition 10.2 uses. -/
@[kb "milne2017mf" "Section 7, Theorem 7.2 (pdf p. 94), fullness"]
structure CurveFunctionFieldFull : Prop where
  full : ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Spec (CommRingCat.of k₀))
    (g : Y ⟶ Spec (CommRingCat.of k₀)), IsCompleteRegularCurve k₀ f → IsCompleteRegularCurve k₀ g →
    ∀ σ : Y.functionField ⟶ X.functionField,
      (∀ c : k₀, σ.hom (functionFieldAlgebraMap k₀ g c) = functionFieldAlgebraMap k₀ f c) →
      ∃ (φ : X ⟶ Y) (_ : IsDominant φ), φ ≫ g = f ∧ functionFieldMap φ = σ

/-- Theorem 7.2 gives its full half. -/
theorem curveFunctionFieldFull_of_equivalence (h : CurveFunctionFieldEquivalence k₀) :
    CurveFunctionFieldFull k₀ :=
  ⟨h.full⟩

end ModularFormsKB.Milne
