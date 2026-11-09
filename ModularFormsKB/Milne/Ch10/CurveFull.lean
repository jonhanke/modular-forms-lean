import ModularFormsKB.Milne.Ch10.CurveFaithful
import ModularFormsKB.Milne.Ch10.FunctionFieldBridge
import TauCeti.AlgebraicGeometry.Birational.AlgHom
import TauCeti.AlgebraicGeometry.Curves.Basic
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
# Milne, Theorem 7.2: the full half

A complete regular curve in Milne's sense (`IsCompleteRegularCurve`: a variety of dimension one, i.e. with function
field of transcendence degree one, regular at the closed points, complete) is a regular proper curve in Tau Ceti's
sense: proper, integral, of Krull dimension one (`TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField`),
with discrete valuation rings at the codimension-one points (these are the closed points, where the local ring is
regular of dimension one). Tau Ceti's `AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom` (Hartshorne, Corollary
I.6.12: the local rings are valuation rings and the target is proper, so the map at the generic point extends)
then gives every $k_0$-embedding of function fields as the pullback along a dominant $k_0$-morphism:
**`curveFunctionFieldFull : CurveFunctionFieldFull k₀`**, for every field $k_0$.
-/

open CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

namespace ModularFormsKB.Milne

universe u

variable (k : Type u) [Field k]

/-- A complete regular curve is proper over $k$. -/
theorem isProper_of_isCompleteRegularCurve {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ Spec (CommRingCat.of k)}
    (hf : IsCompleteRegularCurve k f) : IsProper f := by
  haveI : LocallyOfFiniteType f := hf.1.1.locallyOfFiniteType
  haveI : IsSeparated f := hf.1.1.2
  haveI : UniversallyClosed f := hf.2.2
  exact ⟨⟩

/-- A complete regular curve is a Tau Ceti curve. -/
theorem isCurveOver_of_isCompleteRegularCurve {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsCompleteRegularCurve k f) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    X.IsCurveOver k := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of k)) := hf.1.1.locallyOfFiniteType
  haveI : IsProper (X ↘ Spec (.of k)) := isProper_of_isCompleteRegularCurve k hf
  have hfun := isFunctionField_functionField k f hf.1
  have h : functionFieldAlgebraMap k f = Scheme.baseRingToFunctionField k X := by
    ext c
    rfl
  have hdim : topologicalKrullDim X = 1 := by
    refine (TauCeti.AlgebraicGeometry.isFunctionField_functionField_iff k).mp ?_
    convert hfun using 2
    exact congrArg RingHom.toAlgebra h.symm
  exact ⟨hdim⟩

/-- The codimension-one points of a curve are closed. -/
theorem isClosed_of_codimensionOnePoint {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsCurveOver k]
    (y : TauCeti.AlgebraicGeometry.CodimensionOnePoint X) : IsClosed ({(y : X)} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun z hz => ?_
  have hyz : (y : X) ⤳ z := specializes_iff_mem_closure.mpr hz
  by_contra hne
  have hlt : z < (y : X) :=
    ⟨hyz, fun hzy => hne (Inseparable.eq (inseparable_iff_specializes_and.mpr ⟨hzy, hyz⟩))⟩
  have hz1 := Scheme.IsCurveOver.coheight_le_one (k := k) z
  have := Order.coheight_strictAnti hlt (by simp [y.property])
  rw [y.property] at this
  exact absurd (lt_of_lt_of_le this hz1) (lt_irrefl _)

/-- The local rings of a complete regular curve at its codimension-one points are discrete valuation rings. -/
theorem isDiscreteValuationRing_stalk_of_isCompleteRegularCurve {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsCompleteRegularCurve k f) :
    letI : X.Over (Spec (.of k)) := ⟨f⟩
    ∀ y : TauCeti.AlgebraicGeometry.CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := by
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI := isCurveOver_of_isCompleteRegularCurve k f hf
  haveI : LocallyOfFiniteType f := hf.1.1.locallyOfFiniteType
  intro y
  have hcl := isClosed_of_codimensionOnePoint k y
  haveI hreg : IsRegularLocalRing (X.presheaf.stalk (y : X)) := hf.2.1 _ hcl
  have hdim : ringKrullDim (X.presheaf.stalk (y : X)) = 1 := by
    rw [TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed f hcl,
      Scheme.IsCurveOver.topologicalKrullDim_eq_one k]
  have hnf : ¬ IsField (X.presheaf.stalk (y : X)) := by
    intro hfield
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at this
    exact absurd this (by decide)
  have hcot : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk (y : X)))
      (IsLocalRing.CotangentSpace (X.presheaf.stalk (y : X))) = 1 := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk (y : X))).mp hreg
    rw [hdim] at this
    exact_mod_cast this
  exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (y : X)) hnf).out 1 6).mpr hcot

/-- **The full half of Milne's Theorem 7.2**, proved: every $k$-embedding of the function fields of complete
regular curves is the pullback along a dominant $k$-morphism. -/
theorem curveFunctionFieldFull : CurveFunctionFieldFull.{u} k := by
  refine ⟨fun {X Y} _ _ f g hf hg σ hσ => ?_⟩
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  letI : Y.Over (Spec (.of k)) := ⟨g⟩
  haveI := isCurveOver_of_isCompleteRegularCurve k f hf
  haveI := isCurveOver_of_isCompleteRegularCurve k g hg
  haveI : IsProper (Y ↘ Spec (.of k)) := isProper_of_isCompleteRegularCurve k hg
  haveI := isDiscreteValuationRing_stalk_of_isCompleteRegularCurve k f hf
  have hX := Scheme.IsCurveOver.valuationRing_stalk k X
  let ψ : Y.functionField →ₐ[k] X.functionField :=
    { σ.hom with commutes' := fun c => hσ c }
  let φ := Scheme.homOfFunctionFieldAlgHom hX ψ
  refine ⟨φ, inferInstance, CategoryTheory.comp_over φ (Spec (.of k)), ?_⟩
  have h1 := Scheme.fromSpecStalk_homOfFunctionFieldAlgHom hX ψ
  have h2 := fromSpecStalk_genericPoint_comp φ
  have hσψ : CommRingCat.ofHom ψ.toRingHom = σ := rfl
  rw [hσψ] at h1
  have h3 : Spec.map (functionFieldMap φ) ≫ Y.fromSpecStalk (genericPoint Y) =
      Spec.map σ ≫ Y.fromSpecStalk (genericPoint Y) := h2.symm.trans h1
  rw [cancel_mono, Spec.map_inj] at h3
  exact h3

end ModularFormsKB.Milne
