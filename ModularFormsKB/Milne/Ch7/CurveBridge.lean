import ModularFormsKB.Milne.Ch7.Curves
import TauCeti.AlgebraicGeometry.Scheme.FunctionField
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.Topology.KrullDimension.Basic

/-!
# Milne's curves and Tau Ceti's curves

Dictionary between Milne's notions (Section 7: varieties with finite affine covers by geometrically reduced affine
algebras, dimension the transcendence degree of the function field, regularity at closed points) and the
scheme-theoretic notions used by Tau Ceti's theory of curves (structure morphism as an `Over` instance, Krull
dimension, valuation rings as local rings).

- `functionFieldAlgebraMap_eq`: Milne's $k_0 \to k_0(X)$ is Tau Ceti's `Scheme.baseRingToFunctionField` for the
  `Over` structure given by $f$.
- `topologicalKrullDim_eq_one`: a Milne curve has Krull dimension one
  (Tau Ceti's `topologicalKrullDim_eq_toNat_trdeg_functionField`).
- `valuationRing_stalk`: every local ring of a regular Milne curve is a valuation ring (a field at the generic
  point, a regular local ring of dimension one, i.e. a discrete valuation ring, at the closed points; Tau Ceti's
  `IsRegularLocalRing.valuationRing_of_ringKrullDim_le_one`).
-/

universe u

open AlgebraicGeometry CategoryTheory Order

noncomputable section

namespace ModularFormsKB.Milne

variable (k₀ : Type u) [Field k₀]

/-- The `Over` structure given by a morphism to $\operatorname{Spec} k_0$. -/
abbrev overOf {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k₀)) : X.Over (Spec (CommRingCat.of k₀)) := ⟨f⟩

theorem functionFieldAlgebraMap_eq {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀)) :
    functionFieldAlgebraMap k₀ f = @Scheme.baseRingToFunctionField k₀ _ X (overOf k₀ f) _ := by
  rfl

/-- A Milne curve has Krull dimension one. -/
theorem topologicalKrullDim_eq_one {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀))
    (hX : IsCurve k₀ f) : topologicalKrullDim X = 1 := by
  letI := overOf k₀ f
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := hX.1.locallyOfFiniteType
  rw [TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField k₀]
  have h := hX.2
  simp only [dimension] at h
  have e : (functionFieldAlgebraMap k₀ f).toAlgebra = Scheme.functionFieldBaseAlgebra k₀ X := by
    rw [functionFieldAlgebraMap_eq]
    rfl
  rw [e] at h
  rw [h]
  simp

/-- **Every local ring of a regular Milne curve is a valuation ring.** -/
theorem valuationRing_stalk {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k₀))
    (hX : IsRegularCurve k₀ f) (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have hdim := topologicalKrullDim_eq_one k₀ f hX.1
  have hle : ∀ y : X, coheight y ≤ 1 := by
    intro y
    have := TauCeti.coheight_le_topologicalKrullDim y
    rw [hdim] at this
    exact_mod_cast this
  have : IsLocallyNoetherian X := by
    letI := overOf k₀ f
    have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := hX.1.1.locallyOfFiniteType
    exact LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  by_cases hx : IsClosed ({x} : Set X)
  · have := hX.2 x hx
    refine TauCeti.IsRegularLocalRing.valuationRing_of_ringKrullDim_le_one ?_
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast hle x
  · -- `x` has a proper specialization, so its local ring has dimension zero: it is a field.
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ closure ({x} : Set X), z ≠ x := by
      by_contra h
      push Not at h
      exact hx (by
        rw [← closure_subset_iff_isClosed]
        intro z hz
        exact h z hz)
    have hspec : x ⤳ z := specializes_iff_mem_closure.2 hz
    have hlt : z < x := ⟨hspec, fun h ↦ hzx (h.antisymm hspec).eq⟩
    have h0 : coheight x = 0 := by
      have hfin : coheight x < ⊤ := lt_of_le_of_lt (hle x) (by decide)
      have h1 := Order.coheight_strictAnti hlt hfin
      have : coheight x < 1 := lt_of_lt_of_le h1 (hle z)
      exact Order.lt_one_iff.1 this
    have hd : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h0]
      simp
    have hd0 : ringKrullDim (X.presheaf.stalk x) = 0 := by
      rw [ringKrullDim_stalk_eq_coheight, h0]
      rfl
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := (Ring.krullDimLE_iff).2 (by rw [hd0]; simp)
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    exact TauCeti.IsRegularLocalRing.valuationRing_of_ringKrullDim_le_one hd

end ModularFormsKB.Milne
