import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.XRatFunc

/-!
# Milne wave 5: the action of an isogeny on points, computed by rational functions

Tau Ceti records a morphism `f : Hom W₁ W₂` of elliptic curves by its pullback of functions and defines its action on
points `f.pointMap` through places of the function field. For the `x`-coordinate it proves that `x ∘ φ = r(x)` and
that the image of an affine point `(x₀, y₀)` has `x`-coordinate `r(x₀)` away from the poles of `r`
(`TauCeti.Isogeny.xCoord_pointMap_ofIsogeny_some`). This file adds the companion statement for the `y`-coordinate, for
any presentation of `y ∘ φ` as a quotient of two classes of the coordinate ring: if `y ∘ φ = p / q` and `q(x₀, y₀) ≠ 0`
then the image of `(x₀, y₀)` has `y`-coordinate `p(x₀, y₀) / q(x₀, y₀)`.

These are the inputs for comparing Tau Ceti's endomorphisms of `E(Λ)` with holomorphic maps of `ℂ/Λ`
(Milne, Proposition 3.3 with Proposition 3.12; `ModularFormsKB.Milne.Wave5.EndomorphismLift`).
-/

open Polynomial WeierstrassCurve.Affine TauCeti TauCeti.Isogeny

open scoped RatFunc

namespace ModularFormsKB.Milne.Wave5

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The `y`-coordinate of the image of an affine point**, for a presentation `y ∘ φ = p / q` of the pulled-back
coordinate by two classes of the coordinate ring, where `q` does not vanish at the point. -/
theorem yCoord_pointMap_ofIsogeny_some [DecidableEq F] (φ : Isogeny W₁ W₂) {x y : F} (h : W₁.Nonsingular x y)
    {p q : F[X][X]} (hq : q.evalEval x y ≠ 0)
    (hpq : φ.fieldPullback (genericY W₂) =
      algebraMap W₁.CoordinateRing W₁.FunctionField (CoordinateRing.mk W₁ p) /
        algebraMap W₁.CoordinateRing W₁.FunctionField (CoordinateRing.mk W₁ q))
    (hne : (Hom.ofIsogeny φ).pointMap (.some x y h) ≠ 0) :
    Point.yCoord ((Hom.ofIsogeny φ).pointMap (.some x y h)) = p.evalEval x y / q.evalEval x y := by
  have hQ := (Hom.pointMap_eq_iff (f := Hom.ofIsogeny φ) (P := .some x y h)).mp rfl
  generalize (Hom.ofIsogeny φ).pointMap (.some x y h) = Q at hQ hne ⊢
  rcases Q with _ | ⟨c, d, hc⟩
  · exact absurd rfl hne
  rw [Point.yCoord_some]
  rw [Point.equivBaseChangeSelf_some, Hom.tautologicalPoint_ofIsogeny,
    ← Point.some_coords (CoordinatePullback.tautologicalPoint_ne_zero _),
    coe_pointEquivDegreeOnePlace_some, some_sub_baseChange_mem_polePoints_iff,
    CoordinatePullback.yCoord_tautologicalPoint, ← AdjoinRoot.mk_X, ← CoordinateRing.mk,
    ← fieldPullback_algebraMap, ← genericY_def] at hQ
  set e := p.evalEval x y / q.evalEval x y
  have hq0 : CoordinateRing.mk W₁ q ≠ 0 := by
    intro h0
    -- a class vanishing in the coordinate ring vanishes at every point of the curve
    obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_zero.1 h0
    apply hq
    rw [hr, evalEval_mul, h.left, zero_mul]
  have hD : algebraMap W₁.CoordinateRing W₁.FunctionField (CoordinateRing.mk W₁ q) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective W₁.CoordinateRing
      W₁.FunctionField)).mpr hq0
  have heq : φ.fieldPullback (genericY W₂) - algebraMap F W₁.FunctionField e =
      algebraMap W₁.CoordinateRing W₁.FunctionField
          (CoordinateRing.mk W₁ (p - C (C e) * q)) /
        algebraMap W₁.CoordinateRing W₁.FunctionField (CoordinateRing.mk W₁ q) := by
    rw [hpq, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, map_sub, map_sub, map_mul, map_mul,
      CoordinateRing.mk_C_eq_algebraMap, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hR : (Place.ofPrime F W₁.FunctionField (CoordinateRing.pointPlace h.left)).valuation
      (φ.fieldPullback (genericY W₂) - algebraMap F W₁.FunctionField e) < 1 := by
    rw [Place.valuation_ofPrime, heq]
    refine CoordinateRing.valuation_pointPlace_div_lt_one _ h.left hq ?_
    rw [evalEval_sub, evalEval_mul, evalEval_C, eval_C, div_mul_cancel₀ _ hq, sub_self]
  exact (Place.eq_of_valuation_sub_lt_one _ hQ.2 hR)

/-! ### Curves with `a₁ = a₃ = 0`: `y ∘ φ = y · s(x)` -/

section ShortForm

variable {W : WeierstrassCurve.Affine F} [W.IsElliptic]

omit [W.IsElliptic] in
/-- On a curve with `a₁ = a₃ = 0`, negation sends `y` to `-y`. -/
theorem fieldPullback_negIsogeny_genericY_of_a₁_a₃ (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) :
    (negIsogeny W).fieldPullback (genericY W) = -genericY W := by
  rw [fieldPullback_negIsogeny_genericY]
  simp only [negY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, h₁, h₃,
    map_zero, zero_mul, sub_zero]

/-- On a curve with `a₁ = a₃ = 0`, the generic `y` is nonzero. -/
theorem genericY_ne_zero_of_a₁_a₃ (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) : genericY W ≠ 0 := by
  intro h0
  apply evalEval_polynomialY_genericX_genericY_ne_zero W
  simp only [polynomialY, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, h₁,
    h₃, map_zero, h0, evalEval_mul, evalEval_C, evalEval_X, eval_C, mul_zero, zero_mul, add_zero]

/-- **`y ∘ φ = y · s(x)`** for an isogeny between curves with `a₁ = a₃ = 0`: `(y ∘ φ) / y` is fixed by negation, as
`φ` commutes with negation and negation sends `y` to `-y`, so it is a rational function of `x`. -/
theorem exists_fieldPullback_genericY_eq {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁ W₂) (h₁ : W₁.a₁ = 0) (h₃ : W₁.a₃ = 0)
    (h₁' : W₂.a₁ = 0) (h₃' : W₂.a₃ = 0) :
    ∃ s : RatFunc F, φ.fieldPullback (genericY W₂) =
      genericY W₁ * algebraMap (RatFunc F) W₁.FunctionField s := by
  have hfix : (negIsogeny W₁).fieldPullback (φ.fieldPullback (genericY W₂)) =
      -φ.fieldPullback (genericY W₂) := by
    rw [← AlgHom.comp_apply, ← comp_fieldPullback, ← negIsogeny_comp, comp_fieldPullback, AlgHom.comp_apply,
      fieldPullback_negIsogeny_genericY_of_a₁_a₃ h₁' h₃', map_neg]
  have hy := genericY_ne_zero_of_a₁_a₃ h₁ h₃ (W := W₁)
  have hu : (negIsogeny W₁).fieldPullback (φ.fieldPullback (genericY W₂) / genericY W₁) =
      φ.fieldPullback (genericY W₂) / genericY W₁ := by
    rw [map_div₀, hfix, fieldPullback_negIsogeny_genericY_of_a₁_a₃ h₁ h₃, neg_div_neg_eq]
  obtain ⟨s, hs⟩ := (mem_ratFuncRange W₁).1 ((fieldPullback_negIsogeny_eq_self_iff W₁).1 hu)
  refine ⟨s, ?_⟩
  rw [IsScalarTower.toAlgHom_apply] at hs
  rw [hs, mul_div_cancel₀ _ hy]

end ShortForm

/-- An affine point with given coordinates. -/
theorem point_some_eq_some {W : WeierstrassCurve.Affine F} {x y x' y' : F} (h : W.Nonsingular x y)
    (h' : W.Nonsingular x' y') (hx : x = x') (hy : y = y') : Point.some x y h = Point.some x' y' h' := by
  subst hx hy
  rfl

/-- **The image of an affine point under an isogeny**, read off the rational functions `r = φ.xRatFunc` and `s` with
`y ∘ φ = y s(x)`: if neither denominator vanishes at `x₀`, then `φ(x₀, y₀) = (r(x₀), y₀ s(x₀))`. -/
theorem pointMap_ofIsogeny_some_eq [DecidableEq F] (φ : Isogeny W₁ W₂) {s : RatFunc F}
    (hs : φ.fieldPullback (genericY W₂) = genericY W₁ * algebraMap (RatFunc F) W₁.FunctionField s)
    {x y : F} (h : W₁.Nonsingular x y) (hr : φ.xRatFunc.denom.eval x ≠ 0) (hsd : s.denom.eval x ≠ 0) :
    ∃ h' : W₂.Nonsingular (φ.xRatFunc.num.eval x / φ.xRatFunc.denom.eval x)
        (y * (s.num.eval x / s.denom.eval x)),
      (Hom.ofIsogeny φ).pointMap (.some x y h) = .some _ _ h' := by
  have hne : (Hom.ofIsogeny φ).pointMap (.some x y h) ≠ 0 :=
    (pointMap_ofIsogeny_some_eq_zero_iff (φ := φ) h).not.mpr hr
  have hxc := xCoord_pointMap_ofIsogeny_some (φ := φ) h hr
  have hpq : φ.fieldPullback (genericY W₂) =
      algebraMap W₁.CoordinateRing W₁.FunctionField (CoordinateRing.mk W₁ (C s.num * X)) /
        algebraMap W₁.CoordinateRing W₁.FunctionField (CoordinateRing.mk W₁ (C s.denom)) := by
    rw [hs, map_mul, map_mul, ← genericY_def, CoordinateRing.mk_C_eq_algebraMap,
      CoordinateRing.mk_C_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    nth_rewrite 1 [← RatFunc.num_div_denom s]
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    ring
  have hyc := yCoord_pointMap_ofIsogeny_some φ h (p := C s.num * X) (q := C s.denom)
    (by rwa [evalEval_C]) hpq hne
  generalize (Hom.ofIsogeny φ).pointMap (.some x y h) = Q at hne hxc hyc ⊢
  rcases Q with _ | ⟨c, d, hc⟩
  · exact absurd rfl hne
  rw [Point.xCoord_some] at hxc
  rw [Point.yCoord_some, evalEval_C, evalEval_mul, evalEval_C, evalEval_X] at hyc
  subst hxc
  refine ⟨by rw [show y * (s.num.eval x / s.denom.eval x) = d by rw [hyc]; ring]; exact hc, ?_⟩
  exact point_some_eq_some _ _ rfl (by rw [hyc]; ring)
