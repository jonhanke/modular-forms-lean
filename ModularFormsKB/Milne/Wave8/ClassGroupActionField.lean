import ModularFormsKB.Milne.Wave8.ClassGroupAction
import ModularFormsKB.Milne.Ch12.CMBaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Milne wave 8: Proposition 12.21 (corrected form) over every field isomorphic to `ℂ`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 126.

The instance `k = ℂ` of `ClassGroupActionPrincipalNormalized` (`classGroupActionPrincipalNormalized_complex`) is
transported along a field isomorphism `σ : k ≅ ℂ`: base change along `σ` preserves complex multiplication
(`hasCMBy_map`), normalization (the constant of `f^*ω = cω` becomes `σ(c)`, Tau Ceti
`Isogeny.map_pullbackDifferential_invariantDifferential_eq_smul`), kernels on points (`Hom.pointMap_map`, and every
point over `ℂ` comes from a point over `k`) and `j`-invariants (`WeierstrassCurve.map_j`).

By Steinitz's classification (Mathlib `IsAlgClosed.ringEquiv_of_equiv_of_charZero`) every algebraically closed field of
characteristic zero with the cardinality of `ℂ` is isomorphic to `ℂ`; this gives the named statement for all of them
(`classGroupActionPrincipalNormalized_of_nonempty_equiv`), for example `ℂ`, `AlgebraicClosure ℂ` and `ℂ_p`. Fields of
other cardinalities (for example `ℚ̄`) need the Lefschetz principle: the descent of a curve with complex
multiplication, its endomorphisms and its `𝔞`-isogenies to the algebraic closure of `ℚ` in `k`.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields WeierstrassCurve.Affine Cardinal
open scoped Classical

namespace ModularFormsKB.Milne.Wave8

section BaseChange

variable {k k' : Type*} [Field k] [Field k']

/-- **The constant of a morphism under base change**: if `f^*ω₂ = c ω₁` then `(f ⊗ k')^*ω₂ = σ(c) ω₁`. -/
theorem hom_map_pullbackDifferential {W₁ W₂ : WeierstrassCurve.Affine k} [W₁.IsElliptic] [W₂.IsElliptic]
    (f : Hom W₁ W₂) (σ : k →+* k') {c : k}
    (hc : f.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    (f.map σ).pullbackDifferential (invariantDifferential (W₂.map σ)) = σ c • invariantDifferential (W₁.map σ) := by
  rcases Hom.eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · rw [Hom.pullbackDifferential_zero, LinearMap.zero_apply, eq_comm] at hc
    rw [(smul_eq_zero.1 hc).resolve_right (invariantDifferential_ne_zero _), map_zero, zero_smul, Hom.zero_map,
      Hom.pullbackDifferential_zero, LinearMap.zero_apply]
  rw [Hom.pullbackDifferential_ofIsogeny] at hc
  rw [Hom.ofIsogeny_map, Hom.pullbackDifferential_ofIsogeny]
  exact map_pullbackDifferential_invariantDifferential_eq_smul φ σ hc

/-- **Normalization is preserved by base change** along a field isomorphism `σ`, for the embedding `σ ∘ ι`. -/
theorem isNormalizedCM_map (σ : k ≃+* k') {W : WeierstrassCurve k} [W.IsElliptic] {K : Type*} [Field K]
    [NumberField K] {O : NumberFieldOrder K} (ι : K →+* k) (i : O.toSubalgebra ≃+* Hom W.toAffine W.toAffine)
    (hi : IsNormalizedCM ι i) :
    IsNormalizedCM ((σ : k →+* k').comp ι) (i.trans (homMapRingEquiv σ W)) := by
  intro a
  exact hom_map_pullbackDifferential (i a) (σ : k →+* k') (hi a)

/-- Every point over `k'` of `W ⊗ k'` comes from a point over `k`, for a field isomorphism `σ : k ≅ k'`. -/
theorem mapAlong_surjective (σ : k ≃+* k') (W : WeierstrassCurve k) :
    Function.Surjective (Point.mapAlong (σ : k →+* k') σ.injective (W := W)) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, Point.mapAlong_zero _ _⟩
  have h' : W.toAffine.Nonsingular (σ.symm x) (σ.symm y) := by
    rw [← WeierstrassCurve.Affine.map_nonsingular W.toAffine (f := (σ : k →+* k')) σ.injective]
    simpa using h
  refine ⟨.some _ _ h', ?_⟩
  exact Wave5.point_some_eq_some _ _ (by simp) (by simp)

/-- **Kernels on points under base change** along a field isomorphism. -/
theorem pointMap_eq_zero_iff_map (σ : k ≃+* k') {W W' : WeierstrassCurve k} [W.IsElliptic] [W'.IsElliptic]
    {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} (i : O.toSubalgebra ≃+* Hom W.toAffine W.toAffine)
    (J : Ideal O.toSubalgebra) (φ : Hom W.toAffine W'.toAffine)
    (h : ∀ P : W.toAffine.Point, φ.pointMap P = 0 ↔ ∀ a ∈ J, (i a).pointMap P = 0)
    (Q : (W.map (σ : k →+* k')).toAffine.Point) :
    (φ.map (σ : k →+* k')).pointMap Q = 0 ↔
      ∀ a ∈ J, ((i.trans (homMapRingEquiv σ W)) a).pointMap Q = 0 := by
  obtain ⟨P, rfl⟩ := mapAlong_surjective σ W Q
  have key : ∀ {V : WeierstrassCurve k} [V.IsElliptic] (g : Hom W.toAffine V.toAffine),
      (g.map (σ : k →+* k')).pointMap (P.mapAlong (σ : k →+* k') σ.injective) = 0 ↔ g.pointMap P = 0 := by
    intro V _ g
    rw [Hom.pointMap_map, ← Point.mapAlong_zero (σ : k →+* k') σ.injective,
      (Point.mapAlong_injective (σ : k →+* k') σ.injective).eq_iff]
  rw [key φ, h]
  exact forall₂_congr fun a _ ↦ (key (i a)).symm

/-- `Ell(R)` is carried to `Ell(R)` by a field isomorphism. -/
theorem map_mem_ellCMOver (σ : k ≃+* k') {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} {x : k}
    (hx : x ∈ EllCMOver k O) : σ x ∈ EllCMOver k' O := by
  obtain ⟨W, hW, hcm, rfl⟩ := hx
  exact ⟨W.map (σ : k →+* k'), inferInstance, hasCMBy_map σ W hcm, WeierstrassCurve.map_j W _⟩

theorem j_map_mem_ellCMOver (σ : k ≃+* k') {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}
    {W : WeierstrassCurve k} [W.IsElliptic] (hW : W.j ∈ EllCMOver k O) : (W.map (σ : k →+* k')).j ∈ EllCMOver k' O := by
  rw [WeierstrassCurve.map_j]; exact map_mem_ellCMOver σ hW

/-- The bijection `Ell_k(R) ≅ Ell_{k'}(R)` induced by a field isomorphism. -/
noncomputable def ellCMOverEquiv (σ : k ≃+* k') {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K) :
    EllCMOver k O ≃ EllCMOver k' O where
  toFun x := ⟨σ x, map_mem_ellCMOver σ x.2⟩
  invFun y := ⟨σ.symm y, map_mem_ellCMOver σ.symm y.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv y := Subtype.ext (σ.apply_symm_apply y)

end BaseChange

/-- **Proposition 12.21, corrected, over a field isomorphic to `ℂ`**: the instance of the named statement
`ClassGroupActionPrincipalNormalized` for an algebraically closed field `k` of characteristic zero with a field
isomorphism `k ≅ ℂ`. -/
theorem classGroupActionPrincipalNormalized_of_ringEquiv (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (σ : k ≃+* ℂ) (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (hTC : IsTotallyComplex K) (ι : K →+* k) :
    ∃ act : Pic O → EllCMOver k O → EllCMOver k O,
      (∀ (W W' : WeierstrassCurve.Affine k) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver k O) → (hW' : W'.j ∈ EllCMOver k O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  obtain ⟨actC, hC, hbij⟩ := exists_act_complex K O hK hTC ((σ : k →+* ℂ).comp ι)
  set e := ellCMOverEquiv σ O
  refine ⟨fun c x ↦ e.symm (actC c (e x)), ?_, fun x₀ ↦ e.symm.bijective.comp (hbij (e x₀))⟩
  intro W W' _ _ i hi I J hJI hW hW' φ hφ
  have h := hC (W.map (σ : k →+* ℂ)) (W'.map (σ : k →+* ℂ)) (i.trans (homMapRingEquiv σ W))
    (isNormalizedCM_map σ ι i hi) I J hJI (j_map_mem_ellCMOver σ hW) (j_map_mem_ellCMOver σ hW')
    (φ.map (σ : k →+* ℂ))
    (pointMap_eq_zero_iff_map σ i J φ (pointMap_eq_zero_iff_of_isAIsogeny O i J φ hφ))
  have e1 : e ⟨W.j, hW⟩ = ⟨(W.map (σ : k →+* ℂ)).j, j_map_mem_ellCMOver σ hW⟩ :=
    Subtype.ext (WeierstrassCurve.map_j W (σ : k →+* ℂ)).symm
  simp only
  rw [e1, h, Equiv.symm_apply_eq]
  exact Subtype.ext (WeierstrassCurve.map_j W' (σ : k →+* ℂ))

/-- **Proposition 12.21, corrected** (Milne; proof omitted in the book), for every algebraically closed field `k` of
characteristic zero with the cardinality of `ℂ` (such a field is isomorphic to `ℂ`, by Steinitz): `Cl(R)` acts simply
transitively on `Ell_k(R)`, compatibly with `𝔞`-isogenies for normalized complex multiplication. -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126), corrected, fields of the cardinality of C"]
theorem classGroupActionPrincipalNormalized_of_nonempty_equiv (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (hk : Nonempty (k ≃ ℂ)) (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (ι : K →+* k) :
    ∃ act : Pic O → EllCMOver k O → EllCMOver k O,
      (∀ (W W' : WeierstrassCurve.Affine k) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver k O) → (hW' : W'.j ∈ EllCMOver k O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  obtain ⟨τ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero hC ⟨hk.some.symm⟩
  exact classGroupActionPrincipalNormalized_of_ringEquiv k τ.symm K O hK hTC ι

end ModularFormsKB.Milne.Wave8
