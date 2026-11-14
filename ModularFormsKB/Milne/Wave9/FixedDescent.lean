import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Descent
import TauCeti.FieldTheory.IsAlgClosed.Automorphism
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.FixedField

/-!
# Descent of isogenies along extensions with fixed field the base

Tau Ceti descends isogenies along a Galois extension `K/F` (`TauCeti.Isogeny.existsUnique_map_eq_iff_galoisFixed`).
Its proof uses the Galois hypothesis only through the fixed-field property: an element of `K` fixed by every
automorphism of `K/F` lies in `F`. Tau Ceti's descent of rational functions
(`TauCeti.RatFunc.mem_range_of_forall_mapRingEquiv_eq`) needs nothing more. This file repeats the two descent steps
(function fields, then isogenies) under the fixed-field hypothesis alone, so that they apply to transcendental
extensions such as `F ⊆ L` with `F` algebraically closed of characteristic zero and `L` algebraically closed (where
the fixed-field property is Tau Ceti's `TauCeti.IsAlgClosed.mem_range_algebraMap_iff_fixed`).

The proofs follow Tau Ceti's `Affine/FunctionField/Galois/FixedField.lean`, `Affine/FunctionField/Galois/Descent.lean`
and `Isogeny/Descent.lean` line by line, with the fixed-field hypothesis in place of `IsGalois`.

## Items

- `ratFunc_mem_range_of_fixed`, `mem_range_functionFieldMap_of_fixed`: fixed rational functions and fixed functions
  on `W_K` come from `F`.
- `exists_functionFieldMap_of_equivariant`: descent of equivariant function-field maps.
- `exists_isogeny_map_eq_of_equivariant`: descent of isogenies whose function-field pullback is equivariant.
-/

open Polynomial
open scoped WeierstrassCurve RatFunc nonZeroDivisors

namespace ModularFormsKB.Milne.Wave9

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The fixed-field property of `K/F`: every element of `K` fixed by all automorphisms of `K/F` lies in `F`. -/
def FixedFieldIsBase (F K : Type*) [Field F] [Field K] [Algebra F K] : Prop :=
  ∀ c : K, (∀ σ : K ≃ₐ[F] K, σ c = c) → c ∈ Set.range (algebraMap F K)

/-- For `F` perfect and `K` algebraically closed, the fixed field of `Aut(K/F)` is `F` (Tau Ceti). -/
theorem fixedFieldIsBase_of_isAlgClosed [PerfectField F] [IsAlgClosed K] : FixedFieldIsBase F K :=
  fun c hc ↦ (TauCeti.IsAlgClosed.mem_range_algebraMap_iff_fixed c).mpr hc

/-- A rational function over `K` fixed by every coefficient automorphism of `K/F` comes from `F(X)`, when the fixed
field of `Aut(K/F)` is `F`. -/
theorem ratFunc_mem_range_of_fixed (hS : FixedFieldIsBase F K) (z : RatFunc K)
    (hz : ∀ σ : K ≃ₐ[F] K,
      RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (Polynomial.map_injective _ σ.injective)) z = z) :
    z ∈ Set.range (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap F K))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algebraMap F K).injective))) := by
  let : Algebra (RatFunc F) (RatFunc K) :=
    (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap F K))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algebraMap F K).injective))).toAlgebra
  have hpoly (p : F[X]) : algebraMap (RatFunc F) (RatFunc K) (algebraMap F[X] _ p) =
      algebraMap K[X] _ (p.map (algebraMap F K)) := by
    rw [RingHom.algebraMap_toAlgebra, RatFunc.coe_mapRingHom_eq_coe_map]
    simpa using RatFunc.map_apply_div (Polynomial.mapRingHom (algebraMap F K)) _ p 1
  have := TauCeti.RatFunc.isScalarTower_of_algebraMap_C (F := F) (K := K) fun c ↦ by
    rw [← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C, hpoly, Polynomial.map_C]
  have hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X := by
    rw [← RatFunc.algebraMap_X, hpoly, Polynomial.map_X, RatFunc.algebraMap_X]
  rw [← RingHom.algebraMap_toAlgebra (RatFunc.mapRingHom _ _)]
  refine TauCeti.RatFunc.mem_range_of_forall_mapRingEquiv_eq hX (S := Set.range AlgEquiv.toRingEquiv)
    (fun c hc ↦ hS c fun σ ↦ hc _ ⟨σ, rfl⟩) ?_
  rintro _ ⟨σ, rfl⟩
  simpa [TauCeti.RatFunc.coe_mapRingEquiv] using hz σ

variable (W W₁ W₂ : WeierstrassCurve F)

/-- **Fixed functions come from the ground field**, when the fixed field of `Aut(K/F)` is `F` (Tau Ceti's
`WeierstrassCurve.mem_range_functionFieldMap_iff_fixed` without the Galois hypothesis). -/
theorem mem_range_functionFieldMap_of_fixed (hS : FixedFieldIsBase F K) (z : (W⁄K).toAffine.FunctionField)
    (hz : ∀ σ : K ≃ₐ[F] K, functionFieldGaloisAction W σ z = z) :
    z ∈ Set.range (Affine.FunctionField.map W.toAffine (algebraMap F K)) := by
  let b := Affine.FunctionField.basis (W⁄K).toAffine (RatFunc K)
  have hcoeff (i : Fin 2) : b.repr z i ∈ Set.range
      (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap F K))
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (Polynomial.map_injective _ (algebraMap F K).injective))) := by
    apply ratFunc_mem_range_of_fixed hS (b.repr z i)
    intro σ
    rw [← functionFieldGaloisAction_basis_repr, hz σ]
  choose r hr using hcoeff
  let bF := Affine.FunctionField.basis W.toAffine (RatFunc F)
  have hb (i : Fin 2) :
      Affine.FunctionField.map W.toAffine (algebraMap F K) (bF i) = b i := by
    fin_cases i <;> simp [b, bF] <;> rfl
  refine ⟨∑ i : Fin 2, r i • bF i, ?_⟩
  simp only [map_sum, Algebra.smul_def, map_mul, Affine.FunctionField.map_algebraMap_ratFunc, hr, hb]
  exact b.sum_repr z

/-- **Descent of an equivariant function-field map** along an extension with fixed field the base (Tau Ceti's
`WeierstrassCurve.exists_functionFieldMap_of_galoisEquivariant` without the Galois hypothesis). -/
theorem exists_functionFieldMap_of_equivariant (hS : FixedFieldIsBase F K)
    (g : (W₂⁄K).toAffine.FunctionField →ₐ[K] (W₁⁄K).toAffine.FunctionField)
    (hg : ∀ (σ : K ≃ₐ[F] K) z,
      W₁.functionFieldGaloisAction σ (g z) = g (W₂.functionFieldGaloisAction σ z)) :
    ∃ f : W₂.toAffine.FunctionField →ₐ[F] W₁.toAffine.FunctionField,
      ∀ z, Affine.FunctionField.map W₁.toAffine (algebraMap F K) (f z) =
        g (Affine.FunctionField.map W₂.toAffine (algebraMap F K) z) := by
  classical
  let b₁ : W₁.toAffine.FunctionField →ₐ[F] (W₁⁄K).toAffine.FunctionField :=
    { toRingHom := Affine.FunctionField.map W₁.toAffine (algebraMap F K)
      commutes' := fun a ↦ (Affine.FunctionField.map_algebraMap ..).trans
        (IsScalarTower.algebraMap_apply F K (W₁⁄K).toAffine.FunctionField a).symm }
  let b₂ : W₂.toAffine.FunctionField →ₐ[F] (W₂⁄K).toAffine.FunctionField :=
    { toRingHom := Affine.FunctionField.map W₂.toAffine (algebraMap F K)
      commutes' := fun a ↦ (Affine.FunctionField.map_algebraMap ..).trans
        (IsScalarTower.algebraMap_apply F K (W₂⁄K).toAffine.FunctionField a).symm }
  let r : W₂.toAffine.FunctionField →ₐ[F] (W₁⁄K).toAffine.FunctionField :=
    (g.restrictScalars F).comp b₂
  have hr (z : W₂.toAffine.FunctionField) : r z ∈ b₁.fieldRange.toSubalgebra := by
    apply mem_range_functionFieldMap_of_fixed W₁ hS
    intro σ
    change W₁.functionFieldGaloisAction σ
        (g (Affine.FunctionField.map W₂.toAffine (algebraMap F K) z)) =
      g (Affine.FunctionField.map W₂.toAffine (algebraMap F K) z)
    exact (hg σ _).trans (congrArg g (functionFieldGaloisAction_map_algebraMap W₂ σ z))
  let f : W₂.toAffine.FunctionField →ₐ[F] W₁.toAffine.FunctionField :=
    (AlgEquiv.ofInjectiveField b₁).symm.toAlgHom.comp (r.codRestrict _ hr)
  have hf (z : W₂.toAffine.FunctionField) :
      Affine.FunctionField.map W₁.toAffine (algebraMap F K) (f z) =
        g (Affine.FunctionField.map W₂.toAffine (algebraMap F K) z) := by
    change b₁ ((AlgEquiv.ofInjectiveField b₁).symm ⟨r z, hr z⟩) = r z
    simpa only [AlgEquiv.ofInjectiveField, AlgEquiv.ofInjective_apply] using
      congrArg Subtype.val ((AlgEquiv.ofInjectiveField b₁).apply_symm_apply ⟨r z, hr z⟩)
  exact ⟨f, hf⟩

/-- **Descent of an isogeny with equivariant pullback** along an extension with fixed field the base (the backward
direction of Tau Ceti's `TauCeti.Isogeny.existsUnique_map_eq_iff_galoisEquivariant`, without the Galois
hypothesis). -/
theorem exists_isogeny_map_eq_of_equivariant (hS : FixedFieldIsBase F K)
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine)
    (hφ : ∀ (σ : K ≃ₐ[F] K) z,
      W₁.functionFieldGaloisAction σ (φ.fieldPullback z) =
        φ.fieldPullback (W₂.functionFieldGaloisAction σ z)) :
    ∃ ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ := by
  obtain ⟨f, hf⟩ := exists_functionFieldMap_of_equivariant W₁ W₂ hS φ.fieldPullback hφ
  let p : CoordinatePullback W₁.toAffine W₂.toAffine :=
    f.comp (IsScalarTower.toAlgHom F W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField)
  have hmap : p.map (algebraMap F K) = φ.pullback := by
    apply CoordinateRing.algHom_ext
    · rw [CoordinatePullback.map_of_X]
      change Affine.FunctionField.map W₁.toAffine (algebraMap F K)
          (f (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
            (AdjoinRoot.of W₂.toAffine.polynomial Polynomial.X))) =
        φ.pullback (AdjoinRoot.of (W₂⁄K).toAffine.polynomial Polynomial.X)
      rw [hf, Affine.FunctionField.map_algebraMap_coordinateRing, CoordinateRing.map_of_X]
      exact φ.fieldPullback_algebraMap _
    · rw [CoordinatePullback.map_root]
      change Affine.FunctionField.map W₁.toAffine (algebraMap F K)
          (f (algebraMap W₂.toAffine.CoordinateRing W₂.toAffine.FunctionField
            (AdjoinRoot.root W₂.toAffine.polynomial))) =
        φ.pullback (AdjoinRoot.root (W₂⁄K).toAffine.polynomial)
      rw [hf, Affine.FunctionField.map_algebraMap_coordinateRing, CoordinateRing.map_root]
      exact φ.fieldPullback_algebraMap _
  have hp : p.MapsInfinity := (CoordinatePullback.mapsInfinity_map_iff p _).mp
    (hmap.symm ▸ φ.mapsInfinity)
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Isogeny.ext
  rw [map_pullback]
  exact hmap

end ModularFormsKB.Milne.Wave9
