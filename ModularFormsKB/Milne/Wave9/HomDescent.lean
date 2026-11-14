import ModularFormsKB.Milne.Wave9.FixedDescent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed

/-!
# Morphisms of elliptic curves do not change under algebraically closed base change

Let `F ⊆ L` be algebraically closed fields of characteristic zero and `W₁`, `W₂` elliptic curves over `F`. Every
morphism `W₁ ⊗ L → W₂ ⊗ L` is the base change of a unique morphism `W₁ → W₂` (`hom_map_bijective`). With
injectivity (Tau Ceti `TauCeti.Isogeny.Hom.map_injective`), base change identifies `Hom(W₁, W₂)` over `F` and over
`L`; in particular `End(W)` does not grow (`endMapRingEquiv`). This is the rigidity behind the Lefschetz principle
for complex multiplication used in Milne's Section 12 (pdf p. 126), and the descent step named in LE-MF-0210.

Proof. Let `h` be a morphism over `L` and `σ` an automorphism of `L` over `F`. The conjugate of `h` by `σ`, the base
change `h ⊗_σ L` read on `W₁ ⊗ L` again (`(W ⊗ L) ⊗_σ L = W ⊗ L`), acts on the torsion points as `h` does: torsion
points of `W ⊗ L` are defined over `F` (Tau Ceti `WeierstrassCurve.torsionMapAlong_bijective`), so `σ` fixes them and
their images. Two morphisms agreeing on all prime torsion are equal (Tau Ceti
`TauCeti.Isogeny.Hom.ext_pointMap_of_prime_zsmul_eq_zero`). Hence the pullbacks `h^*x`, `h^*y` are fixed by every
`σ`, the pullback is equivariant, and it descends (`exists_isogeny_map_eq_of_equivariant`, the fixed field of
`Aut(L/F)` being `F`, Tau Ceti `TauCeti.IsAlgClosed.mem_range_algebraMap_iff_fixed`).
-/

open Polynomial
open scoped WeierstrassCurve

namespace ModularFormsKB.Milne.Wave9

open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny

section Cast

variable {L : Type*} [Field L]

/-- Transport of function-field elements along an equality of curves, as a ring homomorphism. -/
noncomputable def ffCast {V V' : WeierstrassCurve L} (e : V = V') :
    V.toAffine.FunctionField →+* V'.toAffine.FunctionField :=
  e ▸ RingHom.id _

theorem ffCast_apply {V V' : WeierstrassCurve L} (e : V = V') (z : V.toAffine.FunctionField) :
    ffCast e z = cast (congrArg (fun V : WeierstrassCurve L ↦ V.toAffine.FunctionField) e) z := by
  subst e; rfl

theorem ffCast_algebraMap {V V' : WeierstrassCurve L} (e : V = V') (c : L) :
    ffCast e (algebraMap L V.toAffine.FunctionField c) = algebraMap L V'.toAffine.FunctionField c := by
  subst e; rfl

theorem ffCast_genericX {V V' : WeierstrassCurve L} (e : V = V') :
    ffCast e V.toAffine.genericX = V'.toAffine.genericX := by
  subst e; rfl

theorem ffCast_genericY {V V' : WeierstrassCurve L} (e : V = V') :
    ffCast e V.toAffine.genericY = V'.toAffine.genericY := by
  subst e; rfl

theorem cast_coordinateRing_mk {V V' : WeierstrassCurve L} (e : V = V') (p : L[X][X]) :
    cast (congrArg (fun V : WeierstrassCurve L ↦ V.toAffine.CoordinateRing) e) (CoordinateRing.mk V.toAffine p) =
      CoordinateRing.mk V'.toAffine p := by
  subst e; rfl

/-- A morphism transported along equalities of its curves acts on transported coordinate functions by transport. -/
theorem toNonUnitalAlgHom_cast {V₁ V₁' V₂ V₂' : WeierstrassCurve L} (e₁ : V₁ = V₁') (e₂ : V₂ = V₂')
    {h : Hom V₁.toAffine V₂.toAffine} {h' : Hom V₁'.toAffine V₂'.toAffine} (hh : HEq h h')
    (z : V₂.toAffine.CoordinateRing) :
    h'.toNonUnitalAlgHom (cast (congrArg (fun V : WeierstrassCurve L ↦ V.toAffine.CoordinateRing) e₂) z) =
      ffCast e₁ (h.toNonUnitalAlgHom z) := by
  subst e₁ e₂
  cases eq_of_heq hh
  rfl

end Cast

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- The coefficient action of `σ ∈ Aut(L/F)` on the function field of `W ⊗ L` is `FunctionField.map σ` followed by
the identification `(W ⊗ L) ⊗_σ L = W ⊗ L`. -/
theorem ffCast_map_eq_functionFieldGaloisAction (W : WeierstrassCurve F) (σ : L ≃ₐ[F] L)
    (z : (W⁄L).toAffine.FunctionField) :
    ffCast (W.map_baseChange σ.toAlgHom) (Affine.FunctionField.map (W⁄L).toAffine (σ.toAlgHom : L →+* L) z) =
      W.functionFieldGaloisAction σ z := by
  have h : (ffCast (W.map_baseChange σ.toAlgHom)).comp
      (Affine.FunctionField.map (W⁄L).toAffine (σ.toAlgHom : L →+* L)) =
      (W.functionFieldGaloisAction σ).toRingHom := by
    apply Affine.FunctionField.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Affine.FunctionField.map_algebraMap, ffCast_algebraMap,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, functionFieldGaloisAction_algebraMap]
      rfl
    · simp only [RingHom.comp_apply, Affine.FunctionField.map_genericX, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, functionFieldGaloisAction_genericX]
      exact ffCast_genericX _
    · simp only [RingHom.comp_apply, Affine.FunctionField.map_genericY, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, functionFieldGaloisAction_genericY]
      exact ffCast_genericY _
  exact RingHom.congr_fun h z

variable [IsAlgClosed F] [CharZero F] [IsAlgClosed L] [DecidableEq F] [DecidableEq L]

/-- A torsion point of `W ⊗ L` is defined over `F`, when `F` is algebraically closed of characteristic zero. -/
theorem exists_mapAlong_eq_of_zsmul_eq_zero (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    {P : (W⁄L).toAffine.Point} (hP : n • P = 0) :
    ∃ Q : W.toAffine.Point, Q.mapAlong (algebraMap F L) (algebraMap F L).injective = P := by
  have hnF : (n : F) ≠ 0 := Int.cast_ne_zero.mpr hn
  obtain ⟨S, hS⟩ := (W.torsionMapAlong_bijective (algebraMap F L) hnF).2
    ⟨P, (Submodule.mem_torsionBy_iff _ _).mpr hP⟩
  refine ⟨S, ?_⟩
  rw [← W.coe_torsionMapAlong_apply, hS]

/-- An automorphism of `L` over `F` fixes the torsion points of `W ⊗ L`. -/
theorem map_eq_self_of_zsmul_eq_zero (W : WeierstrassCurve F) [W.IsElliptic] (σ : L ≃ₐ[F] L) {n : ℤ} (hn : n ≠ 0)
    {P : (W⁄L).toAffine.Point} (hP : n • P = 0) : Affine.Point.map σ.toAlgHom P = P := by
  obtain ⟨Q, rfl⟩ := exists_mapAlong_eq_of_zsmul_eq_zero W hn hP
  rcases Q with _ | ⟨x, y, h⟩
  · exact map_zero _
  · rw [WeierstrassCurve.Affine.Point.mapAlong_some]
    erw [Affine.Point.map_some]
    congr 1 <;> exact σ.commutes _

/-- **Rigidity under conjugation**: for `σ ∈ Aut(L/F)`, the base change of a morphism `h : W₁ ⊗ L → W₂ ⊗ L` along
`σ` is `h` again, after `(W ⊗ L) ⊗_σ L = W ⊗ L`. -/
theorem hom_map_heq (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    (h : Hom (W₁⁄L).toAffine (W₂⁄L).toAffine) (σ : L ≃ₐ[F] L) :
    HEq (h.map (σ.toAlgHom : L →+* L)) h := by
  set g : L →+* L := (σ.toAlgHom : L →+* L) with hg
  have e₁ : (W₁⁄L).map g = W₁⁄L := W₁.map_baseChange σ.toAlgHom
  have e₂ : (W₂⁄L).map g = W₂⁄L := W₂.map_baseChange σ.toAlgHom
  let h' : Hom (W₁⁄L).toAffine (W₂⁄L).toAffine := cast (by rw [e₁, e₂]) (h.map g)
  have hh : HEq (h.map g) h' := (cast_heq _ _).symm
  suffices h' = h from hh.trans (heq_of_eq this)
  apply Hom.ext_pointMap_of_prime_zsmul_eq_zero
  intro p hp _ P hP
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hPfix := map_eq_self_of_zsmul_eq_zero W₁ σ hp0 hP
  have hhP : (p : ℤ) • h.pointMap P = 0 := by
    rw [← Hom.pointMapHom_apply, ← map_zsmul, hP, map_zero]
  have hhfix := map_eq_self_of_zsmul_eq_zero W₂ σ hp0 hhP
  calc h'.pointMap P = h'.pointMap (Affine.Point.map σ.toAlgHom P) := by rw [hPfix]
    _ = h'.pointMap (cast (congrArg (fun V : WeierstrassCurve L ↦ V.toAffine.Point) e₁)
          (P.mapAlong g g.injective)) := by rw [Affine.Point.map_eq_cast_mapAlong]
    _ = cast (congrArg (fun V : WeierstrassCurve L ↦ V.toAffine.Point) e₂)
          ((h.map g).pointMap (P.mapAlong g g.injective)) := Hom.pointMap_cast e₁ e₂ hh _
    _ = cast (congrArg (fun V : WeierstrassCurve L ↦ V.toAffine.Point) e₂)
          ((h.pointMap P).mapAlong g g.injective) := by rw [Hom.pointMap_map]
    _ = Affine.Point.map σ.toAlgHom (h.pointMap P) := (Affine.Point.map_eq_cast_mapAlong _ _).symm
    _ = h.pointMap P := hhfix

/-- The pullback of a coordinate function along a morphism `W₁ ⊗ L → W₂ ⊗ L` is fixed by `Aut(L/F)`. -/
theorem functionFieldGaloisAction_toNonUnitalAlgHom (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    (h : Hom (W₁⁄L).toAffine (W₂⁄L).toAffine) (σ : L ≃ₐ[F] L) (p : F[X][X]) :
    W₁.functionFieldGaloisAction σ
        (h.toNonUnitalAlgHom (CoordinateRing.mk (W₂⁄L).toAffine (p.map (mapRingHom (algebraMap F L))))) =
      h.toNonUnitalAlgHom (CoordinateRing.mk (W₂⁄L).toAffine (p.map (mapRingHom (algebraMap F L)))) := by
  set g : L →+* L := (σ.toAlgHom : L →+* L) with hg
  have e₁ : (W₁⁄L).map g = W₁⁄L := W₁.map_baseChange σ.toAlgHom
  have e₂ : (W₂⁄L).map g = W₂⁄L := W₂.map_baseChange σ.toAlgHom
  set z := CoordinateRing.mk (W₂⁄L).toAffine (p.map (mapRingHom (algebraMap F L)))
  have hz : cast (congrArg (fun V : WeierstrassCurve L ↦ V.toAffine.CoordinateRing) e₂)
      (CoordinateRing.map (W₂⁄L).toAffine g z) = z := by
    have hc : (mapRingHom g).comp (mapRingHom (algebraMap F L)) = mapRingHom (algebraMap F L) := by
      rw [Polynomial.mapRingHom_comp]
      congr 1
      exact σ.toAlgHom.comp_algebraMap
    rw [CoordinateRing.map_mk, cast_coordinateRing_mk e₂, Polynomial.map_map, hc]
  rw [← ffCast_map_eq_functionFieldGaloisAction, ← Hom.map_coordinateRingMap,
    ← toNonUnitalAlgHom_cast e₁ e₂ (hom_map_heq W₁ W₂ h σ), hz]

/-- **Morphisms descend**: every morphism `W₁ ⊗ L → W₂ ⊗ L` is the base change of a morphism `W₁ → W₂`, for
`F ⊆ L` algebraically closed of characteristic zero. -/
theorem exists_hom_map_eq (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    (h : Hom (W₁⁄L).toAffine (W₂⁄L).toAffine) :
    ∃ g : Hom W₁.toAffine W₂.toAffine, g.map (algebraMap F L) = h := by
  rcases Hom.eq_zero_or_exists_ofIsogeny h with rfl | ⟨φ, rfl⟩
  · exact ⟨0, Hom.zero_map _⟩
  have hfix := fun (p : F[X][X]) (σ : L ≃ₐ[F] L) ↦
    functionFieldGaloisAction_toNonUnitalAlgHom W₁ W₂ (Hom.ofIsogeny φ) σ p
  have hφ : ∀ (σ : L ≃ₐ[F] L) z,
      W₁.functionFieldGaloisAction σ (φ.fieldPullback z) =
        φ.fieldPullback (W₂.functionFieldGaloisAction σ z) := by
    intro σ z
    have key : (W₁.functionFieldGaloisAction σ).toRingHom.comp φ.fieldPullback.toRingHom =
        φ.fieldPullback.toRingHom.comp (W₂.functionFieldGaloisAction σ).toRingHom := by
      apply Affine.FunctionField.ringHom_ext
      · intro a
        simp [functionFieldGaloisAction_algebraMap]
      · show (W₁.functionFieldGaloisAction σ) (φ.fieldPullback (W₂⁄L).toAffine.genericX) =
          φ.fieldPullback ((W₂.functionFieldGaloisAction σ) (W₂⁄L).toAffine.genericX)
        rw [functionFieldGaloisAction_genericX, Affine.genericX_def, Isogeny.fieldPullback_algebraMap]
        simpa using hfix (C X) σ
      · show (W₁.functionFieldGaloisAction σ) (φ.fieldPullback (W₂⁄L).toAffine.genericY) =
          φ.fieldPullback ((W₂.functionFieldGaloisAction σ) (W₂⁄L).toAffine.genericY)
        rw [functionFieldGaloisAction_genericY, Affine.genericY_def, Isogeny.fieldPullback_algebraMap]
        simpa using hfix X σ
    exact RingHom.congr_fun key z
  obtain ⟨ψ, hψ⟩ := exists_isogeny_map_eq_of_equivariant W₁ W₂ fixedFieldIsBase_of_isAlgClosed φ hφ
  exact ⟨Hom.ofIsogeny ψ, by rw [Hom.ofIsogeny_map]; exact congrArg Hom.ofIsogeny hψ⟩

/-- **Base change is a bijection on morphisms** between curves over `F`, for `F ⊆ L` algebraically closed of
characteristic zero. -/
theorem hom_map_bijective (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] :
    Function.Bijective (fun g : Hom W₁.toAffine W₂.toAffine ↦ g.map (algebraMap F L)) :=
  ⟨Hom.map_injective _, fun h ↦ exists_hom_map_eq W₁ W₂ h⟩

end ModularFormsKB.Milne.Wave9
