import ModularFormsKB.Milne.Ch8.LegendreAlgebra
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Affine varieties from reduced finitely generated algebras and from smooth affine schemes

Over an algebraically closed field $k$:

- a reduced finitely generated $k$-algebra is an affine $k$-algebra in Milne's sense (`isAffineAlgebra_of_isReduced`;
  $k = \bar k$, so geometric reducedness is reducedness);
- an affine scheme $X$ with a morphism $f : X \to \operatorname{Spec} k$ of finite type with $X$ reduced is an affine
  variety, through $X \cong \operatorname{Spec} \Gamma(X)$ (`isAffineVariety_of_isAffine`); this applies to smooth
  $f$ (`isAffineVariety_of_smooth`, Tau Ceti's `isReduced_of_smooth`).
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ModularFormsKB.Milne

variable {k : Type u} [Field k]

theorem isAffineAlgebra_of_isReduced [IsAlgClosed k] (A : Type u) [CommRing A] [_root_.IsReduced A]
    [Algebra k A] [Algebra.FiniteType k A] : IsAffineAlgebra k A := by
  refine ⟨inferInstance, ?_⟩
  have hb : Function.Bijective (algebraMap k (AlgebraicClosure k)) :=
    ⟨(algebraMap k (AlgebraicClosure k)).injective,
      IsSepClosed.algebraMap_surjective k _⟩
  let e : k ≃ₐ[k] AlgebraicClosure k := AlgEquiv.ofBijective (Algebra.ofId k _) hb
  let f := (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : A ≃ₐ[k] A)).trans
    (Algebra.TensorProduct.lid k A)
  exact isReduced_of_injective f.toRingEquiv.toRingHom f.injective

/-- The $k$-algebra structure on $\Gamma(X)$ of a scheme over $\operatorname{Spec} k$. -/
def gammaAlgHom {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop).hom

theorem toSpecΓ_specMap_gammaAlgHom {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (gammaAlgHom f)) = f := by
  rw [gammaAlgHom, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc]
  convert Category.comp_id f
  simp

theorem isAffineVariety_of_isAffine [IsAlgClosed k] {X : Scheme.{u}} [IsAffine X] [IsReduced X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] : IsAffineVariety k f := by
  let : Algebra k Γ(X, ⊤) := (gammaAlgHom f).toAlgebra
  have hft : Algebra.FiniteType k Γ(X, ⊤) := by
    have h := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp ‹LocallyOfFiniteType f›
    have h' : (gammaAlgHom f).FiniteType := by
      rw [gammaAlgHom, CommRingCat.hom_comp]
      exact RingHom.FiniteType.comp h (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
    exact h'
  refine ⟨Γ(X, ⊤), inferInstance, inferInstance, isAffineAlgebra_of_isReduced _, X.isoSpec, ?_⟩
  rw [Scheme.isoSpec_hom]
  exact toSpecΓ_specMap_gammaAlgHom f

theorem isAffineVariety_of_smooth [IsAlgClosed k] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] : IsAffineVariety k f := by
  have hsm := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp ‹Smooth f›
  let : Algebra k Γ(X, ⊤) := (gammaAlgHom f).toAlgebra
  have : Algebra.Smooth k Γ(X, ⊤) := by
    have h' : (gammaAlgHom f).Smooth := by
      rw [gammaAlgHom, CommRingCat.hom_comp]
      exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.bijective) hsm
    exact h'
  have : _root_.IsReduced Γ(X, ⊤) := TauCeti.isReduced_of_smooth k _
  have : IsReduced X := isReduced_of_isAffine_isReduced X
  exact isAffineVariety_of_isAffine f

theorem finiteType_gammaAlgHom {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] : @Algebra.FiniteType k Γ(X, ⊤) _ _ (gammaAlgHom f).toAlgebra := by
  let : Algebra k Γ(X, ⊤) := (gammaAlgHom f).toAlgebra
  have h := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp ‹LocallyOfFiniteType f›
  have h' : (gammaAlgHom f).FiniteType := by
    rw [gammaAlgHom, CommRingCat.hom_comp]
    exact RingHom.FiniteType.comp h (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  exact h'

theorem isReduced_gamma_of_smooth {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    _root_.IsReduced Γ(X, ⊤) := by
  have hsm := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp ‹Smooth f›
  let : Algebra k Γ(X, ⊤) := (gammaAlgHom f).toAlgebra
  have : Algebra.Smooth k Γ(X, ⊤) := by
    have h' : (gammaAlgHom f).Smooth := by
      rw [gammaAlgHom, CommRingCat.hom_comp]
      exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.bijective) hsm
    exact h'
  exact TauCeti.isReduced_of_smooth k _

end ModularFormsKB.Milne
