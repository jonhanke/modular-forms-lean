import ModularFormsKB.Milne.Ch8.EllipticModuli
import Mathlib.RingTheory.LaurentSeries

/-!
# Pure algebra of the Legendre line and its double cover

Algebraic lemmas about `LegendreRing k = k[λ, (λ(λ-1))⁻¹]` and `LegendreSqrtRing k = k[s, (s(s²-1))⁻¹]`
(the double cover `λ = s²`): `λ³` is not a square in `LegendreRing k`, the map `λ ↦ s²`, lifting of
`k`-points over an algebraically closed field, and that both rings are affine `k`-algebras.
-/

open Polynomial

namespace ModularFormsKB.Milne

noncomputable section

universe u

variable {k : Type u} [Field k]

variable (k) in
/-- The coordinate `λ` of the Legendre line. -/
abbrev legendreLambda : LegendreRing k := algebraMap (Polynomial k) (LegendreRing k) Polynomial.X

/-! ### `λ³` is not a square -/

private lemma isUnit_laurent_X_mul_sub_one :
    IsUnit (Polynomial.aeval (HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k)
      (Polynomial.X * (Polynomial.X - 1) : Polynomial k)) := by
  have hT : IsUnit (HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k) := by
    refine IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : k)) ?_
    rw [HahnSeries.single_mul_single]; simp
  have h1 : IsUnit (1 - PowerSeries.X : PowerSeries k) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  have h2 : IsUnit (HahnSeries.ofPowerSeries ℤ k (1 - PowerSeries.X)) := h1.map _
  have h3 : (HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k) - 1 =
      -(HahnSeries.ofPowerSeries ℤ k (1 - PowerSeries.X)) := by
    have : HahnSeries.ofPowerSeries ℤ k (1 - PowerSeries.X) =
        1 - (HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k) := by
      rw [map_sub, map_one, HahnSeries.ofPowerSeries_X]
    rw [this]; ring
  simp only [map_mul, map_sub, Polynomial.aeval_X, map_one]
  refine hT.mul ?_
  rw [h3]; exact h2.neg

/-- The ring map `LegendreRing k → k((T))`, `λ ↦ T`. -/
private def legendreToLaurent : LegendreRing k →ₐ[k] LaurentSeries k :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k))
    (f := Polynomial.aeval (HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k))
    (by
      rintro ⟨y, n, rfl⟩
      simpa using (isUnit_laurent_X_mul_sub_one (k := k)).pow n)

private lemma legendreToLaurent_lambda :
    legendreToLaurent (legendreLambda k) = (HahnSeries.single (1 : ℤ) (1 : k) : LaurentSeries k) := by
  unfold legendreToLaurent legendreLambda
  rw [IsLocalization.liftAlgHom_apply]
  simp [IsLocalization.lift_eq]

theorem not_exists_sq_eq_legendreLambda_pow_three :
    ¬ ∃ w : LegendreRing k, w ^ 2 = legendreLambda k ^ 3 := by
  rintro ⟨w, hw⟩
  have h := congrArg (fun z => (legendreToLaurent z).order) hw
  simp only [map_pow, legendreToLaurent_lambda, HahnSeries.order_pow] at h
  rw [HahnSeries.order_single one_ne_zero] at h
  simp at h
  omega

/-! ### The double cover -/

variable (k) in
/-- The coordinate ring `k[s, (s(s²-1))⁻¹]` of the double cover `λ = s²`. -/
abbrev LegendreSqrtRing : Type u :=
  Localization.Away (Polynomial.X * (Polynomial.X ^ 2 - 1) : Polynomial k)

variable (k) in
/-- The coordinate `s` of the double cover. -/
abbrev legendreSqrt : LegendreSqrtRing k :=
  algebraMap (Polynomial k) (LegendreSqrtRing k) Polynomial.X

private lemma isUnit_legendreSqrt : IsUnit (legendreSqrt k) := by
  have : IsUnit (algebraMap (Polynomial k) (LegendreSqrtRing k)
      (Polynomial.X * (Polynomial.X ^ 2 - 1))) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at this
  exact isUnit_of_mul_isUnit_left this

private lemma isUnit_legendreSqrt_sq_sub_one : IsUnit (legendreSqrt k ^ 2 - 1) := by
  have : IsUnit (algebraMap (Polynomial k) (LegendreSqrtRing k)
      (Polynomial.X * (Polynomial.X ^ 2 - 1))) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at this
  have := isUnit_of_mul_isUnit_right this
  simpa using this

variable (k) in
/-- The `k`-algebra map `LegendreRing k → LegendreSqrtRing k`, `λ ↦ s²`. -/
def legendreSqrtMap : LegendreRing k →ₐ[k] LegendreSqrtRing k :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k))
    (f := Polynomial.aeval (legendreSqrt k ^ 2))
    (by
      rintro ⟨y, n, rfl⟩
      have : IsUnit (Polynomial.aeval (legendreSqrt k ^ 2)
          (Polynomial.X * (Polynomial.X - 1) : Polynomial k)) := by
        simp only [map_mul, map_sub, Polynomial.aeval_X, map_one]
        have h : legendreSqrt k ^ 2 = legendreSqrt k * legendreSqrt k := sq _
        exact (isUnit_legendreSqrt.pow 2).mul isUnit_legendreSqrt_sq_sub_one
      simpa using this.pow n)

theorem legendreSqrtMap_lambda :
    legendreSqrtMap k (legendreLambda k) = legendreSqrt k ^ 2 := by
  unfold legendreSqrtMap legendreLambda
  rw [IsLocalization.liftAlgHom_apply]
  simp [IsLocalization.lift_eq]

/-! ### Lifting points -/

theorem exists_algHom_comp_legendreSqrtMap [IsAlgClosed k] (φ : LegendreRing k →ₐ[k] k) :
    ∃ ψ : LegendreSqrtRing k →ₐ[k] k, ψ.comp (legendreSqrtMap k) = φ := by
  have hu : IsUnit (φ (algebraMap (Polynomial k) (LegendreRing k)
      (Polynomial.X * (Polynomial.X - 1)))) :=
    (IsLocalization.Away.algebraMap_isUnit _).map φ
  simp only [map_mul, map_sub, map_one] at hu
  have hu' := hu.ne_zero
  have hl0 : φ (legendreLambda k) ≠ 0 := left_ne_zero_of_mul hu'
  have hl1 : φ (legendreLambda k) - 1 ≠ 0 := right_ne_zero_of_mul hu'
  obtain ⟨s0, hs0⟩ := IsAlgClosed.exists_pow_nat_eq (φ (legendreLambda k)) (n := 2) (by norm_num)
  have hs00 : s0 ≠ 0 := fun h => hl0 (by rw [← hs0, h]; simp)
  have hs01 : s0 ^ 2 - 1 ≠ 0 := by rw [hs0]; exact hl1
  have hunit : ∀ y ∈ Submonoid.powers (Polynomial.X * (Polynomial.X ^ 2 - 1) : Polynomial k),
      IsUnit (Polynomial.aeval s0 y) := by
    rintro y ⟨n, rfl⟩
    simp only [map_pow, map_mul, map_sub, Polynomial.aeval_X, map_one]
    exact IsUnit.pow _ (isUnit_iff_ne_zero.mpr (mul_ne_zero hs00 hs01))
  let ψ : LegendreSqrtRing k →ₐ[k] k := IsLocalization.liftAlgHom
    (M := Submonoid.powers (Polynomial.X * (Polynomial.X ^ 2 - 1) : Polynomial k))
    (f := Polynomial.aeval s0) (fun y => hunit y y.2)
  have hψ : ψ (legendreSqrt k) = s0 := by
    show ψ (algebraMap (Polynomial k) (LegendreSqrtRing k) Polynomial.X) = s0
    simp only [ψ, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    simp
  refine ⟨ψ, ?_⟩
  apply IsLocalization.algHom_ext (Submonoid.powers (Polynomial.X * (Polynomial.X - 1) : Polynomial k))
  apply Polynomial.algHom_ext
  have h1 : ψ (legendreSqrtMap k (legendreLambda k)) = φ (legendreLambda k) := by
    rw [legendreSqrtMap_lambda, map_pow, hψ, hs0]
  exact h1

/-! ### Affine algebras -/

theorem isAffineAlgebra_of_isDomain [IsAlgClosed k] (A : Type u) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] : IsAffineAlgebra k A := by
  refine ⟨inferInstance, ?_⟩
  have hb : Function.Bijective (algebraMap k (AlgebraicClosure k)) :=
    ⟨(algebraMap k (AlgebraicClosure k)).injective,
      IsSepClosed.algebraMap_surjective k _⟩
  let e : k ≃ₐ[k] AlgebraicClosure k := AlgEquiv.ofBijective (Algebra.ofId k _) hb
  let f := (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : A ≃ₐ[k] A)).trans
    (Algebra.TensorProduct.lid k A)
  exact isReduced_of_injective f.toRingEquiv.toRingHom f.injective

theorem isAffineAlgebra_legendreRing [IsAlgClosed k] : IsAffineAlgebra k (LegendreRing k) := by
  have : Algebra.FiniteType k (LegendreRing k) :=
    Algebra.FiniteType.trans (S := Polynomial k) inferInstance
      (inferInstance)
  have : IsDomain (LegendreRing k) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
      (mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_sub_C_ne_zero 1)))
  exact isAffineAlgebra_of_isDomain _

theorem isAffineAlgebra_legendreSqrtRing [IsAlgClosed k] :
    IsAffineAlgebra k (LegendreSqrtRing k) := by
  have : Algebra.FiniteType k (LegendreSqrtRing k) :=
    Algebra.FiniteType.trans (S := Polynomial k) inferInstance
      (inferInstance)
  have : IsDomain (LegendreSqrtRing k) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
      (mul_ne_zero Polynomial.X_ne_zero (by
        intro h
        have := congrArg (Polynomial.eval 0) h
        simp at this)))
  exact isAffineAlgebra_of_isDomain _

end

end ModularFormsKB.Milne
