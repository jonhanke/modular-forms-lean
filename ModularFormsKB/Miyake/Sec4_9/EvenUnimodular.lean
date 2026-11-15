import ModularFormsKB.Citation
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.EvenUnimodular
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Gram

/-!
# Miyake Corollary 4.9.6: even unimodular Gram matrices exist exactly in ranks divisible by 8

Miyake, *Modular Forms* (Springer 1989), Corollary 4.9.6, p. 193: *assume that `r` is even. Then
there exists a positive definite symmetric matrix `A` in `M_r(ℤ)` satisfying (i) `det A = 1` and
(ii) all the diagonal components of `A` and `A⁻¹` are even, if and only if `r ≡ 0 mod 8`.*

Miyake proves the "only if" part from the transformation formula of the theta series
(Corollary 4.9.5 (3)) and the "if" part with an explicit rank-8 matrix (Minkowski's). Here the
statement is a bridge to Tau Ceti's lattice theorem
`TauCeti.IntegralLattice.exists_isEven_isUnimodular_isPosDef_iff` (Milgram's formula for the
"only if" part, the lattice `E₈^k` for the "if" part): a matrix `A` as in the corollary is the Gram
matrix of a positive definite even unimodular lattice on `ℚ^r`, and conversely.

Conventions. Indices are `Fin r` (0-based). `A⁻¹` is the inverse in `M_r(ℤ)` (Mathlib's
`Matrix.inv`, which is the adjugate when `det A = 1`), so "the diagonal components of `A⁻¹` are
even" is a statement about integers. Positive definiteness is that of `A` cast to real matrices.

The hypothesis "`r` even" is not needed: `exists_isEvenUnimodularGram_iff` holds for every `r`
(both sides fail for odd `r`), and `corollary_4_9_6` is Miyake's statement.
-/

open Matrix

namespace ModularFormsKB.Miyake.Sec4_9

/-- **Miyake's conditions of Corollary 4.9.6** on an integer matrix `A` of size `r`: `A` is
symmetric and positive definite, (i) `det A = 1`, and (ii) the diagonal components of `A` and of
`A⁻¹` are even. -/
def IsEvenUnimodularGram {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) : Prop :=
  A.IsSymm ∧ (A.map (Int.cast : ℤ → ℝ)).PosDef ∧ A.det = 1 ∧ (∀ i, Even (A i i)) ∧
    ∀ i, Even (A⁻¹ i i)

/-- For a symmetric integer matrix with even diagonal, `A[v] = vᵀ A v` is even for every integer
vector `v`. -/
theorem even_dotProduct_mulVec_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℤ} (hA : A.IsSymm) (hd : ∀ i, Even (A i i)) (v : ι → ℤ) :
    Even (v ⬝ᵥ A *ᵥ v) := by
  classical
  -- Write `A = B + Bᵀ` with `B` the upper triangle and half the diagonal; then `A[v] = 2 B[v]`.
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let B : Matrix ι ι ℤ := fun i j ↦ if i < j then A i j else if i = j then A i i / 2 else 0
  have hAB : A = B + Bᵀ := by
    ext i j
    show A i j = B i j + B j i
    simp only [B]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (lt_asymm h), if_neg (ne_of_lt h).symm, add_zero]
    · rw [if_neg (lt_irrefl _), if_pos rfl]
      obtain ⟨t, ht⟩ := hd i
      rw [ht]
      omega
    · rw [if_neg (lt_asymm h), if_neg (ne_of_lt h).symm, if_pos h, zero_add]
      simpa using congrFun (congrFun hA j) i
  have hT : v ⬝ᵥ Bᵀ *ᵥ v = v ⬝ᵥ B *ᵥ v := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  rw [hAB, Matrix.add_mulVec, dotProduct_add, hT]
  exact ⟨_, rfl⟩

/-- For a symmetric integer matrix of determinant `1` with even diagonal, the diagonal of the inverse
is even: `A⁻¹ = (A⁻¹)ᵀ A A⁻¹`, so `(A⁻¹)_{ii} = A[A⁻¹ eᵢ]`. -/
theorem even_inv_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℤ} (hA : A.IsSymm) (hdet : A.det = 1) (hd : ∀ i, Even (A i i)) (i : ι) :
    Even (A⁻¹ i i) := by
  have hu : IsUnit A.det := hdet ▸ isUnit_one
  have hinvS : (A⁻¹).IsSymm := hA.inv
  have hkey : A⁻¹ = (A⁻¹)ᵀ * A * A⁻¹ := by
    rw [hinvS.eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hv : A⁻¹ i i = (fun j ↦ A⁻¹ j i) ⬝ᵥ A *ᵥ (fun j ↦ A⁻¹ j i) := by
    conv_lhs => rw [hkey]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, mulVec, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [hv]
  exact even_dotProduct_mulVec_self hA hd _

/-- **Even unimodular positive definite Gram matrices of size `r` exist iff `8 ∣ r`**, for every
`r`; a bridge to Tau Ceti's `exists_isEven_isUnimodular_isPosDef_iff`. -/
theorem exists_isEvenUnimodularGram_iff (r : ℕ) :
    (∃ A : Matrix (Fin r) (Fin r) ℤ, IsEvenUnimodularGram A) ↔ 8 ∣ r := by
  rw [← TauCeti.IntegralLattice.exists_isEven_isUnimodular_isPosDef_iff]
  constructor
  · rintro ⟨A, hS, hP, hdet, hd, -⟩
    let b := Pi.basisFun ℚ (Fin r)
    let L := TauCeti.IntegralLattice.ofGramMatrix b A hS
    let e := TauCeti.IntegralLattice.ofGramMatrix.basis b A hS
    refine ⟨L, ?_, ?_, ?_⟩
    · exact (TauCeti.IntegralLattice.isEven_ofGramMatrix_iff b A hS).mpr hd
    · rw [L.isUnimodular_iff_natAbs_gramDet_eq_one e,
        TauCeti.IntegralLattice.gramDet_ofGramMatrix, hdet]
      rfl
    · rw [L.isPosDef_iff_posDef_map_gramMatrix (K := ℝ) e,
        TauCeti.IntegralLattice.gramMatrix_ofGramMatrix]
      exact hP
  · rintro ⟨L, hE, hU, hP⟩
    have hrank : Module.finrank ℤ L = r := by
      rw [TauCeti.IntegralLattice.finrank_carrier, Module.finrank_fin_fun]
    let e : Module.Basis (Fin r) ℤ L := Module.finBasisOfFinrankEq ℤ L hrank
    let A := L.gramMatrix e
    have hS : A.IsSymm := L.isSymm_gramMatrix e
    have hPA : (A.map (Int.cast : ℤ → ℝ)).PosDef :=
      (L.isPosDef_iff_posDef_map_gramMatrix (K := ℝ) e).mp hP
    have hd : ∀ i, Even (A i i) := by
      intro i
      have := (TauCeti.IntegralLattice.isEven_iff_basis L e).mp hE i
      simpa [A, TauCeti.IntegralLattice.gramMatrix_apply,
        TauCeti.IntegralLattice.integralNorm_apply] using this
    have hdet : A.det = 1 := by
      have h1 : (L.gramDet e).natAbs = 1 := (L.isUnimodular_iff_natAbs_gramDet_eq_one e).mp hU
      have hpos : 0 < A.det := by
        have := hPA.det_pos
        rw [← Int.cast_det] at this
        exact_mod_cast this
      rw [TauCeti.IntegralLattice.gramDet_def] at h1
      have h1' : A.det.natAbs = 1 := h1
      omega
    exact ⟨A, hS, hPA, hdet, hd, even_inv_diag hS hdet hd⟩

/-- **Miyake, Corollary 4.9.6.** For even `r`, a positive definite symmetric `A ∈ M_r(ℤ)` with
(i) `det A = 1` and (ii) all diagonal components of `A` and `A⁻¹` even exists if and only if
`r ≡ 0 mod 8`. -/
@[kb "miyake1989" "Corollary 4.9.6, p. 193: for even r, a positive definite symmetric A in M_r(Z) with det A = 1 and even diagonals of A and A⁻¹ exists iff r ≡ 0 mod 8"]
theorem corollary_4_9_6 (r : ℕ) (_hr : Even r) :
    (∃ A : Matrix (Fin r) (Fin r) ℤ, IsEvenUnimodularGram A) ↔ r % 8 = 0 := by
  rw [exists_isEvenUnimodularGram_iff, Nat.dvd_iff_mod_eq_zero]

end ModularFormsKB.Miyake.Sec4_9
