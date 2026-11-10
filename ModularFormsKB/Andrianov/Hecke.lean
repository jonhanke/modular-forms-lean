import ModularFormsKB.Andrianov.ModularGroup
import Mathlib.GroupTheory.Commensurable
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Andrianov–Zhuravlev, Chapter 3, §3.1: Hecke pairs of the symplectic group

A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (`andrianovzhuravlev1995`), Chapter 3, §3,
pdf pp. 132–134.

* `GSpPlus n = S^n = GSp_n^+(ℚ)`: invertible rational `2n × 2n` matrices with `ᵗM J_n M = r(M) J_n`, `r(M) > 0`
  (`isSimilitude_iff_blocks` gives (3.1)).
* `SiegelModularGroup.toGSp`: `Γ_n` inside `S^n`.
* Lemma 3.1 (the commensurator of a congruence subgroup in `S^n` is `S^n`, so `(K, S^n)` is a Hecke pair) and
  Lemma 3.2 (reduction modulo `q` is onto `Sp_n(ℤ/qℤ)`; `Γ^n(q) Γ^n(q₁) = Γ_n` for coprime `q, q₁`), as named
  statements.

The Hecke rings themselves (convolution of double cosets) are not in Mathlib at this pin (only the coset modules of
`Mathlib.NumberTheory.HeckeRing.Defs`); the ring-theoretic results of §3 (Theorem 3.7 and after) are left for a later
session.
-/

open Matrix

namespace ModularFormsKB.Andrianov

variable {n : ℕ}

/-- A rational symplectic similitude with positive multiplier: `ᵗM J_n M = r J_n`, `r > 0`. -/
def IsSimilitude (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) : Prop :=
  ∃ r : ℚ, 0 < r ∧ Mᵀ * Jn n ℚ * M = r • Jn n ℚ

/-- **Andrianov–Zhuravlev, Chapter 3, §3.1.** `S^n = GSp_n^+(ℚ)`, the group of rational symplectic similitudes with
positive multiplier, as a subgroup of `GL_{2n}(ℚ)`. -/
@[kb "andrianovzhuravlev1995" "Chapter 3, §3.1, p. 132"]
def GSpPlus (n : ℕ) : Subgroup (GL (Fin n ⊕ Fin n) ℚ) where
  carrier := {g | IsSimilitude (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)}
  one_mem' := ⟨1, one_pos, by simp⟩
  mul_mem' {g h} hg hh := by
    obtain ⟨r, hr, hg⟩ := hg
    obtain ⟨s, hs, hh⟩ := hh
    refine ⟨r * s, mul_pos hr hs, ?_⟩
    simp only [Units.val_mul, transpose_mul]
    calc (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * Jn n ℚ * (g * h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
        = (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * Jn n ℚ * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = (r * s) • Jn n ℚ := by
          rw [hg, Matrix.mul_smul, Matrix.smul_mul, hh, smul_smul]
  inv_mem' {g} hg := by
    obtain ⟨r, hr, hg⟩ := hg
    refine ⟨r⁻¹, inv_pos.2 hr, ?_⟩
    have h1 : ((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ = 1 := by
      rw [← transpose_mul]; simp
    have h2 : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) * ((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) = 1 := by simp
    calc ((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * Jn n ℚ * ((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
        = r⁻¹ • (((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * (r • Jn n ℚ) * ((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      _ = r⁻¹ • Jn n ℚ := by
          rw [← hg]
          congr 1
          calc ((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * Jn n ℚ * g) *
                ((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
              = (((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)ᵀ) * Jn n ℚ *
                  ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) * ((g⁻¹ : GL _ ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)) := by
                simp only [Matrix.mul_assoc]
            _ = Jn n ℚ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/-- An integral symplectic matrix is invertible over `ℚ`. -/
theorem SiegelModularGroup.isUnit_det_map (M : SiegelModularGroup n) :
    IsUnit ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ).map (Int.castRingHom ℚ)).det := by
  have h := RingHom.map_det (Int.castRingHom ℚ) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
  rw [RingHom.mapMatrix_apply] at h
  rw [← h, SymplecticGroup.det_eq_one M.2]; simp

/-- `Γ_n → S^n`. -/
noncomputable def SiegelModularGroup.toGL : SiegelModularGroup n →* GL (Fin n ⊕ Fin n) ℚ where
  toFun M := Matrix.GeneralLinearGroup.mk'' ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ).map (Int.castRingHom ℚ))
    (SiegelModularGroup.isUnit_det_map M)
  map_one' := by ext : 1; simp
  map_mul' M N := by ext : 1; exact Matrix.map_mul

theorem SiegelModularGroup.toGL_coe (M : SiegelModularGroup n) :
    ((SiegelModularGroup.toGL M : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) =
      (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ).map (Int.castRingHom ℚ) := rfl

theorem SiegelModularGroup.toGL_mem (M : SiegelModularGroup n) : SiegelModularGroup.toGL M ∈ GSpPlus n := by
  show IsSimilitude _
  refine ⟨1, one_pos, ?_⟩
  have h := SymplecticGroup.map_mem M.2 (Int.castRingHom ℚ)
  rw [mem_symplecticGroup_iff_book] at h
  rw [SiegelModularGroup.toGL_coe, h, one_smul]

/-- The image of a subgroup `K ⊆ Γ_n` in `S^n`. -/
noncomputable def SiegelModularGroup.imageGSp (K : Subgroup (SiegelModularGroup n)) :
    Subgroup (GL (Fin n ⊕ Fin n) ℚ) :=
  K.map SiegelModularGroup.toGL

/-- **Andrianov–Zhuravlev, Chapter 3, Lemma 3.1**, named statement: for a congruence subgroup `K` of `Γ_n`, every
element of `S^n` commensurates `K`; in particular `(K, S^n)` is a Hecke pair. -/
@[kb "andrianovzhuravlev1995" "Chapter 3, Lemma 3.1, p. 132"]
structure CongruenceCommensurator (n : ℕ) : Prop where
  le_commensurator : ∀ K : Subgroup (SiegelModularGroup n), IsCongruenceSubgroup K →
    GSpPlus n ≤ Subgroup.Commensurable.commensurator (SiegelModularGroup.imageGSp K)

/-- **Andrianov–Zhuravlev, Chapter 3, Lemma 3.2**, named statement: (1) reduction modulo `q` maps `SL_n(ℤ)` onto
`SL_n(ℤ/qℤ)` and `Γ_n = Sp_n(ℤ)` onto `Sp_n(ℤ/qℤ)`; (2) `Γ^n(q) Γ^n(q₁) = Γ_n` when `gcd(q, q₁) = 1`. -/
@[kb "andrianovzhuravlev1995" "Chapter 3, Lemma 3.2, p. 133"]
structure ReductionSurjective (n : ℕ) : Prop where
  sl : ∀ q : ℕ, 0 < q → Function.Surjective
    (Matrix.SpecialLinearGroup.map (n := Fin n) (Int.castRingHom (ZMod q)))
  sp : ∀ q : ℕ, 0 < q → ∀ M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod q),
    M ∈ symplecticGroup (Fin n) (ZMod q) → ∃ M' : SiegelModularGroup n,
      (M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ).map (Int.castRingHom (ZMod q)) = M
  coprime : ∀ q q₁ : ℕ, 0 < q → 0 < q₁ → Nat.Coprime q q₁ → ∀ M : SiegelModularGroup n,
    ∃ g ∈ principalCongruence n q, ∃ g₁ ∈ principalCongruence n q₁, M = g * g₁

end ModularFormsKB.Andrianov
