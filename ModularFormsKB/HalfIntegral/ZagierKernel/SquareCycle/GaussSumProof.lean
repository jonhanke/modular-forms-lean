/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.GaussSum
import ModularFormsKB.HalfIntegral.GaussSign
import ModularFormsKB.Miyake.Sec4_8.KroneckerGaussAll
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Proof of `KroneckerGaussSum`

From Miyake's Lemma 4.8.1 (1) as proved in `Miyake.Sec4_8.kroneckerGaussSumStatement` (`W(χ_D) = √D`), primitivity of
the Kronecker character (`gaussSum_mulShift_of_isPrimitive` gives general `m`), and the trivial case `D = 1`.
-/

open Complex Finset
open scoped Real

namespace ModularFormsKB.HalfIntegral

private theorem isFund_of (D : ℤ) (h : IsFundamentalDiscriminant D) : Int.IsFundamentalDiscr D := by
  rw [Int.isFundamentalDiscr_iff_squarefree]
  rcases h with ⟨h1, hs⟩ | ⟨m, rfl, hm, hsf⟩
  · exact Or.inl ⟨h1, hs⟩
  · refine Or.inr ⟨by omega, ?_, by omega⟩
    have : 4 * m / 4 = m := by omega
    rw [this]; exact hsf

/-- **Gauss sums of the Kronecker character of a fundamental discriminant** (proof of `KroneckerGaussSum`). -/
theorem kroneckerGaussSum : KroneckerGaussSum := by
  refine ⟨fun D hDf m ↦ ?_⟩
  have hD := isFund_of D hDf
  by_cases hD1 : D = 1
  · subst hD1
    simp [sqrtDisc, TauCeti.kroneckerSym_one_left]
  have hne : D ≠ 0 := hD.ne_zero
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hne⟩
  set χ : DirichletCharacter ℂ D.natAbs :=
    TauCeti.kroneckerChar ℂ D (hD.emod_four_eq_zero_or_one.imp id id) hne with hχ
  have hχeq : χ = TauCeti.Multiquadratic.fundamentalDiscriminantCharCast ℂ D hD := by
    ext a
    simp only [TauCeti.Multiquadratic.fundamentalDiscriminantCharCast_apply, hχ]
    rfl
  have hprim : χ.IsPrimitive := hχeq ▸ TauCeti.Multiquadratic.isPrimitive_fundamentalDiscriminantCharCast hD
  have hW := ModularFormsKB.Miyake.Sec4_8.kroneckerGaussSumStatement D hD hD1
  have hquad : χ.IsQuadratic := hχeq ▸ TauCeti.Multiquadratic.fundamentalDiscriminantCharCast_isQuadratic hD
  -- the left side as a Gauss sum
  have hL : ∑ c ∈ range D.natAbs, (TauCeti.kroneckerSym D c : ℂ) * cexp (2 * π * I * m * c / D.natAbs) =
      gaussSum χ (ZMod.stdAddChar.mulShift (m : ZMod D.natAbs)) := by
    rw [gaussSum, ← sum_range_eq_sum_zmod]
    refine sum_congr rfl fun c _ ↦ ?_
    have h1 : (TauCeti.kroneckerSym D c : ℂ) = χ (c : ZMod D.natAbs) := by
      have := TauCeti.kroneckerChar_intCast (R := ℂ) (hD.emod_four_eq_zero_or_one.imp id id) hne (c : ℤ)
      simp [hχ]
    have h2 : cexp (2 * π * I * m * c / D.natAbs) =
        ZMod.stdAddChar.mulShift (m : ZMod D.natAbs) (c : ZMod D.natAbs) := by
      have := ZMod.stdAddChar_coe (N := D.natAbs) (m * (c : ℤ))
      push_cast at this
      rw [AddChar.mulShift_apply, this, mul_assoc (2 * (π : ℂ) * I)]
    rw [h1, h2]
  rw [hL, gaussSum_mulShift_of_isPrimitive _ hprim]
  have hW' : gaussSum χ ZMod.stdAddChar = sqrtDisc D := by
    have := hW
    unfold Miyake.gaussW at this
    rw [this, sqrtDisc]
    by_cases h0 : 0 ≤ D
    · have : 0 < D := lt_of_le_of_ne h0 (Ne.symm hne)
      simp [this, h0]
    · have : ¬ 0 < D := by omega
      simp [this, h0, abs_of_neg (by exact_mod_cast (by omega : D < 0) : (D : ℝ) < 0)]
  rw [hW']
  congr 1
  have hinv : χ⁻¹ = χ := hquad.inv
  rw [hinv]
  simp [hχ]
end ModularFormsKB.HalfIntegral
