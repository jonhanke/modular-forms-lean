import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Hermite normal form of a $2 \times 2$ integer matrix of positive determinant

Every $M \in M_2(\mathbb Z)$ with $\det M > 0$ is $\delta \begin{pmatrix} a & b \\ 0 & d \end{pmatrix}$ with
$\delta \in \mathrm{SL}_2(\mathbb Z)$, $a, d > 0$ and $0 \le b < d$ (Milne, Section 6, pdf p. 87: the representatives of
$\Gamma(1)\backslash\Delta_N$). Used for the modular equation (`ModularFormsKB.Milne.ModularEquation`).
-/

open Matrix
open scoped MatrixGroups

namespace ModularFormsKB.Milne.HNF

/-- **Hermite normal form.** -/
theorem exists_SL2Z_mul_upper (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) :
    ∃ (δ : SL(2, ℤ)) (a b d : ℤ), 0 < a ∧ 0 < d ∧ 0 ≤ b ∧ b < d ∧
      M = (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b; 0, d] := by
  have hdet := Matrix.det_fin_two M
  set p := M 0 0 with hp
  set r := M 1 0 with hr
  have hg0 : (Int.gcd p r : ℤ) ≠ 0 := by
    intro h
    have h' := Int.gcd_eq_zero_iff.mp (by exact_mod_cast h)
    rw [hdet, h'.1, h'.2] at hM
    simp at hM
  set g : ℤ := (Int.gcd p r : ℤ) with hg
  have hgpos : 0 < g := lt_of_le_of_ne (by positivity) (Ne.symm hg0)
  obtain ⟨p', hp'⟩ : g ∣ p := Int.gcd_dvd_left p r
  obtain ⟨r', hr'⟩ : g ∣ r := Int.gcd_dvd_right p r
  have hbez : g = p * Int.gcdA p r + r * Int.gcdB p r := Int.gcd_eq_gcd_ab p r
  set x := Int.gcdA p r
  set y := Int.gcdB p r
  have hdet1 : x * p' + y * r' = 1 := by
    have : g * (x * p' + y * r') = g * 1 := by
      calc g * (x * p' + y * r') = p * x + r * y := by rw [hp', hr']; ring
        _ = g * 1 := by rw [mul_one]; linarith
    exact mul_left_cancel₀ hg0 this
  let δ₁ : SL(2, ℤ) := ⟨!![x, y; -r', p'], by
    rw [Matrix.det_fin_two_of]; linarith⟩
  set b' := x * M 0 1 + y * M 1 1 with hb'
  set d' := -r' * M 0 1 + p' * M 1 1 with hd'
  have hgd : g * d' = M.det := by
    rw [hdet, hd']
    rw [hp', hr']; ring
  have hdpos : 0 < d' := by
    rw [← hgd] at hM
    exact pos_of_mul_pos_right hM hgpos.le
  have hprod : (δ₁ : Matrix (Fin 2) (Fin 2) ℤ) * M = !![g, b'; 0, d'] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [δ₁, Matrix.mul_apply, Fin.sum_univ_two, hb', hd']
    · linarith
    · rw [← hp, ← hr, hp', hr']; ring
  set k := b' / d' with hk
  let T : SL(2, ℤ) := ⟨!![1, -k; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  refine ⟨(T * δ₁)⁻¹, g, b' % d', d', hgpos, hdpos, Int.emod_nonneg _ hdpos.ne',
    Int.emod_lt_of_pos _ hdpos, ?_⟩
  have h2 : ((T * δ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M = !![g, b' % d'; 0, d'] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hprod]
    have : b' % d' = b' - d' * k := by rw [hk]; exact Int.emod_def b' d'
    ext i j
    fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two, this]
    ring
  rw [← h2, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
  simp

end ModularFormsKB.Milne.HNF
