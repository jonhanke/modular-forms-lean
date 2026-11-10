import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import ModularFormsKB.Citation
/-!
# Miyake, Theorem 2.5.2 for `SL₂(ℤ)`: dimensions of `𝒮_k` and `𝒢_k`

Miyake, *Modular Forms* (Springer 1989), §2.5, pp. 60–61, Theorem 2.5.2, for the modular group
`Γ(1) = SL₂(ℤ)`. Its invariants are: genus `g = 0`
(`ModularFormsKB.Milne.genus_modularCurveXOne`), two elliptic points, of orders `e₁ = 2` and
`e₂ = 3`, and `t = 1` cusp. For even `k`, Miyake's formula reads

* `dim 𝒮_k = (k - 1)(g - 1) + [k/2 (1 - 1/2)] + [k/2 (1 - 1/3)] + (k/2 - 1) t
  = -(k - 1) + [k/4] + [k/3] + k/2 - 1` for `k > 2`; `dim 𝒮_2 = g = 0`; `dim 𝒮_0 = 0` (`t > 0`);
* `dim 𝒢_k = dim 𝒮_k + t` for `k ≥ 4`; `dim 𝒢_2 = g + t - 1 = 0`; `dim 𝒢_0 = 1`;
  `dim 𝒢_k = dim 𝒮_k = 0` for `k < 0`.

Everything is proved here from Mathlib's level-one dimension formula
(`ModularForm.dimension_level_one`, `ModularForm.rank_eq_one_add_rank_cuspForm`), without
Riemann–Roch. Miyake's weight `k` is `k` here (no halving).
-/

open ModularForm
open scoped MatrixGroups

private lemma finrank_M_eq {k : ℕ} (hk : Even k) :
    Module.finrank ℂ (ModularForm 𝒮ℒ k) = if k ≡ 2 [MOD 12] then k / 12 else k / 12 + 1 := by
  have h := dimension_level_one k hk
  rw [← Module.finrank_eq_rank] at h
  split_ifs at h ⊢
  · exact_mod_cast h
  · exact_mod_cast h

private lemma finrank_S_eq_M {k : ℕ} (hk : Even k) (hk4 : 4 ≤ k) :
    Module.finrank ℂ (ModularForm 𝒮ℒ k) = Module.finrank ℂ (CuspForm 𝒮ℒ k) + 1 := by
  have h := rank_eq_one_add_rank_cuspForm (k := k) (by omega) hk
  have : FiniteDimensional ℂ (CuspForm 𝒮ℒ k) :=
    (CuspForm.discriminantEquiv (k := (k : ℤ))).symm.finiteDimensional
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  have : (Module.finrank ℂ (ModularForm 𝒮ℒ k) : Cardinal) =
      ((Module.finrank ℂ (CuspForm 𝒮ℒ k) + 1 : ℕ) : Cardinal) := by
    rw [h]; push_cast; ring
  exact_mod_cast this

private lemma finrank_zero_of_rank_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : Module.rank ℂ V = 0) : Module.finrank ℂ V = 0 := by
  simp [Module.finrank, h]

namespace ModularFormsKB.Miyake

/-- **Miyake, Theorem 2.5.2** for `SL₂(ℤ)`, cusp forms of even weight `k > 2`:
`dim 𝒮_k(Γ(1)) = (k - 1)(g - 1) + [k/2 (1 - 1/2)] + [k/2 (1 - 1/3)] + (k/2 - 1) t` with `g = 0`,
`t = 1`, i.e. `-(k - 1) + [k/4] + [k/3] + k/2 - 1`. -/
@[kb "miyake1989" "Theorem 2.5.2, p. 60 (for SL2(Z), k > 2)"]
theorem finrank_cuspForm_levelOne {k : ℕ} (hk : Even k) (hk2 : 2 < k) :
    (Module.finrank ℂ (CuspForm 𝒮ℒ k) : ℤ) =
      ((k : ℤ) - 1) * (0 - 1) + (k : ℤ) / 4 + (k : ℤ) / 3 + ((k : ℤ) / 2 - 1) * 1 := by
  have h1 := finrank_M_eq hk
  have h2 := finrank_S_eq_M hk (by obtain ⟨m, hm⟩ := hk; omega)
  simp only [Nat.ModEq] at h1
  obtain ⟨m, hm⟩ := hk
  have : k % 12 = 0 ∨ k % 12 = 2 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨ k % 12 = 8 ∨ k % 12 = 10 := by
    omega
  rcases this with h | h | h | h | h | h <;> simp [h] at h1 <;> omega

/-- **Miyake, Theorem 2.5.2** for `SL₂(ℤ)`, `k = 2`: `dim 𝒮_2(Γ(1)) = g = 0`. -/
@[kb "miyake1989" "Theorem 2.5.2, p. 60 (for SL2(Z), k = 2)"]
theorem finrank_cuspForm_levelOne_two : Module.finrank ℂ (CuspForm 𝒮ℒ 2) = 0 :=
  finrank_zero_of_rank_zero (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))

/-- **Miyake, Theorem 2.5.2** for `SL₂(ℤ)`, `k = 0` (`t > 0`): `dim 𝒮_0(Γ(1)) = 0`. -/
@[kb "miyake1989" "Theorem 2.5.2, p. 60 (for SL2(Z), k = 0)"]
theorem finrank_cuspForm_levelOne_zero : Module.finrank ℂ (CuspForm 𝒮ℒ 0) = 0 :=
  finrank_zero_of_rank_zero (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))

/-- **Miyake, Theorem 2.5.2** for `SL₂(ℤ)`, `k < 0`: `dim 𝒮_k(Γ(1)) = 0`. -/
@[kb "miyake1989" "Theorem 2.5.2, p. 60 (for SL2(Z), k < 0)"]
theorem finrank_cuspForm_levelOne_neg {k : ℤ} (hk : k < 0) :
    Module.finrank ℂ (CuspForm 𝒮ℒ k) = 0 :=
  finrank_zero_of_rank_zero (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega))

/-- **Miyake, Theorem 2.5.2** for `SL₂(ℤ)`, `k ≥ 4` even: `dim 𝒢_k(Γ(1)) = dim 𝒮_k(Γ(1)) + t`,
`t = 1`. -/
@[kb "miyake1989" "Theorem 2.5.2, p. 61 (for SL2(Z), k >= 4)"]
theorem finrank_modularForm_levelOne {k : ℕ} (hk : Even k) (hk4 : 4 ≤ k) :
    Module.finrank ℂ (ModularForm 𝒮ℒ k) = Module.finrank ℂ (CuspForm 𝒮ℒ k) + 1 :=
  finrank_S_eq_M hk hk4

/-- **Miyake, Theorem 2.5.2** for `SL₂(ℤ)`, `k = 2`: `dim 𝒢_2(Γ(1)) = g + t - 1 = 0`. -/
@[kb "miyake1989" "Theorem 2.5.2, p. 61 (for SL2(Z), k = 2)"]
theorem finrank_modularForm_levelOne_two : Module.finrank ℂ (ModularForm 𝒮ℒ 2) = 0 :=
  finrank_zero_of_rank_zero levelOne_weight_two_rank_zero

/-- **Miyake, Theorem 2.5.2** for `SL₂(ℤ)`, `k = 0`: `dim 𝒢_0(Γ(1)) = 1`. -/
@[kb "miyake1989" "Theorem 2.5.2, p. 61 (for SL2(Z), k = 0)"]
theorem finrank_modularForm_levelOne_zero : Module.finrank ℂ (ModularForm 𝒮ℒ 0) = 1 := by
  rw [Module.finrank, levelOne_weight_zero_rank_one]; simp

/-- **Miyake, Theorem 2.5.2** for `SL₂(ℤ)`, `k < 0`: `dim 𝒢_k(Γ(1)) = 0`. -/
@[kb "miyake1989" "Theorem 2.5.2, p. 61 (for SL2(Z), k < 0)"]
theorem finrank_modularForm_levelOne_neg {k : ℤ} (hk : k < 0) :
    Module.finrank ℂ (ModularForm 𝒮ℒ k) = 0 :=
  finrank_zero_of_rank_zero (levelOne_neg_weight_rank_zero hk)

end ModularFormsKB.Miyake
