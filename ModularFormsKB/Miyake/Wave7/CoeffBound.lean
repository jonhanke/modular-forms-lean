import ModularFormsKB.Miyake.Wave4.Notation
import TauCeti.NumberTheory.ModularForms.LFunction.Abscissa

/-!
# Miyake, Theorem 4.7.3 for weight `k ≥ 2`

Miyake, *Modular Forms* (Springer 1989), §4.7, p. 181.

Theorem 4.7.3: if `f(z) = Σ a_n e^{2πinz}` belongs to the Eisenstein space `ℰ_k(N, χ)` (4.7.17),
then `a_n = O(n^{k-1})` if `k > 2`, and `a_n = O(n^{k-1+ε})` for every `ε > 0` if `k = 1, 2`.

Since `ℰ_k(N, χ) ⊂ 𝒢_k(N, χ)`, the cases `k ≥ 2` follow from bounds valid on all of
`𝒢_k(N, χ)`, which Tau Ceti proves for forms on `Γ₁(N)`
(`TauCeti.ModularFormClass.qExpansion_isBigO_of_Gamma1_le`, `_rpow_of_Gamma1_le`); these are
stated here for `𝒢_k(N, χ)` (a generalization of Miyake's statement, without the space `ℰ_k`).
The case `k = 1` is not formalized (it needs `ℰ_1(N, χ)`; loose end).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave7

open ModularFormsKB.Miyake.Wave4

variable {N : ℕ} [NeZero N]

/-- **Miyake, Theorem 4.7.3** for `k > 2`, on all of `𝒢_k(N, χ)`: `a_n = O(n^{k-1})`. -/
@[kb "miyake1989" "Theorem 4.7.3, p. 181 (k > 2, on G_k(N, chi))"]
theorem coeffMod_isBigO {k : ℤ} (hk : 2 < k) (χ : DirichletCharacter ℂ N) (f : modSpace k χ) :
    (fun n ↦ coeffMod f n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (k - 1) :=
  TauCeti.ModularFormClass.qExpansion_isBigO_of_Gamma1_le le_rfl (by omega)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- **Miyake, Theorem 4.7.3** for `k ≥ 2` with `ε`, on all of `𝒢_k(N, χ)`:
`a_n = O(n^{k-1+ε})` for every `ε > 0` (Miyake states it for `k = 1, 2`). -/
@[kb "miyake1989" "Theorem 4.7.3, p. 181 (k = 2, on G_k(N, chi))"]
theorem coeffMod_isBigO_rpow {k : ℤ} (hk : 2 ≤ k) (χ : DirichletCharacter ℂ N) {ε : ℝ}
    (hε : 0 < ε) (f : modSpace k χ) :
    (fun n ↦ coeffMod f n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) - 1 + ε) :=
  TauCeti.ModularFormClass.qExpansion_isBigO_rpow_of_Gamma1_le le_rfl hk hε
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)

end ModularFormsKB.Miyake.Wave7
