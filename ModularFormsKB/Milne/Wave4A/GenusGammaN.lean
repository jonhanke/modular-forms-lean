import ModularFormsKB.Milne.Wave4A.GenusFormula
import ModularFormsKB.Milne.Ch4.UncondDimension

/-!
# Milne, Example 2.23: the genus of `X(N)`

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, Example 2.23 (pdf p. 38).

For `N ≥ 2`, `Γ(N)` has no elliptic points (`nuTwo_Gamma`, `nuThree_Gamma`: the elements `S`, `ST` of finite order
and their conjugates are not in the normal subgroup `Γ(N)`), its number of cusps is `μ_N / N` (Exercise 2.24,
`card_cuspOrbits_Gamma_eq`), with `μ_N = (Γ̄(1) : Γ̄(N))` the index of `±Γ(N)`. Theorem 2.22 then gives
`g(N) = 1 + μ_N (N - 6) / (12 N)` (`genus_modularCurveX_Gamma`, conditional on Riemann–Hurwitz as Theorem 2.22 is).
-/

open MulAction UpperHalfPlane CongruenceSubgroup ModularGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti

/-- The centre of `SL₂(ℤ)` is `{±1}`, so `±Γ` (Tau Ceti's `withCenter`) is Miyake's `adjoinNegOne`. -/
theorem withCenter_eq_adjoinNegOne (Γ : Subgroup SL(2, ℤ)) : Γ.withCenter = Miyake.adjoinNegOne Γ := by
  rw [Subgroup.withCenter_def, Miyake.adjoinNegOne]
  congr 1
  ext g
  rw [Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one, Subgroup.mem_zpowers_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with hk | hk
    · left; exact hk.neg_one_zpow
    · right; exact hk.neg_one_zpow

/-- `S ∉ Γ(N)` for `N ≥ 2`. -/
theorem S_notMem_Gamma {N : ℕ} (hN : 2 ≤ N) : S ∉ Gamma N := by
  intro h
  have := (Gamma_mem.mp h).2.2.1
  simp [ModularGroup.coe_S] at this
  have h1 : ((1 : ℕ) : ZMod N) = 0 := by simpa using this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd one_pos h1
  omega

/-- `T⁻¹ S ∉ Γ(N)` for `N ≥ 2`. -/
theorem T_inv_mul_S_notMem_Gamma {N : ℕ} (hN : 2 ≤ N) : T⁻¹ * S ∉ Gamma N := by
  intro h
  have := (Gamma_mem.mp h).2.2.1
  simp [ModularGroup.coe_S] at this
  have h1 : ((1 : ℕ) : ZMod N) = 0 := by simpa using this
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd one_pos h1
  omega

/-- For `N ≥ 2`, `Γ(N)` has no elliptic points (Milne, Example 2.23). -/
@[kb "milne2017mf" "Example 2.23: Gamma(N) has no elliptic points, pdf p. 38"]
theorem ellipticOrbits_Gamma_eq_empty {N : ℕ} (hN : 2 ≤ N) :
    (barGamma (Gamma N)).ellipticOrbits = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  intro q hq
  induction q using Quotient.inductionOn with
  | h z =>
    rw [Subgroup.quotientMk_mem_ellipticOrbits_iff, mem_freeLocus] at hq
    have hne : Nat.card (stabilizer ((Gamma N).map sl2zToPSL2R) z) ≠ 1 := fun h1 ↦
      hq (Subgroup.card_eq_one.mp h1)
    have hnorm := Gamma_normal N
    rcases (Gamma N).exists_smul_eq_of_card_stabilizer_ne_one hne with ⟨γ, rfl, h⟩ | ⟨γ, rfl, h⟩
    · rw [(Gamma N).card_stabilizer_map_smul_I] at h
      split_ifs at h with hmem
      · have : S ∈ Gamma N := by
          simpa [mul_assoc] using hnorm.conj_mem _ hmem γ⁻¹
        exact S_notMem_Gamma hN this
      · omega
    · rw [(Gamma N).card_stabilizer_map_smul_ρ] at h
      split_ifs at h with hmem
      · have : T⁻¹ * S ∈ Gamma N := by
          simpa [mul_assoc] using hnorm.conj_mem _ hmem γ⁻¹
        exact T_inv_mul_S_notMem_Gamma hN this
      · omega

theorem nuTwo_Gamma {N : ℕ} (hN : 2 ≤ N) : nuTwo (Gamma N) = 0 := by
  simp [nuTwo, ellipticOrbits_Gamma_eq_empty hN]

theorem nuThree_Gamma {N : ℕ} (hN : 2 ≤ N) : nuThree (Gamma N) = 0 := by
  simp [nuThree, ellipticOrbits_Gamma_eq_empty hN]

/-- The right side of Theorem 2.22 for `Γ(N)`, `N ≥ 2`: `1 + μ_N (N - 6) / (12 N)` (unconditional). -/
theorem genusFormula_Gamma {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    genusFormula (Gamma N) = 1 + ((Miyake.adjoinNegOne (Gamma N)).index : ℚ) * (N - 6) / (12 * N) := by
  rw [genusFormula, nuTwo_Gamma hN, nuThree_Gamma hN, genusIndex, withCenter_eq_adjoinNegOne]
  have hcusp : (nuInfty (Gamma N) : ℚ) = ((Miyake.adjoinNegOne (Gamma N)).index : ℚ) / N := by
    rw [nuInfty, ← UncondDim.cuspCount_eq, cuspCount]
    exact card_cuspOrbits_Gamma_eq hN
  rw [hcusp]
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp
  ring

/-- **Milne, Example 2.23** (the genus of `X(N)`), conditional on the Riemann–Hurwitz formula as Theorem 2.22 is:
for `N ≥ 2`, with `μ_N = (Γ̄(1) : Γ̄(N))` the index of `±Γ(N)` in `SL₂(ℤ)`,
`g(X(N)) = 1 + μ_N (N - 6) / (12 N)`. -/
@[kb "milne2017mf" "Example 2.23: the genus of X(N), pdf p. 38"]
theorem genus_modularCurveX_Gamma {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (hRH : RiemannSurface.RiemannHurwitzStatement (ModularCurveX (Gamma N)) (OnePoint ℂ)) :
    (RiemannSurface.genus (ModularCurveX (Gamma N)) : ℚ) =
      1 + ((Miyake.adjoinNegOne (Gamma N)).index : ℚ) * (N - 6) / (12 * N) := by
  rw [genus_modularCurveX (Gamma N) hRH, ← genusFormula_Gamma hN, genusFormula]

end ModularFormsKB.Milne
