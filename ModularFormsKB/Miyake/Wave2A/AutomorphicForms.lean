import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import ModularFormsKB.Citation
/-!
# Miyake §2.1: automorphic forms at cusps and finite-index subgroups

Miyake, *Modular Forms* (Springer 1989), §2.1, pp. 39–41.

We work with Mathlib's `ModularForm Γ k` and `CuspForm Γ k` for a subgroup `Γ` of
`GL₂(ℝ)` (Miyake's `𝒢_k(Γ)` and `𝒮_k(Γ)` for a Fuchsian group `Γ`, integral weight `k`):
holomorphic on `ℍ`, `Γ`-invariant under `∣[k]`, and bounded (resp. zero) at every cusp. For a
holomorphic `f` with `f ∣[k] σ⁻¹` periodic, Miyake's "holomorphic (resp. has a zero) at the cusp
`x`" is equivalent to boundedness (resp. decay) of `f ∣[k] σ⁻¹` at `i∞`; Mathlib encodes the
condition at a cusp `c` through every `g ∈ GL₂(ℝ)` with `g ∞ = c` (Miyake's `g = σ⁻¹`).

* Lemma 2.1.2: these conditions do not depend on the choice of `σ`
  (`ModularFormsKB.Miyake.isBoundedAtImInfty_slash_iff`,
  `ModularFormsKB.Miyake.isZeroAtImInfty_slash_iff`). The meromorphic case of Miyake's lemma is
  not covered (Mathlib has no meromorphic modular forms).
* Lemma 2.1.3: for a subgroup `Γ'` of finite index in `Γ`,
  `𝒢_k(Γ) = Ω_k(Γ) ∩ 𝒢_k(Γ')` and `𝒮_k(Γ) = Ω_k(Γ) ∩ 𝒮_k(Γ')`
  (`ModularFormsKB.Miyake.exists_modularForm_iff`, `ModularFormsKB.Miyake.exists_cuspForm_iff`),
  where `Ω_k(Γ)` is represented by Mathlib's `SlashInvariantForm Γ k`. The meromorphic space
  `𝒜_k` is not covered.
-/

open UpperHalfPlane ModularForm OnePoint
open scoped MatrixGroups ModularForm

namespace ModularFormsKB.Miyake

variable {k : ℤ}

/-- **Miyake, Lemma 2.1.2 (holomorphy at a cusp).** For `g₁, g₂ ∈ GL₂(ℝ)` sending `∞` to the same
cusp `c`, `f ∣[k] g₁` is bounded at `i∞` if and only if `f ∣[k] g₂` is. -/
@[kb "miyake1989" "Lemma 2.1.2, p. 39"]
theorem isBoundedAtImInfty_slash_iff (f : ℍ → ℂ) {c : OnePoint ℝ} {g₁ g₂ : GL (Fin 2) ℝ}
    (h₁ : g₁ • (∞ : OnePoint ℝ) = c) (h₂ : g₂ • (∞ : OnePoint ℝ) = c) :
    IsBoundedAtImInfty (f ∣[k] g₁) ↔ IsBoundedAtImInfty (f ∣[k] g₂) := by
  rw [← isBoundedAt_iff h₁, ← isBoundedAt_iff h₂]

/-- **Miyake, Lemma 2.1.2 (zero at a cusp).** For `g₁, g₂ ∈ GL₂(ℝ)` sending `∞` to the same cusp
`c`, `f ∣[k] g₁` vanishes at `i∞` if and only if `f ∣[k] g₂` does. -/
@[kb "miyake1989" "Lemma 2.1.2, p. 39"]
theorem isZeroAtImInfty_slash_iff (f : ℍ → ℂ) {c : OnePoint ℝ} {g₁ g₂ : GL (Fin 2) ℝ}
    (h₁ : g₁ • (∞ : OnePoint ℝ) = c) (h₂ : g₂ • (∞ : OnePoint ℝ) = c) :
    IsZeroAtImInfty (f ∣[k] g₁) ↔ IsZeroAtImInfty (f ∣[k] g₂) := by
  rw [← isZeroAt_iff h₁, ← isZeroAt_iff h₂]

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}

/-- **Miyake, Lemma 2.1.3 (integral forms).** If `Γ' ≤ Γ` has finite index, then
`𝒢_k(Γ) = Ω_k(Γ) ∩ 𝒢_k(Γ')`: a function is a modular form for `Γ` if and only if it is
`Γ`-invariant of weight `k` and a modular form for `Γ'`. -/
@[kb "miyake1989" "Lemma 2.1.3, p. 41"]
theorem exists_modularForm_iff (hle : Γ' ≤ Γ) [Γ'.IsFiniteRelIndex Γ] (f : ℍ → ℂ) :
    (∃ F : ModularForm Γ k, ⇑F = f) ↔
      (∃ F : SlashInvariantForm Γ k, ⇑F = f) ∧ ∃ F : ModularForm Γ' k, ⇑F = f := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨⟨F.toSlashInvariantForm, rfl⟩,
      ⟨⟨⟨(F : ℍ → ℂ), fun γ hγ => F.slash_action_eq' γ (hle hγ)⟩, F.holo',
        fun hc => F.bdd_at_cusps' (hc.mono hle)⟩, rfl⟩⟩
  · rintro ⟨⟨F, rfl⟩, ⟨G, hG⟩⟩
    refine ⟨⟨F, ?_, fun hc => ?_⟩, rfl⟩
    · rw [← hG]; exact G.holo'
    · change OnePoint.IsBoundedAt _ (⇑F) k
      rw [← hG]; exact G.bdd_at_cusps' hc.of_isFiniteRelIndex

/-- **Miyake, Lemma 2.1.3 (cusp forms).** If `Γ' ≤ Γ` has finite index, then
`𝒮_k(Γ) = Ω_k(Γ) ∩ 𝒮_k(Γ')`. -/
@[kb "miyake1989" "Lemma 2.1.3, p. 41"]
theorem exists_cuspForm_iff (hle : Γ' ≤ Γ) [Γ'.IsFiniteRelIndex Γ] (f : ℍ → ℂ) :
    (∃ F : CuspForm Γ k, ⇑F = f) ↔
      (∃ F : SlashInvariantForm Γ k, ⇑F = f) ∧ ∃ F : CuspForm Γ' k, ⇑F = f := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨⟨F.toSlashInvariantForm, rfl⟩,
      ⟨⟨⟨(F : ℍ → ℂ), fun γ hγ => F.slash_action_eq' γ (hle hγ)⟩, F.holo',
        fun hc => F.zero_at_cusps' (hc.mono hle)⟩, rfl⟩⟩
  · rintro ⟨⟨F, rfl⟩, ⟨G, hG⟩⟩
    refine ⟨⟨F, ?_, fun hc => ?_⟩, rfl⟩
    · rw [← hG]; exact G.holo'
    · change OnePoint.IsZeroAt _ (⇑F) k
      rw [← hG]; exact G.zero_at_cusps' hc.of_isFiniteRelIndex

end ModularFormsKB.Miyake
