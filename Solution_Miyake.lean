/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Miyake.Sec4_3.Hecke
import ModularFormsKB.Miyake.Sec4_3.WeilTheorem

/-!
# Headline statements of modular-forms-lean 0.3.0: Miyake, *Modular Forms*, proved

The statements of `Challenge_Miyake.lean`, each proved by appeal to the library theorem. `lake comparator`
(configured by `comparator/Miyake.json`) checks that each statement here is exactly the one in
`Challenge_Miyake.lean` and that its proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

Each statement is the library's statement, copied, except that a named statement in the conclusion (a `Prop`
structure of the library) is unfolded into its field. The statements were not yet reviewed by a human (see the
README).

## Definitions used

Besides Mathlib and Tau Ceti, the statements use these definitions of the library; a reader checking a statement
should check these too:

* `Miyake.CoeffGrowth`, `Miyake.qSeries`, `Miyake.completedL`, `Miyake.BoundedOnVerticalStrips`,
  `Miyake.HeckeCondition`, `Miyake.fricke`, `Miyake.twist`, `Miyake.twistedCompletedL`,
  `Miyake.TwistedHeckeCondition`, `Miyake.gaussW`, `Miyake.weilConstant`, `Miyake.IsModularFormChar`,
  `Miyake.IsCuspFormChar`, `Miyake.IsOddPrimeOrFour`, `Miyake.IsWeilSet` (converse theorems)
-/

namespace ModularFormsKB.Headlines

section Converse

open Complex Filter Asymptotics CongruenceSubgroup _root_.Miyake
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

/-- **Hecke's theorem with the Fricke involution** (Miyake, Theorem 4.3.6). For positive integers `k`, `N` and
coefficients `a_n`, `b_n` of polynomial growth, with `f = ∑ a_n e^{2πinz}` and `g = ∑ b_n e^{2πinz}`:
`g = f|_k ω_N` on `ℍ` if and only if `Λ_N(s; f)` and `Λ_N(s; g)` continue to the whole plane with
`Λ_N(s; f) = i^k Λ_N(k - s; g)` and `Λ_N(s; f) + a_0/s + i^k b_0/(k - s)` entire and bounded on vertical strips. -/
theorem hecke_converse {k N : ℕ} (hk : 0 < k) (hN : 0 < N) {a b : ℕ → ℂ}
    (ha : CoeffGrowth a) (hb : CoeffGrowth b) :
    (∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z) ↔
      HeckeCondition k N (I ^ k) a b := by
  exact _root_.Miyake.hecke_fricke hk hN ha hb

/-- **Hecke's converse theorem at level one** (Miyake, Theorem 4.3.8). For even `k ≥ 2` and coefficients `a_n` of
polynomial growth, `∑ a_n e^{2πinz}` is a modular form of weight `k` for `SL₂(ℤ)` if and only if
`Λ(s) = (2π)^{-s} Γ(s) L(s)` continues to the whole plane with `Λ(s) = (-1)^{k/2} Λ(k - s)` and
`Λ(s) + a_0/s + (-1)^{k/2} a_0/(k - s)` entire and bounded on vertical strips. -/
theorem hecke_converse_levelOne {k : ℕ} (hk : Even k) (hk2 : 2 ≤ k) {a : ℕ → ℂ} (ha : CoeffGrowth a) :
    (∃ F : ModularForm 𝒮ℒ k, ∀ τ : ℍ, F τ = qSeries a τ) ↔
      HeckeCondition k 1 ((-1) ^ (k / 2)) a a := by
  exact _root_.Miyake.levelOne_converse hk hk2 ha

/-- **Weil's converse theorem** (Miyake, Theorem 4.3.15). Let `k`, `N` be positive integers, `χ` a Dirichlet
character modulo `N` with `χ(-1) = (-1)^k`, `a_n`, `b_n` of polynomial growth, `f = ∑ a_n e^{2πinz}`,
`g = ∑ b_n e^{2πinz}`, and `𝓜` a set of odd primes and `4`, prime to `N`, meeting every arithmetic progression of
coprime positive integers. If `Λ_N(s; f)`, `Λ_N(s; g)` satisfy Hecke's condition with root number `i^k`, and for
every primitive character `ψ` of conductor in `𝓜` the twisted functions satisfy the twisted condition with Weil's
constant `χ(m_ψ) ψ(-N) W(ψ)/W(ψ̄)`, then `f ∈ M_k(N, χ)`, `g ∈ M_k(N, χ̄)` and `g = f|_k ω_N`. -/
theorem weil_converse {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    {M : Set ℕ} (hM : IsWeilSet N M) (h1 : HeckeCondition k N (I ^ k) a b)
    (h2 : ∀ (m : ℕ) [NeZero m], m ∈ M → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b) :
    IsModularFormChar k N χ (fun τ : ℍ ↦ qSeries a τ) ∧
      IsModularFormChar k N χ⁻¹ (fun τ : ℍ ↦ qSeries b τ) ∧
      ∀ z : ℂ, 0 < z.im → qSeries b z = fricke k N (qSeries a) z := by
  exact _root_.Miyake.weil hk hN χ hχ ha hb hM h1 h2

/-- **Weil's converse theorem for cusp forms** (Miyake, Theorem 4.3.15, last sentence): under the hypotheses of
`weil_converse`, if moreover `L(s; f)` converges absolutely at `s = k - δ` for some `δ > 0`, then `f` and `g` are
cusp forms. -/
theorem weil_converse_cusp {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (χ : DirichletCharacter ℂ N)
    (hχ : χ (-1) = (-1) ^ k) {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b)
    {M : Set ℕ} (hM : IsWeilSet N M) (h1 : HeckeCondition k N (I ^ k) a b)
    (h2 : ∀ (m : ℕ) [NeZero m], m ∈ M → ∀ ψ : DirichletCharacter ℂ m, ψ.IsPrimitive →
      TwistedHeckeCondition k N ψ (weilConstant χ ψ) a b)
    {δ : ℝ} (hδ : 0 < δ) (hL : LSeriesSummable a (k - δ)) :
    IsCuspFormChar k N χ (fun τ : ℍ ↦ qSeries a τ) ∧
      IsCuspFormChar k N χ⁻¹ (fun τ : ℍ ↦ qSeries b τ) := by
  exact _root_.Miyake.weil_cusp hk hN χ hχ ha hb hM h1 h2 hδ hL

end Converse

end ModularFormsKB.Headlines
