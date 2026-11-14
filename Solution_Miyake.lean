/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Miyake.Sec4_3.Hecke
import ModularFormsKB.Miyake.Sec4_3.WeilTheorem
import ModularFormsKB.Miyake.Wave6.HeckeIndependence
import ModularFormsKB.Miyake.Wave8.GeneralAdjoint

/-!
# Headline statements of modular-forms-lean 0.3.1: Miyake, *Modular Forms*, proved

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
* (0.3.1) `ModularFormsKB.Miyake.HeckeGenerators`, `ModularFormsKB.Miyake.heckeGenerator` (the generators `T(p)`,
  `T(p, p)` for `p ∤ N` and `T(q)` for `q ∣ N` of the Hecke ring of `Γ₀(N)`, Tau Ceti's double cosets); the
  space `ModularFormsKB.Miyake.Wave4.cuspSpace` (Tau Ceti's `𝒮_k(N, χ)`), `ModularFormsKB.Miyake.Wave4.heckeT`
  (Tau Ceti's `T(n)`), `ModularFormsKB.Miyake.Wave7.heckeTStar` and `ModularFormsKB.Miyake.Wave7.heckeTStarN`
  (Miyake's `T*(m, l)`, the double coset `Γ₀(N) diag(m, l) Γ₀(N)` acting with the weight `conj χ(d)`, and
  `T*(n) = Σ T*(m, l)` over `l m = n`, `l ∣ m`, (4.5.16)), `ModularFormsKB.Miyake.Wave7.pet` (Tau Ceti's Petersson
  product on `Γ₁(N)`) (Theorem 4.5.4)
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

section HeckeAlgebra

open CongruenceSubgroup Matrix.SpecialLinearGroup ModularFormsKB.Miyake
open scoped MatrixGroups HeckeCosetModule

/-- **The Hecke ring of `Γ₀(N)` is a polynomial ring** (Miyake, Theorem 4.5.9). For `N ≥ 1`, the Hecke ring
`ℛ(N) = ℛ(Γ₀(N), Δ₀(N))` over `ℤ` is the polynomial ring over `ℤ` in `T(p)`, `T(p, p)` (`p` prime, `p ∤ N`) and
`T(q)` (`q` prime, `q ∣ N`): there is a ring isomorphism from the polynomial ring on these symbols onto `ℛ(N)`
sending each variable to its generator. Tau Ceti has the local polynomial-ring theorem at level one (Shimura,
Theorem 3.20), not this one at level `N`. -/
theorem heckeRing_gamma0_polynomial (N : ℕ) [NeZero N] :
    ∃ e : MvPolynomial (HeckeGenerators N) ℤ ≃+*
        𝕋 (HeckeRing.GL2.Delta0 N) ((Gamma0 N).map (mapGL ℚ)) ℤ,
      ∀ i, e (MvPolynomial.X i) = heckeGenerator N i := by
  exact (ModularFormsKB.Miyake.Wave6.heckeAlgebraPolynomial N).exists_equiv

end HeckeAlgebra

section Adjoint

open ModularFormsKB.Miyake.Wave4 ModularFormsKB.Miyake.Wave7

/-- **`T(n)` and `T*(n)` are adjoint for every `n`** (Miyake, Theorem 4.5.4 (2)). For a Dirichlet character `χ`
modulo `N`, an integer weight `k` and every `n ≥ 1` (with no condition on `(n, N)`), the operators `T(n)` and `T*(n)`
on `𝒮_k(N, χ)` are mutually adjoint for the Petersson product: `⟨f | T(n), g⟩ = ⟨f, g | T*(n)⟩` and
`⟨f | T*(n), g⟩ = ⟨f, g | T(n)⟩`. Tau Ceti has the case `(n, N) = 1`. -/
theorem hecke_adjoint_heckeTStar {N : ℕ} [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 0 < n)
    (f g : cuspSpace k χ) :
    pet (heckeT k χ n f) g = pet f (heckeTStarN k χ n g) ∧
      pet (heckeTStarN k χ n f) g = pet f (heckeT k χ n g) := by
  exact ⟨ModularFormsKB.Miyake.Wave8.pet_heckeT_left_all k χ hn f g, ModularFormsKB.Miyake.Wave8.pet_heckeTStarN_left_all k χ hn f g⟩

end Adjoint

end ModularFormsKB.Headlines
