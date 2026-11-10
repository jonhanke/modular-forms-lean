/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Milne.Wave4A.GenusZero

/-!
# The modular curves `X(N)`, `2 ≤ N ≤ 5`, have no nonzero holomorphic differential

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, Example 2.23 (pdf p. 38).

The genus `RiemannSurface.genus X` is `Module.finrank ℂ` of the space of holomorphic differentials, which is also `0`
for an infinite-dimensional space. This file proves the stronger statement that the space itself is zero when the
genus formula gives `0`: a nonzero meromorphic differential `θ₀` of degree `-2` identifies `L(div θ₀)` with the
holomorphic differentials (`RS.rrSpaceEquivHolomorphicDifferentials`), and `L(D) = 0` when `deg D < 0`.
-/

open Set CongruenceSubgroup
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti TauCeti.RiemannSurface TauCeti.AlgebraicGeometry RiemannSurface MeromorphicFunction

/-- `L(D) = 0` for a divisor of negative degree (the argument of `RiemannSurface.ell_eq_zero_of_degree_neg`). -/
theorem rrSpace_eq_bot_of_degree_neg {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [CompactSpace X] [ConnectedSpace X] [T2Space X] {D : WeilDivisor X}
    (hD : WeilDivisor.degree D < 0) : rrSpace X D = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  have heff : 0 ≤ (D + principalDivisor X f) := by
    intro x
    have h1 := hf x
    rw [← coe_principalDivisor_apply hf0 x] at h1
    have h2 : -(D x) ≤ principalDivisor X f x := by exact_mod_cast h1
    show 0 ≤ (D + principalDivisor X f) x
    rw [Finsupp.add_apply]
    omega
  have h3 := WeilDivisor.degree_nonneg heff
  rw [WeilDivisor.degree_add, degree_principalDivisor] at h3
  omega

/-- A compact Riemann surface carrying a nonzero meromorphic differential of negative degree has no nonzero
holomorphic differential. -/
theorem holomorphicDifferentials_eq_bot_of_degree_neg {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [ConnectedSpace X] [T2Space X]
    {θ₀ : MeromorphicDifferential X} (hθ₀ : ¬ θ₀.IsZero) (hdeg : WeilDivisor.degree θ₀.divisor < 0) :
    holomorphicDifferentials X = ⊥ := by
  have e := RS.rrSpaceEquivHolomorphicDifferentials hθ₀
  rw [Submodule.eq_bot_iff]
  intro c hc
  have h := rrSpace_eq_bot_of_degree_neg hdeg
  have hz : e.symm ⟨c, hc⟩ = 0 :=
    Subtype.ext ((Submodule.eq_bot_iff _).mp h _ (e.symm ⟨c, hc⟩).2)
  have h2 : e (e.symm ⟨c, hc⟩) = e 0 := congrArg e hz
  rw [LinearEquiv.apply_symm_apply, map_zero] at h2
  exact congrArg Subtype.val h2

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- If `1 + m/12 - ν₂/4 - ν₃/3 - ν∞/2 = 0`, every holomorphic differential on `X(Γ)` is zero. -/
theorem holomorphicDifferentials_modularCurveX_eq_bot_of_genusFormula_eq_zero (h : genusFormula Γ = 0) :
    holomorphicDifferentials (ModularCurveX Γ) = ⊥ := by
  obtain ⟨hg, hK⟩ := genus_and_canonicalDegree_of_genusFormula_eq_zero Γ h
  have hθ := differential_pullback_coordinate_not_isZero (modularCurveXJ Γ)
  refine holomorphicDifferentials_eq_bot_of_degree_neg hθ ?_
  rw [hK.out _ hθ, hg]
  norm_num

/-- **Milne, Example 2.23**, `N = 2, 3, 4, 5`: the modular curve `X(N)` has genus `0`, and more precisely every
holomorphic differential on `X(N)` is zero. -/
@[kb "milne2017mf" "Example 2.23, genus 0 for N = 2, 3, 4, 5 (pdf p. 38)"]
theorem holomorphicDifferentials_modularCurveX_Gamma_eq_bot {N : ℕ} [NeZero N] (hN : 2 ≤ N) (hN5 : N ≤ 5) :
    holomorphicDifferentials (ModularCurveX (Gamma N)) = ⊥ ∧
      RiemannSurface.genus (ModularCurveX (Gamma N)) = 0 :=
  ⟨holomorphicDifferentials_modularCurveX_eq_bot_of_genusFormula_eq_zero _ (genusFormula_Gamma_eq_zero hN hN5),
    genus_modularCurveX_Gamma_eq_zero hN hN5⟩

end ModularFormsKB.Milne
