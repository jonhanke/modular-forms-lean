/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Milne.Ch11.WeilUnconditional
import ModularFormsKB.Milne.Ch12.JIntegral
import ModularFormsKB.Milne.Wave6.Betti
import ModularFormsKB.Milne.Wave7.OggTame
import ModularFormsKB.Milne.Wave9.ClassGroupActionAll

/-!
# Headline statements of modular-forms-lean 0.4.0: Milne, *Modular Functions and Modular Forms*, sections 11 and 12, proved

The statements of `Challenge_MilneArithmetic.lean`, each proved by appeal to the library theorem. `lake comparator`
(configured by `comparator/MilneArithmetic.json`) checks that each statement here is exactly the one in
`Challenge_MilneArithmetic.lean` and that its proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

Each statement is the library's statement, copied, except that a named statement in the conclusion (a `Prop`
structure of the library) is unfolded into its field. The statements were not yet reviewed by a human (see the
README).

## Definitions used

Besides Mathlib and Tau Ceti, the statements use these definitions of the library; a reader checking a statement
should check these too:

* `ModularFormsKB.Milne.curvePointCount` (Weil's theorem; with Tau Ceti's places `TauCeti.Place`, their degrees and
  the genus `TauCeti.genus` of a function field)
* `ModularFormsKB.Milne.EllCMOver` (the `j`-invariants over `k` of the elliptic curves with complex
  multiplication by the order `O`), `ModularFormsKB.Milne.IsNormalizedCM` (the action of `O` on the invariant
  differential is through the embedding `ι`), `ModularFormsKB.Milne.IsAIsogeny` (an isogeny with kernel
  `E[𝔞]`) (Proposition 12.21); `ModularFormsKB.Milne.Wave6.TorusGroup`, `ModularFormsKB.Milne.Wave6.torusMul`,
  `ModularFormsKB.Milne.Wave6.latticeMul`, `ModularFormsKB.Milne.tateRep` (Proposition 11.5);
  `ModularFormsKB.Milne.Wave4B.geometricConductor` (the norm of Tau Ceti's conductor ideal, D116)
-/

namespace ModularFormsKB.Headlines


universe u v

section Weil

open TauCeti PowerSeries Polynomial ModularFormsKB.Milne

/-- **Weil's Riemann hypothesis for curves over finite fields** (Milne, Theorem 11.4). Let `F` be a function field
of one variable over a finite field `k` with `q` elements, `k` algebraically closed in `F` (the curve is
geometrically irreducible), of genus `g`, and let `N_n` be the number of points over the extension of degree `n`
(`∑_{d ∣ n} d B_d`, `B_d` the number of places of degree `d`). There are algebraic integers `α_1, …, α_{2g}` with
`N_n = 1 + q^n - ∑ α_i^n` for all `n ≥ 1`, the `q/α_i` are a permutation of the `α_i`, and `|α_i| = √q`.

Also proved in the Stacks Project formalization (Axiom), in étale-cohomological form (tag 03V8, Bombieri–Stepanov);
ours is the function-field form of Milne 11.4 and includes the functional equation. (The Stacks theorems, e.g.
`Stacks.BombieriStepanov.norm_curveEigenvalue_eq_sqrt`, are stated for smooth proper curves as schemes; they were
matched from the Stacks declaration index, not from its source.) -/
theorem weil_riemannHypothesis_curves (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F]
    (hF : IsFunctionField k F) (hk : IsIntegrallyClosedIn k F) :
    ∃ α : Fin (2 * genus k F) → ℂ, (∀ i, IsIntegral ℤ (α i)) ∧
      (∀ n : ℕ, 1 ≤ n → (curvePointCount k F n : ℂ) = 1 + (Nat.card k : ℂ) ^ n - ∑ i, α i ^ n) ∧
      (∃ σ : Equiv.Perm (Fin (2 * genus k F)), ∀ i, (Nat.card k : ℂ) / α i = α (σ i)) ∧
      (∀ i, ‖α i‖ = Real.sqrt (Nat.card k)) := by
  exact ModularFormsKB.Milne.weilCurveTheorem.{u, v}.weil k F hF hk

end Weil

section CM

open UpperHalfPlane

/-- **`j` is an algebraic integer at the points of complex multiplication** (Milne, Corollary 12.16): if `z ∈ ℍ` is
quadratic over `ℚ` (so `ℚ(z)` is an imaginary quadratic field), then `j(z)` is an algebraic integer. -/
theorem j_isIntegral_of_imaginaryQuadratic (z : ℍ) (hz : IsIntegral ℚ (z : ℂ))
    (hz2 : (minpoly ℚ (z : ℂ)).natDegree = 2) : IsIntegral ℤ (TauCeti.ModularForm.j z) := by
  exact ModularFormsKB.Milne.jIntegralAtCM.isIntegral z hz hz2

end CM

section ClassGroupAction

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields WeierstrassCurve.Affine ModularFormsKB.Milne
open scoped WeierstrassCurve Classical

/-- **The class group acts on the `j`-invariants with complex multiplication** (Milne, Proposition 12.21, in the
corrected form with a normalized `i`; Milne omits the proof). Let `k` be an algebraically closed field of
characteristic zero, `K` an imaginary quadratic field with an embedding `ι : K → k`, and `O` an order of `K`. There is
a map `Pic(O) × Ell_k(O) → Ell_k(O)` such that (1) for elliptic curves `E`, `E'` over `k` with complex
multiplication by `O`, `i : O ≅ End(E)` normalized with respect to `ι`, an invertible ideal `𝔞` of `O` and an
`𝔞`-isogeny `E → E'`, the class of `𝔞` sends `j(E)` to `j(E')`; and (2) for each `x₀ ∈ Ell_k(O)` the map
`c ↦ c · x₀` is a bijection `Pic(O) → Ell_k(O)`. (The statement does not ask for the action laws; (1) and the
existence of `𝔞`-isogenies determine the map.) -/
theorem classGroupAction_ellCM (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (K : Type) [Field K]
    [NumberField K] (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (ι : K →+* k) :
    ∃ act : Pic O → EllCMOver k O → EllCMOver k O,
      (∀ (W W' : WeierstrassCurve.Affine k) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver k O) → (hW' : W'.j ∈ EllCMOver k O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  exact ModularFormsKB.Milne.Wave9.classGroupActionPrincipalNormalized.principal k K O hK hTC ι

end ClassGroupAction

section BettiTate

open TauCeti TauCeti.Isogeny TensorProduct ModularFormsKB.Milne ModularFormsKB.Milne.Wave6
open scoped WeierstrassCurve ComplexConjugate

/-- **The Betti, ℓ-adic and tangent representations of an elliptic curve over `ℂ`** (Milne, Proposition 11.5). For
every elliptic curve `E` over `ℂ` (Weierstrass model `W`) and every prime `ℓ` there are a lattice `Λ`, a group
isomorphism `u : ℂ/Λ ≅ E(ℂ)` and a ring homomorphism `ρ : End(E) → ℂ` with `ρ(f)Λ ⊆ Λ` and `f(u(z)) = u(ρ(f) z)`,
such that, with `ρ_B(f)` multiplication by `ρ(f)` on `H₁(E, ℤ) = Λ` and `ρ_ℓ(f)` the action on the Tate module
`T_ℓE`: (a) `ρ_B ⊗ ℤ_ℓ ≅ ρ_ℓ` and (b) `ρ_B ⊗ ℂ ≅ ρ ⊕ ρ̄`, by linear isomorphisms `ℤ_ℓ ⊗ Λ ≅ T_ℓE` and
`ℂ ⊗ Λ ≅ ℂ × ℂ` intertwining the actions of every endomorphism. -/
theorem betti_tate_comparison (W : WeierstrassCurve ℂ) [W.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (L : PeriodPair) (u : TorusGroup L ≃+ W.toAffine.Point) (ρ : Hom W.toAffine W.toAffine →+* ℂ)
      (hρ : ∀ f, ∀ x ∈ L.lattice, ρ f * x ∈ L.lattice),
      (∀ f z, f.pointMap (u z) = u (torusMul L (ρ f) (hρ f) z)) ∧
      (∃ Φ : ℤ_[ℓ] ⊗[ℤ] L.lattice ≃ₗ[ℤ_[ℓ]] TateModule ℓ W.toAffine.Point,
        ∀ f, Φ.toLinearMap ∘ₗ (latticeMul L (ρ f) (hρ f)).baseChange ℤ_[ℓ] = tateRep W ℓ f ∘ₗ Φ.toLinearMap) ∧
      (∃ Ψ : ℂ ⊗[ℤ] L.lattice ≃ₗ[ℂ] ℂ × ℂ, ∀ f (x : ℂ ⊗[ℤ] L.lattice),
        Ψ ((latticeMul L (ρ f) (hρ f)).baseChange ℂ x) = (ρ f * (Ψ x).1, conj (ρ f) * (Ψ x).2)) := by
  exact ModularFormsKB.Milne.Wave6.proposition_11_5_general W ℓ

end BettiTate

section Conductor

open WeierstrassCurve TauCeti IsLocalRing IsDiscreteValuationRing IsDedekindDomain ModularFormsKB.Milne

/-- **The conductor exponent at a cusp is 2 for `p ≠ 2, 3`** (Milne, the geometric conductor, p. 111: "`f_p ≥ 2` if
`E(p)` has a cusp, with equality unless `p = 2, 3`"). For an elliptic curve `E` over `ℚ` and a prime `p ≠ 2, 3`, the
exponent of `p` in the conductor `N` of `E` (the norm of Tau Ceti's conductor ideal, defined by Tate's algorithm) is
exactly `2` (`p² ∣ N`, `p³ ∤ N`) if and only if a minimal model of `E` at `p` has additive reduction. -/
theorem conductor_exponent_eq_two_iff (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {v : HeightOneSpectrum ℤ} (hv : v.asIdeal = Ideal.span {(p : ℤ)}) :
    (p ^ 2 ∣ Wave4B.geometricConductor E ∧ ¬ p ^ 3 ∣ Wave4B.geometricConductor E) ↔
      (E.minimal (Localization.AtPrime v.asIdeal)).HasAdditiveReduction (Localization.AtPrime v.asIdeal) := by
  exact ModularFormsKB.Milne.Wave7.geometricConductor_exponent_eq_two_iff E hp hp2 hp3 hv

end Conductor

end ModularFormsKB.Headlines
