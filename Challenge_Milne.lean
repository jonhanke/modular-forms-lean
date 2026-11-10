/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Milne.Ch3.ParallelogramContour
import ModularFormsKB.Milne.Ch3.AbelJacobi
import ModularFormsKB.Milne.Ch6.ModularEquationProof
import ModularFormsKB.Milne.Ch8.EllipticModuliProof
import ModularFormsKB.Milne.Ch8.YOneSolution
import ModularFormsKB.Milne.Ch11.WeilUnconditional
import ModularFormsKB.Milne.Ch12.JIntegral
import ModularFormsKB.Milne.Wave4A.GenusZeroDifferentials

/-!
# Headline statements of modular-forms-lean 0.2.0: Milne, *Modular Functions and Modular Forms*

The main results of the library for Milne's *Modular Functions and Modular Forms* (version 1.31), one theorem each, with every proof a deliberate `sorry`: to check what
is claimed, read this file. `Solution_Milne.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/Milne.json`) checks that each proved statement is exactly the one here and uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied, except that a named statement in the conclusion (a `Prop`
structure of the library) is unfolded into its field. The statements were not yet reviewed by a human (see the
README).

## Definitions used

Besides Mathlib and Tau Ceti, the statements use these definitions of the library; a reader checking a statement
should check these too:

* `ModularFormsKB.Milne.curvePointCount` (Weil's theorem; with Tau Ceti's places `TauCeti.Place`, their degrees and
  the genus `TauCeti.genus` of a function field)
* `ModularFormsKB.Milne.X0`, `ModularFormsKB.Milne.IsJOnX0`, `ModularFormsKB.Milne.IsJNOnX0`,
  `ModularFormsKB.Milne.IsModularPolynomial`, `ModularFormsKB.Milne.scaleH` (the modular equation)
* `ModularFormsKB.Milne.IsDoublyPeriodic`, `ModularFormsKB.Milne.openParallelogram` (elliptic functions)
* `ModularFormsKB.Milne.Variety`, `ModularFormsKB.Milne.Variety.point`, `ModularFormsKB.Milne.affineLine`,
  `ModularFormsKB.Milne.affineLineCoordinate`, `ModularFormsKB.Milne.ellipticFunctor`, `ModularFormsKB.Milne.jClass`,
  `ModularFormsKB.Milne.cyclicFunctor`, `ModularFormsKB.Milne.IsModuliSolution` (moduli of elliptic curves)
* `ModularFormsKB.Milne.ModularCurveX` (the compactified quotient `Γ\ℍ*` of Tau Ceti, for the image of `Γ` in
  `PSL₂(ℝ)`), `ModularFormsKB.Milne.RiemannSurface.holomorphicDifferentials` (families of chart coefficients,
  holomorphic on each chart and satisfying the transformation rule) and `ModularFormsKB.Milne.RiemannSurface.genus`
  (its dimension, `Module.finrank`) (the genus of `X(N)`)
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
  sorry

end Weil

section ModularEquation

open UpperHalfPlane CongruenceSubgroup Matrix ModularFormsKB.Milne
open scoped MatrixGroups

/-- **Kronecker's modular equation, for every level `N`** (Milne, Theorem 6.1). On the compact Riemann surface
`X_0(N)` there are meromorphic functions `j` and `j_N` with values `j(z)` and `j(Nz)` at the class of `z ∈ ℍ`, and:
they generate the field of meromorphic functions on `X_0(N)` over `ℂ`; the minimal polynomial of `j_N` over `ℂ(j)`
has degree `ψ(N) = [SL₂(ℤ) : Γ_0(N)]`; it is `F(j, Y)` for a polynomial `F ∈ ℤ[X, Y]`; `F` is symmetric when
`N > 1`; and for `N = p` prime, `F ≡ X^{p+1} + Y^{p+1} - X^p Y^p - XY (mod p)`. -/
theorem kronecker_modularEquation (N : ℕ) (hN : 0 < N) :
    ∃ jX jNX : TauCeti.RiemannSurface.MeromorphicFunction (X0 N), IsJOnX0 N jX ∧ IsJNOnX0 N hN jNX ∧
      IntermediateField.adjoin ℂ {jX, jNX} = ⊤ ∧
      (minpoly (IntermediateField.adjoin ℂ {jX}) jNX).natDegree = (Gamma0 N).index ∧
      ∃ F : MvPolynomial (Fin 2) ℤ, IsModularPolynomial N jX jNX F ∧
        (1 < N → MvPolynomial.rename (Equiv.swap 0 1) F = F) ∧
        (N.Prime → MvPolynomial.map (Int.castRingHom (ZMod N)) F =
          MvPolynomial.X 0 ^ (N + 1) + MvPolynomial.X 1 ^ (N + 1) -
            MvPolynomial.X 0 ^ N * MvPolynomial.X 1 ^ N - MvPolynomial.X 0 * MvPolynomial.X 1) := by
  sorry

end ModularEquation

section CM

open UpperHalfPlane

/-- **`j` is an algebraic integer at the points of complex multiplication** (Milne, Corollary 12.16): if `z ∈ ℍ` is
quadratic over `ℚ` (so `ℚ(z)` is an imaginary quadratic field), then `j(z)` is an algebraic integer. -/
theorem j_isIntegral_of_imaginaryQuadratic (z : ℍ) (hz : IsIntegral ℚ (z : ℂ))
    (hz2 : (minpoly ℚ (z : ℂ)).natDegree = 2) : IsIntegral ℤ (TauCeti.ModularForm.j z) := by
  sorry

end CM

section EllipticFunctions

open Complex Filter Topology Set PeriodPair ModularFormsKB.Milne
open scoped Manifold

/-- **Zeros, poles and residues of an elliptic function** (Milne, Proposition 3.1). Let `f` be doubly periodic for
the lattice `Λ` and not identically zero, and `D` an open fundamental parallelogram with no zero or pole of `f` on
its boundary. Then over the points of `D`: the orders of `f` sum to `0`, the residues sum to `0`, and
`∑ ord_P(f) · P ∈ Λ`. -/
theorem doublyPeriodic_sums (L : PeriodPair) (f : ℂ → ℂ) (hf : IsDoublyPeriodic L.lattice f)
    (hnz : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) (z₀ : ℂ)
    (hb : ∀ z ∈ frontier (openParallelogram L z₀), meromorphicOrderAt f z = 0) :
    (∑ᶠ z ∈ openParallelogram L z₀, (meromorphicOrderAt f z).untop₀ = 0) ∧
      (∑ᶠ z ∈ openParallelogram L z₀, TauCeti.Contour.residue f z = 0) ∧
      (∑ᶠ z ∈ openParallelogram L z₀, ((meromorphicOrderAt f z).untop₀ : ℂ) * z) ∈ L.lattice := by
  sorry

/-- **Elliptic functions with prescribed zeros and poles** (Milne, Theorem 3.8; Abel's theorem for `ℂ/Λ`). Given
`n ≥ 2` points `P_1, …, P_n` and `Q_1, …, Q_n` of `ℂ`, no `P_i` congruent to a `Q_j` modulo `Λ`, with
`∑ P_i ≡ ∑ Q_j (mod Λ)`, there is a doubly periodic function whose order at every `z` is the number of `Q_j ≡ z`
minus the number of `P_i ≡ z`, and it is unique up to a nonzero constant factor (off a discrete set). -/
theorem prescribedDivisor (L : PeriodPair) (n : ℕ) (P Q : Fin n → ℂ) (hn : 2 ≤ n)
    (hPQ : ∀ i j, P i - Q j ∉ L.lattice) (hsum : (∑ i, P i) - (∑ j, Q j) ∈ L.lattice) :
    let ordAt : ℂ → ℤ := fun z ↦ haveI := Classical.propDecidable;
      ((Finset.univ.filter fun j ↦ Q j - z ∈ L.lattice).card : ℤ) -
        ((Finset.univ.filter fun i ↦ P i - z ∈ L.lattice).card : ℤ)
    (∃ f : ℂ → ℂ, IsDoublyPeriodic L.lattice f ∧ ∀ z, meromorphicOrderAt f z = ordAt z) ∧
      ∀ f g : ℂ → ℂ, IsDoublyPeriodic L.lattice f → (∀ z, meromorphicOrderAt f z = ordAt z) →
        IsDoublyPeriodic L.lattice g → (∀ z, meromorphicOrderAt g z = ordAt z) →
          ∃ c : ℂ, c ≠ 0 ∧ ∀ᶠ z in codiscrete ℂ, g z = c * f z := by
  sorry

/-- **The field of elliptic functions is `ℂ(℘, ℘')`** (Milne, Proposition 3.11): every doubly periodic function is
`P(℘, ℘')/Q(℘, ℘')` off a discrete set, for polynomials `P`, `Q` with `Q(℘, ℘')` not identically zero. -/
theorem ellipticFunctionField (L : PeriodPair) (f : ℂ → ℂ) (hf : IsDoublyPeriodic L.lattice f) :
    ∃ P Q : MvPolynomial (Fin 2) ℂ,
      ¬ (∀ᶠ z in codiscrete ℂ, MvPolynomial.eval ![℘[L] z, ℘'[L] z] Q = 0) ∧
      ∀ᶠ z in codiscrete ℂ, f z * MvPolynomial.eval ![℘[L] z, ℘'[L] z] Q =
        MvPolynomial.eval ![℘[L] z, ℘'[L] z] P := by
  sorry

end EllipticFunctions

section Moduli

open AlgebraicGeometry CategoryTheory Opposite TauCeti.AlgebraicGeometry MonoidalCategory ModularFormsKB.Milne

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- **The `j`-line is the coarse moduli variety of elliptic curves** (Milne, Theorem 8.4, over an algebraically closed
field `k`): there is a bijection `α` from the isomorphism classes of elliptic curves over `k` to the points of the
affine line sending `E` to `j(E)`, and `(𝔸¹, α)` is a solution of the moduli problem (conditions (a) and (b) of
Milne's Definition 8.1). -/
theorem ellipticModuli_jLine :
    ∃ α : (ellipticFunctor k).obj (op (Variety.point k)) ≃ (Variety.point k ⟶ affineLine k),
      (∀ x, (α x).hom.left.appTop (affineLineCoordinate k) = jClass x) ∧
        IsModuliSolution (ellipticFunctor k) (affineLine k) α := by
  sorry

/-- **The moduli problem of elliptic curves with a cyclic subgroup of order `N` has a solution** (Milne,
Theorem 8.6, over an algebraically closed field `k`, for every `N` not divisible by the characteristic of `k`):
there is a variety `M` over `k` and a bijection `α` from the isomorphism classes of pairs (elliptic curve, cyclic
subgroup of order `N`) to the points of `M` such that `(M, α)` is a solution of the moduli problem. -/
theorem cyclicModuli (N : ℕ) (hN : (N : k) ≠ 0) :
    ∃ (M : Variety k) (α : (cyclicFunctor k N).obj (op (Variety.point k)) ≃ (Variety.point k ⟶ M)),
      IsModuliSolution (cyclicFunctor k N) M α := by
  sorry

end Moduli

section GenusZero

open CongruenceSubgroup ModularFormsKB.Milne

/-- **The modular curves `X(N)`, `N = 2, 3, 4, 5`, have genus zero** (Milne, Example 2.23): every holomorphic
differential on the compact Riemann surface `X(N) = Γ(N)\ℍ*` is zero, so its genus (the dimension of the space of
holomorphic differentials) is `0`. The first part is stated because `Module.finrank` is also `0` on an
infinite-dimensional space. Tau Ceti (main) proves the Riemann–Hurwitz formula for Fuchsian groups in
Euler-characteristic form, under finite-CW-type hypotheses; it does not state the genus of `X(N)`. -/
theorem modularCurveX_Gamma_genus_eq_zero {N : ℕ} [NeZero N] (hN : 2 ≤ N) (hN5 : N ≤ 5) :
    RiemannSurface.holomorphicDifferentials (ModularCurveX (Gamma N)) = ⊥ ∧
      RiemannSurface.genus (ModularCurveX (Gamma N)) = 0 := by
  sorry

end GenusZero

end ModularFormsKB.Headlines
