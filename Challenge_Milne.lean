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
import ModularFormsKB.Milne.Wave4A.GenusZeroDifferentials
import ModularFormsKB.Milne.Wave10.LittlePicard
import ModularFormsKB.Milne.Wave13.AllFiniteIndex
import ModularFormsKB.Milne.Wave14.LineBundles
import ModularFormsKB.Milne.Wave15.Corollaries

/-!
# Headline statements of modular-forms-lean 0.5.0: Milne, *Modular Functions and Modular Forms*, sections 0 to 10

The main results of the library for sections 0 to 10 of Milne's *Modular Functions and Modular Forms* (version 1.31), one theorem each, with every proof a deliberate `sorry`: to check what
is claimed, read this file. `Solution_Milne.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/Milne.json`) checks that each proved statement is exactly the one here and uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. Sections 11 and 12 (Weil's theorem, elliptic curves,
complex multiplication) are in `Challenge_MilneArithmetic.lean` (until 0.3.1 one file held both; it was split in
0.4.0 so that each comparator check stays under 30 minutes).

Each statement is the library's statement, copied, except that a named statement in the conclusion (a `Prop`
structure of the library) is unfolded into its field. The statements were not yet reviewed by a human (see the
README).

## Definitions used

Besides Mathlib and Tau Ceti, the statements use these definitions of the library; a reader checking a statement
should check these too:

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
* (0.4.0) `ModularFormsKB.Milne.RiemannSurface.MeromorphicDifferential` (with `.IsZero`, `.divisor`),
  `ModularFormsKB.Milne.RiemannSurface.rrSpace` (the space `L(D)`), `ModularFormsKB.Milne.RiemannSurface.ell`
  (`ℓ(D) = dim L(D)`), with Tau Ceti's `TauCeti.RiemannSurface.MeromorphicFunction` and Weil divisors
  (Riemann–Roch, the existence theorem); `ModularFormsKB.Milne.modularCurve`, `ModularFormsKB.Milne.genus`,
  `ModularFormsKB.Milne.cuspCount`, `ModularFormsKB.Milne.ellipticTerm` (the dimension formula);
  `ModularFormsKB.Milne.genusIndex`, `ModularFormsKB.Milne.nuTwo`, `ModularFormsKB.Milne.nuThree`,
  `ModularFormsKB.Milne.nuInfty` (the genus formula)
-/

namespace ModularFormsKB.Headlines


universe u v

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

section LittlePicard

open Set

/-- **The little Picard theorem** (Milne, Remark 2.25). A nonconstant entire function `f : ℂ → ℂ` omits at most one
value: the complement of its range has at most one point. Milne derives it from the covering `ℍ → ℂ ∖ {0, 1}` given
by the modular function `λ` of `Γ(2)`; the library runs the same argument with the level-one `j` on the free locus
of `PSL(2, ℤ)` (a covering of `ℂ ∖ {0, 1728}`). -/
theorem littlePicard {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnc : ∃ z w, f z ≠ f w) :
    (range f)ᶜ.Subsingleton := by
  sorry

end LittlePicard

section RiemannSurfaces

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry ModularFormsKB.Milne.RiemannSurface
open scoped Manifold

/-- **The existence theorem on a compact Riemann surface** (Milne, Theorem 1.17; proof after Forster, *Lectures on
Riemann Surfaces*, §14). On every compact connected Riemann surface `X` the meromorphic functions separate points,
and the field `M(X)` of meromorphic functions is a function field of one variable over `ℂ` (finitely generated, of
transcendence degree one). Tau Ceti main has the field `M(X)` but no existence theorem for nonconstant functions. -/
theorem meromorphicFunctions_separate_points (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [CompactSpace X] [ConnectedSpace X] :
    (∀ x y : X, x ≠ y → ∃ g : MeromorphicFunction X, g x ≠ g y) ∧
      TauCeti.IsFunctionField ℂ (MeromorphicFunction X) := by
  sorry

/-- **The Riemann–Roch theorem** (Milne, Theorem 1.20), on every compact connected Riemann surface `X`: the spaces
`L(D)` are finite-dimensional, and there is an integer `g ≥ 0` such that for every nonzero meromorphic differential
form `ω` (canonical divisor `K = div(ω)`) and every divisor `D`, `ℓ(D) = deg D + 1 - g + ℓ(K - D)`. Milne refers to
Gunning for the proof; the library derives it from Tau Ceti's Riemann–Roch for function fields through the
existence theorem (points of `X` = places of `M(X)`). -/
theorem riemannRoch (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] :
    (∀ D : WeilDivisor X, FiniteDimensional ℂ (rrSpace X D)) ∧
      ∃ g : ℕ, ∀ ω : MeromorphicDifferential X, ¬ ω.IsZero → ∀ D : WeilDivisor X,
        (ell X D : ℤ) = WeilDivisor.degree D + 1 - g + ell X (ω.divisor - D) := by
  sorry

end RiemannSurfaces

section FiniteIndex

open CongruenceSubgroup ModularFormsKB.Milne
open scoped MatrixGroups

/-- **The dimension formula** (Milne, Theorem 4.9), for every subgroup `Γ` of finite index in `SL₂(ℤ)`, congruence
or not: for `k ≥ 1`, `dim M_{2k}(Γ) = (2k - 1)(g - 1) + ε_∞ k + ∑_P ⌊k(1 - 1/e_P)⌋`, with `g` the genus of `X(Γ)`,
`ε_∞` the number of cusps and `P` running over the elliptic points of `Γ\ℍ` (stabilizer order `e_P`). -/
theorem dimensionFormula (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∀ k : ℕ, 1 ≤ k →
      (Module.finrank ℂ (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k : ℕ)) : ℤ) =
        (2 * k - 1) * ((ModularFormsKB.Milne.genus (modularCurve Γ) : ℤ) - 1) + cuspCount Γ * k +
          ellipticTerm Γ k := by
  sorry

/-- **The genus formula** (Milne, Theorem 2.22), for every subgroup `Γ` of finite index in `SL₂(ℤ)`: the genus of
`X(Γ)` (the dimension of its space of holomorphic differentials) is `1 + m/12 - ν₂/4 - ν₃/3 - ν_∞/2`, with `m` the
index of `±Γ` in `SL₂(ℤ)`, `ν₂`, `ν₃` the numbers of elliptic points of order 2 and 3 and `ν_∞` the number of cusps. -/
theorem genusFormula (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    (ModularFormsKB.Milne.RiemannSurface.genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 := by
  sorry

end FiniteIndex

section LineBundles

open UpperHalfPlane
open scoped Manifold ContDiff

/-- **Every holomorphic line bundle on `ℍ` is trivial** (Milne, Remark 4.26, cited there without proof): a
holomorphic line bundle on the upper half plane has a nowhere-vanishing holomorphic section. The library proves the
multiplicative Cousin problem on `ℍ` (smooth logarithms and the `∂̄`-equation on `ℍ`, after Forster, §30). -/
theorem holomorphicLineBundle_upperHalfPlane_trivial (E : ℍ → Type) [∀ x, NormedAddCommGroup (E x)]
    [∀ x, NormedSpace ℂ (E x)] [TopologicalSpace (Bundle.TotalSpace ℂ E)] [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
    [ContMDiffVectorBundle ω ℂ E 𝓘(ℂ)] :
    ∃ s : (x : ℍ) → E x, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun x ↦ (⟨x, s x⟩ : Bundle.TotalSpace ℂ E)) ∧
      ∀ x, s x ≠ 0 := by
  sorry

end LineBundles

end ModularFormsKB.Headlines
