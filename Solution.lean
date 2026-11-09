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
import ModularFormsKB.Miyake.Sec4_3.Hecke
import ModularFormsKB.Miyake.Sec4_3.WeilTheorem

/-!
# Headline statements of ModularFormsKB 0.1.0, proved

The statements of `Challenge.lean`, each proved by appeal to the library theorem. `lake comparator`
(configured by `comparator.json`) checks that each statement here is exactly the one in
`Challenge.lean` and that its proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

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
* `Miyake.CoeffGrowth`, `Miyake.qSeries`, `Miyake.completedL`, `Miyake.BoundedOnVerticalStrips`,
  `Miyake.HeckeCondition`, `Miyake.fricke`, `Miyake.twist`, `Miyake.twistedCompletedL`,
  `Miyake.TwistedHeckeCondition`, `Miyake.gaussW`, `Miyake.weilConstant`, `Miyake.IsModularFormChar`,
  `Miyake.IsCuspFormChar`, `Miyake.IsOddPrimeOrFour`, `Miyake.IsWeilSet` (converse theorems)
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
  exact (ModularFormsKB.Milne.modularEquation N hN).statement

end ModularEquation

section CM

open UpperHalfPlane

/-- **`j` is an algebraic integer at the points of complex multiplication** (Milne, Corollary 12.16): if `z ∈ ℍ` is
quadratic over `ℚ` (so `ℚ(z)` is an imaginary quadratic field), then `j(z)` is an algebraic integer. -/
theorem j_isIntegral_of_imaginaryQuadratic (z : ℍ) (hz : IsIntegral ℚ (z : ℂ))
    (hz2 : (minpoly ℚ (z : ℂ)).natDegree = 2) : IsIntegral ℤ (TauCeti.ModularForm.j z) := by
  exact ModularFormsKB.Milne.jIntegralAtCM.isIntegral z hz hz2

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
  exact ModularFormsKB.Milne.doublyPeriodicSumsStatement.out L f hf hnz z₀ hb

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
  exact ModularFormsKB.Milne.prescribedDivisorStatement.out L n P Q hn hPQ hsum

/-- **The field of elliptic functions is `ℂ(℘, ℘')`** (Milne, Proposition 3.11): every doubly periodic function is
`P(℘, ℘')/Q(℘, ℘')` off a discrete set, for polynomials `P`, `Q` with `Q(℘, ℘')` not identically zero. -/
theorem ellipticFunctionField (L : PeriodPair) (f : ℂ → ℂ) (hf : IsDoublyPeriodic L.lattice f) :
    ∃ P Q : MvPolynomial (Fin 2) ℂ,
      ¬ (∀ᶠ z in codiscrete ℂ, MvPolynomial.eval ![℘[L] z, ℘'[L] z] Q = 0) ∧
      ∀ᶠ z in codiscrete ℂ, f z * MvPolynomial.eval ![℘[L] z, ℘'[L] z] Q =
        MvPolynomial.eval ![℘[L] z, ℘'[L] z] P := by
  exact ModularFormsKB.Milne.ellipticFunctionFieldStatement.out L f hf

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
  exact (ModularFormsKB.Milne.ellipticModuliSolution k).solution

/-- **The moduli problem of elliptic curves with a cyclic subgroup of order `N` has a solution** (Milne,
Theorem 8.6, over an algebraically closed field `k`, for every `N` not divisible by the characteristic of `k`):
there is a variety `M` over `k` and a bijection `α` from the isomorphism classes of pairs (elliptic curve, cyclic
subgroup of order `N`) to the points of `M` such that `(M, α)` is a solution of the moduli problem. -/
theorem cyclicModuli (N : ℕ) (hN : (N : k) ≠ 0) :
    ∃ (M : Variety k) (α : (cyclicFunctor k N).obj (op (Variety.point k)) ≃ (Variety.point k ⟶ M)),
      IsModuliSolution (cyclicFunctor k N) M α := by
  exact (ModularFormsKB.Milne.cyclicModuliSolution k N).solution hN

end Moduli

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
