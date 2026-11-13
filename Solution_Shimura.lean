/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Shimura2007.Ch2.HalfRangeSums

/-!
# Headline statements of modular-forms-lean 0.3.0: Shimura, *Elementary Dirichlet Series and Modular Forms*, proved

The statements of `Challenge_Shimura.lean`, each proved by appeal to the library theorem. `lake comparator`
(configured by `comparator/Shimura.json`) checks that each statement here is exactly the one in
`Challenge_Shimura.lean` and that its proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

`L(s, χ)` is Mathlib's `DirichletCharacter.LFunction χ s`; `G(χ̄) = gaussSum χ⁻¹ ZMod.stdAddChar`.

## Definitions used

Besides Mathlib, the statements use this definition of the library; a reader checking a statement should check it
too:

* `ModularFormsKB.Shimura2007.bernoulliPoly` (`B_k(t)`: Mathlib's Bernoulli polynomial `Polynomial.bernoulli k`,
  mapped to `ℂ` and evaluated at `t`)
-/

namespace ModularFormsKB.Headlines

section HalfRange

open Complex DirichletCharacter ModularFormsKB.Shimura2007
open scoped Real

/-- **`L(k, χ)` by a sum over half the residues** (Shimura, Theorem 4.14 (i), (4.33)). For a nontrivial primitive
Dirichlet character `χ` modulo `d` and `k ≥ 2` with `χ(-1) = (-1)^k`,
`k! (2πi)^{-k} G(χ̄) L(k, χ) = -∑_{1 ≤ a ≤ (d-1)/2} χ̄(a) B_k(a/d)`.

Related: the value through the generalized Bernoulli number `B_{k,χ}` (a sum over all residues `1 ≤ a ≤ d`, for the
series over `n ∈ ℤ`) is in Tau Ceti (main, 2026-11-10,
`DirichletCharacter.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`); the sum over half the residues is
Shimura's and is in neither Tau Ceti nor Mathlib. -/
theorem LFunction_halfRange {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {k : ℕ} (hk : 2 ≤ k) (hpar : χ (-1) = (-1) ^ k) :
    (k.factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar * LFunction χ k =
      -∑ a ∈ Finset.Icc 1 ((d - 1) / 2), χ⁻¹ a * bernoulliPoly k ((a : ℂ) / d) := by
  exact ModularFormsKB.Shimura2007.theorem_4_14_i hχ hχ1 hk hpar

end HalfRange

end ModularFormsKB.Headlines
