/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Andrianov.ThetaSeries

/-!
# Headline statements of modular-forms-lean 0.2.0: Andrianov and Zhuravlev, *Modular Forms and Hecke Operators*

The main results of the library for Andrianov and Zhuravlev's *Modular Forms and Hecke Operators* (1995), one theorem
each, with every proof a deliberate `sorry`: to check what is claimed, read this file.
`Solution_AndrianovZhuravlev.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator/AndrianovZhuravlev.json`) checks that each proved statement is exactly the one here and uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied, with the term of the theta series written out. Neither Mathlib
nor Tau Ceti (main, 2026-11-10) has the Siegel upper half space or Siegel theta series. The statements were not yet
reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `ModularFormsKB.Andrianov.evenPD` (`A_m⁺`: integral symmetric `m × m` matrices with even diagonal, positive
  definite over `ℝ`), `ModularFormsKB.Andrianov.IsEvenSymm`
* `ModularFormsKB.Andrianov.SiegelSpace` (`H_n`: complex symmetric `n × n` matrices with positive definite imaginary
  part), `ModularFormsKB.Andrianov.SiegelSpace.im`, `ModularFormsKB.Andrianov.siegelSetEps` (`H_n(ε)`: those with
  `Im Z - ε·1` positive semidefinite)
-/

namespace ModularFormsKB.Headlines

section SiegelTheta

open Matrix ModularFormsKB.Andrianov

/-- **Siegel theta series converge absolutely and uniformly on `H_n(ε)`** (Andrianov–Zhuravlev, Chapter 1,
Proposition 1.3). Let `Q` be an even integral positive definite `m × m` matrix and `ε > 0`. The terms
`exp(πi tr(ᵗN Q N Z))`, `N` an integral `m × n` matrix, of the theta series `θ^n(Z, Q)` of degree `n` are bounded on
`H_n(ε)` by a summable family independent of `Z` (the Weierstrass test). -/
theorem siegelTheta_dominated {m n : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : Q ∈ evenPD m) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : Matrix (Fin m) (Fin n) ℤ → ℝ, Summable u ∧
      ∀ N : Matrix (Fin m) (Fin n) ℤ, ∀ Z ∈ siegelSetEps n ε,
        ‖Complex.exp (Real.pi * Complex.I * ((N.map (Int.cast : ℤ → ℂ))ᵀ * Q.map (Int.cast : ℤ → ℂ) *
          N.map (Int.cast : ℤ → ℂ) * (Z : Matrix (Fin n) (Fin n) ℂ)).trace)‖ ≤ u N := by
  sorry

end SiegelTheta

end ModularFormsKB.Headlines
