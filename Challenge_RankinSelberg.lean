/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.RankinSelberg.LevelOne
import ModularFormsKB.RankinSelberg.SymmetricSquareValue

/-!
# Headline statements of modular-forms-lean 0.5.1: the Rankin–Selberg method at level one

A topic, not a book: the Rankin–Selberg integral of two cusp forms of level one (R. A. Rankin, *Contributions to the
theory of Ramanujan's function τ(n) and similar arithmetical functions*, 1939; A. Selberg, 1940) and the Petersson
norm of a normalized Hecke eigenform as a value of its symmetric square L-function (D. Zagier, *Modular forms whose
Fourier coefficients involve zeta-functions of quadratic fields*, 1977). New in 0.5.0.

The main results of the library for this topic, one theorem each, with every proof a deliberate `sorry`: to check
what is claimed, read this file. `Solution_RankinSelberg.lean` proves the same statements from the library, and
`lake comparator` (configured by `comparator/RankinSelberg.json`) checks that each proved statement is exactly the one
here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

Both theorems are unconditional. The hypothesis `IsNormalizedEigenform k (coeff f)` of the second is a condition on
the coefficients of `f` (it holds for every normalized Hecke eigenform of level one), not a cited result. The
holomorphy of `L(Sym² f, s)` on all of `ℂ` (Shimura 1975) is not proved: it is stated in the library as
`ModularFormsKB.RankinSelberg.SymmetricSquareHolomorphy` and not used.

## Definitions used

Besides Mathlib (`CuspForm`, `riemannZeta`, `LSeries`, `Complex.Gamma`, the `q`-expansion
`UpperHalfPlane.qExpansion`) and Tau Ceti (`CuspForm.peterssonInnerFd`, the Petersson product as the integral of
`y^k conj(g) f` over the standard fundamental domain, with `dμ = dx dy / y²`), the statements use these definitions of
the library:

* `ModularFormsKB.RankinSelberg.coeff f n`: the `n`-th Fourier coefficient of `f` at `∞` (`q`-expansion of width 1);
* `ModularFormsKB.RankinSelberg.rankinSelbergL k f g s = ζ(2s) Σ_{n ≥ 1} a_n conj(b_n) n^{-(s+k-1)}`, the
  Rankin–Selberg Dirichlet series, absolutely convergent for `Re s > 2`;
* `ModularFormsKB.RankinSelberg.rankinSelbergCompleted k f g s`: the integral over the fundamental domain of
  `y^k conj(g) f` against the completed Eisenstein series `E*(z, s) = π^{-s} Γ(s) Σ' y^s / |mz + n|^{2s}` (as the
  Mellin transform of the theta function of the lattice `ℤz + ℤ`, so it is defined for every `s`);
* `ModularFormsKB.RankinSelberg.rankinSelbergLc k f g`: an explicit function on `ℂ` built from the entire part of the
  Rankin integral and the Gamma function (the continuation of `rankinSelbergL`; the first theorem says that it agrees
  with the series for `Re s > 2`);
* `ModularFormsKB.RankinSelberg.IsNormalizedEigenform k a`: `a 1 = 1`, `a` multiplicative on coprime indices,
  `a(p^{r+2}) = a(p) a(p^{r+1}) - p^{k-1} a(p^r)` for primes `p`, and `a` real;
* `ModularFormsKB.RankinSelberg.symSqL k f w = Π_p [(1 - p^{k-1} p^{-w})(1 - (a_p² - 2p^{k-1}) p^{-w} + p^{2k-2} p^{-2w})]⁻¹`,
  the Euler product of the symmetric square L-function;
* `ModularFormsKB.RankinSelberg.symSqLc k f`: its continuation to `Re w ≥ k`, the quotient of `(s - 1) L(f × f̄, s)`
  by `(s - 1) ζ(s)` at `s = w - k + 1`.
-/

namespace ModularFormsKB.Headlines

section RankinSelberg

open MeasureTheory Set Filter Topology Complex Asymptotics MatrixGroups
open scoped UpperHalfPlane Real ComplexConjugate
open ModularFormsKB.RankinSelberg ModularFormsKB.HalfIntegral UpperHalfPlane

/-- **The Rankin–Selberg method at level one** (Rankin 1939, Selberg 1940). For cusp forms `f`, `g` of weight
`k ≥ 1` on `SL₂(ℤ)`, the function `rankinSelbergLc` continues `L(f × ḡ, s) = ζ(2s) Σ a_n conj(b_n) n^{-(s+k-1)}`
from `Re s > 2` to a holomorphic function on `ℂ \ {1}`, with at most a simple pole at `s = 1` of residue
`(π/2) (4π)^k / Γ(k) · ⟨g, f⟩`. The completed function `Λ(s)` satisfies `Λ(1 - s) = Λ(s)`, equals
`2 π^{-s} (4π)^{-(s+k-1)} Γ(s) Γ(s+k-1) L(f × ḡ, s)` for `Re s > 0`, `s ≠ 1`, and
`Λ(s) - ⟨g, f⟩/(s - 1) + ⟨g, f⟩/s` is entire. -/
theorem rankinSelberg_levelOne (k : ℕ) (hk : 1 ≤ k) (f g : CuspForm 𝒮ℒ (k : ℤ)) :
    (∀ s, 2 < s.re → rankinSelbergLc k f g s = rankinSelbergL k f g s) ∧
    DifferentiableOn ℂ (rankinSelbergLc k f g) {1}ᶜ ∧
    Tendsto (fun s ↦ (s - 1) * rankinSelbergLc k f g s) (𝓝[≠] 1)
      (𝓝 ((π : ℂ) / 2 * (4 * π : ℂ) ^ k / Gamma k * CuspForm.peterssonInnerFd g f)) ∧
    (∀ s, rankinSelbergCompleted k f g (1 - s) = rankinSelbergCompleted k f g s) ∧
    (∀ s, 0 < s.re → s ≠ 1 → rankinSelbergCompleted k f g s = 2 * (π : ℂ) ^ (-s) *
      (4 * π : ℂ) ^ (-(s + k - 1)) * Gamma s * Gamma (s + k - 1) * rankinSelbergLc k f g s) ∧
    Differentiable ℂ (fun s ↦ rankinSelbergCompleted k f g s - CuspForm.peterssonInnerFd g f / (s - 1) +
      CuspForm.peterssonInnerFd g f / s) := by
  sorry

/-- **The Petersson norm and the symmetric square L-function** (Rankin 1939; Zagier 1977). For a normalized Hecke
eigenform `f` of weight `k ≥ 1` on `SL₂(ℤ)`, the continuation `symSqLc` agrees with the Euler product
`L(Sym² f, w)` for `Re w > k + 1`, is holomorphic on `Re w ≥ k`, and
`⟨f, f⟩ = 2 Γ(k) / (π (4π)^k) · L(Sym² f, k)`. -/
theorem petersson_eq_symSq (k : ℕ) (hk : 1 ≤ k) (f : CuspForm 𝒮ℒ (k : ℤ))
    (hf : IsNormalizedEigenform k (coeff f)) :
    (∀ w : ℂ, (k : ℝ) + 1 < w.re → symSqLc k f w = symSqL k f w) ∧
    (∀ w : ℂ, (k : ℝ) ≤ w.re → DifferentiableAt ℂ (symSqLc k f) w) ∧
    CuspForm.peterssonInnerFd f f = 2 * Gamma k / ((π : ℂ) * (4 * π : ℂ) ^ k) * symSqLc k f k := by
  sorry

end RankinSelberg

end ModularFormsKB.Headlines
