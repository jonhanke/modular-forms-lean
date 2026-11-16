/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Elliptic.WeilConverse
import ModularFormsKB.Elliptic.TwistLevel

/-!
# Headline statements of modular-forms-lean 0.5.0: modular elliptic curves

A topic, not a book: elliptic curves over `ℚ` whose L-function is that of a newform of weight 2 (Milne, *Modular
Functions and Modular Forms*, section 11: Conjecture 11.17, Theorem 11.19, Theorem 11.24), the functional equation and
parity that follow, and Weil's converse theorem in the form of Milne's Theorem 11.19. New in 0.5.0.

The main results of the library for this topic, one theorem each, with every proof a deliberate `sorry`: to check
what is claimed, read this file. `Solution_EllipticCurves.lean` proves the same statements from the library, and
`lake comparator` (configured by `comparator/EllipticCurves.json`) checks that each proved statement is exactly the one
here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied (the first combines three library theorems into one conjunction).
The statements were not yet reviewed by a human (see the README).

**Unconditional theorems.** `elliptic_hasNewform_functionalEquation` and `elliptic_hasNewform_strongHasseWeil` assume
`HasNewform E N f`, which is a condition on `E`, `N` and `f` (the coefficients of the newform `f` are those of
`L(E, s)`), not a cited result. `elliptic_congruentCurve_one_hasNewform` and `elliptic_congruentCurve_hasNewform`
prove `HasNewform` for the congruent number curves `E_n : y² = x³ - n²x`, `n = 1` and `n` odd squarefree, with no
named input, so the first theorem applies to them.

**Conditional theorems.** Each has the form *(named input) → statement*; the named input is a `Prop` structure
whose field is a classical theorem the library does not prove, with its source. Inputs are hypotheses, not axioms,
so `#print axioms` shows only the standard axioms. All locators below are unverified.

## Named inputs (assumed, not proved here)

* `ModularFormsKB.Elliptic.ModularityTheorem`: the modularity theorem (A. Wiles, *Modular elliptic curves and
  Fermat's Last Theorem*, Ann. of Math. 141 (1995); R. Taylor and A. Wiles, 1995; C. Breuil, B. Conrad, F. Diamond and
  R. Taylor, J. Amer. Math. Soc. 14 (2001); Milne, Theorem 11.24): every elliptic curve `E` over `ℚ` has a newform of
  weight 2, trivial character and level the geometric conductor of `E`, whose coefficients are those of `L(E, s)`.
* `ModularFormsKB.Elliptic.NewformOfConductor`: newness from the conductor (A. O. L. Atkin and J. Lehner, 1970;
  W.-C. W. Li, 1975; Miyake, Theorems 4.6.13 and 4.6.19): a cusp form of weight 2 on `Γ₁(N)`, invariant under
  `Γ₀(N)`, with `N` the geometric conductor of `E` and the coefficients of `L(E, s)`, is a newform of level `N`.

## Definitions used

Besides Mathlib (`WeierstrassCurve`, `WeierstrassCurve.LFunction`, the arithmetic function of the L-series of `E`,
`LSeries`, `LSeries.HasEntireExtension`, `Complex.Gamma`) and Tau Ceti (`HeckeRing.GL2.Newform N k`, newforms of level
`N` and weight `k`, with nebentypus `f.χ`; `LSeries.IsContinuationOn a F U`: `F` is analytic on the connected open
set `U` and equals the L-series of `a` where it converges), the statements use these definitions of the library:

* `ModularFormsKB.Elliptic.HasNewform E N f`: `f.χ = 1` and the `n`-th Fourier coefficient of `f` at `∞` is
  `E.LFunction n` for every `n`;
* `ModularFormsKB.Elliptic.coeffE E n`: `E.LFunction n` as a complex number;
* `ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.congruentCurve n`: the Weierstrass curve
  `y² = x³ - n²x` over `ℚ` (`a₁ = a₂ = a₃ = a₆ = 0`, `a₄ = -n²`);
* `ModularFormsKB.Milne.Wave4B.geometricConductor E`: the conductor of `E` (Milne, page 111), the norm of Tau Ceti's
  conductor ideal `WeierstrassCurve.algorithmicConductor ℤ E` (from Tate's algorithm);
* `ModularFormsKB.Milne.Wave4B.StrongHasseWeil E`: Milne's Conjecture 11.17. For every `m ≥ 1` prime to the conductor
  `N` and every primitive Dirichlet character `χ` modulo `m`, the completed twisted L-functions
  `Λ_χ(E, s) = N^{s/2} (m/2π)^s Γ(s) Σ a_n χ(n) n^{-s}` (`completedTwistedLSeries`) and `Λ_χ̄(E, s)` have
  entire continuations bounded in vertical strips (`IsBoundedEntireContinuation`), with
  `Λ_χ(E, s) = ± χ(N) g(χ)/g(χ̄) · Λ_χ̄(E, 2 - s)` (`g` the Gauss sum);
* `ModularFormsKB.Elliptic.StrongHasseWeilUniform E w`: the same with one sign `w = ±1` for all `χ`, in the form
  `Λ_χ(E, s) = w χ(-1) χ(N) g(χ)/g(χ̄) · Λ_χ̄(E, 2 - s)`.
-/

namespace ModularFormsKB.Headlines

section EllipticCurves

open UpperHalfPlane ModularForm CongruenceSubgroup Complex
open scoped MatrixGroups Real
open HeckeRing.GL2 ModularFormsKB.Milne.Wave4B ModularFormsKB.Elliptic
open ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves (congruentCurve)

/-- **L-function, functional equation and parity of an elliptic curve with a newform** (Milne, section 11, after
Theorem 11.19). Let `E` over `ℚ` have the newform `f` of level `N`. Then `L(E, s)` has an entire extension, and there
are an entire `Λ` and a sign `w = ±1` with `Λ(s) = N^{s/2} (2π)^{-s} Γ(s) L(E, s)` for `Re s > 3/2` and
`Λ(2 - s) = w Λ(s)`; if `w = -1`, every continuation of `L(E, s)` to a connected open set containing `1` vanishes at
`s = 1`. -/
theorem elliptic_hasNewform_functionalEquation (E : WeierstrassCurve ℚ) [E.IsElliptic] {N : ℕ} [NeZero N]
    {f : Newform N 2} (hf : HasNewform E N f) :
    LSeries.HasEntireExtension (coeffE E) ∧
    ∃ Λ : ℂ → ℂ, ∃ w : ℂ, Differentiable ℂ Λ ∧ (w = 1 ∨ w = -1) ∧
      (∀ s : ℂ, 3 / 2 < s.re → Λ s = (N : ℂ) ^ (s / 2) * (2 * π : ℂ) ^ (-s) * Gamma s *
        LSeries (coeffE E) s) ∧
      (∀ s : ℂ, Λ (2 - s) = w * Λ s) ∧
      (w = -1 → ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄, LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U → 1 ∈ U →
        F 1 = 0) := by
  sorry

/-- **Modular implies strong Hasse–Weil** (Milne, Theorem 11.19, one direction, analytic form): an elliptic curve over
`ℚ` with a newform of level its conductor satisfies Milne's strong Hasse–Weil conjecture (Conjecture 11.17). -/
theorem elliptic_hasNewform_strongHasseWeil {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {f : Newform (geometricConductor E) 2} (hf : HasNewform E (geometricConductor E) f) :
    StrongHasseWeil E := by
  sorry

/-- **The curve `E_1 : y² = x³ - x` has a newform of level 32** (unconditional; new in 0.5.0): there is a newform
`f` of level 32, weight 2 and trivial character (Tau Ceti's `Newform`) whose Fourier coefficients are those of
Mathlib's `L`-function of `E_1`. The newform is `f₃₂ = η(4τ)²η(8τ)²`, the theta series of the Hecke character
`α ↦ α` of `ℚ(i)` modulo `2 + 2i`; newness comes from the vanishing of `S₂(Γ₀(16))`. -/
theorem elliptic_congruentCurve_one_hasNewform :
    ∃ f : Newform 32 2, HasNewform (congruentCurve 1) 32 f := by
  sorry

/-- **The congruent number curves `E_n : y² = x³ - n²x`, `n` odd squarefree, have a newform of level `32n²`**
(unconditional; new in 0.5.0): the newform is the twist of `f₃₂` by the Jacobi character `χ_n = (·/n)`, and its
level is exactly `32n²` (Atkin–Li 1978, Theorem 3.1, proved here for this twist). -/
theorem elliptic_congruentCurve_hasNewform {n : ℕ} [NeZero n] (hn : Odd n) (hsq : Squarefree n) :
    ∃ f : Newform (32 * n ^ 2) 2, HasNewform (congruentCurve n) (32 * n ^ 2) f := by
  sorry

/-- **Every elliptic curve over `ℚ`, conditional on the modularity theorem** (named input `ModularityTheorem`):
`E` satisfies the strong Hasse–Weil conjecture, `L(E, s)` is entire, and `Λ(E, s) = N^{s/2} (2π)^{-s} Γ(s) L(E, s)`
(`N` the conductor) is entire with `Λ(E, 2 - s) = w Λ(E, s)`, `w = ±1`; if `w = -1`, `L(E, 1) = 0` for every
continuation. -/
theorem elliptic_modularity_consequences (h : ModularityTheorem) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    StrongHasseWeil E ∧ LSeries.HasEntireExtension (coeffE E) ∧
    ∃ Λ : ℂ → ℂ, ∃ w : ℂ, Differentiable ℂ Λ ∧ (w = 1 ∨ w = -1) ∧
      (∀ s : ℂ, 3 / 2 < s.re → Λ s = (geometricConductor E : ℂ) ^ (s / 2) * (2 * π : ℂ) ^ (-s) * Gamma s *
        LSeries (coeffE E) s) ∧
      (∀ s : ℂ, Λ (2 - s) = w * Λ s) ∧
      (w = -1 → ∀ ⦃F : ℂ → ℂ⦄ ⦃U : Set ℂ⦄, LSeries.IsContinuationOn ((↑) ∘ E.LFunction) F U → 1 ∈ U →
        F 1 = 0) := by
  sorry

/-- **Milne's Theorem 11.19 in analytic form, both directions, conditional on newness from the conductor** (named
input `NewformOfConductor`; the converse direction is Weil's converse theorem, Miyake Theorem 4.3.15, which the
library proves): `E` has a newform of level its conductor if and only if it satisfies the strong Hasse–Weil
conjecture with a uniform sign `w`. -/
theorem elliptic_newform_iff_strongHasseWeil (hN : NewformOfConductor) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (∃ f : Newform (geometricConductor E) 2, HasNewform E (geometricConductor E) f) ↔
      ∃ w : ℂ, StrongHasseWeilUniform E w := by
  sorry

end EllipticCurves

end ModularFormsKB.Headlines
