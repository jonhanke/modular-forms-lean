/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Historical.WeberHeegnerStark.Main

/-!
# Headline statements of modular-forms-lean 0.3.1: the class number one theorem (Heegner, Stark), conditional, proved

The statements of `Challenge_HeegnerStark.lean`, each proved by appeal to the library theorem. `lake comparator`
(configured by `comparator/HeegnerStark.json`) checks that each statement here is exactly the one in
`Challenge_HeegnerStark.lean` and that its proof uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

**These are conditional theorems.** Each has the form *(named inputs) → statement*: its first hypothesis is a named
`Prop` structure whose fields are classical theorems that the library does not prove, each with its source. The
inputs are hypotheses, not axioms, so `#print axioms` shows only the standard axioms. The theorem says: whoever proves
the named inputs has proved the conclusion. No field of an input mentions class number one, the nine discriminants
or Heegner's Diophantine equation.

## Named inputs (assumed, not proved here)

`ModularFormsKB.WeberHeegnerStark.WeberHeegnerStarkInputs`, eight classical theorems (section numbers of H. Weber,
*Elliptische Functionen und algebraische Zahlen*, 1891; its second edition is *Lehrbuch der Algebra*, volume III,
1908):

* `isIntegral_kleinJ`: singular moduli `j(τ)` are algebraic integers (Weber § 87);
* `finrank_kleinJ`: `[ℚ(j(τ)) : ℚ] = h(D)` for the root `τ` of a primitive form of discriminant `D` (Weber § 88;
  the first main theorem of complex multiplication);
* `imaginaryQuadratic`: the discriminant `d_K` of an imaginary quadratic field is a fundamental discriminant and its
  class number is the number `h(d_K)` of classes of primitive positive definite forms (Dirichlet, Dedekind);
* `classNumber_four_mul`: `h(-4m) = 3 h(-m)` for `m ≡ 3 mod 8`, `m > 3` (Weber § 89);
* `gammaTwo_mem`: `γ₂(τ) ∈ ℚ(j(τ))` when `3 ∤ D`, `3 ∤ a`, `3 ∣ b` (Weber § 92);
* `weberF_pow_eight_mem`: Weber's Theorem I, `f(√-m)⁸ ∈ ℚ(j(√-m))` for odd `m`, `3 ∤ m` (Weber § 94);
* `weberF_pow_three_mem`: Weber's Theorem VI, `f(√-m)³ ∈ ℚ(j(√-m))` for `m ≡ 3 mod 8`, `3 ∤ m` (Weber § 94,
  stated by Weber without a complete proof: the "gap" in Heegner's proof that Stark closed);
* `weber_cubic`: `(f₂²⁴ + 16)³ = j f₂²⁴` (Weber § 93 (1); proved in Tau Ceti for its Siegel function
  `g_{(0,1/2)}`, with `g_{(0,1/2)}¹² = f₂²⁴`).

`ModularFormsKB.WeberHeegnerStark.QuadraticDiscriminantInput` (second theorem only): the discriminant of `ℚ(√m)`
is `m` or `4m` (Dedekind).

Proved here, without inputs: Gauss's reduction of `h(D) = 1` to `D ∈ {-3, -4, -7, -8}` or `D = -p` with `p ≡ 3
mod 8` prime; `h(D) = 1` for the nine discriminants; Heegner's step (K. Heegner, *Diophantische Analysis und
Modulfunktionen*, 1952) from Weber's class invariants to the equation `y² = 2u(u³ + 1)`; its integer points; and
the numerical enclosure of `j((-3 + √-p)/2)` that recovers `p`. H. M. Stark (1967) gave an independent proof of the
theorem.

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
them too:

* `ModularFormsKB.WeberHeegnerStark.WeberHeegnerStarkInputs` and
  `ModularFormsKB.WeberHeegnerStark.QuadraticDiscriminantInput` (the named inputs above);
* in their fields: `kleinJ` (`j = E₄³ / Δ`), `gammaTwo` (`γ₂ = E₄ / η⁸`), `weberF` and `weberF₂` (Weber's `f` and
  `f₂` as quotients of Mathlib's `η`), `IsPrimitiveForm`, `IsFormRoot`, `IsReducedForm`, `reducedForms` and
  `formClassNumber` (`h(D)`, the number of reduced primitive positive definite forms of discriminant `D`), all in
  the namespace `ModularFormsKB.WeberHeegnerStark`.

The conclusions use only Mathlib: `NumberField.classNumber`, `NumberField.discr`.
-/

namespace ModularFormsKB.Headlines

section HeegnerStark

open NumberField Module ModularFormsKB.WeberHeegnerStark

/-- **The class number one theorem (Heegner 1952, Stark 1967), conditional on Weber's theorems.**
Given the named inputs `WeberHeegnerStarkInputs`, an imaginary quadratic field `K` has class number one if and only
if its discriminant is `-3, -4, -7, -8, -11, -19, -43, -67` or `-163`, that is, `K = ℚ(√-d)` for
`d = 3, 1, 7, 2, 11, 19, 43, 67, 163`.

Related: Tau Ceti (at the pinned commit) proves the direction "the nine fields have class number one"
(`TauCeti.NumberField.classNumber_eq_one_of_mem_heegnerDiscriminants`) and the classification for `|d_K| < 51`
(`TauCeti.NumberField.classNumber_eq_one_iff_of_neg_fifty_one_lt_discr`); the direction "class number one implies one of the nine",
here from the named inputs, is in neither Tau Ceti nor Mathlib. -/
theorem heegnerStark_classNumber_eq_one_iff (hin : WeberHeegnerStarkInputs) (K : Type) [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    classNumber K = 1 ↔
      discr K ∈ ({-3, -4, -7, -8, -11, -19, -43, -67, -163} : Finset ℤ) := by
  exact ModularFormsKB.WeberHeegnerStark.heegnerStark_classNumber_eq_one_iff hin K hK hD

/-- **The class number one theorem, in Gauss's form, conditional.** Given the named inputs
`WeberHeegnerStarkInputs` and `QuadraticDiscriminantInput`, an imaginary quadratic field `K` has class number one
if and only if `K = ℚ(√-d)` for some `d ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`, that is, `-d` is a square in `K`. -/
theorem heegnerStark_classNumber_eq_one_iff_isSquare (hin : WeberHeegnerStarkInputs)
    (hq : QuadraticDiscriminantInput) (K : Type) [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) (hD : discr K < 0) :
    classNumber K = 1 ↔
      ∃ d ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ), IsSquare (-(d : K)) := by
  exact ModularFormsKB.WeberHeegnerStark.heegnerStark_classNumber_eq_one_iff_isSquare hin hq K hK hD

end HeegnerStark

end ModularFormsKB.Headlines
