/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.HalfIntegral.Waldspurger.Tunnell
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Criterion

/-!
# Headline statements of modular-forms-lean 0.5.0: Congruent numbers and Tunnell's criterion

The main results of the library for congruent numbers and Tunnell's criterion, one theorem each (a few closely related
concrete facts are combined into one conjunction), with every proof a deliberate `sorry`: to check what is claimed,
read this file. `Solution_CongruentNumbers.lean` proves the same statements from the library, and `lake comparator`
(configured by `comparator/CongruentNumbers.json`) checks that each proved statement is exactly the one here and uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. The statements were not yet reviewed by a human (see the README).

A positive integer `n` is *congruent* if it is the area of a right triangle with rational sides (`IsCongruent`).

**Unconditional theorems** (no named input; `#print axioms` shows only the standard axioms): `n` is congruent iff the
elliptic curve `E_n : y² = x³ - n²x` has a rational point with `y ≠ 0`; the right triangles with rational sides that
exhibit `5`, `6`, `7` and `41` as congruent; Tunnell's counts `A(n) = #{x² + 2y² + 8z² = n}` and
`B(n) = #{x² + 2y² + 32z² = n}` (for odd `n`), `C(n) = #{x² + 4y² + 8z² = n/2}` and `D(n) = #{x² + 4y² + 32z² = n/2}`
(for even `n`) for small `n`; and the consistency of the criterion for `n = 5`.

**Conditional theorems.** Each has the form *(named inputs) → statement*: its hypotheses are named `Prop` structures
whose fields are classical theorems that the library does not prove, each with its source. The inputs are hypotheses,
not axioms, so `#print axioms` shows only the standard axioms. The theorem says: whoever proves the named inputs has
proved the conclusion. All locators below (theorem or page numbers) are unverified: the papers were not checked.

## Named inputs for the conditional theorems (assumed, not proved here)

* `ModularFormsKB.HalfIntegral.Waldspurger.Tunnell.TunnellFormula`: J. B. Tunnell, *A classical Diophantine problem and
  modular forms of weight 3/2*, Invent. Math. 72 (1983), Theorem 2 (locator unverified; the proof there rests on
  Waldspurger's theorem for forms of weight 3/2). For squarefree `n`, with `Lval n = L(E_n, 1)` and
  `β = ∫₁^∞ dx / √(x³ - x)`: `L(E_n, 1) = β (A(n) - 2B(n))² / (16 √n)` for odd `n` and
  `L(E_n, 1) = β (C(n) - 2D(n))² / (8 √n)` for even `n`. Both constants were checked numerically for all squarefree
  `n ≤ 59`;
* `ModularFormsKB.HalfIntegral.Waldspurger.Tunnell.CoatesWiles`: J. Coates and A. Wiles, *On the conjecture of Birch
  and Swinnerton-Dyer*, Invent. Math. 39 (1977) (locator unverified): for the curves `E_n`, which have complex
  multiplication by `ℤ[i]`, if `L(E_n, 1) ≠ 0` then `E_n(ℚ)` is finite, so it consists of the four points of order
  dividing 2 and has no point with `y ≠ 0`.

In the theorems of 0.3.0 the value `L(E_n, 1)` enters only through the abstract function `Lval : ℕ → ℝ`, which is
constrained only by the named inputs (jointly): it is not defined from the curve. The theorems new in 0.5.0 (section
`CongruentCurves` below) use instead the true L-function: the L-series of Mathlib's `WeierstrassCurve.LFunction` of
`E_n`, which the library continues to an entire function (`congruent_curve_modular`), and its value at `1`.

## Named inputs of the 0.5.0 theorems with the true L-function (assumed, not proved here)

The structure `ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellInputs` bundles:

* `WaldspurgerSquareClassFull thetaMultiplierSystem 1 32 χ` for the trivial character and for `(2/·)` modulo 128:
  Waldspurger's theorem on square classes (J.-L. Waldspurger, J. Math. Pures Appl. 60 (1981), Corollaire 2) at level
  128 and weight 3/2, for all squarefree `n₁, n₂` in one square class at the primes dividing 128;
* `TunnellEigenforms`: Tunnell's eigenform proposition (Tunnell 1983): Shimura's `T(p²)`, `p` odd, acts on the
  coefficients of Tunnell's two forms `η(8τ)η(16τ)θ(2τ)` and `η(8τ)η(16τ)θ(4τ)` by the `p`-th coefficient of `f₃₂`
  (checked numerically);
* `TunnellConstants`: Tunnell's four central values `L(E_1, 1) = β/4`, `L(E_3, 1) = β/√3`, `L(E_2, 1) = β/(2√2)`,
  `L(E_10, 1) = 2β/√10` (Tunnell 1983; exact values of Hecke L-functions of `ℚ(i)`; checked numerically).

and, separately:

* `CoatesWilesCM`: the theorem of Coates and Wiles (J. Coates and A. Wiles, *On the conjecture of Birch and
  Swinnerton-Dyer*, Invent. Math. 39 (1977), Theorem 1): an elliptic curve `E` over `ℚ` with complex multiplication by
  the maximal order of an imaginary quadratic field (over `ℚ`: `j(E)` is one of the nine values `cmMaximalJ`) and
  `L(E, 1) ≠ 0` (for a continuation of the true L-series of Mathlib's `E.LFunction` to a connected open set containing
  `1`) has finitely many rational points. The library applies it to `E_n`, whose `j`-invariant is `1728`.

Two former inputs are proved in the library and are no longer fields of `TunnellInputs`: Tunnell's two `q`-series
`η(8τ)η(16τ)θ(2τ)` and `η(8τ)η(16τ)θ(4τ)` are cusp forms of weight 3/2 on `Γ₀(128)` (`tunnellMembership`), and the
functional equation of `L(E_{2m}, s)` with its sign (`heckeCharacterRootNumber`).

The equivalences `congruent_isCongruent_iff_odd_trueL` and `..._even_trueL` assume in addition Tau Ceti's statement
of the Birch and Swinnerton-Dyer conjecture for `E_n` (`WeierstrassCurve.BirchSwinnertonDyer`), a conjecture and not
a theorem; nothing in this file asserts it.

## Conditional on the weak Birch and Swinnerton-Dyer conjecture (a conjecture, not a theorem)

The two criteria `isCongruent_iff_odd` and `isCongruent_iff_even` below need, besides `TunnellFormula` and
`CoatesWiles`, the structure `ModularFormsKB.HalfIntegral.Waldspurger.Tunnell.WeakBSD`. This is the weak Birch and
Swinnerton-Dyer conjecture for the curves `E_n`, as a hypothesis and not as a theorem: if `L(E_n, 1) = 0` then `E_n(ℚ)`
is infinite, hence has a point with `y ≠ 0`. It is open (the conjecture of B. J. Birch and H. P. F. Swinnerton-Dyer).
Nothing in this file asserts it; the two theorems say only that, if it holds, Tunnell's
criterion is an equivalence.

## Definitions used

Besides Mathlib, the statements use these definitions of the library, in the namespace
`ModularFormsKB.HalfIntegral.Waldspurger.Tunnell`; a reader checking a statement should check them too:

* `IsCongruent` (`∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a² + b² = c² ∧ a b / 2 = n`) and `HasPointYNeZero`
  (`∃ x y : ℚ, y ≠ 0 ∧ y² = x³ - n² x`);
* `repCount α β m` (the number of `(x, y, z) ∈ ℤ³` with `x² + α y² + β z² = m`, counted in a box that contains every
  solution), `tunnellA`, `tunnellB`, `tunnellC`, `tunnellD`;
* the named inputs `TunnellFormula`, `CoatesWiles` and `WeakBSD`.

and (0.5.0), in the namespace `ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves`:

* `congruentCurve n` (Mathlib's Weierstrass curve `y² = x³ - n²x` over `ℚ`), `f32Coeff m` (`b(m)`, the sum of
  `Re α` over the Gaussian integers `α = a + ci` with `a² + c² = m`, `a` odd, `c` even, `a + c ≡ 1 mod 4`), `f32`
  (the function `τ ↦ Σ b(m) e^{2πimτ}`), `congruentCoeff n m = (n/m) b(m)` (Jacobi symbol), `lCoeff n m` (the
  `m`-th coefficient of `(congruentCurve n).LFunction`, as a complex number);
* `cmMaximalJ` (the nine `j`-invariants `0, 1728, -3375, 8000, -32768, -884736, -884736000, -147197952000,
  -262537412640768000` of the maximal orders of class number one);
* the named inputs `TunnellInputs` and `CoatesWilesCM`.
-/

namespace ModularFormsKB.Headlines

section CongruentNumbers

open ModularFormsKB.HalfIntegral.Waldspurger.Tunnell

/-! ### Unconditional -/

/-- **$n$ is congruent iff $E_n : y^2 = x^3 - n^2x$ has a rational point with $y \ne 0$.** -/
theorem congruent_isCongruent_iff_point {n : ℕ} (hn : 0 < n) : IsCongruent n ↔ HasPointYNeZero n := by
  sorry

/-- **Four congruent numbers:** the triangles $(3/2, 20/3, 41/6)$ for $5$ (Fibonacci), $(3, 4, 5)$ for $6$,
$(24/5, 35/12, 337/60)$ for $7$ (Euler) and $(40/3, 123/20, 881/60)$ for $41$. -/
theorem congruent_five_six_seven_fortyOne :
    IsCongruent 5 ∧ IsCongruent 6 ∧ IsCongruent 7 ∧ IsCongruent 41 := by
  sorry

/-- **Tunnell's counts for small $n$:** $A(1) = B(1) = 2$, $A(3) = B(3) = 4$, $A(5) = B(5) = 0$, $A(11) = 12$,
$B(11) = 4$ (odd $n$), and $C(2) = D(2) = 2$ (even $n$). -/
theorem congruent_tunnell_counts :
    tunnellA 1 = 2 ∧ tunnellB 1 = 2 ∧ tunnellA 3 = 4 ∧ tunnellB 3 = 4 ∧ tunnellA 5 = 0 ∧ tunnellB 5 = 0 ∧
      tunnellA 11 = 12 ∧ tunnellB 11 = 4 ∧ tunnellC 2 = 2 ∧ tunnellD 2 = 2 := by
  sorry

/-- **Consistency check:** $5$ is congruent and $A(5) = 2B(5)$, as Tunnell's criterion predicts. -/
theorem congruent_tunnell_five_consistent : IsCongruent 5 ∧ tunnellA 5 = 2 * tunnellB 5 := by
  sorry

/-! ### Conditional on Tunnell's formula and the theorem of Coates and Wiles -/

/-- **Tunnell's criterion, the direction without the Birch and Swinnerton-Dyer conjecture, odd $n$** (conditional
on the named inputs `TunnellFormula` and `CoatesWiles`): an odd squarefree $n$ with $A(n) \ne 2B(n)$ is not congruent. -/
theorem congruent_not_isCongruent_of_odd {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β)
    (hCW : CoatesWiles Lval) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (hodd : Odd n)
    (h : tunnellA n ≠ 2 * tunnellB n) : ¬ IsCongruent n := by
  sorry

/-- **Tunnell's criterion, the direction without the Birch and Swinnerton-Dyer conjecture, even $n$** (conditional
on `TunnellFormula` and `CoatesWiles`): an even
squarefree $n$ with $C(n) \ne 2D(n)$ is not congruent. -/
theorem congruent_not_isCongruent_of_even {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β)
    (hCW : CoatesWiles Lval) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (heven : Even n)
    (h : tunnellC n ≠ 2 * tunnellD n) : ¬ IsCongruent n := by
  sorry

/-- **$1$, $3$ and $11$ are not congruent** (conditional on `TunnellFormula` and `CoatesWiles`; here
$A - 2B = -2, -4, 4$). -/
theorem congruent_not_isCongruent_one_three_eleven {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β)
    (hCW : CoatesWiles Lval) : ¬ IsCongruent 1 ∧ ¬ IsCongruent 3 ∧ ¬ IsCongruent 11 := by
  sorry

/-! ### Conditional on the weak Birch and Swinnerton-Dyer conjecture -/

/-- **Tunnell's criterion, odd $n$, conditional on the weak Birch and Swinnerton-Dyer conjecture** (`WeakBSD`, a
conjecture, in addition to `TunnellFormula` and `CoatesWiles`): an odd squarefree $n$ is congruent iff
$A(n) = 2B(n)$. -/
theorem congruent_isCongruent_iff_odd {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β)
    (hCW : CoatesWiles Lval) (hBSD : WeakBSD Lval) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n) (hodd : Odd n) :
    IsCongruent n ↔ tunnellA n = 2 * tunnellB n := by
  sorry

/-- **Tunnell's criterion, even $n$, conditional on the weak Birch and Swinnerton-Dyer conjecture** (`WeakBSD`, a
conjecture, in addition to `TunnellFormula` and `CoatesWiles`): an even squarefree $n$ is congruent iff
$C(n) = 2D(n)$. -/
theorem congruent_isCongruent_iff_even {Lval : ℕ → ℝ} {β : ℝ} (hT : TunnellFormula Lval β)
    (hCW : CoatesWiles Lval) (hBSD : WeakBSD Lval) {n : ℕ} (hn : 0 < n) (hsq : Squarefree n)
    (heven : Even n) : IsCongruent n ↔ tunnellC n = 2 * tunnellD n := by
  sorry

end CongruentNumbers

/-! ## New in 0.5.0: the true L-function of `E_n` -/

section CongruentCurves

open Complex WeierstrassCurve ModularFormsKB.HalfIntegral.Waldspurger.Tunnell
open ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
open scoped Real

/-- **The congruent number curves are modular, with an entire L-function** (unconditional; new in 0.5.0). The
`q`-series `f₃₂ = Σ b(m) qᵐ`, `b(m) = Σ_{α primary, N(α) = m} Re α` over the Gaussian integers `α ≡ 1 mod (2 + 2i)`,
is a cusp form of weight 2 on `Γ₀(32)` (as a theta series of `ℤ[i]` with a harmonic polynomial and a
characteristic). For squarefree `n ≥ 1`, the coefficients of Mathlib's L-function of `E_n : y² = x³ - n²x` are
`(n/m) b(m)`, and its L-series has an entire extension. -/
theorem congruent_curve_modular :
    (∃ f : CuspForm ((CongruenceSubgroup.Gamma0 32).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2, ⇑f = f32) ∧
      ∀ (n : ℕ) [NeZero n], Squarefree n →
        (∀ m : ℕ, (congruentCurve n).LFunction m = congruentCoeff n m) ∧
          LSeries.HasEntireExtension (lCoeff n) := by
  sorry

/-- **Tunnell's criterion with the true L-function, the direction without the Birch and Swinnerton-Dyer conjecture,
odd `n`** (new in 0.5.0; conditional on the named inputs bundled in `TunnellInputs` and on `CoatesWilesCM`): an odd
squarefree `n` with `A(n) ≠ 2B(n)` is not congruent. Here `L(E_n, 1)` is the value at 1 of the continuation of the
L-series of Mathlib's `E_n`, not an abstract function. -/
theorem congruent_not_isCongruent_odd_trueL (h : TunnellInputs) (hCW : CoatesWilesCM) {n : ℕ} (hn : 0 < n)
    (hsq : Squarefree n) (hodd : Odd n) (hAB : tunnellA n ≠ 2 * tunnellB n) : ¬ IsCongruent n := by
  sorry

/-- **Tunnell's criterion with the true L-function, the direction without the Birch and Swinnerton-Dyer conjecture,
even `n`** (new in 0.5.0; conditional on `TunnellInputs` and `CoatesWilesCM`): an even squarefree `n` with
`C(n) ≠ 2D(n)` is not congruent. -/
theorem congruent_not_isCongruent_even_trueL (h : TunnellInputs) (hCW : CoatesWilesCM) {n : ℕ} (hn : 0 < n)
    (hsq : Squarefree n) (heven : Even n) (hCD : tunnellC n ≠ 2 * tunnellD n) : ¬ IsCongruent n := by
  sorry

/-- **Tunnell's criterion with the true L-function, odd `n`, conditional on the Birch and Swinnerton-Dyer conjecture
for `E_n`** (new in 0.5.0; the conjecture is Tau Ceti's statement `WeierstrassCurve.BirchSwinnertonDyer`, a
hypothesis, in addition to `TunnellInputs` and `CoatesWilesCM`): an odd squarefree `n` is congruent iff
`A(n) = 2B(n)`. -/
theorem congruent_isCongruent_iff_odd_trueL (h : TunnellInputs) (hCW : CoatesWilesCM) {n : ℕ} [NeZero n]
    (hsq : Squarefree n) (hodd : Odd n) (hBSD : (congruentCurve n).BirchSwinnertonDyer) :
    IsCongruent n ↔ tunnellA n = 2 * tunnellB n := by
  sorry

/-- **Tunnell's criterion with the true L-function, even `n`, conditional on the Birch and Swinnerton-Dyer conjecture
for `E_n`** (new in 0.5.0; as `congruent_isCongruent_iff_odd_trueL`): an even squarefree `n` is congruent iff
`C(n) = 2D(n)`. -/
theorem congruent_isCongruent_iff_even_trueL (h : TunnellInputs) (hCW : CoatesWilesCM) {n : ℕ} [NeZero n]
    (hsq : Squarefree n) (heven : Even n) (hBSD : (congruentCurve n).BirchSwinnertonDyer) :
    IsCongruent n ↔ tunnellC n = 2 * tunnellD n := by
  sorry

end CongruentCurves

end ModularFormsKB.Headlines
