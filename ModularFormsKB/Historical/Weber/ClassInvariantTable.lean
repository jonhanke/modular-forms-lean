import ModularFormsKB.Historical.Weber.ThetaEta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weber's table of class invariants (first rows)

Weber, *Elliptische Functionen und algebraische Zahlen* (1891), Anhang, "Verzeichniss von
Classeninvarianten", pp. 499–504, and *Lehrbuch der Algebra* III (1908), Tabelle VI, pp. 721–726: about 105
values, for `m = 1, …, 1848`, of a power of `f(√-m)` or `f₁(√-m)` (times a power of 2), in radicals or as a root
of an equation over a small quadratic field.

This file states the first nine rows of Tabelle VI (p. 721), `m = 1, …, 9`, each as a named proposition, and
collects them in `WeberTableVIFirstRows`. None is proved: every row is a special value of an `η`-quotient at a
CM point, which needs either the theory of complex multiplication (Weber's route: the value is a class
invariant, a root of an explicit equation, located numerically) or explicit evaluations of `η` at CM points
(Chowla–Selberg type), none of which is in Mathlib. The rows have been checked numerically from the
`q`-products (agreement to `10⁻¹⁵`). The remaining ~96 rows of the table are not transcribed (loose end).

The point `√-m` is `τ = i√m` in the upper half-plane; `f = weberF`, `f₁ = weberF₁`.
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Weber

open ModularFormsKB.WeberHeegnerStark (weberF)

/-- The point `√-m = i√m` of the upper half-plane. -/
def sqrtNeg (m : ℕ) : ℂ := I * ((√(m : ℝ) : ℝ) : ℂ)

/-- Tabelle VI, `m = 1`: `f(√-1) = ⁴√2`. -/
@[kb "weber1908" "Tabelle VI, m = 1, p. 721"]
def TableRow1 : Prop := weberF (sqrtNeg 1) = ((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ)

/-- Tabelle VI, `m = 2`: `f₁(√-2) = ⁴√2`. -/
@[kb "weber1908" "Tabelle VI, m = 2, p. 721"]
def TableRow2 : Prop := weberF₁ (sqrtNeg 2) = ((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ)

/-- Tabelle VI, `m = 3`: `f(√-3) = ∛2`. -/
@[kb "weber1908" "Tabelle VI, m = 3, p. 721"]
def TableRow3 : Prop := weberF (sqrtNeg 3) = ((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ)

/-- Tabelle VI, `m = 4`: `f₁(√-4) = ⁸√8`. -/
@[kb "weber1908" "Tabelle VI, m = 4, p. 721"]
def TableRow4 : Prop := weberF₁ (sqrtNeg 4) = ((8 : ℝ) ^ (1 / 8 : ℝ) : ℝ)

/-- Tabelle VI, `m = 5`: `f(√-5)⁴ = 1 + √5`. -/
@[kb "weber1908" "Tabelle VI, m = 5, p. 721"]
def TableRow5 : Prop := weberF (sqrtNeg 5) ^ 4 = ((1 + √5 : ℝ) : ℂ)

/-- Tabelle VI, `m = 6`: `f₁(√-6)⁶ = 4 + 2√2`. -/
@[kb "weber1908" "Tabelle VI, m = 6, p. 721"]
def TableRow6 : Prop := weberF₁ (sqrtNeg 6) ^ 6 = ((4 + 2 * √2 : ℝ) : ℂ)

/-- Tabelle VI, `m = 7`: `f(√-7) = √2`. -/
@[kb "weber1908" "Tabelle VI, m = 7, p. 721"]
def TableRow7 : Prop := weberF (sqrtNeg 7) = ((√2 : ℝ) : ℂ)

/-- Tabelle VI, `m = 8`: `f₁(√-8)⁸ = 8 + 8√2`. -/
@[kb "weber1908" "Tabelle VI, m = 8, p. 721"]
def TableRow8 : Prop := weberF₁ (sqrtNeg 8) ^ 8 = ((8 + 8 * √2 : ℝ) : ℂ)

/-- Tabelle VI, `m = 9`: `f(√-9)³ = ⁴√2 (1 + √3)`. -/
@[kb "weber1908" "Tabelle VI, m = 9, p. 721"]
def TableRow9 : Prop := weberF (sqrtNeg 9) ^ 3 = (((2 : ℝ) ^ (1 / 4 : ℝ) * (1 + √3) : ℝ) : ℂ)

/-- **Weber's Tabelle VI, rows `m = 1, …, 9`** (Weber 1908, p. 721; Weber 1891, Anhang, p. 499), as a proposition. Stated, not proved. -/
@[kb "weber1908" "Tabelle VI, pp. 721–726"]
def WeberTableVIFirstRows : Prop :=
  TableRow1 ∧ TableRow2 ∧ TableRow3 ∧ TableRow4 ∧ TableRow5 ∧ TableRow6 ∧ TableRow7 ∧ TableRow8 ∧
    TableRow9

end ModularFormsKB.Historical.Weber
