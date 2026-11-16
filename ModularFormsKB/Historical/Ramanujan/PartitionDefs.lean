import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import ModularFormsKB.Citation
/-!
# Ramanujan's congruences for the partition function: definitions and statements

Ramanujan, *Some properties of p(n), the number of partitions of n* (1919; *Collected Papers* 1927, No. 25),
*Congruence properties of partitions* (1919; No. 28) and the posthumous manuscript of the same title (No. 30),
together with the values of `p(n)` of Hardy–Ramanujan (1918; No. 36).

All power series here are formal, with integer coefficients (`ℤ⟦X⟧`); infinite products are taken in the
coefficientwise ("pi") topology, in which `∏_{n ≥ 1} (1 - Xⁿ)` converges. A congruence of power series modulo
`m` means a congruence of every coefficient.

* `partitionCount n` is `p(n)`, the number of partitions of `n` (Mathlib's `Nat.Partition n`).
* `partitionSeries = ∑ p(n) Xⁿ`, `eulerSeries = ∏_{n ≥ 1} (1 - Xⁿ)`, `eulerSeriesPow m = ∏_{n ≥ 1} (1 - X^{mn})`.
* `jacobiCubeSeries = ∑_{k ≥ 0} (-1)ᵏ (2k + 1) X^{k(k+1)/2}`, the right side of Jacobi's identity for the
  cube of Euler's product.

The statements are named propositions; the proofs are in `Congruences.lean`, `PartitionValues.lean` and
`TauModFive.lean`.
-/

noncomputable section

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Ramanujan

/-- `p(n)`, the number of partitions of `n`. -/
def partitionCount (n : ℕ) : ℕ := Fintype.card n.Partition

/-- The generating function `∑_{n ≥ 0} p(n) Xⁿ`. -/
def partitionSeries : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ (partitionCount n : ℤ)

/-- Euler's product `∏_{n ≥ 1} (1 - Xⁿ)` (index shifted to start at `0`). -/
def eulerSeries : ℤ⟦X⟧ := ∏' n : ℕ, (1 - X ^ (n + 1))

/-- `∏_{n ≥ 1} (1 - X^{mn})`, Euler's product in `X^m`. -/
def eulerSeriesPow (m : ℕ) : ℤ⟦X⟧ := ∏' n : ℕ, (1 - X ^ (m * (n + 1)))

/-- The coefficient of `X^N` in `∑_{k ≥ 0} (-1)ᵏ (2k + 1) X^{k(k+1)/2}`. -/
def jacobiCubeCoeff (N : ℕ) : ℤ :=
  ∑ k ∈ range (N + 1), if k * (k + 1) / 2 = N then (-1) ^ k * (2 * k + 1) else 0

/-- Jacobi's series `∑_{k ≥ 0} (-1)ᵏ (2k + 1) X^{k(k+1)/2} = 1 - 3X + 5X³ - 7X⁶ + ⋯`. -/
def jacobiCubeSeries : ℤ⟦X⟧ := PowerSeries.mk jacobiCubeCoeff

/-! ### Statements -/

/-- **Ramanujan No. 30, (2.2)**: for a prime `p`,
`∏ (1 - xⁿ)^{p²} ≡ ∏ (1 - x^{p²n}) (mod p)`, coefficientwise; stated with the companion
`∏ (1 - xⁿ)^p ≡ ∏ (1 - x^{pn})`, from which it follows. -/
@[kb "ramanujan1927" "No. 30, § 2, (2.2), p. 234"]
def EulerFrobenius : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n : ℕ,
    (eulerSeries ^ p).coeff n ≡ (eulerSeriesPow p).coeff n [ZMOD p] ∧
    (eulerSeries ^ (p ^ 2)).coeff n ≡ (eulerSeriesPow (p ^ 2)).coeff n [ZMOD p]

/-- **Ramanujan's congruence modulo 5** (No. 25, (1), p. 210; proof § 2, p. 211):
`p(5m + 4) ≡ 0 (mod 5)`. -/
@[kb "ramanujan1927" "No. 25, § 1, (1), p. 210; § 2, p. 211"]
def RamanujanModFive : Prop := ∀ m : ℕ, 5 ∣ partitionCount (5 * m + 4)

/-- **Ramanujan's congruence modulo 7** (No. 25, (2), p. 210; proof § 3, p. 212):
`p(7m + 5) ≡ 0 (mod 7)`. -/
@[kb "ramanujan1927" "No. 25, § 1, (2), p. 210; § 3, p. 212"]
def RamanujanModSeven : Prop := ∀ m : ℕ, 7 ∣ partitionCount (7 * m + 5)

/-- **Ramanujan's corollary modulo 35** (No. 25, (3), p. 210):
`p(35m + 19) ≡ 0 (mod 35)`. -/
@[kb "ramanujan1927" "No. 25, § 1, (3), p. 210"]
def RamanujanModThirtyFive : Prop := ∀ m : ℕ, 35 ∣ partitionCount (35 * m + 19)

/-- **Ramanujan's congruence modulo 11** (No. 28, p. 230; proof No. 30, § 4, (4.7), p. 237):
`p(11m + 6) ≡ 0 (mod 11)`. Stated, not proved. -/
@[kb "ramanujan1927" "No. 28, p. 230; No. 30, § 4, (4.7), p. 237"]
def RamanujanModEleven : Prop := ∀ m : ℕ, 11 ∣ partitionCount (11 * m + 6)

/-- **Ramanujan No. 30, (2.3)–(2.4)**:
`x ∏ (1 - x^{25n}) / ∏ (1 - xⁿ) ≡ ∑_{n ≥ 1} n σ₁(n) xⁿ (mod 5)`, i.e. with `1/∏(1 - xⁿ) = ∑ p(n) xⁿ`, the
coefficient of `xⁿ` in `x ∏ (1 - x^{25n}) ∑ p(k) x^k` is `≡ n σ₁(n) (mod 5)` for every `n`. -/
@[kb "ramanujan1927" "No. 30, § 2, (2.3)–(2.4), p. 234"]
def RamanujanTauModFive : Prop :=
  ∀ n : ℕ, (X * eulerSeriesPow 25 * partitionSeries).coeff n ≡ (n * σ 1 n : ℕ) [ZMOD 5]

/-- **Ramanujan's identity** (No. 25, § 4, (17), p. 213):
`∑_{m ≥ 0} p(5m + 4) x^m = 5 ∏ (1 - x^{5n})⁵ / ∏ (1 - xⁿ)⁶`, i.e. `5 ∏ (1 - x^{5n})⁵ (∑ p(k) x^k)⁶`.
Stated, not proved. -/
@[kb "ramanujan1927" "No. 25, § 4, (17), p. 213"]
def RamanujanFiveIdentity : Prop :=
  PowerSeries.mk (fun m ↦ (partitionCount (5 * m + 4) : ℤ)) =
    5 * eulerSeriesPow 5 ^ 5 * partitionSeries ^ 6

/-- **Values of `p(n)`** quoted by Hardy and Ramanujan (No. 36, § 1.7, pp. 283–284, from MacMahon's table):
`p(100) = 190569292`, `p(200) = 3972999029388`, and `p(61) = 1121505`,
`p(62) = 1300156`, `p(63) = 1505499`. (Only the values; the row's comparison with the asymptotic series is
not formalized.) -/
@[kb "ramanujan1927" "No. 36, § 1.7, pp. 283–284"]
def HardyRamanujanValues : Prop :=
  partitionCount 100 = 190569292 ∧ partitionCount 200 = 3972999029388 ∧
    partitionCount 61 = 1121505 ∧ partitionCount 62 = 1300156 ∧ partitionCount 63 = 1505499

/-- **The case `7³` fails** (a verification attached to No. 28, p. 230):
`p(243) = 133978259344888 ≡ 245 (mod 343)` although `24 · 243 ≡ 1 (mod 343)`; so Ramanujan's conjectured
congruence modulo `7³` for `24n ≡ 1 (mod 7³)` is false (it holds modulo `7²`). -/
@[kb "ramanujan1927" "No. 28, p. 230"]
def PartitionCount243 : Prop :=
  partitionCount 243 = 133978259344888 ∧ partitionCount 243 % 343 = 245 ∧ (24 * 243) % 343 = 1

end ModularFormsKB.Historical.Ramanujan
