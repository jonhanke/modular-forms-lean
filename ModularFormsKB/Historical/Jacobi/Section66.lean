import ModularFormsKB.Historical.Jacobi.TripleProduct
import ModularFormsKB.Historical.Ramanujan.JacobiCube
import ModularFormsKB.Citation
/-!
# *Fundamenta nova* § 66: the special cases of the triple product

Jacobi, *Fundamenta nova theoriae functionum ellipticarum* (1829), § 66, pp. 185–186, specialises the triple
product (§ 64, `triple_product`) to four product–series identities:

* 3) (`x = 0`): `∏ (1 - qⁿ)/(1 + qⁿ) = 1 - 2q + 2q⁴ - 2q⁹ + ⋯ = ∑_{n ∈ ℤ} (-1)ⁿ q^{n²}`
  (Gauss's identity for `ϑ₄(0)`);
* 4) (`x = π/2`): `∏ (1 - q^{2n})/(1 - q^{2n-1}) = 1 + q + q³ + q⁶ + ⋯ = ∑_{n ≥ 0} q^{n(n+1)/2}`
  (found also by Gauss, *Summatio serierum*);
* 5): `∏ (1 - qⁿ)³ = 1 - 3q + 5q³ - 7q⁶ + ⋯ = ∑_{n ≥ 0} (-1)ⁿ (2n+1) q^{n(n+1)/2}`;
* 7) (comparing 5) with Euler's pentagonal series 6)): `(1 - q - q² + q⁵ + q⁷ - ⋯)³ = 1 - 3q + 5q³ - 7q⁶ + ⋯`.

Products over `n ≥ 1` are written with the index shifted to start at `0`. Items 5) and 7) are wrappers of
results proved in `HistoricalRamanujan` (`Ramanujan.jacobi_cube_hasSum`, `Ramanujan.eulerSeries_cube`) and
Mathlib's pentagonal number theorem; items 3) and 4) are deduced from `triple_product` with `z = -1` and `z = q`
and Euler's identity `∏ (1 + qⁿ) ∏ (1 - q^{2n-1}) = 1`.
-/

noncomputable section

open Complex PowerSeries

namespace ModularFormsKB.Historical.Jacobi

/-- **Fundamenta nova § 66, 3)** (p. 185): for `‖q‖ < 1`,
`∏_{n ≥ 1} (1 - qⁿ)/(1 + qⁿ) = ∑_{n ∈ ℤ} (-1)ⁿ q^{n²}`. -/
@[kb "jacobi1829" "§ 66, 3), p. 185"]
def GaussThetaFourProduct : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun n : ℤ ↦ (-1 : ℂ) ^ n.natAbs * q ^ (n.natAbs ^ 2))
      (∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1)))

/-- **Fundamenta nova § 66, 4)** (p. 185): for `‖q‖ < 1`,
`∏_{n ≥ 1} (1 - q^{2n})/(1 - q^{2n-1}) = ∑_{n ≥ 0} q^{n(n+1)/2}`. -/
@[kb "jacobi1829" "§ 66, 4), p. 185"]
def TriangularProduct : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun n : ℕ ↦ q ^ (n * (n + 1) / 2))
      (∏' n : ℕ, (1 - q ^ (2 * n + 2)) / (1 - q ^ (2 * n + 1)))

/-- **Fundamenta nova § 66, 5)** (p. 185), Jacobi's identity for the cube of
Euler's product: for `‖q‖ < 1`, `∏_{n ≥ 1} (1 - qⁿ)³ = ∑_{n ≥ 0} (-1)ⁿ (2n + 1) q^{n(n+1)/2}`.
Wrapper of `Ramanujan.jacobi_cube_hasSum` (proved there from `triple_product_sin`). -/
@[kb "jacobi1829" "§ 66, 5), p. 185"]
theorem jacobi_cube {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ n * (2 * n + 1) * q ^ (n * (n + 1) / 2))
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ 3) :=
  Ramanujan.jacobi_cube_hasSum hq

/-- **Fundamenta nova § 66, 7)** (p. 186): the cube of Euler's pentagonal series
`∑_{k ∈ ℤ} (-1)ᵏ X^{k(3k-1)/2} = 1 - X - X² + X⁵ + X⁷ - ⋯` (Mathlib's `PowerSeries.pentagonalSeries`) is
`∑_{k ≥ 0} (-1)ᵏ (2k + 1) X^{k(k+1)/2}`, as formal power series over `ℤ`. Wrapper of
`Ramanujan.eulerSeries_cube` and `Ramanujan.eulerSeries_eq_pentagonalSeries` (Mathlib's pentagonal number
theorem). -/
@[kb "jacobi1829" "§ 66, 7), p. 186"]
theorem pentagonalSeries_cube :
    PowerSeries.pentagonalSeries ℤ ^ 3 = Ramanujan.jacobiCubeSeries := by
  rw [← Ramanujan.eulerSeries_eq_pentagonalSeries, Ramanujan.eulerSeries_cube]

end ModularFormsKB.Historical.Jacobi
