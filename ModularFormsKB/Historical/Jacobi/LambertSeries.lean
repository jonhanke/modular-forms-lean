import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import ModularFormsKB.Citation
/-!
# Jacobi's Lambert series for `(2K/π)⁴` and his Euler-type expansions (`-00039`,
`-00051`)

Jacobi, *Fundamenta nova* (1829). In the nome `q` (`‖q‖ < 1`) write `ϑ₃ = ∑_{n ∈ ℤ} q^{n²}`,
`ϑ₄ = ∑_{n ∈ ℤ} (-1)ⁿ q^{n²}` and `ϑ₂⁴ = 16 q (∑_{n ≥ 0} q^{n(n+1)})⁴` (so that `ϑ₂ = 2 q^{1/4} ∑ q^{n(n+1)}`, and no root
of `q` is needed). With Jacobi's `2K/π = ϑ₃²`, `k = ϑ₂²/ϑ₃²`, `k' = ϑ₄²/ϑ₃²`:

* § 41, 3)–5): `ϑ₂⁴ ϑ₃⁴ = 16 ∑ n³ qⁿ/(1 - q^{2n}) = 16 ∑_{m odd} q^m (1 + 4q^m + q^{2m})/(1 - q^m)⁴`,
  `ϑ₂⁴ ϑ₄⁴ = 16 ∑ (-1)^{n-1} n³ qⁿ/(1 - q^{2n}) = 16 ∑_{m odd} q^m (1 - 4q^m + q^{2m})/(1 + q^m)⁴`, and
  `ϑ₂⁸ = 256 ∑ n³ q^{2n}/(1 - q^{4n})`;
* § 41: `(2K/π)⁴ (1 - k² + k⁴) = ϑ₃⁸ - ϑ₂⁴ ϑ₃⁴ + ϑ₂⁸ = 1 + 240 ∑ n³ q^{2n}/(1 - q^{2n})`, i.e.
  `E₄(q²) = ½ (ϑ₂⁸ + ϑ₃⁸ + ϑ₄⁸)`;
* § 64, lemmas 1), 2), pp. 180–181:
  `∏_{n ≥ 1} (1 + q^{2n-1} z) = ∑_{m ≥ 0} q^{m²} z^m / ((1 - q²)(1 - q⁴)⋯(1 - q^{2m}))` and
  `∏_{n ≥ 1} 1/(1 - qⁿ z) = ∑_{m ≥ 0} q^{m²} z^m / ((1 - q)⋯(1 - q^m)(1 - qz)⋯(1 - q^m z))` (for `‖q z‖ < 1` in the
  second).

All three are stated only (recorded as open): the theta identities need either the modularity of
`ϑ₂⁸ + ϑ₃⁸ + ϑ₄⁸` for `SL₂(ℤ)` and of `ϑ₂⁴ ϑ₃⁴` for a congruence subgroup, or Jacobi's own route through the
elliptic functions (the identification of `ϑ₃²` with `2K/π`, `JacobiSnThetaQuotient`), none of which this library or
its dependencies provide yet.
-/

noncomputable section

open Complex Finset

namespace ModularFormsKB.Historical.Jacobi

/-- `ϑ₃(q) = ∑_{n ∈ ℤ} q^{n²}`. -/
def nomeTheta3 (q : ℂ) : ℂ := ∑' n : ℤ, q ^ (n.natAbs ^ 2)

/-- `ϑ₄(q) = ∑_{n ∈ ℤ} (-1)ⁿ q^{n²}`. -/
def nomeTheta4 (q : ℂ) : ℂ := ∑' n : ℤ, (-1) ^ n.natAbs * q ^ (n.natAbs ^ 2)

/-- `ϑ₂(q)⁴ = 16 q (∑_{n ≥ 0} q^{n(n+1)})⁴`. -/
def nomeTheta2Four (q : ℂ) : ℂ := 16 * q * (∑' n : ℕ, q ^ (n * (n + 1))) ^ 4

/-- **Jacobi, *Fundamenta nova*, § 41, 3)–5)**: the Lambert series for
`k²(2K/π)⁴ = ϑ₂⁴ϑ₃⁴`, `k²k'²(2K/π)⁴ = ϑ₂⁴ϑ₄⁴` and `(2kK/π)⁴ = ϑ₂⁸`. -/
@[kb "jacobi1829" "§ 41, 3)–5)"]
def JacobiLambertCubes : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun n : ℕ ↦ 16 * ((n + 1 : ℕ) : ℂ) ^ 3 * q ^ (n + 1) / (1 - q ^ (2 * (n + 1))))
        (nomeTheta2Four q * nomeTheta3 q ^ 4) ∧
    HasSum (fun j : ℕ ↦ 16 * (q ^ (2 * j + 1) * (1 + 4 * q ^ (2 * j + 1) + q ^ (2 * (2 * j + 1))) /
        (1 - q ^ (2 * j + 1)) ^ 4)) (nomeTheta2Four q * nomeTheta3 q ^ 4) ∧
    HasSum (fun n : ℕ ↦ 16 * (-1) ^ n * ((n + 1 : ℕ) : ℂ) ^ 3 * q ^ (n + 1) / (1 - q ^ (2 * (n + 1))))
        (nomeTheta2Four q * nomeTheta4 q ^ 4) ∧
    HasSum (fun j : ℕ ↦ 16 * (q ^ (2 * j + 1) * (1 - 4 * q ^ (2 * j + 1) + q ^ (2 * (2 * j + 1))) /
        (1 + q ^ (2 * j + 1)) ^ 4)) (nomeTheta2Four q * nomeTheta4 q ^ 4) ∧
    HasSum (fun n : ℕ ↦ 256 * ((n + 1 : ℕ) : ℂ) ^ 3 * q ^ (2 * (n + 1)) / (1 - q ^ (4 * (n + 1))))
        (nomeTheta2Four q ^ 2)

/-- **Jacobi, *Fundamenta nova*, § 41**:
`(2K/π)⁴(1 - k² + k⁴) = ϑ₃⁸ - ϑ₂⁴ϑ₃⁴ + ϑ₂⁸ = 1 + 240 ∑ n³ q^{2n}/(1 - q^{2n})`. -/
@[kb "jacobi1829" "§ 41"]
def JacobiLambertE4 : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    HasSum (fun n : ℕ ↦ 240 * ((n + 1 : ℕ) : ℂ) ^ 3 * q ^ (2 * (n + 1)) / (1 - q ^ (2 * (n + 1))))
      (nomeTheta3 q ^ 8 - nomeTheta2Four q * nomeTheta3 q ^ 4 + nomeTheta2Four q ^ 2 - 1)

/-- **Jacobi, *Fundamenta nova*, § 64, lemmas 1), 2)** (pp. 180–181). -/
@[kb "jacobi1829" "§ 64, 1)–2), pp. 180–181"]
def JacobiEulerExpansions : Prop :=
  (∀ q z : ℂ, ‖q‖ < 1 →
    HasProd (fun n : ℕ ↦ 1 + q ^ (2 * n + 1) * z)
      (∑' m : ℕ, q ^ (m ^ 2) * z ^ m / ∏ j ∈ range m, (1 - q ^ (2 * (j + 1))))) ∧
  ∀ q z : ℂ, ‖q‖ < 1 → ‖q * z‖ < 1 →
    HasProd (fun n : ℕ ↦ (1 - q ^ (n + 1) * z)⁻¹)
      (∑' m : ℕ, q ^ (m ^ 2) * z ^ m / ∏ j ∈ range m, ((1 - q ^ (j + 1)) * (1 - q ^ (j + 1) * z)))

end ModularFormsKB.Historical.Jacobi
