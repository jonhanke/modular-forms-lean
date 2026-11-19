import ModularFormsKB.Historical.Jacobi.TripleProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ModularFormsKB.Citation
/-!
# Smith, *Report on the Theory of Numbers* (1859–1865): elliptic and modular parts

H. J. S. Smith, *Report on the Theory of Numbers*, Part VI (Arts. 124–138), in *Collected Mathematical Papers* I
(1894); page numbers are those of the *Collected Papers*.

* `smith_triple_product` (art. 124, pp. 290–291): Jacobi's triple product
  `∑ q^{n²} vⁿ = ∏ (1 - q^{2m})(1 + q^{2m-1}v)(1 + q^{2m-1}/v)`. **Wrapper** of
  `ModularFormsKB.Historical.Jacobi.triple_product`. (Smith's printed (7) has `v` where his footnote says `v²`; the
  statement is the corrected one.)
* Art. 127, pp. 306–307:`ϑ₃(q)⁴ = 1 + 8 ∑ (2 + (-1)ⁿ) σ_odd(n) qⁿ`, i.e. Jacobi's four-square
  theorem `r₄(n) = 8(2 + (-1)ⁿ) σ_odd(n)`: **stated** as the named input
  `ModularFormsKB.Historical.Kronecker.JacobiFourSquares` (in `Kronecker/ClassNumberRelations.lean`, where
  Kronecker's class number relations use it), checked by the kernel for `n ≤ 12`. Its proof needs the
  `q`-expansion of `ϑ⁴` as a weight-two Eisenstein series on `Γ₀(4)`, not in Mathlib or Tau Ceti (LE-MF-0264).
* `SmithKroneckerLimitFormula` (art. 138, p. 354; Smith quotes Kronecker, *Monatsberichte*,
  22 January 1863, p. 44): Kronecker's second limit formula. **Stated** (LE-MF-0265).
-/

noncomputable section

open Complex Filter
open scoped Real Topology

namespace ModularFormsKB.Historical.Smith

/-- **Jacobi's triple product, as in Smith's Report** (art. 124, pp. 290–291): for
`|q| < 1` and `v ≠ 0`, `∑_{n ∈ ℤ} q^{n²} vⁿ = ∏_{m ≥ 1} (1 - q^{2m})(1 + q^{2m-1} v)(1 + q^{2m-1} v⁻¹)` (product
index shifted to start at `0`). A wrapper of `Jacobi.triple_product`. -/
@[kb "smith1894" "Report, art. 124, pp. 290-291: Jacobi's triple product"]
theorem smith_triple_product {q v : ℂ} (hq : ‖q‖ < 1) (hv : v ≠ 0) :
    HasSum (fun n : ℤ ↦ q ^ (n.natAbs ^ 2) * v ^ n)
      (∏' m : ℕ, (1 - q ^ (2 * m + 2)) * (1 + q ^ (2 * m + 1) * v) * (1 + q ^ (2 * m + 1) / v)) :=
  Jacobi.triple_product hq hv

/-- Smith's odd theta function `ϑ(x, ω) = 2 ∑_{n ≥ 0} (-1)ⁿ q^{(n+1/2)²} sin((2n+1)πx)`, `q^{(n+1/2)²} =
e^{iπω(n+1/2)²}` (Jacobi's `ϑ₁(πx | ω)`; Smith's `(1/i) θ_{1,1}(2Kx, ω)`).
**Restriction:** the series converges for `Im ω > 0` (for every `x`); for `Im ω ≤ 0` it diverges except in degenerate
cases such as `x ∈ ℤ` (every term `0`). Elsewhere the value is `0` by Lean's convention for a non-summable `∑'`, not an
analytic continuation or the intended value. -/
def smithTheta (x ω : ℂ) : ℂ :=
  2 * ∑' n : ℕ, (-1) ^ n * cexp (π * I * ω * ((n : ℂ) + 1 / 2) ^ 2) * Complex.sin ((2 * n + 1) * π * x)

/-- The twisted lattice sum `∑_{(x,y) ≠ 0} e^{2πi(σx + τy)} (ax² + 2bxy + cy²)^{-1-ρ}`. -/
def twistedLatticeSum (σ τ a b c ρ : ℝ) : ℂ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else
    cexp (2 * π * I * (σ * p.1 + τ * p.2)) /
      (((a * p.1 ^ 2 + 2 * b * p.1 * p.2 + c * p.2 ^ 2 : ℝ) ^ (1 + ρ) : ℝ) : ℂ)

/-- **Kronecker's second limit formula, as quoted in Smith's Report** (art. 138, p. 354), stated: for real `σ, τ` not both integers, `a > 0`, `Δ = ac - b² > 0`, `ω = (-b + i√Δ)/a`,
`ω' = (b + i√Δ)/a`,
`lim_{ρ→0⁺} ∑' e^{2πi(σx+τy)} (ax² + 2bxy + cy²)^{-1-ρ} = 2σ²π²/a + (π/(3√Δ)) log[(4π²)⁻¹ ϑ'(0,ω) ϑ'(0,ω')]
 - (π/√Δ) log[-ϑ(τ + σω, ω) ϑ(-τ + σω', ω')]`.
Since `ω' = -ω̄`, the two products in the logarithms are `|ϑ'(0, ω)|²` and `|ϑ(τ + σω, ω)|²`; they are written so
here (real logarithms, as Smith requires). The formula is as printed in the Report (read from the page image), not
independently re-derived (LE-MF-0265). -/
@[kb "smith1894" "Report, art. 138, p. 354: Kronecker's limit formula (second), stated"]
def SmithKroneckerLimitFormula : Prop :=
  ∀ σ τ a b c : ℝ, ¬ (∃ m n : ℤ, σ = m ∧ τ = n) → 0 < a → 0 < a * c - b ^ 2 →
    let Δ := a * c - b ^ 2
    let ω : ℂ := (-b + I * √Δ) / a
    Tendsto (fun ρ : ℝ ↦ twistedLatticeSum σ τ a b c ρ) (𝓝[>] 0)
      (𝓝 (((2 * σ ^ 2 * π ^ 2 / a
        + π / (3 * √Δ) * Real.log (‖deriv (fun x ↦ smithTheta x ω) 0‖ ^ 2 / (4 * π ^ 2))
        - π / √Δ * Real.log (‖smithTheta (τ + σ * ω) ω‖ ^ 2) : ℝ) : ℂ)))

end ModularFormsKB.Historical.Smith
