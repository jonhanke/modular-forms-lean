import ModularFormsKB.Historical.Jacobi.ThetaFourier
import ModularFormsKB.Historical.Jacobi.ModularEquationK
import TauCeti.Analysis.SpecialFunctions.JacobiElliptic.Basic

/-!
# Jacobi's `Θ` and `H` and the theta series: the identification, stated

Jacobi, *Fundamenta nova* (1829). `ThetaFourier` proves that the theta series `jacobiΘ`, `jacobiH`
(`ϑ₄`, `ϑ₁` in Jacobi's variable `x`, nome `q = e^{πiτ}`) have Jacobi's displayed Fourier expansions
(§ 62). Jacobi, however, defines `Θ` and `H` analytically, from the elliptic
functions of modulus `k` (`0 < k < 1`, complete integrals `K`, `K'`, `τ = iK'/K`, `q = e^{-πK'/K}`):

* § 52, (6), p. 146: `Θ(u)/Θ(0) = exp ∫₀ᵘ Z(u) du`, with Jacobi's zeta function `Z(u) = E(am u) - (E/K) u`
  (`E(φ)` the integral of the second kind, `E = E(π/2)`);
* § 61, (2), p. 173: `sin am u = H(u)/(√k Θ(u))`.

That these analytically defined functions are the theta series, `Θ(2Kx/π)/Θ(0) = ϑ₄(x)/ϑ₄(0)` and
`H(2Kx/π)/Θ(2Kx/π) = ϑ₁(x)/ϑ₄(x)`, is the content of §§ 61–62 not covered by `ThetaFourier` (loose end
LE-MF-0190). Both are stated here as named propositions, in terms of Tau Ceti's Legendre integrals
(`TauCeti.Real.legendreK`, `legendreE`, `legendreEc`) and Jacobi amplitude and sine (`jacobiAm`, `jacobiSn`), and
checked numerically (agreement to `10⁻¹⁰` for `k = 0.3, 0.7, 0.95`, several `x`). Proving them needs the theory of
the elliptic functions in the complex domain (double periodicity, zeros and poles of `sn`), which neither Mathlib
nor Tau Ceti has (Tau Ceti's `jacobiSn` is defined for real arguments only).
-/

noncomputable section

open Complex TauCeti.Real
open scoped Real

namespace ModularFormsKB.Historical.Jacobi

/-- Jacobi's zeta function `Z(u) = E(am u) - (E/K) u` (*Fundamenta nova* § 47–52), for real `u`. -/
def jacobiZeta (k u : ℝ) : ℝ := legendreE (jacobiAm k u) k - legendreEc k / legendreK k * u

/-- The point `τ = iK'/K` of the upper half-plane (Jacobi's nome `q = e^{πiτ} = e^{-πK'/K}`). -/
def jacobiTau (k : ℝ) : ℂ := I * ((legendreK' k / legendreK k : ℝ) : ℂ)

/-- **Jacobi's `Θ` is the theta series** (*Fundamenta nova* § 52, (6), p. 146 and § 62, pp. 176–177), as a
proposition: for `0 < k < 1` and real `x`, `exp ∫₀^{2Kx/π} Z(u) du = ϑ₄(x)/ϑ₄(0)` at `τ = iK'/K`. -/
@[kb "jacobi1829" "§ 52, (6), p. 146; § 62, pp. 176–177"]
def JacobiThetaIdentification : Prop :=
  ∀ k x : ℝ, 0 < k → k < 1 →
    jacobiΘ x (jacobiTau k) / jacobiΘ 0 (jacobiTau k) =
      ((Real.exp (∫ u in (0 : ℝ)..(2 * legendreK k * x / π), jacobiZeta k u) : ℝ) : ℂ)

/-- **Jacobi's `sn` as a quotient of theta series** (*Fundamenta nova* § 61, (2), p. 173 and § 62), as a
proposition: for `0 < k < 1` and real `x`, `√k sin am(2Kx/π) ϑ₄(x) = ϑ₁(x)` at `τ = iK'/K`, i.e.
`sin am u = H(u)/(√k Θ(u))` with Jacobi's `H`, `Θ` the theta series. -/
@[kb "jacobi1829" "§ 61, (2), p. 173; § 62, pp. 176–177"]
def JacobiSnThetaQuotient : Prop :=
  ∀ k x : ℝ, 0 < k → k < 1 →
    ((√k * jacobiSn k (2 * legendreK k * x / π) : ℝ) : ℂ) * jacobiΘ x (jacobiTau k) = jacobiH x (jacobiTau k)

end ModularFormsKB.Historical.Jacobi
