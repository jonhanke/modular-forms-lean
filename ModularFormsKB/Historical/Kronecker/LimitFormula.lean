import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ModularFormsKB.Citation
/-!
# Kronecker's first limit formula (stated)

Kronecker, *Zur Theorie der elliptischen Functionen*, *Werke* 5 (ed. Hensel, 1930), I, art. XIV, (1), p. 4 and
art. XV, (18)–(19), p. 9, in the form derived by Weber, *Elliptische Functionen und algebraische Zahlen* (1891),
§ 112, pp. 454–463 (1908: § 141).

For a positive definite real form `ψ = Ax² + 2Bxy + Cy²`, `m = AC - B² > 0`, and `ω = (-B + i√m)/A` (a root of
`Aω² + 2Bω + C = 0` in the upper half-plane; Weber's `ω₁, ω₂` are `ω` and `-ω̄`, so `η(ω₁)η(ω₂) = |η(ω)|²`):
$$\lim_{s\to1^+}\Bigl(\sum_{(x,y)\ne0}\psi(x,y)^{-s}-\frac{\pi}{(s-1)\sqrt m}\Bigr)
  =\frac{2\pi\gamma}{\sqrt m}+\frac{\pi}{\sqrt m}\log\frac{A}{4m}-\frac{2\pi}{\sqrt m}\log|\eta(\omega)|^2,$$
`γ = -Γ'(1)` Euler's constant. (The normalization was checked by hand against the standard form
`∑' y^s/|mτ + n|^{2s} = π/(s - 1) + 2π(γ - log 2 - log(√y |η(τ)|²)) + O(s - 1)`.)

**Stated** as the named proposition `KroneckerFirstLimitFormula`: its proof needs the Fourier expansion of the
real-analytic Eisenstein series in `s` near `s = 1` (Poisson summation in one variable, the `K`-Bessel terms, and
the product expansion of `η`), none of which is in Mathlib or Tau Ceti (loose end LE-MF-0263). Weber's
consequences in the same row (the difference of two forms through `f(ω)`, and the residue `πh/√m` summed over a
system of classes) are not stated separately.
-/

noncomputable section

open Complex Filter
open scoped Real Topology

namespace ModularFormsKB.Historical.Kronecker

/-- The value of the binary form `ψ = Ax² + 2Bxy + Cy²` at an integer pair. -/
def binaryFormValue (A B C : ℝ) (p : ℤ × ℤ) : ℝ := A * p.1 ^ 2 + 2 * B * p.1 * p.2 + C * p.2 ^ 2

/-- The Epstein zeta function `∑_{(x,y) ≠ 0} ψ(x,y)^{-s}` of `ψ = Ax² + 2Bxy + Cy²` at real `s` (absolutely
convergent for `s > 1` when `ψ` is positive definite; the term `(0, 0)` is excluded). -/
def epsteinZeta (A B C s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else binaryFormValue A B C p ^ (-s)

/-- **Kronecker's first limit formula** (Kronecker, Werke 5, I, art. XIV (1), p. 4, art. XV (18), p. 9; Weber 1891,
§ 112), stated: for real `A > 0`, `AC - B² = m > 0` and `ω = (-B + i√m)/A`,
`∑' ψ^{-s} - π/((s - 1)√m) → 2πγ/√m + (π/√m) log(A/(4m)) - (2π/√m) log |η(ω)|²` as `s → 1⁺`. -/
@[kb "kronecker1930" "I, art. XIV (1), p. 4; art. XV (18), p. 9: Kronecker's limit formula (stated)"]
def KroneckerFirstLimitFormula : Prop :=
  ∀ A B C : ℝ, 0 < A → 0 < A * C - B ^ 2 →
    Tendsto (fun s : ℝ ↦ epsteinZeta A B C s - π / ((s - 1) * √(A * C - B ^ 2))) (𝓝[>] 1)
      (𝓝 (2 * π * Real.eulerMascheroniConstant / √(A * C - B ^ 2)
        + π / √(A * C - B ^ 2) * Real.log (A / (4 * (A * C - B ^ 2)))
        - 2 * π / √(A * C - B ^ 2) *
            Real.log (‖ModularForm.eta ((-B + I * √(A * C - B ^ 2)) / A)‖ ^ 2)))

end ModularFormsKB.Historical.Kronecker
