/-
# The coefficients of $f_{32}$ and of Tunnell's two weight $3/2$ forms

Conventions checked numerically.

**The newform of conductor 32.** $f_{32} = \sum_{\alpha \equiv 1 \bmod (2+2i)} \alpha\,q^{N\alpha}$, the sum over
$\alpha = a + ci \in \mathbb Z[i]$; $\alpha \equiv 1 \bmod (2+2i)$ means $a$ odd, $c$ even and $a + c \equiv 1 \bmod 4$.
The terms $\alpha$ and $\bar\alpha$ pair up, so the coefficients are $b(m) = \sum a$ over the
$(a, c)$ with $a^2 + c^2 = m$ (`f32Coeff`); for example $b(1) = 1$, $b(5) = -2$, $b(9) = -3$. Its $L$-series is that of $E_1 : y^2 = x^3 - x$. Equivalently
$f_{32} = \eta(4\tau)^2\eta(8\tau)^2$ [unverified identity, checked numerically].

**The twisted coefficients** $\left(\frac nm\right) b(m)$ (`congruentCoeff`, Jacobi symbol in the lower argument; $b$
vanishes at even $m$, so the junk values of `jacobiSym` at even $m$ do not matter). Row 33: these are the coefficients
of Mathlib's `(congruentCurve n).LFunction`.

**Tunnell's forms** (Tunnell 1983 `tunnell1983` [unverified]; Koblitz 1984, Ch. IV §4 [unverified]):
$g_{\mathrm{odd}} = \eta(8\tau)\eta(16\tau)\theta(2\tau) \in S_{3/2}(128)$ and
$g_{\mathrm{even}} = \eta(8\tau)\eta(16\tau)\theta(4\tau) \in S_{3/2}(128, (\tfrac 2\cdot))$. Both are supported on odd
exponents, with coefficients (checked numerically for $m \le 400$)
$$c_{\mathrm{odd}}(m) = B(m) - \tfrac12 A(m),\qquad c_{\mathrm{even}}(m) = D(2m) - \tfrac12 C(2m)\qquad(m \text{ odd}).$$
Here they are *defined* by these coefficients (`tunnellOddCoeff`, `tunnellEvenCoeff`, `tunnellOdd`, `tunnellEven`);
their membership in $S_{3/2}$ is a hypothesis of row 36, to be discharged by wave 6 (rows 38, 39).

Note: the docstring of `Tunnell.lean` before this job described $g_{\mathrm{odd}}$ as $\theta_{1,2,8} - \frac12\theta_{1,2,32}$;
the coefficients of that combination are $A - \frac12 B$, not $\pm\frac12(A - 2B)$, and it has a constant term. Recorded
as a loose end and corrected there.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.Tunnell
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex Tunnell
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- The Gaussian integers $a + ci$ with $a^2 + c^2 = m$ and $a + ci \equiv 1 \bmod (2 + 2i)$
($a$ odd, $c$ even, $a + c \equiv 1 \bmod 4$), as pairs $(a, c)$ in the box $|a|, |c| \le m$. -/
def primaryOfNorm (m : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(m : ℤ)) m) ×ˢ (Finset.Icc (-(m : ℤ)) m)).filter
    (fun v ↦ v.1 ^ 2 + v.2 ^ 2 = m ∧ v.1 % 2 = 1 ∧ v.2 % 2 = 0 ∧ (v.1 + v.2) % 4 = 1)

/-- **The coefficients of $f_{32}$:** $b(m) = \sum_{\alpha \equiv 1 \bmod (2+2i),\ N\alpha = m} \operatorname{Re}\alpha$
(which is $\sum \alpha$, the imaginary parts cancelling under $\alpha \mapsto \bar\alpha$). -/
def f32Coeff (m : ℕ) : ℤ := ∑ v ∈ primaryOfNorm m, v.1

theorem f32Coeff_zero : f32Coeff 0 = 0 := by decide
theorem f32Coeff_one : f32Coeff 1 = 1 := by decide
theorem f32Coeff_two : f32Coeff 2 = 0 := by decide
theorem f32Coeff_three : f32Coeff 3 = 0 := by decide
theorem f32Coeff_five : f32Coeff 5 = -2 := by decide +kernel

/-- **The coefficients of the twist $f_{32} \otimes \left(\frac n\cdot\right)$**: $\left(\frac nm\right) b(m)$. -/
def congruentCoeff (n m : ℕ) : ℤ := jacobiSym n m * f32Coeff m

/-- **$E_n$ over $\mathbb Z/p$**: $y^2 = x^3 - n^2x$. -/
def congruentCurveMod (n p : ℕ) : WeierstrassCurve (ZMod p) := ⟨0, 0, 0, -((n : ZMod p) ^ 2), 0⟩

/-- $q = e^{2\pi i\tau}$. -/
noncomputable def qParam (τ : ℍ) : ℂ := cexp (2 * π * I * (τ : ℂ))

/-- **$f_{32}$ as a function on $\mathbb H$:** $\sum_m b(m) q^m$. -/
noncomputable def f32 (τ : ℍ) : ℂ := ∑' m : ℕ, (f32Coeff m : ℂ) * cexp (2 * π * I * m * τ)

/-- **The coefficients of Tunnell's odd form** $\eta(8\tau)\eta(16\tau)\theta(2\tau)$:
$B(m) - \tfrac12 A(m)$ for odd $m$, $0$ for even $m$. -/
noncomputable def tunnellOddCoeff (m : ℕ) : ℂ :=
  if Odd m then (tunnellB m : ℂ) - (tunnellA m : ℂ) / 2 else 0

/-- **The coefficients of Tunnell's even form** $\eta(8\tau)\eta(16\tau)\theta(4\tau)$:
$D(2m) - \tfrac12 C(2m)$ for odd $m$, $0$ for even $m$. -/
noncomputable def tunnellEvenCoeff (m : ℕ) : ℂ :=
  if Odd m then (tunnellD (2 * m) : ℂ) - (tunnellC (2 * m) : ℂ) / 2 else 0

/-- **Tunnell's odd form** as a $q$-series. -/
noncomputable def tunnellOdd (τ : ℍ) : ℂ := ∑' m : ℕ, tunnellOddCoeff m * cexp (2 * π * I * m * τ)

/-- **Tunnell's even form** as a $q$-series. -/
noncomputable def tunnellEven (τ : ℍ) : ℂ := ∑' m : ℕ, tunnellEvenCoeff m * cexp (2 * π * I * m * τ)

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
