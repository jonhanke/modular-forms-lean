/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.Abstract.Kohnen
import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Gauss sum of the Kronecker character of a fundamental discriminant

For a fundamental discriminant $D$ and every integer $m$,
$$ \sum_{c \bmod |D|}\left(\frac Dc\right)e^{2\pi i mc/|D|} = \left(\frac Dm\right)\sqrt D, \qquad
   \sqrt D = \begin{cases}\sqrt{D} & D > 0\\ i\sqrt{|D|} & D < 0\end{cases} $$
(`sqrtDisc`), with the Kronecker symbol of Tau Ceti (`TauCeti.kroneckerSym`, which is $0$ at $c = 0$ for $|D| > 1$). The
case $m = 1$ is Gauss's determination of the sign of the quadratic Gauss sum (Gauss 1811; Ireland–Rosen `irelandrosen1990`,
Ch. 6 [unverified]); the general $m$ follows because $\left(\frac D\cdot\right)$ is a primitive character
modulo $|D|$ (its conductor is $|D|$ for $D$ fundamental).

This is the named statement `KroneckerGaussSum`; the sign enters the constant of `KohnenSquareCycle`.
-/

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

/-- **The square root of a discriminant in $\mathbb C$**: $\sqrt D$ for $D \ge 0$ and $i\sqrt{|D|}$ for $D < 0$. -/
noncomputable def sqrtDisc (D : ℤ) : ℂ :=
  if 0 ≤ D then ((√(D : ℝ) : ℝ) : ℂ) else I * ((√(-D : ℝ) : ℝ) : ℂ)

/-- **Gauss sums of the Kronecker character of a fundamental discriminant** (Gauss 1811; Ireland–Rosen `irelandrosen1990`,
Ch. 6 [unverified]): for $D$ fundamental and $m \in \mathbb Z$,
$\sum_{0 \le c < |D|}\left(\frac Dc\right)e^{2\pi i mc/|D|} = \left(\frac Dm\right)\sqrt D$. -/
@[kb "irelandrosen1990" "Ch. 6: the Gauss sum of the primitive quadratic character of a fundamental discriminant D is √D (Gauss's sign) [unverified]"]
structure KroneckerGaussSum : Prop where
  eq : ∀ D : ℤ, IsFundamentalDiscriminant D → ∀ m : ℤ,
    ∑ c ∈ Finset.range D.natAbs, (TauCeti.kroneckerSym D c : ℂ) * cexp (2 * π * I * m * c / D.natAbs) =
      (TauCeti.kroneckerSym D m : ℂ) * sqrtDisc D

end ModularFormsKB.HalfIntegral
