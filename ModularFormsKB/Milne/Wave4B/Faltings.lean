import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
import ModularFormsKB.Citation
/-!
# Milne, Theorem 11.20 (Faltings): elliptic curves with the same $L$-function are isogenous

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, Theorem 11.20
(pdf p. 117), quoted by Milne from Faltings (1983) [unverified].

**Theorem 11.20.** Let $E$ and $E'$ be elliptic curves over $\mathbb Q$. If $L(E,s) = L(E',s)$, then $E$ and $E'$
are isogenous.

The $L$-function is Mathlib's `WeierstrassCurve.LFunction`, the Euler product over all primes of the local factors
$1 - a_pT + pT^2$ (good reduction), $1 \mp T$ (multiplicative) and $1$ (additive), as a formal Dirichlet series;
equality of formal Dirichlet series is equality of the $L$-series where they converge. An isogeny over $\mathbb Q$ is
Tau Ceti's `TauCeti.Isogeny` (a nonzero morphism of the curves preserving the origin). The statement is a named
statement (`FaltingsIsogenyTheorem`): its proof (Faltings's proof of the Tate conjecture for abelian varieties over
number fields) is far beyond Mathlib and Tau Ceti.
-/

namespace ModularFormsKB.Milne.Wave4B

/-- **Theorem 11.20** (Milne, p. 117; Faltings 1983 [unverified]), as a named statement: two elliptic curves over
$\mathbb Q$ with the same $L$-function are isogenous over $\mathbb Q$. -/
@[kb "milne2017mf" "Section 11, Theorem 11.20 (pdf p. 117)"]
structure FaltingsIsogenyTheorem : Prop where
  isogenous : ∀ E E' : WeierstrassCurve ℚ, E.IsElliptic → E'.IsElliptic → E.LFunction = E'.LFunction →
    Nonempty (TauCeti.Isogeny E.toAffine E'.toAffine)

end ModularFormsKB.Milne.Wave4B
