import ModularFormsKB.Milne.Wave4A.SphereGenus
import ModularFormsKB.Milne.Wave4A.GenusFormula
import ModularFormsKB.Milne.Wave4A.GenusGammaN
import ModularFormsKB.Milne.Wave4A.GenusEuler
import ModularFormsKB.Milne.Wave4A.CanonicalClass
import ModularFormsKB.Milne.Wave4A.SphereRiemannRoch
import ModularFormsKB.Milne.Wave4A.CanonicalDegree
import ModularFormsKB.Milne.Wave4A.GenusZero
import ModularFormsKB.Milne.Wave4A.GenusZeroDifferentials
import ModularFormsKB.Milne.Wave4A.DegreeOneTransfer

/-!
# Milne, Sections 0–4, wave 4A

* `Wave4A/SphereGenus.lean`: the Riemann sphere has genus `0` (Example 1.23, Proposition 2.21).
* `Wave4A/GenusFormula.lean`: Theorem 2.22, the genus of `X(Γ)` (ramification count unconditional; the genus
  formula conditional on the Riemann–Hurwitz formula, Theorem 1.27).
* `Wave4A/GenusGammaN.lean`: Example 2.23, the genus of `X(N)`.
* `Wave4A/GenusEuler.lean`: Theorem 2.22 for the Euler characteristic (topological genus).
* `Wave4A/CanonicalClass.lean`: `div(η) = div(η/ω) + div(ω)`; canonical divisors have one degree.
* `Wave4A/SphereRiemannRoch.lean`: Exercise 1.24, the Riemann–Roch theorem for the sphere.
* `Wave4A/CanonicalDegree.lean`: Proposition 2.21 (`X(1)` has genus `0`), and Theorem 2.22 from Corollary 1.21.
* `Wave4A/GenusZero.lean`: Theorem 2.22 and Proposition 4.12 unconditionally when the formula gives genus `0`
  (`Γ(1)`, `Γ(N)` for `2 ≤ N ≤ 5`).
* `Wave4A/DegreeOneTransfer.lean`: Riemann–Roch transfers along degree-one maps; Riemann–Roch on `X(1)` and
  Theorem 4.9 for `Γ(1)`.
-/
