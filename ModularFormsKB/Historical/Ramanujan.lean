import ModularFormsKB.Historical.Ramanujan.Equations
import ModularFormsKB.Historical.Ramanujan.PartitionDefs
import ModularFormsKB.Historical.Ramanujan.Congruences
import ModularFormsKB.Historical.Ramanujan.PartitionValues
import ModularFormsKB.Historical.Ramanujan.PowerSeriesBridge
import ModularFormsKB.Historical.Ramanujan.JacobiCube
import ModularFormsKB.Historical.Ramanujan.TauModFive
import ModularFormsKB.Historical.Ramanujan.TauDefs
import ModularFormsKB.Historical.Ramanujan.Tau
import ModularFormsKB.Historical.Ramanujan.Question387
import ModularFormsKB.Historical.Ramanujan.EisensteinTable
import ModularFormsKB.Historical.Ramanujan.PhiTwo
import ModularFormsKB.Historical.Ramanujan.PhiThree
import ModularFormsKB.Historical.Ramanujan.DivisorProducts
import ModularFormsKB.Historical.Ramanujan.ClassInvariants
import ModularFormsKB.Historical.Ramanujan.ZetaProducts
import ModularFormsKB.Historical.Ramanujan.ZetaCorollaries
import ModularFormsKB.Historical.Ramanujan.ThetaSum
import ModularFormsKB.Historical.Ramanujan.TableI
import ModularFormsKB.Historical.Ramanujan.DivisorProductsL
import ModularFormsKB.Historical.Ramanujan.FunctionalEquation

/-!
# Ramanujan, *Collected Papers* (1927): historical library

* `Basic`: Ramanujan's `P`, `Q`, `R` and `Φ_{r,s}`.
* `Equations`: his differential equations (No. 18, (30)) in the variable `x` and the table of `Φ_{1,s}`
  (No. 30, (1.71)–(1.74)).
* `PartitionDefs`: definitions and statements for the partition function (`partitionCount`, Euler's
  product, Jacobi's cube series) and Ramanujan's congruences.
* `Congruences`: Euler's `P · E = 1`, the pentagonal number theorem, the Frobenius congruence
  `∏(1 - xⁿ)^p ≡ ∏(1 - x^{pn})` (No. 30, (2.2)), and the congruences modulo `5`, `7`, `35`
  (No. 25, §§ 2–3) from Jacobi's cube identity.
* `PartitionValues`: Euler's recurrence for `p(n)`, and the values `p(100)`, `p(200)`, `p(61..63)`
  (No. 36) and `p(243)` (No. 28) by kernel evaluation.
* `PowerSeriesBridge`: transfer of analytic identities on the unit disc to formal power series
  (`SumsTo`: Cauchy product, uniqueness; Euler's product via the pentagonal number theorem).
* `JacobiCube`: Jacobi's cube identity `∏(1 - xⁿ)³ = ∑ (-1)ᵏ (2k+1) x^{k(k+1)/2}` from the triple
  product (`jacobi_cube_hasSum`, `eulerSeries_cube`), and the unconditional congruences
  `ramanujanModFive`, `ramanujanModSeven`, `ramanujanModThirtyFive`.
* `TauModFive`: `x ∏(1 - x^{25n}) / ∏(1 - xⁿ) ≡ ∑ n σ₁(n) xⁿ (mod 5)` (No. 30, (2.3)–(2.4)), via the
  formal identities `Qf - Pf² = 288 Φf` and `1728 X E²⁴ = Qf³ - Rf²` (Jacobi's product for `Δ`).
-/
