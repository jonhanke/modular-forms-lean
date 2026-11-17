import ModularFormsKB.Historical.Jacobi.ThetaFourier
import ModularFormsKB.Historical.Jacobi.ModularEquationODE
import ModularFormsKB.Historical.Jacobi.ModularEquationK
import ModularFormsKB.Historical.Jacobi.TripleProduct
import ModularFormsKB.Historical.Jacobi.ThetaIdentification
import ModularFormsKB.Historical.Jacobi.Section66
import ModularFormsKB.Historical.Jacobi.Section66Proofs
import ModularFormsKB.Historical.Jacobi.Clausen
import ModularFormsKB.Historical.Jacobi.Multipliers
import ModularFormsKB.Historical.Jacobi.LambertSeries
import ModularFormsKB.Historical.Jacobi.ModularEquationForms
import ModularFormsKB.Historical.Jacobi.ThetaNullwerte
import ModularFormsKB.Historical.Jacobi.ThetaProducts
import ModularFormsKB.Historical.Jacobi.EulerExpansions

/-!
# Jacobi, *Fundamenta nova theoriae functionum ellipticarum* (1829): historical library

* `ThetaFourier`: the Fourier series of `Θ` and `H` (§§ 61–63).
* `ModularEquationODE`: the differential equation of the third order satisfied by all modular equations
  (§ 33).
* `ModularEquationK`: the same for Jacobi's complete integrals `K`, `K'` and the modular relation of any
  degree `n` (imports Tau Ceti's elliptic integrals).
* `ThetaIdentification`: Jacobi's analytic `Θ`, `H` versus the theta series (§§ 52, 61–62), stated as
  named propositions (loose end LE-MF-0190).
* `TripleProduct`: the triple product identity, with its cosine and sine forms (§ 64).
* `ModularEquationForms`: the modular equations of orders 3 and 5: symmetries, the forms in `q = 1 - 2k²`,
  Legendre's relation, the multiplier formula (§§ 16, 29, 30, 34).
* `ThetaNullwerte`: `ϑ₃² = 2K/π`, `ϑ₂² = 2kK/π`, `ϑ₄² = 2k'K/π` at the nome `e^{-πK'/K}` (§§ 63, 65), through
  the arithmetic–geometric mean; `ThetaProducts`: the product formulas of § 36.
-/
