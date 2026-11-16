import ModularFormsKB.Historical.Kronecker.Ser
import ModularFormsKB.Historical.Kronecker.AnalyticInvariant
import ModularFormsKB.Historical.Kronecker.AInvariance
import ModularFormsKB.Historical.Kronecker.ClassNumberRelations
import ModularFormsKB.Historical.Kronecker.LimitFormula
import ModularFormsKB.Historical.Kronecker.E2Values
import ModularFormsKB.Historical.Kronecker.ThetaE2
import ModularFormsKB.Historical.Kronecker.EisensteinSums

/-!
# Kronecker, *Werke* (ed. Hensel), volumes 2 (1897), 4 (1929) and 5 (1930): historical library

* `Ser`: the series `Ser_ρ` and its general transformation law (Werke 5, I art. XXI, § 7, (E)).
* `AnalyticInvariant`: the function `A` and its invariance under arithmetic equivalence (Werke 4, XXXI,
  §§ II, V).
* `AInvariance`: proofs of (𝔅), `kroneckerA_invariance` and `kroneckerA_form_invariance`, from the
  transformation laws of `ϑ` and `η` and the generation of `SL₂(ℤ)` by `S` and `T`.
* `ClassNumberRelations`: Kronecker's weighted class numbers `G`, `F`, `E` and their relations (Werke 4, XXIII;
  Werke 2, XVII § 22), through the Hurwitz class numbers of Tau Ceti
  and the three-squares formula of the core library. This file imports the core library's
  `ModularFormsKB.Hurwitz.Relations` (a thin wrapper, not a re-proof).
* `E2Values`, `ThetaE2`: Kronecker's `E₂(i) = 3/π`, `E₂(e^{2πi/3}) = 2√3/π` and `ϑ'''(0, w) = -π² E₂(w) ϑ'(0, w)`
  (Werke 5, II art. IV), and Jacobi's cube identity.
* `LimitFormula`: Kronecker's first limit formula (Werke 5, I, arts. XIV–XV), stated.
-/
