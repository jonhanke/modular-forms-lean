import ModularFormsKB.Milne.Wave10.LittlePicard
import ModularFormsKB.Milne.Wave10.GenusGammaTop
import ModularFormsKB.Milne.Wave10.ModularCurveJ
import ModularFormsKB.Milne.Wave10.RiemannRochInputs

/-!
# Milne wave 10

* Remark 2.25, the little Picard theorem, by Milne's covering argument run in level one: `j` makes the free locus of
  `PSL(2, ℤ)` on `ℍ` a covering of `ℂ ∖ {0, 1728}`, an entire function omitting two values lifts to `ℍ` and is
  constant by Liouville's theorem (`Wave10/LittlePicard.lean`); the named statement `LittlePicardStatement` is proved.
* Example 2.23 (the genus of `X(N)`) in punctured Euler-characteristic form, unconditional
  (`Wave10/GenusGammaTop.lean`).
* On every modular curve `X(Γ)` (`Γ` of finite index): Theorem 1.17 and Proposition 1.12 (b) unconditional (`j` is a
  nonconstant meromorphic function), Riemann–Hurwitz for `j` and the genus formula 2.22 from Riemann–Roch on `X(Γ)`
  alone (`Wave10/ModularCurveJ.lean`).
* Corollary 1.21 (`deg K = 2g - 2`) from Riemann–Roch; Theorem 4.9 and Proposition 4.12 from Riemann–Roch on `X(Γ)`
  alone (`Wave10/RiemannRochInputs.lean`).
-/
