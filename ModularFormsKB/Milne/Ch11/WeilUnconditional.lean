import ModularFormsKB.Milne.Ch11.TwistAssembly

/-!
# Milne, Theorem 11.4, unconditionally

**Weil's theorem** (the Riemann hypothesis for curves over finite fields), in the function field form of
`WeilCurveTheorem`, with no hypothesis: `weilCurveTheorem_of_lowerBoundMultiple` reduces it to the lower bound
`HasseWeilLowerBoundMultiple`, which is `hasseWeilLowerBoundMultiple` (Bombieri's twisting argument over the Galois
closure of $F/k(x)$, `TwistAssembly.lean`); the upper bound is `bombieriUpperBound` (Stepanov–Bombieri) and the
rationality of the zeta function `zetaLPolynomial_of_schmidt schmidtDegreeOne` (F. K. Schmidt).
-/

namespace ModularFormsKB.Milne

universe u v

/-- **Theorem 11.4** (Milne; Weil's Riemann hypothesis for curves over finite fields), proved. -/
theorem weilCurveTheorem : WeilCurveTheorem.{u, v} :=
  weilCurveTheorem_of_lowerBoundMultiple hasseWeilLowerBoundMultiple

end ModularFormsKB.Milne
