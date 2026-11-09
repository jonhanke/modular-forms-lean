import ModularFormsKB.Milne.Ch10.FrobeniusUnconditional
import ModularFormsKB.Milne.Ch10.FrobeniusTwistRegular

/-!
# Milne, Section 10: the intermediate named statements of Proposition 10.2, unconditionally

The files of Sections 7 and 10 prove `FrobeniusTwistCurveDegree` and
`CurveFunctionFieldFull` (the full half of Theorem 7.2, for every field) and reduce the named steps
`FrobeniusTwistCurveProperties` and `PurelyInseparableFactorization` to them; here the reductions are applied.
-/

open AlgebraicGeometry CategoryTheory

namespace ModularFormsKB.Milne

universe u

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] (hk : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0)

/-- The Frobenius twist $C^{(q)}$ of a complete regular curve over an algebraically closed field of characteristic
$p$ is a complete regular curve and $\Pi_q$ is purely inseparable of degree $q$, proved. -/
theorem frobeniusTwistCurveProperties [IsAlgClosed k] : FrobeniusTwistCurveProperties k p hk :=
  frobeniusTwistCurveProperties_of k p hk (frobeniusTwistCurveDegree k p hk)

/-- Every purely inseparable map of degree $q$ of complete regular curves factors through $\Pi_q$, proved. -/
theorem purelyInseparableFactorization [IsAlgClosed k] : PurelyInseparableFactorization k p hk :=
  purelyInseparableFactorization_of_full k p hk (curveFunctionFieldFull k)

end ModularFormsKB.Milne
