import ModularFormsKB.Milne.Ch10.FrobeniusTwistCurve
import ModularFormsKB.Milne.Ch10.FrobeniusDegree

/-!
# Milne, Proposition 10.2: the first half proved; the factorization as the only input

`frobeniusTwistCurveDegree`: the named statement `FrobeniusTwistCurveDegree` holds (the twist is a curve,
`isCurve_frobeniusTwistStructure`; $\Pi_q$ is purely inseparable of degree $q$,
`frobeniusMap_isPurelyInseparable_degree`). Hence `FrobeniusFactorization` follows from
`PurelyInseparableFactorization` alone (`frobeniusFactorization_of_factorization`), whose proof needs
Theorem 7.2 (`CurveFunctionFieldEquivalence`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularFormsKB.Milne

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
  (hk : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0)

/-- **The twist is a curve and $\Pi_q$ is purely inseparable of degree $q$.** -/
theorem frobeniusTwistCurveDegree [IsAlgClosed k] : FrobeniusTwistCurveDegree k p hk where
  curve := by
    intro C _ f hf n _ _
    exact ⟨isCurve_frobeniusTwistStructure k p hk f hf.1 n,
      frobeniusMap_isPurelyInseparable_degree k p hk f hf.1 n⟩

/-- **Proposition 10.2 from the factorization statement alone.** -/
theorem frobeniusFactorization_of_factorization [IsAlgClosed k]
    (h : PurelyInseparableFactorization k p hk) : FrobeniusFactorization k p hk :=
  frobeniusFactorization_of_curveDegree k p hk (frobeniusTwistCurveDegree k p hk) h

end ModularFormsKB.Milne
