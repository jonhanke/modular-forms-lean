import ModularFormsKB.Milne.Ch10.FrobeniusFactorization
import ModularFormsKB.Milne.Ch10.CurveFull

/-!
# Milne, Proposition 10.2, unconditionally

`frobeniusFactorization_of_curveFunctionFieldFull` reduces Proposition 10.2 to the full half of Theorem 7.2
(`CurveFunctionFieldFull`), which is proved for every field in `CurveFull.lean` (via Tau Ceti's
`AlgebraicGeometry.Scheme.homOfFunctionFieldAlgHom`); the faithful half is `curveFunctionField_faithful`.
-/

open AlgebraicGeometry CategoryTheory

namespace ModularFormsKB.Milne

universe u

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] (hk : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0)

/-- **Proposition 10.2** (Milne; the Frobenius map $\Pi_q : C \to C^{(q)}$ is purely inseparable of degree $q$, and
every purely inseparable map of degree $q$ of complete nonsingular curves factors through it), proved. -/
theorem frobeniusFactorization [IsAlgClosed k] : FrobeniusFactorization k p hk :=
  frobeniusFactorization_of_curveFunctionFieldFull k p hk (curveFunctionFieldFull k)

end ModularFormsKB.Milne
