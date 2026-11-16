/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.ClassSum
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.Mellin

/-!
# `KohnenSquareCycle`

The cycle integrals of discriminant $D^2$ give $L(G, D, k)$: steps in
`SquareCycle/ClassSum.lean` (classes and invariance) and `SquareCycle/Mellin.lean` (Gauss sum and periods).
-/

namespace ModularFormsKB.HalfIntegral

/-- **`KohnenSquareCycle` from Gauss's sign of the quadratic Gauss sum.** -/
theorem kohnenSquareCycle_of_gaussSum (hGauss : KroneckerGaussSum) (k : ℕ) : KohnenSquareCycle k :=
  ⟨fun hk D hD G b hb L hL ↦ by
    rw [shintaniCoeff_natAbs_eq_sum hk hD G]
    exact sum_kroneckerSym_cycleIntegral hGauss hk hD G b hb L hL⟩

end ModularFormsKB.HalfIntegral
