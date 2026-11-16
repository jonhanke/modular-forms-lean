/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.KohnenTrace
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierMain

/-!
# The Kohnen–Zagier formula from the trace identity

The theorems `kohnenZagier_theta` and `waldspurgerPlus_theta` take finite dimension of $S^+_{k+1/2}(4)$, multiplicity one
(`KohnenPlusMultOne`) and `KohnenDLift` as hypotheses. These are supplied by
`finiteDimensional_plusSpace` (an instance), `kohnenPlusMultOne_of_trace` and `kohnenDLift_of_trace`.

- `kohnenZagier_of_trace`: `KohnenZagier thetaMultiplierSystem k` from `KohnenTraceIdentity`,
  `KohnenTPlusFourStable`, `PlusHeckeSelfAdjoint`, `LevelOneHeckeSelfAdjoint` and `KohnenAdjointCoeff`.
- `waldspurgerPlus_of_trace`: `WaldspurgerPlus thetaMultiplierSystem k` from the same inputs.
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane ModularForm

/-- **The Kohnen–Zagier formula for the theta multiplier from the trace identity.** -/
theorem kohnenZagier_of_trace (k : ℕ) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k)
    (hS : PlusHeckeSelfAdjoint k) (hO : LevelOneHeckeSelfAdjoint k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_theta k inferInstance (fun _ hD ↦ kohnenDLift_of_trace h hT hD) (kohnenPlusMultOne_of_trace h)
    hS hO hcoeff

/-- **Waldspurger's theorem for the plus space (ratio form), from the trace identity.** -/
theorem waldspurgerPlus_of_trace (k : ℕ) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k)
    (hS : PlusHeckeSelfAdjoint k) (hO : LevelOneHeckeSelfAdjoint k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_theta k inferInstance (fun _ hD ↦ kohnenDLift_of_trace h hT hD) (kohnenPlusMultOne_of_trace h)
    hS hO hcoeff

end ModularFormsKB.HalfIntegral
