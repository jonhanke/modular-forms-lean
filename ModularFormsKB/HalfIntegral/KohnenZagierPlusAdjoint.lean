/-
# H3 without `PlusHeckeSelfAdjoint`

The named input `PlusHeckeSelfAdjoint` (LE-MF-0269) is now proved
(`PlusHeckeAdjoint.plusHeckeSelfAdjoint`, `ModularFormsKB/HalfIntegral/PlusHeckeAdjoint.lean`), so H3 (the Kohnen–Zagier
formula and Waldspurger's theorem on the plus space, theta multiplier) depends on `KohnenTraceIdentity` and
`KohnenAdjointCoeff` (the allowed inputs) and on `KohnenTPlusFourStable` (LE-MF-0268) only. The statements are those of
`kohnenZagier_of_trace'` and `waldspurgerPlus_of_trace'` with the hypothesis `PlusHeckeSelfAdjoint k` removed.
-/
import ModularFormsKB.HalfIntegral.KohnenLevelOneAdjoint
import ModularFormsKB.HalfIntegral.PlusHeckeAdjoint

namespace ModularFormsKB.HalfIntegral

open MatrixGroups

local notation "ℍ" => UpperHalfPlane

/-- **H3 (Kohnen–Zagier) for the theta multiplier** from `KohnenTraceIdentity`, `KohnenTPlusFourStable` and
`KohnenAdjointCoeff`; both Hecke adjointness statements are now proved. -/
@[kb "kohnenzagier1981" "Kohnen–Zagier formula, theta multiplier, from the trace identity, T⁺(4) and the kernel coefficient [unverified]"]
theorem kohnenZagier_of_trace_stable (k : ℕ) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_of_trace' k h hT (PlusHeckeAdjoint.plusHeckeSelfAdjoint k) hcoeff

/-- **H3 (Waldspurger's plus-space theorem) for the theta multiplier**, from the same inputs as
`kohnenZagier_of_trace_stable`. -/
@[kb "kohnenzagier1981" "Waldspurger's theorem on the plus space, from the trace identity, T⁺(4) and the kernel coefficient [unverified]"]
theorem waldspurgerPlus_of_trace_stable (k : ℕ) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_of_trace' k h hT (PlusHeckeAdjoint.plusHeckeSelfAdjoint k) hcoeff

end ModularFormsKB.HalfIntegral
