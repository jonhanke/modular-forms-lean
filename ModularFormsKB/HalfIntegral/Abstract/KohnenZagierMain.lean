/-
# The Kohnen–Zagier formula and Waldspurger's plus space theorem from `KohnenDLift`

For the theta multiplier. Assembly of the preceding statements:

- `kohnenZagier_theta`: `KohnenZagier thetaMultiplierSystem k` from
  - `KohnenDLift` for every admissible $D$ (hypothesis `hL`);
  - `KohnenAdjointCoeff` for every adjoint (hypothesis `hcoeff`, the one analytic input);
  - multiplicity one `KohnenPlusMultOne` and finite dimension of $S^+_{k+1/2}(4)$, which
    follow from `KohnenTraceIdentity` (hypotheses `hmult`, `hfin`);
  - the two Hecke adjointness statements `PlusHeckeSelfAdjoint`, `LevelOneHeckeSelfAdjoint` (loose ends).
- `waldspurgerPlus_theta`: `WaldspurgerPlus thetaMultiplierSystem k` from the same inputs;
  `PlusPeterssonNonzero` is replaced by the theorem `peterssonDefinite`, and `PlusRealCoefficients` by the theorem
  `plusRealCoefficients_theta`.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierHecke
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierMultOne
import ModularFormsKB.HalfIntegral.Abstract.WaldspurgerGround
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierRealMain

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane ModularForm
open scoped Real

/-- **`KohnenAdjointInputs` for the theta multiplier** from `KohnenDLift` and `KohnenAdjointCoeff`. -/
theorem kohnenAdjointInputs_theta (k : ℕ) (hfin : FiniteDimensional ℂ (thetaMultiplierSystem.plusCuspForms k 1 1))
    (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    (hS : PlusHeckeSelfAdjoint k) (hO : LevelOneHeckeSelfAdjoint k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    KohnenAdjointInputs thetaMultiplierSystem k where
  exists_adjoint hk D hD hsign := by
    obtain ⟨Sstar, hadj⟩ := kohnenAdjoint_of_dLift thetaMultiplierSystem k hk hfin (hL D ⟨hD, hsign⟩)
    exact ⟨Sstar, hadj, kohnenAdjointHecke_of_adjoint k hk ⟨hD, hsign⟩ (hL D ⟨hD, hsign⟩) hS hO hadj,
      hcoeff D ⟨hD, hsign⟩ Sstar hadj⟩

/-- **Row 25: the Kohnen–Zagier formula** for the theta multiplier. -/
theorem kohnenZagier_theta (k : ℕ) (hfin : FiniteDimensional ℂ (thetaMultiplierSystem.plusCuspForms k 1 1))
    (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    (hmult : KohnenPlusMultOne thetaMultiplierSystem k)
    (hS : PlusHeckeSelfAdjoint k) (hO : LevelOneHeckeSelfAdjoint k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_of_four_inputs thetaMultiplierSystem k (kohnenLiftEigen_of_dLift thetaMultiplierSystem k hL)
    (kohnenAdjointInputs_theta k hfin hL hS hO hcoeff) (plusMultiplicityOne_of_kohnenPlusMultOne hmult)

/-- `PlusPeterssonNonzero` is a theorem. -/
theorem plusPeterssonNonzero (M : MultiplierSystem) (k : ℕ) : PlusPeterssonNonzero M k :=
  ⟨fun g hg hg0 ↦ (peterssonDefinite M k).four g hg hg0⟩

/-- **Row 25: Waldspurger's theorem for the plus space** (ratio form), from the Kohnen–Zagier formula. -/
theorem waldspurgerPlus_theta (k : ℕ) (hfin : FiniteDimensional ℂ (thetaMultiplierSystem.plusCuspForms k 1 1))
    (hL : ∀ D, KohnenDisc k D → KohnenDLift thetaMultiplierSystem k D)
    (hmult : KohnenPlusMultOne thetaMultiplierSystem k)
    (hS : PlusHeckeSelfAdjoint k) (hO : LevelOneHeckeSelfAdjoint k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_of_kohnenZagier (kohnenZagier_theta k hfin hL hmult hS hO hcoeff)
    (plusPeterssonNonzero _ k) (plusRealCoefficients_theta k hmult hO)

end ModularFormsKB.HalfIntegral
