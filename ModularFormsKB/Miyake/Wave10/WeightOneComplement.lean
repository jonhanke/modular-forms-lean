import ModularFormsKB.Miyake.Wave10.WeightOne
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Dimension

/-!
# Miyake, Theorem 4.7.2 in weight one: `𝒢₁(N, χ) = 𝒮₁(N, χ) ⊕ ℰ₁(N, χ)`

Miyake, *Modular Forms* (Springer 1989), Theorem 4.7.2, pp. 179–181 (case 3° of the proof, `k = 1`).

`isCompl_eisensteinSpace_range_cuspSpace` (`EisensteinSpace.lean`, `k ≥ 3`) and
`isCompl_eisensteinSpaceTwo_range_cuspSpace` (`WeightTwo.lean`) give the decomposition of Theorem 4.7.2 as a
complement in the sense of linear algebra. This file adds weight one, as a bridge to Tau Ceti main's
`TauCeti.isCompl_weightOneEisensteinSubspace_range_cuspToModFormCharSpace` (cusp forms against the weight-one
Eisenstein series compared at the cusps), through `eisensteinSpace_one_eq`.

* `isCompl_eisensteinSpace_one_range_cuspSpace`: `ℰ₁(N, χ)` is a complement of `𝒮₁(N, χ)` in `𝒢₁(N, χ)`.
* `isCompl_eisensteinSpaceGamma1_one_cuspFormSubmodule`: `ℰ₁(Γ₁(N))` is a complement of `𝒮₁(Γ₁(N))`.

As for `k ≥ 2`, Miyake's statement `ℰ₁(N, χ) = 𝒩₁(N, χ)` (the Petersson orthogonal complement) is not
formalized (LE-MF-0227).
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DirichletCharacter
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave10

open ModularFormsKB.Miyake.Wave4 TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- **Miyake, Theorem 4.7.2**, `k = 1`, as a complement: for `χ(-1) = -1`,
`𝒢₁(N, χ) = 𝒮₁(N, χ) ⊕ ℰ₁(N, χ)`. -/
@[kb "miyake1989" "Theorem 4.7.2, p. 179 (k = 1, complement of the cusp forms)"]
theorem isCompl_eisensteinSpace_one_range_cuspSpace {χ : DirichletCharacter ℂ N} (hχ : χ (-1) = -1) :
    IsCompl (eisensteinSpace 1 χ)
      (LinearMap.range (TauCeti.cuspToModFormCharSpace ((1 : ℕ) : ℤ) χ.toUnitHom)) := by
  rw [eisensteinSpace_one_eq hχ]
  exact TauCeti.isCompl_weightOneEisensteinSubspace_range_cuspToModFormCharSpace _

/-- **Miyake, Theorem 4.7.2** and (4.7.19), `k = 1`, for `Γ₁(N)`: `𝒢₁(Γ₁(N)) = 𝒮₁(Γ₁(N)) ⊕ ℰ₁(Γ₁(N))`. -/
@[kb "miyake1989" "Theorem 4.7.2 and (4.7.19), p. 180 (k = 1, Gamma_1(N))"]
theorem isCompl_eisensteinSpaceGamma1_one_cuspFormSubmodule :
    IsCompl (eisensteinSpaceGamma1 (N := N) 1)
      (cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) ((1 : ℕ) : ℤ)) := by
  rw [eisensteinSpaceGamma1_one_eq]
  exact isCompl_span_range_weightOneForm_cuspFormSubmodule

end ModularFormsKB.Miyake.Wave10
