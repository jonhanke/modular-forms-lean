import ModularFormsKB.Milne.Wave13.AllFiniteIndex
import ModularFormsKB.Miyake.Wave3.GenusDimension

/-!
# Miyake's dimension and genus formulas for every modular group, unconditional

T. Miyake, *Modular Forms* (`miyake1989`), Theorem 2.5.2 (pp. 60–61) and Theorem 4.2.11 (p. 113), for a modular group
(a subgroup of finite index in `SL₂(ℤ)`). The library stated them conditionally on Riemann–Roch and the canonical
degree on `X(Γ)` (`ModularFormsKB.Miyake.finrank_modularForm_of_riemannRoch`), respectively on the Riemann–Hurwitz
formula (`ModularFormsKB.Miyake.genus_modularCurveX_eq`); both inputs are now proved for every finite-index `Γ`
(`ModularFormsKB.Milne.Wave13.riemannRoch_of_finiteIndex`).
-/

open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave13

open ModularFormsKB.Milne ModularFormsKB.Milne.RiemannSurface

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Miyake, Theorem 2.5.2** (the dimension of `𝒢_{2k}(Γ)`, `2k ≥ 2`) for every modular group, unconditional:
`dim 𝒢_{2k}(Γ) = (2k - 1)(g - 1) + k t + Σ_μ [k(1 - 1/e_μ)]`, `t` the number of cusps. -/
@[kb "miyake1989" "Theorem 2.5.2, pp. 60-61 (every modular group)"]
theorem miyake_finrank_modularForm (k : ℕ) (hk : 1 ≤ k) :
    (Module.finrank ℂ (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (2 * k : ℕ)) : ℤ) =
      (2 * k - 1) * ((Milne.genus (modularCurve Γ) : ℤ) - 1) + cuspCount Γ * k + ellipticTerm Γ k :=
  Miyake.finrank_modularForm_of_riemannRoch Γ (riemannRoch_of_finiteIndex Γ) (canonicalDegree_of_finiteIndex Γ) k hk

/-- **Miyake, Theorem 4.2.11** (the genus of `X(Γ)`) for every modular group, unconditional:
`g = 1 + μ/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "miyake1989" "Theorem 4.2.11, p. 113 (every modular group)"]
theorem miyake_genus_modularCurveX :
    (RiemannSurface.genus (ModularCurveX Γ) : ℚ) =
      1 + (genusIndex Γ : ℚ) / 12 - (nuTwo Γ : ℚ) / 4 - (nuThree Γ : ℚ) / 3 - (nuInfty Γ : ℚ) / 2 :=
  Miyake.genus_modularCurveX_eq Γ (riemannHurwitz_of_finiteIndex Γ)

end ModularFormsKB.Milne.Wave13
