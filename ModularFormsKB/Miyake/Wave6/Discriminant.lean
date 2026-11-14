import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import ModularFormsKB.Citation
/-!
# Miyake §4.1: the discriminant `Δ`, Theorem 4.1.7 (1), (2)

Miyake, *Modular Forms* (Springer 1989), Theorem 4.1.7, p. 101. Miyake's
`Δ(z) = 12^{-3} (G₄(z)³ − G₆(z)²)` ((4.1.14), with `G₄`, `G₆` the normalized Eisenstein series of
(4.1.19), (4.1.20)) is Mathlib's `CuspForm.discriminant` (`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`:
`Δ = (E₄³ − E₆²)/1728`).

* (1) `Δ ∈ 𝒮₁₂(Γ)`, its Fourier coefficients `τ_n` are rational integers and `τ₁ = 1`
  (`discriminant_coeff_int`, `discriminant_coeff_one`); integrality is Tau Ceti's
  `TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast` (Miyake postpones it to
  Theorem 4.4.2), `τ₁ = 1` is Mathlib's.
* (2) `Δ` has no zeros on `H` (Mathlib's `ModularForm.discriminant_ne_zero`, from the product
  formula).
* (3) (`𝒜₀(Γ) = ℂ(J)` and the expansion `J = e^{-2πiz} + Σ c_n e^{2πinz}`, `c_n ∈ ℤ`) is in
  `Wave6/LevelOneFunctions.lean` (`adjoin_J_eq_top`, `J_expansion`).
-/

open ModularForm ModularFormClass UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

/-- Miyake's `Δ = 12⁻³ (G₄³ − G₆²)` is Mathlib's discriminant. -/
@[kb "miyake1989" "(4.1.14), p. 101"]
theorem discriminant_eq (z : UpperHalfPlane) :
    CuspForm.discriminant z = (E₄ z ^ 3 - E₆ z ^ 2) / 1728 := by
  rw [CuspForm.coe_discriminant]
  exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z

/-- **Miyake, Theorem 4.1.7 (1)**: the Fourier coefficients `τ_n` of `Δ` are rational integers. -/
@[kb "miyake1989" "Theorem 4.1.7 (1), p. 101 (integrality)"]
theorem discriminant_coeff_int (n : ℕ) :
    ∃ t : ℤ, (qExpansion 1 CuspForm.discriminant).coeff n = t :=
  TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast n

/-- **Miyake, Theorem 4.1.7 (1)**: `τ₁ = 1`. -/
@[kb "miyake1989" "Theorem 4.1.7 (1), p. 101 (tau_1 = 1)"]
theorem discriminant_coeff_one : (qExpansion 1 CuspForm.discriminant).coeff 1 = 1 := by
  rw [CuspForm.coe_discriminant]
  exact ModularForm.discriminant_qExpansion_coeff_one

/-- **Miyake, Theorem 4.1.7 (2)**: `Δ` has no zeros on `H`. -/
@[kb "miyake1989" "Theorem 4.1.7 (2), p. 101"]
theorem discriminant_ne_zero (z : UpperHalfPlane) : CuspForm.discriminant z ≠ 0 := by
  rw [CuspForm.coe_discriminant]
  exact ModularForm.discriminant_ne_zero z

end ModularFormsKB.Miyake.Wave6
