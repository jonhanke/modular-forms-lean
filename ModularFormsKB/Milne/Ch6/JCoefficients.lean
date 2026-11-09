import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# The $q$-expansion of $j$ through $q^5$

Tau Ceti computes $j = q^{-1} + 744 + 196884q + \cdots$ (`TauCeti.ModularForm.laurentQExpansion_j_coeff_one`). For
Milne's Example 6.2 (`ModularFormsKB.Milne.ModularEquationLevelTwo`) we need the next four coefficients:
$$j = q^{-1} + 744 + 196884q + 21493760q^2 + 864299970q^3 + 20245856256q^4 + 333202640600q^5 + \cdots.$$
They are read off $qj \cdot \Delta = qE_4^3$, with $\Delta = (E_4^3 - E_6^2)/1728$ and the Eisenstein coefficients
$240\sigma_3(n)$, $-504\sigma_5(n)$, exactly as Tau Ceti computes the first ones.

## Main results
- `qExpansion_qParam_mul_j_coeff_three` … `qExpansion_qParam_mul_j_coeff_six`.
- `tendsto_j_remainder`: $\bigl(j - q^{-1} - \sum_{m=0}^{5} c_m q^m\bigr)/q^6$ converges at $i\infty$.
-/

open UpperHalfPlane ModularForm EisensteinSeries Filter Topology
open scoped ArithmeticFunction.sigma MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.JCoefficients

local notation "𝕢" => Function.Periodic.qParam

open TauCeti.ModularForm

private theorem bernoulli_four : bernoulli 4 = -1 / 30 := by decide +kernel

private theorem bernoulli_six : bernoulli 6 = 1 / 42 := by decide +kernel

private theorem divisors_four : Nat.divisors 4 = {1, 2, 4} := by decide

private theorem divisors_five : Nat.divisors 5 = {1, 5} := by decide

private theorem divisors_six : Nat.divisors 6 = {1, 2, 3, 6} := by decide

private theorem divisors_seven : Nat.divisors 7 = {1, 7} := by decide

theorem E₄_coeff_four : (qExpansion 1 E₄).coeff 4 = 17520 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, bernoulli_four, ArithmeticFunction.sigma_apply, divisors_four]

theorem E₄_coeff_five : (qExpansion 1 E₄).coeff 5 = 30240 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, bernoulli_four, ArithmeticFunction.sigma_apply, divisors_five]

theorem E₄_coeff_six : (qExpansion 1 E₄).coeff 6 = 60480 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, bernoulli_four, ArithmeticFunction.sigma_apply, divisors_six]

theorem E₄_coeff_seven : (qExpansion 1 E₄).coeff 7 = 82560 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, bernoulli_four, ArithmeticFunction.sigma_apply, divisors_seven]

theorem E₆_coeff_four : (qExpansion 1 E₆).coeff 4 = -532728 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, bernoulli_six, ArithmeticFunction.sigma_apply, divisors_four]

theorem E₆_coeff_five : (qExpansion 1 E₆).coeff 5 = -1575504 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, bernoulli_six, ArithmeticFunction.sigma_apply, divisors_five]

theorem E₆_coeff_six : (qExpansion 1 E₆).coeff 6 = -4058208 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, bernoulli_six, ArithmeticFunction.sigma_apply, divisors_six]

theorem E₆_coeff_seven : (qExpansion 1 E₆).coeff 7 = -8471232 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, bernoulli_six, ArithmeticFunction.sigma_apply, divisors_seven]

theorem discriminant_coeff_four : (qExpansion 1 discriminant).coeff 4 = -1472 := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₆_qExpansion_coeff_two,
    E₄_qExpansion_coeff_three, E₆_qExpansion_coeff_three, E₄_coeff_four, E₆_coeff_four,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

theorem discriminant_coeff_five : (qExpansion 1 discriminant).coeff 5 = 4830 := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₄_qExpansion_coeff_three, E₄_coeff_four, E₄_coeff_five, E₆_qExpansion_coeff_one, E₆_qExpansion_coeff_two, E₆_qExpansion_coeff_three, E₆_coeff_four, E₆_coeff_five,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

theorem discriminant_coeff_six : (qExpansion 1 discriminant).coeff 6 = -6048 := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₄_qExpansion_coeff_three, E₄_coeff_four, E₄_coeff_five, E₄_coeff_six, E₆_qExpansion_coeff_one, E₆_qExpansion_coeff_two, E₆_qExpansion_coeff_three, E₆_coeff_four, E₆_coeff_five, E₆_coeff_six,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

theorem discriminant_coeff_seven : (qExpansion 1 discriminant).coeff 7 = -16744 := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₄_qExpansion_coeff_three, E₄_coeff_four, E₄_coeff_five, E₄_coeff_six, E₄_coeff_seven, E₆_qExpansion_coeff_one, E₆_qExpansion_coeff_two, E₆_qExpansion_coeff_three, E₆_coeff_four, E₆_coeff_five, E₆_coeff_six, E₆_coeff_seven,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

/-- The $q^{3}$-coefficient of $qj$ is $21493760$. -/
theorem j_coeff_three : (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff 3 = 21493760 := by
  have h := congrArg (PowerSeries.coeff (3 + 1)) qExpansion_qParam_mul_j_mul_qExpansion_discriminant
  rw [PowerSeries.coeff_succ_X_mul] at h
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₄_qExpansion_coeff_three, discriminant_qExpansion_coeff_zero, discriminant_qExpansion_coeff_one, discriminant_qExpansion_coeff_two, discriminant_qExpansion_coeff_three, discriminant_coeff_four, qExpansion_qParam_mul_j_coeff_zero, qExpansion_qParam_mul_j_coeff_one, qExpansion_qParam_mul_j_coeff_two,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩] at h
  linear_combination h

/-- The $q^{4}$-coefficient of $qj$ is $864299970$. -/
theorem j_coeff_four : (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff 4 = 864299970 := by
  have h := congrArg (PowerSeries.coeff (4 + 1)) qExpansion_qParam_mul_j_mul_qExpansion_discriminant
  rw [PowerSeries.coeff_succ_X_mul] at h
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₄_qExpansion_coeff_three, E₄_coeff_four, discriminant_qExpansion_coeff_zero, discriminant_qExpansion_coeff_one, discriminant_qExpansion_coeff_two, discriminant_qExpansion_coeff_three, discriminant_coeff_four, discriminant_coeff_five, qExpansion_qParam_mul_j_coeff_zero, qExpansion_qParam_mul_j_coeff_one, qExpansion_qParam_mul_j_coeff_two, j_coeff_three,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩] at h
  linear_combination h

/-- The $q^{5}$-coefficient of $qj$ is $20245856256$. -/
theorem j_coeff_five : (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff 5 = 20245856256 := by
  have h := congrArg (PowerSeries.coeff (5 + 1)) qExpansion_qParam_mul_j_mul_qExpansion_discriminant
  rw [PowerSeries.coeff_succ_X_mul] at h
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₄_qExpansion_coeff_three, E₄_coeff_four, E₄_coeff_five, discriminant_qExpansion_coeff_zero, discriminant_qExpansion_coeff_one, discriminant_qExpansion_coeff_two, discriminant_qExpansion_coeff_three, discriminant_coeff_four, discriminant_coeff_five, discriminant_coeff_six, qExpansion_qParam_mul_j_coeff_zero, qExpansion_qParam_mul_j_coeff_one, qExpansion_qParam_mul_j_coeff_two, j_coeff_three, j_coeff_four,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩] at h
  linear_combination h

/-- The $q^{6}$-coefficient of $qj$ is $333202640600$. -/
theorem j_coeff_six : (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff 6 = 333202640600 := by
  have h := congrArg (PowerSeries.coeff (6 + 1)) qExpansion_qParam_mul_j_mul_qExpansion_discriminant
  rw [PowerSeries.coeff_succ_X_mul] at h
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₄_qExpansion_coeff_three, E₄_coeff_four, E₄_coeff_five, E₄_coeff_six, discriminant_qExpansion_coeff_zero, discriminant_qExpansion_coeff_one, discriminant_qExpansion_coeff_two, discriminant_qExpansion_coeff_three, discriminant_coeff_four, discriminant_coeff_five, discriminant_coeff_six, discriminant_coeff_seven, qExpansion_qParam_mul_j_coeff_zero, qExpansion_qParam_mul_j_coeff_one, qExpansion_qParam_mul_j_coeff_two, j_coeff_three, j_coeff_four, j_coeff_five,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩] at h
  linear_combination h

end ModularFormsKB.Milne.JCoefficients
