import ModularFormsKB.Historical.Ramanujan.PhiTwo
import ModularFormsKB.Citation
/-!
# Ramanujan's `Φ_{3,4}`, `Φ_{3,6}`, `Φ_{4,5}` in terms of `P`, `Q`, `R`

Ramanujan (*Collected Papers*, No. 30, § 1, (1.91)–(1.93), p. 233) continues the table of
`Φ_{r,s}(x) = ∑ N^r σ_{s-r}(N) x^N` as polynomials in `P`, `Q`, `R`:

* (1.91) `6P²Q - 8PR + 3Q² - P⁴ = 6912 ∑ N³ σ₁(N) x^N` (`Φ_{3,4}`),
* (1.92) `P³Q - 3P²R + 3PQ² - QR = 3456 ∑ N³ σ₃(N) x^N` (`Φ_{3,6}`),
* (1.93) `15PQ² - 20P²R + 10P³Q - 4QR - P⁵ = 20736 ∑ N⁴ σ₁(N) x^N` (`Φ_{4,5}`).

In the printed (1.93) the exponent of the last `P` is not legible in the scan; it is `P⁵` (weight 10;
checked to`x¹¹`). Stated, as `PhiTwoTable`, as identities of formal power series over `ℤ` (`Pf`, `Qf`, `Rf`
of `TauModFive.lean`); they follow from Ramanujan's differential equations by further applications of
`θ = x d/dx` to the table of `PhiTwo.lean`.
-/

noncomputable section

open PowerSeries
open scoped ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Ramanujan

/-- `Φ_{3, s+3} = ∑ N³ σ_s(N) X^N` as a formal power series over `ℤ`. -/
def Phi3s (s : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ ((n ^ 3 * σ s n : ℕ) : ℤ)

/-- `Φ_{4, s+4} = ∑ N⁴ σ_s(N) X^N` as a formal power series over `ℤ`. -/
def Phi4s (s : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ ((n ^ 4 * σ s n : ℕ) : ℤ)

/-- **Ramanujan's `Φ_{3,4}`, `Φ_{3,6}`, `Φ_{4,5}`** (No. 30, (1.91)–(1.93), p. 233). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.91)–(1.93), p. 233"]
def PhiThreeTable : Prop :=
  6 * Pf ^ 2 * Qf - 8 * Pf * Rf + 3 * Qf ^ 2 - Pf ^ 4 = 6912 * Phi3s 1 ∧
  Pf ^ 3 * Qf - 3 * Pf ^ 2 * Rf + 3 * Pf * Qf ^ 2 - Qf * Rf = 3456 * Phi3s 3 ∧
  15 * Pf * Qf ^ 2 - 20 * Pf ^ 2 * Rf + 10 * Pf ^ 3 * Qf - 4 * Qf * Rf - Pf ^ 5 = 20736 * Phi4s 1

theorem Phi3s_eq_theta (s : ℕ) : Phi3s s = theta (Phi2s s) := by
  ext n
  simp only [Phi3s, Phi2s, coeff_theta, coeff_mk]
  push_cast
  ring

theorem Phi4s_eq_theta (s : ℕ) : Phi4s s = theta (Phi3s s) := by
  ext n
  simp only [Phi4s, Phi3s, coeff_theta, coeff_mk]
  push_cast
  ring

private theorem theta_ofNat_zero (k : ℕ) [k.AtLeastTwo] :
    theta (no_index (OfNat.ofNat k : ℤ⟦X⟧)) = 0 := by
  ext n
  rw [coeff_theta]
  rcases n with _ | n
  · simp
  · have : (OfNat.ofNat k : ℤ⟦X⟧) = C (OfNat.ofNat k : ℤ) := (map_ofNat C k).symm
    rw [this, coeff_C]
    simp

private theorem ode_P : 12 * theta Pf = Pf ^ 2 - Qf := by
  have hA := Qf_sub_Pf_sq
  change Qf - Pf ^ 2 = 288 * Phis 1 at hA
  linear_combination 12 * theta_Pf + hA

private theorem ode_Q : 3 * theta Qf = Pf * Qf - Rf := by
  linear_combination 3 * theta_Qf - PQ_sub_R

private theorem ode_R : 2 * theta Rf = Pf * Rf - Qf ^ 2 := by
  linear_combination 2 * theta_Rf + Qsq_sub_PR

private theorem three_ne : (3 : ℤ⟦X⟧) ≠ 0 := by
  intro h0
  have := congrArg constantCoeff h0
  rw [map_ofNat] at this
  norm_num at this

theorem phiThree_one :
    6 * Pf ^ 2 * Qf - 8 * Pf * Rf + 3 * Qf ^ 2 - Pf ^ 4 = 6912 * Phi3s 1 := by
  have e := congrArg theta phiTwo_one
  simp only [theta_sub, theta_mul, theta_pow, theta_ofNat_zero] at e
  norm_num at e
  have h1 := ode_P
  have h2 := ode_Q
  have h3 := ode_R
  rw [Phi3s_eq_theta]
  linear_combination 4 * e - (Qf - Pf ^ 2) * h1 - 4 * Pf * h2 + 4 * h3

theorem phiThree_three :
    Pf ^ 3 * Qf - 3 * Pf ^ 2 * Rf + 3 * Pf * Qf ^ 2 - Qf * Rf = 3456 * Phi3s 3 := by
  have e := congrArg theta phiTwo_three
  simp only [theta_sub, theta_add, theta_mul, theta_pow, theta_ofNat_zero] at e
  norm_num at e
  have h1 := ode_P
  have h2 := ode_Q
  have h3 := ode_R
  rw [Phi3s_eq_theta]
  apply mul_left_cancel₀ three_ne
  linear_combination 6 * e - (Pf * Qf - Rf) * h1 - (2 * Pf ^ 2 + 4 * Qf) * h2 + 6 * Pf * h3

theorem phiThree_four :
    15 * Pf * Qf ^ 2 - 20 * Pf ^ 2 * Rf + 10 * Pf ^ 3 * Qf - 4 * Qf * Rf - Pf ^ 5 =
      20736 * Phi4s 1 := by
  have e := congrArg theta phiThree_one
  simp only [theta_sub, theta_add, theta_mul, theta_pow, theta_ofNat_zero] at e
  norm_num at e
  have h1 := ode_P
  have h2 := ode_Q
  have h3 := ode_R
  rw [Phi4s_eq_theta]
  linear_combination 3 * e - (3 * Pf * Qf - 2 * Rf - Pf ^ 3) * h1
    - (6 * Pf ^ 2 + 6 * Qf) * h2 + 12 * Pf * h3

/-- **Ramanujan's `Φ_{3,4}`, `Φ_{3,6}`, `Φ_{4,5}`**: by applying `θ = X d/dX` to
the table of `PhiTwo.lean` and Ramanujan's differential equations. -/
@[kb "ramanujan1927" "No. 30, § 1, (1.91)–(1.93), p. 233"]
theorem phiThreeTable : PhiThreeTable :=
  ⟨phiThree_one, phiThree_three, phiThree_four⟩

end ModularFormsKB.Historical.Ramanujan
