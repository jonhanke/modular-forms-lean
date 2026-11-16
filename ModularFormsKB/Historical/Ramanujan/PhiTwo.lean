import ModularFormsKB.Historical.Ramanujan.Tau
import ModularFormsKB.Citation
/-!
# Ramanujan's `Φ_{2,s}` in terms of `P`, `Q`, `R`

Ramanujan (*Collected Papers*, No. 30, § 1, (1.81)–(1.83), p. 233) expresses
`Φ_{r,s}(x) = ∑ N^r σ_{s-r}(N) x^N` as polynomials in `P`, `Q`, `R`. For `r = 2`:

* `3PQ - 2R - P³ = 1728 ∑ N² σ₁(N) x^N` (`Φ_{2,3}`),
* `P²Q - 2PR + Q² = 1728 ∑ N² σ₃(N) x^N` (`Φ_{2,5}`),
* `2PQ² - P²R - QR = 1728 ∑ N² σ₅(N) x^N` (`Φ_{2,7}`).

Stated as identities of formal power series over `ℤ` (`Pf`, `Qf`, `Rf` of `TauModFive.lean`); they follow from
Ramanujan's differential equations by one more application of `θ = x d/dx`.
-/

noncomputable section

open PowerSeries
open scoped ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Ramanujan

/-- `Φ_{2, s+2} = ∑ N² σ_s(N) X^N` as a formal power series over `ℤ`. -/
def Phi2s (s : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ ((n ^ 2 * σ s n : ℕ) : ℤ)

/-- **Ramanujan's `Φ_{2,3}`, `Φ_{2,5}`, `Φ_{2,7}`** (No. 30, (1.81)–(1.83), p. 233):
`3PQ - 2R - P³ = 1728 Φ_{2,3}`, `P²Q - 2PR + Q² = 1728 Φ_{2,5}`,
`2PQ² - P²R - QR = 1728 Φ_{2,7}`. -/
@[kb "ramanujan1927" "No. 30, § 1, (1.81)–(1.83), p. 233"]
def PhiTwoTable : Prop :=
  3 * Pf * Qf - 2 * Rf - Pf ^ 3 = 1728 * Phi2s 1 ∧
  Pf ^ 2 * Qf - 2 * Pf * Rf + Qf ^ 2 = 1728 * Phi2s 3 ∧
  2 * Pf * Qf ^ 2 - Pf ^ 2 * Rf - Qf * Rf = 1728 * Phi2s 5

theorem theta_Pf : theta Pf = -24 * Phis 1 := by
  ext n
  rw [coeff_theta, show (-24 : ℤ⟦X⟧) = -(24 : ℤ⟦X⟧) by rfl, neg_mul, map_neg, coeff_ofNat_mul']
  rcases n with _ | n
  · simp [Phis]
  · simp [Pf, affSeries, Phis, coeff_mk]; ring

theorem Phi2s_eq_theta (s : ℕ) : Phi2s s = theta (Phis s) := by
  ext n
  simp only [Phi2s, Phis, coeff_theta, coeff_mk]
  push_cast
  ring

theorem phiTwo_one :
    3 * Pf * Qf - 2 * Rf - Pf ^ 3 = 1728 * Phi2s 1 := by
  have e := congrArg theta Qf_sub_Pf_sq
  rw [theta_sub, theta_pow, theta_ofNat_mul, theta_Qf, theta_Pf] at e
  have hA : Phif = Phis 1 := rfl
  rw [hA] at e
  have h := PQ_sub_R
  rw [Phi2s_eq_theta]
  norm_num at e
  have hA' := Qf_sub_Pf_sq
  rw [hA] at hA'
  linear_combination 6 * e + 2 * h + Pf * hA'

theorem phiTwo_three :
    Pf ^ 2 * Qf - 2 * Pf * Rf + Qf ^ 2 = 1728 * Phi2s 3 := by
  have e := congrArg theta PQ_sub_R
  rw [theta_mul, theta_add, theta_ofNat_mul, theta_Qf, theta_Rf, theta_Pf] at e
  have hA := Qf_sub_Pf_sq
  change Qf - Pf ^ 2 = 288 * Phis 1 at hA
  have h := PQ_sub_R
  have h2 := Qsq_sub_PR
  rw [Phi2s_eq_theta]
  apply mul_left_cancel₀ (show (5 : ℤ⟦X⟧) ≠ 0 from by
    intro h0
    have := congrArg constantCoeff h0
    rw [map_ofNat] at this
    norm_num at this)
  linear_combination 12 * e - Qf * hA + 4 * Pf * h + 6 * h2

theorem phiTwo_five :
    2 * Pf * Qf ^ 2 - Pf ^ 2 * Rf - Qf * Rf = 1728 * Phi2s 5 := by
  have e := congrArg theta Qsq_sub_PR
  rw [theta_pow, theta_add, theta_mul, theta_ofNat_mul, theta_Qf, theta_Rf, theta_Pf] at e
  have hA := Qf_sub_Pf_sq
  change Qf - Pf ^ 2 = 288 * Phis 1 at hA
  have h := PQ_sub_R
  have h2 := Qsq_sub_PR
  rw [Phi2s_eq_theta]
  norm_num at e
  apply mul_left_cancel₀ (show (7 : ℤ⟦X⟧) ≠ 0 from by
    intro h0
    have := congrArg constantCoeff h0
    rw [map_ofNat] at this
    norm_num at this)
  linear_combination 12 * e + Rf * hA + 8 * Qf * h + 6 * Pf * h2

/-- **Ramanujan's `Φ_{2,3}`, `Φ_{2,5}`, `Φ_{2,7}`**: proved by applying
`θ = X d/dX` to `Q - P² = 288 Φ_{1,2}`, `PQ - R = 720 Φ_{1,4}`, `Q² - PR = 1008 Φ_{1,6}`. -/
@[kb "ramanujan1927" "No. 30, § 1, (1.81)–(1.83), p. 233"]
theorem phiTwoTable : PhiTwoTable :=
  ⟨phiTwo_one, phiTwo_three, phiTwo_five⟩

end ModularFormsKB.Historical.Ramanujan
