import ModularFormsKB.Historical.Ramanujan.TauDefs
import ModularFormsKB.Historical.Ramanujan.TauModFive
import ModularFormsKB.Historical.Ramanujan.JacobiCube
import Mathlib.RingTheory.PowerSeries.Derivative
import ModularFormsKB.Citation
/-!
# Ramanujan's `τ`: congruences modulo `5` and `7` and the two recurrences

Proofs of `TauModFive`, `TauModSeven`, `TauRecurrenceSigma`, `TauRecurrenceJacobi`
(statements in `TauDefs.lean`), from the formal identities `1728 D = Qf³ - Rf²`
(`delta_series_eq`, `D = X E²⁴`), `Qf² = 1 + 480 ∑ σ₇ Xⁿ`, `Pf Qf - Rf = 720 Φ_{1,4}`,
`Qf² - Pf Rf = 1008 Φ_{1,6}`, and Jacobi's cube identity `E³ = ∑ (-1)ᵏ (2k+1) X^{k(k+1)/2}`.
-/

noncomputable section

open PowerSeries Finset
open scoped ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Ramanujan

/-! ### The operator `θ = X d/dX` -/

/-- `θ f = ∑ n aₙ Xⁿ`, i.e. `X · d f/dX`. -/
def theta (f : ℤ⟦X⟧) : ℤ⟦X⟧ := X * d⁄dX f

theorem coeff_theta (f : ℤ⟦X⟧) (n : ℕ) : coeff n (theta f) = n * coeff n f := by
  unfold theta
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem theta_add (f g : ℤ⟦X⟧) : theta (f + g) = theta f + theta g := by
  ext n; simp [coeff_theta, mul_add]

theorem theta_sub (f g : ℤ⟦X⟧) : theta (f - g) = theta f - theta g := by
  ext n; simp [coeff_theta, mul_sub]

theorem theta_mul (f g : ℤ⟦X⟧) : theta (f * g) = theta f * g + f * theta g := by
  unfold theta
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem theta_pow (f : ℤ⟦X⟧) (n : ℕ) : theta (f ^ n) = n * f ^ (n - 1) * theta f := by
  unfold theta
  rw [Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem theta_X : theta (X : ℤ⟦X⟧) = X := by
  unfold theta; simp

theorem theta_ofNat_mul (k : ℕ) [k.AtLeastTwo] (f : ℤ⟦X⟧) :
    theta ((OfNat.ofNat k : ℤ⟦X⟧) * f) = (OfNat.ofNat k : ℤ⟦X⟧) * theta f := by
  have : (OfNat.ofNat k : ℤ⟦X⟧) = C (OfNat.ofNat k : ℤ) := (map_ofNat C k).symm
  rw [this]
  ext n
  rw [coeff_theta, coeff_C_mul, coeff_C_mul, coeff_theta]
  ring

theorem coeff_ofNat_mul' (k : ℕ) [k.AtLeastTwo] (f : ℤ⟦X⟧) (n : ℕ) :
    coeff n ((OfNat.ofNat k : ℤ⟦X⟧) * f) = (OfNat.ofNat k : ℤ) * coeff n f := by
  have : (OfNat.ofNat k : ℤ⟦X⟧) = C (OfNat.ofNat k : ℤ) := (map_ofNat C k).symm
  rw [this, coeff_C_mul]

/-! ### Formal identities -/

/-- `∑ n σ_s(n) Xⁿ`. -/
def Phis (s : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ ((n * σ s n : ℕ) : ℤ)

theorem sumsTo_Phis (s : ℕ) :
    SumsTo (PowerSeries.map (Int.castRingHom ℂ) (Phis s)) (Phi 1 (s + 1)) := by
  have h := sumsTo_mk (fun n ↦ ((n * σ s n : ℕ) : ℤ)) 1 (s + 2) (by
    intro n hn
    have h1 := sigma_norm_le s ⟨n, hn⟩
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    show ‖(((n * σ s n : ℕ) : ℤ) : ℂ)‖ ≤ _
    rw [Int.cast_natCast, Nat.cast_mul, norm_mul, Complex.norm_natCast]
    calc (n : ℝ) * ‖(σ s n : ℂ)‖ ≤ (n : ℝ) * (n : ℝ) ^ (s + 1) := by
          gcongr
          simpa using h1
      _ = 1 * (n : ℝ) ^ (s + 2) := by ring)
  refine h.congr fun x _ ↦ ?_
  rw [Phi_one s x]
  simp

theorem Qf_sq : Qf ^ 2 = affSeries 480 7 := by
  have h2 := (sumsTo_Qf.pow 2).unique ((sumsTo_affSeries 480 7).congr fun x hx ↦ by
    rw [Q_sq hx]; push_cast; rfl)
  apply map_intCast_injective
  rw [map_pow]
  exact h2

theorem PQ_sub_R : Pf * Qf = Rf + 720 * Phis 3 := by
  have h : SumsTo (PowerSeries.map (Int.castRingHom ℂ) Rf +
      C (720 : ℂ) * PowerSeries.map (Int.castRingHom ℂ) (Phis 3)) (fun x ↦ P x * Q x) := by
    refine (sumsTo_Rf.add ((sumsTo_Phis 3).cmul 720)).congr fun x hx ↦ ?_
    have := P_mul_Q_sub_R hx
    linear_combination (-1) * this
  have h2 := (sumsTo_Pf.mul sumsTo_Qf).unique h
  apply map_intCast_injective
  rw [map_mul, map_add, map_mul, map_ofNat, ← map_ofNat C]
  exact h2

theorem Qsq_sub_PR : Qf ^ 2 = Pf * Rf + 1008 * Phis 5 := by
  have h : SumsTo (PowerSeries.map (Int.castRingHom ℂ) Pf * PowerSeries.map (Int.castRingHom ℂ) Rf +
      C (1008 : ℂ) * PowerSeries.map (Int.castRingHom ℂ) (Phis 5)) (fun x ↦ Q x ^ 2) := by
    refine ((sumsTo_Pf.mul sumsTo_Rf).add ((sumsTo_Phis 5).cmul 1008)).congr fun x hx ↦ ?_
    have := Q_sq_sub_P_mul_R hx
    linear_combination (-1) * this
  have h2 := (sumsTo_Qf.pow 2).unique h
  apply map_intCast_injective
  rw [map_pow, map_add, map_mul, map_mul, map_ofNat, ← map_ofNat C]
  exact h2

theorem theta_Qf : theta Qf = 240 * Phis 3 := by
  ext n
  rw [coeff_theta, coeff_ofNat_mul']
  rcases n with _ | n
  · simp [Phis]
  · simp [Qf, affSeries, Phis, coeff_mk]; ring

theorem theta_Rf : theta Rf = -504 * Phis 5 := by
  ext n
  rw [coeff_theta, show (-504 : ℤ⟦X⟧) = -(504 : ℤ⟦X⟧) by rfl, neg_mul, map_neg, coeff_ofNat_mul']
  rcases n with _ | n
  · simp [Phis]
  · simp [Rf, affSeries, Phis, coeff_mk]; ring

theorem tau_zero : tau 0 = 0 := by simp [tau]

theorem tau_eq_coeff (n : ℕ) : tau n = coeff n (X * eulerSeries ^ 24 : ℤ⟦X⟧) := rfl

/-! ### The first recurrence -/

theorem theta_D : theta (X * eulerSeries ^ 24) = Pf * (X * eulerSeries ^ 24) := by
  have h1 := delta_series_eq
  have e1 := congrArg theta h1
  rw [theta_ofNat_mul, theta_sub, theta_pow, theta_pow, theta_Qf, theta_Rf] at e1
  have hne : (1728 : ℤ⟦X⟧) ≠ 0 := by
    rw [show (1728 : ℤ⟦X⟧) = C (1728 : ℤ) from (map_ofNat C 1728).symm]
    intro h
    exact absurd (C_injective (h.trans (map_zero C).symm)) (by norm_num)
  refine mul_left_cancel₀ hne ?_
  push_cast at e1
  norm_num at e1
  linear_combination e1 - Pf * h1 - Qf ^ 2 * PQ_sub_R - Rf * Qsq_sub_PR


theorem tau_antidiag (n : ℕ) :
    (n : ℤ) * tau n = ∑ p ∈ antidiagonal n, coeff p.1 Pf * tau p.2 := by
  have h := congrArg (coeff n) theta_D
  rw [coeff_theta, coeff_mul n Pf (X * eulerSeries ^ 24)] at h
  exact h

/-- **Ramanujan's first recurrence for `τ`** (No. 18, § 17, (99), p. 152, first
part): `(n - 1) τ(n) = -24 ∑_{k=1}^{n-1} σ₁(k) τ(n - k)`. -/
@[kb "ramanujan1927" "No. 18, § 17, (99), p. 152"]
theorem tauRecurrenceSigma : TauRecurrenceSigma := by
  intro n
  rcases n with _ | m
  · simp [tau_zero]
  · have h := tau_antidiag (m + 1)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ', sum_range_succ] at h
    rw [Finset.sum_Ico_eq_sum_range]
    have hs : ∑ k ∈ range m, coeff (k + 1) Pf * tau (m + 1 - (k + 1)) =
        -24 * ∑ k ∈ range (m + 1 - 1), (σ 1 (1 + k) : ℤ) * tau (m + 1 - (1 + k)) := by
      rw [Nat.add_sub_cancel, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [Pf, affSeries, coeff_mk, add_comm 1 k]
      simp
      ring
    simp only [Nat.sub_self, tau_zero, mul_zero, add_zero] at h
    have h0 : coeff 0 Pf = 1 := by simp [Pf, affSeries]
    rw [h0, one_mul, Nat.sub_zero, hs] at h
    push_cast at h ⊢
    linarith

/-! ### Modulo `5` -/

local notation "μ5" => PowerSeries.map (Int.castRingHom (ZMod 5))

theorem tau_cast_five (n : ℕ) : (tau n : ZMod 5) = ((n * σ 1 n : ℕ) : ZMod 5) := by
  have hQ := congrArg μ5 Qf_sub_Pf_sq
  have hD := congrArg μ5 delta_series_eq
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_X] at hQ hD
  rw [map5_Qf] at hQ hD
  rw [map5_Rf] at hD
  have h5 : (5 : (ZMod 5)⟦X⟧) = 0 := by
    rw [← map_ofNat C 5]
    have : (5 : ZMod 5) = 0 := by decide
    rw [this, map_zero]
  have key : X * μ5 eulerSeries ^ 24 = μ5 Phif := by
    linear_combination 2 * hD + 2 * hQ - (691 * (X * μ5 eulerSeries ^ 24) - 115 * μ5 Phif) * h5
  have e : X * μ5 eulerSeries ^ 24 = μ5 (X * eulerSeries ^ 24) := by
    simp [map_mul, map_pow, map_X]
  rw [e] at key
  have h := congrArg (coeff n) key
  rw [coeff_map, coeff_map] at h
  simpa [Phif, coeff_mk, tau] using h

/-- **Ramanujan's congruence `τ(5n) ≡ 0 (mod 5)`** (No. 28, p. 230; proof in the manuscript No. 30;
see also the editors' note in App. I, p. 346). -/
@[kb "ramanujan1927" "No. 28, p. 230"]
theorem tauModFive : TauModFive := by
  intro n
  have h : ((tau (5 * n) : ℤ) : ZMod 5) = 0 := by
    rw [tau_cast_five]
    have : (5 : ZMod 5) = 0 := by decide
    push_cast
    simp [this]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h

/-! ### Modulo `7` -/

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

local notation "μ7" => PowerSeries.map (Int.castRingHom (ZMod 7))

theorem map7_Rf : μ7 Rf = 1 := by
  ext n
  rw [coeff_map, coeff_one]
  simp only [Rf, affSeries, coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · have h : (504 : ZMod 7) = 0 := by decide
    simp [hn, h]

theorem sigma_seven_cast (n : ℕ) : ((σ 7 n : ℕ) : ZMod 7) = ((σ 1 n : ℕ) : ZMod 7) := by
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  push_cast
  rw [pow_one]
  exact ZMod.pow_card _

theorem map7_aff : μ7 (affSeries 480 7) = μ7 Pf := by
  ext n
  rw [coeff_map, coeff_map]
  simp only [Pf, affSeries, coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false, eq_intCast]
    push_cast
    rw [sigma_seven_cast]
    have : (480 : ZMod 7) = -24 := by decide
    rw [this]

theorem tau_cast_seven (n : ℕ) : (tau n : ZMod 7) = ((n * σ 3 n : ℕ) : ZMod 7) := by
  have hD := congrArg μ7 delta_series_eq
  have hA := congrArg μ7 Qf_sq
  have hB := congrArg μ7 PQ_sub_R
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_X, map_add] at hD hA hB
  rw [map7_aff] at hA
  rw [map7_Rf] at hD hB
  have h7 : (7 : (ZMod 7)⟦X⟧) = 0 := by
    rw [← map_ofNat C 7]
    have : (7 : ZMod 7) = 0 := by decide
    rw [this, map_zero]
  have key : X * μ7 eulerSeries ^ 24 = μ7 (Phis 3) := by
    linear_combination (-1) * hD - hB - μ7 Qf * hA +
      (247 * (X * μ7 eulerSeries ^ 24) - 103 * μ7 (Phis 3)) * h7
  have e : X * μ7 eulerSeries ^ 24 = μ7 (X * eulerSeries ^ 24) := by
    simp [map_mul, map_pow, map_X]
  rw [e] at key
  have h := congrArg (coeff n) key
  rw [coeff_map, coeff_map] at h
  simpa [Phis, coeff_mk, tau] using h

theorem sigma_three_zero (n : ℕ) (h : n % 7 = 3 ∨ n % 7 = 5 ∨ n % 7 = 6) :
    ((σ 3 n : ℕ) : ZMod 7) = 0 := by
  have hn3 : ((n : ℕ) : ZMod 7) ^ 3 = -1 := by
    rw [← ZMod.natCast_mod n 7]
    rcases h with h | h | h <;> rw [h] <;> decide
  have hn0 : n ≠ 0 := by omega
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Nat.cast_pow]
  have key : ∀ x y : ZMod 7, x ^ 3 * y ^ 3 = -1 → x ^ 3 + y ^ 3 = 0 := by decide
  have nsq : ∀ x : ZMod 7, (x * x) ^ 3 ≠ -1 := by decide
  refine Finset.sum_involution (fun d _ ↦ n / d) ?_ ?_ ?_ ?_
  · intro d hd
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hm : (d : ZMod 7) * ((n / d : ℕ) : ZMod 7) = n := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdn]
    apply key
    rw [← mul_pow, hm]
    exact hn3
  · intro d hd _ heq
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hm : (d : ZMod 7) * ((n / d : ℕ) : ZMod 7) = n := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdn]
    rw [heq] at hm
    exact nsq _ (by rw [hm]; exact hn3)
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1, hn0⟩
  · intro d hd
    exact Nat.div_div_self (Nat.mem_divisors.mp hd).1 hn0

/-- **Ramanujan's congruence modulo 7** (No. 28, p. 230):
`τ(7n), τ(7n + 3), τ(7n + 5), τ(7n + 6) ≡ 0 (mod 7)`. -/
@[kb "ramanujan1927" "No. 28, p. 230"]
theorem tauModSeven : TauModSeven := by
  intro n h
  suffices hz : ((tau n : ℤ) : ZMod 7) = 0 by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz
  rw [tau_cast_seven]
  rcases h with h | h | h | h
  · have : (n : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff n 7).mpr (by omega)
    push_cast
    simp [this]
  all_goals
    have := sigma_three_zero n (by omega)
    push_cast
    simp [this]

/-! ### The second recurrence -/

theorem coeff_identity (J D : ℤ⟦X⟧) (h : J * theta D = J * D + 8 * (theta J * D)) (n : ℕ) :
    ∑ k ∈ range (n + 1), coeff k J * coeff (n - k) D * (((n - k : ℕ) : ℤ) - 1 - 8 * k) = 0 := by
  have h' := congrArg (coeff n) h
  rw [coeff_mul, map_add, coeff_mul, coeff_ofNat_mul', coeff_mul] at h'
  simp only [coeff_theta, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h'
  have e : ∑ k ∈ range (n + 1), coeff k J * coeff (n - k) D * (((n - k : ℕ) : ℤ) - 1 - 8 * k) =
      ∑ k ∈ range (n + 1), coeff k J * (((n - k : ℕ) : ℤ) * coeff (n - k) D) -
      ∑ k ∈ range (n + 1), coeff k J * coeff (n - k) D -
      8 * ∑ k ∈ range (n + 1), ((k : ℤ) * coeff k J) * coeff (n - k) D := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [e]
  linear_combination h'

theorem jacobi_ident :
    jacobiCubeSeries * theta (X * eulerSeries ^ 24) =
      jacobiCubeSeries * (X * eulerSeries ^ 24) +
        8 * (theta jacobiCubeSeries * (X * eulerSeries ^ 24)) := by
  have hD : (X * eulerSeries ^ 24 : ℤ⟦X⟧) = X * jacobiCubeSeries ^ 8 := by
    rw [show eulerSeries ^ 24 = (eulerSeries ^ 3) ^ 8 by ring, eulerSeries_cube]
  rw [hD, theta_mul, theta_X, theta_pow]
  norm_num
  ring

/-- **Ramanujan's second recurrence for `τ`** (No. 18, § 17, (100), p. 153,
second part): with `t_r = r(r-1)/2`,
`∑_{r ≥ 1} (-1)^{r-1} (2r - 1) (n - 1 - 9 t_r) τ(n - t_r) = 0`, i.e.
`(n-1) τ(n) - 3(n-10) τ(n-1) + 5(n-28) τ(n-3) - 7(n-55) τ(n-6) + ⋯ = 0`.
Written with `r = j + 1`, `t_r = j(j+1)/2`, the sum over `j` with `j(j+1)/2 < n`. -/
@[kb "ramanujan1927" "No. 18, § 17, (100), p. 153"]
theorem tauRecurrenceJacobi : TauRecurrenceJacobi := by
  intro n
  have hc : ∀ k, coeff k jacobiCubeSeries = jacobiCubeCoeff k := fun k ↦ coeff_mk _ _
  have hmain := coeff_identity _ _ jacobi_ident n
  simp only [hc, ← tau_eq_coeff] at hmain
  set S := (range n).filter (fun j ↦ j * (j + 1) / 2 < n) with hS
  set g : ℕ → ℤ := fun k ↦
    jacobiCubeCoeff k * tau (n - k) * (((n - k : ℕ) : ℤ) - 1 - 8 * k) with hg
  have himg : ∑ k ∈ S.image (fun j ↦ j * (j + 1) / 2), g k =
      ∑ j ∈ S, g (j * (j + 1) / 2) :=
    Finset.sum_image fun a _ b _ h ↦ triangular_strictMono.injective h
  have hsub : ∑ k ∈ S.image (fun j ↦ j * (j + 1) / 2), g k = ∑ k ∈ range (n + 1), g k := by
    apply Finset.sum_subset
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      have := (Finset.mem_filter.mp hj).2
      exact Finset.mem_range.mpr (by show j * (j + 1) / 2 < n + 1; omega)
    · intro k hk hnot
      by_cases hr : k ∈ Set.range (fun k : ℕ ↦ k * (k + 1) / 2)
      · obtain ⟨j, rfl⟩ := hr
        have hkn : j * (j + 1) / 2 = n := by
          by_contra hne
          have hlt : j * (j + 1) / 2 < n := by
            have := Finset.mem_range.mp hk
            beta_reduce at this
            omega
          exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (lt_of_le_of_lt (le_triangular j) hlt), hlt⟩, rfl⟩)
        simp [hg, hkn, tau_zero]
      · simp [hg, jacobiCubeCoeff_eq_zero hr]
  rw [← hmain, ← hsub, himg]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hlt : j * (j + 1) / 2 < n := (Finset.mem_filter.mp hj).2
  simp only [hg]
  rw [jacobiCubeCoeff_triangular, Nat.cast_sub hlt.le]
  ring

end ModularFormsKB.Historical.Ramanujan
