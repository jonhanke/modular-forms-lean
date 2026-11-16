import ModularFormsKB.Historical.Ramanujan.Congruences
import ModularFormsKB.Historical.Ramanujan.PowerSeriesBridge
import ModularFormsKB.Historical.Ramanujan.Equations
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import ModularFormsKB.Citation
/-!
# Ramanujan's congruence `x ∏ (1 - x^{25n}) / ∏ (1 - xⁿ) ≡ ∑ n σ₁(n) xⁿ (mod 5)`

Ramanujan, *Congruence properties of partitions* (posthumous; *Collected Papers* 1927, No. 30, § 2,
(2.3)–(2.4), p. 234).

Proof structure, with `E = ∏ (1 - Xⁿ)` and the integer series `Pf, Qf, Rf, Phif` of Ramanujan's
`P, Q, R, Φ_{1,2}`:
* `sumsTo_Pf` etc.: each of these series converges on the unit disc to `P, Q, R, Φ_{1,2}`;
* `Qf_sub_Pf_sq`: `Qf - Pf² = 288 Φf`, from `Q - P² = 288 Φ_{1,2}` (`Equations.lean`);
* `delta_analytic`: `1728 x ∏ (1 - xⁿ)²⁴ = Q³ - R²` for `|x| < 1`, from Mathlib's product formula for
  the discriminant and `Δ = (E₄³ - E₆²)/1728`;
* `delta_series_eq`: `1728 X E²⁴ = Qf³ - Rf²` in `ℤ⟦X⟧`, by the bridge `SumsTo`;
* modulo `5`: `Qf ≡ 1`, `Rf ≡ Pf`, hence `X E²⁴ ≡ Φf`; and `E²⁵ ≡ ∏ (1 - X^{25n})` (Frobenius) with
  `P · E = 1` gives the statement.
-/

noncomputable section

open PowerSeries Finset Complex
open UpperHalfPlane hiding I
open scoped ArithmeticFunction.sigma Real

namespace ModularFormsKB.Historical.Ramanujan

/-! ### More closure properties of `SumsTo` -/

theorem SumsTo.congr {f : ℂ⟦X⟧} {F G : ℂ → ℂ} (h : SumsTo f F)
    (hFG : ∀ x : ℂ, ‖x‖ < 1 → F x = G x) : SumsTo f G := by
  intro x hx
  obtain ⟨a, b⟩ := h x hx
  refine ⟨a, ?_⟩
  rw [← hFG x hx]
  exact b

theorem SumsTo.add {f g : ℂ⟦X⟧} {F G : ℂ → ℂ} (hf : SumsTo f F) (hg : SumsTo g G) :
    SumsTo (f + g) (fun x ↦ F x + G x) := by
  intro x hx
  obtain ⟨sf, hf'⟩ := hf x hx
  obtain ⟨sg, hg'⟩ := hg x hx
  refine ⟨?_, ?_⟩
  · refine (sf.add sg).of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ ?_
    rw [map_add, ← add_mul]
    gcongr
    exact norm_add_le _ _
  · simpa [map_add, add_mul] using hf'.add hg'

theorem SumsTo.cmul (c : ℂ) {f : ℂ⟦X⟧} {F : ℂ → ℂ} (hf : SumsTo f F) :
    SumsTo (C c * f) (fun x ↦ c * F x) := by
  intro x hx
  obtain ⟨sf, hf'⟩ := hf x hx
  refine ⟨?_, ?_⟩
  · refine (sf.mul_left ‖c‖).congr fun n ↦ ?_
    rw [coeff_C_mul, norm_mul]
    ring
  · simpa [coeff_C_mul, mul_assoc] using hf'.mul_left c

theorem sumsTo_X : SumsTo (X : ℂ⟦X⟧) (fun x ↦ x) := by
  intro x hx
  refine ⟨summable_of_ne_finset_zero (s := {1}) fun n hn ↦ ?_, ?_⟩
  · simp at hn
    simp [coeff_X, hn]
  · simpa [coeff_X] using hasSum_single (f := fun n : ℕ ↦ coeff n (X : ℂ⟦X⟧) * x ^ n) 1
      (fun n hn ↦ by simp [coeff_X, hn])

/-- An integer series with coefficients bounded by `C n^k` (for `n ≥ 1`) converges on the open unit
disc, with sum `a₀ + ∑_{n ≥ 1} aₙ xⁿ`. -/
theorem sumsTo_mk (a : ℕ → ℤ) (c : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, 0 < n → ‖(a n : ℂ)‖ ≤ c * (n : ℝ) ^ k) :
    SumsTo (PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.mk a))
      (fun x ↦ (a 0 : ℂ) + ∑' n : ℕ+, (a n : ℂ) * x ^ (n : ℕ)) := by
  intro x hx
  have hr : ‖‖x‖‖ < 1 := by simpa using hx
  have hs : Summable (fun n : ℕ ↦ (n : ℝ) ^ k * ‖x‖ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  have hn : Summable (fun n : ℕ ↦ ‖(a n : ℂ)‖ * ‖x‖ ^ n) := by
    rw [← summable_nat_add_iff 1]
    have hs1 := (summable_nat_add_iff 1).mpr (hs.mul_left c)
    refine hs1.of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ ?_
    have := ha (n + 1) (Nat.succ_pos n)
    calc ‖(a (n + 1) : ℂ)‖ * ‖x‖ ^ (n + 1)
        ≤ (c * ((n + 1 : ℕ) : ℝ) ^ k) * ‖x‖ ^ (n + 1) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by push_cast; ring
  have hx' : Summable (fun n : ℕ ↦ (a n : ℂ) * x ^ n) := by
    refine Summable.of_norm ?_
    simpa [norm_mul, norm_pow] using hn
  have e : (a 0 : ℂ) + ∑' n : ℕ+, (a n : ℂ) * x ^ (n : ℕ) = ∑' n : ℕ, (a n : ℂ) * x ^ n := by
    rw [hx'.tsum_eq_zero_add, tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ (a n : ℂ) * x ^ n)]
    simp
  refine ⟨?_, ?_⟩
  · simpa [coeff_map] using hn
  · beta_reduce
    rw [e]
    simpa [coeff_map] using hx'.hasSum

/-! ### Ramanujan's series as integer power series -/

/-- `1 + c ∑_{n ≥ 1} σ_s(n) Xⁿ ∈ ℤ⟦X⟧`. -/
def affSeries (c : ℤ) (s : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n ↦ if n = 0 then 1 else c * (σ s n : ℤ)

theorem sumsTo_affSeries (c : ℤ) (s : ℕ) :
    SumsTo (PowerSeries.map (Int.castRingHom ℂ) (affSeries c s))
      (fun x ↦ 1 + (c : ℂ) * ∑' n : ℕ+, (σ s n : ℂ) * x ^ (n : ℕ)) := by
  have h := sumsTo_mk (fun n ↦ if n = 0 then 1 else c * (σ s n : ℤ)) ‖(c : ℂ)‖ (s + 1) (by
    intro n hn
    simp only [hn.ne', ite_false]
    push_cast
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (sigma_norm_le s ⟨n, hn⟩) (norm_nonneg _))
  refine h.congr fun x hx ↦ ?_
  have h2 : ∀ n : ℕ+, (((if (n : ℕ) = 0 then 1 else c * (σ s n : ℤ) : ℤ)) : ℂ) * x ^ (n : ℕ) =
      (c : ℂ) * ((σ s n : ℂ) * x ^ (n : ℕ)) := by
    intro n
    simp only [n.ne_zero, ite_false]
    push_cast
    ring
  simp only [h2, tsum_mul_left]
  simp

/-- `Pf = 1 - 24 ∑ σ₁(n) Xⁿ`, Ramanujan's `P` as an integer power series. -/
def Pf : ℤ⟦X⟧ := affSeries (-24) 1

/-- `Qf = 1 + 240 ∑ σ₃(n) Xⁿ`, Ramanujan's `Q`. -/
def Qf : ℤ⟦X⟧ := affSeries 240 3

/-- `Rf = 1 - 504 ∑ σ₅(n) Xⁿ`, Ramanujan's `R`. -/
def Rf : ℤ⟦X⟧ := affSeries (-504) 5

/-- `Phif = ∑ n σ₁(n) Xⁿ`, Ramanujan's `Φ_{1,2}` as an integer power series. -/
def Phif : ℤ⟦X⟧ := PowerSeries.mk fun n ↦ ((n * σ 1 n : ℕ) : ℤ)

theorem sumsTo_Pf : SumsTo (PowerSeries.map (Int.castRingHom ℂ) Pf) P := by
  refine (sumsTo_affSeries (-24) 1).congr fun x _ ↦ ?_
  rw [P_eq_fun]
  push_cast
  rfl

theorem sumsTo_Qf : SumsTo (PowerSeries.map (Int.castRingHom ℂ) Qf) Q := by
  refine (sumsTo_affSeries 240 3).congr fun x _ ↦ ?_
  rw [Q_eq_fun]
  push_cast
  rfl

theorem sumsTo_Rf : SumsTo (PowerSeries.map (Int.castRingHom ℂ) Rf) R := by
  refine (sumsTo_affSeries (-504) 5).congr fun x _ ↦ ?_
  rw [R_eq_fun]
  push_cast
  rfl

theorem sumsTo_Phif : SumsTo (PowerSeries.map (Int.castRingHom ℂ) Phif) (Phi 1 2) := by
  have h := sumsTo_mk (fun n ↦ ((n * σ 1 n : ℕ) : ℤ)) 1 3 (by
    intro n hn
    have h1 := sigma_norm_le 1 ⟨n, hn⟩
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    show ‖(((n * σ 1 n : ℕ) : ℤ) : ℂ)‖ ≤ _
    rw [Int.cast_natCast, Nat.cast_mul, norm_mul, Complex.norm_natCast]
    calc (n : ℝ) * ‖(σ 1 n : ℂ)‖ ≤ (n : ℝ) * (n : ℝ) ^ (1 + 1) := by
          gcongr
          simpa using h1
      _ = 1 * (n : ℝ) ^ 3 := by ring)
  refine h.congr fun x _ ↦ ?_
  have := Phi_one 1 x
  rw [show (2 : ℕ) = 1 + 1 from rfl, this]
  simp

/-! ### Formal identities -/

/-- **Ramanujan No. 30, (1.71)** as an identity in `ℤ⟦X⟧`: `Q - P² = 288 Φ_{1,2}`. -/
theorem Qf_sub_Pf_sq : Qf - Pf ^ 2 = 288 * Phif := by
  have h : SumsTo (PowerSeries.map (Int.castRingHom ℂ) Pf ^ 2 +
      C (288 : ℂ) * PowerSeries.map (Int.castRingHom ℂ) Phif) Q := by
    refine ((sumsTo_Pf.pow 2).add (sumsTo_Phif.cmul 288)).congr fun x hx ↦ ?_
    linear_combination (-1) * Q_sub_P_sq hx
  have h2 := sumsTo_Qf.unique h
  have e : PowerSeries.map (Int.castRingHom ℂ) (Pf ^ 2 + 288 * Phif) =
      PowerSeries.map (Int.castRingHom ℂ) Pf ^ 2 +
      C (288 : ℂ) * PowerSeries.map (Int.castRingHom ℂ) Phif := by
    rw [map_add, map_mul, map_pow, map_ofNat, map_ofNat C]
  have h3 : Qf = Pf ^ 2 + 288 * Phif := map_intCast_injective (by rw [e]; exact h2)
  linear_combination h3

/-- For `|x| < 1`: `1728 x ∏ (1 - xⁿ)²⁴ = Q(x)³ - R(x)²` (Ramanujan's form of `Δ = (E₄³ - E₆²)/1728`
with Jacobi's product `Δ = q ∏ (1 - qⁿ)²⁴`, both from Mathlib). -/
theorem delta_analytic {x : ℂ} (hx : ‖x‖ < 1) :
    1728 * x * (∏' n : ℕ, (1 - x ^ (n + 1))) ^ 24 = Q x ^ 3 - R x ^ 2 := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [Q_zero, R_zero]
  obtain ⟨τ, rfl⟩ := exists_tau hx hx0
  have h1 := ModularForm.discriminant_eq_q_prod τ
  have h2 := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hq : (Function.Periodic.qParam 1 (τ : ℂ)) = cexp (2 * π * I * τ) := by
    simp [Function.Periodic.qParam]
  have hm := (hasProd_eulerFunction hx).multipliable
  simp_rw [ModularForm.eta_q_eq_pow] at h1
  rw [hq, hm.tprod_pow 24] at h1
  rw [Q_exp, R_exp]
  linear_combination 1728 * h2 - 1728 * h1

/-- **Jacobi's product for `Δ`** as an identity in `ℤ⟦X⟧`: `1728 X ∏ (1 - Xⁿ)²⁴ = Q³ - R²`. -/
theorem delta_series_eq : 1728 * (X * eulerSeries ^ 24) = Qf ^ 3 - Rf ^ 2 := by
  have h : SumsTo (C (1728 : ℂ) * (X * PowerSeries.map (Int.castRingHom ℂ) eulerSeries ^ 24) +
      PowerSeries.map (Int.castRingHom ℂ) Rf ^ 2) (fun x ↦ Q x ^ 3) := by
    refine (((sumsTo_X.mul (sumsTo_euler.pow 24)).cmul 1728).add (sumsTo_Rf.pow 2)).congr
      fun x hx ↦ ?_
    linear_combination delta_analytic hx
  have h2 := (sumsTo_Qf.pow 3).unique h
  have e : PowerSeries.map (Int.castRingHom ℂ) (1728 * (X * eulerSeries ^ 24) + Rf ^ 2) =
      C (1728 : ℂ) * (X * PowerSeries.map (Int.castRingHom ℂ) eulerSeries ^ 24) +
      PowerSeries.map (Int.castRingHom ℂ) Rf ^ 2 := by
    rw [map_add, map_mul, map_mul, map_pow, map_pow, map_ofNat, map_ofNat C, map_X]
  have h3 : Qf ^ 3 = 1728 * (X * eulerSeries ^ 24) + Rf ^ 2 :=
    map_intCast_injective (by rw [e, map_pow]; exact h2)
  linear_combination -h3

/-! ### Reduction modulo `5` -/

local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

local notation "μ" => PowerSeries.map (Int.castRingHom (ZMod 5))

theorem map5_Qf : μ Qf = 1 := by
  ext n
  rw [coeff_map, coeff_one]
  simp only [Qf, affSeries, coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · have h240 : (240 : ZMod 5) = 0 := by decide
    simp [hn, h240]

theorem sigma_five_cast (n : ℕ) : ((σ 5 n : ℕ) : ZMod 5) = ((σ 1 n : ℕ) : ZMod 5) := by
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  push_cast
  rw [pow_one]
  exact ZMod.pow_card _

theorem map5_Rf : μ Rf = μ Pf := by
  ext n
  rw [coeff_map, coeff_map]
  simp only [Rf, Pf, affSeries, coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false, eq_intCast]
    push_cast
    rw [sigma_five_cast]
    have : (-504 : ZMod 5) = -24 := by decide
    rw [this]

/-- **Ramanujan No. 30, (2.3)–(2.4)**:
`x ∏ (1 - x^{25n}) / ∏ (1 - xⁿ) ≡ ∑_{n ≥ 1} n σ₁(n) xⁿ (mod 5)`; i.e. the coefficient of `xⁿ` in
`x ∏ (1 - x^{25n}) ∑ p(k) x^k` is `≡ n σ₁(n) (mod 5)`. -/
@[kb "ramanujan1927" "No. 30, § 2, (2.3)–(2.4), p. 234"]
theorem ramanujanTauModFive : RamanujanTauModFive := by
  have hQ := congrArg μ Qf_sub_Pf_sq
  have hD := congrArg μ delta_series_eq
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_X] at hQ hD
  rw [map5_Qf] at hQ hD
  rw [map5_Rf] at hD
  have h5 : (5 : (ZMod 5)⟦X⟧) = 0 := by
    have := charP_powerSeries_zmod 5
    exact CharP.cast_eq_zero ((ZMod 5)⟦X⟧) 5
  have key : X * μ eulerSeries ^ 24 = μ Phif := by
    linear_combination 2 * hD + 2 * hQ - (691 * (X * μ eulerSeries ^ 24) - 115 * μ Phif) * h5
  have hE := eulerSeries_pow_prime_pow 5 2
  have hPE : μ partitionSeries * μ eulerSeries = 1 := by
    rw [← map_mul, partitionSeries_mul_eulerSeries, map_one]
  have hfin : μ (X * eulerSeriesPow 25 * partitionSeries) = μ Phif := by
    have h25 : μ (eulerSeriesPow 25) = μ eulerSeries ^ 25 := by
      have := hE.symm
      norm_num at this
      exact this
    rw [map_mul, map_mul, map_X, h25, ← key]
    linear_combination (X * μ eulerSeries ^ 24) * hPE
  intro n
  have h := congrArg (coeff n) hfin
  simp only [coeff_map, Phif, coeff_mk] at h
  have := (ZMod.intCast_eq_intCast_iff _ _ 5).mp h
  simpa using this

end ModularFormsKB.Historical.Ramanujan
