import ModularFormsKB.Historical.Ramanujan.Equations
import ModularFormsKB.Citation
/-!
# Ramanujan's products of Eisenstein series

Ramanujan, *Collected Papers*, No. 30, § 1, (1.61)–(1.63), p. 233, with `Q = 1 + 240 ∑ σ₃(n) xⁿ` and
`R = 1 - 504 ∑ σ₅(n) xⁿ`:

* `Q² = 1 + 480 ∑ σ₇(n) xⁿ` (`ramanujan_Q_sq`, wrapper of `Ramanujan.Q_sq`);
* `Q R = 1 - 264 ∑ σ₉(n) xⁿ` (`QRIdentity`);
* `441 Q³ + 250 R² = 691 + 65520 ∑ σ₁₁(n) xⁿ` (`WeightTwelveIdentity`).

In modern terms: `E₄² = E₈`, `E₄ E₆ = E₁₀`, and `441 E₄³ + 250 E₆² = 691 E₁₂` (the source of
`τ(n) ≡ σ₁₁(n) mod 691`). The proofs use Mathlib's dimension formula for level-one modular forms and the
`q`-expansions of the Eisenstein series `E_k` (`EisensteinSeries.q_expansion_bernoulli`).
-/

noncomputable section

open Complex
open scoped ArithmeticFunction.sigma

namespace ModularFormsKB.Historical.Ramanujan

/-- **Ramanujan, No. 30, (1.61)** (p. 233, first identity):
`Q² = 1 + 480 ∑ σ₇(n) xⁿ` for `‖x‖ < 1`. Wrapper of `Ramanujan.Q_sq`. -/
@[kb "ramanujan1927" "No. 30, § 1, (1.61), p. 233"]
theorem ramanujan_Q_sq {x : ℂ} (hx : ‖x‖ < 1) :
    Q x ^ 2 = 1 + 480 * ∑' n : ℕ+, (σ 7 n : ℂ) * x ^ (n : ℕ) :=
  Q_sq hx

/-- **Ramanujan, No. 30, (1.62)** (p. 233, second identity):
`Q R = 1 - 264 ∑ σ₉(n) xⁿ` for `‖x‖ < 1` (`E₄ E₆ = E₁₀`). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.62), p. 233"]
def QRIdentity : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 → Q x * R x = 1 - 264 * ∑' n : ℕ+, (σ 9 n : ℂ) * x ^ (n : ℕ)

/-- **Ramanujan, No. 30, (1.63)** (p. 233, third identity):
`441 Q³ + 250 R² = 691 + 65520 ∑ σ₁₁(n) xⁿ` for `‖x‖ < 1` (`441 E₄³ + 250 E₆² = 691 E₁₂`). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.63), p. 233"]
def WeightTwelveIdentity : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 →
    441 * Q x ^ 3 + 250 * R x ^ 2 = 691 + 65520 * ∑' n : ℕ+, (σ 11 n : ℂ) * x ^ (n : ℕ)

open UpperHalfPlane hiding I
open scoped MatrixGroups

/-- `E₄ E₆ = E₁₀`, by the Sturm bound (weight `10 < 12`, constant term `0`). -/
lemma E4_mul_E6_eq_E10 (z : ℍ) :
    ModularForm.E₄ z * ModularForm.E₆ z = ModularForm.E (k := 10) (by norm_num) z := by
  let f : ModularForm 𝒮ℒ 10 :=
    ModularForm.mcast (by norm_num) (ModularForm.E₄.mul ModularForm.E₆) -
      ModularForm.E (k := 10) (by norm_num)
  have h0 : f = 0 := by
    refine ModularForm.sturm_bound_levelOne_nat (k := 10) (f := f) ?_
    refine lt_of_lt_of_le (by norm_num) (PowerSeries.nat_le_order _ 1 ?_)
    intro i hi
    obtain rfl : i = 0 := by omega
    simp [f, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨5, rfl⟩]
  have := congrFun (congrArg DFunLike.coe h0) z
  simp [f] at this
  have hm : (ModularForm.E₄.mul ModularForm.E₆) z = ModularForm.E₄ z * ModularForm.E₆ z := rfl
  rw [hm] at this
  linear_combination this

/-- `441 E₄³ + 250 E₆² = 691 E₁₂`, by the Sturm bound (weight `12`, `q`-coefficients `0` and `1` agree). -/
lemma weight_twelve_eq (z : ℍ) :
    441 * ModularForm.E₄ z ^ 3 + 250 * ModularForm.E₆ z ^ 2 =
      691 * ModularForm.E (k := 12) (by norm_num) z := by
  let f : ModularForm 𝒮ℒ 12 :=
    (441 : ℂ) • ModularForm.mcast (by norm_num) (ModularForm.E₄.pow 3) +
      (250 : ℂ) • ModularForm.mcast (by norm_num) (ModularForm.E₆.pow 2) -
      (691 : ℂ) • ModularForm.E (k := 12) (by norm_num)
  have hq : qExpansion 1 f = (441 : ℂ) • (qExpansion 1 ModularForm.E₄) ^ 3 +
      (250 : ℂ) • (qExpansion 1 ModularForm.E₆) ^ 2 -
      (691 : ℂ) • qExpansion 1 (ModularForm.E (k := 12) (by norm_num)) := by
    have eS : ∀ A B : ModularForm 𝒮ℒ 12,
        qExpansion 1 ⇑(A - B) = qExpansion 1 ⇑A - qExpansion 1 ⇑B := fun A B => by
      rw [FunLike.coe_sub]
      exact ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL A B
    have eA : ∀ A B : ModularForm 𝒮ℒ 12,
        qExpansion 1 ⇑(A + B) = qExpansion 1 ⇑A + qExpansion 1 ⇑B := fun A B => by
      rw [FunLike.coe_add]
      exact ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL A B
    have eM : ∀ (c : ℂ) (A : ModularForm 𝒮ℒ 12),
        qExpansion 1 ⇑(c • A) = c • qExpansion 1 ⇑A := fun c A => by
      rw [FunLike.coe_smul]
      exact ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c A
    simp only [f]
    rw [eS, eA, eM, eM, eM,
      ModularForm.qExpansion_mcast, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hc0 : (qExpansion 1 f).coeff 0 = 0 := by
    rw [hq]
    simp [pow_succ, PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨6, rfl⟩]
    norm_num
  have hc1 : (qExpansion 1 f).coeff 1 = 0 := by
    rw [hq]
    have h12 : (qExpansion 1 (ModularForm.E (k := 12) (by norm_num))).coeff 1 = 65520 / 691 := by
      rw [EisensteinSeries.E_qExpansion_coeff _ ⟨6, rfl⟩,
        show bernoulli 12 = -691 / 2730 by decide +kernel]
      norm_num
    simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
      -PowerSeries.coeff_zero_eq_constantCoeff, h12,
      ModularForm.E₄_qExpansion_coeff_one, ModularForm.E₆_qExpansion_coeff_one,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
      EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
    norm_num
  have h0 : f = 0 := by
    refine ModularForm.sturm_bound_levelOne_nat (k := 12) (f := f) ?_
    refine lt_of_lt_of_le (by norm_num) (PowerSeries.nat_le_order _ 2 ?_)
    intro i hi
    interval_cases i
    · exact hc0
    · exact hc1
  have := congrFun (congrArg DFunLike.coe h0) z
  simp [f] at this
  have h3 : (ModularForm.E₄.pow 3) z = ModularForm.E₄ z ^ 3 := congrFun (ModularForm.coe_pow _ 3) z
  have h2 : (ModularForm.E₆.pow 2) z = ModularForm.E₆ z ^ 2 := congrFun (ModularForm.coe_pow _ 2) z
  rw [h3, h2] at this
  linear_combination this

/-- **Ramanujan, No. 30, (1.62)**: `Q R = 1 - 264 ∑ σ₉(n) xⁿ`, i.e. `E₄ E₆ = E₁₀`
(Sturm bound in weight `10`, then `EisensteinSeries.q_expansion_bernoulli` with `B₁₀ = 5/66`). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.62), p. 233"]
theorem qRIdentity : QRIdentity := by
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0; simp [Q_zero, R_zero]
  obtain ⟨τ, rfl⟩ := exists_tau hx hx0
  have h10 := EisensteinSeries.q_expansion_bernoulli (k := 10) (by norm_num) (by decide) τ
  simp_rw [zpow_natCast] at h10
  have hb : bernoulli 10 = 5 / 66 := by decide +kernel
  rw [Q_exp, R_exp, E4_mul_E6_eq_E10]
  show ModularForm.E _ τ = _
  rw [h10, hb]
  norm_num

/-- **Ramanujan, No. 30, (1.63)**: `441 Q³ + 250 R² = 691 + 65520 ∑ σ₁₁(n) xⁿ`,
i.e. `441 E₄³ + 250 E₆² = 691 E₁₂` (Sturm bound in weight `12`, then `q_expansion_bernoulli` with
`B₁₂ = -691/2730`). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.63), p. 233"]
theorem weightTwelveIdentity : WeightTwelveIdentity := by
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0; simp [Q_zero, R_zero]; norm_num
  obtain ⟨τ, rfl⟩ := exists_tau hx hx0
  have h12 := EisensteinSeries.q_expansion_bernoulli (k := 12) (by norm_num) (by decide) τ
  simp_rw [zpow_natCast] at h12
  have hb : bernoulli 12 = -691 / 2730 := by decide +kernel
  rw [Q_exp, R_exp, weight_twelve_eq]
  show 691 * ModularForm.E _ τ = _
  rw [h12, hb]
  norm_num
  ring

end ModularFormsKB.Historical.Ramanujan
