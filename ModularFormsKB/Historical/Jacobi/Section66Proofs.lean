import ModularFormsKB.Historical.Jacobi.Section66
import ModularFormsKB.Citation
/-!
# *Fundamenta nova* § 66, 3) and 4): proofs

Proofs of `GaussThetaFourProduct` and `TriangularProduct` from `triple_product` (with `z = -1`, resp.
`q = p²`, `z = p`) and Euler's identity `∏ (1 + qⁿ) ∏ (1 - q^{2n-1}) = 1`.
-/

noncomputable section

open Complex

namespace ModularFormsKB.Historical.Jacobi

section Euler

variable {q : ℂ}

lemma mA (hq : ‖q‖ < 1) : Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) :=
  ModularForm.multipliable_one_sub_pow hq

lemma mE (hq : ‖q‖ < 1) : Multipliable fun n : ℕ ↦ 1 + q ^ (n + 1) :=
  (multipliable_one_add_mul_pow q q hq).congr fun n ↦ by ring

lemma mEv (hq : ‖q‖ < 1) : Multipliable fun n : ℕ ↦ 1 - q ^ (2 * n + 2) :=
  (ModularForm.multipliable_one_sub_pow (norm_sq_lt_one hq)).congr fun n ↦ by ring

lemma mO (hq : ‖q‖ < 1) : Multipliable fun n : ℕ ↦ 1 - q ^ (2 * n + 1) :=
  (multipliable_one_add_odd (-1) hq).congr fun n ↦ by ring

lemma ne_Ev (hq : ‖q‖ < 1) : (∏' n : ℕ, (1 - q ^ (2 * n + 2))) ≠ 0 := by
  have := eulerProd_ne_zero (norm_sq_lt_one hq)
  unfold eulerProd at this
  convert this using 1
  exact tprod_congr fun n ↦ by ring

lemma A_eq (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * ∏' n : ℕ, (1 - q ^ (2 * n + 2)) :=
  (tprod_even_mul_odd (f := fun n : ℕ ↦ 1 - q ^ (n + 1)) (mO hq) (mEv hq)).symm

lemma AE_eq (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 - q ^ (n + 1))) * ∏' n : ℕ, (1 + q ^ (n + 1)) =
      ∏' n : ℕ, (1 - q ^ (2 * n + 2)) := by
  rw [← (mA hq).tprod_mul (mE hq)]
  exact tprod_congr fun n ↦ by ring

/-- Euler's identity `∏ (1 + qⁿ) ∏ (1 - q^{2n-1}) = 1`. -/
lemma E_mul_O (hq : ‖q‖ < 1) :
    (∏' n : ℕ, (1 + q ^ (n + 1))) * ∏' n : ℕ, (1 - q ^ (2 * n + 1)) = 1 := by
  have h1 := A_eq hq
  have h2 := AE_eq hq
  have h3 := ne_Ev hq
  refine mul_left_cancel₀ h3 ?_
  rw [h1] at h2
  linear_combination h2

lemma ne_E (hq : ‖q‖ < 1) : (∏' n : ℕ, (1 + q ^ (n + 1))) ≠ 0 :=
  left_ne_zero_of_mul_eq_one (E_mul_O hq)

lemma ne_O (hq : ‖q‖ < 1) : (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ≠ 0 :=
  right_ne_zero_of_mul_eq_one (E_mul_O hq)

lemma neg_one_zpow_eq (n : ℤ) : (-1 : ℂ) ^ n = (-1) ^ n.natAbs := by
  rcases n with n | n
  · simp
  · rw [zpow_negSucc, Int.natAbs_negSucc]
    rcases neg_one_pow_eq_or ℂ (n + 1) with h | h <;> simp [h]

end Euler

lemma pow_sq_div (p : ℂ) (n : ℕ) : (p ^ 2) ^ (n * (n + 1) / 2) = p ^ (n ^ 2) * p ^ n := by
  rw [← pow_mul, ← pow_add]
  congr 1
  have := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  nlinarith [this]

/-- **Fundamenta nova § 66, 3)** (p. 185): for `‖q‖ < 1`,
`∏_{n ≥ 1} (1 - qⁿ)/(1 + qⁿ) = ∑_{n ∈ ℤ} (-1)ⁿ q^{n²}`. -/
@[kb "jacobi1829" "§ 66, 3), p. 185"]
theorem gaussThetaFourProduct : GaussThetaFourProduct := by
  intro q hq
  have h := triple_product hq (z := -1) (neg_ne_zero.mpr one_ne_zero)
  rw [(mA hq).tprod_div₀ (mE hq) (ne_E hq)]
  have hp : ∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1) * (-1)) *
      (1 + q ^ (2 * n + 1) / (-1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 2))) * (∏' n : ℕ, (1 - q ^ (2 * n + 1))) *
        ∏' n : ℕ, (1 - q ^ (2 * n + 1)) := by
    rw [← tprod_mul_three (mEv hq) (mO hq) (mO hq)]
    exact tprod_congr fun n ↦ by ring
  rw [hp] at h
  have hv : (∏' n : ℕ, (1 - q ^ (n + 1))) / ∏' n : ℕ, (1 + q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 2))) * (∏' n : ℕ, (1 - q ^ (2 * n + 1))) *
        ∏' n : ℕ, (1 - q ^ (2 * n + 1)) := by
    rw [div_eq_iff (ne_E hq)]
    linear_combination A_eq hq - (∏' n : ℕ, (1 - q ^ (2 * n + 2))) *
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) * E_mul_O hq
  rw [hv]
  convert h using 2 with n
  rw [neg_one_zpow_eq]; ring

/-- **Fundamenta nova § 66, 4)** (p. 185): for `‖q‖ < 1`,
`∏_{n ≥ 1} (1 - q^{2n})/(1 - q^{2n-1}) = ∑_{n ≥ 0} q^{n(n+1)/2}`. -/
@[kb "jacobi1829" "§ 66, 4), p. 185"]
theorem triangularProduct : TriangularProduct := by
  intro q hq
  by_cases hq0 : q = 0
  · subst hq0
    have h1 : ∏' n : ℕ, (1 - (0 : ℂ) ^ (2 * n + 2)) / (1 - (0 : ℂ) ^ (2 * n + 1)) = 1 := by
      simp
    rw [h1]
    have := hasSum_single (f := fun n : ℕ ↦ (0 : ℂ) ^ (n * (n + 1) / 2)) 0
      (fun b hb ↦ by
        have : b * (b + 1) / 2 ≠ 0 := by
          rcases b with _ | b
          · exact absurd rfl hb
          · rcases b with _ | b
            · simp
            · have : 2 ≤ (b + 1 + 1) * (b + 1 + 1 + 1) / 2 := by
                apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
                nlinarith
              omega
        simp [this])
    simpa using this
  · obtain ⟨p, rfl⟩ := IsAlgClosed.exists_pow_nat_eq q (by norm_num : 0 < 2)
    have hpn : ‖p‖ < 1 := by
      by_contra hc
      rw [not_lt] at hc
      rw [norm_pow] at hq
      nlinarith
    have hp0 : p ≠ 0 := fun h ↦ hq0 (by simp [h])
    have hq' : ‖p ^ 2‖ < 1 := hq
    have h := triple_product hpn (z := p) hp0
    set Q := p ^ 2 with hQ
    have hE0 : Multipliable fun n : ℕ ↦ 1 + Q ^ n :=
      (multipliable_one_add_mul_pow 1 Q hq').congr fun n ↦ by ring
    have hE0v : ∏' n : ℕ, (1 + Q ^ n) = 2 * ∏' n : ℕ, (1 + Q ^ (n + 1)) := by
      rw [tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 + Q ^ n) (mE hq')]
      norm_num
    have hprod : ∏' n : ℕ, (1 - p ^ (2 * n + 2)) * (1 + p ^ (2 * n + 1) * p) *
        (1 + p ^ (2 * n + 1) / p) =
        2 * ((∏' n : ℕ, (1 - Q ^ (2 * n + 2))) * ∏' n : ℕ, (1 + Q ^ (n + 1))) := by
      have : ∀ n : ℕ, (1 - p ^ (2 * n + 2)) * (1 + p ^ (2 * n + 1) * p) *
          (1 + p ^ (2 * n + 1) / p) =
          (1 - Q ^ (n + 1)) * (1 + Q ^ (n + 1)) * (1 + Q ^ n) := by
        intro n
        rw [hQ]
        field_simp
        ring
      simp_rw [this]
      rw [tprod_mul_three (mA hq') (mE hq') hE0, hE0v, ← AE_eq hq']
      ring
    rw [hprod] at h
    have hsum : Summable fun n : ℕ ↦ (p ^ 2) ^ (n * (n + 1) / 2) := by
      have := h.summable.comp_injective (i := fun n : ℕ ↦ (n : ℤ)) Nat.cast_injective
      refine this.congr fun n ↦ ?_
      simp only [Function.comp, Int.natAbs_natCast, zpow_natCast]
      rw [pow_sq_div]
    have hpair := tsum_int_pair h.summable
    have hterm : ∀ n : ℕ, (p ^ ((n : ℤ).natAbs ^ 2) * p ^ (n : ℤ) +
        p ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * p ^ (-((n : ℤ) + 1))) =
        2 * (p ^ 2) ^ (n * (n + 1) / 2) := by
      intro n
      rw [pair_term, pow_sq_div]
      have : p ^ ((n + 1) ^ 2) * (p ^ (n + 1))⁻¹ = p ^ (n ^ 2) * p ^ n := by
        have : p ^ ((n + 1) ^ 2) = p ^ (n ^ 2) * p ^ n * p ^ (n + 1) := by
          rw [← pow_add, ← pow_add]; congr 1; ring
        rw [this]; field_simp
      rw [this]; ring
    simp_rw [hterm] at hpair
    rw [tsum_mul_left, h.tsum_eq] at hpair
    have hv : ∏' n : ℕ, (1 - (p ^ 2) ^ (2 * n + 2)) / (1 - (p ^ 2) ^ (2 * n + 1)) =
        (∏' n : ℕ, (1 - Q ^ (2 * n + 2))) * ∏' n : ℕ, (1 + Q ^ (n + 1)) := by
      rw [(mEv hq').tprod_div₀ (mO hq') (ne_O hq')]
      have := E_mul_O hq'
      rw [div_eq_iff (ne_O hq')]
      linear_combination (-(∏' n : ℕ, (1 - Q ^ (2 * n + 2)))) * this
    rw [hv]
    have : ∑' n : ℕ, (p ^ 2) ^ (n * (n + 1) / 2) =
        (∏' n : ℕ, (1 - Q ^ (2 * n + 2))) * ∏' n : ℕ, (1 + Q ^ (n + 1)) :=
      mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) hpair.symm
    rw [← this]
    exact hsum.hasSum

end ModularFormsKB.Historical.Jacobi
