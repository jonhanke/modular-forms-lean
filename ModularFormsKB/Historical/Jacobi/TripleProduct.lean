import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Normed.Group.Tannery
import ModularFormsKB.Citation
/-!
# Jacobi's triple product identity

Jacobi, *Fundamenta nova theoriae functionum ellipticarum* (1829), § 64, pp. 180–183: for `|q| < 1` and `z ≠ 0`,

  `(1 - q²)(1 - q⁴)(1 - q⁶)⋯ · (1 + qz)(1 + q³z)(1 + q⁵z)⋯ · (1 + q/z)(1 + q³/z)(1 + q⁵/z)⋯ = ∑_{n ∈ ℤ} q^{n²} zⁿ`

(`triple_product`), with its cosine form (`z = -e^{2ix}`, p. 182)

  `∏_{n ≥ 1} (1 - q^{2n})(1 - 2q^{2n-1} cos 2x + q^{4n-2}) = 1 - 2q cos 2x + 2q⁴ cos 4x - 2q⁹ cos 6x + ⋯`

(`triple_product_cos`) and the sine analogue (`z = -qe^{2ix}`, p. 183)

  `∏ (1 - q^{2n}) · 2 sin x · ∏ (1 - 2q^{2n} cos 2x + q^{4n}) = 2 ∑_{n ≥ 0} (-1)ⁿ q^{n(n+1)} sin (2n+1)x`

(`triple_product_sin`). In Mathlib's notation (`q = e^{πiτ}`, `z = e^{2πiw}`) the identity reads
`jacobiTheta₂ w τ = ∏ (1 - q^{2n})(1 + q^{2n-1} z)(1 + q^{2n-1}/z)` (`jacobiTheta₂_eq_tprod`); this is the
named input `JacobiTripleProduct` of Weber's theta–eta formulas (`Historical.Weber`), now proved.

## Proof

Not Jacobi's (his § 64 proof multiplies two Euler-type expansions, his "lemmas"), but the finite form via
Gaussian binomial coefficients `[m, j]` in `Q = q²` (Cauchy's `q`-binomial theorem):

  `∏_{k < n} (1 + z q^{2k+1})(1 + z⁻¹ q^{2k+1}) = ∑_{j = -n}^{n} [2n, n + j] q^{j²} z^j`,

followed by `n → ∞` term by term (Tannery's theorem, `tendsto_tsum_of_dominated_convergence`): each
`[2n, n + j] → 1/∏(1 - q^{2k})`, and `|[2n, n + j]| ≤ ∏(1 + |q|^{2k}) / ∏(1 - |q|^{2k})²`.

Neither Mathlib nor Tau Ceti has the identity (searched 2026-11-14: Mathlib has `jacobiTheta₂` as a series and
Euler's pentagonal theorem `eulerFunction_eq_tprod`; Tau Ceti has the product `qTheta` and the Tate-curve
series `tateTheta`, not their equality).
-/

noncomputable section

open Complex Filter Finset
open scoped Real Topology

namespace ModularFormsKB.Historical.Jacobi

/-! ### Gaussian binomial coefficients -/

/-- The `q`-Pochhammer symbol `(Q; Q)ₙ = ∏_{i < n} (1 - Q^{i+1})`. -/
def qPoch (Q : ℂ) (n : ℕ) : ℂ := ∏ i ∈ range n, (1 - Q ^ (i + 1))

/-- The Gaussian binomial coefficient `[m, j]_Q = (Q; Q)_m / ((Q; Q)_j (Q; Q)_{m-j})` for `j ≤ m`, and `0`
for `j > m`. -/
def gaussBinom (Q : ℂ) (m j : ℕ) : ℂ :=
  if j ≤ m then qPoch Q m / (qPoch Q j * qPoch Q (m - j)) else 0

/-! ### Algebra of the Gaussian binomials -/

section Algebra

lemma qPoch_succ (Q : ℂ) (n : ℕ) : qPoch Q (n + 1) = qPoch Q n * (1 - Q ^ (n + 1)) :=
  prod_range_succ _ _

@[simp] lemma qPoch_zero (Q : ℂ) : qPoch Q 0 = 1 := by simp [qPoch]

lemma qPoch_ne_zero {Q : ℂ} (hQ : ‖Q‖ < 1) (n : ℕ) : qPoch Q n ≠ 0 := by
  refine prod_ne_zero_iff.mpr fun i _ h ↦ ?_
  have h1 : Q ^ (i + 1) = 1 := by linear_combination -h
  have h2 : ‖Q‖ ^ (i + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hQ (Nat.succ_ne_zero i)
  rw [← norm_pow, h1, norm_one] at h2
  exact lt_irrefl _ h2

lemma gaussBinom_zero_right {Q : ℂ} (hQ : ‖Q‖ < 1) (m : ℕ) : gaussBinom Q m 0 = 1 := by
  have := qPoch_ne_zero hQ m
  simp [gaussBinom, this]

lemma gaussBinom_self {Q : ℂ} (hQ : ‖Q‖ < 1) (m : ℕ) : gaussBinom Q m m = 1 := by
  have := qPoch_ne_zero hQ m
  simp [gaussBinom, this]

lemma gaussBinom_of_lt {Q : ℂ} {m j : ℕ} (h : m < j) : gaussBinom Q m j = 0 := by
  simp [gaussBinom, not_le.mpr h]

/-- The `q`-Pascal rule. -/
lemma gaussBinom_pascal {Q : ℂ} (hQ : ‖Q‖ < 1) {m j : ℕ} (hj : j ≤ m) :
    gaussBinom Q (m + 1) (j + 1) = gaussBinom Q m (j + 1) + Q ^ (m - j) * gaussBinom Q m j := by
  rcases hj.eq_or_lt with rfl | hlt
  · rw [gaussBinom_self hQ, gaussBinom_of_lt (Nat.lt_succ_self _), gaussBinom_self hQ]; simp
  · obtain ⟨d, rfl⟩ : ∃ d, m = j + d + 1 := ⟨m - j - 1, by omega⟩
    have e1 : j + d + 1 + 1 - (j + 1) = d + 1 := by omega
    have e2 : j + d + 1 - (j + 1) = d := by omega
    have e3 : j + d + 1 - j = d + 1 := by omega
    unfold gaussBinom
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), e1, e2, e3,
      qPoch_succ Q (j + d + 1), qPoch_succ Q j, qPoch_succ Q d]
    have h1 := qPoch_ne_zero hQ j
    have h2 := qPoch_ne_zero hQ d
    have h3 := qPoch_ne_zero hQ (j + d + 1)
    have n : ∀ i, 1 - Q ^ (i + 1) ≠ 0 := fun i h ↦ by
      have := qPoch_ne_zero hQ (i + 1)
      rw [qPoch_succ] at this
      exact this (by rw [h, mul_zero])
    have h4 := n j
    have h5 := n d
    field_simp
    ring

lemma choose_two_succ (j : ℕ) : (j + 1).choose 2 = j.choose 2 + j := by
  have := Nat.choose_succ_succ j 1
  rw [Nat.choose_one_right] at this
  rw [show (2 : ℕ) = 1 + 1 from rfl, this]; ring

/-- Cauchy's `q`-binomial theorem, finite form. -/
theorem q_binomial {Q : ℂ} (hQ : ‖Q‖ < 1) (y : ℂ) (m : ℕ) :
    ∏ k ∈ range m, (1 + y * Q ^ k) =
      ∑ j ∈ range (m + 1), gaussBinom Q m j * Q ^ (j.choose 2) * y ^ j := by
  induction m with
  | zero => simp [gaussBinom_self hQ]
  | succ m ih =>
    rw [prod_range_succ, ih]
    set t : ℕ → ℂ := fun j ↦ gaussBinom Q m j * Q ^ (j.choose 2) * y ^ j with ht
    rw [sum_range_succ' _ (m + 1)]
    have key : ∀ j ∈ range (m + 1), gaussBinom Q (m + 1) (j + 1) * Q ^ ((j + 1).choose 2) *
        y ^ (j + 1) = t (j + 1) + y * Q ^ m * t j := by
      intro j hj
      have hj' : j ≤ m := by simpa [Nat.lt_succ_iff] using hj
      rw [gaussBinom_pascal hQ hj']
      simp only [ht]
      have : Q ^ (m - j) * Q ^ (j.choose 2 + j) = Q ^ m * Q ^ (j.choose 2) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [choose_two_succ, pow_succ y j]
      linear_combination (gaussBinom Q m j * y ^ j * y) * this
    rw [sum_congr rfl key, sum_add_distrib, ← mul_sum]
    have h1 := sum_range_succ' t (m + 1)
    have h2 := sum_range_succ t (m + 1)
    have h3 : t (m + 1) = 0 := by simp [ht, gaussBinom_of_lt (Nat.lt_succ_self m)]
    have h4 : t 0 = 1 := by simp [ht, gaussBinom_zero_right hQ]
    have h5 : gaussBinom Q (m + 1) 0 * Q ^ (Nat.choose 0 2) * y ^ 0 = 1 := by
      simp [gaussBinom_zero_right hQ]
    rw [h5]
    rw [h3, add_zero] at h2
    rw [h4] at h1
    linear_combination (h2.symm.trans h1)

lemma two_mul_choose (j : ℕ) : (2 * (j.choose 2) : ℤ) = j * (j - 1) := by
  induction j with
  | zero => simp
  | succ j ih => rw [choose_two_succ]; push_cast; linear_combination ih

end Algebra

/-! ### The finite triple product -/

section Finite

variable {q x : ℂ}

/-- The `q`-binomial product with `y = x q^{1-2n}`, split symmetrically. -/
lemma finite_prod_aux (hq0 : q ≠ 0) (hx : x ≠ 0) (n : ℕ) :
    ∏ k ∈ range n, ((1 + x * q ^ (2 * k + 1)) * (1 + x⁻¹ * q ^ (2 * k + 1))) =
      x ^ (-(n : ℤ)) * q ^ ((n : ℤ) ^ 2) *
        ∏ k ∈ range (2 * n), (1 + x * q ^ ((2 * (k : ℤ) + 1) - 2 * n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hR : ∏ k ∈ range (2 * (n + 1)), (1 + x * q ^ ((2 * (k : ℤ) + 1) - 2 * ((n + 1 : ℕ) : ℤ))) =
        (1 + x * q ^ (-(2 * (n : ℤ) + 1))) *
          (∏ k ∈ range (2 * n), (1 + x * q ^ ((2 * (k : ℤ) + 1) - 2 * n))) *
          (1 + x * q ^ (2 * (n : ℤ) + 1)) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, prod_range_succ, prod_range_succ']
      have : ∏ k ∈ range (2 * n), (1 + x * q ^ ((2 * ((k + 1 : ℕ) : ℤ) + 1) - 2 * ((n + 1 : ℕ) : ℤ))) =
          ∏ k ∈ range (2 * n), (1 + x * q ^ ((2 * (k : ℤ) + 1) - 2 * n)) :=
        prod_congr rfl fun k _ ↦ by congr 3; push_cast; ring
      rw [this, show ((2 * ((0 : ℕ) : ℤ) + 1) - 2 * ((n + 1 : ℕ) : ℤ)) = -(2 * (n : ℤ) + 1) by
        push_cast; ring, show ((2 * ((2 * n + 1 : ℕ) : ℤ) + 1) - 2 * ((n + 1 : ℕ) : ℤ)) =
        2 * (n : ℤ) + 1 by push_cast; ring]
      ring
    rw [prod_range_succ, ih, hR]
    have e1 : q ^ (((n + 1 : ℕ) : ℤ) ^ 2) = q ^ ((n : ℤ) ^ 2) * q ^ (2 * n + 1) := by
      rw [← zpow_natCast q (2 * n + 1), ← zpow_add₀ hq0]; congr 1; push_cast; ring
    have e2 : x ^ (-((n + 1 : ℕ) : ℤ)) = x ^ (-(n : ℤ)) * x⁻¹ := by
      rw [← zpow_neg_one, ← zpow_add₀ hx]; congr 1; push_cast; ring
    have e3 : q ^ (-(2 * (n : ℤ) + 1)) = (q ^ (2 * n + 1))⁻¹ := by
      rw [zpow_neg, ← zpow_natCast]; push_cast; rfl
    have e4 : q ^ (2 * (n : ℤ) + 1) = q ^ (2 * n + 1) := by
      rw [← zpow_natCast]; push_cast; rfl
    rw [e1, e2, e3, e4]
    have : q ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hq0
    field_simp
    ring

lemma term_eq (hq0 : q ≠ 0) (hx : x ≠ 0) (n j : ℕ) :
    (q ^ 2) ^ (j.choose 2) * (x * q ^ ((1 : ℤ) - 2 * n)) ^ j * (x ^ (-(n : ℤ)) * q ^ ((n : ℤ) ^ 2)) =
      q ^ (((j : ℤ) - n) ^ 2) * x ^ ((j : ℤ) - n) := by
  have e1 : (q ^ 2) ^ (j.choose 2) = q ^ ((2 * j.choose 2 : ℕ) : ℤ) := by
    rw [← pow_mul, ← zpow_natCast]
  have e2 : (x * q ^ ((1 : ℤ) - 2 * n)) ^ j = x ^ (j : ℤ) * q ^(((1 : ℤ) - 2 * n) * j) := by
    rw [mul_pow, ← zpow_natCast (q ^ ((1 : ℤ) - 2 * n)) j, ← zpow_mul, zpow_natCast]
  rw [e1, e2]
  calc _ = (q ^ ((2 * j.choose 2 : ℕ) : ℤ) * q ^ (((1 : ℤ) - 2 * n) * j) * q ^ ((n : ℤ) ^ 2)) *
        (x ^ (j : ℤ) * x ^ (-(n : ℤ))) := by ring
    _ = q ^ (((2 * j.choose 2 : ℕ) : ℤ) + ((1 : ℤ) - 2 * n) * j + (n : ℤ) ^ 2) *
        x ^ ((j : ℤ) + -(n : ℤ)) := by
      rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, ← zpow_add₀ hx]
    _ = _ := by
      have := two_mul_choose j
      rw [show (((2 * j.choose 2 : ℕ) : ℤ) + ((1 : ℤ) - 2 * n) * j + (n : ℤ) ^ 2) =
        ((j : ℤ) - n) ^ 2 by push_cast; linear_combination this,
        show (j : ℤ) + -(n : ℤ) = (j : ℤ) - n by ring]

/-- **The finite triple product**: with `Q = q²`,
`∏_{k<n} (1 + x q^{2k+1})(1 + x⁻¹ q^{2k+1}) = ∑_{j ≤ 2n} [2n, j]_Q q^{(j-n)²} x^{j-n}`. -/
theorem finite_triple (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hx : x ≠ 0) (n : ℕ) :
    ∏ k ∈ range n, ((1 + x * q ^ (2 * k + 1)) * (1 + x⁻¹ * q ^ (2 * k + 1))) =
      ∑ j ∈ range (2 * n + 1),
        gaussBinom (q ^ 2) (2 * n) j * (q ^ (((j : ℤ) - n) ^ 2) * x ^ ((j : ℤ) - n)) := by
  have hQ : ‖q ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg q]
  rw [finite_prod_aux hq0 hx n]
  have h := q_binomial hQ (x * q ^ ((1 : ℤ) - 2 * n)) (2 * n)
  have h2 : ∏ k ∈ range (2 * n), (1 + x * q ^ ((2 * (k : ℤ) + 1) - 2 * n)) =
      ∏ k ∈ range (2 * n), (1 + x * q ^ ((1 : ℤ) - 2 * n) * (q ^ 2) ^ k) := by
    refine prod_congr rfl fun k _ ↦ ?_
    have e : (q ^ 2) ^ k = q ^ ((2 * k : ℕ) : ℤ) := by rw [← pow_mul, ← zpow_natCast]
    rw [mul_assoc, e, ← zpow_add₀ hq0]
    congr 3; push_cast; ring
  rw [h2, h, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← term_eq hq0 hx n j]
  ring

end Finite

/-! ### Bounds and limits of the Gaussian binomials -/

section Bounds

lemma sum_pow_succ_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (m : ℕ) :
    ∑ i ∈ range m, r ^ (i + 1) ≤ r / (1 - r) := by
  have hs : HasSum (fun i : ℕ ↦ r ^ (i + 1)) (r / (1 - r)) := by
    have := (hasSum_geometric_of_lt_one h0 h1).mul_left r
    convert this using 1
    · funext i; ring
    · rw [div_eq_mul_inv]
  exact sum_le_hasSum _ (fun i _ ↦ by positivity) hs

lemma exp_neg_le_one_sub {a r : ℝ} (h0 : 0 ≤ a) (har : a ≤ r) (hr : r < 1) :
    Real.exp (-(a / (1 - r))) ≤ 1 - a := by
  have hpos : 0 < 1 - a := by linarith
  have hr' : 0 < 1 - r := by linarith
  have h1 : Real.exp (-(a / (1 - r))) ≤ Real.exp (-(a / (1 - a))) :=
    Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_left h0 hr' (by linarith)))
  have h2 : Real.exp (-(a / (1 - a))) ≤ 1 - a := by
    have h := Real.add_one_le_exp (a / (1 - a))
    have e : a / (1 - a) + 1 = (1 - a)⁻¹ := by field_simp; ring
    rw [e] at h
    rw [Real.exp_neg]
    calc (Real.exp (a / (1 - a)))⁻¹ ≤ ((1 - a)⁻¹)⁻¹ := inv_anti₀ (by positivity) h
      _ = 1 - a := inv_inv _
  exact h1.trans h2

variable {Q : ℂ}

lemma norm_qPoch_le (hQ : ‖Q‖ < 1) (m : ℕ) :
    ‖qPoch Q m‖ ≤ Real.exp (‖Q‖ / (1 - ‖Q‖)) := by
  unfold qPoch
  rw [norm_prod]
  calc ∏ i ∈ range m, ‖1 - Q ^ (i + 1)‖ ≤ ∏ i ∈ range m, Real.exp (‖Q‖ ^ (i + 1)) := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
        have := norm_sub_le (1 : ℂ) (Q ^ (i + 1))
        rw [norm_one, norm_pow] at this
        linarith [Real.add_one_le_exp (‖Q‖ ^ (i + 1))]
    _ = Real.exp (∑ i ∈ range m, ‖Q‖ ^ (i + 1)) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (sum_pow_succ_le (norm_nonneg _) hQ m)

lemma norm_qPoch_ge (hQ : ‖Q‖ < 1) (m : ℕ) :
    Real.exp (-(‖Q‖ / (1 - ‖Q‖) / (1 - ‖Q‖))) ≤ ‖qPoch Q m‖ := by
  unfold qPoch
  rw [norm_prod]
  have hr' : 0 < 1 - ‖Q‖ := by linarith
  calc Real.exp (-(‖Q‖ / (1 - ‖Q‖) / (1 - ‖Q‖))) ≤
        Real.exp (∑ i ∈ range m, -(‖Q‖ ^ (i + 1) / (1 - ‖Q‖))) := by
        refine Real.exp_le_exp.mpr ?_
        rw [sum_neg_distrib, neg_le_neg_iff, ← sum_div]
        exact div_le_div_of_nonneg_right (sum_pow_succ_le (norm_nonneg _) hQ m) hr'.le
    _ = ∏ i ∈ range m, Real.exp (-(‖Q‖ ^ (i + 1) / (1 - ‖Q‖))) := Real.exp_sum _ _
    _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) fun i _ ↦ ?_
        have hle : ‖Q‖ ^ (i + 1) ≤ ‖Q‖ :=
          pow_le_of_le_one (norm_nonneg _) hQ.le (Nat.succ_ne_zero i)
        have h1 := exp_neg_le_one_sub (pow_nonneg (norm_nonneg Q) (i + 1)) hle hQ
        have h2 := abs_norm_sub_norm_le (1 : ℂ) (Q ^ (i + 1))
        rw [norm_one, norm_pow] at h2
        linarith [le_abs_self (1 - ‖Q‖ ^ (i + 1))]

/-- A uniform bound for the Gaussian binomial coefficients. -/
lemma norm_gaussBinom_le (hQ : ‖Q‖ < 1) (m j : ℕ) :
    ‖gaussBinom Q m j‖ ≤ Real.exp (‖Q‖ / (1 - ‖Q‖)) /
      (Real.exp (-(‖Q‖ / (1 - ‖Q‖) / (1 - ‖Q‖))) * Real.exp (-(‖Q‖ / (1 - ‖Q‖) / (1 - ‖Q‖)))) := by
  unfold gaussBinom
  split_ifs
  · rw [norm_div, norm_mul]
    exact div_le_div₀ (Real.exp_pos _).le (norm_qPoch_le hQ m) (by positivity)
      (mul_le_mul (norm_qPoch_ge hQ _) (norm_qPoch_ge hQ _) (Real.exp_pos _).le (norm_nonneg _))
  · simp only [norm_zero]; positivity

/-- `E = ∏ (1 - Q^{i+1})`. -/
def eulerProd (Q : ℂ) : ℂ := ∏' i : ℕ, (1 - Q ^ (i + 1))

lemma tendsto_qPoch (hQ : ‖Q‖ < 1) : Tendsto (qPoch Q) atTop (𝓝 (eulerProd Q)) :=
  (ModularForm.multipliable_one_sub_pow hQ).hasProd.tendsto_prod_nat

lemma eulerProd_ne_zero (hQ : ‖Q‖ < 1) : eulerProd Q ≠ 0 := by
  intro h
  have := ge_of_tendsto' (tendsto_qPoch hQ).norm fun m ↦ norm_qPoch_ge hQ m
  rw [h, norm_zero] at this
  exact absurd this (not_le.mpr (Real.exp_pos _))

lemma tendsto_gaussBinom (hQ : ‖Q‖ < 1) (k : ℤ) :
    Tendsto (fun n : ℕ ↦ gaussBinom Q (2 * n) (k + n).toNat) atTop (𝓝 (eulerProd Q)⁻¹) := by
  have hE := eulerProd_ne_zero hQ
  have h1 : Tendsto (fun n : ℕ ↦ qPoch Q (2 * n)) atTop (𝓝 (eulerProd Q)) :=
    (tendsto_qPoch hQ).comp (tendsto_atTop_atTop.mpr fun b ↦ ⟨b, fun a ha ↦ by omega⟩)
  have h2 : Tendsto (fun n : ℕ ↦ qPoch Q (k + n).toNat) atTop (𝓝 (eulerProd Q)) :=
    (tendsto_qPoch hQ).comp
      (tendsto_atTop_atTop.mpr fun b ↦ ⟨b + k.natAbs, fun a ha ↦ by omega⟩)
  have h3 : Tendsto (fun n : ℕ ↦ qPoch Q (2 * n - (k + n).toNat)) atTop (𝓝 (eulerProd Q)) :=
    (tendsto_qPoch hQ).comp
      (tendsto_atTop_atTop.mpr fun b ↦ ⟨b + k.natAbs, fun a ha ↦ by omega⟩)
  have h4 := h1.div (h2.mul h3) (mul_ne_zero hE hE)
  have e : eulerProd Q / (eulerProd Q * eulerProd Q) = (eulerProd Q)⁻¹ := by field_simp
  rw [e] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop k.natAbs] with n hn
  unfold gaussBinom
  rw [if_pos (by omega)]
  rfl

end Bounds

/-! ### Summability of the theta series -/

section Theta

lemma exists_tau {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    ∃ τ : ℂ, 0 < τ.im ∧ cexp (π * I * τ) = q := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨-(I * Complex.log q) / π, ?_, ?_⟩
  · have h := Real.log_neg (norm_pos_iff.mpr hq0) hq
    simp only [Complex.div_ofReal_im, Complex.neg_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_add, Complex.log_re]
    exact div_pos (by linarith) Real.pi_pos
  · have : π * I * (-(I * Complex.log q) / π) = Complex.log q := by
      field_simp
      rw [Complex.I_sq]; ring
    rw [this, Complex.exp_log hq0]

lemma exists_w {x : ℂ} (hx : x ≠ 0) : ∃ w : ℂ, cexp (2 * π * I * w) = x := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨-(I * Complex.log x) / (2 * π), ?_⟩
  have : 2 * π * I * (-(I * Complex.log x) / (2 * π)) = Complex.log x := by
    field_simp
    rw [Complex.I_sq]; ring
  rw [this, Complex.exp_log hx]

lemma natAbs_sq_cast (n : ℤ) : ((n.natAbs ^ 2 : ℕ) : ℂ) = (n : ℂ) ^ 2 := by
  have h : ((n.natAbs ^ 2 : ℕ) : ℤ) = n ^ 2 := by rw [Nat.cast_pow]; exact Int.natAbs_sq n
  have := congrArg (Int.cast (R := ℂ)) h
  rw [Int.cast_natCast, Int.cast_pow] at this
  exact this

lemma jacobiTheta₂_term_eq (w τ : ℂ) (n : ℤ) :
    jacobiTheta₂_term n w τ = cexp (π * I * τ) ^ (n.natAbs ^ 2) * cexp (2 * π * I * w) ^ n := by
  unfold jacobiTheta₂_term
  rw [Complex.exp_add, ← Complex.exp_int_mul, ← Complex.exp_nat_mul, natAbs_sq_cast, mul_comm]
  congr 2 <;> ring

lemma summable_theta_norm {q x : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hx : x ≠ 0) :
    Summable fun n : ℤ ↦ ‖q ^ (n.natAbs ^ 2) * x ^ n‖ := by
  obtain ⟨τ, hτ, rfl⟩ := exists_tau hq0 hq
  obtain ⟨w, rfl⟩ := exists_w hx
  have := (summable_jacobiTheta₂_term_iff w τ).mpr hτ
  simp_rw [jacobiTheta₂_term_eq] at this
  exact summable_norm_iff.mpr this

end Theta

/-! ### Passing to the limit -/

section Limit

variable {q x : ℂ}

/-- `∏ (1 + c rⁿ)` converges for `‖r‖ < 1`. -/
lemma multipliable_one_add_mul_pow (c r : ℂ) (hr : ‖r‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 + c * r ^ n := by
  apply multipliable_one_add_of_summable
  simpa [norm_mul, norm_pow] using (summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left ‖c‖

lemma norm_sq_lt_one {q : ℂ} (hq : ‖q‖ < 1) : ‖q ^ 2‖ < 1 := by
  rw [norm_pow]; nlinarith [norm_nonneg q]

lemma multipliable_one_add_odd (c : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun k : ℕ ↦ 1 + c * q ^ (2 * k + 1) :=
  (multipliable_one_add_mul_pow (c * q) (q ^ 2) (norm_sq_lt_one hq)).congr fun n ↦ by ring

lemma tprod_mul_three {a b c : ℕ → ℂ} (ha : Multipliable a) (hb : Multipliable b)
    (hc : Multipliable c) :
    ∏' n, (a n * b n * c n) = (∏' n, a n) * (∏' n, b n) * ∏' n, c n := by
  rw [(ha.mul hb).tprod_mul hc, ha.tprod_mul hb]

/-- The terms of the finite triple product sum, re-indexed over `ℤ`. -/
def Fterm (q x : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  if k.natAbs ≤ n then gaussBinom (q ^ 2) (2 * n) (k + n).toNat * (q ^ (k.natAbs ^ 2) * x ^ k)
  else 0

lemma natAbs_pow_eq (q : ℂ) (k : ℤ) : q ^ (k.natAbs ^ 2) = q ^ (k ^ 2) := by
  rw [← zpow_natCast]; congr 1
  rw [Nat.cast_pow]; exact Int.natAbs_sq k

lemma tsum_Fterm (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hx : x ≠ 0) (n : ℕ) :
    ∑' k, Fterm q x n k =
      ∏ k ∈ range n, ((1 + x * q ^ (2 * k + 1)) * (1 + x⁻¹ * q ^ (2 * k + 1))) := by
  rw [finite_triple hq0 hq hx n]
  have hg : Function.Injective (fun j : ℕ ↦ (j : ℤ) - n) := fun a b h ↦ by simpa using h
  have hsupp : Function.support (Fterm q x n) ⊆ Set.range (fun j : ℕ ↦ (j : ℤ) - n) := by
    intro k hk
    have : k.natAbs ≤ n := by
      by_contra h; exact hk (by simp [Fterm, h])
    exact ⟨(k + n).toNat, by simp only; omega⟩
  rw [← hg.tsum_eq hsupp, tsum_eq_sum (s := range (2 * n + 1))]
  · refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j < 2 * n + 1 := mem_range.mp hj
    simp only [Fterm]
    rw [if_pos (by omega), natAbs_pow_eq]
    have : ((j : ℤ) - n + n).toNat = j := by omega
    rw [this]
  · intro j hj
    have : ¬ (((j : ℤ) - n).natAbs ≤ n) := by have := mem_range.not.mp hj; omega
    simp [Fterm, this]

lemma norm_Fterm_le (hq : ‖q‖ < 1) (n : ℕ) (k : ℤ) :
    ‖Fterm q x n k‖ ≤ (Real.exp (‖q ^ 2‖ / (1 - ‖q ^ 2‖)) /
      (Real.exp (-(‖q ^ 2‖ / (1 - ‖q ^ 2‖) / (1 - ‖q ^ 2‖))) *
        Real.exp (-(‖q ^ 2‖ / (1 - ‖q ^ 2‖) / (1 - ‖q ^ 2‖))))) * ‖q ^ (k.natAbs ^ 2) * x ^ k‖ := by
  unfold Fterm
  split_ifs
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_gaussBinom_le (norm_sq_lt_one hq) _ _) (norm_nonneg _)
  · simp only [norm_zero]; positivity

lemma tendsto_Fterm (hq : ‖q‖ < 1) (k : ℤ) :
    Tendsto (fun n ↦ Fterm q x n k) atTop
      (𝓝 ((eulerProd (q ^ 2))⁻¹ * (q ^ (k.natAbs ^ 2) * x ^ k))) := by
  refine ((tendsto_gaussBinom (norm_sq_lt_one hq) k).mul_const _).congr' ?_
  filter_upwards [eventually_ge_atTop k.natAbs] with n hn
  simp only [Fterm]
  rw [if_pos hn]

/-- The triple product, `q ≠ 0` case. -/
theorem hasSum_theta_eulerProd (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hx : x ≠ 0) :
    HasSum (fun k : ℤ ↦ q ^ (k.natAbs ^ 2) * x ^ k)
      (eulerProd (q ^ 2) *
        ∏' k : ℕ, ((1 + x * q ^ (2 * k + 1)) * (1 + x⁻¹ * q ^ (2 * k + 1)))) := by
  have hsum := summable_theta_norm hq0 hq hx
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun n k ↦ Fterm q x n k)
    (g := fun k : ℤ ↦ (eulerProd (q ^ 2))⁻¹ * (q ^ (k.natAbs ^ 2) * x ^ k))
    (bound := fun k : ℤ ↦ (Real.exp (‖q ^ 2‖ / (1 - ‖q ^ 2‖)) /
      (Real.exp (-(‖q ^ 2‖ / (1 - ‖q ^ 2‖) / (1 - ‖q ^ 2‖))) *
        Real.exp (-(‖q ^ 2‖ / (1 - ‖q ^ 2‖) / (1 - ‖q ^ 2‖))))) * ‖q ^ (k.natAbs ^ 2) * x ^ k‖)
    (hsum.mul_left _) (fun k ↦ tendsto_Fterm hq k)
    (Eventually.of_forall fun n k ↦ norm_Fterm_le hq n k)
  have hmult : Multipliable fun k : ℕ ↦ ((1 + x * q ^ (2 * k + 1)) * (1 + x⁻¹ * q ^ (2 * k + 1))) :=
    (multipliable_one_add_odd x hq).mul (multipliable_one_add_odd x⁻¹ hq)
  have hP := hmult.hasProd.tendsto_prod_nat
  have hT' : Tendsto (fun n ↦ ∏ k ∈ range n,
      ((1 + x * q ^ (2 * k + 1)) * (1 + x⁻¹ * q ^ (2 * k + 1)))) atTop
      (𝓝 (∑' k : ℤ, (eulerProd (q ^ 2))⁻¹ * (q ^ (k.natAbs ^ 2) * x ^ k))) :=
    hT.congr fun n ↦ tsum_Fterm hq0 hq hx n
  have h := tendsto_nhds_unique hT' hP
  rw [tsum_mul_left] at h
  have hE := eulerProd_ne_zero (norm_sq_lt_one hq)
  have h2 : ∑' k : ℤ, q ^ (k.natAbs ^ 2) * x ^ k = eulerProd (q ^ 2) *
      ∏' k : ℕ, ((1 + x * q ^ (2 * k + 1)) * (1 + x⁻¹ * q ^ (2 * k + 1))) := by
    rw [← h]; field_simp
  rw [← h2]
  exact hsum.of_norm.hasSum

end Limit

/-! ### Pairing positive and negative indices -/

section Pairing

lemma tsum_int_pair_succ {f : ℤ → ℂ} (hf : Summable f) :
    ∑' k, f k = f 0 + ∑' n : ℕ, (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) := by
  have h1 : Summable fun n : ℕ ↦ f ((n : ℤ) + 1) :=
    hf.comp_injective (i := fun n : ℕ ↦ (n : ℤ) + 1) (fun a b h ↦ by simpa using h)
  have h2 : Summable fun n : ℕ ↦ f (-((n : ℤ) + 1)) :=
    hf.comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1)) (fun a b h ↦ by simpa using h)
  rw [h1.tsum_add h2, (h1.hasSum.of_add_one_of_neg_add_one h2.hasSum).tsum_eq]
  ring

lemma tsum_int_pair {f : ℤ → ℂ} (hf : Summable f) :
    ∑' k, f k = ∑' n : ℕ, (f n + f (-((n : ℤ) + 1))) := by
  have h1 : Summable fun n : ℕ ↦ f n := hf.comp_injective (i := fun n : ℕ ↦ (n : ℤ))
    Nat.cast_injective
  have h2 : Summable fun n : ℕ ↦ f (-((n : ℤ) + 1)) :=
    hf.comp_injective (i := fun n : ℕ ↦ -((n : ℤ) + 1)) (fun a b h ↦ by simpa using h)
  rw [tsum_of_nat_of_neg_add_one h1 h2, h1.tsum_add h2]

lemma pair_succ_term (q z : ℂ) (n : ℕ) :
    q ^ (((n : ℤ) + 1).natAbs ^ 2) * z ^ ((n : ℤ) + 1) +
      q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * z ^ (-((n : ℤ) + 1)) =
    q ^ ((n + 1) ^ 2) * (z ^ (n + 1) + (z ^ (n + 1))⁻¹) := by
  have a : ((n : ℤ) + 1).natAbs = n + 1 := by omega
  have b : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
  rw [a, b, zpow_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  ring

lemma pair_term (q z : ℂ) (n : ℕ) :
    q ^ ((n : ℤ).natAbs ^ 2) * z ^ (n : ℤ) +
      q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * z ^ (-((n : ℤ) + 1)) =
    q ^ (n ^ 2) * z ^ n + q ^ ((n + 1) ^ 2) * (z ^ (n + 1))⁻¹ := by
  have b : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
  rw [Int.natAbs_natCast, b, zpow_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, zpow_natCast]

lemma two_cos_eq (y : ℂ) : 2 * Complex.cos y = cexp (y * I) + (cexp (y * I))⁻¹ := by
  rw [Complex.two_cos, ← Complex.exp_neg, neg_mul]

lemma two_I_sin_eq (y : ℂ) : 2 * I * Complex.sin y = cexp (y * I) - (cexp (y * I))⁻¹ := by
  have h := Complex.two_sin (x := y)
  rw [neg_mul, Complex.exp_neg] at h
  calc 2 * I * Complex.sin y = I * (2 * Complex.sin y) := by ring
    _ = I * (((cexp (y * I))⁻¹ - cexp (y * I)) * I) := by rw [h]
    _ = _ := by linear_combination ((cexp (y * I))⁻¹ - cexp (y * I)) * Complex.I_sq

end Pairing

/-! ### The identity -/

/-- **Jacobi's triple product identity** (*Fundamenta nova* 1829, § 64, p. 182),
in Jacobi's variables: for `|q| < 1` and `z ≠ 0`,
`∏_{n ≥ 1} (1 - q^{2n})(1 + q^{2n-1} z)(1 + q^{2n-1}/z) = ∑_{n ∈ ℤ} q^{n²} zⁿ` (indices shifted to start at `0`
on the product side). -/
@[kb "jacobi1829" "§ 64, p. 182"]
theorem triple_product {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    HasSum (fun n : ℤ ↦ q ^ (n.natAbs ^ 2) * z ^ n)
      (∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1) * z) * (1 + q ^ (2 * n + 1) / z)) := by
  by_cases hq0 : q = 0
  · subst hq0
    have h1 : ∏' n : ℕ, (1 - (0 : ℂ) ^ (2 * n + 2)) * (1 + (0 : ℂ) ^ (2 * n + 1) * z) *
        (1 + (0 : ℂ) ^ (2 * n + 1) / z) = 1 := by
      simp
    rw [h1]
    have := hasSum_single (f := fun n : ℤ ↦ (0 : ℂ) ^ (n.natAbs ^ 2) * z ^ n) 0
      (fun b hb ↦ by simp [hb])
    simpa using this
  · have h := hasSum_theta_eulerProd hq0 hq hz
    have hQ := norm_sq_lt_one hq
    have ha : Multipliable fun i : ℕ ↦ 1 - (q ^ 2) ^ (i + 1) :=
      ModularForm.multipliable_one_sub_pow hQ
    have hbc : Multipliable fun k : ℕ ↦ ((1 + z * q ^ (2 * k + 1)) * (1 + z⁻¹ * q ^ (2 * k + 1))) :=
      (multipliable_one_add_odd z hq).mul (multipliable_one_add_odd z⁻¹ hq)
    have e : ∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1) * z) *
        (1 + q ^ (2 * n + 1) / z) = eulerProd (q ^ 2) *
          ∏' k : ℕ, ((1 + z * q ^ (2 * k + 1)) * (1 + z⁻¹ * q ^ (2 * k + 1))) := by
      rw [eulerProd, ← ha.tprod_mul hbc]
      exact tprod_congr fun n ↦ by ring
    rw [e]
    exact h

/-- **The triple product in theta notation**: `ϑ(w, τ) = ∑ e^{2πinw + πin²τ} = ∏_{n ≥ 1} (1 - q^{2n})
(1 + q^{2n-1} e^{2πiw})(1 + q^{2n-1} e^{-2πiw})`, `q = e^{πiτ}`, `Im τ > 0` (the form of
`Historical.Weber.JacobiTripleProduct`). -/
@[kb "jacobi1829" "§ 64, p. 182"]
theorem jacobiTheta₂_eq_tprod (w τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂ w τ =
      ∏' n : ℕ, (1 - cexp (2 * π * I * (n + 1) * τ)) * (1 + cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w)) *
        (1 + cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w)) := by
  obtain ⟨q, hq⟩ : ∃ q, q = cexp (π * I * τ) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = cexp (2 * π * I * w) := ⟨_, rfl⟩
  have hqn : ‖q‖ < 1 := by
    rw [hq, Complex.norm_exp, Real.exp_lt_one_iff]
    have : (π * I * τ).re = -(π * τ.im) := by simp
    rw [this]
    have := Real.pi_pos
    nlinarith
  have hz0 : z ≠ 0 := hz ▸ Complex.exp_ne_zero _
  have h := triple_product hqn hz0
  have e1 : ∀ n : ℕ, cexp (2 * π * I * (n + 1) * τ) = q ^ (2 * n + 2) := fun n ↦ by
    rw [hq, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : ∀ n : ℕ, cexp (π * I * (2 * n + 1) * τ + 2 * π * I * w) = q ^ (2 * n + 1) * z :=
    fun n ↦ by
    rw [Complex.exp_add, hq, hz, ← Complex.exp_nat_mul]; congr 2; push_cast; ring
  have e3 : ∀ n : ℕ, cexp (π * I * (2 * n + 1) * τ - 2 * π * I * w) = q ^ (2 * n + 1) / z :=
    fun n ↦ by
    rw [Complex.exp_sub, hq, hz, ← Complex.exp_nat_mul]; congr 2; push_cast; ring
  simp_rw [e1, e2, e3]
  rw [← h.tsum_eq]
  unfold jacobiTheta₂
  refine tsum_congr fun n ↦ ?_
  rw [jacobiTheta₂_term_eq, ← hq, ← hz]

/-- **The cosine form** (*Fundamenta nova* § 64, pp. 180–182): for `|q| < 1` and every complex `x`,
`∏_{n ≥ 1} (1 - q^{2n})(1 - 2q^{2n-1} cos 2x + q^{4n-2}) = 1 + 2 ∑_{n ≥ 1} (-1)ⁿ q^{n²} cos 2nx`
(indices shifted to start at `0`). -/
@[kb "jacobi1829" "§ 64, pp. 180–182"]
theorem triple_product_cos {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    ∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 - 2 * q ^ (2 * n + 1) * Complex.cos (2 * x) + q ^ (4 * n + 2)) =
      1 + 2 * ∑' n : ℕ, (-1) ^ (n + 1) * q ^ ((n + 1) ^ 2) * Complex.cos (2 * (n + 1) * x) := by
  by_cases hq0 : q = 0
  · subst hq0
    simp
  · obtain ⟨u, hu⟩ : ∃ u, u = cexp (2 * x * I) := ⟨_, rfl⟩
    have hu0 : u ≠ 0 := hu ▸ Complex.exp_ne_zero _
    have hz0 : -u ≠ 0 := neg_ne_zero.mpr hu0
    have h := triple_product hq hz0
    have h1 : u + u⁻¹ = 2 * Complex.cos (2 * x) := by rw [two_cos_eq, ← hu]
    have e1 : ∏' n : ℕ, (1 - q ^ (2 * n + 2)) *
          (1 - 2 * q ^ (2 * n + 1) * Complex.cos (2 * x) + q ^ (4 * n + 2)) =
        ∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1) * (-u)) *
          (1 + q ^ (2 * n + 1) / (-u)) := by
      refine tprod_congr fun n ↦ ?_
      have : 2 * q ^ (2 * n + 1) * Complex.cos (2 * x) = q ^ (2 * n + 1) * (u + u⁻¹) := by
        rw [h1]; ring
      rw [this]
      field_simp
      ring
    rw [e1, ← h.tsum_eq, tsum_int_pair_succ h.summable]
    have e2 : ∀ n : ℕ, q ^ (((n : ℤ) + 1).natAbs ^ 2) * (-u) ^ ((n : ℤ) + 1) +
        q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * (-u) ^ (-((n : ℤ) + 1)) =
        2 * ((-1) ^ (n + 1) * q ^ ((n + 1) ^ 2) * Complex.cos (2 * ((n : ℂ) + 1) * x)) := by
      intro n
      rw [pair_succ_term]
      have hcc : ((-1 : ℂ) ^ (n + 1))⁻¹ = (-1) ^ (n + 1) :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_pow]; norm_num)
      have hc : u ^ (n + 1) + (u ^ (n + 1))⁻¹ = 2 * Complex.cos (2 * ((n : ℂ) + 1) * x) := by
        have : u ^ (n + 1) = cexp (2 * ((n : ℂ) + 1) * x * I) := by
          rw [hu, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
        rw [this, two_cos_eq]
      rw [neg_pow, mul_inv, hcc]
      linear_combination ((-1 : ℂ) ^ (n + 1) * q ^ ((n + 1) ^ 2)) * hc
    simp_rw [e2]
    rw [tsum_mul_left]
    simp

/-- **The sine analogue** (*Fundamenta nova* § 64, p. 183): for `|q| < 1` and every complex `x`,
`∏_{n ≥ 1} (1 - q^{2n}) · 2 sin x · ∏_{n ≥ 1} (1 - 2q^{2n} cos 2x + q^{4n}) = 2 ∑_{n ≥ 0} (-1)ⁿ q^{n(n+1)} sin (2n+1)x`
(indices shifted to start at `0`). -/
@[kb "jacobi1829" "§ 64, p. 183"]
theorem triple_product_sin {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) :
    (∏' n : ℕ, (1 - q ^ (2 * n + 2))) * (2 * Complex.sin x) *
        ∏' n : ℕ, (1 - 2 * q ^ (2 * n + 2) * Complex.cos (2 * x) + q ^ (4 * n + 4)) =
      2 * ∑' n : ℕ, (-1) ^ n * q ^ (n * (n + 1)) * Complex.sin ((2 * n + 1) * x) := by
  by_cases hq0 : q = 0
  · subst hq0
    have h1 : ∏' n : ℕ, (1 - (0 : ℂ) ^ (2 * n + 2)) = 1 := by simp
    have h2 : ∏' n : ℕ, (1 - 2 * (0 : ℂ) ^ (2 * n + 2) * Complex.cos (2 * x) + 0 ^ (4 * n + 4)) =
        1 := by simp
    rw [h1, h2, tsum_eq_single 0 (fun n hn ↦ by simp [hn])]
    simp
  · obtain ⟨s, hs⟩ : ∃ s, s = cexp (x * I) := ⟨_, rfl⟩
    have hs0 : s ≠ 0 := hs ▸ Complex.exp_ne_zero _
    obtain ⟨z, hz⟩ : ∃ z, z = -(q * s ^ 2) := ⟨_, rfl⟩
    have hz0 : z ≠ 0 := hz ▸ neg_ne_zero.mpr (mul_ne_zero hq0 (pow_ne_zero _ hs0))
    have h := triple_product hq hz0
    have hQ := norm_sq_lt_one hq
    have ha : Multipliable fun n : ℕ ↦ 1 - q ^ (2 * n + 2) :=
      (ModularForm.multipliable_one_sub_pow hQ).congr fun n ↦ by ring
    have hb : Multipliable fun n : ℕ ↦ 1 + q ^ (2 * n + 1) * z :=
      (multipliable_one_add_odd z hq).congr fun n ↦ by ring
    have hc : Multipliable fun n : ℕ ↦ 1 + q ^ (2 * n + 1) / z :=
      (multipliable_one_add_odd z⁻¹ hq).congr fun n ↦ by ring
    have hc' : Multipliable fun n : ℕ ↦ 1 + q ^ (2 * (n + 1) + 1) / z :=
      (multipliable_one_add_odd (z⁻¹ * q ^ 2) hq).congr fun n ↦ by ring
    have h1 : s ^ 2 + (s ^ 2)⁻¹ = 2 * Complex.cos (2 * x) := by
      rw [two_cos_eq, hs, ← Complex.exp_nat_mul]
      congr 2 <;> (push_cast; ring_nf)
    have hmid : (∏' n : ℕ, (1 + q ^ (2 * n + 1) * z)) *
        ∏' n : ℕ, (1 + q ^ (2 * (n + 1) + 1) / z) =
        ∏' n : ℕ, (1 - 2 * q ^ (2 * n + 2) * Complex.cos (2 * x) + q ^ (4 * n + 4)) := by
      rw [← hb.tprod_mul hc']
      refine tprod_congr fun n ↦ ?_
      have : 2 * q ^ (2 * n + 2) * Complex.cos (2 * x) = q ^ (2 * n + 2) * (s ^ 2 + (s ^ 2)⁻¹) := by
        rw [h1]; ring
      rw [this, hz]
      field_simp
      ring
    have hc0 : 1 + q ^ (2 * 0 + 1) / z = 1 - (s ^ 2)⁻¹ := by
      rw [hz]; field_simp; ring
    have eq2 : (∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1) * z) *
        (1 + q ^ (2 * n + 1) / z)) = (∏' n : ℕ, (1 - q ^ (2 * n + 2))) * (1 - (s ^ 2)⁻¹) *
          ∏' n : ℕ, (1 - 2 * q ^ (2 * n + 2) * Complex.cos (2 * x) + q ^ (4 * n + 4)) := by
      have h3 := tprod_mul_three ha hb hc
      have hct : ∏' n : ℕ, (1 + q ^ (2 * n + 1) / z) =
          (1 + q ^ (2 * 0 + 1) / z) * ∏' n : ℕ, (1 + q ^ (2 * (n + 1) + 1) / z) :=
        tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 + q ^ (2 * n + 1) / z) hc'
      rw [h3, hct, hc0, ← hmid]
      ring
    have e3 : ∀ n : ℕ, s * (q ^ ((n : ℤ).natAbs ^ 2) * z ^ (n : ℤ) +
        q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * z ^ (-((n : ℤ) + 1))) =
        2 * I * ((-1) ^ n * q ^ (n * (n + 1)) * Complex.sin ((2 * n + 1) * x)) := by
      intro n
      have hs2 : 2 * I * Complex.sin ((2 * n + 1) * x) = s ^ (2 * n + 1) - (s ^ (2 * n + 1))⁻¹ := by
        have : s ^ (2 * n + 1) = cexp (((2 : ℂ) * n + 1) * x * I) := by
          rw [hs, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
        rw [two_I_sin_eq, this]
      have key : s * (q ^ ((n : ℤ).natAbs ^ 2) * z ^ (n : ℤ) +
          q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * z ^ (-((n : ℤ) + 1))) =
          (-1) ^ n * q ^ (n * (n + 1)) * (s ^ (2 * n + 1) - (s ^ (2 * n + 1))⁻¹) := by
        rw [pair_term, hz]
        have p1 : (-(q * s ^ 2)) ^ n = (-1) ^ n * q ^ n * s ^ (2 * n) := by
          rw [neg_pow, mul_pow, ← pow_mul]; ring
        have p2 : (-(q * s ^ 2)) ^ (n + 1) = (-1) ^ (n + 1) * q ^ (n + 1) * s ^ (2 * (n + 1)) := by
          rw [neg_pow, mul_pow, ← pow_mul]; ring
        have qq1 : q ^ ((n + 1) ^ 2) = q ^ (n ^ 2) * q ^ (2 * n + 1) := by
          rw [← pow_add]; congr 1; ring
        have qq2 : q ^ (n * (n + 1)) = q ^ (n ^ 2) * q ^ n := by
          rw [← pow_add]; congr 1; ring
        have hc1 : (-1 : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        have hcc : ((-1 : ℂ) ^ (n + 1))⁻¹ = (-1) ^ (n + 1) :=
          inv_eq_of_mul_eq_one_right (by rw [← mul_pow]; norm_num)
        rw [p1, p2, qq1, qq2]
        simp only [mul_inv, hcc]
        have : q ^ (n + 1) ≠ 0 := pow_ne_zero _ hq0
        have : s ^ (2 * (n + 1)) ≠ 0 := pow_ne_zero _ hs0
        have : s ^ (2 * n + 1) ≠ 0 := pow_ne_zero _ hs0
        field_simp
        ring
      rw [key]
      linear_combination (-((-1 : ℂ) ^ n * q ^ (n * (n + 1)))) * hs2
    have eq1 : s * (∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + q ^ (2 * n + 1) * z) *
        (1 + q ^ (2 * n + 1) / z)) =
        2 * I * ∑' n : ℕ, (-1) ^ n * q ^ (n * (n + 1)) * Complex.sin ((2 * n + 1) * x) := by
      calc _ = s * ∑' n : ℕ, (q ^ ((n : ℤ).natAbs ^ 2) * z ^ (n : ℤ) +
            q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * z ^ (-((n : ℤ) + 1))) := by
            rw [← h.tsum_eq, tsum_int_pair h.summable]
        _ = ∑' n : ℕ, s * (q ^ ((n : ℤ).natAbs ^ 2) * z ^ (n : ℤ) +
            q ^ ((-((n : ℤ) + 1)).natAbs ^ 2) * z ^ (-((n : ℤ) + 1))) := tsum_mul_left.symm
        _ = ∑' n : ℕ, 2 * I * ((-1) ^ n * q ^ (n * (n + 1)) * Complex.sin ((2 * n + 1) * x)) :=
            tsum_congr e3
        _ = _ := tsum_mul_left
    have eq3 : s * (1 - (s ^ 2)⁻¹) = s - s⁻¹ := by field_simp
    have eq4 : 2 * I * Complex.sin x = s - s⁻¹ := by rw [two_I_sin_eq, ← hs]
    refine mul_left_cancel₀ Complex.I_ne_zero ?_
    linear_combination
      ((∏' n : ℕ, (1 - q ^ (2 * n + 2))) *
        ∏' n : ℕ, (1 - 2 * q ^ (2 * n + 2) * Complex.cos (2 * x) + q ^ (4 * n + 4))) * eq4 -
      ((∏' n : ℕ, (1 - q ^ (2 * n + 2))) *
        ∏' n : ℕ, (1 - 2 * q ^ (2 * n + 2) * Complex.cos (2 * x) + q ^ (4 * n + 4))) * eq3 -
      s * eq2 + eq1

end ModularFormsKB.Historical.Jacobi
