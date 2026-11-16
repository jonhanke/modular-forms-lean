import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import ModularFormsKB.Citation
/-!
# Ramanujan's Euler products for `ζ(s)/ζ(2s)` (No. 4)

Ramanujan, *Collected Papers*, No. 4, §§ 3, 5–6, pp. 20–21:

* (4) `∏_p (1 + p^{-s}) = ζ(s)/ζ(2s)`, with the examples (5) `∏_p (1 + p^{-2}) = 15/π²` and
  (6) `∏_p (1 + p^{-4}) = 105/π⁴`;
* (11) `∑_{k squarefree} k^{-s} = ζ(s)/ζ(2s)` and (10) `∑_k μ(k) k^{-s} = 1/ζ(s)`.

Ramanujan states these for real `n > 1`; they are stated here for complex `s` with `Re s > 1`.
-/

noncomputable section

open Complex
open scoped ArithmeticFunction.Moebius Real

namespace ModularFormsKB.Historical.Ramanujan

/-- **Ramanujan, No. 4, § 3, (4)** (p. 20): for `Re s > 1`,
`∏_p (1 + p^{-s}) = ζ(s)/ζ(2s)`. -/
@[kb "ramanujan1927" "No. 4, § 3, (4), p. 20"]
def PrimeProductZetaQuotient : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasProd (fun p : Nat.Primes ↦ 1 + (p : ℂ) ^ (-s)) (riemannZeta s / riemannZeta (2 * s))

/-- **Ramanujan, No. 4, § 3, (5)–(6)** (p. 20):
`∏_p (1 + p^{-2}) = 15/π²` and `∏_p (1 + p^{-4}) = 105/π⁴`. -/
@[kb "ramanujan1927" "No. 4, § 3, (5)-(6), p. 20"]
def PrimeProductValues : Prop :=
  HasProd (fun p : Nat.Primes ↦ 1 + ((p : ℂ) ^ 2)⁻¹) (15 / (π : ℂ) ^ 2) ∧
  HasProd (fun p : Nat.Primes ↦ 1 + ((p : ℂ) ^ 4)⁻¹) (105 / (π : ℂ) ^ 4)

/-- **Ramanujan, No. 4, § 6, (11)** (p. 21, first identity): for `Re s > 1`,
`∑_{k squarefree} k^{-s} = ζ(s)/ζ(2s)` (the sum includes `k = 1`). -/
@[kb "ramanujan1927" "No. 4, § 6, (11), p. 21"]
def SquarefreeZetaQuotient : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasSum (fun k : ℕ ↦ if Squarefree k then (k : ℂ) ^ (-s) else 0)
      (riemannZeta s / riemannZeta (2 * s))

/-- **Ramanujan, No. 4, § 5, (10)** (p. 21, second identity): for `Re s > 1`,
`∑_k μ(k) k^{-s} = 1/ζ(s)`. -/
@[kb "ramanujan1927" "No. 4, § 5, (10), p. 21"]
def MoebiusZetaInverse : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasSum (fun k : ℕ ↦ (μ k : ℂ) * (k : ℂ) ^ (-s)) (1 / riemannZeta s)

/-- Local factor identity: `1 + p^{-s} = (1 - p^{-s})⁻¹ / (1 - p^{-2s})⁻¹`. -/
private lemma local_factor (s : ℂ) (hs : 1 < s.re) (p : Nat.Primes) :
    1 + (p : ℂ) ^ (-s) = (1 - (p : ℂ) ^ (-s))⁻¹ / (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ := by
  have hp : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
    rw [show -(2 * s) = (2 : ℕ) * (-s) by push_cast; ring, cpow_nat_mul]
  have hne : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have h1 : ‖(p : ℂ) ^ (-s)‖ = 1 := by
      rw [show (p : ℂ) ^ (-s) = 1 by linear_combination -h, norm_one]
    have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg _)
        (by simp; linarith), neg_re]
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · exact_mod_cast p.2.one_lt
      · linarith
    linarith
  rw [inv_div_inv, hp]
  field_simp
  ring

/-- Ramanujan, No. 4, § 3, (4). -/
@[kb "ramanujan1927" "No. 4, § 3, (4), p. 20"]
theorem primeProductZetaQuotient : PrimeProductZetaQuotient := by
  intro s hs
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have h1 := riemannZeta_eulerProduct_hasProd hs
  have h2 := riemannZeta_eulerProduct_hasProd hs2
  have hne : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs2
  have := h1.div₀ h2 hne
  convert this using 1
  funext p
  exact local_factor s hs p

private lemma pow_neg_nat (n : ℕ) (p : Nat.Primes) :
    (p : ℂ) ^ (-(n : ℂ)) = (((p : ℂ) ^ n))⁻¹ := by
  rw [cpow_neg, cpow_natCast]

/-- Ramanujan, No. 4, § 3, (5)-(6). -/
@[kb "ramanujan1927" "No. 4, § 3, (5)-(6), p. 20"]
theorem primeProductValues : PrimeProductValues := by
  have hb : bernoulli 8 = -1 / 30 := by
    have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
    have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
    have h6 : bernoulli' 6 = 1 / 42 := by
      rw [bernoulli'_def]
      simp [Finset.sum_range_succ, Nat.choose, h5]
      norm_num
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    simp [Finset.sum_range_succ, Nat.choose, h5, h6, h7]
    norm_num
  have h8 : riemannZeta 8 = (π : ℂ) ^ 8 / 9450 := by
    have := riemannZeta_two_mul_nat (k := 4) (by norm_num)
    norm_num [hb, Nat.factorial] at this
    rw [this]
    ring
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · have := primeProductZetaQuotient (2 : ℂ) (by simp)
    convert this using 1
    · funext p
      rw [show (-(2 : ℂ)) = -((2 : ℕ) : ℂ) by norm_num, pow_neg_nat]
    · rw [show (2 : ℂ) * 2 = 4 by norm_num, riemannZeta_two, riemannZeta_four]
      field_simp
      norm_num
  · have := primeProductZetaQuotient (4 : ℂ) (by simp)
    convert this using 1
    · funext p
      rw [show (-(4 : ℂ)) = -((4 : ℕ) : ℂ) by norm_num, pow_neg_nat]
    · rw [show (2 : ℂ) * 4 = 8 by norm_num, h8, riemannZeta_four]
      field_simp
      norm_num

/-- The squarefree indicator weighted by `k^{-s}`. -/
private def sqf (s : ℂ) (k : ℕ) : ℂ := if Squarefree k then (k : ℂ) ^ (-s) else 0

private lemma sqf_summable (s : ℂ) (hs : 1 < s.re) : Summable (fun k ↦ ‖sqf s k‖) := by
  refine (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ ?_
  unfold sqf riemannZetaSummandHom
  split_ifs <;> simp

/-- Ramanujan, No. 4, § 6, (11). -/
@[kb "ramanujan1927" "No. 4, § 6, (11), p. 21"]
theorem squarefreeZetaQuotient : SquarefreeZetaQuotient := by
  intro s hs
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → sqf s (m * n) = sqf s m * sqf s n := by
    intro m n h
    have e : ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) :=
      (riemannZetaSummandHom hs0).map_mul m n
    simp only [sqf, Nat.squarefree_mul_iff]
    split_ifs <;> first | exact e | simp_all
  have h1 : sqf s 1 = 1 := by simp [sqf]
  have h0 : sqf s 0 = 0 := by simp [sqf]
  have hE := EulerProduct.eulerProduct_hasProd h1 hmul (sqf_summable s hs) h0
  have hloc : ∀ p : Nat.Primes, ∑' e, sqf s ((p : ℕ) ^ e) = 1 + (p : ℂ) ^ (-s) := by
    intro p
    rw [tsum_eq_sum (s := Finset.range 2)]
    · have hp : Squarefree (p : ℕ) := p.2.squarefree
      simp [sqf, Finset.sum_range_succ, hp]
    · intro e he
      simp only [Finset.mem_range, not_lt] at he
      have : ¬ Squarefree ((p : ℕ) ^ e) := by
        rw [Nat.squarefree_pow_iff p.2.ne_one (by lia)]
        lia
      simp [sqf, this]
  simp_rw [hloc] at hE
  have hP := primeProductZetaQuotient s hs
  have : ∑' n, sqf s n = riemannZeta s / riemannZeta (2 * s) := hE.unique hP
  have hsum : HasSum (sqf s) (∑' n, sqf s n) := (sqf_summable s hs).of_norm.hasSum
  rw [this] at hsum
  exact hsum

/-- Ramanujan, No. 4, § 5, (10). -/
@[kb "ramanujan1927" "No. 4, § 5, (10), p. 21"]
theorem moebiusZetaInverse : MoebiusZetaInverse := by
  intro s hs
  have hsum : LSeriesSummable (fun n ↦ (μ n : ℂ)) s := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have h := hsum.LSeriesHasSum
  have hL : LSeries (fun n ↦ (μ n : ℂ)) s = 1 / riemannZeta s := by
    have := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at this
    have hz := riemannZeta_ne_zero_of_one_lt_re hs
    rw [eq_div_iff hz]
    linear_combination this
  rw [hL] at h
  unfold LSeriesHasSum at h
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  convert h using 1
  funext k
  rcases eq_or_ne k 0 with rfl | hk
  · simp [LSeries.term, hs0]
  · rw [LSeries.term_of_ne_zero hk, cpow_neg, div_eq_mul_inv]

end ModularFormsKB.Historical.Ramanujan