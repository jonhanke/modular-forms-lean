import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import ModularFormsKB.Citation
/-!
# Ramanujan's Dirichlet series `∑ σ_a(n) σ_b(n) n^{-s}` (No. 17)

Ramanujan, *Collected Papers*, No. 17 (*Some formulae in the analytic theory of numbers*, Messenger of Math. 45
(1916), 81–84), (A) (1), p. 133 and (I) (15), p. 135:

  (15) `∑_{n ≥ 1} σ_a(n) σ_b(n) n^{-s} = ζ(s) ζ(s-a) ζ(s-b) ζ(s-a-b) / ζ(2s-a-b)`,  `σ_a(n) = ∑_{d ∣ n} d^a`,

"for all `a`, `b`" and `Re s` large; and its case `a = b = 0`,

  (1) `∑_{n ≥ 1} d(n)² n^{-s} = ζ(s)⁴/ζ(2s)`  (`Re s > 1`).

Here `a`, `b`, `s` are complex and the half plane is `Re s > 1 + max(0, Re a) + max(0, Re b)`, where every factor
converges absolutely (for `a = b = 0` it is Ramanujan's `Re s > 1`).

Proof: both sides are Euler products. The local factor at `p` is the identity
`∑_k σ_a(p^k) σ_b(p^k) X^k = (1 - αβX²)/((1 - X)(1 - αX)(1 - βX)(1 - αβX))`, `α = p^a`, `β = p^b`, `X = p^{-s}`
(`local_hasSum`), from `S_k(α) = 1 + α S_{k-1}(α)` for `S_k(α) = ∑_{i ≤ k} αⁱ`, which gives
`A_k - αβ A_{k-1} = S_k(α) + S_k(β) - 1` for `A_k = S_k(α) S_k(β)`. Absolute convergence uses the divisor bound
`d(n) ≤ C n^ε` (Tau Ceti, `exists_pos_card_divisors_le_rpow`).
-/

noncomputable section

open Complex Finset
open scoped Real

namespace ModularFormsKB.Historical.Ramanujan

/-- `σ_a(n) = ∑_{d ∣ n} d^a` for complex `a` (Ramanujan No. 17; `σ_a(0) = 0`). -/
def sigmaC (a : ℂ) (n : ℕ) : ℂ := ∑ d ∈ n.divisors, (d : ℂ) ^ a

/-- **Ramanujan, No. 17, (I) (15)** (p. 135): for complex `a`, `b`, `s` with
`Re s > 1 + max(0, Re a) + max(0, Re b)`,
`∑ σ_a(n) σ_b(n) n^{-s} = ζ(s) ζ(s-a) ζ(s-b) ζ(s-a-b)/ζ(2s-a-b)`. -/
@[kb "ramanujan1927" "No. 17, (I), (15), p. 135"]
def SigmaSigmaZetaQuotient : Prop :=
  ∀ a b s : ℂ, 1 + max 0 a.re + max 0 b.re < s.re →
    HasSum (fun n : ℕ ↦ sigmaC a n * sigmaC b n * (n : ℂ) ^ (-s))
      (riemannZeta s * riemannZeta (s - a) * riemannZeta (s - b) * riemannZeta (s - a - b) /
        riemannZeta (2 * s - a - b))

/-- **Ramanujan, No. 17, (A) (1)** (p. 133, the case `a = b = 0`): for `Re s > 1`,
`∑ d(n)² n^{-s} = ζ(s)⁴/ζ(2s)`. -/
@[kb "ramanujan1927" "No. 17, (A), (1), p. 133"]
def DivisorSquareZetaQuotient : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasSum (fun n : ℕ ↦ ((n.divisors.card : ℂ)) ^ 2 * (n : ℂ) ^ (-s))
      (riemannZeta s ^ 4 / riemannZeta (2 * s))

/-! ### The local factor -/

/-- `S_k(γ) = ∑_{i ≤ k} γⁱ`. -/
private def S (γ : ℂ) (k : ℕ) : ℂ := ∑ i ∈ range (k + 1), γ ^ i

private lemma S_succ (γ : ℂ) (k : ℕ) : S γ (k + 1) = 1 + γ * S γ k := by
  unfold S
  rw [sum_range_succ', mul_sum]
  simp only [pow_succ', pow_zero]
  ring

private lemma one_sub_ne {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, norm_one] at hz
  exact lt_irrefl _ hz

/-- `∑_k S_k(γ) X^k = 1/((1 - X)(1 - γX))`. -/
private lemma hasSum_S {γ X : ℂ} (hX : ‖X‖ < 1) (hγ : ‖γ * X‖ < 1) :
    HasSum (fun k ↦ S γ k * X ^ k) (1 / ((1 - X) * (1 - γ * X))) := by
  have h1 : Summable fun i : ℕ ↦ ‖(γ * X) ^ i‖ := by
    simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hγ
  have h2 : Summable fun j : ℕ ↦ ‖X ^ j‖ := by
    simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hX
  have h := hasSum_sum_range_mul_of_summable_norm h1 h2
  rw [tsum_geometric_of_norm_lt_one hγ, tsum_geometric_of_norm_lt_one hX] at h
  convert h using 1
  · funext k
    unfold S
    rw [sum_mul]
    refine sum_congr rfl fun i hi ↦ ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hik]
  · rw [one_div, mul_inv, mul_comm]

private lemma norm_S_le (γ : ℂ) (k : ℕ) : ‖S γ k‖ ≤ (k + 1) * max 1 ‖γ‖ ^ k := by
  unfold S
  calc ‖∑ i ∈ range (k + 1), γ ^ i‖ ≤ ∑ i ∈ range (k + 1), ‖γ ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range (k + 1), max 1 ‖γ‖ ^ k := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [norm_pow]
        have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
        calc ‖γ‖ ^ i ≤ max 1 ‖γ‖ ^ i := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
          _ ≤ max 1 ‖γ‖ ^ k := pow_le_pow_right₀ (le_max_left _ _) hik
    _ = (k + 1) * max 1 ‖γ‖ ^ k := by simp

/-- The local factor: `∑_k S_k(α) S_k(β) X^k = (1 - αβX²)/((1 - X)(1 - αX)(1 - βX)(1 - αβX))`. -/
lemma local_hasSum {α β X : ℂ} (h1 : ‖X‖ < 1) (h2 : ‖α * X‖ < 1) (h3 : ‖β * X‖ < 1)
    (h4 : ‖α * β * X‖ < 1) :
    HasSum (fun k ↦ (∑ i ∈ range (k + 1), α ^ i) * (∑ j ∈ range (k + 1), β ^ j) * X ^ k)
      ((1 - α * β * X ^ 2) / ((1 - X) * (1 - α * X) * (1 - β * X) * (1 - α * β * X))) := by
  change HasSum (fun k ↦ S α k * S β k * X ^ k) _
  -- summability
  set r := max 1 ‖α‖ * max 1 ‖β‖ * ‖X‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rcases le_total ‖α‖ 1 with ha | ha <;> rcases le_total ‖β‖ 1 with hb | hb
    · rw [hr, max_eq_left ha, max_eq_left hb]; simpa using h1
    · rw [hr, max_eq_left ha, max_eq_right hb]; simpa [norm_mul, mul_comm] using h3
    · rw [hr, max_eq_right ha, max_eq_left hb]; simpa [norm_mul] using h2
    · rw [hr, max_eq_right ha, max_eq_right hb]; simpa [norm_mul, mul_assoc] using h4
  have hsumr : Summable fun k : ℕ ↦ ((k : ℝ) + 1) ^ 2 * r ^ k := by
    have hn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
    have e0 := summable_pow_mul_geometric_of_norm_lt_one 0 hn
    have e1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
    have e2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
    convert (e2.add (e1.mul_left 2)).add e0 using 1
    funext k
    ring
  have hsum : Summable fun k ↦ S α k * S β k * X ^ k := by
    refine Summable.of_norm_bounded hsumr fun k ↦ ?_
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖S α k‖ * ‖S β k‖ * ‖X‖ ^ k
        ≤ ((k + 1) * max 1 ‖α‖ ^ k) * ((k + 1) * max 1 ‖β‖ ^ k) * ‖X‖ ^ k := by
          gcongr
          · exact norm_S_le α k
          · exact norm_S_le β k
      _ = ((k : ℝ) + 1) ^ 2 * r ^ k := by rw [hr, mul_pow, mul_pow]; ring
  obtain ⟨T, hT⟩ := hsum
  -- the recurrence
  have hshift := (hasSum_nat_add_iff' 1).mpr hT
  simp only [range_one, sum_singleton, pow_zero, mul_one] at hshift
  have hS0 : ∀ γ : ℂ, S γ 0 = 1 := fun γ ↦ by simp [S]
  rw [hS0, hS0, one_mul] at hshift
  have hGα := hasSum_S h1 h2
  have hGβ := hasSum_S h1 h3
  have hG1 : HasSum (fun k ↦ S 0 k * X ^ k) (1 / ((1 - X) * (1 - 0 * X))) := hasSum_S h1 (by simp)
  have hGα' := (hasSum_nat_add_iff' 1).mpr hGα
  have hGβ' := (hasSum_nat_add_iff' 1).mpr hGβ
  have hG1' := (hasSum_nat_add_iff' 1).mpr hG1
  simp only [range_one, sum_singleton, pow_zero, mul_one, hS0] at hGα' hGβ' hG1'
  have hTX := hT.mul_left (α * β * X)
  have hcomb := ((hGα'.add hGβ').sub hG1').add hTX
  have key : (fun k ↦ S α (k + 1) * S β (k + 1) * X ^ (k + 1)) =
      fun k ↦ S α (k + 1) * X ^ (k + 1) + S β (k + 1) * X ^ (k + 1) - S 0 (k + 1) * X ^ (k + 1) +
        α * β * X * (S α k * S β k * X ^ k) := by
    funext k
    have hz : S 0 (k + 1) = 1 := by simp [S, sum_range_succ', zero_pow]
    rw [S_succ α, S_succ β, hz, pow_succ]
    ring
  rw [key] at hshift
  have hT' := hshift.unique hcomb
  have e1 := one_sub_ne h1
  have e2 := one_sub_ne h2
  have e3 := one_sub_ne h3
  have e4 := one_sub_ne h4
  have hTval : T = (1 - α * β * X ^ 2) / ((1 - X) * (1 - α * X) * (1 - β * X) * (1 - α * β * X)) := by
    rw [zero_mul, sub_zero, mul_one] at hT'
    have hT2 : T * (1 - α * β * X) =
        1 / ((1 - X) * (1 - α * X)) + 1 / ((1 - X) * (1 - β * X)) - 1 / (1 - X) := by
      linear_combination hT'
    rw [eq_div_iff (by simp [e1, e2, e3, e4]),
      show T * ((1 - X) * (1 - α * X) * (1 - β * X) * (1 - α * β * X)) =
        (T * (1 - α * β * X)) * ((1 - X) * (1 - α * X) * (1 - β * X)) by ring, hT2]
    have e2' : 1 - X * α ≠ 0 := by rwa [mul_comm]
    have e3' : 1 - X * β ≠ 0 := by rwa [mul_comm]
    field_simp
    ring
  rw [← hTval]
  exact hT

/-! ### The Euler product -/

/-- `n ↦ n^a` as an arithmetic function over `ℂ` (value `0` at `0`). -/
private def powC (a : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ a, by simp⟩

private lemma powC_isMultiplicative (a : ℂ) : (powC a).IsMultiplicative := by
  refine ⟨by simp [powC], fun {m n} _ ↦ ?_⟩
  simp only [powC, ArithmeticFunction.coe_mk]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hm, hn, natCast_mul_natCast_cpow]

private lemma sigmaC_eq (a : ℂ) (n : ℕ) :
    sigmaC a n = ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * powC a) n := by
  rw [ArithmeticFunction.coe_zeta_mul_apply, sigmaC]
  refine sum_congr rfl fun d hd ↦ ?_
  have : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  simp [powC, this]

private lemma sigmaC_mul {a : ℂ} {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaC a (m * n) = sigmaC a m * sigmaC a n := by
  rw [sigmaC_eq, sigmaC_eq, sigmaC_eq]
  exact (ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (powC_isMultiplicative a)).map_mul_of_coprime h

private lemma sigmaC_prime_pow (a : ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    sigmaC a (p ^ e) = ∑ i ∈ range (e + 1), ((p : ℂ) ^ a) ^ i := by
  rw [sigmaC, Nat.divisors_prime_pow hp, sum_map]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [Function.Embedding.coeFn_mk]
  push_cast
  rw [← natCast_cpow_natCast_mul, cpow_nat_mul]

private lemma norm_sigmaC_le (a : ℂ) (n : ℕ) :
    ‖sigmaC a n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ max 0 a.re := by
  unfold sigmaC
  calc ‖∑ d ∈ n.divisors, (d : ℂ) ^ a‖ ≤ ∑ d ∈ n.divisors, ‖(d : ℂ) ^ a‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (n : ℝ) ^ max 0 a.re := by
        refine sum_le_sum fun d hd ↦ ?_
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        have hdn : d ≤ n := Nat.divisor_le hd
        rw [norm_natCast_cpow_of_pos hd0]
        have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
        calc (d : ℝ) ^ a.re ≤ (d : ℝ) ^ max 0 a.re :=
              Real.rpow_le_rpow_of_exponent_le h1 (le_max_right _ _)
          _ ≤ (n : ℝ) ^ max 0 a.re :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast hdn) (le_max_left _ _)
    _ = (n.divisors.card : ℝ) * (n : ℝ) ^ max 0 a.re := by simp

/-- The summand `σ_a(n) σ_b(n) n^{-s}`. -/
private def F (a b s : ℂ) (n : ℕ) : ℂ := sigmaC a n * sigmaC b n * (n : ℂ) ^ (-s)

private lemma F_summable {a b s : ℂ} (hs : 1 + max 0 a.re + max 0 b.re < s.re) :
    Summable fun n ↦ ‖F a b s n‖ := by
  set δ := s.re - 1 - max 0 a.re - max 0 b.re with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨C, hC0, hC⟩ := TauCeti.exists_pos_card_divisors_le_rpow (ε := δ / 4) (by positivity)
  have hsum : Summable fun n : ℕ ↦ C ^ 2 * (n : ℝ) ^ (-1 - δ / 2) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  refine hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [F, sigmaC, Nat.divisors_zero, sum_empty, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := hC n
  have hdpos : (0 : ℝ) ≤ n.divisors.card := Nat.cast_nonneg _
  unfold F
  rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hn, neg_re]
  calc ‖sigmaC a n‖ * ‖sigmaC b n‖ * (n : ℝ) ^ (-s.re)
      ≤ ((n.divisors.card : ℝ) * (n : ℝ) ^ max 0 a.re) *
          ((n.divisors.card : ℝ) * (n : ℝ) ^ max 0 b.re) * (n : ℝ) ^ (-s.re) := by
        gcongr
        · exact norm_sigmaC_le a n
        · exact norm_sigmaC_le b n
    _ ≤ ((C * (n : ℝ) ^ (δ / 4)) * (n : ℝ) ^ max 0 a.re) *
          ((C * (n : ℝ) ^ (δ / 4)) * (n : ℝ) ^ max 0 b.re) * (n : ℝ) ^ (-s.re) := by
        gcongr
    _ = C ^ 2 * (n : ℝ) ^ (-1 - δ / 2) := by
        have e : ∀ x y : ℝ, (n : ℝ) ^ x * (n : ℝ) ^ y = (n : ℝ) ^ (x + y) := fun x y ↦
          (Real.rpow_add hn0 x y).symm
        calc ((C * (n : ℝ) ^ (δ / 4)) * (n : ℝ) ^ max 0 a.re) *
              ((C * (n : ℝ) ^ (δ / 4)) * (n : ℝ) ^ max 0 b.re) * (n : ℝ) ^ (-s.re)
            = C ^ 2 * (((n : ℝ) ^ (δ / 4) * (n : ℝ) ^ max 0 a.re) *
                ((n : ℝ) ^ (δ / 4) * (n : ℝ) ^ max 0 b.re) * (n : ℝ) ^ (-s.re)) := by ring
          _ = C ^ 2 * (n : ℝ) ^ (-1 - δ / 2) := by
              rw [e, e, e, e]
              congr 2
              rw [hδ]
              ring

private lemma F_one (a b s : ℂ) : F a b s 1 = 1 := by
  simp [F, sigmaC]

private lemma F_zero (a b s : ℂ) : F a b s 0 = 0 := by
  simp [F, sigmaC]

private lemma F_mul (a b s : ℂ) {m n : ℕ} (h : Nat.Coprime m n) :
    F a b s (m * n) = F a b s m * F a b s n := by
  unfold F
  rw [sigmaC_mul h, sigmaC_mul h, Nat.cast_mul, natCast_mul_natCast_cpow]
  ring

private lemma norm_cpow_lt_one {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z.re < 0) : ‖(p : ℂ) ^ z‖ < 1 := by
  rw [norm_natCast_cpow_of_pos hp.pos]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) hz

private lemma cpow_add_p {p : ℕ} (hp : p.Prime) (x y : ℂ) :
    (p : ℂ) ^ (x + y) = (p : ℂ) ^ x * (p : ℂ) ^ y :=
  cpow_add _ _ (by exact_mod_cast hp.ne_zero)

/-- Ramanujan, No. 17, (I) (15). -/
@[kb "ramanujan1927" "No. 17, (I), (15), p. 135"]
theorem sigmaSigmaZetaQuotient : SigmaSigmaZetaQuotient := by
  intro a b s hs
  have hA := le_max_left 0 a.re
  have hA' := le_max_right 0 a.re
  have hB := le_max_left 0 b.re
  have hB' := le_max_right 0 b.re
  have hs1 : 1 < s.re := by linarith
  have hsa : 1 < (s - a).re := by simp; linarith
  have hsb : 1 < (s - b).re := by simp; linarith
  have hsab : 1 < (s - a - b).re := by simp; linarith
  have hs2 : 1 < (2 * s - a - b).re := by simp; linarith
  have hne : riemannZeta (2 * s - a - b) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs2
  have hZ := ((((riemannZeta_eulerProduct_hasProd hs1).mul (riemannZeta_eulerProduct_hasProd hsa)).mul
    (riemannZeta_eulerProduct_hasProd hsb)).mul (riemannZeta_eulerProduct_hasProd hsab)).div₀
    (riemannZeta_eulerProduct_hasProd hs2) hne
  have hE := EulerProduct.eulerProduct_hasProd (F_one a b s) (fun h ↦ F_mul a b s h) (F_summable hs)
    (F_zero a b s)
  have hloc : ∀ p : Nat.Primes, ∑' e, F a b s ((p : ℕ) ^ e) =
      (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (p : ℂ) ^ (-(s - a)))⁻¹ * (1 - (p : ℂ) ^ (-(s - b)))⁻¹ *
        (1 - (p : ℂ) ^ (-(s - a - b)))⁻¹ / (1 - (p : ℂ) ^ (-(2 * s - a - b)))⁻¹ := by
    intro p
    have hp := p.2
    set α := (p : ℂ) ^ a
    set β := (p : ℂ) ^ b
    set X := (p : ℂ) ^ (-s)
    have h1 : ‖X‖ < 1 := norm_cpow_lt_one hp (by simp; linarith)
    have e2 : α * X = (p : ℂ) ^ (a + -s) := (cpow_add_p hp a (-s)).symm
    have e3 : β * X = (p : ℂ) ^ (b + -s) := (cpow_add_p hp b (-s)).symm
    have e4 : α * β * X = (p : ℂ) ^ (a + b + -s) := by
      rw [cpow_add_p hp, cpow_add_p hp]
    have e5 : α * β * X ^ 2 = (p : ℂ) ^ (a + b + -s + -s) := by
      rw [cpow_add_p hp, cpow_add_p hp, cpow_add_p hp]; ring
    have h2 : ‖α * X‖ < 1 := by rw [e2]; exact norm_cpow_lt_one hp (by simp; linarith)
    have h3 : ‖β * X‖ < 1 := by rw [e3]; exact norm_cpow_lt_one hp (by simp; linarith)
    have h4 : ‖α * β * X‖ < 1 := by rw [e4]; exact norm_cpow_lt_one hp (by simp; linarith)
    have h5 : ‖α * β * X ^ 2‖ < 1 := by rw [e5]; exact norm_cpow_lt_one hp (by simp; linarith)
    have hterm : ∀ e : ℕ, F a b s ((p : ℕ) ^ e) =
        (∑ i ∈ range (e + 1), α ^ i) * (∑ j ∈ range (e + 1), β ^ j) * X ^ e := by
      intro e
      unfold F
      rw [sigmaC_prime_pow a hp, sigmaC_prime_pow b hp]
      push_cast
      rw [← natCast_cpow_natCast_mul, cpow_nat_mul]
    rw [tsum_congr hterm, (local_hasSum h1 h2 h3 h4).tsum_eq]
    rw [show -(s - a) = a + -s by ring, show -(s - b) = b + -s by ring,
      show -(s - a - b) = a + b + -s by ring, show -(2 * s - a - b) = a + b + -s + -s by ring,
      ← e2, ← e3, ← e4, ← e5]
    have n1 := one_sub_ne h1
    have n2 := one_sub_ne h2
    have n3 := one_sub_ne h3
    have n4 := one_sub_ne h4
    have n5 := one_sub_ne h5
    field_simp
  simp_rw [hloc] at hE
  have hval := hE.unique hZ
  have hsum : HasSum (F a b s) (∑' n, F a b s n) := (F_summable hs).of_norm.hasSum
  rw [hval] at hsum
  exact hsum

/-- Ramanujan, No. 17, (A) (1). -/
@[kb "ramanujan1927" "No. 17, (A), (1), p. 133"]
theorem divisorSquareZetaQuotient : DivisorSquareZetaQuotient := by
  intro s hs
  have h := sigmaSigmaZetaQuotient 0 0 s (by simpa using hs)
  have hd : ∀ n : ℕ, sigmaC 0 n = (n.divisors.card : ℂ) := fun n ↦ by simp [sigmaC]
  simp only [hd, sub_zero] at h
  convert h using 1
  · funext n; ring
  · ring

end ModularFormsKB.Historical.Ramanujan
