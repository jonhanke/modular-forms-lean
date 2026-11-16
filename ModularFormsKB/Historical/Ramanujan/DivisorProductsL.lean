import ModularFormsKB.Historical.Ramanujan.DivisorProducts
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import ModularFormsKB.Citation
/-!
# Ramanujan's `∑ (-1)^{(n-1)/2} σ_a(n) σ_b(n) n^{-s}` over odd `n` (No. 17, (16) and (2))

Ramanujan, *Collected Papers*, No. 17, (I) (16), p. 135, and (A) (2), p. 133, with
`L(s) = 1 - 3^{-s} + 5^{-s} - 7^{-s} + ⋯` (his `η(s)`) and `σ_a(n) = ∑_{d ∣ n} d^a`:

  (16) `∑_{n odd} (-1)^{(n-1)/2} σ_a(n) σ_b(n) n^{-s} = L(s) L(s-a) L(s-b) L(s-a-b) / ((1 - 2^{a+b-2s}) ζ(2s-a-b))`,

  (2) `1^{-s} d(1)² - 3^{-s} d(3)² + 5^{-s} d(5)² - ⋯ = L(s)⁴ / ((1 - 2^{-2s}) ζ(2s))`.

Here `a`, `b`, `s` are complex with `Re s > 1 + max(0, Re a) + max(0, Re b)` (as for `SigmaSigmaZetaQuotient`).
The factor at `2` is `1 - 2^{a+b-2s}`; one reading of the printed exponent of (16) is `-2s-a+b`, which
agrees with this only for `a = 0` (recorded as a possible erratum). The proof is the Euler product of
`SigmaSigmaZetaQuotient` twisted by the character `χ₄` (`χ₄(p)² = 1` for odd `p`).
-/

noncomputable section

open Complex

namespace ModularFormsKB.Historical.Ramanujan

/-- The character `χ₄(n) = (-1)^{(n-1)/2}` for odd `n`, `0` for even `n`. -/
def chiFour (n : ℕ) : ℂ := if n % 2 = 1 then (-1) ^ ((n - 1) / 2) else 0

/-- Ramanujan's `L(s) = 1 - 3^{-s} + 5^{-s} - ⋯` (his `η(s)`, No. 17), for `Re s > 1`. -/
def ramanujanL (s : ℂ) : ℂ := ∑' n : ℕ, chiFour n * (n : ℂ) ^ (-s)

/-- **Ramanujan, No. 17, (I) (16)** (p. 135): for complex `a`, `b`, `s` with
`Re s > 1 + max(0, Re a) + max(0, Re b)`,
`∑ χ₄(n) σ_a(n) σ_b(n) n^{-s} = L(s) L(s-a) L(s-b) L(s-a-b) / ((1 - 2^{a+b-2s}) ζ(2s-a-b))`. -/
@[kb "ramanujan1927" "No. 17, (I), (16), p. 135"]
def ChiFourSigmaSigmaQuotient : Prop :=
  ∀ a b s : ℂ, 1 + max 0 a.re + max 0 b.re < s.re →
    HasSum (fun n : ℕ ↦ chiFour n * sigmaC a n * sigmaC b n * (n : ℂ) ^ (-s))
      (ramanujanL s * ramanujanL (s - a) * ramanujanL (s - b) * ramanujanL (s - a - b) /
        ((1 - (2 : ℂ) ^ (a + b - 2 * s)) * riemannZeta (2 * s - a - b)))

/-- **Ramanujan, No. 17, (A) (2)** (p. 133, the case `a = b = 0`): for `Re s > 1`,
`∑ χ₄(n) d(n)² n^{-s} = L(s)⁴ / ((1 - 2^{-2s}) ζ(2s))`. -/
@[kb "ramanujan1927" "No. 17, (A), (2), p. 133"]
def ChiFourDivisorSquareQuotient : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasSum (fun n : ℕ ↦ chiFour n * ((n.divisors.card : ℂ)) ^ 2 * (n : ℂ) ^ (-s))
      (ramanujanL s ^ 4 / ((1 - (2 : ℂ) ^ (-2 * s)) * riemannZeta (2 * s)))

open Finset

/-! ### Properties of `χ₄` -/

private lemma chiFour_eq (n : ℕ) : chiFour n = ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℂ) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  unfold chiFour
  by_cases h2 : n % 2 = 1
  · have h0 : ¬ n % 2 = 0 := by omega
    by_cases h4 : n % 4 = 1
    · have : Even ((n - 1) / 2) := ⟨(n - 1) / 4, by omega⟩
      simp [h2, h4, this.neg_one_pow]
    · have : Odd ((n - 1) / 2) := ⟨(n - 1) / 4, by omega⟩
      simp [h2, h4, this.neg_one_pow]
  · have : n % 2 = 0 := by omega
    simp [this]

private lemma chiFour_mul (m n : ℕ) : chiFour (m * n) = chiFour m * chiFour n := by
  rw [chiFour_eq, chiFour_eq, chiFour_eq, Nat.cast_mul, map_mul]
  push_cast
  rfl

private lemma chiFour_zero : chiFour 0 = 0 := by simp [chiFour]

private lemma chiFour_one : chiFour 1 = 1 := by simp [chiFour]

private lemma chiFour_two : chiFour 2 = 0 := by simp [chiFour]

private lemma chiFour_pow (p e : ℕ) : chiFour (p ^ e) = chiFour p ^ e := by
  induction e with
  | zero => simp [chiFour_one]
  | succ e ih => rw [pow_succ, chiFour_mul, ih, pow_succ]

private lemma norm_chiFour_le (n : ℕ) : ‖chiFour n‖ ≤ 1 := by
  unfold chiFour
  split_ifs
  · simp [norm_pow]
  · simp

private lemma chiFour_sq {n : ℕ} (h : n % 2 = 1) : chiFour n ^ 2 = 1 := by
  unfold chiFour
  simp only [h, ite_true]
  rw [← pow_mul, mul_comm, pow_mul]
  simp

private lemma norm_chi_mul_lt {c z : ℂ} (hc : ‖c‖ ≤ 1) (hz : ‖z‖ < 1) : ‖c * z‖ < 1 := by
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hc) hz

/-- `n ↦ χ₄(n) n^{-w}` as a monoid-with-zero homomorphism. -/
private def chiMon (w : ℂ) : ℕ →*₀ ℂ where
  toFun n := chiFour n * (n : ℂ) ^ (-w)
  map_zero' := by simp [chiFour_zero]
  map_one' := by simp [chiFour_one]
  map_mul' m n := by
    simp only [Nat.cast_mul, natCast_mul_natCast_cpow, chiFour_mul]
    ring

private lemma chiMon_summable {w : ℂ} (hw : 1 < w.re) : Summable fun n ↦ ‖chiMon w n‖ := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -w.re < -1)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · show ‖chiFour 0 * ((0 : ℕ) : ℂ) ^ (-w)‖ ≤ _
    rw [chiFour_zero, zero_mul, norm_zero]
    exact Real.rpow_nonneg (by simp) _
  · show ‖chiFour n * (n : ℂ) ^ (-w)‖ ≤ _
    rw [norm_mul, norm_natCast_cpow_of_pos hn, neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (norm_chiFour_le n)

/-! ### Copies of the private lemmas of `DivisorProducts` -/

private def powCL (a : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 0 then 0 else (n : ℂ) ^ a, by simp⟩

private lemma powCL_isMultiplicative (a : ℂ) : (powCL a).IsMultiplicative := by
  refine ⟨by simp [powCL], fun {m n} _ ↦ ?_⟩
  simp only [powCL, ArithmeticFunction.coe_mk]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp [hm, hn, natCast_mul_natCast_cpow]

private lemma sigmaCL_eq (a : ℂ) (n : ℕ) :
    sigmaC a n = ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * powCL a) n := by
  rw [ArithmeticFunction.coe_zeta_mul_apply, sigmaC]
  refine sum_congr rfl fun d hd ↦ ?_
  have : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  simp [powCL, this]

private lemma sigmaCL_mul {a : ℂ} {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaC a (m * n) = sigmaC a m * sigmaC a n := by
  rw [sigmaCL_eq, sigmaCL_eq, sigmaCL_eq]
  exact (ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (powCL_isMultiplicative a)).map_mul_of_coprime h

private lemma sigmaCL_prime_pow (a : ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    sigmaC a (p ^ e) = ∑ i ∈ range (e + 1), ((p : ℂ) ^ a) ^ i := by
  rw [sigmaC, Nat.divisors_prime_pow hp, sum_map]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [Function.Embedding.coeFn_mk]
  push_cast
  rw [← natCast_cpow_natCast_mul, cpow_nat_mul]

private lemma norm_sigmaCL_le (a : ℂ) (n : ℕ) :
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

/-- The untwisted summand `σ_a(n) σ_b(n) n^{-s}`. -/
private def FL (a b s : ℂ) (n : ℕ) : ℂ := sigmaC a n * sigmaC b n * (n : ℂ) ^ (-s)

private lemma FL_summable {a b s : ℂ} (hs : 1 + max 0 a.re + max 0 b.re < s.re) :
    Summable fun n ↦ ‖FL a b s n‖ := by
  set δ := s.re - 1 - max 0 a.re - max 0 b.re with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨C, hC0, hC⟩ := TauCeti.exists_pos_card_divisors_le_rpow (ε := δ / 4) (by positivity)
  have hsum : Summable fun n : ℕ ↦ C ^ 2 * (n : ℝ) ^ (-1 - δ / 2) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  refine hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [FL, sigmaC, Nat.divisors_zero, sum_empty, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := hC n
  have hdpos : (0 : ℝ) ≤ n.divisors.card := Nat.cast_nonneg _
  unfold FL
  rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hn, neg_re]
  calc ‖sigmaC a n‖ * ‖sigmaC b n‖ * (n : ℝ) ^ (-s.re)
      ≤ ((n.divisors.card : ℝ) * (n : ℝ) ^ max 0 a.re) *
          ((n.divisors.card : ℝ) * (n : ℝ) ^ max 0 b.re) * (n : ℝ) ^ (-s.re) := by
        gcongr
        · exact norm_sigmaCL_le a n
        · exact norm_sigmaCL_le b n
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

private lemma FL_mul (a b s : ℂ) {m n : ℕ} (h : Nat.Coprime m n) :
    FL a b s (m * n) = FL a b s m * FL a b s n := by
  unfold FL
  rw [sigmaCL_mul h, sigmaCL_mul h, Nat.cast_mul, natCast_mul_natCast_cpow]
  ring

private lemma norm_cpow_lt_oneL {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z.re < 0) :
    ‖(p : ℂ) ^ z‖ < 1 := by
  rw [norm_natCast_cpow_of_pos hp.pos]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) hz

private lemma cpow_add_pL {p : ℕ} (hp : p.Prime) (x y : ℂ) :
    (p : ℂ) ^ (x + y) = (p : ℂ) ^ x * (p : ℂ) ^ y :=
  cpow_add _ _ (by exact_mod_cast hp.ne_zero)

private lemma one_sub_neL {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, norm_one] at hz
  exact lt_irrefl _ hz

/-! ### The twisted Euler product -/

/-- The summand `χ₄(n) σ_a(n) σ_b(n) n^{-s}`. -/
private def CG (a b s : ℂ) (n : ℕ) : ℂ :=
  chiFour n * sigmaC a n * sigmaC b n * (n : ℂ) ^ (-s)

private lemma CG_eq (a b s : ℂ) (n : ℕ) : CG a b s n = chiFour n * FL a b s n := by
  unfold CG FL; ring

private lemma CG_summable {a b s : ℂ} (hs : 1 + max 0 a.re + max 0 b.re < s.re) :
    Summable fun n ↦ ‖CG a b s n‖ := by
  refine (FL_summable hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  rw [CG_eq, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_chiFour_le n)

/-- **Ramanujan, No. 17, (I) (16)**. Proof: Euler products; the local factor of
the twisted series is `local_hasSum` with `X` replaced by `χ₄(p) p^{-s}`; the factor at `2` is `1`, which
accounts for the factor `1 - 2^{a+b-2s}`. -/
@[kb "ramanujan1927" "No. 17, (I), (16), p. 135"]
theorem chiFourSigmaSigmaQuotient : ChiFourSigmaSigmaQuotient := by
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
  have hLp : ∀ w : ℂ, 1 < w.re → HasProd
      (fun p : Nat.Primes ↦ (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-w))⁻¹) (ramanujanL w) :=
    fun w hw ↦ EulerProduct.eulerProduct_completely_multiplicative_hasProd (f := chiMon w)
      (chiMon_summable hw)
  have hZ : HasProd (fun p : Nat.Primes ↦
      (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
        (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(s - a)))⁻¹ *
        (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(s - b)))⁻¹ *
        (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(s - a - b)))⁻¹ /
        (1 - ((p : ℕ) : ℂ) ^ (-(2 * s - a - b)))⁻¹)
      (ramanujanL s * ramanujanL (s - a) * ramanujanL (s - b) * ramanujanL (s - a - b) /
        riemannZeta (2 * s - a - b)) :=
    ((((hLp s hs1).mul (hLp _ hsa)).mul (hLp _ hsb)).mul (hLp _ hsab)).div₀
      (riemannZeta_eulerProduct_hasProd hs2) hne
  have hG1 : CG a b s 1 = 1 := by simp [CG, sigmaC, chiFour_one]
  have hG0 : CG a b s 0 = 0 := by simp [CG, sigmaC]
  have hGm : ∀ {m n : ℕ}, Nat.Coprime m n → CG a b s (m * n) = CG a b s m * CG a b s n := by
    intro m n h
    rw [CG_eq, CG_eq, CG_eq, FL_mul a b s h, chiFour_mul]
    ring
  have hE := EulerProduct.eulerProduct_hasProd hG1 hGm (CG_summable hs) hG0
  -- the correction factor at `2`
  let u : Nat.Primes → ℂ := fun p ↦
    if (p : ℕ) = 2 then 1 - ((p : ℕ) : ℂ) ^ (a + b - 2 * s) else 1
  have hu : HasProd u (1 - (2 : ℂ) ^ (a + b - 2 * s)) := by
    have := hasProd_single (f := u) (⟨2, Nat.prime_two⟩ : Nat.Primes) (by
      intro q hq
      have : (q : ℕ) ≠ 2 := fun h ↦ hq (Subtype.ext h)
      simp [u, this])
    simpa [u] using this
  have hc : (1 - (2 : ℂ) ^ (a + b - 2 * s)) ≠ 0 := by
    have : ‖(((2 : ℕ)) : ℂ) ^ (a + b - 2 * s)‖ < 1 :=
      norm_cpow_lt_oneL Nat.prime_two (by simp; linarith)
    simpa using one_sub_neL this
  have hE' := hE.mul hu
  have hfun : (fun p : Nat.Primes ↦ (∑' e, CG a b s ((p : ℕ) ^ e)) * u p) = fun p : Nat.Primes ↦
      (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ *
        (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(s - a)))⁻¹ *
        (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(s - b)))⁻¹ *
        (1 - chiFour (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(s - a - b)))⁻¹ /
        (1 - ((p : ℕ) : ℂ) ^ (-(2 * s - a - b)))⁻¹ := by
    funext p
    have hp := p.2
    set c := chiFour (p : ℕ) with hcdef
    have hcn : ‖c‖ ≤ 1 := norm_chiFour_le _
    set α := ((p : ℕ) : ℂ) ^ a
    set β := ((p : ℕ) : ℂ) ^ b
    set X := ((p : ℕ) : ℂ) ^ (-s)
    have h1 : ‖X‖ < 1 := norm_cpow_lt_oneL hp (by simp; linarith)
    have e2 : α * X = ((p : ℕ) : ℂ) ^ (a + -s) := (cpow_add_pL hp a (-s)).symm
    have e3 : β * X = ((p : ℕ) : ℂ) ^ (b + -s) := (cpow_add_pL hp b (-s)).symm
    have e4 : α * β * X = ((p : ℕ) : ℂ) ^ (a + b + -s) := by
      rw [cpow_add_pL hp, cpow_add_pL hp]
    have e5 : α * β * X ^ 2 = ((p : ℕ) : ℂ) ^ (a + b + -s + -s) := by
      rw [cpow_add_pL hp, cpow_add_pL hp, cpow_add_pL hp]; ring
    have h2 : ‖α * X‖ < 1 := by rw [e2]; exact norm_cpow_lt_oneL hp (by simp; linarith)
    have h3 : ‖β * X‖ < 1 := by rw [e3]; exact norm_cpow_lt_oneL hp (by simp; linarith)
    have h4 : ‖α * β * X‖ < 1 := by rw [e4]; exact norm_cpow_lt_oneL hp (by simp; linarith)
    have h5 : ‖α * β * X ^ 2‖ < 1 := by rw [e5]; exact norm_cpow_lt_oneL hp (by simp; linarith)
    have g1 : ‖c * X‖ < 1 := norm_chi_mul_lt hcn h1
    have g2 : ‖α * (c * X)‖ < 1 := by
      rw [show α * (c * X) = c * (α * X) by ring]; exact norm_chi_mul_lt hcn h2
    have g3 : ‖β * (c * X)‖ < 1 := by
      rw [show β * (c * X) = c * (β * X) by ring]; exact norm_chi_mul_lt hcn h3
    have g4 : ‖α * β * (c * X)‖ < 1 := by
      rw [show α * β * (c * X) = c * (α * β * X) by ring]; exact norm_chi_mul_lt hcn h4
    have hterm : ∀ e : ℕ, CG a b s ((p : ℕ) ^ e) =
        (∑ i ∈ range (e + 1), α ^ i) * (∑ j ∈ range (e + 1), β ^ j) * (c * X) ^ e := by
      intro e
      have hcp : (((p : ℕ) ^ e : ℕ) : ℂ) ^ (-s) = X ^ e := by
        push_cast
        rw [← natCast_cpow_natCast_mul, cpow_nat_mul]
      unfold CG
      rw [chiFour_pow, sigmaCL_prime_pow a hp, sigmaCL_prime_pow b hp, hcp, mul_pow]
      ring
    rw [tsum_congr hterm, (local_hasSum g1 g2 g3 g4).tsum_eq]
    rw [show -(s - a) = a + -s by ring, show -(s - b) = b + -s by ring,
      show -(s - a - b) = a + b + -s by ring, show -(2 * s - a - b) = a + b + -s + -s by ring,
      ← e2, ← e3, ← e4, ← e5]
    rw [show α * (c * X) = c * (α * X) by ring, show β * (c * X) = c * (β * X) by ring,
      show α * β * (c * X) = c * (α * β * X) by ring, show (c * X) ^ 2 = c ^ 2 * X ^ 2 by ring]
    rcases hp.eq_two_or_odd with h2p | hodd
    · have hc0 : c = 0 := by rw [hcdef, h2p, chiFour_two]
      have hu2 : u p = 1 - α * β * X ^ 2 := by
        simp only [u, h2p, ite_true]
        rw [e5, show a + b + -s + -s = a + b - 2 * s by ring, h2p]
      rw [hu2, hc0]
      simp
    · have hc2 : c ^ 2 = 1 := chiFour_sq hodd
      have hup : u p = 1 := by
        have : (p : ℕ) ≠ 2 := by omega
        simp [u, this]
      rw [hup, hc2, one_mul, mul_one]
      have n1 := one_sub_neL g1
      have n2 := one_sub_neL (show ‖c * (α * X)‖ < 1 by
        rw [← show α * (c * X) = c * (α * X) by ring]; exact g2)
      have n3 := one_sub_neL (show ‖c * (β * X)‖ < 1 by
        rw [← show β * (c * X) = c * (β * X) by ring]; exact g3)
      have n4 := one_sub_neL (show ‖c * (α * β * X)‖ < 1 by
        rw [← show α * β * (c * X) = c * (α * β * X) by ring]; exact g4)
      have n5 := one_sub_neL h5
      field_simp
  rw [hfun] at hE'
  have hval := hE'.unique hZ
  have hsum : HasSum (CG a b s) (∑' n, CG a b s n) := (CG_summable hs).of_norm.hasSum
  rw [eq_div_of_mul_eq hc hval, div_div, mul_comm (riemannZeta _)] at hsum
  exact hsum

/-- **Ramanujan, No. 17, (A) (2)**: the case `a = b = 0` of
`chiFourSigmaSigmaQuotient`. -/
@[kb "ramanujan1927" "No. 17, (A), (2), p. 133"]
theorem chiFourDivisorSquareQuotient : ChiFourDivisorSquareQuotient := by
  intro s hs
  have h := chiFourSigmaSigmaQuotient 0 0 s (by simpa using hs)
  have hd : ∀ n : ℕ, sigmaC 0 n = (n.divisors.card : ℂ) := fun n ↦ by simp [sigmaC]
  simp only [hd, sub_zero] at h
  convert h using 1
  · funext n; ring
  · rw [show (0 : ℂ) + 0 - 2 * s = -2 * s by ring]
    ring

end ModularFormsKB.Historical.Ramanujan
