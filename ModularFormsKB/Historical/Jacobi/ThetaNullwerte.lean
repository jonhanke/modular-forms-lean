import ModularFormsKB.Historical.Weber.ThetaDuplication
import ModularFormsKB.Historical.Jacobi.ThetaIdentification
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Gauss
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Monotonicity
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import ModularFormsKB.Citation
/-!
# Jacobi's theta constants through the complete integral: `ϑ₃² = 2K/π`

Jacobi, *Fundamenta nova* (1829), § 63, p. 180 and § 65, p. 184 (and § 36, pp. 87–90, in product form). For
`0 < k < 1`, with `K = K(k)`, `K' = K(√(1 - k²))` and the nome `q = e^{-πK'/K}`,

  `√(2K/π) = 1 + 2q + 2q⁴ + 2q⁹ + ⋯`,  `√(2kK/π) = 2q^{1/4} + 2q^{9/4} + ⋯`,  `√(2k'K/π) = 1 - 2q + 2q⁴ - ⋯`,

that is `ϑ₃² = 2K/π`, `ϑ₂² = 2kK/π`, `ϑ₄² = 2k'K/π`; in Jacobi's notation `Θ(0) = √(2k'K/π)`, `Θ(K) = √(2K/π)`,
`H(K) = √(2kK/π)`.

## The proof (not Jacobi's)

Jacobi obtains these from his analytic theory of `Θ` and `H` (the theta functions as functions of `u`), which is not
available (`ThetaIdentification.lean`, loose end LE-MF-0190). We use instead Gauss's route through the
arithmetic–geometric mean. For `y > 0` put `q = e^{-πy}` and let `ϑ₃(y)`, `ϑ₄(y)`, `ϑ₂(y)` be the three real theta
series (`thetaNull3`, `thetaNull4`, `thetaNull2`).

1. The duplication formulas (`Weber.thetaDuplication`) say that `aₙ = ϑ₃(2ⁿy)²`, `bₙ = ϑ₄(2ⁿy)²` is the
   arithmetic–geometric sequence of `(a₀, b₀)`: `aₙ₊₁ = (aₙ + bₙ)/2`, `bₙ₊₁ = √(aₙbₙ)`.
2. `ϑ₃(t) → 1` as `t → ∞` (Mathlib's `norm_jacobiTheta_sub_one_le`), so `M(ϑ₃², ϑ₄²) = 1`.
3. With `k = ϑ₂²/ϑ₃²`, Jacobi's quartic identity (`Weber.jacobiQuartic`) gives `k' = √(1 - k²) = ϑ₄²/ϑ₃²`, and Gauss's
   theorem `K(k) = π/(2 M(1, k'))` (Tau Ceti's `TauCeti.Real.legendreK_eq_pi_div_two_mul_agm`) gives
   `K(k) = π ϑ₃²/2`.
4. The imaginary transformation `ϑ₃(1/y)² = y ϑ₃(y)²`, `ϑ₂(1/y)² = y ϑ₄(y)²` (Mathlib's
   `jacobiTheta₂_functional_equation`) gives `k(1/y) = k'(y)`, hence `K'(k) = K(k(1/y)) = y K(k)`: the nome of the
   modulus `k(y)` is `e^{-πy}`.
5. `k ↦ K'/K` is strictly decreasing on `(0, 1)` (Tau Ceti's `strictMonoOn_legendreK`), so every modulus
   `0 < k < 1` is `k(y)` for `y = K'/K`: this is Jacobi's statement.
-/

noncomputable section

open Complex Filter Topology TauCeti.Real
open scoped Real NNReal

namespace ModularFormsKB.Historical.Jacobi

open ModularFormsKB.Historical.Weber (weberTheta00 weberTheta01 weberTheta10)

/-- `ϑ₃ = ∑_{n ∈ ℤ} q^{n²}` at `q = e^{-πy}`. -/
def thetaNull3 (y : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * y)

/-- `ϑ₄ = ∑_{n ∈ ℤ} (-1)ⁿ q^{n²}` at `q = e^{-πy}`. -/
def thetaNull4 (y : ℝ) : ℝ := ∑' n : ℤ, (-1 : ℝ) ^ n * Real.exp (-π * (n : ℝ) ^ 2 * y)

/-- `ϑ₂ = ∑_{n ∈ ℤ} q^{(n + 1/2)²} = 2q^{1/4}(1 + q² + q⁶ + ⋯)` at `q = e^{-πy}`. -/
def thetaNull2 (y : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * y)

/-- Jacobi's modulus as a function of `y` (nome `q = e^{-πy}`): `k = ϑ₂²/ϑ₃²`. -/
def jacobiModulusOf (y : ℝ) : ℝ := thetaNull2 y ^ 2 / thetaNull3 y ^ 2

section Series

variable {y : ℝ}

lemma im_I_mul_ofReal_pos (hy : 0 < y) : 0 < (I * (y : ℂ)).im := by simpa using hy

lemma summable_and_weberTheta00 (hy : 0 < y) :
    Summable (fun n : ℤ ↦ Real.exp (-π * (n : ℝ) ^ 2 * y)) ∧
      weberTheta00 (I * y) = thetaNull3 y := by
  have h := hasSum_jacobiTheta₂_term 0 (im_I_mul_ofReal_pos hy)
  have hterm : (fun n : ℤ ↦ jacobiTheta₂_term n 0 (I * y)) =
      fun n : ℤ ↦ ((Real.exp (-π * (n : ℝ) ^ 2 * y) : ℝ) : ℂ) := by
    funext n
    rw [jacobiTheta₂_term, Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hterm] at h
  have hs : Summable (fun n : ℤ ↦ Real.exp (-π * (n : ℝ) ^ 2 * y)) :=
    Complex.summable_ofReal.mp h.summable
  refine ⟨hs, ?_⟩
  exact (h.unique (Complex.hasSum_ofReal.mpr hs.hasSum)).symm ▸ rfl

lemma summable_and_weberTheta01 (hy : 0 < y) :
    Summable (fun n : ℤ ↦ (-1 : ℝ) ^ n * Real.exp (-π * (n : ℝ) ^ 2 * y)) ∧
      weberTheta01 (I * y) = thetaNull4 y := by
  have h := hasSum_jacobiTheta₂_term (1 / 2) (im_I_mul_ofReal_pos hy)
  have hterm : (fun n : ℤ ↦ jacobiTheta₂_term n (1 / 2) (I * y)) =
      fun n : ℤ ↦ (((-1 : ℝ) ^ n * Real.exp (-π * (n : ℝ) ^ 2 * y) : ℝ) : ℂ) := by
    funext n
    rw [jacobiTheta₂_term, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_zpow,
      Complex.ofReal_neg, Complex.ofReal_one]
    have h1 : (2 * π * I * n * (1 / 2) + π * I * n ^ 2 * (I * y) : ℂ) =
        n * (π * I) + ((-π * (n : ℝ) ^ 2 * y : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [hterm] at h
  have hs := Complex.summable_ofReal.mp h.summable
  refine ⟨hs, ?_⟩
  exact (h.unique (Complex.hasSum_ofReal.mpr hs.hasSum)).symm ▸ rfl

lemma summable_and_weberTheta10 (hy : 0 < y) :
    Summable (fun n : ℤ ↦ Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * y)) ∧
      weberTheta10 (I * y) = thetaNull2 y := by
  have h := (hasSum_jacobiTheta₂_term (I * y / 2) (im_I_mul_ofReal_pos hy)).mul_left
    (cexp (π * I * (I * y) / 4))
  have hterm : (fun n : ℤ ↦ cexp (π * I * (I * y) / 4) * jacobiTheta₂_term n (I * y / 2) (I * y)) =
      fun n : ℤ ↦ ((Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * y) : ℝ) : ℂ) := by
    funext n
    rw [jacobiTheta₂_term, ← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hterm] at h
  have hs := Complex.summable_ofReal.mp h.summable
  refine ⟨hs, ?_⟩
  exact (h.unique (Complex.hasSum_ofReal.mpr hs.hasSum)).symm ▸ rfl

lemma weberTheta00_I_mul (hy : 0 < y) : weberTheta00 (I * y) = thetaNull3 y :=
  (summable_and_weberTheta00 hy).2

lemma weberTheta01_I_mul (hy : 0 < y) : weberTheta01 (I * y) = thetaNull4 y :=
  (summable_and_weberTheta01 hy).2

lemma weberTheta10_I_mul (hy : 0 < y) : weberTheta10 (I * y) = thetaNull2 y :=
  (summable_and_weberTheta10 hy).2

lemma thetaNull3_pos (hy : 0 < y) : 0 < thetaNull3 y :=
  (summable_and_weberTheta00 hy).1.tsum_pos (fun _ ↦ (Real.exp_pos _).le) 0 (Real.exp_pos _)

lemma thetaNull2_pos (hy : 0 < y) : 0 < thetaNull2 y :=
  (summable_and_weberTheta10 hy).1.tsum_pos (fun _ ↦ (Real.exp_pos _).le) 0 (Real.exp_pos _)

end Series

section Identities

variable {y : ℝ}

lemma two_mul_I_mul (y : ℝ) : 2 * (I * (y : ℂ)) = I * ((2 * y : ℝ) : ℂ) := by push_cast; ring

/-- The duplication formulas for the real theta constants. -/
lemma thetaNull_duplication (hy : 0 < y) :
    thetaNull3 y ^ 2 + thetaNull4 y ^ 2 = 2 * thetaNull3 (2 * y) ^ 2 ∧
      thetaNull3 y * thetaNull4 y = thetaNull4 (2 * y) ^ 2 := by
  obtain ⟨h1, h2, -⟩ := Weber.thetaDuplication (I * y) (im_I_mul_ofReal_pos hy)
  have hy2 : 0 < 2 * y := by linarith
  rw [two_mul_I_mul, weberTheta00_I_mul hy, weberTheta01_I_mul hy, weberTheta00_I_mul hy2] at h1
  rw [two_mul_I_mul, weberTheta00_I_mul hy, weberTheta01_I_mul hy, weberTheta01_I_mul hy2] at h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- Jacobi's quartic identity for the real theta constants. -/
lemma thetaNull_quartic (hy : 0 < y) :
    thetaNull3 y ^ 4 = thetaNull4 y ^ 4 + thetaNull2 y ^ 4 := by
  have h := Weber.jacobiQuartic (I * y) (im_I_mul_ofReal_pos hy)
  rw [weberTheta00_I_mul hy, weberTheta01_I_mul hy, weberTheta10_I_mul hy] at h
  exact_mod_cast h

lemma thetaNull4_nonneg (hy : 0 < y) : 0 ≤ thetaNull4 y := by
  have h := (thetaNull_duplication hy).2
  have h3 := thetaNull3_pos hy
  by_contra hneg
  push Not at hneg
  have : thetaNull3 y * thetaNull4 y < 0 := mul_neg_of_pos_of_neg h3 hneg
  nlinarith [sq_nonneg (thetaNull4 (2 * y))]

lemma neg_one_div_I_mul {y : ℝ} (hy : 0 < y) : -1 / (I * (y : ℂ)) = I * ((1 / y : ℝ) : ℂ) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp
  simp [I_sq]

lemma sqrt_cpow_sq {y : ℝ} : ((-I * (I * (y : ℂ))) ^ (1 / 2 : ℂ)) ^ 2 = y := by
  rw [show -I * (I * (y : ℂ)) = y by ring_nf; rw [I_sq]; ring, one_div]
  exact Complex.cpow_ofNat_inv_pow (y : ℂ) 2

/-- The imaginary transformation of `ϑ₃`: `ϑ₃(1/y)² = y ϑ₃(y)²`. -/
lemma thetaNull3_inv_sq (hy : 0 < y) : thetaNull3 (1 / y) ^ 2 = y * thetaNull3 y ^ 2 := by
  have h := jacobiTheta₂_functional_equation 0 (I * y)
  have hy1 : 0 < 1 / y := by positivity
  rw [zero_div, neg_one_div_I_mul hy] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Complex.exp_zero, mul_one] at h
  have h0 : (thetaNull3 y : ℂ) = 1 / (-I * (I * y)) ^ (1 / 2 : ℂ) * thetaNull3 (1 / y) := by
    rw [← weberTheta00_I_mul hy, ← weberTheta00_I_mul hy1]
    exact h
  have hc : ((-I * (I * (y : ℂ))) ^ (1 / 2 : ℂ)) ≠ 0 := by
    intro h'
    have := sqrt_cpow_sq (y := y)
    rw [h'] at this
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    exact hy' (by rw [← this]; ring)
  have h2 : ((thetaNull3 (1 / y) : ℝ) : ℂ) ^ 2 = y * (thetaNull3 y : ℂ) ^ 2 := by
    rw [h0, div_mul_eq_mul_div, one_mul, div_pow, sqrt_cpow_sq]
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    field_simp
  exact_mod_cast h2

/-- The imaginary transformation exchanging `ϑ₄` and `ϑ₂`: `ϑ₂(1/y)² = y ϑ₄(y)²`. -/
lemma thetaNull2_inv_sq (hy : 0 < y) : thetaNull2 (1 / y) ^ 2 = y * thetaNull4 y ^ 2 := by
  have h := jacobiTheta₂_functional_equation (1 / 2) (I * y)
  have hy1 : 0 < 1 / y := by positivity
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [neg_one_div_I_mul hy] at h
  have h10 := weberTheta10_I_mul hy1
  rw [Weber.weberTheta10] at h10
  have harg : (1 / 2 : ℂ) / (I * y) = -(I * ((1 / y : ℝ) : ℂ) / 2) := by
    push_cast
    field_simp
    simp [I_sq]
  have hexp : cexp (-π * I * (1 / 2) ^ 2 / (I * y)) = cexp (π * I * (I * ((1 / y : ℝ) : ℂ)) / 4) := by
    congr 1
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [harg, jacobiTheta₂_neg_left, hexp, mul_assoc, h10] at h
  have h0 : (thetaNull4 y : ℂ) = 1 / (-I * (I * y)) ^ (1 / 2 : ℂ) * thetaNull2 (1 / y) := by
    rw [← weberTheta01_I_mul hy]
    exact h
  have hc : ((-I * (I * (y : ℂ))) ^ (1 / 2 : ℂ)) ≠ 0 := by
    intro h'
    have := sqrt_cpow_sq (y := y)
    rw [h'] at this
    exact hy' (by rw [← this]; ring)
  have h2 : ((thetaNull2 (1 / y) : ℝ) : ℂ) ^ 2 = y * (thetaNull4 y : ℂ) ^ 2 := by
    rw [h0, div_mul_eq_mul_div, one_mul, div_pow, sqrt_cpow_sq]
    field_simp
  exact_mod_cast h2

/-- `ϑ₃(t) → 1` as `t → ∞`. -/
lemma tendsto_thetaNull3 : Tendsto thetaNull3 atTop (𝓝 1) := by
  have hE : Tendsto (fun t : ℝ ↦ Real.exp (-π * t)) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ ↦ π * t) atTop atTop := tendsto_id.const_mul_atTop Real.pi_pos
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).congr fun t ↦ ?_
    simp [neg_mul]
  have hB : Tendsto (fun t : ℝ ↦ 2 / (1 - Real.exp (-π * t)) * Real.exp (-π * t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ ↦ 1 - Real.exp (-π * t)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hE
    have := ((tendsto_const_nhds (x := (2 : ℝ))).div h1 (by norm_num)).mul hE
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hB
  filter_upwards [eventually_gt_atTop 0] with t ht
  have h := norm_jacobiTheta_sub_one_le (im_I_mul_ofReal_pos ht)
  rw [jacobiTheta_eq_jacobiTheta₂, ← Weber.weberTheta00, weberTheta00_I_mul ht] at h
  simp only [mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul, zero_add] at h
  have he : ‖((thetaNull3 t : ℝ) : ℂ) - 1‖ = |thetaNull3 t - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [norm_norm, Real.norm_eq_abs, ← he]
  exact h

end Identities

section AGM

variable {y : ℝ}

/-- `aₙ = ϑ₃(2ⁿy)²` as a non-negative real. -/
def agmA (y : ℝ) (n : ℕ) : ℝ≥0 := (thetaNull3 (2 ^ n * y) ^ 2).toNNReal

/-- `bₙ = ϑ₄(2ⁿy)²` as a non-negative real. -/
def agmB (y : ℝ) (n : ℕ) : ℝ≥0 := (thetaNull4 (2 ^ n * y) ^ 2).toNNReal

lemma agm_step (hy : 0 < y) (n : ℕ) :
    NNReal.sqrt (agmA y n * agmB y n) = agmB y (n + 1) ∧
      (agmA y n + agmB y n) / 2 = agmA y (n + 1) := by
  have hyn : 0 < 2 ^ n * y := by positivity
  obtain ⟨h1, h2⟩ := thetaNull_duplication hyn
  rw [show 2 * (2 ^ n * y) = 2 ^ (n + 1) * y by ring] at h1 h2
  constructor
  · apply NNReal.eq
    rw [Real.coe_sqrt, NNReal.coe_mul, agmA, agmB, agmB, Real.coe_toNNReal _ (sq_nonneg _),
      Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ (sq_nonneg _), ← mul_pow, h2,
      Real.sqrt_sq (sq_nonneg _)]
  · apply NNReal.eq
    rw [NNReal.coe_div, NNReal.coe_add, agmA, agmB, agmA, Real.coe_toNNReal _ (sq_nonneg _),
      Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ (sq_nonneg _), h1]
    push_cast
    ring

lemma agmSequences_eq (hy : 0 < y) (n : ℕ) :
    NNReal.agmSequences (agmA y 0) (agmB y 0) n = (agmB y (n + 1), agmA y (n + 1)) := by
  induction n with
  | zero =>
    rw [NNReal.agmSequences_zero, (agm_step hy 0).1, (agm_step hy 0).2]
  | succ n ih =>
    rw [NNReal.agmSequences_succ', ih]
    dsimp only
    rw [mul_comm (agmB y (n + 1)), add_comm (agmB y (n + 1)), (agm_step hy (n + 1)).1,
      (agm_step hy (n + 1)).2]

/-- **Gauss**: the arithmetic–geometric mean of `ϑ₃²` and `ϑ₄²` is `1`. -/
lemma agm_thetaNull (hy : 0 < y) : NNReal.agm (agmA y 0) (agmB y 0) = 1 := by
  have h1 := NNReal.tendsto_agmSequences_snd_agm (x := agmA y 0) (y := agmB y 0)
  simp_rw [agmSequences_eq hy] at h1
  have h2 : Tendsto (fun n : ℕ ↦ agmA y (n + 1)) atTop (𝓝 1) := by
    rw [← NNReal.tendsto_coe]
    have hpow : Tendsto (fun n : ℕ ↦ 2 ^ (n + 1) * y) atTop atTop :=
      ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)).atTop_mul_const hy
    have := ((tendsto_thetaNull3.comp hpow).pow 2)
    simp only [one_pow] at this
    refine this.congr fun n ↦ ?_
    simp [agmA, Real.coe_toNNReal _ (sq_nonneg _)]
  exact tendsto_nhds_unique h1 h2

end AGM

section Main

variable {y : ℝ}

lemma thetaNull4_ne_zero (hy : 0 < y) : thetaNull4 y ≠ 0 := by
  intro h0
  have h := agm_thetaNull hy
  have hb : agmB y 0 = 0 := by simp [agmB, h0]
  rw [hb, NNReal.agm_zero_right] at h
  exact zero_ne_one h

lemma thetaNull4_pos (hy : 0 < y) : 0 < thetaNull4 y :=
  lt_of_le_of_ne (thetaNull4_nonneg hy) (thetaNull4_ne_zero hy).symm

lemma jacobiModulusOf_pos (hy : 0 < y) : 0 < jacobiModulusOf y := by
  unfold jacobiModulusOf
  have := thetaNull2_pos hy
  have := thetaNull3_pos hy
  positivity

/-- `1 - k² = (ϑ₄²/ϑ₃²)²`, from Jacobi's quartic identity. -/
lemma one_sub_jacobiModulusOf_sq (hy : 0 < y) :
    1 - jacobiModulusOf y ^ 2 = (thetaNull4 y ^ 2 / thetaNull3 y ^ 2) ^ 2 := by
  have h3 := (thetaNull3_pos hy).ne'
  have hq := thetaNull_quartic hy
  unfold jacobiModulusOf
  field_simp
  linear_combination hq

lemma jacobiModulusOf_lt_one (hy : 0 < y) : jacobiModulusOf y < 1 := by
  have h := one_sub_jacobiModulusOf_sq hy
  have h4 : 0 < (thetaNull4 y ^ 2 / thetaNull3 y ^ 2) ^ 2 := by
    have := thetaNull4_ne_zero hy
    have := (thetaNull3_pos hy).ne'
    positivity
  have hk := jacobiModulusOf_pos hy
  nlinarith

lemma sqrt_one_sub_jacobiModulusOf_sq (hy : 0 < y) :
    √(1 - jacobiModulusOf y ^ 2) = thetaNull4 y ^ 2 / thetaNull3 y ^ 2 := by
  rw [one_sub_jacobiModulusOf_sq hy, Real.sqrt_sq (by positivity)]

/-- `ϑ₃² = 2K(k)/π` with `k = ϑ₂²/ϑ₃²`. -/
lemma thetaNull3_sq_eq (hy : 0 < y) :
    thetaNull3 y ^ 2 = 2 * legendreK (jacobiModulusOf y) / π := by
  have h3 := thetaNull3_pos hy
  have hk2 : jacobiModulusOf y ^ 2 < 1 := by
    have := jacobiModulusOf_pos hy
    have := jacobiModulusOf_lt_one hy
    nlinarith
  have hG := legendreK_eq_pi_div_two_mul_agm hk2
  rw [sqrt_one_sub_jacobiModulusOf_sq hy] at hG
  -- `M(ϑ₃², ϑ₄²) = ϑ₃² M(1, ϑ₄²/ϑ₃²) = 1`
  have hagm := agm_thetaNull hy
  set c : ℝ≥0 := (thetaNull4 y ^ 2 / thetaNull3 y ^ 2).toNNReal with hc
  have hA : agmA y 0 = agmA y 0 * 1 := (mul_one _).symm
  have hB : agmB y 0 = agmA y 0 * c := by
    apply NNReal.eq
    simp only [agmA, agmB, pow_zero, one_mul, NNReal.coe_mul, hc]
    rw [Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ (sq_nonneg _),
      Real.coe_toNNReal _ (by positivity)]
    field_simp
  rw [hB, hA, mul_assoc, one_mul, NNReal.agm_mul_distrib] at hagm
  have hagm' : ((NNReal.agm 1 c : ℝ≥0) : ℝ) = 1 / thetaNull3 y ^ 2 := by
    have := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hagm
    simp only [NNReal.coe_mul, NNReal.coe_one, agmA, pow_zero, one_mul,
      Real.coe_toNNReal _ (sq_nonneg _)] at this
    field_simp
    linarith
  rw [hG, hagm']
  field_simp

/-- The nome of `k(y)` is `e^{-πy}`: `K'(k)/K(k) = y`. -/
lemma legendreK'_div_legendreK (hy : 0 < y) :
    legendreK' (jacobiModulusOf y) / legendreK (jacobiModulusOf y) = y := by
  have hy1 : 0 < 1 / y := by positivity
  have hmod : √(1 - jacobiModulusOf y ^ 2) = jacobiModulusOf (1 / y) := by
    rw [sqrt_one_sub_jacobiModulusOf_sq hy, jacobiModulusOf, thetaNull2_inv_sq hy, thetaNull3_inv_sq hy]
    field_simp
  have hK : legendreK (jacobiModulusOf y) = π * thetaNull3 y ^ 2 / 2 := by
    rw [thetaNull3_sq_eq hy]; field_simp
  have hK' : legendreK (jacobiModulusOf (1 / y)) = π * thetaNull3 (1 / y) ^ 2 / 2 := by
    rw [thetaNull3_sq_eq hy1]; field_simp
  rw [legendreK', hmod, hK', hK, thetaNull3_inv_sq hy]
  have := (thetaNull3_pos hy).ne'
  field_simp

/-- `K'/K` is strictly decreasing in the modulus on `(0, 1)`. -/
lemma strictAntiOn_legendreK'_div : StrictAntiOn (fun k ↦ legendreK' k / legendreK k) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  have hKa : 0 < legendreK a := legendreK_pos (by nlinarith [ha.1, ha.2])
  have hKb : 0 < legendreK b := legendreK_pos (by nlinarith [hb.1, hb.2])
  have hlt : legendreK a < legendreK b :=
    strictMonoOn_legendreK ⟨ha.1.le, ha.2⟩ ⟨hb.1.le, hb.2⟩ hab
  have hsa : √(1 - a ^ 2) ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, by rw [Real.sqrt_lt' one_pos]; nlinarith [ha.1]⟩
  have hsb : √(1 - b ^ 2) ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, by rw [Real.sqrt_lt' one_pos]; nlinarith [hb.1]⟩
  have hs : √(1 - b ^ 2) < √(1 - a ^ 2) :=
    Real.sqrt_lt_sqrt (by nlinarith [hb.1, hb.2]) (by nlinarith [ha.1, hb.1])
  have hlt' : legendreK' b < legendreK' a := strictMonoOn_legendreK hsb hsa hs
  have hK'b : 0 < legendreK' b := legendreK_pos (by rw [Real.sq_sqrt (by nlinarith [hb.1, hb.2])]; nlinarith [hb.1])
  show legendreK' b / legendreK b < legendreK' a / legendreK a
  rw [div_lt_div_iff₀ hKb hKa]
  nlinarith

/-- **Jacobi's theta constants** (*Fundamenta nova* § 63, p. 180; § 65, p. 184),
in the nome `q = e^{-πy}`, `y > 0`: the modulus `k = ϑ₂²/ϑ₃²` lies in `(0, 1)`, its complement is
`k' = √(1 - k²) = ϑ₄²/ϑ₃²`, its nome is `q` (`K'/K = y`), and `ϑ₃² = 2K/π`, `ϑ₂² = 2kK/π`, `ϑ₄² = 2k'K/π`. -/
@[kb "jacobi1829" "§ 63, p. 180; § 65, p. 184"]
theorem jacobiThetaConstants (hy : 0 < y) :
    0 < jacobiModulusOf y ∧ jacobiModulusOf y < 1 ∧
      √(1 - jacobiModulusOf y ^ 2) = thetaNull4 y ^ 2 / thetaNull3 y ^ 2 ∧
      legendreK' (jacobiModulusOf y) / legendreK (jacobiModulusOf y) = y ∧
      thetaNull3 y ^ 2 = 2 * legendreK (jacobiModulusOf y) / π ∧
      thetaNull2 y ^ 2 = 2 * jacobiModulusOf y * legendreK (jacobiModulusOf y) / π ∧
      thetaNull4 y ^ 2 = 2 * √(1 - jacobiModulusOf y ^ 2) * legendreK (jacobiModulusOf y) / π := by
  have h3 := (thetaNull3_pos hy).ne'
  have hK := thetaNull3_sq_eq hy
  refine ⟨jacobiModulusOf_pos hy, jacobiModulusOf_lt_one hy, sqrt_one_sub_jacobiModulusOf_sq hy,
    legendreK'_div_legendreK hy, hK, ?_, ?_⟩
  · rw [show 2 * jacobiModulusOf y * legendreK (jacobiModulusOf y) / π =
        jacobiModulusOf y * (2 * legendreK (jacobiModulusOf y) / π) by ring, ← hK, jacobiModulusOf]
    field_simp
  · rw [show 2 * √(1 - jacobiModulusOf y ^ 2) * legendreK (jacobiModulusOf y) / π =
        √(1 - jacobiModulusOf y ^ 2) * (2 * legendreK (jacobiModulusOf y) / π) by ring, ← hK,
      sqrt_one_sub_jacobiModulusOf_sq hy]
    field_simp

/-- **Jacobi's theta constants, given the modulus** (*Fundamenta nova* § 63, p. 180; § 65, p. 184): for `0 < k < 1`, at the nome `q = e^{-πK'/K}`,
`√(2K/π) = ϑ₃ = 1 + 2q + 2q⁴ + ⋯`, `√(2kK/π) = ϑ₂ = 2q^{1/4} + 2q^{9/4} + ⋯`,
`√(2k'K/π) = ϑ₄ = 1 - 2q + 2q⁴ - ⋯`; and `k = ϑ₂²/ϑ₃²`. -/
@[kb "jacobi1829" "§ 63, p. 180; § 65, p. 184"]
theorem jacobiThetaConstantsOfModulus {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    jacobiModulusOf (legendreK' k / legendreK k) = k ∧
      thetaNull3 (legendreK' k / legendreK k) = √(2 * legendreK k / π) ∧
      thetaNull2 (legendreK' k / legendreK k) = √(2 * k * legendreK k / π) ∧
      thetaNull4 (legendreK' k / legendreK k) = √(2 * √(1 - k ^ 2) * legendreK k / π) := by
  set y := legendreK' k / legendreK k with hydef
  have hK : 0 < legendreK k := legendreK_pos (by nlinarith)
  have hK' : 0 < legendreK' k :=
    legendreK_pos (by rw [Real.sq_sqrt (by nlinarith)]; nlinarith)
  have hy : 0 < y := div_pos hK' hK
  obtain ⟨hp, hl, -, hrat, h3, h2, h4⟩ := jacobiThetaConstants hy
  have hkk : jacobiModulusOf y = k :=
    strictAntiOn_legendreK'_div.injOn ⟨hp, hl⟩ ⟨hk0, hk1⟩ (by rw [hrat])
  rw [hkk] at h3 h2 h4
  refine ⟨hkk, ?_, ?_, ?_⟩
  · rw [← h3, Real.sqrt_sq (thetaNull3_pos hy).le]
  · rw [← h2, Real.sqrt_sq (thetaNull2_pos hy).le]
  · rw [← h4, Real.sqrt_sq (thetaNull4_pos hy).le]

/-- **Jacobi's normalisation of `Θ` and `H`** (*Fundamenta nova* § 63, p. 180 and § 65, p. 184): for `0 < k < 1`, at `τ = iK'/K`, the theta series `Θ`, `H` of `ThetaFourier` (in Jacobi's variable
`x`, `u = 2Kx/π`) satisfy `Θ(0) = √(2k'K/π)`, `Θ(K) = √(2K/π)` and `H(K) = √(2kK/π)` (the values at `u = 0`, `K`
are those at `x = 0`, `π/2`). -/
@[kb "jacobi1829" "§ 63, p. 180; § 65, p. 184"]
theorem jacobiThetaNormalisation {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    jacobiΘ 0 (jacobiTau k) = ((√(2 * √(1 - k ^ 2) * legendreK k / π) : ℝ) : ℂ) ∧
      jacobiΘ (π / 2) (jacobiTau k) = ((√(2 * legendreK k / π) : ℝ) : ℂ) ∧
      jacobiH (π / 2) (jacobiTau k) = ((√(2 * k * legendreK k / π) : ℝ) : ℂ) := by
  obtain ⟨-, h3, h2, h4⟩ := jacobiThetaConstantsOfModulus hk0 hk1
  have hK : 0 < legendreK k := legendreK_pos (by nlinarith)
  have hK' : 0 < legendreK' k :=
    legendreK_pos (by rw [Real.sq_sqrt (by nlinarith)]; nlinarith)
  have hy : 0 < legendreK' k / legendreK k := div_pos hK' hK
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [← h4, ← weberTheta01_I_mul hy, jacobiΘ, jacobiTau, Weber.weberTheta01, zero_div, zero_add]
  · rw [← h3, ← weberTheta00_I_mul hy, jacobiΘ, jacobiTau, Weber.weberTheta00,
      show (π / 2 : ℂ) / π + 1 / 2 = 0 + 1 by field_simp; ring, jacobiTheta₂_add_left]
  · rw [← h2, ← weberTheta10_I_mul hy, jacobiH, jacobiTau, Weber.weberTheta10]
    set τ := I * ((legendreK' k / legendreK k : ℝ) : ℂ)
    rw [show (π / 2 : ℂ) / π + 1 / 2 + τ / 2 = τ / 2 + 1 by field_simp; ring, jacobiTheta₂_add_left,
      Complex.exp_add, show I * (π / 2 : ℂ) = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]
    ring_nf
    rw [I_sq]
    ring

end Main

end ModularFormsKB.Historical.Jacobi
