import ModularFormsKB.Historical.Weber.ThetaEta
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weber's table of class invariants (first rows)

Weber, *Elliptische Functionen und algebraische Zahlen* (1891), Anhang, "Verzeichniss von
Classeninvarianten", pp. 499–504, and *Lehrbuch der Algebra* III (1908), Tabelle VI, pp. 721–726: about 105
values, for `m = 1, …, 1848`, of a power of `f(√-m)` or `f₁(√-m)` (times a power of 2), in radicals or as a root
of an equation over a small quadratic field.

This file states the first nine rows of Tabelle VI (p. 721), `m = 1, …, 9`, each as a named proposition, and
collects them in `WeberTableVIFirstRows`. Rows 1, 2 and 4 are proved here (`tableRow1`, `tableRow2`, `tableRow4`), and row 3 in `TableRow3.lean`
(`tableRow3`), using only Mathlib's `η` inversion formula, `η(z+1) = e^{2πi/24} η(z)` and Weber's `f f₁ f₂ = √2`. The other
rows are not proved: each is a special value of an `η`-quotient at a CM point, which needs either the theory of
complex multiplication (Weber's route: the value is a class invariant, a root of an explicit equation, located
numerically) or further explicit evaluations of `η` at CM points, none of which is in Mathlib. The rows have
been checked numerically from the `q`-products (agreement to `10⁻¹⁵`). The remaining ~96 rows of the table are
not transcribed (loose end).

The point `√-m` is `τ = i√m` in the upper half-plane; `f = weberF`, `f₁ = weberF₁`.
-/

noncomputable section

open Complex
open scoped Real

namespace ModularFormsKB.Historical.Weber

open ModularFormsKB.WeberHeegnerStark (weberF)

/-- The point `√-m = i√m` of the upper half-plane. -/
def sqrtNeg (m : ℕ) : ℂ := I * ((√(m : ℝ) : ℝ) : ℂ)

/-- Tabelle VI, `m = 1`: `f(√-1) = ⁴√2`. -/
@[kb "weber1908" "Tabelle VI, m = 1, p. 721"]
def TableRow1 : Prop := weberF (sqrtNeg 1) = ((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ)

/-- Tabelle VI, `m = 2`: `f₁(√-2) = ⁴√2`. -/
@[kb "weber1908" "Tabelle VI, m = 2, p. 721"]
def TableRow2 : Prop := weberF₁ (sqrtNeg 2) = ((2 : ℝ) ^ (1 / 4 : ℝ) : ℝ)

/-- Tabelle VI, `m = 3`: `f(√-3) = ∛2`. -/
@[kb "weber1908" "Tabelle VI, m = 3, p. 721"]
def TableRow3 : Prop := weberF (sqrtNeg 3) = ((2 : ℝ) ^ (1 / 3 : ℝ) : ℝ)

/-- Tabelle VI, `m = 4`: `f₁(√-4) = ⁸√8`. -/
@[kb "weber1908" "Tabelle VI, m = 4, p. 721"]
def TableRow4 : Prop := weberF₁ (sqrtNeg 4) = ((8 : ℝ) ^ (1 / 8 : ℝ) : ℝ)

/-- Tabelle VI, `m = 5`: `f(√-5)⁴ = 1 + √5`. -/
@[kb "weber1908" "Tabelle VI, m = 5, p. 721"]
def TableRow5 : Prop := weberF (sqrtNeg 5) ^ 4 = ((1 + √5 : ℝ) : ℂ)

/-- Tabelle VI, `m = 6`: `f₁(√-6)⁶ = 4 + 2√2`. -/
@[kb "weber1908" "Tabelle VI, m = 6, p. 721"]
def TableRow6 : Prop := weberF₁ (sqrtNeg 6) ^ 6 = ((4 + 2 * √2 : ℝ) : ℂ)

/-- Tabelle VI, `m = 7`: `f(√-7) = √2`. -/
@[kb "weber1908" "Tabelle VI, m = 7, p. 721"]
def TableRow7 : Prop := weberF (sqrtNeg 7) = ((√2 : ℝ) : ℂ)

/-- Tabelle VI, `m = 8`: `f₁(√-8)⁸ = 8 + 8√2`. -/
@[kb "weber1908" "Tabelle VI, m = 8, p. 721"]
def TableRow8 : Prop := weberF₁ (sqrtNeg 8) ^ 8 = ((8 + 8 * √2 : ℝ) : ℂ)

/-- Tabelle VI, `m = 9`: `f(√-9)³ = ⁴√2 (1 + √3)`. -/
@[kb "weber1908" "Tabelle VI, m = 9, p. 721"]
def TableRow9 : Prop := weberF (sqrtNeg 9) ^ 3 = (((2 : ℝ) ^ (1 / 4 : ℝ) * (1 + √3) : ℝ) : ℂ)

/-- **Weber's Tabelle VI, rows `m = 1, …, 9`** (Weber 1908, p. 721; Weber 1891, Anhang, p. 499), as a proposition. Stated, not proved. -/
@[kb "weber1908" "Tabelle VI, pp. 721–726"]
def WeberTableVIFirstRows : Prop :=
  TableRow1 ∧ TableRow2 ∧ TableRow3 ∧ TableRow4 ∧ TableRow5 ∧ TableRow6 ∧ TableRow7 ∧ TableRow8 ∧
    TableRow9

/-! ### Proofs of rows 1, 2 and 4

These three need only the inversion formula `η(-1/z)² = -iz η(z)²` (Mathlib, `eta_comp_eq_csqrt_I_inv`),
`η(z+1) = e^{2πi/24} η(z)`, and Weber's `q`-product identity `f f₁ f₂ = √2`; signs are fixed by the positivity
of the `q`-products at `q = e^{-πt} > 0`. -/

section Proofs

open ModularFormsKB.WeberHeegnerStark (weberF₂)

lemma csqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  unfold Complex.sqrt
  simp

/-- `η(-1/z)² = -i z η(z)²` on the upper half-plane (square of Mathlib's `eta_comp_eq_csqrt_I_inv`). -/
lemma eta_S_sq {z : ℂ} (hz : 0 < z.im) :
    ModularForm.eta (-1 / z) ^ 2 = -I * z * ModularForm.eta z ^ 2 := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv hz
  simp only [Function.comp, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  rw [h, mul_pow, mul_pow, inv_pow, csqrt_sq, csqrt_sq, Complex.inv_I]
  ring

/-- `η(z+1) = e^{2πi/24} η(z)`. -/
lemma eta_add_one (z : ℂ) :
    ModularForm.eta (z + 1) = cexp (2 * π * I / 24) * ModularForm.eta z := by
  have hp : cexp (2 * π * I * (z + 1)) = cexp (2 * π * I * z) := by
    rw [mul_add, mul_one, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hq : cexp (2 * π * I * (z + 1) / 24) = cexp (2 * π * I / 24) * cexp (2 * π * I * z / 24) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [eta_eq_cexp, eta_eq_cexp, hp, hq, mul_assoc]

/-- Euler: `∏ (1 - x^{2n+1}) · ∏ (1 + x^{n+1}) = 1`. -/
lemma euler_odd_mul {x : ℂ} (hx : ‖x‖ < 1) :
    (∏' n : ℕ, (1 - x ^ (2 * n + 1))) * ∏' n : ℕ, (1 + x ^ (n + 1)) = 1 := by
  have hAB := tprod_one_sub_mul_one_add hx
  have hAO := tprod_one_sub_pow_split hx
  have hE0 : ∏' n : ℕ, (1 - (x ^ 2) ^ (n + 1)) ≠ 0 :=
    Historical.Jacobi.eulerProd_ne_zero (norm_sq_lt_one hx)
  apply mul_left_cancel₀ hE0
  set A := ∏' n : ℕ, (1 - x ^ (n + 1))
  set B := ∏' n : ℕ, (1 + x ^ (n + 1))
  set O := ∏' n : ℕ, (1 - x ^ (2 * n + 1))
  set E := ∏' n : ℕ, (1 - (x ^ 2) ^ (n + 1))
  linear_combination hAB - B * hAO

/-- **Weber's `f f₁ f₂ = √2`** (Weber 1891, § 21), from the `q`-products. -/
lemma weber_triple {ω : ℂ} (hω : 0 < ω.im) :
    weberF ω * weberF₁ ω * weberF₂ ω = ((√2 : ℝ) : ℂ) := by
  obtain ⟨q, hq⟩ : ∃ q, q = cexp (π * I * ω) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = cexp (π * I * ω / 24) := ⟨_, rfl⟩
  have hqn : ‖q‖ < 1 := hq ▸ norm_cexp_pi_mul_lt_one hω
  have hs0 : s ≠ 0 := by rw [hs]; exact Complex.exp_ne_zero _
  rw [weberF_eq_q hω hq hs, weberF₁_eq_q hω hq hs, weberF₂_eq_q hω hq hs]
  have euler := euler_odd_mul (norm_sq_lt_one hqn)
  have hPP : (∏' n : ℕ, (1 + q ^ (2 * n + 1))) * ∏' n : ℕ, (1 - q ^ (2 * n + 1)) =
      ∏' n : ℕ, (1 - (q ^ 2) ^ (2 * n + 1)) := by
    rw [← (multipliable_one_add_pow_odd hqn).tprod_mul (multipliable_one_sub_pow_odd hqn)]
    exact tprod_congr fun n ↦ by ring
  calc _ = ((√2 : ℝ) : ℂ) * (((∏' n : ℕ, (1 + q ^ (2 * n + 1))) * ∏' n : ℕ, (1 - q ^ (2 * n + 1))) *
        ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) := by field_simp
    _ = _ := by rw [hPP, euler, mul_one]

/-- A convergent product of reals `≥ 1`, viewed in `ℂ`, is a real `≥ 1`. -/
lemma tprod_real_ge_one (b : ℕ → ℝ) (hb : ∀ n, 1 ≤ b n)
    (hm : Multipliable fun n ↦ ((b n : ℝ) : ℂ)) :
    ∃ d : ℝ, 1 ≤ d ∧ ∏' n, ((b n : ℝ) : ℂ) = (d : ℂ) := by
  have hS : IsClosed {z : ℂ | z.im = 0 ∧ 1 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hge : ∀ N : ℕ, 1 ≤ ∏ i ∈ Finset.range N, b i := fun N ↦ by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.prod_range_succ]
      nlinarith [hb N]
  have hmem := hS.mem_of_tendsto hm.hasProd.tendsto_prod_nat
    (Filter.Eventually.of_forall fun N ↦ by
      have := hge N
      show (∏ i ∈ Finset.range N, ((b i : ℝ) : ℂ)).im = 0 ∧
        1 ≤ (∏ i ∈ Finset.range N, ((b i : ℝ) : ℂ)).re
      rw [← Complex.ofReal_prod]
      exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact this⟩)
  refine ⟨(∏' n, ((b n : ℝ) : ℂ)).re, hmem.2, ?_⟩
  apply Complex.ext <;> simp [hmem.1]

lemma tprod_odd_real {qr : ℝ} (h0 : 0 ≤ qr) (h1 : qr < 1) :
    ∃ d : ℝ, 1 ≤ d ∧ ∏' n : ℕ, (1 + (qr : ℂ) ^ (2 * n + 1)) = (d : ℂ) := by
  have hn : ‖(qr : ℂ)‖ < 1 := by simpa [abs_of_nonneg h0] using h1
  obtain ⟨d, hd, hd'⟩ := tprod_real_ge_one (fun n ↦ 1 + qr ^ (2 * n + 1))
    (fun n ↦ by have := pow_nonneg h0 (2 * n + 1); linarith)
    ((multipliable_one_add_pow_odd hn).congr fun n ↦ by push_cast; ring)
  exact ⟨d, hd, by rw [← hd']; exact tprod_congr fun n ↦ by push_cast; ring⟩

lemma tprod_even_real {qr : ℝ} (h0 : 0 ≤ qr) (h1 : qr < 1) :
    ∃ d : ℝ, 1 ≤ d ∧ ∏' n : ℕ, (1 + ((qr : ℂ) ^ 2) ^ (n + 1)) = (d : ℂ) := by
  have hn : ‖(qr : ℂ)‖ < 1 := by simpa [abs_of_nonneg h0] using h1
  obtain ⟨d, hd, hd'⟩ := tprod_real_ge_one (fun n ↦ 1 + (qr ^ 2) ^ (n + 1))
    (fun n ↦ by have := pow_nonneg (pow_nonneg h0 2) (n + 1); linarith)
    ((multipliable_one_add_pow_succ (norm_sq_lt_one hn)).congr fun n ↦ by push_cast; ring)
  exact ⟨d, hd, by rw [← hd']; exact tprod_congr fun n ↦ by push_cast; ring⟩

lemma q_real (t : ℝ) : cexp (π * I * (I * (t : ℂ))) = ((Real.exp (-(π * t)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]; congr 1; push_cast
  linear_combination ((π : ℂ) * t) * Complex.I_sq

lemma s_real (t : ℝ) :
    cexp (π * I * (I * (t : ℂ)) / 24) = ((Real.exp (-(π * t) / 24) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]; congr 1; push_cast
  linear_combination ((π : ℂ) * t / 24) * Complex.I_sq

lemma qr_bounds {t : ℝ} (ht : 0 < t) : 0 ≤ Real.exp (-(π * t)) ∧ Real.exp (-(π * t)) < 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])⟩

/-- `f(it) > 0` for `t > 0`. -/
lemma weberF_pos {t : ℝ} (ht : 0 < t) : ∃ d : ℝ, 0 < d ∧ weberF (I * (t : ℂ)) = d := by
  have hω : 0 < (I * (t : ℂ)).im := by simpa using ht
  obtain ⟨h0, h1⟩ := qr_bounds ht
  obtain ⟨D, hD1, hD⟩ := tprod_odd_real h0 h1
  rw [weberF_eq_q hω (q_real t).symm (s_real t).symm, hD]
  refine ⟨D / Real.exp (-(π * t) / 24), by positivity, ?_⟩
  push_cast; rfl

/-- `f₂(it) > 0` for `t > 0`. -/
lemma weberF₂_pos {t : ℝ} (ht : 0 < t) : ∃ d : ℝ, 0 < d ∧ weberF₂ (I * (t : ℂ)) = d := by
  have hω : 0 < (I * (t : ℂ)).im := by simpa using ht
  obtain ⟨h0, h1⟩ := qr_bounds ht
  obtain ⟨D, hD1, hD⟩ := tprod_even_real h0 h1
  rw [weberF₂_eq_q hω (q_real t).symm (s_real t).symm, hD]
  refine ⟨√2 * (Real.exp (-(π * t) / 24) ^ 2 * D), by positivity, ?_⟩
  push_cast; rfl

lemma two_rpow_facts :
    ∃ g : ℝ, 0 < g ∧ (2 : ℝ) ^ (1 / 4 : ℝ) = g ^ 2 ∧ (8 : ℝ) ^ (1 / 8 : ℝ) = g ^ 3 ∧ √2 = g ^ 4 := by
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = (2 : ℝ) ^ (1 / 8 : ℝ) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; positivity
  have hg8 : g ^ 8 = 2 := by
    rw [hg, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  refine ⟨g, hg0, ?_, ?_, ?_⟩
  · rw [hg, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  · have h8 : (8 : ℝ) = (2 : ℝ) ^ ((3 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
    rw [h8, hg, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  · rw [show (2 : ℝ) = (g ^ 4) ^ 2 by rw [← pow_mul]; exact hg8.symm]
    exact Real.sqrt_sq (by positivity)

lemma cexp_neg_pi_div_four :
    cexp (-(π : ℂ) * I / 4) = ((√2 : ℝ) : ℂ) / 2 * (1 - I) := by
  rw [show -(π : ℂ) * I / 4 = ((-(π / 4) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast; ring

lemma sqrt2_sq : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow]; simp

lemma sqrt2_ne : ((√2 : ℝ) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < √2 := by positivity
  exact_mod_cast this.ne'

/-- `f(i)² = √2`. -/
lemma weberF_I_sq : weberF I ^ 2 = ((√2 : ℝ) : ℂ) := by
  have hz : 0 < ((I + 1) / 2 : ℂ).im := by simp
  have hI : 0 < (I : ℂ).im := by simp
  have ha : ModularForm.eta I ≠ 0 := ModularForm.eta_ne_zero hI
  have hb : ModularForm.eta ((I + 1) / 2) ≠ 0 := ModularForm.eta_ne_zero hz
  have hS := eta_S_sq hz
  have hinv : -1 / ((I + 1) / 2 : ℂ) = I - 1 := by
    have : (I + 1 : ℂ) ≠ 0 := fun h ↦ by
      have := congrArg Complex.im h; simp at this
    field_simp
    linear_combination (-1 : ℂ) * Complex.I_sq
  rw [hinv] at hS
  have hT := eta_add_one (I - 1)
  rw [sub_add_cancel] at hT
  have hf : weberF I * ModularForm.eta I = cexp (-(π * I) / 24) * ModularForm.eta ((I + 1) / 2) := by
    unfold weberF; field_simp
  have k1 : weberF I ^ 2 * ModularForm.eta I ^ 2 =
      cexp (-(π * I) / 24) ^ 2 * ModularForm.eta ((I + 1) / 2) ^ 2 := by
    rw [← mul_pow, ← mul_pow, hf]
  have k2 : ModularForm.eta I ^ 2 =
      cexp (2 * π * I / 24) ^ 2 * (-I * ((I + 1) / 2) * ModularForm.eta ((I + 1) / 2) ^ 2) := by
    rw [hT, mul_pow, ← hS]
  have k3 : ModularForm.eta ((I + 1) / 2) ^ 2 *
      (weberF I ^ 2 * (cexp (2 * π * I / 24) ^ 2 * (-I * ((I + 1) / 2))) -
        cexp (-(π * I) / 24) ^ 2) = 0 := by
    linear_combination k1 - weberF I ^ 2 * k2
  have k4 : weberF I ^ 2 * (cexp (2 * π * I / 24) ^ 2 * (-I * ((I + 1) / 2))) =
      cexp (-(π * I) / 24) ^ 2 := by
    rcases mul_eq_zero.mp k3 with h | h
    · exact absurd (pow_eq_zero_iff (two_ne_zero) |>.mp h) hb
    · exact sub_eq_zero.mp h
  have hE2 : cexp (-(π * I) / 24) ^ 2 = cexp (-(π : ℂ) * I / 4) * cexp (2 * π * I / 24) ^ 2 := by
    rw [sq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [hE2, cexp_neg_pi_div_four] at k4
  have hu : cexp (2 * π * I / 24) ^ 2 ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have h1I : (1 - I : ℂ) ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h; simp at this
  apply mul_left_cancel₀ (mul_ne_zero hu h1I)
  linear_combination 2 * k4 + (weberF I ^ 2 * cexp (2 * π * I / 24) ^ 2) * Complex.I_sq

lemma eta_S_two {ω : ℂ} (hω : 0 < ω.im) :
    ModularForm.eta (-1 / (2 * ω)) ^ 2 = -I * (2 * ω) * ModularForm.eta (2 * ω) ^ 2 :=
  eta_S_sq (by simpa using hω)

/-- `f₁(2ω) f₂(ω) = √2` (from the definitions). -/
lemma weber_prod12 {ω : ℂ} (hω : 0 < ω.im) :
    weberF₁ (2 * ω) * weberF₂ ω = ((√2 : ℝ) : ℂ) := by
  have h1 : ModularForm.eta (2 * ω) ≠ 0 := ModularForm.eta_ne_zero (by simpa using hω)
  have h2 : ModularForm.eta ω ≠ 0 := ModularForm.eta_ne_zero hω
  unfold weberF₁ weberF₂
  rw [show 2 * ω / 2 = ω by ring]
  field_simp

/-- A positive real `d` with `d² = g²` (`g > 0`) equals `g`. -/
lemma pos_eq_of_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ^ 2 = b ^ 2) : a = b :=
  (sq_eq_sq₀ ha.le hb.le).mp h

/-- **Tabelle VI, `m = 1`**: `f(i) = ⁴√2`. Proof: Mathlib's `η(-1/z)` formula at `z = (1+i)/2` (`-1/z = i - 1`)
and `η(z+1) = e^{2πi/24} η(z)` give `f(i)² = √2` (`weberF_I_sq`); `f(i) > 0` from the `q`-product at
`q = e^{-π}` (`weberF_pos`). -/
@[kb "weber1908" "Tabelle VI, m = 1, p. 721"]
theorem tableRow1 : TableRow1 := by
  unfold TableRow1
  obtain ⟨g, hg0, h14, -, h2⟩ := two_rpow_facts
  have hs : sqrtNeg 1 = I * ((1 : ℝ) : ℂ) := by simp [sqrtNeg]
  rw [hs]
  obtain ⟨d, hd0, hd⟩ := weberF_pos (t := 1) one_pos
  have hsq := weberF_I_sq
  have hI : I * ((1 : ℝ) : ℂ) = I := by simp
  rw [hI] at hd
  rw [hd] at hsq
  have hreal : d ^ 2 = √2 := by exact_mod_cast hsq
  have hdg : d = g ^ 2 := pos_eq_of_sq hd0 (by positivity) (by rw [hreal, h2]; ring)
  rw [hI, hd, h14, hdg]

/-- **Tabelle VI, `m = 2`**: `f₁(√-2) = ⁴√2`. Proof: with `ω = i/√2` (so `2ω = i√2`), `f₁(2ω) f₂(ω) = √2`
(`weber_prod12`); the `η` inversion at `z = 2ω` (`-1/(2ω) = ω`) gives `f₂(ω)² = √2`; `f₂(ω) > 0` from the
`q`-product (`weberF₂_pos`), so `f₂(ω) = ⁴√2` and `f₁(2ω) = √2/⁴√2 = ⁴√2`. -/
@[kb "weber1908" "Tabelle VI, m = 2, p. 721"]
theorem tableRow2 : TableRow2 := by
  unfold TableRow2
  obtain ⟨g, hg0, h14, -, h2⟩ := two_rpow_facts
  have hr2 := sqrt2_sq
  have hr0 := sqrt2_ne
  have ht : (0 : ℝ) < √2 / 2 := by positivity
  obtain ⟨d, hd0, hd⟩ := weberF₂_pos ht
  have hω : 0 < (I * ((√2 / 2 : ℝ) : ℂ)).im := by simp
  generalize hωdef : I * ((√2 / 2 : ℝ) : ℂ) = ω at hω hd
  have e2 : 2 * ω = I * ((√2 : ℝ) : ℂ) := by rw [← hωdef]; push_cast; ring
  have e3 : 2 * ω = sqrtNeg 2 := by rw [e2]; unfold sqrtNeg; push_cast; ring
  have hω2 : 0 < (2 * ω).im := by simpa using hω
  have hinv : -1 / (2 * ω) = ω := by
    have hne : 2 * ω ≠ 0 := by
      rw [e2]; exact mul_ne_zero Complex.I_ne_zero hr0
    rw [div_eq_iff hne, e2, ← hωdef]
    push_cast
    linear_combination (1 / 2 : ℂ) * hr2 - (((√2 : ℝ) : ℂ) ^ 2 / 2) * Complex.I_sq
  have hS := eta_S_two hω
  rw [hinv] at hS
  have hη2 : ModularForm.eta ω ^ 2 = ((√2 : ℝ) : ℂ) * ModularForm.eta (2 * ω) ^ 2 := by
    rw [hS]
    linear_combination (-I * ModularForm.eta (2 * ω) ^ 2) * e2 +
      (-(((√2 : ℝ) : ℂ)) * ModularForm.eta (2 * ω) ^ 2) * Complex.I_sq
  have hη0 : ModularForm.eta (2 * ω) ≠ 0 := ModularForm.eta_ne_zero hω2
  have hF2 : weberF₂ ω ^ 2 = ((√2 : ℝ) : ℂ) := by
    have hn : ((√2 : ℝ) : ℂ) * ModularForm.eta (2 * ω) ^ 2 ≠ 0 :=
      mul_ne_zero hr0 (pow_ne_zero 2 hη0)
    unfold weberF₂
    rw [div_pow, mul_pow, hη2, div_eq_iff hn]
    ring
  rw [hd] at hF2
  have hreal : d ^ 2 = √2 := by exact_mod_cast hF2
  have hdg : d = g ^ 2 := pos_eq_of_sq hd0 (by positivity) (by rw [hreal, h2]; ring)
  have hprod := weber_prod12 hω
  rw [hd, hdg, h2] at hprod
  rw [← e3, h14]
  have hp : weberF₁ (2 * ω) * ((g ^ 2 : ℝ) : ℂ) = ((g ^ 2 : ℝ) : ℂ) * ((g ^ 2 : ℝ) : ℂ) := by
    rw [hprod]; push_cast; ring
  exact mul_right_cancel₀ (by exact_mod_cast (by positivity : (g ^ 2 : ℝ) ≠ 0)) hp

/-- **Tabelle VI, `m = 4`**: `f₁(√-4) = ⁸√8`. Proof: `f₁(2i) f₂(i) = √2`; the `η` inversion at `z = 2i` gives
`f₁(i)² = f₂(i)²`; Weber's `f f₁ f₂ = √2` (`weber_triple`) with `f(i) = ⁴√2` (`tableRow1`) rules out
`f₁(i) = -f₂(i)` and gives `f₂(i)² = ⁴√2`; `f₂(i) > 0` (`weberF₂_pos`) so `f₂(i) = ⁸√2`
and `f₁(2i) = √2/⁸√2 = 2^{3/8} = ⁸√8`. -/
@[kb "weber1908" "Tabelle VI, m = 4, p. 721"]
theorem tableRow4 : TableRow4 := by
  unfold TableRow4
  obtain ⟨g, hg0, h14, h18, h2⟩ := two_rpow_facts
  have hr2 := sqrt2_sq
  have hr0 := sqrt2_ne
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  have hs : sqrtNeg 4 = 2 * I := by
    unfold sqrtNeg; rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, h4]; push_cast; ring
  have hs1 : sqrtNeg 1 = I := by simp [sqrtNeg]
  have hI : I * ((1 : ℝ) : ℂ) = I := by simp
  have hIim : 0 < (I : ℂ).im := by simp
  have hI2 : 0 < (2 * I : ℂ).im := by simp
  have hF : weberF I = ((g ^ 2 : ℝ) : ℂ) := by
    have h1 := tableRow1
    unfold TableRow1 at h1
    rw [hs1, h14] at h1
    exact h1
  obtain ⟨d, hd0, hd⟩ := weberF₂_pos (t := 1) one_pos
  rw [hI] at hd
  -- f₁(i)² = f₂(i)²
  have hinv : -1 / (2 * I : ℂ) = I / 2 := by
    rw [div_eq_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
    linear_combination (-1 : ℂ) * Complex.I_sq
  have hS := eta_S_two hIim
  rw [hinv] at hS
  have hhalf : ModularForm.eta (I / 2) ^ 2 = 2 * ModularForm.eta (2 * I) ^ 2 := by
    rw [hS]
    linear_combination (-(2 : ℂ) * ModularForm.eta (2 * I) ^ 2) * Complex.I_sq
  have hsq : weberF₁ I ^ 2 = weberF₂ I ^ 2 := by
    unfold weberF₁ weberF₂
    rw [div_pow, div_pow, mul_pow, hr2, hhalf]
  have htriple := weber_triple hIim
  rw [hF, hd] at htriple
  rw [hd] at hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with he | he
  · rw [he] at htriple
    have hreal : g ^ 2 * d * d = g ^ 4 := by
      rw [← h2]; exact_mod_cast htriple
    have hd2 : d ^ 2 = g ^ 2 := by
      have : g ^ 2 * (d ^ 2 - g ^ 2) = 0 := by linear_combination hreal
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · linarith
    have hdg : d = g := pos_eq_of_sq hd0 hg0 hd2
    have hprod := weber_prod12 hIim
    rw [hd, hdg, h2] at hprod
    rw [hs, h18]
    have hp : weberF₁ (2 * I) * (g : ℂ) = ((g ^ 3 : ℝ) : ℂ) * (g : ℂ) := by
      rw [hprod]; push_cast; ring
    exact mul_right_cancel₀ (by exact_mod_cast hg0.ne') hp
  · rw [he] at htriple
    exfalso
    have hreal : g ^ 2 * (-d) * d = g ^ 4 := by
      rw [← h2]; exact_mod_cast htriple
    nlinarith [pow_pos hg0 2, pow_pos hd0 2, mul_pos (pow_pos hg0 2) (pow_pos hd0 2), pow_pos hg0 4]

end Proofs

end ModularFormsKB.Historical.Weber
