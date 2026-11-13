import ModularFormsKB.Historical.WeberHeegnerStark.Inputs
import ModularFormsKB.Historical.WeberHeegnerStark.CubicField
import Mathlib.Tactic.ComputeDegree

/-!
# Heegner's step: from class number one to `γ₂ ∈ {0, -32, -96, -960, -5280, -640320}`

Let `p ≡ 3 mod 8` be a prime, `p ≥ 11`, with `h(-p) = 1`. Write `τ = √-p` and `s₀ = (-3 + √-p)/2`.
Heegner's argument (1952, as completed by Stark 1969 [from memory; to check against the papers]) runs as
follows; every input from complex multiplication is a field of `WeberHeegnerStarkInputs`.

1. `L = ℚ(j(√-p))` is a cubic field: `[L : ℚ] = h(-4p) = 3 h(-p) = 3` (`finrank_kleinJ`,
   `classNumber_four_mul`).
2. `j(s₀)` is rational (`finrank_kleinJ` with `h(-p) = 1`) and an algebraic integer
   (`isIntegral_kleinJ`), and `γ₂(s₀) ∈ ℚ(j(s₀)) = ℚ` (`gammaTwo_mem`, Weber's normalization `3 ∣ b`). As
   `γ₂³ = j`, `g = γ₂(s₀)` is a rational integer.
3. Weber's Theorems I and VI put `f = f(√-p)` in `L`, so `x = 2/f²` is in `L`.
4. `f(√-p)²⁴ f₂(s₀)²⁴ = -2¹²` (`weberF_pow_mul_weberF₂_pow`, from the definitions as `η`-quotients),
   so `w = x⁴` has `w³ = -f₂(s₀)²⁴`. Weber's cubic at `s₀` gives `(16 - w³)³ = (-g w)³`, hence
   `w³ - g w - 16 = 0` because `L` has no primitive cube root of unity. So `w` and `x` are algebraic
   integers.
5. `w` is irrational, since `|w|³ = |f₂(s₀)²⁴| < 1` and `w ≠ 0`.
6. Heegner's coefficient comparison (`exists_coeffs_of_pow_four`) and the integer points of
   `y² = 2u(u³ + 1)` give `g ∈ {0, -32, -96, -960, -5280, -640320}`, and the enclosure of `j` recovers `p`.

The Diophantine step (6, second half) and the enclosure are passed to `mem_heegner_of_formClassNumber_eq_one`
as hypotheses here and supplied by `Diophantine.lean` and `Numerics.lean` in `Main.lean`.
-/

noncomputable section

open ModularForm Complex IntermediateField Module Polynomial
open UpperHalfPlane hiding I
open scoped Real

namespace ModularFormsKB.WeberHeegnerStark

/-! ### `η²⁴` is periodic -/

theorem eta_add_one_pow (w : ℂ) : ModularForm.eta (w + 1) ^ 24 = ModularForm.eta w ^ 24 := by
  have hq : cexp (2 * π * I * (w + 1)) = cexp (2 * π * I * w) := by
    rw [show 2 * π * I * (w + 1) = 2 * π * I * w + 2 * π * I by ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  have hprod : (∏' n, (1 - eta_q n (w + 1))) = ∏' n, (1 - eta_q n w) := by
    simp only [eta_q_eq_pow, hq]
  have h24 (z : ℂ) : Function.Periodic.qParam 24 z ^ 24 = cexp (2 * π * I * z) := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold ModularForm.eta
  rw [mul_pow, mul_pow, h24, h24, hq, hprod]

theorem eta_add_nat_pow (w : ℂ) (k : ℕ) : ModularForm.eta (w + k) ^ 24 = ModularForm.eta w ^ 24 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, eta_add_one_pow, ih]

/-- `f(z)²⁴ f₂((z - 3)/2)²⁴ = -2¹²`: the identity behind Heegner's choice of `x = 2/f(√-p)²`. -/
theorem weberF_pow_mul_weberF₂_pow {z : ℂ} (hz : ModularForm.eta z ≠ 0) (hz' : ModularForm.eta ((z + 1) / 2) ≠ 0) :
    weberF z ^ 24 * weberF₂ ((z - 3) / 2) ^ 24 = -4096 := by
  have he : cexp (-(π * I) / 24) ^ 24 = -1 := by
    rw [← Complex.exp_nat_mul]
    push_cast
    rw [show (24 : ℂ) * (-(π * I) / 24) = -(π * I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hs : ((√2 : ℝ) : ℂ) ^ 24 = 4096 := by
    rw [show (24 : ℕ) = 2 * 12 by rfl, pow_mul, ← Complex.ofReal_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h1 : ModularForm.eta (2 * ((z - 3) / 2)) ^ 24 = ModularForm.eta z ^ 24 := by
    rw [show 2 * ((z - 3) / 2) = z - 3 by ring, ← eta_add_nat_pow (z - 3) 3]
    push_cast
    ring_nf
  have h2 : ModularForm.eta ((z - 3) / 2) ^ 24 = ModularForm.eta ((z + 1) / 2) ^ 24 := by
    rw [← eta_add_nat_pow ((z - 3) / 2) 2]
    push_cast
    ring_nf
  rw [weberF, weberF₂, div_pow, div_pow, mul_pow, mul_pow, he, hs, h1, h2]
  field_simp

/-! ### The two CM points -/

/-- The point `√-p` of the upper half-plane. -/
def cmPointI (p : ℕ) (hp : 0 < p) : ℍ :=
  ⟨((√(p : ℝ) : ℝ) : ℂ) * I, by simpa using Real.sqrt_pos.2 (Nat.cast_pos.2 hp)⟩

/-- The point `(-3 + √-p)/2` of the upper half-plane. -/
def cmPointS (p : ℕ) (hp : 0 < p) : ℍ :=
  ⟨(-3 + ((√(p : ℝ) : ℝ) : ℂ) * I) / 2, by
    simpa using Real.sqrt_pos.2 (Nat.cast_pos.2 hp)⟩

theorem cmPointS_im (p : ℕ) (hp : 0 < p) : (cmPointS p hp).im = √(p : ℝ) / 2 := by
  change ((-3 + ((√(p : ℝ) : ℝ) : ℂ) * I) / 2).im = _
  simp

theorem sqrt_cast_sq (p : ℕ) : ((√(p : ℝ) : ℝ) : ℂ) ^ 2 = p := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  simp

theorem isPrimitiveForm_one' (b c : ℤ) : IsPrimitiveForm 1 b c := by
  simp [IsPrimitiveForm]

theorem isFormRoot_cmPointI (p : ℕ) (hp : 0 < p) : IsFormRoot 1 0 p (cmPointI p hp) := by
  refine ⟨one_pos, by simp; exact_mod_cast hp, ?_⟩
  change ((√(p : ℝ) : ℝ) : ℂ) * I = _
  have : Real.sqrt (((-((0 : ℤ) ^ 2 - 4 * 1 * (p : ℤ))) : ℤ) : ℝ) = 2 * √(p : ℝ) := by
    rw [show (((-((0 : ℤ) ^ 2 - 4 * 1 * (p : ℤ))) : ℤ) : ℝ) = 2 ^ 2 * p by push_cast; ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [this]
  push_cast
  ring

theorem isFormRoot_cmPointS (p : ℕ) (hp : 0 < p) {c : ℤ} (hc : 4 * c = 9 + p) :
    IsFormRoot 1 3 c (cmPointS p hp) := by
  have hD : (3 : ℤ) ^ 2 - 4 * 1 * c = -p := by linarith
  refine ⟨one_pos, by rw [hD]; simp; exact_mod_cast hp, ?_⟩
  change (-3 + ((√(p : ℝ) : ℝ) : ℂ) * I) / 2 = _
  rw [hD]
  push_cast
  ring_nf

/-! ### Heegner's step -/

/-- **Heegner's step.** Let `p ≡ 3 mod 8` be a prime with `p ≥ 11` and `h(-p) = 1`. Given the named
inputs, the integer `g = γ₂((-3 + √-p)/2)` satisfies `j((-3 + √-p)/2) = g³` and is the `γ` of an integer
cubic `X³ + aX² + bX + c` with `(a² - 2b)² = 2(b² - 2ac)` and `c⁴ = 16`. -/
theorem exists_heegner_cubic (hin : WeberHeegnerStarkInputs) {p : ℕ} (hp : p.Prime)
    (h8 : p % 8 = 3) (h11 : 11 ≤ p) (h1 : formClassNumber (-p) = 1)
    (hsmall : ‖weberF₂ (cmPointS p hp.pos) ^ 24‖ < 1) :
    ∃ g : ℤ, kleinJ (cmPointS p hp.pos) = (g : ℂ) ^ 3 ∧
      ∃ a b c : ℤ, (a ^ 2 - 2 * b) ^ 2 = 2 * (b ^ 2 - 2 * a * c) ∧ c ^ 4 = 16 ∧
        g = -((b ^ 2 - 2 * a * c) ^ 2 - 2 * (a ^ 2 - 2 * b) * c ^ 2) := by
  have hp0 := hp.pos
  have hp3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    omega
  set τ := cmPointI p hp0 with hτ
  set s := cmPointS p hp0 with hs
  set L := ℚ⟮kleinJ τ⟯ with hL
  -- Step 1: `L` is a cubic field.
  have hL3 : finrank ℚ L = 3 := by
    have := hin.finrank_kleinJ 1 0 p τ (isPrimitiveForm_one' 0 p) (isFormRoot_cmPointI p hp0)
    rw [this, show ((0 : ℤ) ^ 2 - 4 * 1 * (p : ℤ)) = -4 * (p : ℕ) by ring,
      hin.classNumber_four_mul p h8 (by omega), h1]
  -- Step 2: `g = γ₂(s)` is a rational integer with `g³ = j(s)`.
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℤ, 4 * c₀ = 9 + p := ⟨(9 + p) / 4, by omega⟩
  have hsroot := isFormRoot_cmPointS p hp0 hc₀
  have hD : (3 : ℤ) ^ 2 - 4 * 1 * c₀ = -p := by linarith
  have hbot : ℚ⟮kleinJ s⟯ = ⊥ := by
    have := hin.finrank_kleinJ 1 3 c₀ s (isPrimitiveForm_one' 3 c₀) hsroot
    rw [hD, h1] at this
    exact finrank_eq_one_iff.1 this
  have hγbot : gammaTwo s ∈ (⊥ : IntermediateField ℚ ℂ) := by
    have := hin.gammaTwo_mem 1 3 c₀ s (isPrimitiveForm_one' 3 c₀) hsroot
      (by rw [hD]; intro h; exact hp3 (by exact_mod_cast (Int.dvd_neg.1 h)))
      (by decide) (by decide)
    rwa [hbot] at this
  have hJint : IsIntegral ℤ (kleinJ s) := by
    refine hin.isIntegral_kleinJ s 1 3 c₀ one_ne_zero ?_
    change (1 : ℤ) * ((-3 + ((√(p : ℝ) : ℝ) : ℂ) * I) / 2) ^ 2 +
      (3 : ℤ) * ((-3 + ((√(p : ℝ) : ℝ) : ℂ) * I) / 2) + (c₀ : ℂ) = 0
    have hc : (4 : ℂ) * c₀ = 9 + p := by exact_mod_cast hc₀
    push_cast
    linear_combination (1 / 4 : ℂ) * I ^ 2 * sqrt_cast_sq p + ((p : ℂ) / 4) * I_sq +
      (1 / 4 : ℂ) * hc
  have hγint : IsIntegral ℤ (gammaTwo s) :=
    IsIntegral.of_pow (by norm_num : 0 < 3) (by rwa [gammaTwo_pow_three])
  obtain ⟨g, hg⟩ := exists_intCast_eq_of_mem_bot hγbot hγint
  have hjg : kleinJ s = (g : ℂ) ^ 3 := by rw [hg, gammaTwo_pow_three]
  refine ⟨g, hjg, ?_⟩
  -- Step 3: `x = 2/f²` lies in `L`.
  have hτI : (τ : ℂ) = ((√(p : ℝ) : ℝ) : ℂ) * I := rfl
  have hη1 : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hη2 : ModularForm.eta (((τ : ℂ) + 1) / 2) ≠ 0 := by
    apply ModularForm.eta_ne_zero
    change 0 < (((τ : ℂ) + 1) / 2).im
    simpa using τ.2
  set f := weberF τ with hf
  have hf0 : f ≠ 0 := by
    rw [hf, weberF]
    exact div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hη2) hη1
  have hf8 := hin.weberF_pow_eight_mem p τ (hp.odd_of_ne_two (by omega)) hp3 hτI
  have hf3 := hin.weberF_pow_three_mem p τ h8 hp3 hτI
  have hfL : f ∈ L := by
    have : f = (f ^ 3) ^ 3 / f ^ 8 := by field_simp
    rw [this]
    exact div_mem (pow_mem hf3 3) hf8
  set x : ℂ := 2 / f ^ 2 with hx
  have hx0 : x ≠ 0 := by rw [hx]; exact div_ne_zero two_ne_zero (pow_ne_zero 2 hf0)
  have hxL : x ∈ L := div_mem (by simp) (pow_mem hfL 2)
  -- Step 4: `w = x⁴` satisfies `w³ - g w - 16 = 0`.
  set y := weberF₂ s ^ 24 with hy
  have hfy : f ^ 24 * y = -4096 := by
    have h := weberF_pow_mul_weberF₂_pow hη1 hη2
    have hs' : ((τ : ℂ) - 3) / 2 = (s : ℂ) := by
      change (((√(p : ℝ) : ℝ) : ℂ) * I - 3) / 2 = (-3 + ((√(p : ℝ) : ℝ) : ℂ) * I) / 2
      ring
    rwa [hs'] at h
  set w := x ^ 4 with hw
  have hw3 : w ^ 3 = -y := by
    have hy' : y = -4096 / f ^ 24 := by field_simp; linear_combination hfy
    rw [hw, hx, ← pow_mul, div_pow, hy']
    field_simp
    ring
  have hcubic := hin.weber_cubic s
  rw [← hy, hjg] at hcubic
  have hwL : w ∈ L := pow_mem hxL 4
  have hgL : ((g : ℂ)) ∈ L := by simp
  have huv : 16 - w ^ 3 = -(g : ℂ) * w := by
    refine eq_of_pow_three_eq_pow_three hL3 (sub_mem (by simp)
      (pow_mem hwL 3)) (mul_mem (neg_mem hgL) hwL) ?_
    rw [show 16 - w ^ 3 = y + 16 by rw [hw3]; ring, hcubic, show y = -w ^ 3 by rw [hw3]; ring]
    ring
  have hcub : w ^ 3 - g * w - 16 = 0 := by linear_combination -huv
  have hwint : IsIntegral ℤ w := by
    refine ⟨X ^ 3 - C g * X - 16, ?_, ?_⟩
    · monicity!
    · simp only [eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_ofNat]
      simpa using hcub
  have hxint : IsIntegral ℤ x := IsIntegral.of_pow (by norm_num : 0 < 4) hwint
  -- Step 5: `w` is irrational.
  have hwq : w ∉ (⊥ : IntermediateField ℚ ℂ) := by
    intro hq
    obtain ⟨n, hn⟩ := exists_intCast_eq_of_mem_bot hq hwint
    have hn3 : ‖((n : ℂ)) ^ 3‖ < 1 := by rw [hn, hw3, norm_neg]; exact hsmall
    have hn0 : n = 0 := by
      rw [norm_pow, Complex.norm_intCast] at hn3
      have : |(n : ℝ)| < 1 := by
        by_contra h
        push Not at h
        nlinarith [pow_le_pow_left₀ (zero_le_one) h 3]
      have : |n| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.1 this
    rw [hn0, Int.cast_zero, eq_comm, hw] at hn
    exact hx0 ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).1 hn)
  -- Step 6: Heegner's coefficient comparison.
  exact exists_coeffs_of_pow_four hL3 hxL hxint hwq hcub

end ModularFormsKB.WeberHeegnerStark
