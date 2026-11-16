/-
# Eighth roots of unity in Kohnen's operator on the plus space

The cusp computation of `KohnenLUFourProof.lean` evaluates $W(4)U(4)$ and $W(4)U(4)U(4)$ on a plus form at the points
$(\tau + j)/4$ and $\tau - r/8$; the constants that come out are sums of powers of $\omega = e^{\pi i/4}$ (`omega8`).
This file proves the two finite identities needed, by reducing $k$ and $n$ modulo $8$:
* `omega8_kappa`: $\omega^{2k+6n} + \omega^{2k+6n+2} + \omega^{6k+2n} + \omega^{6k+2n+6} = \pm 2(-1)^{\lfloor (k+1)/2\rfloor}$,
  with sign $+$ at plus indices and $-$ at minus indices;
* `omega8_gauss`: at plus indices, $\sum_{r \in \{1,3,5,7\}} \omega^{r(2k+1) + (8-r)n} =
  4(-1)^{\lfloor (k+1)/2\rfloor}\left(\frac{(-1)^k n}{2}\right)$ (a Gauss sum of the character $(\frac 2\cdot)$ modulo $8$).
Both were also checked numerically for $k < 16$, $n < 32$.
-/
import ModularFormsKB.HalfIntegral.KohnenLift

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

/-- $\omega = e^{\pi i/4}$, a primitive eighth root of unity. -/
noncomputable def omega8 : ℂ := cexp (π / 4 * I)

theorem omega8_eq : omega8 = (Real.sqrt 2 / 2 : ℝ) + (Real.sqrt 2 / 2 : ℝ) * I := by
  unfold omega8
  rw [show (π / 4 * I : ℂ) = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]

theorem omega8_sq : omega8 ^ 2 = I := by
  unfold omega8
  rw [← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (π / 4 * I) = π / 2 * I by push_cast; ring]
  rw [Complex.exp_mul_I]
  have h1 : Complex.cos (π / 2) = 0 := by exact_mod_cast Real.cos_pi_div_two
  have h2 : Complex.sin (π / 2) = 1 := by exact_mod_cast Real.sin_pi_div_two
  rw [h1, h2]; ring

theorem omega8_four : omega8 ^ 4 = -1 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, omega8_sq]; simp

theorem omega8_eight : omega8 ^ 8 = 1 := by
  rw [show 8 = 4 * 2 by norm_num, pow_mul, omega8_four]; simp

theorem omega8_pow_mod (m : ℕ) : omega8 ^ m = omega8 ^ (m % 8) := by
  conv_lhs => rw [← Nat.div_add_mod m 8, pow_add, pow_mul, omega8_eight, one_pow, one_mul]

theorem omega8_re_pos : 0 < omega8.re := by
  rw [omega8_eq]; simp

theorem omega8_re_eq_im : omega8.re = omega8.im := by
  rw [omega8_eq]; simp

/-- $e^{2\pi i n(-r/8)} = \omega^{(8-r)n}$ for $0 \le r \le 8$. -/
theorem cexp_neg_eighth (n r : ℕ) (hr : r ≤ 8) :
    cexp (2 * π * I * n * (-(r : ℂ) / 8)) = omega8 ^ ((8 - r) * n) := by
  unfold omega8
  rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(n : ℤ), ?_⟩
  push_cast [Nat.cast_sub hr]
  ring

/-- $e^{2\pi i n/4} = \omega^{2n}$. -/
theorem cexp_pos_quarter (n : ℕ) : cexp (2 * π * I * n * (1 / 4 : ℂ)) = omega8 ^ (2 * n) := by
  unfold omega8
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

private lemma negpow_int (k : ℕ) : (-1 : ℤ) ^ k = if k % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, if_pos (Nat.even_iff.mp h)]
  · rw [h.neg_one_pow, if_neg (by have := Nat.odd_iff.mp h; omega)]

private lemma minus_iff (k n : ℕ) :
    MinusIdx k n ↔ (k % 2 = 0 ∧ (n % 4 = 2 ∨ n % 4 = 3)) ∨ (k % 2 = 1 ∧ (n % 4 = 2 ∨ n % 4 = 1)) := by
  unfold MinusIdx
  rw [negpow_int]
  split_ifs <;> omega

private lemma minus_red (k n : ℕ) : MinusIdx k n ↔ MinusIdx (k % 8) (n % 8) := by
  rw [minus_iff, minus_iff]; omega

private lemma kron_red (k n : ℕ) :
    kroneckerTwo ((-1) ^ k * (n : ℤ)) = kroneckerTwo ((-1) ^ (k % 8) * ((n % 8 : ℕ) : ℤ)) := by
  rw [negpow_int k, negpow_int (k % 8)]
  have : (k % 8) % 2 = k % 2 := by omega
  rw [this]
  unfold kroneckerTwo
  split_ifs <;> push_cast <;> omega

private lemma sign_red (k : ℕ) : ((-1 : ℂ) ^ ((k + 1) / 2)) = (-1) ^ ((k % 8 + 1) / 2) := by
  have : (k + 1) / 2 = (k % 8 + 1) / 2 + 4 * (k / 8) := by omega
  rw [this, pow_add, pow_mul]; norm_num

private lemma omega8_five : omega8 ^ 5 = -omega8 := by
  rw [pow_succ, omega8_four]; ring
private lemma omega8_six : omega8 ^ 6 = -omega8 ^ 2 := by
  rw [show 6 = 4 + 2 by norm_num, pow_add, omega8_four]; ring
private lemma omega8_seven : omega8 ^ 7 = -omega8 ^ 3 := by
  rw [show 7 = 4 + 3 by norm_num, pow_add, omega8_four]; ring

/-- **The constant of $W(4)U(4)$ on the plus space.** -/
theorem omega8_kappa (k n : ℕ) :
    omega8 ^ (2 * k + 6 * n) + omega8 ^ (2 * k + 6 * n + 2) + omega8 ^ (6 * k + 2 * n) +
        omega8 ^ (6 * k + 2 * n + 6) =
      2 * (-1) ^ ((k + 1) / 2) * (if MinusIdx k n then -1 else 1) := by
  have e1 : (2 * k + 6 * n) % 8 = (2 * (k % 8) + 6 * (n % 8)) % 8 := by omega
  have e2 : (2 * k + 6 * n + 2) % 8 = (2 * (k % 8) + 6 * (n % 8) + 2) % 8 := by omega
  have e3 : (6 * k + 2 * n) % 8 = (6 * (k % 8) + 2 * (n % 8)) % 8 := by omega
  have e4 : (6 * k + 2 * n + 6) % 8 = (6 * (k % 8) + 2 * (n % 8) + 6) % 8 := by omega
  rw [omega8_pow_mod (2 * k + 6 * n), omega8_pow_mod (2 * k + 6 * n + 2),
    omega8_pow_mod (6 * k + 2 * n), omega8_pow_mod (6 * k + 2 * n + 6), e1, e2, e3, e4,
    sign_red]
  have hM : (if MinusIdx k n then (-1 : ℂ) else 1) = if MinusIdx (k % 8) (n % 8) then -1 else 1 := by
    simp only [minus_red k n]
  rw [hM]
  have ha : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hb : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize k % 8 = a at *
  generalize n % 8 = b at *
  interval_cases a <;> interval_cases b <;>
    simp [MinusIdx, omega8_four, omega8_five, omega8_six, omega8_seven] <;> ring_nf

/-- **The Gauss sum at the cusp $1/2$.** -/
theorem omega8_gauss (k n : ℕ) (hn : ¬ MinusIdx k n) :
    omega8 ^ ((2 * k + 1) + 7 * n) + omega8 ^ (3 * (2 * k + 1) + 5 * n) +
        omega8 ^ (5 * (2 * k + 1) + 3 * n) + omega8 ^ (7 * (2 * k + 1) + n) =
      4 * (-1) ^ ((k + 1) / 2) * (kroneckerTwo ((-1) ^ k * (n : ℤ)) : ℂ) := by
  rw [minus_red] at hn
  have e1 : ((2 * k + 1) + 7 * n) % 8 = ((2 * (k % 8) + 1) + 7 * (n % 8)) % 8 := by omega
  have e2 : (3 * (2 * k + 1) + 5 * n) % 8 = (3 * (2 * (k % 8) + 1) + 5 * (n % 8)) % 8 := by omega
  have e3 : (5 * (2 * k + 1) + 3 * n) % 8 = (5 * (2 * (k % 8) + 1) + 3 * (n % 8)) % 8 := by omega
  have e4 : (7 * (2 * k + 1) + n) % 8 = (7 * (2 * (k % 8) + 1) + (n % 8)) % 8 := by omega
  rw [omega8_pow_mod ((2 * k + 1) + 7 * n), omega8_pow_mod (3 * (2 * k + 1) + 5 * n),
    omega8_pow_mod (5 * (2 * k + 1) + 3 * n), omega8_pow_mod (7 * (2 * k + 1) + n),
    e1, e2, e3, e4, sign_red, kron_red]
  have ha : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hb : n % 8 < 8 := Nat.mod_lt _ (by norm_num)
  generalize k % 8 = a at *
  generalize n % 8 = b at *
  interval_cases a <;> interval_cases b <;>
    simp_all [MinusIdx, kroneckerTwo, omega8_four, omega8_five, omega8_six, omega8_seven] <;> ring_nf

end ModularFormsKB.HalfIntegral
