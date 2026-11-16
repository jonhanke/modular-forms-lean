/-
# Kohnen's $T^+(4)$ commutes with $T(p^2)$ for odd $p$

Formal, on coefficient sequences: it uses only $p^2 \equiv 1 \bmod 8$ for odd $p$ (so
$\left(\frac{p^2 m}{2}\right) = \left(\frac{m}{2}\right)$ in `kroneckerTwo`) and
$\left(\frac{4m}{p}\right) = \left(\frac{m}{p}\right)$ for the Jacobi symbol, together with the coprimality of $4$ and $p^2$.
-/
import ModularFormsKB.HalfIntegral.KohnenRecursion

namespace ModularFormsKB.HalfIntegral

open Complex

private theorem one_char_odd' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (1 : DirichletCharacter ℂ (4 * 1)) p = 1 := by
  apply MulChar.one_apply
  rw [ZMod.isUnit_iff_coprime]
  have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  simpa using Nat.Coprime.pow_right 2 h2

private theorem jac_four_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : ℤ) (m : ℕ) :
    jacobiSym (x * ((4 * m : ℕ) : ℤ)) p = jacobiSym (x * (m : ℤ)) p := by
  have h : (2 : ℤ).gcd p = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes Nat.prime_two hp).2 hp2.symm
  have : x * ((4 * m : ℕ) : ℤ) = (2 : ℤ) ^ 2 * (x * m) := by push_cast; ring
  rw [this, jacobiSym.mul_left, jacobiSym.sq_one' h, one_mul]

private theorem sq_eq_eight_mul_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ c : ℕ, p ^ 2 = 8 * c + 1 := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  obtain ⟨j, hj⟩ : ∃ j, p = 2 * j + 1 := ⟨p / 2, by omega⟩
  subst hj
  have h2 : 2 ∣ j * (j + 1) := by
    rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * (j + 1), by rw [ht]; ring⟩
    · exact ⟨(t + 1) * j, by rw [ht]; ring⟩
  obtain ⟨c, hc⟩ := h2
  exact ⟨c, by nlinarith [hc]⟩

private theorem kron_sq_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : ℤ) (m : ℕ) :
    kroneckerTwo (x * ((p ^ 2 * m : ℕ) : ℤ)) = kroneckerTwo (x * (m : ℤ)) := by
  obtain ⟨c, hc⟩ := sq_eq_eight_mul_add_one hp hp2
  have hc' : (p : ℤ) ^ 2 = 8 * (c : ℤ) + 1 := by exact_mod_cast hc
  push_cast
  rw [hc']
  have : x * ((8 * (c : ℤ) + 1) * m) = x * m + 8 * (x * (c * m)) := by ring
  rw [this]
  generalize x * ((c : ℤ) * m) = w
  generalize x * (m : ℤ) = z
  have e1 : (2 : ℤ) ∣ z + 8 * w ↔ (2 : ℤ) ∣ z := by omega
  have e2 : (z + 8 * w) % 8 = z % 8 := by omega
  unfold kroneckerTwo
  simp only [e1, e2]

private theorem four_p_cop {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : Nat.Coprime (p ^ 2) 4 := by
  have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  simpa using Nat.Coprime.pow 2 2 h2

/-- **Kohnen's formula for $T^+(4)$ commutes with $T(p^2)$ for odd primes $p$** on coefficient sequences, at every
index (formal: uses $p^2 \equiv 1 \bmod 8$, so $\left(\frac{p^2 m}{2}\right) = \left(\frac m2\right)$, and
$\left(\frac{4m}{p}\right) = \left(\frac mp\right)$). -/
theorem heckeTPlusFourFormula_comm (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ → ℂ) :
    heckeT k 1 1 p (heckeTPlusFourFormula k a) = heckeTPlusFourFormula k (heckeT k 1 1 p a) := by
  have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hcop := four_p_cop hp hp2
  have hc1 := one_char_odd' hp hp2
  have d1' : ∀ n : ℕ, 4 ∣ p ^ 2 * n ↔ 4 ∣ n := fun n ↦
    ⟨fun h => hcop.symm.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩
  have d2' : ∀ n : ℕ, p ^ 2 ∣ 4 * n ↔ p ^ 2 ∣ n := fun n ↦
    ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => Dvd.dvd.mul_left h _⟩
  funext n
  have d1 := d1' n
  have d2 := d2' n
  have e : p ^ 2 * (4 * n) = 4 * (p ^ 2 * n) := by ring
  have g3 : n / p ^ 2 / 4 = n / 4 / p ^ 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  have g1 : 4 ∣ n → p ^ 2 * n / 4 = p ^ 2 * (n / 4) := by
    rintro ⟨m, rfl⟩
    rw [show p ^ 2 * (4 * m) = 4 * (p ^ 2 * m) by ring, Nat.mul_div_cancel_left _ (by norm_num),
      Nat.mul_div_cancel_left _ (by norm_num)]
  have g2 : p ^ 2 ∣ n → 4 * n / p ^ 2 = 4 * (n / p ^ 2) := by
    rintro ⟨m, rfl⟩
    rw [show 4 * (p ^ 2 * m) = p ^ 2 * (4 * m) by ring, Nat.mul_div_cancel_left _ hp0,
      Nat.mul_div_cancel_left _ hp0]
  have dd1 : p ^ 2 ∣ n → (4 ∣ n / p ^ 2 ↔ 4 ∣ n) := by
    rintro ⟨m, rfl⟩
    rw [Nat.mul_div_cancel_left _ hp0]
    exact (d1' m).symm
  have dd2 : 4 ∣ n → (p ^ 2 ∣ n / 4 ↔ p ^ 2 ∣ n) := by
    rintro ⟨m, rfl⟩
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
    exact (d2' m).symm
  have j1 : 4 ∣ n → jacobiSym ((-1) ^ k * ((n / 4 : ℕ) : ℤ)) p = jacobiSym ((-1) ^ k * (n : ℤ)) p := by
    rintro ⟨m, rfl⟩
    rw [Nat.mul_div_cancel_left _ (by norm_num), jac_four_mul hp hp2]
  have k1 : p ^ 2 ∣ n →
      kroneckerTwo ((-1) ^ k * ((n / p ^ 2 : ℕ) : ℤ)) = kroneckerTwo ((-1) ^ k * (n : ℤ)) := by
    rintro ⟨m, rfl⟩
    rw [Nat.mul_div_cancel_left _ hp0, kron_sq_mul hp hp2]
  simp only [heckeT, heckeTPlusFourFormula, hc1, one_mul, one_pow, jac_four_mul hp hp2, kron_sq_mul hp hp2, e, d1, d2]
  by_cases hpn : p ^ 2 ∣ n <;> by_cases h4 : 4 ∣ n
  · simp only [hpn, h4, ite_true, g1 h4, g2 hpn, g3, (dd1 hpn).2 h4, (dd2 h4).2 hpn, j1 h4, k1 hpn]
    ring
  · simp only [hpn, h4, ite_true, ite_false, g2 hpn, k1 hpn, (dd1 hpn).not.2 h4]
    ring
  · simp only [hpn, h4, ite_true, ite_false, g1 h4, j1 h4, (dd2 h4).not.2 hpn]
    ring
  · simp only [hpn, h4, ite_false]
    ring

/-- **Kohnen's $T^+(4)$ commutes with $T(p^2)$ for odd primes $p$** on coefficient sequences: the formula commutes
(`heckeTPlusFourFormula_comm`) and so does the plus projection (`heckeT_plusProj`). -/
theorem heckeTPlusFour_comm (k : ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ → ℂ) :
    heckeT k 1 1 p (heckeTPlusFour k a) = heckeTPlusFour k (heckeT k 1 1 p a) := by
  rw [heckeTPlusFour_eq_plusProj, heckeTPlusFour_eq_plusProj, heckeT_plusProj 1 hp hp2,
    heckeTPlusFourFormula_comm k hp hp2]

end ModularFormsKB.HalfIntegral
