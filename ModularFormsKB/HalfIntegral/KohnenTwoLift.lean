/-
# The $D$-th lift at the prime $2$, and eigen-sequences of the level one Hecke operators

- `kohnenLiftCoeff_heckeTPlusFour` (Kohnen 1980 `kohnen1980`, Prop. 4 and Thm. 1 [unverified]): for a fundamental
  discriminant $D$ with $(-1)^kD > 0$ and a coefficient sequence $c$ supported on the plus indices, the $D$-th lift
  intertwines Kohnen's $T^+(4)$ with $T(2)$: $\mathcal S_D(T^+(4)c) = T(2)\,\mathcal S_D(c)$. Purely formal; checked
  numerically for $1 \le k \le 5$, $|D| \le 40$ and $n \le 12$ before being stated.
- `eq_zero_of_heckeTInt_eigen`: a sequence that is an eigenvector of every $T(p)$ (weight $w$, level one) and has
  $b(1) = 0$ vanishes in every degree $n \ge 1$.
-/
import ModularFormsKB.HalfIntegral.KohnenRecursion

namespace ModularFormsKB.HalfIntegral

open Complex

private theorem kroneckerDisc_two_mul (D : ℤ) {d : ℕ} (hd : d ≠ 0) :
    kroneckerDisc D (2 * d) = kroneckerDisc D 2 * kroneckerDisc D d := by
  have h2 : kroneckerDisc D 2 = kroneckerTwo D := by
    simp [kroneckerDisc, Nat.Prime.factorization_self Nat.prime_two]
  rw [h2]
  have hf : (2 * d).factorization 2 = d.factorization 2 + 1 := by
    rw [Nat.factorization_mul two_ne_zero hd, Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two]
    ring
  have hdiv : 2 * d / 2 ^ (d.factorization 2 + 1) = d / 2 ^ d.factorization 2 := by
    rw [pow_succ, mul_comm (2 ^ d.factorization 2) 2, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ two_pos]
  unfold kroneckerDisc
  rw [hf, hdiv]
  ring

private theorem sq_mod_eight_of_odd (m : ℕ) (hm : ¬ 2 ∣ m) : ((m : ℤ) ^ 2) % 8 = 1 := by
  have h : (m : ℤ) % 8 = 1 ∨ (m : ℤ) % 8 = 3 ∨ (m : ℤ) % 8 = 5 ∨ (m : ℤ) % 8 = 7 := by omega
  rw [pow_two, Int.mul_emod]
  rcases h with h | h | h | h <;> rw [h] <;> norm_num

private theorem dsum_lin3 (f g h j : ℕ → ℂ) (a b : ℂ) (n : ℕ) :
    liftDsum f (fun m ↦ g m + a * h m + b * j m) n = liftDsum f g n + a * liftDsum f h n + b * liftDsum f j n := by
  unfold liftDsum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  ring

/-- $T^+(4)c$ at $|D|m^2$ for a plus sequence $c$. -/
private theorem heckeTPlusFour_Dsq (k : ℕ) {D : ℤ} (hD : KohnenDisc k D) {c : ℕ → ℂ} (hc : c ∈ plusSeq k) (m : ℕ) :
    heckeTPlusFour k c (D.natAbs * m ^ 2) = c (D.natAbs * (2 * m) ^ 2) +
      (kroneckerDisc D 2 : ℂ) * (2 : ℂ) ^ ((k : ℤ) - 1) * (if 2 ∣ m then 0 else c (D.natAbs * m ^ 2)) +
      (2 : ℂ) ^ (2 * (k : ℤ) - 1) * (if 2 ∣ m then c (D.natAbs * (m / 2) ^ 2) else 0) := by
  have hσ : (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := by
    rcases neg_one_pow_eq_or ℤ k with h | h <;> simp [h]
  have hsign := hD.2
  have hDabs : (-1) ^ k * (D.natAbs : ℤ) = D := by
    rcases hσ with h | h <;> rw [h] at hsign ⊢ <;> omega
  have h2 : kroneckerDisc D 2 = kroneckerTwo D := by
    simp [kroneckerDisc, Nat.Prime.factorization_self Nat.prime_two]
  rw [heckeTPlusFour_of_not_minusIdx k c (not_minusIdx_kohnenDisc_mul_sq hD m)]
  unfold heckeTPlusFourFormula
  rw [h2, show 4 * (D.natAbs * m ^ 2) = D.natAbs * (2 * m) ^ 2 by ring]
  rcases Nat.even_or_odd' m with ⟨u, rfl | rfl⟩
  · have e2 : kroneckerTwo ((-1) ^ k * ((D.natAbs * (2 * u) ^ 2 : ℕ) : ℤ)) = 0 := by
      unfold kroneckerTwo
      rw [if_pos]
      exact ⟨(-1) ^ k * D.natAbs * (2 * u ^ 2), by push_cast; ring⟩
    have e3 : 4 ∣ D.natAbs * (2 * u) ^ 2 := ⟨D.natAbs * u ^ 2, by ring⟩
    have e4 : D.natAbs * (2 * u) ^ 2 / 4 = D.natAbs * (2 * u / 2) ^ 2 := by
      rw [Nat.mul_div_cancel_left u two_pos]
      exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
    have e5 : 2 ∣ 2 * u := ⟨u, rfl⟩
    rw [e2, if_pos e3, e4, if_pos e5, if_pos e5]
    simp
  · have hodd : ¬ 2 ∣ 2 * u + 1 := by omega
    have hm8 := sq_mod_eight_of_odd _ hodd
    have e2 : kroneckerTwo ((-1) ^ k * ((D.natAbs * (2 * u + 1) ^ 2 : ℕ) : ℤ)) = kroneckerTwo D := by
      rw [show (-1 : ℤ) ^ k * ((D.natAbs * (2 * u + 1) ^ 2 : ℕ) : ℤ) = D * ((2 * u + 1 : ℕ) : ℤ) ^ 2 by
        rw [show (-1 : ℤ) ^ k * ((D.natAbs * (2 * u + 1) ^ 2 : ℕ) : ℤ) =
          ((-1) ^ k * (D.natAbs : ℤ)) * ((2 * u + 1 : ℕ) : ℤ) ^ 2 by push_cast; ring, hDabs]]
      have hx : (D * ((2 * u + 1 : ℕ) : ℤ) ^ 2) % 8 = D % 8 := by
        rw [Int.mul_emod, hm8]; simp
      unfold kroneckerTwo
      generalize D * ((2 * u + 1 : ℕ) : ℤ) ^ 2 = x at hx
      by_cases hd : 2 ∣ D
      · rw [if_pos hd, if_pos (by omega)]
      · rw [if_neg hd, if_neg (by omega)]
        by_cases h8 : D % 8 = 1 ∨ D % 8 = 7
        · rw [if_pos h8, if_pos (by omega)]
        · rw [if_neg h8, if_neg (by omega)]
    rw [e2, if_neg hodd, if_neg hodd]
    by_cases h4 : 4 ∣ D.natAbs * (2 * u + 1) ^ 2
    · rw [if_pos h4]
      have hcop : Nat.Coprime 4 ((2 * u + 1) ^ 2) := by
        have : Nat.Coprime 2 (2 * u + 1) := by
          exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
        simpa using Nat.Coprime.pow 2 2 this
      obtain ⟨s, hs⟩ := hcop.dvd_of_dvd_mul_right h4
      have hz : c (D.natAbs * (2 * u + 1) ^ 2 / 4) = 0 := by
        apply hc
        have hD4 : D = 4 * ((-1) ^ k * (s : ℤ)) := by
          rw [← hDabs, hs]; push_cast; ring
        have hD4' : D % 4 = 0 := by omega
        have hq : D.natAbs * (2 * u + 1) ^ 2 / 4 = s * (2 * u + 1) ^ 2 := by
          rw [hs, mul_assoc]; exact Nat.mul_div_cancel_left _ (by norm_num)
        rcases hD.1 with ⟨h1, _⟩ | ⟨m', hm', hm23, _⟩
        · omega
        · have hm'e : m' = (-1) ^ k * (s : ℤ) := by omega
          rw [hq]
          have : (-1 : ℤ) ^ k * ((s * (2 * u + 1) ^ 2 : ℕ) : ℤ) = m' * ((2 * u + 1 : ℕ) : ℤ) ^ 2 := by
            rw [hm'e]; push_cast; ring
          have h4' : (((2 * u + 1 : ℕ) : ℤ) ^ 2) % 4 = 1 := by omega
          rw [this, Int.mul_emod, h4']
          omega
      rw [hz]
    · rw [if_neg h4]; simp

/-- **The $D$-th lift intertwines $T^+(4)$ and $T(2)$** on plus sequences. -/
@[kb "kohnen1980" "the D-th lift carries T⁺(4) to T(2), on coefficients [unverified]"]
theorem kohnenLiftCoeff_heckeTPlusFour (k : ℕ) {D : ℤ} (hD : KohnenDisc k D) {c : ℕ → ℂ} (hc : c ∈ plusSeq k) :
    kohnenLiftCoeff k D (heckeTPlusFour k c) = heckeTInt (2 * k) 1 1 2 (kohnenLiftCoeff k D c) := by
  funext n
  set F : ℕ → ℂ := fun d ↦ (kroneckerDisc D d : ℂ) * (d : ℂ) ^ ((k : ℤ) - 1) with hF
  set B : ℕ → ℂ := fun m ↦ c (D.natAbs * m ^ 2) with hB
  have hFmul : ∀ d, d ≠ 0 → F (2 * d) = F 2 * F d := by
    intro d hd
    simp only [hF]
    rw [kroneckerDisc_two_mul D hd]
    push_cast
    rw [mul_zpow]
    ring
  have hF2 : F 2 = (kroneckerDisc D 2 : ℂ) * (2 : ℂ) ^ ((k : ℤ) - 1) := by simp [hF]
  have hψ : ∀ x, (1 : DirichletCharacter ℂ 1) x = 1 := fun x ↦ MulChar.one_apply (isUnit_of_subsingleton _)
  have hpt : (fun m ↦ heckeTPlusFour k c (D.natAbs * m ^ 2)) = fun m ↦ B (2 * m) +
      (kroneckerDisc D 2 : ℂ) * (2 : ℂ) ^ ((k : ℤ) - 1) * (if 2 ∣ m then 0 else B m) +
      (2 : ℂ) ^ (2 * (k : ℤ) - 1) * (if 2 ∣ m then B (m / 2) else 0) :=
    funext fun m ↦ heckeTPlusFour_Dsq k hD hc m
  simp only [heckeTInt, kohnenLiftCoeff_eq_dsum, ← hF, ← hB, hψ]
  rw [hpt, dsum_lin3, liftDsum_mul_prime F B Nat.prime_two hFmul, hF2]
  have hV := liftDsum_V F B two_pos n
  rw [hV]
  push_cast
  split_ifs <;> simp

/-- **An eigen-sequence of all $T(p)$ with $b(1) = 0$ vanishes in positive degrees.** -/
theorem eq_zero_of_heckeTInt_eigen {w : ℕ} {b : ℕ → ℂ} (ev : ℕ → ℂ)
    (h : ∀ p : ℕ, p.Prime → heckeTInt w 1 1 p b = ev p • b) (h1 : b 1 = 0) : ∀ n, 1 ≤ n → b n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  by_cases hn1 : n = 1
  · subst hn1; exact h1
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  set p := n.minFac with hpdef
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; omega
    · exact h0
  have hmn : m < n := by rw [hm]; nlinarith [hp.one_lt]
  have e := congrFun (h p hp) m
  simp only [heckeTInt, Pi.smul_apply, smul_eq_mul] at e
  have hbm : b m = 0 := ih m hmn hm0
  have hψ : (1 : DirichletCharacter ℂ 1) p = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
  rw [hbm, mul_zero, hψ] at e
  by_cases hpm : p ∣ m
  · obtain ⟨r, hr⟩ := hpm
    have hr0 : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; omega
      · exact h0
    have hrn : r < n := by rw [hm, hr]; nlinarith [hp.one_lt, hp.pos]
    rw [if_pos ⟨r, hr⟩, hr, Nat.mul_div_cancel_left _ hp.pos, ih r hrn hr0] at e
    rw [hm, hr]; simpa using e
  · rw [if_neg hpm] at e
    rw [hm]; simpa using e

end ModularFormsKB.HalfIntegral
