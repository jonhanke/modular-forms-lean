/-
# Periodicity of Shimura's symbol and the multiplier under $T$

For $4 \mid c$ and odd $d$, Shimura's symbol $(c/d)$ (`shimuraSym`) is periodic in $d$ with period
$c$, across sign changes of $d$:
$$\Big(\frac{c}{d+c}\Big) = \Big(\frac cd\Big).$$
For positive $d$ and $d + c$ this is the periodicity of the Jacobi symbol in the denominator (`jacobiSym.mod_right`). When
$d$ and $d + c$ have opposite signs, $|d| + |d+c| = |c|$, and it reduces to `jacobiSym_eq_of_add`: for $a \in \mathbb N$ and odd
$n, m$ with $4a \mid n + m$, $J(a \mid n) = J(a \mid m)$ (quadratic reciprocity), together with
$J(-1 \mid n) = -J(-1 \mid m)$ to account for Shimura's sign when $c < 0$.

Consequence: $j(\gamma T, z) = j(\gamma, z + 1)$ for $\gamma \in \Gamma_0(4)$ (`thetaMultCD_add_right`).
-/
import ModularFormsKB.HalfIntegral.Theta

namespace ModularFormsKB.HalfIntegral

open Complex

/-- Odd-`a` case of `jacobiSym_eq_of_add`. -/
theorem jacobiSym_eq_of_add_odd {a : ℕ} (ha : Odd a) {n m : ℕ} (hn : Odd n) (hm : Odd m)
    (h : 4 * a ∣ n + m) : jacobiSym a n = jacobiSym a m := by
  rw [jacobiSym.quadratic_reciprocity' ha hn, jacobiSym.quadratic_reciprocity' ha hm]
  have h4 : (n + m) % 4 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_mul_right 4 a) h)
  have hdv : (a : ℤ) ∣ (n : ℤ) + m := by
    have : a ∣ n + m := dvd_trans (dvd_mul_left a 4) h
    exact_mod_cast this
  have hmod : (m : ℤ) % (a : ℤ) = (-(n : ℤ)) % (a : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, sub_neg_eq_add, add_comm]
    exact Int.emod_eq_zero_of_dvd hdv
  have hJ : jacobiSym m a = ZMod.χ₄ (a : ZMod 4) * jacobiSym n a := by
    rw [jacobiSym.mod_left' hmod]
    exact jacobiSym.neg _ ha
  rw [hJ]
  have hn2 := Nat.odd_iff.mp hn
  have hm2 := Nat.odd_iff.mp hm
  have ha2 := Nat.odd_iff.mp ha
  have hq : qrSign n a = qrSign m a * ZMod.χ₄ (a : ZMod 4) := by
    rw [qrSign.neg_one_pow hn ha, qrSign.neg_one_pow hm ha]
    rcases Nat.odd_mod_four_iff.mp ha2 with h1 | h1
    · rw [ZMod.χ₄_nat_one_mod_four h1]
      have e1 : Even (n / 2 * (a / 2)) := Even.mul_left (Nat.even_iff.mpr (by omega)) _
      have e2 : Even (m / 2 * (a / 2)) := Even.mul_left (Nat.even_iff.mpr (by omega)) _
      rw [e1.neg_one_pow, e2.neg_one_pow]; simp
    · rw [ZMod.χ₄_nat_three_mod_four h1]
      have o : Odd (a / 2) := Nat.odd_iff.mpr (by omega)
      rcases Nat.odd_mod_four_iff.mp hn2 with h2 | h2
      · have e1 : Even (n / 2 * (a / 2)) := Even.mul_right (Nat.even_iff.mpr (by omega)) _
        have e2 : Odd (m / 2 * (a / 2)) := Odd.mul (Nat.odd_iff.mpr (by omega)) o
        rw [e1.neg_one_pow, e2.neg_one_pow]; simp
      · have e1 : Odd (n / 2 * (a / 2)) := Odd.mul (Nat.odd_iff.mpr (by omega)) o
        have e2 : Even (m / 2 * (a / 2)) := Even.mul_right (Nat.even_iff.mpr (by omega)) _
        rw [e1.neg_one_pow, e2.neg_one_pow]; simp
  rw [hq]; ring

/-- For $a \in \mathbb N$ and odd $n, m$ with $4a \mid n + m$: $J(a \mid n) = J(a \mid m)$. -/
theorem jacobiSym_eq_of_add (a : ℕ) {n m : ℕ} (hn : Odd n) (hm : Odd m) (h : 4 * a ∣ n + m) :
    jacobiSym a n = jacobiSym a m := by
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨x, hx⟩ := hn
    simp at h
    omega
  obtain ⟨e, a', ha1', ha2⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 2 (by simp)
  have ha1 : Odd a' := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ha1')
  subst ha2
  have hodd : jacobiSym a' n = jacobiSym a' m :=
    jacobiSym_eq_of_add_odd ha1 hn hm (dvd_trans (Nat.mul_dvd_mul_left 4
      (dvd_mul_left a' (2 ^ e))) h)
  rw [Nat.cast_mul, jacobiSym.mul_left, jacobiSym.mul_left, Nat.cast_pow, jacobiSym.pow_left,
    jacobiSym.pow_left, Nat.cast_two, jacobiSym.at_two hn, jacobiSym.at_two hm, hodd]
  congr 1
  rcases e with - | e
  · simp
  · have h8 : (n + m) % 8 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      refine dvd_trans ?_ h
      exact ⟨2 ^ e * a', by rw [pow_succ]; ring⟩
    have hn2 := Nat.odd_iff.mp hn
    have hm2 := Nat.odd_iff.mp hm
    have hχ : ZMod.χ₈ (n : ZMod 8) = ZMod.χ₈ (m : ZMod 8) := by
      rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight]
      split_ifs <;> omega
    rw [hχ]

theorem chi4_opp {b b' : ℕ} (hb : Odd b) (hb' : Odd b') (h : 4 ∣ b + b') :
    ZMod.χ₄ (b' : ZMod 4) = - ZMod.χ₄ (b : ZMod 4) := by
  have h1 := Nat.odd_iff.mp hb
  have h2 := Nat.odd_iff.mp hb'
  rcases Nat.odd_mod_four_iff.mp h1 with h3 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h3, ZMod.χ₄_nat_three_mod_four (by omega)]
  · rw [ZMod.χ₄_nat_three_mod_four h3, ZMod.χ₄_nat_one_mod_four (by omega)]; simp

theorem jacobiSym_opp (k : ℤ) {b b' : ℕ} (hb : Odd b) (hb' : Odd b')
    (h : 4 * k.natAbs ∣ b + b') :
    jacobiSym k b = (if k < 0 then -1 else 1) * jacobiSym k b' := by
  have key := jacobiSym_eq_of_add k.natAbs hb hb' h
  rcases lt_or_ge k 0 with hk | hk
  · have hk' : k = -(k.natAbs : ℤ) := by omega
    have e1 : jacobiSym k b = ZMod.χ₄ (b : ZMod 4) * jacobiSym k.natAbs b := by
      have := jacobiSym.neg (k.natAbs : ℤ) hb
      rwa [← hk'] at this
    have e2 : jacobiSym k b' = ZMod.χ₄ (b' : ZMod 4) * jacobiSym k.natAbs b' := by
      have := jacobiSym.neg (k.natAbs : ℤ) hb'
      rwa [← hk'] at this
    simp only [hk, ↓reduceIte]
    rw [e1, e2, chi4_opp hb hb' (dvd_trans (dvd_mul_right 4 _) h), key]
    ring
  · have hk' : k = (k.natAbs : ℤ) := by omega
    simp only [not_lt.mpr hk, ↓reduceIte, one_mul]
    have := key
    rw [← hk'] at this
    exact this

theorem jacobiSym_congr_of_dvd (k : ℤ) {b b' : ℕ} (hb : Odd b) (hb' : Odd b')
    (h : ((4 * k.natAbs : ℕ) : ℤ) ∣ (b' : ℤ) - b) : jacobiSym k b = jacobiSym k b' := by
  rw [jacobiSym.mod_right k hb, jacobiSym.mod_right k hb']
  congr 1
  have h2 : (b : ℤ) ≡ b' [ZMOD ((4 * k.natAbs : ℕ) : ℤ)] := (Int.modEq_iff_dvd.mpr h)
  exact Int.natCast_modEq_iff.mp h2

/-- **Shimura's symbol is periodic in the denominator** with period $c$, for $4 \mid c$ and odd $d$. -/
theorem shimuraSym_add_right {c d : ℤ} (hc : 4 ∣ c) (hd : Odd d) :
    shimuraSym c (d + c) = shimuraSym c d := by
  obtain ⟨k, rfl⟩ := hc
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  obtain ⟨m, hm⟩ := hd
  have hodde : Odd (d + 4 * k) := ⟨m + 2 * k, by omega⟩
  have hd' : Odd d.natAbs := Int.natAbs_odd.mpr ⟨m, hm⟩
  have he' : Odd (d + 4 * k).natAbs := Int.natAbs_odd.mpr hodde
  have hJ : ∀ b : ℕ, Odd b → jacobiSym (4 * k) b = jacobiSym k b := by
    intro b hb
    rw [jacobiSym.mul_left, jacobiSym.at_four hb, one_mul]
  have hN : ((4 * k.natAbs : ℕ) : ℤ) ∣ 4 * k := by
    push_cast
    exact mul_dvd_mul_left 4 (abs_dvd_self k)
  unfold shimuraSym
  rw [hJ _ hd', hJ _ he']
  have hd0 : d ≠ 0 := by omega
  have he0 : d + 4 * k ≠ 0 := by omega
  rcases lt_or_gt_of_ne hd0 with hdn | hdp <;> rcases lt_or_gt_of_ne he0 with hen | hep
  · -- both negative
    have hper : jacobiSym k (d + 4 * k).natAbs = jacobiSym k d.natAbs := by
      apply (jacobiSym_congr_of_dvd k hd' he' ?_).symm
      have : (((d + 4 * k).natAbs : ℕ) : ℤ) - (d.natAbs : ℤ) = -(4 * k) := by omega
      rw [this]
      exact (dvd_neg).mpr hN
    rw [hper]
    split_ifs <;> omega
  · -- d < 0, e > 0
    have hk : 0 < k := by omega
    have hsum : d.natAbs + (d + 4 * k).natAbs = 4 * k.natAbs := by omega
    have hdv : 4 * k.natAbs ∣ d.natAbs + (d + 4 * k).natAbs := by rw [hsum]
    have hnk : ¬ k < 0 := by omega
    rw [jacobiSym_opp k hd' he' hdv]
    simp only [hnk, ↓reduceIte]
    split_ifs <;> omega
  · -- d > 0, e < 0
    have hk : k < 0 := by omega
    have hsum : d.natAbs + (d + 4 * k).natAbs = 4 * k.natAbs := by omega
    have hdv : 4 * k.natAbs ∣ d.natAbs + (d + 4 * k).natAbs := by rw [hsum]
    rw [jacobiSym_opp k hd' he' hdv]
    simp only [hk, ↓reduceIte]
    split_ifs <;> omega
  · -- both positive
    have hper : jacobiSym k (d + 4 * k).natAbs = jacobiSym k d.natAbs := by
      apply (jacobiSym_congr_of_dvd k hd' he' ?_).symm
      have : (((d + 4 * k).natAbs : ℕ) : ℤ) - (d.natAbs : ℤ) = 4 * k := by omega
      rw [this]
      exact hN
    rw [hper]
    split_ifs <;> omega

/-- $\varepsilon_{d+c} = \varepsilon_d$ for $4 \mid c$. -/
theorem epsD_add_right {c d : ℤ} (hc : 4 ∣ c) : epsD (d + c) = epsD d := by
  obtain ⟨k, rfl⟩ := hc
  unfold epsD
  have : (d + 4 * k) % 4 = d % 4 := by omega
  rw [this]

/-- **The multiplier under $T$:** $j(\gamma T, z) = j(\gamma, z+1)$; the bottom row of $\gamma T$ is $(c, d + c)$. -/
theorem thetaMultCD_add_right {c d : ℤ} (hc : 4 ∣ c) (hd : Odd d) (z : ℂ) :
    thetaMultCD c (d + c) z = thetaMultCD c d (z + 1) := by
  unfold thetaMultCD
  rw [epsD_add_right hc, shimuraSym_add_right hc hd]
  congr 2
  push_cast
  ring

end ModularFormsKB.HalfIntegral
