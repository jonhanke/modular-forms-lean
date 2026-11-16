import ModularFormsKB.HalfIntegral.SerreStark

/-!
# Totally even characters are trivial on the square roots of `1`

`psi_eq_one_of_isTotallyEven`: if `ψ` modulo `r` is totally even (Serre–Stark, `IsTotallyEven`) and `4r² ∣ u² - 1`, then
`ψ(u) = 1`. **Proof.** At every prime `p ∣ r`, `p^e ∥ r`, the hypothesis gives `u ≡ ±1 mod p^e`
(`modEq_one_or_neg_one`: for `p` odd one of `u ∓ 1` is prime to `p`; for `p = 2`, `u = 2a + 1` and `2^{2e} ∣ a(a + 1)`).
So `u ≡ ∏_{p ∈ S} a_p mod r`, where `S` is the set of primes with `u ≢ 1 mod p^e` and `a_p ≡ -1 mod p^e`,
`a_p ≡ 1 mod r/p^e`; and `ψ(a_p) = 1` by total evenness.
-/

namespace ModularFormsKB.HalfIntegral

/-- If `p^{2e}` (times `4` when `p = 2`) divides `u² - 1`, then `u ≡ ±1 mod p^e`. -/
theorem modEq_one_or_neg_one {p e : ℕ} (hp : p.Prime) {u : ℤ}
    (h : ((p : ℤ) ^ (2 * e) * 4) ∣ u ^ 2 - 1) :
    u ≡ 1 [ZMOD (p : ℤ) ^ e] ∨ u ≡ -1 [ZMOD (p : ℤ) ^ e] := by
  have hfac : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
  have hpe : (p : ℤ) ^ e ∣ (p : ℤ) ^ (2 * e) := pow_dvd_pow _ (by omega)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases h1 : (p : ℤ) ∣ u - 1
  · by_cases h2 : (p : ℤ) ∣ u + 1
    · -- `p ∣ 2`, so `p = 2`
      have h3 : (p : ℤ) ∣ 2 := by
        have := dvd_sub h2 h1
        simpa using this
      have hp2 : p = 2 := by
        have := Int.natAbs_dvd_natAbs.mpr h3
        simp only [Int.natAbs_natCast] at this
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
      subst hp2
      obtain ⟨a, ha⟩ : ∃ a, u = 2 * a + 1 := by
        obtain ⟨c, hc⟩ := h1
        exact ⟨c, by push_cast at hc; linarith⟩
      have hdiv : (2 : ℤ) ^ (2 * e) ∣ a * (a + 1) := by
        have : (2 : ℤ) ^ (2 * e) * 4 ∣ a * (a + 1) * 4 := by
          have e1 : u ^ 2 - 1 = a * (a + 1) * 4 := by rw [ha]; ring
          rw [← e1]; exact_mod_cast h
        exact (mul_dvd_mul_iff_right (by norm_num)).mp this
      rcases Int.even_or_odd a with hae | hao
      · -- `a + 1` is odd, so prime to `2^{2e}`
        have hcop : IsCoprime ((2 : ℤ) ^ (2 * e)) (a + 1) := by
          apply IsCoprime.pow_left
          refine (Prime.coprime_iff_not_dvd Int.prime_two).mpr ?_
          rw [← even_iff_two_dvd, Int.not_even_iff_odd]
          exact hae.add_one
        have ha2 : (2 : ℤ) ^ (2 * e) ∣ a := hcop.dvd_of_dvd_mul_right hdiv
        left
        refine (Int.modEq_iff_dvd.mpr ?_).symm
        rw [ha]
        exact dvd_trans hpe (by simpa using dvd_mul_of_dvd_right ha2 2)
      · have hcop : IsCoprime ((2 : ℤ) ^ (2 * e)) a := by
          apply IsCoprime.pow_left
          refine (Prime.coprime_iff_not_dvd Int.prime_two).mpr ?_
          rw [← even_iff_two_dvd, Int.not_even_iff_odd]
          exact hao
        have ha2 : (2 : ℤ) ^ (2 * e) ∣ a + 1 := hcop.dvd_of_dvd_mul_left hdiv
        right
        refine (Int.modEq_iff_dvd.mpr ?_).symm
        rw [ha]
        have : 2 * a + 1 - (-1 : ℤ) = 2 * (a + 1) := by ring
        rw [this]
        exact dvd_trans hpe (by simpa using dvd_mul_of_dvd_right ha2 2)
    · -- `p ∤ u + 1`: `p^{2e} ∣ u - 1`
      have hcop : IsCoprime ((p : ℤ) ^ (2 * e)) (u + 1) :=
        IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpz).mpr h2)
      have : (p : ℤ) ^ (2 * e) ∣ (u - 1) * (u + 1) := by
        rw [← hfac]; exact dvd_trans (dvd_mul_right _ _) h
      left
      exact (Int.modEq_iff_dvd.mpr (dvd_trans hpe (hcop.dvd_of_dvd_mul_right this))).symm
  · have hcop : IsCoprime ((p : ℤ) ^ (2 * e)) (u - 1) :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hpz).mpr h1)
    have : (p : ℤ) ^ (2 * e) ∣ (u - 1) * (u + 1) := by
      rw [← hfac]; exact dvd_trans (dvd_mul_right _ _) h
    right
    have h' : (p : ℤ) ^ e ∣ u + 1 := dvd_trans hpe (hcop.dvd_of_dvd_mul_left this)
    refine (Int.modEq_iff_dvd.mpr ?_).symm
    have : u - (-1 : ℤ) = u + 1 := by ring
    rw [this]
    exact h'

/-- For every prime `p` there is an integer `a ≡ -1 mod p^e`, `a ≡ 1 mod r/p^e` (`p^e ∥ r`). -/
theorem exists_localSign {r : ℕ} (hr : r ≠ 0) {p : ℕ} (hp : p.Prime) :
    ∃ a : ℤ, a ≡ -1 [ZMOD ((p ^ r.factorization p : ℕ) : ℤ)] ∧
      a ≡ 1 [ZMOD ((r / p ^ r.factorization p : ℕ) : ℤ)] := by
  have hcop : Nat.Coprime (p ^ r.factorization p) (r / p ^ r.factorization p) :=
    (Nat.coprime_ordCompl hp hr).pow_left _
  have hP1 : 1 ≤ p ^ r.factorization p := Nat.one_le_pow _ _ hp.pos
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop (p ^ r.factorization p - 1) 1
  refine ⟨k, ?_, ?_⟩
  · have h' : (k : ℤ) ≡ ((p ^ r.factorization p - 1 : ℕ) : ℤ) [ZMOD ((p ^ r.factorization p : ℕ) : ℤ)] :=
      Int.natCast_modEq_iff.mpr hk1
    refine h'.trans ?_
    rw [Nat.cast_sub hP1, Nat.cast_one]
    exact Int.modEq_iff_dvd.mpr ⟨-1, by push_cast; ring⟩
  · exact_mod_cast Int.natCast_modEq_iff.mpr hk2

/-- **A totally even character is trivial on every `u` with `4r² ∣ u² - 1`.** -/
theorem psi_eq_one_of_isTotallyEven {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r)
    (hψ : IsTotallyEven ψ) {u : ℤ} (hu : (4 * (r : ℤ) ^ 2) ∣ u ^ 2 - 1) :
    ψ (u : ZMod r) = 1 := by
  classical
  have hr : r ≠ 0 := NeZero.ne r
  -- local signs
  choose! a ha1 ha2 using fun (p : ℕ) (hp : p.Prime) ↦ exists_localSign hr hp
  set P := r.primeFactors
  set e : ℕ → ℕ := fun p ↦ r.factorization p
  set S := P.filter fun p ↦ ¬ u ≡ 1 [ZMOD ((p ^ e p : ℕ) : ℤ)]
  set w : ℤ := ∏ p ∈ S, a p
  -- `u ≡ w` modulo each `p^e`
  have hloc : ∀ p ∈ P, ((p ^ e p : ℕ) : ℤ) ∣ w - u := by
    intro p hpP
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpP
    set n := p ^ e p
    -- `u ≡ ±1`
    have hpm : u ≡ 1 [ZMOD (p : ℤ) ^ e p] ∨ u ≡ -1 [ZMOD (p : ℤ) ^ e p] := by
      apply modEq_one_or_neg_one hp
      refine dvd_trans ?_ hu
      have h1 : ((p : ℤ) ^ e p) ∣ r := by exact_mod_cast Nat.ordProj_dvd r p
      have : (p : ℤ) ^ (2 * e p) * 4 = 4 * ((p : ℤ) ^ e p) ^ 2 := by ring
      rw [this]
      exact mul_dvd_mul_left 4 (pow_dvd_pow_of_dvd h1 2)
    -- the other local signs are `1` modulo `n`
    have hother : ∀ q ∈ S, q ≠ p → a q ≡ 1 [ZMOD (n : ℤ)] := by
      intro q hqS hqp
      have hqP : q ∈ P := (Finset.mem_filter.mp hqS).1
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hqP
      have hdvd : n ∣ r / q ^ r.factorization q := by
        have hcop : Nat.Coprime n (q ^ r.factorization q) :=
          Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hqp.symm)
        have hn : n ∣ r := Nat.ordProj_dvd r p
        have hq' : q ^ r.factorization q ∣ r := Nat.ordProj_dvd r q
        exact (Nat.dvd_div_iff_mul_dvd hq').mpr (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop.symm hq' hn)
      exact Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hdvd) (ha2 q hq)
    -- compute in `ZMod n`
    rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
    have hw : ((w : ℤ) : ZMod n) = if p ∈ S then -1 else 1 := by
      rw [Int.cast_prod]
      split_ifs with hpS
      · rw [Finset.prod_eq_single_of_mem p hpS fun q hq hqp ↦ by
          rw [(ZMod.intCast_eq_intCast_iff _ _ n).mpr (hother q hq hqp)]; simp]
        rw [(ZMod.intCast_eq_intCast_iff _ _ n).mpr (ha1 p hp)]
        simp
      · refine Finset.prod_eq_one fun q hq ↦ ?_
        have hqp : q ≠ p := fun h ↦ hpS (h ▸ hq)
        rw [(ZMod.intCast_eq_intCast_iff _ _ n).mpr (hother q hq hqp)]
        simp
    rw [hw]
    by_cases hpS : p ∈ S
    · rw [if_pos hpS]
      have hn1 : ¬ u ≡ 1 [ZMOD (n : ℤ)] := (Finset.mem_filter.mp hpS).2
      have : u ≡ -1 [ZMOD (n : ℤ)] := by
        rcases hpm with h | h
        · exact absurd (by exact_mod_cast h) hn1
        · exact_mod_cast h
      rw [(ZMod.intCast_eq_intCast_iff _ _ n).mpr this]
      simp
    · rw [if_neg hpS]
      have : u ≡ 1 [ZMOD (n : ℤ)] := by
        by_contra hc
        exact hpS (Finset.mem_filter.mpr ⟨hpP, hc⟩)
      rw [(ZMod.intCast_eq_intCast_iff _ _ n).mpr this]
      simp
  -- `u ≡ w` modulo `r`
  have hrw : (r : ℤ) ∣ w - u := by
    have hprod : (∏ p ∈ P, ((p ^ e p : ℕ) : ℤ)) = r := by
      rw [← Nat.cast_prod]
      exact_mod_cast (Nat.prod_primeFactors_pow_factorization hr).symm
    rw [← hprod]
    refine Finset.prod_dvd_of_coprime ?_ hloc
    intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  have hcast : ((u : ℤ) : ZMod r) = ((w : ℤ) : ZMod r) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ r).mpr hrw
  rw [hcast, Int.cast_prod, map_prod]
  refine Finset.prod_eq_one fun p hpS ↦ ?_
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hpS).1
  exact hψ p hp (a p) (ha1 p hp) (ha2 p hp)

end ModularFormsKB.HalfIntegral
