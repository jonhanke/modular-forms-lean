import ModularFormsKB.Iwaniec1997.KloostermanBounds
import ModularFormsKB.Citation
/-!
# Iwaniec, Chapter 4: twisted multiplicativity of Kloosterman sums

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Section 4.3, (4.12), p. 59. Page numbers are the
printed pages.

If $(q,r) = 1$ and $q\bar q \equiv 1 \pmod r$, $r\bar r \equiv 1 \pmod q$, then
$$S(m,n;qr) = S(\bar q m,\bar q n;r)\,S(\bar r m,\bar r n;q).$$
The proof uses the Chinese remainder theorem for the units of $\mathbb Z/qr$ and the identity
$e(x/qr) = e(x\bar r/q)\,e(x\bar q/r)$, which holds because $r\bar r + q\bar q \equiv 1 \pmod{qr}$.

## Items
- (4.12) `kloosterman_mul_of_coprime` (and `kloostermanMod_mul_of_coprime`).
- Theorem 4.5 (4.20) for squarefree moduli, from Weil's bound: `kloosterman_bound_squarefree`.
-/

open Complex Finset
open scoped ComplexConjugate Real

noncomputable section

namespace ModularFormsKB.Iwaniec1997

/-- $e(x/qr) = e(x\bar r/q)\,e(x\bar q/r)$ when $r\bar r + q\bar q \equiv 1 \pmod{qr}$. -/
theorem stdAddChar_mul_split {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q * r)]
    (qbar rbar : ℤ) (hqbar : (q : ℤ) * qbar ≡ 1 [ZMOD r]) (hrbar : (r : ℤ) * rbar ≡ 1 [ZMOD q])
    (hqr : Nat.Coprime q r) (z : ℤ) :
    ZMod.stdAddChar (z : ZMod (q * r)) =
      ZMod.stdAddChar ((rbar * z : ℤ) : ZMod q) * ZMod.stdAddChar ((qbar * z : ℤ) : ZMod r) := by
  have h1 : (q : ℤ) ∣ (r : ℤ) * rbar + q * qbar - 1 := by
    have := (Int.modEq_iff_dvd.1 hrbar.symm)
    have h2 : (q : ℤ) ∣ (q : ℤ) * qbar := dvd_mul_right _ _
    have := dvd_add this h2
    convert this using 1; ring
  have h2 : (r : ℤ) ∣ (r : ℤ) * rbar + q * qbar - 1 := by
    have := (Int.modEq_iff_dvd.1 hqbar.symm)
    have h2 : (r : ℤ) ∣ (r : ℤ) * rbar := dvd_mul_right _ _
    have := dvd_add this h2
    convert this using 1; ring
  have hcop : IsCoprime (q : ℤ) (r : ℤ) := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hqr
  obtain ⟨k, hk⟩ := hcop.mul_dvd h1 h2
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hk' : ((r : ℂ) * rbar + q * qbar) = 1 + (q * r) * k := by
    have := congrArg (Int.cast : ℤ → ℂ) hk
    push_cast at this
    linear_combination this
  have key : ((rbar * z : ℤ) : ℂ) / q + ((qbar * z : ℤ) : ℂ) / r =
      (z : ℂ) / ((q * r : ℕ) : ℂ) + ((z * k : ℤ) : ℂ) := by
    push_cast
    field_simp
    linear_combination (z : ℂ) * hk'
  have : (2 * π * I * ((rbar * z : ℤ) : ℂ) / q) + 2 * π * I * ((qbar * z : ℤ) : ℂ) / r =
      2 * π * I * (z : ℂ) / ((q * r : ℕ) : ℂ) + (z * k : ℤ) * (2 * π * I) := by
    rw [show (2 * π * I * ((rbar * z : ℤ) : ℂ) / q) + 2 * π * I * ((qbar * z : ℤ) : ℂ) / r =
      2 * π * I * (((rbar * z : ℤ) : ℂ) / q + ((qbar * z : ℤ) : ℂ) / r) by ring, key]
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The splitting of the standard character on $\mathbb Z/qr$ for a residue class. -/
theorem stdAddChar_mul_split' {q r : ℕ} [NeZero q] [NeZero r] [NeZero (q * r)]
    (qbar rbar : ℤ) (hqbar : (q : ℤ) * qbar ≡ 1 [ZMOD r]) (hrbar : (r : ℤ) * rbar ≡ 1 [ZMOD q])
    (hqr : Nat.Coprime q r) (x : ZMod (q * r)) :
    ZMod.stdAddChar x =
      ZMod.stdAddChar ((rbar : ZMod q) * ZMod.castHom (dvd_mul_right q r) (ZMod q) x) *
        ZMod.stdAddChar ((qbar : ZMod r) * ZMod.castHom (dvd_mul_left r q) (ZMod r) x) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have := stdAddChar_mul_split qbar rbar hqbar hrbar hqr z
  simp only [map_intCast]
  rw [this]
  push_cast
  rfl

/-- The unit equivalence from the Chinese remainder theorem. -/
def unitsCRT {q r : ℕ} (hqr : Nat.Coprime q r) :
    (ZMod (q * r))ˣ ≃* (ZMod q)ˣ × (ZMod r)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder hqr).toMulEquiv).trans MulEquiv.prodUnits

theorem unitsCRT_fst {q r : ℕ} (hqr : Nat.Coprime q r) (d : (ZMod (q * r))ˣ) :
    (((unitsCRT hqr d).1 : (ZMod q)ˣ) : ZMod q) = ZMod.castHom (dvd_mul_right q r) (ZMod q) (d : ZMod (q * r)) := by
  rw [ZMod.castHom_apply]
  exact Prod.fst_zmod_cast (d : ZMod (q * r))

theorem unitsCRT_snd {q r : ℕ} (hqr : Nat.Coprime q r) (d : (ZMod (q * r))ˣ) :
    (((unitsCRT hqr d).2 : (ZMod r)ˣ) : ZMod r) = ZMod.castHom (dvd_mul_left r q) (ZMod r) (d : ZMod (q * r)) := by
  rw [ZMod.castHom_apply]
  exact Prod.snd_zmod_cast (d : ZMod (q * r))

/-- **(4.12)** for `kloostermanMod`. -/
@[kb "iwaniec1997" "Section 4.3, (4.12), p. 59"]
theorem kloostermanMod_mul_of_coprime {q r : ℕ} [NeZero q] [NeZero r] (hqr : Nat.Coprime q r)
    (m n : ℤ) (qbar rbar : ℤ) (hqbar : (q : ℤ) * qbar ≡ 1 [ZMOD r]) (hrbar : (r : ℤ) * rbar ≡ 1 [ZMOD q]) :
    haveI : NeZero (q * r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
    kloostermanMod (q * r) (m : ZMod (q * r)) (n : ZMod (q * r)) =
      kloostermanMod r ((qbar * m : ℤ) : ZMod r) ((qbar * n : ℤ) : ZMod r) *
        kloostermanMod q ((rbar * m : ℤ) : ZMod q) ((rbar * n : ℤ) : ZMod q) := by
  have : NeZero (q * r) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne r)⟩
  unfold kloostermanMod
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Fintype.sum_equiv ((unitsCRT hqr).toEquiv.trans (Equiv.prodComm _ _)) _ _ fun d ↦ ?_
  rw [stdAddChar_mul_split' qbar rbar hqbar hrbar hqr]
  simp only [Equiv.trans_apply, Equiv.prodComm_apply,
    Prod.fst_swap, Prod.snd_swap, map_add, map_mul, map_intCast]
  have hinv : ∀ e : (ZMod (q * r))ˣ,
      ZMod.castHom (dvd_mul_right q r) (ZMod q) ((e⁻¹ : (ZMod (q * r))ˣ) : ZMod (q * r)) =
        ((((unitsCRT hqr e).1)⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    intro e
    rw [← unitsCRT_fst hqr, map_inv, Prod.fst_inv]
  have hinv' : ∀ e : (ZMod (q * r))ˣ,
      ZMod.castHom (dvd_mul_left r q) (ZMod r) ((e⁻¹ : (ZMod (q * r))ˣ) : ZMod (q * r)) =
        ((((unitsCRT hqr e).2)⁻¹ : (ZMod r)ˣ) : ZMod r) := by
    intro e
    rw [← unitsCRT_snd hqr, map_inv, Prod.snd_inv]
  rw [hinv, hinv', ← unitsCRT_fst hqr, ← unitsCRT_snd hqr]
  push_cast
  rw [mul_comm]
  have e1 : ∀ x : (ZMod (q * r))ˣ, (unitsCRT hqr).toEquiv x = unitsCRT hqr x := fun _ ↦ rfl
  simp only [e1]
  congr 2 <;> ring

/-- **(4.12)**: twisted multiplicativity of Kloosterman sums. If $(q,r)=1$, $q\bar q\equiv 1 \pmod r$ and
$r\bar r \equiv 1 \pmod q$, then $S(m,n;qr) = S(\bar q m,\bar q n;r)\,S(\bar r m,\bar r n;q)$. -/
@[kb "iwaniec1997" "Section 4.3, (4.12), p. 59"]
theorem kloosterman_mul_of_coprime {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : Nat.Coprime q r)
    (m n qbar rbar : ℤ) (hqbar : (q : ℤ) * qbar ≡ 1 [ZMOD r]) (hrbar : (r : ℤ) * rbar ≡ 1 [ZMOD q]) :
    kloosterman m n (q * r) =
      kloosterman (qbar * m) (qbar * n) r * kloosterman (rbar * m) (rbar * n) q := by
  have : NeZero q := ⟨hq.ne'⟩
  have : NeZero r := ⟨hr.ne'⟩
  have : NeZero (q * r) := ⟨mul_ne_zero hq.ne' hr.ne'⟩
  rw [kloosterman_def, kloosterman_def, kloosterman_def]
  exact kloostermanMod_mul_of_coprime hqr m n qbar rbar hqbar hrbar

/-- The prime case of Theorem 4.5, from Weil's bound: all three gcd cases. -/
theorem kloosterman_bound_prime (hW : WeilKloostermanBound) {p : ℕ} (hp : p.Prime) (m n : ℤ) :
    ‖kloosterman m n p‖ ≤
      Real.sqrt (Nat.gcd (Int.gcd m n) p) * Real.sqrt p * divisorCount p := by
  have hd : divisorCount p = 2 := by
    rw [divisorCount, hp.divisors, Finset.card_pair hp.one_lt.ne]
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0
  by_cases h : (p : ℤ) ∣ m ∧ (p : ℤ) ∣ n
  · have hg : Nat.gcd (Int.gcd m n) p = p :=
      Nat.gcd_eq_right (Int.dvd_gcd h.1 h.2)
    have : NeZero p := ⟨hp.ne_zero⟩
    have hS : kloosterman m n p = kloosterman 0 0 p :=
      kloosterman_congr (by simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd m p).2 h.1)
        (by simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd n p).2 h.2)
    rw [hS, kloosterman_zero_zero, Nat.totient_prime hp, hg, hd, Complex.norm_natCast]
    have h1 : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
    push_cast
    nlinarith
  · have hg : Nat.gcd (Int.gcd m n) p = 1 := by
      have : ¬ p ∣ Int.gcd m n := fun hd ↦ h
        ⟨(Int.natCast_dvd_natCast.2 hd).trans (Int.gcd_dvd_left _ _),
         (Int.natCast_dvd_natCast.2 hd).trans (Int.gcd_dvd_right _ _)⟩
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 this).symm
    rw [hg, hd]
    have := hW.bound p hp m n h
    simp only [Nat.cast_one, Real.sqrt_one, one_mul]
    push_cast
    linarith

/-- **Theorem 4.5** (4.20) for squarefree moduli, conditional on Weil's bound (4.19):
$|S(m,n;c)| \le (m,n,c)^{1/2} c^{1/2} \tau(c)$. -/
@[kb "iwaniec1997" "Section 4.3, Theorem 4.5, (4.20), p. 61"]
theorem kloosterman_bound_squarefree (hW : WeilKloostermanBound) {c : ℕ} (hc : Squarefree c)
    (hc0 : 0 < c) (m n : ℤ) :
    ‖kloosterman m n c‖ ≤
      Real.sqrt (Nat.gcd (Int.gcd m n) c) * Real.sqrt c * divisorCount c := by
  induction c using Nat.strong_induction_on generalizing m n with
  | _ c ih =>
  rcases Nat.lt_or_ge 1 c with h1 | h1
  · set p := c.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime h1.ne'
    obtain ⟨c', hc'⟩ : p ∣ c := Nat.minFac_dvd c
    have hc'0 : 0 < c' := by
      rcases Nat.eq_zero_or_pos c' with h | h
      · simp [h] at hc'; omega
      · exact h
    have hlt : c' < c := by
      rw [hc']; nlinarith [hp.two_le]
    rw [hc'] at hc
    obtain ⟨hcop, -, hsq'⟩ := Nat.squarefree_mul_iff.1 hc
    have hcop' : IsCoprime (p : ℤ) (c' : ℤ) := by
      exact_mod_cast Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨u, v, huv⟩ := hcop'
    have hu : (p : ℤ) * u ≡ 1 [ZMOD c'] := by
      apply (Int.modEq_iff_dvd.2 _).symm
      exact ⟨-v, by linarith⟩
    have hv : (c' : ℤ) * v ≡ 1 [ZMOD p] := by
      apply (Int.modEq_iff_dvd.2 _).symm
      exact ⟨-u, by linarith⟩
    rw [hc', kloosterman_mul_of_coprime hp.pos hc'0 hcop m n u v hu hv, norm_mul]
    have ihc := ih c' hlt hsq' hc'0 (u * m) (u * n)
    have hpp := kloosterman_bound_prime hW hp (v * m) (v * n)
    -- gcd computations
    have hucop : Nat.Coprime u.natAbs c' := by
      have : IsCoprime u (c' : ℤ) := ⟨p, v, by linarith⟩
      exact Int.isCoprime_iff_gcd_eq_one.1 this
    have hvcop : Nat.Coprime v.natAbs p := by
      have : IsCoprime v (p : ℤ) := ⟨c', u, by linarith⟩
      exact Int.isCoprime_iff_gcd_eq_one.1 this
    have g1 : Nat.gcd (Int.gcd (u * m) (u * n)) c' = Nat.gcd (Int.gcd m n) c' := by
      rw [Int.gcd_mul_left]; exact Nat.Coprime.gcd_mul_left_cancel _ hucop
    have g2 : Nat.gcd (Int.gcd (v * m) (v * n)) p = Nat.gcd (Int.gcd m n) p := by
      rw [Int.gcd_mul_left]; exact Nat.Coprime.gcd_mul_left_cancel _ hvcop
    rw [g1] at ihc
    rw [g2] at hpp
    have hg : Nat.gcd (Int.gcd m n) (p * c') =
        Nat.gcd (Int.gcd m n) p * Nat.gcd (Int.gcd m n) c' := Nat.Coprime.gcd_mul _ hcop
    have hτ : divisorCount (p * c') = divisorCount p * divisorCount c' :=
      Nat.Coprime.card_divisors_mul hcop
    rw [hg, hτ]
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _)]
    calc ‖kloosterman (u * m) (u * n) c'‖ * ‖kloosterman (v * m) (v * n) p‖
        ≤ _ := mul_le_mul ihc hpp (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have : c = 1 := by omega
    subst this
    simp [kloosterman_one, divisorCount]
  
end ModularFormsKB.Iwaniec1997
