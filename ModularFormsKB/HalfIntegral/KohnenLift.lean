/-
# Kohnen's plus space and the $D$-th lift, on coefficients

Level $4$, trivial character. Everything here is about coefficient
sequences $a : \mathbb N \to \mathbb C$; the forms-level statements are in
`ModularFormsKB/HalfIntegral/Abstract/KohnenReduction.lean`.

**The projection by coefficients.** `plusProj k` keeps $a(n)$ when $(-1)^k n \equiv 0, 1 \bmod 4$ and kills it otherwise.
It is a linear idempotent with range the plus condition `plusSeq k` (`plusProj_mem`, `plusProj_eq_self_iff`,
`plusProj_idem`), and commutes with $T(p^2)$ for odd $p$ (`heckeT_plusProj`). Kohnen's projection on *forms*
(Kohnen 1980 `kohnen1980`, Prop. 3 [unverified]) is a different operator, built from $W(4)$ and $U(4)$, since truncating
the $q$-expansion of a form need not give a form; on the plus space both are the identity.

**The $D$-th lift** (Kohnen 1980 `kohnen1980`, Thm. 1 [unverified]). For a fundamental discriminant $D$ with
$(-1)^kD > 0$ and $a$ the coefficients of $g \in S^+_{k+1/2}(4)$,
$$ (\mathcal S_D a)(n) = \sum_{d \mid n}\Big(\frac Dd\Big) d^{k-1} a\big(|D|n^2/d^2\big) $$
(`kohnenLiftCoeff`), with the Kronecker symbol $\left(\frac Dd\right)$ (`kroneckerDisc`). Proved:
`kohnenLiftCoeff_heckeT`: $\mathcal S_D(T(p^2)a) = T(p)\mathcal S_D(a)$ for every odd prime $p$ with $p^2 \nmid D$ (in
particular for fundamental $D$, `kohnenLiftCoeff_heckeT_of_fundamental`), with $T(p^2)$ of weight $k+\tfrac12$, level 4 and
$T(p)$ of weight $2k$, level 1. This is the same computation as `shimuraCoeff_heckeT`; the Kronecker symbol differs from
Shimura's character only at $d$ even, which does not matter for odd $p$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Kohnen

namespace ModularFormsKB.HalfIntegral

open Complex

/-! ### The projection by coefficients -/

/-- The index $n$ is outside the plus space: $(-1)^k n \equiv 2, 3 \bmod 4$. -/
def MinusIdx (k n : ℕ) : Prop := ((-1) ^ k * (n : ℤ)) % 4 = 2 ∨ ((-1) ^ k * (n : ℤ)) % 4 = 3

instance (k n : ℕ) : Decidable (MinusIdx k n) := by unfold MinusIdx; infer_instance

/-- **The plus projection on coefficients:** $a(n)$ is kept if $(-1)^k n \equiv 0,1 \bmod 4$ and replaced by $0$ otherwise. -/
noncomputable def plusProj (k : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun a n := if MinusIdx k n then 0 else a n
  map_add' a b := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c a := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem plusProj_apply (k : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    plusProj k a n = if MinusIdx k n then 0 else a n := rfl

/-- The plus projection lands in the plus condition. -/
theorem plusProj_mem (k : ℕ) (a : ℕ → ℂ) : plusProj k a ∈ plusSeq k := by
  intro n hn
  simp [plusProj_apply, show MinusIdx k n from hn]

/-- **The plus condition is the fixed space of the projection.** -/
theorem plusProj_eq_self_iff (k : ℕ) (a : ℕ → ℂ) : plusProj k a = a ↔ a ∈ plusSeq k := by
  constructor
  · intro h
    rw [← h]
    exact plusProj_mem k a
  · intro h
    funext n
    rw [plusProj_apply]
    split_ifs with hn
    · exact (h n hn).symm
    · rfl

/-- **The plus projection is idempotent.** -/
theorem plusProj_idem (k : ℕ) (a : ℕ → ℂ) : plusProj k (plusProj k a) = plusProj k a :=
  (plusProj_eq_self_iff k _).2 (plusProj_mem k a)

/-- **The range of the plus projection is the plus condition.** -/
theorem range_plusProj (k : ℕ) : LinearMap.range (plusProj k) = plusSeq k := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact plusProj_mem k b
  · intro h
    exact ⟨a, (plusProj_eq_self_iff k a).2 h⟩

private theorem odd_sq_mod_four {p : ℕ} (hp : Odd p) : ((p : ℤ) ^ 2) % 4 = 1 := by
  obtain ⟨m, rfl⟩ := hp
  push_cast
  have : (2 * (m : ℤ) + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
  rw [this]
  omega

private theorem minusIdx_sq_mul {p : ℕ} (hp : Odd p) (k m : ℕ) : MinusIdx k (p ^ 2 * m) ↔ MinusIdx k m := by
  have h := odd_sq_mod_four hp
  have : ((-1) ^ k * ((p ^ 2 * m : ℕ) : ℤ)) % 4 = ((-1) ^ k * (m : ℤ)) % 4 := by
    push_cast
    rw [show (-1 : ℤ) ^ k * ((p : ℤ) ^ 2 * m) = (p : ℤ) ^ 2 * ((-1) ^ k * m) by ring, Int.mul_emod, h, one_mul,
      Int.emod_emod_of_dvd _ (dvd_refl 4)]
  unfold MinusIdx
  rw [this]

/-- **The plus projection commutes with $T(p^2)$ for odd $p$:** $p^2 \equiv 1 \bmod 4$, so $p^2n$, $n$ and $n/p^2$ lie on
the same side of the plus condition. -/
theorem heckeT_plusProj {k N : ℕ} (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℕ → ℂ) : heckeT k N χ p (plusProj k a) = plusProj k (heckeT k N χ p a) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hdiv : ∀ n, p ^ 2 ∣ n → (MinusIdx k (n / p ^ 2) ↔ MinusIdx k n) := by
    rintro n ⟨m, rfl⟩
    rw [Nat.mul_div_cancel_left _ (pow_pos hp.pos 2), minusIdx_sq_mul hodd]
  funext n
  simp only [heckeT, plusProj_apply, minusIdx_sq_mul hodd]
  by_cases hn : MinusIdx k n
  · by_cases h : p ^ 2 ∣ n
    · simp [hn, h, (hdiv n h).2 hn]
    · simp [hn, h]
  · by_cases h : p ^ 2 ∣ n
    · simp [hn, h, mt (hdiv n h).1 hn]
    · simp [hn, h]

/-! ### The Kronecker symbol at odd primes -/

theorem kroneckerDisc_one (D : ℤ) : kroneckerDisc D 1 = 1 := by
  simp [kroneckerDisc]

/-- **The Kronecker symbol is multiplicative at odd primes:** $\left(\frac D{pd}\right) = \left(\frac Dp\right)\left(\frac Dd\right)$
for $p$ an odd prime and $d \ne 0$, where $\left(\frac Dp\right)$ is the Jacobi (Legendre) symbol. -/
theorem kroneckerDisc_prime_mul (D : ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {d : ℕ} (hd : d ≠ 0) :
    kroneckerDisc D (p * d) = jacobiSym D p * kroneckerDisc D d := by
  have h2p : ¬ 2 ∣ p := fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  have hfac : (p * d).factorization 2 = d.factorization 2 := by
    rw [Nat.factorization_mul hp.ne_zero hd, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h2p, zero_add]
  have hdiv : p * d / 2 ^ d.factorization 2 = p * (d / 2 ^ d.factorization 2) :=
    Nat.mul_div_assoc p (Nat.ordProj_dvd d 2)
  have hpos : d / 2 ^ d.factorization 2 ≠ 0 := (Nat.ordCompl_pos 2 hd).ne'
  unfold kroneckerDisc
  rw [hfac, hdiv, jacobiSym.mul_right' D hp.ne_zero hpos]
  ring

theorem kroneckerDisc_prime (D : ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    kroneckerDisc D p = jacobiSym D p := by
  simpa [kroneckerDisc_one] using kroneckerDisc_prime_mul D hp hp2 one_ne_zero

/-! ### The $D$-th lift -/

/-- **Kohnen's $D$-th lift on coefficients:** $(\mathcal S_D a)(n) = \sum_{d\mid n}\left(\frac Dd\right)d^{k-1}a(|D|n^2/d^2)$
(Kohnen 1980 `kohnen1980`, Thm. 1 [unverified]). Its value at $n = 0$ is $0$ (empty sum), as for a cusp form. -/
noncomputable def kohnenLiftCoeff (k : ℕ) (D : ℤ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (kroneckerDisc D d : ℂ) * (d : ℂ) ^ ((k : ℤ) - 1) * a (D.natAbs * (n / d) ^ 2)

@[simp] theorem kohnenLiftCoeff_zero (k : ℕ) (D : ℤ) (a : ℕ → ℂ) : kohnenLiftCoeff k D a 0 = 0 := by
  simp [kohnenLiftCoeff]

/-- **The $D$-th lift is linear** in the coefficient sequence. -/
noncomputable def kohnenLiftLin (k : ℕ) (D : ℤ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun := kohnenLiftCoeff k D
  map_add' a b := by
    funext n
    simp only [kohnenLiftCoeff, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext n
    simp only [kohnenLiftCoeff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    ring

@[simp] theorem kohnenLiftLin_apply (k : ℕ) (D : ℤ) (a : ℕ → ℂ) : kohnenLiftLin k D a = kohnenLiftCoeff k D a := rfl

/-- **$T(p)$ is linear** on coefficient sequences (integral weight). -/
noncomputable def heckeTIntLin (w M : ℕ) (ψ : DirichletCharacter ℂ M) (p : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun := heckeTInt w M ψ p
  map_add' a b := by
    funext n
    simp only [heckeTInt, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c a := by
    funext n
    simp only [heckeTInt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[simp] theorem heckeTIntLin_apply (w M : ℕ) (ψ : DirichletCharacter ℂ M) (p : ℕ) (c : ℕ → ℂ) :
    heckeTIntLin w M ψ p c = heckeTInt w M ψ p c := rfl

/-! The proof of the Hecke equivariance repeats the divisor-sum manipulations of `ShimuraLift.lean` (private there). -/

/-- Divisor-antidiagonal sum $\sum_{de = n} f(d)g(e)$. -/
private noncomputable def dsum (f g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2

private theorem dsum_filter_dvd (f g : ℕ → ℂ) {p : ℕ} (hp : 0 < p) (n : ℕ) :
    ∑ x ∈ (p * n).divisorsAntidiagonal with p ∣ x.2, f x.1 * g x.2 = dsum f (fun m ↦ g (p * m)) n := by
  unfold dsum
  refine Finset.sum_nbij' (fun x ↦ (x.1, x.2 / p)) (fun y ↦ (y.1, p * y.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨hde, hn⟩, c, rfl⟩ := hx
    rw [Nat.mul_div_cancel_left _ hp]
    refine ⟨?_, fun h ↦ hn (by simp [h])⟩
    have : p * (d * c) = p * n := by rw [← hde]; ring
    exact Nat.eq_of_mul_eq_mul_left hp this
  · rintro ⟨d, e⟩ hy
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hy ⊢
    obtain ⟨hde, hn⟩ := hy
    refine ⟨⟨by rw [← hde]; ring, mul_ne_zero hp.ne' hn⟩, dvd_mul_right _ _⟩
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_filter] at hx
    simp [Nat.mul_div_cancel' hx.2]
  · rintro ⟨d, e⟩ _
    simp [Nat.mul_div_cancel_left _ hp]
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_filter] at hx
    simp [Nat.mul_div_cancel' hx.2]

private theorem dsum_filter_not_dvd (f g : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ∑ x ∈ (p * n).divisorsAntidiagonal with ¬ p ∣ x.2, f x.1 * g x.2 =
      ∑ y ∈ n.divisorsAntidiagonal with ¬ p ∣ y.2, f (p * y.1) * g y.2 := by
  have hp0 := hp.pos
  refine Finset.sum_nbij' (fun x ↦ (x.1 / p, x.2)) (fun y ↦ (p * y.1, y.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨hde, hn⟩, he⟩ := hx
    have hd : p ∣ d := by
      have : p ∣ d * e := ⟨n, hde⟩
      exact ((Nat.Prime.dvd_mul hp).1 this).resolve_right he
    obtain ⟨c, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ hp0]
    refine ⟨⟨?_, fun h ↦ hn (by simp [h])⟩, he⟩
    have : p * (c * e) = p * n := by rw [← hde]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  · rintro ⟨d, e⟩ hy
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hy ⊢
    obtain ⟨⟨hde, hn⟩, he⟩ := hy
    exact ⟨⟨by rw [← hde]; ring, mul_ne_zero hp0.ne' hn⟩, he⟩
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨⟨hde, hn⟩, he⟩ := hx
    have hd : p ∣ d := ((Nat.Prime.dvd_mul hp).1 ⟨n, hde⟩).resolve_right he
    simp [Nat.mul_div_cancel' hd]
  · rintro ⟨d, e⟩ _
    simp [Nat.mul_div_cancel_left _ hp0]
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨⟨hde, hn⟩, he⟩ := hx
    have hd : p ∣ d := ((Nat.Prime.dvd_mul hp).1 ⟨n, hde⟩).resolve_right he
    simp [Nat.mul_div_cancel' hd]

private theorem dsum_mul_prime (f g : ℕ → ℂ) {p : ℕ} (hp : p.Prime)
    (hf : ∀ d, d ≠ 0 → f (p * d) = f p * f d) (n : ℕ) :
    dsum f g (p * n) = dsum f (fun m ↦ g (p * m)) n +
      f p * dsum f (fun m ↦ if p ∣ m then 0 else g m) n := by
  rw [dsum, ← Finset.sum_filter_add_sum_filter_not _ (fun x ↦ p ∣ x.2),
    dsum_filter_dvd f g hp.pos, dsum_filter_not_dvd f g hp]
  congr 1
  rw [dsum, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx1 : x.1 ≠ 0 := by
    rw [Nat.mem_divisorsAntidiagonal] at hx
    rintro h; exact hx.2 (by rw [← hx.1, h, zero_mul])
  split_ifs <;> simp [hf _ hx1]; ring

private theorem dsum_V (f g : ℕ → ℂ) {p : ℕ} (hp : 0 < p) (n : ℕ) :
    dsum f (fun m ↦ if p ∣ m then g (m / p) else 0) n = if p ∣ n then dsum f g (n / p) else 0 := by
  split_ifs with hn
  · obtain ⟨n', rfl⟩ := hn
    have h := dsum_filter_dvd f (fun m ↦ g (m / p)) hp n'
    simp only [Nat.mul_div_cancel_left _ hp] at h
    rw [Nat.mul_div_cancel_left _ hp, dsum, ← h, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs with h
    · simp
    · simp
  · refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have : ¬ p ∣ x.2 := fun h ↦ hn (hx.1 ▸ dvd_mul_of_dvd_right h _)
    simp [this]

private theorem kohnenLiftCoeff_eq_dsum (k : ℕ) (D : ℤ) (a : ℕ → ℂ) (n : ℕ) :
    kohnenLiftCoeff k D a n =
      dsum (fun d ↦ (kroneckerDisc D d : ℂ) * (d : ℂ) ^ ((k : ℤ) - 1)) (fun m ↦ a (D.natAbs * m ^ 2)) n :=
  (Nat.sum_divisorsAntidiagonal
    (fun d e ↦ (kroneckerDisc D d : ℂ) * (d : ℂ) ^ ((k : ℤ) - 1) * a (D.natAbs * e ^ 2))).symm

private theorem jacobiSym_sq_prime' (m : ℕ) {p : ℕ} (hp : p.Prime) :
    jacobiSym (m : ℤ) p ^ 2 = if p ∣ m then 0 else 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  split_ifs with h
  · have : jacobiSym (m : ℤ) p = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      intro hc
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.symm hc) h
    rw [this]; norm_num
  · apply jacobiSym.sq_one
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm

/-- The trivial character mod 4 is $1$ at odd primes. -/
private theorem one_char_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (1 : DirichletCharacter ℂ (4 * 1)) p = 1 := by
  apply MulChar.one_apply
  rw [ZMod.isUnit_iff_coprime]
  have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
  simpa using Nat.Coprime.pow_right 2 h2

/-- $T(p^2)a$ at $|D|m^2$, for odd $p$ with $p^2 \nmid D$ and $(-1)^k|D| = D$. -/
private theorem heckeT_Dsq (k : ℕ) {D : ℤ} (hD : (-1) ^ k * (D.natAbs : ℤ) = D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : ¬ p ^ 2 ∣ D.natAbs) (a : ℕ → ℂ) (m : ℕ) :
    heckeT k 1 1 p a (D.natAbs * m ^ 2) = a (D.natAbs * (p * m) ^ 2) +
      (kroneckerDisc D p : ℂ) * (p : ℂ) ^ ((k : ℤ) - 1) * (if p ∣ m then 0 else a (D.natAbs * m ^ 2)) +
      (p : ℂ) ^ (2 * (k : ℤ) - 1) * (if p ∣ m then a (D.natAbs * (m / p) ^ 2) else 0) := by
  set t := D.natAbs with htdef
  have hdvd : p ^ 2 ∣ t * m ^ 2 ↔ p ∣ m := by
    constructor
    · intro h
      by_contra hm
      have hc : Nat.Coprime (p ^ 2) (m ^ 2) := Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
      exact ht (hc.dvd_of_dvd_mul_right h)
    · intro h
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd h 2) _
  have hJ : (jacobiSym ((-1) ^ k * ((t * m ^ 2 : ℕ) : ℤ)) p : ℂ) =
      (jacobiSym D p : ℂ) * (if p ∣ m then 0 else 1) := by
    rw [show (-1) ^ k * ((t * m ^ 2 : ℕ) : ℤ) = ((-1) ^ k * (t : ℤ)) * (m : ℤ) ^ 2 by push_cast; ring, hD,
      jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym_sq_prime' m hp]
    split_ifs <;> simp
  rw [heckeT, hJ, if_congr hdvd rfl rfl, kroneckerDisc_prime D hp hp2, one_char_odd hp hp2]
  have h1 : p ^ 2 * (t * m ^ 2) = t * (p * m) ^ 2 := by ring
  rw [h1]
  split_ifs with hm
  · obtain ⟨c, rfl⟩ := hm
    rw [show t * (p * c) ^ 2 / p ^ 2 = t * c ^ 2 by
        rw [show t * (p * c) ^ 2 = p ^ 2 * (t * c ^ 2) by ring, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)],
      Nat.mul_div_cancel_left _ hp.pos]
    ring
  · ring

/-- **The $D$-th lift intertwines $T(p^2)$ and $T(p)$ for odd $p$** (Kohnen 1980 `kohnen1980`, Thm. 1 [unverified]): for
$(-1)^k D > 0$, every odd prime $p$ with $p^2 \nmid D$, every coefficient sequence $a$ and every $n$,
$\mathcal S_D(T(p^2)a)(n) = (T(p)\mathcal S_D a)(n)$, with $T(p^2)$ of weight $k+\tfrac12$ on $\Gamma_0(4)$ and $T(p)$ of
weight $2k$ on $\mathrm{SL}_2(\mathbb Z)$. Purely formal. -/
@[kb "kohnen1980" "Thm. 1: the D-th lift commutes with T(p²) ↦ T(p), p odd, on coefficients [unverified]"]
theorem kohnenLiftCoeff_heckeT (k : ℕ) {D : ℤ} (hD : 0 < (-1) ^ k * D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : ¬ (p ^ 2 : ℤ) ∣ D) (a : ℕ → ℂ) (n : ℕ) :
    kohnenLiftCoeff k D (heckeT k 1 1 p a) n = heckeTInt (2 * k) 1 1 p (kohnenLiftCoeff k D a) n := by
  have hDabs : (-1) ^ k * (D.natAbs : ℤ) = D := by
    rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] at hD ⊢ <;> omega
  have ht' : ¬ p ^ 2 ∣ D.natAbs := by
    intro h
    exact ht (Int.dvd_natAbs.1 (by exact_mod_cast h))
  set F : ℕ → ℂ := fun d ↦ (kroneckerDisc D d : ℂ) * (d : ℂ) ^ ((k : ℤ) - 1) with hF
  set B : ℕ → ℂ := fun m ↦ a (D.natAbs * m ^ 2) with hB
  have hFmul : ∀ d, d ≠ 0 → F (p * d) = F p * F d := by
    intro d hd
    simp only [hF]
    rw [kroneckerDisc_prime_mul D hp hp2 hd, kroneckerDisc_prime D hp hp2]
    push_cast
    rw [mul_zpow]
    ring
  have hψ : (1 : DirichletCharacter ℂ 1) p = 1 := MulChar.one_apply (isUnit_of_subsingleton _)
  simp only [heckeTInt, kohnenLiftCoeff_eq_dsum, ← hF, ← hB, hψ]
  rw [dsum_mul_prime F B hp hFmul, ← mul_ite_zero, ← dsum_V F B hp.pos]
  unfold dsum
  simp only [hB, heckeT_Dsq k hDabs hp hp2 ht' a, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  push_cast
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [hF]; ring
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    ring

/-- **A fundamental discriminant is not divisible by $p^2$** for odd primes $p$. -/
theorem not_sq_dvd_of_fundamental {D : ℤ} (hD : IsFundamentalDiscriminant D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ (p ^ 2 : ℤ) ∣ D := by
  have hpu : ¬ IsUnit (p : ℤ) := by
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast]; exact hp.one_lt.ne'
  rcases hD with ⟨_, hsq⟩ | ⟨m, rfl, _, hsq⟩
  · intro h
    exact hpu (hsq p (by simpa [sq] using h))
  · intro h
    have hcop : IsCoprime ((p : ℤ) ^ 2) 4 := by
      have : IsCoprime (p : ℤ) 2 := by
        rw [Int.isCoprime_iff_gcd_eq_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, Int.gcd_natCast_natCast]
        exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
      exact (this.pow_left).pow_right (n := 2) |>.of_isCoprime_of_dvd_right (by norm_num)
    exact hpu (hsq p (by simpa [sq] using hcop.dvd_of_dvd_mul_left h))

/-- **Hecke equivariance for the discriminants of Kohnen's theorem:** fundamental $D$ with $(-1)^k D > 0$, odd $p$. -/
theorem kohnenLiftCoeff_heckeT_of_fundamental (k : ℕ) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ → ℂ) :
    kohnenLiftCoeff k D (heckeT k 1 1 p a) = heckeTInt (2 * k) 1 1 p (kohnenLiftCoeff k D a) :=
  funext fun n ↦ kohnenLiftCoeff_heckeT k hsign hp hp2 (not_sq_dvd_of_fundamental hD hp hp2) a n

end ModularFormsKB.HalfIntegral
