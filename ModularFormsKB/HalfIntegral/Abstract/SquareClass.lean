/-
# Square classes of the plus space and fundamental discriminants

Elementary number theory used by
`ModularFormsKB/HalfIntegral/Abstract/WaldspurgerGround.lean`:
- the odd part of $|D|$ is squarefree for a fundamental discriminant $D$ (`IsFundamentalDiscriminant.not_sq_dvd_natAbs`);
- **square-class decomposition:** every $n \ge 1$ with $(-1)^k n \equiv 0, 1 \bmod 4$ is $|D|m^2$ for a fundamental
  discriminant $D$ with $(-1)^k D > 0$ and $m \ge 1$ (`exists_fundamentalDiscriminant_mul_sq`), and $D$, $m$ are unique
  (`fundamentalDiscriminant_mul_sq_unique`);
- Möbius inversion against a completely multiplicative weight (`sum_moebius_mul_inversion`).
-/
import ModularFormsKB.HalfIntegral.Abstract.Kohnen

namespace ModularFormsKB.HalfIntegral

/-- A squarefree natural number that is a square is `1`. -/
private lemma sqfree_eq_one_of_sq {a u : ℕ} (ha : Squarefree a) (h : a = u ^ 2) : a = 1 := by
  subst h
  have := ha u (by rw [sq])
  simp [Nat.isUnit_iff.mp this]

/-- Uniqueness of the squarefree part. -/
private lemma sqfree_eq_of_mul_sq {a b x y : ℕ} (ha : Squarefree a) (hb : Squarefree b) (hx : x ≠ 0)
    (h : a * x ^ 2 = b * y ^ 2) : a = b := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha.ne_zero)
  obtain ⟨g, a', b', hg0, hcop, rfl, rfl⟩ := Nat.exists_coprime' hg
  have ha' : Squarefree a' := Squarefree.of_mul_left ha
  have hb' : Squarefree b' := Squarefree.of_mul_left hb
  have h1 : a' * x ^ 2 = b' * y ^ 2 :=
    Nat.eq_of_mul_eq_mul_right hg0 (by linarith [h])
  have h2 : (b' * y) ^ 2 = (a' * b') * x ^ 2 := by
    calc (b' * y) ^ 2 = b' * (b' * y ^ 2) := by ring
      _ = b' * (a' * x ^ 2) := by rw [h1]
      _ = _ := by ring
  have h3 : x ^ 2 ∣ (b' * y) ^ 2 := ⟨a' * b', by rw [h2]; ring⟩
  obtain ⟨c, hc⟩ := (Nat.pow_dvd_pow_iff two_ne_zero).mp h3
  have h5 : a' * b' = c ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hx) 2) ?_
    rw [hc, mul_pow] at h2
    linarith [h2]
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) h5
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm)
    (by rw [mul_comm]; exact h5 : b' * a' = c ^ 2)
  rw [sqfree_eq_one_of_sq ha' hu, sqfree_eq_one_of_sq hb' hv]

/-- **The odd part of $|D|$ is squarefree:** for a fundamental discriminant $D$ and an odd prime $p$, $p^2 \nmid |D|$. -/
theorem IsFundamentalDiscriminant.not_sq_dvd_natAbs {D : ℤ} (hD : IsFundamentalDiscriminant D) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ D.natAbs := by
  intro hdvd
  have hpp : p * p ∣ D.natAbs := by rwa [← sq]
  rcases hD with ⟨-, hsq⟩ | ⟨m, rfl, -, hsq⟩
  · have := Int.squarefree_natAbs.mpr hsq p hpp
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  · have hsq' := Int.squarefree_natAbs.mpr hsq
    have h4 : (4 * m).natAbs = 4 * m.natAbs := by rw [Int.natAbs_mul]; rfl
    rw [h4] at hdvd
    have hcop : Nat.Coprime p 4 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have : p ∣ 2 ^ 2 := by simpa using h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
    have hcop2 : Nat.Coprime (p ^ 2) 4 := Nat.Coprime.pow_left 2 hcop
    have : p ^ 2 ∣ m.natAbs := hcop2.dvd_of_dvd_mul_left hdvd
    rw [sq] at this
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq' p this))

/-- **Square-class decomposition** (existence): every $n \ge 1$ with $(-1)^k n \equiv 0, 1 \bmod 4$ is $|D|\,m^2$ with $D$
a fundamental discriminant, $(-1)^k D > 0$ and $m \ge 1$. -/
theorem exists_fundamentalDiscriminant_mul_sq (k : ℕ) {n : ℕ} (hn : 0 < n)
    (hplus : ((-1) ^ k * (n : ℤ)) % 4 = 0 ∨ ((-1) ^ k * (n : ℤ)) % 4 = 1) :
    ∃ D : ℤ, ∃ m : ℕ, IsFundamentalDiscriminant D ∧ 0 < (-1) ^ k * D ∧ 0 < m ∧ n = D.natAbs * m ^ 2 := by
  obtain ⟨s, f, hs0, hf0, hfs, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℤ, ε = (-1) ^ k := ⟨_, rfl⟩
  rw [← hεdef] at hplus ⊢
  have hε : ε * ε = 1 := by rw [hεdef, ← mul_pow]; simp
  have hεabs : ε.natAbs = 1 := by simp [hεdef, Int.natAbs_pow]
  have hn' : (n : ℤ) = f ^ 2 * s := by rw [← hfs]; push_cast; ring
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = ε * s := ⟨_, rfl⟩
  have hdabs : d.natAbs = s := by rw [hd, Int.natAbs_mul, hεabs]; simp
  have hdsq : Squarefree d := Int.squarefree_natAbs.mp (by rw [hdabs]; exact hsq)
  have hεd : ε * d = s := by rw [hd, ← mul_assoc, hε]; simp
  have hN : ε * n = f ^ 2 * d := by rw [hn', hd]; ring
  rw [hN] at hplus
  have hspos : (0 : ℤ) < s := by exact_mod_cast hs0
  by_cases h1 : d % 4 = 1
  · refine ⟨d, f, Or.inl ⟨h1, hdsq⟩, ?_, hf0, ?_⟩
    · rw [hεd]; exact hspos
    · rw [hdabs, ← hfs]; ring
  · have h0 : d % 4 ≠ 0 := by
      intro h
      have h22 : (2 : ℤ) * 2 ∣ d := by omega
      have := hdsq 2 h22
      exact absurd (Int.isUnit_iff.mp this) (by norm_num)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rcases Nat.even_or_odd' f with ⟨f', hf' | hf'⟩
    · refine ⟨4 * d, f', Or.inr ⟨d, rfl, hd4, hdsq⟩, ?_, by omega, ?_⟩
      · have : ε * (4 * d) = 4 * (ε * d) := by ring
        rw [this, hεd]; positivity
      · have h4 : (4 * d).natAbs = 4 * s := by rw [Int.natAbs_mul, hdabs]; rfl
        rw [h4, ← hfs, hf']; ring
    · exfalso
      have hq : (f : ℤ) ^ 2 * d = 4 * (((f' : ℤ) ^ 2 + f') * d) + d := by
        rw [hf']; push_cast; ring
      rw [hq] at hplus
      omega

private lemma natAbs_four_mul' (e : ℤ) : (4 * e).natAbs = 4 * e.natAbs := by
  rw [Int.natAbs_mul]; rfl

private lemma eq_of_natAbs_eq_of_pos_mul {a b : ℤ} (h : a.natAbs = b.natAbs) (hs : 0 < a * b) : a = b := by
  rcases Int.natAbs_eq_natAbs_iff.mp h with h | h
  · exact h
  · subst h; nlinarith [sq_nonneg b]

private lemma fd_cross' {D e : ℤ} {m m' : ℕ} (hm : m ≠ 0) (hD1 : D % 4 = 1) (hDsq : Squarefree D)
    (he : e % 4 = 2 ∨ e % 4 = 3) (hesq : Squarefree e) (hsign : 0 < D * (4 * e))
    (h : D.natAbs * m ^ 2 = (4 * e).natAbs * m' ^ 2) : False := by
  rw [natAbs_four_mul'] at h
  have h2 : D.natAbs * m ^ 2 = e.natAbs * (2 * m') ^ 2 := by rw [h]; ring
  have := sqfree_eq_of_mul_sq (Int.squarefree_natAbs.mpr hDsq) (Int.squarefree_natAbs.mpr hesq) hm h2
  have hs : 0 < D * e := by nlinarith
  have := eq_of_natAbs_eq_of_pos_mul this hs
  omega

private lemma fundamentalDiscriminant_mul_sq_unique_aux {D D' : ℤ} {m m' : ℕ}
    (hD : IsFundamentalDiscriminant D) (hD' : IsFundamentalDiscriminant D') (hsign : 0 < D * D')
    (hm : 0 < m) (h : D.natAbs * m ^ 2 = D'.natAbs * m' ^ 2) : D = D' ∧ m = m' := by
  have hm0 : m ≠ 0 := hm.ne'
  have fin : D = D' → m = m' := by
    intro hDD
    subst hDD
    have hpos : 0 < D.natAbs :=
      Int.natAbs_pos.mpr (by rintro rfl; simp at hsign)
    have := Nat.eq_of_mul_eq_mul_left hpos h
    exact (Nat.pow_left_injective two_ne_zero) this
  have hm0' : m' ≠ 0 := by
    intro h0
    have hD0 : D ≠ 0 := by rintro rfl; simp at hsign
    rw [h0] at h
    simp at h
    rcases h with h | h
    · exact hD0 h
    · exact hm0 h
  rcases hD with ⟨h1, hsq⟩ | ⟨e, rfl, he, hesq⟩ <;> rcases hD' with ⟨h1', hsq'⟩ | ⟨e', rfl, he', hesq'⟩
  · have := sqfree_eq_of_mul_sq (Int.squarefree_natAbs.mpr hsq) (Int.squarefree_natAbs.mpr hsq') hm0 h
    have hDD := eq_of_natAbs_eq_of_pos_mul this hsign
    exact ⟨hDD, fin hDD⟩
  · exact (fd_cross' hm0 h1 hsq he' hesq' hsign h).elim
  · exact (fd_cross' (m := m') (m' := m) hm0' h1' hsq' he hesq
      (by linarith [hsign]) h.symm).elim
  · rw [natAbs_four_mul', natAbs_four_mul'] at h
    have h' : e.natAbs * m ^ 2 = e'.natAbs * m' ^ 2 := by linarith [h]
    have := sqfree_eq_of_mul_sq (Int.squarefree_natAbs.mpr hesq) (Int.squarefree_natAbs.mpr hesq') hm0 h'
    have hs : 0 < e * e' := by nlinarith
    have hee := eq_of_natAbs_eq_of_pos_mul this hs
    subst hee
    exact ⟨rfl, fin rfl⟩

/-- **Square-class decomposition** (uniqueness): if $|D|\,m^2 = |D'|\,m'^2$ for fundamental discriminants $D, D'$ of the
same sign and $m \ge 1$, then $D = D'$ and $m = m'$. (The hypothesis $m \ge 1$ is needed: $m = m' = 0$, $D = 1$,
$D' = 5$.) -/
theorem fundamentalDiscriminant_mul_sq_unique {D D' : ℤ} {m m' : ℕ} (hD : IsFundamentalDiscriminant D)
    (hD' : IsFundamentalDiscriminant D') (hsign : 0 < D * D') (hm : 0 < m)
    (h : D.natAbs * m ^ 2 = D'.natAbs * m' ^ 2) : D = D' ∧ m = m' :=
  fundamentalDiscriminant_mul_sq_unique_aux hD hD' hsign hm h

/-- **Möbius inversion against a completely multiplicative weight:** if $f(1) = 1$ and $f(xy) = f(x)f(y)$, then for
$m \ge 1$, $a(m) = \sum_{d \mid m}\mu(d)f(d)A(m/d)$ where $A(n) = \sum_{e \mid n} f(e)\,a(n/e)$. -/
theorem sum_moebius_mul_inversion (f a : ℕ → ℂ) (hf1 : f 1 = 1) (hf : ∀ x y, f (x * y) = f x * f y) {m : ℕ}
    (hm : 0 < m) :
    a m = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * f d *
      ∑ e ∈ (m / d).divisors, f e * a (m / d / e) := by
  let F : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else f n, by simp⟩
  let A : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else a n, by simp⟩
  let M : ArithmeticFunction ℂ := (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ).pmul F
  have hM : ∀ n, M n = (ArithmeticFunction.moebius n : ℂ) * F n := fun n => by
    simp [M, ArithmeticFunction.pmul_apply]
  have hF : ∀ n, F n = if n = 0 then 0 else f n := fun _ => rfl
  have hA : ∀ n, A n = if n = 0 then 0 else a n := fun _ => rfl
  have hF' : ∀ n, n ≠ 0 → F n = f n := fun n h => by simp [hF, h]
  have hA' : ∀ n, n ≠ 0 → A n = a n := fun n h => by simp [hA, h]
  have hMF : M * F = 1 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h1 : (M * F) n = f n * ((↑ArithmeticFunction.moebius * ArithmeticFunction.zeta :
        ArithmeticFunction ℂ) n) := by
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨hxy, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have hx0 : x.1 ≠ 0 := left_ne_zero_of_mul (hxy ▸ hn.ne')
      have hy0 : x.2 ≠ 0 := right_ne_zero_of_mul (hxy ▸ hn.ne')
      have : f n = f x.1 * f x.2 := by rw [← hf, hxy]
      rw [hM]
      simp [hF, hx0, hy0, this, ArithmeticFunction.zeta_apply]
      ring
    rw [h1, ArithmeticFunction.coe_moebius_mul_coe_zeta]
    by_cases h : n = 1
    · subst h; simp [hf1]
    · simp [h]
  have key : ((M * F) * A) m = A m := by rw [hMF]; simp
  rw [mul_assoc, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => M x * (F * A) y)] at key
  have hm0 : m ≠ 0 := hm.ne'
  rw [hA' m hm0] at key
  rw [← key]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hdv := Nat.dvd_of_mem_divisors hd
  have hq : m / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm hdv) (Nat.pos_of_ne_zero hd0)).ne'
  rw [hM, hF' d hd0, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => (F x * A y : ℂ))]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have he0 : e ≠ 0 := (Nat.pos_of_mem_divisors he).ne'
  have hdv2 := Nat.dvd_of_mem_divisors he
  have : (m / d / e) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdv2) (Nat.pos_of_ne_zero he0)).ne'
  rw [hF' e he0, hA' _ this]

end ModularFormsKB.HalfIntegral
