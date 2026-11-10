/-
# The $t$-th Shimura lift on coefficients

For $f = \sum a(n)q^n \in S_{k+1/2}(4N,\chi)$ and squarefree $t \ge 1$, Shimura's $t$-th lift has
coefficients (Shimura 1973 `shimura1973`, Main Theorem [unverified])
$$ A_t(n) = \sum_{d \mid n} \chi_t(d)\, d^{k-1} a(tn^2/d^2), \qquad \chi_t(d) = \chi(d)\Big(\frac{(-1)^k t}{d}\Big), $$
equivalently $\sum_n A_t(n)n^{-s} = L(s-k+1,\chi_t)\sum_m a(tm^2)m^{-s}$.

**Proved here (formal, for every coefficient sequence).**
- `shimuraCoeff_eq_convolution`: $A_t = (\chi_t\cdot n^{k-1}) \star (m \mapsto a(tm^2))$ (Dirichlet convolution), on $n \ge 1$.
- `LSeries_shimuraCoeff`: the Dirichlet series identity, wherever both factors converge absolutely.
- `shimuraCoeff_heckeT`: the lift intertwines $T(p^2)$ (weight $k+\tfrac12$, character $\chi$) with $T(p)$ (weight $2k$,
  character $\chi^2$), for every prime $p$ with $p^2 \nmid t$. This is the formal core of the Hecke-equivariance in
  Shimura's theorem.

**Statement change (2026-10-27).** The draft `shimuraCoeff_heckeT` (commit 00cca8c) had no hypothesis on $t$. It is false
when $p^2 \mid t$: for $t = 9$, $p = 3$, $\chi$ trivial mod 4 and $n = 1$ the two sides differ by $3^{2k-1}a(1)$, because
$T(9)a$ at $t = 9$ picks up $a(1)$, which is not a coefficient $a(tm^2)$. The numerical check behind the draft only used
$t \le 7$. Shimura's $t$ is squarefree, so the hypothesis $p^2 \nmid t$ (implied by `Squarefree t`) loses nothing.
-/
import ModularFormsKB.HalfIntegral.Hecke
import Mathlib.NumberTheory.LSeries.Convolution

namespace ModularFormsKB.HalfIntegral

open Complex

/-- **The character $\chi_t(d) = \chi(d)\left(\frac{(-1)^k t}{d}\right)$** of the $t$-th Shimura lift (as a function on $\mathbb N$). -/
noncomputable def shimuraChar (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t d : ℕ) : ℂ :=
  χ d * (jacobiSym ((-1) ^ k * t) d : ℂ)

/-- **The $t$-th Shimura lift on coefficients:** $A_t(n) = \sum_{d \mid n}\chi_t(d)\,d^{k-1}a(tn^2/d^2)$ (for $n \ge 1$;
$A_t(0)$ is not given by this formula and is left to the analytic statement). -/
noncomputable def shimuraCoeff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) * a (t * (n / d) ^ 2)

/-- **$A_t$ is a Dirichlet convolution:** $A_t = (\chi_t\cdot n^{k-1}) \star (m \mapsto a(tm^2))$. -/
theorem shimuraCoeff_eq_convolution (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) :
    shimuraCoeff k N χ t a =
      LSeries.convolution (fun d ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1)) (fun m ↦ a (t * m ^ 2)) := by
  funext n
  rw [LSeries.convolution_def]
  exact (Nat.sum_divisorsAntidiagonal
    (fun d e ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) * a (t * e ^ 2))).symm

/-- **The twist by $n^{k-1}$ shifts the variable:** $\sum_n \chi_t(n) n^{k-1} n^{-s} = L(s-k+1, \chi_t)$, termwise. -/
theorem LSeries_shimuraChar_twist (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (s : ℂ) :
    LSeries (fun d ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1)) s =
      LSeries (shimuraChar k N χ t) (s - (k - 1)) := by
  unfold LSeries
  refine tsum_congr fun n ↦ ?_
  simp only [LSeries.term]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false]
    have hx : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have h1 : ((k : ℂ) - 1) = (((k : ℤ) - 1 : ℤ) : ℂ) := by push_cast; ring
    rw [h1, Complex.cpow_sub _ _ hx, Complex.cpow_intCast]
    have h2 : (n : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hx)
    have h3 : (n : ℂ) ^ ((k : ℤ) - 1) ≠ 0 := zpow_ne_zero _ hx
    field_simp

/-- **The Dirichlet series of the $t$-th Shimura lift** (Shimura 1973 `shimura1973`, Main Theorem [unverified]):
$\sum_n A_t(n)n^{-s} = L(s-k+1,\chi_t)\sum_m a(tm^2)m^{-s}$, wherever both series on the right converge absolutely. -/
@[kb "shimura1973" "Main Theorem: the Dirichlet series of the t-th lift [unverified]"]
theorem LSeries_shimuraCoeff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) {s : ℂ}
    (h₁ : LSeriesSummable (fun d ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1)) s)
    (h₂ : LSeriesSummable (fun m ↦ a (t * m ^ 2)) s) :
    LSeries (shimuraCoeff k N χ t a) s =
      LSeries (shimuraChar k N χ t) (s - (k - 1)) * LSeries (fun m ↦ a (t * m ^ 2)) s := by
  rw [shimuraCoeff_eq_convolution, LSeries_convolution' h₁ h₂, LSeries_shimuraChar_twist]

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

/-- $(f \star g)(pn) = (f \star U_p g)(n) + f(p)\,(f \star I_p g)(n)$ for $f$ multiplicative at $p$. -/
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

/-- $(f \star V_p g)(n) = [p \mid n]\,(f \star g)(n/p)$. -/
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

private theorem shimuraCoeff_eq_dsum (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    shimuraCoeff k N χ t a n =
      dsum (fun d ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1)) (fun m ↦ a (t * m ^ 2)) n :=
  (Nat.sum_divisorsAntidiagonal
    (fun d e ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) * a (t * e ^ 2))).symm

private theorem jacobiSym_sq_prime (m : ℕ) {p : ℕ} (hp : p.Prime) :
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

/-- $T(p^2)a$ at $tm^2$, for $p^2 \nmid t$. -/
private theorem heckeT_tsq (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    {t : ℕ} (ht : ¬ p ^ 2 ∣ t) (a : ℕ → ℂ) (m : ℕ) :
    heckeT k N χ p a (t * m ^ 2) = a (t * (p * m) ^ 2) +
      shimuraChar k N χ t p * (p : ℂ) ^ ((k : ℤ) - 1) * (if p ∣ m then 0 else a (t * m ^ 2)) +
      χ p ^ 2 * (p : ℂ) ^ (2 * (k : ℤ) - 1) * (if p ∣ m then a (t * (m / p) ^ 2) else 0) := by
  have hdvd : p ^ 2 ∣ t * m ^ 2 ↔ p ∣ m := by
    constructor
    · intro h
      by_contra hm
      have hc : Nat.Coprime (p ^ 2) (m ^ 2) := Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
      exact ht (hc.dvd_of_dvd_mul_right h)
    · intro h
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd h 2) _
  have hJ : (jacobiSym ((-1) ^ k * ((t * m ^ 2 : ℕ) : ℤ)) p : ℂ) =
      (jacobiSym ((-1) ^ k * (t : ℤ)) p : ℂ) * (if p ∣ m then 0 else 1) := by
    rw [show (-1) ^ k * ((t * m ^ 2 : ℕ) : ℤ) = ((-1) ^ k * (t : ℤ)) * (m : ℤ) ^ 2 by push_cast; ring,
      jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym_sq_prime m hp]
    split_ifs <;> simp
  rw [heckeT, hJ, if_congr hdvd rfl rfl, shimuraChar]
  have h1 : p ^ 2 * (t * m ^ 2) = t * (p * m) ^ 2 := by ring
  rw [h1]
  split_ifs with hm
  · obtain ⟨c, rfl⟩ := hm
    rw [show t * (p * c) ^ 2 / p ^ 2 = t * c ^ 2 by
        rw [show t * (p * c) ^ 2 = p ^ 2 * (t * c ^ 2) by ring, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)],
      Nat.mul_div_cancel_left _ hp.pos]
    ring
  · ring

/-- **The Shimura lift intertwines $T(p^2)$ and $T(p)$** (Shimura 1973 `shimura1973`, proof of the Main Theorem
[unverified]): for every prime $p$ with $p^2 \nmid t$, every coefficient sequence $a$ and every $n \ge 1$,
$A_t(T(p^2)a)(n) = (T(p)A_t(a))(n)$, where $T(p)$ has weight $2k$ and character $\chi^2$ (mod $4N$). Purely formal. -/
@[kb "shimura1973" "Main Theorem, Hecke equivariance T(p²) ↦ T(p), on coefficients [unverified]"]
theorem shimuraCoeff_heckeT (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    {t : ℕ} (ht : ¬ p ^ 2 ∣ t) (a : ℕ → ℂ) {n : ℕ} (_hn : 1 ≤ n) :
    shimuraCoeff k N χ t (heckeT k N χ p a) n =
      heckeTInt (2 * k) (4 * N) (χ ^ 2) p (shimuraCoeff k N χ t a) n := by
  set F : ℕ → ℂ := fun d ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) with hF
  set B : ℕ → ℂ := fun m ↦ a (t * m ^ 2) with hB
  have hFmul : ∀ d, d ≠ 0 → F (p * d) = F p * F d := by
    intro d hd
    simp only [hF, shimuraChar]
    push_cast
    rw [map_mul, jacobiSym.mul_right' _ hp.ne_zero hd, mul_zpow]
    push_cast
    ring
  have hpow : (χ ^ 2) p = χ p ^ 2 := MulChar.pow_apply' χ two_ne_zero p
  simp only [heckeTInt, shimuraCoeff_eq_dsum, ← hF, ← hB, hpow]
  rw [dsum_mul_prime F B hp hFmul, ← mul_ite_zero, ← dsum_V F B hp.pos]
  unfold dsum
  simp only [hB, heckeT_tsq k N χ hp ht a, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  push_cast
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [hF]; ring
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    ring

/-- **Hecke equivariance for squarefree $t$**, Shimura's setting: $A_t \circ T(p^2) = T(p) \circ A_t$ on $n \ge 1$, all primes $p$. -/
theorem shimuraCoeff_heckeT_of_squarefree (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {p : ℕ} (hp : p.Prime)
    {t : ℕ} (ht : Squarefree t) (a : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    shimuraCoeff k N χ t (heckeT k N χ p a) n =
      heckeTInt (2 * k) (4 * N) (χ ^ 2) p (shimuraCoeff k N χ t a) n :=
  shimuraCoeff_heckeT k N χ hp (fun h ↦ hp.one_lt.ne' (Nat.isUnit_iff.mp (ht p (by simpa [sq] using h)))) a hn

end ModularFormsKB.HalfIntegral
