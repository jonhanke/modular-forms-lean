/-
# The coefficients $c(tm^2)$ of a Hecke eigenform of level $4N$

`Corresponds.coeff_mul_sq_odd` (`Abstract/WaldspurgerGround.lean`) gives, in Kohnen's plus space of level 4,
$c(|D|m^2) = c(|D|)\sum_{d\mid m}\mu(d)\left(\frac Dd\right)d^{k-1}b(m/d)$ for odd $m$. Here the same is proved at level
$4N$ for the relation `Waldspurger.LiftsTo` (a $T(p^2)$-eigenform $g = \sum c(n)q^n \in S_{k+1/2}(4N,\chi)$ whose Shimura
lift is the normalized eigenform $F = \sum b(n)q^n$ of weight $2k$ on $\Gamma_0(4N)$), with $\chi^2 = 1$, any $t$
with $p^2 \nmid t$ for $p \nmid 4N$ (for example $t$ squarefree), and $m$ prime to $4N$ (Shimura 1973 `shimura1973`,
§1 [unverified]):
- `shimuraCoeff_eq_of_eigen_coprime`: the Shimura-lift relation $A_t(m) = c(t)\,b(m)$, from the Hecke relations
  `shimuraCoeff_heckeT` at every prime $p \nmid 4N$ (induction on $m$);
- `LiftsTo.shimuraCoeff_coprime`, `LiftsTo.coeff_mul_prime_sq`: in particular
  $c(tp^2) = \big(b(p) - \chi_t(p)p^{k-1}\big)c(t)$, $\chi_t$ = `shimuraChar k N χ t`;
- `LiftsTo.coeff_mul_sq_coprime`: by Möbius inversion (`sum_moebius_mul_inversion`)
  $c(tm^2) = c(t)\sum_{d\mid m}\mu(d)\chi_t(d)d^{k-1}b(m/d)$.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.Coefficients
import ModularFormsKB.HalfIntegral.Abstract.WaldspurgerGround

namespace ModularFormsKB.HalfIntegral.Waldspurger

open Complex MatrixGroups CongruenceSubgroup
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- Hecke recursion for the lift at a prime $p \nmid 4N$ (with $\chi^2 = 1$). -/
private theorem shimuraCoeff_rec' {k N t p : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hχ : χ ^ 2 = 1)
    (hp : p.Prime) (hpN : ¬ p ∣ 4 * N) (ht : ¬ p ^ 2 ∣ t) {c : ℕ → ℂ} {lam : ℂ} (hc : heckeT k N χ p c = lam • c) {n : ℕ}
    (hn : 1 ≤ n) :
    shimuraCoeff k N χ t c (p * n) = lam * shimuraCoeff k N χ t c n -
      if p ∣ n then (p : ℂ) ^ (2 * (k : ℤ) - 1) * shimuraCoeff k N χ t c (n / p) else 0 := by
  have h := shimuraCoeff_heckeT k N χ hp ht c hn
  rw [hc, shimuraCoeff_smul, hχ] at h
  have h1 : (1 : DirichletCharacter ℂ (4 * N)) p = 1 := by
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime p (4 * N)).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN))
  rw [h, heckeTInt, h1]
  split_ifs <;> push_cast <;> ring

/-- Hecke recursion for $F$ at a prime, level $4N$. -/
private theorem heckeTInt_rec' {k N p : ℕ} {b : ℕ → ℂ} (hp : p.Prime)
    (hpN : ¬ p ∣ 4 * N)
    (hb : heckeTInt (2 * k) (4 * N) 1 p b = b p • b) (n : ℕ) :
    b (p * n) = b p * b n - if p ∣ n then (p : ℂ) ^ (2 * (k : ℤ) - 1) * b (n / p) else 0 := by
  have h := congrFun hb n
  have h1 : (1 : DirichletCharacter ℂ (4 * N)) p = 1 := by
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime p (4 * N)).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN))
  simp only [heckeTInt, h1, one_mul, Pi.smul_apply, smul_eq_mul] at h
  push_cast at h ⊢
  rw [← h]
  split_ifs <;> ring

/-- The weight $\chi_t(d)d^{k-1}$ of the lift is completely multiplicative. -/
private theorem shimuraWeight_mul' (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t x y : ℕ) :
    shimuraChar k N χ t (x * y) * ((x * y : ℕ) : ℂ) ^ ((k : ℤ) - 1) =
      (shimuraChar k N χ t x * (x : ℂ) ^ ((k : ℤ) - 1)) *
        (shimuraChar k N χ t y * (y : ℂ) ^ ((k : ℤ) - 1)) := by
  have h0 : shimuraChar k N χ t 0 = 0 := by
    haveI : Nontrivial (ZMod (4 * N)) := ZMod.nontrivial_iff.2 (by omega)
    simp only [shimuraChar, Nat.cast_zero]
    rw [MulChar.map_nonunit χ not_isUnit_zero, zero_mul]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [h0]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [h0]
  simp only [shimuraChar]
  push_cast
  rw [map_mul, jacobiSym.mul_right' _ hx hy, mul_zpow]
  push_cast
  ring

/-- **The Shimura-lift relation for $m$ prime to $4N$, formal version:** if $\chi^2 = 1$, $T(p^2)c = b(p)c$ and
$T(p)b = b(p)b$ (level $4N$, trivial character) for every prime $p \nmid 4N$, $b(1) = 1$, and $p^2 \nmid t$ for primes
$p \nmid 4N$, then $A_t(m) = c(t)\,b(m)$ for every $m$ prime to $4N$. -/
theorem shimuraCoeff_eq_of_eigen_coprime {k N t : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hχ : χ ^ 2 = 1)
    (ht : ∀ p, p.Prime → ¬ p ∣ 4 * N → ¬ p ^ 2 ∣ t) {c b : ℕ → ℂ} (hb1 : b 1 = 1)
    (hF : ∀ p, p.Prime → ¬ p ∣ 4 * N → heckeTInt (2 * k) (4 * N) 1 p b = b p • b)
    (hg : ∀ p, p.Prime → ¬ p ∣ 4 * N → heckeT k N χ p c = b p • c) :
    ∀ m, Nat.Coprime m (4 * N) → shimuraCoeff k N χ t c m = c t * b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  by_cases h1 : m = 1
  · subst h1; rw [shimuraCoeff_one, hb1, mul_one]
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 4 * N = 1 := by simpa using hm
    omega
  obtain ⟨p, m', hp, rfl⟩ : ∃ p m', p.Prime ∧ m = p * m' :=
    ⟨m.minFac, m / m.minFac, Nat.minFac_prime h1, (Nat.mul_div_cancel' (Nat.minFac_dvd m)).symm⟩
  have hpN : ¬ p ∣ 4 * N := fun h ↦
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (dvd_mul_right p m') hm) h)
  have hm' : Nat.Coprime m' (4 * N) := (Nat.coprime_mul_iff_left.1 hm).2
  have hm'pos : 1 ≤ m' := Nat.pos_of_ne_zero (fun h ↦ hm0 (by simp [h]))
  have hlt : m' < p * m' := lt_mul_left hm'pos hp.one_lt
  rw [shimuraCoeff_rec' hχ hp hpN (ht p hp hpN) (hg p hp hpN) hm'pos,
    heckeTInt_rec' hp hpN (hF p hp hpN) m', ih m' hlt hm']
  split_ifs with hdvd
  · obtain ⟨r, rfl⟩ := hdvd
    have hr : Nat.Coprime r (4 * N) := (Nat.coprime_mul_iff_left.1 hm').2
    rw [Nat.mul_div_cancel_left _ hp.pos,
      ih r (lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hp.pos) hlt) hr]
    ring
  · ring

/-- **The Shimura-lift relation on the square class of a squarefree $t$**, $m$ prime to $4N$. -/
theorem LiftsTo.shimuraCoeff_coprime {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : ℍ → ℂ} {b : ℕ → ℂ} (h : LiftsTo M k N χ g c F b) (hχ : χ ^ 2 = 1) {t : ℕ}
    (ht : Squarefree t) {m : ℕ} (hm : Nat.Coprime m (4 * N)) :
    shimuraCoeff k N χ t c m = c t * b m :=
  shimuraCoeff_eq_of_eigen_coprime hχ
    (fun p hp _ hd ↦ hp.one_lt.ne' (Nat.isUnit_iff.mp (ht p (by simpa [sq] using hd)))) h.normalized
    h.eigen_F h.eigen_g m hm

/-- **Hecke relation at a prime $p \nmid 4N$:** $c(tp^2) = \big(b(p) - \chi_t(p)p^{k-1}\big)\,c(t)$. -/
theorem LiftsTo.coeff_mul_prime_sq {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : ℍ → ℂ} {b : ℕ → ℂ} (h : LiftsTo M k N χ g c F b) (hχ : χ ^ 2 = 1) {t : ℕ}
    (ht : Squarefree t) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ 4 * N) :
    c (t * p ^ 2) = (b p - shimuraChar k N χ t p * (p : ℂ) ^ ((k : ℤ) - 1)) * c t := by
  have h' := h.shimuraCoeff_coprime hχ ht (m := p) ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  rw [shimuraCoeff, Nat.Prime.sum_divisors hp] at h'
  simp only [Nat.div_self hp.pos, Nat.div_one, Nat.cast_one, one_zpow, mul_one, one_pow] at h'
  have h1 : shimuraChar k N χ t 1 = 1 := by simp [shimuraChar]
  rw [h1, one_mul] at h'
  linear_combination h'


/-- **The coefficients on the square class of $t$, $m$ prime to $4N$** (Möbius-inverted form):
$c(tm^2) = c(t)\sum_{d\mid m}\mu(d)\chi_t(d)d^{k-1}b(m/d)$. -/
@[kb "shimura1973" "§1: c(tm²) = c(t) Σ_{d|m} μ(d) χ_t(d) d^{k-1} b(m/d) for a T(p²)-eigenform, m prime to 4N [unverified]"]
theorem LiftsTo.coeff_mul_sq_coprime {M : MultiplierSystem} {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : ℍ → ℂ} {b : ℕ → ℂ} (h : LiftsTo M k N χ g c F b) (hχ : χ ^ 2 = 1) {t : ℕ}
    (ht : Squarefree t) {m : ℕ} (hm : Nat.Coprime m (4 * N)) :
    c (t * m ^ 2) = c t *
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ) * shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) *
        b (m / d) := by
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · have : 4 * N = 1 := by simpa using hm
      omega
    · exact h0
  set f : ℕ → ℂ := fun d ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) with hf
  have hinv := sum_moebius_mul_inversion f (fun n ↦ c (t * n ^ 2)) (by simp [hf, shimuraChar])
    (shimuraWeight_mul' k N χ t) hm0
  rw [hinv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
  have hmd : Nat.Coprime (m / d) (4 * N) := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hdm) hm
  have hA : ∑ e ∈ (m / d).divisors, f e * c (t * (m / d / e) ^ 2) = c t * b (m / d) := by
    rw [← h.shimuraCoeff_coprime hχ ht hmd, shimuraCoeff]
  rw [hA, hf]
  ring

end ModularFormsKB.HalfIntegral.Waldspurger