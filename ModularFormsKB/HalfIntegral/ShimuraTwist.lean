/-
# The twisted Dirichlet series of the Shimura lift

Shimura's proof of his Main Theorem (Shimura 1973 `shimura1973` [unverified]) feeds Weil's
converse theorem with the functional equations of the twists $\sum_n \psi(n)A_t(n)n^{-s}$ of the Dirichlet series of the
lift by Dirichlet characters $\psi$. This file proves the coefficient-level input of that argument: the twisted form of the
Rankin-type identity `LSeries_shimuraCoeff`,
$$ \sum_n \psi(n)A_t(n)n^{-s} = L(s-k+1,\psi\chi_t)\sum_m \psi(m)a(tm^2)m^{-s}, $$
wherever both factors converge absolutely, together with the bounds that make both factors converge for
$\operatorname{Re}s > k+\tfrac32$ when $a(n) = O(n^{(2k+1)/4})$ (Hecke's bound for weight $k+\tfrac12$).

**Proved here (formal, for every coefficient sequence).**
- `twist_convolution`: twisting by a Dirichlet character commutes with Dirichlet convolution.
- `LSeries_twist_shimuraCoeff`: the twisted identity above.
- `LSeriesSummable_shimuraChar_twist`, `LSeriesSummable_twist_tsq`, `LSeriesSummable_twist_shimuraCoeff`: absolute
  convergence of both factors and of the product for $\operatorname{Re}s > k+\tfrac32$, from $a(n) = O(n^{(2k+1)/4})$.
- `norm_shimuraCoeff_le`: the crude polynomial bound $|A_t(n)| \le C\,t^k n^{3k+1}$ from $|a(m)| \le C m^k$.

The trivial twist ($\psi$ the character mod 1) recovers `LSeries_shimuraCoeff`.
-/
import ModularFormsKB.HalfIntegral.ShimuraLift
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace ModularFormsKB.HalfIntegral

open Complex

/-- **Twist of a coefficient sequence by a Dirichlet character:** $n \mapsto \psi(n)a(n)$. -/
noncomputable def twist {m : ℕ} (ψ : DirichletCharacter ℂ m) (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ ψ n * a n

/-- **Twisting commutes with Dirichlet convolution**, since $\psi$ is completely multiplicative:
$\psi\cdot(f\star g) = (\psi f)\star(\psi g)$. -/
theorem twist_convolution {m : ℕ} (ψ : DirichletCharacter ℂ m) (f g : ℕ → ℂ) :
    twist ψ (LSeries.convolution f g) = LSeries.convolution (twist ψ f) (twist ψ g) := by
  funext n
  simp only [twist, LSeries.convolution_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  rw [← hx.1]
  push_cast
  rw [map_mul]
  ring

/-- **The twist by $n^{k-1}$ shifts the variable**, for any sequence $g$: $\sum_n g(n)n^{k-1}n^{-s} = \sum_n g(n)n^{-(s-k+1)}$. -/
theorem LSeries_mul_zpow (k : ℕ) (g : ℕ → ℂ) (s : ℂ) :
    LSeries (fun d ↦ g d * (d : ℂ) ^ ((k : ℤ) - 1)) s = LSeries g (s - (k - 1)) := by
  unfold LSeries
  refine tsum_congr fun n => ?_
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

/-- **The twisted Dirichlet series of the $t$-th Shimura lift** (Shimura 1973 `shimura1973`, proof of the Main Theorem
[unverified]): for a Dirichlet character $\psi$,
$\sum_n\psi(n)A_t(n)n^{-s} = L(s-k+1,\psi\chi_t)\sum_m\psi(m)a(tm^2)m^{-s}$, wherever both series on the right (in the
forms $\sum\psi(d)\chi_t(d)d^{k-1}d^{-s}$ and $\sum\psi(m)a(tm^2)m^{-s}$) converge absolutely. -/
@[kb "shimura1973" "proof of the Main Theorem: the twisted Dirichlet series of the t-th lift [unverified]"]
theorem LSeries_twist_shimuraCoeff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) (a : ℕ → ℂ) {m : ℕ}
    (ψ : DirichletCharacter ℂ m) {s : ℂ}
    (h₁ : LSeriesSummable (twist ψ fun d ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1)) s)
    (h₂ : LSeriesSummable (twist ψ fun m ↦ a (t * m ^ 2)) s) :
    LSeries (twist ψ (shimuraCoeff k N χ t a)) s =
      LSeries (twist ψ (shimuraChar k N χ t)) (s - (k - 1)) * LSeries (twist ψ fun m ↦ a (t * m ^ 2)) s := by
  rw [shimuraCoeff_eq_convolution, twist_convolution, LSeries_convolution' h₁ h₂, ← LSeries_mul_zpow]
  congr 2
  funext d
  simp only [twist]
  ring

/-- $|\psi(n)| \le 1$. -/
theorem norm_dirichletCharacter_le {m : ℕ} (ψ : DirichletCharacter ℂ m) (n : ℕ) : ‖ψ n‖ ≤ 1 :=
  DirichletCharacter.norm_le_one ψ _

/-- $|\chi_t(d)| \le 1$. -/
theorem norm_shimuraChar_le (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t d : ℕ) :
    ‖shimuraChar k N χ t d‖ ≤ 1 := by
  unfold shimuraChar
  rw [norm_mul]
  have h1 : ‖χ d‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have h2 : ‖(jacobiSym ((-1) ^ k * t) d : ℂ)‖ ≤ 1 := by
    rcases jacobiSym.trichotomy ((-1) ^ k * (t : ℤ)) d with h | h | h <;> simp [h]
  calc ‖χ d‖ * ‖(jacobiSym ((-1) ^ k * t) d : ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **The first factor converges for $\operatorname{Re}s > k$:** $|\psi(d)\chi_t(d)d^{k-1}| \le d^{k-1}$. -/
theorem LSeriesSummable_shimuraChar_twist (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (t : ℕ) {m : ℕ}
    (ψ : DirichletCharacter ℂ m) {s : ℂ} (hs : (k : ℝ) < s.re) :
    LSeriesSummable (twist ψ fun d ↦ shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1)) s := by
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨1, fun n hn ↦ ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [twist, norm_mul, norm_zpow, Complex.norm_natCast, one_mul]
  rw [show ((k : ℝ) - 1) = (((k : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
  calc ‖ψ n‖ * (‖shimuraChar k N χ t n‖ * (n : ℝ) ^ ((k : ℤ) - 1))
      ≤ 1 * (1 * (n : ℝ) ^ ((k : ℤ) - 1)) := by
        gcongr
        · exact norm_dirichletCharacter_le ψ n
        · exact norm_shimuraChar_le k N χ t n
    _ = (n : ℝ) ^ ((k : ℤ) - 1) := by ring

/-- **The second factor converges for $\operatorname{Re}s > k+\tfrac32$** when $|a(n)| \le C n^{(2k+1)/4}$ for $n \ge 1$
(Hecke's bound in weight $k+\tfrac12$): then $|\psi(m)a(tm^2)| \le C t^{(2k+1)/4} m^{k+1/2}$. -/
theorem LSeriesSummable_twist_tsq (k : ℕ) {t : ℕ} (ht : 1 ≤ t) {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4)) {m : ℕ}
    (ψ : DirichletCharacter ℂ m) {s : ℂ} (hs : (k : ℝ) + 3 / 2 < s.re) :
    LSeriesSummable (twist ψ fun m ↦ a (t * m ^ 2)) s := by
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨C * (t : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4), fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
  have htn : 1 ≤ t * n ^ 2 := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (pow_ne_zero _ hn))
  have hb := ha _ htn
  have hC : 0 ≤ C := by
    have h0 : 0 ≤ C * ((t * n ^ 2 : ℕ) : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4) := le_trans (norm_nonneg _) hb
    have hp : 0 < ((t * n ^ 2 : ℕ) : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4) :=
      Real.rpow_pos_of_pos (by exact_mod_cast htn) _
    exact nonneg_of_mul_nonneg_left h0 hp
  have heq : ((t * n ^ 2 : ℕ) : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4) =
      (t : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4) * (n : ℝ) ^ ((k : ℝ) + 3 / 2 - 1) := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (n : ℝ) 2,
      ← Real.rpow_mul (by positivity)]
    congr 2
    ring
  simp only [twist, norm_mul]
  calc ‖ψ n‖ * ‖a (t * n ^ 2)‖ ≤ 1 * (C * ((t * n ^ 2 : ℕ) : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4)) :=
        mul_le_mul (norm_dirichletCharacter_le ψ n) hb (norm_nonneg _) zero_le_one
    _ = C * (t : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4) * (n : ℝ) ^ ((k : ℝ) + 3 / 2 - 1) := by
        rw [heq]; ring

/-- **The twisted Dirichlet series of the lift converges for $\operatorname{Re}s > k+\tfrac32$**, from Hecke's bound. -/
theorem LSeriesSummable_twist_shimuraCoeff (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {t : ℕ} (ht : 1 ≤ t)
    {a : ℕ → ℂ} {C : ℝ} (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4)) {m : ℕ}
    (ψ : DirichletCharacter ℂ m) {s : ℂ} (hs : (k : ℝ) + 3 / 2 < s.re) :
    LSeriesSummable (twist ψ (shimuraCoeff k N χ t a)) s := by
  rw [shimuraCoeff_eq_convolution, twist_convolution]
  exact (LSeriesSummable_shimuraChar_twist k N χ t ψ (by linarith)).convolution
    (LSeriesSummable_twist_tsq k ht ha ψ hs)

/-- **The twisted identity for $\operatorname{Re}s > k+\tfrac32$**, from Hecke's bound $|a(n)| \le Cn^{(2k+1)/4}$. -/
theorem LSeries_twist_shimuraCoeff_of_bound (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {t : ℕ} (ht : 1 ≤ t)
    {a : ℕ → ℂ} {C : ℝ} (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 4)) {m : ℕ}
    (ψ : DirichletCharacter ℂ m) {s : ℂ} (hs : (k : ℝ) + 3 / 2 < s.re) :
    LSeries (twist ψ (shimuraCoeff k N χ t a)) s =
      LSeries (twist ψ (shimuraChar k N χ t)) (s - (k - 1)) * LSeries (twist ψ fun m ↦ a (t * m ^ 2)) s :=
  LSeries_twist_shimuraCoeff k N χ t a ψ (LSeriesSummable_shimuraChar_twist k N χ t ψ (by linarith))
    (LSeriesSummable_twist_tsq k ht ha ψ hs)

/-- **A crude polynomial bound for the lift:** if $|a(m)| \le C m^k$ for $m \ge 1$, then $|A_t(n)| \le C t^k n^{3k+1}$ for
$n \ge 1$ and $t \ge 1$. -/
theorem norm_shimuraCoeff_le (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) {t : ℕ} (ht : 1 ≤ t) {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ n, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ k) {n : ℕ} (hn : 1 ≤ n) :
    ‖shimuraCoeff k N χ t a n‖ ≤ C * (t : ℝ) ^ k * (n : ℝ) ^ (3 * k + 1) := by
  have hC : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (ha 1 le_rfl)
    simpa using this
  unfold shimuraCoeff
  have hterm : ∀ d ∈ n.divisors, ‖shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) * a (t * (n / d) ^ 2)‖ ≤
      C * (t : ℝ) ^ k * (n : ℝ) ^ (3 * k) := by
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    have hdle : d ≤ n := Nat.divisor_le hd
    have hq1 : 1 ≤ n / d := Nat.div_pos hdle hd1
    have hqle : n / d ≤ n := Nat.div_le_self n d
    have htq : 1 ≤ t * (n / d) ^ 2 := Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by omega) (by positivity))
    rw [norm_mul, norm_mul, norm_zpow, Complex.norm_natCast]
    have h1 := norm_shimuraChar_le k N χ t d
    have h2 : (d : ℝ) ^ ((k : ℤ) - 1) ≤ (n : ℝ) ^ k := by
      have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      calc (d : ℝ) ^ ((k : ℤ) - 1) ≤ (d : ℝ) ^ (k : ℤ) := zpow_le_zpow_right₀ hd' (by omega)
        _ = (d : ℝ) ^ k := zpow_natCast _ _
        _ ≤ (n : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hdle) k
    have h3 : ‖a (t * (n / d) ^ 2)‖ ≤ C * (t : ℝ) ^ k * (n : ℝ) ^ (2 * k) := by
      refine le_trans (ha _ htq) ?_
      rw [mul_assoc]
      gcongr
      push_cast
      rw [mul_pow, ← pow_mul, mul_comm 2 k]
      gcongr
    calc ‖shimuraChar k N χ t d‖ * (d : ℝ) ^ ((k : ℤ) - 1) * ‖a (t * (n / d) ^ 2)‖
        ≤ 1 * (n : ℝ) ^ k * (C * (t : ℝ) ^ k * (n : ℝ) ^ (2 * k)) := by
          gcongr
      _ = C * (t : ℝ) ^ k * (n : ℝ) ^ (3 * k) := by ring
  calc ‖∑ d ∈ n.divisors, shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) * a (t * (n / d) ^ 2)‖
      ≤ ∑ d ∈ n.divisors, ‖shimuraChar k N χ t d * (d : ℂ) ^ ((k : ℤ) - 1) * a (t * (n / d) ^ 2)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, C * (t : ℝ) ^ k * (n : ℝ) ^ (3 * k) := Finset.sum_le_sum hterm
    _ = (n.divisors.card : ℝ) * (C * (t : ℝ) ^ k * (n : ℝ) ^ (3 * k)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (C * (t : ℝ) ^ k * (n : ℝ) ^ (3 * k)) := by
        gcongr
        exact_mod_cast Nat.card_divisors_le_self n
    _ = C * (t : ℝ) ^ k * (n : ℝ) ^ (3 * k + 1) := by ring

end ModularFormsKB.HalfIntegral
