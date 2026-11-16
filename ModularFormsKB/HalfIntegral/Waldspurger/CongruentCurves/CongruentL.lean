/-
# $L(E_n, s) = L(f_{32} \otimes \left(\frac n\cdot\right), s)$, hence entire (first part of H4)

**Theorem** (`LFunction_congruentCurve_eq`). For squarefree $n \ge 1$, the coefficients of Mathlib's
`(congruentCurve n).LFunction` are $\left(\frac nm\right) b(m)$, $b$ the coefficients of $f_{32}$. Both sides are
multiplicative (Tau Ceti `isMultiplicative_LFunction`; `f32Coeff_mul_of_coprime` and `jacobiSym.mul_right`), and they
agree at prime powers:
- at $p \mid 2n$ both vanish at $p^k$, $k \ge 1$ (`LFunction_congruentCurve_prime_pow_of_dvd`; $b$ vanishes at even
  numbers and $\left(\frac np\right) = 0$);
- at $p \nmid 2n$ both satisfy $c(p^{k+2}) = a_p c(p^{k+1}) - p c(p^k)$ with
  $a_p = \left(\frac np\right) b(p)$ (`LFunction_congruentCurve_prime_pow_add_two`, `frobeniusTrace_congruentCurveMod_eq`,
  `f32Coeff_hecke`).
Gauss's count at $p \equiv 1 \bmod 4$ (row 30) is `gaussCountX3SubX` (`GaussCount.lean`), so this is unconditional.

**Theorem** (`hasEntireExtension_lCoeff`, H4 first part). With `F32Modular` (row 29), the $L$-series of Mathlib's
$E_n$ has an entire extension (`hasEntireExtension_congruentCoeff`).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.LocalFactors
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.GaussCount
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Hecke
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Modular

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open WeierstrassCurve ArithmeticFunction

/-- The $L$-series coefficients of $E_n$ as complex numbers. -/
noncomputable def lCoeff (n : ℕ) (m : ℕ) : ℂ := ((congruentCurve n).LFunction m : ℂ)

/-- $m \mapsto \left(\frac nm\right) b(m)$ as an arithmetic function. -/
def congruentArith (n : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun m ↦ congruentCoeff n m, by simp [congruentCoeff, f32Coeff_zero]⟩

theorem congruentArith_apply (n m : ℕ) : congruentArith n m = congruentCoeff n m := rfl

theorem isMultiplicative_congruentArith (n : ℕ) : (congruentArith n).IsMultiplicative := by
  refine ⟨by simp [congruentArith_apply, congruentCoeff, f32Coeff_one], fun {a b} hab ↦ ?_⟩
  simp only [congruentArith_apply, congruentCoeff]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [f32Coeff_zero]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [f32Coeff_zero]
  rw [jacobiSym.mul_right' _ ha.ne' hb.ne', f32Coeff_mul_of_coprime hab]
  ring

/-- $b(p^k) $ satisfies the Hecke recursion at odd $p$. -/
theorem f32Coeff_prime_pow_add_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    f32Coeff (p ^ (k + 2)) = f32Coeff p * f32Coeff (p ^ (k + 1)) - p * f32Coeff (p ^ k) := by
  have h := f32Coeff_hecke hp hp2 (p ^ (k + 1))
  have hd : p ∣ p ^ (k + 1) := dvd_pow_self p (by omega)
  have hq : p ^ (k + 1) / p = p ^ k := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [if_pos hd, ← pow_succ', hq] at h
  rw [show k + 2 = k + 1 + 1 by ring]
  linear_combination h

/-- Two sequences with the same first two terms and the same two-step recursion agree. -/
theorem two_step_eq {u v : ℕ → ℤ} {a c : ℤ} (h0 : u 0 = v 0) (h1 : u 1 = v 1)
    (hu : ∀ k, u (k + 2) = a * u (k + 1) - c * u k) (hv : ∀ k, v (k + 2) = a * v (k + 1) - c * v k) :
    ∀ k, u k = v k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | j + 2 => rw [hu, hv, ih (j + 1) (by omega), ih j (by omega)]

/-- **The coefficients of Mathlib's $L$-function of $E_n$** (rows 31, 33), unconditional. -/
theorem LFunction_congruentCurve_eq {n : ℕ} [NeZero n] (hn : Squarefree n) (m : ℕ) :
    (congruentCurve n).LFunction m = congruentCoeff n m := by
  have key : (congruentCurve n).LFunction = congruentArith n := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_LFunction _) _
      (isMultiplicative_congruentArith n)).2 fun p k hp ↦ ?_
    rw [congruentArith_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [congruentCoeff, f32Coeff_one, LFunction_apply_one]
    by_cases hpn : p ∣ 2 * n
    · rw [LFunction_congruentCurve_prime_pow_of_dvd hn hp hpn hk]
      symm
      rcases (Nat.Prime.dvd_mul hp).1 hpn with h2 | hpn'
      · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
        subst this
        have : f32Coeff (2 ^ k) = 0 := f32Coeff_of_even (by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          exact ⟨2 ^ j, by ring⟩)
        simp [congruentCoeff, this]
      · have hJ : jacobiSym n p = 0 := by
          rw [jacobiSym.eq_zero_iff]
          refine ⟨hp.ne_zero, fun h1 ↦ ?_⟩
          have : (p : ℤ) ∣ Int.gcd n p := Int.dvd_coe_gcd (by exact_mod_cast hpn') dvd_rfl
          rw [h1] at this
          exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
        simp [congruentCoeff, jacobiSym.pow_right, hJ, zero_pow hk.ne']
    · haveI : Fact p.Prime := ⟨hp⟩
      have hp2 : p ≠ 2 := fun h ↦ hpn (h ▸ dvd_mul_right 2 n)
      have hpn' : ¬ p ∣ n := fun h ↦ hpn (dvd_mul_of_dvd_right h 2)
      have ha := frobeniusTrace_congruentCurveMod_eq gaussCountX3SubX hp2 n
      have hJ2 : jacobiSym n p ^ 2 = 1 := by
        apply jacobiSym.sq_one
        rw [Int.gcd_natCast_natCast]
        exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn')
      refine two_step_eq (u := fun k ↦ (congruentCurve n).LFunction (p ^ k))
        (v := fun k ↦ congruentCoeff n (p ^ k)) (a := congruentCoeff n p) (c := p) ?_ ?_ ?_ ?_ k
      · simp [congruentCoeff, f32Coeff_one, LFunction_apply_one]
      · simp only [pow_one]; rw [LFunction_congruentCurve_prime hpn, ha]
      · intro j; rw [LFunction_congruentCurve_prime_pow_add_two hpn j, ha]
      · intro j
        simp only [congruentCoeff, jacobiSym.pow_right, f32Coeff_prime_pow_add_two hp hp2 j, pow_one]
        linear_combination (-(p : ℤ) * jacobiSym n p ^ j * f32Coeff (p ^ j)) * hJ2
  rw [key, congruentArith_apply]

/-- **H4, first part: the $L$-series of Mathlib's $E_n$ has an entire extension**, conditional on
`F32Modular` (row 29) only. -/
theorem hasEntireExtension_lCoeff (hM : F32Modular) {n : ℕ} [NeZero n]
    (hn : Squarefree n) : LSeries.HasEntireExtension (lCoeff n) := by
  have : lCoeff n = fun m ↦ (congruentCoeff n m : ℂ) := by
    funext m
    rw [lCoeff, LFunction_congruentCurve_eq hn m]
  rw [this]
  exact hasEntireExtension_congruentCoeff hM (Nat.pos_of_ne_zero (NeZero.ne n))

/-- The abscissa of absolute convergence of the $L$-series of $E_n$ is at most $2$. -/
theorem abscissaOfAbsConv_lCoeff_le {n : ℕ} [NeZero n] (hn : Squarefree n) :
    LSeries.abscissaOfAbsConv (lCoeff n) ≤ 2 := by
  have : lCoeff n = fun m ↦ (congruentCoeff n m : ℂ) := by
    funext m
    rw [lCoeff, LFunction_congruentCurve_eq hn m]
  rw [this]
  exact abscissaOfAbsConv_congruentCoeff_le n

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
