/-
# The local factors of Mathlib's $L$-function of $E_n$

Mathlib's `WeierstrassCurve.LFunction` is the Euler product over the height-one primes of $\mathcal O_{\mathbb Q}$ of
local factors built from the minimal model over the completion. For $E_n$, $n \ge 1$ squarefree, $\Delta = 64n^6$:
- at $p \nmid 2n$ the model is minimal with good reduction, and the local polynomial is $1 - a_pT + pT^2$ with $a_p$
  the Frobenius trace of $E_n \bmod p$ (`congruentCurveMod`): `LFunction_congruentCurve_prime`,
  `LFunction_congruentCurve_prime_pow_add_two`;
- at $p \mid 2n$ the reduction is bad but potentially good ($j = 1728$), so the local polynomial is $1$
  (Tau Ceti `localPolynomial_eq_one_of_hasPotentialGoodReduction_of_not_hasGoodReduction`) and the coefficients at
  $p^k$, $k \ge 1$, vanish: `LFunction_congruentCurve_prime_pow_of_dvd`. At $p = 2$ with $n$ even, $v_2(\Delta) = 12$;
  good reduction is excluded because a model with unit discriminant and $j \equiv 0$ has $a_1$ even, hence
  $16 \mid c_4$, while $v_2(c_4/2^4) = 2$ here.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Curve
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Coefficients
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralReduction
import TauCeti.AlgebraicGeometry.EllipticCurve.LFunction.Basic
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.LocalFactorsAux

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open WeierstrassCurve IsDedekindDomain NumberField Rat.HeightOneSpectrum

/-- If `p ∤ 2n` then `p ∤ 64 n⁶`. -/
theorem not_dvd_64_mul_pow {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ 2 * n) : ¬ p ∣ 64 * n ^ 6 := by
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · apply h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 6 by norm_num; exact h1)
    exact dvd_mul_of_dvd_left h2 n
  · exact h (dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow h1) 2)

/-- **Bad primes**: the coefficients of `LFunction` at $p^k$, $k \ge 1$, vanish for $p \mid 2n$. -/
theorem LFunction_congruentCurve_prime_pow_of_dvd {n : ℕ} [NeZero n] (hn : Squarefree n) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 * n) {k : ℕ} (hk : 1 ≤ k) : (congruentCurve n).LFunction (p ^ k) = 0 := by
  set v : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm (⟨p, hp⟩ : Nat.Primes) with hv
  have hg : natGenerator v = p := natGenerator_symm hp
  have h1 : localSeriesOf (congruentCurve n) v = 1 :=
    localPowerSeries_eq_one (R := v.adicCompletionIntegers ℚ) _ (localPolynomial_bad v hp hg n hn hpn)
  rw [LFunction_prime_pow_eq _ hp k, h1, PowerSeries.coeff_one, ite_eq_right (by omega)]

/-- **Good primes**: the $p$-th coefficient is the Frobenius trace of $E_n \bmod p$. -/
theorem LFunction_congruentCurve_prime {n : ℕ} [NeZero n] {p : ℕ} [Fact p.Prime] (hpn : ¬ p ∣ 2 * n) :
    (congruentCurve n).LFunction p = (congruentCurveMod n p).frobeniusTrace := by
  have hp : p.Prime := Fact.out
  set v : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm (⟨p, hp⟩ : Nat.Primes) with hv
  have hg : natGenerator v = p := natGenerator_symm hp
  have h := LFunction_prime_pow_eq (congruentCurve n) hp 1
  rw [pow_one] at h
  rw [h]
  exact (localSeries_good v hg n (not_dvd_64_mul_pow hp hpn)).2.1

/-- **Good primes**: the recursion $c(p^{k+2}) = a_p\,c(p^{k+1}) - p\,c(p^k)$. -/
theorem LFunction_congruentCurve_prime_pow_add_two {n : ℕ} [NeZero n] {p : ℕ} [Fact p.Prime] (hpn : ¬ p ∣ 2 * n)
    (k : ℕ) : (congruentCurve n).LFunction (p ^ (k + 2)) =
      (congruentCurveMod n p).frobeniusTrace * (congruentCurve n).LFunction (p ^ (k + 1)) -
        p * (congruentCurve n).LFunction (p ^ k) := by
  have hp : p.Prime := Fact.out
  set v : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm (⟨p, hp⟩ : Nat.Primes) with hv
  have hg : natGenerator v = p := natGenerator_symm hp
  rw [LFunction_prime_pow_eq _ hp (k + 2), LFunction_prime_pow_eq _ hp (k + 1),
    LFunction_prime_pow_eq _ hp k]
  exact (localSeries_good v hg n (not_dvd_64_mul_pow hp hpn)).2.2 k

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
