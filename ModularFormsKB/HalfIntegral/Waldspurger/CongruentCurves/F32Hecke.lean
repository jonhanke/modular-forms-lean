/-
# The Hecke relations of $f_{32}$ (coefficient side)

$b(m) = \sum_{\alpha \equiv 1 \bmod (2+2i),\ N\alpha = m}\alpha$ (`f32Coeff`). The elements $\alpha \equiv 1 \bmod (2+2i)$
form a multiplicative monoid meeting every ideal of $\mathbb Z[i]$ prime to $1 + i$ exactly once, and
$\alpha \mapsto \alpha$ is multiplicative on it; with unique factorization in $\mathbb Z[i]$ this gives the Hecke
relations of weight $2$ and trivial character at every odd prime $p$:
$$ b(pn) + [p \mid n]\,p\,b(n/p) = b(p)\,b(n).$$
Also proved: $b$ is multiplicative.

Proofs (Sonnet 5.5): in `F32HeckeAux*.lean`, with $B(m) = \sum \alpha \in \mathbb Z[i]$; for $p \equiv 1 \bmod 4$ by
inclusion-exclusion on $\pi\cdot S(n) \cup \bar\pi\cdot S(n)$, for $p \equiv 3 \bmod 4$ since $p$ is inert.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Coefficients
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32HeckeAux3
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open F32Aux

/-- **The Hecke relations of $f_{32}$** at odd primes. -/
theorem f32Coeff_hecke {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    f32Coeff (p * n) + (if p ∣ n then (p : ℤ) * f32Coeff (n / p) else 0) = f32Coeff p * f32Coeff n := by
  have h := B_hecke hp hp2 n
  simp only [B_eq] at h
  by_cases hd : p ∣ n
  · rw [if_pos hd] at h
    have := congrArg Zsqrtd.re h
    simp at this
    rw [if_pos hd]
    linarith
  · rw [if_neg hd] at h
    have := congrArg Zsqrtd.re h
    simp at this
    rw [if_neg hd]
    linarith

private theorem pow_mul_of_not_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : ¬ p ∣ n) :
    ∀ k, f32Coeff (p ^ k * n) = f32Coeff (p ^ k) * f32Coeff n := by
  have H : ∀ k, (f32Coeff (p ^ k * n) = f32Coeff (p ^ k) * f32Coeff n) ∧
      (f32Coeff (p ^ (k + 1) * n) = f32Coeff (p ^ (k + 1)) * f32Coeff n) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp [f32Coeff_one], ?_⟩
      have := f32Coeff_hecke hp hp2 n
      rw [if_neg hn, add_zero] at this
      simpa using this
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := f32Coeff_hecke hp hp2 (p ^ (k + 1) * n)
      have h2 := f32Coeff_hecke hp hp2 (p ^ (k + 1))
      have hk : p ∣ p ^ (k + 1) := dvd_pow_self p (Nat.succ_ne_zero k)
      rw [if_pos (Dvd.dvd.mul_right hk n)] at h1
      rw [if_pos hk] at h2
      have e1 : p ^ (k + 1) * n / p = p ^ k * n := by
        rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
      have e2 : p * (p ^ (k + 1) * n) = p ^ (k + 1 + 1) * n := by ring
      have e3 : p ^ (k + 1) / p = p ^ k := by
        rw [pow_succ', Nat.mul_div_cancel_left _ hp.pos]
      have e4 : p * p ^ (k + 1) = p ^ (k + 1 + 1) := by ring
      rw [e1, e2] at h1
      rw [e3, e4] at h2
      linear_combination h1 - f32Coeff n * h2 - (p : ℤ) * ih.1 + f32Coeff p * ih.2
  exact fun k => (H k).1

/-- **$b$ is multiplicative.** -/
theorem f32Coeff_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) : f32Coeff (m * n) = f32Coeff m * f32Coeff n := by
  revert n
  induction m using Nat.recOnPrimeCoprime with
  | zero =>
    intro n h
    obtain rfl := (Nat.coprime_zero_left n).1 h
    simp [f32Coeff_zero]
  | prime_pow p k hp =>
    intro n h
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [f32Coeff_one]
    by_cases hp2 : p = 2
    · subst hp2
      have h1 : 2 ∣ 2 ^ k * n := Dvd.dvd.mul_right (dvd_pow_self 2 hk.ne') n
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
      rw [f32Coeff_even (by omega), f32Coeff_even (by omega), zero_mul]
    · have hc : Nat.Coprime p n := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk.ne') h
      have hn : ¬ p ∣ n := (Nat.Prime.coprime_iff_not_dvd hp).1 hc
      exact pow_mul_of_not_dvd hp hp2 hn k
  | coprime a b ha hb hab iha ihb =>
    intro n h
    obtain ⟨han, hbn⟩ := Nat.coprime_mul_iff_left.1 h
    rw [mul_assoc, iha (Nat.Coprime.mul_right hab han), ihb hbn, iha hab]
    ring

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
