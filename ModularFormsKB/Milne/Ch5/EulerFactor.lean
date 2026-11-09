import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ModularFormsKB.Miyake.HeckeAlgebras

/-!
# Milne, Chapter 5: Euler products and the Ramanujan factor (Propositions 5.1, 5.2)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 67–69.

**Euler products are formal.** Milne proves Proposition 5.1 by comparing coefficients of $p^{-ms}$: the identity
$L(\Delta, s) = \prod_p (1 - \tau(p)p^{-s} + p^{11-2s})^{-1}$ is read as the multiplicativity of $\tau$ together with
the local identity $\big(\sum_{m \ge 0} \tau(p^m) X^m\big)(1 - \tau(p)X + p^{11}X^2) = 1$ in $\mathbb C[[X]]$,
$X = p^{-s}$, for every prime $p$. This is `ModularFormsKB.Miyake.HasHeckeEulerProduct` with $d(n) = n^{2k-2}$,
so that $p\,d(p) = p^{2k-1}$; the equivalence is Miyake's Lemma 4.5.12 (`Miyake.heckeRecursion_tfae`).

**Weight convention.** Milne writes weight $2k$; the sequence `d` below is $n \mapsto n^{2k-2}$ and the Euler factor
is $1 - c(p)X + p^{2k-1}X^2$. For $\Delta$, $2k = 12$.

## Items
- Proposition 5.1, in the general form used for Proposition 5.21 (`eulerProduct_iff_heckeRelations`).
- Proposition 5.2, and its weight-$2k$ form on p. 69 (`eulerFactor_tfae`, `eulerFactor_tfae_of_poly`).
-/

open Polynomial

namespace ModularFormsKB.Milne

/-- The completely multiplicative sequence $n \mapsto n^{2k-2}$ whose value at a prime gives the Euler factor
$1 - c(p)X + p\cdot p^{2k-2}X^2 = 1 - c(p)X + p^{2k-1}X^2$ of weight $2k$. -/
def weightChar (k : ℕ) (n : ℕ) : ℂ := (n : ℂ) ^ (2 * k - 2)

theorem weightChar_one (k : ℕ) : weightChar k 1 = 1 := by simp [weightChar]

theorem weightChar_mul (k : ℕ) (m n : ℕ) : weightChar k (m * n) = weightChar k m * weightChar k n := by
  simp [weightChar, mul_pow]

/-- $p \cdot p^{2k-2} = p^{2k-1}$ for $k \ge 1$. -/
theorem natCast_mul_weightChar {k : ℕ} (hk : 1 ≤ k) (p : ℕ) :
    (p : ℂ) * weightChar k p = (p : ℂ) ^ (2 * k - 1) := by
  rw [weightChar, ← pow_succ']
  congr 1
  omega

/-- **Milne, Proposition 5.1** (general weight; Milne states it for $\tau$, $2k = 12$, and reuses the argument for
Proposition 5.21). Let $c : \mathbb N \to \mathbb C$ with $c(1) = 1$. The Dirichlet series $\sum c(n)n^{-s}$ has the
Euler product $\prod_p (1 - c(p)p^{-s} + p^{2k-1-2s})^{-1}$ (read formally, see the module docstring) if and only if
$c(mn) = c(m)c(n)$ for coprime $m, n$ and $c(p)c(p^n) = c(p^{n+1}) + p^{2k-1}c(p^{n-1})$ for primes $p$ and
$n \ge 1$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.1 (pdf p. 67)"]
theorem eulerProduct_iff_heckeRelations (k : ℕ) (c : ℕ → ℂ) (hc : c 1 = 1) :
    Miyake.HasHeckeEulerProduct c (weightChar k) ↔ Miyake.HeckeRecursion c (weightChar k) :=
  ((Miyake.heckeRecursion_tfae c (weightChar k) hc (weightChar_one k)
    (fun m n _ _ ↦ weightChar_mul k m n)).out 2 1)

/-- **Milne, Proposition 5.2**, for a real number $t$ and $c > 0$ (Milne: $t = \tau(p)$, $c = p^{11}$; on p. 69:
$t = c(p)$, $c = p^{2k-1}$). If $a + a' = t$ and $aa' = c$, i.e. $1 - tX + cX^2 = (1 - aX)(1 - a'X)$, the following
are equivalent: (a) $|t| \le 2\sqrt c$; (b) $|a| = \sqrt c = |a'|$; (c) $a' = \bar a$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.2 (pdf p. 68); weight 2k form (pdf p. 69)"]
theorem eulerFactor_tfae {t c : ℝ} (hc : 0 < c) {a a' : ℂ} (hsum : a + a' = t) (hprod : a * a' = c) :
    [|t| ≤ 2 * √c, ‖a‖ = √c ∧ ‖a'‖ = √c, a' = (starRingEnd ℂ) a].TFAE := by
  have ha' : a' = t - a := by rw [← hsum]; ring
  tfae_have 2 → 1 := by
    rintro ⟨h1, h2⟩
    have : ‖(t : ℂ)‖ ≤ ‖a‖ + ‖a'‖ := hsum ▸ norm_add_le a a'
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  tfae_have 3 → 2 := by
    intro h3
    have hn : ‖a‖ ^ 2 = c := by
      have := congrArg Complex.re hprod
      rw [h3, Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
      exact_mod_cast this
    have hna : ‖a‖ = √c := by
      rw [← hn, Real.sqrt_sq (norm_nonneg _)]
    exact ⟨hna, by rw [h3, Complex.norm_conj, hna]⟩
  tfae_have 1 → 3 := by
    intro h1
    have hq : a * a - t * a + c = 0 := by
      rw [show ((c : ℝ) : ℂ) = a * a' from hprod.symm, ha']; ring
    have hre := congrArg Complex.re hq
    have him := congrArg Complex.im hq
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.zero_im] at hre him
    have h2c : (2 * √c) ^ 2 = 4 * c := by
      rw [mul_pow, Real.sq_sqrt hc.le]; ring
    have ht2 : t ^ 2 ≤ 4 * c := by
      rw [← h2c, ← sq_abs t]
      exact pow_le_pow_left₀ (abs_nonneg t) h1 2
    have hx : a.re = t / 2 := by
      rcases mul_eq_zero.1 (show a.im * (2 * a.re - t) = 0 by linarith) with hy | hx
      · rw [hy] at hre
        nlinarith [sq_nonneg (2 * a.re - t)]
      · linarith
    rw [ha']
    apply Complex.ext <;> simp [hx]; ring
  tfae_finish

/-- Proposition 5.2 with the factorization written as an identity of polynomials, as in Milne:
$1 - tX + cX^2 = (1 - aX)(1 - a'X)$ in $\mathbb C[X]$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.2 (pdf p. 68)"]
theorem eulerFactor_tfae_of_poly {t c : ℝ} (hc : 0 < c) {a a' : ℂ}
    (h : (1 - C (t : ℂ) * X + C (c : ℂ) * X ^ 2 : ℂ[X]) = (1 - C a * X) * (1 - C a' * X)) :
    [|t| ≤ 2 * √c, ‖a‖ = √c ∧ ‖a'‖ = √c, a' = (starRingEnd ℂ) a].TFAE := by
  have h1 := congrArg (Polynomial.coeff · 1) h
  have h2 := congrArg (Polynomial.coeff · 2) h
  simp only [coeff_sub, coeff_add, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow] at h1 h2
  have e : (1 - C a * X) * (1 - C a' * X) = (1 : ℂ[X]) - C (a + a') * X + C (a * a') * X ^ 2 := by
    simp only [C_add, C_mul]; ring
  rw [e] at h1 h2
  simp only [coeff_sub, coeff_add, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow] at h1 h2
  norm_num at h1 h2
  exact eulerFactor_tfae hc (by linear_combination h1) h2.symm

end ModularFormsKB.Milne
