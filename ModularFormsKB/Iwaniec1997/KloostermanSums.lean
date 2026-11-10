import ModularFormsKB.Iwaniec1997.KloostermanBounds
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Iwaniec, Chapter 4: Katz's bound, sums of Kloosterman sums, Salié's formula (statements)

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Sections 4.4-4.6, pp. 64-68. Page numbers are
printed pages. All results in this file are **stated, not proved** (named propositions).

- **Theorem 4.6** (Katz), (4.31): `KatzBound`. The book writes $S(a,1;p) = 2\sqrt p\cos\theta_p(a)$ with
  $0 \le \theta_p(a) \le \pi$ and uses the Chebyshev polynomials $U_k(2\cos\theta) = \sin(k+1)\theta/\sin\theta$. Mathlib's
  `Polynomial.Chebyshev.U` is normalized by $U_k(\cos\theta)\sin\theta = \sin(k+1)\theta$, so the book's
  $U_k(2\cos\theta_p(a))$ is Mathlib's $U_k$ at $\cos\theta_p(a) = S(a,1;p)/2\sqrt p$; no angle is needed.
- (4.34): `KloostermanSquareMean`.
- **Lemma 4.7** (4.35): `KloostermanDoubleSumBound`, with $\tau_3$ (`divisorCount3`).
- **Corollary 4.11** (4.46), Salié's formula: `SalieFormula`.
-/

open Complex Finset
open scoped Real

noncomputable section

namespace ModularFormsKB.Iwaniec1997

/-- The function $\tau_3(n)$, the number of ordered factorizations $n = d_1d_2d_3$; equal to $\sum_{d \mid n}\tau(d)$. -/
def divisorCount3 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, divisorCount d

/-- $e(x/b) = e^{2\pi i x/b}$ for an integer $x$ and a natural number $b$. -/
def eFrac (x : ℤ) (b : ℕ) : ℂ := cexp (2 * π * I * x / b)

/-- **Theorem 4.6** (N. Katz; not proved here), (4.31): for $k \ge 1$ and a prime $p > 2$,
$\big|\sum^*_{a \bmod p} U_k(2\cos\theta_p(a))\big| \le \tfrac12(k+1)p^{1/2}$, where $S(a,1;p) = 2\sqrt p\cos\theta_p(a)$.
In Mathlib's normalization of the Chebyshev polynomials the summand is $U_k\big(S(a,1;p)/2\sqrt p\big)$. -/
@[kb "iwaniec1997" "Section 4.4, Theorem 4.6, (4.31), p. 64"]
def KatzBound : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (p : ℕ) (hp : p.Prime), 2 < p →
    haveI : NeZero p := ⟨hp.ne_zero⟩
    |∑ a : (ZMod p)ˣ, (Polynomial.Chebyshev.U ℝ k).eval
        ((kloostermanMod p (a : ZMod p) 1).re / (2 * Real.sqrt p))| ≤ (k + 1) / 2 * Real.sqrt p

/-- **(4.34)** (not proved here): for $r \ge 1$ and an integer $n$,
$\frac1r\sum_{a \bmod r}|S(an,an;r)|^2 \le 4(n,r)\,r\,\tau(r)$. -/
@[kb "iwaniec1997" "Section 4.5, (4.34), p. 65"]
def KloostermanSquareMean : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ n : ℤ,
    (1 / (r : ℝ)) * ∑ a ∈ range r, ‖kloosterman (a * n) (a * n) r‖ ^ 2 ≤
      4 * Int.gcd n r * r * divisorCount r

/-- **Lemma 4.7** (not proved here), (4.35): there is an absolute constant $C$ such that for every positive integer
$n$ and all real $Q, R \ge 1$,
$\sum_{q \le Q}\sum_{r \le R}(qr)^{-1}|S(n,n;qr)| \le C\,\tau_3(n)(Q+R)(\log 4QR)^3$. -/
@[kb "iwaniec1997" "Section 4.5, Lemma 4.7, (4.35), p. 65"]
def KloostermanDoubleSumBound : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (Q R : ℝ), 1 ≤ Q → 1 ≤ R →
    ∑ q ∈ Icc 1 ⌊Q⌋₊, ∑ r ∈ Icc 1 ⌊R⌋₊, ‖kloosterman n n (q * r)‖ / ((q : ℝ) * r) ≤
      C * divisorCount3 n * (Q + R) * Real.log (4 * Q * R) ^ 3

/-- **Corollary 4.11** (Salié's formula; not proved here), (4.46): if $(c, 2n) = 1$ then
$$T(n,n;c) = \Big(\frac nc\Big) g(c) \sum_{ab = c,\ (a,b) = 1} e\Big(2n\Big(\frac{\bar a}{b} - \frac{\bar b}{a}\Big)\Big),$$
with $a\bar a \equiv 1 \pmod b$, $b\bar b \equiv 1 \pmod a$ and $g(c) = g(1,c)$ (4.37). The sum runs over the divisors
$a$ of $c$ coprime to $b = c/a$; $\bar a$ is the least nonnegative residue of the inverse of $a$ in $\mathbb Z/b$. -/
@[kb "iwaniec1997" "Section 4.6, Corollary 4.11, (4.46), p. 68"]
def SalieFormula : Prop :=
  ∀ (c : ℕ) [NeZero c] (n : ℤ), IsCoprime (c : ℤ) (2 * n) →
    salie n n c = (jacobiSym n c : ℂ) * quadGaussSum 1 c *
      ∑ a ∈ c.divisors.filter (fun a ↦ Nat.Coprime a (c / a)),
        eFrac (2 * n * (((a : ZMod (c / a))⁻¹).val : ℤ)) (c / a) *
          eFrac (-(2 * n * ((((c / a : ℕ) : ZMod a)⁻¹).val : ℤ))) a

end ModularFormsKB.Iwaniec1997
