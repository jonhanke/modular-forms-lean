import ModularFormsKB.HalfIntegral.Forms
import ModularFormsKB.Iwaniec1997.KloostermanBounds

/-!
# Iwaniec, Section 5.3: coefficients of cusp forms with the theta multiplier (statements)

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Section 5.3, p. 75. Page numbers are printed pages.

The book's weight is $k = \ell + \tfrac12$; in this repository a form of weight $\ell + \tfrac12$ on $\Gamma_0(4N)$ with
the theta multiplier (5.26) and trivial character is `ModularFormsKB.HalfIntegral.IsHalfIntCuspForm ℓ N 1`: its
transformation law is $f(\gamma z) = j(\gamma, z)^{2\ell+1} f(z)$ with $j(\gamma,z) = \theta(\gamma z)/\theta(z)$
(`ModularFormsKB.HalfIntegral.thetaMult`), which is $\vartheta(\gamma)(cz+d)^k$ for the book's (5.26). The book's level
$N$ with $4 \mid N$ is our $4N$.

- (5.27): `ThetaMultiplierCoeffBound`, the bound $a(n) \ll n^{k/2-1/4+\varepsilon}$ obtained in the book from the Salié
  bound (4.45) and Proposition 5.5. Not proved here.
- **Theorem 5.6**: `IwaniecTheorem56`, for squarefree $n$,
  $a(n) \ll n^{k/2 - 1/4 - 1/222}\tau(n)\log n$. Not proved here. (The exponent $1/222$ is confirmed by the last step
  (5.42) of the proof, $\mathcal S \ll n^{1/2 - 1/111}(\tau(n)\log n)^2$, which is squared relative to $a(n)$.)

These are stated, not proved: the proofs need the Petersson formula (`PeterssonFormulaGamma0`, here only stated)
in half-integral weight and the Salié-sum evaluation (Corollary 4.11). In this repository's normalization
$k/2 - 1/4 = \ell/2$.
-/

open Complex
open scoped Real

noncomputable section

namespace ModularFormsKB.Iwaniec1997

open ModularFormsKB.HalfIntegral

/-- **(5.27)** (not proved here): for $\ell \ge 1$ and $f \in S_{\ell+1/2}(\Gamma_0(4N), \vartheta)$ with Fourier
coefficients $a(n)$, $a(n) \ll_{f,\varepsilon} n^{k/2 - 1/4 + \varepsilon}$ for every $\varepsilon > 0$, where
$k = \ell + \tfrac12$, i.e. the exponent is $\ell/2 + \varepsilon$. -/
@[kb "iwaniec1997" "Section 5.3, (5.27), p. 75"]
def ThetaMultiplierCoeffBound : Prop :=
  ∀ (ℓ N : ℕ), 1 ≤ ℓ → 1 ≤ N → ∀ (f : UpperHalfPlane → ℂ), IsHalfIntCuspForm ℓ N 1 f →
    ∀ (a : ℕ → ℂ), HasQExpansion f a → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((ℓ : ℝ) / 2 + ε)

/-- **Theorem 5.6** (not proved here): let $k = \ell + \tfrac12 \ge \tfrac52$, $4 \mid N$ and
$f \in S_k(\Gamma_0(N), \vartheta)$. Then for squarefree $n$ the $n$-th Fourier coefficient satisfies
$a(n) \ll_f n^{k/2 - 1/4 - 1/222}\,\tau(n)\log n$. The logarithm vanishes at $n = 1$, so the bound is asserted for
$n \ge 2$. In our normalization the exponent is $\ell/2 - 1/222$. -/
@[kb "iwaniec1997" "Section 5.3, Theorem 5.6, (5.29), p. 75"]
def IwaniecTheorem56 : Prop :=
  ∀ (ℓ N : ℕ), 2 ≤ ℓ → 1 ≤ N → ∀ (f : UpperHalfPlane → ℂ), IsHalfIntCuspForm ℓ N 1 f →
    ∀ (a : ℕ → ℂ), HasQExpansion f a →
      ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → Squarefree n →
        ‖a n‖ ≤ C * (n : ℝ) ^ ((ℓ : ℝ) / 2 - 1 / 222) * divisorCount n * Real.log n

end ModularFormsKB.Iwaniec1997
