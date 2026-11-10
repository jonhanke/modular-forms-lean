import ModularFormsKB.Miyake.Wave2B.TraceFormulaLevelOne
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action
import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.Composite
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.NumberTheory.DirichletCharacter.Basic
import ModularFormsKB.Citation
/-!
# Miyake Theorem 6.8.4 for $B = M_2(\mathbb Q)$ at level $N$ with character (statement only)

Miyake, *Modular Forms* (Springer 1989), Theorem 6.8.4 and Remark 6.8.2, pp. 262–265.

For $B = M_2(\mathbb Q)$ ($d_B = 1$), an order of level $N$ is an Eichler order, $\Gamma_R = \Gamma_0(N)$
(`normOneUnits_eichlerOrder`) and $T(n)$ is the Hecke operator of §4.5 (Remark 6.8.2). For a
Dirichlet character $\chi$ mod $N$ with conductor $m_\chi = \prod_p p^{e_p}$ and $k \ge 3$, Miyake's
formula reads
$$\operatorname{tr}\big(T(n) \mid S_k(\Gamma_0(N),\chi)\big)
 = \chi(\sqrt n)\,\frac{k-1}{12}\,n^{k/2-1}N\prod_{p\mid N}(1+p^{-1})
 - \sum_t a(t)\sum_{f\mid m} b(t,f)\,c(t,f),$$
with the terms below. Only $N = 1$, trivial $\chi$, even $k \ge 4$ is proved in this library
(`trace_T_levelOne`). The general statement is recorded here as the proposition
`MiyakeTheorem6_8_4_M2`; it is **not proved**. Miyake's proof needs the whole analytic
machinery of §6.1–§6.4 (reproducing kernels and the trace of an integral operator) and the local
computations of §6.5–§6.6 (Lemmas 6.6.1–6.6.5, Theorems 6.6.6–6.6.8), none of which is in Mathlib
or Tau Ceti.

## Conventions of the statement
* $S_k(\Gamma_0(N),\chi)$ is Tau Ceti's `cuspFormCharSpace k χ` ($f|_k\gamma = \chi(d)f$, the
  convention of Miyake §4.3) and $T(n)$ acts through Tau Ceti's Hecke-ring action
  `HeckeRing.GL2.heckeRingHomCuspCharSpace` of the element `heckeTCompositeGamma0 N n`
  (the classical $T(n)$, normalized as in Diamond–Shurman, which is Miyake's normalization
  $f|T(n) = n^{k/2-1}\sum f|_k\alpha$).
* $t$ runs over the integers with $t^2 - 4n$ negative or a square; $t^2 - 4n = m^2 d$ with $d$ the
  discriminant of $\mathbb Q(\sqrt{t^2-4n})$ if $t^2 < 4n$, $d = 1$ if $t^2 - 4n$ is a positive square
  and $d = 0$, $m = 1$ if $t^2 = 4n$.
* $a(t)$: `aEll`, `aHyp` of `TraceFormulaLevelOne`, and for $d = 0$
  $\frac14\chi(t/2)\operatorname{sgn}(t)^k n^{(k-1)/2}$.
* $b(t,f) = \frac{h(d)}{w(d)} f \prod_{p \mid f}(1 - (\tfrac dp)p^{-1})$ for $d < 0$, $\varphi(f)$ for
  $d = 1$, $1$ for $d = 0$. Here $(\tfrac dp)$ is the Kronecker symbol (Tau Ceti `kroneckerSym`)
  and $h(d)/w(d)$, for the fundamental discriminant $d < 0$, is written $H(|d|)/2$ with the Hurwitz
  class number $H$ (Tau Ceti `TauCeti.hurwitzClassNumber`): for fundamental $d$ every form of
  discriminant $d$ is primitive, and the weighted count $H(|d|)$ of reduced forms equals
  $2h(d)/w(d)$ by the classical correspondence between form classes and ideal classes (not
  formalized here).
* $c(t,f) = 1$ if $N = 1$; for $N > 1$, $c(t,f) = \prod_{p\mid N} c_p(t,f)$ with, for $\nu = \nu_p(N)$,
  $\rho = \nu_p(m/f)$, $e = e_p$:
  if $d \ne 0$, $c_p = \sum_{\xi \in \Omega/p^{\nu+\rho}} \chi_p(\xi)
  + \sum_{\xi \in \Omega'/p^{\nu+\rho}} \chi_p(t-\xi)$, where
  $\Omega = \{\xi \in \mathbb Z_p : \xi^2 - t\xi + n \equiv 0 \bmod p^{2\rho+\nu}\}$,
  $\Omega' = \{\xi : \xi^2 - t\xi + n \equiv 0 \bmod p^{2\rho+\nu+1}\}$ if $p \mid df$ and
  $\Omega' = \emptyset$ otherwise (both are unions of classes mod $p^{\nu+\rho}$, so the sums run
  over the residues $0 \le \xi < p^{\nu+\rho}$ in them); and if $d = 0$,
  $c_p = p^{\nu-[(\nu+1)/2]-\mu} + p^{\nu-[\nu/2]-1-\mu'}$ with $\mu = \max\{0, e-[(\nu+1)/2]\}$,
  $\mu' = \max\{0, e - [\nu/2] - 1\}$. Here $\chi_p$ is the character of $(\mathbb Z_p/N\mathbb Z_p)^\times$
  induced from $\chi$: $\chi_p(a) = \chi(a')$ with $a' \equiv a \bmod p^\nu$ and
  $a' \equiv 1 \bmod N/p^\nu$, and $\chi_p(a) = 0$ if $p \mid a$.
-/

open Complex

noncomputable section

namespace ModularFormsKB.Miyake.Wave2B

/-- The local component $\chi_p$ of a Dirichlet character $\chi$ mod $N$ at a prime $p \mid N$:
$\chi_p(a) = \chi(a')$ with $a' \equiv a \bmod p^{\nu}$, $a' \equiv 1 \bmod N/p^{\nu}$
($\nu = \nu_p(N)$), and $\chi_p(a) = 0$ if $p \mid a$. -/
def localChar {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) (a : ℤ) : ℂ :=
  if (p : ℤ) ∣ a then 0 else
    if h : Nat.Coprime (p ^ N.factorization p) (N / p ^ N.factorization p) then
      χ ((Nat.chineseRemainder h (a % (p ^ N.factorization p : ℕ)).toNat 1).1 : ZMod N)
    else 0

/-- Miyake's $c_p(t,f)$ for $d \ne 0$:
$\sum_{\xi \in \Omega/p^{\nu+\rho}}\chi_p(\xi) + \sum_{\xi\in\Omega'/p^{\nu+\rho}}\chi_p(t - \xi)$, with
`hd : p ∣ d f` deciding whether $\Omega'$ is empty. -/
def localSumNonzero {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) (t : ℤ) (n : ℕ) (ρ : ℕ)
    (hd : Prop) [Decidable hd] : ℂ :=
  let ν := N.factorization p
  (∑ ξ ∈ Finset.range (p ^ (ν + ρ)),
    if ((p ^ (2 * ρ + ν) : ℕ) : ℤ) ∣ (ξ : ℤ) ^ 2 - t * ξ + n then localChar χ p ξ else 0) +
  (if hd then ∑ ξ ∈ Finset.range (p ^ (ν + ρ)),
    if ((p ^ (2 * ρ + ν + 1) : ℕ) : ℤ) ∣ (ξ : ℤ) ^ 2 - t * ξ + n then localChar χ p (t - ξ)
      else 0
   else 0)

/-- Miyake's $c_p(t,1)$ for $d = 0$:
$p^{\nu-[(\nu+1)/2]-\mu} + p^{\nu-[\nu/2]-1-\mu'}$. -/
def localSumZero {N : ℕ} (χ : DirichletCharacter ℂ N) (p : ℕ) : ℂ :=
  let ν := N.factorization p
  let e := χ.conductor.factorization p
  let μ := e - (ν + 1) / 2
  let μ' := e - ν / 2 - 1
  (p : ℂ) ^ (ν - (ν + 1) / 2 - μ) + (p : ℂ) ^ (ν - ν / 2 - 1 - μ')

/-- Miyake's $c(t,f)$ for $d \ne 0$, with $m$ the integer of $t^2 - 4n = m^2 d$. -/
def cNonzero {N : ℕ} (χ : DirichletCharacter ℂ N) (t : ℤ) (n : ℕ) (d : ℤ) (m f : ℕ) : ℂ :=
  if N = 1 then 1 else
    ∏ p ∈ N.primeFactors, localSumNonzero χ p t n ((m / f).factorization p)
      ((p : ℤ) ∣ d * f)

/-- Miyake's $c(t,1)$ for $d = 0$. -/
def cZero {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ :=
  if N = 1 then 1 else ∏ p ∈ N.primeFactors, localSumZero χ p

/-- Miyake's $b(t,f)$ for $d < 0$: $\frac{h(d)}{w(d)} f\prod_{p\mid f}(1 - (\tfrac dp)p^{-1})$, with
$h(d)/w(d) = H(|d|)/2$ (see the module docstring). -/
def bEll (d : ℤ) (f : ℕ) : ℂ :=
  ((TauCeti.hurwitzClassNumber d.natAbs : ℚ) : ℂ) / 2 * f *
    ∏ p ∈ f.primeFactors, (1 - (TauCeti.kroneckerSym d p : ℂ) / p)

/-- The elliptic terms: pairs $(t, m)$ with $t^2 < 4n$, $m > 0$ and $(t^2 - 4n)/m^2$ a
fundamental discriminant (for each such $t$ there is exactly one such $m$). -/
def ellipticPairs (n : ℕ) : Finset (ℤ × ℕ) :=
  ((Finset.Icc (-2 * (n : ℤ)) (2 * n)) ×ˢ Finset.Icc 1 (2 * n)).filter fun q ↦
    q.1 ^ 2 < 4 * (n : ℤ) ∧ ((q.2 : ℤ) ^ 2 ∣ q.1 ^ 2 - 4 * n) ∧
      Int.IsFundamentalDiscr ((q.1 ^ 2 - 4 * n) / (q.2 : ℤ) ^ 2)

open scoped Classical in
/-- **Miyake, Theorem 6.8.4 for $B = M_2(\mathbb Q)$** (statement only, NOT proved). For $N \ge 1$,
a Dirichlet character $\chi$ mod $N$, $k \ge 3$ and $n \ge 1$, the trace of $T(n)$ on
$S_k(\Gamma_0(N),\chi)$ is given by Miyake's formula (see the module docstring for each term).
The case $N = 1$, $\chi = 1$, $k$ even is `trace_T_levelOne`. -/
@[kb "miyake1989" "Theorem 6.8.4, p. 263 (B = M2(Q); statement)"]
def MiyakeTheorem6_8_4_M2 : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℕ), 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (n : ℕ) [NeZero n],
    LinearMap.trace ℂ _ (HeckeRing.GL2.heckeRingHomCuspCharSpace (k : ℤ) χ.toUnitHom
        (HeckeRing.GL2.heckeTCompositeGamma0 N n)) =
      (if IsSquare n then χ (Nat.sqrt n) * (((k : ℂ) - 1) / 12) * (Nat.sqrt n : ℂ) ^ (k - 2) *
          N * ∏ p ∈ N.primeFactors, (1 + (p : ℂ)⁻¹) else 0)
      - ∑ q ∈ ellipticPairs n, aEll k q.1 n *
          ∑ f ∈ q.2.divisors, bEll ((q.1 ^ 2 - 4 * n) / (q.2 : ℤ) ^ 2) f *
            cNonzero χ q.1 n ((q.1 ^ 2 - 4 * n) / (q.2 : ℤ) ^ 2) q.2 f
      - ∑ q ∈ hyperbolicTs n, (aHyp k q.1 q.2 : ℂ) *
          ∑ f ∈ q.2.divisors, (f.totient : ℂ) * cNonzero χ q.1 n 1 q.2 f
      - ∑ t ∈ parabolicTs n, (1 / 4 * χ ((t / 2 : ℤ) : ZMod N) * (Real.sign (t : ℝ) ^ k : ℝ) *
          ((n : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ)) * cZero χ

end ModularFormsKB.Miyake.Wave2B
