import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Basic
import ModularFormsKB.Citation
/-!
# Shimura 2007, §3.1: Hecke's functional equation (Theorem 3.2)

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), §3.1,
pp. 19–20 (pdf pp. 25–26).

**Setting (3.1)–(3.3).** Fix integers $h, N > 0$ and a real $k$. Let
$f(z) = \sum_{0 \le \xi \in h^{-1}\mathbb Z} a_\xi\,\mathbf e(\xi z)$ be holomorphic on $\mathfrak H$ and
$$f^\#(z) = N^{-k/2}(-iz)^{-k}f(-(Nz)^{-1}) = \sum_{0\le\xi\in h^{-1}\mathbb Z} b_\xi\,\mathbf e(\xi z),$$
with $|a_\xi|, |b_\xi| = O(\xi^\alpha)$; $D(s,f) = \sum_{\xi>0}a_\xi\xi^{-s}$ and
$R(s,f) = (2\pi)^{-s}\Gamma(s)D(s,f)$. We index the coefficients by $n \in \mathbb N$,
$\xi = n/h$; $(-iz)^{-k}$ is the principal branch (`Complex.cpow`), real and positive on
$\mathfrak H \cap i\mathbb R$ as Shimura requires.

Theorem 3.2 is stated as `HeckeFunctionalEquationStatement`, **not proved**. Mathlib's abstract
form is `WeakFEPair.functional_equation` with the residues `WeakFEPair.Λ_residue_k`,
`WeakFEPair.Λ_residue_zero`; deriving Shimura's form needs the Mellin transform of
$f(iy) - a_0$ computed termwise, which is not done here.
-/

open Complex
open scoped Real

namespace ModularFormsKB.Shimura2007

/-- The Dirichlet series $D(s,f) = \sum_{\xi > 0}a_\xi\xi^{-s}$ of (3.3), with $\xi = n/h$. -/
noncomputable def heckeD (h : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, if n = 0 then 0 else a n * ((n : ℂ) / h) ^ (-s)

/-- $R(s,f) = (2\pi)^{-s}\Gamma(s)D(s,f)$ of (3.3). -/
noncomputable def heckeR (h : ℕ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  (2 * π : ℂ) ^ (-s) * Gamma s * heckeD h a s

/-- The $q$-series $\sum_{n \ge 0} a_n\,\mathbf e(nz/h)$ of (3.1). -/
noncomputable def heckeSeries (h : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, a n * cexp (2 * π * I * (n / h) * z)

/-- **Theorem 3.2** (Hecke), (3.4a), (3.4b), **stated, not proved**. In the setting (3.1)–(3.3)
(coefficients $a_n, b_n$ of $f$ and $f^\#$ at $\xi = n/h$, both $O(n^\alpha)$ for $n \ge 1$), there are
functions $R_f, R_{f^\#}$ on $\mathbb C$ (the continuations) such that
* $R_f(s) = R(s,f)$ and $R_{f^\#}(s) = R(s,f^\#)$ for $\operatorname{Re}s > \alpha + 1$;
* (3.4a) $N^{s/2}R_f(s) = -a_0/s + b_0/(s-k) + (\text{entire})$, and likewise
  $N^{s/2}R_{f^\#}(s) = -b_0/s + a_0/(s-k) + (\text{entire})$, as $(f^\#)^\# = f$;
* (3.4b) $R_f(k-s) = N^{s-k/2}R_{f^\#}(s)$ for $s \ne 0, k$.

The hypothesis that $f$ is the $q$-series is imposed on $\mathfrak H$ (`0 < z.im`). -/
@[kb "shimura2007" "Theorem 3.2, (3.4a), (3.4b), p. 20"]
def HeckeFunctionalEquationStatement : Prop :=
  ∀ (h N : ℕ), 0 < h → 0 < N → ∀ (k α : ℝ) (a b : ℕ → ℂ),
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ α ∧ ‖b n‖ ≤ C * (n : ℝ) ^ α) →
    (∀ z : ℂ, 0 < z.im → Summable fun n ↦ a n * cexp (2 * π * I * (n / h) * z)) →
    (∀ z : ℂ, 0 < z.im → Summable fun n ↦ b n * cexp (2 * π * I * (n / h) * z)) →
    (∀ z : ℂ, 0 < z.im →
      heckeSeries h b z = (N : ℂ) ^ (-(k : ℂ) / 2) * (-I * z) ^ (-(k : ℂ)) *
        heckeSeries h a (-(N * z)⁻¹)) →
    ∃ Rf Rg Ef Eg : ℂ → ℂ, Differentiable ℂ Ef ∧ Differentiable ℂ Eg ∧
      (∀ s : ℂ, α + 1 < s.re → Rf s = heckeR h a s ∧ Rg s = heckeR h b s) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ k →
        (N : ℂ) ^ (s / 2) * Rf s = -a 0 / s + b 0 / (s - k) + Ef s ∧
        (N : ℂ) ^ (s / 2) * Rg s = -b 0 / s + a 0 / (s - k) + Eg s ∧
        Rf (k - s) = (N : ℂ) ^ (s - k / 2) * Rg s)

end ModularFormsKB.Shimura2007
