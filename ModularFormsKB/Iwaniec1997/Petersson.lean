import ModularFormsKB.Iwaniec1997.Kloosterman
import ModularFormsKB.Milne.Ch4.Petersson
import ModularFormsKB.Milne.Ch4.Poincare
import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# Iwaniec, Chapter 3: the Petersson formula for $\Gamma_0(q)$ (statements)

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Section 3.3 and Section 4.2. Page numbers are
printed pages.

The book proves Corollary 3.4 and Theorem 3.6 for any pair of singular cusps $\mathfrak a, \mathfrak b$ of a Fuchsian
group with a multiplier system. General cusps, scaling matrices and multiplier systems are not available in Mathlib
or here, so we state the case that the book itself specializes in Section 4.2: the Hecke congruence group
$\Gamma = \Gamma_0(q)$, the trivial multiplier system, $\mathfrak a = \mathfrak b = \infty$ with $\sigma_\infty = 1$.
By (4.5) the moduli are $c \equiv 0 \pmod q$, $c > 0$, and $S_{\infty\infty}(m,n;c) = S(m,n;c)$ is the classical sum
(`kloosterman`).

The weight is written $k = 2\kappa$ (for the trivial multiplier on $\Gamma_0(q) \ni -1$ the weight is even) and
$k > 2$ as in the book. The Petersson inner product (3.21) $\langle f, g\rangle = \int_{\Gamma\backslash\mathbb H}
y^k f\bar g\,d\mu$ is `ModularFormsKB.Milne.milnePetersson` (linear in the first variable, like the book's). The Fourier
coefficient $\hat f(n)$ at $\infty$ is the $n$-th coefficient of Mathlib's `qExpansion 1 f`
(the cusp $\infty$ of $\Gamma_0(q)$ has width $1$). The Bessel function is Mathlib's `Complex.besselJ`, which is the
book's (3.12).

Both results are **stated, not proved** (`PeterssonFormulaGamma0`, `PoincareInnerProductGamma0`). What is proved in
this repository towards them is Theorem 3.3 (`ModularFormsKB.Miyake.petersson_poincareSeries`) and Corollary 3.5
(`ModularFormsKB.Miyake.cuspForm_mem_span_poincareSeries`); the missing piece is the Fourier expansion (3.18), (3.19)
of the Poincaré series, which needs the Bessel integral (3.11).
-/

open Complex CongruenceSubgroup ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups ComplexConjugate Real

noncomputable section

namespace ModularFormsKB.Iwaniec1997

/-- The Kloosterman-Bessel series of (3.23), (3.26) for $\Gamma_0(q)$ at the cusp $\infty$:
the $c$-th term $c^{-1} S(m,n;c) J_{k-1}(4\pi\sqrt{mn}/c)$ for $c > 0$, $c \equiv 0 \pmod q$, and $0$ otherwise. -/
def kloostermanBesselTerm (q k m n c : ℕ) : ℂ :=
  if 0 < c ∧ q ∣ c then
    (c : ℂ)⁻¹ * kloosterman m n c *
      besselJ ((k : ℂ) - 1) ((4 * π * Real.sqrt (m * n) / c : ℝ) : ℂ)
  else 0

/-- The normalizing factor $\Gamma(k-1)/(4\pi\sqrt{mn})^{k-1}$ of (3.23), (3.26). -/
def peterssonFactor (k m n : ℕ) : ℂ :=
  (Real.Gamma (k - 1) / (4 * π * Real.sqrt (m * n)) ^ (k - 1 : ℕ) : ℝ)

/-- **Theorem 3.6 (the Petersson formula)** for $\Gamma_0(q)$, the trivial multiplier and $\mathfrak a = \mathfrak b =
\infty$ (not proved here): let $k = 2\kappa > 2$ and let $\mathcal F$ be an orthonormal basis of $S_k(\Gamma_0(q))$.
Then for all positive integers $m, n$ the series of Kloosterman sums converges absolutely and
$$\frac{\Gamma(k-1)}{(4\pi\sqrt{mn})^{k-1}} \sum_{f\in\mathcal F} \overline{\hat f(m)}\,\hat f(n)
= \delta_{mn} + 2\pi i^{-k} \sum_{c > 0,\ c \equiv 0\,(q)} c^{-1} S(m,n;c)\, J_{k-1}\Big(\frac{4\pi\sqrt{mn}}{c}\Big).$$ -/
@[kb "iwaniec1997" "Section 3.3, Theorem 3.6, (3.26), p. 54; specialized by (4.5), p. 58"]
def PeterssonFormulaGamma0 (q : ℕ) [NeZero q] (κ : ℕ) : Prop :=
  2 ≤ κ →
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → CuspForm ((Gamma0 q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) (2 * κ : ℕ)),
    (∀ i j, Milne.milnePetersson (Gamma0 q) κ (F i) (F j) = if i = j then 1 else 0) →
    Submodule.span ℂ (Set.range F) = ⊤ →
    ∀ m n : ℕ, 0 < m → 0 < n →
      Summable (fun c ↦ ‖kloostermanBesselTerm q (2 * κ) m n c‖) ∧
      peterssonFactor (2 * κ) m n *
          ∑ i, conj ((qExpansion 1 (F i)).coeff m) * (qExpansion 1 (F i)).coeff n =
        (if m = n then 1 else 0) +
          2 * π * I ^ (-(2 * κ : ℤ)) * ∑' c : ℕ, kloostermanBesselTerm q (2 * κ) m n c

/-- **Corollary 3.4** for $\Gamma_0(q)$, the trivial multiplier and $\mathfrak a = \mathfrak b = \infty$ (not proved
here): for $k = 2\kappa > 2$ and positive integers $m, n$, the Poincaré series $P_m$ (3.17)
(`ModularFormsKB.Milne.poincareSeries`) satisfy
$$\langle P_m, P_n\rangle = \frac{\Gamma(k-1)}{(4\pi\sqrt{mn})^{k-1}}\Big\{\delta_{mn} + 2\pi i^{-k}
\sum_{c > 0,\ c \equiv 0\,(q)} c^{-1} S(m,n;c)\, J_{k-1}\Big(\frac{4\pi\sqrt{mn}}{c}\Big)\Big\}.$$ -/
@[kb "iwaniec1997" "Section 3.3, Corollary 3.4, (3.23), p. 53; specialized by (4.5), p. 58"]
def PoincareInnerProductGamma0 (q : ℕ) [NeZero q] (κ : ℕ) : Prop :=
  2 ≤ κ → ∀ m n : ℕ, 0 < m → 0 < n →
    Milne.milnePetersson (Gamma0 q) κ (Milne.poincareSeries (Gamma0 q) κ m)
        (Milne.poincareSeries (Gamma0 q) κ n) =
      peterssonFactor (2 * κ) m n *
        ((if m = n then 1 else 0) +
          2 * π * I ^ (-(2 * κ : ℤ)) * ∑' c : ℕ, kloostermanBesselTerm q (2 * κ) m n c)

end ModularFormsKB.Iwaniec1997
