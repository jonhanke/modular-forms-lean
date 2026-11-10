import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import ModularFormsKB.Citation
/-!
# Shimura 2007, §16.5–16.6: the Rankin–Cohen bracket

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), §16.5–16.6,
pp. 124–125 (pdf pp. 130–131).

For functions $f, g$ on the upper half plane $\mathfrak H$, with $f^{(\nu)} = (\partial/\partial z)^\nu f$
as in Shimura's (16.1) (no factor $2\pi i$), Cohen's operator (16.11) is
$$F^{k,m}_p(f,g) = \sum_{\nu=0}^{p}(-1)^\nu\binom p\nu
  \frac{\Gamma(k+p)\Gamma(m+p)}{\Gamma(k+p-\nu)\Gamma(m+\nu)}\,f^{(p-\nu)}g^{(\nu)},$$
where, as Shimura says after (16.1), the quotients of Gamma values mean the products
$\Gamma(k+p)/\Gamma(k+p-\nu) = \prod_{\mu=p-\nu}^{p-1}(k+\mu)$ and
$\Gamma(m+p)/\Gamma(m+\nu) = \prod_{\mu=\nu}^{p-1}(m+\mu)$ (`cohenBracket`).

Cohen's covariance (16.12) is stated as `CohenCovarianceStatement`, **not proved**; Shimura
deduces it from Theorem 16.6 (the bracket written with the non-holomorphic operators
$\delta_k^p$ of (8.5)) and (8.7). The operators $\delta_k^p$ are not formalized, so (16.13) is not
stated. Shimura allows complex weights with a chosen branch of $j_\alpha^k$; we take integer
weights and Mathlib's slash action `f ∣[k] α` of $\mathrm{GL}_2(\mathbb R)$, restricted to
$\det\alpha = 1$ (Shimura's $\alpha \in \mathrm{SL}_2(\mathbb R)$). The case $p = 0$ is proved
(`cohenBracket_zero`, `cohenCovariance_zero`).
-/

open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

namespace ModularFormsKB.Shimura2007

/-- Shimura's $f^{(\nu)} = (\partial/\partial z)^\nu f$ of (16.1), for $f : \mathfrak H \to \mathbb C$
(computed on $\mathbb C$ through `UpperHalfPlane.ofComplex`). -/
noncomputable def halfPlaneDeriv (ν : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z ↦ iteratedDeriv ν (f ∘ ofComplex) z

/-- Shimura's coefficient $(-1)^\nu\binom p\nu\,\Gamma(k+p)\Gamma(m+p)/(\Gamma(k+p-\nu)\Gamma(m+\nu))$
of (16.11), with the Gamma quotients read as finite products. -/
def cohenCoeff (p ν : ℕ) (k m : ℂ) : ℂ :=
  (-1) ^ ν * (p.choose ν : ℂ) * (∏ μ ∈ Finset.Ico (p - ν) p, (k + μ)) *
    ∏ μ ∈ Finset.Ico ν p, (m + μ)

/-- **Cohen's operator** $F^{k,m}_p(f,g)$, Shimura (16.11). -/
@[kb "shimura2007" "§16.5, (16.11), p. 124"]
noncomputable def cohenBracket (p : ℕ) (k m : ℂ) (f g : ℍ → ℂ) : ℍ → ℂ :=
  fun z ↦ ∑ ν ∈ Finset.range (p + 1),
    cohenCoeff p ν k m * halfPlaneDeriv (p - ν) f z * halfPlaneDeriv ν g z

/-- **Cohen's covariance** (16.12), **stated, not proved**: for holomorphic $f, g$ on
$\mathfrak H$, integers $k, m$, $p \ge 0$ and $\alpha \in \mathrm{SL}_2(\mathbb R)$,
$$F^{k,m}_p(f\|_k\alpha,\ g\|_m\alpha) = F^{k,m}_p(f,g)\|_{k+m+2p}\,\alpha.$$
Shimura derives it from Theorem 16.6 and (8.7). -/
@[kb "shimura2007" "§16.5, (16.12), p. 125"]
def CohenCovarianceStatement : Prop :=
  ∀ (p : ℕ) (k m : ℤ) (f g : ℍ → ℂ), MDiff f → MDiff g →
    ∀ α : GL (Fin 2) ℝ, α.val.det = 1 →
      cohenBracket p k m (f ∣[k] α) (g ∣[m] α) =
        cohenBracket p k m f g ∣[k + m + 2 * (p : ℤ)] α

/-- For $p = 0$ the bracket is the product: $F^{k,m}_0(f,g) = fg$. -/
theorem cohenBracket_zero (k m : ℂ) (f g : ℍ → ℂ) : cohenBracket 0 k m f g = f * g := by
  funext z
  simp [cohenBracket, cohenCoeff, halfPlaneDeriv, ofComplex_apply]

/-- (16.12) for $p = 0$: $(f\|_k\alpha)(g\|_m\alpha) = (fg)\|_{k+m}\alpha$ when $\det\alpha = 1$. -/
theorem cohenCovariance_zero (k m : ℤ) (f g : ℍ → ℂ) (α : GL (Fin 2) ℝ)
    (hα : α.val.det = 1) :
    cohenBracket 0 k m (f ∣[k] α) (g ∣[m] α) = cohenBracket 0 k m f g ∣[k + m + 2 * (0 : ℕ)] α := by
  rw [cohenBracket_zero, cohenBracket_zero, Nat.cast_zero, mul_zero, add_zero,
    ModularForm.mul_slash]
  have h : (α.det : ℝ) = 1 := by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hα
  rw [h, abs_one, one_smul]

end ModularFormsKB.Shimura2007
