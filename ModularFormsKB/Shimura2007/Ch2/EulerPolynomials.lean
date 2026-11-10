import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ModularFormsKB.Citation
/-!
# Shimura 2007, §4.1: generalized Euler polynomials $E_{c,n}(t)$

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), §4.1–4.2,
pp. 25–27 (pdf pp. 31–33).

For $c \ne -1$ Shimura defines the **generalized Euler polynomials** $E_{c,n}(t)$ by the
generating function (4.2)
$$\frac{(1+c)e^{tz}}{e^z + c} = \sum_{n\ge0}\frac{E_{c,n}(t)}{n!}z^n,$$
and the generalized Euler numbers by (4.1), equivalently (4.3a) $E_{c,n} = 2^nE_{c,n}(1/2)$.
The classical Euler polynomials are $E_{1,n}(t)$.

We define $E_{c,n}$ as a polynomial over a field $K$ of characteristic zero by the recursion
(4.3b), $E_{c,n}(t) = t^n + b\sum_{k<n}\binom nk E_{c,k}(t)$ with $b = -(1+c)^{-1}$
(`eulerPoly`). The generating function (4.2) in $K[t][[z]]$ (`eulerPoly_generating_function`),
(4.3c), (4.3d) and (4.3h) are proved in `ModularFormsKB.Shimura2007.Ch2.EulerPolynomialProps`.

Shimura's Theorem 4.2 (the Fourier expansion of $E_{c,n}(t)$, proved by a contour integral) is
stated as `EulerFourierStatement`, **not proved**.
-/

open Polynomial

namespace ModularFormsKB.Shimura2007

variable {K : Type*} [Field K] [CharZero K]

/-- Shimura's $b = -(1+c)^{-1}$ (§4.1). -/
def eulerB (c : K) : K := -(1 + c)⁻¹

/-- The generalized Euler polynomial $E_{c,n}(t) \in K[t]$ of Shimura (4.2), defined by the
recursion (4.3b): $E_{c,n}(t) = t^n + b\sum_{k=0}^{n-1}\binom nk E_{c,k}(t)$,
$b = -(1+c)^{-1}$. For $c = -1$ (excluded by Shimura) the formula still defines a polynomial
($b = 0$, $E_{-1,n} = t^n$), which carries no meaning. -/
@[kb "shimura2007" "§4.1, (4.2), (4.3b), p. 25"]
noncomputable def eulerPoly (c : K) : ℕ → K[X]
  | n => X ^ n + C (eulerB c) *
      ∑ k : Fin n, (n.choose k : K[X]) * eulerPoly c k

/-- The defining recursion (4.3b). -/
@[kb "shimura2007" "§4.1, (4.3b), p. 25"]
theorem eulerPoly_eq (c : K) (n : ℕ) :
    eulerPoly c n = X ^ n + C (eulerB c) *
      ∑ k ∈ Finset.range n, (n.choose k : K[X]) * eulerPoly c k := by
  rw [eulerPoly, Finset.sum_range (fun k ↦ (n.choose k : K[X]) * eulerPoly c k)]

/-- Shimura's $\mathbf e(x) = e^{2\pi i x}$. -/
noncomputable abbrev e (x : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- The term $(h+\alpha)^{-n-1}\mathbf e((h+\alpha)t)$ of Shimura's series $F_{c,n}(t)$ (4.4),
$c = -\mathbf e(\alpha)$. -/
noncomputable def eulerFourierTerm (α : ℝ) (n : ℕ) (t : ℝ) (h : ℤ) : ℂ :=
  (((h : ℂ) + α) ^ (n + 1))⁻¹ * e (((h : ℂ) + α) * t)

/-- **Theorem 4.2**, (4.5) and (4.5a), **stated, not proved** (Shimura proves it by a contour
integral over squares): let $\alpha \in \mathbb R \setminus \mathbb Z$ and $c = -\mathbf e(\alpha)$.
1. For $n \ge 1$ and $0 \le t \le 1$ the series
   $F_{c,n}(t) = \sum_{h\in\mathbb Z}(h+\alpha)^{-n-1}\mathbf e((h+\alpha)t)$ converges (absolutely)
   and $E_{c,n}(t) = (1+c^{-1})\,n!\,(2\pi i)^{-n-1}F_{c,n}(t)$.
2. For $n = 0$ and $0 < t < 1$ the symmetric partial sums $\sum_{|h|\le m}$ of $F_{c,0}(t)$
   converge to $F_{c,0}(t)$ with $E_{c,0}(t) = 1 = (1+c^{-1})(2\pi i)^{-1}F_{c,0}(t)$.
3. (4.5a) At $t = 0$: $(1+c^{-1})(2\pi i)^{-1}F_{c,0}(0) = (1-c^{-1})/2$, with $F_{c,0}(0)$ the
   limit of the symmetric partial sums. -/
@[kb "shimura2007" "Theorem 4.2, (4.5), (4.5a), p. 26"]
def EulerFourierStatement : Prop :=
  ∀ α : ℝ, (∀ m : ℤ, α ≠ m) →
    let c : ℂ := -e α
    (∀ n : ℕ, 1 ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Summable (eulerFourierTerm α n t) ∧
      (eulerPoly c n).eval (t : ℂ) = (1 + c⁻¹) * n.factorial *
        ((2 * Real.pi * Complex.I) ^ (n + 1))⁻¹ * ∑' h, eulerFourierTerm α n t h) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) 1,
      Filter.Tendsto (fun m : ℕ ↦ ∑ h ∈ Finset.Icc (-(m : ℤ)) m, eulerFourierTerm α 0 t h)
        Filter.atTop (nhds ((2 * Real.pi * Complex.I) / (1 + c⁻¹)))) ∧
    Filter.Tendsto (fun m : ℕ ↦ ∑ h ∈ Finset.Icc (-(m : ℤ)) m, eulerFourierTerm α 0 0 h)
      Filter.atTop (nhds ((2 * Real.pi * Complex.I) * (1 - c⁻¹) / (2 * (1 + c⁻¹))))

end ModularFormsKB.Shimura2007
