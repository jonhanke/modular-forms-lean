import ModularFormsKB.Shimura2007.Ch2.EulerPolynomials
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Shimura 2007, §4.8–4.9: $L(k,\chi)$ through roots of unity (Theorem 4.9)

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), §4.8–4.9,
pp. 30–31 (pdf pp. 36–37).

Shimura's §4.8 allows $\chi$ to be any Dirichlet character modulo $N > 1$, primitive or not and
possibly trivial; $L(s,\chi)$ is Mathlib's `DirichletCharacter.LFunction χ s`. With
$\zeta = \mathbf e(1/N)$ and $m = [(N-1)/2]$, Theorem 4.9 expresses
$N^k(k-1)!(2\pi i)^{-k}L(k,\chi)$ through the values $E_{-\zeta^a,k-1}(0)$ of the generalized Euler
polynomials (`eulerPoly`).

**Erratum (N = 2).** For $N = 2$, $\chi$ trivial and $k$ even, the sum over $1 \le a \le m = 0$ is
empty while $L(k,\chi) = (1 - 2^{-k})\zeta(k) \ne 0$: Shimura's proof uses $\chi(m+1) = 0$ for
even $N$, which fails for $N = 2$. The statements below assume $N > 2$; the printed version
(`RootOfUnityValueBookStatement`, $N > 1$) is refuted by `not_rootOfUnityValueBookStatement`.

Both parts are **stated, not proved**: Shimura's proof goes through Theorem 3.5 (values of the
series $M^{\nu}_{a,N}$ at $s = 0$), or through Theorem 4.2 (`EulerFourierStatement`) at
$t = 0$.
-/

open Complex DirichletCharacter
open scoped Real

namespace ModularFormsKB.Shimura2007

/-- **Theorem 4.9**, (4.16a), **stated, not proved**: for a Dirichlet character $\chi$ modulo
$N > 2$ (primitive or not, possibly trivial) and an integer $k > 1$ with $\chi(-1) = (-1)^k$,
with $\zeta = \mathbf e(1/N)$ and $m = [(N-1)/2]$,
$$N^k(k-1)!\,(2\pi i)^{-k}L(k,\chi) = \sum_{a=1}^{m}\chi(a)\,
  \frac{\zeta^aE_{-\zeta^a,k-1}(0)}{\zeta^a - 1}.$$
Shimura states $1 < N$; the case $N = 2$ is false (see the module docstring). The second
expression of (4.16a), through the polynomials $P_k$ of (4.6), is not stated. -/
@[kb "shimura2007" "Theorem 4.9, (4.16a), p. 30"]
def RootOfUnityValueStatement : Prop :=
  ∀ (N : ℕ) [NeZero N], 2 < N → ∀ (χ : DirichletCharacter ℂ N) (k : ℕ), 2 ≤ k →
    χ (-1) = (-1) ^ k →
      (N : ℂ) ^ k * ((k - 1).factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * LFunction χ k =
        ∑ a ∈ Finset.Icc 1 ((N - 1) / 2),
          χ a * (e (1 / N) ^ a * (eulerPoly (-e (1 / N) ^ a) (k - 1)).eval 0 /
            (e (1 / N) ^ a - 1))

/-- **Theorem 4.9**, (4.16b), **stated, not proved**: for an odd Dirichlet character $\chi$
modulo $N > 1$, with $\zeta = \mathbf e(1/N)$ and $m = [(N-1)/2]$,
$$L(1,\chi) = \frac{\pi i}{N}\sum_{a=1}^{m}\chi(a)\,\frac{\zeta^a + 1}{\zeta^a - 1}.$$
(No odd character exists modulo $2$, so $N = 2$ is harmless here.) -/
@[kb "shimura2007" "Theorem 4.9, (4.16b), p. 30"]
def RootOfUnityValueOneStatement : Prop :=
  ∀ (N : ℕ) [NeZero N], 1 < N → ∀ (χ : DirichletCharacter ℂ N), χ (-1) = -1 →
    LFunction χ 1 = π * I / N * ∑ a ∈ Finset.Icc 1 ((N - 1) / 2),
      χ a * ((e (1 / N) ^ a + 1) / (e (1 / N) ^ a - 1))

/-- (4.16a) **as printed**, with Shimura's hypothesis $1 < N$; it is false
(`not_rootOfUnityValueBookStatement`). -/
def RootOfUnityValueBookStatement : Prop :=
  ∀ (N : ℕ) [NeZero N], 1 < N → ∀ (χ : DirichletCharacter ℂ N) (k : ℕ), 2 ≤ k →
    χ (-1) = (-1) ^ k →
      (N : ℂ) ^ k * ((k - 1).factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * LFunction χ k =
        ∑ a ∈ Finset.Icc 1 ((N - 1) / 2),
          χ a * (e (1 / N) ^ a * (eulerPoly (-e (1 / N) ^ a) (k - 1)).eval 0 /
            (e (1 / N) ^ a - 1))

/-- **Erratum to Theorem 4.9**: (4.16a) fails for $N = 2$, $\chi$ trivial, $k = 2$: the right
side is an empty sum, while $L(2,\chi) \ne 0$. -/
theorem not_rootOfUnityValueBookStatement : ¬ RootOfUnityValueBookStatement := by
  intro h
  have h2 := h 2 (by norm_num) (1 : DirichletCharacter ℂ 2) 2 le_rfl (by simp)
  have hsum : Finset.Icc 1 ((2 - 1) / 2) = ∅ := by decide
  rw [hsum, Finset.sum_empty] at h2
  have hL : LFunction (1 : DirichletCharacter ℂ 2) ((2 : ℕ) : ℂ) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re _ (Or.inr (by norm_num)) (by norm_num)
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine hL ?_
  have hne : ((2 : ℕ) : ℂ) ^ 2 * (((2 - 1).factorial : ℕ) : ℂ) * ((2 * π * I) ^ 2)⁻¹ ≠ 0 := by
    simp [hpi, I_ne_zero]
  exact (mul_eq_zero.mp h2).resolve_left hne

end ModularFormsKB.Shimura2007
