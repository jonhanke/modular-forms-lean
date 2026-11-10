import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Basic
import ModularFormsKB.Citation
/-!
# Milne, Section 11: twisted $L$-series

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf p. 111.

**D117**: for $L(E,s) = \sum c_n n^{-s}$ and a primitive Dirichlet character $\chi$ modulo $m$, Milne sets
$L_\chi(E,s) = \sum c_n\chi(n)n^{-s}$ and $\Lambda_\chi(E,s) = (m/2\pi)^s\Gamma(s)L_\chi(E,s)$.

Neither Mathlib nor Tau Ceti has the $L$-series of an elliptic curve over $\mathbb Q$ (its Euler factors at the bad
primes need the conductor), so the definitions take the coefficient sequence $(c_n)$ as input; applied to the
coefficients of $L(E,s)$ they are Milne's. Primitivity of $\chi$ is a hypothesis of the theorems in which the twist
is used (Weil's converse theorem), not of the definition; Mathlib's predicate is `DirichletCharacter.IsPrimitive`.
-/

namespace ModularFormsKB.Milne

/-- **D117** (Milne): the twist $L_\chi(s) = \sum_{n \ge 1} c_n\chi(n)n^{-s}$ of the Dirichlet series
$\sum c_n n^{-s}$ by a Dirichlet character $\chi$ modulo $m$ (Mathlib's `LSeries`, which ignores $n = 0$). -/
@[kb "milne2017mf" "Section 11, twisted L-series (pdf p. 111)"]
noncomputable def twistedLSeries (c : ℕ → ℂ) {m : ℕ} (χ : DirichletCharacter ℂ m) (s : ℂ) : ℂ :=
  LSeries (fun n => c n * χ n) s

/-- **D117** (Milne): the completed twist $\Lambda_\chi(s) = (m/2\pi)^s\,\Gamma(s)\,L_\chi(s)$. -/
@[kb "milne2017mf" "Section 11, twisted L-series (pdf p. 111)"]
noncomputable def completedTwistedLSeries (c : ℕ → ℂ) {m : ℕ} (χ : DirichletCharacter ℂ m) (s : ℂ) : ℂ :=
  ((m : ℂ) / (2 * Real.pi)) ^ s * Complex.Gamma s * twistedLSeries c χ s

/-- The twist by the trivial character modulo $1$ is the original series. -/
theorem twistedLSeries_one (c : ℕ → ℂ) (s : ℂ) :
    twistedLSeries c (1 : DirichletCharacter ℂ 1) s = LSeries c s := by
  unfold twistedLSeries
  congr 1
  funext n
  rw [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one]

end ModularFormsKB.Milne
