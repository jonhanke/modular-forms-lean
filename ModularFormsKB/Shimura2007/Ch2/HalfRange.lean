import ModularFormsKB.Shimura2007.Ch2.CriticalValues
import ModularFormsKB.Shimura2007.Ch2.EulerPolynomials

/-!
# Shimura 2007, §4.11 continued: half-range formulas (Lemma 4.13 to Corollary 4.16)

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), pp. 33–38
(pdf pp. 39–44).

Throughout, $\chi$ is a Dirichlet character modulo $d$ with values in $\mathbb C$, Shimura's
$\overline\chi$ is `χ⁻¹`, $q = [(d-1)/2]$ is `(d - 1) / 2` (natural division), and
$E_{1,n}(t)$ is `(eulerPoly (1 : ℂ) n).eval t` (the classical Euler polynomial).

**Note on (4.32), (4.35).** The scanned text loses complex-conjugation bars. The factor
$2^k - \chi(2)$ in (4.32) and the prefactor $\chi(2)$ in (4.35) are **without** bar: Shimura's
proof starts from $2G(\overline\chi)(1-\chi(2)2^{-k})L(k,\chi) = G(\overline\chi)\sum_{m\ \rm odd}
\chi(m)m^{-k}$; the statements below follow that derivation.
-/

open Complex DirichletCharacter
open scoped Real

namespace ModularFormsKB.Shimura2007

/-- **Theorem 4.14 (i)**, (4.32), **stated, not proved**: for a nontrivial primitive $\chi$
modulo $d$ and $k \ge 1$ with $\chi(-1) = (-1)^k$,
$$(k-1)!\,(2\pi i)^{-k}G(\overline\chi)L(k,\chi) = \frac{1}{2(2^k-\chi(2))}
  \sum_{a=1}^{q}\overline\chi(a)\,E_{1,k-1}(2a/d).$$
Shimura's proof uses Theorem 4.2 (`EulerFourierStatement`) at $\alpha = 1/2$. -/
@[kb "shimura2007" "Theorem 4.14 (i), (4.32), p. 35"]
def HalfRangeEulerStatement : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive → χ ≠ 1 →
    ∀ k : ℕ, 1 ≤ k → χ (-1) = (-1) ^ k →
      ((k - 1).factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar *
          LFunction χ k =
        (2 * (2 ^ k - χ 2))⁻¹ * ∑ a ∈ Finset.Icc 1 ((d - 1) / 2),
          χ⁻¹ a * (eulerPoly (1 : ℂ) (k - 1)).eval (2 * (a : ℂ) / d)

/-- **Theorem 4.14 (ii)**, (4.34), **stated, not proved**: if moreover $d = 4d_0$ with
$d_0 > 1$, then
$(k-1)!\,(\pi i)^{-k}G(\overline\chi)L(k,\chi) = \sum_{a=1}^{d_0-1}\overline\chi(a)E_{1,k-1}(2a/d)$. -/
@[kb "shimura2007" "Theorem 4.14 (ii), (4.34), p. 35"]
def HalfRangeEulerFourStatement : Prop :=
  ∀ (d₀ : ℕ), 1 < d₀ → ∀ [NeZero (4 * d₀)] (χ : DirichletCharacter ℂ (4 * d₀)),
    χ.IsPrimitive → χ ≠ 1 →
    ∀ k : ℕ, 1 ≤ k → χ (-1) = (-1) ^ k →
      ((k - 1).factorial : ℂ) * ((π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar *
          LFunction χ k =
        ∑ a ∈ Finset.Ico 1 d₀,
          χ⁻¹ a * (eulerPoly (1 : ℂ) (k - 1)).eval (2 * (a : ℂ) / (4 * d₀ : ℕ))

/-- **Theorem 4.14 (iii)**, (4.35), **stated, not proved**: if $d$ is odd,
$$(k-1)!\,(2\pi i)^{-k}G(\overline\chi)L(k,\chi) = \frac{\chi(2)}{2(2^k-\chi(2))}
  \sum_{b=1}^{q}(-1)^b\,\overline\chi(b)\,E_{1,k-1}(b/d).$$ -/
@[kb "shimura2007" "Theorem 4.14 (iii), (4.35), p. 35"]
def HalfRangeEulerOddStatement : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), Odd d → χ.IsPrimitive → χ ≠ 1 →
    ∀ k : ℕ, 1 ≤ k → χ (-1) = (-1) ^ k →
      ((k - 1).factorial : ℂ) * ((2 * π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar *
          LFunction χ k =
        χ 2 / (2 * (2 ^ k - χ 2)) * ∑ b ∈ Finset.Icc 1 ((d - 1) / 2),
          (-1) ^ b * χ⁻¹ b * (eulerPoly (1 : ℂ) (k - 1)).eval ((b : ℂ) / d)

/-- Shimura's $\Lambda(k,\chi)$ of (4.43): $4\{\overline\chi(2) - 2^{-k}\}(k-1)!(\pi i)^{-k}
G(\overline\chi)L(k,\chi)$ if $d$ is odd, $2(k-1)!(\pi i)^{-k}G(\overline\chi)L(k,\chi)$ if $d$ is
even. -/
@[kb "shimura2007" "Theorem 4.15 (ii), (4.43), p. 37"]
noncomputable def shimuraLambda {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (k : ℕ) : ℂ :=
  (if Even d then 2 else 4 * (χ⁻¹ 2 - (2 ^ k)⁻¹)) * ((k - 1).factorial : ℂ) *
    ((π * I) ^ k)⁻¹ * gaussSum χ⁻¹ ZMod.stdAddChar * LFunction χ k

/-- **Theorem 4.15 (ii)**, (4.44), **stated, not proved**: for a nontrivial primitive $\chi$
of conductor $d$ with $d$ odd or $d > 4$, $k \ge 1$ with $\chi(-1) = (-1)^k$,
$q = [(d-1)/2]$, $m = [(k-1)/2]$,
$$\Lambda(k,\chi) = -\frac12\sum_{\nu=1}^{m}\binom{k-1}{2\nu}\Lambda(k-2\nu,\chi) +
  \begin{cases} d^{1-k}\sum_{a=1}^{d-1}(-1)^a\overline\chi(a)a^{k-1} & d \notin 2\mathbb Z,\\
  2^{k-1}d^{1-k}\sum_{a=1}^{q}\overline\chi(a)a^{k-1} & d \in 2\mathbb Z.\end{cases}$$
Shimura derives it from (4.34), (4.35) (`HalfRangeEulerFourStatement`,
`HalfRangeEulerOddStatement`) and the recursion (4.3b) at $c = 1$. -/
@[kb "shimura2007" "Theorem 4.15 (ii), (4.44), p. 38"]
def RecurrenceLambdaStatement : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), (Odd d ∨ 4 < d) → χ.IsPrimitive →
    χ ≠ 1 → ∀ k : ℕ, 1 ≤ k → χ (-1) = (-1) ^ k →
      shimuraLambda χ k =
        -(1 / 2) * ∑ ν ∈ Finset.Icc 1 ((k - 1) / 2),
            ((k - 1).choose (2 * ν) : ℂ) * shimuraLambda χ (k - 2 * ν) +
          if Even d then
            2 ^ (k - 1) * ((d : ℂ) ^ (k - 1))⁻¹ *
              ∑ a ∈ Finset.Icc 1 ((d - 1) / 2), χ⁻¹ a * (a : ℂ) ^ (k - 1)
          else
            ((d : ℂ) ^ (k - 1))⁻¹ * ∑ a ∈ Finset.Ico 1 d, (-1) ^ a * χ⁻¹ a * (a : ℂ) ^ (k - 1)

end ModularFormsKB.Shimura2007
