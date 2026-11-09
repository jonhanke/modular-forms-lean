import ModularFormsKB.Milne.Ch11.WeilReduction

/-!
# Milne, Section 11: the $L$-polynomial of a function field over a finite field

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf p. 110;
H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed. (`stichtenoth2009`), Section 5.1.

For a function field $F$ over a finite field $k$ with $q$ elements let $A_n$ be the number of effective divisors of
degree $n$ (`effectiveDivisorCount`) and $Z(t) = \sum_n A_n t^n$ the zeta function. This file reduces the named
statement `WeilZetaRationality` of `ModularFormsKB.Milne.Ch11.WeilReduction` to two facts:

- `ZetaLPolynomial` (named statement; Stichtenoth, Theorem 5.1.15 (a), (b) with F. K. Schmidt's theorem 5.1.11):
  $(1 - t)(1 - qt)Z(t) = L(t)$ for an integer polynomial $L$ of degree $2g$ with $L(0) = 1$ satisfying the
  functional equation $L(t) = q^g t^{2g} L(1/qt)$;
- `ZetaNewtonIdentity` (Stichtenoth, Proposition 5.1.17 in the form of the logarithmic derivative of the Euler
  product): $n A_n = \sum_{k=1}^{n} N_k A_{n-k}$, with $N_k$ the point count `curvePointCount`.

Granting both, `weilZetaRationality_of_zetaLPolynomial` produces the reciprocal roots $\alpha_1, \dots, \alpha_{2g}$
of $L$: they are nonzero algebraic integers, $\alpha \mapsto q/\alpha$ permutes them, and comparing
$tZ'/Z = \sum_k (1 + q^k - \sum_i \alpha_i^k)t^k$ with the Newton identity gives $N_n = 1 + q^n - \sum_i\alpha_i^n$.
-/

open Finset Polynomial

namespace ModularFormsKB.Milne

universe u v

variable (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]

/-- The number $A_n$ of effective divisors of degree $n$ of $F/k$ (finite when $k$ is finite,
`TauCeti.Divisor.finite_setOf_isEffective_degree_le`). -/
noncomputable def effectiveDivisorCount (n : ℕ) : ℕ :=
  Nat.card {D : TauCeti.Divisor k F // 0 ≤ D ∧ TauCeti.Divisor.degree D = n}

/-- **The $L$-polynomial** (Stichtenoth, Theorem 5.1.15 (a), (b); F. K. Schmidt 1931), as a named statement: for a
function field $F$ over a finite field $k$ with $q$ elements, $k$ algebraically closed in $F$, of genus $g$, there
is $L \in \mathbb Z[t]$ of degree $2g$ with $L(0) = 1$, $q^i\,c_{2g-i} = q^g\,c_i$ for $i \le 2g$ (the functional
equation $L(t) = q^g t^{2g} L(1/qt)$, $c_i$ the coefficients of $L$), and
$(1 - t)(1 - qt)\sum_n A_n t^n = L(t)$. -/
@[kb "stichtenoth2009" "Theorem 5.1.15 (a), (b)"]
structure ZetaLPolynomial : Prop where
  lpoly : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    TauCeti.IsFunctionField k F → IsIntegrallyClosedIn k F →
    ∃ L : ℤ[X], L.natDegree = 2 * TauCeti.genus k F ∧ L.coeff 0 = 1 ∧
      (∀ i, i ≤ 2 * TauCeti.genus k F →
        (Nat.card k : ℤ) ^ i * L.coeff (2 * TauCeti.genus k F - i) =
          (Nat.card k : ℤ) ^ TauCeti.genus k F * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℤ) * PowerSeries.X) *
          PowerSeries.mk (fun n => (effectiveDivisorCount k F n : ℤ)) = (L : PowerSeries ℤ)

/-- **The Newton identity for the zeta function**: $n A_n = \sum_{k=1}^n N_k A_{n-k}$, the coefficientwise form of
$tZ'(t) = Z(t)\sum_{k\ge1} N_k t^k$, i.e. of the logarithmic derivative of the Euler product
$Z(t) = \prod_P (1 - t^{\deg P})^{-1}$ (Stichtenoth, Proposition 5.1.17 and Corollary 5.1.20 [unverified numbering]).
Combinatorially: $n A_n = \sum_{\deg D = n} \sum_P v_P(D)\deg P$, and $D \mapsto D - jP$ matches the effective
divisors of degree $n$ with $v_P(D) \ge j$ with those of degree $n - j\deg P$. -/
@[kb "stichtenoth2009" "Section 5.1, logarithmic derivative of the Euler product"]
structure ZetaNewtonIdentity : Prop where
  newton : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    TauCeti.IsFunctionField k F → ∀ n : ℕ,
      n * effectiveDivisorCount k F n =
        ∑ j ∈ range n, curvePointCount k F (j + 1) * effectiveDivisorCount k F (n - 1 - j)

end ModularFormsKB.Milne
