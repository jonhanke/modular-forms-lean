# G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer, 2007): statement map

A first statement wave: each row is a central result of the book (pages: printed page numbers) that the library states in Lean, with its declarations and its status, computed from the Lean kernel: *proved* means proved with only the standard axioms and no unproved input; *proved in part* that a part, a special case or one instance is proved; *conditional* names the unproved inputs (named statements) still assumed; *stated, not proved* that the library states the result as a named structure (a `Prop`) without proof. Unlike a book map, a statement map does not list every item of the book: the results not yet stated are not shown. The statements in the third column are short descriptions, not quotations; read the book for the exact wording.

Rows: 12. proved: 3; proved in part: 6; stated, not proved: 3.

## Section 1

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Lemma 1.12 | 13 | For a primitive Dirichlet character $\chi$ of conductor $2g$ with $g > 0$, $\chi(1-g) = -1$ (and $g$ is even). | `Shimura2007.primitive_apply_one_sub_half`, `Shimura2007.even_of_isPrimitive_two_mul` | proved |

## Section 3

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Theorem 3.2 | 20 | Hecke's theorem: the Dirichlet series of $f$ and of its partner $f^\#$ continue meromorphically with simple poles at $0$ and $k$ and satisfy $R_f(k-s) = N^{s-k/2}R_{f^\#}(s)$. | `Shimura2007.HeckeFunctionalEquationStatement` | stated, not proved |

## Section 4

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (4.2), (4.3c), (4.3d), (4.3f), (4.3g), (4.3h) | 25 | Generating function, derivative, shift, reflection, value-at-zero and low-degree formulas for the generalized Euler polynomials $E_{c,n}(t)$. | `Shimura2007.eulerPoly_generating_function`, `Shimura2007.derivative_eulerPoly_succ`, `Shimura2007.eulerPoly_comp_add_one`, `Shimura2007.eulerPoly_comp_one_sub`, `Shimura2007.eulerPoly_eval_zero_inv`, `Shimura2007.eulerPoly_zero`, … (8 in all) | proved in part ((4.3g) proved for n >= 1 only (it fails at n = 0)) |
| Theorem 4.2 | 26 | For non-integral real $\alpha$, the generalized Euler polynomial $E_{c,n}(t)$ on $[0,1]$ equals a constant times the Fourier-type series $\sum_h (h+\alpha)^{-n-1}\mathbf e((h+\alpha)t)$. | `Shimura2007.EulerFourierStatement` | stated, not proved |
| Theorem 4.9 | 30 | For $\chi(-1) = (-1)^k$, $N^k(k-1)!(2\pi i)^{-k}L(k,\chi)$ is a finite sum of values of Euler polynomials at roots of unity; for odd $\chi$, $L(1,\chi)$ is a finite sum of cotangent-type terms. | `Shimura2007.RootOfUnityValueStatement`, `Shimura2007.RootOfUnityValueOneStatement`, `Shimura2007.not_rootOfUnityValueBookStatement` | stated, not proved ((4.16a) stated for N > 2; the book form with N > 1 is refuted in Lean (erratum); (4.16b) stated) |
| Theorem 4.12 | 32 | Euler's formula $2\,n!(2\pi i)^{-n}\zeta(n) = -B_n$ and its Dirichlet analogue relating $k!(2\pi i)^{-k}G(\bar\chi)L(k,\chi)$ to $L(1-k,\bar\chi)$ and Bernoulli sums. | `Shimura2007.two_mul_factorial_mul_riemannZeta`, `Shimura2007.nat_mul_riemannZeta_one_sub`, `Shimura2007.two_mul_factorial_gaussSum_mul_LFunction`, `Shimura2007.nat_mul_LFunction_one_sub`, `Shimura2007.theorem_4_12_ii`, `Shimura2007.theorem_4_12_ii_one`, … (7 in all) | proved in part (the case k = 1 of the right equality is conditional on LZeroValueStatement) |
| Lemma 4.13 | 33 | Half-range and alternating character sums of Bernoulli polynomials, Euler polynomials and powers of $a$ vanish or reduce to full-range sums for a nontrivial primitive character of suitable parity. | `Shimura2007.sum_bernoulli_eq_two_mul_halfSum`, `Shimura2007.sum_bernoulli_eq_zero_of_pred`, `Shimura2007.sum_alt_eulerPoly_pred`, `Shimura2007.sum_alt_eulerPoly_self`, `Shimura2007.sum_eulerPoly_four_pred`, `Shimura2007.sum_eulerPoly_four_self`, … (10 in all) | proved |
| Theorem 4.14 | 35 | For a primitive character, $k!(2\pi i)^{-k}G(\bar\chi)L(k,\chi)$ equals a half-range sum of Bernoulli polynomials, with Euler polynomial variants for moduli divisible by 4 and for odd moduli. | `Shimura2007.theorem_4_14_i`, `Shimura2007.HalfRangeEulerStatement`, `Shimura2007.HalfRangeEulerFourStatement`, `Shimura2007.HalfRangeEulerOddStatement` | proved in part ((4.33) proved; (4.32), (4.34), (4.35) stated; (iv) not stated) |
| Theorem 4.15 | 37 | A recursion expressing $A(k,\chi) = 2\,k!(2\pi i)^{-k}G(\bar\chi)L(k,\chi)$ through a character power sum and lower $A(k-2\nu,\chi)$, and a similar recurrence for $\Lambda(k,\chi)$. | `Shimura2007.theorem_4_15_i_even`, `Shimura2007.theorem_4_15_i`, `Shimura2007.RecurrenceLambdaStatement` | proved in part ((i) proved for even k, odd k conditional on LZeroValueStatement; (ii) stated) |
| Corollary 4.16 | 38 | For a nontrivial primitive even character $\chi$ modulo $d$, $\pi^{-2}G(\bar\chi)L(2,\chi) = d^{-2}\sum_{a=1}^{d-1}\bar\chi(a)a^2$. | `Shimura2007.corollary_4_16` | proved in part ((4.46) proved; (4.45) not formalized) |

## Section 6

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Lemma 6.2 | 45 | For $\varepsilon = \pm1$, $0 \le \varepsilon/s + j/d \le 1$ for every integer $j$ with $1-g \le j \le d-g$, strictly when $s \nmid d$. | `Shimura2007.lemma_6_2` | proved |

## Section 16

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Theorem 16.6 / (16.11), (16.12) | 125 | Cohen's covariance: the bracket $F^{k,m}_p$ of holomorphic $f, g$ satisfies $F^{k,m}_p(f\|_k\alpha, g\|_m\alpha) = F^{k,m}_p(f,g)\|_{k+m+2p}\alpha$ for $\alpha \in \mathrm{SL}_2(\mathbb R)$. | `Shimura2007.cohenBracket`, `Shimura2007.CohenCovarianceStatement`, `Shimura2007.cohenCovariance_zero` | proved in part ((16.12) stated, case p = 0 proved; (16.13) not stated) |
