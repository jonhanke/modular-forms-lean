# H. Iwaniec, *Topics in Classical Automorphic Forms* (American Mathematical Society, 1997): statement map

A first statement wave: each row is a central result of the book (pages: printed page numbers) that the library states in Lean, with its declarations and its status, computed from the Lean kernel: *proved* means proved with only the standard axioms and no unproved input; *proved in part* that a part, a special case or one instance is proved; *conditional* names the unproved inputs (named statements) still assumed; *stated, not proved* that the library states the result as a named structure (a `Prop`) without proof. Unlike a book map, a statement map does not list every item of the book: the results not yet stated are not shown. The statements in the third column are short descriptions, not quotations; read the book for the exact wording.

Rows: 28. proved: 6; proved in part: 2; proved, conditional: 2; stated, not proved: 18.

## Chapter 3

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Corollary 3.4 | 53 | For weight $k > 2$ on $\Gamma_0(q)$, the inner product of two Poincare series is a gamma factor times $\delta_{mn}$ plus a Kloosterman-Bessel series. | `Iwaniec1997.PoincareInnerProductGamma0` | stated, not proved (stated for Gamma0(q), cusp infinity) |
| Theorem 3.6 | 54 | Petersson's formula: for weight $k > 2$ on $\Gamma_0(q)$, a gamma-normalized sum over an orthonormal basis of cusp forms equals $\delta_{mn}$ plus a series of Kloosterman sums with Bessel functions. | `Iwaniec1997.PeterssonFormulaGamma0` | stated, not proved (stated for Gamma0(q), cusp infinity) |

## Chapter 4

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| (4.8), (4.9) | 59 | The Kloosterman sum is symmetric in its two arguments and invariant under multiplying one argument by a unit and dividing the other. | `Iwaniec1997.kloosterman_comm`, `Iwaniec1997.kloosterman_mul_left_eq_mul_right` | proved |
| (4.10) | 59 | Selberg's identity writes $S(m,n;c)$ as a sum over $d \mid (c,m,n)$ of $d\,S(mn d^{-2},1;c/d)$, so that $S(m,n;c) = S(mn,1;c)$ when $(c,m,n)=1$. | `Iwaniec1997.SelbergIdentity`, `Iwaniec1997.kloosterman_eq_kloosterman_mul_one_of_selberg` | proved in part ((4.10) stated; (4.11) proved from it) |
| (4.12) | 59 | Twisted multiplicativity of Kloosterman sums: for coprime moduli $q, r$ the sum modulo $qr$ factors into sums modulo $q$ and $r$ with adjusted arguments. | `Iwaniec1997.kloosterman_mul_of_coprime`, `Iwaniec1997.kloostermanMod_mul_of_coprime` | proved |
| Lemma 4.1 | 59 | Salie's evaluation: for $c = p^{2\alpha}$ and $(c,2n)=1$, $S(n,n;c) = c^{1/2}(e(2n/c) + e(-2n/c))$. | `Iwaniec1997.SalieLemma41` | stated, not proved |
| Lemma 4.2 | 60 | Salie's evaluation: for $c = p^{2\alpha+1}$ and $(c,2n)=1$, $S(n,n;c) = 2\left(\tfrac nc\right)c^{1/2}\,\mathrm{Re}\,\varepsilon_c e(2n/c)$. | `Iwaniec1997.SalieLemma42` | stated, not proved |
| Proposition 4.3 | 60 | For $c = p^\beta$ with $\beta \ge 2$ and $(c,2n)=1$, $S(n,n;c) = 2\left(\tfrac nc\right)c^{1/2}\,\mathrm{Re}\,\varepsilon_c e(2n/c)$. | `Iwaniec1997.SalieProposition43` | stated, not proved |
| Corollary 4.4 | 61 | For $c = p^\beta$ with $\beta \ge 2$ and $(c,2mn)=1$, the Kloosterman sum satisfies $|S(m,n;c)| \le 2c^{1/2}$. | `Iwaniec1997.KloostermanPrimePowerBound` | stated, not proved |
| (4.19) Weil's bound | 61 | Weil's bound: for a prime $p$ and integers $m,n$ not both divisible by $p$, $|S(m,n;p)| \le 2p^{1/2}$ (taken as a named input). | `Iwaniec1997.WeilKloostermanBound` | stated, not proved |
| Theorem 4.5 | 61 | For every $c \ge 1$ and integers $m,n$, $|S(m,n;c)| \le (m,n,c)^{1/2} c^{1/2}\tau(c)$. | `Iwaniec1997.KloostermanWeilBound`, `Iwaniec1997.kloosterman_bound_squarefree` | proved, conditional on `Iwaniec1997.WeilKloostermanBound` (general statement stated; proved for squarefree c from Weil's bound) |
| (4.22), (4.23) | 62 | The first two moments of Kloosterman sums over a prime modulus: $V_1(p) = 1$ and $V_2(p) = p^2 - p - 1$. | `Iwaniec1997.kloostermanMoment_one`, `Iwaniec1997.kloostermanMoment_two` | proved |
| Theorem 4.6 (Katz) | 64 | For a prime $p > 2$ and $k \ge 1$, the sum of Chebyshev values $U_k$ at normalized Kloosterman sums is at most $\tfrac12(k+1)p^{1/2}$ in absolute value. | `Iwaniec1997.KatzBound` | stated, not proved |
| (4.34) | 65 | Mean square estimate: $\frac1r\sum_{a \bmod r}|S(an,an;r)|^2 \le 4(n,r)\,r\,\tau(r)$. | `Iwaniec1997.KloostermanSquareMean` | stated, not proved |
| Lemma 4.7 | 65 | A double sum of $|S(n,n;qr)|/(qr)$ over $q \le Q$, $r \le R$ is at most $C\tau_3(n)(Q+R)(\log 4QR)^3$ for an absolute constant $C$. | `Iwaniec1997.KloostermanDoubleSumBound` | stated, not proved |
| Lemma 4.8 | 66 | For $(c,2n)=1$ the quadratic Gauss sum is $g(n,c) = \left(\tfrac nc\right)\varepsilon_c c^{1/2}$. | `Iwaniec1997.GaussSumEvaluation` | stated, not proved |
| Lemma 4.9 | 68 | For $(c,2n)=1$ the Salie sum is $T(m,n;c) = \left(\tfrac nc\right)g(c)\sum_{y^2 \equiv mn\,(c)} e(2y/c)$. | `Iwaniec1997.SalieLemma49` | stated, not proved |
| Corollary 4.10 | 68 | For $(c,2n)=1$ the Salie sum satisfies $|T(m,n;c)| \le c^{1/2}\tau(c)$. | `Iwaniec1997.SalieBound` | stated, not proved |
| Corollary 4.11 | 68 | Salie's formula: for $(c,2n)=1$, $T(n,n;c)$ equals $\left(\tfrac nc\right)g(c)$ times a sum over coprime factorizations $c = ab$ of exponentials in the inverses of $a$ and $b$. | `Iwaniec1997.SalieFormula` | stated, not proved |

## Chapter 5

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Corollary 5.2 | 71 | For a cusp form of weight $k$ there is a constant $C$ with $\sum_{n \le N}|a(n)| \le C N^{(k+1)/2}$ for all $N \ge 1$. | `Iwaniec1997.sum_norm_qExpansion_coeff_le` | proved |
| Theorem 5.3 | 71 | For a cusp form of weight $k$ there is $C$ with $|\sum_{n \le N} a(n)e(\alpha n)| \le C N^{k/2}\log 2N$ for all real $\alpha$ and $N \ge 1$ (named input). | `Iwaniec1997.ExponentialSumBound` | stated, not proved |
| Corollary 5.4 | 72 | From Theorem 5.3, $|\sum_{n \le N,\ n \equiv b\,(q)} a(n)| \le C N^{k/2}\log 2N$ uniformly in the modulus $q$, the residue $b$ and $N$. | `Iwaniec1997.sum_qExpansion_coeff_modEq_le` | proved, conditional on `Iwaniec1997.ExponentialSumBound` |
| (5.27) | 75 | Fourier coefficients of a half-integral weight cusp form of weight $\ell+\tfrac12$ with the theta multiplier satisfy $a(n) \ll n^{\ell/2+\varepsilon}$. | `Iwaniec1997.ThetaMultiplierCoeffBound` | stated, not proved |
| Theorem 5.6 | 75 | For a cusp form of weight $\ell+\tfrac12 \ge \tfrac52$ and squarefree $n \ge 2$, $a(n) \ll n^{\ell/2-1/222}\tau(n)\log n$. | `Iwaniec1997.IwaniecTheorem56` | stated, not proved |

## Chapter 10

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Proposition 10.1 | 167 | Generalized Jacobi inversion: the theta series with a spherical polynomial $P$ at $z$ equals a gamma-type factor times the dual theta series with $P^*(x) = P(A^{-1}x)$ at $-1/z$. | `Iwaniec1997.GeneralizedJacobiInversion`, `Iwaniec1997.jacobiInversion_rankOne` | proved in part (general statement stated; proved in rank one with P = 1) |
| Theta(z;h) depends on h mod N | 168 | The theta function with congruence condition depends only on the residue class of $h$ modulo $N$. | `Iwaniec1997.thetaCongruent_congr` | proved |
| (10.14), Proposition 10.3 | 168 | For homogeneous $P$ of degree $\nu$, $\Theta(z;-h) = (-1)^\nu\Theta(z;h)$, and $\Theta(z+2;h)$ and $\Theta(z+1;h)$ are $\Theta(z;h)$ times explicit roots of unity $e(A[h]/N^2)$, $e(A[h]/2N^2)$. | `Iwaniec1997.thetaCongruent_neg`, `Iwaniec1997.thetaCongruent_add_two`, `Iwaniec1997.thetaCongruent_add_one` | proved |
| Theorem 10.9 | 175 | For suitable integral $A$ of even rank $r$ and level $N$, the theta function with a spherical polynomial is a modular form of weight $\nu+r/2$ on $\Gamma_0(N)$, cuspidal if $\nu>0$. | `Iwaniec1997.ThetaModularGamma0` | stated, not proved |
