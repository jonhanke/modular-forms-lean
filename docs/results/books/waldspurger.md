# Waldspurger's theorems, the Shimura lift, Gross's example for $p = 11$ and Tunnell's theorem (papers of Waldspurger 1981 and 1991, Kohnen 1985, Gross 1987, Tunnell 1983, Coates and Wiles 1977): statement map

A topic from several papers, not a book: each row is a central result of one of the papers (the section heading) that the library states in Lean, with its declarations and its status, computed from the Lean kernel: *proved* means proved with only the standard axioms and no unproved input; *conditional* names the unproved inputs (named statements) still assumed; *stated, not proved* that the library states the result as a named structure (a `Prop`) without proof. The theorem numbers in the papers are not yet checked against the papers, and only the results stated in Lean are shown. The statements in the third column are short descriptions, not quotations; read the papers for the exact wording.

Rows: 17. proved: 7; proved, conditional: 8; stated, not proved: 2.

## Waldspurger 1991

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Sign patterns | — | A sign pattern $(\varepsilon_v)_v$ is admissible when $\prod_v \varepsilon_v = \varepsilon(\tfrac12, \pi)$; when the set of places is nonempty, $2^{\lvert S\rvert-1}$ of the $2^{\lvert S\rvert}$ patterns are admissible, and when $\varepsilon(\tfrac12,\pi) = +1$ a pattern is admissible if and only if it is $-1$ at an even number of places. | `HalfIntegral.Waldspurger.LocalData.card_admissible`, `HalfIntegral.Waldspurger.LocalData.isAdmissible_iff_even`, `HalfIntegral.Waldspurger.LocalData.prod_eq_neg_one_pow` | proved |
| Dimension of the fibre | — | The cusp forms of half-integral weight whose Shimura lifts are multiples of a given newform form a space of dimension $\sum_{\varepsilon\ \mathrm{admissible}}\prod_v d_v(\varepsilon_v)$ (local fixed-vector dimensions). | `HalfIntegral.Waldspurger.WaldspurgerFibreDimension` | stated, not proved |
| Dimension of the fibre: combinatorics | — | The sum over admissible patterns in closed form, $2\dim = \prod_v (d_v^+ + d_v^-) + \varepsilon(\tfrac12,\pi)\prod_v (d_v^+ - d_v^-)$; multiplicity one (at most a line when every local packet has at most a line of fixed vectors); without discrete series places only the pattern $+1$ contributes. | `HalfIntegral.Waldspurger.LocalData.two_mul_fibreDim`, `HalfIntegral.Waldspurger.LocalData.fibreDim_le_one`, `HalfIntegral.Waldspurger.LocalData.fibreDim_of_not_discrete` | proved |
| Coefficients and square classes | — | The $t$-th Fourier coefficient of the component of pattern $\varepsilon$ is nonzero only if $\varepsilon$ is the pattern of local signs of $t$ and $L(\tfrac12, \pi \otimes \chi_t) \ne 0$; hence a carried square class has root number $+1$ and is carried by exactly one pattern. | `HalfIntegral.Waldspurger.WaldspurgerCoefficients`, `HalfIntegral.Waldspurger.WaldspurgerCoefficients.twistRoot_eq_one`, `HalfIntegral.Waldspurger.WaldspurgerCoefficients.carries_unique`, `HalfIntegral.Waldspurger.WaldspurgerCoefficients.not_carries_of_twistRoot` | proved, conditional on `HalfIntegral.Waldspurger.WaldspurgerCoefficients` |
| Local signs: product formula | — | The product of the local signs $\varepsilon_v(\pi)\varepsilon_v(\pi\otimes\chi_t)\chi_{t,v}(-1)$ is $\varepsilon(\tfrac12,\pi)\,\varepsilon(\tfrac12,\pi\otimes\chi_t)$, so the pattern of $t$ is admissible if and only if the twisted root number is $+1$. | `HalfIntegral.Waldspurger.TwistData.prod_localSign`, `HalfIntegral.Waldspurger.TwistData.isAdmissible_localSign_iff` | proved |

## Waldspurger 1981

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Corollaire 2 | — | For a Hecke eigenform $g = \sum c(n)q^n$ of weight $k + \tfrac12$ with Shimura lift $F$ and squarefree $n_1, n_2$ in one square class, $c(n_1)^2 L(F, \chi'_{n_2}, k)\, n_2^{k-1/2} = c(n_2)^2 L(F, \chi'_{n_1}, k)\, n_1^{k-1/2}$; hence one constant per square class, and $c(n) = 0$ if and only if $L(F, \chi'_n, k) = 0$. | `HalfIntegral.Waldspurger.WaldspurgerSquareClass`, `HalfIntegral.Waldspurger.WaldspurgerSquareClass.exists_constant`, `HalfIntegral.Waldspurger.WaldspurgerSquareClass.coeff_eq_zero_iff` | proved, conditional on `HalfIntegral.Waldspurger.WaldspurgerSquareClass` (quadratic character and $n_1, n_2$ prime to $4N$) |

## Kohnen 1985

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Theorem 1 and its corollary | — | For odd squarefree $N$ and $g$ in Kohnen's plus space attached to a newform $f$: $\lvert c(\lvert D\rvert)\rvert^2/\langle g,g\rangle = 2^{\nu(N)}\frac{(k-1)!}{\pi^k}\lvert D\rvert^{k-1/2}\frac{L(f,D,k)}{\langle f,f\rangle}$ when $(D/\ell) = w_\ell$ for all $\ell \mid N$, and $c(\lvert D\rvert) = 0$ otherwise; hence the ratio form, $L(f,D,k) \ge 0$, and $c(\lvert D\rvert) \ne 0$ if and only if $L(f,D,k) \ne 0$. | `HalfIntegral.Waldspurger.KohnenSquarefree`, `HalfIntegral.Waldspurger.KohnenSquarefree.ratio`, `HalfIntegral.Waldspurger.KohnenSquarefree.central_nonneg`, `HalfIntegral.Waldspurger.KohnenSquarefree.coeff_ne_zero_iff` | proved, conditional on `HalfIntegral.Waldspurger.KohnenSquarefree` (the Petersson quotient is an unspecified positive constant) |
| Kohnen's plus space as a sign pattern | — | For odd squarefree level, Kohnen's pattern $\varepsilon_\ell = w_\ell$ is admissible, it carries a fundamental discriminant $D$ if and only if $(D/\ell) = w_\ell$ for all $\ell \mid N$, and its fibre has dimension one. | `HalfIntegral.Waldspurger.kohnenPattern_isAdmissible`, `HalfIntegral.Waldspurger.localSign_eq_kohnenPattern_iff`, `HalfIntegral.Waldspurger.kohnen_fibreDim` | proved |
| Multiplicity one in the plus space | — | The forms of Kohnen's plus space whose Shimura lifts are multiples of a given newform of odd squarefree level form a line. | `HalfIntegral.Waldspurger.finrank_plusFibre_eq_one` | proved, conditional on `HalfIntegral.Waldspurger.WaldspurgerFibreDimension` |

## Gross 1987

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| The weight 3/2 form of level 44 | — | For $p = 11$, $g = \tfrac12(\theta_{Q_1} - \theta_{Q_2})$ from the two classes of maximal orders: its coefficients vanish at $n \equiv 1, 2 \bmod 4$ (plus space) and when $11$ splits in $\mathbb Q(\sqrt{-n})$, and $c(3), c(4), \dots, c(16)$ are computed. | `HalfIntegral.Waldspurger.Gross.grossCoeff_eq_zero_of_mod_four`, `HalfIntegral.Waldspurger.Gross.grossCoeff_eq_zero_of_split`, `HalfIntegral.Waldspurger.Gross.grossCoeff_three`, `HalfIntegral.Waldspurger.Gross.grossCoeff_sixteen`, `HalfIntegral.Waldspurger.Gross.grossCoeff_twelve_hecke` | proved |
| Brandt matrices for p = 11 | — | The Brandt matrices $B(2), B(3), B(5)$ have row sums $\sigma(m)$ and the symmetry $w_jB_{ij} = w_iB_{ji}$; $(1,-1)$ is an eigenvector of the transposes with the eigenvalues $a_2 = -2$, $a_3 = -1$, $a_5 = 1$ of the curve of conductor $11$, and $(1,1)$ one with eigenvalue $\sigma(m)$. | `HalfIntegral.Waldspurger.Gross.brandt_rowSum_symm`, `HalfIntegral.Waldspurger.Gross.brandt_eigen`, `HalfIntegral.Waldspurger.Gross.brandt_eisenstein` | proved |
| Gross's formula | — | For fundamental $D_1, D_2 < 0$ with $11$ inert in $\mathbb Q(\sqrt{D_i})$, $c(\lvert D_1\rvert)^2\sqrt{\lvert D_2\rvert}\,L(f,D_2,1) = c(\lvert D_2\rvert)^2\sqrt{\lvert D_1\rvert}\,L(f,D_1,1)$; hence $c(\lvert D\rvert) = 0$ if and only if $L(f, D, 1) = 0$ for every such $D$. | `HalfIntegral.Waldspurger.Gross.GrossRatio`, `HalfIntegral.Waldspurger.Gross.grossCoeff_eq_zero_iff` | proved, conditional on `HalfIntegral.Waldspurger.Gross.GrossRatio` (the ratio form, for p = 11) |

## Tunnell 1983

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Congruent numbers and the curve $y^2 = x^3 - n^2x$ | — | A positive integer $n$ is the area of a right triangle with rational sides if and only if $y^2 = x^3 - n^2x$ has a rational point with $y \ne 0$; $5$, $6$, $7$ and $41$ are congruent. | `HalfIntegral.Waldspurger.Tunnell.isCongruent_iff_point`, `HalfIntegral.Waldspurger.Tunnell.isCongruent_five`, `HalfIntegral.Waldspurger.Tunnell.isCongruent_six`, `HalfIntegral.Waldspurger.Tunnell.isCongruent_seven`, `HalfIntegral.Waldspurger.Tunnell.isCongruent_fortyOne` | proved |
| Theorem 2 (Tunnell's formula) | — | For squarefree $n$, $L(E_n, 1) = \beta(A(n) - 2B(n))^2/(16\sqrt n)$ for odd $n$ and $\beta(C(n) - 2D(n))^2/(8\sqrt n)$ for even $n$, with Tunnell's counts of representations by $x^2 + 2y^2 + 8z^2$, $x^2 + 2y^2 + 32z^2$, $x^2 + 4y^2 + 8z^2$, $x^2 + 4y^2 + 32z^2$; hence $L(E_n, 1) = 0$ if and only if $A(n) = 2B(n)$ (resp. $C(n) = 2D(n)$). | `HalfIntegral.Waldspurger.Tunnell.TunnellFormula`, `HalfIntegral.Waldspurger.Tunnell.lval_eq_zero_iff_odd`, `HalfIntegral.Waldspurger.Tunnell.lval_eq_zero_iff_even` | proved, conditional on `HalfIntegral.Waldspurger.Tunnell.TunnellFormula` ($L(E_n, 1)$ is an abstract function: Mathlib has no L-functions of elliptic curves) |
| Tunnell's criterion, the direction without the conjecture | — | With the theorem of Coates and Wiles: an odd squarefree $n$ with $A(n) \ne 2B(n)$ (an even one with $C(n) \ne 2D(n)$) is not congruent; $1$, $3$ and $11$ are not congruent. | `HalfIntegral.Waldspurger.Tunnell.not_isCongruent_of_odd`, `HalfIntegral.Waldspurger.Tunnell.not_isCongruent_of_even`, `HalfIntegral.Waldspurger.Tunnell.not_isCongruent_one_three_eleven` | proved, conditional on `HalfIntegral.Waldspurger.Tunnell.TunnellFormula`, `HalfIntegral.Waldspurger.Tunnell.CoatesWiles` |
| Tunnell's criterion, conditional on the weak Birch and Swinnerton-Dyer conjecture | — | If the weak Birch and Swinnerton-Dyer conjecture holds for the curves $E_n$, an odd squarefree $n$ is congruent if and only if $A(n) = 2B(n)$, and an even one if and only if $C(n) = 2D(n)$. | `HalfIntegral.Waldspurger.Tunnell.isCongruent_iff_odd`, `HalfIntegral.Waldspurger.Tunnell.isCongruent_iff_even` | proved, conditional on `HalfIntegral.Waldspurger.Tunnell.TunnellFormula`, `HalfIntegral.Waldspurger.Tunnell.CoatesWiles`, `HalfIntegral.Waldspurger.Tunnell.WeakBSD` |

## Coates–Wiles 1977

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Theorem of Coates and Wiles, for $E_n$ | — | If $L(E_n, 1) \ne 0$ then $E_n(\mathbb Q)$ is finite, so it consists of the four points with $y = 0$. | `HalfIntegral.Waldspurger.Tunnell.CoatesWiles` | stated, not proved |
