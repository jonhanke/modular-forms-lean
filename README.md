# Modular forms in Lean 4

[![Lean build](https://github.com/jonhanke/modular-forms-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/modular-forms-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24069385.svg)](https://doi.org/10.5281/zenodo.24069385)

A Lean 4 library (built on Mathlib and [Tau Ceti](https://github.com/TauCetiProject/TauCeti)) that formalizes two
texts on modular forms item by item: J. S. Milne's *Modular Functions and Modular Forms* (version 1.31) and
T. Miyake's *Modular Forms*, together with dimension bounds for modular forms on $`\Gamma_0(N)`$ and $`\Gamma_1(N)`$.
Since 0.2.0 it also states the central results of three more books in Lean, as a first statement wave: G. Shimura's
*Elementary Dirichlet Series and Modular Forms*, H. Iwaniec's *Topics in Classical Automorphic Forms* and
A. N. Andrianov and V. G. Zhuravlev's *Modular Forms and Hecke Operators*. Since 0.3.0 it also has *conditional
theorems*, proved from named classical inputs: the class number one theorem of Heegner and Stark (from Weber's class
invariants), and consequences of Waldspurger's theorems on the Fourier coefficients of half-integral weight forms,
among them Tunnell's theorem on congruent numbers; and, unconditionally, the combinatorics of Waldspurger's sign
patterns, Gross's example for the prime $`11`$ and the elementary theory of congruent numbers. Since 0.3.1 it also
has theorems read in the original papers of Jacobi, Ramanujan, Weber and Kronecker. Since 0.4.0 it proves theta
series with spherical functions modular in every rank, Hecke's continuation of Eisenstein series, Riemann–Roch on
every compact Riemann surface, the dimension formula for every subgroup of finite index of
$`\mathrm{SL}_2(\mathbb Z)`$ and the Jacobi triple product, and has Shimura's theorem for the theta multiplier
conditional on one named input. Since 0.5.0 it has the Rankin–Selberg method at level one with the Petersson norm as a
value of the symmetric square $`L`$-function, the functional equation and parity of elliptic curves with a newform,
the modularity of the congruent number curves with their true $`L`$-functions and their newforms (of level $`32n^2`$
for odd squarefree $`n`$), theta series of quadratic forms in one genus differing by a cusp form in every rank,
Ramanujan's partition and $`\tau`$ congruences, and, conditional on named inputs, Kohnen's isomorphism (from Kohnen's
trace identity alone), the Kohnen–Zagier formula and Tunnell's theorem with the true $`L`$-function. The Lean
library is called `ModularFormsKB`.

## What's new in 0.5.0

- **Twenty-eight new headlines** (107 in all; the 79 of 0.4.0 are kept), each a result that neither Mathlib master nor
  Tau Ceti main (both checked on 2026-11-16) has, in **four new challenge files** (fourteen in all) and four extended
  ones:
  - [`Challenge_RankinSelberg.lean`](Challenge_RankinSelberg.lean) (2, new): for cusp forms $`f, g`$ of weight
    $`k`$ on $`\mathrm{SL}_2(\mathbb Z)`$, the Rankin–Selberg function
    $`L(f \times \bar g, s) = \zeta(2s)\sum a_n\bar b_n n^{-(s+k-1)}`$ continues to $`\mathbb C \setminus \{1\}`$ with
    a simple pole at $`s = 1`$ of residue a multiple of $`\langle g, f\rangle`$ and a functional equation under
    $`s \mapsto 1 - s`$; for a normalized Hecke eigenform, $`\langle f, f\rangle = 2\Gamma(k)/(\pi(4\pi)^k)\,L(\mathrm{Sym}^2 f, k)`$.
  - [`Challenge_EllipticCurves.lean`](Challenge_EllipticCurves.lean) (6, new): an elliptic curve over $`\mathbb Q`$
    whose $`L`$-function is that of a newform of weight 2 has an entire $`L`$-function, a functional equation with
    sign $`w = \pm 1`$, $`L(E, 1) = 0`$ when $`w = -1`$, and satisfies Milne's strong Hasse–Weil conjecture
    (Conjecture 11.17); **the congruent number curve $`E_1 : y^2 = x^3 - x`$ has the newform $`f_{32}`$ of level 32,
    and $`E_n : y^2 = x^3 - n^2x`$, $`n`$ odd squarefree, has the newform $`f_{32} \otimes (\cdot/n)`$ of level
    $`32n^2`$** (unconditional; the level of the twist is computed, Atkin–Li's Theorem 3.1 for this twist); for every
    elliptic curve over $`\mathbb Q`$ the same consequences, conditional on the modularity theorem; and Milne's
    Theorem 11.19 in analytic form (both directions, the converse by Weil's converse theorem), conditional on newness
    from the conductor.
  - [`Challenge_ThetaGenus.lean`](Challenge_ThetaGenus.lean) (3, new): theta series of positive definite even
    integral quadratic forms in one genus differ by a cusp form, in every rank (weight $`n/2`$ on $`\Gamma_1(N)`$ for
    even $`n`$, Shimura's $`S_{k+1/2}(4N, \chi)`$ for odd $`n = 2k + 1`$), in Gram-matrix form; Gross's weight-$`3/2`$
    form for the prime 11 lies in Kohnen's plus space of level 44.
  - [`Challenge_KohnenPlusSpace.lean`](Challenge_KohnenPlusSpace.lean) (5, new): Shimura's $`T(p^2)`$ is self-adjoint
    on Kohnen's plus space (unconditional); and, in [Conditional theorems](#conditional-theorems), Kohnen's isomorphism
    $`S^+_{k+1/2}(4) \cong S_{2k}(\mathrm{SL}_2(\mathbb Z))`$ (from one named input, Kohnen's trace identity), and the
    Kohnen–Zagier formula, Waldspurger's theorem on the plus space and the nonnegativity of the central twisted values
    $`L(F, D, k) \ge 0`$ (through Zagier's kernel, from three named inputs). Kohnen's $`U(4)`$ identity on the plus
    space and the cycle integrals at square discriminants, named inputs in earlier drafts, are proved.
  - [`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean) (14, was 9): **the congruent number curves
    $`E_n : y^2 = x^3 - n^2x`$ are modular with an entire $`L`$-function** (unconditional: the $`q`$-series $`f_{32}`$
    is a cusp form of weight 2 on $`\Gamma_0(32)`$, and Mathlib's $`L`$-function of $`E_n`$ has coefficients
    $`(n/m)\,b(m)`$); and Tunnell's theorem with this true $`L`$-function in place of an abstract one, conditional on
    cited theorems only (Waldspurger, Tunnell's eigenform proposition and central values, Coates–Wiles; and, for the
    converse, Tau Ceti's statement of the Birch and Swinnerton-Dyer conjecture). That Tunnell's two series are cusp
    forms of weight $`3/2`$ on $`\Gamma_0(128)`$ and the root number of $`L(E_{2m}, s)`$ are proved.
  - [`Challenge_Waldspurger.lean`](Challenge_Waldspurger.lean) (28, was 27): Shimura's theorem for the theta
    multiplier conditional on a smaller named input, the unfolding of an explicit kernel built from $`f|W_{4N}`$
    (`ShimuraFrickeKernelUnfolding`).
  - [`Challenge_Historical.lean`](Challenge_Historical.lean) (12, was 6): Jacobi's identity for the cube of Euler's
    product; Ramanujan's partition congruences $`p(5m + 4) \equiv 0 \pmod 5`$, $`p(7m + 5) \equiv 0 \pmod 7`$,
    $`p(35m + 19) \equiv 0 \pmod{35}`$; his congruences $`\tau(5n) \equiv 0 \pmod 5`$ and $`\tau(n) \equiv 0
    \pmod 7`$ for $`n \equiv 0, 3, 5, 6 \pmod 7`$; his Question 387,
    $`\sum_{n \ge 1} n/(e^{2\pi n} - 1) = 1/24 - 1/(8\pi)`$; Jacobi's quartic identity
    $`\vartheta_{00}^4 = \vartheta_{01}^4 + \vartheta_{10}^4`$ with Weber's $`\mathfrak f^8 = \mathfrak f_1^8 + \mathfrak f_2^8`$;
    and Kronecker's $`\vartheta'''(0, w) = -\pi^2 E_2(w)\,\vartheta'(0, w)`$.
- **New in the library** since 0.4.0 (beyond the headlines):
  - Half-integral weight: the Petersson product on $`S_{k+1/2}(4N, \chi)`$ for every $`N`$, the change of variables
    for $`\Gamma_0(L)`$-invariant integrands, the Hecke operators $`T(p^2)`$ as commuting linear operators,
    $`f|W_{4N}`$ with its $`q`$-expansion, the theta series $`\theta_{\psi,t}`$ at the cusp 0 (Miyake, Corollary
    4.9.7 (2)), the expansion of theta series at every cusp, Kohnen's projection, $`U(4)`$ and $`W(4)`$ on the plus
    space with Kohnen's $`U(4)`$ identity, Kohnen's $`D`$-th lift derived from his trace identity, and Zagier's kernel
    function with its coefficients and the cycle integrals of Shintani's lift, evaluated at square discriminants
    through the classes of binary quadratic forms of discriminant $`D^2`$ and Gauss's sign of the quadratic Gauss sum
    (`HalfIntegral/`, `HalfIntegral/ZagierKernel/`).
  - Congruent numbers: the coefficients of Mathlib's $`L`$-function of $`E_n`$ (point counts, Gauss's count for
    $`y^2 = x^3 - x`$), $`f_{32}`$ as a theta series of $`\mathbb Z[i]`$ with a characteristic, its Fricke involution,
    the root number of $`L(E_n, s)`$ for every squarefree $`n`$ (for even $`n`$ through $`f_{64}`$ as a coset theta
    series), Tunnell's two forms as products of theta series, the torsion of $`E_n(\mathbb Q)`$, and the Coates–Wiles
    theorem for $`E_n`$ from its general form for curves with complex multiplication by a maximal order
    (`HalfIntegral/Waldspurger/CongruentCurves/`); $`S_2(\Gamma_0(16)) = 0`$, $`f_{32}`$ as a Tau Ceti newform, and
    the Fricke involution on $`q`$-series dilations (`Elliptic/`).
  - Modular elliptic curves (`Elliptic/`): the Hasse bound for the coefficients of $`L(E, s)`$, Milne's Proposition
    11.21 (the bijection between isogeny classes of conductor $`N`$ and rational newforms of level $`N`$) from named
    inputs, and the degree of a modular parametrization stated.
  - Theta series of quadratic forms (`ThetaGenus/`): Miyake's Theorem 4.9.3, Corollaries 4.9.4 and 4.9.5 (3) in
    Gram-matrix form, the odd-rank character $`(2\det H/\cdot)`$, constant terms at every cusp as local Gauss sums.
  - Rankin–Selberg (`RankinSelberg/`): the weight-0 Eisenstein series of level one as a Mellin transform, Hecke's
    bounds, the unfolding at level one and the Euler product of $`L(f \times \bar f, s)`$.
  - Historical: more of Jacobi's § 66 (with Clausen's transformation), Ramanujan's recurrence for $`\tau(n)`$,
    Kronecker's class number relations (some conditional on a named input), some of Eisenstein's lattice sums in
    terms of $`\wp`$, the duplication formulas of the theta constants, a new library for H. J. S. Smith's
    *Report on the Theory of Numbers* (`Historical/Smith/`); Ramanujan's Table I (the Eisenstein series up to weight
    32 as polynomials in $`Q`$, $`R`$) and Dirichlet series, Eisenstein's Dirichlet series for the cubic residue
    character, his reduced matrices and lattices with multiplication by $`i`$, and Jacobi's multipliers of the
    transformations of orders 3 and 5.
  - Pins: Mathlib `e8ba86f` (unchanged) and Tau Ceti `1ff5324` (Tau Ceti main of 2026-11-16), was `ca32605`.
- **Book maps regenerated** (rows of each status, 0.4.0 → 0.5.0): Milne 179 proved (was 178), 19 in part (was 18),
  6 conditional (was 7); Miyake 106 proved (was 105), 41 in part (was 40); four rows formalized in files that were
  outside the 0.4.0 release are now in it. The Waldspurger statement map has 22 rows (was 17): 7 proved, 2 in part,
  12 conditional, 1 stated.
- **[Known restrictions](#known-restrictions)** of the new headlines.

- **Book maps**: for Milne and Miyake, a table from every item (theorem, proposition, lemma, corollary, definition) to
  the Lean declaration that formalizes it and its status: [docs/results/books/](docs/results/books/README.md).
- **Statement maps**: for Shimura, Iwaniec and Andrianov–Zhuravlev, for the papers on Waldspurger's theorems and for
  the historical papers,
  each central result that the library states in Lean, with its declaration and whether it is proved, conditional or
  only stated (same page).
- **Literature statements**: each result from a book or paper is a Lean declaration tagged
  `@[kb "<source key>" "<locator>"]`, with the keys of [`references.bib`](references.bib).
- **What is proved**: every theorem is checked by the Lean kernel; the only `sorry`s in the repository are the
  deliberate ones in the `Challenge_<book>.lean` files, which state the headline results without proofs. The CI
  workflow builds the library, checks that the headline theorems depend only on the standard axioms `propext`,
  `Classical.choice` and `Quot.sound` ([scripts/check_axioms.lean](scripts/check_axioms.lean)), checks that every Lean
  name of the book and statement maps exists ([scripts/check_map_names.lean](scripts/check_map_names.lean)), and runs
  `lake comparator` once per book to check the proved statements against the `Challenge_<book>.lean` files.
- **Cited results are named**: where the library assumes a result it does not prove, the result is a named Lean
  structure (a "named statement"), never assumed silently; a theorem that uses it has it as a hypothesis and the maps
  mark the row *conditional*.
- **Comparison**: [docs/results/comparison.md](docs/results/comparison.md) says, for each headline and each chapter,
  what Mathlib and Tau Ceti already have, what other formalizations (the Stacks Project formalization by Axiom) also
  prove, and what this library adds.

## The books

| book | rows | proved | proved in part | conditional | definitions | in Mathlib | in Tau Ceti | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|---|
| [J. S. Milne, *Modular Functions and Modular Forms* (version 1.31)](docs/results/books/milne-mf.md) | 293 | 179 | 19 | 6 | 44 | 23 | 4 | 18 | 29 |
| [T. Miyake, *Modular Forms* (Springer, 1989)](docs/results/books/miyake.md) | 272 | 106 | 41 | 0 | 2 | 17 | 33 | 73 | 2 |
| [Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)](docs/results/books/dimension.md) | 22 | 21 | 0 | 0 | 1 | 0 | 0 | 0 | 12 |

*Proved*: proved with only the standard axioms and no unproved input. *Other*: refuted as stated, stated without proof, formalized in the source library but not in this release, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) in this library whose result, or a part of it, is also proved in Mathlib, Tau Ceti or the Stacks Project formalization (Axiom); each map names the declarations in its column *Also in*. Rows that are not results are omitted from the maps.

**Statement maps** (a first statement wave: the central results stated in Lean, each marked proved or stated):

| book | rows | proved | proved in part | conditional | stated, not proved |
|---|---|---|---|---|---|
| [G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer, 2007)](docs/results/books/shimura2007.md) | 12 | 3 | 6 | 0 | 3 |
| [H. Iwaniec, *Topics in Classical Automorphic Forms* (American Mathematical Society, 1997)](docs/results/books/iwaniec1997.md) | 28 | 6 | 2 | 2 | 18 |
| [A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (American Mathematical Society, 1995)](docs/results/books/andrianovzhuravlev1995.md) | 26 | 12 | 3 | 1 | 10 |
| [Waldspurger's theorems, the Shimura lift, Gross's example for $p = 11$ and Tunnell's theorem (papers of Waldspurger 1981 and 1991, Kohnen 1985, Gross 1987, Tunnell 1983, Coates and Wiles 1977)](docs/results/books/waldspurger.md) | 22 | 7 | 2 | 12 | 1 |
| [Historical theorems: Jacobi, *Fundamenta nova* (1829); Ramanujan, *Collected Papers* (1927); Weber, *Elliptische Functionen und algebraische Zahlen* (1891) and *Lehrbuch der Algebra* III (1908); Kronecker, *Werke* 4 and 5](docs/results/books/historical.md) | 8 | 4 | 3 | 0 | 1 |

## Highlights

Every result listed here is a headline theorem of a `Challenge_<book>.lean` file: it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input. Headlines are only results that are in neither Mathlib
nor Tau Ceti (main branch, checked on 2026-11-10 for the headlines new in 0.2.0, on 2026-11-12 for those new in
0.3.0, on 2026-11-14 for those new in 0.3.1, on 2026-11-15 for those new in 0.4.0 and on 2026-11-16 for those new in
0.5.0), or that are stronger here
([comparison](docs/results/comparison.md)). One of them, Weil's Riemann hypothesis for curves, is also proved in the
Stacks Project formalization by Axiom, in another form; it is labelled below. Related results of other libraries are
cited next to the headlines, and the book maps credit, in their column *Also in*, every result proved here that is
also proved in Mathlib, Tau Ceti or the Stacks Project formalization. The statements have **not yet been reviewed by
a human** (see Provenance).

**Milne, *Modular Functions and Modular Forms*, sections 0 to 10** ([`Challenge_Milne.lean`](Challenge_Milne.lean))

- **Kronecker's modular equation, for every level $`N`$:** $`\mathbb C(X_0(N)) = \mathbb C(j, j_N)`$, and the minimal polynomial of $`j(Nz)`$ over $`\mathbb C(j)`$ has degree $`[\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]`$ and is $`F_N(j, Y)`$ with $`F_N \in \mathbb Z[X, Y]`$, symmetric for $`N > 1`$, and $`F_p \equiv X^{p+1} + Y^{p+1} - X^pY^p - XY \pmod p`$ (`kronecker_modularEquation`, Theorem 6.1).
- **Elliptic functions:** on a fundamental parallelogram the orders and the residues of an elliptic function sum to $`0`$ and $`\sum \operatorname{ord}_P(f)P \in \Lambda`$ (`doublyPeriodic_sums`, Proposition 3.1); an elliptic function with prescribed zeros and poles exists when their sums agree modulo $`\Lambda`$, and is unique up to a constant (`prescribedDivisor`, Theorem 3.8); every elliptic function is a rational function of $`\wp`$ and $`\wp'`$ (`ellipticFunctionField`, Proposition 3.11).
- **Moduli of elliptic curves:** over an algebraically closed field, the $`j`$-line solves the moduli problem of elliptic curves (`ellipticModuli_jLine`, Theorem 8.4), and the moduli problem of elliptic curves with a cyclic subgroup of order $`N`$ has a solution for every $`N`$ prime to the characteristic (`cyclicModuli`, Theorem 8.6). Related results: Tau Ceti's fine moduli scheme $`Y_1(N)`$, $`N \ge 4`$ (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne`), on which the proof of Theorem 8.6 for $`N \ge 4`$ is built, and the algebraic moduli stack $`\mathcal M_{1,1}`$ of the Stacks Project formalization (Axiom; Tag 072R, index match).
- **The modular curves $`X(N)`$, $`N = 2, 3, 4, 5`$, have genus zero:** every holomorphic differential on the compact Riemann surface $`X(N) = \Gamma(N)\backslash\mathbb H^*`$ is zero (`modularCurveX_Gamma_genus_eq_zero`, Example 2.23; new in 0.2.0). Related: Tau Ceti (main) proves the Riemann–Hurwitz formula for Fuchsian groups in Euler-characteristic form, under finite-CW-type hypotheses.
- **The little Picard theorem:** a nonconstant entire function omits at most one complex value (`littlePicard`, Remark 2.25; new in 0.3.1). Milne's covering argument, run with the level-one $`j`$ on the free locus of $`\mathrm{PSL}_2(\mathbb Z)`$ (a covering of $`\mathbb C \setminus \{0, 1728\}`$) instead of $`\lambda`$ on $`\Gamma(2)`$. Neither Mathlib nor Tau Ceti (main, checked on 2026-11-14) has it.
- **The existence theorem and the Riemann–Roch theorem on every compact Riemann surface:** on a compact connected Riemann surface $`X`$ the meromorphic functions separate points and form a function field of one variable over $`\mathbb C`$ (`meromorphicFunctions_separate_points`, Theorem 1.17), and $`\ell(D) = \deg D + 1 - g + \ell(K - D)`$ for every divisor $`D`$ and canonical divisor $`K`$, with all $`L(D)`$ finite-dimensional (`riemannRoch`, Theorem 1.20; new in 0.4.0). Milne cites both; the library proves the existence theorem after Forster (§ 14), with Tau Ceti's analytic tools, and transfers Tau Ceti's Riemann–Roch for function fields through the bijection between points and places. Tau Ceti (main, checked on 2026-11-15) has the field $`M(X)`$ but no existence theorem and no Riemann–Roch on Riemann surfaces.
- **The dimension and genus formulas for every subgroup of finite index:** for every $`\Gamma \subseteq \mathrm{SL}_2(\mathbb Z)`$ of finite index, congruence or not, $`\dim M_{2k}(\Gamma) = (2k - 1)(g - 1) + \varepsilon_\infty k + \sum_P \lfloor k(1 - 1/e_P)\rfloor`$ for $`k \ge 1`$ (`dimensionFormula`, Theorem 4.9) and $`g(X(\Gamma)) = 1 + m/12 - \nu_2/4 - \nu_3/3 - \nu_\infty/2`$ (`genusFormula`, Theorem 2.22; new in 0.4.0). Mathlib has the dimension formula at level one; Tau Ceti has dimensions of Eisenstein subspaces and some weight-two cases, not these formulas.
- **Holomorphic line bundles on $`\mathbb H`$ are trivial:** every holomorphic line bundle on the upper half plane has a nowhere-vanishing holomorphic section (`holomorphicLineBundle_upperHalfPlane_trivial`, Remark 4.26, cited by Milne without proof; new in 0.4.0), by the multiplicative Cousin problem on $`\mathbb H`$.

**Milne, *Modular Functions and Modular Forms*, sections 11 and 12** ([`Challenge_MilneArithmetic.lean`](Challenge_MilneArithmetic.lean)) (a separate file since 0.4.0)

- **Weil's Riemann hypothesis for curves over finite fields:** for a function field $`F`$ of one variable over $`\mathbb F_q`$, $`\mathbb F_q`$ algebraically closed in $`F`$, of genus $`g`$, there are algebraic integers $`\alpha_1, \dots, \alpha_{2g}`$ with $`N_n = 1 + q^n - \sum \alpha_i^n`$ for every $`n \ge 1`$, permuted by $`\alpha \mapsto q/\alpha`$, and $`|\alpha_i| = \sqrt q`$ (`weil_riemannHypothesis_curves`, Theorem 11.4; Tau Ceti has the genus-one case). *Also proved in the Stacks Project formalization (Axiom), in étale-cohomological form (tag 03V8, Bombieri–Stepanov); ours is the function-field form of Milne 11.4 and includes the functional equation* (the Stacks match is from its declaration index; see the [comparison](docs/results/comparison.md)).
- **Singular moduli are algebraic integers:** $`j(z)`$ is an algebraic integer for every imaginary quadratic $`z \in \mathbb H`$ (`j_isIntegral_of_imaginaryQuadratic`, Corollary 12.16).
- **The class group acts on the $`j`$-invariants with complex multiplication:** for an order $`O`$ of an imaginary quadratic field $`K`$, an algebraically closed field $`k`$ of characteristic zero and an embedding $`K \to k`$, there is a map $`\mathrm{Pic}(O) \times \mathrm{Ell}_k(O) \to \mathrm{Ell}_k(O)`$ sending $`([\mathfrak a], j(E))`$ to $`j(E')`$ for every $`\mathfrak a`$-isogeny $`E \to E'`$ with normalized complex multiplication, whose orbit maps are bijections (`classGroupAction_ellCM`, Proposition 12.21 in the corrected form; new in 0.3.1). The action laws are not stated ([Known restrictions](#known-restrictions)).
- **Betti, $`\ell`$-adic and tangent representations:** for every elliptic curve $`E`$ over $`\mathbb C`$, with $`\Lambda`$ its lattice and $`\rho`$ the action of $`\mathrm{End}(E)`$ on the tangent space, $`\mathbb Z_\ell \otimes \Lambda \cong T_\ell E`$ and $`\mathbb C \otimes \Lambda \cong \rho \oplus \bar\rho`$, compatibly with every endomorphism (`betti_tate_comparison`, Proposition 11.5; new in 0.3.1).
- **The conductor exponent at a cusp:** for an elliptic curve over $`\mathbb Q`$ and a prime $`p \ne 2, 3`$, the exponent of $`p`$ in the conductor is exactly $`2`$ if and only if the reduction at $`p`$ is additive (`conductor_exponent_eq_two_iff`, Milne p. 111; new in 0.3.1). The conductor is Tau Ceti's, from Tate's algorithm; Tau Ceti proves "at least $`2`$", not the equality.

**Miyake, *Modular Forms*** ([`Challenge_Miyake.lean`](Challenge_Miyake.lean))

- **Hecke's theorem:** for coefficients of polynomial growth, $`g = f|_k\omega_N`$ if and only if $`\Lambda_N(s; f)`$ and $`\Lambda_N(s; g)`$ continue to the plane, with $`\Lambda_N(s; f) = i^k\Lambda_N(k - s; g)`$ and the usual polar parts, bounded on vertical strips (`hecke_converse`, Theorem 4.3.6); at level one, $`\sum a_n q^n`$ is a modular form of weight $`k`$ if and only if its $`L`$-function has this analytic behaviour (`hecke_converse_levelOne`, Theorem 4.3.8). The forward direction for cusp forms (the Fricke relation gives the functional equation) is in Tau Ceti (`CuspForm.frickeCompletedL_functional_equation`); the converse direction is new here.
- **Weil's converse theorem:** if $`L(s; f)`$, $`L(s; g)`$ and their twists by the primitive characters of conductor in a suitable set of primes satisfy the functional equations with Weil's constant, then $`f \in M_k(N, \chi)`$, $`g \in M_k(N, \bar\chi)`$ and $`g = f|_k\omega_N`$ (`weil_converse`), and $`f`$, $`g`$ are cusp forms when $`L(s; f)`$ converges absolutely at $`k - \delta`$ (`weil_converse_cusp`, Theorem 4.3.15).
- **The Hecke ring of $`\Gamma_0(N)`$ is a polynomial ring:** $`\mathcal R(\Gamma_0(N), \Delta_0(N))`$ over $`\mathbb Z`$ is the polynomial ring in $`T(p)`$, $`T(p, p)`$ ($`p \nmid N`$) and $`T(q)`$ ($`q \mid N`$) (`heckeRing_gamma0_polynomial`, Theorem 4.5.9; new in 0.3.1). Tau Ceti has the local theorem at level one (Shimura, Theorem 3.20).
- **$`T(n)`$ and $`T^*(n)`$ are adjoint for every $`n`$:** on $`S_k(N, \chi)`$, $`\langle f | T(n), g\rangle = \langle f, g | T^*(n)\rangle`$ for every $`n \ge 1`$, with no condition on $`(n, N)`$ (`hecke_adjoint_heckeTStar`, Theorem 4.5.4 (2); new in 0.3.1). Tau Ceti has the case $`(n, N) = 1`$.
- **Theta series with spherical functions are modular forms, in every rank:** for an even lattice $`L`$ of rank $`r`$ and level $`N`$ and a spherical function $`P(x) = (\langle u, x\rangle + i\langle w, x\rangle)^\nu`$ ($`\nu \le 1`$ or $`u + iw`$ isotropic), $`\theta_L(\tau; P) = \sum_{v \in L} P(v)e^{\pi i\|v\|^2\tau}`$ lies in $`M_{r/2+\nu}(\Gamma_0(N), \chi_L)`$ for even $`r`$ (`thetaSpherical_even`) and in Shimura's half-integral weight space $`M_{r/2+\nu}(4N, \chi)`$ for odd $`r`$ (`thetaSpherical_odd`), and is a cusp form when $`\nu \ge 1`$ (Theorem 4.9.3, Corollary 4.9.4, in lattice form; new in 0.4.0). Tau Ceti (main) has the case $`P = 1`$.
- **Shimura's twisted theta law for every character:** for every Dirichlet character $`\psi`$ modulo $`r`$, primitive or not, of parity $`\nu`$, $`\theta_{\psi,t}(\gamma z) = \bar\psi(d)\,(t/|d|)\,(cz + d)^\nu j(\gamma, z)\,\theta_{\psi,t}(z)`$ on $`\Gamma_0(4tr^2)`$ (`thetaTwist_transformation`, Corollary 4.9.7 (1); new in 0.4.0).
- **Hecke's continuation of Eisenstein series in $`s`$:** $`s \mapsto E_k(z, s; \chi, \psi)`$ continues to a meromorphic function on $`\mathbb C`$, given by its Fourier expansion, for every integer $`k`$ with $`\chi(-1)\psi(-1) = (-1)^k`$ (`heckeEisenstein_continuation`, Theorem 7.2.9), and Hecke's limits at $`s = 0`$ in weights $`2`$ and $`1`$ have the Fourier expansions of Theorems 7.2.12 and 7.2.13, with the non-holomorphic term in weight $`2`$ (`heckeLimit_weightTwo`, `heckeLimit_weightOne`; new in 0.4.0). Tau Ceti (main) has the weight-one and weight-two Eisenstein series by other constructions, not Hecke's continuation in $`s`$.
- **Hecke's lemma:** if $`f`$ and $`f|_k\alpha`$ both lie in $`\mathcal G_k(N, \chi)`$, $`k > 0`$, for a primitive integer matrix $`\alpha \in \Delta_0(N)`$ with $`\det\alpha > 1`$ prime to $`N`$, then $`f = 0`$ (`hecke_lemma`, Lemma 4.6.3; new in 0.4.0). Tau Ceti's newform theory goes around this lemma.

**Shimura, *Elementary Dirichlet Series and Modular Forms*** ([`Challenge_Shimura.lean`](Challenge_Shimura.lean)) (new in 0.2.0)

- **$`L(k,\chi)`$ by a sum over half the residues:** for a nontrivial primitive character $`\chi`$ modulo $`d`$ and $`k \ge 2`$ with $`\chi(-1) = (-1)^k`$, $`k!\,(2\pi i)^{-k}\,G(\bar\chi)\,L(k,\chi) = -\sum_{1 \le a \le (d-1)/2} \bar\chi(a)\,B_k(a/d)`$ (`LFunction_halfRange`, Theorem 4.14 (i)). Related: Tau Ceti (main) has the value through the generalized Bernoulli number $`B_{k,\chi}`$, a sum over all residues.

**Iwaniec, *Topics in Classical Automorphic Forms*** ([`Challenge_Iwaniec.lean`](Challenge_Iwaniec.lean)) (new in 0.2.0)

- **Kloosterman sums:** twisted multiplicativity $`S(m, n; qr) = S(\bar q m, \bar q n; r)\,S(\bar r m, \bar r n; q)`$ for coprime $`q, r`$ (`kloosterman_mul_of_coprime`, (4.12)), and the second moment $`\sum_{a \not\equiv 0} S(a, 1; p)^2 = p^2 - p - 1`$ at a prime $`p`$ (`kloostermanMoment_two`, (4.23)). Neither Mathlib nor Tau Ceti defines Kloosterman sums.

**Andrianov and Zhuravlev, *Modular Forms and Hecke Operators*** ([`Challenge_AndrianovZhuravlev.lean`](Challenge_AndrianovZhuravlev.lean)) (new in 0.2.0)

- **Siegel theta series converge absolutely and uniformly:** for an even integral positive definite $`m \times m`$ matrix $`Q`$ and $`\varepsilon > 0`$, the terms $`\exp(\pi i\,\mathrm{tr}({}^tN Q N Z))`$ of the theta series of degree $`n`$ are bounded on $`\{Z \in H_n : \mathrm{Im}\,Z \ge \varepsilon\}`$ by a summable family independent of $`Z`$ (`siegelTheta_dominated`, Chapter 1, Proposition 1.3). Neither Mathlib nor Tau Ceti has the Siegel upper half space.

**Waldspurger's theorems, the Shimura lift and Gross's example for $`p = 11`$** ([`Challenge_Waldspurger.lean`](Challenge_Waldspurger.lean)) (new in 0.3.0; the conditional results of this file are in [Conditional theorems](#conditional-theorems))

- **Waldspurger's sign patterns (1991):** for local data at a nonempty finite set of places, exactly $`2^{|S|-1}`$ of the $`2^{|S|}`$ sign patterns are admissible ($`\prod_v \varepsilon_v = \varepsilon(\tfrac12, \pi)`$) (`waldspurger_card_admissible`); when $`\varepsilon(\tfrac12,\pi) = +1`$ a pattern is admissible if and only if it is $`-1`$ at an even number of places (`waldspurger_isAdmissible_iff_even`); the dimension $`\sum_{\varepsilon}\prod_v d_v(\varepsilon_v)`$ in closed form, $`2\dim = \prod_v (d_v^+ + d_v^-) + \varepsilon(\tfrac12,\pi)\prod_v (d_v^+ - d_v^-)`$ (`waldspurger_two_mul_fibreDim`), and multiplicity one (`waldspurger_fibreDim_le_one`); the local signs selected by a square class $`t`$ multiply to $`\varepsilon(\tfrac12,\pi)\,\varepsilon(\tfrac12,\pi\otimes\chi_t)`$, so their pattern is admissible if and only if the twisted root number is $`+1`$ (`waldspurger_prod_localSign`, `waldspurger_isAdmissible_localSign_iff`). The local data are parameters (see [Known restrictions](#known-restrictions)).
- **Kohnen's plus space as a sign pattern (odd squarefree level):** Kohnen's pattern $`\varepsilon_\ell = w_\ell`$ (the Atkin–Lehner eigenvalues) is admissible (`waldspurger_kohnenPattern_isAdmissible`), it carries a fundamental discriminant $`D`$ if and only if $`(D/\ell) = w_\ell`$ for every $`\ell \mid N`$, Kohnen's condition (`waldspurger_localSign_eq_kohnenPattern_iff`), and with Kohnen's local data the fibre has dimension one (`waldspurger_kohnen_fibreDim`).
- **Gross's example for $`p = 11`$:** for the ternary forms $`Q_1 = 4x_0^2 + 4x_0x_2 + 11x_1^2 + 12x_2^2`$ and $`Q_2 = 3x_0^2 + 4x_0x_2 + 44x_1^2 + 44x_1x_2 + 16x_2^2`$ of the two classes of maximal orders of the quaternion algebra ramified at $`\{11, \infty\}`$, the coefficients $`c(n) = (r_{Q_1}(n) - r_{Q_2}(n))/2`$ of $`g = \tfrac12(\theta_1 - \theta_2)`$ vanish for $`n \equiv 1, 2 \bmod 4`$ (Kohnen's plus condition) and whenever $`11`$ splits in $`\mathbb Q(\sqrt{-n})`$ (`gross_grossCoeff_eq_zero_of_mod_four`, `gross_grossCoeff_eq_zero_of_split`), and $`g = -q^3 + q^4 + q^{11} + q^{12} - q^{15} - 2q^{16} + \cdots`$ (`gross_grossCoeff_values`, computed by the kernel); the Brandt matrices $`B(2), B(3), B(5)`$ have row sums $`\sigma(m)`$, the symmetry $`w_jB_{ij} = w_iB_{ji}`$, the eigenvector $`(1, 1)`$ with eigenvalue $`\sigma(m)`$, and the eigenvector $`(1, -1)`$ of the transposes with the eigenvalues $`a_2 = -2`$, $`a_3 = -1`$, $`a_5 = 1`$ of the elliptic curve of conductor $`11`$ (`gross_brandt_rowSum_symm`, `gross_brandt_eisenstein`, `gross_brandt_eigen`). The forms and the matrices are entered explicitly; their identification with Gross's quaternionic objects was checked numerically, not in Lean.
- **Gross's form is modular** (new in 0.5.0): $`g = \tfrac12(\theta_1 - \theta_2)`$ is a cusp form of weight $`3/2`$ on $`\Gamma_0(44)`$ in Kohnen's plus space, because $`Q_1`$ and $`Q_2`$ lie in one genus (`gross_form_mem_plusCuspForms`, in [`Challenge_ThetaGenus.lean`](Challenge_ThetaGenus.lean)).
- **Hecke's functional equation and the Rankin–Selberg unfolding** (new in 0.4.0; both were named inputs of Shimura's theorem in 0.3.1): the lattice Eisenstein series $`E(z, s) = y^s\sum_{(c,d) \in L\mathbb Z \times \mathbb Z}\omega(d)(cz+d)^\lambda|cz+d|^{-\lambda-2s}`$ with $`\omega(-1) = (-1)^\lambda`$ has a completion $`L^s\pi^{-s}\Gamma(s + \lambda/2)E(z, s)`$ that is entire in $`s`$, bounded on vertical strips, and equal to the completed dual series at $`1 - s`$ (`eisensteinLattice_functionalEquation`); and for $`G`$ with the unitary weight-$`\lambda`$ law on $`\Gamma_0(L)`$, $`\int_{\Gamma_0(L)\backslash\mathbb H} G\,E(\cdot, s)\,d\mu = 2L(2s, \omega)\int_0^\infty\!\int_0^1 G(x + iy)\,y^{s-2}\,dx\,dy`$ (`rankin_unfolding`).

Neither Mathlib (at the pinned commit) nor Tau Ceti (main, checked on 2026-11-12) has half-integral weight forms, Waldspurger's theorems or Brandt matrices.

**Congruent numbers** ([`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean)) (new in 0.3.0; Tunnell's criterion is in [Conditional theorems](#conditional-theorems))

- **Congruent numbers and the curve $`y^2 = x^3 - n^2x`$:** a positive integer $`n`$ is the area of a right triangle with rational sides if and only if $`E_n : y^2 = x^3 - n^2x`$ has a rational point with $`y \ne 0`$ (`congruent_isCongruent_iff_point`).
- **Explicit congruent triangles:** $`5`$, $`6`$, $`7`$ and $`41`$ are congruent, by the triangles $`(3/2, 20/3, 41/6)`$, $`(3, 4, 5)`$, $`(24/5, 35/12, 337/60)`$ and $`(40/3, 123/20, 881/60)`$ (`congruent_five_six_seven_fortyOne`); Tunnell's counts $`A(n) = \#\{x^2 + 2y^2 + 8z^2 = n\}`$, $`B(n) = \#\{x^2 + 2y^2 + 32z^2 = n\}`$ (and $`C`$, $`D`$ for even $`n`$) for small $`n`$, by kernel computation (`congruent_tunnell_counts`), and the consistency check $`A(5) = 2B(5)`$ for the congruent number $`5`$ (`congruent_tunnell_five_consistent`).

- **The congruent number curves are modular** (new in 0.5.0): $`f_{32} = \sum b(m)q^m`$, with $`b(m)`$ the sum of $`\operatorname{Re}\alpha`$ over the Gaussian integers $`\alpha \equiv 1 \bmod (2 + 2i)`$ of norm $`m`$, is a cusp form of weight 2 on $`\Gamma_0(32)`$, and for squarefree $`n \ge 1`$ Mathlib's $`L`$-function of $`E_n`$ has the coefficients $`(n/m)\,b(m)`$ and an entire extension (`congruent_curve_modular`).

Neither Mathlib (at the pinned commit) nor Tau Ceti (main, checked on 2026-11-12) defines congruent numbers; neither has the modularity of $`y^2 = x^3 - x`$ or of its twists (checked again on 2026-11-16; Tau Ceti has the curve and its rational points).

**Historical theorems: Jacobi, Ramanujan, Weber, Kronecker** ([`Challenge_Historical.lean`](Challenge_Historical.lean)) (new in 0.3.1; all unconditional since 0.4.0; six more in 0.5.0)

- **Jacobi's differential equation of the modular equations** (*Fundamenta nova*, 1829, § 33): if $`\lambda(k)`$ is related to $`k`$ by a modular equation $`B(\lambda)/A(\lambda) = (aB(k)/A(k) + b)/(cB(k)/A(k) + d)`$, $`ad - bc \ne 0`$, for solutions $`A`$, $`B`$ of Legendre's equation with nonzero Wronskian, then $`3\lambda''^2 - 2\lambda'\lambda''' + \lambda'^2\big[\big(\tfrac{1+k^2}{k-k^3}\big)^2 - \big(\tfrac{1+\lambda^2}{\lambda-\lambda^3}\big)^2\lambda'^2\big] = 0`$ (`jacobi_modular_equation_ode`); and the Fourier series of $`\Theta`$ and $`H`$ (§ 62, `jacobi_theta_fourier`).
- **Ramanujan's differential equations** in his variable $`x`$, $`|x| < 1`$: $`x\,P' = (P^2 - Q)/12`$, $`x\,Q' = (PQ - R)/3`$, $`x\,R' = (PR - Q^2)/2`$ (`ramanujan_differential_equations`). Mathlib proves them in the variable $`\tau`$ for the normalized Eisenstein series.
- **Kronecker's transformation law for $`\mathrm{Ser}_\rho`$** (*Werke* 5, I, art. XXI, § 7, (E)) for $`\rho \ge 2`$, where the series converges absolutely (`kronecker_ser_transformation`).
- **The Jacobi triple product identity** (*Fundamenta nova*, § 64): $`\sum_{n \in \mathbb Z} q^{n^2}z^n = \prod_{n \ge 1}(1 - q^{2n})(1 + q^{2n-1}z)(1 + q^{2n-1}/z)`$ for $`|q| < 1`$, $`z \ne 0`$ (`jacobi_triple_product`; new in 0.4.0).
- **Weber's theta functions as products of $`\eta`$ and his functions $`\mathfrak f`$** (Weber 1891, § 21, (9)): $`\vartheta_{00} = \eta\,\mathfrak f^2`$, $`\vartheta_{01} = \eta\,\mathfrak f_1^2`$, $`\vartheta_{10} = \eta\,\mathfrak f_2^2`$ on $`\mathbb H`$ (`weber_theta_eta`; new in 0.3.1, where it was conditional on the triple product; unconditional since 0.4.0).

- **New in 0.5.0:** Jacobi's identity $`\prod_{n \ge 1}(1 - q^n)^3 = \sum_{n \ge 0}(-1)^n(2n + 1)q^{n(n+1)/2}`$ (§ 66, `jacobi_cube`); Ramanujan's partition congruences $`p(5m + 4) \equiv 0 \pmod 5`$, $`p(7m + 5) \equiv 0 \pmod 7`$, $`p(35m + 19) \equiv 0 \pmod{35}`$ (`ramanujan_partition_congruences`), proved as Ramanujan did, from Jacobi's identity; his congruences $`\tau(5n) \equiv 0 \pmod 5`$ and $`\tau(n) \equiv 0 \pmod 7`$ for $`n \equiv 0, 3, 5, 6 \pmod 7`$ (`ramanujan_tau_congruences`); his Question 387, $`\sum_{n \ge 1} n/(e^{2\pi n} - 1) = 1/24 - 1/(8\pi)`$ (`ramanujan_question387`); Jacobi's quartic identity $`\vartheta_{00}^4 = \vartheta_{01}^4 + \vartheta_{10}^4`$ and Weber's $`\mathfrak f^8 = \mathfrak f_1^8 + \mathfrak f_2^8`$ (`jacobi_quartic_weber_eighth_powers`); and Kronecker's $`\vartheta'''(0, w) = -\pi^2E_2(w)\vartheta'(0, w)`$ for his odd theta function (`kronecker_theta_E2`).

Neither Mathlib (at the pinned commit; master checked on 2026-11-14) nor Tau Ceti (main, checked on 2026-11-14) has Jacobi's equation, the theta functions $`\Theta`$, $`H`$ in Jacobi's form, Ramanujan's equations in the variable $`x`$, or Kronecker's series; neither has the Jacobi triple product (master and main checked again on 2026-11-15), Ramanujan's congruences for $`p(n)`$ or $`\tau(n)`$, Jacobi's cube or quartic identities, or Kronecker's identity (checked again on 2026-11-16; Mathlib has Euler's pentagonal theorem and the transformation of $`E_2`$).

**The Rankin–Selberg method at level one** ([`Challenge_RankinSelberg.lean`](Challenge_RankinSelberg.lean)) (new in 0.5.0)

- **Continuation, pole and functional equation** (Rankin 1939, Selberg 1940): for cusp forms $`f = \sum a_nq^n`$, $`g = \sum b_nq^n`$ of weight $`k`$ on $`\mathrm{SL}_2(\mathbb Z)`$, $`L(f \times \bar g, s) = \zeta(2s)\sum a_n\bar b_n n^{-(s+k-1)}`$ continues to a holomorphic function on $`\mathbb C \setminus \{1\}`$ with $`(s - 1)L(f \times \bar g, s) \to \frac\pi2\frac{(4\pi)^k}{\Gamma(k)}\langle g, f\rangle`$, and its completion $`\Lambda(s) = 2\pi^{-s}(4\pi)^{-(s+k-1)}\Gamma(s)\Gamma(s+k-1)L(f \times \bar g, s)`$ satisfies $`\Lambda(1 - s) = \Lambda(s)`$, with $`\Lambda(s) - \langle g, f\rangle/(s-1) + \langle g, f\rangle/s`$ entire (`rankinSelberg_levelOne`).
- **The Petersson norm as a symmetric square value** (Zagier 1977): for a normalized Hecke eigenform, $`\langle f, f\rangle = \frac{2\Gamma(k)}{\pi(4\pi)^k}L(\mathrm{Sym}^2 f, k)`$, with $`L(\mathrm{Sym}^2 f, w)`$ continued from its Euler product to $`\operatorname{Re} w \ge k`$ (`petersson_eq_symSq`).

Neither Mathlib (master, checked on 2026-11-16) nor Tau Ceti (main, checked on 2026-11-16) has the Rankin–Selberg integral or the symmetric square $`L`$-function.

**Modular elliptic curves** ([`Challenge_EllipticCurves.lean`](Challenge_EllipticCurves.lean)) (new in 0.5.0; the theorems conditional on the modularity theorem are in [Conditional theorems](#conditional-theorems))

- **Functional equation and parity:** if an elliptic curve $`E`$ over $`\mathbb Q`$ has a newform $`f`$ of weight 2 and level $`N`$ with its coefficients, then $`L(E, s)`$ is entire and $`\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)`$ satisfies $`\Lambda(E, 2 - s) = w\Lambda(E, s)`$, $`w = \pm1`$, with $`L(E, 1) = 0`$ when $`w = -1`$ (`elliptic_hasNewform_functionalEquation`).
- **Strong Hasse–Weil** (Milne, Theorem 11.19, one direction): with $`N`$ the conductor, $`E`$ satisfies Milne's strong Hasse–Weil conjecture (Conjecture 11.17), the functional equations of all twisted $`L`$-functions by primitive characters of conductor prime to $`N`$ (`elliptic_hasNewform_strongHasseWeil`).
- **The congruent number curves have newforms:** $`E_1 : y^2 = x^3 - x`$ has the newform $`f_{32} = \eta(4\tau)^2\eta(8\tau)^2`$ of level 32 (`elliptic_congruentCurve_one_hasNewform`; newness from $`S_2(\Gamma_0(16)) = 0`$), and for odd squarefree $`n`$, $`E_n : y^2 = x^3 - n^2x`$ has the newform $`f_{32} \otimes (\cdot/n)`$ of level exactly $`32n^2`$ (`elliptic_congruentCurve_hasNewform`; Atkin–Li's Theorem 3.1 for this twist, proved by comparing Fricke involutions). With the first theorem, $`L(E_n, s)`$ has a functional equation and parity.

Neither Mathlib nor Tau Ceti (checked on 2026-11-16) relates elliptic curves to newforms; Tau Ceti has the functional equation of newforms and the primitive twist of a newform, which the proofs use.

**Theta series of one genus** ([`Challenge_ThetaGenus.lean`](Challenge_ThetaGenus.lean)) (new in 0.5.0)

- **The difference of two theta series of one genus is a cusp form** (a consequence of Siegel 1935, proved here directly): for positive definite even integral Hessians $`H`$, $`H'`$ of rank $`n`$ in one genus, with a common level, $`\theta_H - \theta_{H'}`$ is a cusp form of weight $`n/2`$ on $`\Gamma_1(N)`$ for even $`n`$ (`thetaGenus_sub_cuspForm_even`), and lies in Shimura's $`S_{k+1/2}(4N, \chi)`$, $`\chi(d) = (2\det H/d)`$, for odd $`n = 2k + 1`$ (`thetaGenus_sub_cuspForm_odd`). The proof compares the constant terms at every cusp, which are local Gauss sums.

Tau Ceti (main, checked on 2026-11-16) has theta series of even lattices, their transformation law at every level and the even unimodular cases; neither it nor Mathlib has the cuspidality of differences in a genus or theta series of odd rank in half-integral weight.

**Kohnen's plus space** ([`Challenge_KohnenPlusSpace.lean`](Challenge_KohnenPlusSpace.lean)) (new in 0.5.0; Kohnen's isomorphism and the Kohnen–Zagier formula are in [Conditional theorems](#conditional-theorems))

- **$`T(p^2)`$ is self-adjoint on the plus space:** for an odd prime $`p`$, Shimura's $`T(p^2)`$ is self-adjoint on $`S^+_{k+1/2}(4)`$ for the Petersson product (`plus_heckeT_selfAdjoint`; Shimura 1973, Kohnen 1980), by the double coset change of variables.

## Conditional theorems

A *conditional theorem* is proved in Lean from **named inputs**: classical theorems that the library does not prove,
each stated as a field of a Lean `Prop` structure, with its source in the docstring. The theorem takes the structure
as a hypothesis, so it has the form *(named inputs) → statement*, and `#print axioms` shows only `propext`,
`Classical.choice` and `Quot.sound`: the inputs are hypotheses, never axioms. No input is the conclusion in disguise:
for the class number one theorem, no field mentions class number one, the nine discriminants or Heegner's Diophantine
equation. Proving the inputs would make the theorem unconditional. One result below is conditional on a
**conjecture** rather than on theorems of the literature, and is marked so. The statements have **not yet been
reviewed by a human**.

**The class number one theorem (Heegner 1952, Stark 1967)** ([`Challenge_HeegnerStark.lean`](Challenge_HeegnerStark.lean))

- **Statement:** let $`K`$ be an imaginary quadratic field. Then $`h_K = 1`$ if and only if
  $`d_K \in \{-3, -4, -7, -8, -11, -19, -43, -67, -163\}`$, that is, $`K = \mathbb Q(\sqrt{-d})`$ with
  $`d \in \{1, 2, 3, 7, 11, 19, 43, 67, 163\}`$.
- **Headline:** `WeberHeegnerStarkInputs → (classNumber K = 1 ↔ discr K ∈ {-3, -4, -7, -8, -11, -19, -43, -67, -163})`
  (`heegnerStark_classNumber_eq_one_iff`); in Gauss's form, with $`-d`$ a square in $`K`$,
  `WeberHeegnerStarkInputs → QuadraticDiscriminantInput → (classNumber K = 1 ↔ ∃ d ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}, IsSquare (-d : K))`
  (`heegnerStark_classNumber_eq_one_iff_isSquare`). Both: axioms `propext`, `Classical.choice`, `Quot.sound`.
- **Named inputs** (all **assumed**, none proved in this library), the fields of `WeberHeegnerStarkInputs` in
  [`Inputs.lean`](ModularFormsKB/Historical/WeberHeegnerStark/Inputs.lean). Weber's section numbers are those of
  *Elliptische Functionen und algebraische Zahlen* (1891), whose second edition is volume III of the *Lehrbuch der
  Algebra* (1908); the 1908 numbering has not been compared.

  | Lean field | classical theorem | source | elsewhere |
  |---|---|---|---|
  | `isIntegral_kleinJ` | $`j(\tau)`$ is an algebraic integer for imaginary quadratic $`\tau`$ | Weber § 87 | not formalized |
  | `finrank_kleinJ` | $`[\mathbb Q(j(\tau)) : \mathbb Q] = h(D)`$ for the root $`\tau`$ of a primitive form of discriminant $`D`$ | Weber § 88 (first main theorem of complex multiplication) | not formalized |
  | `imaginaryQuadratic` | $`d_K`$ is a fundamental discriminant and $`h_K = h(d_K)`$, the number of reduced forms | Dirichlet, Dedekind | the class number part in Tau Ceti, for its own count of reduced forms (`TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms_of_discr_eq`); not connected here |
  | `classNumber_four_mul` | $`h(-4m) = 3h(-m)`$ for $`m \equiv 3 \bmod 8`$, $`m > 3`$ | Weber § 89 | not formalized |
  | `gammaTwo_mem` | $`\gamma_2(\tau) \in \mathbb Q(j(\tau))`$ when $`3 \nmid D`$, $`3 \nmid a`$, $`3 \mid b`$ | Weber § 92 | not formalized |
  | `weberF_pow_eight_mem` | Weber's Theorem I: $`\mathfrak f(\sqrt{-m})^8 \in \mathbb Q(j(\sqrt{-m}))`$, $`m`$ odd, $`3 \nmid m`$ | Weber § 94 | not formalized |
  | `weberF_pow_three_mem` | Weber's Theorem VI: $`\mathfrak f(\sqrt{-m})^3 \in \mathbb Q(j(\sqrt{-m}))`$, $`m \equiv 3 \bmod 8`$, $`3 \nmid m`$ | Weber § 94, stated without a complete proof (the "gap" in Heegner's proof, closed by Stark 1969 and Deuring 1968) | not formalized |
  | `weber_cubic` | $`(\mathfrak f_2^{24} + 16)^3 = j\,\mathfrak f_2^{24}`$ | Weber § 93 (1) | Tau Ceti, for its Siegel function $`g_{(0,1/2)}`$, with $`g_{(0,1/2)}^{12} = \mathfrak f_2^{24}`$ (`TauCeti.ModularForm.siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three`); not connected here |

  A second structure, `QuadraticDiscriminantInput` (the discriminant of $`\mathbb Q(\sqrt m)`$ is $`m`$ or $`4m`$;
  Dedekind), is used only for the form with $`\mathbb Q(\sqrt{-d})`$. Two fields are weaker than Weber's statements
  (Theorem VI with the extra condition $`3 \nmid m`$; Theorems I and VI only at $`\sqrt{-m}`$), which makes the
  conditional theorem stronger.
- **Proved here, from the inputs:** Gauss's reduction ($`h(D) = 1`$ for a fundamental $`D < 0`$ forces
  $`D \in \{-3, -4, -7, -8\}`$ or $`D = -p`$, $`p \equiv 3 \bmod 8`$ prime) and $`h(D) = 1`$ for the nine
  discriminants, by computation; Heegner's step (K. Heegner, *Diophantische Analysis und Modulfunktionen*, 1952): for
  $`p \ge 11`$ with $`h(-p) = 1`$, $`\gamma_2((-3 + \sqrt{-p})/2)`$ is an integer $`g`$ and $`2/\mathfrak f(\sqrt{-p})^2`$ gives an
  integer point of $`y^2 = 2u(u^3 + 1)`$; the six integer points of that curve; and a certified numerical enclosure of
  $`j((-3 + \sqrt{-p})/2)`$ that recovers $`p \in \{11, 19, 43, 67, 163\}`$. The last two are ported from Tau Ceti
  (Apache 2.0).
- **Sources:** H. Weber 1891 and 1908 (above); K. Heegner, Math. Z. 56 (1952); H. M. Stark, *A complete determination
  of the complex quadratic fields of class-number one*, Michigan Math. J. 14 (1967), an independent proof; Stark, *On
  the "gap" in a theorem of Heegner*, J. Number Theory 1 (1969). Bibliographic details are in
  [`references.bib`](references.bib) (not yet checked against the papers).
- **Related:** Tau Ceti (main, checked on 2026-11-12) proves that the nine fields have class number one and the
  classification for $`|d_K| < 51`$; the direction "class number one implies one of the nine" is in neither Tau Ceti
  nor Mathlib.

**Waldspurger's theorems on Fourier coefficients of half-integral weight** ([`Challenge_Waldspurger.lean`](Challenge_Waldspurger.lean))

- **Statements and headlines** (each takes its named input as the first hypothesis; axioms `propext`,
  `Classical.choice`, `Quot.sound`):
  - `WaldspurgerSquareClass → …`: for a Hecke eigenform $`g = \sum c(n)q^n`$ of weight $`k + \tfrac12`$ whose Shimura
    lift is $`F`$, on a square class in which one central value $`L(F, \chi'_{n_0}, k)`$ is nonzero,
    $`c(n)^2 = A\,L(F, \chi'_n, k)\,n^{k-1/2}`$ with one constant $`A`$ (`waldspurger_exists_constant`), and
    $`c(n) = 0 \iff L(F, \chi'_n, k) = 0`$ (`waldspurger_coeff_eq_zero_iff`).
  - `KohnenSquarefree → …`: for odd squarefree level and $`D`$ satisfying Kohnen's condition, the central value
    $`L(f, D, k)`$ is real and $`\ge 0`$ (`waldspurger_kohnen_central_nonneg`), the ratio form
    $`|c(|D_1|)|^2|D_2|^{k-1/2}L(f,D_2,k) = |c(|D_2|)|^2|D_1|^{k-1/2}L(f,D_1,k)`$ (`waldspurger_kohnen_ratio`), and
    $`c(|D|) \ne 0 \iff L(f, D, k) \ne 0`$ (`waldspurger_kohnen_coeff_ne_zero_iff`).
  - `WaldspurgerCoefficients → …`: a square class carried by an admissible pattern has root number $`+1`$
    (`waldspurger_twistRoot_eq_one`) and is carried by only one pattern (`waldspurger_carries_unique`).
  - `WaldspurgerFibreDimension → …`: the forms of Kohnen's plus space whose Shimura lifts are multiples of a given
    newform form a line (`waldspurger_finrank_plusFibre_eq_one`).
  - `GrossRatio → …`: for $`p = 11`$ and fundamental $`D < 0`$ with $`11`$ inert in $`\mathbb Q(\sqrt D)`$,
    $`c(|D|) = 0 \iff L(f, D, 1) = 0`$, given one inert $`D_0`$ with $`c(|D_0|) \ne 0`$ and $`L(f, D_0, 1) \ne 0`$
    (`gross_grossCoeff_eq_zero_iff`).
- **Named inputs** (all **assumed**, none proved in this library; locators not yet checked against the papers):

  | Lean structure | classical theorem | source |
  |---|---|---|
  | `WaldspurgerSquareClass` | $`c(n_1)^2 L(F, \chi'_{n_2}, k)\,n_2^{k-1/2} = c(n_2)^2 L(F, \chi'_{n_1}, k)\,n_1^{k-1/2}`$ on a square class, for quadratic $`\chi`$ and $`n_i`$ prime to $`4N`$ (weaker than the source) | Waldspurger 1981, Corollaire 2 |
  | `KohnenSquarefree` | Kohnen's formula for $`\lvert c(\lvert D\rvert)\rvert^2`$ in terms of $`L(f, D, k)`$ for odd squarefree level, and $`c(\lvert D\rvert) = 0`$ off Kohnen's condition; the Petersson quotient $`\langle g,g\rangle/\langle f,f\rangle`$ is an unspecified positive constant | Kohnen 1985, Theorem 1 |
  | `WaldspurgerCoefficients` | the $`t`$-th coefficient of $`\sigma_\varepsilon`$ is nonzero if and only if $`\varepsilon`$ is the pattern of local signs of $`t`$ and $`L(\tfrac12, \pi\otimes\chi_t) \ne 0`$ | Waldspurger 1991, main theorem |
  | `WaldspurgerFibreDimension` | the forms with a given Shimura lift form a space of dimension $`\sum_{\varepsilon}\prod_v d_v(\varepsilon_v)`$ | Waldspurger 1991 |
  | `GrossRatio` | $`c(\lvert D_1\rvert)^2\sqrt{\lvert D_2\rvert}\,L(f,D_2,1) = c(\lvert D_2\rvert)^2\sqrt{\lvert D_1\rvert}\,L(f,D_1,1)`$ for fundamental $`D_i < 0`$ with $`11`$ inert, $`f`$ the newform of level $`11`$ | Gross 1987 |

- **Proved here, without inputs:** the sign-pattern combinatorics, Kohnen's pattern, and Gross's form and Brandt
  matrices for $`p = 11`$ ([Highlights](#highlights)).
- **Sources:** J.-L. Waldspurger, *Sur les coefficients de Fourier des formes modulaires de poids demi-entier*,
  J. Math. Pures Appl. 60 (1981); *Correspondances de Shimura et quaternions*, Forum Math. 3 (1991); W. Kohnen,
  *Fourier coefficients of modular forms of half-integral weight*, Math. Ann. 271 (1985); B. H. Gross, *Heights and
  the special values of L-series*, CMS Conference Proceedings 7 (1987).

**Tunnell's theorem on congruent numbers** ([`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean))

- **Statement:** let $`n`$ be a squarefree positive integer, odd (for even $`n`$ the same with
  $`C(n) = \#\{x^2 + 4y^2 + 8z^2 = n/2\}`$ and $`D(n) = \#\{x^2 + 4y^2 + 32z^2 = n/2\}`$), and
  $`A(n) = \#\{(x,y,z) \in \mathbb Z^3 : x^2 + 2y^2 + 8z^2 = n\}`$, $`B(n) = \#\{x^2 + 2y^2 + 32z^2 = n\}`$. If
  $`n`$ is congruent then $`A(n) = 2B(n)`$.
- **Headlines:** `TunnellFormula → CoatesWiles → (A(n) ≠ 2B(n) → ¬ IsCongruent n)` (`congruent_not_isCongruent_of_odd`,
  and `congruent_not_isCongruent_of_even`); in particular $`1`$, $`3`$ and $`11`$ are not congruent
  (`congruent_not_isCongruent_one_three_eleven`). Axioms `propext`, `Classical.choice`, `Quot.sound`.
- **Named inputs** (assumed): `TunnellFormula`, Tunnell's formula $`L(E_n, 1) = \beta(A(n) - 2B(n))^2/(16\sqrt n)`$
  ($`n`$ odd; $`\beta(C(n) - 2D(n))^2/(8\sqrt n)`$ for $`n`$ even), $`\beta = \int_1^\infty dx/\sqrt{x^3 - x}`$
  (J. B. Tunnell, *A classical Diophantine problem and modular forms of weight 3/2*, Invent. Math. 72 (1983),
  Theorem 2; it rests on Waldspurger's theorem); `CoatesWiles`, if $`L(E_n, 1) \ne 0`$ then $`E_n(\mathbb Q)`$ has
  only the four points with $`y = 0`$ (J. Coates and A. Wiles, *On the conjecture of Birch and Swinnerton-Dyer*,
  Invent. Math. 39 (1977)). In these headlines (of 0.3.0) $`L(E_n, 1)`$ is a function `Lval` constrained only by
  these inputs; the headlines new in 0.5.0 below use the true $`L`$-function instead. Both constants of Tunnell's formula were checked numerically for all
  squarefree $`n \le 59`$.
- **Proved here, without inputs:** $`n`$ is congruent if and only if $`E_n`$ has a rational point with $`y \ne 0`$;
  the counts $`A`$, $`B`$, $`C`$, $`D`$ (computable) and their values for small $`n`$.

**Conditional on a conjecture: Tunnell's criterion as an equivalence** ([`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean))

- **Headlines:** `TunnellFormula → CoatesWiles → WeakBSD → (IsCongruent n ↔ A(n) = 2B(n))` for odd squarefree
  $`n`$ (`congruent_isCongruent_iff_odd`), and `… ↔ C(n) = 2D(n)` for even $`n`$ (`congruent_isCongruent_iff_even`).
- **The extra input is a conjecture, not a theorem:** `WeakBSD` is the weak Birch and Swinnerton-Dyer conjecture for
  the curves $`E_n`$ (if $`L(E_n, 1) = 0`$ then $`E_n(\mathbb Q)`$ is infinite, so it has a point with $`y \ne 0`$).
  It is open; the library does not claim it. These two headlines say only: if the conjecture holds, Tunnell's
  criterion decides which $`n`$ are congruent.

**Shimura's theorem for the theta multiplier** ([`Challenge_Waldspurger.lean`](Challenge_Waldspurger.lean)) (new in 0.4.0)

- **Statement** (G. Shimura, *On modular forms of half integral weight*, Ann. of Math. 97 (1973), Main Theorem): let
  $`k \ge 2`$, $`t \ge 1`$ squarefree, and $`f = \sum a(n)q^n`$ a cusp form of weight $`k + \tfrac12`$ on
  $`\Gamma_0(4N)`$ with character $`\chi`$ (theta multiplier). Then there is a cusp form $`F`$ of weight $`2k`$ on
  $`\Gamma_0(4N)`$ with character $`\chi^2`$ whose coefficients are
  $`c(n) = \sum_{d \mid n}\chi_t(d)\,d^{k-1}\,a(tn^2/d^2)`$ for $`n \ge 1`$.
- **Headline:** `ShimuraDualUnfolding thetaMultiplierSystem k N χ → (the statement)`
  (`shimuraLift_theta_of_dualUnfolding`); axioms `propext`, `Classical.choice`, `Quot.sound`.
- **Named input** (assumed): `ShimuraDualUnfolding`, the dual side of the Rankin integral in Shimura's proof: for the
  integral of $`f`$ against the theta series and the Eisenstein series at the cusps other than $`\infty`$, twisted by
  every primitive character of odd prime conductor prime to $`4N`$, the value is $`i^{2k}`$ (times Weil's constant)
  times the completed Dirichlet series of one sequence $`b`$ (and of its twist). Shimura 1973, proof of the Main
  Theorem (locator unverified).
- **Proved here, no longer inputs** (they were named inputs of this theorem in 0.3.1): the transformation law of the
  twisted theta series for every character (Miyake, Corollary 4.9.7 (1)), Hecke's functional equation of the
  lattice Eisenstein series (`eisensteinLattice_functionalEquation`), the Rankin–Selberg unfolding
  (`rankin_unfolding`), and Gauss's sign of the quadratic Gauss sum (so that the Hecke operators preserve the
  spaces); with them the library assembles Weil's converse theorem (Miyake, Theorem 4.3.15) for the lift.
- **New in 0.5.0, a smaller input:** `ShimuraFrickeKernelUnfolding thetaMultiplierSystem k N χ → (the statement)`
  (`shimuraLift_theta_of_frickeKernel`). The library now proves that $`f|W_{4N}`$ is a cusp form of weight
  $`k + \tfrac12`$ for the conjugate character with a $`q`$-expansion, and rewrites the dual side of the Rankin integral
  as the integral over $`\Gamma_0(L)\backslash\mathbb H`$ of an explicit kernel built from $`f|W_{4N}`$, the theta series
  $`\theta_{\bar\psi}`$ and an Eisenstein series at $`\infty`$. The named input is the unfolding of that integral into
  the completed Dirichlet series of one sequence $`b`$ (and of its twists), from the same proof of Shimura.

**Tunnell's theorem with the true $`L`$-function** ([`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean)) (new in 0.5.0)

- **Proved here, without inputs:** the congruent number curves are modular: the $`q`$-series
  $`f_{32} = \sum b(m)q^m`$, $`b(m) = \sum \operatorname{Re}\alpha`$ over the Gaussian integers
  $`\alpha \equiv 1 \bmod (2 + 2i)`$ of norm $`m`$, is a cusp form of weight 2 on $`\Gamma_0(32)`$, and for squarefree
  $`n \ge 1`$ the coefficients of Mathlib's $`L`$-function of $`E_n`$ are $`(n/m)\,b(m)`$, so $`L(E_n, s)`$ has an
  entire extension (`congruent_curve_modular`).
- **Headlines:** `TunnellInputs → CoatesWilesCM → (A(n) ≠ 2B(n) → ¬ IsCongruent n)` for odd squarefree $`n`$
  (`congruent_not_isCongruent_odd_trueL`; `…_even_trueL` with $`C`$, $`D`$), where $`L(E_n, 1)`$ is now the value at
  $`1`$ of the continuation of the true $`L`$-series; and, **conditional in addition on a conjecture**, Tau Ceti's
  statement of the Birch and Swinnerton-Dyer conjecture for $`E_n`$ (`WeierstrassCurve.BirchSwinnertonDyer`; open),
  `IsCongruent n ↔ A(n) = 2B(n)` (`congruent_isCongruent_iff_odd_trueL`, `…_even_trueL`).
- **Named inputs** (assumed; each a cited theorem), the fields of `TunnellInputs` and `CoatesWilesCM`:

  | Lean structure | classical theorem | source |
  |---|---|---|
  | `WaldspurgerSquareClassFull` | Waldspurger's theorem on square classes for all squarefree $`n_1, n_2`$ in one square class at the primes dividing $`4N`$, here at level 128 and weight $`3/2`$ for the characters $`1`$ and $`(2/\cdot)`$ | Waldspurger 1981, Corollaire 2 |
  | `TunnellEigenforms` | Tunnell's two forms $`\eta(8\tau)\eta(16\tau)\theta(2\tau)`$, $`\eta(8\tau)\eta(16\tau)\theta(4\tau)`$ are eigenforms of $`T(p^2)`$, $`p`$ odd, with eigenvalue $`b(p)`$ (checked numerically) | Tunnell 1983 |
  | `TunnellConstants` | $`L(E_1, 1) = \beta/4`$, $`L(E_3, 1) = \beta/\sqrt3`$, $`L(E_2, 1) = \beta/(2\sqrt2)`$, $`L(E_{10}, 1) = 2\beta/\sqrt{10}`$ (checked numerically) | Tunnell 1983 |
  | `CoatesWilesCM` | an elliptic curve over $`\mathbb Q`$ with complex multiplication by the maximal order of an imaginary quadratic field (its $`j`$-invariant is one of nine values) and $`L(E, 1) \ne 0`$ has finitely many rational points; applied to $`E_n`$, $`j = 1728`$ | Coates and Wiles 1977, Theorem 1 |

- **Proved here, no longer inputs:** the modularity of $`f_{32}`$, the root number of $`L(E_n, s)`$ for every
  squarefree $`n`$ (for even $`n`$ through $`f_{64}`$, a theta series of a coset of a binary lattice), that Tunnell's two
  $`q`$-series are cusp forms of weight $`3/2`$ on $`\Gamma_0(128)`$ (as products of theta series), the torsion of
  $`E_n(\mathbb Q)`$, the case $`E_n`$ of Coates–Wiles from its general form; and Tunnell's formula itself, with the
  true $`L`$-values, from the inputs above.

**Kohnen's plus space: Kohnen's isomorphism and the Kohnen–Zagier formula** ([`Challenge_KohnenPlusSpace.lean`](Challenge_KohnenPlusSpace.lean)) (new in 0.5.0)

- **Statements** (W. Kohnen, *Modular forms of half-integral weight on $`\Gamma_0(4)`$*, Math. Ann. 248 (1980),
  Theorem 1; W. Kohnen and D. Zagier, *Values of L-series of modular forms at the center of the critical strip*,
  Invent. Math. 64 (1981), Theorem 1 and Corollary 1): for $`k \ge 1`$ there is a Hecke-equivariant isomorphism
  $`S^+_{k+1/2}(4) \cong S_{2k}(\mathrm{SL}_2(\mathbb Z))`$ (`kohnen_isomorphism`); if $`g = \sum c(n)q^n`$ in the plus
  space corresponds to the normalized eigenform $`F`$ and $`D`$ is a fundamental discriminant with $`(-1)^kD > 0`$,
  then $`|c(|D|)|^2/\langle g, g\rangle = \frac{(k-1)!}{\pi^k}|D|^{k-1/2}L(F, D, k)/\langle F, F\rangle`$
  (`kohnen_zagier`); hence Waldspurger's ratio on the plus space (`waldspurger_plus`) and $`L(F, D, k) \ge 0`$
  (`kohnen_zagier_twistedL_nonneg`).
- **Named inputs** (assumed; the isomorphism needs only the first, the other three headlines all three):

  | Lean structure | classical theorem | source |
  |---|---|---|
  | `KohnenTraceIdentity` | the traces of every product of Hecke operators agree on $`S^+_{k+1/2}(4)`$ and on $`S_{2k}(\mathrm{SL}_2(\mathbb Z))`$ ($`T(p^2) \leftrightarrow T(p)`$, and $`T^+(4) \leftrightarrow T(2)`$) | Kohnen 1980, §§ 2–4 |
  | `KohnenKernelModular` | Zagier's kernel $`\Omega(z, \tau)`$ is a form in the plus space in $`\tau`$ and the kernel of the adjoint of the $`D`$-th Shimura lift | Kohnen and Zagier 1981, § II |
  | `ZagierKernelUnfolding` | the Petersson product of Zagier's function $`f_{k,D,|D|m}`$ with $`G`$ is a constant times the cycle integral $`r_{k,D}(G; m)`$ | Kohnen and Zagier 1981, § II, Proposition |

- **Proved here:** the self-adjointness of $`T(p^2)`$ on the plus space (`plus_heckeT_selfAdjoint`, unconditional;
  formerly a named input); Kohnen's $`U(4)`$ identity, the $`q`$-expansion of $`W(4)U(4)U(4)g`$ on the plus space,
  which makes $`T^+(4)`$ an operator on the plus space (Kohnen 1980, § 2 and Proposition 2; formerly the named input
  `KohnenLUFour`); the cycle integrals at the square discriminant $`D^2`$ give $`L(G, D, k)`$ (Kohnen and Zagier 1981,
  § II; formerly the named input `KohnenSquareCycle`); and, from the trace identity (formerly separate inputs),
  Kohnen's $`D`$-th lift to level one and multiplicity one on the plus space.

**Modular elliptic curves** ([`Challenge_EllipticCurves.lean`](Challenge_EllipticCurves.lean)) (new in 0.5.0)

- **Unconditional:** if $`E`$ over $`\mathbb Q`$ has a newform $`f`$ of weight 2 and trivial character with
  $`a_n(f) = a_n(E)`$ for all $`n`$ (`HasNewform`, a condition, not an input), then $`L(E, s)`$ is entire,
  $`\Lambda(E, s) = N^{s/2}(2\pi)^{-s}\Gamma(s)L(E, s)`$ satisfies $`\Lambda(E, 2 - s) = w\Lambda(E, s)`$ with
  $`w = \pm1`$, $`L(E, 1) = 0`$ if $`w = -1`$ (`elliptic_hasNewform_functionalEquation`), and, at the level of the
  conductor, $`E`$ satisfies Milne's strong Hasse–Weil conjecture (`elliptic_hasNewform_strongHasseWeil`). The
  congruent number curves have newforms, so the first theorem applies to them: $`E_1`$ has $`f_{32}`$, of level 32
  (`elliptic_congruentCurve_one_hasNewform`), and $`E_n`$, $`n`$ odd squarefree, has $`f_{32} \otimes (\cdot/n)`$, of
  level exactly $`32n^2`$ (`elliptic_congruentCurve_hasNewform`).
- **Headlines:** `ModularityTheorem → (for every E: strong Hasse–Weil, entire L(E, s), functional equation, parity)`
  (`elliptic_modularity_consequences`); `NewformOfConductor → (E has a newform of level its conductor ↔ E satisfies
  the strong Hasse–Weil conjecture with a uniform sign)` (`elliptic_newform_iff_strongHasseWeil`; the converse is
  Weil's converse theorem, proved in the library).
- **Named inputs** (assumed): `ModularityTheorem`, every elliptic curve over $`\mathbb Q`$ has a newform of level its
  conductor with its coefficients (A. Wiles, Ann. of Math. 141 (1995); R. Taylor and A. Wiles, 1995; C. Breuil,
  B. Conrad, F. Diamond and R. Taylor, J. Amer. Math. Soc. 14 (2001); Milne, Theorem 11.24); `NewformOfConductor`, a
  cusp form of weight 2 on $`\Gamma_0(N_E)`$ with the coefficients of $`L(E, s)`$ is a newform (A. O. L. Atkin and
  J. Lehner, 1970; W.-C. W. Li, 1975; Miyake, Theorems 4.6.13 and 4.6.19).

**Weber's theta functions as products of $`\eta`$ and his functions $`\mathfrak f`$**: conditional in 0.3.1 on the Jacobi
triple product (`JacobiTripleProduct`), **unconditional since 0.4.0** (the identity is proved, `jacobi_triple_product`);
both are now in [Highlights](#highlights).

## Known restrictions

Of the headlines new in 0.5.0:

- **Rankin–Selberg** (`rankinSelberg_levelOne`, `petersson_eq_symSq`): at level one only. The continuation is shown to
  agree with the Dirichlet series for $`\operatorname{Re} s > 2`$ (the unfolding uses Hecke's bound), not on the whole
  half-plane of convergence $`\operatorname{Re} s > 1`$. The Petersson product is Tau Ceti's integral of
  $`y^k\bar g f`$ over the standard fundamental domain, without division by its volume. A normalized Hecke eigenform
  is given by conditions on its coefficients (`IsNormalizedEigenform`); the bridge from Tau Ceti's level-one newforms
  is not part of the headline. $`L(\mathrm{Sym}^2 f, w)`$ is continued only to $`\operatorname{Re} w \ge k`$; its
  holomorphy on $`\mathbb C`$ (Shimura 1975) is stated, not proved.
- **Modular elliptic curves** (`elliptic_*`): the conductor is Milne's geometric conductor, here the norm of Tau Ceti's
  conductor ideal from Tate's algorithm; its agreement with Ogg's formula is not formalized. `HasNewform E N f` asks
  $`a_n(f) = a_n(E)`$ for every $`n`$, at the bad primes too. The converse direction of Theorem 11.19 is proved from
  the strong Hasse–Weil conjecture with one sign $`w\chi(-1)`$ for all twists, slightly stronger than Milne's form,
  where the sign may depend on $`\chi`$. The modularity theorem and newness from the conductor are assumed. For the
  congruent number curves `HasNewform` is proved for $`n = 1`$ and for odd squarefree $`n`$ only (for even $`n`$ the
  level of the twist of $`f_{32}`$ by a character of even conductor is not computed), at the level $`32n^2`$; that
  $`32n^2`$ is the conductor of $`E_n`$ (Tate's algorithm at 2 and at $`p \mid n`$) is not formalized.
- **Theta series of one genus** (`thetaGenus_*`, `gross_form_mem_plusCuspForms`): the forms are given by their
  Hessians $`H`$ ($`x^{\mathsf T}Hx = 2Q(x)`$, the theta series $`\sum q^{Q(x)}`$, level and character through
  $`H`$); this convention has not yet been reviewed. The genus is defined by congruences (equal determinants and an
  isometry modulo every $`c`$), not linked to Tau Ceti's genus of lattices. Only positive definite forms and the
  trivial spherical function.
- **Kohnen's plus space** (`kohnen_*`, `waldspurger_plus`, `plus_heckeT_selfAdjoint`): level 4 only, the theta
  multiplier only. Kohnen's trace identity is assumed in a reformulated form (traces of products of prime Hecke
  operators), and his operator $`T^+(4)`$ is given through its coefficient formula. The Kohnen–Zagier formula rests
  on two inputs about Zagier's kernel (its modularity, with the adjoint of the Shimura lift, and its unfolding along
  geodesics) besides the trace identity. The Petersson products are Kohnen and Zagier's normalizations.
- **Tunnell with the true $`L`$-function** (`congruent_*_trueL`): the cited theorems `WaldspurgerSquareClassFull`,
  `TunnellEigenforms`, `TunnellConstants` and `CoatesWilesCM` are assumed. Coates–Wiles is stated for curves whose
  $`j`$-invariant is one of the nine values of the maximal orders of class number one, which over $`\mathbb Q`$ is
  complex multiplication by a maximal order (this characterization is not formalized). The converse needs, for each $`E_n`$, the Birch and
  Swinnerton-Dyer conjecture (open). $`L(E_n, 1)`$ is the value at $`1`$ of every continuation of the $`L`$-series to
  a connected open set containing $`1`$.
- **Shimura's theorem** (`shimuraLift_theta_of_frickeKernel`): conditional on `ShimuraFrickeKernelUnfolding`, assumed;
  only for the theta multiplier and $`k \ge 2`$ (weight $`5/2`$ and up: weight $`3/2`$ has no lift here).
- **Historical** (new in 0.5.0): $`\tau(n)`$ is defined as a coefficient of the formal power series
  $`x\prod(1 - x^n)^{24}`$, $`p(n)`$ as the number of Mathlib's partitions of $`n`$; their identification with the
  coefficients of Mathlib's discriminant form is not part of the headlines. Jacobi's quartic identity is for Weber's
  theta constants, defined as values of Mathlib's `jacobiTheta₂`.

Of the headlines new in 0.4.0:

- **Theta series with spherical functions** (`thetaSpherical_even`, `thetaSpherical_odd`): the spherical functions are
  the powers $`(\langle u, x\rangle + i\langle w, x\rangle)^\nu`$ with $`u + iw`$ isotropic (or $`\nu \le 1`$); these
  span the harmonic polynomials of degree $`\nu`$, but the spanning theorem is not formalized, so a general harmonic
  $`P`$ needs a linear combination. The statements are in lattice form (a lattice in a Euclidean space, its level and
  theta character); the bridge to Miyake's matrix form (Gram matrix $`A`$, level $`N`$, characteristic $`h`$) is not
  formalized. In odd rank the level is $`4N`$ with $`N`$ the level of the lattice, and the character
  (`oddThetaChar`) is not identified with Miyake's formula. Corollary 4.9.5 (1)–(2) and 4.9.7 (2) are not proved.
  (Since 0.5.0 the library has Theorem 4.9.3, Corollary 4.9.4 and Corollary 4.9.5 (3) in Gram-matrix form for the
  trivial spherical function, with the odd-rank character $`(2\det H/\cdot)`$, and Corollary 4.9.7 (2); not as
  headlines, except through `thetaGenus_*`.)
- **Hecke's continuation and limits** (`heckeEisenstein_continuation`, `heckeLimit_weightTwo`,
  `heckeLimit_weightOne`): the continuation is given by the library's Fourier expansion (`eisensteinCharSCont`), and
  Hecke's limit by the predicate `IsHeckeLimit`; the normalizations are the library's reading of Miyake's (7.2.1)
  and (7.2.12).
- **Hecke's lemma** (`hecke_lemma`): for $`k > 0`$ (Miyake's proof uses it; for $`k = 0`$ constants are
  counterexamples), with Mathlib's slash operator, which differs from Miyake's by a nonzero constant.
- **Shimura's theorem** (`shimuraLift_theta_of_dualUnfolding`): conditional on `ShimuraDualUnfolding`, assumed; only
  for the theta multiplier; Niwa's level $`2N`$ is not proved.
- **Hecke's functional equation and the unfolding** (`eisensteinLattice_functionalEquation`, `rankin_unfolding`): the
  normalizations (Hecke's, for the lattice $`L\mathbb Z \times \mathbb Z`$) are the library's; their constants were
  checked numerically, not against a source.
- **Riemann–Roch** (`riemannRoch`): as Milne states it, with "an integer $`g \ge 0`$"; that $`g`$ is the dimension of
  the space of holomorphic differentials is Corollary 1.21, proved in the library but not part of the headline.
  Theorem 0.5 (c) (isomorphic function fields give isomorphic surfaces) is not proved.
- **The dimension and genus formulas** (`dimensionFormula`, `genusFormula`): the genus is the analytic genus (the
  dimension of the holomorphic differentials on $`X(\Gamma)`$); the dimension formula is for even weights $`2k`$,
  $`k \ge 1`$, as in Milne.
- **Not a headline: Miyake's Theorem 4.8.2** (forms from Hecke characters of imaginary quadratic fields) is stated in
  corrected form, not proved; the form stated in 0.3.1 is refuted in the library (an erratum of the library, not of
  the book).

Of the headlines new in 0.3.1:

- **Proposition 12.21** (`classGroupAction_ellCM`): the statement asserts a map
  $`\mathrm{Pic}(O) \times \mathrm{Ell}_k(O) \to \mathrm{Ell}_k(O)`$ compatible with $`\mathfrak a`$-isogenies whose
  orbit maps are bijective; that it is a group action is not stated (Milne says "acts simply transitively"). The
  complex multiplication is normalized (the library's corrected form of Milne's statement; see the errata).
- **Proposition 11.5** (`betti_tate_comparison`): $`H_1(E, \mathbb Z)`$ and the tangent space at $`0`$ are modelled by
  the lattice $`\Lambda`$ and by $`\mathbb C`$ through the complex uniformization, as in Milne's proof; singular
  homology is not used.
- **The conductor exponent** (`conductor_exponent_eq_two_iff`): the conductor is Tau Ceti's, defined by Tate's
  algorithm; Ogg's formula, which identifies it with the conductor of the $`\ell`$-adic representation, is not
  formalized; $`p = 2, 3`$ are not treated.
- **Theorem 4.5.4 (2)** (`hecke_adjoint_heckeTStar`): Miyake's $`T^*(n)`$ is defined by his formula (4.5.16) as a sum of
  the double cosets $`T^*(m, l)`$, not as the sum of all double cosets of determinant $`n`$ (the analogue of Lemma
  4.5.2 for $`\Delta_0^*(N)`$ is not formalized), and only on cusp forms.
- **Jacobi** (`jacobi_modular_equation_ode`, `jacobi_theta_fourier`): the equation is proved for any two solutions
  $`A`$, $`B`$ of Legendre's equation; that the complete elliptic integrals $`K`$, $`K'`$ are such solutions, and that a
  modular equation of order $`n`$ is the relation $`\Lambda'/\Lambda = nK'/K`$, are not formalized, and $`\lambda`$ is
  assumed three times continuously differentiable. $`\Theta`$ and $`H`$ are defined as values of Mathlib's theta
  series; their identification with Jacobi's analytic definitions is not formalized.
- **Kronecker** (`kronecker_ser_transformation`): only for $`\rho \ge 2`$, where the series converges absolutely and the
  law is a rearrangement; the cases $`\rho = 0, 1`$ (conditionally convergent square limits) are not proved.

Of the headlines new in 0.3.0:

- **Class number one:** the eight inputs of `WeberHeegnerStarkInputs` (the theory of complex multiplication) are
  assumed; two of them are proved in Tau Ceti for its own definitions but not connected here.
- **Waldspurger's sign patterns:** the local packets of the metaplectic group are not constructed. The local data
  (discreteness, fixed-vector dimensions, local root numbers, the twisted signs) are parameters (`LocalData`,
  `TwistData`); the unconditional headlines hold for all such data, and their link with representations is the
  content of the named inputs.
- **The inputs `WaldspurgerCoefficients` and `WaldspurgerFibreDimension`** are stated for these abstract data; the
  predicate "the $`t`$-th coefficient of $`\sigma_\varepsilon`$ is nonzero" is a parameter. The theorems drawn from
  them are short consequences: their content is the combinatorics above.
- **`KohnenSquarefree` and `WaldspurgerSquareClass`** are hypotheses on coefficient sequences and on entire
  continuations of the twisted $`L`$-series, not on functions constructed in the library; Kohnen's Petersson quotient
  is an unspecified positive constant (the Petersson product at level $`4N`$ is not constructed), and
  `WaldspurgerSquareClass` is restricted to quadratic characters and to $`n`$ prime to $`4N`$.
- **Gross's example:** only $`p = 11`$. The ternary forms and the Brandt matrices are entered explicitly; that they
  come from the maximal orders and that the Shimura lift of $`g`$ is the newform of level $`11`$ are not proved in
  Lean. (Since 0.5.0, that $`g`$ is a cusp form of weight $`3/2`$ and level $`44`$ in Kohnen's plus space is proved:
  `gross_form_mem_plusCuspForms`.)
- **Tunnell:** $`L(E_n, 1)`$ is an abstract function in these headlines (the headlines new in 0.5.0 use the true
  $`L`$-function); Tunnell's formula and the theorem of Coates and Wiles are assumed; the converse direction needs the
  weak Birch and Swinnerton-Dyer conjecture.
- **Locators:** the theorem numbers cited from the papers of Waldspurger, Kohnen, Gross, Tunnell and Coates–Wiles
  have not been checked against the papers; the normalizations were checked numerically.

**Main statements.** To check what is claimed, read the fourteen files [`Challenge_Milne.lean`](Challenge_Milne.lean),
[`Challenge_MilneArithmetic.lean`](Challenge_MilneArithmetic.lean), [`Challenge_Miyake.lean`](Challenge_Miyake.lean), [`Challenge_Shimura.lean`](Challenge_Shimura.lean),
[`Challenge_Iwaniec.lean`](Challenge_Iwaniec.lean),
[`Challenge_AndrianovZhuravlev.lean`](Challenge_AndrianovZhuravlev.lean) (one per book), and
[`Challenge_HeegnerStark.lean`](Challenge_HeegnerStark.lean), [`Challenge_Waldspurger.lean`](Challenge_Waldspurger.lean),
[`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean),
[`Challenge_Historical.lean`](Challenge_Historical.lean), [`Challenge_RankinSelberg.lean`](Challenge_RankinSelberg.lean),
[`Challenge_EllipticCurves.lean`](Challenge_EllipticCurves.lean), [`Challenge_ThetaGenus.lean`](Challenge_ThetaGenus.lean) and
[`Challenge_KohnenPlusSpace.lean`](Challenge_KohnenPlusSpace.lean) (one per topic, with the conditional theorems): they state the results above, with a
docstring for each and a list of the library definitions the statements use; every proof there is a deliberate
`sorry`. The matching `Solution_<book>.lean` files prove the same statements by appeal to the library theorems, and
`lake comparator`, configured per book by `comparator/<book>.json` (the books are listed in
[`comparator.json`](comparator.json)), checks that each proved statement is exactly the one in the challenge file and
uses only the standard axioms. The check is run one book (or topic) at a time: each needs only the files of its book.
[`formalization.yaml`](formalization.yaml) records the scope, sources, divergences from the literature, provenance and
review status in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

**Corrections to the books** found while formalizing them (statements false as written, with the corrected form the
library proves) are listed in [docs/updates-and-errata.md](docs/updates-and-errata.md).

## Layout

```
Challenge_<book>.lean   the headline statements of one book or topic (proofs: deliberate sorry);
                        <book> = Milne (sections 0-10), MilneArithmetic (sections 11-12), Miyake, Shimura,
                        Iwaniec, AndrianovZhuravlev (books), HeegnerStark, Waldspurger, CongruentNumbers,
                        Historical, RankinSelberg, EllipticCurves, ThetaGenus, KohnenPlusSpace (topics)
Solution_<book>.lean    the same statements, proved from the library
MapNameDeps.lean        imports the Tau Ceti and Mathlib modules of names cited by the maps (for the name check)
comparator.json         the books, each with its lake comparator configuration comparator/<book>.json
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/results/books/     the book maps and statement maps; docs/results/comparison.md: comparison with Mathlib and
                        Tau Ceti
docs/updates-and-errata.md  corrections to the books
ModularFormsKB/
  Milne/                Milne, Modular Functions and Modular Forms: Ch0/ ... Ch12/ by section;
                        RiemannSurface/, RS/: Riemann surfaces (Section 1 and supporting results);
                        Wave4A/, Wave4B/: the genus of X(Gamma), Riemann-Roch on the sphere and X(1), Sections 11-12;
                        Wave5/ ... Wave10/: complex multiplication (Section 12), Proposition 11.5, the conductor,
                        the little Picard theorem, modular curves X(Gamma) (Sections 1-2);
                        Wave11/ ... Wave15/: Riemann-Roch on X(Gamma) and on every compact Riemann surface (the
                        existence theorem), the dimension and genus formulas, line bundles on H
  Miyake/               Miyake, Modular Forms (Chapters 1-7; Sec4_3/: L-functions and Weil's theorem;
                        Wave2A/, Wave2B/, Wave3/: further items of Chapters 1-7; Wave4/ ... Wave13/: Hecke algebras
                        and operators, primitive forms, the operators eta_q, Eisenstein spaces (Sections 4.1, 4.3,
                        4.5-4.7); Sec3_1/, Sec3_3/, Sec4_5/, Sec4_6/, Sec4_8/, Sec6_7/: single items;
                        Sec4_9/: theta series with spherical functions; HeckeTrick/: Hecke's method, Section 7.2)
  Dimension/            the Sturm bound and dimension bounds for Gamma_0(N), Gamma_1(N) and a character
  Shimura2007/          Shimura, Elementary Dirichlet Series and Modular Forms (statements, Sections 1-4, 6, 16)
  Iwaniec1997/          Iwaniec, Topics in Classical Automorphic Forms (statements, Chapters 3-5, 9-10)
  Andrianov/            Andrianov and Zhuravlev, Modular Forms and Hecke Operators (statements, Chapters 1-4)
  Historical/WeberHeegnerStark/  the class number one theorem, conditional: Inputs.lean (the named inputs),
                        Defs.lean, Forms.lean, Heegner.lean, CubicField.lean, Diophantine.lean, Numerics.lean,
                        QuadraticField.lean, Main.lean
  Historical/Jacobi/, Historical/Ramanujan/, Historical/Weber/, Historical/Kronecker/, Historical/Eisenstein/,
  Historical/Smith/     theorems of the original papers (one Lean library per author; Mathlib modules, a few
                        Tau Ceti modules and a few supporting files of this library)
  HalfIntegral/         half-integral weight forms, theta series and the Shimura lift (supporting files, used by
                        Iwaniec1997/, Miyake/ and Waldspurger/)
  HalfIntegral/Rankin/  the Rankin-Selberg unfolding and Shimura's theorem for the theta multiplier
  HalfIntegral/Waldspurger/  Waldspurger's theorems: Packets.lean (sign patterns), Coefficients.lean (square
                        classes, Kohnen's formula, the fibre), Gross.lean (p = 11), Tunnell.lean (congruent numbers);
                        CongruentCurves/: the true L-function of y^2 = x^3 - n^2 x, f_32, Tunnell's theorem with it
  HalfIntegral/Kohnen*.lean, PlusHecke*.lean, Abstract/Kohnen*.lean  Kohnen's plus space, his isomorphism and the
                        Kohnen-Zagier formula; HalfIntegral/ZagierKernel/: Zagier's kernel and Shintani's lift
  RankinSelberg/        the Rankin-Selberg method at level one and the symmetric square L-function
  Elliptic/             elliptic curves with a newform: functional equation, parity, strong Hasse-Weil, Weil's converse
  ThetaGenus/           theta series of quadratic forms in Gram-matrix form; one genus gives a cusp form; Gross's form
  Citation.lean         the @[kb] citation attribute
references.bib          bibliography; the keys used by @[kb]
scripts/check_axioms.lean  prints the axioms of the headline theorems (run in CI)
scripts/check_map_names.lean, check_also_in.lean  check that the Lean names of the maps exist
scripts/verify-comparator.sh  runs lake comparator for one book with the toolchain's kernels (run in CI)
.github/workflows/build.yml  the CI workflow (build, axioms, map names, one comparator check per book)
```

No file of the library imports all of Mathlib: every file imports the Mathlib and Tau Ceti modules it uses.

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean   # axioms of the headline theorems
./scripts/verify-comparator.sh Milne      # Solution_Milne against Challenge_Milne (Linux; needs bubblewrap);
                                          # likewise MilneArithmetic, Miyake, Shimura, Iwaniec,
                                          # AndrianovZhuravlev, HeegnerStark, Waldspurger,
                                          # CongruentNumbers, Historical, RankinSelberg,
                                          # EllipticCurves, ThetaGenus, KohnenPlusSpace
```

Mathlib comes prebuilt from its cache; Tau Ceti and this library are built from source (about 22,600 build jobs
besides Mathlib's cache; no file imports all of Mathlib, so only the parts of Tau Ceti that the library uses are
built). A cold build took about 63 minutes on 8 cores (2026-11-16), with at most 8.2 GB of memory in use besides the
page cache and a largest single Lean process of 8.0 GB. One `lake comparator` check per book or topic (build, export,
and the Lean, NanoDa and con-ron kernels; measured without the bubblewrap sandbox, 2026-11-16): Milne, sections 0–10,
31 minutes, at most 9.2 GB in use (largest process `leanexport`, 7.5 GB; most of the time is Lean's own kernel);
Milne, sections 11–12, 20 minutes, 6.5 GB; Miyake 12.5 minutes, 4.9 GB; Shimura 5 minutes, 3.2 GB; Iwaniec 1.2
minutes, 1.8 GB; Andrianov–Zhuravlev 2.7 minutes, 2.4 GB; Heegner–Stark 7 minutes, 6.8 GB (largest process `con-ron`,
4.3 GB); Waldspurger 12 minutes, 4.8 GB; congruent numbers 18 minutes, 9.3 GB (largest process `leanexport`, 6.2 GB);
historical theorems 6.5 minutes, 3.7 GB; Rankin–Selberg 7.3 minutes, 3.8 GB; modular elliptic curves 20 minutes,
5.7 GB; theta series in one genus 9 minutes, 4.1 GB; Kohnen's plus space 10.5 minutes, 4.5 GB. GitHub's standard
runner has 4 cores and 16 GB; the CI workflow adds swap space and saves partial builds, so a first run may need to be
re-run to finish.

## Provenance

ModularFormsKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by
Claude Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the
results, the conventions and the proof routes. The proofs are checked by the Lean kernel, and CI checks that the
headline theorems use only the standard axioms. The 107 headline statements of this release in the
`Challenge_<book>.lean` files, and the definitions they use, have **not yet been reviewed** by a human; that review is
planned for a later release. `lake comparator` checks that each `Solution_<book>.lean` proves exactly the statements
of its `Challenge_<book>.lean`. The rest of the library (its other definitions and intermediate results, and the
maps) has not been reviewed by a human; as with any AI-written formalization, treat it as untrustworthy until checked
against the literature. Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.24069385](https://doi.org/10.5281/zenodo.24069385) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **[v0.5.0](https://github.com/jonhanke/modular-forms-lean/releases/tag/v0.5.0)** (Lean v4.36.0-rc2, Mathlib `e8ba86f`, Tau Ceti `1ff5324`), archived on Zenodo as [doi:10.5281/zenodo.24289630](https://doi.org/10.5281/zenodo.24289630): twenty-eight new headlines (107 in all, the 79 of v0.4.0 kept) and four new challenge files (fourteen in all): the Rankin–Selberg method at level one, with the Petersson norm of a normalized eigenform as a value of its symmetric square $`L`$-function (`Challenge_RankinSelberg.lean`); elliptic curves with a newform, their functional equation, parity and Milne's strong Hasse–Weil conjecture, the newforms of the congruent number curves $`E_1`$ (level 32) and $`E_n`$, $`n`$ odd squarefree (level $`32n^2`$), and for every elliptic curve over $`\mathbb Q`$ conditional on the modularity theorem (`Challenge_EllipticCurves.lean`); theta series of quadratic forms in one genus differ by a cusp form, in every rank, and Gross's form of level 11 lies in Kohnen's plus space (`Challenge_ThetaGenus.lean`); the self-adjointness of $`T(p^2)`$ on Kohnen's plus space, and, conditional on named inputs, Kohnen's isomorphism (from Kohnen's trace identity alone), the Kohnen–Zagier formula, Waldspurger's theorem on the plus space and $`L(F, D, k) \ge 0`$ (`Challenge_KohnenPlusSpace.lean`); the modularity of the congruent number curves with an entire $`L`$-function, and Tunnell's theorem with the true $`L`$-function, conditional on cited theorems only; Shimura's theorem for the theta multiplier conditional on a smaller input; and Jacobi's cube and quartic identities, Ramanujan's congruences for $`p(n)`$ and $`\tau(n)`$ and his Question 387, Weber's $`\mathfrak f^8 = \mathfrak f_1^8 + \mathfrak f_2^8`$ and an identity of Kronecker for $`E_2`$. Tau Ceti pin moved to Tau Ceti main; book maps regenerated (Milne 179 rows proved and 19 in part, was 178 and 18; Miyake 106 proved and 41 in part, was 105 and 40; the Waldspurger statement map has 22 rows, was 17).
- **[v0.4.0](https://github.com/jonhanke/modular-forms-lean/releases/tag/v0.4.0)** (Lean v4.36.0-rc2, Mathlib `e8ba86f`, Tau Ceti `ca32605`), archived on Zenodo as [doi:10.5281/zenodo.24257645](https://doi.org/10.5281/zenodo.24257645): sixteen new headlines (79 in all, the 63 of v0.3.1 kept): for Milne, the existence theorem and the Riemann–Roch theorem on every compact Riemann surface, the dimension and genus formulas for every subgroup of finite index of $`\mathrm{SL}_2(\mathbb Z)`$, and the triviality of holomorphic line bundles on $`\mathbb H`$; for Miyake, theta series with spherical functions in every rank (Theorem 4.9.3, Corollary 4.9.4, half-integral weight for odd rank), Shimura's twisted theta law for every character, Hecke's continuation of Eisenstein series in $`s`$ and his limits in weights two and one (Theorems 7.2.9, 7.2.12, 7.2.13), and Hecke's lemma; Hecke's functional equation of the lattice Eisenstein series and the Rankin–Selberg unfolding, and Shimura's theorem for the theta multiplier conditional on one named input (`ShimuraDualUnfolding`); the Jacobi triple product, with which Weber's formulas $`\vartheta = \eta\,\mathfrak f^2`$ become unconditional. Milne's headlines are split into two challenge files (sections 0 to 10, and 11 and 12), ten in all. Mathlib and Tau Ceti pins moved to Tau Ceti main; book maps regenerated (Milne 178 rows proved and 18 in part, was 170 and 22; Miyake 105 proved and 40 in part, was 83 and 41).
- **[v0.3.1](https://github.com/jonhanke/modular-forms-lean/releases/tag/v0.3.1)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`, Tau Ceti `4908b03`), archived on Zenodo as [doi:10.5281/zenodo.24223180](https://doi.org/10.5281/zenodo.24223180): what was finished since v0.3.0. Eleven new headlines (63 in all, the 52 of v0.3.0 unchanged): for Milne, the little Picard theorem (Remark 2.25), Proposition 12.21 (the class group of an imaginary quadratic order acting on the $`j`$-invariants with complex multiplication, over every algebraically closed field of characteristic zero), Proposition 11.5 (the Betti, $`\ell`$-adic and tangent representations of an elliptic curve over $`\mathbb C`$) and the conductor exponent $`2`$ at additive primes $`p \ne 2, 3`$; for Miyake, Theorem 4.5.9 (the Hecke ring of $`\Gamma_0(N)`$ is a polynomial ring) and Theorem 4.5.4 (2) ($`T(n)`$ and $`T^*(n)`$ are adjoint for every $`n`$); and a ninth challenge file, `Challenge_Historical.lean`, with theorems of Jacobi, Ramanujan, Weber (conditional on the Jacobi triple product) and Kronecker, and its statement map. The book maps of Milne (170 rows proved and 22 in part, was 155 and 28) and Miyake (83 proved and 41 in part, was 56 and 29) are regenerated; the other statement maps are unchanged.
- **[v0.3.0](https://github.com/jonhanke/modular-forms-lean/releases/tag/v0.3.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`, Tau Ceti `4908b03`), archived on Zenodo as [doi:10.5281/zenodo.24184587](https://doi.org/10.5281/zenodo.24184587): conditional
  theorems, of the form *(named inputs) → statement*, in a new section [Conditional theorems](#conditional-theorems):
  the class number one theorem of Heegner and Stark (the imaginary quadratic fields of class number one are
  $`\mathbb Q(\sqrt{-d})`$, $`d \in \{1, 2, 3, 7, 11, 19, 43, 67, 163\}`$), proved from eight named classical inputs
  (Weber's class invariants, Dirichlet and Dedekind), in two forms (`Challenge_HeegnerStark.lean`); Waldspurger's
  theorems and the Shimura lift (`Challenge_Waldspurger.lean`, `Challenge_CongruentNumbers.lean`): unconditionally,
  the combinatorics of Waldspurger's sign patterns and of the fibre dimension, Kohnen's plus space as a sign pattern,
  Gross's weight $`3/2`$ form and Brandt matrices for $`p = 11`$, congruent numbers and the curve
  $`y^2 = x^3 - n^2x`$, explicit congruent triangles; conditionally on named inputs (Waldspurger 1981 and 1991,
  Kohnen 1985, Gross 1987, Tunnell 1983, Coates and Wiles 1977), consequences such as nonnegativity of central values
  and that $`1`$, $`3`$, $`11`$ are not congruent; and, conditional on the weak Birch and Swinnerton-Dyer conjecture,
  Tunnell's criterion as an equivalence. A statement map for the six papers, a list of known restrictions, and three
  new challenge files, one per topic (52 headlines in all, the 17 of v0.2.0 unchanged); the other book and statement maps
  unchanged except Milne's Proposition 8.2, now proved (the map had listed a predicate as an input).
- **[v0.2.0](https://github.com/jonhanke/modular-forms-lean/releases/tag/v0.2.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`, Tau Ceti `4908b03`), archived on Zenodo as [doi:10.5281/zenodo.24121513](https://doi.org/10.5281/zenodo.24121513): statement maps, a new kind of map, for
  three more books: Shimura, *Elementary Dirichlet Series and Modular Forms* (12 central results stated in Lean;
  3 proved, 6 in part), Iwaniec, *Topics in Classical Automorphic Forms* (28; 6 proved, 2 in part, 2 conditional) and
  Andrianov–Zhuravlev, *Modular Forms and Hecke Operators* (26; 12 proved, 3 in part, 1 conditional); refreshed book
  maps of Milne (154 rows proved and 28 in part, was 147 and 21: the genus of $`X(\Gamma)`$ when the genus formula
  gives $`0`$, Riemann–Roch on the sphere and on $`X(1)`$, the valence and dimension formulas for some groups) and
  Miyake (56 proved and 29 in part, was 22 and 9: items of Chapters 1 to 7, among them the Fourier expansion of
  $`E_k(z;\chi,\psi)`$ and the decomposition $`M_k = S_k \oplus N_k`$); five new headlines, in four new challenge
  files: one `Challenge_<book>.lean` per book, checked one book at a time by `lake comparator` (17 headlines in all,
  the 12 of v0.1.0 unchanged); no file imports all of Mathlib.
- **[v0.1.0](https://github.com/jonhanke/modular-forms-lean/releases/tag/v0.1.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`, Tau Ceti `4908b03`), archived on Zenodo as [doi:10.5281/zenodo.24069386](https://doi.org/10.5281/zenodo.24069386): the first release: the book maps of Milne
  and Miyake and 12 headline statements.

**Not in this release** (planned for a later release): the rest of the half-integral weight library (Zagier's
Eisenstein series, Kohnen's newform theory) beyond the files used by the headlines, Hurwitz class numbers and mock
modular forms; the items of Shimura, Iwaniec and Andrianov–Zhuravlev not yet stated; proofs of the named inputs of the
conditional theorems (the theory of complex multiplication; Waldspurger's theorems; the unfolding in Shimura's proof;
Kohnen's trace identity and Zagier's kernel; the modularity theorem). This release is standalone: it does not depend
on the algebraic number theory library
[algebraic-number-theory-lean](https://github.com/jonhanke/algebraic-number-theory-lean), which is on a different
Mathlib; the [comparison](docs/results/comparison.md) lists the results the two libraries share.

## License

Apache License 2.0; see [LICENSE](LICENSE).
