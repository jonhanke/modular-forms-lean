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
patterns, Gross's example for the prime $`11`$ and the elementary theory of congruent numbers. The Lean library is
called `ModularFormsKB`.

## What's new in 0.3.0

- **A new section, [Conditional theorems](#conditional-theorems)**, and a sixth challenge file,
  [`Challenge_HeegnerStark.lean`](Challenge_HeegnerStark.lean): the imaginary quadratic fields of class number one are
  exactly $`\mathbb Q(\sqrt{-d})`$ for $`d \in \{1, 2, 3, 7, 11, 19, 43, 67, 163\}`$, proved in Lean from eight named
  classical inputs (Weber, Dirichlet, Dedekind), each a field of a Lean `Prop` structure with its source. The theorem
  has the form *(named inputs) → statement*; `#print axioms` shows only the standard axioms. Everything else in
  Heegner's proof is proved: Gauss's reduction, Heegner's step from Weber's class invariants to a Diophantine
  equation, that equation's integer points, and a certified numerical enclosure of $`j`$.
- **Waldspurger's theorems and the Shimura lift**, in two more challenge files (one per topic):
  [`Challenge_Waldspurger.lean`](Challenge_Waldspurger.lean) (24 headlines) and
  [`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean) (9 headlines). *Unconditional:* the
  combinatorics of Waldspurger's admissible sign patterns (1991) and of the dimension of the fibres of the Shimura
  correspondence, Kohnen's plus space as a sign pattern, Gross's weight $`3/2`$ form for $`p = 11`$ with its Brandt
  matrices, the equivalence "$`n`$ is congruent if and only if $`y^2 = x^3 - n^2x`$ has a rational point with
  $`y \ne 0`$", and explicit congruent triangles ([Highlights](#highlights)). *Conditional on named inputs*
  (Waldspurger 1981 and 1991, Kohnen 1985, Gross 1987, Tunnell 1983, Coates and Wiles 1977): one constant per square
  class, nonnegativity of central values, multiplicity one in the plus space, Gross's vanishing criterion, and the
  half of Tunnell's criterion that shows $`1`$, $`3`$ and $`11`$ are not congruent; and, *separately, conditional on
  the weak Birch and Swinnerton-Dyer conjecture*, Tunnell's criterion as an equivalence
  ([Conditional theorems](#conditional-theorems)). A new statement map lists the results of the six papers stated in
  Lean ([docs/results/books/waldspurger.md](docs/results/books/waldspurger.md)).
- **[Known restrictions](#known-restrictions)** of the new headlines.
- The book maps of Milne, Miyake and the dimension bounds and the statement maps of Shimura, Iwaniec and
  Andrianov–Zhuravlev are regenerated. One status changed: Milne's Proposition 8.2 (a moduli problem has at most one
  solution up to unique isomorphism) is now *proved*; 0.2.0 listed it as conditional on the definition of a solution,
  which is a condition of the statement, not an assumed result (Milne: 155 rows proved, was 154). The 17 headlines of
  0.2.0 are unchanged (52 headlines in all).

- **Book maps**: for Milne and Miyake, a table from every item (theorem, proposition, lemma, corollary, definition) to
  the Lean declaration that formalizes it and its status: [docs/results/books/](docs/results/books/README.md).
- **Statement maps**: for Shimura, Iwaniec and Andrianov–Zhuravlev, and for the papers on Waldspurger's theorems,
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
| [J. S. Milne, *Modular Functions and Modular Forms* (version 1.31)](docs/results/books/milne-mf.md) | 293 | 155 | 28 | 15 | 44 | 23 | 4 | 24 | 29 |
| [T. Miyake, *Modular Forms* (Springer, 1989)](docs/results/books/miyake.md) | 279 | 56 | 29 | 0 | 2 | 21 | 46 | 125 | 2 |
| [Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)](docs/results/books/dimension.md) | 22 | 21 | 0 | 0 | 1 | 0 | 0 | 0 | 12 |

*Proved*: proved with only the standard axioms and no unproved input. *Other*: refuted as stated, stated without proof, formalized in the source library but not in this release, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) in this library whose result, or a part of it, is also proved in Mathlib, Tau Ceti or the Stacks Project formalization (Axiom); each map names the declarations in its column *Also in*. Rows that are not results are omitted from the maps.

**Statement maps** (a first statement wave: the central results stated in Lean, each marked proved or stated):

| book | rows | proved | proved in part | conditional | stated, not proved |
|---|---|---|---|---|---|
| [G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer, 2007)](docs/results/books/shimura2007.md) | 12 | 3 | 6 | 0 | 3 |
| [H. Iwaniec, *Topics in Classical Automorphic Forms* (American Mathematical Society, 1997)](docs/results/books/iwaniec1997.md) | 28 | 6 | 2 | 2 | 18 |
| [A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (American Mathematical Society, 1995)](docs/results/books/andrianovzhuravlev1995.md) | 26 | 12 | 3 | 1 | 10 |
| [Waldspurger's theorems, the Shimura lift, Gross's example for $p = 11$ and Tunnell's theorem (papers of Waldspurger 1981 and 1991, Kohnen 1985, Gross 1987, Tunnell 1983, Coates and Wiles 1977)](docs/results/books/waldspurger.md) | 17 | 7 | 0 | 8 | 2 |

## Highlights

Every result listed here is a headline theorem of a `Challenge_<book>.lean` file: it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input. Headlines are only results that are in neither Mathlib
nor Tau Ceti (main branch, checked on 2026-11-10 for the headlines new in 0.2.0 and on 2026-11-12 for those new in
0.3.0), or that are stronger here
([comparison](docs/results/comparison.md)). One of them, Weil's Riemann hypothesis for curves, is also proved in the
Stacks Project formalization by Axiom, in another form; it is labelled below. Related results of other libraries are
cited next to the headlines, and the book maps credit, in their column *Also in*, every result proved here that is
also proved in Mathlib, Tau Ceti or the Stacks Project formalization. The statements have **not yet been reviewed by
a human** (see Provenance).

**Milne, *Modular Functions and Modular Forms*** ([`Challenge_Milne.lean`](Challenge_Milne.lean))

- **Weil's Riemann hypothesis for curves over finite fields:** for a function field $`F`$ of one variable over $`\mathbb F_q`$, $`\mathbb F_q`$ algebraically closed in $`F`$, of genus $`g`$, there are algebraic integers $`\alpha_1, \dots, \alpha_{2g}`$ with $`N_n = 1 + q^n - \sum \alpha_i^n`$ for every $`n \ge 1`$, permuted by $`\alpha \mapsto q/\alpha`$, and $`|\alpha_i| = \sqrt q`$ (`weil_riemannHypothesis_curves`, Theorem 11.4; Tau Ceti has the genus-one case). *Also proved in the Stacks Project formalization (Axiom), in étale-cohomological form (tag 03V8, Bombieri–Stepanov); ours is the function-field form of Milne 11.4 and includes the functional equation* (the Stacks match is from its declaration index; see the [comparison](docs/results/comparison.md)).
- **Kronecker's modular equation, for every level $`N`$:** $`\mathbb C(X_0(N)) = \mathbb C(j, j_N)`$, and the minimal polynomial of $`j(Nz)`$ over $`\mathbb C(j)`$ has degree $`[\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]`$ and is $`F_N(j, Y)`$ with $`F_N \in \mathbb Z[X, Y]`$, symmetric for $`N > 1`$, and $`F_p \equiv X^{p+1} + Y^{p+1} - X^pY^p - XY \pmod p`$ (`kronecker_modularEquation`, Theorem 6.1).
- **Singular moduli are algebraic integers:** $`j(z)`$ is an algebraic integer for every imaginary quadratic $`z \in \mathbb H`$ (`j_isIntegral_of_imaginaryQuadratic`, Corollary 12.16).
- **Elliptic functions:** on a fundamental parallelogram the orders and the residues of an elliptic function sum to $`0`$ and $`\sum \operatorname{ord}_P(f)P \in \Lambda`$ (`doublyPeriodic_sums`, Proposition 3.1); an elliptic function with prescribed zeros and poles exists when their sums agree modulo $`\Lambda`$, and is unique up to a constant (`prescribedDivisor`, Theorem 3.8); every elliptic function is a rational function of $`\wp`$ and $`\wp'`$ (`ellipticFunctionField`, Proposition 3.11).
- **Moduli of elliptic curves:** over an algebraically closed field, the $`j`$-line solves the moduli problem of elliptic curves (`ellipticModuli_jLine`, Theorem 8.4), and the moduli problem of elliptic curves with a cyclic subgroup of order $`N`$ has a solution for every $`N`$ prime to the characteristic (`cyclicModuli`, Theorem 8.6). Related results: Tau Ceti's fine moduli scheme $`Y_1(N)`$, $`N \ge 4`$ (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne`), on which the proof of Theorem 8.6 for $`N \ge 4`$ is built, and the algebraic moduli stack $`\mathcal M_{1,1}`$ of the Stacks Project formalization (Axiom; Tag 072R, index match).
- **The modular curves $`X(N)`$, $`N = 2, 3, 4, 5`$, have genus zero:** every holomorphic differential on the compact Riemann surface $`X(N) = \Gamma(N)\backslash\mathbb H^*`$ is zero (`modularCurveX_Gamma_genus_eq_zero`, Example 2.23; new in 0.2.0). Related: Tau Ceti (main) proves the Riemann–Hurwitz formula for Fuchsian groups in Euler-characteristic form, under finite-CW-type hypotheses.

**Miyake, *Modular Forms*** ([`Challenge_Miyake.lean`](Challenge_Miyake.lean))

- **Hecke's theorem:** for coefficients of polynomial growth, $`g = f|_k\omega_N`$ if and only if $`\Lambda_N(s; f)`$ and $`\Lambda_N(s; g)`$ continue to the plane, with $`\Lambda_N(s; f) = i^k\Lambda_N(k - s; g)`$ and the usual polar parts, bounded on vertical strips (`hecke_converse`, Theorem 4.3.6); at level one, $`\sum a_n q^n`$ is a modular form of weight $`k`$ if and only if its $`L`$-function has this analytic behaviour (`hecke_converse_levelOne`, Theorem 4.3.8). The forward direction for cusp forms (the Fricke relation gives the functional equation) is in Tau Ceti (`CuspForm.frickeCompletedL_functional_equation`); the converse direction is new here.
- **Weil's converse theorem:** if $`L(s; f)`$, $`L(s; g)`$ and their twists by the primitive characters of conductor in a suitable set of primes satisfy the functional equations with Weil's constant, then $`f \in M_k(N, \chi)`$, $`g \in M_k(N, \bar\chi)`$ and $`g = f|_k\omega_N`$ (`weil_converse`), and $`f`$, $`g`$ are cusp forms when $`L(s; f)`$ converges absolutely at $`k - \delta`$ (`weil_converse_cusp`, Theorem 4.3.15).

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

Neither Mathlib (at the pinned commit) nor Tau Ceti (main, checked on 2026-11-12) has half-integral weight forms, Waldspurger's theorems or Brandt matrices.

**Congruent numbers** ([`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean)) (new in 0.3.0; Tunnell's criterion is in [Conditional theorems](#conditional-theorems))

- **Congruent numbers and the curve $`y^2 = x^3 - n^2x`$:** a positive integer $`n`$ is the area of a right triangle with rational sides if and only if $`E_n : y^2 = x^3 - n^2x`$ has a rational point with $`y \ne 0`$ (`congruent_isCongruent_iff_point`).
- **Explicit congruent triangles:** $`5`$, $`6`$, $`7`$ and $`41`$ are congruent, by the triangles $`(3/2, 20/3, 41/6)`$, $`(3, 4, 5)`$, $`(24/5, 35/12, 337/60)`$ and $`(40/3, 123/20, 881/60)`$ (`congruent_five_six_seven_fortyOne`); Tunnell's counts $`A(n) = \#\{x^2 + 2y^2 + 8z^2 = n\}`$, $`B(n) = \#\{x^2 + 2y^2 + 32z^2 = n\}`$ (and $`C`$, $`D`$ for even $`n`$) for small $`n`$, by kernel computation (`congruent_tunnell_counts`), and the consistency check $`A(5) = 2B(5)`$ for the congruent number $`5`$ (`congruent_tunnell_five_consistent`).

Neither Mathlib (at the pinned commit) nor Tau Ceti (main, checked on 2026-11-12) defines congruent numbers.

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
  Invent. Math. 39 (1977)). Mathlib has no $`L`$-functions of elliptic curves, so $`L(E_n, 1)`$ is a function
  `Lval` constrained only by these inputs. Both constants of Tunnell's formula were checked numerically for all
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

## Known restrictions

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
  come from the maximal orders, that $`g`$ is a modular form of weight $`3/2`$ and level $`44`$, and that its Shimura
  lift is the newform of level $`11`$ are not proved in Lean.
- **Tunnell:** $`L(E_n, 1)`$ is an abstract function (Mathlib has no $`L`$-functions of elliptic curves); Tunnell's
  formula and the theorem of Coates and Wiles are assumed; the converse direction needs the weak Birch and
  Swinnerton-Dyer conjecture.
- **Locators:** the theorem numbers cited from the papers of Waldspurger, Kohnen, Gross, Tunnell and Coates–Wiles
  have not been checked against the papers; the normalizations were checked numerically.

**Main statements.** To check what is claimed, read the eight files [`Challenge_Milne.lean`](Challenge_Milne.lean),
[`Challenge_Miyake.lean`](Challenge_Miyake.lean), [`Challenge_Shimura.lean`](Challenge_Shimura.lean),
[`Challenge_Iwaniec.lean`](Challenge_Iwaniec.lean),
[`Challenge_AndrianovZhuravlev.lean`](Challenge_AndrianovZhuravlev.lean),
[`Challenge_HeegnerStark.lean`](Challenge_HeegnerStark.lean), [`Challenge_Waldspurger.lean`](Challenge_Waldspurger.lean)
and [`Challenge_CongruentNumbers.lean`](Challenge_CongruentNumbers.lean) (the last three per topic, with the
conditional theorems): they state the results above, with a
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
                        <book> = Milne, Miyake, Shimura, Iwaniec, AndrianovZhuravlev (books), HeegnerStark,
                        Waldspurger, CongruentNumbers (topics)
Solution_<book>.lean    the same statements, proved from the library
comparator.json         the books, each with its lake comparator configuration comparator/<book>.json
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/results/books/     the book maps and statement maps; docs/results/comparison.md: comparison with Mathlib and
                        Tau Ceti
docs/updates-and-errata.md  corrections to the books
ModularFormsKB/
  Milne/                Milne, Modular Functions and Modular Forms: Ch0/ ... Ch12/ by section;
                        RiemannSurface/, RS/: Riemann surfaces (Section 1 and supporting results);
                        Wave4A/, Wave4B/: the genus of X(Gamma), Riemann-Roch on the sphere and X(1), Sections 11-12
  Miyake/               Miyake, Modular Forms (Chapters 1-7; Sec4_3/: L-functions and Weil's theorem;
                        Wave2A/, Wave2B/, Wave3/: further items of Chapters 1-7)
  Dimension/            the Sturm bound and dimension bounds for Gamma_0(N), Gamma_1(N) and a character
  Shimura2007/          Shimura, Elementary Dirichlet Series and Modular Forms (statements, Sections 1-4, 6, 16)
  Iwaniec1997/          Iwaniec, Topics in Classical Automorphic Forms (statements, Chapters 3-5, 9-10)
  Andrianov/            Andrianov and Zhuravlev, Modular Forms and Hecke Operators (statements, Chapters 1-4)
  Historical/WeberHeegnerStark/  the class number one theorem, conditional: Inputs.lean (the named inputs),
                        Defs.lean, Forms.lean, Heegner.lean, CubicField.lean, Diophantine.lean, Numerics.lean,
                        QuadraticField.lean, Main.lean
  HalfIntegral/         half-integral weight forms, theta series and the Shimura lift (supporting files, used by
                        Iwaniec1997/ and Waldspurger/)
  HalfIntegral/Waldspurger/  Waldspurger's theorems: Packets.lean (sign patterns), Coefficients.lean (square
                        classes, Kohnen's formula, the fibre), Gross.lean (p = 11), Tunnell.lean (congruent numbers)
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
                                          # likewise Miyake, Shimura, Iwaniec, AndrianovZhuravlev,
                                          # HeegnerStark, Waldspurger, CongruentNumbers
```

Mathlib comes prebuilt from its cache; Tau Ceti and this library are built from source (about 18,900 build jobs
besides Mathlib's cache; no file imports all of Mathlib, so only the parts of Tau Ceti that the library uses are
built). A cold build took about 43 minutes on 8 cores (2026-11-12), with at most 5.1 GB of memory in use besides the
page cache and a largest single Lean process of 4.9 GB. One `lake comparator` check per book or topic (build, export,
and the Lean, NanoDa and con-ron kernels; measured without the bubblewrap sandbox, 2026-11-12): Milne 32 minutes, at
most 9.0 GB in use (largest process `leanexport`, 7.2 GB; most of the time is Lean's own kernel); Miyake 9 minutes,
4.0 GB; Shimura 5.5 minutes, 3.3 GB; Iwaniec 1.5 minutes, 1.9 GB; Andrianov–Zhuravlev 3 minutes, 2.4 GB;
Heegner–Stark 7 minutes, 6.9 GB (largest process `con-ron`, 4.3 GB); Waldspurger 4.5 minutes, 2.7 GB; congruent
numbers 2 minutes, 4.7 GB. GitHub's standard runner has 4 cores and 16 GB; the CI workflow adds swap space and saves partial
builds, so a first run may need to be re-run to finish.

## Provenance

ModularFormsKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by
Claude Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the
results, the conventions and the proof routes. The proofs are checked by the Lean kernel, and CI checks that the
headline theorems use only the standard axioms. The 52 headline statements of this release in the
`Challenge_<book>.lean` files, and the definitions they use, have **not yet been reviewed** by a human; that review is
planned for a later release. `lake comparator` checks that each `Solution_<book>.lean` proves exactly the statements
of its `Challenge_<book>.lean`. The rest of the library (its other definitions and intermediate results, and the
maps) has not been reviewed by a human; as with any AI-written formalization, treat it as untrustworthy until checked
against the literature. Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.24069385](https://doi.org/10.5281/zenodo.24069385) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **[v0.3.0](https://github.com/jonhanke/modular-forms-lean/releases/tag/v0.3.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`, Tau Ceti `4908b03`), archived on Zenodo as [doi:ZENODO-DOI-v0.3.0](https://doi.org/ZENODO-DOI-v0.3.0): conditional
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

**Not in this release** (planned for a later release): the rest of the half-integral weight library (Shimura's
correspondence, Kohnen's isomorphism and the Kohnen–Zagier formula, Shintani's lift) beyond the files used by the
Iwaniec statements and the Waldspurger headlines, Hurwitz class numbers and mock modular forms; the items of Shimura,
Iwaniec and Andrianov–Zhuravlev not yet stated; proofs of the named inputs of the conditional theorems (the theory of
complex multiplication; Waldspurger's theorems). This release is standalone: it does not depend
on the algebraic number theory library
[algebraic-number-theory-lean](https://github.com/jonhanke/algebraic-number-theory-lean), which is on a different
Mathlib; the [comparison](docs/results/comparison.md) lists the results the two libraries share.

## License

Apache License 2.0; see [LICENSE](LICENSE).
