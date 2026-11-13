# Comparison with Mathlib and Tau Ceti

What each headline and each part of the books in this release adds to [Mathlib](https://github.com/leanprover-community/mathlib4)
and to [Tau Ceti](https://github.com/TauCetiProject/TauCeti). The comparison was made on 2026-11-08 by reading the
statements (not only the names) in Mathlib master at commit `df6966d0d` and Tau Ceti main at commit `686d0d7f`
(the files on analysis, field theory and number theory; Tau Ceti's algebraic geometry files were compared at the
commit `4908b03` that this library depends on). This library is built on Tau Ceti `4908b03` and the Mathlib commit
`1b1ccf4` that Tau Ceti pins; it uses Tau Ceti's Fuchsian groups, compactified modular curves, Hecke operators at
level $N$, function fields and elliptic-curve schemes. The five headlines new in 0.2.0 were compared on 2026-11-10
with Mathlib master at commit `666ab9b6` and Tau Ceti main at commit `46f63277`. The headlines new in 0.3.0 were
compared on 2026-11-12 with Tau Ceti main at commit `a5f657a8` (class number one) and `3780371c` (Waldspurger's
theorems, Gross's example and congruent numbers, by a search of its sources for half-integral weight, the metaplectic
group, Brandt matrices, maximal orders, congruent numbers and Tunnell) and with the Mathlib commit `1b1ccf4` that
this library pins (Mathlib master was not searched again for them).

The last column of the headline table and the column *Also in* of the book maps credit results that are also
proved elsewhere: in Mathlib, in Tau Ceti, or in the Stacks Project formalization by Axiom
([AxiomMath/Stacks](https://github.com/AxiomMath/Stacks), commit `5ed82d14`). The Stacks matches were made from
that library's declaration index (names and docstrings), not from its source, and are marked *index match*. One
headline, `weil_riemannHypothesis_curves`, is also proved there, in another form; it stays a headline, with that
label.

A search of large libraries can miss a result stated under another name or in another form; corrections are
welcome.

## Headlines

| headline | Mathlib | Tau Ceti | this release | other formalizations and related results |
|---|---|---|---|---|
| `weil_riemannHypothesis_curves` | — | the genus-one case: the zeta function and the Riemann hypothesis of an elliptic curve over a finite field (`AlgebraicGeometry/EllipticCurve/Isogeny/Frobenius/Zeta.lean`); the Riemann–Roch theorem and the genus of a function field (`FieldTheory/FunctionField/`) | new: Weil's theorem for every genus, in the function field form (places of a function field of one variable over $\mathbb F_q$, $\mathbb F_q$ algebraically closed in it), through F. K. Schmidt's theorem and Bombieri's proof | **also proved in the Stacks Project formalization (Axiom), in étale-cohomological form (tag 03V8, Bombieri–Stepanov); ours is the function-field form of Milne 11.4 and includes the functional equation**: `Stacks.BombieriStepanov.norm_curveEigenvalue_eq_sqrt`, `Stacks.EtaleCohomology.LAdicSheaf.natCard_fieldValuedPoints_eq_one_sub_sum_add_of_smoothProjectiveCurve` and the neighbouring Tag 03V8 theorems, for smooth proper curves as schemes (index match: matched from the Stacks declaration index, not from its source) |
| `kronecker_modularEquation` | — | the compactified $X_0(N)$ as a compact Riemann surface and its field of meromorphic functions; the $j$-function (`Analysis/Complex/ModularForms/LevelOne/JInputs.lean`); no modular polynomial | new: $\mathbb C(X_0(N)) = \mathbb C(j, j_N)$, the minimal polynomial of $j(Nz)$ of degree $\psi(N)$ with integer coefficients, symmetric, and Kronecker's congruence for $N = p$ | none found |
| `j_isIntegral_of_imaginaryQuadratic` | — | singular moduli and the Hilbert class polynomial (monic, separable, degree the class number); no integrality of $j$ | new: $j(z)$ is an algebraic integer for every imaginary quadratic $z \in \mathbb H$ (from the modular equation) | none found |
| `doublyPeriodic_sums` | the Weierstrass function $\wp$, $\wp'^2 = 4\wp^3 - g_2\wp - g_3$ (`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`) | the addition theorem and $\mathbb C/\Lambda \cong E(\mathbb C)$ (`Analysis/SpecialFunctions/Elliptic/`) | new: orders and residues of an elliptic function on a fundamental parallelogram sum to $0$, and $\sum \operatorname{ord}_P(f)\,P \in \Lambda$ | none found |
| `prescribedDivisor` | — | — | new: Abel's theorem for $\mathbb C/\Lambda$: an elliptic function with prescribed zeros and poles exists when $\sum P_i \equiv \sum Q_j$, unique up to a constant | none found |
| `ellipticFunctionField` | $\wp$ and $\wp'$ | — | new: every elliptic function is a rational function of $\wp$ and $\wp'$ | none found |
| `ellipticModuli_jLine` | — | moduli problems and the fine moduli variety $Y_1(N)$, $N \ge 4$ (`AlgebraicGeometry/ModularCurve/`, at `4908b03`) | new: over an algebraically closed field, $(\mathbb A^1, j)$ solves the moduli problem of elliptic curves | related: the Stacks Project formalization (Axiom) proves that the moduli stack $\mathcal M_{1,1}$ is algebraic (Tag 072R, `AlgebraicGeometry.ModuliEllipticCurves.ModuliStackIsAlgebraic`; index match), a different object (no coarse space, no $j$-map) |
| `cyclicModuli` | — | as above | new: the moduli problem of elliptic curves with a cyclic subgroup of order $N$ has a solution for every $N$ prime to the characteristic (from Tau Ceti's $Y_1(N)$ for $N \ge 4$; by hand for $N \le 3$) | related: Tau Ceti's fine moduli scheme $Y_1(N)$ for points of exact order $N \ge 4$ over any base (`TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneNaiveRepresentableBy`, `TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne`), on which our proof for $N \ge 4$ is built |
| `hecke_converse` | the $L$-function of a modular form of level one (the forward direction) | functional equations of $L$-functions of newforms (the forward direction) | new: Hecke's theorem at level $N$ with the Fricke involution, both directions | related: the forward direction for cusp forms is in Tau Ceti (`CuspForm.frickeCompletedL_functional_equation`, `CuspForm.frickeCompletedL_functional_equation_gamma1`): the Fricke relation gives $\Lambda_N(k - s, f) = i^k\Lambda_N(s, g)$, without the continuation of non-cusp forms, the poles or boundedness on vertical strips; the converse direction is not there |
| `hecke_converse_levelOne` | as above | — | new: the converse direction at level one | related: as for `hecke_converse`, the forward direction for cusp forms (`CuspForm.frickeCompletedL_functional_equation`) |
| `weil_converse` | — | — | new: Weil's converse theorem with character | none found |
| `weil_converse_cusp` | — | — | new: Weil's converse theorem for cusp forms | none found |
| `modularCurveX_Gamma_genus_eq_zero` (0.2.0) | — | the Riemann–Hurwitz formula for Fuchsian groups in Euler-characteristic form, under finite-CW-type hypotheses (`Analysis/Complex/Fuchsian/Compactification/RiemannHurwitz.lean`); the index $m$ of the genus formula (`Analysis/Complex/ModularForms/CongruenceSubgroups/Degree.lean`); no genus of $X(N)$ | new: for $N = 2, 3, 4, 5$ every holomorphic differential on $X(N)$ is zero (Milne, Example 2.23), from the canonical degree $2g_0 - 2 = -2$ | none found |
| `LFunction_halfRange` (0.2.0) | $L(1-k,\chi)$ through Bernoulli polynomials (Hurwitz zeta values) | the value $\tau(\chi)\sum_{n \in \mathbb Z}\bar\chi(n)n^{-k}$ through the generalized Bernoulli number, a sum over all residues (`NumberTheory/DirichletCharacter/LValues.lean`) | new: Shimura's half-range formula (Theorem 4.14 (i)) | related: elementary-number-theory-lean proves $L(k,\chi)$ for primitive $\chi$ of matching parity through $B_{k,\bar\chi}$ |
| `kloosterman_mul_of_coprime` (0.2.0) | — (no Kloosterman sums) | — | new: twisted multiplicativity (Iwaniec, (4.12)) | none found |
| `kloostermanMoment_two` (0.2.0) | — | — | new: $V_2(p) = p^2 - p - 1$ (Iwaniec, (4.23)) | none found |
| `siegelTheta_dominated` (0.2.0) | Jacobi's theta function in one and two variables (`NumberTheory/ModularForms/JacobiTheta/`); no Siegel upper half space | Siegel functions (units), not Siegel modular forms | new: theta series of degree $n$ of an even positive definite form converge absolutely and uniformly on $H_n(\varepsilon)$ (Andrianov–Zhuravlev, Chapter 1, Proposition 1.3) | none found |

## Conditional theorems (0.3.0)

Compared on 2026-11-12 with Tau Ceti main at commit `a5f657a8` and with the Mathlib commit `1b1ccf4` this library
uses (Mathlib has `NumberField.classNumber` and `NumberField.classNumber_eq_one_iff`, class number one if and only if
the ring of integers is a principal ideal domain; no classification).

| headline | Mathlib | Tau Ceti | this release | other formalizations and related results |
|---|---|---|---|---|
| `heegnerStark_classNumber_eq_one_iff`, `heegnerStark_classNumber_eq_one_iff_isSquare` (conditional on named inputs) | the class number of a number field; no classification of imaginary quadratic fields of class number one | the nine fields have class number one, the classification for $d_K > -51$, the integer points of Heegner's equation and the enclosure of $j$ (`NumberTheory/ClassNumberOne/`); class numbers as numbers of reduced forms (`NumberTheory/BinaryQuadraticForm/Ideal/ClassNumber.lean`); Weber's cubic for a Siegel function (`NumberTheory/ModularForms/SiegelFunction/JInvariant.lean`) | new: the direction "class number one implies $d_K$ is one of the nine", by Heegner's proof, from named inputs (Weber's §§ 87–94, Dirichlet and Dedekind); Heegner's step from Weber's class invariants to $y^2 = 2u(u^3+1)$, in a cubic field without Galois theory; Gauss's reduction to $D = -p$, $p \equiv 3 \bmod 8$. The integer points of Heegner's equation and the enclosure of $j$ are ported from Tau Ceti | related, in Tau Ceti (at the pinned commit and on main): `TauCeti.NumberField.classNumber_eq_one_of_mem_heegnerDiscriminants` (the nine fields have $h_K = 1$), `TauCeti.NumberField.classNumber_eq_one_iff_of_neg_fifty_one_lt_discr` ($d_K > -51$), `TauCeti.BinaryQuadraticForm.classNumber_eq_card_primitiveReducedForms_of_discr_eq` (the class number part of the input `imaginaryQuadratic`, for Tau Ceti's reduced forms) and `TauCeti.ModularForm.siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three` (the input `weber_cubic`, for $g_{(0,1/2)}^{12} = \mathfrak f_2^{24}$); none of them discharges an input here, since they are stated for Tau Ceti's own definitions |
| `waldspurger_card_admissible`, `waldspurger_isAdmissible_iff_even`, `waldspurger_two_mul_fibreDim`, `waldspurger_fibreDim_le_one`, `waldspurger_prod_localSign`, `waldspurger_isAdmissible_localSign_iff` (0.3.0) | — (no half-integral weight forms, no metaplectic group) | — ; related: Hilbert symbols and quaternion algebras over local fields (`NumberTheory/HilbertSymbol/`) | new: the combinatorics of Waldspurger's admissible sign patterns (1991) for abstract local data: their number, the parity criterion, the closed form of the fibre dimension, multiplicity one, the product formula for the local signs of a square class | none found |
| `waldspurger_kohnenPattern_isAdmissible`, `waldspurger_localSign_eq_kohnenPattern_iff`, `waldspurger_kohnen_fibreDim` (0.3.0) | — | — | new: Kohnen's plus space as Waldspurger's sign pattern for odd squarefree level; Kohnen's condition $(D/\ell) = w_\ell$ | none found |
| `gross_grossCoeff_eq_zero_of_mod_four`, `gross_grossCoeff_eq_zero_of_split`, `gross_grossCoeff_values`, `gross_brandt_rowSum_symm`, `gross_brandt_eigen`, `gross_brandt_eisenstein` (0.3.0) | ternary quadratic forms only as general quadratic forms; no theta series of ternary forms, no Brandt matrices | — (no maximal orders of quaternion algebras over $\mathbb Q$, no Brandt matrices) | new: Gross's weight $3/2$ form for $p = 11$ from two ternary forms (plus condition, the local obstruction at $11$, coefficients by kernel computation) and the Brandt matrices $B(2), B(3), B(5)$ with the eigenvalues of the curve of conductor $11$; the forms and matrices are entered explicitly | none found |
| `waldspurger_exists_constant`, `waldspurger_coeff_eq_zero_iff`, `waldspurger_kohnen_central_nonneg`, `waldspurger_kohnen_ratio`, `waldspurger_kohnen_coeff_ne_zero_iff`, `waldspurger_twistRoot_eq_one`, `waldspurger_carries_unique`, `waldspurger_finrank_plusFibre_eq_one`, `gross_grossCoeff_eq_zero_iff` (0.3.0; conditional on named inputs) | — | — | new: consequences of Waldspurger 1981 and 1991, Kohnen 1985 and Gross 1987, each from its named input: one constant per square class, nonnegativity of central values, multiplicity one in the plus space, Gross's vanishing criterion | none found |
| `congruent_isCongruent_iff_point`, `congruent_five_six_seven_fortyOne`, `congruent_tunnell_counts`, `congruent_tunnell_five_consistent` (0.3.0) | Weierstrass curves and the group of their points; no congruent numbers | — (no congruent numbers) | new: $n$ is congruent if and only if $y^2 = x^3 - n^2x$ has a rational point with $y \ne 0$; the triangles for $5$, $6$, $7$, $41$; Tunnell's counts | none found |
| `congruent_not_isCongruent_of_odd`, `congruent_not_isCongruent_of_even`, `congruent_not_isCongruent_one_three_eleven` (0.3.0; conditional on named inputs); `congruent_isCongruent_iff_odd`, `congruent_isCongruent_iff_even` (0.3.0; conditional on the weak Birch and Swinnerton-Dyer conjecture) | — (no $L$-functions of elliptic curves) | — | new: Tunnell's criterion from Tunnell's formula and the theorem of Coates and Wiles (named inputs); as an equivalence, from the weak Birch and Swinnerton-Dyer conjecture (a conjecture, a hypothesis) | none found |

| result | here | why not a headline |
|---|---|---|
| Kronecker–Weber theorem (Milne, Theorem 12.1) | `Milne.kroneckerWeber` | Tau Ceti main has it (`NumberTheory/ClassFieldTheory/ClassFields/KroneckerWeber.lean`) |
| Addition formula for $\wp$, $\mathbb C/\Lambda \cong E(\Lambda)$ (Milne, Propositions 3.9, 3.12) | `Milne.weierstrassAdditionStatement`, `Milne.weierstrassUniformizationStatement` | in Tau Ceti (`Analysis/SpecialFunctions/Elliptic/AdditionTheorem.lean`, `Uniformization.lean`) |
| Euler products and the Petersson adjoint of $T(n)$ at level $\Gamma(N)$ (Milne, 5.35–5.37) | `Milne.UncondLevelN.eulerProductLevelN`, `Milne.UncondLevelN.eulerProductLevelNt`, `Milne.UncondLevelN.peterssonHeckeLevelN` | Tau Ceti has the corresponding results for $\Gamma_0(N)$ and $\Gamma_1(N)$, with convergent Euler products |
| Complex tori: biholomorphic iff the lattices are homothetic; $\operatorname{End}(\mathbb C/\Lambda)$ is $\mathbb Z$ or an order of an imaginary quadratic field (Milne, 3.5, 3.6) | `Milne.nonempty_biholomorphic_iff_isHomothetic`, `Milne.endRing_eq_int_or_imagQuadratic` | small; Tau Ceti has the holomorphic maps of tori (3.3, 3.4) |
| The Sturm bound and dimension bounds for $\Gamma_0(N)$, $\Gamma_1(N)$ and a character | `ModularFormsKB.Dimension` | specializations of Tau Ceti's Sturm bound |
| Fourier expansion of the Eisenstein series $E_k(z;\chi,\psi)$ (Miyake, Theorem 7.1.3) | `Miyake.Wave2B.hasSum_eisensteinChar` | Tau Ceti main has the $q$-expansion of Eisenstein series with character (`NumberTheory/ModularForms/EisensteinSeries/QExpansion.lean`) |
| Hecke's bound $a_n = O(n^{k/2})$ for cusp forms (Miyake, Corollary 2.1.6) | `Miyake.qExpansion_slash_isBigO` | in Mathlib master (`CuspFormClass.qExpansion_isBigO`) |
| Euler's formula and $L(k,\chi)$ at positive integers (Shimura, Theorem 4.12) | `Shimura2007.two_mul_factorial_gaussSum_mul_LFunction` | in Tau Ceti main (`NumberTheory/DirichletCharacter/LValues.lean`) |
| Twisted functional equations with Weil's constant (Miyake, 4.3.11, 4.3.12) | `Miyake.fricke_twist`, `Miyake.twisted_completedL_cuspForm` | supporting results of `weil_converse` |

**Not proved here.** The dimension formula for $M_{2k}(\Gamma)$, $\Gamma$ of finite index (Milne, Theorem 4.9), is
proved from two named statements, the Riemann–Roch theorem and the degree of the canonical divisor of a compact
Riemann surface (`Milne.dimensionFormula_of_riemannRoch`); it is not a headline. Mathlib has the dimension formula at
level one.

## Overlap with algebraic-number-theory-lean

The algebraic number theory library [algebraic-number-theory-lean](https://github.com/jonhanke/algebraic-number-theory-lean)
(v0.1.0, on Mathlib v4.35.0) is independent of this one: neither depends on the other, and they are on different
Mathlib versions. Both formalize:

| topic | algebraic-number-theory-lean | this release |
|---|---|---|
| the modular polynomial | rational coefficients and degree $[\mathrm{SL}_2(\mathbb Z):\Gamma_0(N)]$ (`modularPolynomial_rational`) | integer coefficients, symmetric, Kronecker's congruence, and $\mathbb C(X_0(N)) = \mathbb C(j, j_N)$ (`kronecker_modularEquation`) |
| the modular curve $X_0(N)$ | over $\mathbb Q$, by its function field; the genus formula and $\dim S_2(\Gamma_0(N)) = g$ | as a compact Riemann surface (Tau Ceti's); the genus formula is not proved here |
| the Kronecker–Weber theorem | from the reciprocity law, as a named input (Milne, *Class Field Theory*, V, Example 3.10), and ported from Tau Ceti for local class field theory; supporting files outside its books | proved (Milne, Theorem 12.1), not a headline (it is in Tau Ceti) |

## By book and chapter

The book maps ([books/](books/README.md)) give every item. Below, for each chapter: how many items Mathlib or Tau
Ceti (dependencies of this library) already have, and how many this library proves.

### J. S. Milne, *Modular Functions and Modular Forms* (version 1.31)

| chapter | rows | in Mathlib | in Tau Ceti | proved here | proved in part | conditional | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|
| 0 | 5 | 0 | 0 | 2 | 1 | 0 | 2 | 0 |
| 1 | 23 | 0 | 0 | 13 | 7 | 2 | 1 | 2 |
| 2 | 22 | 0 | 0 | 12 | 9 | 0 | 1 | 4 |
| 3 | 13 | 1 | 0 | 11 | 0 | 1 | 0 | 2 |
| 4 | 36 | 0 | 0 | 26 | 8 | 1 | 1 | 7 |
| 5 | 34 | 0 | 0 | 34 | 0 | 0 | 0 | 6 |
| 6 | 2 | 0 | 0 | 2 | 0 | 0 | 0 | 0 |
| 7 | 5 | 1 | 0 | 3 | 1 | 0 | 0 | 1 |
| 8 | 9 | 0 | 0 | 6 | 3 | 0 | 0 | 0 |
| 9 | 4 | 0 | 0 | 4 | 0 | 0 | 0 | 1 |
| 10 | 2 | 0 | 0 | 1 | 0 | 0 | 1 | 1 |
| 11 | 22 | 0 | 0 | 8 | 0 | 5 | 9 | 1 |
| 12 | 116 | 21 | 4 | 37 | 2 | 6 | 46 | 4 |

### T. Miyake, *Modular Forms* (Springer, 1989)

| chapter | rows | in Mathlib | in Tau Ceti | proved here | proved in part | conditional | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|
| 0 | 279 | 21 | 46 | 56 | 29 | 0 | 127 | 2 |

### Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)

| chapter | rows | in Mathlib | in Tau Ceti | proved here | proved in part | conditional | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|
| — | 22 | 0 | 0 | 21 | 0 | 0 | 1 | 12 |

