# Comparison with Mathlib and Tau Ceti

What each headline and each part of the books in this release adds to [Mathlib](https://github.com/leanprover-community/mathlib4)
and to [Tau Ceti](https://github.com/TauCetiProject/TauCeti). The comparison was made on 2026-11-08 by reading the
statements (not only the names) in Mathlib master at commit `df6966d0d` and Tau Ceti main at commit `686d0d7f`
(the files on analysis, field theory and number theory; Tau Ceti's algebraic geometry files were compared at the
commit `4908b03` that this library depends on). This library is built on Tau Ceti `4908b03` and the Mathlib commit
`1b1ccf4` that Tau Ceti pins; it uses Tau Ceti's Fuchsian groups, compactified modular curves, Hecke operators at
level $N$, function fields and elliptic-curve schemes.

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

## Results that are proved here but are not headlines

| result | here | why not a headline |
|---|---|---|
| Kronecker–Weber theorem (Milne, Theorem 12.1) | `Milne.kroneckerWeber` | Tau Ceti main has it (`NumberTheory/ClassFieldTheory/ClassFields/KroneckerWeber.lean`) |
| Addition formula for $\wp$, $\mathbb C/\Lambda \cong E(\Lambda)$ (Milne, Propositions 3.9, 3.12) | `Milne.weierstrassAdditionStatement`, `Milne.weierstrassUniformizationStatement` | in Tau Ceti (`Analysis/SpecialFunctions/Elliptic/AdditionTheorem.lean`, `Uniformization.lean`) |
| Euler products and the Petersson adjoint of $T(n)$ at level $\Gamma(N)$ (Milne, 5.35–5.37) | `Milne.UncondLevelN.eulerProductLevelN`, `Milne.UncondLevelN.eulerProductLevelNt`, `Milne.UncondLevelN.peterssonHeckeLevelN` | Tau Ceti has the corresponding results for $\Gamma_0(N)$ and $\Gamma_1(N)$, with convergent Euler products |
| Complex tori: biholomorphic iff the lattices are homothetic; $\operatorname{End}(\mathbb C/\Lambda)$ is $\mathbb Z$ or an order of an imaginary quadratic field (Milne, 3.5, 3.6) | `Milne.nonempty_biholomorphic_iff_isHomothetic`, `Milne.endRing_eq_int_or_imagQuadratic` | small; Tau Ceti has the holomorphic maps of tori (3.3, 3.4) |
| The Sturm bound and dimension bounds for $\Gamma_0(N)$, $\Gamma_1(N)$ and a character | `ModularFormsKB.Dimension` | specializations of Tau Ceti's Sturm bound |
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
| 1 | 22 | 0 | 0 | 8 | 4 | 1 | 9 | 2 |
| 2 | 22 | 0 | 0 | 12 | 8 | 0 | 2 | 4 |
| 3 | 13 | 1 | 0 | 11 | 0 | 1 | 0 | 2 |
| 4 | 36 | 0 | 0 | 26 | 6 | 3 | 1 | 7 |
| 5 | 34 | 0 | 0 | 34 | 0 | 0 | 0 | 6 |
| 6 | 2 | 0 | 0 | 2 | 0 | 0 | 0 | 0 |
| 7 | 5 | 1 | 0 | 3 | 1 | 0 | 0 | 1 |
| 8 | 9 | 0 | 0 | 5 | 3 | 1 | 0 | 0 |
| 9 | 4 | 0 | 0 | 4 | 0 | 0 | 0 | 1 |
| 10 | 2 | 0 | 0 | 1 | 0 | 0 | 1 | 1 |
| 11 | 22 | 0 | 0 | 7 | 0 | 2 | 13 | 1 |
| 12 | 116 | 21 | 4 | 36 | 1 | 6 | 48 | 4 |

### T. Miyake, *Modular Forms* (Springer, 1989)

| chapter | rows | in Mathlib | in Tau Ceti | proved here | proved in part | conditional | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|
| 0 | 279 | 25 | 47 | 22 | 9 | 0 | 176 | 2 |

### Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)

| chapter | rows | in Mathlib | in Tau Ceti | proved here | proved in part | conditional | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|
| — | 22 | 0 | 0 | 21 | 0 | 0 | 1 | 12 |

