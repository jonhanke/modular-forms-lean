# Comparison with Mathlib and Tau Ceti

What each headline and each part of the books in this release adds to [Mathlib](https://github.com/leanprover-community/mathlib4)
and to [Tau Ceti](https://github.com/TauCetiProject/TauCeti). The comparison was made on 2026-11-08 by reading the
statements (not only the names) in Mathlib master at commit `df6966d0d` and Tau Ceti main at commit `686d0d7f`
(the files on analysis, field theory and number theory; Tau Ceti's algebraic geometry files were compared at the
commit `4908b03` that this library depended on until 0.3.1). Since 0.4.0 this library is built on Tau Ceti `ca32605`
(Tau Ceti main of 2026-11-14) and the Mathlib commit `e8ba86f` that Tau Ceti pins (until 0.3.1: Tau Ceti `4908b03`,
Mathlib `1b1ccf4`); it uses Tau Ceti's Fuchsian groups, compactified modular curves, Hecke operators at
level $N$, function fields and elliptic-curve schemes. The five headlines new in 0.2.0 were compared on 2026-11-10
with Mathlib master at commit `666ab9b6` and Tau Ceti main at commit `46f63277`. The headlines new in 0.3.0 were
compared on 2026-11-12 with Tau Ceti main at commit `a5f657a8` (class number one) and `3780371c` (Waldspurger's
theorems, Gross's example and congruent numbers, by a search of its sources for half-integral weight, the metaplectic
group, Brandt matrices, maximal orders, congruent numbers and Tunnell) and with the Mathlib commit `1b1ccf4` that
this library pins (Mathlib master was not searched again for them). The headlines new in 0.3.1 were compared on 2026-11-14 with
Mathlib master at commit `a647c99f` and Tau Ceti main at commit `71ce0a33`. The headlines new in 0.4.0 were compared
on 2026-11-15 with Mathlib master and Tau Ceti main of that day (section "Headlines new in 0.4.0"). Since 0.5.0
the library is built on Tau Ceti `1ff5324` (Tau Ceti main of 2026-11-16) and the same Mathlib commit `e8ba86f`; the
headlines new in 0.5.0 were compared on 2026-11-16 (section "Headlines new in 0.5.0").

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

## Headlines new in 0.3.1

Compared on 2026-11-14 with Mathlib master at commit `a647c99f` and Tau Ceti main at commit `71ce0a33`, by reading
the statements found by a search of both sources.

| headline | Mathlib | Tau Ceti | this release | other formalizations and related results |
|---|---|---|---|---|
| `littlePicard` (Milne, Remark 2.25) | Liouville's theorem, the open mapping theorem, covering maps and path lifting | the free locus of $\mathrm{PSL}_2(\mathbb Z)$ and the $j$-biholomorphism of $X(1)$ (`Analysis/Complex/Fuchsian/`); no Picard theorem | new: a nonconstant entire function omits at most one value | none found |
| `classGroupAction_ellCM` (Milne, Proposition 12.21, corrected) | — | orders of number fields and their Picard groups, isogenies and their kernels, Galois descent of isogenies, Hilbert and ring class fields; no action of $\mathrm{Pic}(O)$ on $\mathrm{Ell}(O)$ | new: over every algebraically closed field of characteristic zero, compatible with $\mathfrak a$-isogenies, with bijective orbit maps (the action laws are not stated) | none found |
| `betti_tate_comparison` (Milne, Proposition 11.5) | lattices and the Weierstrass $\wp$ (`PeriodPair`) | Tate modules and the uniformization $\mathbb C/\Lambda \cong E(\mathbb C)$; no comparison of the Betti and $\ell$-adic representations | new: $\mathbb Z_\ell \otimes \Lambda \cong T_\ell E$ and $\mathbb C \otimes \Lambda \cong \rho \oplus \bar\rho$, compatibly with $\mathrm{End}(E)$, for every elliptic curve over $\mathbb C$ | none found |
| `conductor_exponent_eq_two_iff` (Milne, p. 111) | — | Tate's algorithm and the conductor; the exponent is at least $2$ exactly at additive reduction (`WeierstrassCurve.two_le_algorithmicOggExponent_iff`, `AlgebraicGeometry/EllipticCurve/TateAlgorithm/Reduction/Curve.lean`) | new: for $p \ne 2, 3$ the exponent is exactly $2$ at additive reduction | none found |
| `heckeRing_gamma0_polynomial` (Miyake, Theorem 4.5.9) | the abstract Hecke ring | the Hecke ring of $\Gamma_0(N)$, its multiplication table and commutativity; the local polynomial-ring theorem at level one for $\mathrm{GL}_n$ (Shimura, Theorem 3.20; `NumberTheory/HeckeRing/GLn/PolynomialRing/Presentation.lean`) | new: $\mathcal R(\Gamma_0(N), \Delta_0(N))$ over $\mathbb Z$ is the polynomial ring in $T(p)$, $T(p, p)$ ($p \nmid N$) and $T(q)$ ($q \mid N$) | none found |
| `hecke_adjoint_heckeTStar` (Miyake, Theorem 4.5.4 (2)) | — | the adjoint of $T_n$ for $(n, N) = 1$ (`HeckeRing.GL2.isAdjointPair_heckeTCuspNat`, `NumberTheory/ModularForms/Petersson/Normal.lean`) and the adjoint formula for double coset operators | new: $T(n)$ and $T^*(n)$ adjoint for every $n \ge 1$ | none found |
| `jacobi_modular_equation_ode` (Jacobi 1829, § 33) | derivatives | Schwarzian derivatives (`Analysis/Complex/Conformal/Schwarzian.lean`); Legendre's equation for $K$ (not used here) | new: Jacobi's third-order equation for any two solutions of Legendre's equation | none found |
| `jacobi_theta_fourier` (Jacobi 1829, § 62) | `jacobiTheta₂` as a sum over $\mathbb Z$ | — | new: the cosine and sine series of $\Theta$ and $H$ (a rewriting of Mathlib's theta series) | none found |
| `ramanujan_differential_equations` (Ramanujan 1916) | Ramanujan's equations in the variable $\tau$ for $E_2$, $E_4$, $E_6$ (`NumberTheory/ModularForms/RamanujanFormula.lean`) | — | new: the equations in Ramanujan's variable $x$ on the whole disc $|x| < 1$ (derived from Mathlib's) | none found |
| `weber_theta_eta` (Weber 1891, § 21 (9); conditional on the Jacobi triple product in 0.3.1, unconditional since 0.4.0) | Dedekind's $\eta$, `jacobiTheta₂`; no triple product identity | $q$-products and theta inversion, not the triple product | new (conditional in 0.3.1): $\vartheta_{00} = \eta\mathfrak f^2$, $\vartheta_{01} = \eta\mathfrak f_1^2$, $\vartheta_{10} = \eta\mathfrak f_2^2$ | none found |
| `kronecker_ser_transformation` (Kronecker, *Werke* 5, art. XXI) | Eisenstein series and their summability | — | new: Kronecker's law (E) for $\rho \ge 2$ (a rearrangement of an absolutely convergent series) | none found |

Results of the new library files that are **not** headlines, because Tau Ceti main has them: a basis of $S_k(N, \chi)$
of common eigenfunctions of the $T(n)$, $(n, N) = 1$ (Miyake, Theorem 4.5.4 (3); Tau Ceti
`HeckeRing.GL2.exists_peterssonOrthonormalBasis_eigenformAwayFromLevel`), the Atkin–Lehner image of a newform (Miyake, Theorems
4.6.15 (2), 4.6.16 (4); Tau Ceti `HeckeRing.GL2.Newform.atkinLehnerTransform`), the coefficients $a_q$, $q \mid N$, of a
newform (Miyake, Theorem 4.6.17; transported here from Tau Ceti), and the degree of the field of modular functions
of $X(N)$ over $\mathbb C(j)$ (close to Milne's Theorem 1.17 on $X(\Gamma)$; Tau Ceti
`TauCeti.finrank_adjoin_coe_modularFunctionJ`); Mathlib has the graded ring of level-one modular forms (close to Miyake's
Theorem 4.1.8).

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

## Headlines new in 0.4.0

Compared on 2026-11-15 with Mathlib master at commit `4cf60f1d` and Tau Ceti main at commit `7ac17318`, by a search
of both sources (Riemann–Roch, existence of meromorphic functions, dimension and genus formulas, line bundles, theta
series with harmonic polynomials, non-holomorphic Eisenstein series, Rankin unfolding, Hecke's lemma, triple product)
and reading the statements found.

| headline | Mathlib | Tau Ceti | this release | other formalizations and related results |
|---|---|---|---|---|
| `meromorphicFunctions_separate_points`, `riemannRoch` (Milne, Theorems 1.17, 1.20) | — | the field of meromorphic functions of a compact Riemann surface, finite-dimensionality of divisor spaces, the canonical divisor; Riemann–Roch for function fields and for curves as schemes (`FieldTheory/FunctionField/`, `AlgebraicGeometry/WeilDivisor/Scheme/RiemannRoch/`); its own file says that it has no existence theorem for nonconstant functions | new: the existence theorem (after Forster, § 14) and Riemann–Roch on every compact connected Riemann surface | none found |
| `dimensionFormula`, `genusFormula` (Milne, Theorems 4.9, 2.22) | the dimension formula at level one | dimensions of Eisenstein subspaces, so $\dim M_k(\Gamma_1(N)) - \dim S_k(\Gamma_1(N))$ (the number of cusps, $N > 2$); $\dim M_2(\Gamma_0(N))$ for $N$ prime or squarefree; the Riemann–Hurwitz formula in Euler-characteristic form | new: both formulas for every subgroup of finite index, congruence or not | none found |
| `holomorphicLineBundle_upperHalfPlane_trivial` (Milne, Remark 4.26) | vector bundles and their smooth sections | the Dolbeault lemma on a disc | new: every holomorphic line bundle on $\mathbb H$ has a nowhere-vanishing holomorphic section | none found |
| `thetaSpherical_even`, `thetaSpherical_odd` (Miyake, Theorem 4.9.3, Corollary 4.9.4) | Jacobi's theta function | theta series of even lattices without weight ($P = 1$), their transformation law with the theta character, Gauss sums of quadratic forms; the Fourier transform of $z^n e^{-b\lvert z\rvert^2}$ in the plane (`Analysis/SpecialFunctions/Gaussian/Harmonic.lean`) | new: theta series with spherical functions in every rank, modular (half-integral weight for odd rank), cuspidal for $\nu \ge 1$ | none found |
| `thetaTwist_transformation` (Miyake, Corollary 4.9.7 (1)) | — | — | new: Shimura's law for the twisted theta series, every character | none found |
| `heckeEisenstein_continuation`, `heckeLimit_weightTwo`, `heckeLimit_weightOne` (Miyake, Theorems 7.2.9, 7.2.12, 7.2.13) | holomorphic Eisenstein series of weight $\ge 3$ and $E_2$ | Eisenstein series with characters in every weight, by other constructions (the corrected $E_2$, the weight-one series), and their $q$-expansions; no continuation in $s$ | new: Hecke's continuation in $s$ for every integer $k$, and the limits at $s = 0$ in weights two and one with their Fourier expansions | none found |
| `hecke_lemma` (Miyake, Lemma 4.6.3) | — | newform theory, which goes around this lemma | new | none found |
| `eisensteinLattice_functionalEquation`, `rankin_unfolding` (Hecke 1927; Rankin 1939, Selberg 1940) | Poisson summation, Mellin transforms (`StrongFEPair`) | Poisson summation over lattices; no non-holomorphic Eisenstein series, no unfolding | new: Hecke's functional equation of the lattice Eisenstein series with a character, and the unfolding of the Rankin integral over $\Gamma_0(L)$ | none found |
| `shimuraLift_theta_of_dualUnfolding` (Shimura 1973; conditional on `ShimuraDualUnfolding`) | — (no half-integral weight forms) | — | new, conditional: Shimura's lift of a cusp form of weight $k + 1/2$ for the theta multiplier is a cusp form of weight $2k$ | none found |
| `jacobi_triple_product` (Jacobi 1829, § 64) | `jacobiTheta₂`; no product formula | — | new | none found |

## Headlines new in 0.5.0

Compared on 2026-11-16 with Mathlib master at commit `98f73a9f` and Tau Ceti main at commit `f6105c5d`, by a search of
both sources (Rankin–Selberg, symmetric square, newforms and elliptic curves, modularity, strong Hasse–Weil, the
curve $y^2 = x^3 - x$, genus and theta series, half-integral weight and the plus space, partition congruences,
Ramanujan's $\tau$, Jacobi's cube and quartic identities, $E_2$) and reading the statements found. The two headlines on the newforms of the
congruent number curves were checked again on the same date with Tau Ceti main at commit `5751803d` and Mathlib
master at commit `c1ab7892` (newforms of elliptic curves, modularity, the curve $y^2 = x^3 - x$ and its twists): neither
relates an elliptic curve to a newform.

| headline | Mathlib | Tau Ceti | this release | other formalizations and related results |
|---|---|---|---|---|
| `rankinSelberg_levelOne`, `petersson_eq_symSq` (Rankin 1939, Selberg 1940; Zagier 1977) | the Riemann zeta function, Dirichlet series, $q$-expansions | the Petersson product (`CuspForm.peterssonInnerFd`), newforms and their Satake parameters; no Rankin–Selberg integral and no symmetric square | new: continuation, pole and functional equation of $L(f \times \bar g, s)$ at level one; $\langle f, f\rangle$ as a value of $L(\mathrm{Sym}^2 f, s)$ | none found |
| `elliptic_hasNewform_functionalEquation`, `elliptic_hasNewform_strongHasseWeil`, `elliptic_modularity_consequences`, `elliptic_newform_iff_strongHasseWeil` (Milne, section 11) | the $L$-series of an elliptic curve (`WeierstrassCurve.LFunction`) | newforms, the Fricke functional equation and the root number of a newform, Tate's algorithm, a statement of the Birch and Swinnerton-Dyer conjecture; nothing that relates an elliptic curve to a newform | new: functional equation, parity and strong Hasse–Weil for a curve with a newform; for every curve from the modularity theorem; Weil's converse in Milne's form 11.19 | none found |
| `thetaGenus_sub_cuspForm_even`, `thetaGenus_sub_cuspForm_odd`, `gross_form_mem_plusCuspForms` (Siegel 1935; Gross 1987) | — | theta series of even lattices and their transformation law at every level, the genus of integral lattices, the even unimodular lattices of ranks 8, 16, 24; no cuspidality of differences in a genus, no odd rank | new: the difference of the theta series of two forms in one genus is a cusp form, every rank (half-integral weight for odd rank); Gross's form in Kohnen's plus space | none found |
| `plus_heckeT_selfAdjoint`, `kohnen_isomorphism`, `kohnen_zagier`, `waldspurger_plus`, `kohnen_zagier_twistedL_nonneg` (Shimura 1973; Kohnen 1980; Kohnen and Zagier 1981) | — (no half-integral weight forms) | the Petersson product and Hecke operators in integral weight; no half-integral weight | new: self-adjointness of $T(p^2)$ on the plus space; and, conditional on named inputs, Kohnen's isomorphism and the Kohnen–Zagier formula | none found |
| `elliptic_congruentCurve_one_hasNewform`, `elliptic_congruentCurve_hasNewform` (Atkin and Li 1978, Theorem 3.1, for the twists of $f_{32}$) | the $L$-series of an elliptic curve | newforms, the primitive twist of a newform with a level dividing $Nr^2$ (its exact level is not determined), the curve $y^2 = x^3 - x$ | new: $E_1$ has the newform $f_{32}$ of level 32, and $E_n$, $n$ odd squarefree, the newform $f_{32} \otimes (\cdot/n)$ of level exactly $32n^2$ | none found |
| `congruent_curve_modular`, `congruent_*_trueL` (Tunnell 1983) | the $L$-series of an elliptic curve | the curve $y^2 = x^3 - x$ and its rational points (`CurveX3SubX.lean`), quadratic twists of curves | new: $f_{32}$ is a cusp form of weight 2 on $\Gamma_0(32)$ and the $L$-series of $E_n$ is that of its twist, hence entire; Tunnell's theorem with the true $L$-function, conditional | none found |
| `shimuraLift_theta_of_frickeKernel` (Shimura 1973; conditional on `ShimuraFrickeKernelUnfolding`) | — | — | new, conditional on a smaller input than in 0.4.0 | none found |
| `jacobi_cube`, `ramanujan_partition_congruences`, `ramanujan_tau_congruences`, `ramanujan_question387`, `jacobi_quartic_weber_eighth_powers`, `kronecker_theta_E2` | Euler's pentagonal theorem, partitions, `jacobiTheta₂`, $E_2$ and its transformation, the derivatives of $E_2, E_4, E_6$; no partition or $\tau$ congruences, no cube or quartic identity | the discriminant form and its $q$-expansion | new | none found |

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
| 0 | 5 | 0 | 0 | 2 | 2 | 0 | 1 | 0 |
| 1 | 23 | 0 | 0 | 20 | 2 | 0 | 1 | 2 |
| 2 | 22 | 0 | 0 | 19 | 3 | 0 | 0 | 4 |
| 3 | 13 | 1 | 0 | 11 | 0 | 1 | 0 | 2 |
| 4 | 36 | 0 | 0 | 30 | 5 | 0 | 1 | 7 |
| 5 | 34 | 0 | 0 | 34 | 0 | 0 | 0 | 6 |
| 6 | 2 | 0 | 0 | 2 | 0 | 0 | 0 | 0 |
| 7 | 5 | 1 | 0 | 3 | 1 | 0 | 0 | 1 |
| 8 | 9 | 0 | 0 | 6 | 3 | 0 | 0 | 0 |
| 9 | 4 | 0 | 0 | 4 | 0 | 0 | 0 | 1 |
| 10 | 2 | 0 | 0 | 1 | 0 | 0 | 1 | 1 |
| 11 | 22 | 0 | 0 | 10 | 1 | 4 | 7 | 1 |
| 12 | 116 | 21 | 4 | 41 | 4 | 1 | 45 | 4 |

### T. Miyake, *Modular Forms* (Springer, 1989)

| chapter | rows | in Mathlib | in Tau Ceti | proved here | proved in part | conditional | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|
| 0 | 272 | 17 | 33 | 106 | 41 | 0 | 75 | 2 |

### Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)

| chapter | rows | in Mathlib | in Tau Ceti | proved here | proved in part | conditional | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|
| — | 22 | 0 | 0 | 21 | 0 | 0 | 1 | 12 |

