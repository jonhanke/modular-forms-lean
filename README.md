# Modular forms in Lean 4

[![Lean build](https://github.com/jonhanke/modular-forms-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/modular-forms-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24069385.svg)](https://doi.org/10.5281/zenodo.24069385)

A Lean 4 library (built on Mathlib and [Tau Ceti](https://github.com/TauCetiProject/TauCeti)) that formalizes two
texts on modular forms item by item: J. S. Milne's *Modular Functions and Modular Forms* (version 1.31) and
T. Miyake's *Modular Forms*, together with dimension bounds for modular forms on $`\Gamma_0(N)`$ and $`\Gamma_1(N)`$.
Since 0.2.0 it also states the central results of three more books in Lean, as a first statement wave: G. Shimura's
*Elementary Dirichlet Series and Modular Forms*, H. Iwaniec's *Topics in Classical Automorphic Forms* and
A. N. Andrianov and V. G. Zhuravlev's *Modular Forms and Hecke Operators*. The Lean library is called `ModularFormsKB`.

- **Book maps**: for Milne and Miyake, a table from every item (theorem, proposition, lemma, corollary, definition) to
  the Lean declaration that formalizes it and its status: [docs/results/books/](docs/results/books/README.md).
- **Statement maps**: for Shimura, Iwaniec and Andrianov–Zhuravlev, each central result that the library states in
  Lean, with its declaration and whether it is proved or only stated (same page).
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
| [J. S. Milne, *Modular Functions and Modular Forms* (version 1.31)](docs/results/books/milne-mf.md) | 293 | 154 | 28 | 16 | 44 | 23 | 4 | 24 | 29 |
| [T. Miyake, *Modular Forms* (Springer, 1989)](docs/results/books/miyake.md) | 279 | 56 | 29 | 0 | 2 | 21 | 46 | 125 | 2 |
| [Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)](docs/results/books/dimension.md) | 22 | 21 | 0 | 0 | 1 | 0 | 0 | 0 | 12 |

*Proved*: proved with only the standard axioms and no unproved input. *Other*: refuted as stated, stated without proof, formalized in the source library but not in this release, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) in this library whose result, or a part of it, is also proved in Mathlib, Tau Ceti or the Stacks Project formalization (Axiom); each map names the declarations in its column *Also in*. Rows that are not results are omitted from the maps.

**Statement maps** (a first statement wave: the central results stated in Lean, each marked proved or stated):

| book | rows | proved | proved in part | conditional | stated, not proved |
|---|---|---|---|---|---|
| [G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer, 2007)](docs/results/books/shimura2007.md) | 12 | 3 | 6 | 0 | 3 |
| [H. Iwaniec, *Topics in Classical Automorphic Forms* (American Mathematical Society, 1997)](docs/results/books/iwaniec1997.md) | 28 | 6 | 2 | 2 | 18 |
| [A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (American Mathematical Society, 1995)](docs/results/books/andrianovzhuravlev1995.md) | 26 | 12 | 3 | 1 | 10 |

## Highlights

Every result listed here is a headline theorem of a `Challenge_<book>.lean` file: it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input. Headlines are only results that are in neither Mathlib
nor Tau Ceti (main branch, checked on 2026-11-10 for the headlines new in 0.2.0), or that are stronger here
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

**Main statements.** To check what is claimed, read the five files [`Challenge_Milne.lean`](Challenge_Milne.lean),
[`Challenge_Miyake.lean`](Challenge_Miyake.lean), [`Challenge_Shimura.lean`](Challenge_Shimura.lean),
[`Challenge_Iwaniec.lean`](Challenge_Iwaniec.lean) and
[`Challenge_AndrianovZhuravlev.lean`](Challenge_AndrianovZhuravlev.lean): they state the results above, with a
docstring for each and a list of the library definitions the statements use; every proof there is a deliberate
`sorry`. The matching `Solution_<book>.lean` files prove the same statements by appeal to the library theorems, and
`lake comparator`, configured per book by `comparator/<book>.json` (the books are listed in
[`comparator.json`](comparator.json)), checks that each proved statement is exactly the one in the challenge file and
uses only the standard axioms. The check is run one book at a time: each needs only the files of its book.
[`formalization.yaml`](formalization.yaml) records the scope, sources, divergences from the literature, provenance and
review status in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

**Corrections to the books** found while formalizing them (statements false as written, with the corrected form the
library proves) are listed in [docs/updates-and-errata.md](docs/updates-and-errata.md).

## Layout

```
Challenge_<book>.lean   the headline statements of one book (proofs: deliberate sorry);
                        <book> = Milne, Miyake, Shimura, Iwaniec, AndrianovZhuravlev
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
  HalfIntegral/         supporting files: half-integral weight forms and theta series, used by Iwaniec1997/
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
                                          # likewise Miyake, Shimura, Iwaniec, AndrianovZhuravlev
```

Mathlib comes prebuilt from its cache; Tau Ceti and this library are built from source (about 18,800 build jobs
besides Mathlib's cache; no file imports all of Mathlib, so only the parts of Tau Ceti that the library uses are
built). A cold build took about 50 minutes on 8 cores (2026-11-10), with at most 5.2 GB of memory in use besides the
page cache and a largest single Lean process of 6.4 GB. One `lake comparator` check per book (build, export, and the
Lean, NanoDa and con-ron kernels; measured without the bubblewrap sandbox): Milne 34 minutes, at most 8.0 GB in use
(largest process `leanexport`, 7.2 GB); Miyake 10 minutes, 4.0 GB; Shimura 6 minutes, 3.3 GB; Iwaniec 1.5 minutes,
1.8 GB; Andrianov–Zhuravlev 3 minutes, 2.5 GB. GitHub's standard runner has 4 cores and 16 GB; the CI workflow adds
swap space and saves partial builds, so a first run may need to be re-run to finish.

## Provenance

ModularFormsKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by
Claude Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the
results, the conventions and the proof routes. The proofs are checked by the Lean kernel, and CI checks that the
headline theorems use only the standard axioms. The 17 headline statements of this release in the
`Challenge_<book>.lean` files, and the definitions they use, have **not yet been reviewed** by a human; that review is
planned for a later release. `lake comparator` checks that each `Solution_<book>.lean` proves exactly the statements
of its `Challenge_<book>.lean`. The rest of the library (its other definitions and intermediate results, and the
maps) has not been reviewed by a human; as with any AI-written formalization, treat it as untrustworthy until checked
against the literature. Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.24069385](https://doi.org/10.5281/zenodo.24069385) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **v0.2.0** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`, Tau Ceti `4908b03`): statement maps, a new kind of map, for
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

**Not in this release** (planned for a later release): half-integral weight forms (Shimura, Kohnen, Waldspurger,
Shintani) beyond the supporting files used by the Iwaniec statements, Hurwitz class numbers and mock modular forms;
the items of Shimura, Iwaniec and Andrianov–Zhuravlev not yet stated. This release is standalone: it does not depend
on the algebraic number theory library
[algebraic-number-theory-lean](https://github.com/jonhanke/algebraic-number-theory-lean), which is on a different
Mathlib; the [comparison](docs/results/comparison.md) lists the results the two libraries share.

## License

Apache License 2.0; see [LICENSE](LICENSE).
