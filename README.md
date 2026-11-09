# Modular forms in Lean 4

[![Lean build](https://github.com/jonhanke/modular-forms-lean/actions/workflows/build.yml/badge.svg)](https://github.com/jonhanke/modular-forms-lean/actions/workflows/build.yml) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24069385.svg)](https://doi.org/10.5281/zenodo.24069385)

A Lean 4 library (built on Mathlib and [Tau Ceti](https://github.com/TauCetiProject/TauCeti)) that formalizes two
texts on modular forms item by item: J. S. Milne's *Modular Functions and Modular Forms* (version 1.31) and
T. Miyake's *Modular Forms*, together with dimension bounds for modular forms on $`\Gamma_0(N)`$ and $`\Gamma_1(N)`$.
The Lean library is called `ModularFormsKB`.

- **Book maps**: for each book, a table from every item (theorem, proposition, lemma, corollary, definition) to the
  Lean declaration that formalizes it and its status: [docs/results/books/](docs/results/books/README.md).
- **Literature statements**: each result from a book or paper is a Lean declaration tagged
  `@[kb "<source key>" "<locator>"]`, with the keys of [`references.bib`](references.bib).
- **What is proved**: every theorem is checked by the Lean kernel; the only `sorry`s in the repository are the
  deliberate ones in [`Challenge.lean`](Challenge.lean), which states the headline results without proofs. The CI
  workflow builds the library, checks that the headline theorems depend only on the standard axioms `propext`,
  `Classical.choice` and `Quot.sound` ([scripts/check_axioms.lean](scripts/check_axioms.lean)), and runs
  `lake comparator` to check the proved statements against [`Challenge.lean`](Challenge.lean).
- **Cited results are named**: where the library assumes a result it does not prove, the result is a named Lean
  structure (a "named statement"), never assumed silently; a theorem that uses it has it as a hypothesis and the book
  maps mark the row *conditional*.
- **Comparison**: [docs/results/comparison.md](docs/results/comparison.md) says, for each headline and each chapter,
  what Mathlib and Tau Ceti already have, what other formalizations (the Stacks Project formalization by Axiom) also
  prove, and what this library adds.

## The books

| book | rows | proved | proved in part | conditional | definitions | in Mathlib | in Tau Ceti | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|---|
| [J. S. Milne, *Modular Functions and Modular Forms* (version 1.31)](docs/results/books/milne-mf.md) | 292 | 147 | 21 | 14 | 44 | 23 | 4 | 39 | 29 |
| [T. Miyake, *Modular Forms* (Springer, 1989)](docs/results/books/miyake.md) | 279 | 22 | 9 | 0 | 0 | 25 | 47 | 176 | 2 |
| [Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)](docs/results/books/dimension.md) | 22 | 21 | 0 | 0 | 1 | 0 | 0 | 0 | 12 |

*Proved*: proved with only the standard axioms and no unproved input. *Other*: refuted as stated, stated without proof, formalized in the source library but not in this release, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) in this library whose result, or a part of it, is also proved in Mathlib, Tau Ceti or the Stacks Project formalization (Axiom); each map names the declarations in its column *Also in*. Rows that are not results are omitted from the maps.

## Highlights

Every result listed here is a headline theorem of [`Challenge.lean`](Challenge.lean): it is checked by the Lean kernel
with only the standard axioms and depends on no unproved input. Headlines are only results that are in neither Mathlib
nor Tau Ceti, or that are stronger here ([comparison](docs/results/comparison.md)). One of them, Weil's Riemann
hypothesis for curves, is also proved in the Stacks Project formalization by Axiom, in another form; it is labelled
below. Related results of other libraries are cited next to the headlines, and the book maps credit, in their column
*Also in*, every result proved here that is also proved in Mathlib, Tau Ceti or the Stacks Project formalization. The
statements have **not yet been reviewed by a human** (see Provenance).

**Milne, *Modular Functions and Modular Forms***

- **Weil's Riemann hypothesis for curves over finite fields:** for a function field $`F`$ of one variable over $`\mathbb F_q`$, $`\mathbb F_q`$ algebraically closed in $`F`$, of genus $`g`$, there are algebraic integers $`\alpha_1, \dots, \alpha_{2g}`$ with $`N_n = 1 + q^n - \sum \alpha_i^n`$ for every $`n \ge 1`$, permuted by $`\alpha \mapsto q/\alpha`$, and $`|\alpha_i| = \sqrt q`$ (`weil_riemannHypothesis_curves`, Theorem 11.4; Tau Ceti has the genus-one case). *Also proved in the Stacks Project formalization (Axiom), in étale-cohomological form (tag 03V8, Bombieri–Stepanov); ours is the function-field form of Milne 11.4 and includes the functional equation* (the Stacks match is from its declaration index; see the [comparison](docs/results/comparison.md)).
- **Kronecker's modular equation, for every level $`N`$:** $`\mathbb C(X_0(N)) = \mathbb C(j, j_N)`$, and the minimal polynomial of $`j(Nz)`$ over $`\mathbb C(j)`$ has degree $`[\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N)]`$ and is $`F_N(j, Y)`$ with $`F_N \in \mathbb Z[X, Y]`$, symmetric for $`N > 1`$, and $`F_p \equiv X^{p+1} + Y^{p+1} - X^pY^p - XY \pmod p`$ (`kronecker_modularEquation`, Theorem 6.1).
- **Singular moduli are algebraic integers:** $`j(z)`$ is an algebraic integer for every imaginary quadratic $`z \in \mathbb H`$ (`j_isIntegral_of_imaginaryQuadratic`, Corollary 12.16).
- **Elliptic functions:** on a fundamental parallelogram the orders and the residues of an elliptic function sum to $`0`$ and $`\sum \operatorname{ord}_P(f)P \in \Lambda`$ (`doublyPeriodic_sums`, Proposition 3.1); an elliptic function with prescribed zeros and poles exists when their sums agree modulo $`\Lambda`$, and is unique up to a constant (`prescribedDivisor`, Theorem 3.8); every elliptic function is a rational function of $`\wp`$ and $`\wp'`$ (`ellipticFunctionField`, Proposition 3.11).
- **Moduli of elliptic curves:** over an algebraically closed field, the $`j`$-line solves the moduli problem of elliptic curves (`ellipticModuli_jLine`, Theorem 8.4), and the moduli problem of elliptic curves with a cyclic subgroup of order $`N`$ has a solution for every $`N`$ prime to the characteristic (`cyclicModuli`, Theorem 8.6). Related results: Tau Ceti's fine moduli scheme $`Y_1(N)`$, $`N \ge 4`$ (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.existsUnique_yOne`), on which the proof of Theorem 8.6 for $`N \ge 4`$ is built, and the algebraic moduli stack $`\mathcal M_{1,1}`$ of the Stacks Project formalization (Axiom; Tag 072R, index match).

**Miyake, *Modular Forms***

- **Hecke's theorem:** for coefficients of polynomial growth, $`g = f|_k\omega_N`$ if and only if $`\Lambda_N(s; f)`$ and $`\Lambda_N(s; g)`$ continue to the plane, with $`\Lambda_N(s; f) = i^k\Lambda_N(k - s; g)`$ and the usual polar parts, bounded on vertical strips (`hecke_converse`, Theorem 4.3.6); at level one, $`\sum a_n q^n`$ is a modular form of weight $`k`$ if and only if its $`L`$-function has this analytic behaviour (`hecke_converse_levelOne`, Theorem 4.3.8). The forward direction for cusp forms (the Fricke relation gives the functional equation) is in Tau Ceti (`CuspForm.frickeCompletedL_functional_equation`); the converse direction is new here.
- **Weil's converse theorem:** if $`L(s; f)`$, $`L(s; g)`$ and their twists by the primitive characters of conductor in a suitable set of primes satisfy the functional equations with Weil's constant, then $`f \in M_k(N, \chi)`$, $`g \in M_k(N, \bar\chi)`$ and $`g = f|_k\omega_N`$ (`weil_converse`), and $`f`$, $`g`$ are cusp forms when $`L(s; f)`$ converges absolutely at $`k - \delta`$ (`weil_converse_cusp`, Theorem 4.3.15).

**Main statements.** To check what is claimed, read one file: [`Challenge.lean`](Challenge.lean) states the results
above, with a docstring for each and a list of the library definitions the statements use; every proof there is a
deliberate `sorry`. [`Solution.lean`](Solution.lean) proves the same statements by appeal to the library theorems, and
`lake comparator` (configured by [`comparator.json`](comparator.json)) checks that each proved statement is exactly
the one in `Challenge.lean` and uses only the standard axioms. [`formalization.yaml`](formalization.yaml) records the
scope, sources, divergences from the literature, provenance and review status in the
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) format.

**Corrections to the books** found while formalizing them (statements false as written, with the corrected form the
library proves) are listed in [docs/updates-and-errata.md](docs/updates-and-errata.md).

## Layout

```
Challenge.lean          the headline statements (proofs: deliberate sorry)
Solution.lean           the same statements, proved from the library
comparator.json         configuration for `lake comparator` (Solution against Challenge)
formalization.yaml      scope, sources, divergences, provenance, review (formalization.yaml v0.4)
docs/results/books/     the book maps; docs/results/comparison.md: comparison with Mathlib and Tau Ceti
docs/updates-and-errata.md  corrections to the books
ModularFormsKB/
  Milne/                Milne, Modular Functions and Modular Forms: Ch0/ ... Ch12/ by section;
                        RiemannSurface/, RS/: Riemann surfaces (Section 1 and supporting results)
  Miyake/               Miyake, Modular Forms (Chapters 1-4; Sec4_3/: L-functions and Weil's theorem)
  Dimension/            the Sturm bound and dimension bounds for Gamma_0(N), Gamma_1(N) and a character
  Citation.lean         the @[kb] citation attribute
references.bib          bibliography; the keys used by @[kb]
scripts/check_axioms.lean  prints the axioms of the headline theorems (run in CI)
scripts/check_map_names.lean, check_also_in.lean  check that the Lean names of the book maps exist
scripts/verify-comparator.sh  runs `lake comparator` with the toolchain's kernels (run in CI)
ci/build.yml            the CI workflow (to be installed as .github/workflows/build.yml)
```

## Usage

```bash
lake exe cache get       # once: download prebuilt Mathlib
lake build               # build and check everything
lake env lean scripts/check_axioms.lean   # axioms of the headline theorems
./scripts/verify-comparator.sh            # Solution against Challenge (Linux; needs bubblewrap)
```

Mathlib comes prebuilt from its cache; Tau Ceti and this library are built from source (2,562 Tau Ceti modules and
266 of this library besides Mathlib's cache). A cold build took about 38 minutes on 8 cores (2026-11-08), with at
most 5.2 GB of memory in use besides the page cache and a largest single Lean process of 7.3 GB. GitHub's standard
runner has 4 cores and 16 GB; the CI workflow adds swap space and saves partial builds, so a first run may need to be
re-run to finish.

## Provenance

ModularFormsKB was written by AI, with Claude Code (Anthropic): almost entirely by Claude Opus 5.5, with a share by
Claude Sonnet 5.5, in October and November 2026. Jonathan Hanke designed and directed it: he chose the books, the
results, the conventions and the proof routes. The proofs are checked by the Lean kernel, and CI checks that the
headline theorems use only the standard axioms. The 12 headline statements of this release in
`Challenge.lean`, and the definitions they use, have **not yet been reviewed** by a human; that review is planned for
a later release. `lake comparator` checks that `Solution.lean` proves exactly the statements of `Challenge.lean`. The
rest of the library (its other definitions and intermediate results, and the book maps) has not been reviewed by a
human; as with any AI-written formalization, treat it as untrustworthy until checked against the literature.
Corrections and reports of mis-formalizations are very welcome.

## Releases

Releases are tagged with semantic versions; `main` continues to develop. The DOI [10.5281/zenodo.24069385](https://doi.org/10.5281/zenodo.24069385) always resolves to the latest release. To cite a specific version, use its release page or the "Cite this repository" button.

- **[v0.1.0](https://github.com/jonhanke/modular-forms-lean/releases/tag/v0.1.0)** (Lean v4.36.0-rc2, Mathlib `1b1ccf4`, Tau Ceti `4908b03`), archived on Zenodo as [doi:10.5281/zenodo.24069386](https://doi.org/10.5281/zenodo.24069386): the first release: the book maps of Milne
  and Miyake and the 12 headline statements above.

**Not in this release** (planned for a later release): half-integral weight forms (Shimura, Kohnen, Waldspurger,
Shintani), Hurwitz class numbers and mock modular forms; the other chapters of Miyake (5 to 7: quaternion algebras,
traces of Hecke operators, Eisenstein series) beyond the items listed in its map. This release is standalone: it
does not depend on the algebraic number theory library
[algebraic-number-theory-lean](https://github.com/jonhanke/algebraic-number-theory-lean), which is on a different
Mathlib; the [comparison](docs/results/comparison.md) lists the results the two libraries share.

## License

Apache License 2.0; see [LICENSE](LICENSE).
