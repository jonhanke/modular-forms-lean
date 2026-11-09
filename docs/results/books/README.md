# Book maps

For each book of this release, a table from the items of the book to the Lean declarations and their status (generated from the coverage tables, the `@[kb]` citations and the kernel-level audit of the source repository).

| book | rows | proved | proved in part | conditional | definitions | in Mathlib | in Tau Ceti | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|---|
| [J. S. Milne, *Modular Functions and Modular Forms* (version 1.31)](milne-mf.md) | 292 | 147 | 21 | 14 | 44 | 23 | 4 | 39 | 29 |
| [T. Miyake, *Modular Forms* (Springer, 1989)](miyake.md) | 279 | 22 | 9 | 0 | 0 | 25 | 47 | 176 | 2 |
| [Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)](dimension.md) | 22 | 21 | 0 | 0 | 1 | 0 | 0 | 0 | 12 |

*Proved*: proved with only the standard axioms and no unproved input. *Other*: refuted as stated, stated without proof, formalized in the source library but not in this release, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) in this library whose result, or a part of it, is also proved in Mathlib, Tau Ceti or the Stacks Project formalization (Axiom); each map names the declarations in its column *Also in*. Rows that are not results are omitted from the maps.
