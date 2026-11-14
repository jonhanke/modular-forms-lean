# Book maps

For each book of this release, a table from the items of the book to the Lean declarations and their status (generated from the coverage tables, the `@[kb]` citations and the kernel-level audit of the source repository).

| book | rows | proved | proved in part | conditional | definitions | in Mathlib | in Tau Ceti | other | proved here, also elsewhere |
|---|---|---|---|---|---|---|---|---|---|
| [J. S. Milne, *Modular Functions and Modular Forms* (version 1.31)](milne-mf.md) | 293 | 170 | 22 | 9 | 44 | 23 | 4 | 21 | 29 |
| [T. Miyake, *Modular Forms* (Springer, 1989)](miyake.md) | 279 | 83 | 41 | 0 | 3 | 18 | 25 | 109 | 2 |
| [Dimension bounds for modular forms on $\Gamma_0(N)$, $\Gamma_1(N)$ and with a character (Sturm)](dimension.md) | 22 | 21 | 0 | 0 | 1 | 0 | 0 | 0 | 12 |

*Proved*: proved with only the standard axioms and no unproved input. *Other*: refuted as stated, stated without proof, formalized in the source library but not in this release, or not formalized (see each map). *Proved here, also elsewhere*: rows proved (in whole or in part) in this library whose result, or a part of it, is also proved in Mathlib, Tau Ceti or the Stacks Project formalization (Axiom); each map names the declarations in its column *Also in*. Rows that are not results are omitted from the maps.

## Statement maps

For three more books, a first statement wave: the central results that the library states in Lean, each marked proved or stated (the other items of these books are not listed).

| book | rows | proved | proved in part | conditional | stated, not proved |
|---|---|---|---|---|---|
| [G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer, 2007)](shimura2007.md) | 12 | 3 | 6 | 0 | 3 |
| [H. Iwaniec, *Topics in Classical Automorphic Forms* (American Mathematical Society, 1997)](iwaniec1997.md) | 28 | 6 | 2 | 2 | 18 |
| [A. N. Andrianov and V. G. Zhuravlev, *Modular Forms and Hecke Operators* (American Mathematical Society, 1995)](andrianovzhuravlev1995.md) | 26 | 12 | 3 | 1 | 10 |
| [Waldspurger's theorems, the Shimura lift, Gross's example for $p = 11$ and Tunnell's theorem (papers of Waldspurger 1981 and 1991, Kohnen 1985, Gross 1987, Tunnell 1983, Coates and Wiles 1977)](waldspurger.md) | 17 | 7 | 0 | 8 | 2 |
| [Historical theorems: Jacobi, *Fundamenta nova* (1829); Ramanujan, *Collected Papers* (1927); Weber, *Elliptische Functionen und algebraische Zahlen* (1891) and *Lehrbuch der Algebra* III (1908); Kronecker, *Werke* 4 and 5](historical.md) | 8 | 3 | 3 | 1 | 1 |
