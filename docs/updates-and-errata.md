# Updates and errata

Corrections to the books found while formalizing them: a statement of the book that is false as written (the library proves its negation for the literal formalization) or that needs an extra hypothesis, with the corrected form that the library proves or states. Gaps in the book's proofs of statements that are true are listed under Remarks at the end.

## 2026-11-08: the paper-only errata are now proved in Lean

Two entries below were argued on paper only; both counterexamples are now Lean theorems, with the standard axioms only.
- Milne, Theorems 4.28/4.33 in weight 2 (entry of 2026-10-29, Section 4): the comparison series
  $\sum_{(c,d)\ne0}|cz+d|^{-2}$ and the lattice majorant $\sum_{v\ne0}\|v\|^{-2}$ diverge
  (`not_summable_norm_mul_add_rpow_neg_two`, `not_summable_norm_rpow_neg_two`), and the weight-2 Poincaré series
  $\varphi_0$ for $\mathrm{SL}_2(\mathbb Z)$ is not absolutely convergent (`not_summable_poincareTerm_weight_two`).
- Milne, Theorem 9.6 (entry of 2026-10-29, chapters 8 and 9): for a nonzero form of weight $2k$,
  $\sum|a_n|n^{-\sigma}$ diverges for $\sigma \le k$ (`not_lseriesSummable_of_ne_zero`), and the printed hypotheses
  force $a = 0$ (`weil_theorem_book_coeff_eq_zero`). Weil's hypothesis was checked against Miyake, Theorem 4.3.15.
- Proposition 12.3(c): the unverified citation is replaced by the Lean proof `proper_tfae`.
- Lemma 5.24 (a proof gap; the statement is true and proved) moved to Remarks.
No released statement changed.

## 2026-11-07: Milne, Riemann-surface named statements 0.1, 1.17, 7.5

- **Wrong statement** (ours, `Milne.UniformizationStatement`, Theorem 0.1): it quantifies over simply connected complex
  manifolds without the Hausdorff axiom (Milne's Riemann surfaces are Hausdorff). **Counterexample:** two copies of
  $\mathbb C$ glued along $\{\operatorname{Re} z > 0\}$ (`RS.DoubledPlane`) is contractible, hence simply connected, and
  not Hausdorff, so isomorphic to none of the sphere, $\mathbb C$, the disk (`RS.not_uniformizationStatement`).
  **Corrected:** `RS.UniformizationStatementT2` (with `[T2Space X]`); not proved (the uniformization theorem is not
  available).
- **Wrong statement** (ours, `Milne.RiemannSurface.ExistsNonconstantStatement X`, Theorem 1.17): stated without
  `[CompactSpace X] [T2Space X]`. **Counterexample:** $\mathbb C$ with $z \sim z + n$ on the upper and
  $z \sim z + n\sqrt 2$ on the lower half-plane (`RS.PeriodGluedPlane`, connected, not Hausdorff) has only constant
  meromorphic functions (`RS.not_existsNonconstantStatement`). **Corrected:** the same structure applied to compact
  Hausdorff `X` (the hypothesis form used by `RS.riemannHurwitzStatement_of_riemannRoch`); not proved.
- **Wrong statement** (ours, `Milne.RiemannSurfaceAlgebraicStructure X`, Theorem 7.5): the `unique` field does not ask
  the field isomorphisms `Φ, Φ'` to be ℂ-linear. **Counterexample:** for the Riemann sphere, composing with complex
  conjugation gives a second compatible structure, and a ℂ-automorphism of the curve acting as conjugation on points
  would make $z \mapsto \bar z$ holomorphic (`RS.not_riemannSurfaceAlgebraicStructure_sphere`). **Corrected:**
  `RS.RiemannSurfaceAlgebraicStructureLinear`; not proved (Riemann's existence theorem is not available).

## 2026-11-07: Milne, *Modular Functions and Modular Forms* v1.31, Example 8.9, second correction

- **Statement** (`milne2017mf`, Section 8, pdf p. 100, as corrected on 2026-10-29 below; our
  `ModularFormsKB.Milne.LegendreFineModuli`): over an algebraically closed field of characteristic $0$, $\mathcal E_2$
  ($\zeta = -1$) has a *fine* moduli variety, the Legendre line $\mathbb A^1 \smallsetminus \{0, 1\}$.
- **Counterexample:** level-two structures are not rigid ($[-1]$ fixes $E[2]$), so $\mathcal E_2$ is not representable
  at all. Over $T = \operatorname{Spec} k[\lambda, (\lambda(\lambda-1))^{-1}]$ the Legendre curve
  $y^2 = x(x-1)(x-\lambda)$ with basis $(0,0), (1,0)$ and its twist $y^2 = x(x-\lambda)(x-\lambda^2)$ with basis
  $(0,0), (\lambda,0)$ become isomorphic (with their level structures) over the double cover $\lambda = s^2$, which is
  surjective on $k$-points, so a representing variety would identify them over $T$; but a pointed isomorphism of
  Weierstrass models is a change of variables, the discriminants differ by $\lambda^6$, and $\lambda^3$ is not a square
  in $k[\lambda, (\lambda(\lambda-1))^{-1}]$. Proved: `ModularFormsKB.Milne.Ch8Counterexample.not_legendreFineModuli`
  and `not_exists_isFineModuliSolution` (`ModularFormsKB/Milne/Ch8/LegendreCounterexample.lean`).
- **Corrected statement:** the Legendre line is a coarse moduli variety (a solution in the sense of Definition 8.1):
  `ModularFormsKB.Milne.LegendreCoarseModuli`, proved: `ModularFormsKB.Milne.legendreCoarseModuli`
  (`ModularFormsKB/Milne/Ch8/LevelTwoModuli.lean`, from `levelModuliSolution_two`, which holds whenever $2 \ne 0$ in
  $k$).

## 2026-11-07: Milne, *Modular Functions and Modular Forms* v1.31, Theorem 7.2

- **Book statement** (`milne2017mf`, Section 7, pdf p. 94; our `ModularFormsKB.Milne.CurveFunctionFieldEquivalence`):
  for a field $k_0$, $X \mapsto k_0(X)$ is an equivalence from complete regular irreducible curves over $k_0$ to function
  fields in one variable over $k_0$.
- **Counterexample:** Milne's varieties are geometrically reduced (an affine $k_0$-algebra has $k \otimes_{k_0} A$
  reduced, pdf p. 91), so $k_0(X)$ is separable over $k_0$. For $k_0 = \mathbb F_2(a)$ and $K = k_0(\sqrt a)(t)$, if
  $K \cong k_0(X)$ then on an affine chart $\operatorname{Spec} A$ we get $\sqrt a = p/q$, $p^2 = aq^2$, and
  $(1 \otimes p - \alpha \otimes q)^2 = 0$ in $\bar k \otimes A$ ($\alpha^2 = a$); reducedness and a linear form killing
  $1$ and sending $\alpha$ to $1$ force $q = 0$. Proved: `ModularFormsKB.Milne.Ch7Counterexample.not_curveFunctionFieldEquivalence`
  (`ModularFormsKB/Milne/Ch7/FunctionFieldCounterexample.lean`).
- **Corrected statement:** assume $k_0$ perfect (Milne assumes this from pdf p. 93 on, but not in Theorem 7.2):
  `ModularFormsKB.Milne.CurveFunctionFieldEquivalencePerfect`, proved unconditionally:
  `ModularFormsKB.Milne.curveFunctionFieldEquivalencePerfect` (`ModularFormsKB/Milne/Ch7/CurveEquivalence.lean`,
  `ModularFormsKB/Milne/Ch7/GeometricConstants.lean`).

## 2026-11-07: Milne Section 12 named statements

Two of our formalized statements are false as stated (the book is right; the Lean encodings drop a hypothesis).
The corrected forms are named statements in `ModularFormsKB/Milne/Ch12/Corrected.lean`
(`SerreTateFreeTateModuleQuadratic`, `ClassGroupActionPrincipalNormalized`); neither corrected form is proved yet.
- **`SerreTateFreeTateModule`** (Remark 12.12, `ModularFormsKB/Milne/Ch12/GaloisCM.lean`). The order $R$ may be the
  order $\mathbb Z$ of $K = \mathbb Q$. **Counterexample:** $E\colon y^2 = x^3 - x$ over $\mathbb R$ (every elliptic
  curve over $\mathbb R$ has $\mathrm{End}_{\mathbb R}(E) = \mathbb Z$), $i\colon\mathbb Z \cong \mathrm{End}(E)$,
  $\omega = 1$: then $R = \mathbb Z + \mathbb Z\omega$ but $t$ and $\omega t = t$ are never linearly independent.
  **Refuted in Lean:** `ModularFormsKB.Milne.not_serreTateFreeTateModule`
  (`ModularFormsKB/Milne/Ch12/EndInteger.lean`). **Corrected:** add $[K:\mathbb Q] = 2$ (Milne's standing assumption
  that $K$ is quadratic imaginary).
- **`ClassGroupActionPrincipal`** (Proposition 12.21, `ModularFormsKB/Milne/Ch12/Isogenies.lean`). The compatibility
  clause quantifies over every ring isomorphism $i\colon R \cong \mathrm{End}(E)$, including $i \circ c$ with $c$
  complex conjugation of $R$. For $i \circ c$ the kernel $\mathrm{Ker}(\mathfrak a)$ is the kernel of $\bar{\mathfrak a}$
  for $i$, so an $\mathfrak a$-isogeny for $i\circ c$ is an $\bar{\mathfrak a}$-isogeny for $i$, with target
  $[\bar{\mathfrak a}]\cdot E = [\mathfrak a]^{-1}\cdot E$ (Proposition 12.20, proved as `aIsogenyExists`, supplies
  both isogenies). The clause then forces $[\mathfrak a]\cdot x = [\mathfrak a]^{-1}\cdot x$, i.e. $[\mathfrak a]^2 = 1$
  by simple transitivity. **Counterexample:** $R = \mathcal O_K$, $K = \mathbb Q(\sqrt{-23})$, $\mathrm{Cl}(R) \cong
  \mathbb Z/3$. **Corrected:** quantify only over normalized $i$, e.g. those for which $i(a)$ acts on the invariant
  differential by $\iota(a)$ for a fixed embedding $\iota\colon K \to k$ (Milne's normalization via the tangent space).
  Not refuted in Lean: that needs a curve with $\mathrm{End}(E) \cong R$ for $R$ with a class of order at least $3$,
  whose $j$-invariant is irrational.

## 2026-10-29: Milne, *Modular Functions and Modular Forms* v1.31, Section 4

Corrections to the book (`milne2017mf`), found while formalizing Chapter 4; the Lean statements use the corrected forms.
- **Definition 4.23 / Proposition 4.25** (automorphy factors and line bundles). Definition 4.23 admits $j \equiv 0$,
  which satisfies (a) and (b) but corresponds to no pair $(L, i)$: a trivialization gives an *action*
  $\gamma(\tau, z) = (\gamma\tau, j_\gamma(\tau)z)$, which forces $j_1 = 1$ and $j_\gamma(\tau) \ne 0$.
  **Counterexample:** $j_\gamma(\tau) = 0$ for all $\gamma, \tau$. **Corrected:** the bijection of 4.25 is with
  automorphy factors satisfying $j_1 = 1$ (`ModularFormsKB.Milne.isAutomorphyFactor_iff_fiberAction`). The remark "so
  also is $j^k$ for every integer $k$" needs $j$ nowhere zero when $k < 0$ (`IsAutomorphyFactor.zpow`).
- **Theorem 4.28 and Theorem 4.33** are stated for $2k \ge 2$, and the proof given needs $2k > 2$. The proof bounds
  the summand for $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix}$ by $|cz+d|^{-2k}$
  (`ModularFormsKB.Milne.poincareSummand_norm_le`) and compares with $\sum_{(c,d)\ne 0}|cz+d|^{-2k}$, which it bounds
  by $r(z)^{-2k}\sum_{v \ne 0}\|v\|^{-2k}$ (`poincareSeries_bound`, through Mathlib's
  `EisensteinSeries.summable_one_div_norm_rpow`, which assumes exponent $> 2$). **In weight 2 both majorants diverge**,
  proved: for every $z \in \mathbb H$, $\sum_{(c,d)\ne 0}|cz+d|^{-2}$ is not summable
  (`ModularFormsKB.Milne.not_summable_norm_mul_add_rpow_neg_two`), and $\sum_{v \in \mathbb Z^2 \smallsetminus 0}
  \|v\|^{-2}$ is not summable (`ModularFormsKB.Milne.not_summable_norm_rpow_neg_two`), both in
  `ModularFormsKB/Milne/Ch4/WeightTwoDivergence.lean` (for $c \ge 1$, $0 \le d < c$: $|cz+d| \le c(|z|+1)$, so row $c$
  contributes at least $1/(c(|z|+1)^2)$, and $\sum 1/c$ diverges). So the argument of the book gives nothing in weight 2.
  **Corrected:** $k \ge 2$ (`PoincareSeriesModular`, `PoincarePetersson`, proved as `poincareSeriesModular`,
  `poincarePetersson`). The weight-2 Poincaré series itself is not absolutely convergent either: for
  $\Gamma = \mathrm{SL}_2(\mathbb Z)$ and $n = 0$ its terms over $\Gamma_\infty\backslash\Gamma$ are $|cz+d|^{-2}$ over
  coprime bottom rows, and already the rows $(p, d)$, $p$ prime, $0 < d < p$, give a divergent sum because
  $\sum_p 1/p$ diverges (`ModularFormsKB.Milne.not_summable_poincareTerm_weight_two`, same file).
- **Theorem 4.29** says the $\varphi_n$, $n \ge 1$, span $M_k(\Gamma)$. They are cusp forms (Theorem 4.28 (b)), so they
  span at most $S_k(\Gamma)$; for $\Gamma = \Gamma(1)$, $k = 2$: $M_2 = \mathbb C G_2 \ne 0 = S_2$.
  **Corrected:** they span $S_k(\Gamma)$, which is what Corollary 4.34 proves (`poincareSeries_span`).

## 2026-10-29: Milne, *Modular Functions and Modular Forms* (`milne2017mf`), chapters 8 and 9

Corrections to the book, recorded where the formal statement departs from it.
- **Theorem 9.6** (pdf p. 104) asks that $L(s)$ converge absolutely at $s = k - \delta$ (weight $2k$).
  **Counterexample:** for a nonzero modular form (in particular a nonzero cusp form) of weight $2k$, $k \ge 1$, on
  $\Gamma_0(N)$ with coefficients $a_n$, $\sum_{n\ge1}|a_n|n^{-\sigma}$ diverges for every $\sigma \le k$; proved:
  `ModularFormsKB.Milne.not_lseriesSummable_of_ne_zero`, from `eq_zero_of_lseriesSummable` (any $\Gamma_0(N)$-invariant
  function of weight $2k$ with such a $q$-expansion and $\sum|a_n|n^{-k} < \infty$ is $0$). So as printed the theorem
  applies only to $f = 0$: its hypotheses force $a_n = 0$ for all $n$ (`weil_theorem_book_coeff_eq_zero`), all in
  `ModularFormsKB/Milne/Ch9/WeilPrinted.lean`. The proof is elementary (no Rankin–Selberg estimate): with
  $t = \operatorname{Im} w$, $t^k|f(w)| \le \sum_n t^k|a_n|e^{-2\pi nt}$, whose $n$-th term is
  $|a_n|n^{-k}(nt)^ke^{-2\pi nt} \le |a_n|n^{-k}k!/(2\pi)^k$ and tends to $0$, so $t^k|f(w)| \to 0$ as $t \to 0^+$ by
  dominated convergence; $y^{2k}|f|^2$ is $\Gamma_0(N)$-invariant and
  $\operatorname{Im}\left(\begin{smallmatrix}1&0\\Nm&1\end{smallmatrix}\tau\right) \to 0$, so $f = 0$. (The earlier
  wording of this entry argued through the Rankin–Selberg estimate $\sum_{n\le x}|a_n|^2 \asymp x^{2k}$; that route is
  not needed and was not formalized.) **Corrected** (Weil; checked against Miyake, *Modular Forms*, Theorem 4.3.15,
  whose last sentence asks that $L(s; f)$ be absolutely convergent at $s = k_{\mathrm{Miyake}} - \delta$ for some
  $\delta > 0$, Miyake's weight being $k_{\mathrm{Miyake}} = 2k$): convergence at $s = 2k - \delta$
  (`ModularFormsKB.Milne.weil_theorem`; the printed form `weil_theorem_book` follows from it).
- **Example 8.9** (pdf p. 100) says the moduli variety for $N = 2$ is $\mathbb A^1$ with universal curve
  $Y^2Z = X(X - Z)(X - \lambda Z)$. **Counterexample:** at $\lambda = 0$ and $\lambda = 1$ this cubic is singular
  (discriminant $16\lambda^2(\lambda - 1)^2 = 0$), so it is not a family of elliptic curves over $\mathbb A^1$, and
  $\mathcal E_2(k)$ has no element over those points. **Corrected:** the fine moduli variety is the Legendre line
  $\mathbb A^1 \smallsetminus \{0, 1\} = \operatorname{Spec} k[\lambda, (\lambda(\lambda - 1))^{-1}]$ (characteristic
  $\ne 2$), and the map $\mathcal E_2(k) \to (\mathbb A^1 \smallsetminus \{0,1\})(k)$ is a bijection for algebraically
  closed $k$ (Katz–Mazur 8.2; Tau Ceti's `existsUnique_legendre` over rings with $2$ invertible).

## 2026-10-29: Milne, *Modular Functions and Modular Forms* v1.31, Proposition 12.3(c)

- **Book statement** (`milne2017mf`, Section 12, pdf p. 122): for an order $R$ of a quadratic imaginary field $K$ and an
  $R$-submodule $\mathfrak a$ of $K$, (a) projective $\Leftrightarrow$ (b) $R = \{x \mid x\mathfrak a \subseteq
  \mathfrak a\}$ $\Leftrightarrow$ (c) $\mathfrak a = x\cdot\mathcal O_K$ for an idele $x$, "i.e. $\mathfrak a\mathcal
  O_v = x_v\mathcal O_v$ for all primes $v$ of $\mathcal O_K$".
- **Counterexample:** (c) as written holds for every lattice $\mathfrak a$ (each $\mathfrak a\mathcal O_v$ is a nonzero
  fractional ideal of the discrete valuation ring $\mathcal O_v$, hence principal), while (b) fails for $\mathfrak a =
  \mathcal O_K$ regarded as an $R$-module when $R \ne \mathcal O_K$.
- **Corrected statement**, proved: (c) $\mathfrak a$ is locally principal over $R$: $\mathfrak aR_{\mathfrak p} =
  x_{\mathfrak p}R_{\mathfrak p}$ for every maximal ideal $\mathfrak p$ of $R$. For a quadratic field $K$, an order $R$
  and a nonzero fractional ideal $\mathfrak a$ of $R$, (a) $\Leftrightarrow$ (b) $\Leftrightarrow$ (c) is
  `ModularFormsKB.Milne.proper_tfae` (`ModularFormsKB/Milne/Ch12/Orders.lean`, with `IsLocallyPrincipalAt`), proved
  with the standard axioms only.

## 2026-10-29: Milne, *Modular Functions and Modular Forms* v1.31, Section 5

Corrections to the book (`milne2017mf`), found while formalizing Chapter 5; the Lean statements use the corrected forms.
- **Proposition 5.18** omits $k > 0$ (Proposition 5.5 has it). **Counterexample:** in weight $0$ the constant $1$ is an
  eigenform of every $T(n)$ (eigenvalue $\sigma_{-1}(n)$) with $c(1) = 0$. **Corrected:** $k > 0$
  (`ModularFormsKB.Milne.coeff_one_ne_zero_of_eigen`).
- **Example on p. 78**: $E_6(z) = 1 + \frac{54600}{691}\sum\sigma_{11}(n)q^n$ (weight $12$). **Wrong coefficient:**
  $\gamma_6 = 24/B_6 = 24\cdot 2730/691$. **Corrected:** $\frac{65520}{691}$ (`ModularFormsKB.Milne.qExpansion_coeff_E_twelve`).
- **Proof of Proposition 5.26**: "$\bigoplus_k M_k(\mathbb Z) = \mathbb Z[E_2, E_3]$" is false. **Counterexample:** $\Delta$ has
  integer coefficients, $1728\Delta = E_2^3 - E_3^2$, and $E_2, E_3$ are algebraically independent, so
  $\Delta \notin \mathbb Z[E_2, E_3]$. **Corrected:** $\bigoplus_k M_k(\mathbb Z) = \mathbb Z[E_2, E_3, \Delta]$; the proposition
  (a $\mathbb Z$-structure) is true (`ModularFormsKB.Milne.exists_basis_integralForms`).
- **Proposition 5.27** fails in weight $0$ ($k = 0$): with the normalization $n^{2k-1} = n^{-1}$, $T(2)$ acts on the
  constants by $\sigma_{-1}(2) = 3/2$, not an algebraic integer
  (`ModularFormsKB.Milne.exists_nonintegral_eigenvalue_heckeT_zero`). **Corrected:** $k \ge 1$
  (`ModularFormsKB.Milne.isIntegral_of_hasEigenvalue_heckeT`).

The Lemma 5.24 item first recorded here is a gap in a proof, not a wrong statement; it is now under Remarks at the end.

## Remarks

Gaps in the book's proofs of statements that are true; the statements are proved in Lean as stated.
- **Milne, Lemma 5.24** (`milne2017mf`, Section 5, pdf p. 77; recorded 2026-10-29). The
  proof shows only that every left orbit $\Gamma(1)\alpha$ meets every right orbit $\beta\Gamma(1)$. A common system of
  representatives also needs the two numbers of orbits to agree (both are $p + 1$, Remark 5.14 and transposition).
  Proved: `ModularFormsKB.Milne.exists_common_representatives` (`ModularFormsKB/Milne/Ch5/Matrices.lean`).
