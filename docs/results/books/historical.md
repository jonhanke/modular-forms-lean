# Historical theorems: Jacobi, *Fundamenta nova* (1829); Ramanujan, *Collected Papers* (1927); Weber, *Elliptische Functionen und algebraische Zahlen* (1891) and *Lehrbuch der Algebra* III (1908); Kronecker, *Werke* 4 and 5: statement map

A topic from several papers, not a book: each row is a central result of one of the papers (the section heading) that the library states in Lean, with its declarations and its status, computed from the Lean kernel: *proved* means proved with only the standard axioms and no unproved input; *conditional* names the unproved inputs (named statements) still assumed; *stated, not proved* that the library states the result as a named structure (a `Prop`) without proof. The theorem numbers in the papers are not yet checked against the papers, and only the results stated in Lean are shown. The statements in the third column are short descriptions, not quotations; read the papers for the exact wording.

Rows: 8. proved: 3; proved in part: 3; proved, conditional: 1; stated, not proved: 1.

## Jacobi 1829

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| § 62 | 176-178 | Fourier series of Jacobi's $\Theta$ and $H$: $\Theta(x) = 1 + 2\sum_{n\ge1}(-1)^n q^{n^2}\cos 2nx$, $H(x) = 2\sum_{n\ge0}(-1)^n q^{(n+1/2)^2}\sin(2n+1)x$, and the quasi-periodicity of $\Theta$ under $x \mapsto x+\pi$, $x \mapsto x+\pi\tau$. | `Historical.Jacobi.jacobiΘ_eq_cos_series`, `Historical.Jacobi.jacobiH_eq_sin_series`, `Historical.Jacobi.jacobiΘ_add_pi`, `Historical.Jacobi.jacobiΘ_add_pi_mul_tau` | proved in part (the theta series are Mathlib's; their identification with Jacobi's analytic definition of $\Theta$, $H$ is not formalized) |
| § 33, (7)-(8) | 77-78 | Jacobi's third-order differential equation satisfied by the modulus $\lambda$ of a transformation as a function of $k$: $3\lambda''^2 - 2\lambda'\lambda''' + \lambda'^2[((1+k^2)/(k-k^3))^2 - ((1+\lambda^2)/(\lambda-\lambda^3))^2\lambda'^2] = 0$. | `Historical.Jacobi.jacobi_modular_equation_ode` | proved |

## Ramanujan, Collected Papers (1927)

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| No. 18, § 7, (30) | 142 | Ramanujan's differential equations $x\,dP/dx = (P^2-Q)/12$, $x\,dQ/dx = (PQ-R)/3$, $x\,dR/dx = (PR-Q^2)/2$ for $|x| < 1$ (and their form in $\tau$). | `Historical.Ramanujan.x_deriv_P`, `Historical.Ramanujan.x_deriv_Q`, `Historical.Ramanujan.x_deriv_R`, `Historical.Ramanujan.ode_tau_P`, `Historical.Ramanujan.ode_tau_Q`, `Historical.Ramanujan.ode_tau_R` | proved |
| No. 30, § 1, (1.71)-(1.74) | 233 | The table of $\Phi_{r,s}$: $Q - P^2 = 288\Phi_{1,2}$, $PQ - R = 720\Phi_{1,4}$, $Q^2 - PR = 1008\Phi_{1,6}$ and $Q(PQ-R) = 720\Phi_{1,8}$. | `Historical.Ramanujan.Q_sub_P_sq`, `Historical.Ramanujan.P_mul_Q_sub_R`, `Historical.Ramanujan.Q_sq_sub_P_mul_R`, `Historical.Ramanujan.Q_mul_P_mul_Q_sub_R` | proved |

## Weber 1891

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| § 21, (9) | 63 | Weber's theta functions as products: $\vartheta_{00} = \eta f^2$, $\vartheta_{01} = \eta f_1^2$, $\vartheta_{10} = \eta f_2^2$. | `Historical.Weber.weberTheta00_eq`, `Historical.Weber.weberTheta01_eq`, `Historical.Weber.weberTheta10_eq` | proved, conditional on `Historical.Weber.JacobiTripleProduct` |

## Weber 1908

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Tabelle VI | 721 | The first rows ($m = 1, \dots, 9$) of Weber's table of class invariants. | `Historical.Weber.WeberTableVIFirstRows` | stated, not proved |

## Kronecker

| Item | Page | Statement | Lean declaration | Status |
|---|---|---|---|---|
| Werke 5, I, art. XXI, § 7, (E) | 118 | Kronecker's general transformation law for the series $\mathrm{Ser}_\rho$ under a unimodular substitution of the periods. | `Historical.Kronecker.ser_transformation_of_two_le`, `Historical.Kronecker.SerTransformationLaw` | proved in part (proved for $\rho \ge 2$ (absolute convergence); $\rho = 0, 1$ stated only) |
| Werke 4, art. XXXI, § V | 361-362 | Invariance of Kronecker's lattice sums, and of his analytic invariant $A$, under equivalence of binary quadratic forms. | `Historical.Kronecker.latticeSum_equiv`, `Historical.Kronecker.KroneckerAInvariance`, `Historical.Kronecker.KroneckerAFormInvariance` | proved in part (the lattice-sum invariance is proved; the invariance of $A$ is stated only) |
