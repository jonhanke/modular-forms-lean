import ModularFormsKB.Milne.Ch12.JIntegralSeries
import ModularFormsKB.Milne.Ch12.JIntegralArith
import ModularFormsKB.Milne.Ch12.ComplexMultiplication
import ModularFormsKB.Citation
/-!
# Milne, Corollary 12.16: $j(z)$ is an algebraic integer for quadratic imaginary $z$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, Cor. 12.16 (pdf p. 125).

Milne derives 12.16 from 12.15 (via a model of $\mathbb C/(\mathbb Z z + \mathbb Z)$ over a number field). We use
instead the classical argument through the modular polynomial (Weber; Lang, *Elliptic Functions*, Ch. 5, Thm. 4
[unverified]), with Milne's Theorem 6.1 as proved in Section 6 here.

Let $F_N \in \mathbb Z[X, Y]$ be the polynomial of `ModularFormsKB.Milne.LevelTwo.cosetPolynomialArithmetic`:
$F_N(j(z), Y) = \prod_c (Y - j(N\gamma_c z))$, the product over the right cosets $\Gamma_0(N)\gamma_c$ in
$\mathrm{SL}_2(\mathbb Z)$. Put $P_N(X) = F_N(X, X) \in \mathbb Z[X]$.

- `leadingCoeff_diagPoly`: **if $N$ is not a square, the leading coefficient of $P_N$ is $\pm 1$.** Write
  $j(N\gamma_c z) = j((az + b)/d)$ with $ad = N$. In $q = e^{2\pi i u}$, $z = Nu$, the factor
  $q^{N^2}(j(Nu) - j(N\gamma_c Nu))$ is $q^{N^2-N}(1 + \dots) - \zeta^{-1} q^{N^2-a^2}(1 + \dots)$ with $|\zeta| = 1$;
  as $a^2 \ne N$, its lowest coefficient has absolute value $1$. Comparing with the lowest coefficient
  $\mathrm{lc}(P_N)$ of $q^M P_N(j(Nu))$ gives $|\mathrm{lc}(P_N)| = 1$.
- `exists_jN_smul_eq_j` (`ModularFormsKB.Milne.Ch12.JIntegralArith`): **a quadratic imaginary $z$ is a fixed point
  of an integer matrix of non-square determinant**: if $az^2 + bz + c = 0$ ($a > 0$), $D = 4ac - b^2$,
  $t = |D| + |b|$, $y = 1 + ta$, $x = y - b$, $N = xy + ac$ and
  $\gamma = \begin{pmatrix} 1 & t \\ a & y \end{pmatrix} \in \mathrm{SL}_2(\mathbb Z)$, then $N\gamma z = z + (c + tx)$
  and $4N = (x + y)^2 + D$ with $x + y > D > 0$, so $N$ is not a square. Hence $j(N\gamma z) = j(z)$, so
  $P_N(j(z)) = 0$.
- `jIntegralAtCM`: **Corollary 12.16**, unconditionally.
-/

open UpperHalfPlane CongruenceSubgroup Polynomial
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.CMIntegral

open TauCeti.ModularForm QSeries LevelTwo

/-- **$j(z)$ is an algebraic integer for every $z \in \mathbb H$ with $az^2 + bz + c = 0$**, $a > 0$, $b$, $c$
integers. -/
theorem isIntegral_j_of_quadratic (z : ℍ) (a b c : ℤ) (ha : 0 < a)
    (hz : (a : ℂ) * (z : ℂ) ^ 2 + b * z + c = 0) : IsIntegral ℤ (j z) := by
  obtain ⟨N, hN, hsq, γ, hγ⟩ := exists_jN_smul_eq_j z a b c ha hz
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨F, hF, -⟩ := (LevelTwo.cosetPolynomialArithmetic N hN).statement
  have hroot : (diagPoly F).eval₂ (algebraMap ℤ ℂ) (j z) = 0 := by
    rw [algebraMap_int_eq, eval_diagPoly_j hN hF z]
    exact Finset.prod_eq_zero (Finset.mem_univ (Quotient.mk _ γ)) (by rw [cosetVal_mk, hγ, sub_self])
  rcases leadingCoeff_diagPoly hN hsq hF with h | h
  · exact ⟨diagPoly F, h, hroot⟩
  · refine ⟨-diagPoly F, ?_, ?_⟩
    · rw [Monic, leadingCoeff_neg, h, neg_neg]
    · rw [eval₂_neg, hroot, neg_zero]

end ModularFormsKB.Milne.CMIntegral

namespace ModularFormsKB.Milne

/-- **Corollary 12.16** (Milne), unconditionally: if $z \in \mathbb H$ generates a quadratic imaginary field, then
$j(z)$ is an algebraic integer. Proof through the modular polynomial (see the module docstring), not through 12.15. -/
@[kb "milne2017mf" "Section 12, Cor. 12.16 (pdf p. 125)"]
theorem jIntegralAtCM : JIntegralAtCM := by
  refine ⟨fun z hz hz2 => ?_⟩
  obtain ⟨a, b, c, ha, hq⟩ := CMIntegral.exists_int_quadratic z hz hz2
  exact CMIntegral.isIntegral_j_of_quadratic z a b c ha hq

end ModularFormsKB.Milne
