import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import ModularFormsKB.Citation
/-!
# Milne, Section 11: the Ramanujan–Petersson bound (Theorem 11.15, Remark 11.16)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 11, pdf p. 116.

- **Theorem 11.15.** For a cusp form $f = \sum a_nq^n$ of weight $2$ on $\Gamma_0(N)$ which is a normalized eigenform
  for the Hecke operators, $|a_p| \le 2p^{1/2}$ for every prime $p \nmid N$. Milne derives it from the
  Eichler–Shimura relation (Theorem 11.14) and Weil's Riemann hypothesis for the reduction of $X_0(N)$ (Theorem 11.4);
  neither the curve $X_0(N)$ over $\mathbb Q$ nor the Eichler–Shimura relation exists in Mathlib or Tau Ceti.
- **Remark 11.16** (Deligne). For a newform of weight $2k$ on $\Gamma_0(N)$, $|a_p| \le 2p^{(2k-1)/2}$ for $p \nmid N$.

Both are consequences of the named statement `RamanujanPeterssonBound` (Deligne 1974, Théorème 8.2; weight $2$:
Eichler 1954, Shimura 1958, Igusa 1959, with Weil 1948), stated for Tau Ceti's good Hecke eigenforms
(`HeckeRing.GL2.EigenformAwayFromLevel`: nonzero cusp forms on $\Gamma_1(N)$ with a nebentypus, eigenvectors of the
Hecke operators at all indices prime to $N$). A form on $\Gamma_0(N)$ is a form on $\Gamma_1(N)$ with trivial
nebentypus. Milne's weight $2k$ is Tau Ceti's weight $k$ in `RamanujanPeterssonBound`.

The repository's `ModularFormsKB.HalfIntegral.DeligneBound` is the same theorem for the repository's own
normalized eigenforms (eigen for every $T(p)$, including $p \mid N$); this file uses Tau Ceti's notion because
Milne's hypotheses ask for eigenvalues only at $p \nmid N$.
-/

open UpperHalfPlane CongruenceSubgroup ModularForm
open scoped MatrixGroups

namespace ModularFormsKB.Milne

open HeckeRing.GL2

/-- **The Ramanujan–Petersson bound** (Deligne 1974, Théorème 8.2 [unverified]; Milne, Section 11, Theorem 11.15 and
Remark 11.16): for $k \ge 2$ and a good Hecke eigenform $f = \sum a_nq^n$ of weight $k$ on $\Gamma_1(N)$ with
$a_1 = 1$, $|a_p| \le 2p^{(k-1)/2}$ for every prime $p \nmid N$. Named statement. -/
@[kb "milne2017mf" "Section 11, Thm. 11.15 and Rem. 11.16 (pdf p. 116), Deligne's theorem"]
structure RamanujanPeterssonBound : Prop where
  bound : ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : EigenformAwayFromLevel N k), 2 ≤ k →
    (qExpansion 1 f.toCuspForm).coeff 1 = 1 →
    ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      ‖(qExpansion 1 f.toCuspForm).coeff p‖ ≤ 2 * (p : ℝ) ^ (((k : ℝ) - 1) / 2)

/-- **Theorem 11.15** (Milne): a normalized weight-$2$ Hecke eigenform $f = \sum a_nq^n$ on $\Gamma_0(N)$ (trivial
nebentypus on $\Gamma_1(N)$) has $|a_p| \le 2p^{1/2}$ for every prime $p \nmid N$; from `RamanujanPeterssonBound`. -/
@[kb "milne2017mf" "Section 11, Thm. 11.15 (pdf p. 116)"]
theorem abs_coeff_prime_le_weight_two (h : RamanujanPeterssonBound) (N : ℕ) [NeZero N]
    (f : EigenformAwayFromLevel N 2) (_hχ : f.χ = 1) (h1 : (qExpansion 1 f.toCuspForm).coeff 1 = 1)
    (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ‖(qExpansion 1 f.toCuspForm).coeff p‖ ≤ 2 * Real.sqrt p := by
  have := h.bound N 2 f le_rfl h1 p hp hpN
  rw [Real.sqrt_eq_rpow]
  norm_num at this ⊢
  exact this

/-- **Remark 11.16** (Milne; Deligne): a newform $f = \sum a_nq^n$ of weight $2k$ on $\Gamma_0(N)$ (trivial
nebentypus), $k \ge 1$, has $|a_p| \le 2p^{(2k-1)/2}$ for every prime $p \nmid N$; from `RamanujanPeterssonBound`. -/
@[kb "milne2017mf" "Section 11, Rem. 11.16 (pdf p. 116)"]
theorem abs_coeff_prime_le_newform (h : RamanujanPeterssonBound) (N : ℕ) [NeZero N] (k : ℕ) (hk : 1 ≤ k)
    (f : Newform N (2 * k)) (_hχ : f.χ = 1) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ‖(qExpansion 1 f.toCuspForm).coeff p‖ ≤ 2 * (p : ℝ) ^ ((2 * (k : ℝ) - 1) / 2) := by
  have := h.bound N (2 * k) f.toEigenformAwayFromLevel (by omega) f.isNorm p hp hpN
  push_cast at this
  exact this

end ModularFormsKB.Milne
