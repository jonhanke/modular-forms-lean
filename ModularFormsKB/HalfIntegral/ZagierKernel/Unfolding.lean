/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.Basic
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierReduction
import ModularFormsKB.HalfIntegral.Abstract.KohnenReduction

/-!
# Cycle integrals and the unfolding of Zagier's kernel (reduced)

The cycle integrals are those of `Abstract/Shintani.lean`: for a form $Q$ of discriminant $\Delta > 0$,
`BinQF.cycleIntegral k G Q` is $\int_{C_Q} G(z)\,Q(z,1)^{k-1}\,dz$ along the geodesic of $Q$ (one period if $\Delta$ is
not a square, the whole geodesic between two cusps if it is), and
$$ r_{k,D}(G; m) = \sum_{Q \in \mathcal Q_{|D|m}/\mathrm{SL}_2(\mathbb Z)} \chi_D(Q)\int_{C_Q} G(z)\,Q(z,1)^{k-1}\,dz $$
is `shintaniCoeff k D G m` (for $m \ge 1$ with $(-1)^k m \equiv 0, 1 \bmod 4$).

**Named inputs.**
- `ZagierKernelUnfolding` (Kohnen–Zagier 1981 `kohnenzagier1981`, §II, Prop. [unverified]; Zagier 1975 `zagier1975`
  for $D = 1$): unfolding the Petersson product of $G$ against $f_{k,D,\Delta}$ along the geodesics,
  $$ \langle f_{k,D,\Delta}, G\rangle = U_{k,\Delta}\, r_{k,D}(G; \Delta/|D|),\qquad
     U_{k,\Delta} = \pi\binom{2k-2}{k-1}2^{2-2k}\Delta^{1/2-k} $$
  (`zagierUnfoldConst`), with this library's Petersson product `peterssonOne` (conjugate-linear in the first argument,
  so $\langle f_{k,D,\Delta}, G\rangle$ here is Kohnen–Zagier's $(G, f_{k,D,\Delta})$).
- `KohnenSquareCycle` (Kohnen–Zagier 1981, §II [unverified]; the computation is recorded below): at the square
  discriminant $\Delta = D^2$,
  $$ r_{k,D}(G; |D|) = (-1)^{\lfloor k/2\rfloor}\,|D|^{k-1/2}\,\frac{(k-1)!}{(2\pi)^k}\,L(G, D, k) $$
  (`squareCycleConst`).

**Where the constant of `KohnenSquareCycle` comes from** (derived here, not read off the source). Every form of
discriminant $D^2$ with $\chi_D \ne 0$ is equivalent to $[0, |D|, c]$ with $c$ prime to $D$, $c \bmod |D|$ (class count
not checked: LE-MF-0310). For $Q = [0, |D|, c]$ the geodesic of `BinQF.geodesic` is $z = -c/|D| + it$, $t$ from $0$ to
$\infty$, with $Q(z, 1) = |D|\,it$, so the cycle integral is $|D|^{k-1}i^k\int_0^\infty G(-c/|D| + it)\,t^{k-1}\,dt$ and
$\chi_D(Q) = \left(\frac Dc\right)$. The Gauss sum $\sum_c \left(\frac Dc\right)e(-nc/|D|) = \operatorname{sgn}(D)\left(\frac Dn\right)\sqrt D$
and the Mellin transform $\int_0^\infty e^{-2\pi nt}t^{k-1}dt = (k-1)!(2\pi n)^{-k}$ give
$i^k\operatorname{sgn}(D)\sqrt D\,|D|^{k-1}(k-1)!(2\pi)^{-k}L(G,D,k)$, which is $(-1)^{\lfloor k/2\rfloor}|D|^{k-1/2}(k-1)!(2\pi)^{-k}L(G,D,k)$
when $(-1)^kD > 0$. The three constants `zagierUnfoldConst`, `squareCycleConst` and Kohnen–Zagier's normalization of the
kernel $\Omega$ (`kohnenKernelConst`, `KohnenKernel.lean`) multiply to the constant of Theorem 1 (`kzConstant`): this
is proved (`kohnenKernelConst_mul_unfold_mul_square`), a check of the three against each other and against Theorem 1.
The orientation of $C_Q$ enters $U$ and $S$ with the same sign, so the product does not depend on it.
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **The unfolding constant** $U_{k,\Delta} = \pi\binom{2k-2}{k-1}\,2^{2-2k}\,\Delta^{1/2-k}$ of `ZagierKernelUnfolding`
(Kohnen–Zagier 1981 `kohnenzagier1981`, §II [unverified]), with $2^{2-2k} = 4/4^k$. -/
noncomputable def zagierUnfoldConst (k : ℕ) (Δ : ℕ) : ℝ :=
  π * ((2 * k - 2).choose (k - 1) : ℝ) * (4 / 4 ^ k) * (Δ : ℝ) ^ ((1 : ℝ) / 2 - k)

/-- **The constant of `KohnenSquareCycle`** $(-1)^{\lfloor k/2\rfloor}|D|^{k-1/2}(k-1)!/(2\pi)^k$ (derived in the module
docstring). -/
noncomputable def squareCycleConst (k : ℕ) (D : ℤ) : ℝ :=
  (-1) ^ (k / 2) * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) * (k - 1).factorial / (2 * π) ^ k

/-- The indices $m$ of the Shintani and Kohnen–Zagier series: $m \ge 1$ and $(-1)^k m \equiv 0, 1 \bmod 4$, i.e.
$(-1)^k m$ is a discriminant. -/
def KernelIndex (k m : ℕ) : Prop :=
  1 ≤ m ∧ (((-1) ^ k * m : ℤ) % 4 = 0 ∨ ((-1) ^ k * m : ℤ) % 4 = 1)

/-- **Unfolding Zagier's kernel along the geodesics** (Kohnen–Zagier 1981 `kohnenzagier1981`, §II, Prop.; Zagier 1975
`zagier1975`, §5, for $D = 1$ [unverified]): for $k \ge 2$, $D$ a fundamental discriminant with $(-1)^kD > 0$, $m$ an
index (`KernelIndex`) and $G \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$,
$$ \langle f_{k,D,|D|m}, G\rangle = U_{k,|D|m}\; r_{k,D}(G; m). $$
Reduced to this statement (loose end LE-MF-0310): the proof unfolds
$\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$ against the sum over $Q$ into $\sum_{Q}\int_{\Gamma_Q\backslash\mathbb H}$, and integrates
over the hyperbolic distance to the geodesic $S_Q$. -/
@[kb "kohnenzagier1981" "§II, Prop.: (G, f_{k,D,D'}) = π binom(2k-2,k-1) 2^{2-2k} (DD')^{1/2-k} r_{k,D,D'}(G) [unverified]"]
structure ZagierKernelUnfolding (k : ℕ) : Prop where
  unfold : 2 ≤ k → ∀ D : ℤ, KohnenDisc k D → ∀ m : ℕ, KernelIndex k m → ∀ G : CuspForm 𝒮ℒ (2 * k : ℕ),
    peterssonOne k (zagierKernelChi k D (D.natAbs * m : ℕ)) G =
      (zagierUnfoldConst k (D.natAbs * m) : ℂ) * shintaniCoeff k D G m

/-- **The cycle integrals at the square discriminant $D^2$ give $L(G, D, k)$** (Kohnen–Zagier 1981
`kohnenzagier1981`, §II [unverified]; constant derived in the module docstring): for $k \ge 2$, $D$ a fundamental
discriminant with $(-1)^kD > 0$, $G \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ with coefficients $b$ and $L$ an entire continuation
of $L(G, D, s) = \sum\left(\frac Dn\right)b(n)n^{-s}$,
$$ r_{k,D}(G; |D|) = (-1)^{\lfloor k/2\rfloor}\,|D|^{k-1/2}\,\frac{(k-1)!}{(2\pi)^k}\,L(k). $$ -/
@[kb "kohnenzagier1981" "§II: the cycle integrals of discriminant D² give (-1)^[k/2] |D|^{k-1/2} (k-1)! (2π)^{-k} L(G,D,k) [unverified]"]
structure KohnenSquareCycle (k : ℕ) : Prop where
  square : 2 ≤ k → ∀ D : ℤ, KohnenDisc k D → ∀ (G : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ), Abstract.HasQExp G b →
    ∀ L : ℂ → ℂ, IsEntireLSeries (twistCoeff D b) ((k : ℝ) + 1) L →
      shintaniCoeff k D G D.natAbs = (squareCycleConst k D : ℂ) * L k

/-- $|D|$ is an index (`KernelIndex`) when $D$ is a fundamental discriminant with $(-1)^kD > 0$: then $(-1)^k|D| = D$. -/
theorem kernelIndex_natAbs {k : ℕ} {D : ℤ} (hD : KohnenDisc k D) : KernelIndex k D.natAbs := by
  obtain ⟨hfund, hsign⟩ := hD
  have hD0 : D ≠ 0 := by rintro rfl; simp at hsign
  have hval : ((-1) ^ k * (D.natAbs : ℕ) : ℤ) = D := by
    rcases neg_one_pow_eq_or ℤ k with h | h
    · rw [h, one_mul] at hsign ⊢
      rw [Int.natCast_natAbs, abs_of_pos hsign]
    · rw [h] at hsign ⊢
      rw [Int.natCast_natAbs, abs_of_neg (by linarith)]
      ring
  refine ⟨Int.natAbs_pos.2 hD0, ?_⟩
  rw [hval]
  rcases hfund with ⟨h1, -⟩ | ⟨m, rfl, -, -⟩
  · exact Or.inr h1
  · left; omega

end ModularFormsKB.HalfIntegral
