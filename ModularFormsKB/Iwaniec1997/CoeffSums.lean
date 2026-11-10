import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import ModularFormsKB.Citation
/-!
# Iwaniec, Section 5.1: sums of Fourier coefficients of cusp forms

H. Iwaniec, *Topics in Classical Automorphic Forms* (`iwaniec1997`), Section 5.1, pp. 70-72. Page numbers are printed
pages.

Setting: an arithmetic subgroup $\Gamma$ of $\mathrm{GL}_2(\mathbb R)$, an integer weight $k$ and a cusp form $f$ of
weight $k$ for $\Gamma$ (Mathlib's `CuspFormClass`). The Fourier coefficients $a(n)$ are the coefficients of Mathlib's
`qExpansion` at the width $h$ of the cusp $\infty$ (`Subgroup.strictWidthInfty`), so
$f(z) = \sum_n a(n) e(nz/h)$; the book normalizes $h = 1$. Implied constants depend on $f$.

## Items
- **Theorem 5.1** (5.4), $\sum_{n \le N} |a(n)|^2 \ll N^k$, is Mathlib's
  `CuspFormClass.exists_sum_range_norm_sq_qExpansion_coeff_le`.
- **Corollary 5.2** (5.8), $\sum_{n\le N} |a(n)| \ll N^{(k+1)/2}$: `sum_norm_qExpansion_coeff_le` (proved, from
  Theorem 5.1 and Cauchy's inequality).
- **Theorem 5.3** (5.9), $\sum_{n \le N} a(n) e(\alpha n) \ll N^{k/2}\log 2N$ uniformly in $\alpha$: the named input
  `ExponentialSumBound` (the book's proof is a line integral of $f$ against a geometric sum; not formalized).
- **Corollary 5.4** (5.10), the same bound for $n$ restricted to a residue class: `sum_qExpansion_coeff_modEq_le`
  (proved from Theorem 5.3 by additive characters, as in the book).
-/

open Complex Finset
open scoped Real

noncomputable section

namespace ModularFormsKB.Iwaniec1997

variable {k : ℕ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
  {F : Type*} [FunLike F UpperHalfPlane ℂ] [CuspFormClass F Γ (k : ℤ)]

/-- **Corollary 5.2** (5.8): for a cusp form $f$ of weight $k$ there is $C$ with
$\sum_{1 \le n \le N} |a(n)| \le C N^{(k+1)/2}$ for all $N \ge 1$. -/
@[kb "iwaniec1997" "Section 5.1, Corollary 5.2, (5.8), p. 71"]
theorem sum_norm_qExpansion_coeff_le (f : F) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Icc 1 N, ‖(UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n‖ ≤
        C * (N : ℝ) ^ (((k : ℝ) + 1) / 2) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_sum_range_norm_sq_qExpansion_coeff_le f
  set a : ℕ → ℝ := fun n ↦ ‖(UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n‖ with ha
  set K : ℝ := max C 0 * 2 ^ k with hK
  have hK0 : 0 ≤ K := mul_nonneg (le_max_right _ _) (by positivity)
  refine ⟨Real.sqrt K, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 ≤ ∑ n ∈ Icc 1 N, a n := Finset.sum_nonneg fun n _ => norm_nonneg _
  have h1 : (∑ n ∈ Icc 1 N, a n) ^ 2 ≤ (Icc 1 N).card * ∑ n ∈ Icc 1 N, a n ^ 2 :=
    by simpa using Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun _ => (1 : ℝ)) a
  have h2 : ∑ n ∈ Icc 1 N, a n ^ 2 ≤ ∑ n ∈ Finset.range (N + 1), a n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
      simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega) (fun _ _ _ => sq_nonneg _)
  have h3 : ∑ n ∈ Finset.range (N + 1), a n ^ 2 ≤ max C 0 * ((N : ℝ) + 1) ^ k :=
    (hC (N + 1)).trans (by
      push_cast
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have h4 : ((N : ℝ) + 1) ^ k ≤ 2 ^ k * (N : ℝ) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hcard : ((Icc 1 N).card : ℝ) = N := by simp
  have h5 : (∑ n ∈ Icc 1 N, a n) ^ 2 ≤ K * (N : ℝ) ^ (k + 1) := by
    calc (∑ n ∈ Icc 1 N, a n) ^ 2 ≤ N * (max C 0 * (2 ^ k * (N : ℝ) ^ k)) := by
          refine h1.trans ?_
          rw [hcard]
          refine mul_le_mul_of_nonneg_left (h2.trans (h3.trans ?_)) hN0.le
          exact mul_le_mul_of_nonneg_left h4 (le_max_right _ _)
      _ = K * (N : ℝ) ^ (k + 1) := by rw [hK]; ring
  calc ∑ n ∈ Icc 1 N, a n = Real.sqrt ((∑ n ∈ Icc 1 N, a n) ^ 2) := (Real.sqrt_sq hs0).symm
    _ ≤ Real.sqrt (K * (N : ℝ) ^ (k + 1)) := Real.sqrt_le_sqrt h5
    _ = Real.sqrt K * (N : ℝ) ^ (((k : ℝ) + 1) / 2) := by
      rw [Real.sqrt_mul hK0, Real.sqrt_eq_rpow ((N : ℝ) ^ (k + 1)), ← Real.rpow_natCast,
        ← Real.rpow_mul hN0.le]
      congr 2
      push_cast
      ring

/-- **Theorem 5.3** (5.9), a named input (not proved here): for a cusp form $f$ of weight $k$ there is $C$ such that
for every real $\alpha$ and every $N \ge 1$, $\big|\sum_{1\le n \le N} a(n) e(\alpha n)\big| \le C N^{k/2}\log 2N$. -/
@[kb "iwaniec1997" "Section 5.1, Theorem 5.3, (5.9), p. 71"]
structure ExponentialSumBound (f : F) : Prop where
  /-- The uniform bound for the twisted partial sums. -/
  bound : ∃ C : ℝ, ∀ (α : ℝ) (N : ℕ), 1 ≤ N →
    ‖∑ n ∈ Icc 1 N, (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n * cexp (2 * π * I * α * n)‖ ≤
      C * (N : ℝ) ^ ((k : ℝ) / 2) * Real.log (2 * N)

/-- The standard additive character has absolute value one. -/
lemma norm_stdAddChar_aux (q : ℕ) [NeZero q] (x : ZMod q) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The standard additive character at `j * n` is an exponential with frequency `j.val / q`. -/
lemma stdAddChar_mul_nat (q : ℕ) [NeZero q] (j : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (j * (n : ZMod q)) =
      cexp (2 * π * I * (((j.val : ℝ) / q : ℝ) : ℂ) * n) := by
  have h : j * (n : ZMod q) = (((j.val * n : ℕ) : ℤ) : ZMod q) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [h, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- Orthogonality: the sum of a coefficient over a residue class as a character sum. -/
lemma filter_sum_eq (q : ℕ) [NeZero q] (b : ℤ) (S : Finset ℕ) (a : ℕ → ℂ) :
    ∑ n ∈ S.filter (fun n : ℕ ↦ (n : ℤ) ≡ b [ZMOD q]), a n =
      (1 / (q : ℂ)) * ∑ j : ZMod q, ZMod.stdAddChar (-(j * (b : ZMod q))) *
        ∑ n ∈ S, a n * ZMod.stdAddChar (j * (n : ZMod q)) := by
  have key : ∀ n : ℕ, ∑ j : ZMod q, ZMod.stdAddChar (-(j * (b : ZMod q))) *
      ZMod.stdAddChar (j * (n : ZMod q)) = if (n : ℤ) ≡ b [ZMOD q] then (q : ℂ) else 0 := by
    intro n
    have h1 : ∀ j : ZMod q, ZMod.stdAddChar (-(j * (b : ZMod q))) * ZMod.stdAddChar (j * (n : ZMod q))
        = ZMod.stdAddChar (j * ((n : ZMod q) - (b : ZMod q))) := by
      intro j
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [h1]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), ZMod.card]
    have h2 : ((n : ZMod q) - (b : ZMod q) = 0) ↔ (n : ℤ) ≡ b [ZMOD q] := by
      rw [sub_eq_zero, ← ZMod.intCast_eq_intCast_iff]
      simp
    simp only [h2]
    split_ifs <;> simp
  rw [Finset.sum_filter]
  have h3 : ∀ n ∈ S, (if (n : ℤ) ≡ b [ZMOD q] then a n else 0) =
      (1 / (q : ℂ)) * (a n * ∑ j : ZMod q, ZMod.stdAddChar (-(j * (b : ZMod q))) *
        ZMod.stdAddChar (j * (n : ZMod q))) := by
    intro n _
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    rw [key n]
    split_ifs
    · field_simp
    · simp
  rw [Finset.sum_congr rfl h3, ← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Corollary 5.4** (5.10), from Theorem 5.3: there is $C$ such that for every $q \ge 1$, every residue $b$ and
every $N \ge 1$, $\big|\sum_{1 \le n \le N,\ n \equiv b\,(q)} a(n)\big| \le C N^{k/2}\log 2N$. -/
@[kb "iwaniec1997" "Section 5.1, Corollary 5.4, (5.10), p. 72"]
theorem sum_qExpansion_coeff_modEq_le (f : F) (hf : ExponentialSumBound (Γ := Γ) (k := k) f) :
    ∃ C : ℝ, ∀ (q : ℕ), 1 ≤ q → ∀ (b : ℤ) (N : ℕ), 1 ≤ N →
      ‖∑ n ∈ (Icc 1 N).filter (fun n : ℕ ↦ (n : ℤ) ≡ b [ZMOD q]),
          (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n‖ ≤
        C * (N : ℝ) ^ ((k : ℝ) / 2) * Real.log (2 * N) := by
  obtain ⟨C, hC⟩ := hf.bound
  refine ⟨max C 0, fun q hq b N hN => ?_⟩
  have : NeZero q := ⟨by omega⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hB : ∀ α : ℝ, ‖∑ n ∈ Icc 1 N,
      (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n * cexp (2 * π * I * α * n)‖ ≤
      max C 0 * (N : ℝ) ^ ((k : ℝ) / 2) * Real.log (2 * N) := fun α =>
    (hC α N hN).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)) hlog)
  set B : ℝ := max C 0 * (N : ℝ) ^ ((k : ℝ) / 2) * Real.log (2 * N) with hBdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [filter_sum_eq q b (Icc 1 N)]
  have hsum : ‖∑ j : ZMod q, ZMod.stdAddChar (-(j * (b : ZMod q))) *
      ∑ n ∈ Icc 1 N, (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n *
        ZMod.stdAddChar (j * (n : ZMod q))‖ ≤ q * B := by
    refine (norm_sum_le _ _).trans ?_
    have h1 : ∀ j ∈ (Finset.univ : Finset (ZMod q)), ‖ZMod.stdAddChar (-(j * (b : ZMod q))) *
        ∑ n ∈ Icc 1 N, (UpperHalfPlane.qExpansion Γ.strictWidthInfty f).coeff n *
          ZMod.stdAddChar (j * (n : ZMod q))‖ ≤ B := by
      intro j _
      rw [norm_mul, norm_stdAddChar_aux, one_mul]
      simp_rw [stdAddChar_mul_nat]
      exact hB _
    refine (Finset.sum_le_sum h1).trans ?_
    simp
  rw [norm_mul]
  have : ‖(1 / (q : ℂ))‖ = 1 / (q : ℝ) := by simp
  rw [this]
  calc 1 / (q : ℝ) * _ ≤ 1 / (q : ℝ) * (q * B) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B := by field_simp

end ModularFormsKB.Iwaniec1997
