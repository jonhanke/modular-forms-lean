import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import ModularFormsKB.Citation
/-!
# Milne, Chapter 5: items in Mathlib, restated in the book's form (Lemma 5.3, normalized Eisenstein series)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 68, 78.

## Items
- Lemma 5.3 (`exists_eigenbasis_of_isSymmetric`, `exists_common_eigenbasis_of_isSymmetric`): Mathlib's spectral
  theorem `LinearMap.IsSymmetric.eigenvectorBasis` and the joint eigenspace decomposition
  `LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`, stated as existence of eigenbases.
- The normalized Eisenstein series $E_k = G_k/2\zeta(2k)$, p. 78: Mathlib's `ModularForm.E` of weight $2k$ (Milne
  indexes by $k$), with $q$-expansion $1 + \gamma_k\sum\sigma_{2k-1}(n)q^n$, $\gamma_k = (-1)^k4k/B_k$
  (`qExpansion_coeff_E_milne`), and Milne's three examples (`qExpansion_coeff_E_four`, `qExpansion_coeff_E_six`,
  `qExpansion_coeff_E_twelve`). Milne's Bernoulli numbers are $B_k = |b_{2k}|$ for Mathlib's `bernoulli`.

**Correction.** Milne prints $E_6(z) = 1 + \frac{54600}{691}\sum\sigma_{11}(n)q^n$ (his $E_6$ has weight $12$).
The coefficient is $\gamma_6 = 24/B_6 = 24 \cdot 2730/691 = \frac{65520}{691}$ (`qExpansion_coeff_E_twelve`).
-/

open UpperHalfPlane ModularForm

open scoped ArithmeticFunction.sigma

namespace ModularFormsKB.Milne

/-- Sign of the even Bernoulli numbers: $(-1)^{k+1}b_{2k} > 0$ for $k \ge 1$. -/
theorem sign_bernoulli_two_mul {k : ℕ} (hk : k ≠ 0) :
    0 < (-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ) := by
  have h := riemannZeta_two_mul_nat hk
  have hpos := riemannZeta_re_pos_of_one_lt (x := (2 * k : ℕ)) (by
    have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have : (2 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * k)
    linarith)
  set P : ℝ := (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) / ((Nat.factorial (2 * k) : ℕ) : ℝ) with hP
  have hPpos : 0 < P := by positivity
  have h2 : riemannZeta ((2 * k : ℕ) : ℝ) = (((P * ((-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ)) : ℝ)) : ℂ) := by
    have : (((2 * k : ℕ) : ℝ) : ℂ) = (2 * k : ℂ) := by push_cast; ring
    rw [this, h, hP]
    push_cast
    ring
  rw [h2, Complex.ofReal_re] at hpos
  exact pos_of_mul_pos_right hpos hPpos.le

/-- **Milne, Lemma 5.3(a).** On a finite-dimensional complex vector space with a positive definite Hermitian form
(an inner product space), a Hermitian operator $\alpha$ ($\langle\alpha v, v'\rangle = \langle v, \alpha v'\rangle$) has a
basis of eigenvectors. -/
@[kb "milne2017mf" "Section 5, Lemma 5.3(a) (pdf p. 68)"]
theorem exists_eigenbasis_of_isSymmetric {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {T : V →ₗ[ℂ] V} (hT : T.IsSymmetric) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℂ V), ∀ i, ∃ μ : ℂ, T (b i) = μ • b i := by
  refine ⟨Fin (Module.finrank ℂ V), inferInstance, (hT.eigenvectorBasis rfl).toBasis, fun i => ?_⟩
  exact ⟨(hT.eigenvalues rfl i : ℂ), by simp⟩

/-- **Milne, Lemma 5.3(b).** A family of pairwise commuting Hermitian operators has a basis of common
eigenvectors. (Milne states it for a sequence $\alpha_1, \alpha_2, \dots$; any index type works.) -/
@[kb "milne2017mf" "Section 5, Lemma 5.3(b) (pdf p. 68)"]
theorem exists_common_eigenbasis_of_isSymmetric {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {κ : Type*} (T : κ → V →ₗ[ℂ] V) (hT : ∀ j, (T j).IsSymmetric)
    (hcomm : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℂ V), ∀ i j, ∃ μ : ℂ, T j (b i) = μ • b i := by
  classical
  have hint := LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute (T := T) hT hcomm
  let B := hint.collectedBasis fun α : κ → ℂ =>
    Module.finBasis ℂ (↥(⨅ j, Module.End.eigenspace (T j) (α j)))
  have : Finite (Σ α : κ → ℂ, Fin (Module.finrank ℂ (↥(⨅ j, Module.End.eigenspace (T j) (α j))))) :=
    Module.Finite.finite_basis B
  let e := Finite.equivFin (Σ α : κ → ℂ, Fin (Module.finrank ℂ (↥(⨅ j, Module.End.eigenspace (T j) (α j)))))
  refine ⟨Fin (Nat.card (Σ α : κ → ℂ, Fin (Module.finrank ℂ (↥(⨅ j, Module.End.eigenspace (T j) (α j)))))),
    inferInstance, B.reindex e, fun i j => ?_⟩
  have hm := hint.collectedBasis_mem (fun α : κ → ℂ =>
    Module.finBasis ℂ (↥(⨅ j, Module.End.eigenspace (T j) (α j)))) (e.symm i)
  rw [Submodule.mem_iInf] at hm
  refine ⟨(e.symm i).1 j, ?_⟩
  have := Module.End.mem_eigenspace_iff.mp (hm j)
  simpa [B, Module.Basis.reindex_apply] using this

/-- **The normalized Eisenstein series** (Milne, p. 78): for $k \ge 2$, $E_k = 1 + \gamma_k\sum_{n \ge 1}
\sigma_{2k-1}(n)q^n$ with $\gamma_k = (-1)^k\,4k/B_k$, $B_k = |b_{2k}|$. Here $E_k$ is Mathlib's `ModularForm.E` of weight
$2k$. -/
@[kb "milne2017mf" "Section 5, the normalized Eisenstein series E_k (pdf p. 78)"]
theorem qExpansion_coeff_E_milne {k : ℕ} (hk : 3 ≤ 2 * k) {n : ℕ} (hn : 0 < n) :
    (qExpansion 1 (ModularForm.E hk)).coeff n =
      ((-1) ^ k * (4 * k / |(bernoulli (2 * k) : ℝ)|) : ℝ) * (σ (2 * k - 1) n : ℂ) := by
  have hk0 : k ≠ 0 := by omega
  have hs := sign_bernoulli_two_mul hk0
  rw [EisensteinSeries.E_qExpansion_coeff hk ⟨k, by ring⟩ n, if_neg hn.ne']
  have hb : (bernoulli (2 * k) : ℝ) ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have habs : |(bernoulli (2 * k) : ℝ)| = -((-1 : ℝ) ^ k) * (bernoulli (2 * k) : ℝ) := by
    calc |(bernoulli (2 * k) : ℝ)| = |(-1 : ℝ) ^ (k + 1) * (bernoulli (2 * k) : ℝ)| := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      _ = _ := by rw [abs_of_pos hs, pow_succ]; ring
  rw [habs]
  have hsq : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hs0 : ((-1 : ℝ) ^ k) ≠ 0 := by positivity
  congr 1
  have hbC : ((bernoulli (2 * k) : ℚ) : ℂ) = ((bernoulli (2 * k) : ℝ) : ℂ) := by push_cast; rfl
  rw [hbC]
  have hbC0 : ((bernoulli (2 * k) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hb
  have hs0' : (((-1 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsq' : (((-1 : ℝ) ^ k : ℝ) : ℂ) * (((-1 : ℝ) ^ k : ℝ) : ℂ) = 1 := by exact_mod_cast hsq
  push_cast at hs0' hsq' ⊢
  field_simp
  ring

/-- Milne's example $E_2(z) = 1 + 240\sum\sigma_3(n)q^n$ (weight $4$). -/
@[kb "milne2017mf" "Section 5, the example E_2 (pdf p. 78)"]
theorem qExpansion_coeff_E_four {n : ℕ} (hn : 0 < n) :
    (qExpansion 1 ModularForm.E₄).coeff n = 240 * (σ 3 n : ℂ) := by
  have := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) ⟨2, rfl⟩ n
  rw [if_neg hn.ne'] at this
  rw [show (ModularForm.E₄) = ModularForm.E (by simp : 3 ≤ 4) from rfl, this,
    show bernoulli 4 = -1 / 30 by decide +kernel]
  norm_num

/-- Milne's example $E_3(z) = 1 - 504\sum\sigma_5(n)q^n$ (weight $6$). -/
@[kb "milne2017mf" "Section 5, the example E_3 (pdf p. 78)"]
theorem qExpansion_coeff_E_six {n : ℕ} (hn : 0 < n) :
    (qExpansion 1 ModularForm.E₆).coeff n = -504 * (σ 5 n : ℂ) := by
  have := EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) ⟨3, rfl⟩ n
  rw [if_neg hn.ne'] at this
  rw [show (ModularForm.E₆) = ModularForm.E (by simp : 3 ≤ 6) from rfl, this,
    show bernoulli 6 = 1 / 42 by decide +kernel]
  norm_num

/-- Milne's example $E_6$ (weight $12$), corrected: $E_6(z) = 1 + \frac{65520}{691}\sum\sigma_{11}(n)q^n$ (Milne
prints $54600/691$). -/
@[kb "milne2017mf" "Section 5, the example E_6 (pdf p. 78), corrected"]
theorem qExpansion_coeff_E_twelve {n : ℕ} (hn : 0 < n) :
    (qExpansion 1 (ModularForm.E (by norm_num : 3 ≤ 12))).coeff n = 65520 / 691 * (σ 11 n : ℂ) := by
  rw [EisensteinSeries.E_qExpansion_coeff (k := 12) (by norm_num) ⟨6, rfl⟩ n, if_neg hn.ne',
    show bernoulli 12 = -691 / 2730 by decide +kernel]
  norm_num

end ModularFormsKB.Milne
