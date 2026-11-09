import ModularFormsKB.Milne.Ch5.LevelOnePetersson
import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Milne, Chapter 5: eigenforms for $\Gamma(1)$ (Propositions 5.5, 5.18, 5.21, Corollaries 5.6, 5.19, 5.20,
Example 5.7, Lemma 5.25)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 5, pdf pp. 68–79.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups ModularForm ArithmeticFunction.sigma LSeries.notation

namespace ModularFormsKB.Milne

/-! ### Eigenforms: Propositions 5.5, 5.18, Corollaries 5.6, 5.19, 5.20, Proposition 5.21 -/

/-- Scalar multiplication on the first-variable `q`-expansion coefficients. -/
theorem coeff_smul_modularForm {w : ℤ} (c : ℂ) (f : ModularForm 𝒮ℒ w) (m : ℕ) :
    (qExpansion 1 ⇑(c • f)).coeff m = c * (qExpansion 1 f).coeff m := by
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, PowerSeries.coeff_smul,
    smul_eq_mul]

/-- A level-one modular form of nonzero weight with vanishing coefficients `c(n)`, $n \ge 1$, is zero. -/
theorem eq_zero_of_coeff_eq_zero {k : ℕ} (hk : 0 < k) {f : ModularForm 𝒮ℒ (2 * k)}
    (h : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = 0) : f = 0 := by
  have hc : ⇑f = Function.const _ ((qExpansion 1 f).coeff 0) := by
    funext z
    have hs := ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_SL z
    have h0 : HasSum (fun m : ℕ ↦ (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 (z : ℂ) ^ m)
        ((qExpansion 1 f).coeff 0) := by
      have := hasSum_single (f := fun m : ℕ ↦ (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 (z : ℂ) ^ m)
        0 (fun m hm ↦ by simp [h m (Nat.pos_of_ne_zero hm)])
      simpa using this
    exact hs.unique h0
  have h2 := SlashInvariantForm.wt_eq_zero_of_eq_const (2 * (k : ℤ)) hc
  have h0 : (qExpansion 1 f).coeff 0 = 0 := by
    rcases h2 with h2 | h2
    · omega
    · exact h2
  ext z
  simp [congrFun hc z, h0]

/-- **Normalized eigenform** (Milne, p. 69): a nonzero modular form of weight $2k$ for $\Gamma(1)$ that is an
eigenfunction of every $T(n)$, $n \ge 1$, with $c(1) = 1$. (Milne writes "modular function"; the context, and the
definition of $T(n)$, are for modular forms.) For cusp forms this is Tau Ceti's `HeckeRing.GL2.Eigenform 1 (2 * k)`
with `(qExpansion 1 f.toCuspForm).coeff 1 = 1` (`isNormalizedEigenform_of_eigenform`). -/
@[kb "milne2017mf" "Section 5, normalized eigenform (pdf p. 69)"]
def IsNormalizedEigenform (k : ℕ) (f : ModularForm 𝒮ℒ (2 * k)) : Prop :=
  f ≠ 0 ∧ (∀ n : ℕ, 0 < n → ∃ c : ℂ, heckeT (2 * k) n f = c • f) ∧ (qExpansion 1 f).coeff 1 = 1

/-- **Milne, Proposition 5.18.** Let $k > 0$ and let $f = \sum c(n)q^n \ne 0$ be a modular form of weight $2k$
with $T(n)f = \lambda(n)f$ for all $n \ge 1$. Then $c(1) \ne 0$.

The hypothesis $k > 0$ is needed and is not in Milne's statement (it is in Proposition 5.5): in weight $0$ the
constant $1$ is an eigenform of every $T(n)$ with $c(1) = 0$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.18 (pdf p. 75)"]
theorem coeff_one_ne_zero_of_eigen {k : ℕ} (hk : 0 < k) {f : ModularForm 𝒮ℒ (2 * k)} (hf : f ≠ 0)
    {ev : ℕ → ℂ} (hev : ∀ n : ℕ, 0 < n → heckeT (2 * k) n f = ev n • f) : (qExpansion 1 f).coeff 1 ≠ 0 := by
  intro h1
  apply hf
  refine eq_zero_of_coeff_eq_zero hk fun n hn ↦ ?_
  have h := qExpansion_coeff_one_heckeT k hn.ne' f
  rw [hev n hn, coeff_smul_modularForm, h1, mul_zero] at h
  exact h.symm

/-- **Milne, Proposition 5.18**, second part: if moreover $c(1) = 1$ then $c(n) = \lambda(n)$ for all $n \ge 1$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.18 (pdf p. 75)"]
theorem coeff_eq_eigenvalue_of_eigen {k : ℕ} {f : ModularForm 𝒮ℒ (2 * k)}
    {ev : ℕ → ℂ} (hev : ∀ n : ℕ, 0 < n → heckeT (2 * k) n f = ev n • f) (h1 : (qExpansion 1 f).coeff 1 = 1)
    {n : ℕ} (hn : 0 < n) : (qExpansion 1 f).coeff n = ev n := by
  have h := qExpansion_coeff_one_heckeT k hn.ne' f
  rw [hev n hn, coeff_smul_modularForm, h1, mul_one] at h
  exact h.symm

/-- **Milne, Proposition 5.5.** Let $f = \sum c(n)q^n \ne 0$ be a modular form of weight $2k$, $k > 0$, that is an
eigenfunction of every $T(n)$. Then $c(1) \ne 0$, and if $c(1) = 1$ then $T(n)f = c(n)f$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.5 (pdf p. 68)"]
theorem coeff_one_ne_zero_and_heckeT_eq_of_eigen {k : ℕ} (hk : 0 < k) {f : ModularForm 𝒮ℒ (2 * k)} (hf : f ≠ 0)
    (heig : ∀ n : ℕ, 0 < n → ∃ c : ℂ, heckeT (2 * k) n f = c • f) :
    (qExpansion 1 f).coeff 1 ≠ 0 ∧
      ((qExpansion 1 f).coeff 1 = 1 → ∀ n : ℕ, 0 < n → heckeT (2 * k) n f = (qExpansion 1 f).coeff n • f) := by
  choose! ev hev using heig
  refine ⟨coeff_one_ne_zero_of_eigen hk hf hev, fun h1 n hn ↦ ?_⟩
  rw [hev n hn, coeff_eq_eigenvalue_of_eigen hev h1 hn]

/-- The eigenvalues of a normalized eigenform are its Fourier coefficients (Proposition 5.5). -/
theorem IsNormalizedEigenform.heckeT_eq {k : ℕ} {f : ModularForm 𝒮ℒ (2 * k)} (hf : IsNormalizedEigenform k f)
    {n : ℕ} (hn : 0 < n) : heckeT (2 * k) n f = (qExpansion 1 f).coeff n • f := by
  choose! ev hev using hf.2.1
  rw [hev n hn, coeff_eq_eigenvalue_of_eigen hev hf.2.2 hn]

/-- **Milne, Corollary 5.6.** The Fourier coefficients $c(n)$, $n \ge 1$, of a normalized eigenform are real. -/
@[kb "milne2017mf" "Section 5, Corollary 5.6 (pdf p. 69)"]
theorem IsNormalizedEigenform.coeff_real {k : ℕ} {f : ModularForm 𝒮ℒ (2 * k)} (hf : IsNormalizedEigenform k f)
    {n : ℕ} (hn : 0 < n) : ((qExpansion 1 f).coeff n).im = 0 := by
  have hT := hf.heckeT_eq hn
  set c := (qExpansion 1 f).coeff n with hcdef
  by_cases h0 : (qExpansion 1 f).coeff 0 = 0
  · obtain ⟨g, hg⟩ := (ModularForm.isCuspForm_iff_coeffZero_eq_zero f).2 h0
    have hgT : heckeTCusp (2 * k) n g = c • g := by
      apply CuspForm.toModularFormₗ_injective
      rw [toModularForm_heckeTCusp, map_smul, hg, hT]
    have hP := petersson_heckeTCusp_left k hn.ne' g g
    rw [hgT] at hP
    simp only [levelOnePetersson, map_smul, Submodule.coe_smul, CuspForm.peterssonInnerCosets_smul_left,
      CuspForm.peterssonInnerCosets_smul_right] at hP
    have hne : CuspForm.peterssonInnerCosets ((levelOneCuspEquiv (2 * k)).symm g : CuspForm ((Gamma1 1).map (mapGL ℝ)) (2 * k))
        ((levelOneCuspEquiv (2 * k)).symm g) ≠ 0 := by
      intro h
      rw [CuspForm.peterssonInnerCosets_self_eq_zero] at h
      have : g = 0 := by simpa using h
      apply hf.1
      rw [← hg, this, map_zero]
    have := mul_right_cancel₀ hne hP
    exact Complex.conj_eq_iff_im.1 this
  · have h := qExpansion_coeff_zero_heckeT k hn.ne' f
    rw [hT, coeff_smul_modularForm] at h
    have h' := mul_right_cancel₀ h0 h
    have hr : c = ((∑ a ∈ n.divisors, (a : ℝ) ^ ((2 * k : ℤ) - 1) : ℝ) : ℂ) := by
      rw [h']; push_cast; rfl
    rw [hr]
    exact Complex.ofReal_im _

/-- **Milne, Corollary 5.19.** Two normalized eigenforms of the same weight with the same eigenvalues are equal.
Here $k > 0$ (in weight $0$ there is no normalized eigenform). -/
@[kb "milne2017mf" "Section 5, Corollary 5.19 (pdf p. 75)"]
theorem IsNormalizedEigenform.eq_of_eigenvalues {k : ℕ} (hk : 0 < k) {f g : ModularForm 𝒮ℒ (2 * k)}
    (hf : IsNormalizedEigenform k f) (hg : IsNormalizedEigenform k g) {ev : ℕ → ℂ}
    (hevf : ∀ n : ℕ, 0 < n → heckeT (2 * k) n f = ev n • f)
    (hevg : ∀ n : ℕ, 0 < n → heckeT (2 * k) n g = ev n • g) : f = g := by
  have key : ∀ m, 0 < m → (qExpansion 1 ⇑(f - g)).coeff m = 0 := fun m hm ↦ by
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, map_sub,
      coeff_eq_eigenvalue_of_eigen hevf hf.2.2 hm, coeff_eq_eigenvalue_of_eigen hevg hg.2.2 hm, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_coeff_eq_zero hk key)

/-- **Milne, Corollary 5.20.** The coefficients of a normalized eigenform satisfy $c(m)c(n) = c(mn)$ for coprime
$m, n$ and $c(p)c(p^n) = c(p^{n+1}) + p^{2k-1}c(p^{n-1})$ for $p$ prime, $n \ge 1$ (here $k \ge 1$, so that
$p \cdot p^{2k-2} = p^{2k-1}$ in `weightChar`). -/
@[kb "milne2017mf" "Section 5, Corollary 5.20 (pdf p. 75)"]
theorem IsNormalizedEigenform.heckeRecursion {k : ℕ} (hk : 0 < k) {f : ModularForm 𝒮ℒ (2 * k)}
    (hf : IsNormalizedEigenform k f) : Miyake.HeckeRecursion (fun n ↦ (qExpansion 1 f).coeff n) (weightChar k) := by
  have hev' : ∀ n : ℕ, 0 < n → heckeT (2 * k) n f = (qExpansion 1 f).coeff n • f := fun n hn ↦ hf.heckeT_eq hn
  have inj := smul_left_injective ℂ hf.1
  refine ⟨fun m n hm hn hmn ↦ ?_, fun p e hp he ↦ ?_⟩
  · apply inj
    have h := congrArg (fun T ↦ T f) (heckeT_mul_of_coprime k hmn)
    simp only [Module.End.mul_apply] at h
    calc _ = heckeT (2 * k) (m * n) f := (hev' _ (Nat.mul_pos hm hn)).symm
      _ = heckeT (2 * k) m (heckeT (2 * k) n f) := h.symm
      _ = _ := by rw [hev' n hn, map_smul, hev' m hm, smul_smul]; exact congrArg (· • f) (mul_comm _ _)
  · apply inj
    have h := congrArg (fun T ↦ T f) (heckeT_prime_mul_prime_pow k hp he)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
    have hz : (p : ℂ) ^ ((2 * k : ℤ) - 1) = (p : ℂ) ^ (2 * k - 1) := by
      rw [show ((2 * k : ℤ) - 1) = ((2 * k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
    rw [hz, hev' (p ^ e) (pow_pos hp.pos e), map_smul, hev' p hp.pos, hev' (p ^ (e + 1)) (pow_pos hp.pos _),
      hev' (p ^ (e - 1)) (pow_pos hp.pos _)] at h
    show _ • f = (_ + (p : ℂ) * weightChar k p * _) • f
    rw [natCast_mul_weightChar hk]
    simp only [add_smul, smul_smul] at h ⊢
    exact (congrArg (· • f) (mul_comm _ _)).trans h

/-- **Milne, Proposition 5.21.** For a normalized eigenform $f$,
$L(f, s) = \prod_p (1 - c(p)p^{-s} + p^{2k-1-2s})^{-1}$, as an identity of formal Dirichlet series (see
`EulerFactor.lean`; the analytic form for cusp forms is Tau Ceti's
`HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd`). -/
@[kb "milne2017mf" "Section 5, Proposition 5.21 (pdf p. 75)"]
theorem IsNormalizedEigenform.hasHeckeEulerProduct {k : ℕ} (hk : 0 < k) {f : ModularForm 𝒮ℒ (2 * k)}
    (hf : IsNormalizedEigenform k f) :
    Miyake.HasHeckeEulerProduct (fun n ↦ (qExpansion 1 f).coeff n) (weightChar k) :=
  (eulerProduct_iff_heckeRelations k _ hf.2.2).2 (hf.heckeRecursion hk)

/-! ### Example 5.7: the discriminant -/

/-- **Milne, Example 5.7.** $\Delta$ is a normalized eigenform of weight $12$. -/
@[kb "milne2017mf" "Section 5, Example 5.7 (pdf p. 69)"]
theorem isNormalizedEigenform_discriminant :
    IsNormalizedEigenform 6 (CuspForm.toModularFormₗ CuspForm.discriminant) := by
  have h1 : (qExpansion 1 ⇑(CuspForm.toModularFormₗ CuspForm.discriminant)).coeff 1 = 1 :=
    ModularForm.discriminant_qExpansion_coeff_one
  refine ⟨?_, fun n _ ↦ ?_, h1⟩
  · intro h
    rw [h] at h1
    simp [qExpansion_zero] at h1
  · obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve
      (heckeTCusp 12 n CuspForm.discriminant)
    have h := toModularForm_heckeTCusp 12 n CuspForm.discriminant
    rw [← hc] at h
    exact ⟨c, h.symm.trans (map_smul _ _ _)⟩

/-- **Milne, Example 5.7**: Ramanujan's conjecture (b) for $\tau(n)$ (the coefficients of $\Delta$; the chapter 4
file names them `ramanujanTau`): $\tau(mn) = \tau(m)\tau(n)$ for coprime $m, n$ and
$\tau(p)\tau(p^n) = \tau(p^{n+1}) + p^{11}\tau(p^{n-1})$. By Proposition 5.1 this is the Euler product of
$L(\Delta, s)$ (`ramanujan_hasHeckeEulerProduct`). -/
@[kb "milne2017mf" "Section 5, Example 5.7 (pdf p. 69); Proposition 5.1 (pdf p. 67)"]
theorem ramanujan_heckeRecursion :
    Miyake.HeckeRecursion (fun n ↦ (qExpansion 1 ModularForm.discriminant).coeff n) (weightChar 6) :=
  isNormalizedEigenform_discriminant.heckeRecursion (by norm_num)

/-- Proposition 5.1 applied to $\Delta$: $L(\Delta, s) = \prod_p (1 - \tau(p)p^{-s} + p^{11-2s})^{-1}$. -/
@[kb "milne2017mf" "Section 5, Proposition 5.1 (pdf p. 67); Example 5.7 (pdf p. 69)"]
theorem ramanujan_hasHeckeEulerProduct :
    Miyake.HasHeckeEulerProduct (fun n ↦ (qExpansion 1 ModularForm.discriminant).coeff n) (weightChar 6) :=
  (eulerProduct_iff_heckeRelations 6 _ ModularForm.discriminant_qExpansion_coeff_one).2 ramanujan_heckeRecursion

/-- **Milne, Proposition 5.2** for $\tau$: $\tau(p)$ is real ("in fact, it is an integer"), and if
$1 - \tau(p)X + p^{11}X^2 = (1 - aX)(1 - a'X)$ then $|\tau(p)| \le 2p^{11/2}$, $|a| = p^{11/2} = |a'|$ and
$a' = \bar a$ are equivalent. -/
@[kb "milne2017mf" "Section 5, Proposition 5.2 (pdf p. 68)"]
theorem ramanujan_eulerFactor_tfae {p : ℕ} (hp : p.Prime) {a a' : ℂ}
    (h : (1 - Polynomial.C ((qExpansion 1 ModularForm.discriminant).coeff p) * Polynomial.X +
      Polynomial.C ((p : ℂ) ^ 11) * Polynomial.X ^ 2 : Polynomial ℂ) =
        (1 - Polynomial.C a * Polynomial.X) * (1 - Polynomial.C a' * Polynomial.X)) :
    ((qExpansion 1 ModularForm.discriminant).coeff p).im = 0 ∧
    [|((qExpansion 1 ModularForm.discriminant).coeff p).re| ≤ 2 * √((p : ℝ) ^ 11),
      ‖a‖ = √((p : ℝ) ^ 11) ∧ ‖a'‖ = √((p : ℝ) ^ 11), a' = (starRingEnd ℂ) a].TFAE := by
  have him : ((qExpansion 1 ModularForm.discriminant).coeff p).im = 0 :=
    isNormalizedEigenform_discriminant.coeff_real hp.pos
  refine ⟨him, ?_⟩
  have hτ : (qExpansion 1 ModularForm.discriminant).coeff p =
      (((qExpansion 1 ModularForm.discriminant).coeff p).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hc : (0 : ℝ) < (p : ℝ) ^ 11 := by have := hp.pos; positivity
  refine eulerFactor_tfae_of_poly hc (t := ((qExpansion 1 ModularForm.discriminant).coeff p).re) ?_
  rw [← hτ]
  push_cast
  exact h

/-! ### Lemma 5.25: Eisenstein series are eigenforms -/

/-- For `k ≥ 1`, `a ^ (2k - 1)` with an integer exponent is the natural-number power. -/
theorem zpow_two_mul_sub_one {k : ℕ} (hk : 1 ≤ k) (a : ℂ) : a ^ ((2 * k : ℤ) - 1) = a ^ (2 * k - 1) := by
  rw [show ((2 * k : ℤ) - 1) = ((2 * k - 1 : ℕ) : ℤ) by omega, zpow_natCast]

/-- The divisor power sum is $\sigma_{2k-1}(n)$. -/
theorem sum_divisors_zpow_eq_sigma {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∑ a ∈ n.divisors, (a : ℂ) ^ ((2 * k : ℤ) - 1)) = ((σ (2 * k - 1) n : ℕ) : ℂ) := by
  simp [zpow_two_mul_sub_one hk, ArithmeticFunction.sigma_apply]

/-- The sequence $\sigma_{2k-1}(n)$ satisfies the Hecke recursion for `weightChar k`. -/
theorem sigma_heckeRecursion {k : ℕ} (hk : 1 ≤ k) :
    Miyake.HeckeRecursion (fun n ↦ ((σ (2 * k - 1) n : ℕ) : ℂ)) (weightChar k) := by
  refine ⟨fun m n _ _ hmn ↦ ?_, fun p e hp he ↦ ?_⟩
  · simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn, Nat.cast_mul]
  · obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [natCast_mul_weightChar hk]
    set q : ℂ := (p : ℂ) ^ (2 * k - 1) with hq
    have key : ∀ i : ℕ, ((σ (2 * k - 1) (p ^ i) : ℕ) : ℂ) = ∑ j ∈ Finset.range (i + 1), q ^ j := by
      intro i
      rw [ArithmeticFunction.sigma_apply_prime_pow hp]
      push_cast
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hq, pow_mul']
    have hp1 : ((σ (2 * k - 1) p : ℕ) : ℂ) = 1 + q := by
      have := key 1
      simp only [pow_one] at this
      rw [this]
      simp [Finset.sum_range_succ]
    have h2 : ∑ j ∈ Finset.range (e' + 1 + 1), q ^ j = ∑ j ∈ Finset.range (e' + 1), q ^ j + q ^ (e' + 1) :=
      Finset.sum_range_succ _ _
    have h3 : ∑ j ∈ Finset.range (e' + 1 + 1 + 1), q ^ j =
        ∑ j ∈ Finset.range (e' + 1), q ^ j + q ^ (e' + 1) + q ^ (e' + 1 + 1) := by
      rw [Finset.sum_range_succ, h2]
    rw [hp1, key (e' + 1), key (e' + 1 + 1), key e', h2, h3]
    ring

/-- The multiplication formula for $\sigma_{2k-1}$ (`Miyake.HeckeMultiplication`). -/
theorem sigma_mul_formula {k : ℕ} (hk : 1 ≤ k) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ((σ (2 * k - 1) m : ℕ) : ℂ) * ((σ (2 * k - 1) n : ℕ) : ℂ) =
      ∑ l ∈ (Nat.gcd m n).divisors, (l : ℂ) ^ ((2 * k : ℤ) - 1) * ((σ (2 * k - 1) (m * n / l ^ 2) : ℕ) : ℂ) := by
  have htfae := Miyake.heckeRecursion_tfae (fun n ↦ ((σ (2 * k - 1) n : ℕ) : ℂ)) (weightChar k)
    (by simp [ArithmeticFunction.sigma_apply]) (weightChar_one k)
    (fun m n _ _ ↦ weightChar_mul k m n)
  have hiff : Miyake.HeckeRecursion (fun n ↦ ((σ (2 * k - 1) n : ℕ) : ℂ)) (weightChar k) ↔
      Miyake.HeckeMultiplication (fun n ↦ ((σ (2 * k - 1) n : ℕ) : ℂ)) (weightChar k) := htfae.out 1 3
  have h := hiff.1 (sigma_heckeRecursion hk) m n hm hn
  rw [h]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [natCast_mul_weightChar hk, zpow_two_mul_sub_one hk]

/-- $B_{2k} \ne 0$ for $k \ge 1$ (via $\zeta(2k) \ne 0$). -/
theorem bernoulli_two_mul_ne_zero {k : ℕ} (hk : 1 ≤ k) : ((bernoulli (2 * k) : ℚ) : ℂ) ≠ 0 := by
  intro h
  have hz := riemannZeta_two_mul_nat (k := k) (by omega)
  rw [h] at hz
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : riemannZeta (2 * k) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  apply this
  rw [hz]
  simp

/-- Coefficients of $\gamma_k^{-1}E_k$ (auxiliary form of `qExpansion_coeff_normalizedE`). -/
theorem coeff_normalizedE_aux {k : ℕ} (hk : 3 ≤ 2 * k) {n : ℕ} (hn : 0 < n) :
    (qExpansion 1 ⇑((-(2 * ((2 * k : ℕ) : ℂ) / (bernoulli (2 * k) : ℂ)))⁻¹ • ModularForm.E hk)).coeff n =
      ((σ (2 * k - 1) n : ℕ) : ℂ) := by
  have hk1 : 1 ≤ k := by omega
  have hβ : (-(2 * ((2 * k : ℕ) : ℂ) / (bernoulli (2 * k) : ℂ))) ≠ 0 := by
    refine neg_ne_zero.2 (div_ne_zero (mul_ne_zero two_ne_zero (Nat.cast_ne_zero.2 (by omega)))
      (bernoulli_two_mul_ne_zero hk1))
  rw [coeff_smul_modularForm, EisensteinSeries.E_qExpansion_coeff hk (even_two_mul k), if_neg hn.ne',
    ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]

/-- $\zeta$-shift: $\sum n^j n^{-s} = \zeta(s - j)$ for $\mathrm{Re}(s) > j + 1$. -/
theorem LSeries_natCast_pow {j : ℕ} {s : ℂ} (hs : (j : ℝ) + 1 < s.re) :
    LSeriesSummable (fun n : ℕ ↦ (n : ℂ) ^ j) s ∧
      LSeries (fun n : ℕ ↦ (n : ℂ) ^ j) s = riemannZeta (s - j) := by
  have hs' : 1 < (s - j).re := by simp; linarith
  have hterm : LSeries.term (fun n : ℕ ↦ (n : ℂ) ^ j) s =
      LSeries.term (fun n : ℕ ↦ ((ArithmeticFunction.zeta n : ℕ) : ℂ)) (s - j) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_sub _ _ hn',
        Complex.cpow_natCast]
      simp [ArithmeticFunction.zeta_apply, hn]
  refine ⟨?_, ?_⟩
  · show Summable _
    rw [hterm]
    exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs'
  · have := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs'
    rw [← this]
    unfold LSeries
    rw [hterm]


/-- **Milne, Lemma 5.25.** The Eisenstein series of weight $2k \ge 4$ is an eigenform of every $T(n)$, with
eigenvalue $\sigma_{2k-1}(n)$. Stated for Mathlib's normalized $E_{2k} = G_k/2\zeta(2k)$ (`ModularForm.E`), a nonzero
multiple of Milne's $G_k$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.25 (pdf p. 78)"]
theorem heckeT_E {k : ℕ} (hk : 3 ≤ 2 * k) {n : ℕ} (hn : 0 < n) :
    heckeT (2 * k) n (ModularForm.E hk) = ((σ (2 * k - 1) n : ℕ) : ℂ) • ModularForm.E hk := by
  have hk1 : 1 ≤ k := by omega
  have hev : Even (2 * k) := even_two_mul k
  refine (ModularForm.qExpansion_inj one_pos one_mem_strictPeriods_SL).1 (PowerSeries.ext fun m ↦ ?_)
  rw [coeff_smul_modularForm]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [qExpansion_coeff_zero_heckeT k hn.ne' (ModularForm.E hk),
      EisensteinSeries.E_qExpansion_coeff_zero hk hev, sum_divisors_zpow_eq_sigma hk1, mul_one]
  · have hne : ∀ a ∈ (Nat.gcd m n).divisors, m * n / a ^ 2 ≠ 0 := by
      intro a ha
      have hd := Nat.dvd_of_mem_divisors ha
      have h1 : a ∣ m := hd.trans (Nat.gcd_dvd_left m n)
      have h2 : a ∣ n := hd.trans (Nat.gcd_dvd_right m n)
      have h3 : a ^ 2 ∣ m * n := by rw [pow_two]; exact mul_dvd_mul h1 h2
      have : 0 < a := Nat.pos_of_mem_divisors ha
      exact (Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hm hn) h3) (by positivity)).ne'
    rw [qExpansion_coeff_heckeT k hn.ne' (ModularForm.E hk) m,
      EisensteinSeries.E_qExpansion_coeff hk hev m, if_neg hm.ne']
    have hsum : ∑ a ∈ (Nat.gcd m n).divisors, (a : ℂ) ^ ((2 * k : ℤ) - 1) * (qExpansion 1 (ModularForm.E hk)).coeff (m * n / a ^ 2) =
        (-(2 * ((2 * k : ℕ) : ℂ) / (bernoulli (2 * k) : ℂ))) *
          ∑ a ∈ (Nat.gcd m n).divisors, (a : ℂ) ^ ((2 * k : ℤ) - 1) * ((σ (2 * k - 1) (m * n / a ^ 2) : ℕ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      rw [EisensteinSeries.E_qExpansion_coeff hk hev, if_neg (hne a ha)]
      ring
    rw [hsum, ← sigma_mul_formula hk1 hm hn]
    ring

/-- **Milne, Lemma 5.25**, normalized eigenform: $\gamma_k^{-1}E_k$ is a normalized eigenform, where
$\gamma_k = (-1)^k\,4k/B_k$ is the first coefficient of $E_k$ (Milne's $B_k = |b_{2k}|$; in Mathlib's Bernoulli numbers
$b$, $\gamma_k = -4k/b_{2k}$, see `EisensteinSeries.E_qExpansion_coeff`). Its coefficients are
$c(n) = \sigma_{2k-1}(n)$ for $n \ge 1$ (`qExpansion_coeff_normalizedE`). -/
@[kb "milne2017mf" "Section 5, Lemma 5.25 (pdf pp. 78-79)"]
theorem isNormalizedEigenform_normalizedE {k : ℕ} (hk : 3 ≤ 2 * k) :
    IsNormalizedEigenform k ((-(2 * ((2 * k : ℕ) : ℂ) / (bernoulli (2 * k) : ℂ)))⁻¹ • ModularForm.E hk) := by
  have h1 : (qExpansion 1 ⇑((-(2 * ((2 * k : ℕ) : ℂ) / (bernoulli (2 * k) : ℂ)))⁻¹ • ModularForm.E hk)).coeff 1 = 1 := by
    rw [coeff_normalizedE_aux hk one_pos]
    simp [ArithmeticFunction.sigma_apply]
  refine ⟨?_, fun n hn ↦ ⟨((σ (2 * k - 1) n : ℕ) : ℂ), ?_⟩, h1⟩
  · intro h
    rw [h] at h1
    simp [qExpansion_zero] at h1
  · rw [map_smul, heckeT_E hk hn, smul_comm]

/-- Lemma 5.25: the coefficients of the normalized eigenform $\gamma_k^{-1}E_k$ are $\sigma_{2k-1}(n)$, $n \ge 1$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.25 (pdf p. 79)"]
theorem qExpansion_coeff_normalizedE {k : ℕ} (hk : 3 ≤ 2 * k) {n : ℕ} (hn : 0 < n) :
    (qExpansion 1 ((-(2 * ((2 * k : ℕ) : ℂ) / (bernoulli (2 * k) : ℂ)))⁻¹ • ModularForm.E hk)).coeff n =
      ((σ (2 * k - 1) n : ℕ) : ℂ) :=
  coeff_normalizedE_aux hk hn

/-- **Milne, Lemma 5.25**, Dirichlet series: $\sum_{n \ge 1}\sigma_{2k-1}(n)n^{-s} = \zeta(s)\zeta(s - 2k + 1)$ for
$\mathrm{Re}(s) > 2k$. -/
@[kb "milne2017mf" "Section 5, Lemma 5.25 (pdf p. 79)"]
theorem LSeries_sigma_eq_riemannZeta_mul {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs : (2 * k : ℝ) < s.re) :
    LSeries (fun n ↦ ((σ (2 * k - 1) n : ℕ) : ℂ)) s = riemannZeta s * riemannZeta (s - (2 * k - 1)) := by
  have hj : ((2 * k - 1 : ℕ) : ℂ) = 2 * k - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs1 : 1 < s.re := by linarith
  have hj' : ((2 * k - 1 : ℕ) : ℝ) + 1 < s.re := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  obtain ⟨hsum, hL⟩ := LSeries_natCast_pow hj'
  have hconv : LSeries (fun n ↦ ((σ (2 * k - 1) n : ℕ) : ℂ)) s =
      LSeries ((fun n : ℕ ↦ ((ArithmeticFunction.zeta n : ℕ) : ℂ)) ⍟ fun n : ℕ ↦ (n : ℂ) ^ (2 * k - 1)) s := by
    refine LSeries_congr (fun {n} hn ↦ ?_) s
    rw [LSeries.convolution_def]
    beta_reduce
    rw [Nat.sum_divisorsAntidiagonal' (fun a b ↦ ((ArithmeticFunction.zeta a : ℕ) : ℂ) * (b : ℂ) ^ (2 * k - 1))]
    simp only [ArithmeticFunction.sigma_apply]
    push_cast
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hd := Nat.dvd_of_mem_divisors hi
    have : n / i ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
      (Nat.pos_of_mem_divisors hi)).ne'
    simp [ArithmeticFunction.zeta_apply, this]
  rw [hconv, LSeries_convolution' (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs1) hsum,
    ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs1, hL, hj]

end ModularFormsKB.Milne
