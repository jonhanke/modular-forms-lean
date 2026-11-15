import ModularFormsKB.Miyake.HeckeTrick.HeckeLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Miyake, Corollary 7.2.14: holomorphy of $E_1$, $E_2$ and of $E_2(z) - NE_2(Nz)$

Miyake, *Modular Forms*, §7.2, p. 288. For $k \ge 1$, Hecke's limit $E_k(z;\chi,\psi)$ (`IsHeckeLimit`) is unique
(`IsHeckeLimit.unique`, by the identity theorem). Corollary 7.2.14 says that for $k > 0$ the function
$z \mapsto E_k(z;\chi,\psi)$ is holomorphic on $\mathfrak H$, except when $k = 2$ and $\chi$, $\psi$ are both
trivial, and that in this exceptional case $E_2(z) - pE_2(pz)$ is holomorphic.

* `mdifferentiable_heckeLimit_two`, `mdifferentiable_heckeLimit_one`: $k = 2$ (unless both characters are
  principal) and $k = 1$, from Theorems 7.2.12 and 7.2.13 (the term $Dy^{-1}$ vanishes);
  `mdifferentiable_eisensteinChar`: $k \ge 3$, where $E_k(z;\chi,\psi)$ is the convergent series, from its
  Fourier expansion (Theorem 7.1.3).
* `mdifferentiable_heckeLimit_two_sub`: for $\chi$, $\psi$ the characters mod $1$ (Miyake's $E_2(z)$) and every
  integer $N \ge 1$ (Miyake: every prime $p$), $E_2(z) - NE_2(Nz)$ is holomorphic: the terms $-\pi/y$ and
  $-N\pi/(Ny)$ cancel.
-/

open MeasureTheory Set Filter Topology Complex
open scoped UpperHalfPlane Manifold
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.Miyake.Wave2B

variable {L M : ℕ}

/-- For $k \ge 1$ Hecke's limit is unique: two holomorphic continuations of $E_k(z,s;\chi,\psi)$ to
$\{|s| < \varepsilon\} \cup \{\operatorname{Re}s > 0\}$ agree, by the identity theorem. -/
theorem IsHeckeLimit.unique {k : ℤ} (hk : 1 ≤ k) {χ : DirichletCharacter ℂ L} {ψ : DirichletCharacter ℂ M}
    {z : ℍ} {w w' : ℂ} (h : IsHeckeLimit k χ ψ z w) (h' : IsHeckeLimit k χ ψ z w') : w = w' := by
  obtain ⟨ε, hε, F, hF, hFE, rfl⟩ := h
  obtain ⟨ε', hε', G, hG, hGE, rfl⟩ := h'
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set ε₀ := min ε ε' with hε₀
  have hε₀pos : 0 < ε₀ := lt_min hε hε'
  set U : Set ℂ := Metric.ball 0 ε₀ ∪ {s | 0 < s.re} with hU
  have hUo : IsOpen U := Metric.isOpen_ball.union (isOpen_lt continuous_const continuous_re)
  have hUF : U ⊆ Metric.ball 0 ε ∪ {s | 0 < s.re} :=
    union_subset_union_left _ (Metric.ball_subset_ball (min_le_left _ _))
  have hUG : U ⊆ Metric.ball 0 ε' ∪ {s | 0 < s.re} :=
    union_subset_union_left _ (Metric.ball_subset_ball (min_le_right _ _))
  have hFa := (hF.mono hUF).analyticOnNhd hUo
  have hGa := (hG.mono hUG).analyticOnNhd hUo
  have hpre : IsPreconnected U := by
    refine IsPreconnected.union ((ε₀ / 2 : ℝ) : ℂ) ?_ ?_ (convex_ball (0 : ℂ) ε₀).isPreconnected
      (convex_halfSpace_re_gt 0).isPreconnected
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    · show 0 < (((ε₀ / 2 : ℝ)) : ℂ).re
      rw [Complex.ofReal_re]; positivity
  have h2U : (2 : ℂ) ∈ U := Or.inr (by show (0 : ℝ) < (2 : ℂ).re; norm_num)
  have hev : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have ho : IsOpen {s : ℂ | 2 < (k : ℝ) + 2 * s.re} :=
      isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_re))
    have hmem : (2 : ℂ) ∈ {s : ℂ | 2 < (k : ℝ) + 2 * s.re} := by
      show 2 < (k : ℝ) + 2 * (2 : ℂ).re
      norm_num; linarith
    filter_upwards [ho.mem_nhds hmem] with s hs
    rw [hFE s hs, hGE s hs]
  have h0U : (0 : ℂ) ∈ U := Or.inl (Metric.mem_ball_self hε₀pos)
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa hpre h2U hev h0U

/-- A $q$-series $\sum_{n\ge1}a_ne^{2\pi inNz/M}$ with $|a_n| \le n^K$ ($N \ge 1$) is holomorphic on
$\mathfrak H$. -/
theorem mdifferentiable_tsum_cexp_mul [NeZero M] (N : ℕ) [NeZero N] {a : ℕ+ → ℂ} {K : ℕ}
    (ha : ∀ n : ℕ+, ‖a n‖ ≤ ((n : ℕ) : ℝ) ^ K) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : ℍ ↦ ∑' n : ℕ+, a n * cexp (2 * π * I * (n : ℕ) * ((N : ℂ) * z) / M)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  set c : ℝ := z₀.im / 2 with hc
  have hcpos : 0 < c := by positivity
  set V : Set ℂ := {z | c < z.im} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_im
  have hz₀V : z₀ ∈ V := by show c < z₀.im; rw [hc]; linarith
  set r : ℝ := Real.exp (-(2 * π * c / M)) with hr
  have hr1 : ‖r‖ < 1 := by
    rw [hr, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : 0 < 2 * π * c / M := by positivity
    simpa using this
  have hsum : Summable fun n : ℕ ↦ (n : ℝ) ^ K * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one _ hr1
  have hd : DifferentiableOn ℂ
      (fun z : ℂ ↦ ∑' n : ℕ+, a n * cexp (2 * π * I * (n : ℕ) * ((N : ℂ) * z) / M)) V := by
    refine differentiableOn_tsum_of_summable_norm (u := fun n : ℕ+ ↦ ((n : ℕ) : ℝ) ^ K * r ^ (n : ℕ))
      (hsum.comp_injective PNat.coe_injective) (fun n ↦ ?_) hVo fun n z hz ↦ ?_
    · exact ((differentiable_const _).mul (by fun_prop)).differentiableOn
    · have hz' : c < z.im := hz
      rw [norm_mul]
      refine mul_le_mul (ha n) ?_ (norm_nonneg _) (by positivity)
      rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have hre : (2 * π * I * (n : ℕ) * ((N : ℂ) * z) / M).re = -(2 * π * (n : ℕ) * (N * z.im) / M) := by
        simp [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_natCast]
        field_simp
      rw [hre]
      have hn : (0 : ℝ) ≤ (n : ℕ) := Nat.cast_nonneg _
      have hNy : z.im ≤ N * z.im := le_mul_of_one_le_left (by linarith) hN1
      have h2pn : 0 ≤ 2 * π * (n : ℕ) := by positivity
      have := mul_le_mul_of_nonneg_left (hz'.le.trans hNy) h2pn
      have : 2 * π * c * (n : ℕ) ≤ 2 * π * (n : ℕ) * (N * z.im) := by linarith
      rw [mul_neg, neg_le_neg_iff, mul_div_assoc', div_le_div_iff_of_pos_right hM]
      linarith
  refine (hd.differentiableAt (hVo.mem_nhds hz₀V)).differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
  · simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz₀]

/-- A $q$-series $\sum_{n\ge1}a_ne^{2\pi inz/M}$ with $|a_n| \le n^K$ is holomorphic on $\mathfrak H$. -/
theorem mdifferentiable_tsum_cexp [NeZero M] {a : ℕ+ → ℂ} {K : ℕ} (ha : ∀ n : ℕ+, ‖a n‖ ≤ ((n : ℕ) : ℝ) ^ K) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ ↦ ∑' n : ℕ+, a n * cexp (2 * π * I * (n : ℕ) * z / M)) := by
  simpa using mdifferentiable_tsum_cexp_mul (M := M) 1 ha

lemma norm_eisensteinCharCoeff_two_le [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (n : ℕ+) : ‖eisensteinCharCoeff 2 χ ψ n‖ ≤ ((n : ℕ) : ℝ) ^ 4 := by
  rw [← heckeCoeff_two_zero]
  exact norm_heckeCoeff_le χ ψ (N := 1) (by norm_num) _ n.pos

lemma norm_eisensteinCharCoeff_one_le [NeZero M] (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (n : ℕ+) : ‖eisensteinCharCoeff 1 χ ψ n‖ ≤ ((n : ℕ) : ℝ) ^ 3 := by
  rw [← heckeCoeff_one_zero]
  exact norm_heckeCoeff_le χ ψ (N := 0) (by norm_num) _ n.pos

/-- The value of Hecke's limit in weight two, by Theorem 7.2.12. -/
lemma heckeLimit_two_eq [NeZero L] [NeZero M] {χ : DirichletCharacter ℂ L} {ψ : DirichletCharacter ℂ M}
    (hpar : χ (-1) * ψ (-1) = 1) {E : ℍ → ℂ} (hE : ∀ z, IsHeckeLimit 2 χ ψ z (E z)) (z : ℍ) :
    E z = heckeLimitTwo χ ψ z 0 := by
  refine IsHeckeLimit.unique (by norm_num) (hE z) ?_
  exact ⟨1 / 2, by norm_num, heckeLimitTwo χ ψ z, (differentiableOn_heckeLimitTwo χ ψ z).mono
    (by
      rintro s (hs | hs)
      · have h2 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
        rw [Metric.mem_ball, dist_zero_right] at hs
        show -1 / 2 < s.re
        linarith [neg_abs_le s.re]
      · show -1 / 2 < s.re
        have : 0 < s.re := hs
        linarith), fun s hs ↦ heckeLimitTwo_eq χ ψ hpar z hs, rfl⟩

lemma heckeLimit_one_eq [NeZero L] [NeZero M] {χ : DirichletCharacter ℂ L} {ψ : DirichletCharacter ℂ M}
    (hpar : χ (-1) * ψ (-1) = -1) {E : ℍ → ℂ} (hE : ∀ z, IsHeckeLimit 1 χ ψ z (E z)) (z : ℍ) :
    E z = heckeLimitOne χ ψ z 0 := by
  refine IsHeckeLimit.unique le_rfl (hE z) ?_
  exact ⟨1 / 2, by norm_num, heckeLimitOne χ ψ z, (differentiableOn_heckeLimitOne χ ψ hpar z).mono
    (by
      rintro s (hs | hs)
      · have h2 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
        rw [Metric.mem_ball, dist_zero_right] at hs
        show -1 / 2 < s.re
        linarith [neg_abs_le s.re]
      · show -1 / 2 < s.re
        have : 0 < s.re := hs
        linarith), fun s hs ↦ heckeLimitOne_eq χ ψ hpar z hs, rfl⟩

/-- **Miyake, Corollary 7.2.14**, $k = 2$: if $\chi(-1)\psi(-1) = 1$ and $\chi$, $\psi$ are not both principal,
Hecke's limit $E_2(z;\chi,\psi)$ is a holomorphic function on $\mathfrak H$. -/
@[kb "miyake1989" "Corollary 7.2.14, p. 288 (k = 2)"]
theorem mdifferentiable_heckeLimit_two [NeZero L] [NeZero M] {χ : DirichletCharacter ℂ L}
    {ψ : DirichletCharacter ℂ M} (hpar : χ (-1) * ψ (-1) = 1) (hne : ¬ (χ = 1 ∧ ψ = 1)) {E : ℍ → ℂ}
    (hE : ∀ z, IsHeckeLimit 2 χ ψ z (E z)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E := by
  classical
  have hfun : E = fun z : ℍ ↦ eisensteinCharConst 2 (L := L) ψ +
      eisensteinCharA 2 ψ * ∑' n : ℕ+, eisensteinCharCoeff 2 χ ψ n * cexp (2 * π * I * (n : ℕ) * z / M) := by
    funext z
    rw [heckeLimit_two_eq hpar hE z, heckeLimitTwo_zero, ite_eq_right_iff.mpr (fun h ↦ absurd h hne), zero_div, add_zero]
  rw [hfun]
  exact mdifferentiable_const.add (mdifferentiable_const.mul
    (mdifferentiable_tsum_cexp (norm_eisensteinCharCoeff_two_le χ ψ)))

/-- **Miyake, Corollary 7.2.14**, $k = 1$: if $\chi(-1)\psi(-1) = -1$, Hecke's limit $E_1(z;\chi,\psi)$ is a
holomorphic function on $\mathfrak H$. -/
@[kb "miyake1989" "Corollary 7.2.14, p. 288 (k = 1)"]
theorem mdifferentiable_heckeLimit_one [NeZero L] [NeZero M] {χ : DirichletCharacter ℂ L}
    {ψ : DirichletCharacter ℂ M} (hpar : χ (-1) * ψ (-1) = -1) {E : ℍ → ℂ}
    (hE : ∀ z, IsHeckeLimit 1 χ ψ z (E z)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E := by
  classical
  have hfun : E = fun z : ℍ ↦ ((if L = 1 then 2 * DirichletCharacter.LFunction ψ 1 else 0) +
      (if ψ = 1 then -2 * π * I * (∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹)) *
        DirichletCharacter.LFunction χ 0 else 0)) +
      eisensteinCharA 1 ψ * ∑' n : ℕ+, eisensteinCharCoeff 1 χ ψ n * cexp (2 * π * I * (n : ℕ) * z / M) := by
    funext z
    rw [heckeLimit_one_eq hpar hE z, heckeLimitOne_zero]
  rw [hfun]
  exact mdifferentiable_const.add (mdifferentiable_const.mul
    (mdifferentiable_tsum_cexp (norm_eisensteinCharCoeff_one_le χ ψ)))

/-- The point $Nz$ of $\mathfrak H$, for an integer $N \ge 1$. -/
def natMulPoint (N : ℕ) [NeZero N] (z : ℍ) : ℍ :=
  ⟨(N : ℂ) * z, by
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    simpa [Complex.mul_im] using mul_pos hN z.im_pos⟩

lemma coe_natMulPoint (N : ℕ) [NeZero N] (z : ℍ) : (natMulPoint N z : ℂ) = (N : ℂ) * z := rfl

lemma im_natMulPoint (N : ℕ) [NeZero N] (z : ℍ) : (natMulPoint N z).im = N * z.im := by
  show ((N : ℂ) * z).im = _
  simp [Complex.mul_im]

/-- **Miyake, Corollary 7.2.14**, the exceptional case: for $E_2(z) = E_2(z;\chi_0,\chi_0)$ (the characters mod
$1$) and every integer $N \ge 1$ (Miyake states it for primes $p$), $E_2(z) - NE_2(Nz)$ is holomorphic on
$\mathfrak H$. -/
@[kb "miyake1989" "Corollary 7.2.14, p. 288 (E_2(z) - p E_2(pz))"]
theorem mdifferentiable_heckeLimit_two_sub (N : ℕ) [NeZero N] {E : ℍ → ℂ}
    (hE : ∀ z, IsHeckeLimit 2 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) z (E z)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z ↦ E z - N * E (natMulPoint N z)) := by
  classical
  have hpar : (1 : DirichletCharacter ℂ 1) (-1) * (1 : DirichletCharacter ℂ 1) (-1) = 1 := by
    rw [trivChar_apply_neg_one]; norm_num
  set A := eisensteinCharA 2 (1 : DirichletCharacter ℂ 1)
  set a : ℕ+ → ℂ := fun n ↦ eisensteinCharCoeff 2 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) n
  set C := eisensteinCharConst 2 (L := 1) (1 : DirichletCharacter ℂ 1)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hval : ∀ z : ℍ, E z = C + (-π) / (z.im : ℂ) +
      A * ∑' n : ℕ+, a n * cexp (2 * π * I * (n : ℕ) * z / (1 : ℕ)) := by
    intro z
    rw [heckeLimit_two_eq hpar hE z, heckeLimitTwo_zero, if_pos (show (1 : DirichletCharacter ℂ 1) = 1 ∧ (1 : DirichletCharacter ℂ 1) = 1 from ⟨rfl, rfl⟩)]
    simp [Nat.primeFactors_one, A, a, C]
  have hfun : (fun z ↦ E z - N * E (natMulPoint N z)) = fun z : ℍ ↦ (C - N * C) +
      (A * ∑' n : ℕ+, a n * cexp (2 * π * I * (n : ℕ) * z / (1 : ℕ)) -
        N * (A * ∑' n : ℕ+, a n * cexp (2 * π * I * (n : ℕ) * (natMulPoint N z : ℂ) / (1 : ℕ)))) := by
    funext z
    rw [hval z, hval (natMulPoint N z), im_natMulPoint]
    generalize (∑' n : ℕ+, a n * cexp (2 * π * I * (n : ℕ) * (z : ℂ) / ((1 : ℕ) : ℂ))) = T1
    generalize (∑' n : ℕ+, a n * cexp (2 * π * I * (n : ℕ) * (natMulPoint N z : ℂ) / ((1 : ℕ) : ℂ))) = T2
    have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
    push_cast
    field_simp
    ring
  rw [hfun]
  refine mdifferentiable_const.add (MDifferentiable.sub
    (mdifferentiable_const.mul (mdifferentiable_tsum_cexp (M := 1) (norm_eisensteinCharCoeff_two_le _ _)))
    (mdifferentiable_const.mul ?_))
  simp only [coe_natMulPoint]
  exact mdifferentiable_const.mul (mdifferentiable_tsum_cexp_mul (M := 1) N (norm_eisensteinCharCoeff_two_le _ _))


lemma heckeCoeff_natCast_zero {k : ℕ} (hk : 1 ≤ k) (χ : DirichletCharacter ℂ L) (ψ : DirichletCharacter ℂ M)
    (n : ℕ) : heckeCoeff (k : ℤ) χ ψ 0 n = eisensteinCharCoeff k χ ψ n := by
  unfold heckeCoeff eisensteinCharCoeff
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  congr 2
  rw [show (((k : ℤ) : ℂ) + 2 * 0 - 1) = ((k - 1 : ℕ) : ℂ) by push_cast [Nat.cast_sub hk]; ring,
    Complex.cpow_natCast]

/-- **Miyake, Corollary 7.2.14**, $k \ge 3$: for $\chi(-1)\psi(-1) = (-1)^k$, the convergent series
$E_k(z;\chi,\psi)$ (7.1.1) is holomorphic on $\mathfrak H$ (from its Fourier expansion, Theorem 7.1.3). -/
@[kb "miyake1989" "Corollary 7.2.14, p. 288 (k >= 3)"]
theorem mdifferentiable_eisensteinChar {k : ℕ} (hk : 3 ≤ k) [NeZero L] [NeZero M] (χ : DirichletCharacter ℂ L)
    (ψ : DirichletCharacter ℂ M) (hpar : χ (-1) * ψ (-1) = (-1) ^ k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (eisensteinChar k χ ψ) := by
  have hfun : eisensteinChar k χ ψ = fun z : ℍ ↦ eisensteinCharConst k (L := L) ψ +
      eisensteinCharA k ψ * ∑' n : ℕ+, eisensteinCharCoeff k χ ψ n * cexp (2 * π * I * (n : ℕ) * z / M) := by
    funext z
    have h := (hasSum_eisensteinChar hk χ ψ hpar z).tsum_eq
    have h2 : ∑' n : ℕ+, eisensteinCharA k ψ * (eisensteinCharCoeff k χ ψ n *
        cexp (2 * π * I * (n : ℕ) * z / M)) = eisensteinChar k χ ψ z - eisensteinCharConst k (L := L) ψ := by
      rw [← h]
      exact tsum_congr fun n ↦ (mul_assoc _ _ _).symm
    rw [tsum_mul_left] at h2
    linear_combination -h2
  have hb : ∀ n : ℕ+, ‖eisensteinCharCoeff k χ ψ n‖ ≤ ((n : ℕ) : ℝ) ^ (k + 3) := by
    intro n
    rw [← heckeCoeff_natCast_zero (by omega)]
    exact norm_heckeCoeff_le χ ψ (N := k) (by simp) _ n.pos
  rw [hfun]
  exact mdifferentiable_const.add (mdifferentiable_const.mul (mdifferentiable_tsum_cexp hb))

end ModularFormsKB.Miyake.HeckeTrick
