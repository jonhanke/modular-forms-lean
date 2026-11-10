import ModularFormsKB.Milne.Ch9.Weil
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Milne, Theorem 9.6 as printed: the convergence hypothesis forces $f = 0$

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 9, Theorem 9.6 (pdf p. 104)
asks that $L(s) = \sum a_n n^{-s}$ converge absolutely at $s = k - \delta$ for a form of weight $2k$. Weil's hypothesis
(Miyake, *Modular Forms*, Theorem 4.3.15, with Miyake's weight $k_{\mathrm{Miyake}} = 2k$) is absolute convergence at
$s = 2k - \delta$. This file proves that the printed hypothesis holds only for $f = 0$.

## Results
- `im_pow_mul_norm_qSeries_le`, `tendsto_qSeriesMajorant`: if $\sum_{n\ge1}|a_n|n^{-k} < \infty$ and $k \ge 1$, then
  $y^k|f(x+iy)| \le h(y)$ with $h(y) \to 0$ as $y \to 0^+$, where $f = \sum_{n\ge0} a_ne^{2\pi i nz}$.
- `eq_zero_of_lseriesSummable`: a function of weight $2k$ ($k \ge 1$) invariant under $\Gamma_0(N)$ whose
  $q$-expansion has $\sum_{n\ge1}|a_n|n^{-k} < \infty$ is $0$. Holomorphy and cuspidality are not used.
- `not_lseriesSummable_of_ne_zero`: for a nonzero modular form (in particular a nonzero cusp form) of weight $2k$ on
  $\Gamma_0(N)$ with $q$-expansion coefficients $a_n$, $\sum|a_n|n^{-\sigma}$ diverges for every real $\sigma \le k$.
- `weil_theorem_book_coeff_eq_zero`: the hypotheses of `weil_theorem_book` (Milne's printed hypotheses) force
  $a_n = 0$ for all $n$.

## Proof (elementary; no Rankin–Selberg estimate)
Put $t = \operatorname{Im} w$. Then $t^k|f(w)| \le \sum_n t^k|a_n|e^{-2\pi nt}$, and for $n \ge 1$ the $n$-th term is
$|a_n|n^{-k}\cdot(nt)^ke^{-2\pi nt} \le |a_n|n^{-k}\cdot k!/(2\pi)^k$; each term tends to $0$ as $t \to 0^+$, so by
dominated convergence $t^k|f(w)| \to 0$ uniformly in $\operatorname{Re} w$. The function $y^{2k}|f|^2$ is
$\Gamma_0(N)$-invariant, and $\gamma_m = \begin{pmatrix}1&0\\Nm&1\end{pmatrix} \in \Gamma_0(N)$ satisfies
$\operatorname{Im}(\gamma_m\tau) \le 1/(N^2m^2\operatorname{Im}\tau) \to 0$. Hence $y^k|f(\tau)| = 0$ for every $\tau$.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups ModularForm

noncomputable section

namespace ModularFormsKB.Milne

/-- $u^k e^{-2\pi u} \le k!/(2\pi)^k$ for $u \ge 0$. -/
lemma pow_mul_exp_neg_two_pi_le (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-(2 * π * u)) ≤ k.factorial / (2 * π) ^ k := by
  have h := Real.pow_div_factorial_le_exp (x := 2 * π * u) (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hf] at h
  rw [le_div_iff₀ (by positivity)]
  calc u ^ k * Real.exp (-(2 * π * u)) * (2 * π) ^ k
      = (2 * π * u) ^ k * Real.exp (-(2 * π * u)) := by ring
    _ ≤ Real.exp (2 * π * u) * k.factorial * Real.exp (-(2 * π * u)) := by gcongr
    _ = k.factorial := by
      rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
      simp

/-- The $n$-th term of the majorant: $t^k|a_n|e^{-2\pi nt}$. -/
def qSeriesMajorantTerm (k : ℕ) (a : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℝ :=
  t ^ k * (‖a n‖ * Real.exp (-(2 * π * n * t)))

/-- The majorant $h(t) = \sum_n t^k|a_n|e^{-2\pi nt}$. -/
def qSeriesMajorant (k : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑' n, qSeriesMajorantTerm k a t n

/-- The dominating sequence: $|a_n|n^{-k}\cdot k!/(2\pi)^k$, plus $|a_0|$ at $n = 0$. -/
def qSeriesBound (k : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  ‖LSeries.term a k n‖ * (k.factorial / (2 * π) ^ k) + if n = 0 then ‖a 0‖ else 0

lemma summable_qSeriesBound {k : ℕ} {a : ℕ → ℂ} (hL : LSeriesSummable a k) :
    Summable (qSeriesBound k a) := by
  refine (hL.norm.mul_right _).add ?_
  exact (hasSum_ite_eq 0 ‖a 0‖).summable

/-- For $n \ge 1$: $|a_n| = |a_n|n^{-k}\cdot n^k$. -/
lemma norm_coeff_eq_norm_term (k : ℕ) (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖a n‖ = ‖LSeries.term a k n‖ * (n : ℝ) ^ k := by
  rw [LSeries.norm_term_eq]; simp only [hn, ↓reduceIte]
  have hpos : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  simp only [natCast_re]
  rw [Real.rpow_natCast, div_mul_cancel₀ _ hpos.ne']

lemma qSeriesMajorantTerm_le {k : ℕ} (a : ℕ → ℂ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (n : ℕ) :
    ‖qSeriesMajorantTerm k a t n‖ ≤ qSeriesBound k a n := by
  have hnn : 0 ≤ qSeriesMajorantTerm k a t n := by unfold qSeriesMajorantTerm; positivity
  rw [Real.norm_of_nonneg hnn]
  unfold qSeriesMajorantTerm qSeriesBound
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one, ite_true,
      LSeries.term_zero, norm_zero, zero_mul, zero_add]
    calc t ^ k * ‖a 0‖ ≤ 1 * ‖a 0‖ := by gcongr; exact pow_le_one₀ ht0 ht1
      _ = ‖a 0‖ := one_mul _
  · simp only [hn, ↓reduceIte, add_zero]; rw [norm_coeff_eq_norm_term k a hn]
    have := pow_mul_exp_neg_two_pi_le k (u := n * t) (by positivity)
    calc t ^ k * (‖LSeries.term a k n‖ * (n : ℝ) ^ k * Real.exp (-(2 * π * n * t)))
        = ‖LSeries.term a k n‖ * ((n * t) ^ k * Real.exp (-(2 * π * (n * t)))) := by ring_nf
      _ ≤ _ := by gcongr

lemma summable_qSeriesMajorantTerm {k : ℕ} {a : ℕ → ℂ} (hL : LSeriesSummable a k) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Summable (qSeriesMajorantTerm k a t) :=
  Summable.of_norm_bounded (summable_qSeriesBound hL) (qSeriesMajorantTerm_le a ht0 ht1)

/-- **The majorant tends to $0$**: $h(t) \to 0$ as $t \to 0^+$ (dominated convergence). -/
theorem tendsto_qSeriesMajorant {k : ℕ} (hk : 0 < k) {a : ℕ → ℂ} (hL : LSeriesSummable a k) :
    Tendsto (qSeriesMajorant k a) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun t n ↦ qSeriesMajorantTerm k a t n) (g := fun _ ↦ (0 : ℝ))
    (summable_qSeriesBound hL) (fun n ↦ ?_) ?_
  · have e : qSeriesMajorant k a = fun t ↦ ∑' n, qSeriesMajorantTerm k a t n := rfl
    rw [e]
    simpa using h
  · have hc : Continuous fun t : ℝ ↦ qSeriesMajorantTerm k a t n := by
      unfold qSeriesMajorantTerm; fun_prop
    have h0 : qSeriesMajorantTerm k a 0 n = 0 := by
      simp [qSeriesMajorantTerm, zero_pow hk.ne']
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [h0] at this
  · have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
    filter_upwards [this] with t ht n
    exact qSeriesMajorantTerm_le a ht.1.le ht.2.le n

lemma norm_cexp_two_pi_I_mul (n : ℕ) (w : ℍ) :
    ‖cexp (2 * π * I * n * (w : ℂ))‖ = Real.exp (-(2 * π * n * w.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [mul_re, mul_im]

/-- **The pointwise bound** $\operatorname{Im}(w)^k\,|f(w)| \le h(\operatorname{Im} w)$ for
$\operatorname{Im} w \le 1$. -/
theorem im_pow_mul_norm_qSeries_le {k : ℕ} {a : ℕ → ℂ} (hL : LSeriesSummable a k) (w : ℍ)
    (hw : w.im ≤ 1) :
    w.im ^ k * ‖Miyake.qSeries a w‖ ≤ qSeriesMajorant k a w.im := by
  have ht := w.im_pos
  have hpow : 0 < w.im ^ k := pow_pos ht k
  have hs : Summable fun n : ℕ ↦ ‖a n * cexp (2 * π * I * n * (w : ℂ))‖ := by
    have h1 := (summable_qSeriesMajorantTerm hL ht.le hw).mul_left (w.im ^ k)⁻¹
    refine h1.congr fun n ↦ ?_
    simp only [qSeriesMajorantTerm, norm_mul, norm_cexp_two_pi_I_mul]
    field_simp
  unfold Miyake.qSeries qSeriesMajorant
  calc w.im ^ k * ‖∑' n : ℕ, a n * cexp (2 * π * I * n * (w : ℂ))‖
      ≤ w.im ^ k * ∑' n : ℕ, ‖a n * cexp (2 * π * I * n * (w : ℂ))‖ := by
        gcongr; exact norm_tsum_le_tsum_norm hs
    _ = ∑' n : ℕ, w.im ^ k * ‖a n * cexp (2 * π * I * n * (w : ℂ))‖ := (tsum_mul_left).symm
    _ = _ := by
      congr 1; ext n
      simp only [qSeriesMajorantTerm, norm_mul, norm_cexp_two_pi_I_mul]

/-- The lower triangular matrix $\begin{pmatrix}1&0\\c&1\end{pmatrix}$. -/
def lowerUnipotent (c : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

lemma lowerUnipotent_mem_Gamma0 (N : ℕ) (m : ℤ) : lowerUnipotent (N * m) ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp [lowerUnipotent]

lemma im_lowerUnipotent_smul_le (c : ℤ) (hc : c ≠ 0) (τ : ℍ) :
    (lowerUnipotent c • τ).im ≤ 1 / ((c : ℝ) ^ 2 * τ.im) := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  have ht := τ.im_pos
  have hc2 : (0 : ℝ) < (c : ℝ) ^ 2 := by positivity
  have hle : ((c : ℝ) * τ.im) ^ 2 ≤ Complex.normSq ((lowerUnipotent c 1 0 : ℂ) * τ + lowerUnipotent c 1 1) := by
    rw [Complex.normSq_apply]
    simp [lowerUnipotent]
    nlinarith [sq_nonneg ((c : ℝ) * τ.re + 1)]
  have hpos : 0 < ((c : ℝ) * τ.im) ^ 2 := by positivity
  rw [div_le_div_iff₀ (hpos.trans_le hle) (by positivity)]
  calc τ.im * ((c : ℝ) ^ 2 * τ.im) = 1 * ((c : ℝ) * τ.im) ^ 2 := by ring
    _ ≤ 1 * Complex.normSq _ := by gcongr

/-- **Theorem 9.6 as printed, key step**: a function of weight $2k$, $k \ge 1$, invariant under $\Gamma_0(N)$, whose
$q$-expansion $\sum_{n\ge0}a_ne^{2\pi inz}$ has $\sum_{n \ge 1}|a_n|n^{-k} < \infty$, vanishes identically. -/
@[kb "milne2017mf" "Section 9, Theorem 9.6 (pdf p. 104), printed hypothesis forces f = 0"]
theorem eq_zero_of_lseriesSummable {k N : ℕ} (hk : 0 < k) (hN : 0 < N) {𝔽 : Type*} [FunLike 𝔽 ℍ ℂ]
    [SlashInvariantFormClass 𝔽 (Gamma0 N) (2 * k : ℤ)] (F : 𝔽) {a : ℕ → ℂ}
    (hF : ∀ τ : ℍ, F τ = Miyake.qSeries a τ) (hL : LSeriesSummable a k) (τ : ℍ) : F τ = 0 := by
  -- the invariant quantity `c = Im(τ)^k |F τ|`
  have hinv : ∀ γ ∈ Gamma0 N, (γ • τ).im ^ k * ‖F (γ • τ)‖ = τ.im ^ k * ‖F τ‖ := by
    intro γ hγ
    have hg : (γ : GL (Fin 2) ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := ⟨γ, hγ, rfl⟩
    have h := SlashInvariantFormClass.norm_petersson_smul (f := F) (f' := F) (τ := τ) hg
    simp only [petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
      Real.norm_eq_abs] at h
    rw [← ModularGroup.sl_moeb] at h
    have h1 : 0 < (γ • τ).im := (γ • τ).im_pos
    have h2 := τ.im_pos
    rw [abs_of_pos h1, abs_of_pos h2] at h
    have e : ∀ x : ℝ, 0 < x → ∀ y : ℝ, y * y * x ^ (2 * k : ℤ) = (x ^ k * y) ^ 2 := by
      intro x _ y; rw [show (2 * k : ℤ) = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast]; ring
    rw [e _ h1, e _ h2] at h
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h
  set c := τ.im ^ k * ‖F τ‖ with hc
  have hc0 : 0 ≤ c := by positivity
  -- the points `γ_m τ` with `Im → 0`
  let t : ℕ → ℝ := fun m ↦ (lowerUnipotent (N * (m + 1 : ℕ)) • τ).im
  have hNm : ∀ m : ℕ, ((N : ℤ) * (m + 1 : ℕ) : ℤ) ≠ 0 := fun m ↦ by positivity
  have ht : Tendsto t atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m ↦ (lowerUnipotent _ • τ).im_pos⟩
    have hb : Tendsto (fun m : ℕ ↦ 1 / ((((N : ℤ) * (m + 1 : ℕ) : ℤ) : ℝ) ^ 2 * τ.im)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      refine Tendsto.atTop_mul_const τ.im_pos ?_
      have : Tendsto (fun m : ℕ ↦ (((N : ℤ) * (m + 1 : ℕ) : ℤ) : ℝ)) atTop atTop := by
        push_cast
        refine Tendsto.const_mul_atTop (by exact_mod_cast hN) ?_
        exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) |>.congr fun m ↦ by simp
      exact (tendsto_pow_atTop two_ne_zero).comp this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun m ↦ (lowerUnipotent _ • τ).im_pos.le) (fun m ↦ im_lowerUnipotent_smul_le _ (hNm m) τ)
  have hlim := (tendsto_qSeriesMajorant hk hL).comp ht
  have hle : ∀ᶠ m in atTop, c ≤ qSeriesMajorant k a (t m) := by
    have h1 : ∀ᶠ m in atTop, t m ≤ 1 := (ht.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds one_pos)
    filter_upwards [h1] with m hm
    show c ≤ _
    rw [← hinv _ (lowerUnipotent_mem_Gamma0 N (m + 1 : ℕ)), hF]
    exact im_pow_mul_norm_qSeries_le hL _ hm
  have hc' : c ≤ 0 := ge_of_tendsto hlim hle
  have : ‖F τ‖ = 0 := by
    have hpos : 0 < τ.im ^ k := pow_pos τ.im_pos k
    nlinarith [norm_nonneg (F τ)]
  exact norm_eq_zero.1 this

/-- **Milne, Theorem 9.6, the printed hypothesis fails for nonzero forms**: if $F \ne 0$ is a modular form (for
instance a cusp form) of weight $2k$, $k \ge 1$, on $\Gamma_0(N)$ with $q$-expansion coefficients $a_n$, then
$\sum_{n\ge1}|a_n|n^{-\sigma}$ diverges for every $\sigma \le k$. -/
@[kb "milne2017mf" "Section 9, Theorem 9.6 (pdf p. 104), printed hypothesis forces f = 0"]
theorem not_lseriesSummable_of_ne_zero {k N : ℕ} (hk : 0 < k) (hN : 0 < N) {𝔽 : Type*} [FunLike 𝔽 ℍ ℂ]
    [SlashInvariantFormClass 𝔽 (Gamma0 N) (2 * k : ℤ)] {F : 𝔽} (hF0 : ⇑F ≠ 0) {a : ℕ → ℂ}
    (hF : ∀ τ : ℍ, F τ = Miyake.qSeries a τ) {σ : ℝ} (hσ : σ ≤ k) : ¬ LSeriesSummable a σ := by
  intro hL
  exact hF0 (funext fun τ ↦ eq_zero_of_lseriesSummable hk hN F hF
    (hL.of_re_le_re (by simpa using hσ)) τ)

/-- **Milne, Theorem 9.6 as printed is vacuous**: under the hypotheses of `weil_theorem_book` (absolute convergence
of $L(s)$ at $s = k - \delta$ for weight $2k$), all coefficients vanish, so the only form it applies to is $f = 0$. -/
@[kb "milne2017mf" "Section 9, Theorem 9.6 (pdf p. 104), printed hypothesis forces f = 0"]
theorem weil_theorem_book_coeff_eq_zero {k N : ℕ} (hk : 0 < k) (hN : 0 < N) {a : ℕ → ℂ} {M : ℝ}
    (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ M) (ha0 : a 0 = 0) {C : ℂ} (hC : C = 1 ∨ C = -1)
    (hΛ : ∃ Ψ : ℂ → ℂ, Differentiable ℂ Ψ ∧ BoundedOnVerticalStrips Ψ ∧
      (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → Ψ s = milneLambda a s) ∧
      ∀ s : ℂ, Ψ s = C * (N : ℂ) ^ ((k : ℂ) - s) * Ψ (2 * k - s))
    (hχ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S →
      ∀ χ : DirichletCharacter ℂ p, χ.IsPrimitive →
        ∃ Ψ Ψ' : ℂ → ℂ, Differentiable ℂ Ψ ∧ Differentiable ℂ Ψ' ∧
          BoundedOnVerticalStrips Ψ ∧ BoundedOnVerticalStrips Ψ' ∧
          (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
            Ψ s = milneTwistLambda χ a s ∧ Ψ' s = milneTwistLambda χ⁻¹ a s) ∧
          ∀ s : ℂ, Ψ s = milneWeilConstant C N χ * (N : ℂ) ^ ((k : ℂ) - s) * Ψ' (2 * k - s))
    {δ : ℝ} (hδ : 0 < δ) (hL : LSeriesSummable a (k - δ)) : a = 0 := by
  obtain ⟨F, hF⟩ := weil_theorem_book hk hN ha ha0 hC hΛ hχ hδ hL
  have hL' : LSeriesSummable a k := hL.of_re_le_re (by simp; linarith)
  have hF' : ∀ τ : ℍ, F τ = Miyake.qSeries a τ := hF
  have h0 := eq_zero_of_lseriesSummable hk hN F (by exact_mod_cast hF') hL'
  refine Miyake.qSeries_coeff_unique ⟨M, ha⟩ ⟨0, (isBigO_zero _ _ : (fun _ : ℕ ↦ (0 : ℂ)) =O[atTop] _)⟩ fun z hz ↦ ?_
  have := h0 ⟨z, hz⟩
  rw [hF'] at this
  rw [show Miyake.qSeries a z = Miyake.qSeries a (⟨z, hz⟩ : ℍ) from rfl, this]
  simp [Miyake.qSeries]

end ModularFormsKB.Milne
