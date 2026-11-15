import ModularFormsKB.Milne.Wave12.GammaNRiemannRoch

/-!
# A Poincaré series with a pole

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 4 (Poincaré series, pdf pp. 60–64) and
Theorem 1.17 (pdf p. 20).

For a point `u ∈ ℍ`, a natural number `k ≥ 3` and any subgroup `Γ ≤ SL₂(ℤ)` let

  `S_u(z) = ∑_{γ ∈ Γ} ((az + b) - u(cz + d))^{-2k}`,  `γ = (a b; c d)`.

Since `(az + b) - u(cz + d) = (cz + d)(γz - u)`, this is the Poincaré series `∑_γ (cz+d)^{-2k} φ(γz)` of the rational
function `φ(w) = (w - u)^{-2k}`. It converges absolutely and locally uniformly away from the orbit `Γu`: off a finite
set of `γ`, `|(az+b) - u(cz+d)| ≥ ε r(z) (‖(a, b)‖ + ‖(c, d)‖)` (`norm_lin_ge`, with Mathlib's Eisenstein bound
`EisensteinSeries.r_mul_max_le`), and `∑_γ ‖(a, b)‖^{-k} ‖(c, d)‖^{-k} < ∞` for `k ≥ 3` (`summable_bnd`).

* `isMeromorphicModularForm_S`: `S_u` is a meromorphic modular form of weight `2k` for every finite-index `Γ`
  (it is bounded at every cusp);
* `continuousAt_S`: `S_u` is continuous at every point outside `Γu`;
* `tendsto_norm_S`: `|S_u(z)| → ∞` as `z → u`, when `u` is not an elliptic point of `SL₂(ℤ)` (the terms with
  `γu = u` are `(z - u)^{-2k}`, the others are holomorphic at `u`).

This is the existence input for Riemann–Roch on `X(Γ)` for noncongruence `Γ`
(`ModularFormsKB.Milne.Wave13.riemannRoch_of_finiteIndex`).
-/

open UpperHalfPlane Complex Filter Topology Matrix ModularForm EisensteinSeries Function
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave13

variable (u : ℍ) (k : ℕ)

/-! ### The terms -/

/-- `(az + b) - u(cz + d)` for `γ = (a b; c d)`. -/
def lin (ξ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((ξ 0 0 : ℂ) * z + (ξ 0 1 : ℂ)) - (u : ℂ) * ((ξ 1 0 : ℂ) * z + (ξ 1 1 : ℂ))

/-- The term `((az + b) - u(cz + d))^{-2k}`. -/
def term (ξ : SL(2, ℤ)) (z : ℂ) : ℂ := (lin u ξ z ^ (2 * k))⁻¹

theorem denom_sl (ξ : SL(2, ℤ)) (z : ℍ) : denom ξ z = (ξ 1 0 : ℂ) * z + (ξ 1 1 : ℂ) := by
  simp [denom]

theorem coe_smul_sl (ξ : SL(2, ℤ)) (z : ℍ) :
    ((ξ • z : ℍ) : ℂ) = ((ξ 0 0 : ℂ) * z + (ξ 0 1 : ℂ)) / ((ξ 1 0 : ℂ) * z + (ξ 1 1 : ℂ)) := by
  rw [coe_specialLinearGroup_apply]
  simp

theorem lin_eq (ξ : SL(2, ℤ)) (z : ℍ) : lin u ξ z = denom ξ z * (((ξ • z : ℍ) : ℂ) - u) := by
  have hd := denom_ne_zero ξ z
  rw [denom_sl] at hd ⊢
  rw [coe_smul_sl, lin, mul_sub, mul_div_cancel₀ _ hd]
  ring

theorem sl_mul_apply (ξ γ : SL(2, ℤ)) (i j : Fin 2) : (ξ * γ) i j = ξ i 0 * γ 0 j + ξ i 1 * γ 1 j := by
  change ((ξ : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)) i j = _
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem lin_mul (ξ γ : SL(2, ℤ)) (z : ℍ) : lin u (ξ * γ) z = lin u ξ ((γ • z : ℍ) : ℂ) * denom γ z := by
  have hd := denom_ne_zero γ z
  rw [denom_sl] at hd ⊢
  rw [coe_smul_sl, lin, lin]
  simp only [sl_mul_apply, Int.cast_add, Int.cast_mul]
  field_simp
  ring

theorem term_smul (ξ γ : SL(2, ℤ)) (z : ℍ) :
    term u k ξ ((γ • z : ℍ) : ℂ) = denom γ z ^ (2 * k) * term u k (ξ * γ) z := by
  have hd := denom_ne_zero γ z
  rw [term, term, lin_mul, mul_pow, mul_inv, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ hd), mul_one]

/-- The terms are meromorphic everywhere (inverse powers of affine functions). -/
theorem meromorphicAt_term (ξ : SL(2, ℤ)) (z : ℂ) : MeromorphicAt (term u k ξ) z := by
  have : AnalyticAt ℂ (lin u ξ) z := by unfold lin; fun_prop
  exact (this.meromorphicAt.pow _).inv

theorem analyticAt_term {ξ : SL(2, ℤ)} {z : ℂ} (hz : lin u ξ z ≠ 0) : AnalyticAt ℂ (term u k ξ) z := by
  have : AnalyticAt ℂ (lin u ξ) z := by unfold lin; fun_prop
  exact (this.pow _).inv (pow_ne_zero _ hz)

theorem differentiableOn_term {ξ : SL(2, ℤ)} {U : Set ℂ} (hU : ∀ z ∈ U, lin u ξ z ≠ 0) :
    DifferentiableOn ℂ (term u k ξ) U := by
  have : Differentiable ℂ (lin u ξ) := by unfold lin; fun_prop
  exact (this.pow _).differentiableOn.inv fun z hz ↦ pow_ne_zero _ (hU z hz)

/-! ### Estimates -/

/-- The rows of `ξ` as vectors in `ℤ²`. -/
abbrev row (ξ : SL(2, ℤ)) (i : Fin 2) : Fin 2 → ℤ := (ξ : Matrix (Fin 2) (Fin 2) ℤ) i

theorem row_ne_zero (ξ : SL(2, ℤ)) (i : Fin 2) : row ξ i ≠ 0 := by
  intro h
  have hdet := ξ.det_coe
  rw [det_fin_two] at hdet
  have h0 : ξ i 0 = 0 := congrFun h 0
  have h1 : ξ i 1 = 0 := congrFun h 1
  fin_cases i <;> simp_all

theorem row_injective : Injective fun ξ : SL(2, ℤ) ↦ (row ξ 0, row ξ 1) := by
  intro ξ ξ' h
  simp only [Prod.mk.injEq] at h
  ext i j
  fin_cases i
  · exact congrFun h.1 j
  · exact congrFun h.2 j

/-- `ε(r, u) = min(r, 1) / (2(1 + |u|))`. -/
def eps (r : ℝ) : ℝ := min r 1 / (2 * (1 + ‖(u : ℂ)‖))

theorem eps_pos {r : ℝ} (hr : 0 < r) : 0 < eps u r := by
  unfold eps; positivity

/-- Away from `u`, `|ζ - u| ≥ ε(1 + |ζ|)`. -/
theorem eps_mul_le {r : ℝ} (hr : 0 < r) {ζ : ℂ} (h : r ≤ ‖ζ - u‖) : eps u r * (1 + ‖ζ‖) ≤ ‖ζ - u‖ := by
  have hu : 0 ≤ ‖(u : ℂ)‖ := norm_nonneg _
  have hm1 : min r 1 ≤ 1 := min_le_right _ _
  have hmr : min r 1 ≤ r := min_le_left _ _
  have hm0 : 0 < min r 1 := lt_min hr one_pos
  unfold eps
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  by_cases hζ : ‖ζ‖ ≤ 2 * ‖(u : ℂ)‖ + 1
  · nlinarith
  · push Not at hζ
    have : ‖ζ‖ - ‖(u : ℂ)‖ ≤ ‖ζ - u‖ := norm_sub_norm_le _ _
    nlinarith

/-- **The basic estimate**: if `|γz - u| ≥ r` then `|(az+b) - u(cz+d)| ≥ ε r(z) (‖(a,b)‖ + ‖(c,d)‖)`. -/
theorem norm_lin_ge (ξ : SL(2, ℤ)) (z : ℍ) {r : ℝ} (hr : 0 < r) (h : r ≤ ‖((ξ • z : ℍ) : ℂ) - u‖) :
    eps u r * EisensteinSeries.r z * (‖row ξ 0‖ + ‖row ξ 1‖) ≤ ‖lin u ξ z‖ := by
  have hd := denom_ne_zero ξ z
  have h1 := eps_mul_le u hr h
  have hnum : ((ξ • z : ℍ) : ℂ) * denom ξ z = (ξ 0 0 : ℂ) * z + (ξ 0 1 : ℂ) := by
    rw [coe_smul_sl, denom_sl, div_mul_cancel₀]
    rwa [denom_sl] at hd
  have hr0 := r_mul_max_le (z := z) (row_ne_zero ξ 0)
  have hr1 := r_mul_max_le (z := z) (row_ne_zero ξ 1)
  simp only [row] at hr0 hr1
  have e0 : ‖((ξ 0 0 : ℤ) : ℂ) * z + (ξ 0 1 : ℤ)‖ = ‖((ξ • z : ℍ) : ℂ)‖ * ‖denom ξ z‖ := by
    rw [← norm_mul, hnum]
  have e1 : ‖((ξ 1 0 : ℤ) : ℂ) * z + (ξ 1 1 : ℤ)‖ = ‖denom ξ z‖ := by rw [denom_sl]
  rw [lin_eq, norm_mul]
  have hD : 0 ≤ ‖denom ξ z‖ := norm_nonneg _
  have he : 0 ≤ eps u r := (eps_pos u hr).le
  calc eps u r * EisensteinSeries.r z * (‖row ξ 0‖ + ‖row ξ 1‖)
      = eps u r * (EisensteinSeries.r z * ‖row ξ 0‖ + EisensteinSeries.r z * ‖row ξ 1‖) := by ring
    _ ≤ eps u r * (‖((ξ • z : ℍ) : ℂ)‖ * ‖denom ξ z‖ + ‖denom ξ z‖) :=
        mul_le_mul_of_nonneg_left (add_le_add (hr0.trans_eq e0) (hr1.trans_eq e1)) he
    _ = ‖denom ξ z‖ * (eps u r * (1 + ‖((ξ • z : ℍ) : ℂ)‖)) := by ring
    _ ≤ ‖denom ξ z‖ * ‖((ξ • z : ℍ) : ℂ) - u‖ := by gcongr

/-- The majorant `‖(a,b)‖^{-k} ‖(c,d)‖^{-k}`. -/
def bnd (ξ : SL(2, ℤ)) : ℝ := ((‖row ξ 0‖ * ‖row ξ 1‖) ^ k)⁻¹

theorem bnd_nonneg (ξ : SL(2, ℤ)) : 0 ≤ bnd k ξ := by unfold bnd; positivity

theorem summable_bnd (hk : 3 ≤ k) : Summable (bnd k) := by
  have hk' : (2 : ℝ) < k := by exact_mod_cast hk
  have hf : Summable fun x : Fin 2 → ℤ ↦ (‖x‖ ^ k)⁻¹ :=
    (summable_one_div_norm_rpow hk').congr fun x ↦ by
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  have hp := Summable.mul_of_nonneg hf hf (fun x ↦ by positivity) (fun x ↦ by positivity)
  have := hp.comp_injective row_injective
  refine this.congr fun ξ ↦ ?_
  simp only [bnd, Function.comp_apply, mul_pow, mul_inv]

/-- The constant `(ε ρ)^{-2k}`. -/
def cst (r ρ : ℝ) : ℝ := (((eps u r * ρ) ^ 2) ^ k)⁻¹

theorem norm_term_le (ξ : SL(2, ℤ)) (z : ℍ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρz : ρ ≤ EisensteinSeries.r z)
    (h : r ≤ ‖((ξ • z : ℍ) : ℂ) - u‖) : ‖term u k ξ z‖ ≤ cst u k r ρ * bnd k ξ := by
  have hL := norm_lin_ge u ξ z hr h
  have he := eps_pos u hr
  have hA : 0 < ‖row ξ 0‖ := norm_pos_iff.2 (row_ne_zero ξ 0)
  have hB : 0 < ‖row ξ 1‖ := norm_pos_iff.2 (row_ne_zero ξ 1)
  have hL' : eps u r * ρ * (‖row ξ 0‖ + ‖row ξ 1‖) ≤ ‖lin u ξ z‖ :=
    le_trans (by gcongr) hL
  have hsq : (eps u r * ρ) ^ 2 * (‖row ξ 0‖ * ‖row ξ 1‖) ≤ ‖lin u ξ z‖ ^ 2 := by
    have h0 : 0 ≤ eps u r * ρ * (‖row ξ 0‖ + ‖row ξ 1‖) := by positivity
    have h2 : (eps u r * ρ) ^ 2 * (‖row ξ 0‖ * ‖row ξ 1‖) ≤ (eps u r * ρ * (‖row ξ 0‖ + ‖row ξ 1‖)) ^ 2 := by
      have : ‖row ξ 0‖ * ‖row ξ 1‖ ≤ (‖row ξ 0‖ + ‖row ξ 1‖) ^ 2 := by nlinarith
      calc (eps u r * ρ) ^ 2 * (‖row ξ 0‖ * ‖row ξ 1‖) ≤ (eps u r * ρ) ^ 2 * (‖row ξ 0‖ + ‖row ξ 1‖) ^ 2 := by
            gcongr
        _ = _ := by ring
    exact h2.trans (pow_le_pow_left₀ h0 hL' 2)
  have hpos : 0 < ((eps u r * ρ) ^ 2 * (‖row ξ 0‖ * ‖row ξ 1‖)) ^ k := by positivity
  rw [term, norm_inv, norm_pow, cst, bnd, ← mul_inv, ← mul_pow, pow_mul]
  exact inv_anti₀ hpos (pow_le_pow_left₀ (by positivity) hsq k)

/-- The pointwise form of the estimate: summability and a bound for the sum. -/
theorem summable_and_norm_tsum_le {ι : Type*} {e : ι → SL(2, ℤ)} (he : Injective e) (hk : 3 ≤ k) (z : ℍ)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρz : ρ ≤ EisensteinSeries.r z)
    (hsep : ∀ i, r ≤ ‖((e i • z : ℍ) : ℂ) - u‖) :
    Summable (fun i ↦ term u k (e i) z) ∧ ‖∑' i, term u k (e i) z‖ ≤ cst u k r ρ * ∑' i, bnd k (e i) := by
  have hs : Summable fun i ↦ cst u k r ρ * bnd k (e i) :=
    ((summable_bnd k hk).comp_injective he).mul_left _
  have hle : ∀ i, ‖term u k (e i) z‖ ≤ cst u k r ρ * bnd k (e i) := fun i ↦
    norm_term_le u k (e i) z hr hρ hρz (hsep i)
  refine ⟨Summable.of_norm_bounded hs hle, ?_⟩
  rw [← tsum_mul_left]
  exact tsum_of_norm_bounded hs.hasSum hle

/-- **Locally uniform convergence away from the orbit**: a family of terms, indexed injectively by elements of
`SL₂(ℤ)`, all of which keep `γz` at distance `≥ r` from `u` on an open set `U` where `r(z) ≥ ρ`. -/
theorem differentiableOn_tsum {ι : Type*} {e : ι → SL(2, ℤ)} (he : Injective e) (hk : 3 ≤ k) {U : Set ℂ}
    (hU : IsOpen U) (hUH : ∀ z ∈ U, 0 < z.im) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hρU : ∀ z (hz : z ∈ U), ρ ≤ EisensteinSeries.r ⟨z, hUH z hz⟩)
    (hsep : ∀ i z (hz : z ∈ U), r ≤ ‖((e i • (⟨z, hUH z hz⟩ : ℍ) : ℍ) : ℂ) - u‖) :
    DifferentiableOn ℂ (fun z ↦ ∑' i, term u k (e i) z) U ∧
      ∀ z ∈ U, Summable (fun i ↦ term u k (e i) z) ∧
        ‖∑' i, term u k (e i) z‖ ≤ cst u k r ρ * ∑' i, bnd k (e i) := by
  have hs : Summable fun i ↦ cst u k r ρ * bnd k (e i) :=
    ((summable_bnd k hk).comp_injective he).mul_left _
  have hle : ∀ i, ∀ z ∈ U, ‖term u k (e i) z‖ ≤ cst u k r ρ * bnd k (e i) := fun i z hz ↦
    norm_term_le u k (e i) ⟨z, hUH z hz⟩ hr hρ (hρU z hz) (hsep i z hz)
  have hne : ∀ i, ∀ z ∈ U, lin u (e i) z ≠ 0 := by
    intro i z hz h0
    have := norm_lin_ge u (e i) ⟨z, hUH z hz⟩ hr (hsep i z hz)
    have hA : 0 < ‖row (e i) 0‖ := norm_pos_iff.2 (row_ne_zero _ 0)
    have : 0 < eps u r * EisensteinSeries.r ⟨z, hUH z hz⟩ * (‖row (e i) 0‖ + ‖row (e i) 1‖) := by
      have := eps_pos u hr
      have := r_pos (⟨z, hUH z hz⟩ : ℍ)
      positivity
    simp only [UpperHalfPlane.coe_mk] at *
    rw [h0, norm_zero] at *
    linarith
  refine ⟨differentiableOn_tsum_of_summable_norm hs (fun i ↦ differentiableOn_term u k (hne i)) hU hle,
    fun z hz ↦ ?_⟩
  exact summable_and_norm_tsum_le u k he hk ⟨z, hUH z hz⟩ hr hρ (hρU z hz) fun i ↦ hsep i z hz

/-! ### The exceptional set -/

/-- Only finitely many `γ` bring a point of a bounded box `|Re z| ≤ A`, `B ≤ Im z ≤ C` close to `u`. -/
theorem finite_exceptional (A B C : ℝ) (hB : 0 < B) :
    {ξ : SL(2, ℤ) | ∃ z : ℍ, |z.re| ≤ A ∧ B ≤ z.im ∧ z.im ≤ C ∧ ‖((ξ • z : ℍ) : ℂ) - u‖ < u.im / 2}.Finite := by
  set ρ := EisensteinSeries.r ⟨⟨A, B⟩, hB⟩
  have hρ : 0 < ρ := r_pos _
  set M1 := Real.sqrt (2 * C / u.im)
  set R := max (M1 / ρ) ((‖(u : ℂ)‖ + u.im / 2) * M1 / ρ)
  have hfin : (Metric.closedBall (0 : Fin 2 → ℤ) R).Finite :=
    (isCompact_closedBall _ _).finite_of_discrete
  refine ((hfin.prod hfin).preimage row_injective.injOn).subset ?_
  rintro ξ ⟨z, hre, him, himC, hclose⟩
  have hz : ρ ≤ EisensteinSeries.r z := r_lower_bound_on_verticalStrip z hB ⟨hre, him⟩
  have hd := denom_ne_zero ξ z
  have hdpos : 0 < ‖denom ξ z‖ := norm_pos_iff.2 hd
  -- `Im(γz) > Im(u)/2`
  have him_close : u.im / 2 < (ξ • z).im := by
    have : |((ξ • z : ℍ) : ℂ).im - (u : ℂ).im| ≤ ‖((ξ • z : ℍ) : ℂ) - u‖ := by
      rw [← Complex.sub_im]; exact abs_im_le_norm _
    have h' := (abs_lt.1 (this.trans_lt hclose)).1
    simp only [UpperHalfPlane.coe_im] at h'
    linarith
  -- `|cz + d|² < 2C / Im(u)`
  have hC : 0 < C := z.im_pos.trans_le himC
  have hden : ‖denom ξ z‖ ≤ M1 := by
    have h1 : (ξ • z).im = z.im / Complex.normSq (denom ξ z) := by
      have := ModularGroup.im_smul_eq_div_normSq ξ z
      simpa using this
    rw [h1, lt_div_iff₀ (Complex.normSq_pos.2 hd)] at him_close
    apply Real.le_sqrt_of_sq_le
    rw [← Complex.normSq_eq_norm_sq, le_div_iff₀ u.im_pos]
    nlinarith [u.im_pos]
  have hζ : ‖((ξ • z : ℍ) : ℂ)‖ ≤ ‖(u : ℂ)‖ + u.im / 2 := by
    have := norm_le_norm_add_norm_sub' (((ξ • z : ℍ) : ℂ)) u
    linarith
  have hnum : ((ξ • z : ℍ) : ℂ) * denom ξ z = (ξ 0 0 : ℂ) * z + (ξ 0 1 : ℂ) := by
    rw [coe_smul_sl, denom_sl, div_mul_cancel₀]
    rwa [denom_sl] at hd
  have hr0 := r_mul_max_le (z := z) (row_ne_zero ξ 0)
  have hr1 := r_mul_max_le (z := z) (row_ne_zero ξ 1)
  simp only [row] at hr0 hr1
  rw [← hnum, norm_mul] at hr0
  rw [← denom_sl] at hr1
  simp only [Set.mem_preimage, Set.mem_prod, Metric.mem_closedBall, dist_zero_right]
  have hM1 : 0 ≤ M1 := Real.sqrt_nonneg _
  constructor
  · refine le_trans ?_ (le_max_right _ _)
    rw [le_div_iff₀ hρ]
    calc ‖row ξ 0‖ * ρ ≤ EisensteinSeries.r z * ‖row ξ 0‖ := by
          rw [mul_comm]; gcongr
      _ ≤ ‖((ξ • z : ℍ) : ℂ)‖ * ‖denom ξ z‖ := hr0
      _ ≤ (‖(u : ℂ)‖ + u.im / 2) * M1 := by gcongr
  · refine le_trans ?_ (le_max_left _ _)
    rw [le_div_iff₀ hρ]
    calc ‖row ξ 1‖ * ρ ≤ EisensteinSeries.r z * ‖row ξ 1‖ := by
          rw [mul_comm]; gcongr
      _ ≤ ‖denom ξ z‖ := hr1
      _ ≤ M1 := hden

end ModularFormsKB.Milne.Wave13
