/-
# Tunnell's theta products vanish at every cusp

For $\gamma \in \mathrm{SL}_2(\mathbb Z)$ with lower left entry $c$ the cusp quantity of
$\tfrac12 F_1F_2F_3$ ($F_1 = \theta_{\mathrm{odd}}$, $F_2 = \theta(2\tau)$ or $\theta(4\tau)$, $F_3 = \phi_8$) is
$\tfrac12 \prod W(F_i, \gamma, \tau)$ with the weight-one-half absolute slash
$W(F, \gamma, \tau) = |c\tau + d|^{-1/2}|F(\gamma\tau)|$. Every factor has bounded $W$
(`isBounded_absSlash_theta_mul`, unary theta series), and for each $\gamma$ one factor tends to $0$:
* $16 \mid c$: $W(\theta_{\mathrm{odd}}, \gamma, \tau) = |\theta_{\mathrm{odd}}(\tau)| \to 0$
  (`tendsto_absSlash_thetaOddPart_of_dvd`);
* $16 \nmid c$: $W(\phi_8, \gamma, \tau) \to 0$ (`tendsto_W_thetaSignPart_of_not_dvd`), by reduction to
  $\varphi(z) = \sum (-1)^n e^{2\pi i n^2 z}$ at a cusp with odd denominator and the functional equation of
  `jacobiTheta₂` (files `TunnellThetaCuspSign`, `TunnellThetaCuspOdd`, `TunnellThetaCuspPhiS`).

Main results: `zero_at_cusps_tunnellOddTheta`, `zero_at_cusps_tunnellEvenTheta`.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellThetaCuspSign

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex MatrixGroups CongruenceSubgroup Filter
open scoped Real Manifold
open ModularFormsKB.Miyake.Sec4_9

local notation "ℍ" => UpperHalfPlane

/-- For $16 \nmid c$, the absolute slash of $\phi_8$ tends to $0$. -/
theorem tendsto_W_thetaSignPart_of_not_dvd {γ : SL(2, ℤ)} (h : ¬ (16 : ℤ) ∣ γ 1 0) :
    Tendsto (W thetaSignPart γ) UpperHalfPlane.atImInfty (nhds 0) := by
  obtain ⟨g, e, c', hg, he, H8, Hc, hodd⟩ := exists_gcd_split (γ 1 0) h
  have hdγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hac : IsCoprime (γ 0 0) c' :=
    ⟨γ 1 1, -(γ 0 1 * g), by rw [Hc] at hdγ; linear_combination hdγ⟩
  have hec : IsCoprime e c' := by
    have h1 := coprime_of_odd_int hodd
    have h2 : e ∣ ((4 * 32 : ℕ) : ℤ) := ⟨16 * g, by push_cast; linarith⟩
    exact (h1.of_isCoprime_of_dvd_right h2).symm
  obtain ⟨B, hB00, hB10⟩ := exists_SL_col (e * γ 0 0) c' (hec.mul_left hac)
  have e1 : W thetaSignPart γ = fun τ ↦ (e : ℝ) ^ (-(1 / 2 : ℝ)) *
      W phiH B (wPt g (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) hg τ) :=
    funext fun τ ↦ W_signPart_eq hg he H8 Hc hB00 hB10 τ
  rw [e1]
  have h2 := (tendsto_W_phiH_of_odd B (by rw [hB10]; exact hodd)).comp
    (tendsto_wPt g (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) hg)
  have h3 := h2.const_mul ((e : ℝ) ^ (-(1 / 2 : ℝ)))
  simpa using h3

theorem bdd_theta_c (t : ℕ) (ht : 1 ≤ t) (c : ℂ) (hc : c = t) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (W (fun τ : ℍ ↦ HalfIntegral.theta (c * τ)) γ) := by
  subst hc; exact isBounded_absSlash_theta_mul t ht γ

theorem bdd_oddPart (γ : SL(2, ℤ)) : UpperHalfPlane.IsBoundedAtImInfty (W thetaOddPart γ) := by
  have h1 := bdd_theta_c 1 le_rfl 1 (by simp) γ
  have h4 := bdd_theta_c 4 (by norm_num) 4 (by norm_num) γ
  refine HalfIntegral.isBounded_of_le_add h1 h4 (fun τ ↦ W_nonneg _ _ _) fun τ ↦ ?_
  have e : W thetaOddPart γ =
      W (fun σ : ℍ ↦ HalfIntegral.theta (1 * (σ : ℂ)) - HalfIntegral.theta (4 * (σ : ℂ))) γ :=
    W_congr (fun σ ↦ by simp [thetaOddPart]) γ
  exact (congrFun e τ).le.trans (W_sub_le _ _ γ τ)

theorem bdd_signPart (γ : SL(2, ℤ)) : UpperHalfPlane.IsBoundedAtImInfty (W thetaSignPart γ) := by
  have h32 := bdd_theta_c 32 (by norm_num) 32 (by norm_num) γ
  have h8 := bdd_theta_c 8 (by norm_num) 8 (by norm_num) γ
  have h32' : UpperHalfPlane.IsBoundedAtImInfty
      (fun τ ↦ 2 * W (fun τ : ℍ ↦ HalfIntegral.theta (32 * (τ : ℂ))) γ τ) := h32.const_mul_left 2
  refine HalfIntegral.isBounded_of_le_add h32' h8 (fun τ ↦ W_nonneg _ _ _) fun τ ↦ ?_
  have e : W thetaSignPart γ = W (fun σ : ℍ ↦
      2 * HalfIntegral.theta (32 * (σ : ℂ)) - HalfIntegral.theta (8 * (σ : ℂ))) γ :=
    W_congr (fun σ ↦ by simp [thetaSignPart]) γ
  refine (congrFun e τ).le.trans ((W_sub_le _ _ γ τ).trans ?_)
  rw [W_const_mul]
  simp

theorem cuspNorm_three (F₁ F₂ F₃ : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HalfIntegral.Abstract.cuspNorm 1 (fun σ ↦ F₁ σ * F₂ σ * F₃ σ / 2) γ τ =
      1 / 2 * (W F₁ γ τ * W F₂ γ τ * W F₃ γ τ) := by
  have hD : 0 ≤ ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := norm_nonneg _
  have e : ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-(((1 : ℕ) : ℝ) + 1 / 2)) =
      (‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-(1 / 2 : ℝ))) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD]
    norm_num
  simp only [HalfIntegral.Abstract.cuspNorm, W_def, HalfIntegral.cuspDenom, norm_mul, norm_div,
    Complex.norm_two]
  rw [e]
  ring

theorem tendsto_mul_bdd {u v : ℍ → ℝ} (hu : Tendsto u UpperHalfPlane.atImInfty (nhds 0))
    (hv : UpperHalfPlane.IsBoundedAtImInfty v) :
    Tendsto (fun τ ↦ u τ * v τ) UpperHalfPlane.atImInfty (nhds 0) := by
  obtain ⟨M, A, hA⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp hv
  refine squeeze_zero_norm' ?_ (by simpa using hu.norm.mul_const M)
  rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
  refine ⟨A, fun z hz ↦ ?_⟩
  show ‖u z * v z‖ ≤ ‖u z‖ * M
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hA z hz) (norm_nonneg _)

theorem tendsto_mul3 {u v w : ℍ → ℝ} (hu : Tendsto u UpperHalfPlane.atImInfty (nhds 0))
    (hv : UpperHalfPlane.IsBoundedAtImInfty v) (hw : UpperHalfPlane.IsBoundedAtImInfty w) :
    Tendsto (fun τ ↦ u τ * v τ * w τ) UpperHalfPlane.atImInfty (nhds 0) :=
  tendsto_mul_bdd (tendsto_mul_bdd hu hv) hw

/-- The vanishing criterion for a product $F_1F_2F_3/2$. -/
theorem zero_at_cusps_of_factors {F₁ F₂ F₃ : ℍ → ℂ} (γ : SL(2, ℤ))
    (h1 : UpperHalfPlane.IsBoundedAtImInfty (W F₁ γ)) (h2 : UpperHalfPlane.IsBoundedAtImInfty (W F₂ γ))
    (h3 : UpperHalfPlane.IsBoundedAtImInfty (W F₃ γ))
    (hz : Tendsto (W F₁ γ) UpperHalfPlane.atImInfty (nhds 0) ∨
      Tendsto (W F₃ γ) UpperHalfPlane.atImInfty (nhds 0)) :
    UpperHalfPlane.IsZeroAtImInfty
      (HalfIntegral.Abstract.cuspNorm 1 (fun σ ↦ F₁ σ * F₂ σ * F₃ σ / 2) γ) := by
  have e : HalfIntegral.Abstract.cuspNorm 1 (fun σ ↦ F₁ σ * F₂ σ * F₃ σ / 2) γ =
      fun τ ↦ 1 / 2 * (W F₁ γ τ * W F₂ γ τ * W F₃ γ τ) := funext (cuspNorm_three F₁ F₂ F₃ γ)
  rw [e]
  show Tendsto _ _ _
  have key : Tendsto (fun τ ↦ W F₁ γ τ * W F₂ γ τ * W F₃ γ τ) UpperHalfPlane.atImInfty (nhds 0) := by
    rcases hz with hz | hz
    · exact tendsto_mul3 hz h2 h3
    · have := tendsto_mul3 hz h1 h2
      refine this.congr fun τ ↦ ?_
      ring
  simpa using key.const_mul (1 / 2 : ℝ)

theorem zero_at_cusps_tunnellOddTheta (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (HalfIntegral.Abstract.cuspNorm 1 tunnellOddTheta γ) := by
  have h2 := bdd_theta_c 2 (by norm_num) 2 (by norm_num) γ
  by_cases h : (16 : ℤ) ∣ γ 1 0
  · exact zero_at_cusps_of_factors (F₁ := thetaOddPart) (F₂ := fun τ : ℍ ↦ HalfIntegral.theta (2 * (τ : ℂ)))
      (F₃ := thetaSignPart) γ (bdd_oddPart γ) h2 (bdd_signPart γ)
      (Or.inl (tendsto_absSlash_thetaOddPart_of_dvd h))
  · exact zero_at_cusps_of_factors (F₁ := thetaOddPart) (F₂ := fun τ : ℍ ↦ HalfIntegral.theta (2 * (τ : ℂ)))
      (F₃ := thetaSignPart) γ (bdd_oddPart γ) h2 (bdd_signPart γ)
      (Or.inr (tendsto_W_thetaSignPart_of_not_dvd h))

theorem zero_at_cusps_tunnellEvenTheta (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (HalfIntegral.Abstract.cuspNorm 1 tunnellEvenTheta γ) := by
  have h4 := bdd_theta_c 4 (by norm_num) 4 (by norm_num) γ
  by_cases h : (16 : ℤ) ∣ γ 1 0
  · exact zero_at_cusps_of_factors (F₁ := thetaOddPart) (F₂ := fun τ : ℍ ↦ HalfIntegral.theta (4 * (τ : ℂ)))
      (F₃ := thetaSignPart) γ (bdd_oddPart γ) h4 (bdd_signPart γ)
      (Or.inl (tendsto_absSlash_thetaOddPart_of_dvd h))
  · exact zero_at_cusps_of_factors (F₁ := thetaOddPart) (F₂ := fun τ : ℍ ↦ HalfIntegral.theta (4 * (τ : ℂ)))
      (F₃ := thetaSignPart) γ (bdd_oddPart γ) h4 (bdd_signPart γ)
      (Or.inr (tendsto_W_thetaSignPart_of_not_dvd h))

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
