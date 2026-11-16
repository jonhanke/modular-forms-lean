/-
# Tunnell's theta products: absolute slashes of the factors (boundedness and the level-16 cusps)

With the weight-one-half absolute slash `W f γ τ = ‖cτ + d‖^(-1/2) ‖f(γτ)‖` (`Miyake.Sec4_9.absSlash (1/2)`):
* every $\theta(t\,\cdot)$ has bounded absolute slash at every cusp (`isBounded_absSlash_theta_mul`), as a rank-one
  spherical theta series;
* $\theta(\tau) - 1$ and $\theta(t\tau) - 1$ tend to $0$ as $\operatorname{Im}\tau \to \infty$
  (`tendsto_theta_mul_sub_one`);
* for $\gamma \in \Gamma_0(16)$ the absolute slash of $\theta_{\mathrm{odd}}$ is $|\theta_{\mathrm{odd}}(\tau)|$, which
  tends to $0$ (`tendsto_absSlash_thetaOddPart_of_dvd`).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellThetaLaw
import ModularFormsKB.Miyake.Sec4_9.Spherical.UnaryModular
import ModularFormsKB.HalfIntegral.Cusps

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex MatrixGroups CongruenceSubgroup Filter Module
open scoped Real Manifold
open ModularFormsKB.Miyake.Sec4_9

local notation "ℍ" => UpperHalfPlane

/-- The weight-one-half absolute slash. -/
noncomputable abbrev W (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) : ℝ := absSlash (1 / 2) f γ τ

theorem W_def (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    W f γ τ = ‖HalfIntegral.cuspDenom γ τ‖ ^ (-(1 / 2 : ℝ)) * ‖f (γ • τ)‖ := rfl

theorem W_nonneg (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) : 0 ≤ W f γ τ := absSlash_nonneg _ _ _ _

theorem W_congr {f g : ℍ → ℂ} (h : ∀ σ, ‖f σ‖ = ‖g σ‖) (γ : SL(2, ℤ)) :
    W f γ = W g γ := by
  funext τ; simp only [W_def, h]

theorem W_sub_le (f g : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    W (fun σ ↦ f σ - g σ) γ τ ≤ W f γ τ + W g γ τ := by
  simp only [W_def]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)

theorem W_const_mul (c : ℂ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    W (fun σ ↦ c * f σ) γ τ = ‖c‖ * W f γ τ := by
  simp only [W_def, norm_mul]; ring

theorem W_add_le (f g : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    W (fun σ ↦ f σ + g σ) γ τ ≤ W f γ τ + W g γ τ := by
  simp only [W_def]
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)

/-- Rank-one spherical form of $\theta(t\,\cdot)$. -/
theorem norm_theta_mul_eq (t : ℕ) (ht : 1 ≤ t) (τ : ℍ) :
    ‖HalfIntegral.theta ((t : ℂ) * τ)‖ =
      ‖thetaSph (twistLattice ht (le_refl 1)) 0 (1 : ℝ) 0 (twistVec t (0 : ℕ)) τ‖ := by
  let ψ : DirichletCharacter ℂ 1 := 1
  have hp : HalfIntegral.charParity ψ = 0 := by simp [ψ, HalfIntegral.charParity]
  have h := thetaTwist_eq_sum ψ ht (le_refl 1) τ
  rw [thetaLat, hp] at h
  have h0 : ψ⁻¹ ((0 : ℕ) : ZMod 1) = 1 := by
    rw [show ((0 : ℕ) : ZMod 1) = 1 from Subsingleton.elim _ _]; exact map_one _
  simp only [Finset.sum_range_one, h0, pow_zero, inv_one, one_mul] at h
  rw [← theta_mul_eq_thetaTwist] at h
  rw [h]

theorem isBounded_absSlash_theta_mul (t : ℕ) (ht : 1 ≤ t) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty (W (fun τ : ℍ ↦ HalfIntegral.theta ((t : ℂ) * τ)) γ) := by
  have hb := isBoundedAtImInfty_absSlash_thetaSph (L := twistLattice ht (le_refl 1)) (ν := 0)
    (u := (1 : ℝ)) (w := 0) (isEven_twistLattice ht (le_refl 1)) (Or.inl (by norm_num)) γ
    (twistVec_mem_dual ht (le_refl 1) (0 : ℕ))
  have hw : ((0 : ℕ) : ℝ) + (finrank ℝ ℝ : ℝ) / 2 = 1 / 2 := by simp
  rw [hw] at hb
  have e : W (fun τ : ℍ ↦ HalfIntegral.theta ((t : ℂ) * τ)) γ =
      absSlash (1 / 2) (thetaSph (twistLattice ht (le_refl 1)) 0 (1 : ℝ) 0 (twistVec t (0 : ℕ))) γ :=
    W_congr (norm_theta_mul_eq t ht) γ
  rw [e]; exact hb

theorem tendsto_im_atImInfty : Tendsto (fun τ : ℍ ↦ τ.im) UpperHalfPlane.atImInfty atTop :=
  Filter.tendsto_comap (f := UpperHalfPlane.im) (x := atTop)

/-- $\theta(t\tau) - 1 \to 0$ as $\operatorname{Im}\tau \to \infty$. -/
theorem tendsto_theta_mul_sub_one (t : ℕ) (ht : 1 ≤ t) :
    Tendsto (fun τ : ℍ ↦ HalfIntegral.theta ((t : ℂ) * τ) - 1) UpperHalfPlane.atImInfty (nhds 0) := by
  have hpos : (0 : ℝ) < 2 * t := by positivity
  have hc : Tendsto (fun τ : ℍ ↦ (2 * (t : ℝ)) * τ.im) UpperHalfPlane.atImInfty atTop :=
    tendsto_im_atImInfty.const_mul_atTop hpos
  set g : ℍ → ℂ := fun τ ↦ 2 * ((t : ℂ) * τ) with hgdef
  have hg : Tendsto g UpperHalfPlane.atImInfty (comap Complex.im atTop) := by
    rw [tendsto_comap_iff]
    have : (Complex.im ∘ g) = fun τ : ℍ ↦ (2 * (t : ℝ)) * τ.im := by
      funext τ; simp [g]; ring
    rw [this]; exact hc
  have hO := isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto hg
  refine hO.trans_tendsto ?_
  have h2 : Tendsto (fun τ : ℍ ↦ -π * ((2 * (t : ℝ)) * τ.im)) UpperHalfPlane.atImInfty atBot :=
    hc.const_mul_atTop_of_neg (by linarith [Real.pi_pos])
  have h3 := Real.tendsto_exp_atBot.comp h2
  refine h3.congr fun τ ↦ ?_
  simp [g]; ring

/-- For $\gamma \in \Gamma_0(16)$, $\theta_{\mathrm{odd}}(\gamma\tau) = j(\gamma, \tau)\,\theta_{\mathrm{odd}}(\tau)$. -/
theorem thetaOddPart_smul {γ : SL(2, ℤ)} (h : (16 : ℤ) ∣ γ 1 0) (τ : ℍ) :
    thetaOddPart (γ • τ) = HalfIntegral.thetaMult γ τ * thetaOddPart τ := by
  have h4 : γ ∈ Gamma0 (4 * 1) := by
    rw [mem_Gamma0_iff_dvd]; push_cast; exact dvd_trans (by norm_num) h
  have h16 : γ ∈ Gamma0 (4 * 4) := by
    rw [mem_Gamma0_iff_dvd]; push_cast; exact h
  have hodd : Odd (γ 1 1) := HalfIntegral.Gamma0_four_odd (by simpa using h4)
  have e1 := theta_mul_law 1 le_rfl h4 τ
  have e4 := theta_mul_law 4 (by norm_num) h16 τ
  have j4 : (jacobiSym ((4 : ℕ) : ℤ) (γ 1 1).natAbs : ℂ) = 1 := by
    have := jacobi_two_pow 2 (γ 1 1).natAbs
    have e2 : ((4 : ℕ) : ℤ) = ((2 ^ 2 : ℕ) : ℤ) := by norm_num
    rw [e2, this]
    push_cast
    exact jacobi_two_sq _ hodd
  rw [j4] at e4
  simp only [Nat.cast_one, one_mul, jacobiSym.one_left, Int.cast_one, Nat.cast_ofNat] at e1 e4
  unfold thetaOddPart
  rw [e1, e4]
  ring

theorem W_thetaOddPart_of_dvd {γ : SL(2, ℤ)} (h : (16 : ℤ) ∣ γ 1 0) (τ : ℍ) :
    W thetaOddPart γ τ = ‖thetaOddPart τ‖ := by
  have h4 : γ ∈ Gamma0 4 := by
    rw [mem_Gamma0_iff_dvd]; push_cast; exact dvd_trans (by norm_num) h
  rw [W_def, thetaOddPart_smul h, norm_mul, HalfIntegral.norm_thetaMult h4]
  have hD : 0 < ‖HalfIntegral.cuspDenom γ τ‖ := norm_pos_iff.mpr (HalfIntegral.cuspDenom_ne_zero γ τ)
  have e : ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ = ‖HalfIntegral.cuspDenom γ τ‖ := rfl
  rw [e, ← mul_assoc, ← Real.rpow_add hD]
  simp

theorem tendsto_absSlash_thetaOddPart_of_dvd {γ : SL(2, ℤ)} (h : (16 : ℤ) ∣ γ 1 0) :
    Tendsto (W thetaOddPart γ) UpperHalfPlane.atImInfty (nhds 0) := by
  have e : W thetaOddPart γ = fun τ ↦ ‖thetaOddPart τ‖ := funext (W_thetaOddPart_of_dvd h)
  rw [e]
  have h1 := tendsto_theta_mul_sub_one 1 le_rfl
  have h4 := tendsto_theta_mul_sub_one 4 (by norm_num)
  have := (h1.sub h4).norm
  simp only [sub_self, norm_zero, Nat.cast_one, one_mul, Nat.cast_ofNat] at this
  refine this.congr fun τ ↦ ?_
  simp [thetaOddPart]

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
