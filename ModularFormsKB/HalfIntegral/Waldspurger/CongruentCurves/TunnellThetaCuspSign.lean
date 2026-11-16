/-
# Reduction of $\phi_8$ at a cusp with $16 \nmid c$ to $\varphi$ at a cusp with odd denominator

$\phi_8(\tau) = \varphi(8\tau)$ (`thetaSignPart_eq_phi`). For $\gamma = (a, b; c, d)$ put $c = g c'$, $8 = g e$
with $g \in \{1, 2, 4, 8\}$ and $c'$ odd (possible exactly when $16 \nmid c$). The vector $(ea, c')$ is
primitive, so it is the first column of some $B \in \mathrm{SL}_2(\mathbb Z)$, and $8\gamma\tau = B w$ with
$w = (g^2\tau + g\beta)/8$, $\beta = 8 b B_{11} - B_{01} d$; moreover $c_B w + d_B = (c\tau + d)/e$. Hence
$W(\phi_8, \gamma, \tau) = e^{-1/2}\, W(\varphi, B, w)$ (`exists_sign_reduction`).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.TunnellThetaCuspOdd

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex MatrixGroups CongruenceSubgroup Filter
open scoped Real Manifold

local notation "ℍ" => UpperHalfPlane

theorem thetaSignPart_eq_phi (σ : ℍ) : thetaSignPart σ = phi (8 * (σ : ℂ)) := by
  have hz : 0 < (8 * (σ : ℂ)).im := by simp; exact σ.im_pos
  rw [phi_eq_two_theta hz, thetaSignPart]
  have : (4 : ℂ) * (8 * (σ : ℂ)) = 32 * σ := by ring
  rw [this]

theorem exists_gcd_split (c : ℤ) (h : ¬ (16 : ℤ) ∣ c) :
    ∃ g e c' : ℤ, 0 < g ∧ 0 < e ∧ g * e = 8 ∧ c = g * c' ∧ Odd c' := by
  by_cases h1 : c % 2 = 1
  · exact ⟨1, 8, c, by norm_num, by norm_num, by norm_num, by ring, Int.odd_iff.mpr h1⟩
  by_cases h2 : c % 4 = 2
  · exact ⟨2, 4, c / 2, by norm_num, by norm_num, by norm_num, by omega, Int.odd_iff.mpr (by omega)⟩
  by_cases h3 : c % 8 = 4
  · exact ⟨4, 2, c / 4, by norm_num, by norm_num, by norm_num, by omega, Int.odd_iff.mpr (by omega)⟩
  · exact ⟨8, 1, c / 8, by norm_num, by norm_num, by norm_num, by omega, Int.odd_iff.mpr (by omega)⟩

theorem exists_SL_col (p q : ℤ) (h : IsCoprime p q) : ∃ B : SL(2, ℤ), B 0 0 = p ∧ B 1 0 = q := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨⟨!![p, -v; q, u], by rw [Matrix.det_fin_two]; simp; linarith⟩, rfl, rfl⟩

/-- The point $w = (g^2\tau + g\beta)/8$. -/
noncomputable def wPt (g β : ℤ) (hg : 0 < g) (τ : ℍ) : ℍ :=
  UpperHalfPlane.mk (((g ^ 2 / 8 : ℝ) : ℂ) * τ + ((g * β / 8 : ℝ) : ℂ)) (by
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, UpperHalfPlane.coe_im]
    exact mul_pos (by positivity) τ.im_pos)

theorem wPt_im (g β : ℤ) (hg : 0 < g) (τ : ℍ) : (wPt g β hg τ).im = (g : ℝ) ^ 2 / 8 * τ.im := by
  have : (wPt g β hg τ).im = ((((g ^ 2 / 8 : ℝ) : ℂ) * τ + ((g * β / 8 : ℝ) : ℂ))).im := rfl
  rw [this, Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero]
  rfl

theorem tendsto_wPt (g β : ℤ) (hg : 0 < g) :
    Tendsto (wPt g β hg) UpperHalfPlane.atImInfty UpperHalfPlane.atImInfty := by
  show Tendsto _ _ (comap UpperHalfPlane.im atTop)
  rw [tendsto_comap_iff]
  have hg' : (0 : ℝ) < (g : ℝ) ^ 2 / 8 := by
    have : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  have := tendsto_im_atImInfty.const_mul_atTop hg'
  refine this.congr fun τ ↦ ?_
  simp [wPt_im]

theorem coe_wPt (g β : ℤ) (hg : 0 < g) (τ : ℍ) :
    ((wPt g β hg τ : ℍ) : ℂ) = ((g : ℂ) ^ 2 * τ + g * β) / 8 := by
  show (((g ^ 2 / 8 : ℝ) : ℂ) * τ + ((g * β / 8 : ℝ) : ℂ)) = _
  push_cast; ring

/-- The integer identities behind the reduction. -/
theorem sign_identities {a b c d g e c' x y : ℤ}
    (H8 : g * e = 8) (Hc : c = g * c') (Hγ : a * d - b * c = 1) (HB : e * a * y - x * c' = 1) :
    c' * (8 * b * y - x * d) + e * y = d ∧ a * (8 * b * y - x * d) + x = g * b := by
  constructor
  · linear_combination (-b * c' * y) * H8 + (-e * b * y) * Hc + d * HB + (-e * y) * Hγ
  · linear_combination (-x) * Hγ + (-b * a * y) * H8 + (-b * x) * Hc + (b * g) * HB

theorem smul_wPt {γ B : SL(2, ℤ)} {g e c' : ℤ} (hg : 0 < g) (he : 0 < e) (H8 : g * e = 8)
    (Hc : γ 1 0 = g * c') (HB00 : B 0 0 = e * γ 0 0) (HB10 : B 1 0 = c') (τ : ℍ) :
    ((B • wPt g (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) hg τ : ℍ) : ℂ) = 8 * ((γ • τ : ℍ) : ℂ) ∧
    HalfIntegral.cuspDenom B (wPt g (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) hg τ) =
      HalfIntegral.cuspDenom γ τ / e := by
  have hdγ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hdB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    have h := B.det_coe
    rwa [Matrix.det_fin_two] at h
  rw [HB00, HB10] at hdB
  obtain ⟨K1, K2⟩ := sign_identities H8 Hc hdγ hdB
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have K1C : (c' : ℂ) * (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) + e * B 1 1 = γ 1 1 := by
    exact_mod_cast K1
  have K2C : (γ 0 0 : ℂ) * (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) + B 0 1 = g * γ 0 1 := by
    exact_mod_cast K2
  have H8C : (g : ℂ) * e = 8 := by exact_mod_cast H8
  have HcC : (γ 1 0 : ℂ) = g * c' := by exact_mod_cast Hc
  have HB00C : (B 0 0 : ℂ) = e * γ 0 0 := by exact_mod_cast HB00
  have HB10C : (B 1 0 : ℂ) = c' := by exact_mod_cast HB10
  have hden : HalfIntegral.cuspDenom B (wPt g (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) hg τ) =
      HalfIntegral.cuspDenom γ τ / e := by
    unfold HalfIntegral.cuspDenom
    rw [coe_wPt, HB10C, eq_div_iff he0]
    push_cast
    linear_combination ((g : ℂ) * c' * τ / 8 + c' * (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) / 8) * H8C
      - (τ : ℂ) * HcC + K1C
  refine ⟨?_, hden⟩
  have hnum : (B 0 0 : ℂ) * ((wPt g (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) hg τ : ℍ) : ℂ) + B 0 1 =
      g * ((γ 0 0 : ℂ) * τ + γ 0 1) := by
    rw [coe_wPt, HB00C]
    push_cast
    linear_combination ((γ 0 0 : ℂ) * g * τ / 8 + γ 0 0 * (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) / 8) * H8C
      + K2C
  have hD : HalfIntegral.cuspDenom γ τ ≠ 0 := HalfIntegral.cuspDenom_ne_zero γ τ
  have hD' : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := hD
  rw [coe_smul_SL B, coe_smul_SL γ τ]
  have hden' : (B 1 0 : ℂ) * ((wPt g (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) hg τ : ℍ) : ℂ) + B 1 1 =
      ((γ 1 0 : ℂ) * τ + γ 1 1) / e := hden
  rw [hnum, hden', div_div_eq_mul_div, ← H8C]
  ring

theorem W_signPart_eq {γ B : SL(2, ℤ)} {g e c' : ℤ} (hg : 0 < g) (he : 0 < e) (H8 : g * e = 8)
    (Hc : γ 1 0 = g * c') (HB00 : B 0 0 = e * γ 0 0) (HB10 : B 1 0 = c') (τ : ℍ) :
    W thetaSignPart γ τ = (e : ℝ) ^ (-(1 / 2 : ℝ)) *
      W phiH B (wPt g (8 * γ 0 1 * B 1 1 - B 0 1 * γ 1 1) hg τ) := by
  obtain ⟨h1, h2⟩ := smul_wPt hg he H8 Hc HB00 HB10 τ
  rw [W_def, W_def, h2]
  simp only [phiH]
  rw [thetaSignPart_eq_phi, ← h1]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hD : 0 < ‖HalfIntegral.cuspDenom γ τ‖ :=
    norm_pos_iff.mpr (HalfIntegral.cuspDenom_ne_zero γ τ)
  have hn : ‖HalfIntegral.cuspDenom γ τ / (e : ℂ)‖ = ‖HalfIntegral.cuspDenom γ τ‖ / e := by
    rw [norm_div]
    congr 1
    simp [abs_of_pos he']
  rw [hn, Real.div_rpow hD.le he'.le]
  have : 0 < (e : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  field_simp

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
