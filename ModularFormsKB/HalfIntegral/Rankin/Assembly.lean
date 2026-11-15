/-
# Shimura's twisted functional equations from the Rankin integral: the assembly

From the named inputs `ThetaTwistLaw M`,
`EisensteinFE`, `RankinUnfolding` and `ShimuraDualUnfolding M k N χ` (`Abstract/ShimuraRankin.lean`) this file proves
`ShimuraTwistedFE M k N χ` for $N \ge 1$ (`shimuraTwistedFE_of_rankin`), hence Shimura's theorem
(`shimuraTheorem_of_rankin`, through `shimuraTheorem_of_twistedFE`).

For each twisting character $\psi$ (trivial modulo $1$, or primitive modulo an odd prime $m \nmid 4N$) put
$E_a(w) = \rho_\psi(w)\,\mathcal R_\psi(\tfrac{w-k+1}2)$, $\mathcal R_\psi$ the Rankin integral of $G_\psi$ against the
completed Eisenstein series $E^*$ of `EisensteinFE`, and $E_b(w) = C^{-1}E_a(2k-w)$.
- $E_a$ is entire and bounded on vertical strips (`differentiable_rankinIntegral`, `bddVStrips_rankinIntegral`): the
  Eisenstein bound, the decay of $G_\psi$ on the translates of `ModularGroup.fd` (`rankinKernel_bound_fd`) and finite volume.
- For $\operatorname{Re}w$ large, $E_a(w)$ is Weil's completed product: `RankinUnfolding`, the strip identity
  (`stripMellin_rankinKernel`), $\omega(n) = \psi(n)\chi_t(n)$ (`rankinChar_natCast`) and Legendre's duplication formula
  (`rankinRho_mul_eq_gammaFactor`).
- For $\operatorname{Re}w$ large, $E_a(2k-w)$ is the dual Rankin integral (second formula of `EisensteinFE`), which
  `ShimuraDualUnfolding` identifies with $C$ times Weil's completed dual series.
If $\omega(-1) \ne (-1)^{k-\nu}$, the law of $G_\psi$ at $-1$ forces $G_\psi = 0$, and both series vanish on a half plane.
-/
import ModularFormsKB.HalfIntegral.Rankin.Theta
import ModularFormsKB.HalfIntegral.Rankin.Strip
import ModularFormsKB.HalfIntegral.Rankin.Character
import ModularFormsKB.HalfIntegral.Rankin.Holo
import ModularFormsKB.HalfIntegral.Rankin.Decay
import ModularFormsKB.HalfIntegral.Rankin.Factors

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup MeasureTheory Set Filter
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-! ### Small facts -/

/-- **The constant term of a cusp form vanishes.** -/
theorem MultiplierSystem.coeff_zero_eq_zero (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)}
    {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) {a : ℕ → ℂ} (ha : Abstract.HasQExp f a) : a 0 = 0 := by
  have hz := (show M.IsCuspForm k N χ f from hf).zero_at_cusps 1
  have h1 : ∀ τ, Abstract.cuspNorm k f 1 τ = ‖f τ‖ := by intro τ; simp [Abstract.cuspNorm]
  have hs := summable_of_hasQExp ha one_pos
  set S := ∑' n : ℕ, ‖a n‖ * Real.exp (-2 * π * n * 1)
  have htail : ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ - a 0‖ ≤ S * Real.exp (-2 * π * (τ.im - 1)) := by
    intro τ hτ
    have hu := (ha τ).update 0 0
    have e0 : a 0 * cexp (2 * π * I * ((0 : ℕ) : ℂ) * τ) = a 0 := by simp
    rw [e0] at hu
    have hg := hs.hasSum.mul_right (Real.exp (-2 * π * (τ.im - 1)))
    refine le_of_eq_of_le (by ring_nf) (hu.norm_le_of_bounded hg fun n ↦ ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Function.update_self, norm_zero]
      positivity
    · rw [Function.update_of_ne hn.ne', norm_mul, Complex.norm_exp]
      have hre : (2 * π * I * n * (τ : ℂ)).re = -2 * π * n * τ.im := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat,
          UpperHalfPlane.coe_im]
        ring
      rw [hre, mul_assoc (‖a n‖), ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
      have h1' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have := Real.pi_pos
      nlinarith [mul_nonneg (sub_nonneg.2 h1') (sub_nonneg.2 hτ)]
  have hlim0 : Tendsto (fun τ : ℍ ↦ S * Real.exp (-2 * π * (τ.im - 1))) UpperHalfPlane.atImInfty (nhds 0) := by
    have him : Tendsto (fun τ : ℍ ↦ τ.im) UpperHalfPlane.atImInfty atTop := tendsto_comap
    have h0 : Tendsto (fun x : ℝ ↦ x - 1) atTop atTop := tendsto_atTop_add_const_right _ (-1) tendsto_id
    have h2 : Tendsto (fun x : ℝ ↦ 2 * π * (x - 1)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) h0
    have h3 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (h2.comp him)).const_mul S
    rw [mul_zero] at h3
    refine h3.congr fun τ ↦ ?_
    simp only [Function.comp]
    ring_nf
  have hA : Tendsto f UpperHalfPlane.atImInfty (nhds (a 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun τ ↦ norm_nonneg _) ?_ hlim0
    rw [UpperHalfPlane.atImInfty, eventually_comap]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy τ hτ
    exact htail τ (hτ ▸ hy)
  have hB : Tendsto f UpperHalfPlane.atImInfty (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hz.congr h1
  exact tendsto_nhds_unique hA hB

theorem continuous_rankinKernel (k : ℕ) {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) {f : ℍ → ℂ}
    (hf : Continuous f) : Continuous (rankinKernel k ψ t f) := by
  unfold rankinKernel
  refine (hf.mul (continuous_conj.comp (continuous_thetaTwist ψ ht))).mul ?_
  exact continuous_ofReal.comp (UpperHalfPlane.continuous_im.rpow_const fun τ ↦ Or.inl τ.im_pos.ne')

theorem repsIntegral_congr (R : List SL(2, ℤ)) {h h' : ℍ → ℂ} (hh : ∀ τ, h τ = h' τ) :
    repsIntegral R h = repsIntegral R h' := by
  rw [show h = h' from funext hh]

theorem repsIntegral_const_mul (R : List SL(2, ℤ)) (c : ℂ) (h : ℍ → ℂ) :
    repsIntegral R (fun τ ↦ c * h τ) = c * repsIntegral R h := by
  induction R with
  | nil => simp [repsIntegral]
  | cons γ R ih =>
    simp only [repsIntegral, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, integral_const_mul, mul_add]

theorem repsIntegral_zero (R : List SL(2, ℤ)) : repsIntegral R (fun _ ↦ 0) = 0 := by
  induction R with
  | nil => simp [repsIntegral]
  | cons γ R ih =>
    simp only [repsIntegral, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; simp

theorem stripMellin_zero (s : ℂ) : stripMellin (fun _ ↦ 0) s = 0 := by
  simp [stripMellin]

/-! ### Bounded on vertical strips -/

theorem BddVStrips.mul {F G : ℂ → ℂ} (hF : BddVStrips F) (hG : BddVStrips G) : BddVStrips (fun s ↦ F s * G s) := by
  intro σ₁ σ₂
  obtain ⟨B₁, h₁⟩ := hF σ₁ σ₂
  obtain ⟨B₂, h₂⟩ := hG σ₁ σ₂
  refine ⟨|B₁| * |B₂|, fun s hs1 hs2 ↦ ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((h₁ s hs1 hs2).trans (le_abs_self _)) ((h₂ s hs1 hs2).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem BddVStrips.const_mul {F : ℂ → ℂ} (hF : BddVStrips F) (c : ℂ) : BddVStrips (fun s ↦ c * F s) := by
  intro σ₁ σ₂
  obtain ⟨B, h⟩ := hF σ₁ σ₂
  refine ⟨‖c‖ * |B|, fun s hs1 hs2 ↦ ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((h s hs1 hs2).trans (le_abs_self _)) (norm_nonneg _)

/-- Precomposition with $w \mapsto aw + b$, $a > 0$ real, $b$ complex. -/
theorem BddVStrips.comp_affine {F : ℂ → ℂ} (hF : BddVStrips F) {a : ℝ} (ha : 0 < a) (b : ℂ) :
    BddVStrips (fun w ↦ F (a * w + b)) := by
  intro σ₁ σ₂
  obtain ⟨B, h⟩ := hF (a * σ₁ + b.re) (a * σ₂ + b.re)
  refine ⟨B, fun s hs1 hs2 ↦ h _ ?_ ?_⟩
  · simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith
  · simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    nlinarith

/-- Precomposition with the reflection $w \mapsto c - w$, $c$ real. -/
theorem BddVStrips.comp_sub {F : ℂ → ℂ} (hF : BddVStrips F) (c : ℝ) :
    BddVStrips (fun w ↦ F (c - w)) := by
  intro σ₁ σ₂
  obtain ⟨B, h⟩ := hF (c - σ₂) (c - σ₁)
  refine ⟨B, fun s hs1 hs2 ↦ h _ ?_ ?_⟩
  · simp only [sub_re, ofReal_re]; linarith
  · simp only [sub_re, ofReal_re]; linarith

theorem rankinS_eq_affine (k : ℕ) (w : ℂ) : rankinS k w = ((1 / 2 : ℝ) : ℂ) * w + (1 - k) / 2 := by
  unfold rankinS; push_cast; ring

theorem re_rankinS (k : ℕ) (w : ℂ) : (rankinS k w).re = (w.re - k + 1) / 2 := by
  unfold rankinS
  simp

/-! ### The Rankin integral is entire and bounded on vertical strips -/

section Analytic

variable (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hN : 0 < N) {f : ℍ → ℂ}
  (hf : f ∈ M.cuspForms k N χ) {r : ℕ} (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t)
  {E : ℍ → ℂ → ℂ} (hEd : ∀ z, Differentiable ℂ (E z)) (hEc : ∀ s, Continuous fun z ↦ E z s)
  (hEb : ∀ σ₁ σ₂ : ℝ, ∃ A B : ℝ, ∀ z s, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖E z s‖ ≤ B * (z.im ^ A + z.im ^ (-A)))

include hN hf ht hEd hEc hEb

/-- The summand for one coset representative, bounded on `fd × strip`. -/
private theorem term_bound (γ : SL(2, ℤ)) (σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, ∀ τ ∈ ModularGroup.fd, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖rankinKernel k ψ t f (γ • τ) * E (γ • τ) s‖ ≤ C := by
  obtain ⟨A, B, hB⟩ := hEb σ₁ σ₂
  have hθ := norm_thetaTwist_le ψ ht
  obtain ⟨C, hC⟩ := rankinKernel_bound_fd M hN hf ψ (continuous_thetaTwist ψ ht)
    (let ⟨C, _, h⟩ := hθ; ⟨C, h⟩) γ A
  refine ⟨|B| * |C|, fun τ hτ s hs1 hs2 ↦ ?_⟩
  have h1 := hB (γ • τ) s hs1 hs2
  have hpos : 0 ≤ (γ • τ).im ^ A + (γ • τ).im ^ (-A) := by
    have := (γ • τ).im_pos
    positivity
  rw [norm_mul]
  calc ‖rankinKernel k ψ t f (γ • τ)‖ * ‖E (γ • τ) s‖
      ≤ ‖rankinKernel k ψ t f (γ • τ)‖ * (|B| * ((γ • τ).im ^ A + (γ • τ).im ^ (-A))) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpos))
          (norm_nonneg _)
    _ = |B| * (‖rankinKernel k ψ t f (γ • τ)‖ * ((γ • τ).im ^ A + (γ • τ).im ^ (-A))) := by ring
    _ ≤ |B| * |C| := mul_le_mul_of_nonneg_left ((hC τ hτ).trans (le_abs_self _)) (abs_nonneg _)

private theorem term_continuous (γ : SL(2, ℤ)) (s : ℂ) :
    Continuous fun τ : ℍ ↦ rankinKernel k ψ t f (γ • τ) * E (γ • τ) s := by
  have hγ : Continuous (fun τ : ℍ ↦ γ • τ) := continuous_const_smul (γ : GL (Fin 2) ℝ)
  exact ((continuous_rankinKernel k ψ ht hf.holo.continuous).comp hγ).mul ((hEc s).comp hγ)

theorem differentiable_rankinIntegral (R : List SL(2, ℤ)) :
    Differentiable ℂ (rankinIntegral k ψ t f R E) := by
  unfold rankinIntegral repsIntegral
  induction R with
  | nil => simpa using differentiable_const (0 : ℂ)
  | cons γ R ih =>
    simp only [List.map_cons, List.sum_cons]
    refine Differentiable.add ?_ ih
    exact differentiable_setIntegral_of_strip_bound measurableSet_fd volume_fd_lt_top
      (fun τ ↦ (hEd (γ • τ)).const_mul _) (term_continuous M hN hf ψ ht hEd hEc hEb γ)
      (term_bound M hN hf ψ ht hEd hEc hEb γ)

theorem bddVStrips_rankinIntegral (R : List SL(2, ℤ)) :
    BddVStrips (rankinIntegral k ψ t f R E) := by
  unfold rankinIntegral repsIntegral
  induction R with
  | nil => exact fun _ _ ↦ ⟨0, fun s _ _ ↦ by simp⟩
  | cons γ R ih =>
    simp only [List.map_cons, List.sum_cons]
    intro σ₁ σ₂
    obtain ⟨B₁, h₁⟩ := bddVStrips_setIntegral_of_strip_bound volume_fd_lt_top
      (term_bound M hN hf ψ ht hEd hEc hEb γ) σ₁ σ₂
    obtain ⟨B₂, h₂⟩ := ih σ₁ σ₂
    exact ⟨B₁ + B₂, fun s hs1 hs2 ↦ (norm_add_le _ _).trans (add_le_add (h₁ s hs1 hs2) (h₂ s hs1 hs2))⟩

end Analytic

/-! ### Hecke's condition for one twisting character -/

/-- **Hecke's condition for the product $L(w-k+1,\psi\chi_t)\sum_m\psi(m)a(tm^2)m^{-w}$** from the Rankin integral, for a
twisting character $\psi$ modulo $r$ ($r = 1$ or an odd prime), a list of coset representatives of $\Gamma_0(16Ntr^2)$, a
nonzero constant $C$ and the dual identity for $b$. -/
theorem heckeConditionL_of_rankin (M : MultiplierSystem) (hT : ThetaTwistLaw M) (hE : EisensteinFE)
    (hU : RankinUnfolding) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hN : 0 < N) (hk : 2 ≤ k) {f : ℍ → ℂ}
    (hf : f ∈ M.cuspForms k N χ) {a : ℕ → ℂ} (ha : Abstract.HasQExp f a) {t : ℕ} (ht : 1 ≤ t) {r : ℕ}
    (hr : r = 1 ∨ (r.Prime ∧ r ≠ 2)) (ψ : DirichletCharacter ℂ r) {R : List SL(2, ℤ)}
    (hR : IsGamma0Reps (rankinLevel N t r) R) {C : ℂ} (hC : C ≠ 0) {b : ℕ → ℂ}
    (hdual : ∃ σ : ℝ, ∀ w : ℂ, σ < w.re →
      rankinDualFactor k N t ψ w * rankinDual k N χ t ψ f R (rankinS k w) =
        C * (gammaFactor (4 * N * r ^ 2) w * LSeries b w)) :
    HeckeConditionL (2 * k) (4 * N * r ^ 2) C
      (fun w ↦ LSeries (twist ψ (shimuraChar k N χ t)) (w - (k - 1)) * LSeries (twist ψ fun m ↦ a (t * m ^ 2)) w)
      (LSeries b) 0 0 := by
  have hν1 : charParity ψ ≤ 1 := charParity_le_one ψ
  have hνk : charParity ψ ≤ k := by omega
  have hr1 : 1 ≤ r := by
    rcases hr with rfl | ⟨hp, _⟩
    · exact le_rfl
    · exact hp.one_lt.le
  have hL2 : 2 ≤ rankinLevel N t r := by
    unfold rankinLevel
    have : 1 ≤ N * t * r ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have ha0 : a 0 = 0 := M.coeff_zero_eq_zero hf ha
  obtain ⟨Ca, hCa⟩ := (heckeCoeffBound M k N χ hN).bound f hf a ha
  have hlaw := unitaryLaw_rankinKernel M hT (show M.IsCuspForm k N χ f from hf).transforms ht hr ψ hνk
  have hGc : Continuous (rankinKernel k ψ t f) := continuous_rankinKernel k ψ ht hf.holo.continuous
  have hline : ∀ y : ℝ, 0 < y → _ := fun y hy ↦ integral_mul_conj_thetaTwist ha ha0 ψ ht hy
  have hstrip : ∀ w : ℂ, (k : ℝ) + 3 / 2 < w.re → stripMellin (rankinKernel k ψ t f) (rankinS k w) =
      2 * Gamma ((w + charParity ψ) / 2) * (((4 * π * t : ℝ) : ℂ) ^ (-((w + charParity ψ) / 2))) *
        LSeries (twist ψ fun m ↦ a (t * m ^ 2)) w :=
    fun w hw ↦ stripMellin_rankinKernel k ψ ht f a hCa ha0 hline hw
  have hLω : ∀ w : ℂ, LSeries (fun n ↦ rankinChar k N χ t ψ n) (2 * rankinS k w) =
      LSeries (twist ψ (shimuraChar k N χ t)) (w - (k - 1)) := by
    intro w
    have h2 : 2 * rankinS k w = w - (k - 1) := by unfold rankinS; ring
    rw [h2]
    congr 1
    funext n
    simp only [twist, rankinChar_natCast k N χ ht ψ n]
  have hφ : ∃ C : ℝ, ∀ τ : ℍ, τ.im ^ (((2 * k + 1 : ℕ) : ℝ) / 4) * ‖f τ‖ ≤ C :=
    HeckeBound.phi_bounded M hN hf
  have hθ : ∃ C : ℝ, ∀ τ : ℍ, ‖thetaTwist ψ t τ‖ ≤ C * (1 + τ.im ^ (-2 : ℝ)) :=
    let ⟨C, _, h⟩ := norm_thetaTwist_le ψ ht; ⟨C, h⟩
  obtain ⟨σd, hσd⟩ := hdual
  have hgf : ∀ w : ℂ, 0 < w.re → gammaFactor (4 * N * r ^ 2) w ≠ 0 := by
    intro w hw
    unfold gammaFactor
    refine mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hw)
    refine (Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_).2 ?_
    · intro h
      have h' : w = 0 := neg_eq_zero.1 h
      rw [h'] at hw; simp at hw
    · have h0 : 0 < 4 * N * r ^ 2 := by positivity
      have : (0 : ℝ) < 2 * π / Real.sqrt (4 * N * r ^ 2 : ℕ) :=
        div_pos (by positivity) (Real.sqrt_pos.2 (by exact_mod_cast h0))
      exact_mod_cast this.ne'
  by_cases hpar : rankinChar k N χ t ψ (-1) = (-1) ^ (k - charParity ψ)
  · obtain ⟨E, hEd, hEc, hE1, hE2, hEb⟩ :=
      hE.fe (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) hL2 (by omega) hpar
    have hRd := differentiable_rankinIntegral M hN hf ψ ht hEd hEc hEb R
    have hRb := bddVStrips_rankinIntegral M hN hf ψ ht hEd hEc hEb R
    set Ea : ℂ → ℂ := fun w ↦ rankinRho k N t ψ w * rankinIntegral k ψ t f R E (rankinS k w) with hEa
    set Eb : ℂ → ℂ := fun w ↦ C⁻¹ * Ea (2 * (k : ℂ) - w) with hEbdef
    have hEad : Differentiable ℂ Ea :=
      (differentiable_rankinRho k N t hN ht hr1 ψ).mul (hRd.comp (by unfold rankinS; fun_prop))
    have hEab : BddVStrips Ea := by
      have h2 : BddVStrips (fun w ↦ rankinIntegral k ψ t f R E (rankinS k w)) := by
        have := hRb.comp_affine (a := 1 / 2) (by norm_num) ((1 - k) / 2)
        simpa only [← rankinS_eq_affine] using this
      exact (bddVStrips_rankinRho k N t hN ht hr1 ψ).mul h2
    have hEbd : Differentiable ℂ Eb := (hEad.comp (by fun_prop)).const_mul _
    have hEbb : BddVStrips Eb := by
      have := hEab.comp_sub (2 * k : ℝ)
      push_cast at this
      exact this.const_mul C⁻¹
    refine ⟨Ea, Eb, hEad, hEbd, hEab, hEbb, ⟨max ((k : ℝ) + 8) σd, fun w hw ↦ ⟨?_, ?_⟩⟩, fun w ↦ ?_⟩
    · have hw1 : (k : ℝ) + 8 < w.re := lt_of_le_of_lt (le_max_left _ _) hw
      have hs1 : 1 < (rankinS k w).re := by rw [re_rankinS]; linarith
      have hs4 : 4 < (rankinS k w).re := by rw [re_rankinS]; linarith
      have hI : rankinIntegral k ψ t f R E (rankinS k w) =
          ((rankinLevel N t r : ℂ) ^ rankinS k w * (π : ℂ) ^ (-rankinS k w) *
            Gamma (rankinS k w + ((k - charParity ψ : ℕ) : ℂ) / 2)) *
          repsIntegral R (fun τ ↦ rankinKernel k ψ t f τ *
            eisensteinLattice (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) τ (rankinS k w)) := by
        unfold rankinIntegral
        rw [← repsIntegral_const_mul]
        refine repsIntegral_congr R fun τ ↦ ?_
        rw [hE1 τ _ hs1]
        ring
      have hU' := hU.unfold (rankinLevel N t r) (k - charParity ψ) (rankinChar k N χ t ψ) R (by omega) hR
        (rankinKernel k ψ t f) hGc hlaw (rankinS k w) hs1
        (integrableOn_rankinKernel_strip k ψ ht hf.holo.continuous ha ha0 hφ (continuous_thetaTwist ψ ht) hθ hs4)
      rw [hU', hstrip w (by linarith), hLω w] at hI
      have key := rankinRho_mul_eq_gammaFactor k N hN ht hr1 ψ hν1 hνk w
      simp only [hEa, hI, zero_div, mul_zero, add_zero]
      rw [← key]
      ring
    · have hwd : σd < w.re := lt_of_le_of_lt (le_max_right _ _) hw
      have hw1 : (k : ℝ) + 8 < w.re := lt_of_le_of_lt (le_max_left _ _) hw
      have hs0 : (rankinS k (2 * k - w)).re < 0 := by
        rw [re_rankinS]
        simp only [sub_re, mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero, sub_zero]
        linarith
      have hI : rankinIntegral k ψ t f R E (rankinS k (2 * k - w)) =
          ((rankinLevel N t r : ℂ) ^ (-rankinS k (2 * k - w)) * (π : ℂ) ^ (-(1 - rankinS k (2 * k - w))) *
            Gamma (1 - rankinS k (2 * k - w) + ((k - charParity ψ : ℕ) : ℂ) / 2)) *
          rankinDual k N χ t ψ f R (1 - rankinS k (2 * k - w)) := by
        unfold rankinIntegral rankinDual
        rw [← repsIntegral_const_mul]
        refine repsIntegral_congr R fun τ ↦ ?_
        rw [hE2 τ _ hs0]
        ring
      rw [one_sub_rankinS_two_mul_sub] at hI
      have hd := hσd w hwd
      unfold rankinDualFactor at hd
      rw [one_sub_rankinS_two_mul_sub] at hd
      have hEa2 : Ea (2 * (k : ℂ) - w) = C * (gammaFactor (4 * N * r ^ 2) w * LSeries b w) := by
        simp only [hEa]
        rw [hI, ← hd]
        ring
      simp only [hEbdef, hEa2, zero_div, mul_zero, add_zero]
      field_simp
    · simp only [hEbdef]
      push_cast
      field_simp
  · -- The law at `-1` forces the kernel to vanish.
    have hG0 : ∀ τ, rankinKernel k ψ t f τ = 0 := by
      intro τ
      have hm1 : (-1 : SL(2, ℤ)) ∈ Gamma0 (rankinLevel N t r) := by
        rw [Gamma0_mem]; simp
      have h := hlaw (-1) hm1 τ
      have hsm : ((-1 : SL(2, ℤ)) • τ) = τ := by
        rw [ModularGroup.SL_neg_smul, one_smul]
      rw [hsm] at h
      have e1 : ((-1 : SL(2, ℤ)) 1 0 : ℤ) = 0 := by simp
      have e2 : ((-1 : SL(2, ℤ)) 1 1 : ℤ) = -1 := by simp
      rw [e1, e2] at h
      simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_neg, Int.cast_one, norm_neg, norm_one,
        Complex.ofReal_one, div_one] at h
      have hω2 : rankinChar k N χ t ψ (-1) ^ 2 = 1 := by
        rw [sq, ← map_mul]; simp
      have hne : rankinChar k N χ t ψ (-1) * (-1) ^ (k - charParity ψ) ≠ 1 := by
        intro h1
        apply hpar
        have h3 : ((-1 : ℂ) ^ (k - charParity ψ)) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul]; simp
        linear_combination (-1 : ℂ) ^ (k - charParity ψ) * h1 - rankinChar k N χ t ψ (-1) * h3
      have : (1 - rankinChar k N χ t ψ (-1) * (-1) ^ (k - charParity ψ)) * rankinKernel k ψ t f τ = 0 := by
        have h' : rankinKernel k ψ t f τ =
            rankinChar k N χ t ψ (-1) * (-1) ^ (k - charParity ψ) * rankinKernel k ψ t f τ := by
          simpa [Int.cast_neg, Int.cast_one] using h
        linear_combination h'
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd (sub_eq_zero.1 h1).symm hne
      · exact h1
    have hG0' : rankinKernel k ψ t f = fun _ ↦ 0 := funext hG0
    refine HeckeConditionL.congr (La' := fun _ ↦ 0) (Lb' := fun _ ↦ 0)
      ⟨(k : ℝ) + 2, fun w hw ↦ ?_⟩ ⟨max σd 1, fun w hw ↦ ?_⟩ ?_
    · have h := hstrip w (by linarith)
      rw [hG0', stripMellin_zero] at h
      have hre : 0 < ((w + charParity ψ) / 2).re := by
        rw [show (w + (charParity ψ : ℂ)) / 2 = ((1 / 2 : ℝ) : ℂ) * (w + charParity ψ) by push_cast; ring,
          Complex.re_ofReal_mul, add_re, natCast_re]
        have : (0 : ℝ) ≤ charParity ψ := by positivity
        nlinarith
      have hΓ := Complex.Gamma_ne_zero_of_re_pos hre
      have hcp : (((4 * π * t : ℝ) : ℂ) ^ (-((w + charParity ψ) / 2))) ≠ 0 := by
        refine (Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_).2 ?_
        · intro h0
          have := congrArg Complex.re h0
          simp only [neg_re, zero_re, neg_eq_zero] at this
          linarith
        · have : (0 : ℝ) < 4 * π * t := by
            have : (1 : ℝ) ≤ t := by exact_mod_cast ht
            positivity
          exact_mod_cast this.ne'
      have hL0 : LSeries (twist ψ fun m ↦ a (t * m ^ 2)) w = 0 := by
        have h2 := h.symm
        rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · rcases mul_eq_zero.1 h4 with h5 | h5
            · norm_num at h5
            · exact absurd h5 hΓ
          · exact absurd h4 hcp
        · exact h3
      simp only [hL0, mul_zero]
    · have hd := hσd w (lt_of_le_of_lt (le_max_left _ _) hw)
      have hD0 : rankinDual k N χ t ψ f R (rankinS k w) = 0 := by
        unfold rankinDual
        rw [repsIntegral_congr R (h' := fun _ ↦ 0) (fun τ ↦ by rw [hG0 τ, zero_mul])]
        exact repsIntegral_zero R
      rw [hD0, mul_zero, eq_comm] at hd
      have hw0 : 0 < w.re := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hw.le)
      rcases mul_eq_zero.1 hd with h1 | h1
      · exact absurd h1 hC
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 (hgf w hw0)
        · exact h2
    · refine ⟨fun _ ↦ 0, fun _ ↦ 0, differentiable_const _, differentiable_const _,
        fun _ _ ↦ ⟨0, fun s _ _ ↦ by simp⟩, fun _ _ ↦ ⟨0, fun s _ _ ↦ by simp⟩, ⟨0, fun s _ ↦ ?_⟩, fun s ↦ ?_⟩
      · simp
      · simp

/-! ### The headline -/

/-- **Shimura's twisted functional equations from the Rankin integral** (Shimura 1973 `shimura1973`, proof of the Main
Theorem [unverified]): for $N \ge 1$, `ShimuraTwistedFE M k N χ` follows from the law of the twisted theta series
(`ThetaTwistLaw M`), Hecke's functional equation of the Eisenstein series (`EisensteinFE`), the unfolding principle
(`RankinUnfolding`) and Shimura's dual unfolding identity (`ShimuraDualUnfolding M k N χ`). -/
@[kb "shimura1973" "proof of the Main Theorem: the twisted functional equations from the Rankin integral [unverified]"]
theorem shimuraTwistedFE_of_rankin (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hT : ThetaTwistLaw M) (hE : EisensteinFE) (hU : RankinUnfolding) (hD : ShimuraDualUnfolding M k N χ) :
    ShimuraTwistedFE M k N χ := by
  refine ⟨fun hk t ht hsq f hf a ha ↦ ?_⟩
  obtain ⟨b, hb, hb0, hd1, hd2⟩ := hD.dual hk t ht hsq f hf a ha
  refine ⟨b, hb, hb0, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := exists_isGamma0Reps (rankinLevel N t 1) (Nat.one_le_iff_ne_zero.2 (by unfold rankinLevel; positivity))
    have h := heckeConditionL_of_rankin M hT hE hU hN hk hf ha ht (Or.inl rfl) (1 : DirichletCharacter ℂ 1) hR
      (C := I ^ (2 * k)) (pow_ne_zero _ I_ne_zero) (b := b)
      (by simpa only [one_pow, mul_one] using hd1 R hR)
    simpa only [twist_one, one_pow, mul_one] using h
  · intro m hm hm2 hmN ψ hψ
    obtain ⟨R, hR⟩ := exists_isGamma0Reps (rankinLevel N t m) (Nat.one_le_iff_ne_zero.2 (by unfold rankinLevel; have := hm.pos; positivity))
    exact heckeConditionL_of_rankin M hT hE hU hN hk hf ha ht (Or.inr ⟨hm, hm2⟩) ψ hR
      (mul_ne_zero (pow_ne_zero _ I_ne_zero) (weilConstant_ne_zero hm hmN χ ψ hψ)) (hd2 m hm hm2 hmN ψ hψ R hR)

/-- **Shimura's theorem from the Rankin integral** (Shimura 1973 `shimura1973`, Main Theorem [unverified]): for $N \ge 1$,
`ShimuraTheorem M k N χ` from `ThetaTwistLaw M`, `EisensteinFE`, `RankinUnfolding` and `ShimuraDualUnfolding M k N χ`
(Weil's converse theorem and Hecke's bound are proved). -/
@[kb "shimura1973" "Main Theorem, reduced to the theta law, the Eisenstein functional equation, unfolding and the dual identity [unverified]"]
theorem shimuraTheorem_of_rankin (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hT : ThetaTwistLaw M) (hE : EisensteinFE) (hU : RankinUnfolding) (hD : ShimuraDualUnfolding M k N χ) :
    ShimuraTheorem M k N χ :=
  shimuraTheorem_of_twistedFE M k N χ hN (shimuraTwistedFE_of_rankin M k N χ hN hT hE hU hD)

end ModularFormsKB.HalfIntegral
