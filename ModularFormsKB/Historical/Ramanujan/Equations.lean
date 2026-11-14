import ModularFormsKB.Historical.Ramanujan.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Ramanujan's differential equations and his table of `Φ_{1,s}`

* `x_deriv_P`, `x_deriv_Q`, `x_deriv_R`: Ramanujan's differential equations (No. 18, § 7, (30), p. 142) in his
  variable `x`, `|x| < 1`.
* `x_deriv_P_eq_Phi`, `x_deriv_Q_eq_Phi`, `x_deriv_R_eq_Phi`: `x dP/dx = -24 Φ_{1,2}`,
  `x dQ/dx = 240 Φ_{1,4}`, `x dR/dx = -504 Φ_{1,6}` (termwise differentiation; No. 18, (30)).
* `Q_sub_P_sq`, `P_mul_Q_sub_R`, `Q_sq_sub_P_mul_R`, `Q_mul_P_mul_Q_sub_R`: the table
  `Q - P² = 288 Φ_{1,2}`, `PQ - R = 720 Φ_{1,4}`, `Q² - PR = 1008 Φ_{1,6}`, `Q(PQ - R) = 720 Φ_{1,8}`
  (No. 30, § 1, (1.71)–(1.74), p. 233). The last one uses `Q² = E₈`.

The `τ`-form of the differential equations is Mathlib's (`ode_tau_P` etc. are thin wrappers).
-/

noncomputable section

open Complex ArithmeticFunction
open UpperHalfPlane hiding I
open scoped ArithmeticFunction.sigma Real MatrixGroups

namespace ModularFormsKB.Historical.Ramanujan

/-! ### The change of variable `x = e^{2πiτ}` -/

theorem P_exp (τ : ℍ) : P (cexp (2 * π * I * τ)) = EisensteinSeries.E2 τ := by
  rw [EisensteinSeries.E2_eq_tsum_cexp, P]

theorem Q_exp (τ : ℍ) : Q (cexp (2 * π * I * τ)) = ModularForm.E₄ τ := by
  have := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) τ
  simp_rw [zpow_natCast] at this
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  show _ = ModularForm.E _ τ
  rw [this, hb, Q]
  norm_num

theorem R_exp (τ : ℍ) : R (cexp (2 * π * I * τ)) = ModularForm.E₆ τ := by
  have := EisensteinSeries.q_expansion_bernoulli (k := 6) (by norm_num) (by decide) τ
  simp_rw [zpow_natCast] at this
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  show _ = ModularForm.E _ τ
  rw [this, hb, R]
  norm_num

/-! ### Ramanujan's differential equations in `τ` (Mathlib) -/

/-- **Ramanujan's equation for `P`** in the variable `τ`, `D = (2πi)⁻¹ d/dτ`: `D E₂ = (E₂² - E₄)/12`.
Wrapper of Mathlib's `Derivative.normalizedDerivOfComplex_E₂`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem ode_tau_P : Derivative.normalizedDerivOfComplex EisensteinSeries.E2 =
    (12⁻¹ : ℂ) • (EisensteinSeries.E2 ^ 2 - ⇑ModularForm.E₄) :=
  Derivative.normalizedDerivOfComplex_E₂

/-- **Ramanujan's equation for `Q`** in `τ`: `D E₄ = (E₂ E₄ - E₆)/3`. Wrapper of Mathlib. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem ode_tau_Q : Derivative.normalizedDerivOfComplex ModularForm.E₄ =
    (3⁻¹ : ℂ) • (EisensteinSeries.E2 * ⇑ModularForm.E₄ - ⇑ModularForm.E₆) :=
  Derivative.normalizedDerivOfComplex_E₄

/-- **Ramanujan's equation for `R`** in `τ`: `D E₆ = (E₂ E₆ - E₄²)/2`. Wrapper of Mathlib. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem ode_tau_R : Derivative.normalizedDerivOfComplex ModularForm.E₆ =
    (2⁻¹ : ℂ) • (EisensteinSeries.E2 * ⇑ModularForm.E₆ - ⇑ModularForm.E₄ ^ 2) :=
  Derivative.normalizedDerivOfComplex_E₆

/-! ### Termwise differentiation: `x d/dx` of the series -/

/-- Termwise differentiation of `∑ aₙ xⁿ` when `|aₙ| ≤ nᵏ`. -/
theorem hasDerivAt_series (a : ℕ+ → ℂ) (k : ℕ) (ha : ∀ n : ℕ+, ‖a n‖ ≤ (n : ℝ) ^ k)
    {x : ℂ} (hx : ‖x‖ < 1) :
    HasDerivAt (fun y : ℂ => ∑' n : ℕ+, a n * y ^ (n : ℕ))
      (∑' n : ℕ+, a n * ((n : ℂ) * x ^ ((n : ℕ) - 1))) x := by
  obtain ⟨r, hxr, hr1⟩ : ∃ r : ℝ, ‖x‖ < r ∧ r < 1 := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg x) hxr
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have hsum0 : Summable (fun n : ℕ => (n : ℝ) ^ (k + 1) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (k + 1) hr'
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (k + 1) * r ^ n / r) := hsum0.div_const r
  have hsum' : Summable (fun n : ℕ+ => (n : ℝ) ^ (k + 1) * r ^ (n : ℕ) / r) :=
    hsum.comp_injective PNat.coe_injective
  refine hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℂ) r) (y₀ := 0)
    (g := fun (n : ℕ+) (y : ℂ) => a n * y ^ (n : ℕ))
    (g' := fun (n : ℕ+) (y : ℂ) => a n * ((n : ℂ) * y ^ ((n : ℕ) - 1))) hsum'
    Metric.isOpen_ball (convex_ball _ _).isPreconnected ?_ ?_ (Metric.mem_ball_self hr0) ?_ ?_
  · intro n y _
    simpa using (hasDerivAt_pow (n : ℕ) y).const_mul (a n)
  · intro n y hy
    rw [mem_ball_zero_iff] at hy
    have hn : (1 : ℕ) ≤ n := n.pos
    have h1 : ‖y ^ ((n : ℕ) - 1)‖ ≤ r ^ ((n : ℕ) - 1) := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hy.le _
    have h2 : r ^ (n : ℕ) = r ^ ((n : ℕ) - 1) * r := by
      rw [← pow_succ]; congr 1; omega
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    calc ‖a n‖ * ((n : ℝ) * ‖y ^ ((n : ℕ) - 1)‖)
        ≤ (n : ℝ) ^ k * ((n : ℝ) * r ^ ((n : ℕ) - 1)) := by
          gcongr
          exact ha n
      _ = (n : ℝ) ^ (k + 1) * r ^ (n : ℕ) / r := by
          rw [h2]; field_simp; ring
  · simp
  · rw [mem_ball_zero_iff]; exact hxr

/-- `x f'(x) = ∑ n aₙ xⁿ` for `f = ∑ aₙ xⁿ`. -/
theorem x_mul_deriv_series (a : ℕ+ → ℂ) {x : ℂ} :
    x * ∑' n : ℕ+, a n * ((n : ℂ) * x ^ ((n : ℕ) - 1)) = ∑' n : ℕ+, (n : ℂ) * a n * x ^ (n : ℕ) := by
  rw [← tsum_mul_left]
  congr 1
  ext n
  have h : x * x ^ ((n : ℕ) - 1) = x ^ (n : ℕ) := by
    rw [← pow_succ']; congr 1; have := n.pos; omega
  rw [← h]
  ring

theorem sigma_norm_le (s : ℕ) (n : ℕ+) : ‖(σ s n : ℂ)‖ ≤ (n : ℝ) ^ (s + 1) := by
  rw [Complex.norm_natCast]
  exact_mod_cast ArithmeticFunction.sigma_le_pow_succ s n

/-- `x d/dx (1 + c ∑ σ_s(n) xⁿ) = c ∑ n σ_s(n) xⁿ`. -/
theorem x_mul_deriv_affine (c : ℂ) (s : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    x * deriv (fun y : ℂ => 1 + c * ∑' n : ℕ+, (σ s n : ℂ) * y ^ (n : ℕ)) x =
      c * ∑' n : ℕ+, (n : ℂ) * (σ s n : ℂ) * x ^ (n : ℕ) := by
  have h := hasDerivAt_series (fun n : ℕ+ => (σ s n : ℂ)) (s + 1) (sigma_norm_le s) hx
  rw [((h.const_mul c).const_add 1).deriv, mul_left_comm,
    x_mul_deriv_series (fun n : ℕ+ => (σ s n : ℂ))]

theorem Phi_one (s : ℕ) (x : ℂ) :
    Phi 1 (s + 1) x = ∑' n : ℕ+, (n : ℂ) * (σ s n : ℂ) * x ^ (n : ℕ) := by
  simp [Phi]

/-- `x dP/dx = -24 Φ_{1,2}(x)` for `|x| < 1` (Ramanujan No. 18, (30), first equality). -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem x_deriv_P_eq_Phi {x : ℂ} (hx : ‖x‖ < 1) : x * deriv P x = -24 * Phi 1 2 x := by
  have hP : P = fun y : ℂ => 1 + (-24 : ℂ) * ∑' n : ℕ+, (σ 1 n : ℂ) * y ^ (n : ℕ) := by
    funext y; simp [P]; ring
  rw [hP, x_mul_deriv_affine _ _ hx, Phi_one 1]

/-- `x dQ/dx = 240 Φ_{1,4}(x)` for `|x| < 1`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem x_deriv_Q_eq_Phi {x : ℂ} (hx : ‖x‖ < 1) : x * deriv Q x = 240 * Phi 1 4 x := by
  have hQ : Q = fun y : ℂ => 1 + (240 : ℂ) * ∑' n : ℕ+, (σ 3 n : ℂ) * y ^ (n : ℕ) := by
    funext y; simp [Q]
  rw [hQ, x_mul_deriv_affine _ _ hx, Phi_one 3]

/-- `x dR/dx = -504 Φ_{1,6}(x)` for `|x| < 1`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem x_deriv_R_eq_Phi {x : ℂ} (hx : ‖x‖ < 1) : x * deriv R x = -504 * Phi 1 6 x := by
  have hR : R = fun y : ℂ => 1 + (-504 : ℂ) * ∑' n : ℕ+, (σ 5 n : ℂ) * y ^ (n : ℕ) := by
    funext y; simp [R]; ring
  rw [hR, x_mul_deriv_affine _ _ hx, Phi_one 5]

/-! ### Ramanujan's differential equations in `x` -/

theorem P_zero : P 0 = 1 := by simp [P]

theorem Q_zero : Q 0 = 1 := by simp [Q]

theorem R_zero : R 0 = 1 := by simp [R]

theorem P_eq_fun : P = fun y : ℂ => 1 + (-24 : ℂ) * ∑' n : ℕ+, (σ 1 n : ℂ) * y ^ (n : ℕ) := by
  funext y; simp [P]; ring

theorem Q_eq_fun : Q = fun y : ℂ => 1 + (240 : ℂ) * ∑' n : ℕ+, (σ 3 n : ℂ) * y ^ (n : ℕ) := by
  funext y; simp [Q]

theorem R_eq_fun : R = fun y : ℂ => 1 + (-504 : ℂ) * ∑' n : ℕ+, (σ 5 n : ℂ) * y ^ (n : ℕ) := by
  funext y; simp [R]; ring

theorem differentiableAt_affine (c : ℂ) (s : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    DifferentiableAt ℂ (fun y : ℂ => 1 + c * ∑' n : ℕ+, (σ s n : ℂ) * y ^ (n : ℕ)) x :=
  (((hasDerivAt_series (fun n : ℕ+ => (σ s n : ℂ)) (s + 1) (sigma_norm_le s) hx).const_mul
    c).const_add 1).differentiableAt

theorem exists_tau {x : ℂ} (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    ∃ τ : ℍ, cexp (2 * π * I * τ) = x := by
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg (norm_pos_iff.mpr hx0) hx
  have him : 0 < (Complex.log x / (2 * π * I)).im := by
    simp [Complex.div_im, Complex.log_re]
    have hp := Real.pi_pos
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hlog (by positivity)) (by positivity)
  refine ⟨⟨_, him⟩, ?_⟩
  show cexp (2 * π * I * (Complex.log x / (2 * π * I))) = x
  rw [mul_div_cancel₀ _ hπ, Complex.exp_log hx0]

/-- Change of variable: `x G'(x) = D F (τ)` when `G (e^{2πiτ}) = F τ` and `x = e^{2πiτ}`. -/
theorem x_deriv_eq_normalizedDeriv (G : ℂ → ℂ) (F : ℍ → ℂ)
    (hFG : ∀ τ : ℍ, G (cexp (2 * π * I * τ)) = F τ) (τ : ℍ)
    (hd : DifferentiableAt ℂ G (cexp (2 * π * I * τ))) :
    cexp (2 * π * I * τ) * deriv G (cexp (2 * π * I * τ)) = Derivative.normalizedDerivOfComplex F τ := by
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have he : HasDerivAt (fun w : ℂ => cexp (2 * π * I * w)) (cexp (2 * π * I * τ) * (2 * π * I)) τ :=
    (((hasDerivAt_id (τ : ℂ)).const_mul (2 * π * I)).cexp).congr_deriv (by simp)
  have hc : HasDerivAt (G ∘ fun w : ℂ => cexp (2 * π * I * w))
      (deriv G (cexp (2 * π * I * τ)) * (cexp (2 * π * I * τ) * (2 * π * I))) (τ : ℂ) :=
    HasDerivAt.comp (τ : ℂ) hd.hasDerivAt he
  have hev : (F ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds (τ : ℂ)] G ∘ (fun w : ℂ => cexp (2 * π * I * w)) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp only [Function.comp_apply]
    rw [← hFG, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  rw [Derivative.normalizedDerivOfComplex, hev.deriv_eq, hc.deriv]
  field_simp

/-- **Ramanujan's differential equation for `P`** (No. 18, § 7, (30), p. 142):
`x dP/dx = (P² - Q)/12` for `|x| < 1`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem x_deriv_P {x : ℂ} (hx : ‖x‖ < 1) : x * deriv P x = (P x ^ 2 - Q x) / 12 := by
  by_cases hx0 : x = 0
  · subst hx0; simp [P_zero, Q_zero]
  obtain ⟨τ, rfl⟩ := exists_tau hx hx0
  have hd : DifferentiableAt ℂ P (cexp (2 * π * I * τ)) := by
    rw [P_eq_fun]; exact differentiableAt_affine _ _ hx
  rw [x_deriv_eq_normalizedDeriv P _ P_exp τ hd, ode_tau_P]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul, P_exp, Q_exp]
  ring

/-- **Ramanujan's differential equation for `Q`**: `x dQ/dx = (PQ - R)/3` for `|x| < 1`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem x_deriv_Q {x : ℂ} (hx : ‖x‖ < 1) : x * deriv Q x = (P x * Q x - R x) / 3 := by
  by_cases hx0 : x = 0
  · subst hx0; simp [P_zero, Q_zero, R_zero]
  obtain ⟨τ, rfl⟩ := exists_tau hx hx0
  have hd : DifferentiableAt ℂ Q (cexp (2 * π * I * τ)) := by
    rw [Q_eq_fun]; exact differentiableAt_affine _ _ hx
  rw [x_deriv_eq_normalizedDeriv Q _ Q_exp τ hd, ode_tau_Q]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul, P_exp, Q_exp, R_exp]
  ring

/-- **Ramanujan's differential equation for `R`**: `x dR/dx = (PR - Q²)/2` for `|x| < 1`. -/
@[kb "ramanujan1927" "No. 18, § 7, (30), p. 142"]
theorem x_deriv_R {x : ℂ} (hx : ‖x‖ < 1) : x * deriv R x = (P x * R x - Q x ^ 2) / 2 := by
  by_cases hx0 : x = 0
  · subst hx0; simp [P_zero, Q_zero, R_zero]
  obtain ⟨τ, rfl⟩ := exists_tau hx hx0
  have hd : DifferentiableAt ℂ R (cexp (2 * π * I * τ)) := by
    rw [R_eq_fun]; exact differentiableAt_affine _ _ hx
  rw [x_deriv_eq_normalizedDeriv R _ R_exp τ hd, ode_tau_R]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul, P_exp, Q_exp,
    R_exp]
  ring

/-! ### The table -/

/-- `Q - P² = 288 Φ_{1,2}` (Ramanujan No. 30, (1.71), p. 233). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.71), p. 233"]
theorem Q_sub_P_sq {x : ℂ} (hx : ‖x‖ < 1) : Q x - P x ^ 2 = 288 * Phi 1 2 x := by
  have h1 := x_deriv_P hx
  have h2 := x_deriv_P_eq_Phi hx
  linear_combination 12 * h1 - 12 * h2

/-- `PQ - R = 720 Φ_{1,4}` (Ramanujan No. 30, (1.72), p. 233). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.72), p. 233"]
theorem P_mul_Q_sub_R {x : ℂ} (hx : ‖x‖ < 1) : P x * Q x - R x = 720 * Phi 1 4 x := by
  have h1 := x_deriv_Q hx
  have h2 := x_deriv_Q_eq_Phi hx
  linear_combination (-3) * h1 + 3 * h2

/-- `Q² - PR = 1008 Φ_{1,6}` (Ramanujan No. 30, (1.73), p. 233). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.73), p. 233"]
theorem Q_sq_sub_P_mul_R {x : ℂ} (hx : ‖x‖ < 1) : Q x ^ 2 - P x * R x = 1008 * Phi 1 6 x := by
  have h1 := x_deriv_R hx
  have h2 := x_deriv_R_eq_Phi hx
  linear_combination 2 * h1 - 2 * h2

/-- `E₄² = E₈` (weight-8 level-one forms have rank one; both sides tend to `1` at `i∞`). -/
theorem E4_sq_eq_E8 :
    (⇑ModularForm.E₄ : ℍ → ℂ) ^ 2 = ⇑(ModularForm.E (k := 8) (by norm_num)) := by
  have hrank : Module.rank ℂ (ModularForm 𝒮ℒ 8) = 1 := by
    simpa [Nat.ModEq] using ModularForm.dimension_level_one 8 ⟨4, rfl⟩
  set g : ModularForm 𝒮ℒ 8 := ModularForm.E (k := 8) (by norm_num) with hgdef
  have hg1 : Filter.Tendsto (g : ℍ → ℂ) UpperHalfPlane.atImInfty (nhds 1) :=
    EisensteinSeries.tendsto_E_atImInfty (k := 8)
  have hg : g ≠ 0 := fun h =>
    one_ne_zero (tendsto_nhds_unique (h ▸ hg1) tendsto_const_nhds)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' g hg).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp hrank) (ModularForm.E₄.pow 2)
  have hcz : ∀ z : ℍ, c * g z = ModularForm.E₄ z ^ 2 := fun z => by
    have := congrArg (fun f : ModularForm 𝒮ℒ 8 => f z) hc
    have hp : (ModularForm.E₄.pow 2) z = ModularForm.E₄ z ^ 2 :=
      congrFun (ModularForm.coe_pow ModularForm.E₄ 2) z
    simpa [hp] using this
  have hF : Filter.Tendsto (fun z : ℍ => ModularForm.E₄ z ^ 2) UpperHalfPlane.atImInfty
      (nhds 1) := by
    simpa using (EisensteinSeries.tendsto_E_atImInfty (k := 4)).pow 2
  have hc1 : c = 1 := by
    have h2 : Filter.Tendsto (fun z : ℍ => c * g z) UpperHalfPlane.atImInfty (nhds c) := by
      simpa using hg1.const_mul c
    have h3 : Filter.Tendsto (fun z : ℍ => c * g z) UpperHalfPlane.atImInfty (nhds 1) := by
      simpa [hcz] using hF
    exact tendsto_nhds_unique h2 h3
  funext z
  have := hcz z
  rw [hc1, one_mul] at this
  simpa using this.symm

/-- `Q² = 1 + 480 ∑ σ₇(n) xⁿ` (`E₄² = E₈`; Ramanujan No. 18, Table I [table number from memory]). -/
@[kb "ramanujan1927" "No. 18, Q² = 1 + 480 Φ_{0,7}"]
theorem Q_sq {x : ℂ} (hx : ‖x‖ < 1) :
    Q x ^ 2 = 1 + 480 * ∑' n : ℕ+, (σ 7 n : ℂ) * x ^ (n : ℕ) := by
  by_cases hx0 : x = 0
  · subst hx0; simp [Q_zero]
  obtain ⟨τ, rfl⟩ := exists_tau hx hx0
  have h8 := EisensteinSeries.q_expansion_bernoulli (k := 8) (by norm_num) (by decide) τ
  simp_rw [zpow_natCast] at h8
  have hb : bernoulli 8 = -1 / 30 := by decide +kernel
  have h := congrFun E4_sq_eq_E8 τ
  rw [Q_exp]
  simp only [Pi.pow_apply] at h
  rw [h]
  show ModularForm.E _ τ = _
  rw [h8, hb]
  norm_num

/-- `Q(PQ - R) = 720 Φ_{1,8}` (Ramanujan No. 30, (1.74), p. 233). -/
@[kb "ramanujan1927" "No. 30, § 1, (1.74), p. 233"]
theorem Q_mul_P_mul_Q_sub_R {x : ℂ} (hx : ‖x‖ < 1) :
    Q x * (P x * Q x - R x) = 720 * Phi 1 8 x := by
  have hQ : HasDerivAt Q (deriv Q x) x := by
    rw [Q_eq_fun]
    exact (differentiableAt_affine _ _ hx).hasDerivAt
  have h1 : HasDerivAt (fun y => Q y ^ 2) (2 * Q x * deriv Q x) x := by
    have := hQ.fun_pow 2
    simpa using this
  have hev : (fun y => Q y ^ 2) =ᶠ[nhds x]
      fun y : ℂ => 1 + (480 : ℂ) * ∑' n : ℕ+, (σ 7 n : ℂ) * y ^ (n : ℕ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : ℂ) 1 by simpa using hx)]
      with y hy
    exact Q_sq (by simpa using hy)
  have h2 := x_mul_deriv_affine 480 7 hx
  rw [← hev.deriv_eq, h1.deriv] at h2
  have h3 := x_deriv_Q hx
  have h4 : Phi 1 8 x = ∑' n : ℕ+, (n : ℂ) * (σ 7 n : ℂ) * x ^ (n : ℕ) := Phi_one 7 x
  rw [← h4] at h2
  linear_combination (3 / 2) * h2 - 3 * Q x * h3

end ModularFormsKB.Historical.Ramanujan
