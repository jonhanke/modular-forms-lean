/-
# Cusp forms of half-integral weight decay exponentially at every cusp

Groundwork for the Petersson product (`ModularFormsKB/HalfIntegral/Abstract/PeterssonFour.lean`). Relative to an
abstract multiplier system `M`, let $f \in S_{k+1/2}(4N, \chi)$ and $\gamma \in \mathrm{SL}_2(\mathbb Z)$. Then
$$|c\tau + d|^{-(2k+1)}\,|f(\gamma\tau)|^2 = O(e^{-a\operatorname{Im}\tau}) \quad (\operatorname{Im}\tau \to \infty)$$
for some $a > 0$ (`cuspNorm_sq_isBigO_exp`).

**Proof.** Put $h = 4N$, $G(\tau) = f(\gamma\tau)^2(c\tau+d)^{-(2k+1)}$ (integral weight, no branch of a square root is needed)
and $\delta = \gamma T^h\gamma^{-1} \in \Gamma(4N)$. The function $u(z) = j(\delta, z)^2/(c_\delta z + d_\delta)$ is holomorphic on
$\mathbb H$ of absolute value $1$, hence constant (maximum modulus principle, `eq_of_norm_eq_one`), and
$G(\tau + h) = \lambda\,G(\tau)$ with $\lambda = u^{2k+1}$, $|\lambda| = 1$. Choosing $0 \le \beta < 2\pi/h$ with
$e^{i\beta h}\lambda = 1$, the function $e^{i\beta\tau}G(\tau)$ is $h$-periodic, holomorphic and tends to $0$ at $i\infty$, so it
is $O(e^{-2\pi\operatorname{Im}\tau/h})$ (Mathlib's `Function.Periodic.exp_decay_of_zero_at_inf`). Hence $a = 2\pi/h - \beta$.
-/
import ModularFormsKB.HalfIntegral.Abstract.Multiplier
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Complex.AbsMax

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup ModularForm UpperHalfPlane Filter Asymptotics
open scoped Real
open scoped Manifold

/-- **A holomorphic function on $\mathbb H$ of absolute value $1$ is constant** (maximum modulus principle). -/
theorem eq_of_norm_eq_one {u : ℍ → ℂ} (hu : MDiff u) (hn : ∀ τ, ‖u τ‖ = 1) (τ : ℍ) : u τ = u I := by
  have hd := UpperHalfPlane.mdifferentiable_iff.1 hu
  have h := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (c := ((I : ℍ) : ℂ))
    (convex_halfSpace_im_gt 0).isPreconnected isOpen_upperHalfPlaneSet hd (by simp)
    (fun z _ ↦ by simp [hn]) (show 0 < (τ : ℂ).im from τ.im_pos)
  simp only [Function.comp_apply, Function.const_apply, ofComplex_apply] at h
  exact h

/-- $\gamma T^n \gamma^{-1} \in \Gamma(n)$. -/
theorem conj_T_pow_mem_Gamma (γ : SL(2, ℤ)) (n : ℕ) :
    γ * ModularGroup.T ^ (n : ℤ) * γ⁻¹ ∈ Gamma n := by
  have hT : ModularGroup.T ^ (n : ℤ) ∈ Gamma n := by
    rw [Gamma_mem, ModularGroup.coe_T_zpow]
    simp
  exact (Gamma_normal n).conj_mem _ hT γ

theorem denom_SL_eq (γ : SL(2, ℤ)) (τ : ℍ) : denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := by
  simp [ModularGroup.denom_apply]

theorem mdiff_denom (γ : SL(2, ℤ)) : MDiff (fun τ : ℍ ↦ denom γ τ) := by
  simp_rw [denom_SL_eq]
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun z : ℂ ↦ (γ 1 0 : ℂ) * z + γ 1 1) (by fun_prop) fun z hz ↦ ?_
  simp [Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- **The ratio $j(\delta, z)^2/(c_\delta z + d_\delta)$ is a constant of absolute value $1$** for $\delta \in \Gamma_0(4)$. -/
theorem MultiplierSystem.ratio_const (M : MultiplierSystem) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 4) :
    ∃ μ : ℂ, ‖μ‖ = 1 ∧ ∀ z : ℍ, M.j δ z ^ 2 = μ * denom δ z := by
  set u : ℍ → ℂ := fun z ↦ M.j δ z ^ 2 / denom δ z
  have hden : ∀ z : ℍ, denom δ z ≠ 0 := fun z ↦ denom_ne_zero _ z
  have hn : ∀ z, ‖u z‖ = 1 := fun z ↦ by
    simp only [u, norm_div, norm_pow, M.norm_sq δ hδ z, denom_SL_eq]
    exact div_self (by rw [← denom_SL_eq]; exact norm_ne_zero_iff.2 (hden z))
  have hu : MDiff u := by
    rw [UpperHalfPlane.mdifferentiable_iff] at *
    have h1 := UpperHalfPlane.mdifferentiable_iff.1 ((M.holo δ hδ).pow 2)
    have h2 := UpperHalfPlane.mdifferentiable_iff.1 (mdiff_denom δ)
    refine (h1.div h2 fun z hz ↦ hden _).congr fun z hz ↦ ?_
    simp [u]
  refine ⟨u I, by rw [hn], fun z ↦ ?_⟩
  rw [← eq_of_norm_eq_one hu hn z]
  simp only [u]
  field_simp [hden z]

/-- $G(\tau) = f(\gamma\tau)^2\,(c\tau+d)^{-(2k+1)}$, the square of $f$ at the cusp $\gamma\infty$ in integral weight $2k+1$. -/
noncomputable def cuspSq (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  f (γ • τ) ^ 2 * (denom γ τ ^ (2 * k + 1))⁻¹

theorem norm_cuspSq (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖cuspSq k f γ τ‖ = Abstract.cuspNorm k f γ τ ^ 2 := by
  have hx : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
    rw [← denom_SL_eq]; exact norm_pos_iff.2 (denom_ne_zero _ τ)
  rw [cuspSq, Abstract.cuspNorm, norm_mul, norm_inv, norm_pow, norm_pow, denom_SL_eq, mul_pow,
    ← Real.rpow_natCast (_ ^ _) 2, ← Real.rpow_mul hx.le, neg_mul, Real.rpow_neg hx.le, mul_comm]
  congr 2
  rw [← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem mdiff_cuspSq (k : ℕ) {f : ℍ → ℂ} (hf : MDiff f) (γ : SL(2, ℤ)) : MDiff (cuspSq k f γ) := by
  have h := (hf.pow 2).slash ((2 * k + 1 : ℕ) : ℤ) (γ : GL (Fin 2) ℝ)
  convert h using 1
  funext τ
  rw [← SL_slash, SL_slash_apply, cuspSq, zpow_neg, zpow_natCast]
  rfl

private theorem mem_Gamma0_of_mem_Gamma {n : ℕ} {δ : SL(2, ℤ)} (h : δ ∈ Gamma n) : δ ∈ Gamma0 n := by
  rw [Gamma_mem] at h
  rw [Gamma0_mem]
  exact h.2.2.1

private theorem mem_Gamma0_four {N : ℕ} {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 (4 * N)) : γ ∈ Gamma0 4 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at *
  exact dvd_trans (by push_cast; exact dvd_mul_right (4 : ℤ) N) h

theorem denom_T_zpow (n : ℤ) (τ : ℍ) : denom ((ModularGroup.T ^ n : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = 1 := by
  rw [denom_SL_eq]
  have h1 : ((ModularGroup.T ^ n : SL(2, ℤ)) 1 0) = 0 := by simp [ModularGroup.coe_T_zpow]
  have h2 : ((ModularGroup.T ^ n : SL(2, ℤ)) 1 1) = 1 := by simp [ModularGroup.coe_T_zpow]
  simp [h1, h2]

/-- **Quasi-periodicity at the cusp $\gamma\infty$:** $G(\tau + 4N) = \lambda\,G(\tau)$ with $|\lambda| = 1$. -/
theorem MultiplierSystem.cuspSq_T_pow (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N))
    {f : ℍ → ℂ} (hf : M.Transforms k N χ f) (γ : SL(2, ℤ)) :
    ∃ l : ℂ, ‖l‖ = 1 ∧ ∀ τ : ℍ,
      cuspSq k f γ (ModularGroup.T ^ ((4 * N : ℕ) : ℤ) • τ) = l * cuspSq k f γ τ := by
  set δ := γ * ModularGroup.T ^ ((4 * N : ℕ) : ℤ) * γ⁻¹
  have hδΓ := conj_T_pow_mem_Gamma γ (4 * N)
  have hδ0 : δ ∈ Gamma0 (4 * N) := mem_Gamma0_of_mem_Gamma hδΓ
  have hd : ((δ 1 1 : ℤ) : ZMod (4 * N)) = 1 := ((Gamma_mem.1 hδΓ).2.2.2)
  obtain ⟨μ, hμ, hμz⟩ := M.ratio_const (mem_Gamma0_four hδ0)
  refine ⟨μ ^ (2 * k + 1), by rw [norm_pow, hμ, one_pow], fun τ ↦ ?_⟩
  have hγT : γ * ModularGroup.T ^ ((4 * N : ℕ) : ℤ) = δ * γ := by simp [δ, mul_assoc]
  have hsmul : γ • (ModularGroup.T ^ ((4 * N : ℕ) : ℤ) • τ) = δ • (γ • τ) := by
    rw [← mul_smul, ← mul_smul, hγT]
  have hden : denom γ ((ModularGroup.T ^ ((4 * N : ℕ) : ℤ) • τ : ℍ) : ℂ) =
      denom δ ((γ • τ : ℍ) : ℂ) * denom γ τ := by
    have h1 := denom_cocycle_σ (γ : GL (Fin 2) ℝ)
      ((ModularGroup.T ^ ((4 * N : ℕ) : ℤ) : SL(2, ℤ)) : GL (Fin 2) ℝ) τ
    have h2 := denom_cocycle_σ (δ : GL (Fin 2) ℝ) (γ : GL (Fin 2) ℝ) τ
    have h3 := congrArg (fun g : SL(2, ℤ) ↦ denom (g : GL (Fin 2) ℝ) (τ : ℂ)) hγT
    have h4 := denom_T_zpow ((4 * N : ℕ) : ℤ) τ
    simp only [map_mul] at h3
    rw [h1, h2, h4] at h3
    simpa [σ] using h3
  have hfδ := hf δ hδ0 (γ • τ)
  rw [hd, map_one, one_mul] at hfδ
  have hd1 : denom δ ((γ • τ : ℍ) : ℂ) ≠ 0 := denom_ne_zero _ _
  have hd2 : denom γ τ ≠ 0 := denom_ne_zero _ _
  simp only [cuspSq]
  rw [hsmul, hden, hfδ, mul_pow, ← pow_mul, mul_comm (2 * k + 1) 2, pow_mul, hμz (γ • τ)]
  field_simp
  ring

/-- For $|l| = 1$ and $h > 0$ there is $0 \le \beta < 2\pi/h$ with $e^{i\beta h}\,l = 1$. -/
theorem exists_twist {l : ℂ} (hl : ‖l‖ = 1) {h : ℝ} (hh : 0 < h) :
    ∃ β : ℝ, 0 ≤ β ∧ β * h < 2 * π ∧ cexp (β * h * Complex.I) * l = 1 := by
  have hl' : l = cexp (l.arg * Complex.I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I l, hl]
    simp
  have h1 := neg_pi_lt_arg l
  have h2 := arg_le_pi l
  generalize l.arg = θ at hl' h1 h2
  subst hl'
  have hh' : (h : ℂ) ≠ 0 := ofReal_ne_zero.2 hh.ne'
  rcases le_or_gt θ 0 with h0 | h0
  · refine ⟨-θ / h, div_nonneg (by linarith) hh.le, ?_, ?_⟩
    · rw [div_mul_cancel₀ _ hh.ne']; linarith
    · rw [← Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast
      field_simp
      ring
  · refine ⟨(2 * π - θ) / h, div_nonneg (by linarith) hh.le, ?_, ?_⟩
    · rw [div_mul_cancel₀ _ hh.ne']; linarith
    · rw [← Complex.exp_add]
      have : ((((2 * π - θ) / h : ℝ) : ℂ) * h * Complex.I + θ * Complex.I) = 2 * π * Complex.I := by
        push_cast
        field_simp
        ring
      rw [this, Complex.exp_two_pi_mul_I]

/-- **Exponential decay at every cusp** for $f \in S_{k+1/2}(4N, \chi)$, $N \ge 1$:
$|c\tau+d|^{-(2k+1)}|f(\gamma\tau)|^2 = O(e^{-a\operatorname{Im}\tau})$ for some $a > 0$. -/
theorem MultiplierSystem.cuspNorm_sq_isBigO_exp (M : MultiplierSystem) (k N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ (4 * N)) {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) (γ : SL(2, ℤ)) :
    ∃ a : ℝ, 0 < a ∧
      (fun τ ↦ Abstract.cuspNorm k f γ τ ^ 2) =O[atImInfty] fun τ ↦ Real.exp (-a * τ.im) := by
  set h : ℝ := ((4 * N : ℕ) : ℝ)
  have hh : 0 < h := by positivity
  obtain ⟨l, hl, hper⟩ := M.cuspSq_T_pow k N χ hf.transforms γ
  obtain ⟨β, hβ0, hβh, hβl⟩ := exists_twist hl hh
  set G := cuspSq k f γ
  have hG : MDiff G := mdiff_cuspSq k hf.holo γ
  have hGn : ∀ τ, ‖G τ‖ = Abstract.cuspNorm k f γ τ ^ 2 := norm_cuspSq k f γ
  set Φ : ℂ → ℂ := fun z ↦ if 0 < z.im then cexp (β * z * Complex.I) * G (ofComplex z) else 0
  -- `Φ` is periodic.
  have hΦper : Function.Periodic Φ h := by
    intro z
    by_cases hz : 0 < z.im
    · have hz' : 0 < (z + h).im := by simpa using hz
      have hof : ofComplex (z + h) = ModularGroup.T ^ ((4 * N : ℕ) : ℤ) • ofComplex z := by
        apply UpperHalfPlane.ext
        rw [ModularGroup.coe_T_zpow_smul_eq, ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz]
        simp [h]
      simp only [Φ, hz, hz', ↓reduceIte, hof, hper]
      rw [show cexp (β * (z + h) * Complex.I) * (l * G (ofComplex z)) =
          (cexp (β * h * Complex.I) * l) * (cexp (β * z * Complex.I) * G (ofComplex z)) by
        rw [show (β : ℂ) * (z + h) * Complex.I = β * h * Complex.I + β * z * Complex.I by ring, Complex.exp_add]
        ring, hβl, one_mul]
    · have hz' : ¬ 0 < (z + h).im := by simpa using hz
      simp only [Φ, hz, hz', ↓reduceIte]
  -- `Φ` is holomorphic on the upper half-plane.
  have hupper : {z : ℂ | 0 < z.im} ∈ Filter.comap Complex.im atTop :=
    ⟨Set.Ioi 0, Ioi_mem_atTop 0, fun z hz ↦ hz⟩
  have hΦdiff : ∀ᶠ z in Filter.comap Complex.im atTop, DifferentiableAt ℂ Φ z := by
    filter_upwards [hupper] with z hz
    have hGd := (UpperHalfPlane.mdifferentiable_iff.1 hG).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hz)
    have hd : DifferentiableAt ℂ (fun z ↦ cexp (β * z * Complex.I) * (G ∘ ofComplex) z) z :=
      (by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ cexp (β * z * Complex.I)) z).mul hGd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    simp [Φ, show 0 < w.im from hw]
  -- `Φ` tends to zero at `i∞`.
  have hΦzero : ZeroAtFilter (Filter.comap Complex.im atTop) Φ := by
    have hc : Tendsto (fun z ↦ Abstract.cuspNorm k f γ (ofComplex z) ^ 2) (Filter.comap Complex.im atTop)
        (nhds 0) := by
      have := ((hf.zero_at_cusps γ).comp tendsto_comap_im_ofComplex).pow 2
      simpa using this
    refine squeeze_zero_norm' ?_ hc
    filter_upwards [hupper] with z hz
    simp only [Φ, show 0 < z.im from hz, ↓reduceIte, norm_mul, Complex.norm_exp, hGn]
    refine mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.2 ?_)
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [hz.le]
  have hdecay := (Function.Periodic.exp_decay_of_zero_at_inf hh hΦper hΦdiff hΦzero).comp_tendsto
    tendsto_coe_atImInfty
  refine ⟨2 * π / h - β, by rw [sub_pos, lt_div_iff₀ hh]; linarith, ?_⟩
  have hmul := (isBigO_refl (fun τ : ℍ ↦ Real.exp (β * τ.im)) atImInfty).mul hdecay.norm_left
  refine (hmul.congr' (Eventually.of_forall fun τ ↦ ?_) (Eventually.of_forall fun τ ↦ ?_))
  · simp only [Function.comp_apply, Φ, coe_im, τ.im_pos, ↓reduceIte, ofComplex_apply, norm_mul, Complex.norm_exp,
      hGn]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  · simp only [Function.comp_apply, coe_im]
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring

end ModularFormsKB.HalfIntegral
