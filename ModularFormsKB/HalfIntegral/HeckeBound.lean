/-
# Hecke's bound in weight $k + \tfrac12$

Proves the named input `HeckeCoeffBound` (`Abstract/ShimuraWeil.lean`) for $N \ge 1$:
the coefficients of $f \in S_{k+1/2}(4N,\chi)$ satisfy $|a(n)| \le Cn^{(2k+1)/4}$ (Hecke's argument; Iwaniec 1997
`iwaniec1997`, §5 [unverified]). With $w = k + \tfrac12$ and $\varphi(\tau) = (\operatorname{Im}\tau)^{w/2}|f(\tau)|$:
1. $\varphi(\gamma\tau) = \varphi(\tau)$ for $\gamma \in \Gamma_0(4N)$ (`phi_smul`), from $|j(\gamma,\tau)|^2 = |c\tau+d|$.
2. Exponential decay at every cusp (`cuspNorm_sq_isBigO_exp`). For $g \in \mathrm{SL}_2(\mathbb Z)$ the function
   $G = (f^2)|_{2k+1}\,g$ (Mathlib's integral weight slash) is holomorphic with $|G| = $ `cuspNorm`$^2 \to 0$, and
   $G(\tau + 4N) = \varepsilon G(\tau)$ with $|\varepsilon| = 1$: the factor relating $f^2|_{2k+1}\delta$ and $f^2$ for
   $\delta = gT^{4N}g^{-1} \in \Gamma_0(4N)$ is holomorphic of absolute value $1$, hence constant
   (`eq_const_of_norm_eq_one`, maximum principle). Then $e^{-2\pi i\beta\tau/h}G$ is periodic and tends to $0$ for a
   suitable $\beta \in (-1, 0]$ (`isBigO_exp_of_twisted_periodic`).
3. $\varphi$ is bounded on $\mathbb H$ (`phi_bounded`, Mathlib's `ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO`).
4. The coefficients (`norm_coeff_le_of_norm_le`, `CoeffFromBound.lean`).

The case $N = 0$ (level $0$, where $\Gamma_0(0)$ has infinite index) is not claimed.

**Index shift.** Matrix entries are 0-based: $c = \gamma_{1,0}$, $d = \gamma_{1,1}$.
-/
import ModularFormsKB.HalfIntegral.Abstract.ShimuraWeil
import ModularFormsKB.HalfIntegral.CoeffFromBound
import ModularFormsKB.HalfIntegral.HeckePhi
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Analysis.Complex.AbsMax

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup Asymptotics Filter UpperHalfPlane
open scoped Real Manifold ModularForm Topology

namespace HeckeBound

/-- A holomorphic function on $\mathbb H$ of constant absolute value $1$ is constant (maximum principle). -/
theorem eq_const_of_norm_eq_one {u : UpperHalfPlane → ℂ} (hu : MDiff u) (h1 : ∀ τ, ‖u τ‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ τ, u τ = c := by
  refine ⟨u UpperHalfPlane.I, h1 _, fun τ ↦ ?_⟩
  have hd := UpperHalfPlane.mdifferentiable_iff.mp hu
  have hmax : IsMaxOn (norm ∘ (u ∘ ofComplex)) {z : ℂ | 0 < z.im} (UpperHalfPlane.I : ℂ) := by
    intro z hz
    simp only [Set.mem_ofPred_eq, Function.comp_apply]
    rw [h1, ofComplex_apply_of_im_pos (by simp), h1]
  have := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_halfSpace_im_gt 0).isPreconnected
    (isOpen_lt continuous_const Complex.continuous_im) hd (by simp) hmax
    (show (τ : ℂ) ∈ {z : ℂ | 0 < z.im} from τ.im_pos)
  simpa only [Function.comp_apply, Function.const_apply, ofComplex_apply] using this

/-- **Exponential decay of a twisted-periodic function** vanishing at $i\infty$: if $G$ is holomorphic, tends to $0$,
and $G(\tau + h) = \varepsilon G(\tau)$ with $|\varepsilon| = 1$, then $G = O(e^{-cy})$ for some $c > 0$. -/
theorem isBigO_exp_of_twisted_periodic {G : UpperHalfPlane → ℂ} (hG : MDiff G) (hz : IsZeroAtImInfty G)
    {h : ℝ} (hh : 0 < h) {ε : ℂ} (hε : ‖ε‖ = 1) (hper : ∀ τ : UpperHalfPlane, G (h +ᵥ τ) = ε * G τ) :
    ∃ c : ℝ, 0 < c ∧ G =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im) := by
  -- write ε = e^{2πiβ} with -1 < β ≤ 0
  set θ := Complex.arg (-ε) with hθ
  set β : ℝ := θ / (2 * π) - 1 / 2 with hβ
  have hθ1 : -π < θ := Complex.neg_pi_lt_arg _
  have hθ2 : θ ≤ π := Complex.arg_le_pi _
  have hβ1 : -1 < β := by
    rw [hβ, lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  have hβ2 : β ≤ 0 := by
    rw [hβ, sub_nonpos, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  have hεβ : cexp (2 * π * Complex.I * β) = ε := by
    have e1 := Complex.norm_mul_exp_arg_mul_I (-ε)
    rw [norm_neg, hε, Complex.ofReal_one, one_mul, ← hθ] at e1
    have : (2 * π * Complex.I * β : ℂ) = θ * Complex.I - π * Complex.I := by
      rw [hβ]; push_cast; field_simp
    rw [this, Complex.exp_sub, e1, Complex.exp_pi_mul_I]
    ring
  -- the periodic function H = e^{-2πiβτ/h} G
  set e : ℂ → ℂ := fun z ↦ cexp (-(2 * π * Complex.I * β) * z / h) with he
  have he_norm : ∀ τ : UpperHalfPlane, ‖e τ‖ = Real.exp (2 * π * β * τ.im / h) := by
    intro τ
    rw [he, Complex.norm_exp]
    congr 1
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    field_simp
  set H : UpperHalfPlane → ℂ := fun τ ↦ e τ * G τ with hH
  have hHd : MDiff H :=
    ((show Differentiable ℂ e by rw [he]; fun_prop).mdifferentiable.comp mdifferentiable_coe).mul hG
  have hHle : ∀ τ, ‖H τ‖ ≤ ‖G τ‖ := by
    intro τ
    rw [hH, norm_mul, he_norm]
    have : Real.exp (2 * π * β * τ.im / h) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hβ2) τ.im_pos.le)
        hh.le
    nlinarith [norm_nonneg (G τ)]
  have hHz : IsZeroAtImInfty H :=
    squeeze_zero_norm hHle (by simpa using hz.norm)
  have hHper : Function.Periodic (H ∘ ofComplex) h := by
    intro z
    rcases le_or_gt z.im 0 with hz0 | hz0
    · simp [ofComplex_apply_of_im_nonpos hz0,
        ofComplex_apply_of_im_nonpos (by simpa using hz0 : (z + h).im ≤ 0)]
    · have hz1 : 0 < (z + h).im := by simpa using hz0
      have hv : (⟨z + h, hz1⟩ : UpperHalfPlane) = (h : ℝ) +ᵥ (⟨z, hz0⟩ : UpperHalfPlane) := by
        ext; simp [add_comm]
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz0, ofComplex_apply_of_im_pos hz1]
      rw [hH]
      simp only
      rw [hv, hper]
      rw [he]
      rw [← hεβ, ← mul_assoc]
      congr 1
      rw [← Complex.exp_add]
      congr 1
      have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      field_simp
      ring
  have hdec := hHz.exp_decay_atImInfty hh hHper hHd hHz.isBoundedAtImInfty
  have hc : 0 < 2 * π * (1 + β) / h := by
    have := Real.pi_pos
    have : 0 < 1 + β := by linarith
    positivity
  refine ⟨2 * π * (1 + β) / h, hc, ?_⟩
  have hG' : G = fun τ : UpperHalfPlane ↦ cexp ((2 * π * Complex.I * β) * τ / h) * H τ := by
    funext τ
    rw [hH, he]
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    have : (2 * π * Complex.I * β) * (τ : ℂ) / h + -(2 * π * Complex.I * β) * τ / h = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
  have h1 : (fun τ : UpperHalfPlane ↦ cexp ((2 * π * Complex.I * β) * τ / h)) =O[atImInfty]
      fun τ ↦ Real.exp (-(2 * π * β) * τ.im / h) := by
    refine Asymptotics.isBigO_of_le _ fun τ ↦ ?_
    rw [Complex.norm_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq
    congr 1
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    field_simp
  rw [hG']
  refine (h1.mul hdec).trans (Asymptotics.isBigO_of_le _ fun τ ↦ ?_)
  rw [← Real.exp_add, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply le_of_eq
  congr 1
  field_simp
  ring

/-- $gT^{4N}g^{-1} \in \Gamma_0(4N)$. -/
lemma conj_T_mem (N : ℕ) (g : SL(2, ℤ)) :
    g * ModularGroup.T ^ ((4 * N : ℕ) : ℤ) * g⁻¹ ∈ Gamma0 (4 * N) := by
  rw [Gamma0_mem]
  have h10 : (g * ModularGroup.T ^ ((4 * N : ℕ) : ℤ) * g⁻¹) 1 0 = -(((4 * N : ℕ) : ℤ) * g 1 0 ^ 2) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T_zpow, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [h10, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨-(g 1 0 ^ 2), by push_cast; ring⟩

/-- $|\chi(d)| = 1$ for $\gamma \in \Gamma_0(4N)$. -/
lemma norm_chi_eq_one {N : ℕ} (χ : DirichletCharacter ℂ (4 * N)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (4 * N)) :
    ‖χ (γ 1 1 : ZMod (4 * N))‖ = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod (4 * N)) = 0 := by rwa [Gamma0_mem] at hγ
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have h1 : ((γ 0 0 : ℤ) : ZMod (4 * N)) * (γ 1 1 : ℤ) = 1 := by
    have := congrArg (fun x : ℤ ↦ (x : ZMod (4 * N))) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
    rw [hc] at this
    simpa using this
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (4 * N)) :=
    IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod (4 * N)) (by rw [← h1]; ring)
  simpa using DirichletCharacter.unit_norm_eq_one χ hu.unit

lemma denom_eq (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    denom g τ = (g 1 0 : ℂ) * τ + g 1 1 := by
  simp [ModularGroup.denom_apply]

/-- **$f^2$ is an eigenfunction of the weight $2k+1$ slash action of $\Gamma_0(4N)$** with an eigenvalue of absolute
value $1$: the factor $\chi(d)^2\,(j(\delta,\tau)^2/(c\tau+d))^{2k+1}$ is holomorphic of absolute value $1$, hence
constant. -/
lemma sq_slash_eq_smul (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} {f : UpperHalfPlane → ℂ}
    (hf : M.Transforms k N χ f) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (4 * N)) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ (f * f) ∣[((2 * k + 1 : ℕ) : ℤ)] δ = ε • (f * f) := by
  have hδ4 : δ ∈ Gamma0 4 := by
    rw [Gamma0_mem] at *
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at *
    exact dvd_trans (by push_cast; exact dvd_mul_right (4 : ℤ) N) hδ
  set u : UpperHalfPlane → ℂ := fun τ ↦ M.j δ τ ^ 2 / denom δ τ with hu
  have hud : MDiff u :=
    ((M.holo δ hδ4).pow 2).div ((contMDiff_denom (n := 1) _).mdifferentiable one_ne_zero)
      (fun τ ↦ denom_ne_zero _ τ)
  have hu1 : ∀ τ, ‖u τ‖ = 1 := by
    intro τ
    have hD : 0 < ‖denom δ τ‖ := norm_pos_iff.mpr (denom_ne_zero _ τ)
    rw [hu, norm_div, norm_pow, M.norm_sq δ hδ4 τ, ← denom_eq, div_self hD.ne']
  obtain ⟨c, hc, hcu⟩ := eq_const_of_norm_eq_one hud hu1
  refine ⟨χ (δ 1 1 : ZMod (4 * N)) ^ 2 * c ^ (2 * k + 1), ?_, ?_⟩
  · rw [norm_mul, norm_pow, norm_pow, norm_chi_eq_one χ hδ, hc, one_pow, one_pow, one_mul]
  · funext τ
    rw [ModularForm.SL_slash_apply, Pi.mul_apply, hf δ hδ τ, ← hcu τ, hu, zpow_neg, zpow_natCast]
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    have hD : denom δ τ ≠ 0 := denom_ne_zero _ τ
    rw [div_pow, ← pow_mul]
    field_simp
    ring

lemma norm_sq_slash (k : ℕ) (f : UpperHalfPlane → ℂ) (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    ‖((f * f) ∣[((2 * k + 1 : ℕ) : ℤ)] g) τ‖ = Abstract.cuspNorm k f g τ ^ 2 := by
  have hD : 0 < ‖denom g τ‖ := norm_pos_iff.mpr (denom_ne_zero _ τ)
  rw [ModularForm.SL_slash_apply, Pi.mul_apply, norm_mul, norm_mul, norm_zpow, Abstract.cuspNorm, ← denom_eq, mul_pow,
    ← Real.rpow_natCast (‖denom g τ‖ ^ _), ← Real.rpow_mul hD.le, ← Real.rpow_intCast]
  push_cast
  rw [sq]
  ring_nf

/-- **Exponential decay at every cusp:** for $f \in S_{k+1/2}(4N,\chi)$, $N \ge 1$, the square of the cusp quantity at
$g\infty$ is $O(e^{-cy})$ for some $c > 0$. -/
theorem cuspNorm_sq_isBigO_exp (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hN : 0 < N)
    {f : UpperHalfPlane → ℂ} (hf : f ∈ M.cuspForms k N χ) (g : SL(2, ℤ)) :
    ∃ c : ℝ, 0 < c ∧ (fun τ ↦ Abstract.cuspNorm k f g τ ^ 2) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im) := by
  have hf' : M.IsCuspForm k N χ f := hf
  set m : ℤ := ((4 * N : ℕ) : ℤ) with hm
  set δ := g * ModularGroup.T ^ m * g⁻¹ with hδ
  obtain ⟨ε, hε, hεF⟩ := sq_slash_eq_smul M hf'.transforms (conj_T_mem N g)
  set G := (f * f) ∣[((2 * k + 1 : ℕ) : ℤ)] g with hG
  have hGd : MDiff G := by
    rw [hG, ModularForm.SL_slash]
    exact (hf'.holo.mul hf'.holo).slash _ _
  have hGz : IsZeroAtImInfty G := by
    show Tendsto G atImInfty (𝓝 0)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [hG, norm_sq_slash]
    simpa using (hf'.zero_at_cusps g).pow 2
  have hper : ∀ τ : UpperHalfPlane, G ((m : ℝ) +ᵥ τ) = ε * G τ := by
    intro τ
    have h1 : G ((m : ℝ) +ᵥ τ) = (G ∣[((2 * k + 1 : ℕ) : ℤ)] (ModularGroup.T ^ m)) τ := by
      rw [ModularForm.SL_slash_apply, ← modular_T_zpow_smul]
      rw [denom_eq]
      simp [ModularGroup.coe_T_zpow]
    have h2 : g * ModularGroup.T ^ m = δ * g := by rw [hδ]; group
    rw [h1, hG, ← SlashAction.slash_mul, h2, SlashAction.slash_mul, hεF, ModularForm.SL_smul_slash]
    rfl
  have hm0 : (0 : ℝ) < m := by rw [hm]; push_cast; positivity
  obtain ⟨c, hc, hO⟩ := isBigO_exp_of_twisted_periodic hGd hGz hm0 hε hper
  refine ⟨c, hc, (Asymptotics.isBigO_of_le _ fun τ ↦ ?_).trans hO⟩
  rw [Real.norm_of_nonneg (sq_nonneg _), hG, norm_sq_slash]

/-- **Hecke's function is bounded** on $\mathbb H$ for $f \in S_{k+1/2}(4N,\chi)$, $N \ge 1$. -/
theorem phi_bounded (M : MultiplierSystem) {k N : ℕ} {χ : DirichletCharacter ℂ (4 * N)} (hN : 0 < N)
    {f : UpperHalfPlane → ℂ} (hf : f ∈ M.cuspForms k N χ) : ∃ C : ℝ, ∀ τ, phi k f τ ≤ C := by
  have hf' : M.IsCuspForm k N χ f := hf
  have : NeZero (4 * N) := ⟨by omega⟩
  have hex : 0 ≤ ex k := by unfold ex; positivity
  have hcont : Continuous (phi k f) := by
    unfold phi
    exact (UpperHalfPlane.continuous_im.rpow_const fun _ ↦ Or.inr hex).mul hf'.holo.continuous.norm
  have hinf : ∀ g : SL(2, ℤ), (fun τ ↦ phi k f (g • τ)) =O[atImInfty] fun z ↦ z.im ^ (0 : ℝ) := by
    intro g
    obtain ⟨c, hc, hO⟩ := cuspNorm_sq_isBigO_exp M hN hf g
    obtain ⟨C, hC⟩ := hO.bound
    have ht : Tendsto (fun τ : UpperHalfPlane ↦ τ.im ^ (2 * ex k) * Real.exp (-c * τ.im)) atImInfty (𝓝 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * ex k) c hc).comp tendsto_comap
    refine Asymptotics.IsBigO.of_bound (Real.sqrt |C|) ?_
    filter_upwards [hC, ht.eventually (ge_mem_nhds zero_lt_one)] with τ h1 h2
    rw [Real.rpow_zero, norm_one, mul_one, phi_smul_eq_cuspNorm]
    have hy := τ.im_pos
    have hn : 0 ≤ τ.im ^ ex k * Abstract.cuspNorm k f g τ :=
      mul_nonneg (by positivity) (mul_nonneg (by positivity) (norm_nonneg _))
    rw [Real.norm_of_nonneg hn]
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have e2 : (τ.im ^ ex k) ^ 2 = τ.im ^ (2 * ex k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; ring_nf
    have hp : 0 ≤ τ.im ^ (2 * ex k) := by positivity
    calc (τ.im ^ ex k * Abstract.cuspNorm k f g τ) ^ 2
        = τ.im ^ (2 * ex k) * Abstract.cuspNorm k f g τ ^ 2 := by rw [mul_pow, e2]
      _ ≤ τ.im ^ (2 * ex k) * (|C| * Real.exp (-c * τ.im)) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
            (Real.exp_pos _).le)) hp
      _ = |C| * (τ.im ^ (2 * ex k) * Real.exp (-c * τ.im)) := by ring
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ = |C| := mul_one _
  obtain ⟨C, hC⟩ := ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO hcont le_rfl hinf
    (Γ := Gamma0 (4 * N)) (fun g hg τ ↦ phi_smul M hf'.transforms hg τ)
  refine ⟨C, fun τ ↦ ?_⟩
  have := hC τ
  rw [Real.rpow_zero, mul_one] at this
  exact (le_abs_self _).trans this

end HeckeBound

open HeckeBound in
/-- **Hecke's bound in weight $k+\tfrac12$** (Iwaniec 1997 `iwaniec1997`, §5 [unverified]): for $N \ge 1$ the named input
`HeckeCoeffBound M k N χ` holds, over any multiplier system. -/
@[kb "iwaniec1997" "§5: Hecke's bound a(n) = O(n^{w/2}) for cusp forms of weight w = k + 1/2, proved for N ≥ 1 [unverified]"]
theorem heckeCoeffBound (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N) :
    HeckeCoeffBound M k N χ := by
  refine ⟨fun f hf a ha ↦ ?_⟩
  have hf' : M.IsCuspForm k N χ f := hf
  obtain ⟨C, hC⟩ := phi_bounded M hN hf
  have hB : ∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C * τ.im ^ (-ex k) := by
    intro τ
    have hy : 0 < τ.im ^ ex k := Real.rpow_pos_of_pos τ.im_pos _
    rw [Real.rpow_neg τ.im_pos.le, ← div_eq_mul_inv, le_div_iff₀ hy, mul_comm]
    exact hC τ
  exact ⟨Real.exp (2 * π) * C, fun n hn ↦ norm_coeff_le_of_norm_le hf'.holo ha hB hn⟩

/-- **Shimura's theorem from Weil's converse theorem and the twisted functional equations**: `shimuraTheorem_of_weil`
with Hecke's bound discharged by `heckeCoeffBound`. -/
@[kb "shimura1973" "Main Theorem, reduced to Weil's converse theorem and the twisted functional equations [unverified]"]
theorem shimuraTheorem_of_weil_fe (M : MultiplierSystem) (k N : ℕ) (χ : DirichletCharacter ℂ (4 * N)) (hN : 0 < N)
    (hW : WeilConverse) (hFE : ShimuraTwistedFE M k N χ) : ShimuraTheorem M k N χ :=
  shimuraTheorem_of_weil M k N χ hN hW (heckeCoeffBound M k N χ hN) hFE

end ModularFormsKB.HalfIntegral
