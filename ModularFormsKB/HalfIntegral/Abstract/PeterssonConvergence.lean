/-
# Convergence of the Petersson product for half-integral weight cusp forms

For cusp forms $f, g \in S_{k+1/2}(4N, \chi)$ relative to an abstract multiplier system `M` ($N \ge 1$) and
any $\gamma \in \mathrm{SL}_2(\mathbb Z)$, the integrand $\overline{f(\gamma\tau)}\,g(\gamma\tau)\operatorname{Im}(\gamma\tau)^{k+1/2}$ of
`peterssonReps` is integrable on the fundamental domain `ModularGroup.fd` (`integrableOn_peterssonIntegrand`). Hence the
Petersson product `peterssonFour` converges absolutely on $S_{k+1/2}(4N,\chi)$ and is additive in each argument
(`peterssonFour_add_left`, `peterssonFour_add_right`).

**Proof.** $|\text{integrand}| = |c\tau+d|^{-w}|f(\gamma\tau)|\cdot|c\tau+d|^{-w}|g(\gamma\tau)|\cdot\operatorname{Im}(\tau)^{w}$ with
$w = k + \tfrac12$ (`norm_peterssonIntegrand`); both cusp quantities decay exponentially (`cuspNorm_sq_isBigO_exp`), so the
integrand tends to $0$ at $i\infty$, is bounded on $\mathcal F$ (Mathlib's `exists_bound_fundamental_domain_of_isBigO`), and
$\mathcal F$ has finite volume (`volume_fd_lt_top`).
-/
import ModularFormsKB.HalfIntegral.Abstract.PeterssonFour
import ModularFormsKB.HalfIntegral.Abstract.CuspDecay
import ModularFormsKB.HalfIntegral.Abstract.FundamentalDomainVolume
import Mathlib.NumberTheory.ModularForms.Bounds

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane Filter Asymptotics MeasureTheory
open scoped Real
open scoped Manifold

/-- $\operatorname{Im}(\gamma\tau)^w = |c\tau+d|^{-w}\,|c\tau+d|^{-w}\operatorname{Im}(\tau)^w$. -/
theorem im_smul_rpow (γ : SL(2, ℤ)) (w : ℝ) (τ : ℍ) :
    (γ • τ).im ^ w =
      ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-w) * ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-w) * τ.im ^ w := by
  have hx : 0 < ‖(γ 1 0 : ℂ) * τ + γ 1 1‖ := by
    rw [← denom_SL_eq]; exact norm_pos_iff.2 (denom_ne_zero _ τ)
  rw [ModularGroup.im_smul_eq_div_normSq, normSq_eq_norm_sq, denom_SL_eq,
    Real.div_rpow τ.im_pos.le (sq_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
    ← Real.rpow_add hx, div_eq_mul_inv, ← Real.rpow_neg hx.le, mul_comm]
  congr 2
  push_cast
  ring

/-- $|\overline{f(\gamma\tau)}\,g(\gamma\tau)\operatorname{Im}(\gamma\tau)^{k+1/2}|$ is the product of the two cusp quantities
and $\operatorname{Im}(\tau)^{k+1/2}$. -/
theorem norm_peterssonIntegrand (k : ℕ) (γ : SL(2, ℤ)) (f g : ℍ → ℂ) (τ : ℍ) :
    ‖peterssonIntegrand γ ((k : ℝ) + 1 / 2) f g τ‖ =
      Abstract.cuspNorm k f γ τ * Abstract.cuspNorm k g γ τ * τ.im ^ ((k : ℝ) + 1 / 2) := by
  rw [peterssonIntegrand, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (γ • τ).im_pos.le _), im_smul_rpow, Abstract.cuspNorm,
    Abstract.cuspNorm]
  ring

theorem continuous_peterssonIntegrand (γ : SL(2, ℤ)) (w : ℝ) {f g : ℍ → ℂ} (hf : Continuous f)
    (hg : Continuous g) : Continuous (peterssonIntegrand γ w f g) := by
  have hγ : Continuous (fun τ : ℍ ↦ γ • τ) := continuous_const_smul (γ : GL (Fin 2) ℝ)
  have him : Continuous (fun τ : ℍ ↦ (γ • τ).im ^ w) :=
    (UpperHalfPlane.continuous_im.comp hγ).rpow_const fun τ ↦ Or.inl (γ • τ).im_pos.ne'
  unfold peterssonIntegrand
  exact ((continuous_conj.comp (hf.comp hγ)).mul (hg.comp hγ)).mul (continuous_ofReal.comp him)

/-- $|c\tau+d|^{-2w}|f(\gamma\tau)|^2\operatorname{Im}(\tau)^w \to 0$ at $i\infty$ for a cusp form $f$. -/
theorem MultiplierSystem.tendsto_cuspNorm_sq_mul (M : MultiplierSystem) (k N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ (4 * N)) {f : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) (γ : SL(2, ℤ)) (w : ℝ) :
    Tendsto (fun τ : ℍ ↦ Abstract.cuspNorm k f γ τ ^ 2 * τ.im ^ w) atImInfty (nhds 0) := by
  obtain ⟨a, ha, hdec⟩ := M.cuspNorm_sq_isBigO_exp k N hN χ hf γ
  have h1 := hdec.mul (isBigO_refl (fun τ : ℍ ↦ τ.im ^ w) atImInfty)
  refine h1.trans_tendsto ?_
  have h2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero w a ha).comp
    (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop)
  refine h2.congr fun τ ↦ ?_
  simp [mul_comm]

/-- **Integrability on the fundamental domain:** for cusp forms $f, g \in S_{k+1/2}(4N,\chi)$, $N \ge 1$, every term of
`peterssonReps` converges absolutely. -/
theorem MultiplierSystem.integrableOn_peterssonIntegrand (M : MultiplierSystem) (k N : ℕ) (hN : 0 < N)
    (χ : DirichletCharacter ℂ (4 * N)) {f g : ℍ → ℂ} (hf : f ∈ M.cuspForms k N χ) (hg : g ∈ M.cuspForms k N χ)
    (γ : SL(2, ℤ)) : IntegrableOn (peterssonIntegrand γ ((k : ℝ) + 1 / 2) f g) ModularGroup.fd := by
  set w : ℝ := (k : ℝ) + 1 / 2
  have hcont := continuous_peterssonIntegrand γ w hf.holo.continuous hg.holo.continuous
  -- The integrand tends to zero at `i∞`.
  have hle : ∀ τ : ℍ, ‖peterssonIntegrand γ w f g τ‖ ≤
      (Abstract.cuspNorm k f γ τ ^ 2 * τ.im ^ w + Abstract.cuspNorm k g γ τ ^ 2 * τ.im ^ w) / 2 := by
    intro τ
    rw [norm_peterssonIntegrand]
    have hy : 0 ≤ τ.im ^ w := Real.rpow_nonneg τ.im_pos.le _
    nlinarith [sq_nonneg (Abstract.cuspNorm k f γ τ - Abstract.cuspNorm k g γ τ), mul_nonneg hy
      (sq_nonneg (Abstract.cuspNorm k f γ τ - Abstract.cuspNorm k g γ τ))]
  have hlim : Tendsto (fun τ : ℍ ↦
      (Abstract.cuspNorm k f γ τ ^ 2 * τ.im ^ w + Abstract.cuspNorm k g γ τ ^ 2 * τ.im ^ w) / 2)
      atImInfty (nhds 0) := by
    simpa using ((M.tendsto_cuspNorm_sq_mul k N hN χ hf γ w).add
      (M.tendsto_cuspNorm_sq_mul k N hN χ hg γ w)).div_const 2
  have hzero : Tendsto (peterssonIntegrand γ w f g) atImInfty (nhds 0) :=
    squeeze_zero_norm hle hlim
  have hO : peterssonIntegrand γ w f g =O[atImInfty] fun τ : ℍ ↦ τ.im ^ (0 : ℝ) := by
    simpa using hzero.isBigO_one ℝ
  obtain ⟨C, hC⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hcont hO
  refine Measure.integrableOn_of_bounded (M := C) volume_fd_lt_top.ne hcont.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_fd).2 (Eventually.of_forall fun τ hτ ↦ ?_)
  simpa using hC τ hτ

end ModularFormsKB.HalfIntegral
