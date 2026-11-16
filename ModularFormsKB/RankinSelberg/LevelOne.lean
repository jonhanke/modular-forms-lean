/-
# The Rankin–Selberg L-function at level one: continuation, pole, functional equation

The first half of headline **H2**. For
$f, g \in S_k(\mathrm{SL}_2(\mathbb Z))$ with $f = \sum a_nq^n$, $g = \sum b_nq^n$:
$$L(f\times\bar g, s) = \zeta(2s)\sum_{n\ge1}a_n\bar b_n\,n^{-(s+k-1)}\qquad(\text{`rankinSelbergL`}).$$
The Rankin integral against the completed Eisenstein series $E^*(z,s)$ of `EisensteinZero.lean`,
$$\Lambda(s) = \int_{\mathcal F}y^k\,\bar g f\,E^*(\cdot,s)\,d\mu\qquad(\text{`rankinSelbergCompleted`}),$$
satisfies (`rankinSelberg_levelOne`):
- $\Lambda(1-s) = \Lambda(s)$ for every $s$;
- $\Lambda(s) = R(s) - \frac{P}{s} + \frac{P}{s-1}$ with $R$ entire and $P = \int_{\mathcal F}y^k\bar gf\,d\mu$ (Tau Ceti's
  `CuspForm.peterssonInnerFd g f`; Tau Ceti conjugates the first slot);
- $\Lambda(s) = 2(4\pi)^{-(s+k-1)}\pi^{-s}\Gamma(s)\Gamma(s+k-1)L(f\times\bar g,s)$ for $\operatorname{Re}s > 2$.

Hence $L(f\times\bar g,s)$ continues to a function `rankinSelbergLc` holomorphic on $\mathbb C\setminus\{1\}$, with
$$\lim_{s\to1}(s-1)L(f\times\bar g,s) = \frac{\pi}{2}\,\frac{(4\pi)^k}{\Gamma(k)}\,\langle g, f\rangle,$$
and the completed function satisfies $\Lambda(s) = 2(4\pi)^{-(s+k-1)}\pi^{-s}\Gamma(s)\Gamma(s+k-1)L(f\times\bar g,s)$ on
$\operatorname{Re}s > 0$, $s \ne 1$, so $L(f\times\bar g, \cdot)$ is determined on the left by $\Lambda(1-s) = \Lambda(s)$
(Rankin 1939 `rankin1939`, Selberg 1940 `selberg1940` [unverified]).
-/
import ModularFormsKB.RankinSelberg.Unfolding
import ModularFormsKB.RankinSelberg.EisensteinBounds
import ModularFormsKB.HalfIntegral.Abstract.FundamentalDomainVolume
import TauCeti.NumberTheory.ModularForms.Petersson.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville

open MeasureTheory Set Filter Topology Complex Asymptotics MatrixGroups
open scoped UpperHalfPlane Real ComplexConjugate

noncomputable section

namespace ModularFormsKB.RankinSelberg

open ModularFormsKB.HalfIntegral ModularFormsKB.Miyake.HeckeTrick UpperHalfPlane

/-! ### Holomorphic parametric integrals, with continuity on an open neighbourhood -/

/-- `HalfIntegral.differentiable_setIntegral_of_strip_bound` with continuity in $\tau$ only on an open set $U \supseteq S$. -/
theorem differentiable_setIntegral_of_bound_on {S U : Set ℍ} (hS : MeasurableSet S) (hU : IsOpen U)
    (hSU : S ⊆ U) (hμ : (volume : Measure ℍ) S < ⊤) {h : ℍ → ℂ → ℂ} (hd : ∀ τ, Differentiable ℂ (h τ))
    (hc : ∀ s, ContinuousOn (fun τ ↦ h τ s) U)
    (hb : ∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ τ ∈ S, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖h τ s‖ ≤ C) :
    Differentiable ℂ (fun s ↦ ∫ τ in S, h τ s) := by
  intro s₀
  have : IsFiniteMeasure ((volume : Measure ℍ).restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμ⟩
  obtain ⟨C, hC⟩ := hb (s₀.re - 1) (s₀.re + 1)
  have hmono : (volume : Measure ℍ).restrict S ≤ (volume : Measure ℍ).restrict U :=
    Measure.restrict_mono hSU le_rfl
  have hmeas : ∀ s, AEStronglyMeasurable (fun τ ↦ h τ s) ((volume : Measure ℍ).restrict S) :=
    fun s ↦ ((hc s).aestronglyMeasurable hU.measurableSet).mono_measure hmono
  have hbd : ∀ᵐ τ ∂((volume : Measure ℍ).restrict S), ∀ s ∈ Metric.ball s₀ (1/2 : ℝ),
      ‖deriv (h τ) s‖ ≤ C / (1/2 : ℝ) := by
    refine ae_restrict_of_forall_mem hS fun τ hτ s hs ↦ ?_
    apply norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
    · exact (hd τ).diffContOnCl
    · intro z hz
      have h1 : ‖z - s‖ = 1/2 := by simpa [Complex.dist_eq] using hz
      have h2 : ‖s - s₀‖ < 1/2 := by simpa [Complex.dist_eq] using hs
      have h3 : |(z - s₀).re| ≤ ‖z - s₀‖ := Complex.abs_re_le_norm _
      have h4 : ‖z - s₀‖ ≤ ‖z - s‖ + ‖s - s₀‖ := by
        simpa using norm_add_le (z - s) (s - s₀)
      have h5 := abs_le.mp h3
      simp only [Complex.sub_re] at h5
      exact hC τ hτ z (by linarith [h5.1]) (by linarith [h5.2])
  have hderiv : AEStronglyMeasurable (fun τ ↦ deriv (h τ) s₀) ((volume : Measure ℍ).restrict S) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun (n : ℕ) τ ↦ ((n + 1 : ℂ))⁻¹⁻¹ • (h τ (s₀ + ((n + 1 : ℂ))⁻¹) - h τ s₀)) ?_ ?_
    · intro n
      exact ((((hc (s₀ + ((n + 1 : ℂ))⁻¹)).sub (hc s₀)).const_smul
        (((n + 1 : ℂ))⁻¹⁻¹)).aestronglyMeasurable hU.measurableSet).mono_measure hmono
    · refine Filter.Eventually.of_forall fun τ ↦ ?_
      have h0 : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℂ))⁻¹) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n ↦ ?_⟩
        · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
          simpa using this
        · simp only [mem_compl_iff, mem_singleton_iff, inv_eq_zero]
          exact_mod_cast Nat.succ_ne_zero n
      exact ((hd τ s₀).hasDerivAt.tendsto_slope_zero).comp h0
  have hbound := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℍ).restrict S)
    (F := fun s τ ↦ h τ s) (F' := fun s τ ↦ deriv (h τ) s) (x₀ := s₀) (bound := fun _ ↦ C / (1/2 : ℝ))
    (Metric.ball_mem_nhds s₀ (by norm_num : (0:ℝ) < 1/2)) (Filter.Eventually.of_forall hmeas)
    (Integrable.of_bound (hmeas s₀) (C := C) (ae_restrict_of_forall_mem hS fun τ hτ ↦
      hC τ hτ s₀ (by linarith) (by linarith))) hderiv hbd (integrable_const _)
    (Filter.Eventually.of_forall fun τ s _ ↦ (hd τ s).hasDerivAt)
  exact hbound.2.differentiableAt

/-! ### The kernel on the fundamental domain -/

theorem half_le_im_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) : 1 / 2 < τ.im := by
  have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
  have hy := τ.im_pos
  by_contra hlt
  push_neg at hlt
  nlinarith

theorem fd_subset_half : ModularGroup.fd ⊆ {τ : ℍ | 1 / 2 < τ.im} := fun _ hτ ↦ half_le_im_of_mem_fd hτ

theorem isOpen_half : IsOpen {τ : ℍ | 1 / 2 < τ.im} := isOpen_lt continuous_const UpperHalfPlane.continuous_im

/-- **The kernel decays on the fundamental domain:** $|y^k\bar gf|\,y^A$ is bounded on $\mathcal F$. -/
theorem petersson_mul_rpow_bound_fd {k : ℤ} (f g : CuspForm 𝒮ℒ k) (A : ℝ) :
    ∃ C : ℝ, ∀ τ ∈ ModularGroup.fd, ‖petersson k g f τ‖ * τ.im ^ A ≤ C := by
  obtain ⟨a, ha, hO⟩ := (CuspFormClass.zero_at_infty g).petersson_exp_decay_left k 𝒮ℒ f
  set h : ℍ → ℝ := fun τ ↦ ‖petersson k g f τ‖ * τ.im ^ A with hh
  have hcont : Continuous h :=
    (continuous_petersson f g).norm.mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ ↦ Or.inl τ.im_pos.ne')
  have hdecay : Tendsto (fun τ : ℍ ↦ τ.im ^ A * Real.exp (-a * τ.im)) atImInfty (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A a ha).comp tendsto_comap
  have hO' : h =O[atImInfty] fun τ : ℍ ↦ τ.im ^ (0 : ℝ) := by
    have h1 : h =O[atImInfty] fun τ : ℍ ↦ Real.exp (-a * τ.im) * τ.im ^ A :=
      hO.norm_left.mul (isBigO_refl _ _)
    have h2 : (fun τ : ℍ ↦ Real.exp (-a * τ.im) * τ.im ^ A) =O[atImInfty] fun _ ↦ (1 : ℝ) := by
      refine (hdecay.isBigO_one ℝ).congr_left fun τ ↦ ?_
      ring
    simpa using h1.trans h2
  obtain ⟨F, hF⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hcont hO'
  refine ⟨F, fun τ hτ ↦ ?_⟩
  have := hF τ hτ
  rw [Real.rpow_zero, mul_one, Real.norm_of_nonneg (by positivity)] at this
  exact this

theorem petersson_bound_fd {k : ℤ} (f g : CuspForm 𝒮ℒ k) :
    ∃ C : ℝ, ∀ τ ∈ ModularGroup.fd, ‖petersson k g f τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := petersson_mul_rpow_bound_fd f g 0
  exact ⟨C, fun τ hτ ↦ by simpa using hC τ hτ⟩

theorem integrableOn_petersson_fd {k : ℤ} (f g : CuspForm 𝒮ℒ k) :
    IntegrableOn (petersson k g f) ModularGroup.fd := by
  have : IsFiniteMeasure ((volume : Measure ℍ).restrict ModularGroup.fd) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_fd_lt_top⟩
  obtain ⟨C, hC⟩ := petersson_bound_fd f g
  exact Integrable.of_bound (continuous_petersson f g).aestronglyMeasurable (C := C)
    (ae_restrict_of_forall_mem measurableSet_fd hC)

/-- The integrand $y^k\bar gf\,E^*_0(\cdot,s)$ is bounded on $\mathcal F \times$ every vertical strip. -/
theorem petersson_mul_eisensteinReg_bound {k : ℤ} (f g : CuspForm 𝒮ℒ k) (σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, ∀ τ ∈ ModularGroup.fd, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖petersson k g f τ * eisensteinReg τ s‖ ≤ C := by
  obtain ⟨A, B, hAB⟩ := norm_eisensteinReg_le σ₁ σ₂
  obtain ⟨C, hC⟩ := petersson_mul_rpow_bound_fd f g A
  refine ⟨|B| * C, fun τ hτ s h1 h2 ↦ ?_⟩
  have hy := half_le_im_of_mem_fd hτ
  have hE := hAB τ hy.le s h1 h2
  rw [norm_mul]
  have hp : 0 ≤ τ.im ^ A := Real.rpow_nonneg τ.im_pos.le _
  calc ‖petersson k g f τ‖ * ‖eisensteinReg τ s‖ ≤ ‖petersson k g f τ‖ * (|B| * τ.im ^ A) :=
        mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_right (le_abs_self B) hp))
          (norm_nonneg _)
    _ = |B| * (‖petersson k g f τ‖ * τ.im ^ A) := by ring
    _ ≤ |B| * C := mul_le_mul_of_nonneg_left (hC τ hτ) (abs_nonneg _)

theorem continuousOn_petersson_mul_eisensteinReg {k : ℤ} (f g : CuspForm 𝒮ℒ k) (s : ℂ) :
    ContinuousOn (fun τ ↦ petersson k g f τ * eisensteinReg τ s) {τ : ℍ | 1 / 2 < τ.im} :=
  (continuous_petersson f g).continuousOn.mul (continuousOn_eisensteinReg s)

theorem integrableOn_petersson_mul_eisensteinReg {k : ℤ} (f g : CuspForm 𝒮ℒ k) (s : ℂ) :
    IntegrableOn (fun τ ↦ petersson k g f τ * eisensteinReg τ s) ModularGroup.fd := by
  have : IsFiniteMeasure ((volume : Measure ℍ).restrict ModularGroup.fd) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_fd_lt_top⟩
  obtain ⟨C, hC⟩ := petersson_mul_eisensteinReg_bound f g s.re s.re
  refine Integrable.of_bound (((continuousOn_petersson_mul_eisensteinReg f g s).aestronglyMeasurable
    isOpen_half.measurableSet).mono_measure (Measure.restrict_mono fd_subset_half le_rfl)) (C := C)
    (ae_restrict_of_forall_mem measurableSet_fd fun τ hτ ↦ hC τ hτ s le_rfl le_rfl)

/-! ### The Rankin integral -/

/-- **The completed Rankin–Selberg function** $\Lambda(s) = \int_{\mathcal F}y^k\bar gf\,E^*(\cdot,s)\,d\mu$. -/
def rankinSelbergCompleted (k : ℤ) (f g : CuspForm 𝒮ℒ k) (s : ℂ) : ℂ :=
  ∫ τ in ModularGroup.fd, petersson k g f τ * eisensteinStar τ s

/-- Its entire part $R(s) = \int_{\mathcal F}y^k\bar gf\,E^*_0(\cdot,s)\,d\mu$. -/
def rankinSelbergReg (k : ℤ) (f g : CuspForm 𝒮ℒ k) (s : ℂ) : ℂ :=
  ∫ τ in ModularGroup.fd, petersson k g f τ * eisensteinReg τ s

/-- **The Rankin–Selberg $L$-function** $L(f\times\bar g,s) = \zeta(2s)\sum_n a_n\bar b_n n^{-(s+k-1)}$ (a Dirichlet series,
absolutely convergent for $\operatorname{Re}s > 2$). -/
def rankinSelbergL (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) (s : ℂ) : ℂ :=
  riemannZeta (2 * s) * LSeries (rsCoeff f g) (s + k - 1)

theorem differentiable_rankinSelbergReg {k : ℤ} (f g : CuspForm 𝒮ℒ k) :
    Differentiable ℂ (rankinSelbergReg k f g) :=
  differentiable_setIntegral_of_bound_on measurableSet_fd isOpen_half fd_subset_half volume_fd_lt_top
    (fun τ ↦ (differentiable_eisensteinReg τ).const_mul _)
    (continuousOn_petersson_mul_eisensteinReg f g) (petersson_mul_eisensteinReg_bound f g)

/-- **The polar parts:** $\Lambda(s) = R(s) - P/s + P/(s-1)$, $P = \langle g, f\rangle$. -/
theorem rankinSelbergCompleted_eq_reg {k : ℤ} (f g : CuspForm 𝒮ℒ k) (s : ℂ) :
    rankinSelbergCompleted k f g s = rankinSelbergReg k f g s -
      CuspForm.peterssonInnerFd g f / s + CuspForm.peterssonInnerFd g f / (s - 1) := by
  have hP : CuspForm.peterssonInnerFd g f = ∫ τ in ModularGroup.fd, petersson k g f τ := rfl
  have e : ∀ τ, petersson k g f τ * eisensteinStar τ s =
      petersson k g f τ * eisensteinReg τ s - (1 / s + 1 / (1 - s)) * petersson k g f τ := by
    intro τ; rw [eisensteinStar_eq_reg]; ring
  unfold rankinSelbergCompleted rankinSelbergReg
  simp_rw [e]
  rw [integral_sub (integrableOn_petersson_mul_eisensteinReg f g s)
    ((integrableOn_petersson_fd f g).const_mul _), integral_const_mul, ← hP]
  have : 1 / (1 - s) = -(1 / (s - 1)) := by
    rw [show 1 - s = -(s - 1) by ring, one_div_neg_eq_neg_one_div]
  rw [this]
  ring

/-- **The functional equation** $\Lambda(1-s) = \Lambda(s)$. -/
theorem rankinSelbergCompleted_one_sub {k : ℤ} (f g : CuspForm 𝒮ℒ k) (s : ℂ) :
    rankinSelbergCompleted k f g (1 - s) = rankinSelbergCompleted k f g s := by
  unfold rankinSelbergCompleted
  simp_rw [eisensteinStar_one_sub]

/-- **The Dirichlet series in the half plane** $\operatorname{Re}s > 2$:
$\Lambda(s) = 2\pi^{-s}\Gamma(s)\Gamma(s+k-1)(4\pi)^{-(s+k-1)}L(f\times\bar g,s)$. -/
theorem rankinSelbergCompleted_eq_L (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) {s : ℂ} (hs : 2 < s.re) :
    rankinSelbergCompleted k f g s = 2 * (π : ℂ) ^ (-s) * (4 * π : ℂ) ^ (-(s + k - 1)) *
      Gamma s * Gamma (s + k - 1) * rankinSelbergL k f g s := by
  have hs1 : 1 < s.re := by linarith
  have e : ∀ τ, petersson k g f τ * eisensteinStar τ s =
      (π : ℂ) ^ (-s) * Gamma s * (petersson k g f τ * eisensteinLattice 1 0 1 τ s) := by
    intro τ; rw [eisensteinStar_eq_lattice τ hs1]; ring
  unfold rankinSelbergCompleted
  simp_rw [e]
  rw [integral_const_mul, rankin_unfold_levelOne k f g hs, rankinSelbergL]
  ring

/-! ### The continuation of $L(f\times\bar g, s)$ -/

/-- The factor $c(s) = \pi^s(4\pi)^{s+k-1}/2$, inverse to the gamma factor without the gamma functions. -/
def rsFactor (k : ℕ) (s : ℂ) : ℂ := (π : ℂ) ^ s * (4 * π : ℂ) ^ (s + k - 1) / 2

/-- **The entire function** $(s-1)L(f\times\bar g,s)$:
$\big[(s-1)R(s)\Gamma(s)^{-1} - P(s-1)\Gamma(s+1)^{-1} + P\Gamma(s)^{-1}\big]\Gamma(s+k-1)^{-1}c(s)$. -/
def rankinSelbergEntire (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) (s : ℂ) : ℂ :=
  ((s - 1) * rankinSelbergReg k f g s * (Gamma s)⁻¹ -
      CuspForm.peterssonInnerFd g f * (s - 1) * (Gamma (s + 1))⁻¹ + CuspForm.peterssonInnerFd g f * (Gamma s)⁻¹) *
    (Gamma (s + k - 1))⁻¹ * rsFactor k s

/-- **The continued Rankin–Selberg $L$-function** $L(f\times\bar g,s)$, holomorphic on $\mathbb C\setminus\{1\}$. -/
def rankinSelbergLc (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) (s : ℂ) : ℂ :=
  rankinSelbergEntire k f g s / (s - 1)

theorem differentiable_rsFactor (k : ℕ) : Differentiable ℂ (rsFactor k) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h4π : (4 * π : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  unfold rsFactor
  exact ((differentiable_id.const_cpow (Or.inl hπ)).mul
    (((differentiable_id.add_const _).sub_const _).const_cpow (Or.inl h4π))).div_const _

theorem differentiable_rankinSelbergEntire (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) :
    Differentiable ℂ (rankinSelbergEntire k f g) := by
  have hG : Differentiable ℂ fun s : ℂ ↦ (Gamma s)⁻¹ := differentiable_one_div_Gamma
  have hG1 : Differentiable ℂ fun s : ℂ ↦ (Gamma (s + 1))⁻¹ := hG.comp (differentiable_id.add_const 1)
  have hGk : Differentiable ℂ fun s : ℂ ↦ (Gamma (s + k - 1))⁻¹ :=
    hG.comp ((differentiable_id.add_const _).sub_const _)
  have hR := differentiable_rankinSelbergReg f g
  have hs1 : Differentiable ℂ fun s : ℂ ↦ s - 1 := differentiable_id.sub_const 1
  have hA : Differentiable ℂ fun s : ℂ ↦ (s - 1) * rankinSelbergReg k f g s * (Gamma s)⁻¹ :=
    (hs1.mul hR).mul hG
  have hB : Differentiable ℂ fun s : ℂ ↦ CuspForm.peterssonInnerFd g f * (s - 1) * (Gamma (s + 1))⁻¹ :=
    ((differentiable_const _).mul hs1).mul hG1
  have hC : Differentiable ℂ fun s : ℂ ↦ CuspForm.peterssonInnerFd g f * (Gamma s)⁻¹ :=
    (differentiable_const _).mul hG
  unfold rankinSelbergEntire
  exact ((hA.sub hB).add hC).mul hGk |>.mul (differentiable_rsFactor k)

/-- Off $s = 0, 1$: $(s-1)L(f\times\bar g,s) = (s-1)\Lambda(s)\Gamma(s)^{-1}\Gamma(s+k-1)^{-1}c(s)$. -/
theorem rankinSelbergEntire_eq (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rankinSelbergEntire k f g s = (s - 1) * rankinSelbergCompleted k f g s * (Gamma s)⁻¹ *
      (Gamma (s + k - 1))⁻¹ * rsFactor k s := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  rw [rankinSelbergEntire, rankinSelbergCompleted_eq_reg, Complex.Gamma_add_one s hs0, mul_inv]
  field_simp

theorem rankinSelbergLc_eq (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    rankinSelbergLc k f g s = rankinSelbergCompleted k f g s * (Gamma s)⁻¹ *
      (Gamma (s + k - 1))⁻¹ * rsFactor k s := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  rw [rankinSelbergLc, rankinSelbergEntire_eq k f g hs0 hs1]
  field_simp

theorem cpow_ne_zero_of_base {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero hx]; exact Complex.exp_ne_zero _

theorem rsFactor_mul (k : ℕ) (s : ℂ) :
    2 * (π : ℂ) ^ (-s) * (4 * π : ℂ) ^ (-(s + k - 1)) * rsFactor k s = 1 := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h4π : (4 * π : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  unfold rsFactor
  rw [Complex.cpow_neg, Complex.cpow_neg]
  have h1 : (π : ℂ) ^ s ≠ 0 := cpow_ne_zero_of_base hπ s
  have h2 : (4 * π : ℂ) ^ (s + k - 1) ≠ 0 := cpow_ne_zero_of_base h4π _
  field_simp

/-- **The completed function in terms of the continued $L$-function**, for $\operatorname{Re}s > 0$, $s \ne 1$. -/
theorem rankinSelbergCompleted_eq_Lc (k : ℕ) (hk : 1 ≤ k) (f g : CuspForm 𝒮ℒ (k : ℤ)) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    rankinSelbergCompleted k f g s = 2 * (π : ℂ) ^ (-s) * (4 * π : ℂ) ^ (-(s + k - 1)) *
      Gamma s * Gamma (s + k - 1) * rankinSelbergLc k f g s := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hG1 : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hG2 : Gamma (s + k - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith)
  rw [rankinSelbergLc_eq k f g hs0 hs1]
  have h := rsFactor_mul k s
  have e : 2 * (π : ℂ) ^ (-s) * (4 * π : ℂ) ^ (-(s + k - 1)) * Gamma s * Gamma (s + k - 1) *
      (rankinSelbergCompleted k f g s * (Gamma s)⁻¹ * (Gamma (s + k - 1))⁻¹ * rsFactor k s) =
      rankinSelbergCompleted k f g s * (2 * (π : ℂ) ^ (-s) * (4 * π : ℂ) ^ (-(s + k - 1)) * rsFactor k s) *
        (Gamma s * (Gamma s)⁻¹) * (Gamma (s + k - 1) * (Gamma (s + k - 1))⁻¹) := by ring
  rw [e, h, mul_inv_cancel₀ hG1, mul_inv_cancel₀ hG2]
  ring

/-- **The continuation agrees with the Dirichlet series** for $\operatorname{Re}s > 2$. -/
theorem rankinSelbergLc_eq_L (k : ℕ) (hk : 1 ≤ k) (f g : CuspForm 𝒮ℒ (k : ℤ)) {s : ℂ} (hs : 2 < s.re) :
    rankinSelbergLc k f g s = rankinSelbergL k f g s := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := fun h ↦ by rw [h] at hs; norm_num at hs
  have hG1 : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hG2 : Gamma (s + k - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith)
  have h1 := rankinSelbergCompleted_eq_L k f g hs
  have h2 := rankinSelbergCompleted_eq_Lc k hk f g hs0 hs1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have h4π : (4 * π : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hπ
  have hc : 2 * (π : ℂ) ^ (-s) * (4 * π : ℂ) ^ (-(s + k - 1)) * Gamma s * Gamma (s + k - 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) hG1) hG2
    · exact cpow_ne_zero_of_base hπ _
    · exact cpow_ne_zero_of_base h4π _
  exact mul_left_cancel₀ hc (h2.symm.trans h1)

/-- **The residue at $s = 1$:** $(s-1)L(f\times\bar g,s) \to \frac\pi2\frac{(4\pi)^k}{\Gamma(k)}\langle g,f\rangle$. -/
theorem tendsto_rankinSelbergLc_residue (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) :
    Tendsto (fun s ↦ (s - 1) * rankinSelbergLc k f g s) (𝓝[≠] 1)
      (𝓝 ((π : ℂ) / 2 * (4 * π : ℂ) ^ k / Gamma k * CuspForm.peterssonInnerFd g f)) := by
  have hE := (differentiable_rankinSelbergEntire k f g).continuous.continuousAt (x := 1)
  have h1 : rankinSelbergEntire k f g 1 =
      (π : ℂ) / 2 * (4 * π : ℂ) ^ k / Gamma k * CuspForm.peterssonInnerFd g f := by
    rw [rankinSelbergEntire, rsFactor]
    simp only [sub_self, zero_mul, mul_zero, Complex.Gamma_one, inv_one, mul_one,
      Complex.cpow_one]
    rw [show (1 : ℂ) + k - 1 = k by ring, Complex.cpow_natCast]
    ring
  rw [← h1]
  refine (hE.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [rankinSelbergLc]
  field_simp

theorem differentiableOn_rankinSelbergLc (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) :
    DifferentiableOn ℂ (rankinSelbergLc k f g) {1}ᶜ := by
  intro s hs
  have hs' : s - 1 ≠ 0 := sub_ne_zero.2 hs
  exact ((differentiable_rankinSelbergEntire k f g s).div
    ((differentiable_id.sub_const 1) s) hs').differentiableWithinAt

/-- **Rankin–Selberg at level one** (Rankin 1939 `rankin1939`, Selberg 1940 `selberg1940` [unverified]; headline H2,
first half). For $f, g \in S_k(\mathrm{SL}_2(\mathbb Z))$, $k \ge 1$:
1. $L(f\times\bar g,s) = \zeta(2s)\sum_n a_n\bar b_nn^{-(s+k-1)}$ continues to `rankinSelbergLc`, holomorphic on
   $\mathbb C\setminus\{1\}$;
2. $(s-1)L(f\times\bar g,s) \to \frac\pi2\frac{(4\pi)^k}{\Gamma(k)}\langle g,f\rangle$ as $s \to 1$ (at most a simple pole,
   residue a constant times the Petersson product);
3. the completed function $\Lambda$ satisfies $\Lambda(1-s) = \Lambda(s)$, and
   $\Lambda(s) = 2\pi^{-s}(4\pi)^{-(s+k-1)}\Gamma(s)\Gamma(s+k-1)L(f\times\bar g,s)$ for $\operatorname{Re}s > 0$, $s \ne 1$;
4. $\Lambda(s) - P/(s-1) + P/s$ is entire, $P = \langle g,f\rangle$. -/
@[kb "rankin1939" "Rankin-Selberg at level one: continuation, simple pole with residue a multiple of the Petersson product, functional equation [unverified]"]
theorem rankinSelberg_levelOne (k : ℕ) (hk : 1 ≤ k) (f g : CuspForm 𝒮ℒ (k : ℤ)) :
    (∀ s, 2 < s.re → rankinSelbergLc k f g s = rankinSelbergL k f g s) ∧
    DifferentiableOn ℂ (rankinSelbergLc k f g) {1}ᶜ ∧
    Tendsto (fun s ↦ (s - 1) * rankinSelbergLc k f g s) (𝓝[≠] 1)
      (𝓝 ((π : ℂ) / 2 * (4 * π : ℂ) ^ k / Gamma k * CuspForm.peterssonInnerFd g f)) ∧
    (∀ s, rankinSelbergCompleted k f g (1 - s) = rankinSelbergCompleted k f g s) ∧
    (∀ s, 0 < s.re → s ≠ 1 → rankinSelbergCompleted k f g s = 2 * (π : ℂ) ^ (-s) *
      (4 * π : ℂ) ^ (-(s + k - 1)) * Gamma s * Gamma (s + k - 1) * rankinSelbergLc k f g s) ∧
    Differentiable ℂ (fun s ↦ rankinSelbergCompleted k f g s - CuspForm.peterssonInnerFd g f / (s - 1) +
      CuspForm.peterssonInnerFd g f / s) := by
  refine ⟨fun s hs ↦ rankinSelbergLc_eq_L k hk f g hs, differentiableOn_rankinSelbergLc k f g,
    tendsto_rankinSelbergLc_residue k f g, rankinSelbergCompleted_one_sub f g,
    fun s hs hs1 ↦ rankinSelbergCompleted_eq_Lc k hk f g hs hs1, ?_⟩
  have e : (fun s ↦ rankinSelbergCompleted k f g s - CuspForm.peterssonInnerFd g f / (s - 1) +
      CuspForm.peterssonInnerFd g f / s) = rankinSelbergReg k f g := by
    funext s
    rw [rankinSelbergCompleted_eq_reg]
    ring
  rw [e]
  exact differentiable_rankinSelbergReg f g

end ModularFormsKB.RankinSelberg
