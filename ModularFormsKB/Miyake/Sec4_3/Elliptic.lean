import Mathlib

/-!
# Invariance under an elliptic element of infinite order forces vanishing

The last step of the proof of Miyake Lemma 4.3.14 (p. 127): if $h$ is holomorphic on $\mathbb H$ and
$h|_k\beta = h$ for an elliptic $\beta \in \mathrm{SL}_2(\mathbb R)$ whose eigenvalues are not roots of
unity, then $h = 0$ (for $k > 0$).

Miyake's argument: let $z_0 \in \mathbb H$ be the fixed point of $\beta$ and $\lambda = j(\beta, \bar z_0)$
(an eigenvalue, $|\lambda| = 1$). In the disc coordinate $w = (z - z_0)/(z - \bar z_0)$, the function
$Q(w) = h(z)\,(1 - w)^{-k}$ is holomorphic on the unit disc and satisfies
$Q(\lambda^2 w) = \lambda^{-k} Q(w)$, so its Taylor coefficients satisfy $q_n(\lambda^{2n+k} - 1) = 0$,
hence vanish.

The eigenvalues are not roots of unity when the trace is a rational number that is not an
integer: a root of unity $\lambda$ makes $\lambda + \lambda^{-1}$ an algebraic integer.
-/

open Complex Matrix
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold Topology
open Filter

noncomputable section

namespace Miyake

/-- A unit complex number with rational non-integer trace `L + L⁻¹` is not a root of unity. -/
lemma root_ne_one {L : ℂ} {t : ℚ} (hsum : L + L⁻¹ = (t : ℂ)) (htZ : ∀ n : ℤ, t ≠ n)
    (j : ℕ) (hj : 0 < j) : L ^ j ≠ 1 := by
  intro h1
  have hL1 : IsIntegral ℤ L := IsIntegral.of_pow hj (by rw [h1]; exact isIntegral_one)
  have hinv : L⁻¹ = L ^ (j - 1) := by
    have : L * L ^ (j - 1) = 1 := by rw [← pow_succ']; rw [Nat.sub_add_cancel hj]; exact h1
    exact inv_eq_of_mul_eq_one_right this
  have hL2 : IsIntegral ℤ L⁻¹ := by rw [hinv]; exact hL1.pow _
  have ht : IsIntegral ℤ (algebraMap ℚ ℂ t) := by
    rw [show algebraMap ℚ ℂ t = (t : ℂ) from rfl, ← hsum]; exact hL1.add hL2
  have ht' : IsIntegral ℤ t :=
    (isIntegral_algHom_iff (R := ℤ) ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective).1 ht
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 ht'
  exact htZ n (by simpa using hn.symm)

/-- Core analytic argument: invariance under a Möbius map with fixed points `z₀, z₁` of multiplier
`L` (not a root of unity) forces vanishing, via the disc coordinate `w = (z - z₀)/(z - z₁)`. -/
lemma core {k : ℕ} (hk : 0 < k) {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H {z | 0 < z.im})
    {a b c d z₀ z₁ L : ℂ} (hz₀ : 0 < z₀.im) (hz₁ : z₁.im < 0)
    (ha : a = c*(z₀+z₁)+d) (hb : b = -(c*z₀*z₁)) (hL1 : c*z₁+d = L) (hL0 : c*z₀+d = L⁻¹)
    (hL : L ≠ 0) (hroot : ∀ j : ℕ, 0 < j → L ^ j ≠ 1)
    (hden : ∀ z : ℂ, 0 < z.im → c*z+d ≠ 0)
    (him : ∀ z : ℂ, 0 < z.im → 0 < ((a*z+b)/(c*z+d)).im)
    (hfe : ∀ z : ℂ, 0 < z.im → H ((a*z+b)/(c*z+d)) = H z * (c*z+d)^k) :
    ∀ z : ℂ, 0 < z.im → H z = 0 := by
  have hz01 : z₀ - z₁ ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hzz1 : ∀ z : ℂ, 0 < z.im → z - z₁ ≠ 0 := by
    intro z hz h; have := congrArg Complex.im h; simp at this; linarith
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hHan : AnalyticOnNhd ℂ H {z | 0 < z.im} := hH.analyticOnNhd hopen
  set Cm : ℂ → ℂ := fun w => (z₀ - z₁*w)/(1-w) with hCm
  set W : ℂ → ℂ := fun z => (z-z₀)/(z-z₁) with hW
  have C_W : ∀ z, z - z₁ ≠ 0 → Cm (W z) = z := by
    intro z hz
    simp only [hCm, hW]
    have h1 : 1 - (z-z₀)/(z-z₁) = (z₀-z₁)/(z-z₁) := by field_simp; ring
    have h2 : z₀ - z₁*((z-z₀)/(z-z₁)) = (z₀-z₁)*z/(z-z₁) := by field_simp; ring
    rw [h1, h2]; field_simp
  have W_C : ∀ w, 1 - w ≠ 0 → W (Cm w) = w := by
    intro w hw
    have h1 : Cm w - z₁ = (z₀ - z₁)/(1-w) := by simp only [hCm]; field_simp; ring
    have h2 : Cm w - z₀ = (z₀ - z₁)*w/(1-w) := by simp only [hCm]; field_simp; ring
    simp only [hW]; rw [h1, h2]; field_simp
  have Cm0 : Cm 0 = z₀ := by simp [hCm]
  have hCmAn : AnalyticAt ℂ Cm 0 := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => z₀ - z₁ * w) 0 := by fun_prop
    have h2 : AnalyticAt ℂ (fun w : ℂ => 1 - w) 0 := by fun_prop
    have h3 : (1 : ℂ) - 0 ≠ 0 := by norm_num
    exact h1.div h2 h3
  set P : ℂ → ℂ := fun z => H z * ((z-z₁)/(z₀-z₁))^k with hP
  have hPan : AnalyticAt ℂ P z₀ := by
    simp only [hP]
    exact (hHan z₀ hz₀).mul (((analyticAt_id.sub analyticAt_const).div analyticAt_const
      hz01 |>.pow k))
  have hQan : AnalyticAt ℂ (P ∘ Cm) 0 := by
    rw [← Cm0] at hPan
    exact hPan.comp hCmAn
  set Q : ℂ → ℂ := P ∘ Cm with hQ
  have E0 : ∀ z, c*z+d ≠ 0 → (a*z+b)/(c*z+d) - z₀ = (z-z₀)*L/(c*z+d) := by
    intro z hz
    rw [← hL1, eq_div_iff hz, sub_mul, div_mul_cancel₀ _ hz]; subst ha hb; ring
  have E1 : ∀ z, c*z+d ≠ 0 → (a*z+b)/(c*z+d) - z₁ = (z-z₁)*L⁻¹/(c*z+d) := by
    intro z hz
    rw [← hL0]; subst ha hb; field_simp; ring
  have hrel : ∀ᶠ w in 𝓝 0, Q (L^2*w) * L^k = Q w := by
    have e1 : ∀ᶠ w : ℂ in 𝓝 0, 1 - w ≠ 0 :=
      (continuousAt_const.sub continuousAt_id).eventually_ne (by simp)
    have e2 : ∀ᶠ w : ℂ in 𝓝 0, 0 < (Cm w).im := by
      have : ContinuousAt Cm 0 := hCmAn.continuousAt
      exact this.eventually (hopen.mem_nhds (by rw [Cm0]; exact hz₀))
    filter_upwards [e1, e2] with w hw1 hw2
    have hdz := hden _ hw2
    have hz1 := hzz1 _ hw2
    have hWz : W (Cm w) = w := W_C w hw1
    set z := Cm w with hz
    have hdz' : z * c + d ≠ 0 := by rwa [mul_comm] at hdz
    set zp := (a*z+b)/(c*z+d) with hzp
    have hzp1 : zp - z₁ ≠ 0 := hzz1 _ (him z hw2)
    have hWzp : W zp = L^2 * w := by
      rw [← hWz]
      simp only [hW]
      rw [E0 z hdz, E1 z hdz]
      field_simp
    have hCzp : Cm (L^2*w) = zp := by rw [← hWzp]; exact C_W _ hzp1
    have hq : (zp - z₁)/(z₀-z₁) = (z-z₁)/(z₀-z₁) * (L⁻¹/(c*z+d)) := by
      rw [E1 z hdz]; field_simp
    simp only [hQ, Function.comp, hCzp, hP]
    rw [hq, hfe z hw2, ← hz]
    simp only [mul_pow, div_pow, inv_pow]
    field_simp
  have hQ0 : ∀ᶠ w in 𝓝 0, Q w = 0 := by
    by_contra hne
    obtain ⟨n, R, hRan, hR0, hQeq⟩ := (hQan.exists_eventuallyEq_pow_smul_ne_zero_iff).2 hne
    have hlin : Tendsto (fun w : ℂ => L^2*w) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun w : ℂ => L^2*w := by fun_prop
      simpa only [mul_zero] using hc.tendsto 0
    have hQeq2 := hlin.eventually hQeq
    have hev : ∀ᶠ w in 𝓝[≠] (0:ℂ), L^(2*n) * R (L^2*w) * L^k = R w := by
      filter_upwards [nhdsWithin_le_nhds hrel, nhdsWithin_le_nhds hQeq,
        nhdsWithin_le_nhds hQeq2, self_mem_nhdsWithin] with w h1 h2 h3 hw
      have hw' : w ≠ 0 := hw
      rw [h2, h3] at h1
      simp only [smul_eq_mul, sub_zero] at h1
      have : w^n * (L^(2*n) * R (L^2*w) * L^k - R w) = 0 := by
        rw [mul_pow] at h1
        rw [pow_mul]
        linear_combination h1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (pow_ne_zero _ hw')
      · exact sub_eq_zero.1 h
    have hc1 : ContinuousAt (fun w => L^(2*n) * R (L^2*w) * L^k) 0 := by
      have : ContinuousAt R (L^2*0) := by simpa using hRan.continuousAt
      exact ((continuousAt_const.mul (this.comp (f := fun w : ℂ => L^2*w) (x := 0)
        (continuous_const.mul continuous_id).continuousAt)).mul continuousAt_const)
    have hlim := tendsto_nhds_unique_of_eventuallyEq
      (hc1.tendsto.mono_left nhdsWithin_le_nhds) (hRan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev
    simp only [mul_zero] at hlim
    have : R 0 * (L^(2*n+k) - 1) = 0 := by rw [pow_add]; linear_combination hlim
    rcases mul_eq_zero.1 this with h | h
    · exact hR0 h
    · exact hroot (2*n+k) (by omega) (sub_eq_zero.1 h)
  have hev : ∀ᶠ z in 𝓝 z₀, H z = 0 := by
    have hWt : Tendsto W (𝓝 z₀) (𝓝 0) := by
      have h1 : ContinuousAt (fun z : ℂ => z - z₀) z₀ := by fun_prop
      have h2 : ContinuousAt (fun z : ℂ => z - z₁) z₀ := by fun_prop
      have : ContinuousAt W z₀ := h1.div h2 (hzz1 z₀ hz₀)
      have h0 : W z₀ = 0 := by rw [hW]; simp
      have := this.tendsto
      rwa [h0] at this
    filter_upwards [hWt.eventually hQ0, hopen.mem_nhds hz₀] with z hz hzim
    have hz' : 0 < z.im := hzim
    simp only [hQ, Function.comp, hP] at hz
    rw [C_W z (hzz1 z hz')] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ (div_ne_zero (hzz1 z hz') hz01))
  intro z hz
  have := hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected hz₀ hev hz
  simpa using this

/-- **Vanishing under an elliptic element of infinite order** (Miyake, proof of Lemma 4.3.14,
p. 127). Let $k > 0$, let $\beta \in \mathrm{GL}_2(\mathbb R)$ have determinant $1$ and trace a rational
number $t$ with $|t| < 2$ and $t \notin \mathbb Z$. If $h : \mathbb H \to \mathbb C$ is holomorphic and
$h|_k\beta = h$, then $h = 0$. -/
lemma eq_zero_of_slash_elliptic {k : ℤ} (hk : 0 < k) {h : ℍ → ℂ} (hh : MDiff h)
    {β : GL (Fin 2) ℝ} (hdet : (β : Matrix (Fin 2) (Fin 2) ℝ).det = 1) {t : ℚ}
    (htr : (β : Matrix (Fin 2) (Fin 2) ℝ).trace = t) (ht2 : |(t : ℝ)| < 2)
    (htZ : ∀ n : ℤ, t ≠ n) (hβ : h ∣[k] β = h) : h = 0 := by
  lift k to ℕ using hk.le
  have hk' : 0 < k := by exact_mod_cast hk
  have hdet' : (β 0 0 : ℝ) * β 1 1 - β 0 1 * β 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hdet
  have htr' : (β 0 0 : ℝ) + β 1 1 = t := by
    rw [← Matrix.trace_fin_two]; exact htr
  obtain ⟨a, ha⟩ : ∃ a, a = (β 0 0 : ℝ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (β 0 1 : ℝ) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (β 1 0 : ℝ) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = (β 1 1 : ℝ) := ⟨_, rfl⟩
  simp only [← ha, ← hb, ← hc, ← hd] at hdet' htr'
  have ht4 : (t : ℝ)^2 < 4 := by
    have := abs_lt.1 ht2; nlinarith
  have hc0 : c ≠ 0 := by
    intro h0
    subst h0
    rw [← htr'] at ht4
    nlinarith [sq_nonneg (a - d)]
  have hcabs : 0 < |c| := abs_pos.2 hc0
  obtain ⟨s, hs0, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s^2 = 4 - (t:ℝ)^2 :=
    ⟨Real.sqrt (4 - (t:ℝ)^2), Real.sqrt_pos.2 (by linarith), Real.sq_sqrt (by linarith)⟩
  set u : ℝ := (a - d) / (2 * c) with hu
  set v : ℝ := s / (2 * |c|) with hv
  have hv0 : 0 < v := by positivity
  set m : ℝ := c * v with hm
  have hm2 : m^2 = 1 - (t:ℝ)^2/4 := by
    have : |c|^2 = c^2 := sq_abs c
    simp only [hm, hv]
    field_simp
    nlinarith
  set z₀ : ℂ := ⟨u, v⟩ with hz₀
  set z₁ : ℂ := ⟨u, -v⟩ with hz₁
  set L : ℂ := ⟨t/2, -m⟩ with hL
  have hLinv : L⁻¹ = ⟨t/2, m⟩ := by
    refine inv_eq_of_mul_eq_one_right ?_
    apply Complex.ext <;> simp [hL] <;> nlinarith
  have hL1 : (c:ℂ) * z₁ + d = L := by
    apply Complex.ext <;> simp [hz₁, hL, hu, hm] <;> field_simp <;> nlinarith
  have hL0 : (c:ℂ) * z₀ + d = L⁻¹ := by
    rw [hLinv]
    apply Complex.ext <;> simp [hz₀, hu, hm] <;> field_simp <;> nlinarith
  have hLne : L ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp [hL] at h1 h2
    rw [h2] at hm2; rw [h1] at hm2; norm_num at hm2
  have hLsum : L + L⁻¹ = (t:ℂ) := by
    rw [hLinv]; apply Complex.ext <;> simp [hL]
  have hroot := fun j hj => root_ne_one hLsum htZ j hj
  have ha' : (a:ℂ) = c*(z₀+z₁)+d := by
    apply Complex.ext <;> simp [hz₀, hz₁, hu] <;> field_simp <;> linarith
  have hb' : (b:ℂ) = -(c*z₀*z₁) := by
    have hcc : |c|^2 = c^2 := sq_abs c
    apply Complex.ext <;> simp [hz₀, hz₁, hu, hv]
    · field_simp
      rw [hcc, hs2, ← htr']
      linear_combination (-4*c^2) * hdet'
    · ring
  have hdetpos : 0 < (β.det : ℝˣ).val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]; exact one_pos
  subst ha hb hc hd
  have hden : ∀ z : ℂ, 0 < z.im → (β 1 0 : ℂ)*z + β 1 1 ≠ 0 := fun z hz =>
    denom_ne_zero β ⟨z, hz⟩
  have him : ∀ z : ℂ, 0 < z.im → 0 < (((β 0 0 : ℝ) * z + (β 0 1 : ℝ))/((β 1 0 : ℝ)*z + (β 1 1 : ℝ))).im := by
    intro z hz
    have h2 := (β • (⟨z, hz⟩ : ℍ)).2
    rw [coe_smul_of_det_pos hdetpos] at h2
    exact h2
  have hfe : ∀ z : ℂ, 0 < z.im → h (ofComplex (((β 0 0 : ℝ) * z + (β 0 1 : ℝ))/((β 1 0 : ℝ)*z + (β 1 1 : ℝ)))) = h (ofComplex z) * ((β 1 0 : ℝ)*z + (β 1 1 : ℝ))^k := by
    intro z hz
    have h1 := congrFun hβ ⟨z, hz⟩
    rw [ModularForm.slash_apply] at h1
    have hd1 : |(β.det : ℝˣ).val| = 1 := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]; simp
    have hdp : 0 < (β : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; exact one_pos
    have hd2 : |(β : Matrix (Fin 2) (Fin 2) ℝ).det| = 1 := by rw [hdet]; simp
    simp [UpperHalfPlane.σ, hdp, hd2, _root_.zpow_neg] at h1
    have e : (ofComplex (((β 0 0 : ℝ) * z + (β 0 1 : ℝ))/((β 1 0 : ℝ)*z + (β 1 1 : ℝ))) : ℍ)
        = β • (⟨z, hz⟩ : ℍ) := by
      have := ofComplex_apply (β • (⟨z, hz⟩ : ℍ))
      rw [coe_smul_of_det_pos hdetpos] at this
      exact this
    rw [e, ofComplex_apply_of_im_pos hz]
    have hD := hden z hz
    have hD' : denom β z ^ k ≠ 0 := pow_ne_zero _ hD
    show _ = _ * (denom β z)^k
    rw [← h1]; field_simp
  have key := core hk' (H := fun z => h (ofComplex z)) (UpperHalfPlane.mdifferentiable_iff.1 hh)
    (by simpa [hz₀] using hv0) (by simpa [hz₁] using hv0) ha' hb' hL1 hL0 hLne hroot hden him hfe
  funext τ
  simpa using key τ τ.2

end Miyake
