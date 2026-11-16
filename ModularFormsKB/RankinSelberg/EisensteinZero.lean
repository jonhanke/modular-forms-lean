/-
# The real-analytic Eisenstein series of weight 0 at level one

For $z = x + iy \in \mathbb H$ put
$$\theta_z(t) = \sum_{(c,d)\in\mathbb Z^2} e^{-\pi t|cz+d|^2/y} = \Theta(z, t/y),$$
the theta function of the binary form $|cz+d|^2/y$ of determinant one (`thetaZ`; $\Theta$ is the lattice theta series
`Miyake.HeckeTrick.latticeTheta 1 0 1` of level one, weight zero). The inversion formula of the lattice theta series
(`Miyake.HeckeTrick.Inversion.latticeThetaInversion`, proved) at $L = 1$, $\lambda = 0$ says that $\theta_z$ is self-dual,
$\theta_z(1/t) = t\,\theta_z(t)$ (`thetaZ_inv`). So $(\theta_z, \theta_z)$ is a Mathlib `WeakFEPair` with $k = 1$,
$\varepsilon = 1$ and constant terms $f_0 = g_0 = 1$ (`eisPair`), and its completed Mellin transform $\Lambda$ is the
completed Eisenstein series
$$E^*(z,s) = \pi^{-s}\Gamma(s)\sum_{(c,d)\ne(0,0)}\frac{y^s}{|cz+d|^{2s}} \qquad(\operatorname{Re}s > 1)$$
(`eisensteinStar`, `eisensteinStar_eq_lattice`). Mathlib's theory of FE-pairs then gives:
- $E^*(z, 1-s) = E^*(z, s)$ (`eisensteinStar_one_sub`);
- $E^*(z,s) = E^*_0(z,s) - \frac1s - \frac1{1-s}$ with $E^*_0(z,\cdot)$ entire (`eisensteinStar_eq_reg`,
  `differentiable_eisensteinReg`);
- the residue of $E^*(z,\cdot)$ at $s = 1$ is $1$ (`tendsto_eisensteinStar_residue`).

With $E(z,s) = \frac12\sum_{\gcd(c,d)=1}y^s|cz+d|^{-2s}$ one has $E^*(z,s) = 2\xi(2s)E(z,s)$, $\xi(s) =
\pi^{-s/2}\Gamma(s/2)\zeta(s)$, so these are Miyake's Theorem 7.2.17 at $N = 1$ and the residue $3/\pi$ of $E(z,s)$
(Miyake 1989 `miyake1989`, §7.2 [unverified]).

**Normalization.** Row vectors $(c, d)$ are 0-based pairs `p = (p.1, p.2)`, $v = p_1z + p_2$ (`genVec 1 z p`).
-/
import ModularFormsKB.Miyake.HeckeTrick.LatticeInversion

open MeasureTheory Set Filter Topology Complex Asymptotics
open scoped UpperHalfPlane Real

noncomputable section

namespace ModularFormsKB.RankinSelberg

open ModularFormsKB.HalfIntegral ModularFormsKB.Miyake.HeckeTrick

/-! ### Theta series whose coefficient vanishes at the zero vector -/

section ZeroTerm

variable {a lam : ℕ} {c : ℤ × ℤ → ℂ} {C : ℝ}

/-- **Exponential decay from a base point.** If $c(0) = 0$, then for $0 < u_1 \le u$,
$|\Theta_c(z,u)| \le e^{-\pi(u-u_1)\min(1,y^2)}\sum_p|c(p)v_p^\lambda e^{-\pi u_1|v_p|^2}|$. -/
theorem norm_genTheta_le_shift (ha : 1 ≤ a) (hc0 : c 0 = 0) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ)
    {u₁ u : ℝ} (hu₁ : 0 < u₁) (hu : u₁ ≤ u) :
    ‖genTheta a lam c z u‖ ≤ Real.exp (-π * (u - u₁) * min 1 (z.im ^ 2)) *
      ∑' p : ℤ × ℤ, ‖c p * genVec a z p ^ lam *
        ((Real.exp (-π * u₁ * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ := by
  have hu0 : 0 < u := lt_of_lt_of_le hu₁ hu
  set m := min 1 (z.im ^ 2) with hm
  have hterm : ∀ p : ℤ × ℤ, ‖c p * genVec a z p ^ lam *
        ((Real.exp (-π * u * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ ≤
      Real.exp (-π * (u - u₁) * m) * ‖c p * genVec a z p ^ lam *
        ((Real.exp (-π * u₁ * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖ := fun p ↦ by
    rw [term_norm, term_norm]
    by_cases hp : p = 0
    · subst hp
      simp [hc0]
    · have hmn := min_le_normSq ha z hp
      have h1 : Real.exp (-π * u * ‖genVec a z p‖ ^ 2) ≤
          Real.exp (-π * (u - u₁) * m) * Real.exp (-π * u₁ * ‖genVec a z p‖ ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hmn (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hu))]
      have h2 : 0 ≤ ‖c p‖ * ‖genVec a z p‖ ^ lam := by positivity
      calc ‖c p‖ * ‖genVec a z p‖ ^ lam * Real.exp (-π * u * ‖genVec a z p‖ ^ 2)
          ≤ ‖c p‖ * ‖genVec a z p‖ ^ lam * (Real.exp (-π * (u - u₁) * m) *
              Real.exp (-π * u₁ * ‖genVec a z p‖ ^ 2)) := mul_le_mul_of_nonneg_left h1 h2
        _ = _ := by ring
  have h1 := Summable.tsum_le_tsum hterm (summable_norm_term (lam := lam) (c := c) ha hc z hu0)
    ((summable_norm_term (lam := lam) (c := c) ha hc z hu₁).mul_left _)
  rw [tsum_mul_left] at h1
  exact (norm_genTheta_le_tsum ha hc z hu0).trans h1

/-- **Rapid decay at infinity** of a theta series with $c(0) = 0$, in every weight $\lambda \ge 0$. -/
theorem genTheta_isBigO_atTop_of_zero (ha : 1 ≤ a) (hc0 : c 0 = 0) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ)
    (r : ℝ) : (genTheta a lam c z) =O[atTop] (· ^ r) := by
  set S := ∑' p : ℤ × ℤ, ‖c p * genVec a z p ^ lam *
    ((Real.exp (-π * 1 * ‖genVec a z p‖ ^ 2) : ℝ) : ℂ)‖
  have hy := z.im_pos
  set κ : ℝ := π * min 1 (z.im ^ 2) with hκ
  have hκ0 : 0 < κ := by positivity
  have h1 : (genTheta a lam c z) =O[atTop] fun u : ℝ ↦ Real.exp (-κ * u) := by
    refine Asymptotics.IsBigO.of_bound (Real.exp κ * S) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    refine (norm_genTheta_le_shift ha hc0 hc z one_pos hu).trans (le_of_eq ?_)
    have e : Real.exp (-π * (u - 1) * min 1 (z.im ^ 2)) = Real.exp κ * Real.exp (-κ * u) := by
      rw [← Real.exp_add]; congr 1; simp only [hκ]; ring
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, e]
    ring
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop hκ0 r).isBigO

theorem Fterm_zero_of_zero (hc0 : c 0 = 0) (z : ℍ) (σ : ℂ) (t : ℝ) : Fterm a lam c z σ 0 t = 0 := by
  simp [Fterm, hc0]

theorem integrable_Fterm_of_zero (ha : 1 ≤ a) (hc0 : c 0 = 0) (z : ℍ) {σ : ℂ} (hσ : 0 < σ.re)
    (p : ℤ × ℤ) : Integrable (Fterm a lam c z σ p) (volume.restrict (Ioi (0 : ℝ))) := by
  by_cases hp : p = 0
  · subst hp
    have : Fterm a lam c z σ 0 = fun _ => 0 := funext (Fterm_zero_of_zero hc0 z σ)
    rw [this]; exact integrable_zero _ _ _
  · have hv := genVec_norm_pos ha z hp
    have hg : Integrable (fun t : ℝ ↦ ‖c p‖ * ‖genVec a z p‖ ^ lam *
        (t ^ (σ.re - 1) * Real.exp (-(π * ‖genVec a z p‖ ^ 2 * t))))
        (volume.restrict (Ioi (0 : ℝ))) := by
      refine Integrable.const_mul ?_ _
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ.re - 1)
        (b := π * ‖genVec a z p‖ ^ 2) (by linarith) one_pos (by positivity)
      refine this.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
      simp only [Real.rpow_one, neg_mul]
    refine hg.mono' ?_ ?_
    · unfold Fterm
      exact ((Complex.measurable_ofReal.pow_const (σ - 1)).mul (measurable_const.mul
        (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
          ((measurable_const.mul measurable_id).mul measurable_const))))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_)
      rw [norm_Fterm z p ht]

theorem integral_norm_Fterm_of_zero (ha : 1 ≤ a) (hc0 : c 0 = 0) (z : ℍ) {σ : ℂ} (hσ : 0 < σ.re)
    (p : ℤ × ℤ) :
    ∫ t in Ioi (0 : ℝ), ‖Fterm a lam c z σ p t‖ =
      Real.Gamma σ.re * π ^ (-σ.re) *
        ‖c p * genVec a z p ^ lam * ((‖genVec a z p‖ : ℝ) : ℂ) ^ (-2 * σ)‖ := by
  by_cases hp : p = 0
  · subst hp
    simp [Fterm_zero_of_zero hc0, hc0]
  · have hv := genVec_norm_pos ha z hp
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ norm_Fterm z p ht), integral_const_mul,
      real_integral_aux hv hσ, norm_mul, norm_mul, norm_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos hv]
    simp only [mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.neg_re, neg_mul, zero_mul,
      sub_zero]
    ring

theorem integral_Fterm_of_zero (ha : 1 ≤ a) (hc0 : c 0 = 0) (z : ℍ) {σ : ℂ} (hσ : 0 < σ.re)
    (p : ℤ × ℤ) :
    ∫ t in Ioi (0 : ℝ), Fterm a lam c z σ p t =
      Gamma σ * (π : ℂ) ^ (-σ) *
        (c p * genVec a z p ^ lam * ((‖genVec a z p‖ : ℝ) : ℂ) ^ (-2 * σ)) := by
  by_cases hp : p = 0
  · subst hp
    simp [Fterm_zero_of_zero hc0, hc0]
  · have hv := genVec_norm_pos ha z hp
    have e : ∀ t : ℝ, Fterm a lam c z σ p t = (c p * genVec a z p ^ lam) *
        ((t : ℂ) ^ (σ - 1) *
          Complex.exp (-(((π * ‖genVec a z p‖ ^ 2 : ℝ) : ℂ) * (t : ℂ)))) := fun t ↦ by
      unfold Fterm
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    simp_rw [e]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hσ (by positivity),
      cpow_aux hv]
    ring

/-- **The Mellin transform of a theta series with $c(0) = 0$**, in every weight $\lambda \ge 0$:
$\int_0^\infty\Theta_c(z,u)u^{\sigma-1}du = \Gamma(\sigma)\pi^{-\sigma}S_c(z,\sigma)$ for
$\operatorname{Re}\sigma > 1 + \lambda/2$ (`mellin_genTheta` with the hypothesis $\lambda \ge 1$ replaced by $c(0) = 0$). -/
theorem mellin_genTheta_of_zero (ha : 1 ≤ a) (hc0 : c 0 = 0) (hc : ∀ p, ‖c p‖ ≤ C) (z : ℍ) {σ : ℂ}
    (hσ : 1 + (lam : ℝ) / 2 < σ.re) :
    mellin (genTheta a lam c z) σ = Gamma σ * (π : ℂ) ^ (-σ) * genSeries a lam c z σ := by
  have hσ0 : 0 < σ.re := by
    have : (0 : ℝ) ≤ lam / 2 := by positivity
    linarith
  have hS := summable_genSeries (lam := lam) (c := c) ha hc z hσ
  have h1 : ∀ t : ℝ, (t : ℂ) ^ (σ - 1) • genTheta a lam c z t =
      ∑' p, Fterm a lam c z σ p t := fun t ↦ by
    unfold genTheta Fterm
    rw [smul_eq_mul, ← tsum_mul_left]
  have hsum : Summable fun p : ℤ × ℤ ↦ ∫ t in Ioi (0 : ℝ), ‖Fterm a lam c z σ p t‖ := by
    simp_rw [integral_norm_Fterm_of_zero ha hc0 z hσ0]
    exact hS.mul_left _
  rw [mellin]
  simp_rw [h1]
  rw [← integral_tsum_of_summable_integral_norm
    (fun p ↦ integrable_Fterm_of_zero ha hc0 z hσ0 p) hsum]
  simp_rw [integral_Fterm_of_zero ha hc0 z hσ0]
  rw [tsum_mul_left]
  rfl

end ZeroTerm

/-! ### The self-dual theta function of level one -/

/-- The coefficient $1$ off the zero vector and $0$ at it. -/
def cOff : ℤ × ℤ → ℂ := fun p ↦ if p = 0 then 0 else 1

theorem cOff_zero : cOff 0 = 0 := by simp [cOff]

theorem norm_cOff_le (p : ℤ × ℤ) : ‖cOff p‖ ≤ 1 := by
  unfold cOff; split_ifs <;> simp

theorem norm_one_le (_p : ℤ × ℤ) : ‖(1 : ℂ)‖ ≤ 1 := by simp

/-- **The theta function** $\theta_z(t) = \sum_{(c,d)\in\mathbb Z^2}e^{-\pi t|cz+d|^2/y}$. -/
def thetaZ (z : ℍ) (t : ℝ) : ℂ := genTheta 1 0 (fun _ ↦ 1) z (t / z.im)

theorem trivialChar_apply (x : ZMod 1) : (1 : DirichletCharacter ℂ 1) x = 1 := by
  haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
  rw [Subsingleton.elim x 1, map_one]

theorem latticeTheta_one_eq (z : ℍ) (u : ℝ) :
    latticeTheta 1 0 1 z u = genTheta 1 0 (fun _ ↦ 1) z u := by
  rw [latticeTheta_eq_genTheta]
  congr 1
  funext p
  exact trivialChar_apply _

theorem gaussAt_one (m : ℤ) : gaussAt 1 1 m = 1 := by
  simp [gaussAt, trivialChar_apply]

theorem dualTheta_one_eq (z : ℍ) (u : ℝ) :
    dualTheta 1 0 1 z u = genTheta 1 0 (fun _ ↦ 1) z u := by
  rw [dualTheta_eq_genTheta]
  congr 1
  funext p
  exact gaussAt_one _

/-- **Splitting off the zero vector:** $\Theta(z,u) = 1 + \sum_{p\ne0}e^{-\pi u|v_p|^2}$. -/
theorem genTheta_one_eq (z : ℍ) {u : ℝ} (hu : 0 < u) :
    genTheta 1 0 (fun _ ↦ 1) z u = 1 + genTheta 1 0 cOff z u := by
  unfold genTheta
  have hs : Summable fun p : ℤ × ℤ ↦ (1 : ℂ) * genVec 1 z p ^ 0 *
      ((Real.exp (-π * u * ‖genVec 1 z p‖ ^ 2) : ℝ) : ℂ) :=
    (summable_norm_term (lam := 0) (c := fun _ ↦ (1 : ℂ)) le_rfl norm_one_le z hu).of_norm
  rw [hs.tsum_eq_add_tsum_ite 0]
  have h0 : genVec 1 z 0 = 0 := by simp [genVec]
  congr 1
  · simp [h0]
  · refine tsum_congr fun p ↦ ?_
    unfold cOff
    split_ifs <;> simp

/-- **Self-duality** $\theta_z(1/x) = x\,\theta_z(x)$, from the lattice theta inversion at level one, weight zero. -/
theorem thetaZ_inv (z : ℍ) {x : ℝ} (hx : 0 < x) : thetaZ z (1 / x) = x * thetaZ z x := by
  have hy := z.im_pos
  unfold thetaZ
  rw [← latticeTheta_one_eq,
    Inversion.latticeThetaInversion.inv 1 0 1 le_rfl z (1 / x / z.im) (by positivity),
    dualTheta_one_eq]
  have e1 : 1 / ((1 : ℕ) ^ 2 * z.im ^ 2 * (1 / x / z.im) : ℝ) = x / z.im := by
    simp only [Nat.cast_one, one_pow, one_mul]
    field_simp
  have e2 : (((((1 : ℕ) : ℝ) ^ 2 * z.im)⁻¹ * (((1 : ℕ) : ℝ) * z.im)⁻¹ ^ 0 *
      ((1 / x / z.im) ^ (0 + 1))⁻¹ : ℝ) : ℂ) = (x : ℂ) := by
    congr 1
    simp only [Nat.cast_one, one_pow, one_mul, pow_zero, mul_one, zero_add, pow_one]
    field_simp
  rw [e1, e2]

theorem continuousOn_thetaZ (z : ℍ) : ContinuousOn (thetaZ z) (Ioi 0) := by
  have hy := z.im_pos
  refine (continuousOn_genTheta (lam := 0) le_rfl norm_one_le z).comp
    (continuous_id.div_const _).continuousOn fun t ht ↦ ?_
  exact div_pos ht hy

theorem thetaZ_sub_one (z : ℍ) {t : ℝ} (ht : 0 < t) :
    thetaZ z t - 1 = genTheta 1 0 cOff z (t / z.im) := by
  unfold thetaZ
  rw [genTheta_one_eq z (div_pos ht z.im_pos)]
  ring

theorem thetaZ_sub_one_isBigO (z : ℍ) (r : ℝ) :
    (fun t ↦ thetaZ z t - 1) =O[atTop] (· ^ r) := by
  have hy := z.im_pos
  have e : (fun t ↦ thetaZ z t - 1) =ᶠ[atTop]
      (genTheta 1 0 cOff z) ∘ (fun t ↦ t / z.im) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact thetaZ_sub_one z ht
  exact (((genTheta_isBigO_atTop_of_zero le_rfl cOff_zero norm_cOff_le z r).comp_tendsto
    (tendsto_id.atTop_div_const hy)).trans (isBigO_div_const_rpow hy r)).congr' e.symm
    (EventuallyEq.refl _ _)

/-- **The FE-pair** $(\theta_z, \theta_z)$: weight $k = 1$, root number $\varepsilon = 1$, constant terms $1$. -/
def eisPair (z : ℍ) : WeakFEPair ℂ where
  f := thetaZ z
  g := thetaZ z
  k := 1
  ε := 1
  f₀ := 1
  g₀ := 1
  hf_int := (continuousOn_thetaZ z).locallyIntegrableOn measurableSet_Ioi
  hg_int := (continuousOn_thetaZ z).locallyIntegrableOn measurableSet_Ioi
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun x hx ↦ by
    rw [thetaZ_inv z hx]
    simp
  hf_top := thetaZ_sub_one_isBigO z
  hg_top := thetaZ_sub_one_isBigO z

theorem eisPair_symm (z : ℍ) : (eisPair z).symm = eisPair z := by
  unfold WeakFEPair.symm eisPair
  congr 1
  exact inv_one

/-! ### The completed Eisenstein series -/

/-- **The completed real-analytic Eisenstein series of weight 0 and level one**, $E^*(z,s)$: the $\Lambda$ of the
FE-pair `eisPair z`; for $\operatorname{Re}s > 1$ it is $\pi^{-s}\Gamma(s)\sum_{(c,d)\ne0}y^s|cz+d|^{-2s}$
(`eisensteinStar_eq_lattice`). -/
def eisensteinStar (z : ℍ) (s : ℂ) : ℂ := (eisPair z).Λ s

/-- The entire part $E^*_0(z,s) = E^*(z,s) + \frac1s + \frac1{1-s}$. -/
def eisensteinReg (z : ℍ) (s : ℂ) : ℂ := (eisPair z).Λ₀ s

theorem differentiable_eisensteinReg (z : ℍ) : Differentiable ℂ (eisensteinReg z) :=
  (eisPair z).differentiable_Λ₀

/-- $E^*(z,s) = E^*_0(z,s) - \frac1s - \frac1{1-s}$. -/
theorem eisensteinStar_eq_reg (z : ℍ) (s : ℂ) :
    eisensteinStar z s = eisensteinReg z s - 1 / s - 1 / (1 - s) := by
  simp [eisensteinStar, eisensteinReg, WeakFEPair.Λ, eisPair]

/-- **The functional equation** $E^*(z,1-s) = E^*(z,s)$ (Miyake 1989 `miyake1989`, Theorem 7.2.17 at $N = 1$
[unverified]). -/
@[kb "miyake1989" "Theorem 7.2.17 at N = 1: functional equation of the completed weight-0 Eisenstein series [unverified]"]
theorem eisensteinStar_one_sub (z : ℍ) (s : ℂ) : eisensteinStar z (1 - s) = eisensteinStar z s := by
  have h := (eisPair z).functional_equation s
  rw [eisPair_symm] at h
  simpa [eisensteinStar, eisPair] using h

/-- The entire part is symmetric too: $E^*_0(z, 1-s) = E^*_0(z, s)$. -/
theorem eisensteinReg_one_sub (z : ℍ) (s : ℂ) : eisensteinReg z (1 - s) = eisensteinReg z s := by
  have h := (eisPair z).functional_equation₀ s
  rw [eisPair_symm] at h
  simpa [eisensteinReg, eisPair] using h

/-- **The residue at $s = 1$:** $(s-1)E^*(z,s) \to 1$. -/
@[kb "miyake1989" "Theorem 7.2.17 at N = 1: the completed Eisenstein series has residue 1 at s = 1 [unverified]"]
theorem tendsto_eisensteinStar_residue (z : ℍ) :
    Tendsto (fun s ↦ (s - 1) * eisensteinStar z s) (𝓝[≠] 1) (𝓝 1) := by
  have h := (eisPair z).Λ_residue_k
  simpa [eisPair, eisensteinStar] using h

theorem eisTerm_zero_vec (lam : ℕ) {s : ℂ} (hs : 1 < s.re) : eisTerm lam s 0 = 0 := by
  have hs0 : -(lam : ℂ) - 2 * s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
    linarith
  simp [eisTerm, Complex.zero_cpow hs0]

/-- **The Dirichlet series** for $\operatorname{Re}s > 1$:
$E^*(z,s) = \pi^{-s}\Gamma(s)\,y^s\sum_{(c,d)}{}'|cz+d|^{-2s}$, the lattice Eisenstein series of level one and weight zero. -/
theorem eisensteinStar_eq_lattice (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    eisensteinStar z s = (π : ℂ) ^ (-s) * Gamma s * eisensteinLattice 1 0 1 z s := by
  have hy := z.im_pos
  have hM := (eisPair z).hasMellin (s := s) (by simpa [eisPair] using hs)
  have h1 : eisensteinStar z s = mellin (fun t ↦ thetaZ z t - 1) s := hM.2.symm
  have h2 : mellin (fun t ↦ thetaZ z t - 1) s =
      mellin (fun t ↦ genTheta 1 0 cOff z (z.im⁻¹ * t)) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    simp only
    rw [thetaZ_sub_one z ht, div_eq_inv_mul]
  rw [h1, h2, mellin_comp_mul_left _ _ (inv_pos.2 hy),
    mellin_genTheta_of_zero le_rfl cOff_zero norm_cOff_le z (by simpa using hs)]
  have h3 : ((z.im⁻¹ : ℝ) : ℂ) ^ (-s) = (z.im : ℂ) ^ s := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne), Complex.cpow_neg, inv_inv]
  have h4 : genSeries 1 0 cOff z s =
      ∑' p : ℤ × ℤ, (1 : DirichletCharacter ℂ 1) (p.2 : ZMod 1) *
        eisTerm 0 s (((1 : ℕ) : ℂ) * p.1 * z + p.2) := by
    unfold genSeries
    refine tsum_congr fun p ↦ ?_
    rw [trivialChar_apply]
    by_cases hp : p = 0
    · subst hp
      have h0 : (((1 : ℕ) : ℂ) * ((0 : ℤ × ℤ).1 : ℤ) * z + ((0 : ℤ × ℤ).2 : ℤ)) = 0 := by simp
      rw [h0, eisTerm_zero_vec 0 hs]
      simp [cOff]
    · simp [cOff, hp, eisTerm, genVec]
  rw [h3, smul_eq_mul, eisensteinLattice, h4]
  ring

end ModularFormsKB.RankinSelberg
