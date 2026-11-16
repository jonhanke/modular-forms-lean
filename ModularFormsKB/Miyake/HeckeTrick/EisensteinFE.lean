import ModularFormsKB.HalfIntegral.Abstract.ShimuraRankin
import ModularFormsKB.Miyake.Wave2B.HeckeTrick
import ModularFormsKB.Miyake.HeckeTrick.ThetaBounds
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# Hecke's functional equation `EisensteinFE` from the lattice theta inversion

The named input `ModularFormsKB.HalfIntegral.EisensteinFE` (Hecke 1927 `hecke1927`;
Miyake 1989 `miyake1989`, §7.2) is reduced here to a smaller analytic statement, the inversion formula of the lattice
theta series (`LatticeThetaInversion`), which is two-dimensional Poisson summation for $v^\lambda e^{-\pi u|v|^2}$
($v^\lambda$ is a harmonic polynomial, so its Fourier transform is $(-i)^\lambda u^{-1-\lambda}\xi^\lambda
e^{-\pi|\xi|^2/u}$). Then the Mellin transform of the theta series is Hecke's completed Eisenstein series, and the
abstract Mellin functional-equation machinery of Mathlib (`WeakFEPair`, `StrongFEPair`,
`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`) gives the entire continuation and the functional equation.

**Normalization.** For $z = x+iy \in \mathbf H$, $L \ge 1$, $\lambda \ge 0$, a character $\omega$ mod $L$ and $u > 0$:
$$\Theta(z,u) = \sum_{(c,d)\in\mathbb Z^2}\omega(d)\,v^\lambda e^{-\pi u|v|^2},\quad v = Lcz+d, \qquad
\check\Theta(z,u) = \sum_{(m,n)\in\mathbb Z^2}G(\omega,-m)\,w^\lambda e^{-\pi u|w|^2},\quad w = mz+n,$$
with $G(\omega,m) = \sum_{a=0}^{L-1}\omega(a)e^{2\pi iam/L}$ (`gaussAt`). The dual lattice of $L\mathbb Zz + L\mathbb Z$
for the pairing $\operatorname{Re}(v\bar\xi)$ is $\frac{i}{Ly}(\mathbb Zz+\mathbb Z)$, and Poisson summation over the
cosets $a + L\mathbb Zz + L\mathbb Z$ gives
$$\Theta(z,u) = (L^2y)^{-1}(Ly)^{-\lambda}u^{-1-\lambda}\,\check\Theta\big(z, 1/(L^2y^2u)\big).$$
(Checked numerically for $L = 3, 4$ and $\lambda = 1, 2, 3$ to 14 digits; the constants of `EisensteinFE` were rederived
from this formula by the Mellin transform and agree.)
-/

open MeasureTheory Set Filter Topology Complex
open scoped UpperHalfPlane
open scoped Real

noncomputable section

namespace ModularFormsKB.Miyake.HeckeTrick

open ModularFormsKB.HalfIntegral

/-- The lattice theta series $\Theta(z,u) = \sum_{(c,d)}\omega(d)\,v^\lambda e^{-\pi u|v|^2}$, $v = Lcz+d$. -/
def latticeTheta (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (u : ℝ) : ℂ :=
  ∑' p : ℤ × ℤ, ω (p.2 : ZMod L) * ((L : ℂ) * p.1 * z + p.2) ^ lam *
    ((Real.exp (-π * u * ‖(L : ℂ) * p.1 * z + p.2‖ ^ 2) : ℝ) : ℂ)

/-- The dual theta series $\check\Theta(z,u) = \sum_{(m,n)}G(\omega,-m)\,w^\lambda e^{-\pi u|w|^2}$, $w = mz+n$. -/
def dualTheta (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (u : ℝ) : ℂ :=
  ∑' p : ℤ × ℤ, gaussAt L ω (-p.1) * ((p.1 : ℂ) * z + p.2) ^ lam *
    ((Real.exp (-π * u * ‖(p.1 : ℂ) * z + p.2‖ ^ 2) : ℝ) : ℂ)

/-- **The inversion formula of the lattice theta series** (Hecke 1927 `hecke1927` [unverified]; two-dimensional
Poisson summation): for $L \ge 1$, $z \in \mathbf H$ and $u > 0$,
$\Theta(z,u) = (L^2y)^{-1}(Ly)^{-\lambda}u^{-1-\lambda}\check\Theta(z,1/(L^2y^2u))$.
A cited result assumed as a named input (the smaller analytic lemma to which `EisensteinFE` is reduced). -/
@[kb "hecke1927" "inversion formula of the lattice theta series with a character, by Poisson summation [unverified]"]
structure LatticeThetaInversion : Prop where
  inv : ∀ (L lam : ℕ) (ω : DirichletCharacter ℂ L), 1 ≤ L → ∀ (z : ℍ) (u : ℝ), 0 < u →
    latticeTheta L lam ω z u =
      ((((L : ℝ) ^ 2 * z.im)⁻¹ * ((L : ℝ) * z.im)⁻¹ ^ lam * (u ^ (lam + 1))⁻¹ : ℝ) : ℂ) *
        dualTheta L lam ω z (1 / ((L : ℝ) ^ 2 * z.im ^ 2 * u))

theorem latticeTheta_eq_genTheta (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (u : ℝ) :
    latticeTheta L lam ω z u = genTheta L lam (fun p ↦ ω (p.2 : ZMod L)) z u := by
  rfl

theorem dualTheta_eq_genTheta (L lam : ℕ) (ω : DirichletCharacter ℂ L) (z : ℍ) (u : ℝ) :
    dualTheta L lam ω z u = genTheta 1 lam (fun p ↦ gaussAt L ω (-p.1)) z u := by
  simp [dualTheta, genTheta, genVec]

theorem exists_bound_char (L : ℕ) (hL : 1 ≤ L) (ω : DirichletCharacter ℂ L) :
    ∃ C : ℝ, ∀ p : ℤ × ℤ, ‖ω (p.2 : ZMod L)‖ ≤ C := by
  have : NeZero L := ⟨by omega⟩
  obtain ⟨C, hC⟩ := (Set.finite_range (fun a : ZMod L => ‖ω a‖)).bddAbove
  exact ⟨C, fun p => hC ⟨(p.2 : ZMod L), rfl⟩⟩

theorem exists_bound_gauss (L : ℕ) (ω : DirichletCharacter ℂ L) :
    ∃ C : ℝ, ∀ p : ℤ × ℤ, ‖gaussAt L ω (-p.1)‖ ≤ C := by
  refine ⟨∑ a ∈ Finset.range L, ‖ω a‖, fun p => ?_⟩
  unfold gaussAt
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
  rw [norm_mul]
  have : ‖cexp (2 * π * I * a * ((-p.1 : ℤ) : ℂ) / L)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [this, mul_one]

/-- The root number $\varepsilon = (L^2y)^{-1}(Ly)^{-\lambda}$ of the theta inversion. -/
def thetaEps (L lam : ℕ) (z : ℍ) : ℂ := ((((L : ℝ) ^ 2 * z.im)⁻¹ * ((L : ℝ) * z.im)⁻¹ ^ lam : ℝ) : ℂ)

theorem thetaEps_ne_zero {L : ℕ} (hL : 1 ≤ L) (lam : ℕ) (z : ℍ) : thetaEps L lam z ≠ 0 := by
  have hy := z.im_pos
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  unfold thetaEps
  rw [Complex.ofReal_ne_zero]
  positivity

theorem isBigO_div_const_rpow {c : ℝ} (hc : 0 < c) (r : ℝ) :
    (fun x : ℝ ↦ (x / c) ^ r) =O[atTop] (· ^ r) := by
  refine Asymptotics.IsBigO.of_bound (c ^ r)⁻¹ ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Real.div_rpow hx hc.le, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg hx _)]
  rw [div_eq_inv_mul]

/-- The FE-pair attached to the theta series. -/
def thetaPair (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (z : ℍ) : WeakFEPair ℂ where
  f := latticeTheta L lam ω z
  g := fun x ↦ dualTheta L lam ω z (x / ((L : ℝ) ^ 2 * z.im ^ 2))
  k := (lam : ℝ) + 1
  ε := thetaEps L lam z
  f₀ := 0
  g₀ := 0
  hf_int := by
    obtain ⟨C, hC⟩ := exists_bound_char L hL ω
    have : latticeTheta L lam ω z = genTheta L lam (fun p ↦ ω (p.2 : ZMod L)) z :=
      funext (latticeTheta_eq_genTheta L lam ω z)
    rw [this]
    exact (continuousOn_genTheta hL hC z).locallyIntegrableOn measurableSet_Ioi
  hg_int := by
    obtain ⟨C, hC⟩ := exists_bound_gauss L ω
    have hc : 0 < (L : ℝ) ^ 2 * z.im ^ 2 := by
      have := z.im_pos
      have : (0:ℝ) < L := by exact_mod_cast hL
      positivity
    have : (fun x : ℝ ↦ dualTheta L lam ω z (x / ((L : ℝ) ^ 2 * z.im ^ 2))) =
        fun x ↦ genTheta 1 lam (fun p ↦ gaussAt L ω (-p.1)) z (x / ((L : ℝ) ^ 2 * z.im ^ 2)) :=
      funext fun x ↦ dualTheta_eq_genTheta L lam ω z _
    rw [this]
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine (continuousOn_genTheta (le_refl 1) hC z).comp
      (continuous_id.div_const _).continuousOn fun x hx ↦ ?_
    exact div_pos hx hc
  hk := by positivity
  hε := thetaEps_ne_zero hL lam z
  h_feq := by
    intro x hx
    have hx : 0 < x := hx
    have hy := z.im_pos
    have hL' : (0:ℝ) < L := by exact_mod_cast hL
    show latticeTheta L lam ω z (1 / x) = _
    rw [h.inv L lam ω hL z (1 / x) (one_div_pos.mpr hx)]
    have e : 1 / ((L : ℝ) ^ 2 * z.im ^ 2 * (1 / x)) = x / ((L : ℝ) ^ 2 * z.im ^ 2) := by
      field_simp
    rw [e]
    have hk : x ^ ((lam : ℝ) + 1) = x ^ (lam + 1) := by
      rw [← Real.rpow_natCast]; norm_cast
    rw [hk, smul_eq_mul, thetaEps]
    congr 1
    rw [← Complex.ofReal_mul]
    congr 1
    simp [one_div, inv_pow]
  hf_top := by
    intro r
    obtain ⟨C, hC⟩ := exists_bound_char L hL ω
    have : latticeTheta L lam ω z = genTheta L lam (fun p ↦ ω (p.2 : ZMod L)) z :=
      funext (latticeTheta_eq_genTheta L lam ω z)
    simpa [this] using genTheta_isBigO_atTop hL hlam hC z r
  hg_top := by
    intro r
    obtain ⟨C, hC⟩ := exists_bound_gauss L ω
    have hc : 0 < (L : ℝ) ^ 2 * z.im ^ 2 := by
      have := z.im_pos
      have : (0:ℝ) < L := by exact_mod_cast hL
      positivity
    have e : (fun x : ℝ ↦ dualTheta L lam ω z (x / ((L : ℝ) ^ 2 * z.im ^ 2)) - 0) =
        (genTheta 1 lam (fun p ↦ gaussAt L ω (-p.1)) z) ∘ (fun x ↦ x / ((L : ℝ) ^ 2 * z.im ^ 2)) :=
      funext fun x ↦ by simp [dualTheta_eq_genTheta]
    rw [e]
    exact ((genTheta_isBigO_atTop (le_refl 1) hlam hC z r).comp_tendsto
      (tendsto_id.atTop_div_const hc)).trans (isBigO_div_const_rpow hc r)

theorem thetaPair_strong (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (z : ℍ) : IsStrongFEPair (thetaPair h ω hL hlam z) :=
  ⟨rfl, rfl⟩

/-- The Mellin transform of $\Theta(z,\cdot)$ is entire (it is the $\Lambda$ of a strong FE-pair:
$f = \Theta(z,\cdot)$, $g(x) = \check\Theta(z, x/(L^2y^2))$, $k = \lambda+1$, $\varepsilon$ = `thetaEps`). -/
theorem differentiable_mellin_latticeTheta (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (z : ℍ) :
    Differentiable ℂ (mellin (latticeTheta L lam ω z)) := by
  have hP := thetaPair_strong h ω hL hlam z
  have := hP.differentiable_Λ
  rwa [hP.Λ_eq] at this

/-- The functional equation of the Mellin transforms:
$\mathcal M\Theta(\lambda+1-\sigma) = \varepsilon(L^2y^2)^{\sigma}\mathcal M\check\Theta(\sigma)$
for $\operatorname{Re}\sigma > 1 + \lambda/2$. -/
theorem mellin_latticeTheta_feq (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (z : ℍ) {σ : ℂ} (hσ : 1 + (lam : ℝ) / 2 < σ.re) :
    mellin (latticeTheta L lam ω z) ((lam : ℂ) + 1 - σ) =
      thetaEps L lam z * (((L : ℝ) ^ 2 * z.im ^ 2 : ℝ) : ℂ) ^ σ * mellin (dualTheta L lam ω z) σ := by
  have hP := thetaPair_strong h ω hL hlam z
  have hy := z.im_pos
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hc : 0 < (L : ℝ) ^ 2 * z.im ^ 2 := by positivity
  have h1 := (thetaPair h ω hL hlam z).functional_equation σ
  rw [hP.Λ_eq, hP.symm_Λ_eq] at h1
  have e1 : (((thetaPair h ω hL hlam z).k : ℝ) : ℂ) = (lam : ℂ) + 1 := by
    simp [thetaPair]
  rw [e1] at h1
  refine h1.trans ?_
  have e2 : mellin (thetaPair h ω hL hlam z).g σ =
      (((((L : ℝ) ^ 2 * z.im ^ 2)⁻¹ : ℝ) : ℂ)) ^ (-σ) • mellin (dualTheta L lam ω z) σ := by
    have := mellin_comp_mul_right (dualTheta L lam ω z) σ (a := ((L : ℝ) ^ 2 * z.im ^ 2)⁻¹)
      (inv_pos.mpr hc)
    rw [← this]
    simp only [thetaPair, div_eq_mul_inv]
  rw [e2, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hc.le, Complex.cpow_neg, inv_inv,
    smul_eq_mul, smul_eq_mul]
  simp [thetaPair, mul_assoc]

/-! ### Elementary helpers for the bounds -/

theorem one_le_Q {y : ℝ} (hy : 0 < y) : 1 ≤ y + y⁻¹ := by
  have h0 : 0 < y⁻¹ := inv_pos.2 hy
  rcases le_total 1 y with h | h
  · linarith
  · have := (one_le_inv₀ hy).2 h
    linarith

theorem y_le_Q {y : ℝ} (hy : 0 < y) : y ≤ y + y⁻¹ := by
  have h0 : 0 < y⁻¹ := inv_pos.2 hy
  linarith

theorem yinv_le_Q {y : ℝ} (hy : 0 < y) : y⁻¹ ≤ y + y⁻¹ := by linarith

theorem exp_pow_bound (M : ℕ) {κ : ℝ} (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ M * Real.exp (-(κ * t)) ≤ (M.factorial : ℝ) * (κ⁻¹) ^ M := by
  have h := Real.pow_div_factorial_le_exp (κ * t) (by positivity) M
  have hf : (0 : ℝ) < M.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  have h2 : (κ * t) ^ M * Real.exp (-(κ * t)) ≤ M.factorial := by
    calc (κ * t) ^ M * Real.exp (-(κ * t)) ≤ (Real.exp (κ * t) * M.factorial) * Real.exp (-(κ * t)) := by
          gcongr
      _ = M.factorial := by
          rw [mul_right_comm, ← Real.exp_add]; simp
  have e : t ^ M * Real.exp (-(κ * t)) = (κ⁻¹) ^ M * ((κ * t) ^ M * Real.exp (-(κ * t))) := by
    rw [mul_pow, ← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hκ.ne']
    simp
  rw [e, mul_comm]
  gcongr

/-- The exponential tail integral. -/
theorem integrableOn_pow_exp_Ioi (M : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    IntegrableOn (fun u : ℝ ↦ u ^ M * Real.exp (-κ * (u - 1))) (Ioi 1) := by
  have h0 : IntegrableOn (fun x : ℝ => x ^ (M : ℝ) * Real.exp (-κ * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have : (0:ℝ) ≤ M := by positivity
                                               linarith) one_pos hκ
  have h1 : IntegrableOn (fun x : ℝ => Real.exp κ * (x ^ M * Real.exp (-(κ * x)))) (Ioi 1) := by
    have := (h0.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul (Real.exp κ)
    simpa [IntegrableOn] using this
  refine h1.mono' ?_ ?_
  · have : ContinuousOn (fun u : ℝ ↦ u ^ M * Real.exp (-κ * (u - 1))) (Ioi 1) := by fun_prop
    exact this.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [Real.norm_of_nonneg (by positivity)]
    refine le_of_eq ?_
    rw [← mul_assoc, mul_comm (Real.exp κ), mul_assoc, ← Real.exp_add]
    congr 2
    ring

/-- The exponential tail bound. -/
theorem integral_pow_exp_Ioi_le (M : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    ∫ u in Ioi (1 : ℝ), u ^ M * Real.exp (-κ * (u - 1)) ≤
      Real.exp κ * (M.factorial : ℝ) * (κ⁻¹) ^ (M + 1) := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (M : ℝ) + 1) (r := κ) (by positivity) hκ
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ ((M : ℝ) + 1 - 1) * Real.exp (-(κ * x))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [key]; positivity)
  have hint' : IntegrableOn (fun x : ℝ ↦ x ^ M * Real.exp (-(κ * x))) (Ioi 0) := by
    refine hint.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp
  calc ∫ u in Ioi (1 : ℝ), u ^ M * Real.exp (-κ * (u - 1))
      ≤ ∫ u in Ioi (1 : ℝ), Real.exp κ * (u ^ M * Real.exp (-(κ * u))) := by
        refine setIntegral_mono_on (integrableOn_pow_exp_Ioi M hκ)
          ((hint'.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _) measurableSet_Ioi
          (fun x hx => ?_)
        refine le_of_eq ?_
        rw [← mul_assoc, mul_comm (Real.exp κ), mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp κ * (u ^ M * Real.exp (-(κ * u))) := by
        refine setIntegral_mono_set (hint'.const_mul _) ?_ (Filter.Eventually.of_forall fun x hx => Ioi_subset_Ioi zero_le_one hx)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have : 0 ≤ x := le_of_lt hx
        positivity
    _ = Real.exp κ * (M.factorial : ℝ) * (κ⁻¹) ^ (M + 1) := by
        rw [integral_const_mul]
        have e : ∫ u in Ioi (0 : ℝ), u ^ M * Real.exp (-(κ * u)) =
            ∫ u in Ioi (0 : ℝ), u ^ ((M : ℝ) + 1 - 1) * Real.exp (-(κ * u)) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
          simp
        rw [e, key, Real.Gamma_nat_eq_factorial]
        have : (κ⁻¹) ^ ((M : ℝ) + 1) = (κ⁻¹) ^ (M + 1) := by
          rw [← Real.rpow_natCast]; norm_cast
        rw [one_div, this]
        ring

theorem norm_latticeTheta_eq (h : LatticeThetaInversion) {L : ℕ} (lam : ℕ)
    (ω : DirichletCharacter ℂ L) (hL : 1 ≤ L) (z : ℍ) {u : ℝ} (hu : 0 < u) :
    ‖latticeTheta L lam ω z u‖ = ((L : ℝ) ^ 2 * z.im)⁻¹ * ((L : ℝ) * z.im)⁻¹ ^ lam *
      (u ^ (lam + 1))⁻¹ * ‖dualTheta L lam ω z (1 / ((L : ℝ) ^ 2 * z.im ^ 2 * u))‖ := by
  have hy := z.im_pos
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  rw [h.inv L lam ω hL z u hu, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem eps_le_Q {L : ℕ} (lam : ℕ) (hL : 1 ≤ L) (z : ℍ) :
    ((L : ℝ) ^ 2 * z.im)⁻¹ * ((L : ℝ) * z.im)⁻¹ ^ lam ≤ (z.im + z.im⁻¹) ^ (lam + 1) := by
  have hy := z.im_pos
  have hL' : (1:ℝ) ≤ L := by exact_mod_cast hL
  have h1 : ((L : ℝ) ^ 2 * z.im)⁻¹ ≤ z.im⁻¹ := by
    apply inv_anti₀ hy
    have : 1 ≤ (L : ℝ) ^ 2 := by nlinarith
    nlinarith
  have h2 : ((L : ℝ) * z.im)⁻¹ ≤ z.im⁻¹ := by
    apply inv_anti₀ hy
    nlinarith
  have h3 : ((L : ℝ) * z.im)⁻¹ ^ lam ≤ (z.im⁻¹) ^ lam := by
    gcongr
  calc ((L : ℝ) ^ 2 * z.im)⁻¹ * ((L : ℝ) * z.im)⁻¹ ^ lam ≤ z.im⁻¹ * (z.im⁻¹) ^ lam := by
        gcongr
    _ = (z.im⁻¹) ^ (lam + 1) := by ring
    _ ≤ _ := by gcongr; exact yinv_le_Q hy

theorem c_le_Q {L : ℕ} (z : ℍ) : (L : ℝ) ^ 2 * z.im ^ 2 ≤ (L : ℝ) ^ 2 * (z.im + z.im⁻¹) ^ 2 := by
  have hy := z.im_pos
  gcongr
  exact y_le_Q hy

theorem one_add_inv_sq_le {y : ℝ} (hy : 0 < y) : 1 + y⁻¹ ^ 2 ≤ (y + y⁻¹) ^ 2 := by
  have : (y + y⁻¹) ^ 2 = y ^ 2 + 2 + y⁻¹ ^ 2 := by
    field_simp
    ring
  rw [this]
  nlinarith [sq_nonneg y]

theorem y_sq_le {y : ℝ} (hy : 0 < y) : y ^ 2 ≤ min 1 (y ^ 2) * (y + y⁻¹) ^ 2 := by
  have hQ := one_le_Q hy
  have hQ2 : 1 ≤ (y + y⁻¹) ^ 2 := by nlinarith
  rcases le_total 1 (y ^ 2) with h | h
  · rw [min_eq_left h, one_mul]
    nlinarith [y_le_Q hy]
  · rw [min_eq_right h]
    nlinarith [sq_nonneg y]

/-- The small-`u` bound: rapid vanishing at `0` of the lattice theta series, polynomially in `y`. -/
theorem smallU_bound (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (N : ℕ) :
    ∃ (A : ℕ) (B : ℝ), ∀ (z : ℍ) (u : ℝ), 0 < u → u ≤ 1 →
      ‖latticeTheta L lam ω z u‖ ≤ B * (z.im + z.im⁻¹) ^ A * u ^ N := by
  obtain ⟨Cg, hCg⟩ := exists_bound_gauss L ω
  obtain ⟨B3, hB3, hD1⟩ := norm_genTheta_le_of_one_le (a := 1) (lam := lam)
    (c := fun p ↦ gaussAt L ω (-p.1)) (le_refl 1) hlam hCg
  obtain ⟨B2, hB2, A2', hA2, hD2⟩ := norm_genTheta_le_of_le_one (a := 1) (lam := lam)
    (c := fun p ↦ gaussAt L ω (-p.1)) (le_refl 1) hCg
  set A2 : ℕ := ⌈A2'⌉₊ with hA2def
  set M : ℕ := lam + 1 + N with hM
  have hL' : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hL2 : (0:ℝ) < (L:ℝ) ^ 2 := by positivity
  set K1 : ℝ := B3 * Real.exp π * M.factorial * ((L : ℝ) ^ 2) ^ M with hK1
  set K2 : ℝ := 2 * B2 * ((L : ℝ) ^ 2) ^ (lam + 1 + N) with hK2
  have hK1pos : 0 ≤ K1 := by positivity
  have hK2pos : 0 ≤ K2 := by positivity
  refine ⟨(lam + 1 + 2 + 2 * M) + ((lam + 1) + A2 + 2 * (lam + 1 + N)), K1 + K2, ?_⟩
  intro z u hu hu1
  have hy := z.im_pos
  set y := z.im with hydef
  set Q := y + y⁻¹ with hQdef
  have hQ1 : 1 ≤ Q := one_le_Q hy
  have hQ0 : 0 < Q := by linarith
  set c : ℝ := (L : ℝ) ^ 2 * y ^ 2 with hcdef
  have hc : 0 < c := by positivity
  have hcQ : c ≤ (L : ℝ) ^ 2 * Q ^ 2 := c_le_Q z
  set t : ℝ := 1 / (c * u) with htdef
  have ht0 : 0 < t := by positivity
  have hE := eps_le_Q lam hL z
  have hE0 : 0 ≤ ((L : ℝ) ^ 2 * y)⁻¹ * ((L : ℝ) * y)⁻¹ ^ lam := by positivity
  rw [norm_latticeTheta_eq h lam ω hL z hu]
  rw [← hcdef, ← htdef]
  have hD := dualTheta_eq_genTheta L lam ω z t
  rw [hD]
  have hEu : (u ^ (lam + 1))⁻¹ = u ^ N * (1 / u) ^ M := by
    have hu' := hu.ne'
    rw [hM, one_div, inv_pow]
    field_simp
    ring
  have hu0 : 0 ≤ u ^ N := by positivity
  by_cases ht : 1 ≤ t
  · -- case t ≥ 1
    have hT := hD1 z t ht
    set m : ℝ := min 1 (y ^ 2) with hmdef
    have hm0 : 0 < m := lt_min one_pos (by positivity)
    have hm1 : m ≤ 1 := min_le_left _ _
    set κ : ℝ := π * m / c with hκdef
    have hκ : 0 < κ := by positivity
    have hexp : Real.exp (-π * (t - 1) * m) ≤ Real.exp π * Real.exp (-(κ * (1 / u))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have : -π * (t - 1) * m = π * m - κ * (1 / u) := by
        rw [hκdef, htdef]; field_simp; ring
      rw [this]
      have : π * m ≤ π := by nlinarith [Real.pi_pos]
      linarith
    have hκinv : κ⁻¹ ≤ (L : ℝ) ^ 2 * Q ^ 2 := by
      have := y_sq_le hy
      rw [hκdef, inv_div, div_le_iff₀ (by positivity)]
      have hpi : (1:ℝ) ≤ π := by linarith [Real.pi_gt_three]
      calc c = (L : ℝ) ^ 2 * y ^ 2 := rfl
        _ ≤ (L : ℝ) ^ 2 * (m * Q ^ 2) := by gcongr
        _ ≤ (L : ℝ) ^ 2 * Q ^ 2 * (π * m) := by
          have : 0 ≤ (L : ℝ) ^ 2 * Q ^ 2 * m := by positivity
          nlinarith
    have hX : (1 / u) ^ M * Real.exp (-(κ * (1 / u))) ≤ M.factorial * ((L : ℝ) ^ 2 * Q ^ 2) ^ M := by
      refine (exp_pow_bound M hκ (by positivity)).trans ?_
      gcongr
    have h1y : 1 + y⁻¹ ^ 2 ≤ Q ^ 2 := one_add_inv_sq_le hy
    have hT' : ‖genTheta 1 lam (fun p ↦ gaussAt L ω (-p.1)) z t‖ ≤
        B3 * Q ^ 2 * (Real.exp π * Real.exp (-(κ * (1 / u)))) := by
      refine hT.trans ?_
      calc B3 * (1 + z.im⁻¹ ^ 2) * Real.exp (-π * (t - 1) * m)
          ≤ B3 * Q ^ 2 * Real.exp (-π * (t - 1) * m) := by gcongr
        _ ≤ _ := by gcongr
    have hQp : (0:ℝ) ≤ Q ^ (lam + 1) := by positivity
    have hE' : ((L : ℝ) ^ 2 * y)⁻¹ * ((L : ℝ) * y)⁻¹ ^ lam ≤ Q ^ (lam + 1) := hE
    rw [hEu]
    have hA1 : Q ^ (lam + 1 + 2 + 2 * M) ≤ Q ^ ((lam + 1 + 2 + 2 * M) + ((lam + 1) + A2 + 2 * (lam + 1 + N))) :=
      pow_le_pow_right₀ hQ1 (by omega)
    calc ((L : ℝ) ^ 2 * y)⁻¹ * ((L : ℝ) * y)⁻¹ ^ lam * (u ^ N * (1 / u) ^ M) *
          ‖genTheta 1 lam (fun p ↦ gaussAt L ω (-p.1)) z t‖
        ≤ Q ^ (lam + 1) * (u ^ N * (1 / u) ^ M) * (B3 * Q ^ 2 * (Real.exp π * Real.exp (-(κ * (1 / u))))) := by
          gcongr
      _ = u ^ N * (B3 * Real.exp π * Q ^ (lam + 3)) * ((1 / u) ^ M * Real.exp (-(κ * (1 / u)))) := by ring
      _ ≤ u ^ N * (B3 * Real.exp π * Q ^ (lam + 3)) * (M.factorial * ((L : ℝ) ^ 2 * Q ^ 2) ^ M) := by
          gcongr
      _ = K1 * Q ^ (lam + 1 + 2 + 2 * M) * u ^ N := by
          rw [hK1]; ring
      _ ≤ K1 * Q ^ ((lam + 1 + 2 + 2 * M) + ((lam + 1) + A2 + 2 * (lam + 1 + N))) * u ^ N := by
          gcongr
      _ ≤ (K1 + K2) * Q ^ ((lam + 1 + 2 + 2 * M) + ((lam + 1) + A2 + 2 * (lam + 1 + N))) * u ^ N := by
          gcongr
          linarith
  · -- case t < 1
    have ht1 : t < 1 := not_le.1 ht
    have hcu : 1 < c * u := by
      exact (div_lt_one (by positivity : 0 < c * u)).1 ht1
    have hT := hD2 z t ht0 ht1.le
    have hyA : y ^ A2' ≤ Q ^ (A2 : ℝ) :=
      (Real.rpow_le_rpow hy.le (y_le_Q hy) hA2.le).trans
        (Real.rpow_le_rpow_of_exponent_le hQ1 (Nat.le_ceil A2'))
    have hyA' : y⁻¹ ^ A2' ≤ Q ^ (A2 : ℝ) :=
      (Real.rpow_le_rpow (inv_pos.2 hy).le (yinv_le_Q hy) hA2.le).trans
        (Real.rpow_le_rpow_of_exponent_le hQ1 (Nat.le_ceil A2'))
    rw [Real.rpow_natCast] at hyA hyA'
    have htp : t ^ (-(lam : ℝ) - 1) = (c * u) ^ (lam + 1) := by
      have : -(lam : ℝ) - 1 = -((lam + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_neg ht0.le, Real.rpow_natCast, htdef, one_div, inv_pow, inv_inv]
    rw [htp] at hT
    have hT2 : ‖genTheta 1 lam (fun p ↦ gaussAt L ω (-p.1)) z t‖ ≤
        B2 * (Q ^ A2 + Q ^ A2) * (c * u) ^ (lam + 1) := by
      refine hT.trans ?_
      have := add_le_add hyA hyA'
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hB2.le) (by positivity)
    have hE': ((L : ℝ) ^ 2 * y)⁻¹ * ((L : ℝ) * y)⁻¹ ^ lam ≤ Q ^ (lam + 1) := hE
    have hcN : 1 ≤ (c * u) ^ N := one_le_pow₀ hcu.le
    have hcpow : c ^ (lam + 1 + N) ≤ ((L : ℝ) ^ 2 * Q ^ 2) ^ (lam + 1 + N) := by gcongr
    have hA1 : Q ^ ((lam + 1) + A2 + 2 * (lam + 1 + N)) ≤
        Q ^ ((lam + 1 + 2 + 2 * M) + ((lam + 1) + A2 + 2 * (lam + 1 + N))) :=
      pow_le_pow_right₀ hQ1 (by omega)
    have hu' := hu.ne'
    calc ((L : ℝ) ^ 2 * y)⁻¹ * ((L : ℝ) * y)⁻¹ ^ lam * (u ^ (lam + 1))⁻¹ *
          ‖genTheta 1 lam (fun p ↦ gaussAt L ω (-p.1)) z t‖
        ≤ Q ^ (lam + 1) * (u ^ (lam + 1))⁻¹ *
            (B2 * (Q ^ A2 + Q ^ A2) * (c * u) ^ (lam + 1)) := by
          gcongr
      _ = 2 * B2 * Q ^ (lam + 1 + A2) * c ^ (lam + 1) := by
          field_simp
          ring
      _ ≤ 2 * B2 * Q ^ (lam + 1 + A2) * (c ^ (lam + 1) * (c * u) ^ N) := by
          gcongr
          exact le_mul_of_one_le_right (by positivity) hcN
      _ = 2 * B2 * Q ^ (lam + 1 + A2) * c ^ (lam + 1 + N) * u ^ N := by ring
      _ ≤ 2 * B2 * Q ^ (lam + 1 + A2) * ((L : ℝ) ^ 2 * Q ^ 2) ^ (lam + 1 + N) * u ^ N := by
          gcongr
      _ = K2 * Q ^ ((lam + 1) + A2 + 2 * (lam + 1 + N)) * u ^ N := by
          rw [hK2]; ring
      _ ≤ K2 * Q ^ ((lam + 1 + 2 + 2 * M) + ((lam + 1) + A2 + 2 * (lam + 1 + N))) * u ^ N := by
          gcongr
      _ ≤ (K1 + K2) * Q ^ ((lam + 1 + 2 + 2 * M) + ((lam + 1) + A2 + 2 * (lam + 1 + N))) * u ^ N := by
          gcongr
          linarith

theorem largeU_bound {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) :
    ∃ B : ℝ, 0 < B ∧ ∀ (z : ℍ) (u : ℝ), 1 ≤ u →
      ‖latticeTheta L lam ω z u‖ ≤
        B * (z.im + z.im⁻¹) ^ 2 * Real.exp (-π * (u - 1) * min 1 (z.im ^ 2)) := by
  obtain ⟨C, hC⟩ := exists_bound_char L hL ω
  obtain ⟨B, hB, hb⟩ := norm_genTheta_le_of_one_le (a := L) (lam := lam)
    (c := fun p ↦ ω (p.2 : ZMod L)) hL hlam hC
  refine ⟨B, hB, fun z u hu => ?_⟩
  rw [latticeTheta_eq_genTheta]
  refine (hb z u hu).trans ?_
  have := one_add_inv_sq_le z.im_pos
  gcongr

theorem master_bound (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (σ₁ σ₂ : ℝ) :
    ∃ (K : ℝ) (A M : ℕ), 0 ≤ K ∧ ∀ (z : ℍ) (σ : ℂ), σ₁ ≤ σ.re → σ.re ≤ σ₂ → ∀ u : ℝ, 0 < u →
      (u ≤ 1 → ‖(u : ℂ) ^ (σ - 1) • latticeTheta L lam ω z u‖ ≤ K * (z.im + z.im⁻¹) ^ A) ∧
      (1 < u → ‖(u : ℂ) ^ (σ - 1) • latticeTheta L lam ω z u‖ ≤
        K * (z.im + z.im⁻¹) ^ A * (u ^ M * Real.exp (-π * (u - 1) * min 1 (z.im ^ 2)))) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (1 - σ₁)
  obtain ⟨M, hM⟩ := exists_nat_ge (σ₂ - 1)
  obtain ⟨As, Bs, hs⟩ := smallU_bound h ω hL hlam N
  obtain ⟨Bl, hBl, hl⟩ := largeU_bound ω hL hlam
  have hBs : 0 ≤ Bs := by
    have := hs ⟨(1:ℝ) * I, by simp⟩ 1 one_pos le_rfl
    have h0 : 0 ≤ ‖latticeTheta L lam ω ⟨(1:ℝ) * I, by simp⟩ 1‖ := norm_nonneg _
    have hQ : 0 < ((⟨(1:ℝ) * I, by simp⟩ : ℍ).im + (⟨(1:ℝ) * I, by simp⟩ : ℍ).im⁻¹) ^ As := by
      have := one_le_Q (UpperHalfPlane.im_pos ⟨(1:ℝ) * I, by simp⟩)
      positivity
    simp only [one_pow, mul_one] at this
    by_contra hneg
    push_neg at hneg
    nlinarith
  refine ⟨Bs + Bl, As + 2, M, by positivity, fun z σ h1 h2 u hu => ⟨fun hu1 => ?_, fun hu1 => ?_⟩⟩
  · have hy := z.im_pos
    have hQ1 := one_le_Q hy
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp only [Complex.sub_re, Complex.one_re, Complex.norm_real]
    have h3 : u ^ (σ.re - 1) ≤ u ^ (-(N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith)
    have h4 := hs z u hu hu1
    have h5 : u ^ (-(N : ℝ)) * u ^ N = 1 := by
      rw [Real.rpow_neg hu.le, Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]
    calc u ^ (σ.re - 1) * ‖latticeTheta L lam ω z u‖
        ≤ u ^ (-(N : ℝ)) * (Bs * (z.im + z.im⁻¹) ^ As * u ^ N) := by gcongr
      _ = Bs * (z.im + z.im⁻¹) ^ As := by linear_combination (Bs * (z.im + z.im⁻¹) ^ As) * h5
      _ ≤ (Bs + Bl) * (z.im + z.im⁻¹) ^ (As + 2) := by
        have : (z.im + z.im⁻¹) ^ As ≤ (z.im + z.im⁻¹) ^ (As + 2) :=
          pow_le_pow_right₀ hQ1 (by omega)
        have h0 : 0 ≤ (z.im + z.im⁻¹) ^ As := by positivity
        nlinarith
  · have hy := z.im_pos
    have hQ1 := one_le_Q hy
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp only [Complex.sub_re, Complex.one_re]
    have h3 : u ^ (σ.re - 1) ≤ u ^ (M : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (by linarith)
    rw [Real.rpow_natCast] at h3
    have h4 := hl z u hu1.le
    calc u ^ (σ.re - 1) * ‖latticeTheta L lam ω z u‖
        ≤ u ^ M * (Bl * (z.im + z.im⁻¹) ^ 2 * Real.exp (-π * (u - 1) * min 1 (z.im ^ 2))) := by
          gcongr
      _ = Bl * (z.im + z.im⁻¹) ^ 2 * (u ^ M * Real.exp (-π * (u - 1) * min 1 (z.im ^ 2))) := by ring
      _ ≤ (Bs + Bl) * (z.im + z.im⁻¹) ^ (As + 2) *
            (u ^ M * Real.exp (-π * (u - 1) * min 1 (z.im ^ 2))) := by
        have : (z.im + z.im⁻¹) ^ 2 ≤ (z.im + z.im⁻¹) ^ (As + 2) :=
          pow_le_pow_right₀ hQ1 (by omega)
        gcongr
        linarith

theorem one_le_min_mul_Q {y : ℝ} (hy : 0 < y) : 1 ≤ min 1 (y ^ 2) * (y + y⁻¹) ^ 2 := by
  have hQ := one_le_Q hy
  have hQ2 : 1 ≤ (y + y⁻¹) ^ 2 := by nlinarith
  rcases le_total 1 (y ^ 2) with h | h
  · rw [min_eq_left h, one_mul]; exact hQ2
  · rw [min_eq_right h]
    have : y ^ 2 * (y + y⁻¹) ^ 2 = (y * (y + y⁻¹)) ^ 2 := by ring
    rw [this]
    have h2 : y * (y + y⁻¹) = y ^ 2 + 1 := by field_simp
    rw [h2]
    nlinarith [sq_nonneg y]

theorem Q_pow_le {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (y + y⁻¹) ^ n ≤ 2 ^ n * (y ^ n + y⁻¹ ^ n) := by
  have hi : 0 < y⁻¹ := inv_pos.2 hy
  rcases le_total 1 y with h | h
  · have h1 : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
    have : y + y⁻¹ ≤ 2 * y := by linarith
    calc (y + y⁻¹) ^ n ≤ (2 * y) ^ n := by gcongr
      _ = 2 ^ n * y ^ n := by rw [mul_pow]
      _ ≤ _ := by
        have : 0 ≤ y⁻¹ ^ n := by positivity
        have : (0:ℝ) ≤ 2 ^ n := by positivity
        nlinarith
  · have h1 : 1 ≤ y⁻¹ := (one_le_inv₀ hy).2 h
    have : y + y⁻¹ ≤ 2 * y⁻¹ := by linarith
    calc (y + y⁻¹) ^ n ≤ (2 * y⁻¹) ^ n := by gcongr
      _ = 2 ^ n * y⁻¹ ^ n := by rw [mul_pow]
      _ ≤ _ := by
        have : 0 ≤ y ^ n := by positivity
        have : (0:ℝ) ≤ 2 ^ n := by positivity
        nlinarith

theorem norm_mellin_le_Q (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (σ₁ σ₂ : ℝ) :
    ∃ (n : ℕ) (B : ℝ), ∀ (z : ℍ) (σ : ℂ), σ₁ ≤ σ.re → σ.re ≤ σ₂ →
      ‖mellin (latticeTheta L lam ω z) σ‖ ≤ B * (z.im + z.im⁻¹) ^ n := by
  obtain ⟨K, A, M, hK, hm⟩ := master_bound h ω hL hlam σ₁ σ₂
  refine ⟨A + 2 * (M + 1), K * (1 + Real.exp π * M.factorial), fun z σ h1 h2 => ?_⟩
  have hy := z.im_pos
  have hQ1 := one_le_Q hy
  have hP := thetaPair_strong h ω hL hlam z
  have hint : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (σ - 1) • latticeTheta L lam ω z u) (Ioi 0) :=
    (hP.hasMellin σ).1
  have hmel : mellin (latticeTheta L lam ω z) σ =
      ∫ u in Ioi (0:ℝ), (u : ℂ) ^ (σ - 1) • latticeTheta L lam ω z u := rfl
  rw [hmel, ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set (Ioc_subset_Ioi_self)) (hint.mono_set (Ioi_subset_Ioi zero_le_one))]
  set m : ℝ := min 1 (z.im ^ 2) with hmdef
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hpi : (1:ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hκ : 0 < π * m := by positivity
  have hκinv : (π * m)⁻¹ ≤ (z.im + z.im⁻¹) ^ 2 := by
    have := one_le_min_mul_Q hy
    rw [inv_eq_one_div, div_le_iff₀ hκ]
    have h0 : 0 ≤ m * (z.im + z.im⁻¹) ^ 2 := by positivity
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hpi)]
  have B1 : ‖∫ x in Ioc (0:ℝ) 1, (x : ℂ) ^ (σ - 1) • latticeTheta L lam ω z x‖ ≤
      K * (z.im + z.im⁻¹) ^ A := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0:ℝ) 1)
      (f := fun x : ℝ ↦ (x : ℂ) ^ (σ - 1) • latticeTheta L lam ω z x)
      (C := K * (z.im + z.im⁻¹) ^ A) (by simp)
      (fun x hx => (hm z σ h1 h2 x hx.1).1 hx.2)
    simpa using this
  have B2 : ‖∫ x in Ioi (1:ℝ), (x : ℂ) ^ (σ - 1) • latticeTheta L lam ω z x‖ ≤
      K * (z.im + z.im⁻¹) ^ A * (Real.exp π * M.factorial * ((z.im + z.im⁻¹) ^ 2) ^ (M + 1)) := by
    have hg := (integrableOn_pow_exp_Ioi M hκ).const_mul (K * (z.im + z.im⁻¹) ^ A)
    calc ‖∫ x in Ioi (1:ℝ), (x : ℂ) ^ (σ - 1) • latticeTheta L lam ω z x‖
        ≤ ∫ x in Ioi (1:ℝ), K * (z.im + z.im⁻¹) ^ A * (x ^ M * Real.exp (-(π * m) * (x - 1))) := by
          refine norm_integral_le_of_norm_le hg ?_
          refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
          have := (hm z σ h1 h2 x (lt_trans zero_lt_one hx)).2 hx
          have e : -π * (x - 1) * m = -(π * m) * (x - 1) := by ring
          rw [e] at this
          exact this
      _ = K * (z.im + z.im⁻¹) ^ A * ∫ x in Ioi (1:ℝ), x ^ M * Real.exp (-(π * m) * (x - 1)) := by
          rw [integral_const_mul]
      _ ≤ K * (z.im + z.im⁻¹) ^ A * (Real.exp (π * m) * M.factorial * ((π * m)⁻¹) ^ (M + 1)) := by
          gcongr
          exact integral_pow_exp_Ioi_le M hκ
      _ ≤ _ := by
          have : Real.exp (π * m) ≤ Real.exp π := Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
          gcongr
  have hfin : K * (z.im + z.im⁻¹) ^ A + K * (z.im + z.im⁻¹) ^ A *
      (Real.exp π * M.factorial * ((z.im + z.im⁻¹) ^ 2) ^ (M + 1)) ≤
      K * (1 + Real.exp π * M.factorial) * (z.im + z.im⁻¹) ^ (A + 2 * (M + 1)) := by
    generalize z.im + z.im⁻¹ = Q at hQ1 ⊢
    have e : K * Q ^ A * (Real.exp π * M.factorial * (Q ^ 2) ^ (M + 1)) =
        K * (Real.exp π * M.factorial) * Q ^ (A + 2 * (M + 1)) := by ring
    rw [e]
    have : Q ^ A ≤ Q ^ (A + 2 * (M + 1)) :=
      pow_le_pow_right₀ hQ1 (by omega)
    nlinarith [mul_le_mul_of_nonneg_left this hK]
  exact ((norm_add_le _ _).trans (add_le_add B1 B2)).trans hfin

/-- Continuity of the Mellin transform in $z$ (dominated convergence; near $u = 0$ through the inversion). -/
theorem continuous_mellin_latticeTheta (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (σ : ℂ) :
    Continuous fun z : ℍ ↦ mellin (latticeTheta L lam ω z) σ := by
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  obtain ⟨K, A, M, hK, hm⟩ := master_bound h ω hL hlam σ.re σ.re
  obtain ⟨C, hC⟩ := exists_bound_char L hL ω
  have hy0 := z₀.im_pos
  set y0 := z₀.im with hy0def
  set Q0 : ℝ := 2 * y0 + 2 * y0⁻¹ with hQ0def
  set m0 : ℝ := min 1 ((y0 / 2) ^ 2) with hm0def
  have hm0 : 0 < m0 := lt_min one_pos (by positivity)
  have hκ : 0 < π * m0 := by positivity
  set bound : ℝ → ℝ := fun u ↦
    (Ioc (0:ℝ) 1).indicator (fun _ ↦ K * Q0 ^ A) u +
    (Ioi (1:ℝ)).indicator (fun u ↦ K * Q0 ^ A * (u ^ M * Real.exp (-(π * m0) * (u - 1)))) u
    with hbound
  have hbint : Integrable bound volume := by
    refine Integrable.add ?_ ?_
    · exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
    · exact (integrable_indicator_iff measurableSet_Ioi).2
        ((integrableOn_pow_exp_Ioi M hκ).const_mul _)
  have hU : {z : ℍ | y0 / 2 < z.im ∧ z.im < 2 * y0} ∈ 𝓝 z₀ := by
    refine IsOpen.mem_nhds ?_ ⟨by linarith, by linarith⟩
    exact (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
      (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
  have key : ContinuousAt (fun z : ℍ ↦ ∫ u in Ioi (0:ℝ),
      (u : ℂ) ^ (σ - 1) • latticeTheta L lam ω z u) z₀ := by
    refine continuousAt_of_dominated (bound := bound) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun z => ?_
      have hcont : ContinuousOn (latticeTheta L lam ω z) (Ioi 0) := by
        have : latticeTheta L lam ω z = genTheta L lam (fun p ↦ ω (p.2 : ZMod L)) z :=
          funext (latticeTheta_eq_genTheta L lam ω z)
        rw [this]
        exact continuousOn_genTheta hL hC z
      have hc2 : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (σ - 1)) (Ioi 0) := by
        refine ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn fun u hu => ?_
        exact Complex.ofReal_mem_slitPlane.2 hu
      exact (hc2.smul hcont).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [hU] with z hz
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := hu
      have hy := z.im_pos
      have hQ1 := one_le_Q hy
      have hQle : z.im + z.im⁻¹ ≤ Q0 := by
        have h1 : z.im ≤ 2 * y0 := hz.2.le
        have h2 : z.im⁻¹ ≤ 2 * y0⁻¹ := by
          have : (y0 / 2)⁻¹ = 2 * y0⁻¹ := by field_simp
          rw [← this]
          exact inv_anti₀ (by positivity) hz.1.le
        linarith
      have hQpow : (z.im + z.im⁻¹) ^ A ≤ Q0 ^ A := by gcongr
      rcases le_or_gt u 1 with hu1 | hu1
      · have := (hm z σ le_rfl le_rfl u hu0).1 hu1
        have e : bound u = K * Q0 ^ A := by
          simp [hbound, Set.indicator, hu0, hu1, not_lt.2 hu1]
        rw [e]
        exact this.trans (by gcongr)
      · have := (hm z σ le_rfl le_rfl u hu0).2 hu1
        have e : bound u = K * Q0 ^ A * (u ^ M * Real.exp (-(π * m0) * (u - 1))) := by
          simp [hbound, Set.indicator, hu1, not_le.2 hu1]
        rw [e]
        refine this.trans ?_
        have hmm : m0 ≤ min 1 (z.im ^ 2) := by
          refine min_le_min le_rfl ?_
          have : y0 / 2 ≤ z.im := hz.1.le
          gcongr
        have hex : Real.exp (-π * (u - 1) * min 1 (z.im ^ 2)) ≤ Real.exp (-(π * m0) * (u - 1)) := by
          apply Real.exp_le_exp.2
          have : 0 ≤ π * (u - 1) := by nlinarith [Real.pi_pos]
          nlinarith
        have : 0 ≤ u ^ M := by positivity
        gcongr
    · exact hbint.integrableOn
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := hu
      have : ContinuousAt (fun z : ℍ ↦ latticeTheta L lam ω z u) z₀ := by
        have := continuous_genTheta_z (a := L) (lam := lam) (c := fun p ↦ ω (p.2 : ZMod L)) hL hC hu0
        exact this.continuousAt
      exact ContinuousAt.smul
        (continuousAt_const : ContinuousAt (fun _ : ℍ ↦ (u : ℂ) ^ (σ - 1)) z₀) this
  exact key

/-- The bound on vertical strips, uniform in $z$. -/
theorem norm_mellin_latticeTheta_le (h : LatticeThetaInversion) {L lam : ℕ} (ω : DirichletCharacter ℂ L)
    (hL : 1 ≤ L) (hlam : 1 ≤ lam) (σ₁ σ₂ : ℝ) :
    ∃ A B : ℝ, ∀ (z : ℍ) (σ : ℂ), σ₁ ≤ σ.re → σ.re ≤ σ₂ →
      ‖mellin (latticeTheta L lam ω z) σ‖ ≤ B * (z.im ^ A + z.im ^ (-A)) := by
  obtain ⟨n, B, hB⟩ := norm_mellin_le_Q h ω hL hlam σ₁ σ₂
  refine ⟨(n : ℝ), |B| * 2 ^ n, fun z σ h1 h2 => ?_⟩
  have hy := z.im_pos
  have h3 := hB z σ h1 h2
  have h4 := Q_pow_le hy n
  have e1 : z.im ^ (n : ℝ) = z.im ^ n := Real.rpow_natCast _ _
  have e2 : z.im ^ (-(n : ℝ)) = z.im⁻¹ ^ n := by
    rw [Real.rpow_neg hy.le, Real.rpow_natCast, inv_pow]
  rw [e1, e2]
  calc ‖mellin (latticeTheta L lam ω z) σ‖ ≤ B * (z.im + z.im⁻¹) ^ n := h3
    _ ≤ |B| * (z.im + z.im⁻¹) ^ n := by gcongr; exact le_abs_self B
    _ ≤ |B| * (2 ^ n * (z.im ^ n + z.im⁻¹ ^ n)) := by gcongr
    _ = _ := by ring

end ModularFormsKB.Miyake.HeckeTrick
