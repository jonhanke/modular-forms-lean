/-
# The Rankin unfolding in integral weight, level one

For $f, g \in S_k(\mathrm{SL}_2(\mathbb Z))$ with
$q$-expansions $f = \sum a_n q^n$, $g = \sum b_n q^n$ (`coeff`), the kernel $G = y^k\,\bar g\,f$ (Mathlib's
`petersson k g f`) is $\mathrm{SL}_2(\mathbb Z)$-invariant, so the proved unfolding principle
`HalfIntegral.rankinUnfolding` applies with $L = 1$, $\lambda = 0$:
$$\int_{\mathcal F}y^k\bar g f\,E(\cdot,s)\,d\mu = 2\zeta(2s)\,\Gamma(s+k-1)(4\pi)^{-(s+k-1)}\sum_{n\ge1}a_n\bar b_n
n^{-(s+k-1)}\qquad(\operatorname{Re}s > 2),$$
$E(z,s) = y^s\sum'|cz+d|^{-2s}$ the lattice Eisenstein series `eisensteinLattice 1 0 1` (`rankin_unfold_levelOne`).
The strip integral is computed by Parseval on horizontal lines (`integral_conj_mul_line`) and a termwise Mellin
transform (`stripMellin_petersson`).

**Half plane.** Hecke's bound $a_n, b_n = O(n^{k/2})$ gives absolute convergence of $\sum a_n\bar b_n n^{-(s+k-1)}$ for
$\operatorname{Re}s > 2$, which is where the identity is proved; Rankin's theorem gives $\operatorname{Re}s > 1$ (recorded as a loose
end). The continuation (`RankinSelberg/LevelOne.lean`) does not depend on the half plane.
-/
import ModularFormsKB.HalfIntegral.Rankin.Unfolding
import ModularFormsKB.HalfIntegral.Abstract.FourierLine
import ModularFormsKB.RankinSelberg.EisensteinZero
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.LSeries.Dirichlet

open MeasureTheory Set Filter Topology Complex Asymptotics MatrixGroups CongruenceSubgroup
open scoped UpperHalfPlane Real ComplexConjugate

noncomputable section

namespace ModularFormsKB.RankinSelberg

open ModularFormsKB.HalfIntegral ModularFormsKB.Miyake.HeckeTrick UpperHalfPlane

/-! ### Coefficients of level one cusp forms -/

/-- The $q$-expansion coefficient $a_n(f)$ of $f \in S_k(\mathrm{SL}_2(\mathbb Z))$. -/
def coeff {k : ℤ} (f : CuspForm 𝒮ℒ k) (n : ℕ) : ℂ := (UpperHalfPlane.qExpansion 1 f).coeff n

theorem hasQExp_coeff {k : ℤ} (f : CuspForm 𝒮ℒ k) : Abstract.HasQExp f (coeff f) := fun τ ↦ by
  have hp : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    have := Subgroup.strictWidthInfty_mem_strictPeriods (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))
    rwa [Subgroup.strictWidthInfty_SL2Z] at this
  have h := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := f) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f hp) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) τ
  convert h using 2 with m
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **The Rankin–Selberg coefficients** $a_n(f)\,\overline{b_n(g)}$. -/
def rsCoeff {k : ℤ} (f g : CuspForm 𝒮ℒ k) (n : ℕ) : ℂ := coeff f n * conj (coeff g n)

/-! ### The kernel -/

theorem continuous_petersson {k : ℤ} (f g : CuspForm 𝒮ℒ k) : Continuous (petersson k g f) :=
  petersson_continuous k (ModularFormClass.holo g).continuous (ModularFormClass.holo f).continuous

/-- The kernel $y^k\bar gf$ is invariant: the unitary law of weight $0$ and level $1$. -/
theorem unitaryLaw_petersson {k : ℤ} (f g : CuspForm 𝒮ℒ k) :
    UnitaryLaw 1 0 1 (petersson k g f) := by
  intro γ _ τ
  rw [trivialChar_apply, pow_zero, one_mul, one_mul]
  exact SlashInvariantFormClass.petersson_smul (Γ := 𝒮ℒ) (g := (γ : GL (Fin 2) ℝ)) ⟨γ, rfl⟩

/-! ### The strip integral -/

private lemma stripPt_eq_aux {x y : ℝ} (hy : 0 < y) :
    stripPt x y = ⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ := by
  rw [stripPt, dif_pos hy]

private lemma stripPt_im_aux {x y : ℝ} (hy : 0 < y) : (stripPt x y).im = y := by
  rw [stripPt_eq_aux hy]
  show ((x : ℂ) + y * Complex.I).im = y
  simp

private lemma continuous_stripPt_left_aux {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ ↦ stripPt x y := by
  have : (fun x : ℝ ↦ stripPt x y) =
      fun x : ℝ ↦ (⟨(x : ℂ) + y * Complex.I, by simpa using hy⟩ : ℍ) :=
    funext fun x ↦ stripPt_eq_aux hy
  rw [this]
  refine UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr ?_
  show Continuous fun x : ℝ ↦ (x : ℂ) + y * Complex.I
  fun_prop

private lemma continuousOn_stripPt_aux :
    ContinuousOn (fun p : ℝ × ℝ ↦ stripPt p.1 p.2) {p : ℝ × ℝ | 0 < p.2} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : Continuous (fun p : {p : ℝ × ℝ | 0 < p.2} ↦
      (⟨((p.1.1 : ℝ) : ℂ) + (p.1.2 : ℝ) * Complex.I, by
        have : 0 < p.1.2 := p.2
        simpa using this⟩ : ℍ)) :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (by
      show Continuous fun p : {p : ℝ × ℝ | 0 < p.2} ↦ ((p.1.1 : ℝ) : ℂ) + (p.1.2 : ℝ) * Complex.I
      fun_prop)
  convert h using 1
  funext p
  have hp : 0 < p.1.2 := p.2
  simp [Set.domRestrict, stripPt, hp]

private lemma coeff_zero_aux {w : ℤ} (F : CuspForm 𝒮ℒ w) : coeff F 0 = 0 := by
  have hp : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    have := Subgroup.strictWidthInfty_mem_strictPeriods (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))
    rwa [Subgroup.strictWidthInfty_SL2Z] at this
  exact CuspFormClass.qExpansion_coeff_zero F one_pos hp

private lemma coeff_isBigO {k : ℕ} (f : CuspForm 𝒮ℒ (k : ℤ)) :
    (fun n ↦ coeff f n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
  have h := CuspFormClass.qExpansion_isBigO (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) f
  rw [Subgroup.strictWidthInfty_SL2Z] at h
  simpa [coeff] using h

private lemma integrableOn_cpow_exp_aux {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * (y : ℂ)))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := a.re - 1) (p := 1) (b := r)
    (by linarith) one_pos hr
  refine Integrable.mono' h ?_ ?_
  · exact (by fun_prop : Measurable fun y : ℝ ↦
      (y : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * (y : ℂ)))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy ↦ ?_)
    have hy : 0 < y := hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_exp]
    simp [Real.rpow_one]

private lemma norm_integral_aux_aux {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : 0 < r) :
    ∫ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * (y : ℂ)))‖ =
      (1 / r) ^ a.re * Real.Gamma a.re := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy : 0 < y := hy
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_exp]
  simp

private lemma inv_cpow_aux (q : ℝ) (hq : 0 < q) (m : ℕ) (a : ℂ) :
    (1 / ((q * (m : ℝ) : ℝ) : ℂ)) ^ a = (q : ℂ) ^ (-a) * (m : ℂ) ^ (-a) := by
  have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (mul_nonneg hq.le hmr)]; exact Real.pi_pos.ne),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hq.le hmr, Complex.ofReal_natCast, mul_inv,
    Complex.cpow_neg, Complex.cpow_neg]

/-- **Parseval on a horizontal line:** $\int_0^1\overline{g(x+iy)}f(x+iy)\,dx = \sum_n a_n\bar b_n e^{-4\pi ny}$. -/
theorem integral_conj_mul_line {k : ℤ} (f g : CuspForm 𝒮ℒ k) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, conj (g (stripPt x y)) * f (stripPt x y) =
      ∑' n : ℕ, rsCoeff f g n * Real.exp (-4 * π * n * y) := by
  have hq := hasQExp_coeff f
  have hqg := hasQExp_coeff g
  obtain ⟨M, hM⟩ := CuspFormClass.exists_bound (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) g
  have hgc : Continuous g := (ModularFormClass.holo g).continuous
  have hcont := continuous_stripPt_left_aux hy
  have hcoe : ∀ x : ℝ, ((stripPt x y : ℍ) : ℂ) = (x : ℂ) + y * Complex.I := fun x => by
    rw [stripPt_eq_aux hy]
  set F : ℕ → ℝ → ℂ := fun n x ↦ coeff f n * (conj (g (stripPt x y)) *
    cexp (2 * π * Complex.I * n * ((x : ℂ) + y * Complex.I))) with hF
  have hlim : ∀ x : ℝ, HasSum (fun n ↦ F n x) (conj (g (stripPt x y)) * f (stripPt x y)) := by
    intro x
    have h := (hq (stripPt x y)).mul_left (conj (g (stripPt x y)))
    rw [hcoe x] at h
    convert h using 1
    funext n
    simp only [hF]
    ring
  have hB : ∀ x : ℝ, ‖g (stripPt x y)‖ ≤ M / y ^ ((k : ℝ) / 2) := by
    intro x
    have := hM (stripPt x y)
    rwa [stripPt_im_aux hy] at this
  have hnormF : ∀ (n : ℕ) (x : ℝ), ‖F n x‖ ≤
      M / y ^ ((k : ℝ) / 2) * (‖coeff f n‖ * Real.exp (-2 * π * n * y)) := by
    intro n x
    simp only [hF, norm_mul, RCLike.norm_conj, Complex.norm_exp]
    have hre : (2 * π * Complex.I * n * ((x : ℂ) + y * Complex.I)).re = -2 * π * n * y := by
      simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [hre]
    have he := (Real.exp_pos (-2 * π * n * y)).le
    have hh := mul_le_mul_of_nonneg_right (hB x) (mul_nonneg (norm_nonneg (coeff f n)) he)
    nlinarith [hh]
  have hsumm : Summable fun n : ℕ ↦
      M / y ^ ((k : ℝ) / 2) * (‖coeff f n‖ * Real.exp (-2 * π * n * y)) :=
    (summable_of_hasQExp hq hy).mul_left _
  have hFc : ∀ n, Continuous (F n) := fun n ↦ by
    simp only [hF]
    exact continuous_const.mul ((Complex.continuous_conj.comp (hgc.comp hcont)).mul (by fun_prop))
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1) (F := F)
    (f := fun x ↦ conj (g (stripPt x y)) * f (stripPt x y))
    (fun n _ ↦ M / y ^ ((k : ℝ) / 2) * (‖coeff f n‖ * Real.exp (-2 * π * n * y)))
    (fun n ↦ (hFc n).aestronglyMeasurable)
    (fun n ↦ Filter.Eventually.of_forall fun x _ ↦ hnormF n x)
    (Filter.Eventually.of_forall fun x _ ↦ hsumm)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun x _ ↦ hlim x)
  have hval : ∀ n : ℕ, ∫ x in (0 : ℝ)..1, F n x = rsCoeff f g n * Real.exp (-4 * π * n * y) := by
    intro n
    simp only [hF]
    rw [intervalIntegral.integral_const_mul]
    have h := integral_conj_mul_exp_of_hasQExp hqg hy n
    simp only [stripPt_eq_aux hy]
    rw [h]
    simp only [rsCoeff]
    ring
  simp only [hval] at hdom
  exact hdom.tsum_eq.symm

/-- **Integrability on the strip** (the hypothesis of `RankinUnfolding`): $|y^k\bar gf|\,y^{\sigma-2}$ is integrable on
$[0,1]\times(0,\infty)$ for $\sigma > 1$. -/
theorem integrableOn_petersson_strip (k : ℤ) (f g : CuspForm 𝒮ℒ k) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun p : ℝ × ℝ ↦ ‖petersson k g f (stripPt p.1 p.2)‖ * p.2 ^ (σ - 2))
      (Icc 0 1 ×ˢ Ioi 0) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) g f
  obtain ⟨a, ha, hO⟩ := (CuspFormClass.zero_at_infty (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) g
    ).petersson_exp_decay_left k (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) f
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).1 hc
  have hbd : ∃ C' : ℝ, ∀ τ : ℍ, ‖petersson k g f τ‖ ≤ C' * Real.exp (-a * τ.im) := by
    refine ⟨max |c| (|C| * Real.exp (a * A)), fun τ ↦ ?_⟩
    have hexp : 0 < Real.exp (-a * τ.im) := Real.exp_pos _
    by_cases h : A ≤ τ.im
    · have h1 := hA τ h
      simp only [Set.mem_setOf_eq, Real.norm_of_nonneg hexp.le] at h1
      calc ‖petersson k g f τ‖ ≤ c * Real.exp (-a * τ.im) := h1
        _ ≤ |c| * Real.exp (-a * τ.im) := mul_le_mul_of_nonneg_right (le_abs_self c) hexp.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hexp.le
    · push_neg at h
      calc ‖petersson k g f τ‖ ≤ |C| := (hC τ).trans (le_abs_self C)
        _ ≤ |C| * Real.exp (a * A) * Real.exp (-a * τ.im) := by
            rw [mul_assoc, ← Real.exp_add]
            have : 1 ≤ Real.exp (a * A + -a * τ.im) :=
              Real.one_le_exp (by nlinarith [mul_pos ha (sub_pos.2 h)])
            exact le_mul_of_one_le_right (abs_nonneg C) this
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hexp.le
  obtain ⟨C', hC'⟩ := hbd
  have hI : IntegrableOn (fun y : ℝ ↦ y ^ (σ - 2) * Real.exp (-a * y)) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ - 2) (p := 1) (b := a)
      (by linarith) one_pos ha
    refine this.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have hHint : Integrable (fun y : ℝ ↦ C' * (y ^ (σ - 2) * Real.exp (-a * y)))
      (volume.restrict (Ioi (0 : ℝ))) := hI.const_mul C'
  have hprod : IntegrableOn (fun p : ℝ × ℝ ↦ C' * (p.2 ^ (σ - 2) * Real.exp (-a * p.2)))
      (Icc 0 1 ×ˢ Ioi 0) := by
    have := (integrable_const (1 : ℝ) (μ := volume.restrict (Icc (0 : ℝ) 1))).mul_prod hHint
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa using this
  have hGc := continuous_petersson f g
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ ‖petersson k g f (stripPt p.1 p.2)‖ * p.2 ^ (σ - 2))
      (volume.restrict (Icc 0 1 ×ˢ Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Icc.prod measurableSet_Ioi)
    refine ContinuousOn.mono (s := {p : ℝ × ℝ | 0 < p.2}) ?_ (fun p hp ↦ ?_)
    · exact ((hGc.comp_continuousOn continuousOn_stripPt_aux).norm).mul
        ((continuous_snd.continuousOn).rpow_const (fun p hp ↦ Or.inl (ne_of_gt hp)))
    · exact hp.2
  refine Integrable.mono' hprod hmeas ?_
  refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Ioi)).2
    (Filter.Eventually.of_forall ?_)
  rintro ⟨x, y⟩ ⟨-, hy⟩
  have hy : 0 < y := hy
  show ‖‖petersson k g f (stripPt x y)‖ * y ^ (σ - 2)‖ ≤ C' * (y ^ (σ - 2) * Real.exp (-a * y))
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 := hC' (stripPt x y)
  rw [stripPt_im_aux hy] at h1
  calc ‖petersson k g f (stripPt x y)‖ * y ^ (σ - 2)
      ≤ (C' * Real.exp (-a * y)) * y ^ (σ - 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = C' * (y ^ (σ - 2) * Real.exp (-a * y)) := by ring

/-- **The strip identity:** for $\operatorname{Re}s > 2$,
$\int_0^\infty\!\int_0^1 y^k\bar gf\,y^{s-2}\,dx\,dy = \Gamma(s+k-1)(4\pi)^{-(s+k-1)}\sum_n a_n\bar b_n n^{-(s+k-1)}$. -/
theorem stripMellin_petersson (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) {s : ℂ} (hs : 2 < s.re) :
    stripMellin (petersson k g f) s =
      Gamma (s + k - 1) * (4 * π : ℂ) ^ (-(s + k - 1)) * LSeries (rsCoeff f g) (s + k - 1) := by
  obtain ⟨s', hs'⟩ : ∃ s' : ℂ, s' = s + k - 1 := ⟨_, rfl⟩
  rw [← hs']
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hs're : s'.re = s.re + k - 1 := by rw [hs']; simp
  have hs'pos : 0 < s'.re := by rw [hs're]; linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 4 * π := ⟨_, rfl⟩
  have hqpos : 0 < q := by rw [hq]; positivity
  have hc0 : rsCoeff f g 0 = 0 := by simp [rsCoeff, coeff_zero_aux]
  set F : ℕ → ℝ → ℂ := fun n y ↦
    rsCoeff f g n * ((y : ℂ) ^ (s' - 1) * cexp (-(((q * (n : ℝ) : ℝ) : ℂ) * (y : ℂ)))) with hF
  -- Step A: the integrand in y
  have hA : ∀ y : ℝ, 0 < y →
      (∫ x in (0 : ℝ)..1, petersson k g f (stripPt x y)) * (y : ℂ) ^ (s - 2) =
        ∑' n : ℕ, F n y := by
    intro y hy
    have e1 : ∀ u : ℝ, petersson k g f (stripPt u y) =
        conj (g (stripPt u y)) * f (stripPt u y) * (y : ℂ) ^ (k : ℤ) := by
      intro u; unfold petersson; rw [stripPt_im_aux hy]
    simp only [e1]
    rw [intervalIntegral.integral_mul_const, integral_conj_mul_line f g hy, ← tsum_mul_right,
      ← tsum_mul_right]
    refine tsum_congr fun n ↦ ?_
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hyc : (y : ℂ) ^ (k : ℤ) * (y : ℂ) ^ (s - 2) = (y : ℂ) ^ (s' - 1) := by
      rw [zpow_natCast, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hy0]
      congr 1
      rw [hs']; ring
    have hexp : ((Real.exp (-4 * π * n * y) : ℝ) : ℂ) =
        cexp (-(((q * (n : ℝ) : ℝ) : ℂ) * (y : ℂ))) := by
      rw [Complex.ofReal_exp]; congr 1; rw [hq]; push_cast; ring
    simp only [hF]
    rw [hexp]
    linear_combination (rsCoeff f g n * cexp (-(((q * (n : ℝ) : ℝ) : ℂ) * (y : ℂ)))) * hyc
  -- Step B: integrability
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, hc0]
    · have hr : 0 < q * (n : ℝ) := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      exact (integrableOn_cpow_exp_aux hs'pos hr).const_mul (rsCoeff f g n)
  have hnormF : ∀ n : ℕ, 1 ≤ n → ∫ y in Ioi (0 : ℝ), ‖F n y‖ =
      ‖rsCoeff f g n‖ * ((1 / (q * (n : ℝ))) ^ s'.re * Real.Gamma s'.re) := by
    intro n hn
    have hr : 0 < q * (n : ℝ) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    have hn' : ∀ y, ‖F n y‖ = ‖rsCoeff f g n‖ *
        ‖(y : ℂ) ^ (s' - 1) * cexp (-(((q * (n : ℝ) : ℝ) : ℂ) * (y : ℂ)))‖ :=
      fun y ↦ norm_mul _ _
    simp only [hn']
    rw [integral_const_mul, norm_integral_aux_aux hs'pos hr]
  have hnormF0 : ∫ y in Ioi (0 : ℝ), ‖F 0 y‖ = 0 := by simp [hF, hc0]
  have hsum : Summable fun n : ℕ ↦ ∫ y in Ioi (0 : ℝ), ‖F n y‖ := by
    have hf := coeff_isBigO f
    have hg := coeff_isBigO g
    have hg' : (fun n ↦ conj (coeff g n)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
      obtain ⟨C, hC⟩ := hg.bound
      exact IsBigO.of_bound C (hC.mono fun n h ↦ by simpa using h)
    have hO : rsCoeff f g =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) + 1 - 1) := by
      have h : rsCoeff f g =O[atTop]
          fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) * (n : ℝ) ^ ((k : ℝ) / 2) := hf.mul hg'
      refine h.congr_right (fun n ↦ ?_)
      rw [← Real.rpow_add_of_nonneg (Nat.cast_nonneg _) (by positivity) (by positivity)]
      congr 1; ring
    have hLS : LSeriesSummable (rsCoeff f g) s' :=
      LSeriesSummable_of_isBigO_rpow (x := (k : ℝ) + 1) (by rw [hs're]; linarith) hO
    refine ((hLS.norm).mul_left (Real.Gamma s'.re * (1 / q) ^ s'.re)).congr (fun n ↦ ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hnormF0, LSeries.term_zero]
    · rw [hnormF n hn, LSeries.norm_term_eq, if_neg (by omega)]
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      rw [← one_div_mul_one_div, Real.mul_rpow (by positivity) (by positivity),
        Real.div_rpow zero_le_one hnr.le, Real.one_rpow]
      ring
  -- Step C: interchange and evaluation
  have hint : stripMellin (petersson k g f) s = ∑' n : ℕ, ∫ y in Ioi (0 : ℝ), F n y := by
    rw [integral_tsum_of_summable_integral_norm hFint hsum, stripMellin]
    exact setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ hA y hy
  have hval : ∀ n : ℕ, 1 ≤ n → ∫ y in Ioi (0 : ℝ), F n y =
      rsCoeff f g n * ((1 / ((q * (n : ℝ) : ℝ) : ℂ)) ^ s' * Gamma s') := by
    intro n hn
    have hr : 0 < q * (n : ℝ) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    simp only [hF]
    rw [integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi hs'pos hr]
  have h4 : (4 * π : ℂ) = (q : ℂ) := by rw [hq]; push_cast; ring
  rw [hint, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hF, hc0, LSeries.term_zero]
  · rw [hval n hn, LSeries.term_of_ne_zero (by omega), inv_cpow_aux q hqpos n s', h4]
    simp only [Complex.cpow_neg]
    ring

/-! ### The unfolding -/

theorem isGamma0Reps_one : IsGamma0Reps 1 [1] := by
  intro g
  refine ⟨⟨0, by simp⟩, ?_, fun i _ ↦ Fin.ext ?_⟩
  · show g * ([1].get ⟨0, by simp⟩)⁻¹ ∈ Gamma0 1
    rw [CongruenceSubgroup.Gamma0_mem]
    haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
    exact Subsingleton.elim _ _
  · have := i.2
    simp only [List.length_singleton] at this
    show (i : ℕ) = 0
    omega

theorem lSeries_trivialChar {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (1 : DirichletCharacter ℂ 1) n) s = riemannZeta s := by
  have : (fun n : ℕ ↦ (1 : DirichletCharacter ℂ 1) n) = 1 := by
    funext n
    simp
  rw [this, LSeries_one_eq_riemannZeta hs]

/-- **The Rankin unfolding at level one** (Rankin 1939 `rankin1939`, Selberg 1940 `selberg1940` [unverified]): for
$f, g \in S_k(\mathrm{SL}_2(\mathbb Z))$ and $\operatorname{Re}s > 2$,
$\int_{\mathcal F}y^k\bar gf\,E(\cdot,s)\,d\mu = 2\zeta(2s)\Gamma(s+k-1)(4\pi)^{-(s+k-1)}\sum_n a_n\bar b_n n^{-(s+k-1)}$. -/
@[kb "rankin1939" "Rankin's unfolding for level one cusp forms against the weight-0 Eisenstein series [unverified]"]
theorem rankin_unfold_levelOne (k : ℕ) (f g : CuspForm 𝒮ℒ (k : ℤ)) {s : ℂ} (hs : 2 < s.re) :
    ∫ τ in ModularGroup.fd, petersson k g f τ * eisensteinLattice 1 0 1 τ s =
      2 * riemannZeta (2 * s) *
        (Gamma (s + k - 1) * (4 * π : ℂ) ^ (-(s + k - 1)) * LSeries (rsCoeff f g) (s + k - 1)) := by
  have hs1 : 1 < s.re := by linarith
  have h := RankinUnfold.rankinUnfolding.unfold 1 0 1 [1] le_rfl isGamma0Reps_one (petersson k g f)
    (continuous_petersson f g) (unitaryLaw_petersson f g) s hs1
    (integrableOn_petersson_strip k f g hs1)
  have e : repsIntegral [1] (fun τ ↦ petersson k g f τ * eisensteinLattice 1 0 1 τ s) =
      ∫ τ in ModularGroup.fd, petersson k g f τ * eisensteinLattice 1 0 1 τ s := by
    simp [repsIntegral]
  rw [← e, h, stripMellin_petersson k f g hs,
    lSeries_trivialChar (by simp; linarith)]

end ModularFormsKB.RankinSelberg
