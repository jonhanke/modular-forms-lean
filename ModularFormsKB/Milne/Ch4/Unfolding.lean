import ModularFormsKB.Milne.Ch4.PoincareModular
import ModularFormsKB.Milne.Ch4.EisensteinGammaN
import TauCeti.NumberTheory.ModularForms.Petersson.Adjoint
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: unfolding (Theorem 4.33 and Remark 4.38 (b))

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 4, pdf pp. 64-66.

The Petersson product of a cusp form $f$ with the Poincaré series $\varphi_n$ is computed by the unfolding method:
the integral over a fundamental domain $D$ of $\Gamma$ of $\sum_{\gamma\in\Gamma_\infty\backslash\Gamma}F(\gamma z)$,
with $F = f\,\overline{e_n}\,y^{2k}$, equals the integral of $F$ over the strip $0\le x<h$ (`unfolding_core`,
`milnePetersson_poincare_eq_strip`). That strip integral is computed from the Fourier coefficient on each horizontal
line and a Gamma integral (`integral_unfoldIntegrand`). Remark 4.38 (b) follows from the case $n=0$, where the strip
integral vanishes since $a_0=0$, together with $E_a = c\cdot\varphi_0|\sigma$ and the adjointness of slashing by
$\sigma$ (`eisensteinCuspOrthogonal_of_zero`).

## Items
- Theorem 4.33 (`poincarePetersson`; the formula holds for all $n\ge0$, `integral_unfoldIntegrand`).
- Remark 4.38 (b) (`eisensteinCuspOrthogonal`).
-/

open UpperHalfPlane Complex Filter Topology ModularForm ModularGroup MeasureTheory
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Classical ComplexConjugate Pointwise Matrix

noncomputable section

namespace ModularFormsKB.Milne

variable (Γ : Subgroup SL(2, ℤ))

/-- The vertical strip `0 ≤ Re z < h`, a fundamental domain for translation by `h`. -/
def stripSet (h : ℝ) : Set ℍ := {z | 0 ≤ z.re ∧ z.re < h}

/-- The strip as a subset of `ℂ`. -/
def stripTarget (h : ℝ) : Set ℂ := {w | 0 < w.im ∧ 0 ≤ w.re ∧ w.re < h}

private lemma measurableSet_stripTarget (h : ℝ) : MeasurableSet (stripTarget h) := by
  have h1 : MeasurableSet {w : ℂ | 0 < w.im} := measurableSet_lt measurable_const Complex.measurable_im
  have h2 : MeasurableSet {w : ℂ | 0 ≤ w.re} := measurableSet_le measurable_const Complex.measurable_re
  have h3 : MeasurableSet {w : ℂ | w.re < h} := measurableSet_lt Complex.measurable_re measurable_const
  exact h1.inter (h2.inter h3)

private lemma stripTarget_subset_range (h : ℝ) : stripTarget h ⊆ Set.range UpperHalfPlane.coe := by
  intro w hw
  exact ⟨⟨w, hw.1⟩, rfl⟩

private lemma preimage_stripTarget (h : ℝ) : UpperHalfPlane.coe ⁻¹' stripTarget h = stripSet h := by
  ext z
  simp [stripTarget, stripSet, z.im_pos]

private lemma measurableSet_stripSet (h : ℝ) : MeasurableSet (stripSet h) := by
  rw [← preimage_stripTarget]
  exact measurable_coe (measurableSet_stripTarget h)

/-- The density, as a function on `ℍ`. -/
private lemma density_continuous :
    Continuous fun z : ℍ ↦ (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal) := by
  refine ENNReal.continuous_coe.comp ?_
  refine .pow (.div₀ continuous_const ?_ ?_) _
  · exact continuous_im.subtype_mk _
  · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero

private lemma density_toReal (z : ℍ) :
    ((((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal)).toReal = (z.im ^ 2)⁻¹ := by
  rw [ENNReal.coe_toReal]
  simp

/-- The pulled-back integrand on `ℂ`. -/
def stripG (F : ℍ → ℂ) : ℂ → ℂ := fun w ↦ ((w.im ^ 2)⁻¹ : ℝ) • F (ofComplex w)

private lemma stripG_coe (F : ℍ → ℂ) (z : ℍ) : stripG F (z : ℂ) = ((z.im ^ 2)⁻¹ : ℝ) • F z := by
  simp [stripG, ofComplex_apply]

private lemma setIntegral_stripSet_eq (h : ℝ) (F : ℍ → ℂ) :
    ∫ z in stripSet h, F z = ∫ w in stripTarget h, stripG F w := by
  rw [volume_def, setIntegral_withDensity_eq_setIntegral_toReal_smul density_continuous.measurable
    (Filter.Eventually.of_forall fun z ↦ ENNReal.coe_lt_top) _ (measurableSet_stripSet h)]
  simp_rw [density_toReal]
  have he := measurableEmbedding_coe
  have h1 : ∫ w in stripTarget h, stripG F w = ∫ w in stripTarget h, stripG F w ∂(Measure.map UpperHalfPlane.coe
      (volume.comap UpperHalfPlane.coe)) := by
    rw [he.map_comap, Measure.restrict_restrict (measurableSet_stripTarget h),
      Set.inter_eq_left.mpr (stripTarget_subset_range h)]
  rw [h1, he.setIntegral_map, preimage_stripTarget]
  refine setIntegral_congr_fun (measurableSet_stripSet h) fun z _ ↦ ?_
  simp only [stripG_coe]

private lemma integrableOn_stripSet_iff (h : ℝ) (F : ℍ → ℂ) :
    IntegrableOn F (stripSet h) ↔ IntegrableOn (stripG F) (stripTarget h) := by
  have he := measurableEmbedding_coe
  rw [he.integrableOn_iff_comap (stripTarget_subset_range h), preimage_stripTarget]
  unfold IntegrableOn
  rw [volume_def, restrict_withDensity (measurableSet_stripSet h),
    integrable_withDensity_iff_integrable_smul' density_continuous.measurable
      (Filter.Eventually.of_forall fun z ↦ ENNReal.coe_lt_top)]
  simp_rw [density_toReal]
  refine integrable_congr ?_
  exact Filter.Eventually.of_forall fun z ↦ by simp [stripG_coe]


/-- The integrand on `ℝ × ℝ`. -/
def stripH (h : ℝ) (F : ℍ → ℂ) : ℝ × ℝ → ℂ :=
  (Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ)).indicator fun p ↦
    ((p.2 ^ 2)⁻¹ : ℝ) • F (ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))

private lemma stripH_eq (h : ℝ) (F : ℍ → ℂ) (p : ℝ × ℝ) :
    stripH h F p = (stripTarget h).indicator (stripG F) (Complex.measurableEquivRealProd.symm p) := by
  have hw : (Complex.measurableEquivRealProd.symm p) = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hw]
  unfold stripH
  by_cases hp : p ∈ Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ)
  · have hm : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ stripTarget h := by
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      simp only [stripTarget, Set.mem_ofPred_eq]
      simpa using ⟨h3, h1, h2⟩
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hm]
    simp [stripG]
  · have hm : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∉ stripTarget h := by
      intro hm
      apply hp
      simp only [stripTarget, Set.mem_ofPred_eq] at hm
      simp at hm
      obtain ⟨h3, h1, h2⟩ := hm
      exact ⟨⟨h1, h2⟩, h3⟩
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hm]

private lemma integral_stripH (h : ℝ) (F : ℍ → ℂ) :
    ∫ p, stripH h F p = ∫ w in stripTarget h, stripG F w := by
  rw [← integral_indicator (measurableSet_stripTarget h)]
  simp_rw [stripH_eq]
  exact (Complex.volume_preserving_equiv_real_prod.symm).integral_comp' (g := (stripTarget h).indicator (stripG F))

private lemma integrable_stripH_iff (h : ℝ) (F : ℍ → ℂ) :
    Integrable (stripH h F) ↔ IntegrableOn F (stripSet h) := by
  rw [integrableOn_stripSet_iff, ← integrable_indicator_iff (measurableSet_stripTarget h)]
  have : stripH h F = (stripTarget h).indicator (stripG F) ∘ Complex.measurableEquivRealProd.symm := by
    funext p; exact stripH_eq h F p
  rw [this]
  exact (Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding

/-- (M) Fubini on the strip. -/
theorem integral_stripSet {h : ℝ} (hh : 0 < h) (F : ℍ → ℂ) (hF : IntegrableOn F (stripSet h)) :
    ∫ z in stripSet h, F z =
      ∫ y in Set.Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) •
        ∫ x in (0 : ℝ)..h, F (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [setIntegral_stripSet_eq, ← integral_stripH, Measure.volume_eq_prod,
    integral_prod_symm _ ((integrable_stripH_iff h F).mpr hF)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi (0 : ℝ))]
  · refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    rw [intervalIntegral.integral_of_le hh.le, ← integral_Ico_eq_integral_Ioc,
      ← integral_smul, ← integral_indicator measurableSet_Ico]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [stripH]
    by_cases hx : x ∈ Set.Ico 0 h
    · rw [Set.indicator_of_mem (show (x, y) ∈ Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ) from ⟨hx, hy⟩),
        Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (show (x, y) ∉ Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ) from
        fun hm ↦ hx hm.1), Set.indicator_of_notMem hx]
  · intro y hy
    have hy' : ¬ 0 < y := hy
    have : ∀ x : ℝ, stripH h F (x, y) = 0 := fun x ↦ by
      refine Set.indicator_of_notMem ?_ _
      intro hm
      exact hy' hm.2
    simp only [this, integral_zero]

private lemma continuousOn_ofComplex' : ContinuousOn ofComplex {w : ℂ | 0 < w.im} := by
  rw [continuousOn_iff_continuous_domRestrict]
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  have : (UpperHalfPlane.coe ∘ {w : ℂ | 0 < w.im}.domRestrict ofComplex) =
      fun w : {w : ℂ | 0 < w.im} => (w : ℂ) := by
    funext w
    simp [Set.domRestrict, ofComplex_apply_of_im_pos w.2]
  rw [this]
  exact continuous_subtype_val

private lemma continuousOn_stripH (h : ℝ) {F : ℍ → ℂ} (hF : Continuous F) :
    ContinuousOn (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ) • F (ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))
      (Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ)) := by
  have hc : Continuous fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have h1 : ContinuousOn (fun p : ℝ × ℝ => F (ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))
      (Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ)) := by
    refine hF.comp_continuousOn (continuousOn_ofComplex'.comp hc.continuousOn ?_)
    intro p hp
    simpa using hp.2
  have h2 : ContinuousOn (fun p : ℝ × ℝ => ((p.2 ^ 2)⁻¹ : ℝ)) (Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ)) := by
    have hsq : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ 2) (Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ)) :=
      (continuous_snd.pow 2).continuousOn
    refine hsq.inv₀ fun p hp => ?_
    have : 0 < p.2 := hp.2
    positivity
  exact h2.smul h1

/-- (M) Integrability on the strip from a bound in terms of the height. -/
theorem integrableOn_stripSet_of_bound {h : ℝ} (_hh : 0 < h) {F : ℍ → ℂ} (hF : Continuous F)
    {b : ℝ → ℝ} (hb : IntegrableOn (fun y : ℝ => b y / y ^ 2) (Set.Ioi 0))
    (hFb : ∀ z ∈ stripSet h, ‖F z‖ ≤ b z.im) : IntegrableOn F (stripSet h) := by
  rw [← integrable_stripH_iff]
  let B : ℝ × ℝ → ℝ := (Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ)).indicator fun p ↦ b p.2 / p.2 ^ 2
  have hB : Integrable B := by
    unfold B
    rw [integrable_indicator_iff (measurableSet_Ico.prod measurableSet_Ioi)]
    rw [Measure.volume_eq_prod, IntegrableOn, ← Measure.prod_restrict]
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ico 0 h)) :=
      integrableOn_const (by simp)
    have := Integrable.mul_prod h1 hb
    simpa using this
  refine hB.mono' ?_ ?_
  · unfold stripH
    rw [aestronglyMeasurable_indicator_iff (measurableSet_Ico.prod measurableSet_Ioi)]
    exact (continuousOn_stripH h hF).aestronglyMeasurable (measurableSet_Ico.prod measurableSet_Ioi)
  · refine Filter.Eventually.of_forall fun p ↦ ?_
    by_cases hp : p ∈ Set.Ico 0 h ×ˢ Set.Ioi (0 : ℝ)
    · have hy : 0 < p.2 := hp.2
      have hz : ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ stripSet h := by
        have him : 0 < ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im := by simpa using hy
        simp only [stripSet, Set.mem_ofPred_eq, UpperHalfPlane.re, ofComplex_apply_of_im_pos him]
        simpa using hp.1
      have him : (ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).im = p.2 := by
        have him : 0 < ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im := by simpa using hy
        simp [ofComplex_apply_of_im_pos him]
      simp only [stripH, B, Set.indicator_of_mem hp]
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have := hFb _ hz
      rw [him] at this
      calc ((p.2 ^ 2)⁻¹) * ‖F (ofComplex ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))‖
          ≤ (p.2 ^ 2)⁻¹ * b p.2 := by gcongr
        _ = b p.2 / p.2 ^ 2 := by ring
    · simp [stripH, B, Set.indicator_of_notMem hp]

/-- The unfolding integrand `F(z) = f(z) conj(e_n(z)) y^{2k}`. -/
def unfoldIntegrand (k n : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  petersson (2 * (k : ℤ)) (expTerm Γ n) f
private lemma conj_expTerm (n : ℕ) {x y : ℝ} (hy : 0 < y) :
    conj (expTerm Γ n (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) =
      (Real.exp (-4 * π * n * y / widthAtInfty Γ) : ℂ) *
        (1 / Function.Periodic.qParam (widthAtInfty Γ) ((x : ℂ) + (y : ℂ) * Complex.I) ^ n) := by
  have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  unfold expTerm
  rw [ofComplex_apply_of_im_pos him]
  rw [← Complex.exp_conj, Function.Periodic.qParam, ← Complex.exp_nat_mul, one_div,
    ← Complex.exp_neg, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_div₀, map_mul, map_add, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    Complex.conj_natCast, Complex.conj_ofReal]
  push_cast
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (4 * (π : ℂ) * n * y / (widthAtInfty Γ : ℂ)) * this

private lemma line_integral [Γ.FiniteIndex] {k : ℕ} (n : ℕ)
    (f : CuspForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..widthAtInfty Γ, unfoldIntegrand Γ k n f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) =
      (widthAtInfty Γ : ℂ) * (qExpansion (widthAtInfty Γ) f).coeff n *
        ((Real.exp (-4 * π * n * y / widthAtInfty Γ) : ℂ) * (y : ℂ) ^ (2 * k)) := by
  have hh : 0 < widthAtInfty Γ := Subgroup.widthInfty_pos _
  have : Fact (IsCusp OnePoint.infty (Γ.map (mapGL ℝ))) := inferInstance
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) (widthAtInfty Γ) :=
    UpperHalfPlane.periodic_comp_ofComplex (cuspForm_vadd_width Γ f)
  have hcoef := UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral hh hper
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n hy
  have hint : ∀ x : ℝ, unfoldIntegrand Γ k n f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) =
      ((Real.exp (-4 * π * n * y / widthAtInfty Γ) : ℂ) * (y : ℂ) ^ (2 * k)) *
        (1 / Function.Periodic.qParam (widthAtInfty Γ) ((x : ℂ) + (y : ℂ) * Complex.I) ^ n *
          f ⟨(x : ℂ) + (y : ℂ) * Complex.I, by simpa using hy⟩) := by
    intro x
    have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
    unfold unfoldIntegrand petersson
    rw [conj_expTerm Γ n hy, ofComplex_apply_of_im_pos him]
    have : (UpperHalfPlane.im ⟨(x : ℂ) + (y : ℂ) * Complex.I, him⟩) = y := by simp
    rw [this]
    have h2 : ((y : ℂ)) ^ (2 * (k : ℤ)) = (y : ℂ) ^ (2 * k) := by
      rw [← zpow_natCast]; push_cast; rfl
    rw [h2]; ring
  simp_rw [hint]
  rw [intervalIntegral.integral_const_mul]
  have hc : (widthAtInfty Γ : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hcoef' : ∫ x in (0 : ℝ)..widthAtInfty Γ, 1 / Function.Periodic.qParam (widthAtInfty Γ) ((x : ℂ) + (y : ℂ) * Complex.I) ^ n * f ⟨(x : ℂ) + (y : ℂ) * Complex.I, by simpa using hy⟩ = (widthAtInfty Γ : ℂ) * (qExpansion (widthAtInfty Γ) f).coeff n := by
    rw [hcoef]
    simp only [UpperHalfPlane.coe_I]
    field_simp
  rw [hcoef']
  ring

private lemma norm_expTerm_le (n : ℕ) (z : ℍ) : ‖expTerm Γ n z‖ ≤ 1 := by
  have hh : 0 ≤ widthAtInfty Γ := Subgroup.widthInfty_nonneg _
  unfold expTerm
  rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.div_ofReal_re]
  apply div_nonpos_of_nonpos_of_nonneg _ hh
  have := z.im_pos
  simp only [mul_re, mul_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  have : (0 : ℝ) ≤ π * n * z.im := by positivity
  nlinarith

private lemma norm_unfoldIntegrand_le (k n : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    ‖unfoldIntegrand Γ k n f z‖ ≤ ‖f z‖ * z.im ^ (2 * k) := by
  have h2 : (2 * (k : ℤ)) = ((2 * k : ℕ) : ℤ) := by push_cast; ring
  unfold unfoldIntegrand petersson
  rw [h2, norm_mul, norm_mul, zpow_natCast, norm_pow, Complex.norm_real, Real.norm_of_nonneg z.im_pos.le,
    RCLike.norm_conj]
  have := norm_expTerm_le Γ n z
  have h3 : 0 ≤ ‖f z‖ * z.im ^ (2 * k) := by positivity
  nlinarith [norm_nonneg (expTerm Γ n z), norm_nonneg (f z)]

private lemma continuous_unfoldIntegrand (k n : ℕ) {f : ℍ → ℂ} (hf : Continuous f) :
    Continuous (unfoldIntegrand Γ k n f) :=
  petersson_continuous _ (expTerm_mdifferentiable Γ n).continuous hf

private lemma cusp_bound_left [Γ.FiniteIndex] {k : ℕ} (f : CuspForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) :
    ∃ C : ℝ, ∀ z : ℍ, ‖f z‖ * z.im ^ k ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C, fun z => ?_⟩
  have h1 := hC z
  have h2 : ((((2 * k : ℕ) : ℤ) : ℝ) / 2) = (k : ℝ) := by push_cast; ring
  rw [h2, Real.rpow_natCast] at h1
  have hp : 0 < z.im ^ k := pow_pos z.im_pos k
  rw [le_div_iff₀ hp] at h1
  exact h1

private lemma cusp_bound_decay [Γ.FiniteIndex] {k : ℕ} (f : CuspForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) :
    ∃ C A : ℝ, 0 ≤ C ∧ ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C * Real.exp (-2 * π * z.im / widthAtInfty Γ) := by
  have hh : 0 < widthAtInfty Γ := Subgroup.widthInfty_pos _
  have : Fact (IsCusp OnePoint.infty (Γ.map (mapGL ℝ))) := inferInstance
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) (widthAtInfty Γ) :=
    UpperHalfPlane.periodic_comp_ofComplex (cuspForm_vadd_width Γ f)
  have hO := UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty (CuspFormClass.zero_at_infty f) hh hper
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  refine ⟨|C|, A, abs_nonneg _, fun z hz => ?_⟩
  have : ‖f z‖ ≤ C * ‖Real.exp (-2 * π * z.im / widthAtInfty Γ)‖ := hA z hz
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)

theorem integrableOn_unfoldIntegrand [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (n : ℕ)
    (f : CuspForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) :
    IntegrableOn (unfoldIntegrand Γ k n f) (stripSet (widthAtInfty Γ)) := by
  have hh : 0 < widthAtInfty Γ := Subgroup.widthInfty_pos _
  obtain ⟨C1', hC1'⟩ := cusp_bound_left Γ f
  obtain ⟨C2, A, hC2, hA⟩ := cusp_bound_decay Γ f
  set C1 := |C1'| with hC1def
  have hC1 : ∀ z : ℍ, ‖f z‖ * z.im ^ k ≤ C1 := fun z => (hC1' z).trans (le_abs_self _)
  set A' := max A 1 with hA'
  have hA'pos : 0 < A' := lt_of_lt_of_le one_pos (le_max_right _ _)
  let b : ℝ → ℝ := fun y => if y ≤ A' then C1 * y ^ k else C2 * Real.exp (-2 * π * y / widthAtInfty Γ) * y ^ (2 * k)
  have hFb : ∀ z ∈ stripSet (widthAtInfty Γ), ‖unfoldIntegrand Γ k n f z‖ ≤ b z.im := by
    intro z _
    have h1 := norm_unfoldIntegrand_le Γ k n f z
    by_cases hz : z.im ≤ A'
    · simp only [b, hz, ite_true]
      refine h1.trans ?_
      have : ‖f z‖ * z.im ^ (2 * k) = (‖f z‖ * z.im ^ k) * z.im ^ k := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (hC1 z) (pow_nonneg z.im_pos.le _)
    · simp only [b, hz, ite_false]
      refine h1.trans ?_
      have hAz : A ≤ z.im := (le_max_left _ _).trans (not_le.mp hz).le
      exact mul_le_mul_of_nonneg_right (hA z hAz) (pow_nonneg z.im_pos.le _)
  have hb : IntegrableOn (fun y : ℝ => b y / y ^ 2) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hA'pos.le, integrableOn_union]
    constructor
    · have : IntegrableOn (fun y : ℝ => C1 * y ^ (k - 2)) (Set.Ioc 0 A') :=
        (Continuous.integrableOn_Ioc (by fun_prop))
      refine this.congr_fun (fun y hy => ?_) measurableSet_Ioc
      have hy0 : 0 < y := hy.1
      simp only [b, hy.2, ite_true]
      have : y ^ k = y ^ (k - 2) * y ^ 2 := by rw [← pow_add]; congr 1; omega
      rw [this]
      field_simp
    · have hint : IntegrableOn (fun y : ℝ => y ^ ((2 * k - 2 : ℕ) : ℝ) *
          Real.exp (-(2 * π / widthAtInfty Γ) * y ^ (1 : ℝ))) (Set.Ioi 0) :=
        integrableOn_rpow_mul_exp_neg_mul_rpow (by
          have : (0 : ℝ) ≤ ((2 * k - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith) one_pos (by positivity)
      have hint' : IntegrableOn (fun y : ℝ => C2 * (y ^ ((2 * k - 2 : ℕ) : ℝ) *
          Real.exp (-(2 * π / widthAtInfty Γ) * y ^ (1 : ℝ)))) (Set.Ioi A') :=
        (hint.mono_set (Set.Ioi_subset_Ioi hA'pos.le)).const_mul C2
      refine IntegrableOn.congr_fun hint' (fun y hy => ?_) measurableSet_Ioi
      have hy0 : 0 < y := lt_trans hA'pos hy
      have hnot : ¬ y ≤ A' := not_le.mpr hy
      simp only [b, hnot, ite_false]
      rw [Real.rpow_natCast, Real.rpow_one]
      have : y ^ (2 * k) = y ^ (2 * k - 2) * y ^ 2 := by rw [← pow_add]; congr 1; omega
      rw [this]
      have e : -(2 * π / widthAtInfty Γ) * y = -2 * π * y / widthAtInfty Γ := by ring
      rw [e]
      field_simp
  exact integrableOn_stripSet_of_bound hh
    (continuous_unfoldIntegrand Γ k n (ModularFormClass.continuous f)) hb hFb

private lemma strip_gamma (m n : ℕ) (hn : 1 ≤ n) {h : ℝ} (hh : 0 < h) :
    ∫ y in Set.Ioi (0 : ℝ), Real.exp (-4 * π * n * y / h) * y ^ m =
      (m.factorial : ℝ) * (h / (4 * π * n)) ^ (m + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 < 4 * π * n / h := by positivity
  have ha : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have H := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr
  rw [add_sub_cancel_right] at H
  have e : ∀ y : ℝ, Real.exp (-4 * π * n * y / h) * y ^ m =
      y ^ (m : ℝ) * Real.exp (-(4 * π * n / h * y)) := by
    intro y
    rw [Real.rpow_natCast, mul_comm]
    congr 2
    ring
  simp_rw [e]
  rw [H, Real.Gamma_nat_eq_factorial, show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast, one_div_div]
  ring

theorem integral_unfoldIntegrand [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (n : ℕ)
    (f : CuspForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) :
    ∫ z in stripSet (widthAtInfty Γ), unfoldIntegrand Γ k n f z =
      (widthAtInfty Γ : ℂ) ^ (2 * k) * (2 * k - 2).factorial / (4 * π : ℂ) ^ (2 * k - 1) *
        (n : ℂ) ^ (1 - 2 * (k : ℤ)) * (qExpansion (widthAtInfty Γ) f).coeff n := by
  have hh : 0 < widthAtInfty Γ := Subgroup.widthInfty_pos _
  have hint := integrableOn_unfoldIntegrand Γ hk n f
  rw [integral_stripSet hh _ hint]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (qExpansion (widthAtInfty Γ) f).coeff 0 = 0 := by
      simp [qExpansion_coeff, (CuspFormClass.zero_at_infty f).cuspFunction_apply_zero hh]
    rw [h0, mul_zero]
    have : ∀ y ∈ Set.Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) •
        ∫ x in (0 : ℝ)..widthAtInfty Γ, unfoldIntegrand Γ k 0 f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))
        = 0 := by
      intro y hy
      rw [line_integral Γ 0 f hy, h0]
      simp
    rw [setIntegral_congr_fun measurableSet_Ioi this]
    simp
  · have hG : ∀ y ∈ Set.Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) •
        ∫ x in (0 : ℝ)..widthAtInfty Γ, unfoldIntegrand Γ k n f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))
        = ((widthAtInfty Γ : ℂ) * (qExpansion (widthAtInfty Γ) f).coeff n) *
          ((Real.exp (-4 * π * n * y / widthAtInfty Γ) * y ^ (2 * k - 2) : ℝ) : ℂ) := by
      intro y hy
      have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
      rw [line_integral Γ n f hy, Complex.real_smul]
      push_cast
      rw [show (y : ℂ) ^ (2 * k) = (y : ℂ) ^ (2 * k - 2) * (y : ℂ) ^ 2 by
        rw [← pow_add]; congr 1; omega]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hG, integral_const_mul, integral_complex_ofReal,
      strip_gamma (2 * k - 2) n hn hh]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have e1 : 2 * (j + 2) - 2 = 2 * j + 2 := by omega
    have e2 : 2 * (j + 2) - 1 = 2 * j + 3 := by omega
    have e3 : (1 - 2 * ((j + 2 : ℕ) : ℤ)) = -((2 * j + 3 : ℕ) : ℤ) := by push_cast; ring
    have e4 : 2 * (j + 2) = 2 * j + 4 := by omega
    rw [e1, e2, e3, zpow_neg, zpow_natCast]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    have key : ∀ (hC Pc N a F : ℂ), hC ≠ 0 → Pc ≠ 0 → N ≠ 0 → ∀ m : ℕ,
        hC * a * (F * (hC / (Pc * N)) ^ (m + 1)) = hC ^ (m + 2) * F / Pc ^ (m + 1) * (N ^ (m + 1))⁻¹ * a := by
      intro hC Pc N a F h1 h2 h3 m
      rw [div_pow, mul_pow]
      field_simp
      ring
    exact key (widthAtInfty Γ : ℂ) (4 * π) n _ _ (by exact_mod_cast hh.ne') (mul_ne_zero (by norm_num) hpi)
      hnC (2 * j + 2)

/-- The width is a positive integer `m`, and `±T^m ∈ Γ`. -/
private lemma exists_width_nat [Γ.FiniteIndex] : ∃ m : ℕ, 0 < m ∧ (m : ℝ) = widthAtInfty Γ ∧
    (ModularGroup.T ^ (m : ℤ) ∈ Γ ∨ -(ModularGroup.T ^ (m : ℤ)) ∈ Γ) := by
  have hper : widthAtInfty Γ ∈ (Γ.map (mapGL ℝ)).periods := Subgroup.widthInfty_mem_periods _
  have hpos : 0 < widthAtInfty Γ := Subgroup.widthInfty_pos _
  simp only [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff] at hper
  rcases hper with h | h
  · obtain ⟨δ, hδ, hδe⟩ := Subgroup.mem_map.mp h
    have e01 : ((δ 0 1 : ℤ) : ℝ) = widthAtInfty Γ := by
      have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hδe
      simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using this
    have e00 : ((δ 0 0 : ℤ) : ℝ) = 1 := by
      have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) hδe
      simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using this
    have e10 : ((δ 1 0 : ℤ) : ℝ) = 0 := by
      have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) hδe
      simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using this
    have e11 : ((δ 1 1 : ℤ) : ℝ) = 1 := by
      have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hδe
      simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using this
    have e00' : δ 0 0 = 1 := by exact_mod_cast e00
    have e10' : δ 1 0 = 0 := by exact_mod_cast e10
    have e11' : δ 1 1 = 1 := by exact_mod_cast e11
    have hpos' : 0 < δ 0 1 := by
      have : (0 : ℝ) < (δ 0 1 : ℤ) := by rw [e01]; exact hpos
      exact_mod_cast this
    refine ⟨(δ 0 1).toNat, by omega, ?_, Or.inl ?_⟩
    · rw [← e01]; norm_cast; omega
    · have : δ = ModularGroup.T ^ ((δ 0 1).toNat : ℤ) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ModularGroup.coe_T_zpow, e00', e10', e11', Int.toNat_of_nonneg hpos'.le]
      rw [← this]; exact hδ
  · obtain ⟨δ, hδ, hδe⟩ := Subgroup.mem_map.mp h
    have e01 : ((δ 0 1 : ℤ) : ℝ) = -widthAtInfty Γ := by
      have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hδe
      simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using this
    have e00 : ((δ 0 0 : ℤ) : ℝ) = -1 := by
      have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0) hδe
      simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using this
    have e10 : ((δ 1 0 : ℤ) : ℝ) = 0 := by
      have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) hδe
      simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using this
    have e11 : ((δ 1 1 : ℤ) : ℝ) = -1 := by
      have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hδe
      simpa [Matrix.GeneralLinearGroup.upperRightHom_apply] using this
    have e00' : δ 0 0 = -1 := by exact_mod_cast e00
    have e10' : δ 1 0 = 0 := by exact_mod_cast e10
    have e11' : δ 1 1 = -1 := by exact_mod_cast e11
    have hpos' : δ 0 1 < 0 := by
      have : ((δ 0 1 : ℤ) : ℝ) < 0 := by rw [e01]; linarith
      exact_mod_cast this
    refine ⟨(-(δ 0 1)).toNat, by omega, ?_, Or.inr ?_⟩
    · have : ((-(δ 0 1) : ℤ) : ℝ) = widthAtInfty Γ := by push_cast; rw [e01]; ring
      rw [← this]; norm_cast; omega
    · have : δ = -(ModularGroup.T ^ ((-(δ 0 1)).toNat : ℤ)) := by
        ext i j
        rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
        fin_cases i <;> fin_cases j <;>
          simp [e00', e10', e11', Int.toNat_of_nonneg (by omega : 0 ≤ -(δ 0 1))]
      rw [← this]; exact hδ

/-- The image of `Γ` in `PSL(2, ℤ)`. -/
abbrev Kgrp : Subgroup PSL(2, ℤ) := Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- `Γ → K`. -/
def psi : Γ →* Kgrp Γ :=
  ((QuotientGroup.mk' (Subgroup.center SL(2, ℤ))).comp Γ.subtype).codRestrict (Kgrp Γ)
    (fun γ => ⟨γ, γ.2, rfl⟩)

private lemma psi_coe (β : Γ) : ((psi Γ β : Kgrp Γ) : PSL(2, ℤ)) = ((β : SL(2, ℤ)) : PSL(2, ℤ)) := rfl

private lemma psi_smul (β : Γ) (z : ℍ) : (psi Γ β) • z = (β : SL(2, ℤ)) • z := rfl

/-- The image of `Γ_∞` in `K`. -/
def Hgrp : Subgroup (Kgrp Γ) := (stabInfty Γ).map (psi Γ)

private lemma pslMk_neg' (x : SL(2, ℤ)) : (((-x : SL(2, ℤ))) : PSL(2, ℤ)) = (x : PSL(2, ℤ)) := by
  rw [← mul_neg_one x]
  have : (((-1 : SL(2, ℤ))) : PSL(2, ℤ)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
    right; rfl
  rw [QuotientGroup.mk_mul, this, mul_one]

private lemma exists_T_zpow' (β : SL(2, ℤ)) (h10 : β 1 0 = 0) :
    ∃ t : ℤ, β = ModularGroup.T ^ t ∨ β = -(ModularGroup.T ^ t) := by
  obtain ⟨ε, hε, h00, h11⟩ := sl_lower_zero β h10
  rcases hε with rfl | rfl
  · refine ⟨β 0 1, Or.inl ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, h00, h10, h11]
  · refine ⟨-(β 0 1), Or.inr ?_⟩
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

/-- The image of `Γ` in `GL(2, ℝ)` is discrete. -/
local instance discreteImage' : DiscreteTopology (Γ.map (mapGL ℝ)) :=
  DiscreteTopology.of_subset
    (s := ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range : Set (GL (Fin 2) ℝ)))
    (inferInstance : DiscreteTopology (MonoidHom.range (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)))
    (by
      rintro _ ⟨g, _, rfl⟩
      exact ⟨g, rfl⟩)

/-- Elements of `Γ_∞` are `±T^(m j)`; in `PSL` they are `T^(m j)`. -/
private lemma stab_eq_T [Γ.FiniteIndex] {m : ℕ} (hm : (m : ℝ) = widthAtInfty Γ) {β : Γ}
    (hβ : β ∈ stabInfty Γ) :
    ∃ j : ℤ, ((β : SL(2, ℤ)) : PSL(2, ℤ)) =
      ((ModularGroup.T ^ ((m : ℤ) * j) : SL(2, ℤ)) : PSL(2, ℤ)) := by
  have h10 : (β : SL(2, ℤ)) 1 0 = 0 := hβ
  obtain ⟨ε, hε, h00, h11⟩ := sl_lower_zero _ h10
  have hper := stabInfty_period Γ β.2 hε h00 h11 h10
  have hdisc : DiscreteTopology (Γ.map (mapGL ℝ)).periods := inferInstance
  rw [Subgroup.periods_eq_zmultiples_widthInfty] at hper
  obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp hper
  have hh : (Γ.map (mapGL ℝ)).widthInfty = widthAtInfty Γ := rfl
  rw [hh, ← hm] at hj
  have hj' : j * (m : ℤ) = ε * (β : SL(2, ℤ)) 0 1 := by
    have : ((j * (m : ℤ) : ℤ) : ℝ) = ((ε * (β : SL(2, ℤ)) 0 1 : ℤ) : ℝ) := by
      rw [← hj]; simp
    exact_mod_cast this
  obtain ⟨t, ht'⟩ := exists_T_zpow' _ h10
  refine ⟨j, ?_⟩
  have key : t = ε * (β : SL(2, ℤ)) 0 1 := by
    rcases ht' with e | e
    · have a := congrArg (fun g : SL(2, ℤ) => g 0 0) e
      have b := congrArg (fun g : SL(2, ℤ) => g 0 1) e
      simp [ModularGroup.coe_T_zpow] at a b
      rw [h00] at a
      rw [a, ← b]; ring
    · have a := congrArg (fun g : SL(2, ℤ) => g 0 0) e
      have b := congrArg (fun g : SL(2, ℤ) => g 0 1) e
      simp [ModularGroup.coe_T_zpow] at a b
      rw [h00] at a
      rw [a, b]; ring
  have : ModularGroup.T ^ ((m : ℤ) * j) = (ModularGroup.T ^ t : SL(2, ℤ)) := by
    congr 1; rw [key, ← hj']; ring
  rw [this]
  rcases ht' with e | e
  · rw [e]
  · rw [e, pslMk_neg']

/-- A generator of `Γ_∞` modulo `±`. -/
private lemma exists_gen {m : ℕ} (hT : ModularGroup.T ^ (m : ℤ) ∈ Γ ∨ -(ModularGroup.T ^ (m : ℤ)) ∈ Γ) :
    ∃ u : Γ, u ∈ stabInfty Γ ∧
      ((u : SL(2, ℤ)) : PSL(2, ℤ)) = ((ModularGroup.T ^ (m : ℤ) : SL(2, ℤ)) : PSL(2, ℤ)) := by
  rcases hT with h | h
  · refine ⟨⟨_, h⟩, ?_, rfl⟩
    show (ModularGroup.T ^ (m : ℤ) : SL(2, ℤ)) 1 0 = 0
    rw [ModularGroup.coe_T_zpow]; simp
  · refine ⟨⟨_, h⟩, ?_, pslMk_neg' _⟩
    show (-(ModularGroup.T ^ (m : ℤ)) : SL(2, ℤ)) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]; simp

private lemma psi_zpow {m : ℕ} {u : Γ}
    (hu : ((u : SL(2, ℤ)) : PSL(2, ℤ)) = ((ModularGroup.T ^ (m : ℤ) : SL(2, ℤ)) : PSL(2, ℤ)))
    (j : ℤ) :
    ((psi Γ (u ^ j) : Kgrp Γ) : PSL(2, ℤ)) =
      ((ModularGroup.T ^ ((m : ℤ) * j) : SL(2, ℤ)) : PSL(2, ℤ)) := by
  rw [psi_coe, Subgroup.coe_zpow, QuotientGroup.mk_zpow, hu, ← QuotientGroup.mk_zpow, ← zpow_mul]

private lemma mem_Hgrp {m : ℕ} [Γ.FiniteIndex] (hm : (m : ℝ) = widthAtInfty Γ) {u : Γ} (hus : u ∈ stabInfty Γ)
    (hu : ((u : SL(2, ℤ)) : PSL(2, ℤ)) = ((ModularGroup.T ^ (m : ℤ) : SL(2, ℤ)) : PSL(2, ℤ)))
    (g : Kgrp Γ) : g ∈ Hgrp Γ ↔ ∃ j : ℤ, g = psi Γ (u ^ j) := by
  constructor
  · rintro ⟨β, hβ, rfl⟩
    obtain ⟨j, hj⟩ := stab_eq_T Γ hm hβ
    refine ⟨j, Subtype.ext ?_⟩
    rw [psi_zpow Γ hu, psi_coe, hj]
  · rintro ⟨j, rfl⟩
    exact ⟨u ^ j, Subgroup.zpow_mem _ hus j, rfl⟩

private lemma re_psi_zpow_smul {m : ℕ} {u : Γ}
    (hu : ((u : SL(2, ℤ)) : PSL(2, ℤ)) = ((ModularGroup.T ^ (m : ℤ) : SL(2, ℤ)) : PSL(2, ℤ)))
    (j : ℤ) (z : ℍ) : ((psi Γ (u ^ j)) • z).re = z.re + (((m : ℤ) * j : ℤ) : ℝ) := by
  have : (psi Γ (u ^ j)) • z = (ModularGroup.T ^ ((m : ℤ) * j) : SL(2, ℤ)) • z := by
    show ((psi Γ (u ^ j) : Kgrp Γ) : PSL(2, ℤ)) • z = _
    rw [psi_zpow Γ hu, pslMk_smul]
  rw [this, re_T_zpow_smul]

/-- The strip is a fundamental domain for the image of `Γ_∞`. -/
private lemma isFundamentalDomain_stripSet [Γ.FiniteIndex] :
    IsFundamentalDomain (Hgrp Γ) (stripSet (widthAtInfty Γ)) volume := by
  obtain ⟨m, hm0, hm, hT⟩ := exists_width_nat Γ
  obtain ⟨u, hus, hu⟩ := exists_gen Γ hT
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  refine IsFundamentalDomain.mk' (measurableSet_stripSet _).nullMeasurableSet ?_
  intro z
  have hre : ∀ j : ℤ, ((psi Γ (u ^ j)) • z).re = z.re + (m : ℝ) * j := by
    intro j
    rw [re_psi_zpow_smul Γ hu]; push_cast; ring
  have hmemS : ∀ j : ℤ, ((psi Γ (u ^ j)) • z ∈ stripSet (widthAtInfty Γ)) ↔
      (0 ≤ z.re + (m : ℝ) * j ∧ z.re + (m : ℝ) * j < m) := by
    intro j
    simp only [stripSet, Set.mem_ofPred_eq, ← hm]
    rw [hre j]
  let j0 : ℤ := -⌊z.re / m⌋
  have hfl1 : (⌊z.re / m⌋ : ℝ) ≤ z.re / m := Int.floor_le _
  have hfl2 : z.re / m < (⌊z.re / m⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hex : 0 ≤ z.re + (m : ℝ) * j0 ∧ z.re + (m : ℝ) * j0 < m := by
    have e1 : (⌊z.re / m⌋ : ℝ) * m ≤ z.re := by
      have := mul_le_mul_of_nonneg_right hfl1 hmpos.le
      rwa [div_mul_cancel₀ _ hmpos.ne'] at this
    have e2 : z.re < ((⌊z.re / m⌋ : ℝ) + 1) * m := by
      have := mul_lt_mul_of_pos_right hfl2 hmpos
      rwa [div_mul_cancel₀ _ hmpos.ne'] at this
    simp only [j0, Int.cast_neg]
    constructor <;> nlinarith
  refine ⟨⟨psi Γ (u ^ j0), (mem_Hgrp Γ hm hus hu _).2 ⟨j0, rfl⟩⟩, ?_, ?_⟩
  · exact (hmemS j0).2 hex
  · rintro ⟨g', hg'⟩ hg'S
    obtain ⟨j', rfl⟩ := (mem_Hgrp Γ hm hus hu _).1 hg'
    have h1 := (hmemS j').1 hg'S
    have : j' = j0 := by
      have a1 : (j' : ℝ) - j0 < 1 := by
        by_contra hcon; rw [not_lt] at hcon; nlinarith [hex.1, h1.2]
      have a2 : (j0 : ℝ) - j' < 1 := by
        by_contra hcon; rw [not_lt] at hcon; nlinarith [hex.2, h1.1]
      have b1 : j' - j0 < 1 := by exact_mod_cast a1
      have b2 : j0 - j' < 1 := by exact_mod_cast a2
      omega
    subst this
    rfl

/-- The fundamental domain for `Γ` built from translates of `𝒟ᵒ`. -/
def Dset : Set ℍ := ⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, (q.out)⁻¹ • (fdo : Set ℍ)

/-- The tiling of a strip-fundamental domain by translates of `D`. -/
def Eset : Set ℍ := ⋃ x : StabInftyCosets Γ, (psi Γ (x.out : Γ)) • Dset Γ

private lemma lower_zero_of_psi_eq {β w : SL(2, ℤ)} (h10 : β 1 0 = 0)
    (h : (β : PSL(2, ℤ)) = (w : PSL(2, ℤ))) : w 1 0 = 0 := by
  have hc := QuotientGroup.eq.mp h
  rw [Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hc
  have hw : w = β * (β⁻¹ * w) := by group
  rcases hc with hc | hc
  · rw [hw, hc, mul_one]; exact h10
  · rw [hw, hc, mul_neg_one, Matrix.SpecialLinearGroup.coe_neg]; simp [h10]

private lemma transversal_bijective [Γ.FiniteIndex] :
    Function.Bijective (fun x : StabInftyCosets Γ =>
      (QuotientGroup.mk ((psi Γ (x.out : Γ))⁻¹) : Kgrp Γ ⧸ Hgrp Γ)) := by
  constructor
  · intro x y hxy
    have h := QuotientGroup.eq.mp hxy
    rw [inv_inv, ← map_inv, ← map_mul] at h
    obtain ⟨β, hβ, hβe⟩ := h
    have h1 : ((β : SL(2, ℤ)) : PSL(2, ℤ)) = (((x.out : Γ) * (y.out : Γ)⁻¹ : Γ) : SL(2, ℤ)) := by
      have := congrArg (fun g : Kgrp Γ => (g : PSL(2, ℤ))) hβe
      exact this
    have h10 : (β : SL(2, ℤ)) 1 0 = 0 := hβ
    have h2 := lower_zero_of_psi_eq h10 h1
    have hrel : (x.out : Γ) * (y.out : Γ)⁻¹ ∈ stabInfty Γ := h2
    have : (Quotient.mk _ (y.out : Γ) : StabInftyCosets Γ) = Quotient.mk _ (x.out : Γ) :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr hrel)
    have e1 : (Quotient.mk _ (y.out : Γ) : StabInftyCosets Γ) = y := Quotient.out_eq y
    have e2 : (Quotient.mk _ (x.out : Γ) : StabInftyCosets Γ) = x := Quotient.out_eq x
    rw [e1, e2] at this
    exact this.symm
  · intro c
    induction c using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨γ, hγ, hg⟩ := g.2
      set γ' : Γ := ⟨γ, hγ⟩ with hγ'
      have hgψ : g = psi Γ γ' := Subtype.ext hg.symm
      refine ⟨(Quotient.mk _ γ'⁻¹ : StabInftyCosets Γ), ?_⟩
      simp only
      rw [QuotientGroup.eq, inv_inv, hgψ, ← map_mul]
      refine ⟨_, ?_, rfl⟩
      have h1 := Quotient.exact (Quotient.out_eq (Quotient.mk _ γ'⁻¹ : StabInftyCosets Γ))
      have h2 := QuotientGroup.rightRel_apply.mp h1
      have := Subgroup.inv_mem _ h2
      simpa using this

private lemma isFundamentalDomain_Dset [Γ.FiniteIndex] :
    IsFundamentalDomain (Kgrp Γ) (Dset Γ) volume :=
  ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter Γ

private lemma isFundamentalDomain_Eset [Γ.FiniteIndex] :
    IsFundamentalDomain (Hgrp Γ) (Eset Γ) volume := by
  have hD := isFundamentalDomain_Dset Γ
  exact hD.iUnion_smul_of_transversal (H := Hgrp Γ)
    (r := fun x : StabInftyCosets Γ => psi Γ (x.out : Γ))
    (fun x => hD.nullMeasurableSet_smul _) (transversal_bijective Γ)

private lemma setIntegral_smul_set' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : PSL(2, ℤ)) (s : Set ℍ) (G : ℍ → E) :
    ∫ z in g • s, G z = ∫ z in s, G (g • z) := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul g volume).setIntegral_image_emb
    (measurableEmbedding_const_smul g) _ _

private lemma integrableOn_smul_set' {E : Type*} [NormedAddCommGroup E]
    (g : PSL(2, ℤ)) (s : Set ℍ) (G : ℍ → E) (h : IntegrableOn G (g • s) volume) :
    IntegrableOn (fun z => G (g • z)) s volume := by
  rw [← Set.image_smul] at h
  exact ((measurePreserving_smul g volume).integrableOn_image
    (measurableEmbedding_const_smul g)).1 h

/-- **The abstract unfolding.** -/
theorem unfolding_core [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hinv : ∀ β ∈ stabInfty Γ, ∀ z : ℍ, F (((β : Γ) : SL(2, ℤ)) • z) = F z)
    (hint : IntegrableOn F (stripSet (widthAtInfty Γ))) :
    ∫ z in (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, (q.out)⁻¹ • (fdo : Set ℍ)),
        ∑' x : StabInftyCosets Γ, F ((((x.out : Γ)) : SL(2, ℤ)) • z) =
      ∫ z in stripSet (widthAtInfty Γ), F z := by
  have hD := isFundamentalDomain_Dset Γ
  have hS := isFundamentalDomain_stripSet Γ
  have hE := isFundamentalDomain_Eset Γ
  have hinvH : ∀ (g : Hgrp Γ) (z : ℍ), F (g • z) = F z := by
    rintro ⟨g, β, hβ, rfl⟩ z
    exact hinv β hβ z
  have h1 : ∫ z in stripSet (widthAtInfty Γ), F z = ∫ z in Eset Γ, F z :=
    hS.setIntegral_eq hE hinvH
  have hintE : IntegrableOn F (Eset Γ) volume := (hS.integrableOn_iff hE hinvH).1 hint
  have hrinj : Function.Injective (fun x : StabInftyCosets Γ => psi Γ (x.out : Γ)) := by
    intro x y hxy
    apply (transversal_bijective Γ).1
    exact congrArg (fun g : Kgrp Γ => (QuotientGroup.mk g⁻¹ : Kgrp Γ ⧸ Hgrp Γ)) hxy
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume)
      (fun x : StabInftyCosets Γ => psi Γ (x.out : Γ) • Dset Γ)) :=
    fun x y hxy => hD.aedisjoint (fun h => hxy (hrinj h))
  have hnull : ∀ x : StabInftyCosets Γ, NullMeasurableSet (psi Γ (x.out : Γ) • Dset Γ) volume :=
    fun x => hD.nullMeasurableSet_smul _
  have hsum := hasSum_integral_iUnion_ae hnull hdisj hintE
  have hsumN := hasSum_integral_iUnion_ae hnull hdisj hintE.norm
  have hcv : ∀ x : StabInftyCosets Γ, ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (G : ℍ → E), ∫ z in psi Γ (x.out : Γ) • Dset Γ, G z =
        ∫ z in Dset Γ, G ((((x.out : Γ)) : SL(2, ℤ)) • z) := by
    intro x E _ _ G
    exact setIntegral_smul_set' ((psi Γ (x.out : Γ) : Kgrp Γ) : PSL(2, ℤ)) (Dset Γ) G
  have hint_x : ∀ x : StabInftyCosets Γ,
      Integrable (fun z => F ((((x.out : Γ)) : SL(2, ℤ)) • z)) (volume.restrict (Dset Γ)) := by
    intro x
    have h2 : IntegrableOn F (psi Γ (x.out : Γ) • Dset Γ) volume :=
      hintE.mono_set (Set.subset_iUnion (fun x : StabInftyCosets Γ => psi Γ (x.out : Γ) • Dset Γ) x)
    exact integrableOn_smul_set' ((psi Γ (x.out : Γ) : Kgrp Γ) : PSL(2, ℤ)) (Dset Γ) F h2
  have hsumm : Summable fun x : StabInftyCosets Γ =>
      ∫ z in Dset Γ, ‖F ((((x.out : Γ)) : SL(2, ℤ)) • z)‖ := by
    refine hsumN.summable.congr fun x => ?_
    exact hcv x (fun z => ‖F z‖)
  show ∫ z in Dset Γ, ∑' x : StabInftyCosets Γ, F ((((x.out : Γ)) : SL(2, ℤ)) • z) = _
  rw [h1, show Eset Γ = ⋃ x : StabInftyCosets Γ, psi Γ (x.out : Γ) • Dset Γ from rfl,
    ← hsum.tsum_eq,← integral_tsum_of_summable_integral_norm hint_x hsumm]
  exact tsum_congr fun x => (hcv x F).symm

/-- Step (b): the Petersson product as an integral over the coset domain. -/
private lemma milnePetersson_eq_integral [Γ.FiniteIndex] {k : ℤ}
    (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k)) (Φ : ModularForm (Γ.map (mapGL ℝ)) (2 * k)) :
    milnePetersson Γ k f Φ =
      ∫ z in (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, (q.out)⁻¹ • (fdo : Set ℍ)),
        petersson (2 * k) Φ f z := by
  rw [integral_iUnion_fintype
      (fun q ↦ (isOpen_smul_fdo _).measurableSet)
      (ModularGroup.pairwise_disjoint_smul_fdo_out_withCenter Γ)
      (fun q ↦ (UpperHalfPlane.integrableOn_petersson_sl_smul_fd_right
        (2 * k) (Γ.map (mapGL ℝ)) Φ f _).mono_set (Set.smul_set_mono fdo_subset_fd))]
  unfold milnePetersson
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [UpperHalfPlane.peterssonInner_slash_slash_SL]
  have hae : ((((q.out)⁻¹ : SL(2, ℤ)) • fd : Set ℍ)) =ᵐ[volume]
      (((q.out)⁻¹ : SL(2, ℤ)) • fdo) := by
    rw [ModularGroup.sl_smul_set, ModularGroup.sl_smul_set]
    exact (MeasureTheory.smul_set_ae_eq _).mpr fd_ae_eq_fdo
  rw [UpperHalfPlane.peterssonInner_congr_set hae, UpperHalfPlane.peterssonInner_def]

/-- Step (c): the pointwise unfolding of the Petersson integrand. -/
private lemma petersson_poincare_eq_tsum [Γ.FiniteIndex] {k : ℕ} (n : ℕ)
    (f : CuspForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) (z : ℍ) :
    petersson (2 * (k : ℤ)) (poincareSeries Γ k n) f z =
      ∑' x : StabInftyCosets Γ,
        unfoldIntegrand Γ k n f ((((x.out : Γ)) : SL(2, ℤ)) • z) := by
  have hf : ∀ γ : Γ, (⇑f ∣[(2 * (k : ℤ))] ((γ : Γ) : SL(2, ℤ))) = ⇑f := fun γ ↦ by
    have := SlashInvariantFormClass.SL_slash_eq f (γ := (γ : SL(2, ℤ))) γ.2
    simpa using this
  have h1 : ∀ x : StabInftyCosets Γ,
      unfoldIntegrand Γ k n f ((((x.out : Γ)) : SL(2, ℤ)) • z) =
        conj (poincareTerm Γ k n x z) * f z * (z.im : ℂ) ^ (2 * (k : ℤ)) := by
    intro x
    unfold unfoldIntegrand
    rw [← UpperHalfPlane.petersson_slash_SL, hf x.out, poincareTerm_eq_out,
      poincareSummand_eq_slash]
    simp [UpperHalfPlane.petersson]
  simp_rw [h1]
  unfold UpperHalfPlane.petersson poincareSeries
  rw [Complex.conj_tsum, tsum_mul_right, tsum_mul_right]

/-- Step (d): stabilizer invariance. -/
private lemma unfoldIntegrand_stab {k : ℕ} (n : ℕ) (f : CuspForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ))
    (β : Γ) (hβ : β ∈ stabInfty Γ) (z : ℍ) :
    unfoldIntegrand Γ k n f ((β : SL(2, ℤ)) • z) = unfoldIntegrand Γ k n f z := by
  have hf : (⇑f ∣[(2 * (k : ℤ))] (β : SL(2, ℤ))) = ⇑f := by
    have := SlashInvariantFormClass.SL_slash_eq f (γ := (β : SL(2, ℤ))) β.2
    simpa using this
  have he : (expTerm Γ n ∣[(2 * (k : ℤ))] (β : SL(2, ℤ))) = expTerm Γ n := by
    have h := poincareSummand_stabInfty Γ k n (β := β) (γ := 1) hβ
    rw [mul_one] at h
    have h2 : poincareSummand Γ k n (1 : SL(2, ℤ)) = expTerm Γ n := by
      rw [poincareSummand_eq_slash, SlashAction.slash_one]
    rw [← poincareSummand_eq_slash]
    have h3 : poincareSummand Γ k n ((1 : Γ) : SL(2, ℤ)) = expTerm Γ n := h2
    exact (funext h).trans h3
  unfold unfoldIntegrand
  rw [← UpperHalfPlane.petersson_slash_SL, hf, he]

/-- **Unfolding** of the Petersson product against a Poincaré series. -/
theorem milnePetersson_poincare_eq_strip [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (n : ℕ)
    (f : CuspForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ)) :
    milnePetersson Γ k f (poincareSeries Γ k n) =
      ∫ z in stripSet (widthAtInfty Γ), unfoldIntegrand Γ k n f z := by
  obtain ⟨Φ, hΦ⟩ := (poincareSeriesModular Γ hk).modular n
  have hcast : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; ring
  have hmain : milnePetersson Γ k f (poincareSeries Γ k n) =
      ∫ z in (⋃ q : SL(2, ℤ) ⧸ Γ.withCenter, (q.out)⁻¹ • (fdo : Set ℍ)),
        petersson (2 * (k : ℤ)) (poincareSeries Γ k n) f z := by
    rw [← hΦ]
    exact milnePetersson_eq_integral Γ (k := (k : ℤ)) f Φ
  rw [hmain]
  simp_rw [petersson_poincare_eq_tsum Γ n f]
  exact unfolding_core Γ _ (fun β hβ z ↦ unfoldIntegrand_stab Γ n f β hβ z)
    (integrableOn_unfoldIntegrand Γ hk n f)

section Adjoint

variable (Γ : Subgroup SL(2, ℤ))

/-- A function invariant under `Γ` in even weight is invariant under `Γ.withCenter`. -/
private lemma slash_withCenter_eq {kk : ℤ} {f : ℍ → ℂ} (hf : ∀ γ ∈ Γ, f ∣[2 * kk] γ = f)
    {w : SL(2, ℤ)} (hw : w ∈ Γ.withCenter) : f ∣[2 * kk] w = f := by
  obtain ⟨γ', hγ', hcase⟩ := Subgroup.mem_withCenter_iff_exists_eq_or_eq_neg.mp hw
  rcases hcase with rfl | rfl
  · exact hf _ hγ'
  · have hcoe : ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = -1 := mapGL_neg_one
    rw [← mul_neg_one γ', SlashAction.slash_mul, ModularForm.SL_slash (γ := (-1 : SL(2, ℤ))),
      hcoe, ModularForm.slash_neg_one, hf _ hγ']
    have : ((-1 : ℂ)) ^ (2 * kk) = 1 := Even.neg_one_zpow ⟨kk, by ring⟩
    funext z
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply]
    rw [this, one_mul]

/-- **Adjointness**: for a normal finite-index `Γ` and `Γ`-invariant `f, g` of even weight,
`⟨f, g|σ⟩ = ⟨f|σ⁻¹, g⟩`. -/
theorem milnePetersson_slash_adjoint [Γ.FiniteIndex] [Γ.Normal] (kk : ℤ) {f g : ℍ → ℂ}
    (hf : ∀ γ ∈ Γ, f ∣[2 * kk] γ = f) (hg : ∀ γ ∈ Γ, g ∣[2 * kk] γ = g) (σ : SL(2, ℤ)) :
    milnePetersson Γ kk f (g ∣[2 * kk] σ) = milnePetersson Γ kk (f ∣[2 * kk] σ⁻¹) g := by
  classical
  have : Γ.withCenter.Normal := by rw [Subgroup.withCenter_def]; infer_instance
  have hf' : ∀ γ ∈ Γ, (f ∣[2 * kk] σ⁻¹) ∣[2 * kk] γ = f ∣[2 * kk] σ⁻¹ := by
    intro γ hγ
    rw [← SlashAction.slash_mul]
    have : σ⁻¹ * γ = (σ⁻¹ * γ * σ) * σ⁻¹ := by group
    rw [this, SlashAction.slash_mul, hf _ (by
      have := ‹Γ.Normal›.conj_mem γ hγ σ⁻¹
      simpa using this)]
  set T : SL(2, ℤ) → ℂ := fun δ =>
    peterssonInner (2 * kk) fd (g ∣[2 * kk] δ) ((f ∣[2 * kk] σ⁻¹) ∣[2 * kk] δ) with hT
  have hTinv : ∀ w ∈ Γ.withCenter, ∀ δ, T (w * δ) = T δ := by
    intro w hw δ
    simp only [hT]
    rw [SlashAction.slash_mul, SlashAction.slash_mul, slash_withCenter_eq Γ hg hw,
      slash_withCenter_eq Γ hf' hw]
  have hL : milnePetersson Γ kk f (g ∣[2 * kk] σ) =
      ∑ q : SL(2, ℤ) ⧸ Γ.withCenter, T (σ * (q.out)⁻¹) := by
    unfold milnePetersson
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hT]
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
    simp
  have hR : milnePetersson Γ kk (f ∣[2 * kk] σ⁻¹) g =
      ∑ q : SL(2, ℤ) ⧸ Γ.withCenter, T ((q.out)⁻¹) := rfl
  rw [hL, hR]
  let e : SL(2, ℤ) ⧸ Γ.withCenter → SL(2, ℤ) ⧸ Γ.withCenter :=
    fun q => QuotientGroup.mk (q.out * σ⁻¹)
  have hinj : Function.Injective e := by
    intro q1 q2 h12
    have h1 := QuotientGroup.eq.mp h12
    have h2 : (q1.out)⁻¹ * q2.out ∈ Γ.withCenter := by
      have := ‹Γ.withCenter.Normal›.conj_mem _ h1 σ⁻¹
      have e1 : σ⁻¹ * ((q1.out * σ⁻¹)⁻¹ * (q2.out * σ⁻¹)) * σ⁻¹⁻¹ = (q1.out)⁻¹ * q2.out := by
        group
      rwa [e1] at this
    have h3 : (QuotientGroup.mk q1.out : SL(2, ℤ) ⧸ Γ.withCenter) = QuotientGroup.mk q2.out :=
      QuotientGroup.eq.mpr h2
    simpa using h3
  have hbij : Function.Bijective e := Finite.injective_iff_bijective.mp hinj
  refine Fintype.sum_bijective e hbij _ _ fun q => ?_
  have hw : ((e q).out)⁻¹ * (q.out * σ⁻¹) ∈ Γ.withCenter :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (e q))
  have := hTinv _ hw (σ * (q.out)⁻¹)
  have e2 : ((e q).out)⁻¹ * (q.out * σ⁻¹) * (σ * (q.out)⁻¹) = ((e q).out)⁻¹ := by group
  rw [e2] at this
  exact this.symm

/-- Scalars in the second variable. -/
theorem milnePetersson_smul_right_aux [Γ.FiniteIndex] (k : ℤ) (c : ℂ) (f g : ℍ → ℂ) :
    milnePetersson Γ k f (c • g) = (starRingEnd ℂ) c * milnePetersson Γ k f g := by
  simp only [milnePetersson, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [ModularForm.SL_smul_slash]
  exact UpperHalfPlane.peterssonInner_smul_left _ _ c _ _

theorem milnePetersson_zero_right_aux [Γ.FiniteIndex] (k : ℤ) (f : ℍ → ℂ) :
    milnePetersson Γ k f 0 = 0 := by
  have := milnePetersson_smul_right_aux Γ k 0 f 0
  simpa using this

end Adjoint

section EisensteinPoincare

variable (N : ℕ)

/-- The class `(0, 1)`. -/
def a0 : Fin 2 → ZMod N := ![0, 1]

/-- A coprime pair is the bottom row of an element of `SL(2, ℤ)`. -/
private lemma exists_sl_of_mem_gammaSet {a : Fin 2 → ZMod N} {v : Fin 2 → ℤ}
    (hv : v ∈ EisensteinSeries.gammaSet N 1 a) :
    ∃ σ : SL(2, ℤ), σ 1 0 = v 0 ∧ σ 1 1 = v 1 := by
  have hc : IsCoprime (v 0) (v 1) := Int.isCoprime_iff_gcd_eq_one.mpr hv.2
  obtain ⟨u, w, huw⟩ := hc
  refine ⟨⟨!![w, -u; v 0, v 1], ?_⟩, by simp, by simp⟩
  rw [Matrix.det_fin_two_of]
  linarith

/-- Bottom row of `σ` modulo `N`. -/
private lemma a0_vecMul (σ : SL(2, ℤ)) :
    a0 N ᵥ* σ = ![((σ 1 0 : ℤ) : ZMod N), ((σ 1 1 : ℤ) : ZMod N)] := by
  ext i
  fin_cases i <;> simp [a0, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Coprimality of the bottom row. -/
private lemma gcd_bottom (g : SL(2, ℤ)) : Int.gcd (g 1 0) (g 1 1) = 1 := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two] at hd
  exact Int.isCoprime_iff_gcd_eq_one.mp ⟨-(g 0 1), g 0 0, by linarith⟩

/-- The bottom row of the chosen representative of a coset in `Γ_∞\Γ(N)`. -/
def botRow (x : StabInftyCosets (CongruenceSubgroup.Gamma N)) : Fin 2 → ℤ :=
  ![((x.out : CongruenceSubgroup.Gamma N) : SL(2, ℤ)) 1 0,
    ((x.out : CongruenceSubgroup.Gamma N) : SL(2, ℤ)) 1 1]

/-- The bottom row of an element of `Γ(N)` lies in `gammaSet N 1 (0,1)`. -/
private lemma bottom_mem_gammaSet {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    ![g 1 0, g 1 1] ∈ EisensteinSeries.gammaSet N 1 (a0 N) := by
  obtain ⟨-, -, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hg
  refine ⟨?_, by simpa using gcd_bottom g⟩
  ext i
  fin_cases i <;> simp [a0, h10, h11]

private lemma botRow_mem (x : StabInftyCosets (CongruenceSubgroup.Gamma N)) :
    botRow N x ∈ EisensteinSeries.gammaSet N 1 (a0 N) :=
  bottom_mem_gammaSet N (x.out : CongruenceSubgroup.Gamma N).2

/-- Multiplying a vector of `gammaSet N 1 (0,1)` by a sign that is `1` mod `N`. -/
private lemma smul_mem_gammaSet {s : ℤ} (hs : s = 1 ∨ s = -1) (hc : ((s : ℤ) : ZMod N) = 1)
    {v : Fin 2 → ℤ} (hv : v ∈ EisensteinSeries.gammaSet N 1 (a0 N)) :
    s • v ∈ EisensteinSeries.gammaSet N 1 (a0 N) := by
  refine ⟨?_, ?_⟩
  · ext i
    have := congrFun hv.1 i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul, hc, one_mul] at this ⊢
    exact this
  · have := hv.2
    rcases hs with rfl | rfl <;> simpa [Int.gcd_neg, Int.neg_gcd] using this

/-- The signs `±1` that are `1` modulo `N`. -/
def signs : Finset ℤ := ({1, -1} : Finset ℤ).filter (fun s => ((s : ℤ) : ZMod N) = 1)

private lemma mem_signs {s : ℤ} : s ∈ signs N ↔ (s = 1 ∨ s = -1) ∧ ((s : ℤ) : ZMod N) = 1 := by
  simp [signs]

/-- The parametrisation of `gammaSet N 1 (0,1)` by cosets and signs. -/
def psiE (p : StabInftyCosets (CongruenceSubgroup.Gamma N) × signs N) :
    EisensteinSeries.gammaSet N 1 (a0 N) :=
  ⟨(p.2 : ℤ) • botRow N p.1,
    smul_mem_gammaSet N ((mem_signs N).mp p.2.2).1 ((mem_signs N).mp p.2.2).2 (botRow_mem N p.1)⟩

private lemma psi_injective : Function.Injective (psiE N) := by
  rintro ⟨x, s⟩ ⟨y, t⟩ h
  have h' : (s : ℤ) • botRow N x = (t : ℤ) • botRow N y := congrArg Subtype.val h
  have hs := (mem_signs N).mp s.2
  have ht := (mem_signs N).mp t.2
  have h0 : (s : ℤ) * botRow N x 0 = (t : ℤ) * botRow N y 0 := by simpa using congrFun h' 0
  have h1 : (s : ℤ) * botRow N x 1 = (t : ℤ) * botRow N y 1 := by simpa using congrFun h' 1
  have hs0 : (s : ℤ) ≠ 0 := by rcases hs.1 with h | h <;> simp [h]
  have hcross : (s : ℤ) * (botRow N y 0 * botRow N x 1 - botRow N y 1 * botRow N x 0) = 0 := by
    linear_combination (botRow N y 0) * h1 - (botRow N y 1) * h0
  have hcross' : botRow N y 0 * botRow N x 1 = botRow N y 1 * botRow N x 0 := by
    have := (mul_eq_zero.mp hcross).resolve_left hs0
    linarith
  have hxy : x = y := coset_eq_of_cross _ hcross'
  subst hxy
  have hst : (s : ℤ) = t := by
    by_contra hne
    have hne' : (s : ℤ) - t ≠ 0 := sub_ne_zero.mpr hne
    have e0 : botRow N x 0 = 0 := by
      have : ((s : ℤ) - t) * botRow N x 0 = 0 := by linear_combination h0
      exact (mul_eq_zero.mp this).resolve_left hne'
    have e1 : botRow N x 1 = 0 := by
      have : ((s : ℤ) - t) * botRow N x 1 = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_left hne'
    have := gcd_bottom (x.out : CongruenceSubgroup.Gamma N)
    simp only [botRow, Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    rw [e0, e1] at this
    simp at this
  exact Prod.ext rfl (Subtype.ext hst)

/-- A vector of `gammaSet N 1 (0,1)` is the bottom row of an element of `Γ(N)`. -/
private lemma exists_gamma_of_mem {v : Fin 2 → ℤ} (hv : v ∈ EisensteinSeries.gammaSet N 1 (a0 N)) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma N ∧ γ 1 0 = v 0 ∧ γ 1 1 = v 1 := by
  have hc : IsCoprime (v 0) (v 1) := Int.isCoprime_iff_gcd_eq_one.mpr hv.2
  obtain ⟨u, w, huw⟩ := hc
  have v0c : ((v 0 : ℤ) : ZMod N) = 0 := by simpa [a0] using congrFun hv.1 0
  have v1c : ((v 1 : ℤ) : ZMod N) = 1 := by simpa [a0] using congrFun hv.1 1
  have hwc : ((w : ℤ) : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) huw
    push_cast at this
    rw [v0c, v1c] at this
    simpa using this
  have hdet : (!![w + u * v 0, -u + u * v 1; v 0, v 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination huw
  obtain ⟨g, hg⟩ : ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) =
      !![w + u * v 0, -u + u * v 1; v 0, v 1] := ⟨⟨_, hdet⟩, rfl⟩
  have g00 : g 0 0 = w + u * v 0 := by rw [show g 0 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 from rfl, hg]; simp
  have g01 : g 0 1 = -u + u * v 1 := by rw [show g 0 1 = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 from rfl, hg]; simp
  have g10 : g 1 0 = v 0 := by rw [show g 1 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl, hg]; simp
  have g11 : g 1 1 = v 1 := by rw [show g 1 1 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from rfl, hg]; simp
  refine ⟨g, ?_, g10, g11⟩
  · rw [CongruenceSubgroup.Gamma_mem, g00, g01, g10, g11]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [v0c, hwc]
    · simp [v1c]
    · simp [v0c]
    · simp [v1c]

private lemma psi_surjective : Function.Surjective (psiE N) := by
  rintro ⟨v, hv⟩
  obtain ⟨γ, hγ, h0, h1⟩ := exists_gamma_of_mem N hv
  set x : StabInftyCosets (CongruenceSubgroup.Gamma N) :=
    Quotient.mk _ (⟨γ, hγ⟩ : CongruenceSubgroup.Gamma N) with hx
  have hmk : (Quotient.mk _ x.out : StabInftyCosets (CongruenceSubgroup.Gamma N)) =
      Quotient.mk _ (⟨γ, hγ⟩ : CongruenceSubgroup.Gamma N) := Quotient.out_eq x
  have hrel : (⟨γ, hγ⟩ : CongruenceSubgroup.Gamma N) * x.out⁻¹ ∈
      stabInfty (CongruenceSubgroup.Gamma N) :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hmk)
  have hb10 : ((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma N) * x.out⁻¹ : CongruenceSubgroup.Gamma N)) :
      SL(2, ℤ)) 1 0 = 0 := hrel
  obtain ⟨ε, hε, hb00, hb11⟩ := sl_lower_zero _ hb10
  have hprod : γ = ((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma N) * x.out⁻¹ : CongruenceSubgroup.Gamma N)) :
      SL(2, ℤ)) * ((x.out : CongruenceSubgroup.Gamma N) : SL(2, ℤ)) := by
    simp
  have key : ∀ (b w : SL(2, ℤ)), b 1 0 = 0 → b 1 1 = ε →
      (b * w) 1 0 = ε * w 1 0 ∧ (b * w) 1 1 = ε * w 1 1 := by
    intro b w hb0 hb1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb0, hb1]
  have hkey := key _ ((x.out : CongruenceSubgroup.Gamma N) : SL(2, ℤ)) hb10 hb11
  rw [← hprod] at hkey
  obtain ⟨e0, e1⟩ := hkey
  have v1c : ((v 1 : ℤ) : ZMod N) = 1 := by simpa [a0] using congrFun hv.1 1
  obtain ⟨-, -, -, hx11⟩ := CongruenceSubgroup.Gamma_mem.mp
    (x.out : CongruenceSubgroup.Gamma N).2
  have hεc : ((ε : ℤ) : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) (h1.symm.trans e1)
    push_cast at this
    rw [v1c, hx11] at this
    simpa using this.symm
  have hεs : ε ∈ signs N := (mem_signs N).mpr ⟨hε, hεc⟩
  refine ⟨(x, ⟨ε, hεs⟩), Subtype.ext ?_⟩
  ext i
  fin_cases i
  · simp [psiE, botRow, ← h0, e0]
  · simp [psiE, botRow, ← h1, e1]

private lemma poincareTerm_zero_eq (k : ℕ) (x : StabInftyCosets (CongruenceSubgroup.Gamma N)) (z : ℍ) :
    poincareTerm (CongruenceSubgroup.Gamma N) k 0 x z =
      EisensteinSeries.eisSummand (2 * (k : ℤ)) (botRow N x) z := by
  rw [poincareTerm_eq_out]
  simp [poincareSummand, EisensteinSeries.eisSummand, botRow]

private lemma eisSummand_sign (k : ℕ) {s : ℤ} (hs : s = 1 ∨ s = -1) (v : Fin 2 → ℤ) (z : ℍ) :
    EisensteinSeries.eisSummand (2 * (k : ℤ)) (s • v) z =
      EisensteinSeries.eisSummand (2 * (k : ℤ)) v z := by
  rcases hs with rfl | rfl
  · simp
  · simp only [EisensteinSeries.eisSummand, Pi.smul_apply, smul_eq_mul]
    have : (((-1 * v 0 : ℤ)) : ℂ) * (z : ℂ) + (((-1 * v 1 : ℤ)) : ℂ) =
        -(((v 0 : ℤ) : ℂ) * z + ((v 1 : ℤ) : ℂ)) := by push_cast; ring
    rw [this]
    exact Even.neg_zpow ⟨-(k : ℤ), by ring⟩ _

/-- `E_{(0,1)} = c · φ_0` for `Γ(N)`, with `c = 1` or `2`. -/
theorem eisenstein_a0_eq [NeZero N] {k : ℕ} (hk : 2 ≤ k) (z : ℍ) :
    eisensteinSeries (a0 N) (2 * (k : ℤ)) z =
      ((signs N).card : ℂ) * poincareSeries (CongruenceSubgroup.Gamma N) k 0 z := by
  have hbij : Function.Bijective (psiE N) := ⟨psi_injective N, psi_surjective N⟩
  have e1 : eisensteinSeries (a0 N) (2 * (k : ℤ)) z =
      ∑' p : StabInftyCosets (CongruenceSubgroup.Gamma N) × signs N,
        EisensteinSeries.eisSummand (2 * (k : ℤ)) (botRow N p.1) z := by
    unfold eisensteinSeries
    rw [← (Equiv.ofBijective _ hbij).tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [Equiv.ofBijective_apply, psiE]
    exact eisSummand_sign k ((mem_signs N).mp p.2.2).1 _ z
  have hsum : Summable fun x : StabInftyCosets (CongruenceSubgroup.Gamma N) =>
      ‖EisensteinSeries.eisSummand (2 * (k : ℤ)) (botRow N x) z‖ := by
    obtain ⟨u, hu, hbd⟩ := poincareSeries_bound (CongruenceSubgroup.Gamma N) hk 0
      (isCompact_singleton (x := z))
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_) hu
    rw [← poincareTerm_zero_eq]
    exact hbd x z rfl
  have hfin : Summable fun s : signs N => ‖(1 : ℂ)‖ := Summable.of_finite
  have := tsum_mul_tsum_of_summable_norm (f := fun x : StabInftyCosets (CongruenceSubgroup.Gamma N) =>
    EisensteinSeries.eisSummand (2 * (k : ℤ)) (botRow N x) z) (g := fun _ : signs N => (1 : ℂ))
    hsum hfin
  simp only [mul_one] at this
  rw [e1, ← this]
  simp only [tsum_const, Nat.card_eq_fintype_card, Fintype.card_coe, nsmul_eq_mul, mul_one]
  rw [mul_comm]
  congr 1
  unfold poincareSeries
  exact tsum_congr fun x => (poincareTerm_zero_eq N k x z).symm

end EisensteinPoincare

/-- (D) Remark 4.38(b) from the vanishing at `n = 0`. -/
theorem eisensteinCuspOrthogonal_of_zero (N : ℕ) [NeZero N] {k : ℕ} (hk : 2 ≤ k)
    (h0 : ∀ f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) ((2 * k : ℕ) : ℤ),
      milnePetersson (CongruenceSubgroup.Gamma N) k f
        (poincareSeries (CongruenceSubgroup.Gamma N) k 0) = 0) :
    EisensteinCuspOrthogonal N k := by
  have hnorm : (CongruenceSubgroup.Gamma N).Normal := CongruenceSubgroup.Gamma_normal N
  refine ⟨fun f a => ?_⟩
  by_cases hE : IsEmpty (EisensteinSeries.gammaSet N 1 a)
  · have : eisensteinSeries a (2 * (k : ℤ)) = 0 := by
      funext z
      simp [eisensteinSeries]
    rw [this]
    exact milnePetersson_zero_right_aux _ _ _
  · obtain ⟨⟨v, hv⟩⟩ := not_isEmpty_iff.mp hE
    obtain ⟨σ, hσ0, hσ1⟩ := exists_sl_of_mem_gammaSet N hv
    have haσ : a0 N ᵥ* σ = a := by
      rw [a0_vecMul]
      ext i
      fin_cases i
      · simp [hσ0, ← congrFun hv.1 0]
      · simp [hσ1, ← congrFun hv.1 1]
    have hEa : eisensteinSeries a (2 * (k : ℤ)) =
        ((signs N).card : ℂ) • (poincareSeries (CongruenceSubgroup.Gamma N) k 0 ∣[2 * (k : ℤ)] σ) := by
      rw [← haσ, ← EisensteinSeries.eisensteinSeries_slash_apply]
      have : eisensteinSeries (a0 N) (2 * (k : ℤ)) =
          ((signs N).card : ℂ) • poincareSeries (CongruenceSubgroup.Gamma N) k 0 := by
        funext z
        simp [eisenstein_a0_eq N hk z]
      rw [this, ModularForm.SL_smul_slash]
    rw [hEa, milnePetersson_smul_right_aux]
    have hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, (⇑f) ∣[2 * (k : ℤ)] γ = ⇑f :=
      fun γ hγ => SlashInvariantFormClass.SL_slash_eq f γ hγ
    have hg : ∀ γ ∈ CongruenceSubgroup.Gamma N,
        (poincareSeries (CongruenceSubgroup.Gamma N) k 0) ∣[2 * (k : ℤ)] γ =
          poincareSeries (CongruenceSubgroup.Gamma N) k 0 :=
      fun γ hγ => poincareSeries_slash_of_mem _ k 0 hγ
    rw [milnePetersson_slash_adjoint _ (k : ℤ) hf hg σ]
    let f' : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) ((2 * k : ℕ) : ℤ) :=
      CuspForm.restrict (conj_gamma_le N σ⁻¹) (CuspForm.translate f (mapGL ℝ σ⁻¹))
    have hf' : (⇑f) ∣[2 * (k : ℤ)] σ⁻¹ = ⇑f' := rfl
    rw [hf', h0 f', mul_zero]

/-- **Theorem 4.33** (Petersson product of a cusp form with a Poincaré series): for $2k \ge 4$ and $n \ge 1$,
$\langle f, \varphi_n\rangle = \frac{h^{2k}(2k-2)!}{(4\pi)^{2k-1}}\,n^{1-2k}a_n$, proved by unfolding. -/
@[kb "milne2017mf" "Section 4, Theorem 4.33 (pdf p. 64)"]
theorem poincarePetersson (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) :
    PoincarePetersson Γ k :=
  ⟨fun n _ f => by
    rw [milnePetersson_poincare_eq_strip Γ hk n f, integral_unfoldIntegrand Γ hk n f]⟩

/-- **Remark 4.38 (b)**: cusp forms are orthogonal to the restricted Eisenstein series for $\Gamma(N)$ of weight
$2k > 2$ ("$\varphi_0$ gives the zeroth coefficient"), by the case $n = 0$ of the unfolding. -/
@[kb "milne2017mf" "Section 4, Remark 4.38 (b) (pdf p. 66)"]
theorem eisensteinCuspOrthogonal (N : ℕ) [NeZero N] {k : ℕ} (hk : 2 ≤ k) :
    EisensteinCuspOrthogonal N k := by
  refine eisensteinCuspOrthogonal_of_zero N hk fun f => ?_
  rw [milnePetersson_poincare_eq_strip _ hk 0 f, integral_unfoldIntegrand _ hk 0 f]
  have h : (1 - 2 * (k : ℤ)) ≠ 0 := by omega
  simp [zero_zpow _ h]

/-- **Theorem 4.29 / Corollary 4.34**, unconditionally: for $2k > 2$, every cusp form of weight $2k$ for $\Gamma$ is a
linear combination of the Poincaré series $\varphi_n$, $n \ge 1$ (from Theorems 4.28 and 4.33, both proved). -/
@[kb "milne2017mf" "Section 4, Theorem 4.29 and Corollary 4.34 (pdf pp. 62, 64)"]
theorem poincareSeries_span_cuspForm (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) :
    ⇑f ∈ Submodule.span ℂ (Set.range fun n : {n : ℕ // 1 ≤ n} ↦ poincareSeries Γ k n) :=
  poincareSeries_span_of_petersson Γ hk (poincarePetersson Γ hk) f

/-- **Remark 4.38 (b)**, unconditionally: for $2k > 2$, a modular form of weight $2k$ for $\Gamma(N)$ is orthogonal to
all cusp forms iff it is a linear combination of Eisenstein series: the Eisenstein series span the orthogonal complement
of $S_k(\Gamma(N))$ in $M_k(\Gamma(N))$. -/
@[kb "milne2017mf" "Section 4, Remark 4.38 (b) (pdf p. 66)"]
theorem orthogonal_cuspForms_iff_mem_eisenstein' (N : ℕ) [NeZero N] {k : ℕ} (hk : 2 ≤ k)
    (g : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℤ)) :
    (∀ f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℤ),
        milnePetersson (CongruenceSubgroup.Gamma N) k f g = 0) ↔
      ⇑g ∈ Submodule.span ℂ (Set.range fun a : Fin 2 → ZMod N ↦ eisensteinSeries a (2 * k : ℤ)) :=
  orthogonal_cuspForms_iff_mem_eisenstein N hk (eisensteinCuspOrthogonal N hk) g

end ModularFormsKB.Milne
