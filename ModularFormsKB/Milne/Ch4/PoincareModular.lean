import ModularFormsKB.Milne.Ch4.Poincare
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: Theorem 4.28 for Poincaré series

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 4, Theorem 4.28 (pdf p. 62).
Proof of the named statement `PoincareSeriesModular` (Gunning, III.9): holomorphy from the Weierstrass bound,
slash invariance by permuting the cosets $\Gamma_\infty\backslash\Gamma$, and the behaviour at every cusp by
dominated convergence on vertical strips together with periodicity of $\varphi_n|\sigma$.
-/

open UpperHalfPlane Complex Filter Topology ModularForm ModularGroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Classical

noncomputable section

namespace ModularFormsKB.Milne

variable (Γ : Subgroup SL(2, ℤ))

/-- The function `z ↦ exp(2πi n z/h)`. -/
def expTerm (n : ℕ) (z : ℍ) : ℂ := cexp (2 * π * Complex.I * n * (z : ℂ) / widthAtInfty Γ)

/-- `denom` of an integer matrix. -/
lemma denom_sl (γ : SL(2, ℤ)) (z : ℍ) :
    UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom]

/-- The summand is the slash of `expTerm`. -/
lemma poincareSummand_eq_slash (k n : ℕ) (γ : SL(2, ℤ)) :
    poincareSummand Γ k n γ = expTerm Γ n ∣[(2 * k : ℤ)] γ := by
  funext z
  rw [SL_slash_apply, denom_sl]
  rfl

/-- The term on a coset, via the chosen representative. -/
lemma poincareTerm_eq_out (k n : ℕ) (x : StabInftyCosets Γ) (z : ℍ) :
    poincareTerm Γ k n x z = poincareSummand Γ k n (x.out : SL(2, ℤ)) z := by
  calc poincareTerm Γ k n x z = poincareTerm Γ k n (Quotient.mk _ x.out) z := by rw [Quotient.out_eq]
    _ = _ := rfl

/-- The slash of the Poincaré series by `σ`, as a sum over cosets. -/
lemma poincareSeries_slash_apply (k n : ℕ) (σ : SL(2, ℤ)) (z : ℍ) :
    (poincareSeries Γ k n ∣[(2 * k : ℤ)] σ) z =
      ∑' x : StabInftyCosets Γ, poincareSummand Γ k n ((x.out : SL(2, ℤ)) * σ) z := by
  rw [SL_slash_apply, poincareSeries, ← tsum_mul_right]
  refine tsum_congr fun x => ?_
  rw [poincareTerm_eq_out, poincareSummand_eq_slash Γ k n (x.out : SL(2, ℤ)),
    poincareSummand_eq_slash Γ k n ((x.out : SL(2, ℤ)) * σ), SlashAction.slash_mul]
  exact (SL_slash_apply (γ := σ) (τ := z) ..).symm

/-- Right multiplication by `δ ∈ Γ` on the cosets `Γ_∞\Γ`. -/
def cosetMul (δ : Γ) : StabInftyCosets Γ ≃ StabInftyCosets Γ where
  toFun := Quotient.map' (fun g : Γ => g * δ) (fun a b hab => by
    have h := QuotientGroup.rightRel_apply.mp hab
    exact QuotientGroup.rightRel_apply.mpr (by simpa [mul_assoc] using h))
  invFun := Quotient.map' (fun g : Γ => g * δ⁻¹) (fun a b hab => by
    have h := QuotientGroup.rightRel_apply.mp hab
    exact QuotientGroup.rightRel_apply.mpr (by simpa [mul_assoc] using h))
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h g => exact congrArg (Quotient.mk _) (by simp)
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h g => exact congrArg (Quotient.mk _) (by simp)

/-- The term at `cosetMul δ x`. -/
lemma poincareTerm_cosetMul (k n : ℕ) (δ : Γ) (x : StabInftyCosets Γ) (z : ℍ) :
    poincareTerm Γ k n (cosetMul Γ δ x) z =
      poincareSummand Γ k n ((x.out : SL(2, ℤ)) * δ) z := by
  have h := Quotient.out_eq x
  calc poincareTerm Γ k n (cosetMul Γ δ x) z
      = poincareTerm Γ k n (cosetMul Γ δ (Quotient.mk _ x.out)) z := by rw [h]
    _ = _ := rfl

/-- **Slash invariance**: `φ_n | δ = φ_n` for `δ ∈ Γ`. -/
lemma poincareSeries_slash_of_mem (k n : ℕ) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ) :
    poincareSeries Γ k n ∣[(2 * k : ℤ)] δ = poincareSeries Γ k n := by
  funext z
  rw [poincareSeries_slash_apply]
  unfold poincareSeries
  rw [← Equiv.tsum_eq (cosetMul Γ ⟨δ, hδ⟩) (fun y => poincareTerm Γ k n y z)]
  exact tsum_congr fun x => (poincareTerm_cosetMul Γ k n ⟨δ, hδ⟩ x z).symm

open scoped Manifold

/-- `z ↦ exp(2πi n z/h)` is holomorphic. -/
lemma expTerm_mdifferentiable (n : ℕ) : MDiff (expTerm Γ n) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have : DifferentiableOn ℂ (fun w : ℂ => cexp (2 * π * Complex.I * n * w / widthAtInfty Γ))
      {z : ℂ | 0 < z.im} := by
    fun_prop
  refine this.congr ?_
  intro w hw
  simp [expTerm, ofComplex_apply_of_im_pos hw]

/-- Each term is holomorphic. -/
lemma poincareTerm_mdifferentiable (k n : ℕ) (x : StabInftyCosets Γ) :
    MDiff (poincareTerm Γ k n x) := by
  have : poincareTerm Γ k n x = expTerm Γ n ∣[(2 * k : ℤ)] (x.out : SL(2, ℤ)) := by
    funext z
    rw [poincareTerm_eq_out, poincareSummand_eq_slash]
  rw [this, SL_slash]
  exact (expTerm_mdifferentiable Γ n).slash _ _

/-- The Poincaré series is holomorphic. -/
lemma poincareSeries_mdifferentiable [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    MDiff (poincareSeries Γ k n) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro w hw
  have hw' : 0 < w.im := hw
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ w.im / 2 := ⟨w.im / 2, by positivity, le_rfl⟩
  have hsub : Metric.closedBall w r ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
    have h2 : ‖z - w‖ ≤ r := by simpa [dist_eq_norm] using hz
    have h3 : -(z - w).im ≤ r := (neg_le_abs _).trans (h1.trans h2)
    simp only [Complex.sub_im] at h3
    show 0 < z.im
    linarith
  let K : Set ℍ := UpperHalfPlane.coe ⁻¹' Metric.closedBall w r
  have hK : IsCompact K := by
    rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
    have : UpperHalfPlane.coe '' K = Metric.closedBall w r := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hz
        exact ⟨⟨z, hsub hz⟩, hz, rfl⟩
    rw [this]
    exact isCompact_closedBall _ _
  obtain ⟨u, hu, hbd⟩ := poincareSeries_bound Γ hk n hK
  have hball : Metric.ball w r ⊆ {z : ℂ | 0 < z.im} :=
    Metric.ball_subset_closedBall.trans hsub
  have hdiff : DifferentiableOn ℂ
      (fun w' : ℂ => ∑' x : StabInftyCosets Γ, (poincareTerm Γ k n x ∘ ofComplex) w')
      (Metric.ball w r) := by
    refine differentiableOn_tsum_of_summable_norm hu (fun x => ?_) Metric.isOpen_ball
      (fun x w' hw'' => ?_)
    · exact (UpperHalfPlane.mdifferentiable_iff.mp (poincareTerm_mdifferentiable Γ k n x)).mono hball
    · have him : 0 < w'.im := hball hw''
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos him]
      exact hbd x _ (Metric.ball_subset_closedBall hw'')
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0))).differentiableWithinAt

private lemma mul_inv_apply_10 (x y : SL(2, ℤ)) :
    ((x * y⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = x 1 0 * y 1 1 - x 1 1 * y 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The bottom row of a representative determines the coset. -/
lemma coset_eq_of_bottom_row {a b : StabInftyCosets Γ}
    (h0 : (a.out : SL(2, ℤ)) 1 0 = (b.out : SL(2, ℤ)) 1 0)
    (h1 : (a.out : SL(2, ℤ)) 1 1 = (b.out : SL(2, ℤ)) 1 1) : a = b := by
  have hrel : b.out * a.out⁻¹ ∈ stabInfty Γ := by
    show ((b.out * a.out⁻¹ : Γ) : SL(2, ℤ)) 1 0 = 0
    refine (mul_inv_apply_10 _ _).trans ?_
    rw [← h0, ← h1]
    ring
  have : (Quotient.mk _ a.out : StabInftyCosets Γ) = Quotient.mk _ b.out :=
    Quotient.sound (QuotientGroup.rightRel_apply.mpr hrel)
  simpa using this

/-- The bottom row of `out x * σ` is injective in the coset `x`. -/
lemma bottomRow_injective (σ : SL(2, ℤ)) :
    Function.Injective (fun x : StabInftyCosets Γ =>
      (![((x.out : SL(2, ℤ)) * σ) 1 0, ((x.out : SL(2, ℤ)) * σ) 1 1] : Fin 2 → ℤ)) := by
  intro a b hab
  have h0 : ((a.out : SL(2, ℤ)) * σ) 1 0 = ((b.out : SL(2, ℤ)) * σ) 1 0 := by
    simpa using congrFun hab 0
  have h1 : ((a.out : SL(2, ℤ)) * σ) 1 1 = ((b.out : SL(2, ℤ)) * σ) 1 1 := by
    simpa using congrFun hab 1
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h0 h1
  have key0 : ∀ g : SL(2, ℤ), g 1 0 = (g 1 0 * σ 0 0 + g 1 1 * σ 1 0) * σ 1 1 -
      (g 1 0 * σ 0 1 + g 1 1 * σ 1 1) * σ 1 0 := fun g => by
    linear_combination (-(g 1 0)) * hdet
  have key1 : ∀ g : SL(2, ℤ), g 1 1 = -(g 1 0 * σ 0 0 + g 1 1 * σ 1 0) * σ 0 1 +
      (g 1 0 * σ 0 1 + g 1 1 * σ 1 1) * σ 0 0 := fun g => by
    linear_combination (-(g 1 1)) * hdet
  apply coset_eq_of_bottom_row
  · rw [key0 (a.out : SL(2, ℤ)), key0 (b.out : SL(2, ℤ)), h0, h1]
  · rw [key1 (a.out : SL(2, ℤ)), key1 (b.out : SL(2, ℤ)), h0, h1]

/-- A summable bound for the twisted summands on a vertical strip. -/
lemma exists_strip_bound {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (σ : SL(2, ℤ)) (A : ℝ) :
    ∃ u : StabInftyCosets Γ → ℝ, Summable u ∧ ∀ x, ∀ z ∈ UpperHalfPlane.verticalStrip A 1,
      ‖poincareSummand Γ k n ((x.out : SL(2, ℤ)) * σ) z‖ ≤ u x := by
  have hk' : (2 : ℝ) < 2 * k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨fun x ↦ EisensteinSeries.r ⟨⟨A, 1⟩, one_pos⟩ ^ (-(2 * k : ℝ)) *
    ‖(![((x.out : SL(2, ℤ)) * σ) 1 0, ((x.out : SL(2, ℤ)) * σ) 1 1] : Fin 2 → ℤ)‖ ^ (-(2 * k : ℝ)),
    ?_, ?_⟩
  · exact ((EisensteinSeries.summable_one_div_norm_rpow hk').comp_injective
      (bottomRow_injective Γ σ)).mul_left _
  · intro x z hz
    refine (poincareSummand_norm_le Γ k n _ z).trans ?_
    exact EisensteinSeries.summand_bound_of_mem_verticalStrip (by positivity)
      (![((x.out : SL(2, ℤ)) * σ) 1 0, ((x.out : SL(2, ℤ)) * σ) 1 1] : Fin 2 → ℤ) one_pos hz

/-- `Im z → ∞` along `atImInfty`. -/
lemma tendsto_im_atImInfty : Tendsto (fun z : ℍ => z.im) atImInfty atTop :=
  Filter.tendsto_comap

/-- Summand for a matrix with lower left entry `0`: a pure exponential. -/
lemma summand_of_lower_zero (k n : ℕ) {ρ : SL(2, ℤ)} (h : ρ 1 0 = 0) :
    ∃ t : ℝ, ∀ z : ℍ, poincareSummand Γ k n ρ z =
      cexp (2 * π * Complex.I * n * ((z : ℂ) + t) / widthAtInfty Γ) := by
  obtain ⟨ε, hε, h00, h11⟩ := sl_lower_zero ρ h
  refine ⟨((ε * ρ 0 1 : ℤ) : ℝ), fun z => ?_⟩
  have hact : ((ρ • z : ℍ) : ℂ) = (z : ℂ) + (((ε * ρ 0 1 : ℤ) : ℝ) : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    have hne : (((algebraMap ℤ ℝ (ρ 1 0)) : ℂ) * (z : ℂ) + (algebraMap ℤ ℝ (ρ 1 1) : ℂ)) ≠ 0 := by
      rcases hε with rfl | rfl <;> simp [h, h11]
    rw [div_eq_iff hne]
    rcases hε with rfl | rfl <;> simp [h, h11, h00]; ring
  have hε2 : (ε : ℂ) ^ (-(2 * k : ℤ)) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · rw [Int.cast_neg, Int.cast_one]
      exact (Even.neg_zpow ⟨-(k : ℤ), by ring⟩ _).trans (one_zpow _)
  have hd : ((ρ 1 0 : ℤ) : ℂ) * z + ((ρ 1 1 : ℤ) : ℂ) = ε := by rw [h, h11]; simp
  unfold poincareSummand
  rw [hact, hd, hε2, mul_one]

/-- The pointwise limits of the summands as `Im z → ∞`. -/
lemma tendsto_summand [Γ.FiniteIndex] (k n : ℕ) (hk : 0 < k) (ρ : SL(2, ℤ)) :
    Tendsto (poincareSummand Γ k n ρ) atImInfty (𝓝 (if n = 0 ∧ ρ 1 0 = 0 then 1 else 0)) := by
  by_cases hc : ρ 1 0 = 0
  · obtain ⟨t, ht⟩ := summand_of_lower_zero Γ k n hc
    have : poincareSummand Γ k n ρ = fun z : ℍ => cexp (2 * π * Complex.I * n * ((z : ℂ) + t) /
        widthAtInfty Γ) := funext ht
    rw [this]
    by_cases hn : n = 0
    · subst hn
      simp [hc]
    · have hh : 0 < widthAtInfty Γ := Subgroup.widthInfty_pos _
      simp only [hn, false_and, ite_false]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : ∀ z : ℍ, ‖cexp (2 * π * Complex.I * n * ((z : ℂ) + t) / widthAtInfty Γ)‖ =
          Real.exp (-(2 * π * n / widthAtInfty Γ) * z.im) := by
        intro z
        rw [Complex.norm_exp]
        congr 1
        rw [show (2 * π * Complex.I * n * ((z : ℂ) + t) / (widthAtInfty Γ : ℂ)) =
          (((2 * π * n / widthAtInfty Γ : ℝ)) : ℂ) * (Complex.I * ((z : ℂ) + t)) by
            push_cast; ring]
        rw [Complex.re_ofReal_mul]
        simp
      simp_rw [hnorm]
      have hpos : 0 < 2 * π * n / widthAtInfty Γ := by
        have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      exact Real.tendsto_exp_atBot.comp
        (Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_im_atImInfty)
  · simp only [hc, and_false, ite_false]
    have hc' : 0 < |((ρ 1 0 : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast hc)
    have h1 : Tendsto (fun z : ℍ => |((ρ 1 0 : ℤ) : ℝ)| * z.im) atImInfty atTop :=
      Filter.Tendsto.const_mul_atTop hc' tendsto_im_atImInfty
    have h2 : Tendsto (fun z : ℍ => (|((ρ 1 0 : ℤ) : ℝ)| * z.im) ^ (-(2 * k : ℝ))) atImInfty
        (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by positivity)).comp h1
    refine squeeze_zero_norm (fun z => ?_) h2
    refine (poincareSummand_norm_le Γ k n ρ z).trans ?_
    have hle : |((ρ 1 0 : ℤ) : ℝ)| * z.im ≤ ‖((ρ 1 0 : ℤ) : ℂ) * z + (ρ 1 1 : ℤ)‖ := by
      have := Complex.abs_im_le_norm (((ρ 1 0 : ℤ) : ℂ) * z + (ρ 1 1 : ℤ))
      simpa [abs_mul, abs_of_pos z.im_pos] using this
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by
      have : (0 : ℝ) < k := by exact_mod_cast hk
      linarith)

/-- Lower left entry of a product with an upper triangular matrix. -/
lemma lower_zero_mul (u w : SL(2, ℤ)) (h : u 1 0 = 0) : (u * w) 1 0 = u 1 1 * w 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, h]

/-- The inverse of an upper triangular matrix is upper triangular. -/
lemma inv_lower_zero (u : SL(2, ℤ)) (h : u 1 0 = 0) : (u⁻¹) 1 0 = 0 := by
  simp [h]

/-- Cosets whose representatives have proportional bottom rows are equal. -/
lemma coset_eq_of_cross {a b : StabInftyCosets Γ}
    (h : (b.out : SL(2, ℤ)) 1 0 * (a.out : SL(2, ℤ)) 1 1 =
      (b.out : SL(2, ℤ)) 1 1 * (a.out : SL(2, ℤ)) 1 0) : a = b := by
  have hrel : b.out * a.out⁻¹ ∈ stabInfty Γ := by
    show ((b.out * a.out⁻¹ : Γ) : SL(2, ℤ)) 1 0 = 0
    refine (mul_inv_apply_10 _ _).trans ?_
    linarith
  have : (Quotient.mk _ a.out : StabInftyCosets Γ) = Quotient.mk _ b.out :=
    Quotient.sound (QuotientGroup.rightRel_apply.mpr hrel)
  simpa using this

/-- At most one coset has `(out x * σ)` upper triangular. -/
lemma coset_unique (σ : SL(2, ℤ)) {x y : StabInftyCosets Γ}
    (hx : ((x.out : SL(2, ℤ)) * σ) 1 0 = 0) (hy : ((y.out : SL(2, ℤ)) * σ) 1 0 = 0) : x = y := by
  have hdet := σ.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hx hy
  apply coset_eq_of_cross
  set X := (y.out : SL(2, ℤ)) 1 0 * (x.out : SL(2, ℤ)) 1 1 -
    (y.out : SL(2, ℤ)) 1 1 * (x.out : SL(2, ℤ)) 1 0 with hX
  have hX0 : X * σ 0 0 = 0 := by
    rw [hX]
    linear_combination ((x.out : SL(2, ℤ)) 1 1) * hy - ((y.out : SL(2, ℤ)) 1 1) * hx
  have hX1 : X * σ 1 0 = 0 := by
    rw [hX]
    linear_combination ((y.out : SL(2, ℤ)) 1 0) * hx - ((x.out : SL(2, ℤ)) 1 0) * hy
  have : X = 0 := by
    linear_combination σ 1 1 * hX0 - σ 0 1 * hX1 - X * hdet
  linarith

/-- Some coset has `out x * σ` upper triangular iff some `δ ∈ Γ` has `δ σ` upper triangular. -/
lemma exists_coset_iff (σ : SL(2, ℤ)) :
    (∃ x : StabInftyCosets Γ, ((x.out : SL(2, ℤ)) * σ) 1 0 = 0) ↔
      ∃ δ ∈ Γ, (δ * σ) 1 0 = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.out, x.out.2, hx⟩
  · rintro ⟨δ, hδ, h⟩
    refine ⟨Quotient.mk _ (⟨δ, hδ⟩ : Γ), ?_⟩
    set x : StabInftyCosets Γ := Quotient.mk _ (⟨δ, hδ⟩ : Γ) with hxdef
    have hmk : (Quotient.mk _ x.out : StabInftyCosets Γ) = Quotient.mk _ (⟨δ, hδ⟩ : Γ) :=
      Quotient.out_eq x
    have hrel : (⟨δ, hδ⟩ : Γ) * x.out⁻¹ ∈ stabInfty Γ :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hmk)
    have hβ : (((⟨δ, hδ⟩ : Γ) * x.out⁻¹ : Γ) : SL(2, ℤ)) 1 0 = 0 := hrel
    obtain ⟨β, hβ0, hβx⟩ : ∃ β : SL(2, ℤ), β 1 0 = 0 ∧ (x.out : SL(2, ℤ)) = β * δ := by
      refine ⟨(((⟨δ, hδ⟩ : Γ) * x.out⁻¹ : Γ) : SL(2, ℤ))⁻¹, inv_lower_zero _ hβ, by simp⟩
    rw [hβx, mul_assoc, lower_zero_mul _ _ hβ0, h, mul_zero]

/-- The sum of the limiting values. -/
lemma tsum_indicator (σ : SL(2, ℤ)) (n : ℕ) :
    ∑' x : StabInftyCosets Γ, (if n = 0 ∧ ((x.out : SL(2, ℤ)) * σ) 1 0 = 0 then (1 : ℂ) else 0) =
      if n = 0 ∧ ∃ δ ∈ Γ, (δ * σ) 1 0 = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp only [hn, true_and]
    by_cases hex : ∃ x : StabInftyCosets Γ, ((x.out : SL(2, ℤ)) * σ) 1 0 = 0
    · obtain ⟨x0, hx0⟩ := hex
      rw [tsum_eq_single x0 (fun y hy => ite_eq_right (fun h => hy (coset_unique Γ σ h hx0))),
        ite_eq_left hx0, ite_eq_left ((exists_coset_iff Γ σ).mp ⟨x0, hx0⟩)]
    · rw [ite_eq_right (fun h => hex ((exists_coset_iff Γ σ).mpr h))]
      have h0 : ∀ x : StabInftyCosets Γ,
          (if ((x.out : SL(2, ℤ)) * σ) 1 0 = 0 then (1 : ℂ) else 0) = 0 :=
        fun x => ite_eq_right (fun h => hex ⟨x, h⟩)
      simp only [h0]
      exact tsum_zero
  · simp [hn]

/-- The Poincaré slash is periodic under `T^j` when `σ T^j σ⁻¹ ∈ Γ`. -/
lemma slash_slash_of_conj_mem (k n : ℕ) (σ : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : σ * g * σ⁻¹ ∈ Γ) :
    (poincareSeries Γ k n ∣[(2 * k : ℤ)] σ) ∣[(2 * k : ℤ)] g = poincareSeries Γ k n ∣[(2 * k : ℤ)] σ := by
  rw [← SlashAction.slash_mul, show σ * g = (σ * g * σ⁻¹) * σ by group, SlashAction.slash_mul,
    poincareSeries_slash_of_mem Γ k n hg]

/-- A power of `T` conjugated into `Γ`. -/
lemma exists_period [Γ.FiniteIndex] (σ : SL(2, ℤ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ j : ℤ, σ * ModularGroup.T ^ ((N : ℤ) * j) * σ⁻¹ ∈ Γ := by
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := Γ)) (σ * ModularGroup.T * σ⁻¹)
  refine ⟨N, hN, fun j => ?_⟩
  rw [conj_zpow.symm, zpow_mul, zpow_natCast]
  exact Subgroup.zpow_mem _ hmem j

/-- Slash by `T^j` is evaluation at `T^j z`. -/
lemma slash_T_zpow_apply (k : ℤ) (F : ℍ → ℂ) (j : ℤ) (z : ℍ) :
    (F ∣[k] (ModularGroup.T ^ j)) z = F (ModularGroup.T ^ j • z) := by
  rw [SL_slash_apply]
  have : UpperHalfPlane.denom ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1 := by
    rw [denom_sl]
    simp [ModularGroup.coe_T_zpow]
  rw [this]
  simp

/-- Limit of the slashed Poincaré series along a vertical strip. -/
lemma tendsto_slash_strip [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (σ : SL(2, ℤ)) (A : ℝ) :
    Tendsto (poincareSeries Γ k n ∣[(2 * k : ℤ)] σ)
      (atImInfty ⊓ 𝓟 (UpperHalfPlane.verticalStrip A 1))
      (𝓝 (if n = 0 ∧ ∃ δ ∈ Γ, (δ * σ) 1 0 = 0 then 1 else 0)) := by
  obtain ⟨u, hu, hbd⟩ := exists_strip_bound Γ hk n σ A
  have h := tendsto_tsum_of_dominated_convergence
    (𝓕 := atImInfty ⊓ 𝓟 (UpperHalfPlane.verticalStrip A 1))
    (f := fun z (x : StabInftyCosets Γ) => poincareSummand Γ k n ((x.out : SL(2, ℤ)) * σ) z)
    (g := fun x => if n = 0 ∧ ((x.out : SL(2, ℤ)) * σ) 1 0 = 0 then (1 : ℂ) else 0)
    (bound := u) hu
    (fun x => (tendsto_summand Γ k n (by omega) _).mono_left inf_le_left)
    (eventually_inf_principal.mpr (Eventually.of_forall fun z hz x => hbd x z hz))
  rw [tsum_indicator] at h
  refine h.congr (fun z => ?_)
  exact (poincareSeries_slash_apply Γ k n σ z).symm

/-- **Behaviour at a cusp**: the limit of `φ_n | σ` as `Im z → ∞`. -/
theorem poincareSeries_tendsto [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (n : ℕ) (σ : SL(2, ℤ)) :
    Tendsto (poincareSeries Γ k n ∣[(2 * k : ℤ)] σ) atImInfty
      (𝓝 (if n = 0 ∧ ∃ δ ∈ Γ, (δ * σ) 1 0 = 0 then 1 else 0)) := by
  obtain ⟨N, hN, hper⟩ := exists_period Γ σ
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h2 := Metric.tendsto_nhds.mp (tendsto_slash_strip Γ hk n σ N) ε hε
  rw [eventually_inf_principal] at h2
  obtain ⟨A0, hA0⟩ := (atImInfty_mem _).mp h2
  refine (atImInfty_mem _).mpr ⟨max A0 1, fun z hz => ?_⟩
  show dist ((poincareSeries Γ k n ∣[(2 * k : ℤ)] σ) z) _ < ε
  obtain ⟨j, hj⟩ := ModularGroup_T_zpow_mem_verticalStrip z hN
  have hz1 : 1 ≤ z.im := (le_max_right _ _).trans hz
  have hmem : ModularGroup.T ^ ((N : ℤ) * j) • z ∈ UpperHalfPlane.verticalStrip N 1 :=
    verticalStrip_anti_right N hz1 hj
  have hF : (poincareSeries Γ k n ∣[(2 * k : ℤ)] σ) (ModularGroup.T ^ ((N : ℤ) * j) • z) =
      (poincareSeries Γ k n ∣[(2 * k : ℤ)] σ) z := by
    exact (slash_T_zpow_apply _ _ _ z).symm.trans
      (congrFun (slash_slash_of_conj_mem Γ k n σ (hper j)) z)
  have h3 := hA0 (ModularGroup.T ^ ((N : ℤ) * j) • z) (by
    rw [im_T_zpow_smul]; exact (le_max_left _ _).trans hz)
  simp only [Set.mem_ofPred_eq] at h3
  have h4 := h3 hmem
  rwa [hF] at h4

/-- **Theorem 4.28** (Gunning, III.9): for `2k > 2` and `n ≥ 0`, `φ_n` is a modular form of weight `2k` for `Γ`,
a cusp form for `n ≥ 1`, and `φ_0` has the stated values at the cusps. -/
@[kb "milne2017mf" "Section 4, Theorem 4.28 (pdf p. 62)"]
theorem poincareSeriesModular (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) :
    PoincareSeriesModular Γ k := by
  have hslash : ∀ n : ℕ, ∀ g ∈ Γ.map (mapGL ℝ),
      poincareSeries Γ k n ∣[((2 * k : ℕ) : ℤ)] g = poincareSeries Γ k n := by
    intro n g hg
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hg
    have := poincareSeries_slash_of_mem Γ k n hδ
    push_cast
    exact this
  let SIF : ∀ n : ℕ, SlashInvariantForm (Γ.map (mapGL ℝ)) ((2 * k : ℕ) : ℤ) := fun n =>
    { toFun := poincareSeries Γ k n
      slash_action_eq' := hslash n }
  have hcast : ((2 * k : ℕ) : ℤ) = 2 * k := by push_cast; ring
  have bdd : ∀ n : ℕ, ∀ {c : OnePoint ℝ}, IsCusp c (Γ.map (mapGL ℝ)) →
      c.IsBoundedAt (poincareSeries Γ k n) ((2 * k : ℕ) : ℤ) := by
    intro n c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [hcast]
    exact (poincareSeries_tendsto Γ hk n γ).isBigO_one ℝ
  refine ⟨fun n => ⟨⟨SIF n, poincareSeries_mdifferentiable Γ hk n, bdd n⟩, rfl⟩,
    fun n hn => ⟨⟨SIF n, poincareSeries_mdifferentiable Γ hk n, ?_⟩, rfl⟩, fun γ => ?_⟩
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    show IsZeroAtImInfty (poincareSeries Γ k n ∣[((2 * k : ℕ) : ℤ)] γ)
    rw [hcast]
    have h := poincareSeries_tendsto Γ hk n γ
    have hn0 : n ≠ 0 := by omega
    have h' : Tendsto (poincareSeries Γ k n ∣[(2 * k : ℤ)] γ) atImInfty (𝓝 0) := by
      simpa [hn0] using h
    exact h'
  · simpa using poincareSeries_tendsto Γ hk 0 γ

/-- **Lemma 4.35**, unconditionally: for $2k > 2$ and $\sigma \in \Gamma(1)$, $\varphi_0|_{2k}\sigma$ is a modular form
of weight $2k$ for $\Gamma(N)$ with value $1$ at the cusp $\sigma^{-1}(i\infty)$ and $0$ at the cusps not equivalent to
it (`poincareSeries_zero_slash` with Theorem 4.28, `poincareSeriesModular`). -/
@[kb "milne2017mf" "Section 4, Lemma 4.35 (pdf p. 65)"]
theorem poincareSeries_zero_slash_Gamma {N k : ℕ} [NeZero N] (hk : 2 ≤ k) (σ : SL(2, ℤ)) :
    (∃ F : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℕ),
      ⇑F = poincareSeries (CongruenceSubgroup.Gamma N) k 0 ∣[(2 * k : ℤ)] σ) ∧
    ∀ γ : SL(2, ℤ), Tendsto ((poincareSeries (CongruenceSubgroup.Gamma N) k 0 ∣[(2 * k : ℤ)] σ) ∣[(2 * k : ℤ)] γ)
      atImInfty (𝓝 (if ∃ δ ∈ CongruenceSubgroup.Gamma N, (δ * σ * γ) 1 0 = 0 then 1 else 0)) :=
  poincareSeries_zero_slash hk (poincareSeriesModular _ hk) σ

/-- **Theorem 4.29 / Corollary 4.34**, conditional only on Theorem 4.33 (`PoincarePetersson`): every cusp form of
weight $2k > 2$ is a linear combination of the Poincaré series $\varphi_n$, $n \ge 1$. -/
@[kb "milne2017mf" "Section 4, Theorem 4.29 and Corollary 4.34 (pdf pp. 62, 64)"]
theorem poincareSeries_span_of_petersson (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k)
    (h33 : PoincarePetersson Γ k) (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) :
    ⇑f ∈ Submodule.span ℂ (Set.range fun n : {n : ℕ // 1 ≤ n} ↦ poincareSeries Γ k n) :=
  poincareSeries_span Γ hk (poincareSeriesModular Γ hk) h33 f

end ModularFormsKB.Milne
