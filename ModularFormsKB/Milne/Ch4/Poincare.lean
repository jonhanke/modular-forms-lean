import ModularFormsKB.Milne.Ch4.Petersson
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import TauCeti.NumberTheory.ModularForms.Petersson.Orthogonal
import ModularFormsKB.Citation
/-!
# Milne, Chapter 4: Poincaré series

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 4, pdf pp. 60–65.

For $\Gamma$ of finite index in $\mathrm{SL}_2(\mathbb Z)$, $\Gamma_\infty$ (`stabInfty`) is the subgroup of $\gamma \in
\Gamma$ fixing $i\infty$ (lower left entry $0$; these are $\pm\begin{pmatrix}1&mh\\0&1\end{pmatrix}$), $h$ is the width
of $i\infty$ (`Subgroup.widthInfty`, allowing $-\begin{pmatrix}1&h\\0&1\end{pmatrix}$). Milne sums over
$\Gamma_0\backslash\Gamma'$ with $\Gamma'$ the image of $\Gamma$ in $\mathrm{PSL}_2$; this is the same as
$\Gamma_\infty\backslash\Gamma$ in $\mathrm{SL}_2(\mathbb Z)$, since the summand has even weight.

## Items
- Definition 4.27 (`poincareSeries`).
- Theorem 4.28: absolute, locally uniform convergence for $2k > 2$ (`poincareSeries_bound`); the rest (modular form,
  cusp form for $n \ge 1$, values of $\varphi_0$ at the cusps) is stated here as `PoincareSeriesModular` and proved in
  `ModularFormsKB/Milne/Ch4/PoincareModular.lean` (`poincareSeriesModular`), where Lemma 4.35 and Corollary 4.34 are
  also restated without it.
- Theorem 4.29 and Corollary 4.34 (`poincareSeries_span`), proved from the named statements
  `PoincareSeriesModular` and `PoincarePetersson` (Theorem 4.33) and the definiteness of the Petersson product.
- Theorem 4.33: stated as `PoincarePetersson`, proved in `ModularFormsKB/Milne/Ch4/Unfolding.lean` (`poincarePetersson`),
  with the unconditional Corollary 4.34 `poincareSeries_span_cuspForm`.
- Lemma 4.35 (`poincareSeries_zero_slash`), proved from `PoincareSeriesModular`.

## Deviations from the book
- Theorem 4.28 and Theorem 4.33 are stated in the book for $2k \ge 2$; the series does not converge absolutely in
  weight $2$ (the proof compares with $\sum|mz+n|^{-2k}$, which needs $2k > 2$), so here $k \ge 2$. That the weight-2
  comparison series diverges is proved in `ModularFormsKB/Milne/Ch4/WeightTwoDivergence.lean`.
- Theorem 4.29 says the $\varphi_n$, $n \ge 1$, span $M_k(\Gamma)$; they are cusp forms, and what is proved
  (Corollary 4.34) is that they span $S_k(\Gamma)$.
Both are recorded in `docs/updates-and-errata.md`.
-/

open UpperHalfPlane Complex Filter Topology ModularForm ModularGroup
open Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Classical

noncomputable section

namespace ModularFormsKB.Milne

variable (Γ : Subgroup SL(2, ℤ))

/-- $\Gamma_\infty$: the elements of $\Gamma$ fixing $i\infty$, i.e. with lower left entry $0$. -/
def stabInfty : Subgroup Γ where
  carrier := {γ | (γ : SL(2, ℤ)) 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  one_mem' := by
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp [ha]

/-- The width $h$ of the cusp $i\infty$ for $\Gamma$. -/
def widthAtInfty : ℝ := (Γ.map (mapGL ℝ)).widthInfty

/-- The summand $\exp(2\pi i n\,\gamma z/h)\,(cz+d)^{-2k}$ of the Poincaré series. -/
def poincareSummand (k n : ℕ) (γ : SL(2, ℤ)) (z : ℍ) : ℂ :=
  cexp (2 * π * Complex.I * n * ((γ • z : ℍ) : ℂ) / widthAtInfty Γ) * ((γ 1 0 : ℂ) * z + γ 1 1) ^ (-(2 * k : ℤ))

/-- An element of `SL(2, ℤ)` with lower left entry `0` has diagonal entries `ε = ±1`. -/
lemma sl_lower_zero (β : SL(2, ℤ)) (h : β 1 0 = 0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ β 0 0 = ε ∧ β 1 1 = ε := by
  have hd := β.det_coe
  rw [Matrix.det_fin_two, h] at hd
  have h2 : β 0 0 * β 1 1 = 1 := by simpa using hd
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2 with ⟨h1, h3⟩ | ⟨h1, h3⟩
  · exact ⟨1, Or.inl rfl, h1, h3⟩
  · exact ⟨-1, Or.inr rfl, h1, h3⟩

/-- The translation part of an element of `Γ_∞` is a period of the image of `Γ`. -/
lemma stabInfty_period {β : SL(2, ℤ)} (hβ : β ∈ Γ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h00 : β 0 0 = ε) (h11 : β 1 1 = ε) (h10 : β 1 0 = 0) :
    ((ε * β 0 1 : ℤ) : ℝ) ∈ (Γ.map (mapGL ℝ)).periods := by
  simp only [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff]
  have hmem : mapGL ℝ β ∈ Γ.map (mapGL ℝ) := Subgroup.mem_map_of_mem _ hβ
  rcases hε with rfl | rfl
  · left
    convert hmem using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.upperRightHom_apply, h00, h11, h10]
  · right
    convert hmem using 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.upperRightHom_apply, h00, h11, h10]

/-- The image of `Γ` in `GL(2, ℝ)` is discrete. -/
local instance discreteImage : DiscreteTopology (Γ.map (mapGL ℝ)) :=
  DiscreteTopology.of_subset
    (s := ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range : Set (GL (Fin 2) ℝ)))
    (inferInstance : DiscreteTopology (MonoidHom.range (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)))
    (by
      rintro _ ⟨g, _, rfl⟩
      exact ⟨g, rfl⟩)

/-- The summand depends only on the coset $\Gamma_\infty\gamma$. -/
theorem poincareSummand_stabInfty (k n : ℕ) {β γ : Γ} (hβ : β ∈ stabInfty Γ) (z : ℍ) :
    poincareSummand Γ k n ((β * γ : Γ) : SL(2, ℤ)) z = poincareSummand Γ k n (γ : SL(2, ℤ)) z := by
  have h10 : (β : SL(2, ℤ)) 1 0 = 0 := hβ
  obtain ⟨ε, hε, h00, h11⟩ := sl_lower_zero _ h10
  have hper := stabInfty_period Γ β.2 hε h00 h11 h10
  have hdisc : DiscreteTopology (Γ.map (mapGL ℝ)).periods := inferInstance
  rw [Subgroup.periods_eq_zmultiples_widthInfty] at hper
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hper
  have hh : (Γ.map (mapGL ℝ)).widthInfty = widthAtInfty Γ := rfl
  rw [hh] at hm
  -- the action
  have hact : (((β : SL(2, ℤ)) • (γ : SL(2, ℤ)) • z : ℍ) : ℂ) = (((γ : SL(2, ℤ)) • z : ℍ) : ℂ) + ((ε * (β : SL(2, ℤ)) 0 1 : ℤ) : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    have hne : (((algebraMap ℤ ℝ ((β : SL(2, ℤ)) 1 0) : ℂ)) * (((γ : SL(2, ℤ)) • z : ℍ) : ℂ) +
        (algebraMap ℤ ℝ ((β : SL(2, ℤ)) 1 1) : ℂ)) ≠ 0 := by
      rcases hε with rfl | rfl <;> simp [h10, h11]
    rw [div_eq_iff hne]
    rcases hε with rfl | rfl <;> simp [h10, h11, h00]; ring
  unfold poincareSummand
  rw [Subgroup.coe_mul, mul_smul, hact]
  have hden : ((((β : SL(2, ℤ)) * (γ : SL(2, ℤ))) 1 0 : ℤ) : ℂ) * (z : ℂ) + (((β : SL(2, ℤ)) * (γ : SL(2, ℤ))) 1 1 : ℤ) =
      (ε : ℂ) * (((γ : SL(2, ℤ)) 1 0 : ℂ) * z + (γ : SL(2, ℤ)) 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  rw [hden, mul_zpow]
  have hε2 : (ε : ℂ) ^ (-(2 * k : ℤ)) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · rw [Int.cast_neg, Int.cast_one]
      exact (Even.neg_zpow ⟨-(k : ℤ), by ring⟩ _).trans (one_zpow _)
  rw [hε2, one_mul]
  refine congrArg₂ (· * ·) ?_ rfl
  by_cases h0 : widthAtInfty Γ = 0
  · simp [h0]
  · have : ((ε * (β : SL(2, ℤ)) 0 1 : ℤ) : ℂ) = (m : ℂ) * (widthAtInfty Γ : ℂ) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hm.symm
      simpa using this
    rw [this]
    have e : 2 * (π : ℂ) * Complex.I * n * ((((γ : SL(2, ℤ)) • z : ℍ) : ℂ) + (m : ℂ) * (widthAtInfty Γ : ℂ)) / (widthAtInfty Γ : ℂ)
        = 2 * (π : ℂ) * Complex.I * n * (((γ : SL(2, ℤ)) • z : ℍ) : ℂ) / (widthAtInfty Γ : ℂ) + ((n * m : ℤ) : ℂ) * (2 * π * Complex.I) := by
      have h0' : (widthAtInfty Γ : ℂ) ≠ 0 := by exact_mod_cast h0
      field_simp
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The cosets $\Gamma_\infty\backslash\Gamma$. -/
abbrev StabInftyCosets : Type := Quotient (QuotientGroup.rightRel (stabInfty Γ))

/-- The summand on a coset $\Gamma_\infty\gamma$. -/
def poincareTerm (k n : ℕ) (x : StabInftyCosets Γ) (z : ℍ) : ℂ :=
  Quotient.lift (fun γ : Γ ↦ poincareSummand Γ k n (γ : SL(2, ℤ)) z)
    (fun a b hab ↦ by
      have h : b * a⁻¹ ∈ stabInfty Γ := QuotientGroup.rightRel_apply.mp hab
      have := poincareSummand_stabInfty Γ k n (γ := a) h z
      rw [inv_mul_cancel_right] at this
      exact this.symm) x

/-- **Definition 4.27**: the Poincaré series of weight $2k$ and character $n$ for $\Gamma$,
$\varphi_n(z) = \sum_{\gamma \in \Gamma_0\backslash\Gamma'} \exp(2\pi i n\,\gamma(z)/h)\,(cz+d)^{-2k}$. -/
@[kb "milne2017mf" "Section 4, Definition 4.27 (pdf p. 61)"]
def poincareSeries (k n : ℕ) (z : ℍ) : ℂ := ∑' x : StabInftyCosets Γ, poincareTerm Γ k n x z

/-- The summand is bounded in norm by `|cz+d|^(-2k)`. -/
lemma poincareSummand_norm_le (k n : ℕ) (γ : SL(2, ℤ)) (z : ℍ) :
    ‖poincareSummand Γ k n γ z‖ ≤ ‖((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)‖ ^ (-(2 * k : ℝ)) := by
  unfold poincareSummand
  have hh : 0 ≤ widthAtInfty Γ := Subgroup.widthInfty_nonneg _
  have h1 : ‖cexp (2 * π * Complex.I * n * ((γ • z : ℍ) : ℂ) / widthAtInfty Γ)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.div_ofReal_re]
    apply div_nonpos_of_nonpos_of_nonneg _ hh
    have := (γ • z).im_pos
    simp only [mul_re, mul_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    have : (0 : ℝ) ≤ π * n * (γ • z).im := by positivity
    nlinarith
  rw [norm_mul, norm_zpow]
  have h2 : ‖((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)‖ ^ (-(2 * k : ℤ)) =
      ‖((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)‖ ^ (-(2 * k : ℝ)) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [h2]
  calc _ ≤ 1 * ‖((γ 1 0 : ℤ) : ℂ) * z + (γ 1 1 : ℤ)‖ ^ (-(2 * k : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := one_mul _

/-- **Theorem 4.28**, convergence: for $2k > 2$ and $n \ge 0$ the series converges absolutely and uniformly on compact
subsets of $\mathbb H$ (Weierstrass bound by a summable sequence on each compact set). -/
@[kb "milne2017mf" "Section 4, Theorem 4.28 (pdf p. 62)"]
theorem poincareSeries_bound [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (n : ℕ) {K : Set ℍ} (hK : IsCompact K) :
    ∃ u : StabInftyCosets Γ → ℝ, Summable u ∧ ∀ x, ∀ z ∈ K, ‖poincareTerm Γ k n x z‖ ≤ u x := by
  obtain ⟨A, B, hB, HABK⟩ := UpperHalfPlane.subset_verticalStrip_of_isCompact hK
  let v : StabInftyCosets Γ → (Fin 2 → ℤ) := fun x ↦ ![(x.out : SL(2, ℤ)) 1 0, (x.out : SL(2, ℤ)) 1 1]
  have hv : Function.Injective v := by
    intro a b hab
    have h0 : (a.out : SL(2, ℤ)) 1 0 = (b.out : SL(2, ℤ)) 1 0 := by simpa [v] using congrFun hab 0
    have h1 : (a.out : SL(2, ℤ)) 1 1 = (b.out : SL(2, ℤ)) 1 1 := by simpa [v] using congrFun hab 1
    have hrel : b.out * a.out⁻¹ ∈ stabInfty Γ := by
      show ((b.out * a.out⁻¹ : Γ) : SL(2, ℤ)) 1 0 = 0
      simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv, Subgroup.coe_inv, Matrix.adjugate_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [← h0, ← h1]
      ring
    have : (Quotient.mk _ a.out : StabInftyCosets Γ) = Quotient.mk _ b.out :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr hrel)
    simpa using this
  have hk' : (2 : ℝ) < 2 * k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨fun x ↦ EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ (-(2 * k : ℝ)) * ‖v x‖ ^ (-(2 * k : ℝ)), ?_, ?_⟩
  · exact ((EisensteinSeries.summable_one_div_norm_rpow hk').comp_injective hv).mul_left _
  · intro x z hz
    have hx : poincareTerm Γ k n x z = poincareSummand Γ k n (x.out : SL(2, ℤ)) z := by
      calc poincareTerm Γ k n x z = poincareTerm Γ k n (Quotient.mk _ x.out) z := by rw [Quotient.out_eq]
        _ = _ := rfl
    rw [hx]
    refine (poincareSummand_norm_le Γ k n _ z).trans ?_
    exact EisensteinSeries.summand_bound_of_mem_verticalStrip (by positivity) (v x) hB (HABK hz)

/-- **Theorem 4.28** (statement; proved as `poincareSeriesModular`): for $2k > 2$, $n \ge 0$, $\varphi_n$ is a modular form of weight $2k$ for
$\Gamma$; (a) $\varphi_0$ takes the value $1$ at the cusps equivalent to $i\infty$ and $0$ at the others (the value of
$f$ at the cusp $\gamma(i\infty)$ is the limit of $f|_{2k}\gamma$ at $i\infty$); (b) $\varphi_n$ is a cusp form for
$n \ge 1$. Milne refers to Gunning 1962, III.9 for the proof. -/
@[kb "milne2017mf" "Section 4, Theorem 4.28 (pdf p. 62)"]
structure PoincareSeriesModular (k : ℕ) : Prop where
  modular : ∀ n : ℕ, ∃ F : ModularForm (Γ.map (mapGL ℝ)) (2 * k : ℕ), ⇑F = poincareSeries Γ k n
  cusp : ∀ n : ℕ, 1 ≤ n → ∃ F : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ), ⇑F = poincareSeries Γ k n
  value : ∀ γ : SL(2, ℤ), Tendsto (poincareSeries Γ k 0 ∣[(2 * k : ℤ)] γ) atImInfty
    (𝓝 (if ∃ δ ∈ Γ, (δ * γ) 1 0 = 0 then 1 else 0))

/-- **Theorem 4.33** (statement; proved as `poincarePetersson`): for a cusp form $f = \sum_{n\ge1}a_ne^{2\pi i nz/h}$ of weight $2k$ for
$\Gamma$ and $n \ge 1$, $\langle f, \varphi_n\rangle = \frac{h^{2k}(2k-2)!}{(4\pi)^{2k-1}}\,n^{1-2k}a_n$. Milne omits the
calculation (Gunning 1962, III.11, Theorem 5). -/
@[kb "milne2017mf" "Section 4, Theorem 4.33 (pdf p. 64)"]
structure PoincarePetersson [Γ.FiniteIndex] (k : ℕ) : Prop where
  formula : ∀ n : ℕ, 1 ≤ n → ∀ f : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ),
    milnePetersson Γ k f (poincareSeries Γ k n) =
      (widthAtInfty Γ : ℂ) ^ (2 * k) * (2 * k - 2).factorial / (4 * π : ℂ) ^ (2 * k - 1) *
        (n : ℂ) ^ (1 - 2 * (k : ℤ)) * (qExpansion (widthAtInfty Γ) f).coeff n

/-- A cusp form of even weight is invariant under translation by the width `h` of `i∞`. -/
lemma cuspForm_vadd_width [Γ.FiniteIndex] {k : ℕ} (g : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) (τ : ℍ) :
    g (widthAtInfty Γ +ᵥ τ) = g τ := by
  have hper : widthAtInfty Γ ∈ (Γ.map (mapGL ℝ)).periods := Subgroup.widthInfty_mem_periods _
  simp only [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff] at hper
  rcases hper with h | h
  · exact SlashInvariantForm.vAdd_apply_of_mem_strictPeriods g τ (Subgroup.mem_strictPeriods_iff.mpr h)
  · have h1 := SlashInvariantForm.slash_action_eqn'' g h τ
    have h2 : Matrix.GeneralLinearGroup.upperRightHom (widthAtInfty Γ) • τ = widthAtInfty Γ +ᵥ τ := by
      ext
      simp [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom, add_comm]
    have h3 : UpperHalfPlane.denom (Matrix.GeneralLinearGroup.upperRightHom (widthAtInfty Γ)) τ = 1 := by
      simp [UpperHalfPlane.denom]
    rw [neg_smul, UpperHalfPlane.denom_neg, h3, h2] at h1
    rw [h1]
    have : ((-1 : ℂ)) ^ (((2 * k : ℕ) : ℤ)) = 1 := Even.neg_one_zpow ⟨k, by push_cast; ring⟩
    rw [this, one_mul]

/-- **Theorem 4.29 / Corollary 4.34**: every cusp form of weight $2k > 2$ for $\Gamma$ is a linear combination of the
Poincaré series $\varphi_n$, $n \ge 1$. Proved from Theorem 4.28 and Theorem 4.33 (named statements): a cusp form
orthogonal to all $\varphi_n$ has all Fourier coefficients $0$. -/
@[kb "milne2017mf" "Section 4, Theorem 4.29 and Corollary 4.34 (pdf pp. 62, 64)"]
theorem poincareSeries_span [Γ.FiniteIndex] {k : ℕ} (_hk : 2 ≤ k) (h28 : PoincareSeriesModular Γ k)
    (h33 : PoincarePetersson Γ k) (f : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) :
    ⇑f ∈ Submodule.span ℂ (Set.range fun n : {n : ℕ // 1 ≤ n} ↦ poincareSeries Γ k n) := by
  classical
  choose F hF using fun n : {n : ℕ // 1 ≤ n} ↦ h28.cusp n.1 n.2
  have hh : 0 < widthAtInfty Γ := Subgroup.widthInfty_pos _
  have hhC : (widthAtInfty Γ : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let V : Submodule ℂ (CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) := Submodule.span ℂ (Set.range F)
  have hperp : TauCeti.CuspForm.peterssonOrthogonal V = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Submodule.mem_bot]
    have hcoef : ∀ n : ℕ, 1 ≤ n → (qExpansion (widthAtInfty Γ) g).coeff n = 0 := by
      intro n hn
      have h1 := TauCeti.CuspForm.mem_peterssonOrthogonal_iff.mp hg (F ⟨n, hn⟩)
        (Submodule.subset_span ⟨_, rfl⟩)
      have h2 := h33.formula n hn g
      rw [← hF ⟨n, hn⟩] at h2
      have h3 : milnePetersson Γ k g (F ⟨n, hn⟩) = CuspForm.peterssonInnerCosets (F ⟨n, hn⟩) g := rfl
      rw [h3, h1] at h2
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hC : (widthAtInfty Γ : ℂ) ^ (2 * k) * ((2 * k - 2).factorial : ℂ) / (4 * π : ℂ) ^ (2 * k - 1) *
          (n : ℂ) ^ (1 - 2 * (k : ℤ)) ≠ 0 :=
        mul_ne_zero (div_ne_zero (mul_ne_zero (pow_ne_zero _ hhC) (by exact_mod_cast Nat.factorial_ne_zero _))
          (pow_ne_zero _ (mul_ne_zero (by norm_num) hpi))) (zpow_ne_zero _ hn0)
      exact (mul_eq_zero.mp h2.symm).resolve_left hC
    have : Fact (IsCusp OnePoint.infty (Γ.map (mapGL ℝ))) := inferInstance
    have hper : Function.Periodic (⇑g ∘ UpperHalfPlane.ofComplex) (widthAtInfty Γ) :=
      UpperHalfPlane.periodic_comp_ofComplex (cuspForm_vadd_width Γ g)
    have hq : qExpansion (widthAtInfty Γ) ⇑g = 0 := by
      ext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [qExpansion_coeff, (CuspFormClass.zero_at_infty g).cuspFunction_apply_zero hh]
      · simpa using hcoef n hn
    have h0 := (qExpansion_eq_zero_iff hh hper (ModularFormClass.holo g)
      (ModularFormClass.bdd_at_infty g)).mp hq
    ext x
    simpa using congrFun h0 x
  have hV : V = ⊤ := by
    have := TauCeti.CuspForm.sup_peterssonOrthogonal_eq_top V
    rwa [hperp, sup_bot_eq] at this
  have hf : f ∈ V := hV ▸ Submodule.mem_top
  refine Submodule.span_induction (p := fun (g : CuspForm (Γ.map (mapGL ℝ)) (2 * k : ℕ)) _ ↦ ⇑g ∈ Submodule.span ℂ (Set.range fun n : {n : ℕ // 1 ≤ n} ↦ poincareSeries Γ k n))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨n, rfl⟩
    rw [hF]
    exact Submodule.subset_span ⟨n, rfl⟩
  · simp
  · intro x y _ _ hx hy
    simpa using add_mem hx hy
  · intro c x _ hx
    simpa using Submodule.smul_mem _ c hx

open ConjAct Pointwise in
/-- Conjugating the image of `Γ(N)` by an element of `SL(2, ℤ)` stays inside it (normality). -/
lemma conj_gamma_le (N : ℕ) (σ : SL(2, ℤ)) :
    (CongruenceSubgroup.Gamma N).map (mapGL ℝ) ≤
      toConjAct (mapGL ℝ σ)⁻¹ • ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) := by
  intro j hj
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  obtain ⟨δ, hδ, hδe⟩ := Subgroup.mem_map.mp hj
  refine Subgroup.mem_map.mpr ⟨σ * δ * σ⁻¹, ?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma_normal N).conj_mem δ hδ σ
  · rw [map_mul, map_mul, hδe]
    simp only [map_inv]

/-- **Lemma 4.35**: let $P$ be a cusp of $\Gamma(N)$, $P \ne i\infty$, and $\sigma \in \Gamma(1)$ with $\sigma(P) =
i\infty$. Then $\varphi(z) = j_\sigma(z)^k\varphi_0(\sigma z) = (\varphi_0|_{2k}\sigma)(z)$ is a modular form of weight
$2k$ for $\Gamma(N)$, with value $1$ at $P = \sigma^{-1}(i\infty)$ and $0$ at every cusp not equivalent to $P$. Proved
from Theorem 4.28 (named statement). -/
@[kb "milne2017mf" "Section 4, Lemma 4.35 (pdf p. 65)"]
theorem poincareSeries_zero_slash {N k : ℕ} [NeZero N] (_hk : 2 ≤ k)
    (h28 : PoincareSeriesModular (CongruenceSubgroup.Gamma N) k) (σ : SL(2, ℤ)) :
    (∃ F : ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (2 * k : ℕ),
      ⇑F = poincareSeries (CongruenceSubgroup.Gamma N) k 0 ∣[(2 * k : ℤ)] σ) ∧
    ∀ γ : SL(2, ℤ), Tendsto ((poincareSeries (CongruenceSubgroup.Gamma N) k 0 ∣[(2 * k : ℤ)] σ) ∣[(2 * k : ℤ)] γ)
      atImInfty (𝓝 (if ∃ δ ∈ CongruenceSubgroup.Gamma N, (δ * σ * γ) 1 0 = 0 then 1 else 0)) := by
  obtain ⟨F₀, hF₀⟩ := h28.modular 0
  refine ⟨⟨ModularForm.restrict (conj_gamma_le N σ) (ModularForm.translate F₀ (mapGL ℝ σ)), ?_⟩, ?_⟩
  · change (⇑F₀ ∣[((2 * k : ℕ) : ℤ)] (mapGL ℝ σ)) = _
    rw [hF₀]
    push_cast
    rfl
  · intro γ
    have h := h28.value (σ * γ)
    rw [SlashAction.slash_mul] at h
    simpa [mul_assoc] using h

end ModularFormsKB.Milne
