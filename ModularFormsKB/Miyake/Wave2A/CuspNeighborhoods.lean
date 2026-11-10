import ModularFormsKB.Miyake.QuotientSpaces
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Topology.Algebra.ConstMulAction
import ModularFormsKB.Citation
/-!
# Miyake §§1.7–1.8: neighborhoods of cusps and compact quotients

Miyake, *Modular Forms* (Springer 1989), §1.7, pp. 26–27 and §1.8, p. 30.

* Lemma 1.7.4: separation of the horoball neighborhoods of two cusps
  (`ModularFormsKB.Miyake.disjoint_smul_horoRegion`).
* Lemma 1.7.6: a compact subset of `ℍ` misses every `Γ`-translate of a small enough horoball
  neighborhood of a cusp (`ModularFormsKB.Miyake.exists_disjoint_smul_horoRegion`).
* Theorem 1.8.1: if `Γ \ ℍ` is compact, then `Γ` has no cusps, that is, no parabolic elements
  (`ModularFormsKB.Miyake.not_isParabolic_of_compactSpace`).

## Conventions
* A Fuchsian group is a `Subgroup SL(2, ℝ)` with `DiscreteTopology`; `SL(2, ℝ)` acts on `ℍ` by
  Mathlib's Möbius action.
* `U_l = {z ∈ ℍ | Im z > l}` is `horoRegion l`.
* Miyake's hypothesis that `x` is a cusp of `Γ` with `σ x = ∞` and
  `σ Γ_x σ⁻¹ · {±1} = {±τ_h^m}` (`h > 0`) is used only through `±τ_h ∈ σ Γ σ⁻¹`, written
  `σ⁻¹ τ_h σ ∈ Γ ∨ σ⁻¹ (-τ_h) σ ∈ Γ`; the statements are therefore slight generalizations.
  A cusp of `Γ` is a fixed point on `ℝ ∪ {∞}` of a parabolic element of `Γ` (Miyake §1.5), so
  "`Γ` has no cusps" is "`Γ` has no parabolic elements".
* Matrix entries are 0-based: Miyake's `c` is `γ 1 0`.
-/

open Matrix UpperHalfPlane MulAction Filter Topology
open scoped MatrixGroups Pointwise

namespace ModularFormsKB.Miyake

/-- Miyake's horoball neighborhood of `∞`, `U_l = {z ∈ ℍ | Im z > l}`. -/
def horoRegion (l : ℝ) : Set ℍ := {z | l < z.im}

/-- The imaginary part of `g z` for `g ∈ SL₂(ℝ)`: `Im (g z) = Im z / |c z + d|²`. -/
lemma im_smul_SL (g : SL(2, ℝ)) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq ((g 1 0 : ℂ) * z + g 1 1) := by
  have h := congrArg Complex.im (coe_specialLinearGroup_apply g z)
  rw [coe_im] at h
  rw [h, Complex.div_im]
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, coe_re, coe_im, zero_mul, sub_zero,
    add_zero]
  rw [← sub_div]
  congr 1
  linear_combination z.im * hdet

/-- `|c z + d|² ≥ c² (Im z)²`. -/
lemma normSq_denom_ge (c d : ℝ) (z : ℍ) :
    c ^ 2 * z.im ^ 2 ≤ Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, coe_re,
    coe_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im, add_zero]
  nlinarith [sq_nonneg (c * z.re + d)]

/-- The conjugate subgroup `σ Γ σ⁻¹`. -/
def conjSubgroup (σ : SL(2, ℝ)) (Γ : Subgroup SL(2, ℝ)) : Subgroup SL(2, ℝ) :=
  Γ.map (MulAut.conj σ).toMonoidHom

lemma mem_conjSubgroup_iff {σ δ : SL(2, ℝ)} {Γ : Subgroup SL(2, ℝ)} :
    δ ∈ conjSubgroup σ Γ ↔ σ⁻¹ * δ * σ ∈ Γ := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hγ
  · intro h
    exact ⟨σ⁻¹ * δ * σ, h, by simp [MulAut.conj_apply, mul_assoc]⟩

instance (σ : SL(2, ℝ)) (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] :
    DiscreteTopology (conjSubgroup σ Γ) := by
  let e : SL(2, ℝ) ≃ₜ SL(2, ℝ) := (Homeomorph.mulLeft σ⁻¹).trans (Homeomorph.mulRight σ)
  have he : ∀ x, x ∈ conjSubgroup σ Γ ↔ e x ∈ Γ := fun x => by
    rw [mem_conjSubgroup_iff]; rfl
  exact (e.subtype he).isEmbedding.discreteTopology

lemma translationSL_add (s t : ℝ) : translationSL (s + t) = translationSL s * translationSL t := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translationSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma continuous_translationSL : Continuous translationSL := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- Conjugating a translation by an upper triangular element: `δ τ_s δ⁻¹ = τ_{a² s}`. -/
lemma conj_translationSL {δ : SL(2, ℝ)} (hδ : δ 1 0 = 0) (s : ℝ) :
    δ * translationSL s * δ⁻¹ = translationSL (δ 0 0 ^ 2 * s) := by
  obtain ⟨e00, e01, e10, e11⟩ := conj_entries δ (translationSL s) 1 s
    (by simp [translationSL]) (by simp [translationSL]) (by simp [translationSL])
    (by simp [translationSL])
  ext i j
  fin_cases i <;> fin_cases j
  · exact e00.trans (by simp [translationSL, hδ])
  · exact e01.trans (by simp [translationSL, hδ] <;> ring)
  · exact e10.trans (by simp [translationSL, hδ])
  · exact e11.trans (by simp [translationSL, hδ])

/-- A positive translation in `Γ` from `±τ_h ∈ Γ`. -/
lemma exists_translation_mem {Γ : Subgroup SL(2, ℝ)} {h : ℝ} (hh : 0 < h)
    (hτ : translationSL h ∈ Γ ∨ -translationSL h ∈ Γ) : ∃ t > 0, translationSL t ∈ Γ := by
  rcases hτ with H | H
  · exact ⟨h, hh, H⟩
  · refine ⟨h + h, by linarith, ?_⟩
    rw [translationSL_add, ← neg_mul_neg]
    exact Γ.mul_mem H H

/-- In a discrete subgroup containing `±τ_h` (`h > 0`), an element `δ` with `c = 0` has
`|a| = 1` (part of Miyake, Theorem 1.5.4 (2)). -/
lemma abs_apply_zero_zero_eq_one (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] {h : ℝ}
    (hh : 0 < h) (hτ : translationSL h ∈ Γ ∨ -translationSL h ∈ Γ) {δ : SL(2, ℝ)} (hδΓ : δ ∈ Γ)
    (hδ : δ 1 0 = 0) : |δ 0 0| = 1 := by
  obtain ⟨t, ht, htΓ⟩ := exists_translation_mem hh hτ
  have hdet := δ.det_coe
  rw [Matrix.det_fin_two, hδ, mul_zero, sub_zero] at hdet
  have ha0 : δ 0 0 ≠ 0 := by rintro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
  -- reduce to `|a| < 1`
  suffices key : ∀ ε : SL(2, ℝ), ε ∈ Γ → ε 1 0 = 0 → ¬ |ε 0 0| < 1 by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact key δ hδΓ hδ hlt
    · apply key δ⁻¹ (Γ.inv_mem hδΓ)
      · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hδ]
      · simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of,
          Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.empty_val', Matrix.cons_val_fin_one]
        have : δ 1 1 = (δ 0 0)⁻¹ := by field_simp; linarith
        rw [this, abs_inv]
        exact inv_lt_one_of_one_lt₀ hgt
  intro ε hεΓ hε hlt
  have hεdet := ε.det_coe
  rw [Matrix.det_fin_two, hε, mul_zero, sub_zero] at hεdet
  have hε0 : ε 0 0 ≠ 0 := by rintro h0; rw [h0, zero_mul] at hεdet; exact zero_ne_one hεdet
  -- `ε^n τ_t ε^{-n} = τ_{a^{2n} t} ∈ Γ`
  have hpow : ∀ n : ℕ, translationSL ((ε 0 0 ^ 2) ^ n * t) ∈ Γ := by
    intro n
    induction n with
    | zero => simpa using htΓ
    | succ n ih =>
      have := Γ.mul_mem (Γ.mul_mem hεΓ ih) (Γ.inv_mem hεΓ)
      rw [conj_translationSL hε] at this
      rwa [pow_succ, mul_comm _ (ε 0 0 ^ 2), mul_assoc]
  obtain ⟨U, hU, h1U, hUΓ⟩ := exists_isolating Γ Γ.one_mem
  have htend : Tendsto (fun n : ℕ => translationSL ((ε 0 0 ^ 2) ^ n * t)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => (ε 0 0 ^ 2) ^ n * t) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := ε 0 0 ^ 2)
        (by rw [abs_pow]; nlinarith [abs_nonneg (ε 0 0)])
      simpa using this.mul_const t
    have h1 : translationSL 0 = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [translationSL]
    rw [← h1]
    exact (continuous_translationSL.tendsto 0).comp h0
  obtain ⟨n, hn⟩ := (htend.eventually (hU.mem_nhds h1U)).exists
  have := hUΓ _ (hpow n) hn
  have h01 := congrArg (fun m : SL(2, ℝ) => m 0 1) this
  simp [translationSL] at h01
  rcases h01 with h01 | h01
  · exact hε0 h01.1
  · exact ht.ne' h01

/-- The key estimate behind Lemmas 1.7.4 and 1.7.6: if `Γ` is discrete and `±τ_h ∈ Γ`
(`h > 0`), then every `δ ∈ Γ` satisfies `Im (δ u) = Im u` (when `δ ∞ = ∞`) or
`Im (δ u) ≤ h² / Im u` (otherwise). -/
lemma im_smul_eq_or_le (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ] {h : ℝ} (hh : 0 < h)
    (hτ : translationSL h ∈ Γ ∨ -translationSL h ∈ Γ) {δ : SL(2, ℝ)} (hδΓ : δ ∈ Γ) (u : ℍ) :
    (δ 1 0 = 0 ∧ (δ • u).im = u.im) ∨ (δ 1 0 ≠ 0 ∧ (δ • u).im ≤ h ^ 2 / u.im) := by
  by_cases hc : δ 1 0 = 0
  · left
    refine ⟨hc, ?_⟩
    have ha := abs_apply_zero_zero_eq_one Γ hh hτ hδΓ hc
    have hdet := δ.det_coe
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have hd : δ 1 1 ^ 2 = 1 := by
      have : δ 0 0 ^ 2 = 1 := by rw [← sq_abs, ha, one_pow]
      nlinarith [this]
    rw [im_smul_SL, hc]
    simp [Complex.normSq_apply, ← sq, hd]
  · right
    refine ⟨hc, ?_⟩
    have hch : 1 ≤ |δ 1 0 * h| := by
      by_contra hlt
      exact hc (lower_left_eq_zero_of_abs_lt Γ hh hτ hδΓ (not_le.1 hlt))
    have hch2 : 1 ≤ (δ 1 0) ^ 2 * h ^ 2 := by
      have := mul_self_le_mul_self (by norm_num) hch
      nlinarith [abs_mul_abs_self (δ 1 0 * h), this]
    rw [im_smul_SL]
    have hy := u.im_pos
    have hden := normSq_denom_ge (δ 1 0) (δ 1 1) u
    have hc2 : 0 < δ 1 0 ^ 2 := by positivity
    rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hden) hy]
    nlinarith [mul_le_mul_of_nonneg_left hch2 (by positivity : (0:ℝ) ≤ u.im ^ 2)]

/-- `σ⁻¹ (±τ_h) σ ∈ Γ` gives `±τ_h ∈ σ Γ σ⁻¹`. -/
lemma translation_mem_conjSubgroup {Γ : Subgroup SL(2, ℝ)} {σ : SL(2, ℝ)} {h : ℝ}
    (hτ : σ⁻¹ * translationSL h * σ ∈ Γ ∨ σ⁻¹ * (-translationSL h) * σ ∈ Γ) :
    translationSL h ∈ conjSubgroup σ Γ ∨ -translationSL h ∈ conjSubgroup σ Γ := by
  simpa only [mem_conjSubgroup_iff] using hτ

/-- **Miyake, Lemma 1.7.6.** Let `x` be a cusp of `Γ` and `σ ∈ SL₂(ℝ)` with `σ x = ∞`, so that
`±τ_h ∈ σ Γ σ⁻¹` for some `h > 0`. For every compact subset `M` of `ℍ` there is `l > 0` with
`M ∩ γ σ⁻¹ U_l = ∅` for all `γ ∈ Γ`. -/
@[kb "miyake1989" "Lemma 1.7.6, p. 27"]
theorem exists_disjoint_smul_horoRegion (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (σ : SL(2, ℝ)) {h : ℝ} (hh : 0 < h)
    (hτ : σ⁻¹ * translationSL h * σ ∈ Γ ∨ σ⁻¹ * (-translationSL h) * σ ∈ Γ)
    {M : Set ℍ} (hM : IsCompact M) :
    ∃ l > 0, ∀ γ ∈ Γ, Disjoint M ((γ * σ⁻¹) • horoRegion l) := by
  -- bounds for `Im` on the compact set `σ M`
  have hσM : IsCompact (σ • M) := hM.image (continuous_const_smul σ)
  obtain ⟨m, hm, hmM⟩ : ∃ m > 0, ∀ z ∈ σ • M, m ≤ z.im := by
    rcases (σ • M).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hσM.exists_isMinOn hne UpperHalfPlane.continuous_im.continuousOn
      exact ⟨z₀.im, z₀.im_pos, fun z hz => hmin hz⟩
  obtain ⟨Mx, hMx⟩ : ∃ Mx, ∀ z ∈ σ • M, z.im ≤ Mx := by
    obtain ⟨B, hB⟩ := hσM.bddAbove_image UpperHalfPlane.continuous_im.continuousOn
    exact ⟨B, fun z hz => hB ⟨z, hz, rfl⟩⟩
  refine ⟨max (max Mx (h ^ 2 / m)) 1, by positivity, fun γ hγ => ?_⟩
  rw [Set.disjoint_left]
  rintro k hk ⟨u, hu, rfl⟩
  have hu' : max (max Mx (h ^ 2 / m)) 1 < u.im := hu
  have hσk : σ • ((γ * σ⁻¹) • u) ∈ σ • M := Set.smul_mem_smul_set hk
  have hδ : σ * γ * σ⁻¹ ∈ conjSubgroup σ Γ := by
    rw [mem_conjSubgroup_iff]; simpa [mul_assoc] using hγ
  have heq : σ • ((γ * σ⁻¹) • u) = (σ * γ * σ⁻¹) • u := by rw [smul_smul, mul_assoc]
  rw [heq] at hσk
  rcases im_smul_eq_or_le (conjSubgroup σ Γ) hh (translation_mem_conjSubgroup hτ) hδ u with
    ⟨-, him⟩ | ⟨-, him⟩
  · have := hMx _ hσk
    rw [him] at this
    linarith [le_max_left (max Mx (h ^ 2 / m)) 1, le_max_left Mx (h ^ 2 / m)]
  · have h1 := hmM _ hσk
    have hy := u.im_pos
    have h2 : h ^ 2 / m < u.im := lt_of_le_of_lt
      ((le_max_right Mx _).trans (le_max_left _ 1)) hu'
    have h3 : h ^ 2 / u.im < m := by
      rw [div_lt_iff₀ hy]; rw [div_lt_iff₀ hm] at h2; linarith
    linarith

/-- **Miyake, Lemma 1.7.4.** Let `x₁, x₂` be cusps of `Γ` and `σ₁, σ₂ ∈ SL₂(ℝ)` with
`σ₁ x₁ = σ₂ x₂ = ∞` and `±τ_{h_i} ∈ σ_i Γ σ_i⁻¹` (`h_i > 0`). If `l₁, l₂ > 0` and
`l₁ l₂ > h₁ h₂`, then `γ σ₁⁻¹ U_{l₁} ∩ σ₂⁻¹ U_{l₂} = ∅` for every `γ ∈ Γ` with `γ x₁ ≠ x₂`.
Here `γ x₁ ≠ x₂` is expressed as `(σ₂ γ σ₁⁻¹) ∞ ≠ ∞`, i.e. a nonzero lower-left entry. -/
@[kb "miyake1989" "Lemma 1.7.4, p. 26"]
theorem disjoint_smul_horoRegion (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    (σ₁ σ₂ : SL(2, ℝ)) {h₁ h₂ l₁ l₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (hτ₁ : σ₁⁻¹ * translationSL h₁ * σ₁ ∈ Γ ∨ σ₁⁻¹ * (-translationSL h₁) * σ₁ ∈ Γ)
    (hτ₂ : σ₂⁻¹ * translationSL h₂ * σ₂ ∈ Γ ∨ σ₂⁻¹ * (-translationSL h₂) * σ₂ ∈ Γ)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (hl : h₁ * h₂ < l₁ * l₂) {γ : SL(2, ℝ)} (hγ : γ ∈ Γ)
    (hx : (σ₂ * γ * σ₁⁻¹) 1 0 ≠ 0) :
    Disjoint ((γ * σ₁⁻¹) • horoRegion l₁) (σ₂⁻¹ • horoRegion l₂) := by
  set δ := σ₂ * γ * σ₁⁻¹ with hδdef
  rw [Set.disjoint_left]
  rintro z ⟨w, hw, rfl⟩ ⟨v, hv, hvz⟩
  have hw' : l₁ < w.im := hw
  have hv' : l₂ < v.im := hv
  -- `δ w = v`
  have hδw : δ • w = v := by
    have h' : (γ * σ₁⁻¹) • w = σ₂⁻¹ • v := hvz.symm
    rw [hδdef, mul_assoc, mul_smul, h', smul_inv_smul]
  set c := δ 1 0 with hc
  -- `Im (δ w) ≤ 1 / (c² Im w)`, hence `c² l₁ l₂ < 1`
  have hcl : c ^ 2 * (l₁ * l₂) < 1 := by
    have him := im_smul_SL δ w
    rw [hδw] at him
    have hden := normSq_denom_ge c (δ 1 1) w
    have hy := w.im_pos
    have hc2 : 0 < c ^ 2 := by positivity
    have hpos : 0 < c ^ 2 * w.im ^ 2 := by positivity
    have hle : v.im ≤ 1 / (c ^ 2 * w.im) := by
      rw [him, div_le_div_iff₀ (lt_of_lt_of_le hpos hden) (by positivity)]
      nlinarith
    have : l₂ * (c ^ 2 * w.im) < 1 := by
      rw [le_div_iff₀ (by positivity)] at hle
      nlinarith [mul_lt_mul_of_pos_right hv' (by positivity : 0 < c ^ 2 * w.im)]
    nlinarith [mul_lt_mul_of_pos_left hw' (by positivity : 0 < c ^ 2 * l₂)]
  -- `γ₁ = ±τ_{h₁} ∈ σ₁ Γ σ₁⁻¹` is conjugated by `δ` into `σ₂ Γ σ₂⁻¹`
  obtain ⟨ε, hε, hεmem⟩ : ∃ ε : SL(2, ℝ), (ε = translationSL h₁ ∨ ε = -translationSL h₁) ∧
      σ₁⁻¹ * ε * σ₁ ∈ Γ := by
    rcases hτ₁ with H | H
    · exact ⟨_, Or.inl rfl, H⟩
    · exact ⟨_, Or.inr rfl, H⟩
  have hmem : δ * ε * δ⁻¹ ∈ conjSubgroup σ₂ Γ := by
    rw [mem_conjSubgroup_iff, hδdef]
    have : σ₂⁻¹ * (σ₂ * γ * σ₁⁻¹ * ε * (σ₂ * γ * σ₁⁻¹)⁻¹) * σ₂ =
        γ * (σ₁⁻¹ * ε * σ₁) * γ⁻¹ := by group
    rw [this]
    exact Γ.mul_mem (Γ.mul_mem hγ hεmem) (Γ.inv_mem hγ)
  -- its lower-left entry is `∓ c² h₁`
  have hentry : |(δ * ε * δ⁻¹) 1 0| = c ^ 2 * h₁ := by
    rcases hε with rfl | rfl
    · obtain ⟨-, -, h10, -⟩ := conj_entries δ (translationSL h₁) 1 h₁
        (by simp [translationSL]) (by simp [translationSL]) (by simp [translationSL])
        (by simp [translationSL])
      rw [h10, hc, abs_eq (by positivity)]
      first | (left; ring1) | (right; ring1)
    · obtain ⟨-, -, h10, -⟩ := conj_entries δ (-translationSL h₁) (-1) h₁
        rfl (by show -h₁ = -1 * h₁; ring) (by show -(0:ℝ) = 0; simp) rfl
      rw [h10, hc, abs_eq (by positivity)]
      first | (left; ring) | (right; ring)
  have hlt : |(δ * ε * δ⁻¹) 1 0 * h₂| < 1 := by
    rw [abs_mul, hentry, abs_of_pos hh₂]
    have : c ^ 2 * (h₁ * h₂) < c ^ 2 * (l₁ * l₂) ∨ c = 0 := by
      by_cases hc0 : c = 0
      · exact Or.inr hc0
      · exact Or.inl (mul_lt_mul_of_pos_left hl (by positivity))
    rcases this with H | H
    · nlinarith
    · simp [H]
  have h0 := lower_left_eq_zero_of_abs_lt (conjSubgroup σ₂ Γ) hh₂
    (translation_mem_conjSubgroup hτ₂) hmem hlt
  have : |(δ * ε * δ⁻¹) 1 0| = 0 := by rw [h0, abs_zero]
  rw [hentry] at this
  have : c ^ 2 = 0 := by
    rcases mul_eq_zero.1 this with H | H
    · exact H
    · exact absurd H hh₁.ne'
  exact hx (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)

/-- Conjugation in `SL₂(ℝ)` preserves parabolicity. -/
lemma isParabolic_conj (σ γ : SL(2, ℝ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic) :
    ((σ * γ * σ⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic := by
  have h := (Matrix.GeneralLinearGroup.isParabolic_conj_iff
    (Matrix.SpecialLinearGroup.mapGL ℝ σ) (Matrix.SpecialLinearGroup.mapGL ℝ γ)).2 hγ
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact h

/-- A parabolic element of `SL₂(ℝ)` fixing `∞` is `±τ_b` with `b ≠ 0`. -/
lemma eq_translationSL_of_isParabolic {δ : SL(2, ℝ)}
    (hδ : (δ : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic) (h10 : δ 1 0 = 0) :
    ∃ b ≠ 0, δ = translationSL b ∨ δ = -translationSL b := by
  obtain ⟨had, hb⟩ := (Matrix.isParabolic_iff_of_upperTriangular h10).1 hδ
  have hdet := δ.det_coe
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  have ha : (δ 0 0 - 1) * (δ 0 0 + 1) = 0 := by
    have : δ 0 0 * δ 1 1 = 1 := hdet
    rw [← had] at this
    linear_combination this
  rcases mul_eq_zero.1 ha with ha | ha
  · refine ⟨δ 0 1, hb, Or.inl ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [translationSL, h10] <;> linarith
  · refine ⟨-δ 0 1, neg_ne_zero.2 hb, Or.inr (neg_eq_iff_eq_neg.1 ?_)⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [translationSL, h10] <;> linarith

/-- A parabolic element of `SL₂(ℝ)` is conjugate in `SL₂(ℝ)` to an element fixing `∞`: with
`x = (a - d) / 2c` its fixed point (when `c ≠ 0`) and `σ = [[0, -1], [1, -x]]`, `σ x = ∞`. -/
lemma exists_conj_lower_left_eq_zero {γ : SL(2, ℝ)}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic) :
    ∃ σ : SL(2, ℝ), (σ * γ * σ⁻¹) 1 0 = 0 := by
  by_cases hc : γ 1 0 = 0
  · exact ⟨1, by simpa using hc⟩
  set x := (γ 0 0 - γ 1 1) / (2 * γ 1 0) with hx
  let σ : SL(2, ℝ) := ⟨!![0, -1; 1, -x], by simp [Matrix.det_fin_two_of]⟩
  refine ⟨σ, ?_⟩
  have hdisc := hγ.2
  rw [Matrix.discr_fin_two, Matrix.trace_fin_two, γ.det_coe] at hdisc
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hσv : (σ : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; 1, -x] := rfl
  have key : (σ * γ * σ⁻¹) 1 0 = γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x - γ 0 1 := by
    change ((σ : Matrix (Fin 2) (Fin 2) ℝ) * γ * (σ⁻¹ : SL(2, ℝ))) 1 0 = _
    rw [Matrix.SpecialLinearGroup.coe_inv, hσv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    ring
  rw [key, hx]
  field_simp
  linear_combination (-1 : ℝ) * hdisc + 4 * hdet

/-- If `Γ \ ℍ` is compact, then some compact `K ⊆ ℍ` meets every `Γ`-orbit. -/
lemma exists_isCompact_forall_exists_smul_mem (Γ : Subgroup SL(2, ℝ))
    [CompactSpace (Quotient (orbitRel Γ ℍ))] :
    ∃ K : Set ℍ, IsCompact K ∧ ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ K := by
  have hopen : IsOpenMap (Quotient.mk (orbitRel Γ ℍ)) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  choose C hCc hCn using fun z : ℍ => exists_compact_mem_nhds z
  have hcover : (Set.univ : Set (Quotient (orbitRel Γ ℍ))) ⊆
      ⋃ z, Quotient.mk (orbitRel Γ ℍ) '' interior (C z) := by
    intro q _
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
    exact Set.mem_iUnion.2 ⟨z, z, mem_interior_iff_mem_nhds.2 (hCn z), rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun z => hopen _ isOpen_interior) hcover
  refine ⟨⋃ z ∈ t, C z, t.isCompact_biUnion fun z _ => hCc z, fun w => ?_⟩
  have hw := ht (Set.mem_univ (Quotient.mk (orbitRel Γ ℍ) w))
  simp only [Set.mem_iUnion, Set.mem_image] at hw
  obtain ⟨z, hz, v, hv, hvw⟩ := hw
  obtain ⟨γ, hγ⟩ := Quotient.exact hvw
  refine ⟨γ, γ.2, Set.mem_iUnion₂.2 ⟨z, hz, interior_subset ?_⟩⟩
  rw [← hγ] at hv
  exact hv

/-- **Miyake, Theorem 1.8.1.** If `Γ \ ℍ` is compact, then `Γ` has no cusps: no element of `Γ`
is parabolic.

Miyake argues with the chart of the Riemann surface `Γ \ ℍ*` at a cusp; here the same
non-compactness is detected by Lemma 1.7.6: a compact set meeting every orbit would have to meet
some translate of every horoball neighborhood of the cusp. -/
@[kb "miyake1989" "Theorem 1.8.1, p. 30"]
theorem not_isParabolic_of_compactSpace (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
    [CompactSpace (Quotient (orbitRel Γ ℍ))] {γ : SL(2, ℝ)} (hγ : γ ∈ Γ) :
    ¬ (γ : Matrix (Fin 2) (Fin 2) ℝ).IsParabolic := by
  intro hpar
  obtain ⟨σ, hσ⟩ := exists_conj_lower_left_eq_zero hpar
  obtain ⟨b, hb, hconj⟩ := eq_translationSL_of_isParabolic (isParabolic_conj σ γ hpar) hσ
  have hτinv : ∀ c : ℝ, (translationSL c)⁻¹ = translationSL (-c) := fun c =>
    inv_eq_of_mul_eq_one_right (by
      rw [← translationSL_add, add_neg_cancel]
      ext i j; fin_cases i <;> fin_cases j <;> simp [translationSL])
  -- a positive translation `±τ_h` with `σ⁻¹ (±τ_h) σ ∈ Γ`
  obtain ⟨h, hh, hτ⟩ : ∃ h : ℝ, 0 < h ∧
      (σ⁻¹ * translationSL h * σ ∈ Γ ∨ σ⁻¹ * (-translationSL h) * σ ∈ Γ) := by
    have hγ' : γ = σ⁻¹ * (σ * γ * σ⁻¹) * σ := by group
    have hγinv' : γ⁻¹ = σ⁻¹ * (σ * γ * σ⁻¹)⁻¹ * σ := by group
    rcases lt_or_gt_of_ne hb with hneg | hpos
    · refine ⟨-b, neg_pos.2 hneg, ?_⟩
      rcases hconj with H | H
      · left; rw [← hτinv, ← H, ← hγinv']; exact Γ.inv_mem hγ
      · right; rw [← hτinv, neg_inv, ← H, ← hγinv']; exact Γ.inv_mem hγ
    · refine ⟨b, hpos, ?_⟩
      rcases hconj with H | H
      · left; rw [← H, ← hγ']; exact hγ
      · right; rw [← H, ← hγ']; exact hγ
  obtain ⟨K, hK, hKΓ⟩ := exists_isCompact_forall_exists_smul_mem Γ
  obtain ⟨l, hl, hdisj⟩ := exists_disjoint_smul_horoRegion Γ σ hh hτ hK
  let u : ℍ := ⟨(l + 1 : ℝ) * Complex.I, by simp; linarith⟩
  have hu : u ∈ horoRegion l := by
    change l < ((l + 1 : ℝ) * Complex.I).im
    simp
  obtain ⟨δ, hδ, hδK⟩ := hKΓ (σ⁻¹ • u)
  refine Set.disjoint_left.1 (hdisj δ hδ) hδK ?_
  rw [← smul_smul]
  exact Set.smul_mem_smul_set (Set.smul_mem_smul_set hu)

end ModularFormsKB.Miyake
