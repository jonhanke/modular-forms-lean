import TauCeti.Analysis.Complex.Fuchsian.FreeLocus
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.OpenMapping
import ModularFormsKB.Milne.Ch2.ModularCurves
import ModularFormsKB.Citation
/-!
# Milne, Remark 2.25: the little Picard theorem

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Remark 2.25 (pdf p. 39): the image of a
nonconstant entire function is either `ℂ` or `ℂ` with one point omitted.

## Milne's proof and the version formalized here
Milne: `Y(2)` is `ℂ` minus two points, so an entire function `f` omitting two values is a holomorphic map
`ℂ → Y(2)`; since `ℂ` is simply connected, `f` lifts to the universal covering of `Y(2)`, a disc (here: `ℍ`),
and the lift is constant by Liouville's theorem.

Here the same argument is run with the level-one group in place of `Γ(2)`, because the identification of the
modular curve with an explicit punctured plane is available in level one (Tau Ceti's `j`-biholomorphism of `X(1)`
with the Riemann sphere), while `Y(2) ≅ ℂ ∖ {2 points}` needs the uniformization of a genus-zero curve (a degree-one
function on `X(2)`), which no library has. Let `ℍ'` be the set of points of `ℍ` with trivial stabilizer in
`PSL(2, ℤ)` (the complement of the orbits of `i` and `ρ`). Then:

1. `PSL(2, ℤ)` acts freely and properly discontinuously on `ℍ'`, so `ℍ' → PSL(2, ℤ)\ℍ'` is a covering map
   (Tau Ceti `TauCeti.isCoveringMap_quotientMk_freeLocus`);
2. `j` identifies `PSL(2, ℤ)\ℍ'` with `ℂ ∖ {0, 1728}` (`j` classifies orbits, Tau Ceti `j_eq_j_iff`, is surjective,
   and takes the values `0`, `1728` exactly on the elliptic orbits; it is open by the open mapping theorem), so
   `j : ℍ' → ℂ ∖ {0, 1728}` is a covering map (`isCoveringMap_jFree`);
3. an entire `f` omitting `0` and `1728` lifts through this covering (`ℂ` is simply connected), the lift is
   holomorphic because `j` has holomorphic local inverses on `ℍ'`, and it takes values in `ℍ`, so it is constant
   by Liouville's theorem applied to its Cayley transform.

An entire function omitting two values `a ≠ b` is reduced to this case by an affine change of the target.

## Items
- `mem_freeLocus_iff_j`: `z` has trivial stabilizer iff `j z ∉ {0, 1728}`.
- `jFreeHomeomorph`: `PSL(2, ℤ)\ℍ' ≃ₜ ℂ ∖ {0, 1728}`; `isCoveringMap_jFree`.
- `exists_lift_of_omits`: the holomorphic lift of an entire function omitting `0` and `1728`.
- **`littlePicard`** (Remark 2.25) and `littlePicard'` (the form "omits two values ⇒ constant").
- **`littlePicardStatement`**: the named statement `Milne.LittlePicardStatement` (Ch2/ModularCurves) holds.
-/

open Set Topology Filter MulAction UpperHalfPlane Function
open TauCeti TauCeti.ModularForm TauCeti.ModularGroup
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave10

/-- The values `ℂ ∖ {0, 1728}` of `j` away from the elliptic orbits. -/
def jRegular : Set ℂ := {w | w ≠ 1728 ∧ w ≠ 0}

theorem isOpen_jRegular : IsOpen jRegular :=
  (isOpen_ne.inter isOpen_ne : IsOpen ({w : ℂ | w ≠ 1728} ∩ {w | w ≠ 0}))

/-- A point of `ℍ` has trivial stabilizer in `PSL(2, ℤ)` exactly when `j` does not take the values `1728`, `0` there
(the elliptic orbits are those of `i` and `ρ`). -/
theorem mem_freeLocus_iff_j (z : ℍ) :
    z ∈ freeLocus psl2zToPSL2R.range ℍ ↔ j z ∈ jRegular := by
  rw [TauCeti.mem_freeLocus, stabilizer_psl2zToPSL2RRange_eq_bot_iff]
  simp only [jRegular, mem_ofPred_eq, ne_eq]
  rw [← jQuotient_injective.eq_iff, ← jQuotient_injective.eq_iff, jQuotient_mk, jQuotient_mk, jQuotient_mk,
    j_I, j_ρ]

/-- `j` on the free locus `ℍ'`, with values in `ℂ ∖ {0, 1728}`. -/
def jFree (x : freeLocus psl2zToPSL2R.range ℍ) : jRegular :=
  ⟨j (x : ℍ), (mem_freeLocus_iff_j _).1 x.2⟩

theorem continuous_jFree : Continuous jFree :=
  (j_mdifferentiable.continuous.comp continuous_subtype_val).subtype_mk _

theorem jFree_smul (g : psl2zToPSL2R.range) (x : freeLocus psl2zToPSL2R.range ℍ) : jFree (g • x) = jFree x :=
  Subtype.ext (j_smul_psl2zToPSL2RRange g (x : ℍ))

/-- `j ∘ ofComplex` is analytic on the upper half-plane. -/
theorem analyticOnNhd_j : AnalyticOnNhd ℂ (j ∘ ofComplex) {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.1 j_mdifferentiable).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im)

/-- `j ∘ ofComplex` maps open subsets of the upper half-plane to open sets (open mapping theorem). -/
theorem isOpen_image_j {s : Set ℂ} (hs : s ⊆ {z : ℂ | 0 < z.im}) (ho : IsOpen s) :
    IsOpen ((j ∘ ofComplex) '' s) := by
  refine (analyticOnNhd_j.is_constant_or_isOpen (convex_halfSpace_im_gt 0).isPreconnected).resolve_left ?_ s hs ho
  rintro ⟨w, hw⟩
  have h1 := hw (I : ℂ) I.im_pos
  have h2 := hw (ρ : ℂ) ρ.im_pos
  simp only [comp_apply, ofComplex_apply] at h1 h2
  rw [j_I] at h1
  rw [j_ρ] at h2
  norm_num [← h1] at h2

theorem isOpenMap_jFree : IsOpenMap jFree := by
  intro V hV
  rw [isOpen_jRegular.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]
  have hF : IsOpen (freeLocus psl2zToPSL2R.range ℍ : Set ℍ) := TauCeti.isOpen_freeLocus _ _
  have hV' : IsOpen (((↑) : ℍ → ℂ) '' (((↑) : freeLocus psl2zToPSL2R.range ℍ → ℍ) '' V)) :=
    isOpenEmbedding_coe.isOpenMap _ (hF.isOpenEmbedding_subtypeVal.isOpenMap _ hV)
  convert isOpen_image_j (by rintro _ ⟨_, _, rfl⟩; exact UpperHalfPlane.im_pos _) hV' using 1
  ext w
  simp only [mem_image, jFree, comp_apply]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, by rw [ofComplex_apply]⟩
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by rw [ofComplex_apply]⟩

/-- `j` descended to the free-locus quotient `PSL(2, ℤ)\ℍ'`. -/
def jFreeQuotient : orbitRel.Quotient psl2zToPSL2R.range (freeLocus psl2zToPSL2R.range ℍ) → jRegular :=
  Quotient.lift jFree fun a b h ↦ by
    obtain ⟨g, rfl⟩ := mem_orbit_iff.1 h
    exact jFree_smul g b

theorem jFreeQuotient_mk (x : freeLocus psl2zToPSL2R.range ℍ) : jFreeQuotient (Quotient.mk _ x) = jFree x := rfl

theorem jFreeQuotient_bijective : Bijective jFreeQuotient := by
  refine ⟨fun p q hpq ↦ ?_, fun w ↦ ?_⟩
  · induction p using Quotient.inductionOn with
    | h a =>
    induction q using Quotient.inductionOn with
    | h b =>
    have hab : j (a : ℍ) = j (b : ℍ) := congrArg Subtype.val hpq
    obtain ⟨γ, hγ⟩ := j_eq_j_iff.1 hab
    have hrel : orbitRel psl2zToPSL2R.range ℍ (b : ℍ) (a : ℍ) :=
      orbitRel_psl2zToPSL2RRange_iff_orbitRel_sl.2 (mem_orbit_iff.2 ⟨γ, hγ⟩)
    obtain ⟨g, hg⟩ := mem_orbit_iff.1 hrel
    exact (Quotient.sound (mem_orbit_iff.2 ⟨g, Subtype.ext hg⟩)).symm
  · obtain ⟨z, hz⟩ := j_surjective (w : ℂ)
    exact ⟨Quotient.mk _ ⟨z, (mem_freeLocus_iff_j z).2 (hz ▸ w.2)⟩, Subtype.ext hz⟩

theorem continuous_jFreeQuotient : Continuous jFreeQuotient :=
  continuous_jFree.quotient_lift _

theorem isOpenMap_jFreeQuotient : IsOpenMap jFreeQuotient := by
  intro V hV
  have h : jFreeQuotient '' V = jFree '' (Quotient.mk _ ⁻¹' V) := by
    change _ = (jFreeQuotient ∘ Quotient.mk _) '' _
    rw [image_comp, image_preimage_eq _ Quotient.mk_surjective]
  rw [h]
  exact isOpenMap_jFree _ (hV.preimage continuous_quotient_mk')

/-- **`j` identifies `PSL(2, ℤ)\ℍ'` with `ℂ ∖ {0, 1728}`.** -/
def jFreeHomeomorph :
    orbitRel.Quotient psl2zToPSL2R.range (freeLocus psl2zToPSL2R.range ℍ) ≃ₜ jRegular :=
  (Equiv.ofBijective _ jFreeQuotient_bijective).toHomeomorphOfContinuousOpen continuous_jFreeQuotient
    isOpenMap_jFreeQuotient

/-- **`j : ℍ' → ℂ ∖ {0, 1728}` is a covering map.** -/
theorem isCoveringMap_jFree : IsCoveringMap jFree := by
  have := (TauCeti.isCoveringMap_quotientMk_freeLocus psl2zToPSL2R.range ℍ).homeomorph_comp jFreeHomeomorph
  exact this

/-- `j ∘ ofComplex` has a holomorphic inverse near every point of `ℍ'`: in a neighbourhood of `x` the map is
injective, so (Tau Ceti `DifferentiableOn.invFunOn`) its inverse on the image is holomorphic. -/
theorem exists_injOn_nhds (x : freeLocus psl2zToPSL2R.range ℍ) :
    ∃ W : Set ℂ, IsOpen W ∧ ((x : ℍ) : ℂ) ∈ W ∧ W ⊆ {z : ℂ | 0 < z.im} ∧ InjOn (j ∘ ofComplex) W := by
  obtain ⟨e, hxe, he⟩ := isCoveringMap_jFree.isLocalHomeomorph x
  have hF : IsOpen (freeLocus psl2zToPSL2R.range ℍ : Set ℍ) := TauCeti.isOpen_freeLocus _ _
  refine ⟨((↑) : ℍ → ℂ) '' (((↑) : freeLocus psl2zToPSL2R.range ℍ → ℍ) '' e.source),
    isOpenEmbedding_coe.isOpenMap _ (hF.isOpenEmbedding_subtypeVal.isOpenMap _ e.open_source),
    ⟨_, ⟨x, hxe, rfl⟩, rfl⟩, by rintro _ ⟨_, _, rfl⟩; exact UpperHalfPlane.im_pos _, ?_⟩
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ hab
  simp only [comp_apply, ofComplex_apply] at hab
  have : e a = e b := by
    rw [← he]
    exact Subtype.ext hab
  rw [e.injOn ha hb this]

/-- **The holomorphic lift.** An entire function omitting `0` and `1728` is `j ∘ h` for an entire `h` with values
in `ℍ`. -/
theorem exists_lift_of_omits {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfr : ∀ z, f z ∈ jRegular) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ (∀ z, 0 < (h z).im) ∧ ∀ z, f z = j (ofComplex (h z)) := by
  let f' : C(ℂ, jRegular) := ⟨fun z ↦ ⟨f z, hfr z⟩, hf.continuous.subtype_mk _⟩
  obtain ⟨p, hp⟩ := jFreeQuotient_bijective.2 (f' 0)
  obtain ⟨x₀, rfl⟩ := Quotient.exists_rep p
  obtain ⟨F, -, hF⟩ := (isCoveringMap_jFree.existsUnique_continuousMap_lifts f' 0 x₀ hp).exists
  let h : ℂ → ℂ := fun z ↦ ((F z : ℍ) : ℂ)
  have hFz : ∀ z, j (F z : ℍ) = f z := fun z ↦ congrArg Subtype.val (congrFun hF z)
  have hj : ∀ z, j (ofComplex (h z)) = f z := fun z ↦ by simp only [h, ofComplex_apply, hFz]
  have hcont : Continuous h := continuous_coe.comp (continuous_subtype_val.comp F.continuous)
  refine ⟨h, fun z₀ ↦ ?_, fun z ↦ (F z : ℍ).im_pos, fun z ↦ (hj z).symm⟩
  obtain ⟨W, hWo, hzW, hWH, hinj⟩ := exists_injOn_nhds (F z₀)
  have hd : DifferentiableOn ℂ (j ∘ ofComplex) W := analyticOnNhd_j.differentiableOn.mono hWH
  have himg : IsOpen ((j ∘ ofComplex) '' W) := isOpen_image_j hWH hWo
  have hmem : f z₀ ∈ (j ∘ ofComplex) '' W := ⟨h z₀, hzW, hj z₀⟩
  have hinv : DifferentiableAt ℂ (invFunOn (j ∘ ofComplex) W) (f z₀) :=
    (hd.invFunOn hWo hinj).differentiableAt (himg.mem_nhds hmem)
  refine ((hinv.comp z₀ (hf z₀)).congr_of_eventuallyEq ?_)
  filter_upwards [hcont.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)] with z hz
  have := hinj.leftInvOn_invFunOn hz
  simp only [comp_apply] at this ⊢
  rw [← hj z, this]

/-- The Cayley transform `w ↦ (w - i)/(w + i)` maps the upper half-plane into the closed unit disc. -/
theorem norm_cayley_le {w : ℂ} (hw : 0 < w.im) : ‖(w - Complex.I) / (w + Complex.I)‖ ≤ 1 := by
  have hne : w + Complex.I ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [norm_div, div_le_one (norm_pos_iff.2 hne)]
  have h2 : ‖w - Complex.I‖ ^ 2 ≤ ‖w + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im, Complex.add_re, add_zero,
      Complex.add_im]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- An entire function with values in the upper half-plane is constant (Liouville, through the Cayley
transform). -/
theorem eq_const_of_im_pos {h : ℂ → ℂ} (hh : Differentiable ℂ h) (him : ∀ z, 0 < (h z).im) (z w : ℂ) :
    h z = h w := by
  have hne : ∀ z, h z + Complex.I ≠ 0 := fun z h0 ↦ by
    have := congrArg Complex.im h0
    simp at this
    linarith [him z]
  let C : ℂ → ℂ := fun z ↦ (h z - Complex.I) / (h z + Complex.I)
  have hC : Differentiable ℂ C := fun z ↦
    ((hh z).sub_const _).div ((hh z).add_const _) (hne z)
  have hb : Bornology.IsBounded (range C) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨z, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_cayley_le (him z)
  have hCzw := hC.apply_eq_apply_of_bounded hb z w
  simp only [C] at hCzw
  rw [div_eq_div_iff (hne z) (hne w)] at hCzw
  have : (2 * Complex.I) * (h z - h w) = 0 := by linear_combination hCzw
  rcases mul_eq_zero.1 this with h0 | h0
  · simp at h0
  · exact sub_eq_zero.1 h0

/-- **Milne, Remark 2.25 (little Picard theorem), two-value form**: an entire function omitting two distinct values
is constant. -/
@[kb "milne2017mf" "Remark 2.25, pdf p. 39 (little Picard theorem)"]
theorem littlePicard' {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b : ℂ} (hab : a ≠ b) (ha : ∀ z, f z ≠ a)
    (hb : ∀ z, f z ≠ b) (z w : ℂ) : f z = f w := by
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  let g : ℂ → ℂ := fun z ↦ 1728 / (b - a) * (f z - a)
  have hg : Differentiable ℂ g := fun z ↦ ((hf z).sub_const a).const_mul _
  have hgr : ∀ z, g z ∈ jRegular := by
    intro z
    refine ⟨fun h ↦ hb z ?_, fun h ↦ ha z ?_⟩
    · simp only [g] at h
      field_simp at h
      linear_combination h
    · simp only [g, mul_eq_zero, div_eq_zero_iff, sub_eq_zero] at h
      rcases h with (h | h) | h
      · norm_num at h
      · exact absurd h hab.symm
      · exact h
  obtain ⟨h, hh, him, hgj⟩ := exists_lift_of_omits hg hgr
  have hgzw : g z = g w := by rw [hgj, hgj, eq_const_of_im_pos hh him z w]
  simp only [g] at hgzw
  have h1728 : (1728 : ℂ) / (b - a) ≠ 0 := div_ne_zero (by norm_num) hba
  have := mul_left_cancel₀ h1728 hgzw
  linear_combination this

/-- **Milne, Remark 2.25 (little Picard theorem)**: the image of a nonconstant entire function is `ℂ` or `ℂ` with
one point omitted, i.e. its complement has at most one point. -/
@[kb "milne2017mf" "Remark 2.25, pdf p. 39 (little Picard theorem)"]
theorem littlePicard {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hnc : ∃ z w, f z ≠ f w) :
    (range f)ᶜ.Subsingleton := by
  intro a ha b hb
  by_contra hab
  obtain ⟨z, w, hzw⟩ := hnc
  exact hzw (littlePicard' hf hab (fun z hz ↦ ha ⟨z, hz⟩) (fun z hz ↦ hb ⟨z, hz⟩) z w)

/-- **The named statement `Milne.LittlePicardStatement` (Remark 2.25) holds.** -/
@[kb "milne2017mf" "Remark 2.25 (little Picard theorem), pdf p. 39"]
theorem littlePicardStatement : LittlePicardStatement :=
  ⟨fun f hf hnc a b hab ↦ by
    by_contra h
    rw [not_or] at h
    obtain ⟨z, w, hzw⟩ := hnc
    exact hzw (littlePicard' hf hab (fun z hz ↦ h.1 ⟨z, hz⟩) (fun z hz ↦ h.2 ⟨z, hz⟩) z w)⟩

end ModularFormsKB.Milne.Wave10
