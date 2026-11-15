import ModularFormsKB.Milne.Wave14.SmoothCocycle
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Every smooth cocycle on an open cover of the upper half-plane is smoothly trivial

Part of the proof of Milne, Remark 4.26 (the topological half of the multiplicative Cousin problem). Let $G$ be a
smooth multiplicative cocycle on an open cover $\{U_i\}$ of $\{\operatorname{Im} z > 0\}$
(`IsSmoothCocycle`). Then $G_{ij} = s_i / s_j$ with $s_i$ smooth and nowhere zero (`smoothTriv_upperHalfPlane`).

* A rectangle with compact closure inside $\bigcup U_i$ (`smoothTriv_rect`): by the Lebesgue number lemma, cut it into
  rows, and the rows into small rectangles, each inside one $U_i$; all overlaps are convex, so the chain lemma
  `smoothTriv_chain` applies twice.
* The half-plane: a chain of vertical strips $n - 1 < \operatorname{Re} z < n + 1$, each a chain (in
  $\log \operatorname{Im} z$) of rectangles $e^{k-1} < \operatorname{Im} z < e^{k+1}$.

This replaces the vanishing of $H^2(\mathbb H, \mathbb Z)$ in the exponential-sequence proof (Forster, *Lectures on
Riemann Surfaces*, §30) by an explicit gluing along chains with convex overlaps.
-/

open Set Topology Filter Metric
open scoped ContDiff

noncomputable section

namespace ModularFormsKB.Milne.Wave14

variable {ι : Type*} {U : ι → Set ℂ} {G : ι → ι → ℂ → ℂ}

theorem smoothTriv_empty : SmoothTriv U G ∅ :=
  ⟨fun _ _ ↦ 1, fun _ ↦ by simp, fun _ _ h ↦ h.2.elim, fun _ _ _ h ↦ h.2.elim⟩

/-- A set of small diameter near a compact set covered by the `U i` lies in one `U i`. -/
theorem smoothTriv_of_small (hG : IsSmoothCocycle U G) {K : Set ℂ} {δ : ℝ}
    (hδ : ∀ x ∈ K, ∃ i, ball x δ ⊆ U i) {Q : Set ℂ} (hQK : Q ⊆ K)
    (hd : ∀ y ∈ Q, ∀ z ∈ Q, dist z y < δ) : SmoothTriv U G Q := by
  rcases Q.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · exact smoothTriv_empty
  obtain ⟨i, hi⟩ := hδ y (hQK hy)
  exact smoothTriv_of_subset hG fun z hz ↦ hi (mem_ball.2 (hd y hy z hz))

theorem convex_re_preimage {I : Set ℝ} (hI : Convex ℝ I) : Convex ℝ (Complex.re ⁻¹' I) :=
  hI.linear_preimage Complex.reLm

theorem convex_im_preimage {I : Set ℝ} (hI : Convex ℝ I) : Convex ℝ (Complex.im ⁻¹' I) :=
  hI.linear_preimage Complex.imLm

/-- The open rectangle `(a, b) × (c, d)`. -/
def openRect (a b c d : ℝ) : Set ℂ := Complex.re ⁻¹' Ioo a b ∩ Complex.im ⁻¹' Ioo c d

theorem isOpen_openRect (a b c d : ℝ) : IsOpen (openRect a b c d) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem convex_openRect (a b c d : ℝ) : Convex ℝ (openRect a b c d) :=
  (convex_re_preimage (convex_Ioo a b)).inter (convex_im_preimage (convex_Ioo c d))

theorem contDiffOn_re {s : Set ℂ} : ContDiffOn ℝ ∞ (fun z : ℂ ↦ z.re) s :=
  Complex.reCLM.contDiff.contDiffOn

theorem contDiffOn_im {s : Set ℂ} : ContDiffOn ℝ ∞ (fun z : ℂ ↦ z.im) s :=
  Complex.imCLM.contDiff.contDiffOn

theorem chainPiece_convex {T : Set ℂ} (hT : Convex ℝ T) (c h : ℝ) (k : ℤ) :
    Convex ℝ (chainPiece T (fun z ↦ z.re) c h k) :=
  hT.inter (convex_re_preimage (convex_Ioo _ _))

theorem chainPiece_im_convex {T : Set ℂ} (hT : Convex ℝ T) (c h : ℝ) (k : ℤ) :
    Convex ℝ (chainPiece T (fun z ↦ z.im) c h k) :=
  hT.inter (convex_im_preimage (convex_Ioo _ _))

theorem dist_lt_of_re_im {y z : ℂ} {α β : ℝ} (h1 : |z.re - y.re| < α) (h2 : |z.im - y.im| < β) :
    dist z y < α + β := by
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  simp only [Complex.sub_re, Complex.sub_im]
  linarith

theorem abs_sub_lt_of_mem_chain {s t c h : ℝ} {k : ℤ}
    (hs : s ∈ Ioo (c + (k - 1) * h) (c + (k + 1) * h)) (ht : t ∈ Ioo (c + (k - 1) * h) (c + (k + 1) * h)) :
    |t - s| < 2 * h := by
  rw [abs_lt]; constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2]

/-- **Rectangles.** If the closed rectangle `[a, b] × [c, d]` is covered by the `U i`, the cocycle is smoothly
trivial on the open rectangle. -/
theorem smoothTriv_rect (hG : IsSmoothCocycle U G) (a b c d : ℝ)
    (hK : ∀ z : ℂ, z.re ∈ Icc a b → z.im ∈ Icc c d → ∃ i, z ∈ U i) :
    SmoothTriv U G (openRect a b c d) := by
  set K : Set ℂ := Icc a b ×ℂ Icc c d
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKU : K ⊆ ⋃ i, U i := fun z hz ↦ by
    obtain ⟨i, hi⟩ := hK z hz.1 hz.2
    exact mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hKc hG.isOpen hKU
  set R := openRect a b c d
  have hRK : R ⊆ K := fun z hz ↦ ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩
  have hRo := isOpen_openRect a b c d
  have hRc := convex_openRect a b c d
  have hcovR : ∀ x ∈ R, ∃ i, x ∈ U i := fun x hx ↦ hK x (hRK hx).1 (hRK hx).2
  have hh : 0 < δ / 4 := by positivity
  -- rows
  have hrow : ∀ l : ℤ, SmoothTriv U G (chainPiece R (fun z ↦ z.im) c (δ / 4) l) := by
    intro l
    set row := chainPiece R (fun z ↦ z.im) c (δ / 4) l
    have hrowo : IsOpen row := isOpen_chainPiece hRo contDiffOn_im.continuousOn _ _ l
    have hrowc : Convex ℝ row := chainPiece_im_convex hRc _ _ l
    refine smoothTriv_chain hG hrowo (fun x hx ↦ hcovR x hx.1) contDiffOn_re (c := a) hh (fun k ↦ ?_) (fun k ↦ ?_)
    · refine smoothTriv_of_small hG hball (fun z hz ↦ hRK hz.1.1) fun y hy z hz ↦ ?_
      have := dist_lt_of_re_im (abs_sub_lt_of_mem_chain hy.2 hz.2) (abs_sub_lt_of_mem_chain hy.1.2 hz.1.2)
      linarith
    · exact Convex.hasSmoothLog ((isOpen_chainPiece hrowo contDiffOn_re.continuousOn _ _ _).inter
        (isOpen_chainPiece hrowo contDiffOn_re.continuousOn _ _ _))
        ((chainPiece_convex hrowc _ _ _).inter (chainPiece_convex hrowc _ _ _))
  refine smoothTriv_chain hG hRo hcovR contDiffOn_im (c := c) hh hrow fun l ↦ ?_
  exact Convex.hasSmoothLog ((isOpen_chainPiece hRo contDiffOn_im.continuousOn _ _ _).inter
    (isOpen_chainPiece hRo contDiffOn_im.continuousOn _ _ _))
    ((chainPiece_im_convex hRc _ _ _).inter (chainPiece_im_convex hRc _ _ _))

/-- The open upper half-plane as a subset of `ℂ`. -/
def upperSet : Set ℂ := Complex.im ⁻¹' Ioi 0

theorem isOpen_upperSet : IsOpen upperSet := isOpen_Ioi.preimage Complex.continuous_im

theorem convex_upperSet : Convex ℝ upperSet := convex_im_preimage (convex_Ioi 0)

theorem chainPiece_logIm_eq {T : Set ℂ} (hT : T ⊆ upperSet) (k : ℤ) :
    chainPiece T (fun z ↦ Real.log z.im) 0 1 k =
      T ∩ Complex.im ⁻¹' Ioo (Real.exp (k - 1)) (Real.exp (k + 1)) := by
  ext z
  simp only [chainPiece, mem_inter_iff, mem_preimage, mem_Ioo, zero_add, mul_one]
  constructor
  · rintro ⟨hz, h1, h2⟩
    have hpos : 0 < z.im := hT hz
    refine ⟨hz, ?_, ?_⟩
    · rw [← Real.exp_log hpos]; exact Real.exp_lt_exp.2 h1
    · rw [← Real.exp_log hpos]; exact Real.exp_lt_exp.2 h2
  · rintro ⟨hz, h1, h2⟩
    have hpos : 0 < z.im := hT hz
    exact ⟨hz, (Real.lt_log_iff_exp_lt hpos).2 h1, (Real.log_lt_iff_lt_exp hpos).2 h2⟩

/-- **The half-plane.** A smooth cocycle on an open cover of the upper half-plane is smoothly trivial there. -/
theorem smoothTriv_upperHalfPlane (hG : IsSmoothCocycle U G) (hcov : ∀ z ∈ upperSet, ∃ i, z ∈ U i) :
    SmoothTriv U G upperSet := by
  have hlog : ContDiffOn ℝ ∞ (fun z : ℂ ↦ Real.log z.im) upperSet :=
    (Real.contDiffOn_log.comp contDiffOn_im fun z hz ↦ (ne_of_gt hz : z.im ≠ 0))
  -- vertical strips
  have hstrip : ∀ n : ℤ, SmoothTriv U G (chainPiece upperSet (fun z ↦ z.re) 0 1 n) := by
    intro n
    set S := chainPiece upperSet (fun z ↦ z.re) 0 1 n
    have hSU : S ⊆ upperSet := inter_subset_left
    have hSo : IsOpen S := isOpen_chainPiece isOpen_upperSet contDiffOn_re.continuousOn _ _ n
    have hSc : Convex ℝ S := chainPiece_convex convex_upperSet _ _ n
    have hpiece : ∀ k : ℤ, chainPiece S (fun z ↦ Real.log z.im) 0 1 k =
        openRect ((n : ℝ) - 1) (n + 1) (Real.exp (k - 1)) (Real.exp (k + 1)) := by
      intro k
      rw [chainPiece_logIm_eq hSU]
      ext z
      simp only [S, chainPiece, openRect, upperSet, mem_inter_iff, mem_preimage, mem_Ioo, mem_Ioi,
        zero_add, mul_one]
      constructor
      · rintro ⟨⟨-, h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨(Real.exp_pos _).trans h3, h1, h2⟩, h3, h4⟩
    refine smoothTriv_chain hG hSo (fun x hx ↦ hcov x (hSU hx)) (hlog.mono hSU) (c := 0) one_pos (fun k ↦ ?_)
      (fun k ↦ ?_)
    · rw [hpiece]
      refine smoothTriv_rect hG _ _ _ _ fun z _ hz ↦ hcov z ?_
      exact (Real.exp_pos _).trans_le hz.1
    · rw [hpiece, hpiece]
      exact Convex.hasSmoothLog ((isOpen_openRect _ _ _ _).inter (isOpen_openRect _ _ _ _))
        ((convex_openRect _ _ _ _).inter (convex_openRect _ _ _ _))
  refine smoothTriv_chain hG isOpen_upperSet hcov contDiffOn_re (c := 0) one_pos hstrip fun n ↦ ?_
  exact Convex.hasSmoothLog
    ((isOpen_chainPiece isOpen_upperSet contDiffOn_re.continuousOn _ _ _).inter
      (isOpen_chainPiece isOpen_upperSet contDiffOn_re.continuousOn _ _ _))
    ((chainPiece_convex convex_upperSet _ _ _).inter (chainPiece_convex convex_upperSet _ _ _))

end ModularFormsKB.Milne.Wave14
