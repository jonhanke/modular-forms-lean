import Mathlib
import TauCeti.Geometry.Manifold.Algebra.Quotient
import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
import TauCeti.Analysis.SpecialFunctions.Elliptic.Uniformization
import ModularFormsKB.Citation
/-!
# Milne, Chapter 3: elliptic functions and complex tori

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §3, pdf pp. 41–47 (and Example 1.6, p. 16).

A lattice `Λ = ℤω₁ + ℤω₂` is Mathlib's `PeriodPair` `L` with `L.lattice`. The complex torus `ℂ/Λ` is
`AddAction.orbitRel.Quotient L.lattice ℂ` with Tau Ceti's complex Lie group structure
(`Submodule.instLieAddGroupOrbitRelQuotient`, from the charted structure on quotients by properly discontinuous free
actions: the book's coordinate neighbourhoods `(U, p⁻¹ : U → V)`, p. 41). `℘` is Mathlib's `PeriodPair.weierstrassP`.

* D016 homothetic lattices; D058 doubly periodic functions.
* Example 1.6: the torus has infinitely many non-isomorphic complex structures.
* Proposition 3.1 (named statement), Corollary 3.2.
* Proposition 3.3, Corollaries 3.4, 3.5, 3.6: holomorphic maps of complex tori.
* Lemma 3.7 (general form).
* Theorem 3.8, Proposition 3.9, Proposition 3.11 (first part), Proposition 3.12 (second and third parts) and
  Proposition 3.13: named statements. Proposition 3.12, first part (`Δ ≠ 0`): Tau Ceti
  `PeriodPair.weierstrassCurve_Δ_ne_zero`.
-/

open Complex Filter Topology Set PeriodPair
open scoped Manifold

namespace ModularFormsKB.Milne

/-- The complex torus `ℂ/Λ`. -/
abbrev ComplexTorus (L : PeriodPair) : Type := AddAction.orbitRel.Quotient L.lattice ℂ

/-- The class `[z] ∈ ℂ/Λ`. -/
def ComplexTorus.mk (L : PeriodPair) (z : ℂ) : ComplexTorus L := Quotient.mk _ z

/-! ### Definitions -/

/-- **Homothetic lattices** (Milne, p. 10): `Λ' = cΛ` for some `c ∈ ℂˣ`. -/
@[kb "milne2017mf" "Introduction: homothetic lattices, pdf p. 10"]
def IsHomothetic (Λ Λ' : Submodule ℤ ℂ) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ (Λ' : Set ℂ) = (fun z ↦ c * z) '' Λ

/-- **Doubly periodic function** (Milne, p. 41): a meromorphic function `f` on `ℂ` with `f(z + ω) = f(z)` for all
`ω ∈ Λ`. (Mathlib's meromorphic functions carry arbitrary values at poles; periodicity is required everywhere.) -/
@[kb "milne2017mf" "§3, doubly periodic function, pdf p. 41"]
def IsDoublyPeriodic (Λ : Submodule ℤ ℂ) (f : ℂ → ℂ) : Prop :=
  MeromorphicOn f univ ∧ ∀ ω ∈ Λ, ∀ z, f (z + ω) = f z

/-- The open parallelogram `{z₀ + s ω₁ + t ω₂ | 0 < s, t < 1}`. -/
def openParallelogram (L : PeriodPair) (z₀ : ℂ) : Set ℂ :=
  {z | ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧ z = z₀ + s * L.ω₁ + t * L.ω₂}

/-- The closed parallelogram `{z₀ + s ω₁ + t ω₂ | 0 ≤ s, t ≤ 1}`, a **fundamental parallelogram** (Milne, p. 41). -/
@[kb "milne2017mf" "§3, fundamental parallelogram, pdf p. 41"]
def closedParallelogram (L : PeriodPair) (z₀ : ℂ) : Set ℂ :=
  {z | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ z = z₀ + s * L.ω₁ + t * L.ω₂}

/-! ### Proposition 3.1 and Corollary 3.2 -/

/-- **Milne, Proposition 3.1** (named statement). Let `f` be doubly periodic for `Λ`, not identically zero, and `D` a
fundamental parallelogram with no zeros or poles of `f` on its boundary. Then, summing over the points of `D`:
(a) `∑ ord_P f = 0`; (b) `∑ Res_P f = 0`; (c) `∑ ord_P(f) · P ∈ Λ`. The book derives it from Proposition 1.12 on
`ℂ/Λ`. -/
@[kb "milne2017mf" "Proposition 3.1, pdf p. 42"]
structure DoublyPeriodicSumsStatement : Prop where
  out : ∀ (L : PeriodPair) (f : ℂ → ℂ), IsDoublyPeriodic L.lattice f → ¬ (∀ᶠ z in codiscrete ℂ, f z = 0) →
    ∀ z₀ : ℂ, (∀ z ∈ frontier (openParallelogram L z₀), meromorphicOrderAt f z = 0) →
      (∑ᶠ z ∈ openParallelogram L z₀, (meromorphicOrderAt f z).untop₀ = 0) ∧
      (∑ᶠ z ∈ openParallelogram L z₀, TauCeti.Contour.residue f z = 0) ∧
      (∑ᶠ z ∈ openParallelogram L z₀, ((meromorphicOrderAt f z).untop₀ : ℂ) * z) ∈ L.lattice

/-- The affine parametrisation of the parallelogram by `ℝ²`. -/
def parallelogramMap (L : PeriodPair) (z₀ : ℂ) (p : ℝ × ℝ) : ℂ := z₀ + p.1 * L.ω₁ + p.2 * L.ω₂

theorem continuous_parallelogramMap (L : PeriodPair) (z₀ : ℂ) :
    Continuous (parallelogramMap L z₀) := by
  unfold parallelogramMap; fun_prop

theorem closedParallelogram_eq_image (L : PeriodPair) (z₀ : ℂ) :
    closedParallelogram L z₀ = parallelogramMap L z₀ '' (Icc 0 1 ×ˢ Icc 0 1) := by
  ext z
  simp only [closedParallelogram, mem_setOf_eq, mem_image, mem_prod, mem_Icc, Prod.exists,
    parallelogramMap]
  constructor
  · rintro ⟨s, t, h0, h1, h2, h3, rfl⟩; exact ⟨s, t, ⟨⟨h0, h1⟩, h2, h3⟩, rfl⟩
  · rintro ⟨s, t, ⟨⟨h0, h1⟩, h2, h3⟩, rfl⟩; exact ⟨s, t, h0, h1, h2, h3, rfl⟩

theorem openParallelogram_eq_image (L : PeriodPair) (z₀ : ℂ) :
    openParallelogram L z₀ = parallelogramMap L z₀ '' (Ioo 0 1 ×ˢ Ioo 0 1) := by
  ext z
  simp only [openParallelogram, mem_setOf_eq, mem_image, mem_prod, mem_Ioo, Prod.exists,
    parallelogramMap]
  constructor
  · rintro ⟨s, t, h0, h1, h2, h3, rfl⟩; exact ⟨s, t, ⟨⟨h0, h1⟩, h2, h3⟩, rfl⟩
  · rintro ⟨s, t, ⟨⟨h0, h1⟩, h2, h3⟩, rfl⟩; exact ⟨s, t, h0, h1, h2, h3, rfl⟩

theorem isCompact_closedParallelogram (L : PeriodPair) (z₀ : ℂ) :
    IsCompact (closedParallelogram L z₀) := by
  rw [closedParallelogram_eq_image]
  exact (isCompact_Icc.prod isCompact_Icc).image (continuous_parallelogramMap L z₀)

theorem openParallelogram_subset_closed (L : PeriodPair) (z₀ : ℂ) :
    openParallelogram L z₀ ⊆ closedParallelogram L z₀ := by
  rintro z ⟨s, t, h0, h1, h2, h3, rfl⟩
  exact ⟨s, t, h0.le, h1.le, h2.le, h3.le, rfl⟩

theorem closedParallelogram_subset_closure (L : PeriodPair) (z₀ : ℂ) :
    closedParallelogram L z₀ ⊆ closure (openParallelogram L z₀) := by
  rw [closedParallelogram_eq_image, openParallelogram_eq_image]
  have := image_closure_subset_closure_image (continuous_parallelogramMap L z₀)
    (s := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)
  rw [closure_prod_eq, closure_Ioo (zero_ne_one)] at this
  exact this

theorem exists_lattice_translate (L : PeriodPair) (z₀ z : ℂ) :
    ∃ ω ∈ L.lattice, z + ω ∈ closedParallelogram L z₀ := by
  set a := L.basis.repr (z - z₀) 0 with ha
  set b := L.basis.repr (z - z₀) 1 with hb
  have hw : (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ = z - z₀ := by
    have := L.basis.sum_repr (z - z₀)
    rw [Fin.sum_univ_two, L.basis_zero, L.basis_one, Complex.real_smul, Complex.real_smul] at this
    exact this
  refine ⟨-((⌊a⌋ : ℤ) * L.ω₁ + (⌊b⌋ : ℤ) * L.ω₂), neg_mem (L.mem_lattice.2 ⟨⌊a⌋, ⌊b⌋, rfl⟩),
    a - ⌊a⌋, b - ⌊b⌋, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [Int.floor_le a]
  · linarith [Int.lt_floor_add_one a]
  · linarith [Int.floor_le b]
  · linarith [Int.lt_floor_add_one b]
  · push_cast
    linear_combination (-1 : ℂ) * hw

theorem order_nonneg_of_period {L : PeriodPair} {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    {z₀ : ℂ} (H : ∀ z ∈ closedParallelogram L z₀, 0 ≤ meromorphicOrderAt f z) (z : ℂ) :
    0 ≤ meromorphicOrderAt f z := by
  obtain ⟨ω, hω, hz⟩ := exists_lattice_translate L z₀ z
  have h1 : f ∘ (· + ω) = f := funext fun w ↦ hf.2 ω hω w
  have h2 := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := f) (x := z) (c := ω)
  rw [h1] at h2
  rw [h2]
  exact H _ hz

/-- A doubly periodic meromorphic function without poles is constant (Liouville). -/
theorem const_of_no_poles {L : PeriodPair} {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (H : ∀ z, 0 ≤ meromorphicOrderAt f z) : ∃ c : ℂ, ∀ᶠ z in codiscrete ℂ, f z = c := by
  have hmero : MeromorphicOn f univ := hf.1
  set g := toMeromorphicNFOn f univ with hg
  have hg_an : ∀ z, AnalyticAt ℂ g z := fun z ↦
    ((meromorphicNFOn_toMeromorphicNFOn f univ) (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.1
      (by rw [meromorphicOrderAt_toMeromorphicNFOn hmero (mem_univ z)]; exact H z)
  have hdiff : Differentiable ℂ g := fun z ↦ (hg_an z).differentiableAt
  have hfg : f =ᶠ[codiscrete ℂ] g := by
    exact toMeromorphicNFOn_eqOn_codiscrete hmero
  have hfg' : ∀ z, f =ᶠ[𝓝[≠] z] g := eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.1 hfg
  have hper : ∀ ω ∈ L.lattice, ∀ z, g (z + ω) = g z := by
    intro ω hω z
    have hT : Tendsto (fun w : ℂ ↦ w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) :=
      tendsto_nhdsWithin_iff.2 ⟨(by fun_prop : Continuous fun w : ℂ ↦ w + ω).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, by
          filter_upwards [self_mem_nhdsWithin] with w hw
          simpa using hw⟩
    have h1 : Tendsto f (𝓝[≠] z) (𝓝 (g z)) :=
      ((hdiff.continuous.continuousAt (x := z)).tendsto.mono_left nhdsWithin_le_nhds).congr'
        (hfg' z).symm
    have h2 : Tendsto f (𝓝[≠] (z + ω)) (𝓝 (g (z + ω))) :=
      ((hdiff.continuous.continuousAt (x := z + ω)).tendsto.mono_left nhdsWithin_le_nhds).congr'
        (hfg' (z + ω)).symm
    have h3 : Tendsto f (𝓝[≠] z) (𝓝 (g (z + ω))) := by
      have := h2.comp hT
      have e : f ∘ (fun w : ℂ ↦ w + ω) = f := funext fun w ↦ hf.2 ω hω w
      rwa [e] at this
    exact (tendsto_nhds_unique h3 h1)
  obtain ⟨M, hM⟩ := (isCompact_closedParallelogram L 0).exists_bound_of_continuousOn
    hdiff.continuous.continuousOn
  have hbdd : Bornology.IsBounded (range g) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨z, rfl⟩
    obtain ⟨ω, hω, hz⟩ := exists_lattice_translate L 0 z
    rw [← hper ω hω z]
    exact hM _ hz
  refine ⟨g 0, ?_⟩
  filter_upwards [hfg] with z hz
  rw [hz]
  exact hdiff.apply_eq_apply_of_bounded hbdd z 0

/-- **Milne, Corollary 3.2.** A nonconstant doubly periodic function has at least two poles (counted with
multiplicity) in a fundamental parallelogram `D`, chosen as in Proposition 3.1 with no zeros or poles on its
boundary (the book's proof applies 3.1 to such a `D`). Proved from Proposition 3.1 (b) and Liouville's theorem, as in
the book. -/
@[kb "milne2017mf" "Corollary 3.2, pdf p. 42"]
theorem two_le_card_poles (h31 : DoublyPeriodicSumsStatement) {L : PeriodPair} {f : ℂ → ℂ}
    (hf : IsDoublyPeriodic L.lattice f) (hnc : ¬ ∃ c : ℂ, ∀ᶠ z in codiscrete ℂ, f z = c) {z₀ : ℂ}
    (hb : ∀ z ∈ frontier (openParallelogram L z₀), meromorphicOrderAt f z = 0) :
    2 ≤ ∑ᶠ z ∈ openParallelogram L z₀, (-(meromorphicOrderAt f z).untop₀).toNat := by
  classical
  have hmero : MeromorphicOn f univ := hf.1
  have hM : Meromorphic f := meromorphicOn_univ.1 hmero
  have hnz : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0) := fun h ↦ hnc ⟨0, h⟩
  have hne : ∀ z, meromorphicOrderAt f z ≠ ⊤ := fun z hz ↦
    hnz ((hM.exists_meromorphicOrderAt_eq_top_iff_eventually_zero).1 ⟨z, hz⟩)
  set D := openParallelogram L z₀ with hD
  set P := closedParallelogram L z₀ with hP
  set n : ℂ → ℕ := fun z ↦ (-(meromorphicOrderAt f z).untop₀).toNat with hn
  show 2 ≤ ∑ᶠ z ∈ D, n z
  have hDP : D ⊆ P := openParallelogram_subset_closed L z₀
  have hn0 : ∀ z, n z = 0 → 0 ≤ meromorphicOrderAt f z := by
    intro z hz
    have h1 : -(meromorphicOrderAt f z).untop₀ ≤ 0 := Int.toNat_eq_zero.1 hz
    have h2 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by omega
    rw [← WithTop.coe_untop₀_of_ne_top (hne z)]
    exact_mod_cast h2
  have hn1 : ∀ z, n z = 1 → meromorphicOrderAt f z = -1 := by
    intro z hz
    have h1 : (meromorphicOrderAt f z).untop₀ = -1 := by
      have h : (-(meromorphicOrderAt f z).untop₀).toNat = 1 := hz
      omega
    rw [← WithTop.coe_untop₀_of_ne_top (hne z), h1]
    rfl
  have hmeroP : MeromorphicOn f P := hmero.mono_set (subset_univ _)
  have hT := MeromorphicOn.divisor_support_finite_of_subset hmeroP
    (isCompact_closedParallelogram L z₀) (subset_refl P)
  have hsupp : ∀ z ∈ P, n z ≠ 0 → z ∈ hT.toFinset := by
    intro z hz hnz0
    rw [Set.Finite.mem_toFinset, Function.mem_support, MeromorphicOn.divisor_apply hmeroP hz]
    intro h0
    apply hnz0
    simp [hn, h0]
  have hsum : ∑ᶠ z ∈ D, n z = ∑ z ∈ hT.toFinset, D.indicator n z := by
    rw [finsum_mem_def]
    apply finsum_eq_sum_of_support_subset
    intro z hz
    rw [Function.mem_support] at hz
    have hzD : z ∈ D := by
      by_contra h
      exact hz (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hzD] at hz
    exact hsupp z (hDP hzD) hz
  by_contra hlt
  push_neg at hlt
  rw [hsum] at hlt
  by_cases hall : ∀ z ∈ D, n z = 0
  · -- no poles in the parallelogram
    have H : ∀ z ∈ P, 0 ≤ meromorphicOrderAt f z := by
      intro z hz
      by_cases hzD : z ∈ D
      · exact hn0 z (hall z hzD)
      · have hfr : z ∈ frontier D :=
          ⟨closedParallelogram_subset_closure L z₀ hz, fun hi ↦ hzD (interior_subset hi)⟩
        rw [hb z hfr]
    exact hnc (const_of_no_poles hf (order_nonneg_of_period hf H))
  · push_neg at hall
    obtain ⟨z₁, hz₁D, hz₁⟩ := hall
    have hz₁S : z₁ ∈ hT.toFinset := hsupp z₁ (hDP hz₁D) hz₁
    have hle : n z₁ ≤ ∑ z ∈ hT.toFinset, D.indicator n z := by
      calc n z₁ = D.indicator n z₁ := (Set.indicator_of_mem hz₁D _).symm
        _ ≤ _ := Finset.single_le_sum (f := fun z ↦ D.indicator n z)
          (fun _ _ ↦ Nat.zero_le _) hz₁S
    have hn1' : n z₁ = 1 := by omega
    have hothers : ∀ z ∈ D, z ≠ z₁ → n z = 0 := by
      intro z hzD hzne
      by_contra hz0
      have hzS : z ∈ hT.toFinset := hsupp z (hDP hzD) hz0
      have hsub : ({z₁, z} : Finset ℂ) ⊆ hT.toFinset := by
        intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact hz₁S
        · rw [Finset.mem_singleton.1 hw]; exact hzS
      have := Finset.sum_le_sum_of_subset (f := fun z ↦ D.indicator n z) hsub
      rw [Finset.sum_pair (Ne.symm hzne), Set.indicator_of_mem hzD, Set.indicator_of_mem hz₁D] at this
      omega
    have hres := (h31.out L f hf hnz z₀ hb).2.1
    have hres1 : ∑ᶠ z ∈ D, TauCeti.Contour.residue f z = TauCeti.Contour.residue f z₁ := by
      rw [finsum_mem_def, finsum_eq_single _ z₁]
      · rw [Set.indicator_of_mem hz₁D]
      · intro z hz
        by_cases hzD : z ∈ D
        · rw [Set.indicator_of_mem hzD]
          exact TauCeti.Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg
            (hn0 z (hothers z hzD hz))
        · exact Set.indicator_of_notMem hzD _
    rw [hres1, TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one
      (hn1 z₁ hn1')] at hres
    exact (hM z₁).meromorphicTrailingCoeffAt_ne_zero (hne z₁) hres

/-! ### Lemma 3.7 -/

theorem summable_sq_add_sq_rpow_neg (c : ℝ) (hc : 1 < c) :
    Summable fun p : ℤ × ℤ ↦ (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-c)) := by
  have h := EisensteinSeries.summable_one_div_norm_rpow (k := 2 * c) (by linarith)
  have h2 : Summable fun p : ℤ × ℤ ↦ ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-(2 * c)) :=
    (finTwoArrowEquiv ℤ).symm.summable_iff.mpr h
  refine Summable.of_nonneg_of_le (fun p ↦ by positivity) (fun p ↦ ?_) h2
  have hn : ‖(finTwoArrowEquiv ℤ).symm p‖ = max |(p.1 : ℝ)| |(p.2 : ℝ)| := by
    rw [EisensteinSeries.norm_eq_max_natAbs]
    simp [Nat.cast_max]
  rw [hn]
  set M := max |(p.1 : ℝ)| |(p.2 : ℝ)| with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (abs_nonneg _)
  have hMs : M ^ 2 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    rcases max_choice |(p.1 : ℝ)| |(p.2 : ℝ)| with h | h
    · rw [hM, h, sq_abs]; nlinarith [sq_nonneg (p.2 : ℝ)]
    · rw [hM, h, sq_abs]; nlinarith [sq_nonneg (p.1 : ℝ)]
  rcases hM0.eq_or_lt with h0 | hpos
  · have : (p.1 : ℝ) = 0 ∧ (p.2 : ℝ) = 0 := by
      have h1 : |(p.1 : ℝ)| ≤ M := le_max_left _ _
      have h2 : |(p.2 : ℝ)| ≤ M := le_max_right _ _
      rw [← h0] at h1 h2
      exact ⟨abs_nonpos_iff.mp h1, abs_nonpos_iff.mp h2⟩
    rw [this.1, this.2, ← h0]
    have n1 : (-c) ≠ 0 := by linarith
    have n2 : (-(2 * c)) ≠ 0 := by linarith
    rw [Real.zero_rpow n2]
    simp [Real.zero_rpow n1]
  · have e : M ^ (-(2 * c)) = (M ^ 2) ^ (-c) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM0]; norm_num
    rw [e]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hMs (by linarith)

/-- **Milne, Lemma 3.7.** Let `D ⊆ ℂ` be bounded, `c > 1`, and `φ(z, ω)` (`ω ∈ Λ`) with
`φ(z, mω₁ + nω₂) = O((m² + n²)^{-c})` uniformly for `z ∈ D`. Then the series `∑_ω φ(z, ω)`, with the finitely many
terms with `m² + n² ≤ A` deleted, converges absolutely and uniformly on `D`. (The book deletes the finitely many terms
with poles in `D`; for meromorphic `φ` these are among the deleted ones.) -/
@[kb "milne2017mf" "Lemma 3.7, pdf p. 44"]
theorem tendstoUniformlyOn_lattice_sum (L : PeriodPair) {D : Set ℂ} (_hD : Bornology.IsBounded D) {c : ℝ}
    (hc : 1 < c) (φ : ℂ → ℂ → ℂ) {A B : ℝ}
    (hφ : ∀ m n : ℤ, A < (m : ℝ) ^ 2 + (n : ℝ) ^ 2 → ∀ z ∈ D,
      ‖φ z (m * L.ω₁ + n * L.ω₂)‖ ≤ B * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2) ^ (-c)) :
    let ψ : ℂ → ℤ × ℤ → ℂ := fun z p ↦
      if A < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 then φ z (p.1 * L.ω₁ + p.2 * L.ω₂) else 0
    (∀ z ∈ D, Summable fun p ↦ ‖ψ z p‖) ∧
      TendstoUniformlyOn (fun (s : Finset (ℤ × ℤ)) z ↦ ∑ p ∈ s, ψ z p) (fun z ↦ ∑' p, ψ z p) atTop D := by
  intro ψ
  have hu := (summable_sq_add_sq_rpow_neg c hc).mul_left (max B 0)
  have hb : ∀ (p : ℤ × ℤ) z, z ∈ D →
      ‖ψ z p‖ ≤ max B 0 * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-c)) := by
    intro p z hz
    have hnn : 0 ≤ ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-c) := by positivity
    by_cases h : A < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2
    · simp only [ψ, if_pos h]
      exact (hφ p.1 p.2 h z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn)
    · simp only [ψ, if_neg h, norm_zero]
      positivity
  refine ⟨fun z hz ↦ ?_, tendstoUniformlyOn_tsum hu hb⟩
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ hb p z hz) hu

/-! ### Named statements: Theorem 3.8, Propositions 3.9, 3.11, 3.12, 3.13 -/

/-- **Milne, Theorem 3.8** (named statement). Given `n ≥ 2` points `P₁, …, Pₙ` and `Q₁, …, Qₙ` of `ℂ` (with
repetitions), no `Pᵢ` congruent to a `Qⱼ` modulo `Λ`, and `∑ Pᵢ ≡ ∑ Qⱼ (mod Λ)`, there is a doubly periodic function
whose poles are the `Pᵢ` and whose zeros are the `Qⱼ` (modulo `Λ`, with multiplicity), unique up to a nonzero
constant factor. Multiplicities: the order of `f` at `z` is the number of `j` with `Qⱼ ≡ z` minus the number of `i`
with `Pᵢ ≡ z`. The book cites an elementary construction, or Riemann–Roch on `ℂ/Λ`. -/
@[kb "milne2017mf" "Theorem 3.8, pdf p. 45"]
structure PrescribedDivisorStatement : Prop where
  out : ∀ (L : PeriodPair) (n : ℕ) (P Q : Fin n → ℂ), 2 ≤ n →
    (∀ i j, P i - Q j ∉ L.lattice) → (∑ i, P i) - (∑ j, Q j) ∈ L.lattice →
    let ordAt : ℂ → ℤ := fun z ↦ haveI := Classical.propDecidable; ((Finset.univ.filter fun j ↦ Q j - z ∈ L.lattice).card : ℤ) -
      ((Finset.univ.filter fun i ↦ P i - z ∈ L.lattice).card : ℤ)
    (∃ f : ℂ → ℂ, IsDoublyPeriodic L.lattice f ∧ ∀ z, meromorphicOrderAt f z = ordAt z) ∧
    ∀ f g : ℂ → ℂ, IsDoublyPeriodic L.lattice f → (∀ z, meromorphicOrderAt f z = ordAt z) →
      IsDoublyPeriodic L.lattice g → (∀ z, meromorphicOrderAt g z = ordAt z) →
        ∃ c : ℂ, c ≠ 0 ∧ ∀ᶠ z in codiscrete ℂ, g z = c * f z

/-- **Milne, Proposition 3.9 (addition formula)** (named statement):
`℘(z + z') = ¼ ((℘'(z) - ℘'(z'))/(℘(z) - ℘(z')))² - ℘(z) - ℘(z')`, for `z, z', z + z' ∉ Λ` with `℘(z) ≠ ℘(z')`.
The book's proof compares Laurent expansions and uses Liouville's theorem. -/
@[kb "milne2017mf" "Proposition 3.9, pdf p. 45"]
structure WeierstrassAdditionStatement : Prop where
  out : ∀ (L : PeriodPair) (z z' : ℂ), z ∉ L.lattice → z' ∉ L.lattice → z + z' ∉ L.lattice →
    ℘[L] z ≠ ℘[L] z' →
    ℘[L] (z + z') = (1 / 4) * ((℘'[L] z - ℘'[L] z') / (℘[L] z - ℘[L] z')) ^ 2 - ℘[L] z - ℘[L] z'

/-- **Milne, Proposition 3.11** (first part; named statement): the field of doubly periodic functions is
`ℂ(℘, ℘')`: every doubly periodic `f` is `P(℘, ℘')/Q(℘, ℘')` off a discrete set, for polynomials `P, Q` with
`Q(℘, ℘')` not identically zero. (The second part, `℘'² = 4℘³ - g₂℘ - g₃`, is Mathlib's
`PeriodPair.derivWeierstrassP_sq`.) -/
@[kb "milne2017mf" "Proposition 3.11, pdf p. 46"]
structure EllipticFunctionFieldStatement : Prop where
  out : ∀ (L : PeriodPair) (f : ℂ → ℂ), IsDoublyPeriodic L.lattice f →
    ∃ P Q : MvPolynomial (Fin 2) ℂ,
      ¬ (∀ᶠ z in codiscrete ℂ, MvPolynomial.eval ![℘[L] z, ℘'[L] z] Q = 0) ∧
      ∀ᶠ z in codiscrete ℂ, f z * MvPolynomial.eval ![℘[L] z, ℘'[L] z] Q = MvPolynomial.eval ![℘[L] z, ℘'[L] z] P

/-- **Milne, Proposition 3.12** (first statement): `E(Λ)` is an elliptic curve, `Δ = g₂³ - 27g₃² ≠ 0`. Tau Ceti:
`PeriodPair.weierstrassCurve_Δ_ne_zero` (for the model `y² = x³ - (g₂/4)x - g₃/4`, isomorphic to Milne's
`Y²Z = 4X³ - g₂XZ² - g₃Z³` by `y ↦ 2y`, with discriminant `g₂³ - 27g₃²`, Tau Ceti `weierstrassCurve_Δ`). -/
@[kb "milne2017mf" "Proposition 3.12: E(Lambda) is an elliptic curve, pdf p. 47"]
theorem g₂_cube_sub_g₃_sq_ne_zero (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
  rw [← L.weierstrassCurve_Δ]
  exact L.weierstrassCurve_Δ_ne_zero

/-- **Milne, Proposition 3.12** (second and third statements; named statement): the map
`[z] ↦ (℘(z) : ℘'(z) : 1)`, `[0] ↦ (0 : 1 : 0)` is a bijection `ℂ/Λ → E(Λ)` (Tau Ceti's
`PeriodPair.weierstrassPoint`, in the model `(℘, ℘'/2)`; Tau Ceti also proves it is given locally by holomorphic
functions in projective coordinates, `PeriodPair.exists_analyticAt_toAffine_eq_weierstrassPoint`), and every elliptic
curve over `ℂ` is isomorphic to `E(Λ)` for some lattice. The book proves the last part with the `j`-function in §4.
Deviation: Mathlib has no complex structure on `E(ℂ)`, so "isomorphism of Riemann surfaces" is recorded as a
bijection given locally by holomorphic coordinates. -/
@[kb "milne2017mf" "Proposition 3.12, pdf p. 47"]
structure WeierstrassUniformizationStatement : Prop where
  bijective : ∀ L : PeriodPair, ∃ F : ComplexTorus L → L.weierstrassCurve.toAffine.Point,
    Function.Bijective F ∧ ∀ z, F (ComplexTorus.mk L z) = L.weierstrassPoint z
  surjective : ∀ E : WeierstrassCurve ℂ, E.IsElliptic → ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ),
    C • E = L.weierstrassCurve

/-- **Milne, Proposition 3.13** (named statement, the part beyond 3.3 and 3.12): every compact Riemann surface of genus
one with a base point is isomorphic, by an isomorphism of Riemann surfaces preserving base points, to a complex torus
`ℂ/Λ`. With Proposition 3.3 (morphisms of pointed tori are the `α` with `αΛ ⊆ Λ'`) and Proposition 3.12 this gives
the equivalences of categories (b) ≃ (c) and, on objects, (a) ≃ (b). Genus one is expressed topologically as
"homeomorphic to `ℝ²/ℤ²`" (Milne, p. 41). Deviation: the morphisms of category (a), regular maps of elliptic curves,
are not formalized. -/
@[kb "milne2017mf" "Proposition 3.13, pdf p. 47"]
structure GenusOneStatement : Prop where
  out : ∀ (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) 1 E] (x₀ : E),
    Nonempty (E ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) →
    ∃ (L : PeriodPair) (e : E ≃ ComplexTorus L), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm ∧ e x₀ = ComplexTorus.mk L 0

end ModularFormsKB.Milne
