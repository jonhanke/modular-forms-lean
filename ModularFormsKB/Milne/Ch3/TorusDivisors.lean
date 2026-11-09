import ModularFormsKB.Milne.Ch3.ParallelogramContour

/-!
# Milne, Chapter 3: divisors of elliptic functions on the torus

For a doubly periodic function `f` for `Λ = L.lattice` we record its divisor as a finitely supported function
`ellDiv hf : ℂ ⧸ Λ →₀ ℤ` on the torus (the additive group `ℂ ⧸ Λ`, not to be confused with the complex manifold
`ComplexTorus L`), and restate Milne's Proposition 3.1 (a), (c) on the torus: the degree of the divisor is `0`
(`ellDiv_degree`) and the sum of the divisor in the group `ℂ ⧸ Λ` is `0` (`ellDiv_sum`). The proof chooses a
fundamental parallelogram whose boundary avoids the (countable) set of zeros and poles and uses that the open
parallelogram is a set of representatives of the classes meeting it.
-/

open Complex Filter Topology Set PeriodPair

namespace ModularFormsKB.Milne

noncomputable section

variable {L : PeriodPair}

variable (L) in
/-- The torus `ℂ ⧸ Λ` as an additive group. -/
abbrev Torus : Type := ℂ ⧸ L.lattice.toAddSubgroup

variable (L) in
/-- The class of `z` in `ℂ ⧸ Λ`. -/
def tmk (z : ℂ) : Torus L := QuotientAddGroup.mk z

theorem tmk_eq_tmk_iff {z w : ℂ} : tmk L z = tmk L w ↔ z - w ∈ L.lattice := by
  unfold tmk
  rw [QuotientAddGroup.eq]
  constructor
  · intro h
    have := L.lattice.neg_mem h
    simpa [neg_add_eq_sub] using this
  · intro h
    have := L.lattice.neg_mem h
    simpa [neg_add_eq_sub] using this

theorem tmk_surjective : Function.Surjective (tmk L) := QuotientAddGroup.mk_surjective

@[simp] theorem tmk_add (z w : ℂ) : tmk L (z + w) = tmk L z + tmk L w := rfl
@[simp] theorem tmk_neg (z : ℂ) : tmk L (-z) = -tmk L z := rfl
@[simp] theorem tmk_sub (z w : ℂ) : tmk L (z - w) = tmk L z - tmk L w := rfl
@[simp] theorem tmk_zero : tmk L 0 = 0 := rfl

theorem tmk_eq_zero_iff {z : ℂ} : tmk L z = 0 ↔ z ∈ L.lattice := by
  rw [← tmk_zero, tmk_eq_tmk_iff, sub_zero]

theorem tmk_zsmul (n : ℤ) (z : ℂ) : tmk L ((n : ℂ) * z) = n • tmk L z := by
  rw [← zsmul_eq_mul]; rfl

/-! ### The order function of a doubly periodic function -/

/-- The order of `f` at `z`, as an integer (`0` where `f` vanishes identically). -/
def ordZ (f : ℂ → ℂ) (z : ℂ) : ℤ := (meromorphicOrderAt f z).untop₀

theorem meromorphicOrderAt_add_period {f : ℂ → ℂ} {ω : ℂ} (hf : ∀ z, f (z + ω) = f z) (z : ℂ) :
    meromorphicOrderAt f (z + ω) = meromorphicOrderAt f z := by
  have h1 : f ∘ (· + ω) = f := funext hf
  have h2 := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (f := f) (x := z) (c := ω)
  rw [h1] at h2
  exact h2.symm

theorem IsDoublyPeriodic.meromorphicOrderAt_eq {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    {z w : ℂ} (h : z - w ∈ L.lattice) : meromorphicOrderAt f z = meromorphicOrderAt f w := by
  have : z = w + (z - w) := by ring
  rw [this, meromorphicOrderAt_add_period (hf.2 _ h)]

/-- The order function on the torus, `x ↦ ord_{x.out} f`. -/
def ordT (f : ℂ → ℂ) (x : Torus L) : ℤ := ordZ f (Quotient.out x)

theorem tmk_out (x : Torus L) : tmk L (Quotient.out x) = x := Quotient.out_eq x

theorem IsDoublyPeriodic.ordT_tmk {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) (z : ℂ) :
    ordT f (tmk L z) = ordZ f z := by
  unfold ordT ordZ
  rw [hf.meromorphicOrderAt_eq (tmk_eq_tmk_iff.1 (tmk_out (tmk L z)))]

/-! ### Countability of the zeros and poles -/

theorem countable_ordZ_ne_zero {f : ℂ → ℂ} (hf : MeromorphicOn f univ) :
    {z | ordZ f z ≠ 0}.Countable := by
  have : {z | ordZ f z ≠ 0} ⊆ ⋃ n : ℕ, (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) n)).support := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
    refine mem_iUnion.2 ⟨n, ?_⟩
    have hzB : z ∈ Metric.closedBall (0 : ℂ) n := by simpa using hn
    rw [Function.mem_support, MeromorphicOn.divisor_apply (hf.mono_set (subset_univ _)) hzB]
    exact hz
  refine Countable.mono this (countable_iUnion fun n ↦ ?_)
  exact ((hf.mono_set (subset_univ _)).divisor_support_finite_of_subset
    (isCompact_closedBall (0 : ℂ) n) le_rfl).countable

/-! ### Parallelograms whose boundary avoids a countable set -/

theorem isOpen_openParallelogram (z₀ : ℂ) : IsOpen (openParallelogram L z₀) := by
  have : openParallelogram L z₀ =
      {z | L.basis.repr (z - z₀) 0 ∈ Ioo 0 1 ∧ L.basis.repr (z - z₀) 1 ∈ Ioo 0 1} := by
    ext z
    obtain ⟨A, B, rfl⟩ := exists_comb (L := L) (z₀ := z₀) z
    have e : z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ - z₀ = (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ := by ring
    simp only [mem_ofPred_eq, e, (repr_comb A B).1, (repr_comb A B).2, mem_Ioo]
    constructor
    · rintro ⟨C, D, h0, h1, h2, h3, h⟩
      obtain ⟨rfl, rfl⟩ := comb_inj h
      exact ⟨⟨h0, h1⟩, h2, h3⟩
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      exact ⟨A, B, h0, h1, h2, h3, rfl⟩
  rw [this]
  exact (isOpen_Ioo.preimage ((continuous_repr 0).comp (continuous_id.sub continuous_const))).inter
    (isOpen_Ioo.preimage ((continuous_repr 1).comp (continuous_id.sub continuous_const)))

theorem frontier_openParallelogram_subset (z₀ : ℂ) :
    frontier (openParallelogram L z₀) ⊆ {z | ∃ A B : ℝ, z = z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ ∧
      (A = 0 ∨ A = 1 ∨ B = 0 ∨ B = 1)} := by
  intro z hz
  have hcl : z ∈ closedParallelogram L z₀ := by
    have := closure_minimal (openParallelogram_subset_closed L z₀)
      (isCompact_closedParallelogram L z₀).isClosed
    exact this hz.1
  have hnot : z ∉ openParallelogram L z₀ := by
    intro hD
    exact hz.2 ((isOpen_openParallelogram z₀).interior_eq.symm ▸ hD)
  obtain ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ := hcl
  refine ⟨A, B, rfl, ?_⟩
  by_contra h
  push Not at h
  exact hnot ⟨A, B, lt_of_le_of_ne hA0 (Ne.symm h.1), lt_of_le_of_ne hA1 h.2.1,
    lt_of_le_of_ne hB0 (Ne.symm h.2.2.1), lt_of_le_of_ne hB1 h.2.2.2, rfl⟩

theorem exists_notMem_countable {X : Set ℝ} (hX : X.Countable) : ∃ x : ℝ, x ∉ X :=
  (hX.dense_compl ℝ).nonempty

/-- For a countable set `C`, some fundamental parallelogram has no point of `C` on its boundary. -/
theorem exists_good_parallelogram {C : Set ℂ} (hC : C.Countable) :
    ∃ z₀ : ℂ, ∀ z ∈ frontier (openParallelogram L z₀), z ∉ C := by
  set X : Set ℝ := ((fun z ↦ L.basis.repr z 0) '' C) ∪ ((fun z ↦ L.basis.repr z 0 - 1) '' C)
  set Y : Set ℝ := ((fun z ↦ L.basis.repr z 1) '' C) ∪ ((fun z ↦ L.basis.repr z 1 - 1) '' C)
  obtain ⟨x, hx⟩ := exists_notMem_countable ((hC.image _).union (hC.image _) : X.Countable)
  obtain ⟨y, hy⟩ := exists_notMem_countable ((hC.image _).union (hC.image _) : Y.Countable)
  refine ⟨(x : ℂ) * L.ω₁ + (y : ℂ) * L.ω₂, fun z hz hzC ↦ ?_⟩
  obtain ⟨A, B, rfl, hAB⟩ := frontier_openParallelogram_subset _ hz
  have e : (x : ℂ) * L.ω₁ + (y : ℂ) * L.ω₂ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ =
      ((x + A : ℝ) : ℂ) * L.ω₁ + ((y + B : ℝ) : ℂ) * L.ω₂ := by push_cast; ring
  have h0 := (repr_comb (L := L) (x + A) (y + B)).1
  have h1 := (repr_comb (L := L) (x + A) (y + B)).2
  rw [← e] at h0 h1
  rcases hAB with rfl | rfl | rfl | rfl
  · exact hx (Or.inl ⟨_, hzC, by simp only at h0 ⊢; rw [h0]; ring⟩)
  · exact hx (Or.inr ⟨_, hzC, by simp only at h0 ⊢; rw [h0]; ring⟩)
  · exact hy (Or.inl ⟨_, hzC, by simp only at h1 ⊢; rw [h1]; ring⟩)
  · exact hy (Or.inr ⟨_, hzC, by simp only at h1 ⊢; rw [h1]; ring⟩)

/-- Distinct points of the open parallelogram are incongruent modulo `Λ`. -/
theorem injOn_tmk_openParallelogram (z₀ : ℂ) : InjOn (tmk L) (openParallelogram L z₀) := by
  rintro _ ⟨A, B, hA0, hA1, hB0, hB1, rfl⟩ _ ⟨C, D, hC0, hC1, hD0, hD1, rfl⟩ h
  rw [tmk_eq_tmk_iff] at h
  obtain ⟨m, n, hmn⟩ := L.mem_lattice.1 h
  have e : z₀ + (A : ℂ) * L.ω₁ + (B : ℂ) * L.ω₂ - (z₀ + (C : ℂ) * L.ω₁ + (D : ℂ) * L.ω₂) =
      ((A - C : ℝ) : ℂ) * L.ω₁ + ((B - D : ℝ) : ℂ) * L.ω₂ := by push_cast; ring
  rw [e] at hmn
  have := comb_inj (L := L) (z₀ := 0) (A := m) (B := n) (C := A - C) (D := B - D)
    (by push_cast at hmn ⊢; linear_combination hmn)
  have hm : m = 0 := by
    have h1 : (m : ℝ) < 1 := by linarith [this.1]
    have h2 : (-1 : ℝ) < m := by linarith [this.1]
    have : m < 1 := by exact_mod_cast h1
    have : -1 < m := by exact_mod_cast h2
    omega
  have hn : n = 0 := by
    have h1 : (n : ℝ) < 1 := by linarith [this.2]
    have h2 : (-1 : ℝ) < n := by linarith [this.2]
    have : n < 1 := by exact_mod_cast h1
    have : -1 < n := by exact_mod_cast h2
    omega
  have hAC : A = C := by have := this.1; rw [hm] at this; push_cast at this; linarith
  have hBD : B = D := by have := this.2; rw [hn] at this; push_cast at this; linarith
  rw [hAC, hBD]

/-! ### The divisor on the torus -/

theorem IsDoublyPeriodic.ordT_support_finite {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) :
    (Function.support (ordT (L := L) f)).Finite := by
  have hP := (hf.1.mono_set (subset_univ (closedParallelogram L 0))).divisor_support_finite_of_subset
    (isCompact_closedParallelogram L 0) le_rfl
  refine (hP.image (tmk L)).subset ?_
  intro x hx
  obtain ⟨z, rfl⟩ := tmk_surjective x
  obtain ⟨ω, hω, hz⟩ := exists_lattice_translate L 0 z
  refine ⟨z + ω, ?_, ?_⟩
  · rw [Function.mem_support, MeromorphicOn.divisor_apply (hf.1.mono_set (subset_univ _)) hz]
    rw [Function.mem_support, hf.ordT_tmk] at hx
    unfold ordZ at hx
    rwa [hf.meromorphicOrderAt_eq (show z + ω - z ∈ L.lattice by simpa using hω)]
  · rw [tmk_eq_tmk_iff]; simpa using hω

/-- **The divisor of a doubly periodic function on the torus `ℂ ⧸ Λ`.** -/
def ellDiv {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) : Torus L →₀ ℤ :=
  Finsupp.ofSupportFinite (ordT f) hf.ordT_support_finite

theorem ellDiv_apply {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) (x : Torus L) :
    ellDiv hf x = ordT f x := rfl

@[simp] theorem ellDiv_tmk {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) (z : ℂ) :
    ellDiv hf (tmk L z) = ordZ f z := hf.ordT_tmk z

/-- A doubly periodic function that is not identically zero has finite orders. -/
theorem IsDoublyPeriodic.meromorphicOrderAt_ne_top {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hnz : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ := fun hz ↦
  hnz (((meromorphicOn_univ.1 hf.1).exists_meromorphicOrderAt_eq_top_iff_eventually_zero).1 ⟨z, hz⟩)

theorem IsDoublyPeriodic.meromorphicOrderAt_eq_ordZ {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hnz : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) (z : ℂ) : meromorphicOrderAt f z = ordZ f z :=
  (WithTop.coe_untop₀_of_ne_top (hf.meromorphicOrderAt_ne_top hnz z)).symm

/-- Reindexing a sum over the divisor as a sum over a good fundamental parallelogram. -/
theorem ellDiv_sum_eq_finsum {M : Type*} [AddCommMonoid M] {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    {z₀ : ℂ} (hgood : ∀ z ∈ frontier (openParallelogram L z₀), ordZ f z = 0) (F : Torus L → ℤ → M)
    (hF : ∀ x, F x 0 = 0) :
    (ellDiv hf).sum F = ∑ᶠ z ∈ openParallelogram L z₀, F (tmk L z) (ordZ f z) := by
  classical
  set D := openParallelogram L z₀
  set G : Torus L → M := fun x ↦ F x (ellDiv hf x)
  have hsupp : Function.support G ⊆ tmk L '' D := by
    intro x hx
    have hx' : ellDiv hf x ≠ 0 := fun h0 ↦ hx (by simp only [G, h0, hF])
    obtain ⟨z, rfl⟩ := tmk_surjective x
    obtain ⟨ω, hω, hz⟩ := exists_lattice_translate L z₀ z
    have hzω : tmk L (z + ω) = tmk L z := by rw [tmk_eq_tmk_iff]; simpa using hω
    rw [← hzω, ellDiv_tmk] at hx'
    refine ⟨z + ω, ?_, hzω⟩
    have hcl := closedParallelogram_subset_closure L z₀ hz
    rw [closure_eq_self_union_frontier] at hcl
    rcases hcl with h | h
    · exact h
    · exact absurd (hgood _ h) hx'
  have h1 : (ellDiv hf).sum F = ∑ᶠ x, G x := by
    rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
    intro x hx
    have : ellDiv hf x ≠ 0 := fun h0 ↦ hx (by simp only [G, h0, hF])
    simpa using this
  rw [h1, ← finsum_mem_univ, finsum_mem_inter_support_eq G univ (tmk L '' D) (by
      rw [univ_inter, inter_eq_right.2 hsupp]),
    finsum_mem_image (injOn_tmk_openParallelogram z₀)]
  refine finsum_mem_congr rfl fun z _ ↦ ?_
  simp only [G, ellDiv_tmk]

theorem exists_good_parallelogram_of {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f) :
    ∃ z₀ : ℂ, ∀ z ∈ frontier (openParallelogram L z₀), ordZ f z = 0 := by
  obtain ⟨z₀, hz₀⟩ := exists_good_parallelogram (L := L) (countable_ordZ_ne_zero hf.1)
  exact ⟨z₀, fun z hz ↦ by simpa using hz₀ z hz⟩

/-- **Milne, Proposition 3.1 (a) on the torus**: the degree of the divisor is zero. -/
theorem ellDiv_degree {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hnz : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) : (ellDiv hf).sum (fun _ n ↦ n) = 0 := by
  obtain ⟨z₀, hz₀⟩ := exists_good_parallelogram_of hf
  rw [ellDiv_sum_eq_finsum hf hz₀ _ (fun _ ↦ rfl)]
  have hb : ∀ z ∈ frontier (openParallelogram L z₀), meromorphicOrderAt f z = 0 := fun z hz ↦ by
    rw [hf.meromorphicOrderAt_eq_ordZ hnz, hz₀ z hz]; rfl
  exact (doublyPeriodicSumsStatement.out L f hf hnz z₀ hb).1

/-- **Milne, Proposition 3.1 (c) on the torus** (Abel's condition): the sum of the divisor in the group
`ℂ ⧸ Λ` is zero. -/
theorem ellDiv_sum {f : ℂ → ℂ} (hf : IsDoublyPeriodic L.lattice f)
    (hnz : ¬ (∀ᶠ z in codiscrete ℂ, f z = 0)) : (ellDiv hf).sum (fun x n ↦ n • x) = 0 := by
  obtain ⟨z₀, hz₀⟩ := exists_good_parallelogram_of hf
  rw [ellDiv_sum_eq_finsum hf hz₀ (fun x n ↦ n • x) (fun _ ↦ zero_zsmul _)]
  have hb : ∀ z ∈ frontier (openParallelogram L z₀), meromorphicOrderAt f z = 0 := fun z hz ↦ by
    rw [hf.meromorphicOrderAt_eq_ordZ hnz, hz₀ z hz]; rfl
  have hc := (doublyPeriodicSumsStatement.out L f hf hnz z₀ hb).2.2
  have hfin : (openParallelogram L z₀ ∩ Function.support fun z ↦ ((ordZ f z : ℤ) : ℂ) * z).Finite := by
    have hP := (hf.1.mono_set (subset_univ (closedParallelogram L z₀))).divisor_support_finite_of_subset
      (isCompact_closedParallelogram L z₀) le_rfl
    refine hP.subset fun z hz ↦ ?_
    rw [Function.mem_support, MeromorphicOn.divisor_apply
      (hf.1.mono_set (subset_univ _)) (openParallelogram_subset_closed L z₀ hz.1)]
    intro h0
    apply hz.2
    simp only [ordZ, h0, Int.cast_zero, zero_mul]
  have e : ∑ᶠ z ∈ openParallelogram L z₀, ordZ f z • tmk L z =
      tmk L (∑ᶠ z ∈ openParallelogram L z₀, ((ordZ f z : ℤ) : ℂ) * z) := by
    rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := hfin.toFinset),
      finsum_mem_eq_sum_of_inter_support_eq _ (t := hfin.toFinset)]
    · rw [show tmk L = ((QuotientAddGroup.mk' L.lattice.toAddSubgroup : ℂ →+ Torus L) : ℂ → Torus L)
        from rfl, map_sum]
      exact Finset.sum_congr rfl fun z _ ↦ (tmk_zsmul (L := L) _ _).symm
    · ext z; simp only [Set.Finite.coe_toFinset, mem_inter_iff, Function.mem_support]; tauto
    · ext z
      simp only [Set.Finite.coe_toFinset, mem_inter_iff, Function.mem_support]
      constructor
      · rintro ⟨hz, h⟩
        refine ⟨⟨hz, ?_⟩, h⟩
        intro h0
        rcases mul_eq_zero.1 h0 with h1 | h1
        · exact h (by rw [show ordZ f z = 0 by exact_mod_cast h1, zero_zsmul])
        · exact h (by rw [h1, tmk_zero, zsmul_zero])
      · rintro ⟨⟨hz, -⟩, h⟩; exact ⟨hz, h⟩
  rw [e, tmk_eq_zero_iff]
  exact hc

end

end ModularFormsKB.Milne
