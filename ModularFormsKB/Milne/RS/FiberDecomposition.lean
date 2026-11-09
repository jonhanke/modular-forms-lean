import TauCeti.Analysis.Complex.RiemannSurface.FiberMultiset
import TauCeti.Analysis.Complex.RiemannSurface.LocalNormalForm
import TauCeti.Analysis.Complex.RiemannSurface.Degree
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Fibre decomposition near a point, in normal-form charts

Public restatement of Tau Ceti's private fibre decomposition near a point (normal-form charts), for
the residue theorem (Milne, Proposition 1.12 (b)).

The two theorems `exists_chart_sum_replicate_inter_source_eq'` and
`exists_charts_eventually_fiberMultiset_eq'` are copies of the private theorems
`exists_chart_sum_replicate_inter_source_eq` and `exists_charts_eventually_fiberMultiset_eq` of
Tau Ceti's `TauCeti/Analysis/Complex/RiemannSurface/FiberMultiset.lean` (Apache-2.0, copyright The
Tau Ceti contributors), with the conclusions strengthened by the normal form
`e' (f x') - e' (f x) = e x' ^ localMultiplicity f x` on the chart domain. The final theorem
`eventually_sum_map_fiberMultiset_eq` distributes a sum of an arbitrary function `g` over the
decomposition, as in the end of the proof of Tau Ceti's `analyticAt_sum_map_fiberMultiset`.
-/

open Filter Function IsManifold Polynomial Set Topology TauCeti.RiemannSurface

open scoped Manifold

namespace ModularFormsKB.Milne.RS

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] {f : X → Y}

/-- Public version of Tau Ceti's private `exists_chart_sum_replicate_inter_source_eq`, with the
normal form on the chart domain added. -/
theorem exists_chart_sum_replicate_inter_source_eq' {x : X}
    (hf : ∀ᶠ x' in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x') (hne : ¬ EventuallyConst f (𝓝 x))
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) (hfx : f x ∈ e'.source)
    {W : Set X} (hW : W ∈ 𝓝 x) :
    ∃ e : OpenPartialHomeomorph X ℂ, e ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ e.source ∧ e x = 0 ∧
      e.source ⊆ W ∧
      (∀ x' ∈ e.source, f x' ∈ e'.source ∧
        e' (f x') - e' (f x) = e x' ^ localMultiplicity f x) ∧
      ∀ᶠ z in 𝓝 (e' (f x)),
        ∑ᶠ x' ∈ f ⁻¹' {e'.symm z} ∩ e.source,
            Multiset.replicate (localMultiplicity f x') x' =
          (nthRoots (localMultiplicity f x) (z - e' (f x))).map e.symm := by
  set m := localMultiplicity f x
  have hm : 0 < m := (localMultiplicity_pos_iff hf).2 hne
  have hW' : W ∩ {x' | x' = x ∨ localMultiplicity f x' = 1} ∈ 𝓝 x := by
    refine inter_mem hW ?_
    filter_upwards [eventually_nhdsWithin_iff.1 (eventually_localMultiplicity_eq_one hf hne)]
      with x' hx'
    by_cases h : x' = x
    · exact Or.inl h
    · exact Or.inr (hx' h)
  obtain ⟨e, he, hxe, hex, hsrc, hpow⟩ :=
    exists_chart_eq_pow_localMultiplicity hf hne he' hfx hW'
  refine ⟨e, he, hxe, hex, hsrc.trans inter_subset_left, hpow, ?_⟩
  set c := e' (f x)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target 0 (hex ▸ e.map_source hxe)
  filter_upwards [e'.open_target.mem_nhds (e'.map_source hfx),
    Metric.ball_mem_nhds c (pow_pos hr m)] with z hz hzr
  set s := z - c
  have hroot (w : ℂ) (hw : w ^ m = s) : w ∈ e.target := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_pow_lt_pow_left₀ m hr.le ?_
    rw [← norm_pow, hw]
    simpa [s, dist_eq_norm] using hzr
  have hmem (x' : X) : x' ∈ f ⁻¹' {e'.symm z} ∩ e.source ↔ x' ∈ e.source ∧ e x' ^ m = s := by
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨h2, ?_⟩, fun ⟨h2, h1⟩ ↦ ⟨?_, h2⟩⟩
    · have h := (hpow x' h2).2
      rw [mem_preimage, mem_singleton_iff] at h1
      rw [h1, e'.right_inv hz] at h
      exact h.symm
    · have h := hpow x' h2
      rw [mem_preimage, mem_singleton_iff, ← e'.left_inv h.1]
      congr 1
      linear_combination h.2 + h1
  have hpiece (x' : X) (hx' : x' ∈ f ⁻¹' {e'.symm z} ∩ e.source) :
      x' = e.symm (e x') := (e.left_inv ((hmem x').1 hx').1).symm
  rcases eq_or_ne s 0 with hs | hs
  · have hx : f ⁻¹' {e'.symm z} ∩ e.source = {x} := by
      ext x'
      rw [hmem, mem_singleton_iff]
      refine ⟨fun ⟨h2, h⟩ ↦ e.injOn h2 hxe ?_, fun h ↦ ⟨h ▸ hxe, by rw [h, hex, hs,
        zero_pow hm.ne']⟩⟩
      rw [hex]
      exact pow_eq_zero_iff hm.ne' |>.1 (h.trans hs)
    rw [hx, finsum_mem_singleton, hs, nthRoots_zero_right, Multiset.map_replicate, ← hex,
      e.left_inv hxe]
  · have hmult (x' : X) (hx' : x' ∈ f ⁻¹' {e'.symm z} ∩ e.source) :
        localMultiplicity f x' = 1 := by
      obtain ⟨h2, h⟩ := (hmem x').1 hx'
      refine (hsrc h2).2.resolve_left fun h' ↦ hs ?_
      rw [← h, h', hex, zero_pow hm.ne']
    have hfin : (f ⁻¹' {e'.symm z} ∩ e.source).Finite := by
      refine ((nthRootsFinset m s).finite_toSet.image e.symm).subset fun x' hx' ↦ ?_
      exact ⟨e x', by simpa [mem_nthRootsFinset hm] using ((hmem x').1 hx').2,
        (hpiece x' hx').symm⟩
    rw [finsum_mem_congr rfl fun x' hx' ↦ by rw [hmult x' hx', Multiset.replicate_one],
      finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_eq_multiset_sum,
      Multiset.sum_map_singleton]
    have hnodup : (nthRoots m s).Nodup :=
      (Complex.isPrimitiveRoot_exp m hm.ne').nthRoots_nodup hs
    refine (Multiset.Nodup.ext hfin.toFinset.nodup (hnodup.map_on fun w hw w' hw' h ↦ ?_)).2
      fun x' ↦ ?_
    · rw [mem_nthRoots hm] at hw hw'
      exact e.symm.injOn (hroot w hw) (hroot w' hw') h
    · rw [Finset.mem_val, hfin.mem_toFinset, Multiset.mem_map]
      refine ⟨fun hx' ↦ ⟨e x', (mem_nthRoots hm).2 ((hmem x').1 hx').2, (hpiece x' hx').symm⟩,
        ?_⟩
      rintro ⟨w, hw, rfl⟩
      rw [mem_nthRoots hm] at hw
      rw [hmem, e.right_inv (hroot w hw)]
      exact ⟨e.map_target (hroot w hw), hw⟩

/-- Public version of Tau Ceti's private `exists_charts_eventually_fiberMultiset_eq`, with the
normal form on the chart domains added. -/
theorem exists_charts_eventually_fiberMultiset_eq' [CompactSpace X] [T2Space X]
    [T2Space Y] (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x))
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) {y₀ : Y}
    (hy₀ : y₀ ∈ e'.source) :
    ∃ e : X → OpenPartialHomeomorph X ℂ,
      (∀ x ∈ f ⁻¹' {y₀}, e x ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ (e x).source ∧ e x x = 0 ∧
        ∀ x' ∈ (e x).source, f x' ∈ e'.source ∧
          e' (f x') - e' y₀ = e x x' ^ localMultiplicity f x) ∧
      ∀ᶠ z in 𝓝 (e' y₀), fiberMultiset f (e'.symm z) =
        ∑ᶠ x ∈ f ⁻¹' {y₀}, (nthRoots (localMultiplicity f x) (z - e' y₀)).map (e x).symm := by
  classical
  have hS : (f ⁻¹' {y₀}).Finite := finite_preimage_singleton hf hne y₀
  obtain ⟨O, hO, hOdisj⟩ := hS.t2_separation
  have hloc : ∀ x ∈ f ⁻¹' {y₀}, ∃ e : OpenPartialHomeomorph X ℂ,
      (e ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ e.source ∧ e x = 0 ∧
        ∀ x' ∈ e.source, f x' ∈ e'.source ∧
          e' (f x') - e' y₀ = e x' ^ localMultiplicity f x) ∧ e.source ⊆ O x ∧
      ∀ᶠ z in 𝓝 (e' y₀), ∑ᶠ x' ∈ f ⁻¹' {e'.symm z} ∩ e.source,
          Multiset.replicate (localMultiplicity f x') x' =
        (nthRoots (localMultiplicity f x) (z - e' y₀)).map e.symm := by
    intro x hx
    have hfx : f x = y₀ := hx
    obtain ⟨e, he, hxe, hex, hsub, hpow, hev⟩ := exists_chart_sum_replicate_inter_source_eq'
      (.of_forall fun z ↦ hf z) (hne x) he' (hfx ▸ hy₀) ((hO x).2.mem_nhds (hO x).1)
    refine ⟨e, ⟨he, hxe, hex, fun x' hx' ↦ ?_⟩, hsub, hfx ▸ hev⟩
    have h := hpow x' hx'
    rwa [hfx] at h
  choose e₀ he₀ hsub₀ hev₀ using hloc
  set e : X → OpenPartialHomeomorph X ℂ := fun x ↦
    if hx : x ∈ f ⁻¹' {y₀} then e₀ x hx else chartAt ℂ x
  have he_eq (x : X) (hx : x ∈ f ⁻¹' {y₀}) : e x = e₀ x hx := by
    have hfx : f x = y₀ := hx
    simp [e, hfx]
  have he (x : X) (hx : x ∈ f ⁻¹' {y₀}) :
      e x ∈ maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ (e x).source ∧ e x x = 0 ∧
        ∀ x' ∈ (e x).source, f x' ∈ e'.source ∧
          e' (f x') - e' y₀ = e x x' ^ localMultiplicity f x := he_eq x hx ▸ he₀ x hx
  have hsub (x : X) (hx : x ∈ f ⁻¹' {y₀}) : (e x).source ⊆ O x := he_eq x hx ▸ hsub₀ x hx
  have hev (x : X) (hx : x ∈ f ⁻¹' {y₀}) : ∀ᶠ z in 𝓝 (e' y₀),
      ∑ᶠ x' ∈ f ⁻¹' {e'.symm z} ∩ (e x).source,
          Multiset.replicate (localMultiplicity f x') x' =
        (nthRoots (localMultiplicity f x) (z - e' y₀)).map (e x).symm :=
    he_eq x hx ▸ hev₀ x hx
  refine ⟨e, he, ?_⟩
  have hK : IsCompact (⋃ x ∈ f ⁻¹' {y₀}, (e x).source)ᶜ :=
    (isOpen_biUnion fun x _ ↦ (e x).open_source).isClosed_compl.isCompact
  have hyK : y₀ ∉ f '' (⋃ x ∈ f ⁻¹' {y₀}, (e x).source)ᶜ := by
    rintro ⟨x, hxK, hfx⟩
    exact hxK (mem_iUnion₂.2 ⟨x, hfx, (he x hfx).2.1⟩)
  have hV₀ : (f '' (⋃ x ∈ f ⁻¹' {y₀}, (e x).source)ᶜ)ᶜ ∈ 𝓝 y₀ :=
    (hK.image hf.continuous).isClosed.isOpen_compl.mem_nhds hyK
  have hsymm : Tendsto e'.symm (𝓝 (e' y₀)) (𝓝 y₀) := by
    have h := (e'.continuousAt_symm (e'.map_source hy₀)).tendsto
    rwa [e'.left_inv hy₀] at h
  filter_upwards [hsymm.eventually hV₀, hS.eventually_all.2 hev] with z hz hzev
  have hfib : f ⁻¹' {e'.symm z} = ⋃ x ∈ f ⁻¹' {y₀}, (f ⁻¹' {e'.symm z} ∩ (e x).source) := by
    ext x'
    refine ⟨fun hx' ↦ ?_, fun hx' ↦ ?_⟩
    · have hx'U : x' ∈ ⋃ x ∈ f ⁻¹' {y₀}, (e x).source := by
        by_contra h
        exact hz ⟨x', h, hx'⟩
      obtain ⟨x, hx, hx'U⟩ := mem_iUnion₂.1 hx'U
      exact mem_iUnion₂.2 ⟨x, hx, hx', hx'U⟩
    · obtain ⟨x, -, hx'⟩ := mem_iUnion₂.1 hx'
      exact hx'.1
  have hdisj : (f ⁻¹' {y₀}).PairwiseDisjoint fun x ↦ f ⁻¹' {e'.symm z} ∩ (e x).source :=
    hOdisj.mono_on fun x hx ↦ inter_subset_right.trans (hsub x hx)
  have hfin := finite_preimage_singleton hf hne (e'.symm z)
  rw [fiberMultiset_def, hfib,
    finsum_mem_biUnion hdisj hS fun x _ ↦ hfin.subset inter_subset_left]
  exact finsum_mem_congr rfl hzev

/-- **Decomposition of fibre sums near a point.** In normal-form charts `e x` at the points of the
fibre over `y₀`, for `z` near `e' y₀` the sum of any function `g` over the fibre multiset of
`e'.symm z` is the sum over the points `x` of the fibre of `y₀` of the sums of `g ∘ (e x).symm` over
the `m`-th roots of `z - e' y₀`, where `m` is the local multiplicity of `f` at `x`. -/
theorem eventually_sum_map_fiberMultiset_eq [CompactSpace X] [T2Space X] [T2Space Y]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x))
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 Y) {y₀ : Y}
    (hy₀ : y₀ ∈ e'.source) :
    ∃ e : X → OpenPartialHomeomorph X ℂ,
      (∀ x ∈ f ⁻¹' {y₀}, e x ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X ∧ x ∈ (e x).source ∧
        e x x = 0 ∧
        ∀ x' ∈ (e x).source, f x' ∈ e'.source ∧
          e' (f x') - e' y₀ = e x x' ^ localMultiplicity f x) ∧
      ∀ g : X → ℂ, ∀ᶠ z in 𝓝 (e' y₀), ((fiberMultiset f (e'.symm z)).map g).sum =
        ∑ x ∈ (finite_preimage_singleton hf hne y₀).toFinset,
          ((Polynomial.nthRoots (localMultiplicity f x) (z - e' y₀)).map
            (g ∘ (e x).symm)).sum := by
  obtain ⟨e, he, hev⟩ := exists_charts_eventually_fiberMultiset_eq' hf hne he' hy₀
  refine ⟨e, he, fun g ↦ ?_⟩
  have hS : (f ⁻¹' {y₀}).Finite := finite_preimage_singleton hf hne y₀
  filter_upwards [hev] with z hz
  rw [hz, finsum_mem_eq_finite_toFinset_sum _ hS, ← Multiset.coe_mapAddMonoidHom, map_sum,
    ← Multiset.coe_sumAddMonoidHom, map_sum]
  simp only [Multiset.coe_mapAddMonoidHom, Multiset.coe_sumAddMonoidHom, Multiset.map_map]

end ModularFormsKB.Milne.RS
