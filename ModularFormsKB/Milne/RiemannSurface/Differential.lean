import ModularFormsKB.Milne.RiemannSurface.Basic

/-!
# Milne, Chapter 1: the differential of a function; finiteness of divisors of differentials

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, pdf pp. 17–21.

* `differential`: the differential `df = (df/dz) dz` of a meromorphic function (p. 17).
* `MeromorphicDifferential.finite_support_ordZ`: the divisor of a nonzero differential form on a compact Riemann
  surface is a finite sum (p. 21).
-/

open Filter Topology Set
open scoped Manifold

namespace ModularFormsKB.Milne.RiemannSurface

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-! ### The differential of a meromorphic function -/

section Differential

/-- The transition map between preferred charts is analytic at points of the overlap. -/
theorem analyticAt_transition (x y : X) {v : ℂ} (hv : v ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm v ∈ (chartAt ℂ y).source) :
    AnalyticAt ℂ (transition x y) v := by
  have h := TauCeti.analyticAt_symm_trans
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) x)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) y)
    ((chartAt ℂ x).map_target hv) hy
  rw [(chartAt ℂ x).right_inv hv] at h
  exact h

variable [ConnectedSpace X]

/-- **The differential `df`** of a meromorphic function (Milne, p. 17): in the chart `z_x` its coefficient is
`d(f ∘ z_x⁻¹)/dz_x`. -/
@[kb "milne2017mf" "§1, the differential df of a meromorphic function, pdf p. 17"]
noncomputable def differential (f : MeromorphicFunction X) : MeromorphicDifferential X where
  coeff x := deriv (f.finitePart ∘ (chartAt ℂ x).symm)
  meromorphicAt := by
    intro x w hw
    have h := (TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas
      (f := f.finitePart) (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) x)
      ((chartAt ℂ x).map_target hw)).1 (f.meromorphicAt_finitePart _)
    rw [(chartAt ℂ x).right_inv hw] at h
    exact h.deriv
  compat := by
    intro x y w hw hp
    have hT : ∀ᶠ v in 𝓝 w, v ∈ (chartAt ℂ x).target ∧
        (chartAt ℂ x).symm v ∈ (chartAt ℂ y).source :=
      Filter.Eventually.and ((chartAt ℂ x).open_target.mem_nhds hw)
        (((chartAt ℂ x).continuousAt_symm hw).tendsto.eventually
          ((chartAt ℂ y).open_source.mem_nhds hp))
    have heq : (f.finitePart ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 w]
        ((f.finitePart ∘ (chartAt ℂ y).symm) ∘ transition x y) := by
      filter_upwards [hT] with v hv
      simp only [Function.comp, transition]
      rw [(chartAt ℂ y).left_inv hv.2]
    have hmer : _root_.MeromorphicAt (f.finitePart ∘ (chartAt ℂ y).symm) (transition x y w) :=
      (TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas
        (f := f.finitePart) (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) y)
        hp).1 (f.meromorphicAt_finitePart _)
    have han := hmer.eventually_analyticAt
    have hTw : AnalyticAt ℂ (transition x y) w := analyticAt_transition x y hw hp
    have htend : Tendsto (transition x y) (𝓝[≠] w) (𝓝[≠] (transition x y w)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hTw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [nhdsWithin_le_nhds hT, self_mem_nhdsWithin] with v hv hne h
      apply hne
      have h1 : (chartAt ℂ x).symm v = (chartAt ℂ x).symm w :=
        (chartAt ℂ y).injOn hv.2 hp h
      rw [← (chartAt ℂ x).right_inv hv.1, h1, (chartAt ℂ x).right_inv hw]
      exact Set.mem_singleton _
    filter_upwards [nhdsWithin_le_nhds heq.deriv, htend.eventually han,
      nhdsWithin_le_nhds hT] with v h1 h2 h3
    rw [h1]
    exact deriv_comp v h2.differentiableAt
      (analyticAt_transition x y h3.1 h3.2).differentiableAt

end Differential

section Compact

/-- The order of a differential at `q` is the order of the coefficient in the chart at any `p` whose chart
contains `q`, read at `z_p q`. -/
theorem MeromorphicDifferential.ord_eq_meromorphicOrderAt_coeff (ω : MeromorphicDifferential X)
    {p q : X} (hq : q ∈ (chartAt ℂ p).source) :
    ω.ord q = _root_.meromorphicOrderAt (ω.coeff p) (chartAt ℂ p q) := by
  have hw : chartAt ℂ p q ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hq
  have hsym : (chartAt ℂ p).symm (chartAt ℂ p q) = q := (chartAt ℂ p).left_inv hq
  have hp : (chartAt ℂ p).symm (chartAt ℂ p q) ∈ (chartAt ℂ q).source := by
    rw [hsym]; exact mem_chart_source ℂ q
  have hc := ω.compat p q _ hw hp
  have hTan := analyticAt_transition p q hw hp
  have hder : deriv (transition p q) (chartAt ℂ p q) ≠ 0 :=
    TauCeti.deriv_symm_trans_ne_zero (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) p)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) q) hq (mem_chart_source ℂ q)
  have hTw : transition p q (chartAt ℂ p q) = chartAt ℂ q q := by
    simp only [transition, hsym]
  have h1 : _root_.meromorphicOrderAt (ω.coeff q ∘ transition p q) (chartAt ℂ p q) =
      _root_.meromorphicOrderAt (ω.coeff q) (chartAt ℂ q q) := by
    rw [_root_.meromorphicOrderAt_comp_of_deriv_ne_zero hTan hder, hTw]
  have h2 : _root_.meromorphicOrderAt (deriv (transition p q)) (chartAt ℂ p q) = 0 := by
    have := (_root_.meromorphicOrderAt_eq_int_iff (n := 0) hTan.deriv.meromorphicAt).2
      ⟨deriv (transition p q), hTan.deriv, hder, by simp⟩
    simpa using this
  have hm1 : _root_.MeromorphicAt (ω.coeff q ∘ transition p q) (chartAt ℂ p q) := by
    refine MeromorphicAt.comp_analyticAt ?_ hTan
    rw [hTw]
    exact ω.meromorphicAt q _ ((chartAt ℂ q).map_source (mem_chart_source ℂ q))
  have h3 := _root_.meromorphicOrderAt_mul hm1 hTan.deriv.meromorphicAt
  rw [h1, h2, add_zero] at h3
  rw [_root_.meromorphicOrderAt_congr hc]
  exact h3.symm

/-- Away from a point, the order of a differential vanishes in a punctured neighbourhood. -/
theorem eventually_ordZ_eq_zero (ω : MeromorphicDifferential X) (p : X) :
    ∀ᶠ q in 𝓝[≠] p, ω.ordZ q = 0 := by
  have hc := ω.meromorphicAt p (chartAt ℂ p p) ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  have key : ∀ᶠ w in 𝓝[≠] (chartAt ℂ p p), (_root_.meromorphicOrderAt (ω.coeff p) w).untop₀ = 0 := by
    rcases hc.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · have h1 := (eventually_nhdsWithin_iff.1 h0).eventually_nhds
      filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with y hy hya
      have : _root_.meromorphicOrderAt (ω.coeff p) y = ⊤ := by
        refine _root_.meromorphicOrderAt_eq_top_iff.2 ?_
        filter_upwards [nhdsWithin_le_nhds hy, nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hya)] with x hx hxa
        exact hx hxa
      simp [this]
    · filter_upwards [hc.eventually_analyticAt, hne] with y hy hy0
      have := (_root_.meromorphicOrderAt_eq_int_iff (n := 0) hy.meromorphicAt).2
        ⟨ω.coeff p, hy, hy0, by simp⟩
      simp [this]
  have h2 := (TauCeti.tendsto_chartAt_nhdsNE p).eventually key
  have h3 : ∀ᶠ q in 𝓝[≠] p, q ∈ (chartAt ℂ p).source :=
    nhdsWithin_le_nhds ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
  filter_upwards [h2, h3] with q hq1 hq2
  rw [MeromorphicDifferential.ordZ, ω.ord_eq_meromorphicOrderAt_coeff hq2]
  exact hq1

variable [CompactSpace X] [ConnectedSpace X] [T2Space X]

/-- The divisor of a nonzero differential form on a compact Riemann surface is a finite sum (Milne, p. 21). -/
@[kb "milne2017mf" "§1, div(omega) is a finite sum, pdf p. 21"]
theorem MeromorphicDifferential.finite_support_ordZ {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) :
    (Function.support ω.ordZ).Finite := by
  have hloc : ∀ p : X, {q | q = p ∨ ω.ordZ q = 0} ∈ 𝓝 p := fun p ↦ by
    filter_upwards [eventually_nhdsWithin_iff.1 (eventually_ordZ_eq_zero ω p)] with q hq
    by_cases h : q = p
    · exact Or.inl h
    · exact Or.inr (hq h)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover _ fun p _ ↦ hloc p
  refine t.finite_toSet.subset fun q hq ↦ ?_
  obtain ⟨p, hp, hqp⟩ := Set.mem_iUnion₂.1 (ht.2 (Set.mem_univ q))
  rcases hqp with h | h
  · simpa [h] using hp
  · exact absurd h hq

end Compact

end ModularFormsKB.Milne.RiemannSurface
