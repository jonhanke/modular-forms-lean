import ModularFormsKB.Milne.RiemannSurface.Results
import ModularFormsKB.Milne.RiemannSurface.Differential

/-!
# Milne, Corollary 1.21: `ℓ(K) = g` with `g` the dimension of the holomorphic differentials

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, pdf pp. 21–22.

For a nonzero meromorphic differential `ω` on a connected Riemann surface `X`, multiplication by `ω` is a linear
isomorphism from the Riemann–Roch space `L(div ω)` onto the space `holomorphicDifferentials X` of holomorphic
differentials (`rrSpaceEquivHolomorphicDifferentials`), so `ℓ(div ω) = genus X` (`ell_divisor_eq_genus`). This
identifies the integer `g` of the Riemann–Roch theorem with the genus used in the Riemann–Hurwitz formula.

Technique: the coefficients `(f ∘ z_x⁻¹) · ω_x` of `f ω` are meromorphic with nonnegative orders on the chart
targets; their meromorphic normal forms (Mathlib's `toMeromorphicNFOn`) are holomorphic and satisfy the exact
transformation rule. Conversely a holomorphic differential `η` gives the meromorphic function `η/ω`, built with Tau
Ceti's `MeromorphicFunction.ofMeromorphic` from the normal-form values of the quotients of coefficients.
-/

open Filter Topology Set
open scoped Manifold

namespace ModularFormsKB.Milne.RS

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction ModularFormsKB.Milne.RiemannSurface

/-! ### Local lemmas -/

/-- Two functions continuous at `w` that agree on a punctured neighbourhood agree at `w`. -/
theorem eq_of_eventuallyEq_nhdsNE {a b : ℂ → ℂ} {w : ℂ} (ha : ContinuousAt a w) (hb : ContinuousAt b w)
    (h : a =ᶠ[𝓝[≠] w] b) : a w = b w :=
  tendsto_nhds_unique (ha.tendsto.mono_left nhdsWithin_le_nhds)
    ((hb.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- The normal form of a meromorphic function with nonnegative orders on an open set is analytic there and agrees
with the function on punctured neighbourhoods. -/
theorem analyticAt_toMeromorphicNFOn {u : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hu : MeromorphicOn u U)
    (hord : ∀ w ∈ U, 0 ≤ _root_.meromorphicOrderAt u w) {w : ℂ} (hw : w ∈ U) :
    AnalyticAt ℂ (toMeromorphicNFOn u U) w := by
  have hNF := meromorphicNFOn_toMeromorphicNFOn u U hw
  rw [← hNF.meromorphicOrderAt_nonneg_iff_analyticAt]
  rw [_root_.meromorphicOrderAt_congr (hu.toMeromorphicNFOn_eq_self_on_nhdsNE hw)]
  exact hord w hw

/-! ### Charts -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

theorem chart_mem_maximalAtlas' (x : X) : chartAt ℂ x ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X :=
  IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) x

/-- A function meromorphic on `X` reads as a meromorphic function on every chart target. -/
theorem meromorphicAt_comp_chart_symm {g : X → ℂ} (hg : ∀ p, TauCeti.RiemannSurface.MeromorphicAt g p) (x : X)
    {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) : _root_.MeromorphicAt (g ∘ (chartAt ℂ x).symm) w := by
  have h := (TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas (f := g) (chart_mem_maximalAtlas' x)
    ((chartAt ℂ x).map_target hw)).1 (hg _)
  rwa [(chartAt ℂ x).right_inv hw] at h

/-- The order of a function at a point equals the order of its representative in any chart containing it. -/
theorem meromorphicOrderAt_comp_chart_symm (g : X → ℂ) (x : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) :
    _root_.meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) w =
      TauCeti.RiemannSurface.meromorphicOrderAt g ((chartAt ℂ x).symm w) := by
  rw [TauCeti.RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas (chart_mem_maximalAtlas' x)
    ((chartAt ℂ x).map_target hw), (chartAt ℂ x).right_inv hw]

/-- The transition map sends punctured neighbourhoods to punctured neighbourhoods. -/
theorem tendsto_transition_nhdsNE (x y : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source) :
    Tendsto (transition x y) (𝓝[≠] w) (𝓝[≠] (transition x y w)) := by
  have hT : ∀ᶠ v in 𝓝 w, v ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm v ∈ (chartAt ℂ y).source :=
    Filter.Eventually.and ((chartAt ℂ x).open_target.mem_nhds hw)
      (((chartAt ℂ x).continuousAt_symm hw).tendsto.eventually ((chartAt ℂ y).open_source.mem_nhds hy))
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((analyticAt_transition x y hw hy).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [nhdsWithin_le_nhds hT, self_mem_nhdsWithin] with v hv hne h
  apply hne
  have h1 : (chartAt ℂ x).symm v = (chartAt ℂ x).symm w := (chartAt ℂ y).injOn hv.2 hy h
  rw [← (chartAt ℂ x).right_inv hv.1, h1, (chartAt ℂ x).right_inv hw]
  exact Set.mem_singleton _

/-- Near `w`, the chart inverse at `x` factors through the chart inverse at `y` and the transition map. -/
theorem eventually_chart_symm_transition (x y : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source) :
    ∀ᶠ v in 𝓝 w, v ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm v ∈ (chartAt ℂ y).source ∧
      transition x y v ∈ (chartAt ℂ y).target ∧
      (chartAt ℂ y).symm (transition x y v) = (chartAt ℂ x).symm v := by
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds hw,
    ((chartAt ℂ x).continuousAt_symm hw).tendsto.eventually ((chartAt ℂ y).open_source.mem_nhds hy)]
    with v hv hvy
  exact ⟨hv, hvy, (chartAt ℂ y).map_source hvy, (chartAt ℂ y).left_inv hvy⟩

/-! ### A nonzero differential has finite order everywhere -/

/-- Near every point, the order of a differential is either `⊤` throughout or finite off the point. -/
theorem eventually_ord_top_or_ne_top (ω : MeromorphicDifferential X) (p : X) :
    (ω.ord p = ⊤ ∧ ∀ᶠ q in 𝓝 p, ω.ord q = ⊤) ∨ (ω.ord p ≠ ⊤ ∧ ∀ᶠ q in 𝓝[≠] p, ω.ord q ≠ ⊤) := by
  have hc := ω.meromorphicAt p (chartAt ℂ p p) ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  have hsrc : ∀ᶠ q in 𝓝 p, q ∈ (chartAt ℂ p).source :=
    (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)
  have hcont : Tendsto (chartAt ℂ p) (𝓝 p) (𝓝 (chartAt ℂ p p)) :=
    ((chartAt ℂ p).continuousAt (mem_chart_source ℂ p)).tendsto
  rcases hc.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · left
    have htop : ∀ y, (∀ᶠ v in 𝓝[≠] y, ω.coeff p v = 0) → _root_.meromorphicOrderAt (ω.coeff p) y = ⊤ :=
      fun y hy ↦ _root_.meromorphicOrderAt_eq_top_iff.2 hy
    have h1 := (eventually_nhdsWithin_iff.1 h0).eventually_nhds
    refine ⟨?_, ?_⟩
    · rw [MeromorphicDifferential.ord]; exact htop _ h0
    · filter_upwards [hsrc, hcont.eventually h1] with q hq hq1
      rw [ω.ord_eq_meromorphicOrderAt_coeff hq]
      by_cases hqp : chartAt ℂ p q = chartAt ℂ p p
      · rw [hqp]; exact htop _ h0
      · refine htop _ ?_
        filter_upwards [nhdsWithin_le_nhds hq1, nhdsWithin_le_nhds
          (isOpen_compl_singleton.mem_nhds (show chartAt ℂ p q ∈ ({chartAt ℂ p p} : Set ℂ)ᶜ from hqp))] with v hv hvp
        exact hv hvp
  · right
    refine ⟨fun h ↦ ?_, ?_⟩
    · rw [MeromorphicDifferential.ord, _root_.meromorphicOrderAt_eq_top_iff] at h
      obtain ⟨v, hv1, hv2⟩ := (h.and hne).exists
      exact hv2 hv1
    · have h2 := (TauCeti.tendsto_chartAt_nhdsNE p).eventually (hc.eventually_analyticAt.and hne)
      filter_upwards [h2, nhdsWithin_le_nhds hsrc] with q hq hq2
      rw [ω.ord_eq_meromorphicOrderAt_coeff hq2]
      have := (_root_.meromorphicOrderAt_eq_int_iff (n := 0) hq.1.meromorphicAt).2
        ⟨ω.coeff p, hq.1, hq.2, by simp⟩
      rw [this]; exact WithTop.coe_ne_top

variable [ConnectedSpace X]

/-- On a connected Riemann surface, a nonzero differential has finite order at every point. -/
theorem ord_ne_top_of_not_isZero {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) (p : X) :
    ω.ord p ≠ ⊤ := by
  let S : Set X := {q | ω.ord q = ⊤}
  have hopen : IsOpen S := isOpen_iff_mem_nhds.2 fun q hq ↦ by
    rcases eventually_ord_top_or_ne_top ω q with h | h
    · exact h.2
    · exact absurd hq h.1
  have hclosed : IsOpen Sᶜ := isOpen_iff_mem_nhds.2 fun q hq ↦ by
    rcases eventually_ord_top_or_ne_top ω q with h | h
    · exact absurd h.1 hq
    · have := eventually_nhdsWithin_iff.1 h.2
      filter_upwards [this] with q' hq'
      by_cases e : q' = q
      · subst e; exact h.1
      · exact hq' e
  rcases isClopen_iff.1 ⟨⟨hclosed⟩, hopen⟩ with h | h
  · intro hp
    have : p ∈ S := hp
    rw [h] at this
    exact this
  · intro _
    apply hω
    intro q
    have : q ∈ S := h ▸ mem_univ q
    exact this

/-- The chart inverse sends punctured neighbourhoods to punctured neighbourhoods. -/
theorem tendsto_chart_symm_nhdsNE (x : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) :
    Tendsto (chartAt ℂ x).symm (𝓝[≠] w) (𝓝[≠] ((chartAt ℂ x).symm w)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((chartAt ℂ x).continuousAt_symm hw).tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds hw), self_mem_nhdsWithin]
    with v hv hne h
  exact hne ((chartAt ℂ x).symm.injOn hv hw h)

/-- A differential with finite order at `(chartAt ℂ x).symm w` has coefficient nonzero near `w` (punctured). -/
theorem eventually_coeff_ne_zero {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) : ∀ᶠ v in 𝓝[≠] w, ω.coeff x v ≠ 0 := by
  have hm := ω.meromorphicAt x w hw
  have hq : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hw
  have hord := ord_ne_top_of_not_isZero hω ((chartAt ℂ x).symm w)
  rw [ω.ord_eq_meromorphicOrderAt_coeff hq, (chartAt ℂ x).right_inv hw] at hord
  rcases hm.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exact absurd (_root_.meromorphicOrderAt_eq_top_iff.2 h0) hord
  · exact hne

/-! ### From `L(div ω)` to holomorphic differentials -/

variable [CompactSpace X] [T2Space X]

/-- The coefficient of `F ω` in the chart at `x`. -/
noncomputable def mulCoeff (ω : MeromorphicDifferential X) (F : MeromorphicFunction X) (x : X) : ℂ → ℂ :=
  fun w ↦ F.finitePart ((chartAt ℂ x).symm w) * ω.coeff x w

theorem meromorphicOn_mulCoeff (ω : MeromorphicDifferential X) (F : MeromorphicFunction X) (x : X) :
    MeromorphicOn (mulCoeff ω F x) (chartAt ℂ x).target := fun w hw ↦
  (meromorphicAt_comp_chart_symm (fun p ↦ F.meromorphicAt_finitePart p) x hw).mul (ω.meromorphicAt x w hw)

theorem divisor_apply {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) (p : X) :
    ω.divisor p = ω.ordZ p := by
  classical
  unfold MeromorphicDifferential.divisor
  rw [dif_pos (MeromorphicDifferential.finite_support_ordZ hω)]
  rfl

theorem coe_ordZ {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) (p : X) :
    ((ω.ordZ p : ℤ) : WithTop ℤ) = ω.ord p := by
  unfold MeromorphicDifferential.ordZ
  exact WithTop.coe_untop₀_of_ne_top (ord_ne_top_of_not_isZero hω p)

theorem meromorphicOrderAt_mulCoeff_nonneg {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero)
    {F : MeromorphicFunction X} (hF : F ∈ rrSpace X ω.divisor) (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) : 0 ≤ _root_.meromorphicOrderAt (mulCoeff ω F x) w := by
  set p := (chartAt ℂ x).symm w
  have hp : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hw
  have h1 : _root_.meromorphicOrderAt (F.finitePart ∘ (chartAt ℂ x).symm) w = order p F := by
    rw [order_apply]
    exact meromorphicOrderAt_comp_chart_symm F.finitePart x hw
  have h2 : _root_.meromorphicOrderAt (ω.coeff x) w = ω.ord p := by
    rw [ω.ord_eq_meromorphicOrderAt_coeff hp, (chartAt ℂ x).right_inv hw]
  have hF' := hF p
  rw [divisor_apply hω] at hF'
  have hfun : mulCoeff ω F x = (F.finitePart ∘ (chartAt ℂ x).symm) * ω.coeff x := rfl
  rw [hfun, _root_.meromorphicOrderAt_mul
    (meromorphicAt_comp_chart_symm (fun p ↦ F.meromorphicAt_finitePart p) x hw) (ω.meromorphicAt x w hw),
    h1, h2, ← coe_ordZ hω p]
  by_cases h : order p F = ⊤
  · rw [h]; simp
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h
    rw [← hn] at hF' ⊢
    have : -ω.ordZ p ≤ n := by exact_mod_cast hF'
    exact_mod_cast (by omega : (0 : ℤ) ≤ n + ω.ordZ p)

open Classical in
/-- The holomorphic differential `F ω` (normal forms of the coefficients, `0` off the chart targets). -/
noncomputable def mulDiff (ω : MeromorphicDifferential X) (F : MeromorphicFunction X) : X → ℂ → ℂ :=
  fun x w ↦ if w ∈ (chartAt ℂ x).target then toMeromorphicNFOn (mulCoeff ω F x) (chartAt ℂ x).target w else 0

theorem mulDiff_eventuallyEq {ω : MeromorphicDifferential X} (F : MeromorphicFunction X) (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) :
    mulDiff ω F x =ᶠ[𝓝 w] toMeromorphicNFOn (mulCoeff ω F x) (chartAt ℂ x).target := by
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds hw] with v hv
  simp [mulDiff, hv]

theorem analyticAt_mulDiff {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) {F : MeromorphicFunction X}
    (hF : F ∈ rrSpace X ω.divisor) (x : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) :
    AnalyticAt ℂ (mulDiff ω F x) w :=
  (analyticAt_toMeromorphicNFOn (chartAt ℂ x).open_target (meromorphicOn_mulCoeff ω F x)
    (fun _ hv ↦ meromorphicOrderAt_mulCoeff_nonneg hω hF x hv) hw).congr (mulDiff_eventuallyEq F x hw).symm

theorem mulDiff_eventuallyEq_mulCoeff (ω : MeromorphicDifferential X) (F : MeromorphicFunction X) (x : X)
    {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) : mulDiff ω F x =ᶠ[𝓝[≠] w] mulCoeff ω F x :=
  ((mulDiff_eventuallyEq F x hw).filter_mono nhdsWithin_le_nhds).trans
    ((meromorphicOn_mulCoeff ω F x).toMeromorphicNFOn_eq_self_on_nhdsNE hw)

/-- The coefficients of `F ω` transform as a differential, on punctured neighbourhoods. -/
theorem mulCoeff_compat (ω : MeromorphicDifferential X) (F : MeromorphicFunction X) (x y : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) (hy : (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source) :
    mulCoeff ω F x =ᶠ[𝓝[≠] w] fun v ↦ mulCoeff ω F y (transition x y v) * deriv (transition x y) v := by
  filter_upwards [ω.compat x y w hw hy, nhdsWithin_le_nhds (eventually_chart_symm_transition x y hw hy)]
    with v hv hv2
  simp only [mulCoeff, hv, hv2.2.2.2]
  ring

theorem mulDiff_mem {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) {F : MeromorphicFunction X}
    (hF : F ∈ rrSpace X ω.divisor) : mulDiff ω F ∈ holomorphicDifferentials X := by
  refine ⟨fun x w hw ↦ by simp [mulDiff, hw], fun x w hw ↦
    (analyticAt_mulDiff hω hF x hw).differentiableAt.differentiableWithinAt, fun x y w hw hy ↦ ?_⟩
  have hTw : transition x y w ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy
  have hTan := analyticAt_transition x y hw hy
  have hR : AnalyticAt ℂ (fun v ↦ mulDiff ω F y (transition x y v) * deriv (transition x y) v) w :=
    ((analyticAt_mulDiff hω hF y hTw).comp hTan).mul hTan.deriv
  refine eq_of_eventuallyEq_nhdsNE (analyticAt_mulDiff hω hF x hw).continuousAt hR.continuousAt ?_
  have h3 : (fun v ↦ mulCoeff ω F y (transition x y v)) =ᶠ[𝓝[≠] w]
      fun v ↦ mulDiff ω F y (transition x y v) :=
    (tendsto_transition_nhdsNE x y hw hy).eventually (mulDiff_eventuallyEq_mulCoeff ω F y hTw).symm
  filter_upwards [mulDiff_eventuallyEq_mulCoeff ω F x hw, mulCoeff_compat ω F x y hw hy, h3]
    with v h1 h2 h3
  rw [h1, h2, h3]

/-- The finite part of a meromorphic function, read in a chart, near a point of the chart target (punctured). -/
theorem finitePart_comp_eventuallyEq {F : MeromorphicFunction X} {g : X → ℂ} (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target)
    (h : F.finitePart =ᶠ[𝓝[≠] (chartAt ℂ x).symm w] g) :
    (fun v ↦ F.finitePart ((chartAt ℂ x).symm v)) =ᶠ[𝓝[≠] w] fun v ↦ g ((chartAt ℂ x).symm v) :=
  (tendsto_chart_symm_nhdsNE x hw).eventually h

theorem mulDiff_eq_of_eventuallyEq {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero)
    {F : MeromorphicFunction X} (hF : F ∈ rrSpace X ω.divisor) {x : X} {w : ℂ} (hw : w ∈ (chartAt ℂ x).target)
    {b : ℂ → ℂ} (hb : ContinuousAt b w) (h : mulCoeff ω F x =ᶠ[𝓝[≠] w] b) : mulDiff ω F x w = b w :=
  eq_of_eventuallyEq_nhdsNE (analyticAt_mulDiff hω hF x hw).continuousAt hb
    ((mulDiff_eventuallyEq_mulCoeff ω F x hw).trans h)

/-- Multiplication by a nonzero differential, `L(div ω) → holomorphicDifferentials X`. -/
noncomputable def mulDiffLinear {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) :
    rrSpace X ω.divisor →ₗ[ℂ] holomorphicDifferentials X where
  toFun F := ⟨mulDiff ω F, mulDiff_mem hω F.2⟩
  map_add' F G := by
    apply Subtype.ext
    funext x w
    change mulDiff ω (F + G : MeromorphicFunction X) x w = mulDiff ω F x w + mulDiff ω G x w
    by_cases hw : w ∈ (chartAt ℂ x).target
    · refine mulDiff_eq_of_eventuallyEq hω (F + G).2 hw
        ((analyticAt_mulDiff hω F.2 x hw).add (analyticAt_mulDiff hω G.2 x hw)).continuousAt ?_
      have hsum := finitePart_comp_eventuallyEq (F := (F + G : MeromorphicFunction X)) x hw
        (finitePart_add_eventuallyEq (F : MeromorphicFunction X) G _)
      filter_upwards [hsum, mulDiff_eventuallyEq_mulCoeff ω F x hw,
        mulDiff_eventuallyEq_mulCoeff ω G x hw] with v h1 h2 h3
      simp only [Pi.add_apply, h2, h3, mulCoeff]
      erw [h1]
      simp only [Pi.add_apply]
      ring
    · simp [mulDiff, hw]
  map_smul' c F := by
    apply Subtype.ext
    funext x w
    change mulDiff ω (c • F : MeromorphicFunction X) x w = c * mulDiff ω F x w
    by_cases hw : w ∈ (chartAt ℂ x).target
    · refine mulDiff_eq_of_eventuallyEq hω (c • F).2 hw
        ((analyticAt_mulDiff hω F.2 x hw).continuousAt.const_mul c) ?_
      have hmul' : (c • (F : MeromorphicFunction X)).finitePart =ᶠ[𝓝[≠] (chartAt ℂ x).symm w]
          fun q ↦ c * (F : MeromorphicFunction X).finitePart q := by
        rw [Algebra.smul_def]
        refine (finitePart_mul_eventuallyEq _ _ _).trans ?_
        rw [finitePart_algebraMap]
        rfl
      have hmul := finitePart_comp_eventuallyEq x hw hmul'
      filter_upwards [hmul, mulDiff_eventuallyEq_mulCoeff ω F x hw] with v h1 h2
      simp only [h2, mulCoeff]
      erw [h1]
      ring
    · simp [mulDiff, hw]

theorem injective_mulDiffLinear {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) :
    Function.Injective (mulDiffLinear hω) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  by_contra hne
  have hF0 : (F : MeromorphicFunction X) ≠ 0 := fun h ↦ hne (Subtype.ext h)
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hw : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have h0 : ∀ v, mulDiff ω F x v = 0 := fun v ↦ congrFun (congrFun (congrArg Subtype.val hF) x) v
  have hsymm : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hne1 : ∀ᶠ v in 𝓝[≠] chartAt ℂ x x, (F : MeromorphicFunction X).finitePart ((chartAt ℂ x).symm v) ≠ 0 :=
    (tendsto_chart_symm_nhdsNE x hw).eventually (by rw [hsymm]; exact eventually_finitePart_ne_zero hF0 x)
  obtain ⟨v, h1, h2, h3⟩ := (hne1.and ((eventually_coeff_ne_zero hω x hw).and
    (mulDiff_eventuallyEq_mulCoeff ω F x hw))).exists
  rw [h0 v] at h3
  exact mul_ne_zero h1 h2 h3.symm

/-! ### From holomorphic differentials to `L(div ω)` -/

/-- The quotient `η_x / ω_x` of coefficients in the chart at `x`. -/
noncomputable def quotCoeff (ω : MeromorphicDifferential X) (η : X → ℂ → ℂ) (x : X) : ℂ → ℂ :=
  fun v ↦ η x v / ω.coeff x v

theorem analyticAt_eta {η : X → ℂ → ℂ} (hη : η ∈ holomorphicDifferentials X) (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) : AnalyticAt ℂ (η x) w :=
  (hη.2.1 x).analyticAt ((chartAt ℂ x).open_target.mem_nhds hw)

theorem meromorphicAt_quotCoeff (ω : MeromorphicDifferential X) {η : X → ℂ → ℂ}
    (hη : η ∈ holomorphicDifferentials X) (x : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) :
    _root_.MeromorphicAt (quotCoeff ω η x) w :=
  (analyticAt_eta hη x hw).meromorphicAt.div (ω.meromorphicAt x w hw)

theorem deriv_transition_ne_zero (x y : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source) : deriv (transition x y) w ≠ 0 := by
  have h := TauCeti.deriv_symm_trans_ne_zero (chart_mem_maximalAtlas' x) (chart_mem_maximalAtlas' y)
    ((chartAt ℂ x).map_target hw) hy
  rwa [(chartAt ℂ x).right_inv hw] at h

theorem quotCoeff_compat (ω : MeromorphicDifferential X) {η : X → ℂ → ℂ}
    (hη : η ∈ holomorphicDifferentials X) (x y : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source) :
    quotCoeff ω η x =ᶠ[𝓝[≠] w] fun v ↦ quotCoeff ω η y (transition x y v) := by
  have hT' : ∀ᶠ v in 𝓝 w, deriv (transition x y) v ≠ 0 :=
    (analyticAt_transition x y hw hy).deriv.continuousAt.eventually_ne (deriv_transition_ne_zero x y hw hy)
  filter_upwards [ω.compat x y w hw hy, nhdsWithin_le_nhds (eventually_chart_symm_transition x y hw hy),
    nhdsWithin_le_nhds hT'] with v hv hv2 hv3
  simp only [quotCoeff, hv, hη.2.2 x y v hv2.1 hv2.2.1]
  exact mul_div_mul_right _ _ hv3

/-- The values of `η / ω`: the normal form of the quotient of coefficients at the chart centre. -/
noncomputable def quotFun (ω : MeromorphicDifferential X) (η : X → ℂ → ℂ) (p : X) : ℂ :=
  toMeromorphicNFAt (quotCoeff ω η p) (chartAt ℂ p p) (chartAt ℂ p p)

theorem quotFun_comp_eventuallyEq (ω : MeromorphicDifferential X) {η : X → ℂ → ℂ}
    (hη : η ∈ holomorphicDifferentials X) (x : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) :
    (fun v ↦ quotFun ω η ((chartAt ℂ x).symm v)) =ᶠ[𝓝[≠] w] quotCoeff ω η x := by
  filter_upwards [(meromorphicAt_quotCoeff ω hη x hw).eventually_analyticAt,
    nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds hw)] with v hQ hv
  set p := (chartAt ℂ x).symm v
  have hpx : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hv
  have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hzp : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hzs : (chartAt ℂ p).symm (chartAt ℂ p p) ∈ (chartAt ℂ x).source := by rw [hzp]; exact hpx
  have hTz : transition p x (chartAt ℂ p p) = v := by
    simp only [transition, hzp, p, (chartAt ℂ x).right_inv hv]
  have hcomp := quotCoeff_compat ω hη p x hz hzs
  have han : AnalyticAt ℂ (fun u ↦ quotCoeff ω η x (transition p x u)) (chartAt ℂ p p) := by
    refine AnalyticAt.comp (g := quotCoeff ω η x) (f := transition p x) ?_ (analyticAt_transition p x hz hzs)
    rw [hTz]; exact hQ
  have h1 := (toMeromorphicNFAt_eventuallyEq_nhds_congr hcomp).eq_of_nhds
  rw [toMeromorphicNFAt_eq_self.2 han.meromorphicNFAt] at h1
  change toMeromorphicNFAt (quotCoeff ω η p) (chartAt ℂ p p) (chartAt ℂ p p) = _
  rw [h1]
  exact congrArg (quotCoeff ω η x) hTz

theorem meromorphicAt_quotFun (ω : MeromorphicDifferential X) {η : X → ℂ → ℂ}
    (hη : η ∈ holomorphicDifferentials X) (p : X) : TauCeti.RiemannSurface.MeromorphicAt (quotFun ω η) p := by
  have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  rw [TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas' p)
    (mem_chart_source ℂ p)]
  exact (meromorphicAt_quotCoeff ω hη p hz).congr (quotFun_comp_eventuallyEq ω hη p hz).symm

/-- The meromorphic function `η / ω`. -/
noncomputable def quotMero (ω : MeromorphicDifferential X) {η : X → ℂ → ℂ}
    (hη : η ∈ holomorphicDifferentials X) : MeromorphicFunction X :=
  ofMeromorphic (meromorphicAt_quotFun ω hη)

theorem quotMero_comp_eventuallyEq (ω : MeromorphicDifferential X) {η : X → ℂ → ℂ}
    (hη : η ∈ holomorphicDifferentials X) (x : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) :
    (fun v ↦ (quotMero ω hη).finitePart ((chartAt ℂ x).symm v)) =ᶠ[𝓝[≠] w] quotCoeff ω η x :=
  (finitePart_comp_eventuallyEq x hw (finitePart_ofMeromorphic_eventuallyEq _ _)).trans
    (quotFun_comp_eventuallyEq ω hη x hw)

theorem quotMero_mem {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) {η : X → ℂ → ℂ}
    (hη : η ∈ holomorphicDifferentials X) : quotMero ω hη ∈ rrSpace X ω.divisor := by
  intro p
  have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hzp : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  rw [order_apply, ← hzp, ← meromorphicOrderAt_comp_chart_symm _ p hz, hzp]
  rw [show (quotMero ω hη).finitePart ∘ (chartAt ℂ p).symm =
    fun v ↦ (quotMero ω hη).finitePart ((chartAt ℂ p).symm v) from rfl,
    _root_.meromorphicOrderAt_congr (quotMero_comp_eventuallyEq ω hη p hz)]
  have hq : quotCoeff ω η p = η p * (ω.coeff p)⁻¹ := by
    funext v; simp [quotCoeff, div_eq_mul_inv]
  have hηm := (analyticAt_eta hη p hz).meromorphicAt
  rw [hq, _root_.meromorphicOrderAt_mul hηm (ω.meromorphicAt p _ hz).inv, _root_.meromorphicOrderAt_inv,
    divisor_apply hω]
  have h1 : (0 : WithTop ℤ) ≤ _root_.meromorphicOrderAt (η p) (chartAt ℂ p p) :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hηm).1
      ⟨_, (analyticAt_eta hη p hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
  have h2 : _root_.meromorphicOrderAt (ω.coeff p) (chartAt ℂ p p) = (ω.ordZ p : WithTop ℤ) := by
    rw [coe_ordZ hω]; rfl
  rw [h2]
  by_cases ha : _root_.meromorphicOrderAt (η p) (chartAt ℂ p p) = ⊤
  · rw [ha]; simp
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 ha
    rw [← hn] at h1 ⊢
    have : (0 : ℤ) ≤ n := by exact_mod_cast h1
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add]
    exact_mod_cast (by omega : -ω.ordZ p ≤ n + -ω.ordZ p)

theorem mulDiffLinear_quotMero {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) {η : X → ℂ → ℂ}
    (hη : η ∈ holomorphicDifferentials X) :
    mulDiffLinear hω ⟨quotMero ω hη, quotMero_mem hω hη⟩ = ⟨η, hη⟩ := by
  apply Subtype.ext
  funext x w
  change mulDiff ω (quotMero ω hη) x w = η x w
  by_cases hw : w ∈ (chartAt ℂ x).target
  · refine mulDiff_eq_of_eventuallyEq hω (quotMero_mem hω hη) hw (analyticAt_eta hη x hw).continuousAt ?_
    filter_upwards [quotMero_comp_eventuallyEq ω hη x hw, eventually_coeff_ne_zero hω x hw] with v h1 h2
    simp only [mulCoeff, h1, quotCoeff]
    exact div_mul_cancel₀ _ h2
  · simp [mulDiff, hw, hη.1 x w hw]

theorem surjective_mulDiffLinear {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) :
    Function.Surjective (mulDiffLinear hω) := fun η ↦
  ⟨⟨quotMero ω η.2, quotMero_mem hω η.2⟩, mulDiffLinear_quotMero hω η.2⟩

/-- **Multiplication by a nonzero differential** is a linear isomorphism from `L(div ω)` onto the holomorphic
differentials (Milne, p. 22: `L(K) ≅ Ω¹(X)`). -/
@[kb "milne2017mf" "§1, proof of Corollary 1.21: L(K) is the space of holomorphic differentials, pdf p. 22"]
noncomputable def rrSpaceEquivHolomorphicDifferentials {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) :
    rrSpace X ω.divisor ≃ₗ[ℂ] holomorphicDifferentials X :=
  LinearEquiv.ofBijective (mulDiffLinear hω) ⟨injective_mulDiffLinear hω, surjective_mulDiffLinear hω⟩

/-- **`ℓ(K) = g`**: for a nonzero differential `ω`, `ℓ(div ω)` is the genus (the dimension of the space of holomorphic
differentials). -/
@[kb "milne2017mf" "Corollary 1.21: l(K) = g, pdf p. 22"]
theorem ell_divisor_eq_genus {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) :
    ell X ω.divisor = genus X :=
  (rrSpaceEquivHolomorphicDifferentials hω).finrank_eq

end ModularFormsKB.Milne.RS
