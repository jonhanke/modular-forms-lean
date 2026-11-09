import ModularFormsKB.Milne.RS.CanonicalGenus

/-!
# The quotient of two meromorphic differentials

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, pdf p. 18: "if `ω₀` is a nonzero differential
form, every other is of the form `f ω₀` with `f` meromorphic".

For meromorphic differentials `η` and `ω` on a connected compact Riemann surface with `ω ≠ 0`, `diffQuot η ω` is the
meromorphic function `η / ω`: in every chart, `η_x = (η/ω ∘ z_x⁻¹) · ω_x` on punctured neighbourhoods
(`coeff_eventuallyEq_diffQuot_mul`). The construction is that of `RS.quotMero` (for holomorphic `η`), with the
transformation rule of `η` holding on punctured neighbourhoods only.
-/

open Filter Topology Set
open scoped Manifold

namespace ModularFormsKB.Milne.RS

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction ModularFormsKB.Milne.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
  [CompactSpace X] [T2Space X]

/-- The quotient `η_x / ω_x` of coefficients of two differentials in the chart at `x`. -/
noncomputable def dquotCoeff (η ω : MeromorphicDifferential X) (x : X) : ℂ → ℂ :=
  fun v ↦ η.coeff x v / ω.coeff x v

theorem meromorphicAt_dquotCoeff (η ω : MeromorphicDifferential X) (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) : _root_.MeromorphicAt (dquotCoeff η ω x) w :=
  (η.meromorphicAt x w hw).div (ω.meromorphicAt x w hw)

theorem dquotCoeff_compat (η ω : MeromorphicDifferential X) (x y : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target)
    (hy : (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source) :
    dquotCoeff η ω x =ᶠ[𝓝[≠] w] fun v ↦ dquotCoeff η ω y (transition x y v) := by
  have hT' : ∀ᶠ v in 𝓝 w, deriv (transition x y) v ≠ 0 :=
    (analyticAt_transition x y hw hy).deriv.continuousAt.eventually_ne (deriv_transition_ne_zero x y hw hy)
  filter_upwards [ω.compat x y w hw hy, η.compat x y w hw hy, nhdsWithin_le_nhds hT'] with v hv hv' hv3
  simp only [dquotCoeff, hv, hv']
  exact mul_div_mul_right _ _ hv3

/-- The values of `η / ω`: the normal form of the quotient of coefficients at the chart centre. -/
noncomputable def dquotFun (η ω : MeromorphicDifferential X) (p : X) : ℂ :=
  toMeromorphicNFAt (dquotCoeff η ω p) (chartAt ℂ p p) (chartAt ℂ p p)

theorem dquotFun_comp_eventuallyEq (η ω : MeromorphicDifferential X) (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) :
    (fun v ↦ dquotFun η ω ((chartAt ℂ x).symm v)) =ᶠ[𝓝[≠] w] dquotCoeff η ω x := by
  filter_upwards [(meromorphicAt_dquotCoeff η ω x hw).eventually_analyticAt,
    nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds hw)] with v hQ hv
  set p := (chartAt ℂ x).symm v
  have hpx : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hv
  have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hzp : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hzs : (chartAt ℂ p).symm (chartAt ℂ p p) ∈ (chartAt ℂ x).source := by rw [hzp]; exact hpx
  have hTz : transition p x (chartAt ℂ p p) = v := by
    simp only [transition, hzp, p, (chartAt ℂ x).right_inv hv]
  have hcomp := dquotCoeff_compat η ω p x hz hzs
  have han : AnalyticAt ℂ (fun u ↦ dquotCoeff η ω x (transition p x u)) (chartAt ℂ p p) := by
    refine AnalyticAt.comp (g := dquotCoeff η ω x) (f := transition p x) ?_ (analyticAt_transition p x hz hzs)
    rw [hTz]; exact hQ
  have h1 := (toMeromorphicNFAt_eventuallyEq_nhds_congr hcomp).eq_of_nhds
  rw [toMeromorphicNFAt_eq_self.2 han.meromorphicNFAt] at h1
  change toMeromorphicNFAt (dquotCoeff η ω p) (chartAt ℂ p p) (chartAt ℂ p p) = _
  rw [h1]
  exact congrArg (dquotCoeff η ω x) hTz

theorem meromorphicAt_dquotFun (η ω : MeromorphicDifferential X) (p : X) :
    TauCeti.RiemannSurface.MeromorphicAt (dquotFun η ω) p := by
  have hz : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  rw [TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas' p)
    (mem_chart_source ℂ p)]
  exact (meromorphicAt_dquotCoeff η ω p hz).congr (dquotFun_comp_eventuallyEq η ω p hz).symm

/-- **The meromorphic function `η / ω`.** -/
@[kb "milne2017mf" "§1, every differential form is f ω₀, pdf p. 18"]
noncomputable def diffQuot (η ω : MeromorphicDifferential X) : MeromorphicFunction X :=
  ofMeromorphic (meromorphicAt_dquotFun η ω)

theorem diffQuot_comp_eventuallyEq (η ω : MeromorphicDifferential X) (x : X) {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target) :
    (fun v ↦ (diffQuot η ω).finitePart ((chartAt ℂ x).symm v)) =ᶠ[𝓝[≠] w] dquotCoeff η ω x :=
  (finitePart_comp_eventuallyEq x hw (finitePart_ofMeromorphic_eventuallyEq _ _)).trans
    (dquotFun_comp_eventuallyEq η ω x hw)

/-- `η = (η / ω) ω` in every chart, on punctured neighbourhoods. -/
theorem coeff_eventuallyEq_diffQuot_mul (η : MeromorphicDifferential X) {ω : MeromorphicDifferential X}
    (hω : ¬ ω.IsZero) (x : X) {w : ℂ} (hw : w ∈ (chartAt ℂ x).target) :
    η.coeff x =ᶠ[𝓝[≠] w] fun v ↦ (diffQuot η ω).finitePart ((chartAt ℂ x).symm v) * ω.coeff x v := by
  filter_upwards [diffQuot_comp_eventuallyEq η ω x hw, eventually_coeff_ne_zero hω x hw] with v h1 h2
  rw [h1, dquotCoeff, div_mul_cancel₀ _ h2]

end ModularFormsKB.Milne.RS
