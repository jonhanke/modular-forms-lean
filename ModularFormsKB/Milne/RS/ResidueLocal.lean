import ModularFormsKB.Milne.RS.DifferentialQuotient
import ModularFormsKB.Milne.RS.ResidueGlue
import ModularFormsKB.Milne.RS.FiberDecomposition
import ModularFormsKB.Milne.RS.ResidueSphere

/-!
# Residues of `g dh` in normal-form charts

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Proposition 1.12 (b), pdf p. 19.

Let `h` be a nonconstant meromorphic function on a compact Riemann surface `X`, `y₀` a point of the Riemann sphere,
`e'` the chart at `y₀` and `φ = z ∘ e'⁻¹` the coordinate of the sphere read in that chart. At a point `x` of the fibre
of `y₀`, in a normal-form chart `E` (`E x = 0`, `e'(h x') - e'(y₀) = E(x')^m`), the residue of `g dh` at `x` is the
residue at `0` of `g(E⁻¹ ζ) φ'(ζ^m + e' y₀) m ζ^{m-1}` (`residue_mul_differential_eq_normalForm`): the change of
variables for residues (`RS.residue_comp_mul_deriv_of_deriv_ne_zero`) moves the residue from the chart at `x` to `E`.
-/

open Filter Topology Set OnePoint
open scoped Manifold

namespace ModularFormsKB.Milne.RS

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction ModularFormsKB.Milne.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
  [CompactSpace X] [T2Space X]

/-- The coordinate of the sphere read in the chart at `y₀`. -/
noncomputable def sphereCoord (y₀ : OnePoint ℂ) : ℂ → ℂ :=
  (coordinate : MeromorphicFunction (OnePoint ℂ)).finitePart ∘ (chartAt ℂ y₀).symm

theorem meromorphicAt_sphereCoord (y₀ : OnePoint ℂ) {z : ℂ} (hz : z ∈ (chartAt ℂ y₀).target) :
    _root_.MeromorphicAt (sphereCoord y₀) z :=
  meromorphicAt_comp_chart_symm (fun p ↦ coordinate.meromorphicAt_finitePart p) y₀ hz

theorem finitePart_eq_coordinate (h : MeromorphicFunction X) (x : X) :
    h.finitePart x = (coordinate : MeromorphicFunction (OnePoint ℂ)).finitePart (h x) := by
  simp only [finitePart_def, coordinate_apply]

/-- **The residue of `g dh` in a normal-form chart.** -/
theorem residue_mul_differential_eq_normalForm (g h : MeromorphicFunction X) (y₀ : OnePoint ℂ)
    {x : X} {E : OpenPartialHomeomorph X ℂ} (hE : E ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) (hxE : x ∈ E.source)
    (hEx : E x = 0) {m : ℕ} (hm : 0 < m)
    (hnf : ∀ x' ∈ E.source, h x' ∈ (chartAt ℂ y₀).source ∧
      chartAt ℂ y₀ (h x') - chartAt ℂ y₀ y₀ = E x' ^ m) :
    TauCeti.Contour.residue (fun v ↦ g.finitePart ((chartAt ℂ x).symm v) * (differential h).coeff x v)
        (chartAt ℂ x x) =
      TauCeti.Contour.residue (fun ζ ↦ g.finitePart (E.symm ζ) *
        (deriv (sphereCoord y₀) (ζ ^ m + chartAt ℂ y₀ y₀) * (m * ζ ^ (m - 1)))) 0 := by
  set e' := chartAt ℂ y₀
  set z₀ := e' y₀
  set c := chartAt ℂ x
  set τ : ℂ → ℂ := E ∘ c.symm
  set Φ : ℂ → ℂ := fun ζ ↦ sphereCoord y₀ (ζ ^ m + z₀)
  have hcx := mem_chart_source ℂ x
  have hτan : AnalyticAt ℂ τ (c x) := TauCeti.analyticAt_symm_trans (chart_mem_maximalAtlas' x) hE hcx hxE
  have hτ0 : τ (c x) = 0 := by simp [τ, c, c.left_inv hcx, hEx]
  have hτ' : deriv τ (c x) ≠ 0 :=
    TauCeti.deriv_symm_trans_ne_zero (chart_mem_maximalAtlas' x) hE hcx hxE
  -- near `c x`, the chart inverse at `x` factors through `E` and `τ`
  have hnear : ∀ᶠ v in 𝓝 (c x), c.symm v ∈ E.source ∧ E.symm (τ v) = c.symm v := by
    have h1 : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
      have := (c.continuousAt_symm (c.map_source hcx)).tendsto
      rwa [c.left_inv hcx] at this
    filter_upwards [h1.eventually (E.open_source.mem_nhds hxE)] with v hv
    exact ⟨hv, E.left_inv hv⟩
  -- `z₀` is in the target, and `φ` is meromorphic there
  have hz₀ : z₀ ∈ e'.target := e'.map_source (mem_chart_source ℂ y₀)
  have hφm : _root_.MeromorphicAt (sphereCoord y₀) z₀ := meromorphicAt_sphereCoord y₀ hz₀
  -- `h ∘ E⁻¹` read in the chart at `y₀` is `ζ ↦ φ(ζ^m + z₀)`
  have hHΦ : (fun v ↦ h.finitePart (c.symm v)) =ᶠ[𝓝 (c x)] fun v ↦ Φ (τ v) := by
    filter_upwards [hnear] with v hv
    obtain ⟨hs, hv2⟩ := hnf _ hv.1
    have hτv : τ v = E (c.symm v) := rfl
    simp only [Φ, sphereCoord, Function.comp_apply, hτv]
    rw [← hv2, sub_add_cancel, e'.left_inv hs, finitePart_eq_coordinate]
  -- `τ` does not vanish on a punctured neighbourhood of `c x`
  have hτne : ∀ᶠ v in 𝓝[≠] (c x), τ v ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (c.open_target.mem_nhds (c.map_source hcx)),
      nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with v hvt hv hvne h0
    apply hvne
    have h1 : E (c.symm v) = E x := by rw [hEx]; exact h0
    have h2 := E.injOn hv.1 hxE h1
    rw [← c.right_inv hvt, h2]
    exact Set.mem_singleton _
  have hu : Tendsto (fun v ↦ τ v ^ m + z₀) (𝓝[≠] (c x)) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : ContinuousAt (fun v ↦ τ v ^ m + z₀) (c x) :=
        ContinuousAt.add (ContinuousAt.pow hτan.continuousAt m) continuousAt_const
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {c x}ᶜ))
      simp only [hτ0, zero_pow hm.ne', zero_add] at this
      exact this
    · filter_upwards [hτne] with v hv
      simpa using pow_ne_zero m hv
  have hΦan : ∀ᶠ v in 𝓝[≠] (c x), AnalyticAt ℂ (sphereCoord y₀) (τ v ^ m + z₀) :=
    hu.eventually hφm.eventually_analyticAt
  have hderiv : ∀ᶠ v in 𝓝[≠] (c x), (differential h).coeff x v =
      (deriv (sphereCoord y₀) (τ v ^ m + z₀) * (m * τ v ^ (m - 1))) * deriv τ v := by
    have hd : deriv (fun v ↦ h.finitePart (c.symm v)) =ᶠ[𝓝 (c x)] deriv (fun v ↦ Φ (τ v)) :=
      Filter.EventuallyEq.deriv hHΦ
    filter_upwards [nhdsWithin_le_nhds hd, hΦan, nhdsWithin_le_nhds hτan.eventually_analyticAt]
      with v hv1 hv2 hv3
    change deriv (fun v ↦ h.finitePart (c.symm v)) v = _
    have hpow : HasDerivAt (fun ζ : ℂ ↦ ζ ^ m + z₀) (m * τ v ^ (m - 1)) (τ v) := by
      simpa using (hasDerivAt_pow m (τ v)).add_const z₀
    have hΦd : HasDerivAt Φ (deriv (sphereCoord y₀) (τ v ^ m + z₀) * (m * τ v ^ (m - 1))) (τ v) :=
      HasDerivAt.comp_of_eq (h₂ := sphereCoord y₀) (h := fun ζ : ℂ ↦ ζ ^ m + z₀) (τ v)
        hv2.differentiableAt.hasDerivAt hpow rfl
    rw [hv1]
    exact (hΦd.comp v hv3.differentiableAt.hasDerivAt).deriv
  -- the integrand, written as a pull-back along `τ`
  set F : ℂ → ℂ := fun ζ ↦ g.finitePart (E.symm ζ) *
    (deriv (sphereCoord y₀) (ζ ^ m + z₀) * (m * ζ ^ (m - 1)))
  have hF : _root_.MeromorphicAt F (τ (c x)) := by
    rw [hτ0]
    have hg := (TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas (f := g.finitePart) hE hxE).1
      (g.meromorphicAt_finitePart x)
    rw [hEx] at hg
    have hpan : AnalyticAt ℂ (fun ζ : ℂ ↦ ζ ^ m + z₀) 0 := (analyticAt_id.pow m).add analyticAt_const
    have h2 : _root_.MeromorphicAt (fun ζ : ℂ ↦ deriv (sphereCoord y₀) (ζ ^ m + z₀)) 0 := by
      have this' : _root_.MeromorphicAt (deriv (sphereCoord y₀)) ((fun ζ : ℂ ↦ ζ ^ m + z₀) 0) := by
        simpa [zero_pow hm.ne'] using hφm.deriv
      exact MeromorphicAt.comp_analyticAt (g := fun ζ : ℂ ↦ ζ ^ m + z₀) (x := 0) this' hpan
    exact hg.mul (h2.mul ((analyticAt_const.mul (analyticAt_id.pow _)).meromorphicAt))
  have hcongr : (fun v ↦ g.finitePart (c.symm v) * (differential h).coeff x v) =ᶠ[𝓝[≠] (c x)]
      fun v ↦ F (τ v) * deriv τ v := by
    filter_upwards [hderiv, nhdsWithin_le_nhds hnear] with v hv hv2
    simp only [F, hv, hv2.2]
    ring
  rw [TauCeti.Contour.residue_congr_nhdsNE hcongr, residue_comp_mul_deriv_of_deriv_ne_zero hF hτan hτ', hτ0]

end ModularFormsKB.Milne.RS
