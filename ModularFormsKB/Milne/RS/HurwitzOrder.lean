import ModularFormsKB.Milne.RiemannSurface.Results
import ModularFormsKB.Milne.RiemannSurface.Differential
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Comap
import TauCeti.Analysis.Complex.RiemannSurface.Degree
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Basic
import TauCeti.Analysis.Complex.RiemannSurface.Ramification

/-!
# Milne, Theorem 1.27: the order of the differential of a pullback

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), proof of Theorem 1.27 (Riemann–Hurwitz), pdf p. 22.

For a finite holomorphic map `f : Y → X` of compact connected Riemann surfaces and a nonconstant meromorphic
function `h` on `X`, the proof of Riemann–Hurwitz compares `d(h ∘ f)` with `dh`: locally
`ord_y d(h ∘ f) = e_y · ord_{f y} dh + (e_y - 1)`, with `e_y` the ramification index (local multiplicity) of `f` at
`y`. This file proves that formula and its divisor form
`div d(h ∘ f) = f^* div(dh) + R_f`.

* `pullbackFun`: the pullback `h ∘ f`, as a meromorphic function on `Y`.
* `ord_differential_ne_top`, `differential_not_isZero`: `dh ≠ 0` (finite order everywhere) for nonconstant `h`.
* `ord_differential_pullbackFun`: the order formula.
* `divisor_differential_pullbackFun`: the divisor form.
-/

open Filter Topology Set
open scoped Manifold OnePoint

namespace ModularFormsKB.Milne.RS

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry ModularFormsKB.Milne.RiemannSurface MeromorphicFunction

section Local

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

/-- The finite part of a meromorphic function, read in the chart at `x`, is meromorphic at `chartAt ℂ x x`. -/
theorem meromorphicAt_rep (g : MeromorphicFunction X) (x : X) :
    _root_.MeromorphicAt (g.finitePart ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
  (TauCeti.RiemannSurface.meromorphicAt_def _ _).1 (g.meromorphicAt_finitePart x)

/-- At a point where `g` is finite, the chart representative of its finite part is analytic. -/
theorem analyticAt_rep (g : MeromorphicFunction X) {x : X} (hx : g x ≠ ∞) :
    AnalyticAt ℂ (g.finitePart ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
  refine (meromorphicAt_rep g x).analyticAt ?_
  have h1 : ContinuousAt g.finitePart ((chartAt ℂ x).symm (chartAt ℂ x x)) := by
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    exact continuousAt_finitePart hx
  exact h1.comp ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))

/-- For nonconstant `h`, the differential `dh` has finite order at every point where `h` is finite. -/
theorem ord_differential_ne_top_of_ne_infty {h : MeromorphicFunction X} (hh : IsNonconstant h) {x : X}
    (hx : h x ≠ ∞) : (differential h).ord x ≠ ⊤ := by
  intro htop
  have hG := analyticAt_rep h hx
  have hord : _root_.meromorphicOrderAt (deriv (h.finitePart ∘ (chartAt ℂ x).symm)) (chartAt ℂ x x) = ⊤ :=
    htop
  rw [hG.deriv.meromorphicOrderAt_eq] at hord
  have h1 : analyticOrderAt (deriv (h.finitePart ∘ (chartAt ℂ x).symm)) (chartAt ℂ x x) = ⊤ := by
    simpa using hord
  have h2 := hG.analyticOrderAt_deriv_add_one
  rw [h1, top_add] at h2
  have h3 := analyticOrderAt_eq_top.1 h2.symm
  have hcont : ContinuousAt (chartAt ℂ x) x := (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  have hconst : ∀ᶠ y in 𝓝 x, h y = h x := by
    filter_upwards [hcont.tendsto.eventually h3, (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x),
      h.continuous.continuousAt.eventually_ne hx] with y hy1 hy2 hy3
    simp only [Function.comp, (chartAt ℂ x).left_inv hy2, (chartAt ℂ x).left_inv (mem_chart_source ℂ x),
      sub_eq_zero] at hy1
    rw [← coe_finitePart hy3, ← coe_finitePart hx, hy1]
  have hec : EventuallyConst (⇑h) (𝓝 x) :=
    Filter.eventuallyConst_iff_exists_eventuallyEq.2 ⟨h x, hconst⟩
  obtain ⟨a, b, hab⟩ := hh
  exact hab ((apply_eq_of_eventuallyConst h.mdifferentiable hec a).trans
    (apply_eq_of_eventuallyConst h.mdifferentiable hec b).symm)

variable [CompactSpace X] [T2Space X]

/-- For nonconstant `h`, the differential `dh` has finite order at every point. -/
theorem ord_differential_ne_top {h : MeromorphicFunction X} (hh : IsNonconstant h) (x : X) :
    (differential h).ord x ≠ ⊤ := by
  intro htop
  have hord : _root_.meromorphicOrderAt (deriv (h.finitePart ∘ (chartAt ℂ x).symm)) (chartAt ℂ x x) = ⊤ :=
    htop
  have h0 := _root_.meromorphicOrderAt_eq_top_iff.1 hord
  have key : ∀ᶠ w in 𝓝[≠] (chartAt ℂ x x),
      _root_.meromorphicOrderAt (deriv (h.finitePart ∘ (chartAt ℂ x).symm)) w = ⊤ := by
    have h1 := (eventually_nhdsWithin_iff.1 h0).eventually_nhds
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with y hy hya
    refine _root_.meromorphicOrderAt_eq_top_iff.2 ?_
    filter_upwards [nhdsWithin_le_nhds hy,
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hya)] with a ha hab
    exact ha hab
  have h2 := (TauCeti.tendsto_chartAt_nhdsNE x).eventually key
  have h3 : ∀ᶠ q in 𝓝[≠] x, q ∈ (chartAt ℂ x).source :=
    nhdsWithin_le_nhds ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  have : (𝓝[≠] x).NeBot := (chartAt ℂ x).nhdsNE_neBot (mem_chart_source ℂ x)
  obtain ⟨q, hq1, hq2, hq3⟩ := (h2.and (h3.and (h.eventually_ne_infty x))).exists
  refine ord_differential_ne_top_of_ne_infty hh hq3 ?_
  rw [MeromorphicDifferential.ord_eq_meromorphicOrderAt_coeff _ hq2]
  exact hq1

/-- `dh ≠ 0` for nonconstant `h`. -/
theorem differential_not_isZero {h : MeromorphicFunction X} (hh : IsNonconstant h) :
    ¬ (differential h).IsZero := by
  obtain ⟨a, _, _⟩ := id hh
  exact fun h0 ↦ ord_differential_ne_top hh a (h0 a)

end Local

section Pullback

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [ConnectedSpace X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [CompactSpace Y]
  [ConnectedSpace Y] [T2Space Y]

/-- The pullback `h ∘ f` of a meromorphic function along a finite holomorphic map. -/
noncomputable def pullbackFun (f : FiniteHolomorphicMap Y X) (h : MeromorphicFunction X) :
    MeromorphicFunction Y :=
  comap f f.holomorphic f.nonconstant h

theorem finitePart_pullbackFun (f : FiniteHolomorphicMap Y X) (h : MeromorphicFunction X) :
    (pullbackFun f h).finitePart = h.finitePart ∘ f :=
  finitePart_comap _ _ _ _

/-- The pullback of a nonconstant meromorphic function along a finite holomorphic map is nonconstant (the map is
surjective). -/
theorem isNonconstant_pullbackFun (f : FiniteHolomorphicMap Y X) {h : MeromorphicFunction X}
    (hh : IsNonconstant h) : IsNonconstant (pullbackFun f h) := by
  obtain ⟨a, b, hab⟩ := hh
  obtain ⟨y, rfl⟩ := f.surjective a
  obtain ⟨y', rfl⟩ := f.surjective b
  exact ⟨y, y', hab⟩

/-- **The order formula** (Milne, proof of Theorem 1.27, p. 22): `ord_y d(h ∘ f) = e_y · ord_{f y} dh + (e_y - 1)`,
where `e_y` is the local multiplicity of `f` at `y`. -/
theorem ord_differential_pullbackFun (f : FiniteHolomorphicMap Y X) (h : MeromorphicFunction X) (y : Y) :
    (differential (pullbackFun f h)).ord y =
      (differential h).ord (f y) * (localMultiplicity f y : WithTop ℤ) +
        ((localMultiplicity f y : ℤ) - 1 : ℤ) := by
  have hfd : ∀ᶠ v in 𝓝 y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f v := .of_forall fun v ↦ f.holomorphic v
  have hnc : ¬ EventuallyConst f (𝓝 y) := f.not_eventuallyConst y
  have hmult := natCast_localMultiplicity hfd hnc
  set φ : ℂ → ℂ := fun v ↦ chartAt ℂ (f y) (f ((chartAt ℂ y).symm v)) with hφ
  set G : ℂ → ℂ := h.finitePart ∘ (chartAt ℂ (f y)).symm with hG
  set z0 := chartAt ℂ y y with hz0
  have hφz0 : φ z0 = chartAt ℂ (f y) (f y) := by
    simp only [hφ, hz0, (chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
  have hφan : AnalyticAt ℂ φ z0 := TauCeti.analyticAt_chartAt_comp_comp_chartAt_symm hfd
  have hord : analyticOrderAt (fun z ↦ φ z - φ z0) z0 = (localMultiplicity f y : ℕ∞) := by
    rw [hφz0]; exact hmult.symm
  have hφnc : ¬ EventuallyConst φ (𝓝 z0) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hord]
    exact ENat.natCast_ne_top _
  have hGmer : _root_.MeromorphicAt G (φ z0) := by
    rw [hφz0]; exact meromorphicAt_rep h (f y)
  -- (i), (ii)
  have hi : (pullbackFun f h).finitePart ∘ (chartAt ℂ y).symm =ᶠ[𝓝 z0] G ∘ φ := by
    rw [finitePart_pullbackFun]
    exact TauCeti.comp_comp_chartAt_symm_eventuallyEq (H := ℂ) (H' := ℂ) h.finitePart
      f.holomorphic.continuous.continuousAt
  have hii := hi.deriv
  -- (iii)
  have hiii : deriv (G ∘ φ) =ᶠ[𝓝[≠] z0] (deriv G ∘ φ) * deriv φ := by
    have hne : ∀ᶠ v in 𝓝[≠] z0, φ v ≠ φ z0 := by
      rcases hφan.eventually_eq_or_eventually_ne (analyticAt_const (v := φ z0)) with h | h
      · exact absurd (Filter.eventuallyConst_iff_exists_eventuallyEq.2 ⟨_, h⟩) hφnc
      · exact h
    have htend : Tendsto φ (𝓝[≠] z0) (𝓝[≠] (φ z0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hφan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hne
    filter_upwards [htend.eventually hGmer.eventually_analyticAt,
      nhdsWithin_le_nhds hφan.eventually_analyticAt] with v h1 h2
    exact deriv_comp v h1.differentiableAt h2.differentiableAt
  -- (iv)
  have hmer1 : _root_.MeromorphicAt (deriv G ∘ φ) z0 := hGmer.deriv.comp_analyticAt hφan
  have hord1 := hGmer.deriv.meromorphicOrderAt_comp hφan hφnc
  rw [hord] at hord1
  have hord2 : _root_.meromorphicOrderAt (deriv φ) z0 = (((localMultiplicity f y : ℤ) - 1 : ℤ) : WithTop ℤ) := by
    rw [hφan.deriv.meromorphicOrderAt_eq]
    have h1 := hφan.analyticOrderAt_deriv_add_one
    rw [hord] at h1
    have hpos := localMultiplicity_pos f y
    generalize analyticOrderAt (deriv φ) z0 = m at h1 ⊢
    induction m using ENat.recTopCoe with
    | top => simp at h1
    | coe k =>
      have h2 : k + 1 = localMultiplicity f y := by exact_mod_cast h1
      have h3 : ((localMultiplicity f y : ℤ) - 1) = k := by omega
      rw [h3]; simp
  have hdh : (differential h).ord (f y) = _root_.meromorphicOrderAt (deriv G) (φ z0) := by
    rw [hφz0]; rfl
  have hmul := _root_.meromorphicOrderAt_mul hmer1 hφan.deriv.meromorphicAt
  calc (differential (pullbackFun f h)).ord y
      = _root_.meromorphicOrderAt (deriv (G ∘ φ)) z0 :=
        _root_.meromorphicOrderAt_congr (hii.filter_mono nhdsWithin_le_nhds)
    _ = _root_.meromorphicOrderAt ((deriv G ∘ φ) * deriv φ) z0 := _root_.meromorphicOrderAt_congr hiii
    _ = _ := by
        rw [hmul, hord1, hord2, hdh]
        simp

/-- The finite order of `dh` makes the divisor a function: `div(dh) x = ordZ x`. -/
theorem divisor_apply_of_not_isZero {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) (x : X) :
    ω.divisor x = ω.ordZ x := by
  simp [MeromorphicDifferential.divisor, MeromorphicDifferential.finite_support_ordZ hω]

/-- **Milne, proof of Theorem 1.27, p. 22**: `div d(h ∘ f) = f^* div(dh) + R_f`. -/
theorem divisor_differential_pullbackFun (f : FiniteHolomorphicMap Y X) {h : MeromorphicFunction X}
    (hh : IsNonconstant h) :
    (differential (pullbackFun f h)).divisor =
      divisorPullback f (differential h).divisor + ramificationDivisor f := by
  have h2 := differential_not_isZero (isNonconstant_pullbackFun f hh)
  have h1 := differential_not_isZero hh
  ext y
  change (differential (pullbackFun f h)).divisor y = _ + _
  rw [divisor_apply_of_not_isZero h2]
  have e1 : (divisorPullback f (differential h).divisor) y =
      (localMultiplicity f y : ℤ) * (differential h).divisor (f y) := rfl
  have e2 : (ramificationDivisor f) y = (localMultiplicity f y : ℤ) - 1 := rfl
  rw [e1, e2, divisor_apply_of_not_isZero h1]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (ord_differential_ne_top hh (f y))
  have ha' : (differential h).ordZ (f y) = a := by
    simp [MeromorphicDifferential.ordZ, ← ha]
  rw [ha']
  have hf := ord_differential_pullbackFun f h y
  rw [← ha] at hf
  have : (differential (pullbackFun f h)).ordZ y = a * localMultiplicity f y + ((localMultiplicity f y : ℤ) - 1) := by
    unfold MeromorphicDifferential.ordZ
    rw [hf]
    have : ((a : WithTop ℤ) * (localMultiplicity f y : WithTop ℤ) + (((localMultiplicity f y : ℤ) - 1 : ℤ) : WithTop ℤ)) =
        ((a * localMultiplicity f y + ((localMultiplicity f y : ℤ) - 1) : ℤ) : WithTop ℤ) := by
      push_cast; rfl
    rw [this]
    exact WithTop.untop₀_coe _
  rw [this]
  ring

end Pullback

end ModularFormsKB.Milne.RS
