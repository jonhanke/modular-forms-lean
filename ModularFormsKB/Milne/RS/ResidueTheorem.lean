import ModularFormsKB.Milne.RS.ResidueLocal
import ModularFormsKB.Milne.RS.NthRootResidue
import ModularFormsKB.Milne.RS.HurwitzOrder

/-!
# Milne, Proposition 1.12 (b): the residue theorem, from Theorem 1.17

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Proposition 1.12 (b), pdf p. 19.

Let `X` be a compact Riemann surface with a nonconstant meromorphic function `h` (Theorem 1.17), and `ω` a meromorphic
differential. Write `ω = g dh` (`RS.diffQuot`). The trace `Tr g (y) = ∑ g(x)` over the fibre of `h` over `y` (counted
with multiplicity) is a meromorphic function on the Riemann sphere, and at every point `y` of the sphere
`res_y (Tr g dz) = ∑_{x ∈ h⁻¹ y} res_x ω`: in normal-form charts the fibre near `y` is given by `m`-th roots
(`RS.eventually_sum_map_fiberMultiset_eq`), the residue of a sum over `m`-th roots is computed by
`RS.residue_sum_map_nthRoots`, and the residue of `g dh` at a point of the fibre by
`RS.residue_mul_differential_eq_normalForm`. Summing over `y` and using the residue theorem on the sphere
(`RS.residueTheoremStatement_sphere`) gives `∑_x res_x ω = 0`.

Main result: `residueTheoremStatement_of_existsNonconstant`.
-/

open Filter Topology Set OnePoint Polynomial
open scoped Manifold

namespace ModularFormsKB.Milne.RS

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction ModularFormsKB.Milne.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
  [CompactSpace X] [T2Space X]

section Local

variable (ω : MeromorphicDifferential X) {h : MeromorphicFunction X} (hh : IsNonconstant h)

/-- The trace of `ω / dh` along `h`. -/
noncomputable def traceFun : OnePoint ℂ → ℂ := fun y ↦
  ((fiberMultiset (⇑(toFiniteHolomorphicMap h hh)) y).map (diffQuot ω (differential h)).finitePart).sum

theorem not_eventuallyConst_toFiniteHolomorphicMap (x : X) :
    ¬ EventuallyConst (⇑(toFiniteHolomorphicMap h hh)) (𝓝 x) := by
  obtain ⟨x₁, x₂, h12⟩ := hh
  exact not_eventuallyConst_of_ne (toFiniteHolomorphicMap h ⟨x₁, x₂, h12⟩).holomorphic h12 x

include hh in
/-- The local identity at a point `y₀` of the sphere: meromorphy of the trace and the residue computation. -/
theorem local_identity (y₀ : OnePoint ℂ) :
    _root_.MeromorphicAt (traceFun ω hh ∘ (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀) ∧
      ∀ T : MeromorphicFunction (OnePoint ℂ), T.finitePart =ᶠ[𝓝[≠] y₀] traceFun ω hh →
        (smulDiff T (differential (coordinate : MeromorphicFunction (OnePoint ℂ)))).res y₀ =
          ∑ x ∈ (finite_preimage_singleton (toFiniteHolomorphicMap h hh).holomorphic
            (not_eventuallyConst_toFiniteHolomorphicMap hh) y₀).toFinset, ω.res x := by
  classical
  set β := toFiniteHolomorphicMap h hh
  have hne := not_eventuallyConst_toFiniteHolomorphicMap hh (h := h)
  set g := diffQuot ω (differential h)
  have hdh : ¬ (differential h).IsZero := differential_not_isZero hh
  set e' := chartAt ℂ y₀
  set z₀ := e' y₀
  have hz₀ : z₀ ∈ e'.target := e'.map_source (mem_chart_source ℂ y₀)
  obtain ⟨e, he, hdec⟩ := eventually_sum_map_fiberMultiset_eq β.holomorphic hne
    (chart_mem_maximalAtlas' y₀) (mem_chart_source ℂ y₀)
  set S := (finite_preimage_singleton β.holomorphic hne y₀).toFinset
  have hmem : ∀ x ∈ S, x ∈ (⇑β) ⁻¹' {y₀} := fun x hx ↦ (Set.Finite.mem_toFinset _).1 hx
  set m : X → ℕ := fun x ↦ localMultiplicity (⇑β) x
  have hm : ∀ x, 0 < m x := fun x ↦
    (localMultiplicity_pos_iff (.of_forall fun x' ↦ β.holomorphic x')).2 (hne x)
  set G : X → ℂ → ℂ := fun x ↦ g.finitePart ∘ (e x).symm
  have hG : ∀ x ∈ S, _root_.MeromorphicAt (G x) 0 := by
    intro x hx
    have h1 := (TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas (f := g.finitePart)
      (he x (hmem x hx)).1 (he x (hmem x hx)).2.1).1 (g.meromorphicAt_finitePart x)
    rwa [(he x (hmem x hx)).2.2.1] at h1
  set W : X → ℂ → ℂ := fun x s ↦ ((nthRoots (m x) s).map (G x)).sum
  have hW : ∀ x ∈ S, _root_.MeromorphicAt (W x) 0 := fun x hx ↦
    meromorphicAt_sum_map_nthRoots (hG x hx) (hm x)
  have hdec' : (fun z ↦ traceFun ω hh (e'.symm z)) =ᶠ[𝓝 z₀] fun z ↦ ∑ x ∈ S, W x (z - z₀) :=
    hdec g.finitePart
  have hsub : AnalyticAt ℂ (fun z : ℂ ↦ z - z₀) z₀ := analyticAt_id.sub analyticAt_const
  have hWz : ∀ x ∈ S, _root_.MeromorphicAt (fun z ↦ W x (z - z₀)) z₀ := by
    intro x hx
    have : _root_.MeromorphicAt (W x) ((fun z : ℂ ↦ z - z₀) z₀) := by simpa using hW x hx
    exact MeromorphicAt.comp_analyticAt (g := fun z : ℂ ↦ z - z₀) (x := z₀) this hsub
  have hsumz : _root_.MeromorphicAt (fun z ↦ ∑ x ∈ S, W x (z - z₀)) z₀ :=
    MeromorphicAt.fun_sum fun x hx ↦ hWz x hx
  refine ⟨hsumz.congr ?_, fun T hT ↦ ?_⟩
  · exact (hdec'.filter_mono nhdsWithin_le_nhds).symm
  -- the left-hand side
  have hφm : _root_.MeromorphicAt (sphereCoord y₀) z₀ := meromorphicAt_sphereCoord y₀ hz₀
  have hφ'z : _root_.MeromorphicAt (fun s ↦ deriv (sphereCoord y₀) (s + z₀)) 0 := by
    have : _root_.MeromorphicAt (deriv (sphereCoord y₀)) ((fun s : ℂ ↦ s + z₀) 0) := by
      simpa using hφm.deriv
    exact MeromorphicAt.comp_analyticAt (g := fun s : ℂ ↦ s + z₀) (x := 0) this
      (analyticAt_id.add analyticAt_const)
  have hL1 : (smulDiff T (differential (coordinate : MeromorphicFunction (OnePoint ℂ)))).res y₀ =
      TauCeti.Contour.residue (fun z ↦ (∑ x ∈ S, W x (z - z₀)) * deriv (sphereCoord y₀) z) z₀ := by
    change TauCeti.Contour.residue (fun v ↦ T.finitePart (e'.symm v) *
      deriv (coordinate.finitePart ∘ e'.symm) v) z₀ = _
    refine TauCeti.Contour.residue_congr_nhdsNE ?_
    filter_upwards [finitePart_comp_eventuallyEq (F := T) (g := traceFun ω hh) y₀ hz₀
        (by rw [e'.left_inv (mem_chart_source ℂ y₀)]; exact hT),
      hdec'.filter_mono nhdsWithin_le_nhds] with v hv hv2
    rw [hv]
    erw [hv2]
    rfl
  have hL2 : TauCeti.Contour.residue (fun z ↦ (∑ x ∈ S, W x (z - z₀)) * deriv (sphereCoord y₀) z) z₀ =
      ∑ x ∈ S, TauCeti.Contour.residue (fun s ↦ W x s * deriv (sphereCoord y₀) (s + z₀)) 0 := by
    rw [← residue_comp_add_const (f := fun z ↦ (∑ x ∈ S, W x (z - z₀)) * deriv (sphereCoord y₀) z)
      (hsumz.mul hφm.deriv)]
    simp only [add_sub_cancel_right, Finset.sum_mul]
    rw [show (fun s ↦ ∑ i ∈ S, W i s * deriv (sphereCoord y₀) (s + z₀)) =
        ∑ i ∈ S, (fun s ↦ W i s * deriv (sphereCoord y₀) (s + z₀)) from (Finset.sum_fn _ _).symm]
    exact TauCeti.Contour.residue_sum S (fun x hx ↦ (hW x hx).mul hφ'z)
  have hL3 : ∀ x ∈ S, TauCeti.Contour.residue (fun s ↦ W x s * deriv (sphereCoord y₀) (s + z₀)) 0 =
      TauCeti.Contour.residue (fun ζ ↦ g.finitePart ((e x).symm ζ) *
        (deriv (sphereCoord y₀) (ζ ^ m x + z₀) * (m x * ζ ^ (m x - 1)))) 0 := by
    intro x hx
    have hfun : (fun s ↦ W x s * deriv (sphereCoord y₀) (s + z₀)) =
        fun s ↦ ((nthRoots (m x) s).map (fun ζ ↦ G x ζ * deriv (sphereCoord y₀) (ζ ^ m x + z₀))).sum := by
      funext s
      simp only [W]
      rw [← Multiset.sum_map_mul_right]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun ζ hζ ↦ ?_)
      rw [(mem_nthRoots (hm x)).1 hζ]
    have hGt : _root_.MeromorphicAt (fun ζ ↦ G x ζ * deriv (sphereCoord y₀) (ζ ^ m x + z₀)) 0 := by
      have : _root_.MeromorphicAt (deriv (sphereCoord y₀)) ((fun ζ : ℂ ↦ ζ ^ m x + z₀) 0) := by
        simpa [zero_pow (hm x).ne'] using hφm.deriv
      exact (hG x hx).mul (MeromorphicAt.comp_analyticAt (g := fun ζ : ℂ ↦ ζ ^ m x + z₀) (x := 0) this
        ((analyticAt_id.pow _).add analyticAt_const))
    rw [hfun, residue_sum_map_nthRoots hGt (hm x)]
    congr 1
    funext ζ
    simp only [G, Function.comp_apply]
    ring
  -- the right-hand side
  have hR : ∀ x ∈ S, ω.res x = TauCeti.Contour.residue (fun ζ ↦ g.finitePart ((e x).symm ζ) *
      (deriv (sphereCoord y₀) (ζ ^ m x + z₀) * (m x * ζ ^ (m x - 1)))) 0 := by
    intro x hx
    obtain ⟨hex, hxe, hex0, hnf⟩ := he x (hmem x hx)
    have hw : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    change TauCeti.Contour.residue (ω.coeff x) (chartAt ℂ x x) = _
    rw [TauCeti.Contour.residue_congr_nhdsNE (coeff_eventuallyEq_diffQuot_mul ω hdh x hw)]
    exact residue_mul_differential_eq_normalForm g h y₀ hex hxe hex0 (hm x) hnf
  rw [hL1, hL2]
  exact Finset.sum_congr rfl fun x hx ↦ (hL3 x hx).trans (hR x hx).symm

end Local

/-- **Milne, Proposition 1.12 (b)** (the residue theorem), from Theorem 1.17: on a compact Riemann surface with a
nonconstant meromorphic function, the residues of every meromorphic differential sum to zero. -/
@[kb "milne2017mf" "Proposition 1.12 (b), pdf p. 19, from Theorem 1.17"]
theorem residueTheoremStatement_of_existsNonconstant (hN : ExistsNonconstantStatement X) :
    ResidueTheoremStatement X := by
  classical
  refine ⟨fun ω ↦ ?_⟩
  obtain ⟨h, hh⟩ := hN.out
  set β := toFiniteHolomorphicMap h hh
  have hT : ∀ y, TauCeti.RiemannSurface.MeromorphicAt (traceFun ω hh) y := fun y ↦
    (TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas' y)
      (mem_chart_source ℂ y)).2 (local_identity ω hh y).1
  set T := ofMeromorphic hT
  rw [finsum_eq_finsum_fiber ω.res (finite_support_res ω) (⇑β) β.finite_fiber]
  have : ∀ y, ∑ x ∈ (β.finite_fiber y).toFinset, ω.res x =
      (smulDiff T (differential (coordinate : MeromorphicFunction (OnePoint ℂ)))).res y := fun y ↦
    ((local_identity ω hh y).2 T (finitePart_ofMeromorphic_eventuallyEq hT y)).symm
  rw [finsum_congr this]
  exact residueTheoremStatement_sphere.out _

end ModularFormsKB.Milne.RS
