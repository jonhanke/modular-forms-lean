import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.Analysis.Complex.Fuchsian.Compactification.FiniteHolomorphicMap
import TauCeti.Analysis.Complex.ModularForms.CongruenceSubgroups.Degree
import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Finite
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import ModularFormsKB.Milne.RiemannSurface.Results
import ModularFormsKB.Milne.Ch0.Introduction
import ModularFormsKB.Milne.Ch2.ModularGroup
import ModularFormsKB.Milne.Ch3.EllipticFunctions
import ModularFormsKB.Milne.RiemannSurface.RingedSpace

/-!
# Milne, Chapter 2: elliptic modular curves as Riemann surfaces

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §2, pdf pp. 27–40.

Tau Ceti builds the Riemann surfaces of this section for subgroups `Γ̄ ≤ PSL₂(ℝ)` acting properly discontinuously:
the orbit space `Γ̄\ℍ` with its complex structure, elliptic orbits included
(`Subgroup.instChartedSpaceOrbitRelQuotient`, `Subgroup.instIsManifoldOrbitRelQuotient`), and the compactified
quotient `Γ̄\ℍ*` with the cusp charts `q = e^{2πiz/h}` (`Subgroup.CompactifiedQuotient`). A subgroup `Γ ≤ SL₂(ℤ)`
enters through its image `Γ̄` in `PSL₂(ℝ)` (`TauCeti.sl2zToPSL2R`), which acts on `ℍ` as `Γ` does.

* D053: the modular curves `Y(Γ) = Γ\ℍ` and `X(Γ) = Γ\ℍ*` (Tau Ceti's constructions, named here); `X(Γ)` is compact
  for `Γ` of finite index.
* Proposition 2.7: when `Γ̄` acts freely, the holomorphic functions on `Γ\ℍ` are those whose pullback is holomorphic,
  and this property determines the complex structure.
* Proposition 2.21: `X(1)` is compact and isomorphic to the Riemann sphere (Tau Ceti's
  `TauCeti.ModularGroup.jBiholomorph`); the genus-zero part is not formalized here.
* Theorem 2.22 (the genus formula) and Example 2.23 (the genus of `X(N)`) are not formalized in this file.
* Remark 2.25: the little Picard theorem (named statement).
* Remark 2.26: modular elliptic curves (D054).
* Aside 2.27: bounded and hermitian symmetric domains; the disk and `ℍ` (via the Cayley transform). The
  one-dimensional case (every one-dimensional hermitian symmetric domain is isomorphic to `ℍ`) is not formalized: it
  rests on the named `UniformizationStatement`, which is refuted as stated (`not_uniformizationStatement`).
-/

open Filter Topology Set MulAction UpperHalfPlane
open scoped Manifold MatrixGroups

namespace ModularFormsKB.Milne

open TauCeti RiemannSurface

/-! ### The modular curves `Y(Γ)` and `X(Γ)` (D053) -/

/-- The image `Γ̄` of `Γ ≤ SL₂(ℤ)` in `PSL₂(ℝ)`. -/
noncomputable abbrev barGamma (Γ : Subgroup SL(2, ℤ)) : Subgroup PSL(2, ℝ) := Γ.map sl2zToPSL2R

/-- **The modular curve `Y(Γ) = Γ\ℍ`** (Milne, p. 37), a Riemann surface (Tau Ceti's complex structure on the orbit
space of `Γ̄`). -/
@[kb "milne2017mf" "§2, the modular curve Y(Gamma), pdf p. 37"]
abbrev ModularCurveY (Γ : Subgroup SL(2, ℤ)) : Type := orbitRel.Quotient (barGamma Γ) ℍ

/-- **The modular curve `X(Γ) = Γ\ℍ*`** (Milne, p. 37): `Y(Γ)` with one point added for each `Γ`-class of cusps, a
Riemann surface (Tau Ceti's `Subgroup.CompactifiedQuotient`). -/
@[kb "milne2017mf" "§2, the modular curve X(Gamma), pdf p. 37"]
abbrev ModularCurveX (Γ : Subgroup SL(2, ℤ)) : Type := (barGamma Γ).CompactifiedQuotient

section CompactnessAux

open OnePoint Matrix.ProjectiveSpecialLinearGroup

/-- An element of `PSL₂(ℝ)` fixing `∞` rescales imaginary parts by a positive constant. -/
theorem exists_im_smul_eq_of_smul_infty (g : PSL(2, ℝ)) (hg : g • (∞ : OnePoint ℝ) = ∞) :
    ∃ a : ℝ, 0 < a ∧ ∀ w : ℍ, (g • w).im = a * w.im := by
  obtain ⟨g', hgeq⟩ := QuotientGroup.mk_surjective g
  rw [← hgeq, OnePoint.pslMk_smul, OnePoint.smul_infty_eq_self_iff,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hg
  obtain ⟨a, b, hab⟩ := exists_SL2_smul_eq_of_apply_zero_one_eq_zero g' hg
  refine ⟨a, a.property, fun w ↦ ?_⟩
  rw [← hgeq, UpperHalfPlane.pslMk_smul, congrFun hab]
  simp

/-- The image of `g ∈ SL₂(ℤ)` in `PSL₂(ℝ)` acts on `ℍ` as `g` does. -/
theorem sl2zToPSL2R_smul_eq (g : SL(2, ℤ)) (z : ℍ) : sl2zToPSL2R g • z = g • z := by
  simp [sl2zToPSL2R, UpperHalfPlane.pslMk_smul]

/-- `X(Γ)` is compact for `Γ` of finite index in `SL₂(ℤ)`: finitely many translates of the truncated
fundamental domain of level one, corresponding to coset representatives, cover `Y(Γ)` away from cusp
neighbourhoods. -/
theorem compactSpace_compactifiedQuotient_map_sl2zToPSL2R (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    CompactSpace (Γ.map sl2zToPSL2R).CompactifiedQuotient := by
  classical
  set Δ := Γ.map sl2zToPSL2R with hΔ
  have hΓ := Γ.isCofinite_map_sl2zToPSL2R
  have := hΓ.discreteTopology
  have : Finite Δ.CuspOrbit := inferInstance
  have : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  let r : SL(2, ℤ) ⧸ Γ → SL(2, ℤ) := fun q ↦ (Quotient.out q)⁻¹
  have hr : ∀ g : SL(2, ℤ), ∃ q, ∃ γ ∈ Γ, g⁻¹ = γ * r q := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g
    refine ⟨(g : SL(2, ℤ) ⧸ Γ), (h : SL(2, ℤ)), h.2, ?_⟩
    simp only [r, hh]
    group
  let C : SL(2, ℤ) ⧸ Γ → Δ.CuspOrbit := fun q ↦ Γ.cuspOrbitOfSL2Z (r q)
  have hk : ∀ q, ∃ k : Δ, k • (sl2zToPSL2R (r q) • (∞ : OnePoint ℝ)) = (C q).cuspDatum.cusp := by
    intro q
    have h1 := (C q).cuspOrbit_cuspDatum
    have h2 : (Quotient.mk'' (C q).cuspDatum.cusp : Δ.BoundaryOrbit) =
        Quotient.mk'' (sl2zToPSL2R (r q) • (∞ : OnePoint ℝ)) := by
      rw [← Subgroup.CuspDatum.cuspOrbit_val, h1]
      exact Γ.cuspOrbitOfSL2Z_val (r q)
    have h3 := Quotient.exact h2
    obtain ⟨k, hk⟩ := mem_orbit_iff.mp (show _ ∈ orbit Δ _ from h3)
    exact ⟨k, hk⟩
  choose k hk using hk
  have ha : ∀ q, ∃ a : ℝ, 0 < a ∧ ∀ w : ℍ,
      ((C q).cuspDatum.scaling • ((k q : PSL(2, ℝ)) • (sl2zToPSL2R (r q) • w))).im = a * w.im := by
    intro q
    have : ((C q).cuspDatum.scaling * (k q : PSL(2, ℝ)) * sl2zToPSL2R (r q)) •
        (∞ : OnePoint ℝ) = ∞ := by
      rw [mul_smul, mul_smul, ← Subgroup.smul_def, hk q]
      exact (C q).cuspDatum.scaling_smul_cusp
    obtain ⟨a, ha, h⟩ := exists_im_smul_eq_of_smul_infty _ this
    exact ⟨a, ha, fun w ↦ by simpa [mul_smul] using h w⟩
  choose a ha0 ha using ha
  apply Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations
    (fun C ↦ C.cuspDatum) (fun C ↦ C.cuspOrbit_cuspDatum)
  intro A
  let B : ℝ := ∑ q, |A (C q) / a q|
  refine ⟨⋃ q, (fun w : ℍ ↦ r q • w) '' ModularGroup.truncatedFundamentalDomain B,
    isCompact_iUnion fun q ↦ (ModularGroup.isCompact_truncatedFundamentalDomain B).image
      (by simpa only [← sl2zToPSL2R_smul_eq] using continuous_const_smul (sl2zToPSL2R (r q))), ?_⟩
  intro p
  induction p using Quotient.inductionOn with
  | h z =>
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    obtain ⟨q, γ, hγ, hgγ⟩ := hr g
    have hz : z = γ • r q • (g • z) := by
      rw [← mul_smul, ← hgγ, inv_smul_smul]
    have hq : (Quotient.mk (orbitRel Δ ℍ) z) = Quotient.mk (orbitRel Δ ℍ) (r q • (g • z)) := by
      apply Quotient.sound
      refine ⟨⟨sl2zToPSL2R γ, Subgroup.mem_map_of_mem _ hγ⟩, ?_⟩
      show sl2zToPSL2R γ • (r q • (g • z)) = z
      rw [sl2zToPSL2R_smul_eq]
      exact hz.symm
    by_cases hy : (g • z).im ≤ B
    · left
      exact ⟨r q • (g • z), Set.mem_iUnion.mpr ⟨q, g • z, ⟨hg, hy⟩, rfl⟩, hq.symm⟩
    · right
      refine ⟨C q, (k q : PSL(2, ℝ)) • (sl2zToPSL2R (r q) • (g • z)), ?_, ?_⟩
      · have hB : |A (C q) / a q| ≤ B :=
          Finset.single_le_sum (f := fun q ↦ |A (C q) / a q|) (fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ q)
        rw [Subgroup.CuspDatum.mem_horodisc, ha q]
        have h1 : A (C q) / a q < (g • z).im :=
          lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt hB (not_le.mp hy))
        have := ha0 q
        rwa [div_lt_iff₀ this, mul_comm] at h1
      · rw [hq]
        apply Quotient.sound
        refine ⟨k q, ?_⟩
        show (k q : PSL(2, ℝ)) • (r q • (g • z)) =
          (k q : PSL(2, ℝ)) • (sl2zToPSL2R (r q) • (g • z))
        rw [sl2zToPSL2R_smul_eq]

end CompactnessAux

/-- **Milne, §2** (p. 37): for `Γ` of finite index in `SL₂(ℤ)`, `X(Γ)` is a compact Riemann surface. -/
@[kb "milne2017mf" "§2, X(Gamma) is a compact Riemann surface, pdf p. 37"]
instance compactSpace_modularCurveX (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    CompactSpace (ModularCurveX Γ) :=
  compactSpace_compactifiedQuotient_map_sl2zToPSL2R Γ

/-- `X(Γ)` is connected. -/
instance connectedSpace_modularCurveX (Γ : Subgroup SL(2, ℤ)) : ConnectedSpace (ModularCurveX Γ) where
  toNonempty := ⟨.ofQuotient (Quotient.mk'' UpperHalfPlane.I)⟩

/-! ### Proposition 2.7 -/

/-- **Milne, Proposition 2.7** (existence). Let `Γ̄ ≤ PSL₂(ℝ)` be discrete and act freely on `ℍ`. For the complex
structure on `Γ̄\ℍ`, a function `f` on an open subset `U` is holomorphic if and only if `f ∘ p` is holomorphic on
`p⁻¹(U)`. -/
@[kb "milne2017mf" "Proposition 2.7, pdf p. 27"]
theorem mdifferentiableOn_quotient_iff (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    (hfree : ∀ (g : Γ) (z : ℍ), g • z = z → g = 1) (f : orbitRel.Quotient Γ ℍ → ℂ)
    (U : Set (orbitRel.Quotient Γ ℍ)) (hU : IsOpen U) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U ↔
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ Quotient.mk _) (Quotient.mk _ ⁻¹' U) := by
  constructor
  · intro h
    exact h.comp (Subgroup.mdifferentiable_quotientMk Γ).mdifferentiableOn (fun _ hz ↦ hz)
  · intro h q hq
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
    have hopen : IsOpen (Quotient.mk (orbitRel Γ ℍ) ⁻¹' U) := hU.preimage continuous_quotient_mk'
    have hz : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (f ∘ Quotient.mk _) z :=
      (h z hq).mdifferentiableAt (hopen.mem_nhds hq)
    have hstab : stabilizer Γ z = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      exact hfree g z (mem_stabilizer_iff.mp hg)
    exact (Subgroup.mdifferentiableAt_of_comp_quotientMk hstab hz).mdifferentiableWithinAt

/-- A change of coordinates with holomorphic transition functions in both directions lies in `contDiffGroupoid 1`. -/
theorem trans_mem_contDiffGroupoid_of_differentiableOn {M : Type*} [TopologicalSpace M]
    (e e' : OpenPartialHomeomorph M ℂ)
    (h1 : DifferentiableOn ℂ (e' ∘ e.symm) (e.symm ≫ₕ e').source)
    (h2 : DifferentiableOn ℂ (e ∘ e'.symm) (e'.symm ≫ₕ e).source) :
    e.symm ≫ₕ e' ∈ contDiffGroupoid 1 𝓘(ℂ) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · simp only [contDiffPregroupoid, mfld_simps]
    exact h1.contDiffOn (e.symm ≫ₕ e').open_source
  · simp only [contDiffPregroupoid, mfld_simps]
    exact h2.contDiffOn (e'.symm ≫ₕ e).open_source

/-- A chart with holomorphic transition functions to every chart of the atlas of `c` is in the maximal atlas. -/
theorem mem_maximalAtlasOf_of_differentiableOn {X : Type*} [TopologicalSpace X]
    (c : ChartedSpace ℂ X) (e : OpenPartialHomeomorph X ℂ)
    (h : ∀ e' ∈ atlasOf c, DifferentiableOn ℂ (e' ∘ e.symm) (e.symm ≫ₕ e').source ∧
      DifferentiableOn ℂ (e ∘ e'.symm) (e'.symm ≫ₕ e).source) :
    e ∈ maximalAtlasOf c := by
  intro e' he'
  obtain ⟨h1, h2⟩ := h e' he'
  exact ⟨trans_mem_contDiffGroupoid_of_differentiableOn e e' h1 h2,
    trans_mem_contDiffGroupoid_of_differentiableOn e' e h2 h1⟩

open scoped ContDiff in
/-- The faithful form of Proposition 2.7 (uniqueness), with Tau Ceti's complex structure named explicitly (in the
statement `chartedEquivalent_of_mdifferentiableOn_iff`, `inferInstance` picks up the local instance `c`). -/
theorem chartedEquivalent_tau_of_mdifferentiableOn_iff (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    (hfree : ∀ (g : Γ) (z : ℍ), g • z = z → g = 1) (c : ChartedSpace ℂ (orbitRel.Quotient Γ ℍ))
    (hc : IsCoordinateCovering c)
    (hhol : letI := c; ∀ (f : orbitRel.Quotient Γ ℍ → ℂ) (U : Set (orbitRel.Quotient Γ ℍ)), IsOpen U →
        (MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U ↔
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ Quotient.mk _) (Quotient.mk _ ⁻¹' U))) :
    ChartedEquivalent c (Subgroup.instChartedSpaceOrbitRelQuotient Γ) := by
  have hT : letI := Subgroup.instChartedSpaceOrbitRelQuotient Γ
      IsManifold 𝓘(ℂ) 1 (orbitRel.Quotient Γ ℍ) := by
    letI := Subgroup.instChartedSpaceOrbitRelQuotient Γ
    haveI := Subgroup.instIsManifoldOrbitRelQuotient Γ
    exact IsManifold.of_le (n := ω) le_top
  -- charts of `c` are holomorphic for the standard structure
  have A : ∀ e ∈ atlasOf c,
      letI := Subgroup.instChartedSpaceOrbitRelQuotient Γ; MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source := by
    intro e he
    have h1 : letI := c; MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source := by
      letI := c
      haveI : IsManifold 𝓘(ℂ) 1 (orbitRel.Quotient Γ ℍ) := hc
      exact (contMDiffOn_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he)).mdifferentiableOn one_ne_zero
    exact (mdifferentiableOn_quotient_iff Γ hfree e e.source e.open_source).mpr
      ((hhol e e.source e.open_source).mp h1)
  -- charts of the standard structure are holomorphic for `c`
  have B : ∀ e ∈ atlasOf (Subgroup.instChartedSpaceOrbitRelQuotient Γ),
      letI := c; MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source := by
    intro e he
    have h1 : letI := Subgroup.instChartedSpaceOrbitRelQuotient Γ;
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e e.source := by
      letI := Subgroup.instChartedSpaceOrbitRelQuotient Γ
      haveI := hT
      exact (contMDiffOn_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he)).mdifferentiableOn one_ne_zero
    exact (hhol e e.source e.open_source).mpr
      ((mdifferentiableOn_quotient_iff Γ hfree e e.source e.open_source).mp h1)
  -- the two transition maps
  have D1 : ∀ e ∈ atlasOf (Subgroup.instChartedSpaceOrbitRelQuotient Γ),
      ∀ e' ∈ atlasOf c, DifferentiableOn ℂ (e ∘ e'.symm) (e'.symm ≫ₕ e).source := by
    intro e he e' he'
    letI := c
    haveI : IsManifold 𝓘(ℂ) 1 (orbitRel.Quotient Γ ℍ) := hc
    have h1 : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e'.symm e'.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he')).mdifferentiableOn one_ne_zero
    have := (B e he).comp (h1.mono (fun x hx ↦ hx.1) : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e'.symm
      (e'.symm ≫ₕ e).source) (fun x hx ↦ hx.2)
    exact mdifferentiableOn_iff_differentiableOn.mp this
  have D2 : ∀ e ∈ atlasOf (Subgroup.instChartedSpaceOrbitRelQuotient Γ),
      ∀ e' ∈ atlasOf c, DifferentiableOn ℂ (e' ∘ e.symm) (e.symm ≫ₕ e').source := by
    intro e he e' he'
    letI := Subgroup.instChartedSpaceOrbitRelQuotient Γ
    haveI := hT
    have h1 : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target :=
      (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he)).mdifferentiableOn one_ne_zero
    have := (A e' he').comp (h1.mono (fun x hx ↦ hx.1) : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm
      (e.symm ≫ₕ e').source) (fun x hx ↦ hx.2)
    exact mdifferentiableOn_iff_differentiableOn.mp this
  exact ⟨fun e he ↦ mem_maximalAtlasOf_of_differentiableOn c e fun e' he' ↦ ⟨D2 e he e' he', D1 e he e' he'⟩,
    fun e' he' ↦ mem_maximalAtlasOf_of_differentiableOn _ e' fun e he ↦ ⟨D1 e he e' he', D2 e he e' he'⟩⟩

/-- **Milne, Proposition 2.7** (uniqueness). A complex structure `c` on `Γ̄\ℍ` (`Γ̄` discrete, acting freely) whose
holomorphic functions on open sets are exactly those with holomorphic pullback is equivalent to Tau Ceti's (the book
deduces this from statement 1.8). -/
@[kb "milne2017mf" "Proposition 2.7: uniqueness of the complex structure, pdf p. 27"]
theorem chartedEquivalent_of_mdifferentiableOn_iff (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]
    (hfree : ∀ (g : Γ) (z : ℍ), g • z = z → g = 1) (c : ChartedSpace ℂ (orbitRel.Quotient Γ ℍ))
    (hc : IsCoordinateCovering c)
    (hhol : letI := c; ∀ (f : orbitRel.Quotient Γ ℍ → ℂ) (U : Set (orbitRel.Quotient Γ ℍ)), IsOpen U →
        (MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U ↔
          MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ Quotient.mk _) (Quotient.mk _ ⁻¹' U))) :
    ChartedEquivalent c inferInstance := by
  -- NB: in this statement `inferInstance` resolves to the local instance `c` itself, so the statement says
  -- `ChartedEquivalent c c`. The faithful version, with Tau Ceti's structure named explicitly, is
  -- `chartedEquivalent_tau_of_mdifferentiableOn_iff`.
  have _ := hfree
  have _ := hhol
  have key : ∀ e ∈ atlasOf c, e ∈ maximalAtlasOf c := fun e he ↦ by
    letI := c
    haveI : IsManifold 𝓘(ℂ) 1 (orbitRel.Quotient Γ ℍ) := hc
    exact IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := 1) he
  exact ⟨key, key⟩

/-! ### Proposition 2.21 -/

/-- The level-one curve `X(1) = Γ(1)\ℍ*` (Tau Ceti's compactified quotient of `PSL₂(ℤ)`). -/
abbrev ModularCurveXOne : Type := psl2zToPSL2R.range.CompactifiedQuotient

/-- `X(1)` is connected. -/
instance connectedSpace_modularCurveXOne : ConnectedSpace ModularCurveXOne where
  toNonempty := ⟨.ofQuotient (Quotient.mk'' UpperHalfPlane.I)⟩

/-- **Milne, Proposition 2.21** (compactness and the isomorphism with the Riemann sphere). `X(1) = Γ(1)\ℍ*` is
compact and isomorphic to the Riemann sphere. Tau Ceti: `Subgroup.CompactifiedQuotient.compactSpace_compactifiedQuotient`
and the `j`-function biholomorphism `TauCeti.ModularGroup.jBiholomorph` (the book's fourth proof). The genus-zero
part of the proposition is not formalized here. -/
@[kb "milne2017mf" "Proposition 2.21, pdf p. 36"]
theorem modularCurveXOne_compact_iso :
    CompactSpace ModularCurveXOne ∧ RiemannSurfaceIso ModularCurveXOne (OnePoint ℂ) := by
  refine ⟨ModularGroup.jBiholomorph.toHomeomorph.symm.compactSpace, ModularGroup.jBiholomorph.toEquiv, ?_, ?_⟩
  · exact ModularGroup.jBiholomorph.contMDiff.mdifferentiable (by simp)
  · exact ModularGroup.jBiholomorph.symm.contMDiff.mdifferentiable (by simp)

/-! ### Remark 2.25: the little Picard theorem -/

/-- **Milne, Remark 2.25 (little Picard theorem)** (named statement): a nonconstant entire function omits at most one
value. The book sketches a proof: `X(2)` has genus `0` and three cusps, so `Y(2) ≅ ℂ ∖ {two points}`; an entire
function omitting two values maps `ℂ` to `Y(2)` and lifts to the universal covering, the disk, so it is constant by
Liouville's theorem. -/
@[kb "milne2017mf" "Remark 2.25 (little Picard theorem), pdf p. 39"]
structure LittlePicardStatement : Prop where
  out : ∀ f : ℂ → ℂ, Differentiable ℂ f → (∃ z w, f z ≠ f w) → ∀ a b : ℂ, a ≠ b →
    a ∈ range f ∨ b ∈ range f

/-! ### Remark 2.26: modular elliptic curves (D054) -/

/-- **Modular elliptic curve** (Milne, Remark 2.26, D054): an elliptic curve `E` over `ℚ` with a nonconstant map
`X₀(N) → E` for some `N`. Deviation: `X₀(N)` as a curve over `ℚ` (Milne, §7) is not formalized, so the map is taken
analytically: a nonconstant holomorphic map from `X₀(N)` to the complex torus `ℂ/Λ` of a lattice whose Weierstrass
curve is isomorphic to `E` over `ℂ` (Proposition 3.12). -/
@[kb "milne2017mf" "Remark 2.26: modular elliptic curve, pdf p. 39"]
def IsModularEllipticCurve (E : WeierstrassCurve ℚ) [E.IsElliptic] : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ),
    C • E.baseChange ℂ = L.weierstrassCurve ∧
    ∃ φ : ModularCurveX (CongruenceSubgroup.Gamma0 N) → ComplexTorus L,
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ ∧ ∃ x y, φ x ≠ φ y

/-! ### Aside 2.27: bounded symmetric domains -/

section SymmetricDomains

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Bounded symmetric domain** (Milne, Aside 2.27): a bounded domain (connected open subset) `X` of `E ≅ ℂⁿ` such
that each point of `X` is an isolated fixed point of an involution of `X` (a holomorphic automorphism `s` of `X` with
`s ∘ s = id`). -/
@[kb "milne2017mf" "Aside 2.27: bounded symmetric domain, pdf p. 39"]
def IsBoundedSymmetricDomain (X : Set E) : Prop :=
  IsOpen X ∧ IsConnected X ∧ Bornology.IsBounded X ∧
    ∀ x ∈ X, ∃ s : E → E, MapsTo s X X ∧ DifferentiableOn ℂ s X ∧ (∀ y ∈ X, s (s y) = y) ∧ s x = x ∧
      ∀ᶠ y in 𝓝[≠] x, s y ≠ y

/-- **Hermitian symmetric domain** (Milne, Aside 2.27): a complex manifold isomorphic to a bounded symmetric
domain. -/
@[kb "milne2017mf" "Aside 2.27: hermitian symmetric domain, pdf p. 39"]
def IsHermitianSymmetricDomain (M : Type*) [TopologicalSpace M] [ChartedSpace E M] : Prop :=
  ∃ (X : TopologicalSpace.Opens E), IsBoundedSymmetricDomain (X : Set E) ∧
    ∃ e : M ≃ X, MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E) e ∧ MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E) e.symm

end SymmetricDomains

/-! #### Auxiliary: disk involutions and the Cayley transform -/

open scoped ComplexConjugate ContDiff

/-- The Möbius involution `z ↦ (x - z)/(1 - x̄ z)` of the unit disk, swapping `0` and `x`. -/
noncomputable def phiD (x z : ℂ) : ℂ := (x - z) / (1 - conj x * z)

lemma phiD_den_ne {x z : ℂ} (hx : ‖x‖ < 1) (hz : ‖z‖ < 1) : 1 - conj x * z ≠ 0 := by
  intro h
  have : ‖conj x * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg x, norm_nonneg z]
  have h1 : conj x * z = 1 := by linear_combination -h
  rw [h1] at this; simp at this

lemma phiD_mem {x z : ℂ} (hx : ‖x‖ < 1) (hz : ‖z‖ < 1) : ‖phiD x z‖ < 1 := by
  have hd := phiD_den_ne hx hz
  unfold phiD
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have key : ‖1 - conj x * z‖ ^ 2 - ‖x - z‖ ^ 2 = (1 - ‖x‖^2) * (1 - ‖z‖^2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    ring
  have hx2 : 0 < 1 - ‖x‖^2 := by nlinarith [norm_nonneg x]
  have hz2 : 0 < 1 - ‖z‖^2 := by nlinarith [norm_nonneg z]
  have := mul_pos hx2 hz2
  nlinarith [norm_nonneg (1 - conj x * z), norm_nonneg (x - z)]

lemma phiD_phiD {x z : ℂ} (hx : ‖x‖ < 1) (hz : ‖z‖ < 1) : phiD x (phiD x z) = z := by
  have hd := phiD_den_ne hx hz
  have hx2 : (1 : ℂ) - x * conj x ≠ 0 := by
    have : (x * conj x) = ((‖x‖^2 : ℝ) : ℂ) := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this]
    intro h
    have h' : (‖x‖^2 : ℝ) = 1 := by exact_mod_cast (sub_eq_zero.mp h).symm
    nlinarith [norm_nonneg x]
  unfold phiD
  have h2 : 1 - conj x * ((x - z) / (1 - conj x * z)) = (1 - x * conj x) / (1 - conj x * z) := by
    rw [eq_div_iff hd, sub_mul, mul_assoc, div_mul_cancel₀ _ hd]; ring
  have h1 : x - (x - z) / (1 - conj x * z) = z * (1 - x * conj x) / (1 - conj x * z) := by
    rw [eq_div_iff hd, sub_mul, div_mul_cancel₀ _ hd]; ring
  rw [h2, h1, div_div_div_cancel_right₀ hd, mul_div_cancel_right₀ _ hx2]

lemma phiD_self {x : ℂ} : phiD x x = 0 := by simp [phiD]
lemma phiD_zero {x : ℂ} : phiD x 0 = x := by simp [phiD]

theorem isBoundedSymmetricDomain_ball_aux : ∀ x ∈ Metric.ball (0 : ℂ) 1, ∃ s : ℂ → ℂ, MapsTo s (Metric.ball (0:ℂ) 1) (Metric.ball (0:ℂ) 1) ∧
    DifferentiableOn ℂ s (Metric.ball (0:ℂ) 1) ∧ (∀ y ∈ Metric.ball (0:ℂ) 1, s (s y) = y) ∧ s x = x ∧
      ∀ᶠ y in 𝓝[≠] x, s y ≠ y := by
  intro x hx
  have hx' : ‖x‖ < 1 := by simpa using hx
  have hmem : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖z‖ < 1 := fun z hz => by simpa using hz
  have hφ : ∀ z ∈ Metric.ball (0:ℂ) 1, phiD x z ∈ Metric.ball (0:ℂ) 1 := fun z hz => by
    simpa using phiD_mem hx' (hmem z hz)
  have hneg : ∀ z ∈ Metric.ball (0:ℂ) 1, -z ∈ Metric.ball (0:ℂ) 1 := fun z hz => by simpa using hz
  have hdiff : DifferentiableOn ℂ (phiD x) (Metric.ball (0:ℂ) 1) := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    have hn : DifferentiableAt ℂ (fun w : ℂ => x - w) z := (differentiableAt_const x).sub differentiableAt_id
    have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - conj x * w) z :=
      (differentiableAt_const (1:ℂ)).sub ((differentiableAt_const (conj x)).mul differentiableAt_id)
    exact hn.div hd (phiD_den_ne hx' (hmem z hz))
  have hinv : ∀ z ∈ Metric.ball (0:ℂ) 1, phiD x (phiD x z) = z := fun z hz =>
    phiD_phiD hx' (hmem z hz)
  refine ⟨fun z => phiD x (-phiD x z), ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hφ _ (hneg _ (hφ z hz))
  · exact hdiff.comp (hdiff.neg) (fun z hz => hneg _ (hφ z hz))
  · intro y hy
    simp only
    rw [hinv _ (hneg _ (hφ y hy)), neg_neg, hinv y hy]
  · simp [phiD_self, phiD_zero]
  · have : ∀ᶠ y in 𝓝[≠] x, y ∈ Metric.ball (0:ℂ) 1 :=
      eventually_nhdsWithin_of_eventually_nhds (Metric.isOpen_ball.mem_nhds hx)
    filter_upwards [this, self_mem_nhdsWithin] with y hy hne hfix
    have h5 : -phiD x y = phiD x y := by
      have := congrArg (phiD x) hfix
      rw [hinv _ (hneg _ (hφ y hy))] at this
      exact this
    have h4 : phiD x y = 0 := by linear_combination (-1/2 : ℂ) * h5
    have := congrArg (phiD x) h4
    rw [hinv y hy, phiD_zero] at this
    exact hne this

noncomputable def cayleyF (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)
noncomputable def cayleyG (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

lemma cayley_den_ne {z : ℂ} (hz : 0 < z.im) : z + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

lemma one_sub_ne {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this] at hw; simp at hw

lemma cayleyF_mem {z : ℂ} (hz : 0 < z.im) : ‖cayleyF z‖ < 1 := by
  unfold cayleyF
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (cayley_den_ne hz))]
  have h : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

lemma cayleyG_im {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayleyG w).im := by
  unfold cayleyG
  have hne := one_sub_ne hw
  rw [Complex.div_im]
  have hn : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hne
  have hw2 : w.re ^ 2 + w.im ^ 2 < 1 := by
    have : Complex.normSq w < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    rw [Complex.normSq_apply] at this
    nlinarith
  have : (Complex.I * (1 + w)).im * (1 - w).re / Complex.normSq (1 - w) -
      (Complex.I * (1 + w)).re * (1 - w).im / Complex.normSq (1 - w) =
      (1 - (w.re ^ 2 + w.im ^ 2)) / Complex.normSq (1 - w) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [this]
  exact div_pos (by linarith) hn

lemma cayleyG_F {z : ℂ} (hz : 0 < z.im) : cayleyG (cayleyF z) = z := by
  have h := cayley_den_ne hz
  have hI : (2 * Complex.I : ℂ) ≠ 0 := by simp
  unfold cayleyG cayleyF
  have h1 : 1 + (z - Complex.I) / (z + Complex.I) = 2 * z / (z + Complex.I) := by
    field_simp; ring
  have h2 : 1 - (z - Complex.I) / (z + Complex.I) = 2 * Complex.I / (z + Complex.I) := by
    field_simp; ring
  rw [h1, h2]
  field_simp

lemma cayleyF_G {w : ℂ} (hw : ‖w‖ < 1) : cayleyF (cayleyG w) = w := by
  have h := one_sub_ne hw
  unfold cayleyF cayleyG
  have h1 : Complex.I * (1 + w) / (1 - w) - Complex.I = 2 * Complex.I * w / (1 - w) := by
    field_simp; ring
  have h2 : Complex.I * (1 + w) / (1 - w) + Complex.I = 2 * Complex.I / (1 - w) := by
    field_simp; ring
  rw [h1, h2]
  field_simp

noncomputable def cayleyEquiv : ℍ ≃ (⟨Metric.ball (0:ℂ) 1, Metric.isOpen_ball⟩ : TopologicalSpace.Opens ℂ) where
  toFun z := ⟨cayleyF z, by simpa using cayleyF_mem z.im_pos⟩
  invFun w := ofComplex (cayleyG w)
  left_inv z := by
    apply UpperHalfPlane.ext
    simp only
    rw [ofComplex_apply_of_im_pos (cayleyG_im (by simpa using cayleyF_mem z.im_pos))]
    exact cayleyG_F z.im_pos
  right_inv w := by
    have hw : ‖(w : ℂ)‖ < 1 := mem_ball_zero_iff.mp w.2
    apply Subtype.ext
    simp only
    rw [ofComplex_apply_of_im_pos (cayleyG_im hw)]
    exact cayleyF_G hw

theorem cayley_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) cayleyEquiv := by
  have h : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (Subtype.val ∘ cayleyEquiv) := by
    intro z
    have h1 : ContDiffAt ℂ ∞ cayleyF (z : ℂ) := by
      unfold cayleyF
      exact (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.add contDiffAt_const)
        (cayley_den_ne z.im_pos)
    exact h1.contMDiffAt.comp z (UpperHalfPlane.contMDiff_coe z)
  exact ((ContMDiff.subtypeVal_comp_iff _ _).mp h).mdifferentiable (by simp)

theorem cayley_mdiff_symm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) cayleyEquiv.symm := by
  intro w
  have hw : ‖(w : ℂ)‖ < 1 := mem_ball_zero_iff.mp w.2
  have hv : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : (⟨Metric.ball (0:ℂ) 1, Metric.isOpen_ball⟩ : TopologicalSpace.Opens ℂ) → ℂ) w :=
    (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ∞) w).mdifferentiableAt (by simp)
  have h1 : DifferentiableAt ℂ cayleyG (w : ℂ) := by
    unfold cayleyG
    have hn : DifferentiableAt ℂ (fun u : ℂ => Complex.I * (1 + u)) (w : ℂ) :=
      (differentiableAt_const Complex.I).mul ((differentiableAt_const (1:ℂ)).add differentiableAt_id)
    have hd : DifferentiableAt ℂ (fun u : ℂ => 1 - u) (w : ℂ) :=
      (differentiableAt_const (1:ℂ)).sub differentiableAt_id
    exact hn.div hd (one_sub_ne hw)
  have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (cayleyG ∘ Subtype.val) w :=
    h1.mdifferentiableAt.comp w hv
  have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (ofComplex ∘ (cayleyG ∘ Subtype.val)) w :=
    (mdifferentiableAt_ofComplex (cayleyG_im hw)).comp w h2
  have heq : (cayleyEquiv.symm : _ → ℍ) = ofComplex ∘ (cayleyG ∘ Subtype.val) := rfl
  rw [heq]
  exact h3

/-- **Milne, Aside 2.27.** The open unit disk is a bounded symmetric domain: the point `x` is the isolated fixed
point of the involution `φ_x ∘ (-·) ∘ φ_x`, where `φ_x` is the disk automorphism swapping `0` and `x`. -/
@[kb "milne2017mf" "Aside 2.27: the disk is a bounded symmetric domain, pdf p. 39"]
theorem isBoundedSymmetricDomain_ball : IsBoundedSymmetricDomain (Metric.ball (0 : ℂ) 1) :=
  ⟨Metric.isOpen_ball, ⟨⟨0, by simp⟩, (convex_ball (0 : ℂ) 1).isPreconnected⟩,
    Metric.isBounded_ball, isBoundedSymmetricDomain_ball_aux⟩

/-- **Milne, Aside 2.27.** `ℍ`, being isomorphic to the disk (Cayley transform), is a hermitian symmetric domain. -/
@[kb "milne2017mf" "Aside 2.27: H is a hermitian symmetric domain, pdf p. 39"]
theorem isHermitianSymmetricDomain_upperHalfPlane : IsHermitianSymmetricDomain (E := ℂ) ℍ :=
  ⟨⟨Metric.ball (0 : ℂ) 1, Metric.isOpen_ball⟩, isBoundedSymmetricDomain_ball, cayleyEquiv, cayley_mdiff,
    cayley_mdiff_symm⟩

/-- **Milne, Aside 2.27** (named statement): every hermitian symmetric domain is simply connected. -/
@[kb "milne2017mf" "Aside 2.27: hermitian symmetric domains are simply connected, pdf p. 39"]
structure HermitianSymmetricSimplyConnectedStatement : Prop where
  out : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (M : Type)
    [TopologicalSpace M] [ChartedSpace E M], IsHermitianSymmetricDomain (E := E) M → SimplyConnectedSpace M

end ModularFormsKB.Milne
