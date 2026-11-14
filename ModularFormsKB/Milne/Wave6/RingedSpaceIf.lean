import ModularFormsKB.Milne.RiemannSurface.RingedSpace

/-!
# Milne, statement 1.9: the converse

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), §1, statement 1.9, pdf p. 17.

A sheaf `O` of `ℂ`-algebras of functions on `X` arises from a complex structure if and only if (∗) every point has an
open neighbourhood `U` with `(U, O|U)` isomorphic to a standard ringed space `(V, O_V)`, `V ⊆ ℂ` open. The direction
"only if" is `RiemannSurface.locally_standard_of_chartedSpace`; here the direction "if"
(`exists_coordinateCovering_of_locally_standard`): the isomorphisms `U ≅ V` are the charts of a coordinate covering
(their transition maps are holomorphic because the coordinate `z` on `V` is a section of `O_V`), and its sheaf of
holomorphic functions is `O` (both are sheaves, and they agree on each `U`, where both are isomorphic to `O_V`).

Universes: `SheafOfFunctions` quantifies its gluing axiom over index types of a separate universe; the statements
here take it in the universe of `X` (`SheafOfFunctions.{u, u} X`), so that coverings of `X` indexed by its points can
be glued, as the book's sheaf axiom (c) allows.
-/

open Topology TopologicalSpace Set
open scoped Manifold

universe u w

namespace ModularFormsKB.Milne.Wave6

open RiemannSurface

/-- Two sheaves isomorphic to the same sheaf via the same homeomorphism have the same sections. -/
lemma iso_unique {Y T : Type*} [TopologicalSpace Y] [TopologicalSpace T]
    (R R' : SheafOfFunctions Y) (RT : SheafOfFunctions T) (φ : Y ≃ₜ T)
    (h : R.IsIso RT φ) (h' : R'.IsIso RT φ) (W : Opens Y) : R.O W = R'.O W := by
  obtain ⟨U', rfl⟩ : ∃ U' : Opens T, (⟨φ ⁻¹' U', U'.2.preimage φ.continuous⟩ : Opens Y) = W :=
    ⟨⟨φ.symm ⁻¹' W, W.2.preimage φ.symm.continuous⟩, Opens.ext (by ext y; simp)⟩
  ext f'
  let g : U' → ℂ := fun t ↦ f' ⟨φ.symm t, by
    show φ (φ.symm t.1) ∈ U'
    rw [φ.apply_symm_apply]; exact t.2⟩
  have hg : (fun x : (⟨φ ⁻¹' U', U'.2.preimage φ.continuous⟩ : Opens Y) ↦ g ⟨φ x, x.2⟩) = f' := by
    funext x
    exact congrArg f' (Subtype.ext (φ.symm_apply_apply x.1))
  have h1 := h U' g
  have h2 := h' U' g
  rw [hg] at h1 h2
  exact h1.symm.trans h2

/-- One-sided locality: sections of `S` that are locally sections of `S'` are sections of `S'`. -/
lemma locality_le {X : Type u} [TopologicalSpace X] (S S' : SheafOfFunctions.{u, u} X)
    (hloc : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∀ (W : Opens U) (f : W → ℂ),
      f ∈ (S.restrict U).O W → f ∈ (S'.restrict U).O W)
    (W : Opens X) (f : W → ℂ) (hf : f ∈ S.O W) : f ∈ S'.O W := by
  choose U hxU hU using hloc
  let W' : ∀ y : X, Opens (U y) := fun y ↦
    ⟨Subtype.val ⁻¹' (W : Set X), W.2.preimage continuous_subtype_val⟩
  let M : W → Opens X := fun y ↦ SheafOfFunctions.imgOpen (U y.1) (W' y.1)
  have hM : ∀ y : W, M y ≤ W := by
    intro y z hz
    exact (SheafOfFunctions.mem_imgOpen.1 hz).2
  let g : ∀ y : W, W' y.1 → ℂ := fun y w ↦ f ⟨w.1.1, w.2⟩
  have hmem : ∀ y : W, (fun z : M y ↦ g y (SheafOfFunctions.toSub (U y.1) (W' y.1) z)) ∈ S'.O (M y) := by
    intro y
    have h1 : restrictFun (hM y) f ∈ S.O (M y) := S.restrict_mem (hM y) hf
    exact hU y.1 (W' y.1) (g y) h1
  obtain ⟨g', hg', hgf⟩ := S'.glue M (fun y z ↦ g y (SheafOfFunctions.toSub (U y.1) (W' y.1) z)) hmem
    (fun i j x hi hj ↦ rfl)
  have hle : W ≤ ⨆ i, M i := fun x hx ↦
    Opens.mem_iSup.2 ⟨⟨x, hx⟩, SheafOfFunctions.mem_imgOpen.2 ⟨hxU x, hx⟩⟩
  have e : restrictFun hle g' = f := funext fun x ↦
    hgf ⟨x.1, x.2⟩ ⟨x.1, SheafOfFunctions.mem_imgOpen.2 ⟨hxU _, x.2⟩⟩
  rw [← e]
  exact S'.restrict_mem hle hg'

open Classical

/-- The chart with source `U`, target `V`, equal to `φ` on `U`. -/
noncomputable def mkChart {X : Type u} [TopologicalSpace X] (x : X) (U : Opens X) (V : Opens ℂ) (φ : U ≃ₜ V)
    (hx : x ∈ U) : OpenPartialHomeomorph X ℂ where
  toFun y := if h : y ∈ U then ((φ ⟨y, h⟩ : V) : ℂ) else 0
  invFun z := if h : z ∈ V then ((φ.symm ⟨z, h⟩ : U) : X) else x
  source := U
  target := V
  map_source' := by
    intro y hy
    have hy' : y ∈ U := hy
    show (if h : y ∈ U then ((φ ⟨y, h⟩ : V) : ℂ) else 0) ∈ (V : Set ℂ)
    rw [dif_pos hy']
    exact (φ ⟨y, hy'⟩).2
  map_target' := by
    intro z hz
    have hz' : z ∈ V := hz
    show (if h : z ∈ V then ((φ.symm ⟨z, h⟩ : U) : X) else x) ∈ (U : Set X)
    rw [dif_pos hz']
    exact (φ.symm ⟨z, hz'⟩).2
  left_inv' := by
    intro y hy
    have hy' : y ∈ U := hy
    show (if h : (if h : y ∈ U then ((φ ⟨y, h⟩ : V) : ℂ) else 0) ∈ V then
      ((φ.symm ⟨_, h⟩ : U) : X) else x) = y
    rw [dif_pos hy']
    rw [dif_pos (φ ⟨y, hy'⟩).2]
    exact congrArg Subtype.val (φ.symm_apply_apply ⟨y, hy'⟩)
  right_inv' := by
    intro z hz
    have hz' : z ∈ V := hz
    show (if h : (if h : z ∈ V then ((φ.symm ⟨z, h⟩ : U) : X) else x) ∈ U then
      ((φ ⟨_, h⟩ : V) : ℂ) else 0) = z
    rw [dif_pos hz']
    rw [dif_pos (φ.symm ⟨z, hz'⟩).2]
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨z, hz'⟩)
  open_source := U.2
  open_target := V.2
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (U : Set X).domRestrict (fun y ↦ if h : y ∈ U then ((φ ⟨y, h⟩ : V) : ℂ) else 0) =
        fun y ↦ ((φ y : V) : ℂ) := by
      funext y
      simp [Set.domRestrict]
    rw [this]
    exact continuous_subtype_val.comp φ.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (V : Set ℂ).domRestrict (fun z ↦ if h : z ∈ V then ((φ.symm ⟨z, h⟩ : U) : X) else x) =
        fun z ↦ ((φ.symm z : U) : X) := by
      funext z
      simp [Set.domRestrict]
    rw [this]
    exact continuous_subtype_val.comp φ.symm.continuous

lemma mkChart_apply {X : Type u} [TopologicalSpace X] (x : X) (U : Opens X) (V : Opens ℂ) (φ : U ≃ₜ V)
    (hx : x ∈ U) (y : X) (hy : y ∈ U) : mkChart x U V φ hx y = ((φ ⟨y, hy⟩ : V) : ℂ) :=
  dif_pos hy

lemma mkChart_symm_apply {X : Type u} [TopologicalSpace X] (x : X) (U : Opens X) (V : Opens ℂ) (φ : U ≃ₜ V)
    (hx : x ∈ U) (z : ℂ) (hz : z ∈ V) : (mkChart x U V φ hx).symm z = ((φ.symm ⟨z, hz⟩ : U) : X) :=
  dif_pos hz

/-- `chartHomeo` of `mkChart` is the given homeomorphism. -/
lemma chartHomeo_mkChart {X : Type u} [TopologicalSpace X] (x : X) (U : Opens X) (V : Opens ℂ) (φ : U ≃ₜ V)
    (hx : x ∈ U) : chartHomeo (mkChart x U V φ hx) = φ :=
  Homeomorph.ext fun y ↦ Subtype.ext (by
    rw [chartHomeo_apply]
    exact mkChart_apply x U V φ hx y.1 y.2)

/-- The coordinate `φ` is a section of `S` over every open `N ≤ U` when `(U, S|U) ≅ (V, O_V)`. -/
lemma coord_mem {X : Type u} [TopologicalSpace X] (S : SheafOfFunctions.{u, u} X) {U : Opens X} {V : Opens ℂ}
    (φ : U ≃ₜ V) (hi : (S.restrict U).IsIso (standardSheaf.{w} V) φ) (N : Opens X) (hN : N ≤ U) :
    (fun z : N ↦ ((φ ⟨z.1, hN z.2⟩ : V) : ℂ)) ∈ S.O N := by
  have hf : HolOn (openCS selfCS V) ⊤ (fun t ↦ (t.1 : ℂ)) :=
    MDiffWith.comp (val_mdiff selfCS V) (val_mdiff (openCS selfCS V) ⊤)
  have h1 := (hi ⊤ (fun t ↦ (t.1 : ℂ))).1 hf
  have hle : N ≤ SheafOfFunctions.imgOpen U ⟨φ ⁻¹' ((⊤ : Opens V) : Set V),
      (⊤ : Opens V).2.preimage φ.continuous⟩ :=
    fun z hz ↦ SheafOfFunctions.mem_imgOpen.2 ⟨hN hz, by simp⟩
  exact S.restrict_mem hle h1

/-- Holomorphy on an open subset of the standard ringed space gives complex differentiability. -/
lemma diff_of_hol (V : Opens ℂ) (U' : Opens V) (G : ℂ → ℂ)
    (hg : (fun t : U' ↦ G t.1.1) ∈ (standardSheaf.{w} V).O U') (t : U') : DifferentiableAt ℂ G t.1.1 := by
  have h1 : MDiffAtWith (openCS (openCS selfCS V) U') selfCS (fun t : U' ↦ G t.1.1) t := hg t
  have h2 := (val_comp_iff (openCS selfCS V) selfCS U' (G ∘ Subtype.val) t).2 h1
  have h3 := (val_comp_iff selfCS selfCS V G t.1).2 h2
  unfold MDiffAtWith selfCS at h3
  exact mdifferentiableAt_iff_differentiableAt.1 h3

/-- The transition map between two charts `mkChart` is differentiable. -/
lemma trans_diff {X : Type u} [TopologicalSpace X] (S : SheafOfFunctions.{u, u} X) {x₁ x₂ : X}
    {U₁ U₂ : Opens X} {V₁ V₂ : Opens ℂ} (φ₁ : U₁ ≃ₜ V₁) (φ₂ : U₂ ≃ₜ V₂) (hx₁ : x₁ ∈ U₁) (hx₂ : x₂ ∈ U₂)
    (hi₁ : (S.restrict U₁).IsIso (standardSheaf.{w} V₁) φ₁) (hi₂ : (S.restrict U₂).IsIso (standardSheaf.{w} V₂) φ₂) :
    DifferentiableOn ℂ (mkChart x₂ U₂ V₂ φ₂ hx₂ ∘ (mkChart x₁ U₁ V₁ φ₁ hx₁).symm)
      ((mkChart x₁ U₁ V₁ φ₁ hx₁).symm ≫ₕ mkChart x₂ U₂ V₂ φ₂ hx₂).source := by
  let G : ℂ → ℂ := mkChart x₂ U₂ V₂ φ₂ hx₂ ∘ (mkChart x₁ U₁ V₁ φ₁ hx₁).symm
  let U' : Opens V₁ := ⟨{t | (φ₁.symm t).1 ∈ U₂},
    U₂.2.preimage (continuous_subtype_val.comp φ₁.symm.continuous)⟩
  let g : U' → ℂ := fun t ↦ G t.1.1
  let P : Opens U₁ := ⟨φ₁ ⁻¹' U', U'.2.preimage φ₁.continuous⟩
  let N₁ : Opens X := SheafOfFunctions.imgOpen U₁ P
  have hN₁ : N₁ ≤ U₂ := by
    intro z hz
    obtain ⟨h1, h2⟩ := SheafOfFunctions.mem_imgOpen.1 hz
    have h3 : (φ₁.symm (φ₁ ⟨z, h1⟩)).1 ∈ U₂ := h2
    rwa [φ₁.symm_apply_apply] at h3
  have hs := coord_mem S φ₂ hi₂ N₁ hN₁
  have hg : g ∈ (standardSheaf.{w} V₁).O U' := by
    rw [hi₁ U' g]
    have : (fun z : N₁ ↦ g ⟨φ₁ (SheafOfFunctions.toSub U₁ P z), (SheafOfFunctions.toSub U₁ P z).2⟩) =
        fun z ↦ ((φ₂ ⟨z.1, hN₁ z.2⟩ : V₂) : ℂ) := by
      funext z
      have hz1 : z.1 ∈ U₁ := (SheafOfFunctions.mem_imgOpen.1 z.2).1
      show mkChart x₂ U₂ V₂ φ₂ hx₂ ((mkChart x₁ U₁ V₁ φ₁ hx₁).symm ((φ₁ ⟨z.1, hz1⟩ : V₁) : ℂ)) = _
      rw [mkChart_symm_apply x₁ U₁ V₁ φ₁ hx₁ _ (φ₁ ⟨z.1, hz1⟩).2]
      simp only [Subtype.coe_eta, Homeomorph.symm_apply_apply]
      exact mkChart_apply x₂ U₂ V₂ φ₂ hx₂ z.1 (hN₁ z.2)
    show (fun z : N₁ ↦ g ⟨φ₁ (SheafOfFunctions.toSub U₁ P z), (SheafOfFunctions.toSub U₁ P z).2⟩) ∈ S.O N₁
    rw [this]
    exact hs
  intro z hz
  have hzV : z ∈ V₁ := hz.1
  have hzU : (mkChart x₁ U₁ V₁ φ₁ hx₁).symm z ∈ U₂ := hz.2
  rw [mkChart_symm_apply x₁ U₁ V₁ φ₁ hx₁ z hzV] at hzU
  exact (diff_of_hol.{w} V₁ U' G hg ⟨⟨z, hzV⟩, hzU⟩).differentiableWithinAt

/-- A chart in the atlas of a coordinate covering is an isomorphism of ringed spaces onto its target. -/
lemma hol_iso {X : Type u} [TopologicalSpace X] (c : ChartedSpace ℂ X) (h : IsCoordinateCovering c)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlasOf c) :
    ((holomorphicSheafOf.{u, u} c h).restrict ⟨e.source, e.open_source⟩).IsIso
      (standardSheaf.{w} ⟨e.target, e.open_target⟩) (chartHomeo e) := by
  intro U' f
  exact chart_iso_aux c h he U' f

/-- **Milne, statement 1.9** ("if"). If a sheaf `O` of `ℂ`-algebras of functions on `X` satisfies (∗) (every point
has an open neighbourhood `U` with `(U, O|U)` isomorphic to a standard ringed space), then `O` arises from a complex
structure: there is a coordinate covering of `X` whose sheaf of holomorphic functions is `O`. -/
@[kb "milne2017mf" "Statement 1.9 (if), pdf p. 17"]
theorem exists_coordinateCovering_of_locally_standard {X : Type u} [TopologicalSpace X]
    (S : SheafOfFunctions.{u, u} X)
    (hS : ∀ x : X, ∃ (U : Opens X) (V : Opens ℂ) (φ : U ≃ₜ V), x ∈ U ∧ (S.restrict U).IsIso (standardSheaf V) φ) :
    ∃ (c : ChartedSpace ℂ X) (h : IsCoordinateCovering c),
      ∀ U : Opens X, S.O U = (holomorphicSheafOf.{u, u} c h).O U := by
  choose U V φ hxU hiso using hS
  let e : X → OpenPartialHomeomorph X ℂ := fun x ↦ mkChart x (U x) (V x) (φ x) (hxU x)
  let c : ChartedSpace ℂ X :=
    { atlas := Set.range e
      chartAt := e
      mem_chart_source := fun x ↦ hxU x
      chart_mem_atlas := fun x ↦ ⟨x, rfl⟩ }
  have hc : IsCoordinateCovering c := by
    unfold IsCoordinateCovering
    let _ := c
    refine { compatible := ?_ }
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact mem_cdg _ _ (trans_diff S (φ a) (φ b) (hxU a) (hxU b) (hiso a) (hiso b))
      (trans_diff S (φ b) (φ a) (hxU b) (hxU a) (hiso b) (hiso a))
  have hhol : ∀ x, ((holomorphicSheafOf.{u, u} c hc).restrict (U x)).IsIso (standardSheaf (V x)) (φ x) := by
    intro x
    have h1 := hol_iso c hc (e := e x) ⟨x, rfl⟩
    have h2 : chartHomeo (e x) = φ x := chartHomeo_mkChart x (U x) (V x) (φ x) (hxU x)
    rw [h2] at h1
    exact h1
  have hl : ∀ x, ∃ U₀ : Opens X, x ∈ U₀ ∧ ∀ W : Opens U₀,
      (S.restrict U₀).O W = ((holomorphicSheafOf.{u, u} c hc).restrict U₀).O W :=
    fun x ↦ ⟨U x, hxU x, iso_unique _ _ _ (φ x) (hiso x) (hhol x)⟩
  refine ⟨c, hc, fun W ↦ Set.ext fun f ↦ ⟨?_, ?_⟩⟩
  · exact locality_le S _ (fun x ↦ by
      obtain ⟨U₀, h1, h2⟩ := hl x
      exact ⟨U₀, h1, fun W f hf ↦ by rw [← h2 W]; exact hf⟩) W f
  · exact locality_le _ S (fun x ↦ by
      obtain ⟨U₀, h1, h2⟩ := hl x
      exact ⟨U₀, h1, fun W f hf ↦ by rw [h2 W]; exact hf⟩) W f

/-- **Milne, statement 1.9**, both directions: a sheaf `O` of `ℂ`-algebras of functions on `X` arises from a complex
structure (a coordinate covering whose holomorphic functions are `O`) if and only if every point has an open
neighbourhood `U` with `(U, O|U)` isomorphic to a standard ringed space. -/
@[kb "milne2017mf" "Statement 1.9, pdf p. 17"]
theorem statement_1_9 {X : Type u} [TopologicalSpace X] (S : SheafOfFunctions.{u, u} X) :
    (∃ (c : ChartedSpace ℂ X) (h : IsCoordinateCovering c),
        ∀ U : Opens X, S.O U = (holomorphicSheafOf.{u, u} c h).O U) ↔
      ∀ x : X, ∃ (U : Opens X) (V : Opens ℂ) (φ : U ≃ₜ V), x ∈ U ∧ (S.restrict U).IsIso (standardSheaf V) φ :=
  ⟨fun ⟨c, h, hc⟩ ↦ locally_standard_of_chartedSpace.{u, u, u, u} S c h hc, exists_coordinateCovering_of_locally_standard S⟩

end ModularFormsKB.Milne.Wave6
