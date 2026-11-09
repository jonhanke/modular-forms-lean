import Mathlib
import ModularFormsKB.Citation
/-!
# Milne, Chapter 1: Riemann surfaces as ringed spaces

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1 "Riemann surfaces as ringed spaces", pdf pp. 16–17.

* `SheafOfFunctions X`: Milne's sheaf of `ℂ`-algebras of functions on `X` (conditions (a)–(c), p. 16): sets `O(U)` of
  functions `U → ℂ` closed under `±`, `·`, containing `1`, stable under restriction and gluing. Mathlib's sheaves are
  categorical (`TopCat.Sheaf`); the concrete form is the book's (the comparison with Mathlib's
  `TopCat.LocalPredicate` is not formalized).
* restriction `O|Y` to an open subset; isomorphisms of ringed spaces; standard ringed spaces `(V, O_V)`.
* Statement 1.7: the holomorphic functions of a complex structure form a sheaf of `ℂ`-algebras
  (`holomorphicSheaf`).
* Statement 1.8: two coordinate coverings are equivalent if and only if they define the same sheaf.
* Statement 1.9, "only if": a sheaf of `ℂ`-algebras that comes from a complex structure is locally isomorphic to
  standard ringed spaces (`locally_standard_of_chartedSpace`; the converse is not formalized).

A coordinate covering is a `ChartedSpace ℂ X` with `IsManifold 𝓘(ℂ) 1 X` (holomorphic transition maps); two are
equivalent when their union is again a coordinate covering, i.e. each atlas lies in the maximal atlas of the other.
The book assumes `X` connected and Hausdorff; the statements here hold without it.
-/

open Topology TopologicalSpace Set
open scoped Manifold

namespace ModularFormsKB.Milne.RiemannSurface

/-- The restriction `f|_V` of `f : U → k` to an open `V ⊆ U`. -/
def restrictFun {X k : Type*} [TopologicalSpace X] {U V : Opens X} (h : V ≤ U) (f : U → k) : V → k :=
  fun x ↦ f ⟨x, h x.2⟩

/-- **Sheaf of `ℂ`-algebras of functions** (Milne, p. 16): for each open `U`, a set `O(U)` of functions `U → ℂ` such
that (a) `f, g ∈ O(U) ⇒ f ± g, fg ∈ O(U)` and `1 ∈ O(U)` for `U ≠ ∅`; (b) `O` is stable under restriction; (c) functions
agreeing on overlaps of an open covering glue to a function in `O`. -/
@[kb "milne2017mf" "§1, sheaf of k-algebras of functions, pdf p. 16"]
structure SheafOfFunctions (X : Type*) [TopologicalSpace X] where
  /-- The functions `O(U)`. -/
  O : (U : Opens X) → Set (U → ℂ)
  add_mem : ∀ {U : Opens X} {f g : U → ℂ}, f ∈ O U → g ∈ O U → f + g ∈ O U
  sub_mem : ∀ {U : Opens X} {f g : U → ℂ}, f ∈ O U → g ∈ O U → f - g ∈ O U
  mul_mem : ∀ {U : Opens X} {f g : U → ℂ}, f ∈ O U → g ∈ O U → f * g ∈ O U
  one_mem : ∀ {U : Opens X}, (U : Set X).Nonempty → (1 : U → ℂ) ∈ O U
  restrict_mem : ∀ {U V : Opens X} (h : V ≤ U) {f : U → ℂ}, f ∈ O U → restrictFun h f ∈ O V
  glue : ∀ {ι : Type*} (U : ι → Opens X) (f : ∀ i, U i → ℂ), (∀ i, f i ∈ O (U i)) →
    (∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩) →
    ∃ g ∈ O (⨆ i, U i), ∀ i (x : U i), g ⟨x, Opens.mem_iSup.2 ⟨i, x.2⟩⟩ = f i x

namespace SheafOfFunctions

variable {X : Type*} [TopologicalSpace X]

/-- The image in `X` of an open subset `U` of an open `Y ⊆ X` (helper for `restrict`). -/
def imgOpen (Y : Opens X) (U : Opens Y) : Opens X :=
  ⟨Subtype.val '' (U : Set Y), Y.isOpenEmbedding'.isOpenMap _ U.2⟩

lemma mem_imgOpen {Y : Opens X} {U : Opens Y} {x : X} :
    x ∈ imgOpen Y U ↔ ∃ h : x ∈ Y, (⟨x, h⟩ : Y) ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

lemma imgOpen_mono {Y : Opens X} {U V : Opens Y} (h : V ≤ U) : imgOpen Y V ≤ imgOpen Y U := by
  intro x hx
  obtain ⟨h1, h2⟩ := mem_imgOpen.1 hx
  exact mem_imgOpen.2 ⟨h1, h h2⟩

lemma imgOpen_mono_iSup {Y : Opens X} {ι : Type*} (U : ι → Opens Y) :
    imgOpen Y (⨆ i, U i) ≤ ⨆ i, imgOpen Y (U i) := by
  intro x hx
  obtain ⟨h1, h2⟩ := mem_imgOpen.1 hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h2
  exact Opens.mem_iSup.2 ⟨i, mem_imgOpen.2 ⟨h1, hi⟩⟩

/-- The transport map `imgOpen Y U → U` (helper for `restrict`). -/
def toSub (Y : Opens X) (U : Opens Y) (z : imgOpen Y U) : U :=
  ⟨⟨z.1, (mem_imgOpen.1 z.2).1⟩, (mem_imgOpen.1 z.2).2⟩

/-- The restriction `O|Y` of a sheaf of functions to an open subset `Y` (Milne, p. 16): `(O|Y)(U) = O(U)` for `U`
open in `Y`. -/
@[kb "milne2017mf" "§1, restriction of a sheaf to an open subset, pdf p. 16"]
def restrict (S : SheafOfFunctions X) (Y : Opens X) : SheafOfFunctions Y := by
  exact
  { O := fun U ↦ {f | (fun z : imgOpen Y U ↦ f (toSub Y U z)) ∈ S.O (imgOpen Y U)}
    add_mem := fun hf hg ↦ S.add_mem hf hg
    sub_mem := fun hf hg ↦ S.sub_mem hf hg
    mul_mem := fun hf hg ↦ S.mul_mem hf hg
    one_mem := by
      intro U hU
      obtain ⟨y, hy⟩ := hU
      exact S.one_mem ⟨y.1, mem_imgOpen.2 ⟨y.2, hy⟩⟩
    restrict_mem := by
      intro U V h f hf
      exact S.restrict_mem (imgOpen_mono h) hf
    glue := by
      intro ι U f hf hc
      obtain ⟨g, hg, hgf⟩ := S.glue (fun i ↦ imgOpen Y (U i)) (fun i z ↦ f i (toSub Y (U i) z)) hf
        (fun i j x hi hj ↦ hc i j _ _ _)
      let g' : (⨆ i, U i : Opens Y) → ℂ := fun y ↦ g ⟨y.1.1, by
        obtain ⟨i, hi⟩ := Opens.mem_iSup.1 y.2
        exact Opens.mem_iSup.2 ⟨i, mem_imgOpen.2 ⟨y.1.2, hi⟩⟩⟩
      refine ⟨g', ?_, ?_⟩
      · have : (fun z : imgOpen Y (⨆ i, U i) ↦ g' (toSub Y _ z)) =
            restrictFun (imgOpen_mono_iSup U) g := rfl
        rw [Set.mem_ofPred_eq, this]
        exact S.restrict_mem _ hg
      · intro i x
        exact hgf i ⟨x.1.1, mem_imgOpen.2 ⟨x.1.2, x.2⟩⟩ }

/-- **Isomorphism of ringed spaces** (Milne, p. 16): a homeomorphism `φ : X ≃ₜ X'` such that for every open `U'` of
`X'`, `f ↦ f ∘ φ` is a bijection `O_{X'}(U') → O_X(φ⁻¹ U')`. -/
@[kb "milne2017mf" "§1, isomorphism of ringed spaces, pdf p. 16"]
def IsIso {X' : Type*} [TopologicalSpace X'] (S : SheafOfFunctions X) (S' : SheafOfFunctions X') (φ : X ≃ₜ X') :
    Prop :=
  ∀ (U' : Opens X') (f : U' → ℂ), f ∈ S'.O U' ↔
    (fun x : (⟨φ ⁻¹' U', U'.2.preimage φ.continuous⟩ : Opens X) ↦ f ⟨φ x, x.2⟩) ∈
      S.O ⟨φ ⁻¹' U', U'.2.preimage φ.continuous⟩

end SheafOfFunctions

/-! ### Statement 1.7 -/

set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

section HolomorphicHelpers

lemma mdiffAt_incl_iff {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {U V : Opens X} (h : V ≤ U)
    (F : U → ℂ) (x : V) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F (Set.inclusion h x) ↔
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F ∘ Set.inclusion h : V → ℂ) x :=
  (differentiableWithinAt_localInvariantProp (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))).liftPropAt_iff_comp_inclusion h F x

lemma mdiff_restrict {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {U V : Opens X} (h : V ≤ U)
    {F : U → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : V ↦ F ⟨x, h x.2⟩) := fun x ↦
  (mdiffAt_incl_iff h F x).1 (hF _)

lemma mdiff_glue {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {ι : Type*} (U : ι → Opens X)
    (f : ∀ i, U i → ℂ) (hf : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i))
    (hc : ∀ i j (x : X) (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩) :
    ∃ g : (⨆ i, U i : Opens X) → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧
      ∀ i (x : U i), g ⟨x, Opens.mem_iSup.2 ⟨i, x.2⟩⟩ = f i x := by
  classical
  have hmem : ∀ y : (⨆ i, U i : Opens X), ∃ i, (y : X) ∈ U i := fun y ↦ Opens.mem_iSup.1 y.2
  let g : (⨆ i, U i : Opens X) → ℂ := fun y ↦
    f (Classical.choose (hmem y)) ⟨y, Classical.choose_spec (hmem y)⟩
  have hg : ∀ i (x : U i), g ⟨x, Opens.mem_iSup.2 ⟨i, x.2⟩⟩ = f i x := by
    intro i x
    exact hc _ _ _ _ _
  refine ⟨g, ?_, hg⟩
  intro y
  obtain ⟨i, hi⟩ := hmem y
  have hle : U i ≤ (⨆ i, U i : Opens X) := le_iSup U i
  have : g ∘ Set.inclusion hle = f i := funext fun x ↦ hg i x
  exact (mdiffAt_incl_iff hle g ⟨y, hi⟩).2 (by rw [this]; exact hf i _)

end HolomorphicHelpers

/-- **Milne, statement 1.7.** For a coordinate covering of `X`, the functions `f : U → ℂ` holomorphic relative to it
(on open `U`, with the induced charts) form a sheaf of `ℂ`-algebras on `X`. -/
@[kb "milne2017mf" "Statement 1.7, pdf p. 17"]
def holomorphicSheaf (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] :
    SheafOfFunctions X where
  O U := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  add_mem := fun hf hg ↦ MDifferentiable.add hf hg
  sub_mem := fun hf hg ↦ MDifferentiable.sub hf hg
  mul_mem := fun hf hg ↦ MDifferentiable.mul hf hg
  one_mem := fun _ ↦ mdifferentiable_const
  restrict_mem := by
    intro U V h f hf
    exact mdiff_restrict h hf
  glue := by
    intro ι U f hf hc
    obtain ⟨g, hg, hgf⟩ := mdiff_glue U f hf hc
    exact ⟨g, hg, hgf⟩

/-- The standard ringed space `(V, O_V)` of an open subset `V ⊆ ℂ` (Milne, p. 16): `O_V(U)` is the set of
holomorphic functions on `U`. -/
@[kb "milne2017mf" "§1, standard ringed space, pdf p. 16"]
noncomputable def standardSheaf (V : Opens ℂ) : SheafOfFunctions V := holomorphicSheaf V

/-! ### Statements 1.8 and 1.9 -/

/-- The maximal atlas of a coordinate covering `c` (all charts holomorphically compatible with it). -/
noncomputable def maximalAtlasOf {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) :
    Set (OpenPartialHomeomorph X ℂ) :=
  letI := c; IsManifold.maximalAtlas 𝓘(ℂ) 1 X

/-- The atlas of a coordinate covering `c`. -/
noncomputable def atlasOf {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) : Set (OpenPartialHomeomorph X ℂ) :=
  letI := c; atlas ℂ X

/-- `c` is a coordinate covering in Milne's sense: its transition maps are holomorphic. -/
def IsCoordinateCovering {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) : Prop :=
  letI := c; IsManifold 𝓘(ℂ) 1 X

/-- The sheaf of holomorphic functions of a coordinate covering given explicitly. -/
noncomputable def holomorphicSheafOf {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X)
    (h : IsCoordinateCovering c) : SheafOfFunctions X :=
  letI := c; haveI : IsManifold 𝓘(ℂ) 1 X := h; holomorphicSheaf X

/-- Two coordinate coverings `c₁`, `c₂` of `X` are **equivalent** (Milne, p. 15) when their union is a coordinate
covering: every chart of each is holomorphically compatible with the other. -/
@[kb "milne2017mf" "§1, equivalent coordinate coverings, pdf p. 15"]
def ChartedEquivalent {X : Type*} [TopologicalSpace X] (c₁ c₂ : ChartedSpace ℂ X) : Prop :=
  atlasOf c₂ ⊆ maximalAtlasOf c₁ ∧ atlasOf c₁ ⊆ maximalAtlasOf c₂

/-! #### Helpers: differentiability with explicitly given charted structures -/

/-- Differentiability at a point, with the charted structures given explicitly. -/
def MDiffAtWith {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] (cM : ChartedSpace ℂ M)
    (cN : ChartedSpace ℂ N) (g : M → N) (x : M) : Prop :=
  letI := cM; letI := cN; MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g x

/-- Differentiability, with the charted structures given explicitly. -/
def MDiffWith {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] (cM : ChartedSpace ℂ M)
    (cN : ChartedSpace ℂ N) (g : M → N) : Prop := ∀ x, MDiffAtWith cM cN g x

lemma MDiffAtWith.comp {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    {cM : ChartedSpace ℂ M} {cN : ChartedSpace ℂ N} {cP : ChartedSpace ℂ P} {g : N → P} {f : M → N}
    {x : M} (hg : MDiffAtWith cN cP g (f x)) (hf : MDiffAtWith cM cN f x) :
    MDiffAtWith cM cP (g ∘ f) x := by
  unfold MDiffAtWith at *
  letI := cM; letI := cN; letI := cP
  exact MDifferentiableAt.comp x hg hf

lemma MDiffWith.comp {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    {cM : ChartedSpace ℂ M} {cN : ChartedSpace ℂ N} {cP : ChartedSpace ℂ P} {g : N → P} {f : M → N}
    (hg : MDiffWith cN cP g) (hf : MDiffWith cM cN f) : MDiffWith cM cP (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

/-- Chart characterization of differentiability. -/
lemma mdiffAtWith_iff {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] {cM : ChartedSpace ℂ M}
    {cN : ChartedSpace ℂ N} {g : M → N} {x : M} {e : OpenPartialHomeomorph M ℂ}
    {e' : OpenPartialHomeomorph N ℂ} (he : e ∈ maximalAtlasOf cM) (he' : e' ∈ maximalAtlasOf cN)
    (hx : x ∈ e.source) (hy : g x ∈ e'.source) :
    MDiffAtWith cM cN g x ↔ ContinuousAt g x ∧ DifferentiableAt ℂ (e' ∘ g ∘ e.symm) (e x) := by
  unfold MDiffAtWith
  letI := cM; letI := cN
  rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' hx hy,
    continuousWithinAt_univ]
  simp [OpenPartialHomeomorph.extend, differentiableWithinAt_univ]

/-- The charted structure on an open subset. -/
noncomputable def openCS {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) (U : Opens X) :
    ChartedSpace ℂ U :=
  letI := c; inferInstance

/-- The standard charted structure on `ℂ`. -/
noncomputable def selfCS : ChartedSpace ℂ ℂ := chartedSpaceSelf ℂ

lemma val_comp_iff {X N : Type*} [TopologicalSpace X] [TopologicalSpace N] (c : ChartedSpace ℂ X)
    (cN : ChartedSpace ℂ N) (U : Opens X) (F : X → N) (x : U) :
    MDiffAtWith c cN F x.1 ↔ MDiffAtWith (openCS c U) cN (F ∘ Subtype.val) x := by
  unfold MDiffAtWith openCS
  letI := c; letI := cN
  exact (differentiableWithinAt_localInvariantProp (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))).liftPropAt_iff_comp_subtype_val F x

lemma comp_val_iff {M X : Type*} [TopologicalSpace M] [TopologicalSpace X] (cM : ChartedSpace ℂ M)
    (c : ChartedSpace ℂ X) (U : Opens X) (j : M → U) (x : M) :
    MDiffAtWith cM (openCS c U) j x ↔ MDiffAtWith cM c (Subtype.val ∘ j) x := by
  unfold MDiffAtWith openCS
  letI := cM; letI := c
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (P := DifferentiableWithinAtProp 𝓘(ℂ) 𝓘(ℂ))
    j univ x).symm

lemma val_mdiff {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) (U : Opens X) :
    MDiffWith (openCS c U) c (Subtype.val : U → X) := by
  intro x
  have : MDiffAtWith c c (id : X → X) x.1 := by
    unfold MDiffAtWith
    letI := c
    exact mdifferentiableAt_id
  exact (val_comp_iff c c U id x).1 this

/-- The holomorphic functions on an open `U` for the coordinate covering `c`. -/
def HolOn {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) (U : Opens X) (f : U → ℂ) : Prop :=
  MDiffWith (openCS c U) selfCS f

lemma mdiffWith_id {X : Type*} [TopologicalSpace X] (c₁ c₂ : ChartedSpace ℂ X)
    (h₁ : IsCoordinateCovering c₁) (hsub : atlasOf c₁ ⊆ maximalAtlasOf c₂) :
    MDiffWith c₂ c₁ (id : X → X) := by
  intro x
  have h1 : (letI := c₁; chartAt ℂ x) ∈ atlasOf c₁ := by
    unfold atlasOf; letI := c₁; exact chart_mem_atlas ℂ x
  have h2 : (letI := c₁; chartAt ℂ x) ∈ maximalAtlasOf c₁ := by
    unfold maximalAtlasOf; letI := c₁; haveI : IsManifold 𝓘(ℂ) 1 X := h₁
    exact IsManifold.chart_mem_maximalAtlas x
  have h3 : x ∈ (letI := c₁; chartAt ℂ x).source := by
    letI := c₁; exact mem_chart_source ℂ x
  rw [mdiffAtWith_iff (hsub h1) h2 h3 h3]
  refine ⟨continuousAt_id, ?_⟩
  set e := (letI := c₁; chartAt ℂ x)
  have : (e ∘ id ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source h3)] with y hy
    exact e.right_inv hy
  exact differentiableAt_id.congr_of_eventuallyEq this

lemma holOn_of_subset {X : Type*} [TopologicalSpace X] (c₁ c₂ : ChartedSpace ℂ X)
    (h₁ : IsCoordinateCovering c₁) (hsub : atlasOf c₁ ⊆ maximalAtlasOf c₂) {U : Opens X} {f : U → ℂ}
    (hf : HolOn c₁ U f) : HolOn c₂ U f := by
  have hj : MDiffWith (openCS c₂ U) (openCS c₁ U) (id : U → U) := by
    intro x
    have := ((mdiffWith_id c₁ c₂ h₁ hsub).comp (val_mdiff c₂ U)) x
    exact (comp_val_iff _ _ _ _ x).2 this
  exact hf.comp hj

/-- A chart as a holomorphic function on its source. -/
lemma holOn_chart {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) (h : IsCoordinateCovering c)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlasOf c) :
    HolOn c ⟨e.source, e.open_source⟩ (fun x ↦ e x.1) := by
  intro x
  have : MDiffAtWith c selfCS e x.1 := by
    unfold MDiffAtWith selfCS atlasOf at *
    letI := c; haveI : IsManifold 𝓘(ℂ) 1 X := h
    exact mdifferentiableAt_atlas he x.2
  exact (val_comp_iff c selfCS _ e x).1 this

lemma chart_diff {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X)
    {e a : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlasOf c)
    (ha : HolOn c ⟨a.source, a.open_source⟩ (fun x ↦ a x.1)) :
    DifferentiableOn ℂ (a ∘ e.symm) (e.symm ≫ₕ a).source := by
  intro y hy
  have hy' : y ∈ e.target ∧ e.symm y ∈ a.source := by simpa using hy
  have hx : e.symm y ∈ e.source := e.map_target hy'.1
  have h1 : MDiffAtWith c selfCS a (e.symm y) := (val_comp_iff c selfCS _ a ⟨e.symm y, hy'.2⟩).2 (ha _)
  have hid : (OpenPartialHomeomorph.refl ℂ) ∈ maximalAtlasOf selfCS := by
    unfold maximalAtlasOf selfCS
    letI := chartedSpaceSelf ℂ
    have := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (M := ℂ) (0 : ℂ)
    simpa using this
  have := (mdiffAtWith_iff he hid hx
    (by simp : a (e.symm y) ∈ (OpenPartialHomeomorph.refl ℂ).source)).1 h1
  have h2 := this.2
  simp only [OpenPartialHomeomorph.refl_apply, Function.id_comp, e.right_inv hy'.1] at h2
  exact h2.differentiableWithinAt

lemma mem_cdg {X : Type*} [TopologicalSpace X] (e1 e2 : OpenPartialHomeomorph X ℂ)
    (h1 : DifferentiableOn ℂ (e2 ∘ e1.symm) (e1.symm ≫ₕ e2).source)
    (h2 : DifferentiableOn ℂ (e1 ∘ e2.symm) (e2.symm ≫ₕ e1).source) :
    e1.symm ≫ₕ e2 ∈ contDiffGroupoid 1 𝓘(ℂ) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  have hs : (e1.symm ≫ₕ e2).symm = e2.symm ≫ₕ e1 := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, preimage_id_eq, range_id, inter_univ]
  refine ⟨h1.contDiffOn (OpenPartialHomeomorph.open_source _), ?_⟩
  rw [hs]
  exact h2.contDiffOn (OpenPartialHomeomorph.open_source _)

lemma atlas_sub_of_hol {X : Type*} [TopologicalSpace X] (c₁ c₂ : ChartedSpace ℂ X)
    (h₁ : IsCoordinateCovering c₁) (h₂ : IsCoordinateCovering c₂)
    (hO : ∀ (U : Opens X) (f : U → ℂ), HolOn c₁ U f ↔ HolOn c₂ U f) :
    atlasOf c₂ ⊆ maximalAtlasOf c₁ := by
  intro e' he'
  have hm₂ : e' ∈ maximalAtlasOf c₂ := by
    unfold maximalAtlasOf; letI := c₂; haveI : IsManifold 𝓘(ℂ) 1 X := h₂
    exact IsManifold.subset_maximalAtlas he'
  unfold maximalAtlasOf
  letI := c₁
  intro e'' he''
  have hm₁ : e'' ∈ maximalAtlasOf c₁ := by
    unfold maximalAtlasOf; haveI : IsManifold 𝓘(ℂ) 1 X := h₁
    exact IsManifold.subset_maximalAtlas he''
  have he''a : e'' ∈ atlasOf c₁ := he''
  have hc₁ := holOn_chart c₁ h₁ he''a
  have hc₂ := holOn_chart c₂ h₂ he'
  have d1 : DifferentiableOn ℂ (e'' ∘ e'.symm) (e'.symm ≫ₕ e'').source :=
    chart_diff c₂ hm₂ ((hO _ _).1 hc₁)
  have d2 : DifferentiableOn ℂ (e' ∘ e''.symm) (e''.symm ≫ₕ e').source :=
    chart_diff c₁ hm₁ ((hO _ _).2 hc₂)
  exact ⟨mem_cdg e' e'' d1 d2, mem_cdg e'' e' d2 d1⟩

/-- **Milne, statement 1.8.** Two coordinate coverings of `X` are equivalent if and only if they define the same
sheaves of holomorphic functions. -/
@[kb "milne2017mf" "Statement 1.8, pdf p. 17"]
theorem chartedEquivalent_iff_holomorphicSheaf_eq {X : Type*} [TopologicalSpace X] (c₁ c₂ : ChartedSpace ℂ X)
    (h₁ : IsCoordinateCovering c₁) (h₂ : IsCoordinateCovering c₂) :
    ChartedEquivalent c₁ c₂ ↔ ∀ U : Opens X, (holomorphicSheafOf c₁ h₁).O U = (holomorphicSheafOf c₂ h₂).O U := by
  constructor
  · rintro ⟨hs2, hs1⟩ U
    ext f
    exact ⟨fun hf ↦ holOn_of_subset c₁ c₂ h₁ hs1 (U := U) hf,
      fun hf ↦ holOn_of_subset c₂ c₁ h₂ hs2 (U := U) hf⟩
  · intro h
    have hO : ∀ (U : Opens X) (f : U → ℂ), HolOn c₁ U f ↔ HolOn c₂ U f := fun U f ↦ by
      have := congrArg (f ∈ ·) (h U)
      exact Iff.of_eq this
    exact ⟨atlas_sub_of_hol c₁ c₂ h₁ h₂ hO, atlas_sub_of_hol c₂ c₁ h₂ h₁ fun U f ↦ (hO U f).symm⟩

/-! #### Helpers for statement 1.9, direction (→) -/

/-- The chart `e` as a homeomorphism between its source and its target (viewed as opens). -/
noncomputable def chartHomeo {X : Type*} [TopologicalSpace X] (e : OpenPartialHomeomorph X ℂ) :
    (⟨e.source, e.open_source⟩ : Opens X) ≃ₜ (⟨e.target, e.open_target⟩ : Opens ℂ) :=
  e.toHomeomorphSourceTarget

lemma chartHomeo_apply {X : Type*} [TopologicalSpace X] (e : OpenPartialHomeomorph X ℂ)
    (x : (⟨e.source, e.open_source⟩ : Opens X)) : ((chartHomeo e x : (⟨e.target, e.open_target⟩ : Opens ℂ)) : ℂ) = e x.1 :=
  rfl

lemma chart_iso_aux {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) (h : IsCoordinateCovering c)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlasOf c)
    (U' : Opens (⟨e.target, e.open_target⟩ : Opens ℂ)) (f : U' → ℂ) :
    HolOn (openCS selfCS (⟨e.target, e.open_target⟩ : Opens ℂ)) U' f ↔
      HolOn c (SheafOfFunctions.imgOpen (⟨e.source, e.open_source⟩ : Opens X)
        ⟨chartHomeo e ⁻¹' U', U'.2.preimage (chartHomeo e).continuous⟩)
        (fun z ↦ f ⟨chartHomeo e (SheafOfFunctions.toSub _ _ z),
          (SheafOfFunctions.toSub _ _ z).2⟩) := by
  let V : Opens ℂ := ⟨e.target, e.open_target⟩
  let U : Opens X := ⟨e.source, e.open_source⟩
  let φ := chartHomeo e
  let W : Opens U := ⟨φ ⁻¹' U', U'.2.preimage φ.continuous⟩
  let N : Opens X := SheafOfFunctions.imgOpen U W
  let ψ : N → U' := fun z ↦ ⟨φ (SheafOfFunctions.toSub _ _ z), (SheafOfFunctions.toSub _ _ z).2⟩
  have hmem : ∀ z : N, z.1 ∈ e.source := fun z ↦ (SheafOfFunctions.mem_imgOpen.1 z.2).1
  have hψ : MDiffWith (openCS c N) (openCS (openCS selfCS V) U') ψ := by
    intro z
    refine (comp_val_iff _ _ U' ψ z).2 ?_
    refine (comp_val_iff _ selfCS V (Subtype.val ∘ ψ) z).2 ?_
    have : MDiffAtWith c selfCS e z.1 := by
      unfold MDiffAtWith selfCS atlasOf at *
      letI := c; haveI : IsManifold 𝓘(ℂ) 1 X := h
      exact mdifferentiableAt_atlas he (hmem z)
    exact (val_comp_iff c selfCS N e z).1 this
  have hρmem : ∀ y : U', e.symm y.1.1 ∈ N := by
    intro y
    refine SheafOfFunctions.mem_imgOpen.2 ⟨e.map_target y.1.2, ?_⟩
    have : φ ⟨e.symm y.1.1, e.map_target y.1.2⟩ = y.1 := Subtype.ext (e.right_inv y.1.2)
    show φ _ ∈ U'
    rw [this]
    exact y.2
  let ρ : U' → N := fun y ↦ ⟨e.symm y.1.1, hρmem y⟩
  have hρ : MDiffWith (openCS (openCS selfCS V) U') (openCS c N) ρ := by
    intro y
    refine (comp_val_iff _ _ N ρ y).2 ?_
    have h1 : MDiffAtWith selfCS c e.symm y.1.1 := by
      unfold MDiffAtWith selfCS atlasOf at *
      letI := c; haveI : IsManifold 𝓘(ℂ) 1 X := h
      exact mdifferentiableAt_atlas_symm he y.1.2
    have h2 := ((val_mdiff selfCS V).comp (val_mdiff (openCS selfCS V) U')) y
    exact MDiffAtWith.comp (g := e.symm) (f := Subtype.val ∘ Subtype.val) h1 h2
  have hfeq' : ∀ g : U' → ℂ, (g ∘ ψ) ∘ ρ = g := by
    intro g
    funext y
    exact congrArg g (Subtype.ext (Subtype.ext (e.right_inv y.1.2)))
  constructor
  · intro hf
    exact hf.comp hψ
  · intro hf
    have h3 : MDiffWith (openCS (openCS selfCS V) U') selfCS ((f ∘ ψ) ∘ ρ) :=
      MDiffWith.comp (show MDiffWith (openCS c N) selfCS (f ∘ ψ) from hf) hρ
    rwa [hfeq'] at h3

/-- **Milne, statement 1.9** ("only if"). A sheaf `O` of `ℂ`-algebras on `X` that arises from a complex structure
satisfies (∗): there is an open covering `X = ⋃ Uᵢ` such that every ringed space `(Uᵢ, O|Uᵢ)` is isomorphic to a
standard ringed space. The converse ("if") is not formalized. -/
@[kb "milne2017mf" "Statement 1.9 (only if), pdf p. 17"]
theorem locally_standard_of_chartedSpace {X : Type*} [TopologicalSpace X] (S : SheafOfFunctions X)
    (c : ChartedSpace ℂ X) (h : IsCoordinateCovering c)
    (hS : ∀ U : Opens X, S.O U = (holomorphicSheafOf c h).O U) :
    ∀ x : X, ∃ (U : Opens X) (V : Opens ℂ) (φ : U ≃ₜ V), x ∈ U ∧ (S.restrict U).IsIso (standardSheaf V) φ := by
  intro x
  have he : (letI := c; chartAt ℂ x) ∈ atlasOf c := by
    unfold atlasOf; letI := c; exact chart_mem_atlas ℂ x
  have hx : x ∈ (letI := c; chartAt ℂ x).source := by
    letI := c; exact mem_chart_source ℂ x
  refine ⟨⟨(letI := c; chartAt ℂ x).source, OpenPartialHomeomorph.open_source _⟩,
    ⟨(letI := c; chartAt ℂ x).target, OpenPartialHomeomorph.open_target _⟩,
    chartHomeo (letI := c; chartAt ℂ x), hx, ?_⟩
  intro U' f
  refine Iff.trans (chart_iso_aux c h he U' f) ?_
  show _ ↔ (_ ∈ S.O (SheafOfFunctions.imgOpen _ _))
  rw [hS]
  exact Iff.rfl

end ModularFormsKB.Milne.RiemannSurface
