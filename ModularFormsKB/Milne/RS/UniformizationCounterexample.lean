import ModularFormsKB.Milne.Ch0.Introduction

/-!
# Milne, Theorem 0.1: the named statement is false without the Hausdorff axiom

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 0.1 (uniformization), pdf p. 5.

The named statement `ModularFormsKB.Milne.UniformizationStatement` quantifies over all types `X` with
`[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]` that are simply connected, but it does not require `X` to be Hausdorff
(Milne's Riemann surfaces are Hausdorff, p. 15). The statement is therefore false:

* `DoubledPlane`: two copies of `ℂ` glued along the open right half-plane `{Re z > 0}` (the quotient of `Bool × ℂ`).
  The second coordinate is a global function `DoubledPlane.proj`, and the two inclusions `z ↦ [b, z]` are inverse
  charts, so the transition maps are identities and `DoubledPlane` is a complex manifold.
* It is contractible (the straight-line homotopy to `1` respects the gluing because the right half-plane is convex
  and contains `1`), hence simply connected.
* The points `[true, 0]` and `[false, 0]` cannot be separated, so it is not Hausdorff and is not isomorphic to the
  Riemann sphere, to `ℂ` or to the disk (`not_uniformizationStatement`).

The corrected statement, with `[T2Space X]`, is `UniformizationStatementT2` (recorded as a named statement: the
uniformization theorem itself is not available in Mathlib or Tau Ceti).
-/

open Set Topology Filter
open scoped Manifold

namespace ModularFormsKB.Milne.RS

/-- The gluing relation on `Bool × ℂ`: `(b, z) ~ (c, w)` iff `z = w` and (`b = c` or `Re w > 0`). -/
def gluingRel (p q : Bool × ℂ) : Prop := p.2 = q.2 ∧ (p.1 = q.1 ∨ 0 < q.2.re)

/-- The gluing relation is an equivalence relation. -/
def gluingSetoid : Setoid (Bool × ℂ) where
  r := gluingRel
  iseqv := by
    refine ⟨fun p ↦ ⟨rfl, Or.inl rfl⟩, ?_, ?_⟩
    · rintro p q ⟨h1, h2⟩
      refine ⟨h1.symm, ?_⟩
      rcases h2 with h2 | h2
      · exact Or.inl h2.symm
      · exact Or.inr (h1 ▸ h2)
    · rintro p q r ⟨h1, h2⟩ ⟨h3, h4⟩
      refine ⟨h1.trans h3, ?_⟩
      rcases h4 with h4 | h4
      · rcases h2 with h2 | h2
        · exact Or.inl (h2.trans h4)
        · exact Or.inr (h3 ▸ h2)
      · exact Or.inr h4

/-- **The plane doubled along the right half-plane**: two copies of `ℂ` glued along `{Re z > 0}`. -/
def DoubledPlane : Type := Quotient gluingSetoid

namespace DoubledPlane

instance : TopologicalSpace DoubledPlane := inferInstanceAs (TopologicalSpace (Quotient gluingSetoid))

/-- The point `z` of the copy `b`. -/
def mk (b : Bool) (z : ℂ) : DoubledPlane := Quotient.mk gluingSetoid (b, z)

/-- The global coordinate `[b, z] ↦ z`. -/
def proj : DoubledPlane → ℂ := Quotient.lift Prod.snd fun _ _ h ↦ h.1

@[simp] theorem proj_mk (b : Bool) (z : ℂ) : proj (mk b z) = z := rfl

theorem mk_eq_mk {b c : Bool} {z w : ℂ} : mk b z = mk c w ↔ z = w ∧ (b = c ∨ 0 < w.re) :=
  Quotient.eq (r := gluingSetoid)

theorem mk_surjective (x : DoubledPlane) : ∃ b z, mk b z = x := by
  induction x using Quotient.inductionOn with
  | h p => exact ⟨p.1, p.2, rfl⟩

theorem continuous_proj : Continuous proj :=
  continuous_quot_lift _ continuous_snd

theorem continuous_mk (b : Bool) : Continuous (mk b) :=
  continuous_quot_mk.comp (Continuous.prodMk continuous_const continuous_id)

theorem isOpen_range_mk (b : Bool) : IsOpen (range (mk b)) := by
  refine (isQuotientMap_quotient_mk' (s := gluingSetoid)).isOpen_preimage.mp ?_
  have : (Quotient.mk gluingSetoid ⁻¹' range (mk b) : Set (Bool × ℂ)) = {p | p.1 = b} ∪ {p | 0 < p.2.re} := by
    ext ⟨c, w⟩
    simp only [mem_preimage, mem_union, mem_ofPred_eq]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨h1, h2⟩ := mk_eq_mk.1 hz
      rcases h2 with h2 | h2
      · exact Or.inl h2.symm
      · exact Or.inr h2
    · rintro (h | h)
      · exact ⟨w, by rw [h]; rfl⟩
      · exact ⟨w, mk_eq_mk.2 ⟨rfl, Or.inr h⟩⟩
  change IsOpen (Quotient.mk gluingSetoid ⁻¹' range (mk b))
  rw [this]
  exact (isOpen_discrete {b} |>.preimage continuous_fst).union
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd))

/-- The chart of the copy `b`: the coordinate `proj` on the image of the copy, with inverse `z ↦ [b, z]`. -/
noncomputable def chart (b : Bool) : OpenPartialHomeomorph DoubledPlane ℂ where
  toFun := proj
  invFun := mk b
  source := range (mk b)
  target := univ
  map_source' := fun _ _ ↦ mem_univ _
  map_target' := fun z _ ↦ mem_range_self z
  left_inv' := by
    rintro _ ⟨z, rfl⟩
    rfl
  right_inv' := fun _ _ ↦ rfl
  open_source := isOpen_range_mk b
  open_target := isOpen_univ
  continuousOn_toFun := continuous_proj.continuousOn
  continuousOn_invFun := (continuous_mk b).continuousOn

noncomputable instance : ChartedSpace ℂ DoubledPlane where
  atlas := range chart
  chartAt x := chart (Classical.choose (mk_surjective x))
  mem_chart_source x := by
    obtain ⟨z, hz⟩ := Classical.choose_spec (mk_surjective x)
    exact ⟨z, hz⟩
  chart_mem_atlas x := mem_range_self _

instance : IsManifold 𝓘(ℂ) 1 DoubledPlane := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨b, rfl⟩ ⟨c, rfl⟩
  refine contDiffOn_id.congr fun z _ ↦ ?_
  rfl

/-! ### Contractibility -/

/-- The straight-line homotopy from the identity to the constant map `1`, on representatives. -/
def homotopyAux (p : unitInterval × (Bool × ℂ)) : DoubledPlane :=
  mk p.2.1 ((1 - (p.1 : ℂ)) * p.2.2 + p.1)

theorem homotopyAux_resp (t : unitInterval) {p q : Bool × ℂ} (h : gluingSetoid p q) :
    homotopyAux (t, p) = homotopyAux (t, q) := by
  obtain ⟨h1, h2⟩ := h
  apply mk_eq_mk.2
  refine ⟨by rw [h1], ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl h2
  · right
    have ht0 := t.2.1
    have ht1 := t.2.2
    simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul]
    rcases eq_or_lt_of_le ht1 with h | h
    · rw [h]; norm_num
    · have : 0 < 1 - (t : ℝ) := by linarith
      nlinarith

/-- The homotopy on the quotient. -/
def homotopy (p : unitInterval × DoubledPlane) : DoubledPlane :=
  Quotient.lift (fun q ↦ homotopyAux (p.1, q)) (fun _ _ h ↦ homotopyAux_resp p.1 h) p.2

theorem continuous_homotopy : Continuous homotopy := by
  refine isQuotientMap_quot_mk.continuous_lift_prod_right ?_
  change Continuous fun p : unitInterval × (Bool × ℂ) ↦ homotopyAux p
  refine continuous_quot_mk.comp (Continuous.prodMk (continuous_fst.comp continuous_snd) ?_)
  fun_prop

instance : Nonempty DoubledPlane := ⟨mk true 0⟩

instance : ContractibleSpace DoubledPlane := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨mk true 1, ⟨ContinuousMap.Homotopy.mk ⟨homotopy, continuous_homotopy⟩ ?_ ?_⟩⟩
  · intro x
    obtain ⟨b, z, rfl⟩ := mk_surjective x
    change mk b ((1 - ((0 : unitInterval) : ℂ)) * z + ((0 : unitInterval) : ℂ)) = mk b z
    simp
  · intro x
    obtain ⟨b, z, rfl⟩ := mk_surjective x
    change mk b ((1 - ((1 : unitInterval) : ℂ)) * z + ((1 : unitInterval) : ℂ)) = mk true 1
    simp only [Set.Icc.coe_one, Complex.ofReal_one, sub_self, zero_mul, zero_add]
    exact mk_eq_mk.2 ⟨rfl, Or.inr (by norm_num)⟩

theorem simplyConnectedSpace : SimplyConnectedSpace DoubledPlane := inferInstance

/-! ### Failure of the Hausdorff axiom -/

theorem mk_true_zero_ne : mk true 0 ≠ mk false 0 := by
  intro h
  obtain ⟨-, h2⟩ := mk_eq_mk.1 h
  simp at h2

theorem not_t2Space : ¬ T2Space DoubledPlane := by
  intro hT
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation mk_true_zero_ne
  have h1 : ∀ᶠ ε : ℝ in 𝓝 0, mk true (ε : ℂ) ∈ U :=
    ((continuous_mk true).comp Complex.continuous_ofReal).continuousAt.preimage_mem_nhds
      (by simpa using hU.mem_nhds hxU)
  have h2 : ∀ᶠ ε : ℝ in 𝓝 0, mk false (ε : ℂ) ∈ V :=
    ((continuous_mk false).comp Complex.continuous_ofReal).continuousAt.preimage_mem_nhds
      (by simpa using hV.mem_nhds hyV)
  have h3 : ∀ᶠ ε : ℝ in 𝓝[>] 0, (mk true (ε : ℂ) ∈ U ∧ mk false (ε : ℂ) ∈ V) ∧ ε ∈ Ioi 0 :=
    ((h1.and h2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨ε, ⟨hεU, hεV⟩, hε⟩ := h3.exists
  have heq : mk true (ε : ℂ) = mk false (ε : ℂ) := mk_eq_mk.2 ⟨rfl, Or.inr (by simpa using hε)⟩
  exact hUV.ne_of_mem hεU (heq ▸ hεV) rfl

end DoubledPlane

open DoubledPlane

theorem RiemannSurfaceIso.t2Space {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [T2Space Y] (h : RiemannSurfaceIso X Y) : T2Space X := by
  obtain ⟨e, h1, h2⟩ := h
  let E : X ≃ₜ Y := ⟨e, h1.continuous, h2.continuous⟩
  exact E.symm.t2Space

/-- **Milne, Theorem 0.1, as recorded, is false**: the doubled plane `DoubledPlane` is a simply connected complex
manifold (not Hausdorff) that is isomorphic to none of the Riemann sphere, `ℂ` and the open unit disk. -/
@[kb "milne2017mf" "Theorem 0.1 (uniformization), pdf p. 5: the named statement needs the Hausdorff axiom"]
theorem not_uniformizationStatement : ¬ UniformizationStatement := by
  intro h
  rcases h.out DoubledPlane simplyConnectedSpace with h1 | h1 | h1
  · exact not_t2Space (RiemannSurfaceIso.t2Space h1)
  · exact not_t2Space (RiemannSurfaceIso.t2Space h1)
  · exact not_t2Space (RiemannSurfaceIso.t2Space h1)

/-- **Milne, Theorem 0.1 (uniformization), corrected** (named statement): every simply connected *Hausdorff*
Riemann surface is isomorphic to one of the Riemann sphere, `ℂ` and the open unit disk (exactly one, by
`riemannSurfaceIso_distinct`). The book refers to Forster and Farkas–Kra; the theorem is not in Mathlib or Tau Ceti. -/
@[kb "milne2017mf" "Theorem 0.1 (uniformization), pdf p. 5, with the Hausdorff axiom"]
structure UniformizationStatementT2 : Prop where
  out : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X],
    SimplyConnectedSpace X →
    RiemannSurfaceIso X (OnePoint ℂ) ∨ RiemannSurfaceIso X ℂ ∨ RiemannSurfaceIso X unitDiskOpens

end ModularFormsKB.Milne.RS
