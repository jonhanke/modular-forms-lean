import ModularFormsKB.Milne.Ch3.EllipticFunctions

/-!
# Milne, Chapter 3: holomorphic maps of complex tori

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §3, pdf pp. 42–43, and Example 1.6 (p. 16).

* Proposition 3.3: the holomorphic maps `ℂ/Λ → ℂ/Λ'` sending `0` to `0` are the maps `[z] ↦ [αz]`, `αΛ ⊆ Λ'`.
* Corollary 3.4: they are homomorphisms. Corollary 3.5: `ℂ/Λ ≅ ℂ/Λ'` iff `Λ' = αΛ`.
* Corollary 3.6: `End(ℂ/Λ)` is `ℤ` or an order in an imaginary quadratic field.
* Example 1.6: infinitely many complex structures on the torus.
-/

open Complex Filter Topology Set PeriodPair
open scoped Manifold

namespace ModularFormsKB.Milne

/-! ### Proposition 3.3 and its corollaries -/

/-- The map `[z] ↦ [αz] : ℂ/Λ → ℂ/Λ'` for `αΛ ⊆ Λ'`. -/
@[kb "milne2017mf" "Proposition 3.3: the map phi_alpha, pdf p. 42"]
def torusMap {L L' : PeriodPair} (α : ℂ) (hα : ∀ ω ∈ L.lattice, α * ω ∈ L'.lattice) :
    ComplexTorus L → ComplexTorus L' :=
  Quotient.map (fun z ↦ α * z) (fun z w h ↦ by
    change AddAction.orbitRel L.lattice ℂ z w at h
    change AddAction.orbitRel L'.lattice ℂ (α * z) (α * w)
    rw [Submodule.orbitRel_apply_iff_sub_mem] at h ⊢
    have := hα _ h
    rwa [mul_sub] at this)

section Helpers

open scoped ContDiff

theorem torusMap_mk {L L' : PeriodPair} (α : ℂ) (hα : ∀ w ∈ L.lattice, α * w ∈ L'.lattice) (z : ℂ) :
    torusMap α hα (ComplexTorus.mk L z) = ComplexTorus.mk L' (α * z) := rfl

theorem contMDiff_mk (L : PeriodPair) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ComplexTorus.mk L) :=
  (TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := ω) (G := L.lattice) (M := ℂ)).contMDiff

/-- Lifting a holomorphic pointed map of tori through the covering `ℂ → ℂ/Λ'` (the simply connected `ℂ`). -/
theorem exists_lift {L L' : PeriodPair} (φ : ComplexTorus L → ComplexTorus L')
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (h0 : φ (ComplexTorus.mk L 0) = ComplexTorus.mk L' 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 = 0 ∧ ∀ z, ComplexTorus.mk L' (F z) = φ (ComplexTorus.mk L z) := by
  have hcov : IsCoveringMap (Quotient.mk (AddAction.orbitRel L'.lattice ℂ)) :=
    (isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd (G := L'.lattice) (E := ℂ)).isCoveringMap
  have hmk : Continuous (ComplexTorus.mk L) := (contMDiff_mk L).continuous
  obtain ⟨F, ⟨hF0, hFl⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨fun z ↦ φ (ComplexTorus.mk L z), hφ.continuous.comp hmk⟩ : C(ℂ, ComplexTorus L')) 0 0
    (by simpa [ComplexTorus.mk] using h0.symm)
  have hl : ∀ z, ComplexTorus.mk L' (F z) = φ (ComplexTorus.mk L z) := fun z ↦ congrFun hFl z
  refine ⟨F, ?_, hF0, hl⟩
  have h1 := TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := ω) (G := L'.lattice) (M := ℂ)
  intro z
  have hp := h1 (F z)
  have hpf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Quotient.mk (AddAction.orbitRel L'.lattice ℂ) ∘ F) z := by
    have : (Quotient.mk (AddAction.orbitRel L'.lattice ℂ) ∘ F) = φ ∘ ComplexTorus.mk L := funext hl
    rw [this]
    exact (hφ _).comp z (((contMDiff_mk L) z).mdifferentiableAt (by simp))
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (hp.localInverse ∘ (Quotient.mk (AddAction.orbitRel L'.lattice ℂ) ∘ F)) z :=
    (hp.contMDiffAt_localInverse.mdifferentiableAt (by simp)).comp z hpf
  have heq : Filter.EventuallyEq (𝓝 z)
      (hp.localInverse ∘ (Quotient.mk (AddAction.orbitRel L'.lattice ℂ) ∘ F)) F :=
    hp.localInverse_eventuallyEq_left.comp_tendsto F.continuous.continuousAt
  have := (hcomp.congr_of_eventuallyEq heq.symm)
  rw [mdifferentiableAt_iff_differentiableAt] at this
  exact this

/-- An entire function with `F(z + w) - F(z) ∈ Λ'` for `w ∈ Λ`, `F 0 = 0`, is linear (Liouville). -/
theorem eq_mul_of_periodic {L L' : PeriodPair} (F : ℂ → ℂ) (hF : Differentiable ℂ F) (hF0 : F 0 = 0)
    (hper : ∀ w ∈ L.lattice, ∀ z, F (z + w) - F z ∈ L'.lattice) : ∃ α : ℂ, ∀ z, F z = α * z := by
  have hc : ∀ w ∈ L.lattice, ∃ c, ∀ z, F (z + w) = F z + c := by
    intro w hw
    refine ⟨F (0 + w) - F 0, fun z ↦ ?_⟩
    let g : ℂ → L'.lattice := fun z ↦ ⟨F (z + w) - F z, hper w hw z⟩
    have hg : Continuous g := by
      refine Continuous.subtype_mk ?_ _
      exact (hF.continuous.comp (continuous_id.add continuous_const)).sub hF.continuous
    have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hg (x := z) (y := 0)
    have h2 := congrArg Subtype.val this
    simp only [g] at h2
    linear_combination h2
  have hd : ∀ w ∈ L.lattice, ∀ z, deriv F (z + w) = deriv F z := by
    intro w hw z
    obtain ⟨c, hc⟩ := hc w hw
    have h1 : (fun z ↦ F (z + w)) = fun z ↦ F z + c := funext hc
    have := congrArg (fun f ↦ deriv f z) h1
    simp only [deriv_comp_add_const] at this
    rw [this, deriv_add_const]
  have hdiff : Differentiable ℂ (deriv F) := fun z ↦ ((hF.analyticAt z).deriv).differentiableAt
  have hbd : Bornology.IsBounded (Set.range (deriv F)) :=
    (IsZLattice.isCompact_range_of_periodic L.lattice (deriv F) hdiff.continuous
      (fun z w hw ↦ hd w hw z)).isBounded
  have hconst := hdiff.apply_eq_apply_of_bounded hbd
  refine ⟨deriv F 0, fun z ↦ ?_⟩
  have h3 : ∀ z, deriv (fun z ↦ F z - deriv F 0 * z) z = 0 := by
    intro z
    rw [deriv_fun_sub (hF z) (by fun_prop)]
    simp [hconst z 0]
  have := is_const_of_deriv_eq_zero (f := fun z ↦ F z - deriv F 0 * z)
    (fun z ↦ (hF z).sub (by fun_prop)) h3 z 0
  simp only [hF0, mul_zero, sub_zero] at this
  linear_combination this

theorem torusMap_mdifferentiable' {L L' : PeriodPair} (α : ℂ) (hα : ∀ w ∈ L.lattice, α * w ∈ L'.lattice) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (torusMap α hα) ∧ torusMap α hα (ComplexTorus.mk L 0) = ComplexTorus.mk L' 0 := by
  refine ⟨?_, by simp [torusMap_mk]⟩
  have h1 := TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := ω) (G := L.lattice) (M := ℂ)
  have : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (torusMap α hα) := by
    rw [← h1.contMDiff_comp_iff (I' := 𝓘(ℂ)) Quotient.mk_surjective le_rfl]
    have : torusMap α hα ∘ Quotient.mk (AddAction.orbitRel L.lattice ℂ) =
        ComplexTorus.mk L' ∘ (fun z ↦ α * z) := rfl
    rw [this]
    exact (contMDiff_mk L').comp (contMDiff_const.mul contMDiff_id)
  exact this.mdifferentiable (by simp)

theorem mk_eq_mk_iff {L : PeriodPair} (a b : ℂ) :
    ComplexTorus.mk L a = ComplexTorus.mk L b ↔ a - b ∈ L.lattice := by
  rw [← Submodule.orbitRel_apply_iff_sub_mem]
  exact ⟨fun h ↦ Quotient.exact h, fun h ↦ Quotient.sound h⟩

theorem mk_surjective (L : PeriodPair) : Function.Surjective (ComplexTorus.mk L) := Quotient.mk_surjective

theorem mk_add (L : PeriodPair) (a b : ℂ) :
    ComplexTorus.mk L a + ComplexTorus.mk L b = ComplexTorus.mk L (a + b) :=
  (Submodule.orbitRelQuotient_mk_add (p := L.lattice) a b).symm

@[simp] theorem mk_zero (L : PeriodPair) : ComplexTorus.mk L 0 = 0 :=
  Submodule.orbitRelQuotient_mk_zero (p := L.lattice)

theorem eq_of_torusMap_eq {L L' : PeriodPair} {α α' : ℂ} {hα : ∀ w ∈ L.lattice, α * w ∈ L'.lattice}
    {hα' : ∀ w ∈ L.lattice, α' * w ∈ L'.lattice} (h : torusMap α hα = torusMap α' hα') : α = α' := by
  by_contra hne
  have hsub : α - α' ≠ 0 := sub_ne_zero.mpr hne
  have hall : ∀ w : ℂ, w ∈ L'.lattice := by
    intro w
    have := congrFun h (ComplexTorus.mk L (w / (α - α')))
    simp only [torusMap_mk] at this
    rw [mk_eq_mk_iff] at this
    convert this using 1
    field_simp
  have : Countable L'.lattice := inferInstance
  have hc : Countable ℂ :=
    Function.Surjective.countable (f := fun x : L'.lattice ↦ (x : ℂ)) (fun w ↦ ⟨⟨w, hall w⟩, rfl⟩)
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  exact not_countable hc

theorem existsUnique' {L L' : PeriodPair} (φ : ComplexTorus L → ComplexTorus L')
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (h0 : φ (ComplexTorus.mk L 0) = ComplexTorus.mk L' 0) :
    ∃! α : ℂ, ∃ hα : ∀ w ∈ L.lattice, α * w ∈ L'.lattice, φ = torusMap α hα := by
  obtain ⟨F, hF, hF0, hl⟩ := exists_lift φ hφ h0
  have hper : ∀ w ∈ L.lattice, ∀ z, F (z + w) - F z ∈ L'.lattice := by
    intro w hw z
    rw [← mk_eq_mk_iff, hl, hl]
    congr 1
    rw [mk_eq_mk_iff]
    simpa using hw
  obtain ⟨α, hα⟩ := eq_mul_of_periodic F hF hF0 hper
  have hlat : ∀ w ∈ L.lattice, α * w ∈ L'.lattice := by
    intro w hw
    have := hper w hw 0
    simpa [hα, hF0] using this
  have hφα : φ = torusMap α hlat := by
    funext x
    obtain ⟨z, rfl⟩ := mk_surjective L x
    rw [torusMap_mk, ← hl, hα]
  refine ⟨α, ⟨hlat, hφα⟩, ?_⟩
  rintro α' ⟨hα', h⟩
  exact eq_of_torusMap_eq (hα := hα') (hα' := hlat) (h.symm.trans hφα)

theorem torusMap_comp {L L' L'' : PeriodPair} (α β : ℂ) (hα : ∀ w ∈ L.lattice, α * w ∈ L'.lattice)
    (hβ : ∀ w ∈ L'.lattice, β * w ∈ L''.lattice) (hβα : ∀ w ∈ L.lattice, (β * α) * w ∈ L''.lattice) :
    torusMap β hβ ∘ torusMap α hα = torusMap (β * α) hβα := by
  funext x
  obtain ⟨z, rfl⟩ := mk_surjective L x
  simp only [Function.comp, torusMap_mk, mul_assoc]

theorem torusMap_one (L : PeriodPair) (h : ∀ w ∈ L.lattice, (1 : ℂ) * w ∈ L.lattice) :
    torusMap 1 h = id := by
  funext x
  obtain ⟨z, rfl⟩ := mk_surjective L x
  simp [torusMap_mk]

theorem mdifferentiable_add_const {L : PeriodPair} (c : ComplexTorus L) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : ComplexTorus L ↦ x + c) :=
  (ContMDiff.add contMDiff_id contMDiff_const : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω _).mdifferentiable (by simp)

end Helpers

/-- **Milne, Proposition 3.3** (first part): `φ_α` is holomorphic and sends `[0]` to `[0]`. -/
@[kb "milne2017mf" "Proposition 3.3, pdf p. 42"]
theorem torusMap_mdifferentiable {L L' : PeriodPair} (α : ℂ) (hα : ∀ ω ∈ L.lattice, α * ω ∈ L'.lattice) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (torusMap α hα) ∧ torusMap α hα (ComplexTorus.mk L 0) = ComplexTorus.mk L' 0 :=
  torusMap_mdifferentiable' α hα

/-- **Milne, Proposition 3.3** (second part): every holomorphic map `φ : ℂ/Λ → ℂ/Λ'` with `φ([0]) = [0]` is `φ_α` for
a unique `α` with `αΛ ⊆ Λ'`. -/
@[kb "milne2017mf" "Proposition 3.3, pdf p. 42"]
theorem existsUnique_eq_torusMap {L L' : PeriodPair} (φ : ComplexTorus L → ComplexTorus L')
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (h0 : φ (ComplexTorus.mk L 0) = ComplexTorus.mk L' 0) :
    ∃! α : ℂ, ∃ hα : ∀ ω ∈ L.lattice, α * ω ∈ L'.lattice, φ = torusMap α hα :=
  existsUnique' φ hφ h0

/-- **Milne, Corollary 3.4.** Every holomorphic map `φ : ℂ/Λ → ℂ/Λ'` with `φ(0) = 0` is a homomorphism. -/
@[kb "milne2017mf" "Corollary 3.4, pdf p. 43"]
theorem map_add_of_mdifferentiable {L L' : PeriodPair} (φ : ComplexTorus L → ComplexTorus L')
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (h0 : φ (ComplexTorus.mk L 0) = ComplexTorus.mk L' 0)
    (x y : ComplexTorus L) : φ (x + y) = φ x + φ y := by
  obtain ⟨α, ⟨hα, rfl⟩, -⟩ := existsUnique' φ hφ h0
  obtain ⟨a, rfl⟩ := mk_surjective L x
  obtain ⟨b, rfl⟩ := mk_surjective L y
  rw [mk_add, torusMap_mk, torusMap_mk, torusMap_mk, mk_add, mul_add]

/-- **Milne, Corollary 3.5.** The Riemann surfaces `ℂ/Λ` and `ℂ/Λ'` are isomorphic if and only if `Λ' = αΛ` for some
`α ∈ ℂˣ`. Isomorphisms of Riemann surfaces are bijections, holomorphic with holomorphic inverse. -/
@[kb "milne2017mf" "Corollary 3.5, pdf p. 43"]
theorem nonempty_biholomorphic_iff_isHomothetic (L L' : PeriodPair) :
    (∃ e : ComplexTorus L ≃ ComplexTorus L',
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm) ↔
      IsHomothetic L.lattice L'.lattice := by
  constructor
  · rintro ⟨e, he, he'⟩
    set c := e (ComplexTorus.mk L 0) with hc
    have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x ↦ e x + (-c)) := (mdifferentiable_add_const _).comp he
    have h2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x ↦ e.symm (x + c)) := he'.comp (mdifferentiable_add_const _)
    obtain ⟨α, ⟨hα, hψ⟩, -⟩ := existsUnique' _ h1 (by simp [hc])
    obtain ⟨β, ⟨hβ, hψ'⟩, -⟩ := existsUnique' _ h2 (by simp [hc])
    have hβα : ∀ w ∈ L.lattice, (β * α) * w ∈ L.lattice := fun w hw ↦ by
      rw [mul_assoc]; exact hβ _ (hα w hw)
    have hid : torusMap (β * α) hβα = torusMap 1 (fun w hw ↦ by simpa using hw) := by
      rw [← torusMap_comp α β hα hβ hβα, ← hψ, ← hψ', torusMap_one]
      funext x
      simp
    have h11 := eq_of_torusMap_eq hid
    have hα0 : α ≠ 0 := by rintro rfl; simp at h11
    refine ⟨α, hα0, ?_⟩
    ext w
    constructor
    · intro hw
      refine ⟨β * w, hβ w hw, ?_⟩
      show α * (β * w) = w
      rw [← mul_assoc, mul_comm α β, h11, one_mul]
    · rintro ⟨z, hz, rfl⟩
      exact hα z hz
  · rintro ⟨c, hc0, hc⟩
    have hα : ∀ w ∈ L.lattice, c * w ∈ L'.lattice := fun w hw ↦ by
      have : c * w ∈ (L'.lattice : Set ℂ) := by rw [hc]; exact ⟨w, hw, rfl⟩
      exact this
    have hβ : ∀ w ∈ L'.lattice, c⁻¹ * w ∈ L.lattice := fun w hw ↦ by
      have : w ∈ (L'.lattice : Set ℂ) := hw
      rw [hc] at this
      obtain ⟨z, hz, rfl⟩ := this
      simpa [hc0] using hz
    refine ⟨⟨torusMap c hα, torusMap c⁻¹ hβ, fun x ↦ ?_, fun x ↦ ?_⟩,
      (torusMap_mdifferentiable' c hα).1, (torusMap_mdifferentiable' c⁻¹ hβ).1⟩
    · obtain ⟨z, rfl⟩ := mk_surjective L x
      simp [torusMap_mk, hc0]
    · obtain ⟨z, rfl⟩ := mk_surjective L' x
      simp [torusMap_mk, hc0]

/-- `End(ℂ/Λ) = {α ∈ ℂ | αΛ ⊆ Λ}` (Milne, Proposition 3.3 and Corollary 3.6), a subring of `ℂ`. -/
@[kb "milne2017mf" "Corollary 3.6: End(C/Lambda), pdf p. 43"]
def endRing (L : PeriodPair) : Subring ℂ where
  carrier := {α | ∀ ω ∈ L.lattice, α * ω ∈ L.lattice}
  mul_mem' := by
    intro a b ha hb ω hω
    rw [mul_assoc]
    exact ha _ (hb ω hω)
  one_mem' := by intro ω hω; simpa using hω
  add_mem' := by
    intro a b ha hb ω hω
    rw [add_mul]
    exact L.lattice.add_mem (ha ω hω) (hb ω hω)
  zero_mem' := by intro ω _; simp
  neg_mem' := by
    intro a ha ω hω
    rw [neg_mul]
    exact L.lattice.neg_mem (ha ω hω)

section EndRing

theorem ω₁_ne_zero' (L : PeriodPair) : L.ω₁ ≠ 0 := by
  have := L.indep.ne_zero 0
  simpa using this

theorem tau_im_ne (L : PeriodPair) : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro h
  have h1 := ω₁_ne_zero' L
  have hτ : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := Complex.ext (by simp) (by simpa using h)
  have h2 : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
    rw [← hτ, div_mul_cancel₀ _ h1]
  obtain ⟨r, h2⟩ : ∃ r : ℝ, L.ω₂ = r * L.ω₁ := ⟨_, h2⟩
  have := (LinearIndependent.pair_iff.mp L.indep) (-r) 1 (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.real_smul]
    rw [h2]; push_cast; ring)
  simp at this

theorem endRing_coord (L : PeriodPair) {β : ℂ} (hβ : β ∈ endRing L) :
    ∃ a b : ℤ, β = a + b * (L.ω₂ / L.ω₁) := by
  have h1 := ω₁_ne_zero' L
  have hmem : β * L.ω₁ ∈ L.lattice := hβ _ (Submodule.subset_span (by simp))
  obtain ⟨m, n, h⟩ := PeriodPair.mem_lattice.mp hmem
  refine ⟨m, n, ?_⟩
  field_simp
  linear_combination -h

theorem endRing_quad (L : PeriodPair) {β : ℂ} (hβ : β ∈ endRing L) :
    ∃ s p : ℤ, β ^ 2 - s * β + p = 0 := by
  have h1 := ω₁_ne_zero' L
  have m1 : β * L.ω₁ ∈ L.lattice := hβ _ (Submodule.subset_span (by simp))
  have m2 : β * L.ω₂ ∈ L.lattice := hβ _ (Submodule.subset_span (by simp))
  obtain ⟨a, b, e1⟩ := PeriodPair.mem_lattice.mp m1
  obtain ⟨c, d, e2⟩ := PeriodPair.mem_lattice.mp m2
  refine ⟨a + d, a * d - b * c, ?_⟩
  have : (β ^ 2 - ((a + d : ℤ) : ℂ) * β + ((a * d - b * c : ℤ) : ℂ)) * L.ω₁ = 0 := by
    push_cast
    linear_combination (↑d - β) * e1 - ↑b * e2
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h h1

theorem endRing_isIntegral (L : PeriodPair) {β : ℂ} (hβ : β ∈ endRing L) : IsIntegral ℤ β := by
  obtain ⟨s, p, h⟩ := endRing_quad L hβ
  refine ⟨Polynomial.X ^ 2 - Polynomial.C s * Polynomial.X + Polynomial.C p, by monicity!, ?_⟩
  rw [← Polynomial.aeval_def]
  simp
  linear_combination h

theorem endRing_eq' (L : PeriodPair) :
    (endRing L : Set ℂ) = Set.range ((↑) : ℤ → ℂ) ∨
      ∃ K : IntermediateField ℚ ℂ, Module.finrank ℚ K = 2 ∧ (∃ x ∈ K, x.im ≠ 0) ∧
        (∀ α ∈ endRing L, α ∈ K ∧ IsIntegral ℤ α) ∧ Module.finrank ℤ (endRing L) = 2 := by
  by_cases h : ∀ α ∈ endRing L, ∃ n : ℤ, (n : ℂ) = α
  · left
    ext α
    constructor
    · intro hα; obtain ⟨n, hn⟩ := h α hα; exact ⟨n, hn⟩
    · rintro ⟨n, rfl⟩; exact intCast_mem (endRing L) n
  · right
    push Not at h
    obtain ⟨α, hα, hαn⟩ := h
    obtain ⟨a', b', hab⟩ := endRing_coord L hα
    have hb' : b' ≠ 0 := by
      rintro rfl
      exact hαn a' (by simpa using hab.symm)
    have hτim := tau_im_ne L
    have hαim : α.im ≠ 0 := by
      rw [hab]
      simpa [hb'] using hτim
    have hτeq : L.ω₂ / L.ω₁ = (α - a') / b' := by
      have : (b' : ℂ) ≠ 0 := by exact_mod_cast hb'
      rw [hab]; field_simp; ring
    let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {α}
    have hαK : α ∈ K := IntermediateField.mem_adjoin_simple_self ℚ α
    have hint := endRing_isIntegral L hα
    have hQ : IsIntegral ℚ α := hint.tower_top
    have hdeg : Module.finrank ℚ K = 2 := by
      change Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) = 2
      rw [IntermediateField.adjoin.finrank hQ]
      obtain ⟨s, p, hsp⟩ := endRing_quad L hα
      let q : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (s : ℚ) * Polynomial.X + Polynomial.C (p : ℚ)
      have hqm : q.Monic := by simp only [q]; monicity!
      have hq0 : Polynomial.aeval α q = 0 := by
        simp only [q, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
        simpa using hsp
      have hle : (minpoly ℚ α).natDegree ≤ 2 := by
        have h1 := Polynomial.natDegree_le_natDegree
          (minpoly.degree_le_of_ne_zero (A := ℚ) (x := α) hqm.ne_zero hq0)
        have h2 : q.natDegree ≤ 2 := by simp only [q]; compute_degree
        omega
      have hpos := minpoly.natDegree_pos hQ
      have hne : (minpoly ℚ α).natDegree ≠ 1 := by
        intro h1
        obtain ⟨r, hr⟩ := (minpoly.natDegree_eq_one_iff).mp h1
        apply hαim
        rw [← hr]
        simp
      omega
    refine ⟨K, hdeg, ⟨α, hαK, hαim⟩, fun β hβ => ?_, ?_⟩
    · refine ⟨?_, endRing_isIntegral L hβ⟩
      have hτK : L.ω₂ / L.ω₁ ∈ K := by
        rw [hτeq]; exact K.div_mem (K.sub_mem hαK (intCast_mem K a')) (intCast_mem K b')
      obtain ⟨a, b, hab2⟩ := endRing_coord L hβ
      rw [hab2]
      exact K.add_mem (intCast_mem K a) (K.mul_mem (intCast_mem K b) hτK)
    · have hω : L.ω₁ ∈ L.lattice := Submodule.subset_span (by simp)
      let f : endRing L →ₗ[ℤ] L.lattice :=
        { toFun := fun β => ⟨β.1 * L.ω₁, β.2 _ hω⟩
          map_add' := fun x y => by ext; simp [add_mul]
          map_smul' := fun n x => by ext; simp [mul_assoc] }
      have hf : Function.Injective f := by
        intro x y hxy
        have := congrArg Subtype.val hxy
        simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at this
        exact Subtype.ext (mul_right_cancel₀ (ω₁_ne_zero' L) this)
      have hfin : Module.Finite ℤ L.lattice := Module.Finite.of_basis L.latticeBasis
      have hle : Module.finrank ℤ (endRing L) ≤ 2 := by
        have := LinearMap.finrank_le_finrank_of_injective hf
        have h2 : Module.finrank ℤ L.lattice = 2 := by
          rw [Module.finrank_eq_card_basis L.latticeBasis]; simp
        omega
      have : Module.Finite ℤ (endRing L) := Module.Finite.of_injective f hf
      have li : LinearIndependent ℤ ![(⟨1, (endRing L).one_mem⟩ : endRing L), ⟨α, hα⟩] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        have := congrArg Subtype.val hst
        simp at this
        have h2 := congrArg Complex.im this
        simp at h2
        rcases h2 with h2 | h2
        · subst h2; simp at this; simpa [this] using h2
        · exact absurd h2 hαim
      have hge := li.fintype_card_le_finrank
      simp at hge
      omega

end EndRing

/-- **Milne, Corollary 3.6.** Either `End(ℂ/Λ) = ℤ`, or there is an imaginary quadratic field `K ⊆ ℂ` such that
`End(ℂ/Λ)` is a subring of the ring of integers `𝒪_K` of rank 2 over `ℤ`. (`K` is a degree-2 subfield of `ℂ` not
contained in `ℝ`; "contained in `𝒪_K`" is: contained in `K` and integral over `ℤ`.) -/
@[kb "milne2017mf" "Corollary 3.6, pdf p. 43"]
theorem endRing_eq_int_or_imagQuadratic (L : PeriodPair) :
    (endRing L : Set ℂ) = Set.range ((↑) : ℤ → ℂ) ∨
      ∃ K : IntermediateField ℚ ℂ, Module.finrank ℚ K = 2 ∧ (∃ x ∈ K, x.im ≠ 0) ∧
        (∀ α ∈ endRing L, α ∈ K ∧ IsIntegral ℤ α) ∧ Module.finrank ℤ (endRing L) = 2 :=
  endRing_eq' L

/-! ### Example 1.6 -/

section Example16

/-- The rectangular lattice `ℤ + ℤ t i`. -/
noncomputable def rectLat (t : ℝ) (ht : 0 < t) : PeriodPair where
  ω₁ := 1
  ω₂ := (t : ℂ) * I
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s u h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    refine ⟨h1, ?_⟩
    rcases h2 with h | h
    · exact h
    · exact absurd h ht.ne'

theorem mem_rectLat {t : ℝ} (ht : 0 < t) {w : ℂ} :
    w ∈ (rectLat t ht).lattice ↔ ∃ a b : ℤ, w.re = a ∧ w.im = b * t := by
  rw [PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_, ?_⟩
    · rw [← h]; simp [rectLat]
    · rw [← h]; simp [rectLat]
  · rintro ⟨a, b, h1, h2⟩
    refine ⟨a, b, ?_⟩
    apply Complex.ext
    · simp [rectLat, h1]
    · simp [rectLat, h2]

theorem rect_norm {t : ℝ} (ht : 2 ≤ t) (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) :
    1 ≤ (a : ℝ) ^ 2 + ((b : ℝ) * t) ^ 2 ∧
      ((a : ℝ) ^ 2 + ((b : ℝ) * t) ^ 2 = 1 → b = 0 ∧ (a = 1 ∨ a = -1)) := by
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    have ha : a ≠ 0 := by simpa using h
    have h1 : 1 ≤ a ^ 2 := by
      have := Int.one_le_abs ha
      nlinarith [sq_abs a]
    have h1' : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by exact_mod_cast h1
    refine ⟨by simpa using h1', fun h2 => ⟨rfl, ?_⟩⟩
    have : a ^ 2 = 1 := by
      have : (a : ℝ) ^ 2 = 1 := by simpa using h2
      exact_mod_cast this
    have h4 : a ^ 2 = 1 ^ 2 := by simpa using this
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h4 with h | h
    · exact Or.inl h
    · exact Or.inr h
  · have hb1 : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
    have : (4 : ℝ) ≤ ((b : ℝ) * t) ^ 2 := by
      have : (2 : ℝ) ≤ |(b : ℝ)| * t := by nlinarith
      have h3 : ((b : ℝ) * t) ^ 2 = (|(b : ℝ)| * t) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]
      rw [h3]; nlinarith
    refine ⟨by nlinarith [sq_nonneg (a : ℝ)], fun h2 => ?_⟩
    nlinarith [sq_nonneg (a : ℝ)]

theorem rect_normSq {t : ℝ} (ht : 2 ≤ t) {w : ℂ} (hw : w ∈ (rectLat t (by linarith)).lattice) (hw0 : w ≠ 0) :
    1 ≤ Complex.normSq w ∧ (Complex.normSq w = 1 → w.im = 0 ∧ (w.re = 1 ∨ w.re = -1)) := by
  obtain ⟨a, b, h1, h2⟩ := (mem_rectLat (by linarith)).mp hw
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw0
    apply Complex.ext
    · simp [h1, hcon.1]
    · simp [h2, hcon.2]
  obtain ⟨k1, k2⟩ := rect_norm ht a b hne
  have hn : Complex.normSq w = (a : ℝ) ^ 2 + ((b : ℝ) * t) ^ 2 := by
    rw [Complex.normSq_apply, h1, h2]; ring
  refine ⟨hn ▸ k1, fun h => ?_⟩
  obtain ⟨hb, ha⟩ := k2 (hn ▸ h)
  refine ⟨by simp [h2, hb], ?_⟩
  rcases ha with ha | ha
  · left; simp [h1, ha]
  · right; simp [h1, ha]

/-- Homothetic rectangular lattices `ℤ + ℤ t i`, `ℤ + ℤ s i` with `s, t ≥ 2` have `s = t` (shortest vectors). -/
theorem rect_homothetic_eq {t s : ℝ} (ht : 2 ≤ t) (hs : 2 ≤ s)
    (h : IsHomothetic (rectLat t (by linarith)).lattice (rectLat s (by linarith)).lattice) : t = s := by
  obtain ⟨c, hc0, hset⟩ := h
  have hmem : ∀ w, w ∈ (rectLat s (by linarith)).lattice ↔
      ∃ z ∈ (rectLat t (by linarith)).lattice, c * z = w := by
    intro w
    have := Set.ext_iff.mp hset w
    simpa using this
  have h1t : (1 : ℂ) ∈ (rectLat t (by linarith)).lattice :=
    (mem_rectLat (by linarith)).mpr ⟨1, 0, by simp, by simp⟩
  have h1s : (1 : ℂ) ∈ (rectLat s (by linarith)).lattice :=
    (mem_rectLat (by linarith)).mpr ⟨1, 0, by simp, by simp⟩
  have hcs : c ∈ (rectLat s (by linarith)).lattice := (hmem c).mpr ⟨1, h1t, by simp⟩
  obtain ⟨z, hz, hcz⟩ := (hmem 1).mp h1s
  have hz0 : z ≠ 0 := by rintro rfl; simp at hcz
  have n1 := (rect_normSq hs hcs hc0).1
  have n2 := (rect_normSq ht hz hz0).1
  have hnn : Complex.normSq c * Complex.normSq z = 1 := by rw [← map_mul, hcz]; simp
  have hnc : Complex.normSq c = 1 := by nlinarith
  obtain ⟨hcim, hcre⟩ := (rect_normSq hs hcs hc0).2 hnc
  have h2t : (t : ℂ) * I ∈ (rectLat t (by linarith)).lattice :=
    (mem_rectLat (by linarith)).mpr ⟨0, 1, by simp, by simp⟩
  have h2s : (s : ℂ) * I ∈ (rectLat s (by linarith)).lattice :=
    (mem_rectLat (by linarith)).mpr ⟨0, 1, by simp, by simp⟩
  have e1 := (mem_rectLat (by linarith)).mp ((hmem _).mpr ⟨_, h2t, rfl⟩)
  obtain ⟨a1, b1, ha1, hb1⟩ := e1
  obtain ⟨z2, hz2, hcz2⟩ := (hmem _).mp h2s
  obtain ⟨a2, b2, ha2, hb2⟩ := (mem_rectLat (by linarith)).mp hz2
  have hcz2re := congrArg Complex.re hcz2
  have hcz2im := congrArg Complex.im hcz2
  simp [Complex.mul_re, Complex.mul_im, hcim, ha2, hb2] at hcz2re hcz2im
  simp [Complex.mul_re, Complex.mul_im, hcim] at ha1 hb1
  have ht0 : t ≠ 0 := by linarith
  have key : ((b1 * b2 : ℤ) : ℝ) = 1 := by
    push_cast
    apply mul_right_cancel₀ ht0
    rcases hcre with h | h <;> rw [h] at hcz2im hb1
    · linear_combination (b1 : ℝ) * hcz2im - hb1
    · linear_combination (-(b1 : ℝ)) * hcz2im + hb1
  have key' : b1 * b2 = 1 := by exact_mod_cast key
  rcases Int.eq_one_or_neg_one_of_mul_eq_one key' with hb | hb
  · rcases hcre with h | h <;> rw [h, hb] at hb1 <;> push_cast at hb1 <;> linarith
  · rcases hcre with h | h <;> rw [h, hb] at hb1 <;> push_cast at hb1 <;> linarith

theorem circ_eq (x y : ℝ) : ((x : AddCircle (1 : ℝ)) = y) ↔ ∃ n : ℤ, x - y = n := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  simp [eq_comm]

/-- Circle coordinates on `ℂ`. -/
noncomputable def rectCoord (t : ℝ) (z : ℂ) : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) :=
  ((z.re : AddCircle (1 : ℝ)), ((z.im / t : ℝ) : AddCircle (1 : ℝ)))

theorem rectCoord_eq_iff {t : ℝ} (ht : 0 < t) (a b : ℂ) :
    rectCoord t a = rectCoord t b ↔ a - b ∈ (rectLat t ht).lattice := by
  rw [mem_rectLat ht]
  simp only [rectCoord, Prod.mk.injEq]
  rw [circ_eq, circ_eq]
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine ⟨m, n, by simpa using hm, ?_⟩
    simp only [Complex.sub_im]
    field_simp at hn ⊢
    linarith
  · rintro ⟨m, n, hm, hn⟩
    refine ⟨⟨m, by simpa using hm⟩, ⟨n, ?_⟩⟩
    simp only [Complex.sub_im] at hn
    field_simp
    linarith

theorem compactSpace_torus (L : PeriodPair) : CompactSpace (ComplexTorus L) := by
  refine isCompact_univ_iff.1 ?_
  rw [← Set.range_eq_univ.2 Quotient.mk_surjective]
  exact IsZLattice.isCompact_range_of_periodic L.lattice _ continuous_quotient_mk' fun z w hw ↦ by
    change Quotient.mk _ (z + w) = Quotient.mk _ z
    rw [Submodule.orbitRelQuotient_mk_add, (L.lattice.orbitRelQuotient_mk_eq_zero_iff).2 hw, add_zero]

theorem exists_homeo (t : ℝ) (ht : 0 < t) :
    Nonempty (ComplexTorus (rectLat t ht) ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) := by
  have := compactSpace_torus (rectLat t ht)
  have hcont : Continuous (rectCoord t) := by
    unfold rectCoord
    exact ((AddCircle.continuous_mk' (1 : ℝ)).comp Complex.continuous_re).prodMk
      ((AddCircle.continuous_mk' (1 : ℝ)).comp (Complex.continuous_im.div_const t))
  let F : ComplexTorus (rectLat t ht) → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) :=
    Quotient.lift (rectCoord t) (fun a b h ↦ by
      change AddAction.orbitRel (rectLat t ht).lattice ℂ a b at h
      rw [Submodule.orbitRel_apply_iff_sub_mem] at h
      exact (rectCoord_eq_iff ht a b).mpr h)
  have hF : Continuous F := Continuous.quotient_lift hcont _
  have hinj : Function.Injective F := by
    intro x y
    induction x using Quotient.inductionOn with
    | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
    intro h
    exact Quotient.sound (by
      change AddAction.orbitRel (rectLat t ht).lattice ℂ a b
      rw [Submodule.orbitRel_apply_iff_sub_mem]
      exact (rectCoord_eq_iff ht a b).mp h)
  have hsurj : Function.Surjective F := by
    rintro ⟨p, q⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨Quotient.mk _ ⟨x, y * t⟩, ?_⟩
    simp [F, rectCoord, ht.ne']
  exact ⟨hF.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hsurj⟩)⟩

end Example16

/-- **Milne, Example 1.6.** The torus `ℝ²/ℤ²` has infinitely many non-isomorphic complex structures: there are
lattices `Λₙ`, `n ∈ ℕ`, with `ℂ/Λₙ` homeomorphic to `ℝ²/ℤ²` and pairwise non-isomorphic as Riemann surfaces. -/
@[kb "milne2017mf" "Example 1.6, pdf p. 16"]
theorem exists_infinitely_many_complex_structures :
    ∃ L : ℕ → PeriodPair, (∀ n, Nonempty (ComplexTorus (L n) ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) ∧
      ∀ m n, m ≠ n → ¬ ∃ e : ComplexTorus (L m) ≃ ComplexTorus (L n),
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e.symm := by
  refine ⟨fun n ↦ rectLat ((n : ℝ) + 2) (by positivity), fun n ↦ exists_homeo _ _, ?_⟩
  intro m n hmn he
  have h := (nonempty_biholomorphic_iff_isHomothetic _ _).mp he
  have h2 := rect_homothetic_eq (t := (m : ℝ) + 2) (s := (n : ℝ) + 2)
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) h
  exact hmn (by exact_mod_cast (by linarith : (m : ℝ) = n))

end ModularFormsKB.Milne
