import ModularFormsKB.Milne.Wave9.ClassGroupActionDescent
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Milne wave 9: Proposition 12.21 (corrected form) over every algebraically closed field of characteristic zero

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, Proposition 12.21,
pdf p. 126 (proof omitted in the book).

`Wave9/ClassGroupActionDescent.lean` proves the corrected named statement over algebraically closed fields embedded
in `ℂ`. For an arbitrary algebraically closed field `F` of characteristic zero let `F₀` be the algebraic closure of
`ℚ` in `F`; it embeds in `ℂ`.

* A `j`-invariant with complex multiplication over `F` is algebraic (`isAlgebraic_of_mem_ellCMOver`): the curve is
  isomorphic to one defined over the algebraic closure `F₁` of `ℚ(j)` in `F`, which is countable and so embeds in
  `ℂ`; its endomorphisms descend to `F₁` and go up to `ℂ` (`Wave9/HomDescent.lean`), where `j` is algebraic
  (Theorem 12.8). Hence `Ell_{F₀}(R) ≅ Ell_F(R)` (`ellCMOverEquivAlg`).
* A curve over `F` with complex multiplication is isomorphic to a curve over `F₀`; conjugating the complex
  multiplication `i` and the `𝔞`-isogeny `φ` by the isomorphisms and descending them to `F₀` reduces the
  compatibility clause over `F` to the one over `F₀`.

This proves the named statement `ClassGroupActionPrincipalNormalized` (`classGroupActionPrincipalNormalized`).
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields WeierstrassCurve.Affine Cardinal
open scoped WeierstrassCurve Classical

namespace ModularFormsKB.Milne.Wave9

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K}

/-- A complex `j`-invariant with complex multiplication by `O` is algebraic (Theorem 12.8 through the finiteness of
`Ell(R)`). -/
theorem isAlgebraic_of_mem_ellCMOver_complex (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) {y : ℂ}
    (hy : y ∈ EllCMOver ℂ O) : IsAlgebraic ℚ y := by
  have := hTC
  have hfin : Finite (EllCM O) := by
    obtain ⟨ι⟩ : Nonempty (K →+* ℂ) := inferInstance
    obtain ⟨φ, -⟩ := exists_equiv_pic_ellCM ι O Wave5.complexUniformization hK
    exact Finite.of_equiv _ φ
  exact isAlgebraic_of_finite_range_ringEquiv y
    ((Set.toFinite (EllCM O)).subset (by rintro _ ⟨σ, rfl⟩; exact j_map_mem_ellCM σ hy))

/-- **Descent of membership in `Ell(R)`**: for `F ⊆ L` algebraically closed of characteristic zero, an element of `F`
whose image lies in `Ell_L(R)` lies in `Ell_F(R)`. -/
theorem mem_ellCMOver_of_algebraMap_mem {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed F]
    [CharZero F] [IsAlgClosed L] {x : F} (hx : algebraMap F L x ∈ EllCMOver L O) : x ∈ EllCMOver F O := by
  obtain ⟨W'', hW'', hcm, hj⟩ := hx
  let W₀ : WeierstrassCurve F := WeierstrassCurve.ofJ x
  have hj' : (W₀⁄L).j = W''.j :=
    (WeierstrassCurve.map_j W₀ (algebraMap F L)).trans (by rw [WeierstrassCurve.ofJ_j]; exact hj.symm)
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W'' (W₀⁄L) hj'.symm
  obtain ⟨h1, h2, ⟨e⟩⟩ := hcm
  exact ⟨W₀, inferInstance, (hasCMBy_baseChange_iff (L := L) W₀).mp
    ⟨h1, h2, ⟨e.trans (endRingEquivOfVariableChange hC)⟩⟩, WeierstrassCurve.ofJ_j x⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Theorem 12.8 over every algebraically closed field of characteristic zero**: a `j`-invariant with complex
multiplication by `O` is algebraic over `ℚ`. -/
theorem isAlgebraic_of_mem_ellCMOver (F : Type) [Field F] [IsAlgClosed F] [CharZero F]
    (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) {y : F} (hy : y ∈ EllCMOver F O) :
    IsAlgebraic ℚ y := by
  let E := IntermediateField.adjoin ℚ ({y} : Set F)
  let F₁ := algebraicClosure E F
  have : IsAlgClosed F₁ := IsAlgClosure.isAlgClosed E
  have : CharZero F₁ := (algebraMap F₁ F).charZero
  have hyF₁ : y ∈ F₁ := by
    refine mem_algebraicClosure_iff.mpr ?_
    have hy' : y = algebraMap E F ⟨y, IntermediateField.subset_adjoin ℚ _ rfl⟩ := rfl
    rw [hy']
    exact isAlgebraic_algebraMap _
  have hE : #E ≤ ℵ₀ :=
    (IntermediateField.cardinalMk_adjoin_le ℚ ({y} : Set F)).trans
      (max_le (max_le Cardinal.mk_le_aleph0 ((Cardinal.mk_singleton y).le.trans Cardinal.one_le_aleph0)) le_rfl)
  have hF₁ : #F₁ ≤ #ℂ := by
    refine (Algebra.IsAlgebraic.cardinalMk_le_max E F₁).trans ?_
    rw [Cardinal.mk_complex]
    exact (max_le hE le_rfl).trans Cardinal.aleph0_le_continuum
  obtain ⟨τ₁⟩ := nonempty_ringHom_complex F₁ hF₁
  let y₁ : F₁ := ⟨y, hyF₁⟩
  have h₁ : y₁ ∈ EllCMOver F₁ O := mem_ellCMOver_of_algebraMap_mem (L := F) hy
  let _ : Algebra F₁ ℂ := τ₁.toAlgebra
  have h₂ : τ₁ y₁ ∈ EllCMOver ℂ O := algebraMap_mem_ellCMOver (L := ℂ) h₁
  have h₄ : IsAlgebraic ℚ y₁ :=
    (isAlgebraic_algHom_iff τ₁.toRatAlgHom τ₁.injective).mp (isAlgebraic_of_mem_ellCMOver_complex hK hTC h₂)
  exact (isAlgebraic_algHom_iff (algebraMap F₁ F).toRatAlgHom (algebraMap F₁ F).injective).mpr h₄

section AlgebraicClosure

variable (F : Type) [Field F] [IsAlgClosed F] [CharZero F]

/-- The algebraic closure of `ℚ` in `F`. -/
abbrev ratClosure : IntermediateField ℚ F := algebraicClosure ℚ F

instance : IsAlgClosed (ratClosure F) := IsAlgClosure.isAlgClosed ℚ

instance : CharZero (ratClosure F) := (algebraMap (ratClosure F) F).charZero

/-- `Ell_{F₀}(R) ≅ Ell_F(R)` for `F₀` the algebraic closure of `ℚ` in `F`. -/
noncomputable def ellCMOverEquivAlg (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) :
    EllCMOver (ratClosure F) O ≃ EllCMOver F O :=
  Equiv.ofBijective (fun x ↦ ⟨algebraMap (ratClosure F) F (x : ratClosure F), algebraMap_mem_ellCMOver x.2⟩)
    ⟨fun x y hxy ↦ Subtype.ext ((algebraMap (ratClosure F) F).injective
        (congrArg (fun z : EllCMOver F O ↦ (z : F)) hxy)),
      fun y ↦ by
        have hy := isAlgebraic_of_mem_ellCMOver F hK hTC y.2
        have hyF₀ : (y : F) ∈ ratClosure F := mem_algebraicClosure_iff.mpr hy
        let x : ratClosure F := ⟨(y : F), hyF₀⟩
        exact ⟨⟨x, mem_ellCMOver_of_algebraMap_mem (L := F) (x := x) y.2⟩, Subtype.ext rfl⟩⟩

theorem ellCMOverEquivAlg_apply (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (x : EllCMOver (ratClosure F) O) : (ellCMOverEquivAlg F hK hTC x : F) = algebraMap (ratClosure F) F x :=
  rfl

end AlgebraicClosure

/-- The isomorphisms `u : W → W₀`, `v : W₀ → W` of a change of variables `C • W = W₀`. -/
theorem exists_iso_of_variableChange {F : Type*} [Field F] {W W₀ : WeierstrassCurve F} [W.IsElliptic]
    [W₀.IsElliptic] {C : WeierstrassCurve.VariableChange F} (h : C • W = W₀) :
    ∃ (u : Hom W.toAffine W₀.toAffine) (v : Hom W₀.toAffine W.toAffine),
      v.comp u = Hom.id _ ∧ u.comp v = Hom.id _ := by
  have h' : C⁻¹ • W₀ = W := by rw [← h, inv_smul_smul]
  refine ⟨Hom.ofIsogeny (variableChangeIsogeny C h), Hom.ofIsogeny (variableChangeIsogeny C⁻¹ h'), ?_, ?_⟩
  · simp only [Hom.ofIsogeny_comp_ofIsogeny, variableChangeIsogeny_inv_comp C h h', Hom.id]
  · have := variableChangeIsogeny_inv_comp (C := C⁻¹) h' (by rw [inv_inv]; exact h)
    simp only [Hom.ofIsogeny_comp_ofIsogeny, inv_inv] at this ⊢
    rw [this]; rfl

/-- **Proposition 12.21, corrected** (Milne; proof omitted in the book), over every algebraically closed field `F` of
characteristic zero: `Cl(R)` acts simply transitively on `Ell_F(R)`, compatibly with `𝔞`-isogenies for normalized
complex multiplication. -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126), corrected, every algebraically closed field of char. 0"]
theorem classGroupActionPrincipalNormalized_all (F : Type) [Field F] [IsAlgClosed F] [CharZero F]
    (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (hTC : IsTotallyComplex K) (ι : K →+* F) :
    ∃ act : Pic O → EllCMOver F O → EllCMOver F O,
      (∀ (W W' : WeierstrassCurve.Affine F) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver F O) → (hW' : W'.j ∈ EllCMOver F O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  set F₀ := ratClosure F
  -- `ι` lands in `F₀`
  have hιF₀ : ∀ a, ι a ∈ F₀ := fun a ↦ mem_algebraicClosure_iff.mpr
    ((isAlgebraic_algHom_iff ι.toRatAlgHom ι.injective).mpr (Algebra.IsAlgebraic.isAlgebraic a))
  let ι₀ : K →+* F₀ := ι.codRestrict F₀ hιF₀
  have hι₀ : ∀ a, algebraMap F₀ F (ι₀ a) = ι a := fun _ ↦ rfl
  let τ₀ : F₀ →+* ℂ := (IsAlgClosed.lift : F₀ →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨act₀, hact₀, hbij₀⟩ := exists_act_of_ringHom F₀ τ₀ K O hK hTC ι₀
  set e := ellCMOverEquivAlg F (O := O) hK hTC
  refine ⟨fun c x ↦ e (act₀ c (e.symm x)), ?_, fun x₀ ↦ e.bijective.comp (hbij₀ (e.symm x₀))⟩
  intro W W' _ _ i hi I J hJI hW hW' φ hφ
  have hF := Wave8.pointMap_eq_zero_iff_of_isAIsogeny O i J φ hφ
  -- the curves over `F₀`
  have hW₀ : W.j ∈ F₀ := mem_algebraicClosure_iff.mpr (isAlgebraic_of_mem_ellCMOver F hK hTC hW)
  have hW₀' : W'.j ∈ F₀ := mem_algebraicClosure_iff.mpr (isAlgebraic_of_mem_ellCMOver F hK hTC hW')
  let W₀ : WeierstrassCurve F₀ := WeierstrassCurve.ofJ ⟨W.j, hW₀⟩
  let W₀' : WeierstrassCurve F₀ := WeierstrassCurve.ofJ ⟨W'.j, hW₀'⟩
  have hjW : (W₀⁄F).j = W.j := (WeierstrassCurve.map_j W₀ (algebraMap F₀ F)).trans
    (by rw [WeierstrassCurve.ofJ_j]; rfl)
  have hjW' : (W₀'⁄F).j = W'.j := (WeierstrassCurve.map_j W₀' (algebraMap F₀ F)).trans
    (by rw [WeierstrassCurve.ofJ_j]; rfl)
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W (W₀⁄F) hjW.symm
  obtain ⟨C', hC'⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W' (W₀'⁄F) hjW'.symm
  obtain ⟨u, v, hvu, huv⟩ := exists_iso_of_variableChange hC
  obtain ⟨u', v', hvu', huv'⟩ := exists_iso_of_variableChange hC'
  -- conjugate `i` and `φ` to `W₀ ⊗ F`
  let i' := i.trans (Wave8.conjRingEquiv u v hvu huv)
  have hi' : IsNormalizedCM ι i' := Wave8.isNormalizedCM_conj u v hvu huv ι i hi
  let φ' : Hom (W₀⁄F).toAffine (W₀'⁄F).toAffine := u'.comp (φ.comp v)
  have hF' : ∀ Q : (W₀⁄F).toAffine.Point, φ'.pointMap Q = 0 ↔ ∀ a ∈ J, (i' a).pointMap Q = 0 := by
    intro Q
    simp only [φ', i', RingEquiv.trans_apply, Wave8.conjRingEquiv_apply, Hom.comp_pointMap,
      Wave8.pointMap_eq_zero_iff_of_comp_eq_id u' v' hvu', Wave8.pointMap_eq_zero_iff_of_comp_eq_id u v hvu]
    exact hF (v.pointMap Q)
  -- descend to `F₀`
  let i₀ := i'.trans (endMapRingEquiv (L := F) W₀).symm
  have hi₀map : ∀ a, (i₀ a).map (algebraMap F₀ F) = i' a := fun a ↦
    (endMapRingEquiv (L := F) W₀).apply_symm_apply (i' a)
  obtain ⟨φ₀, hφ₀⟩ := exists_hom_map_eq (L := F) W₀ W₀' φ'
  have hnorm₀ : IsNormalizedCM ι₀ i₀ := by
    intro a
    obtain ⟨c, hc, -⟩ := Hom.existsUnique_pullbackDifferential_invariantDifferential_eq_smul (i₀ a)
    have hcF := Wave8.hom_map_pullbackDifferential (i₀ a) (algebraMap F₀ F) hc
    rw [hi₀map] at hcF
    have h3 : algebraMap F₀ F c • invariantDifferential (W₀⁄F).toAffine =
        ι a • invariantDifferential (W₀⁄F).toAffine := hcF.symm.trans (hi' a)
    have hc' : algebraMap F₀ F c = algebraMap F₀ F (ι₀ a) :=
      ((smul_left_injective F (invariantDifferential_ne_zero _)) h3).trans (hι₀ a).symm
    rw [hc, (algebraMap F₀ F).injective hc']
  have key : ∀ {V : WeierstrassCurve F₀} [V.IsElliptic] (g : Hom W₀.toAffine V.toAffine) (P : W₀.toAffine.Point),
      (g.map (algebraMap F₀ F)).pointMap (P.mapAlong (algebraMap F₀ F) (algebraMap F₀ F).injective) = 0 ↔
        g.pointMap P = 0 := by
    intro V _ g P
    rw [Hom.pointMap_map, ← Point.mapAlong_zero (algebraMap F₀ F) (algebraMap F₀ F).injective,
      (Point.mapAlong_injective (algebraMap F₀ F) (algebraMap F₀ F).injective).eq_iff]
  have hker₀ : ∀ P : W₀.toAffine.Point, φ₀.pointMap P = 0 ↔ ∀ a ∈ J, (i₀ a).pointMap P = 0 := by
    intro P
    calc φ₀.pointMap P = 0 ↔ (φ₀.map (algebraMap F₀ F)).pointMap
          (P.mapAlong (algebraMap F₀ F) (algebraMap F₀ F).injective) = 0 := (key φ₀ P).symm
      _ ↔ ∀ a ∈ J, (i' a).pointMap (P.mapAlong (algebraMap F₀ F) (algebraMap F₀ F).injective) = 0 := by
          rw [hφ₀]; exact hF' _
      _ ↔ ∀ a ∈ J, (i₀ a).pointMap P = 0 := forall₂_congr fun a _ ↦ by
          rw [← hi₀map a]; exact key (i₀ a) P
  have hW₀mem : W₀.j ∈ EllCMOver F₀ O := by
    rw [WeierstrassCurve.ofJ_j]; exact mem_ellCMOver_of_algebraMap_mem (L := F) hW
  have hW₀mem' : W₀'.j ∈ EllCMOver F₀ O := by
    rw [WeierstrassCurve.ofJ_j]; exact mem_ellCMOver_of_algebraMap_mem (L := F) hW'
  have h := hact₀ W₀ W₀' i₀ hnorm₀ I J hJI hW₀mem hW₀mem' φ₀ hker₀
  have e1 : e.symm ⟨W.j, hW⟩ = ⟨W₀.j, hW₀mem⟩ := by
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext (by rw [ellCMOverEquivAlg_apply]; exact hjW.symm.trans (WeierstrassCurve.map_j W₀ _))
  simp only
  rw [e1, h]
  exact Subtype.ext (by rw [ellCMOverEquivAlg_apply]; exact (WeierstrassCurve.map_j W₀' _).symm.trans hjW')

/-- **Proposition 12.21, corrected** (Milne): the named statement `ClassGroupActionPrincipalNormalized` holds. -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126), corrected"]
theorem classGroupActionPrincipalNormalized : ClassGroupActionPrincipalNormalized :=
  ⟨fun k _ _ _ K _ _ O hK hTC ι ↦ classGroupActionPrincipalNormalized_all k K O hK hTC ι⟩

end ModularFormsKB.Milne.Wave9
