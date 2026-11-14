import ModularFormsKB.Milne.Wave8.DiffNormal
import ModularFormsKB.Milne.Ch12.Corrected
import ModularFormsKB.Milne.Ch12.VariableChangeEnd

/-!
# Milne wave 8: Proposition 12.21 (corrected form) over `ℂ`

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 126.

The named statement `ClassGroupActionPrincipalNormalized` (Proposition 12.21 with Milne's normalization of
`i : R ≅ End(E)` through the tangent space) quantifies over every algebraically closed field `k` of characteristic
zero. This file proves its instance `k = ℂ`, for **every** elliptic curve over `ℂ` (not only the curves `E(Λ)` of
wave 7), with kernels on points over `AlgebraicClosure ℂ` as in the named statement
(`classGroupActionPrincipalNormalized_complex`).

**Proof.** Let `E` have normalized complex multiplication `i` by `R` and let `φ : E → E'` be an `𝔞`-isogeny.
1. *Uniformization* (wave 5): `E ≅ E(Λ)` by a change of variables. Conjugating `i` by the isomorphism keeps it
   normalized (`isNormalizedCM_conj`: the isomorphism multiplies `ω` by a unit, which cancels).
2. *Normalization* (`DiffNormal`): each `i(a)` on `E(Λ)` is `[z] ↦ [αz]` (wave 7) with `α ω = ι(a) ω`, so `α = ι(a)`
   (`lift_eq_of_isNormalizedCM`). Hence `{β | βΛ ⊆ Λ} = ι(R)` and `Λ` is homothetic to `ι(𝔟)` for a proper, hence
   invertible, fractional ideal `𝔟` of `R` (`exists_idealLattice_of_latticeEnd`; Tau Ceti
   `isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two`).
3. *Kernels*: points over `ℂ` inject into points over `AlgebraicClosure ℂ` compatibly with morphisms (Tau Ceti
   `Hom.pointMap_map`), so `Ker(φ) = Ker(𝔞)` on `ℂ`-points (`pointMap_eq_zero_iff_of_isAIsogeny`), and transported to
   `E(ι𝔟)` it is `latticeCMKer` (`{z | ι(a) z ∈ ι𝔟 for all a ∈ 𝔞}`).
4. Wave 7's `proposition_12_21_complex` then gives `j(E') = [𝔞] · j(E)`.
-/

open NumberField TauCeti TauCeti.Isogeny TauCeti.GlobalNumberFields PeriodPair WeierstrassCurve.Affine
open ModularFormsKB.Milne.Wave5 ModularFormsKB.Milne.Wave7
open scoped Classical

namespace ModularFormsKB.Milne.Wave8

/-! ### Conjugation along an isomorphism -/

section Generic

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (u : Hom W₁ W₂) (v : Hom W₂ W₁) (hvu : v.comp u = Hom.id W₁) (huv : u.comp v = Hom.id W₂)

/-- Conjugation `f ↦ u ∘ f ∘ v` by an isomorphism `u` with inverse `v`, a ring isomorphism
`End(W₁) ≅ End(W₂)`. -/
noncomputable def conjRingEquiv : Hom W₁ W₁ ≃+* Hom W₂ W₂ where
  toFun f := u.comp (f.comp v)
  invFun g := v.comp (g.comp u)
  left_inv f := by
    simp only [← Hom.comp_assoc, hvu, Hom.id_comp]
    rw [Hom.comp_assoc, hvu, Hom.comp_id]
  right_inv g := by
    simp only [← Hom.comp_assoc, huv, Hom.id_comp]
    rw [Hom.comp_assoc, huv, Hom.comp_id]
  map_add' f g := by rw [Hom.add_comp, Hom.comp_add]
  map_mul' f g := by
    simp only [Hom.mul_def]
    calc u.comp ((f.comp g).comp v)
        = u.comp ((f.comp ((Hom.id _).comp g)).comp v) := by rw [Hom.id_comp]
      _ = u.comp ((f.comp ((v.comp u).comp g)).comp v) := by rw [hvu]
      _ = (u.comp (f.comp v)).comp (u.comp (g.comp v)) := by simp only [Hom.comp_assoc]

theorem conjRingEquiv_apply (f : Hom W₁ W₁) : conjRingEquiv u v hvu huv f = u.comp (f.comp v) := rfl

include hvu in
/-- A morphism with a left inverse sends only `0` to `0`. -/
theorem pointMap_eq_zero_iff_of_comp_eq_id {P : W₁.Point} : u.pointMap P = 0 ↔ P = 0 := by
  constructor
  · intro h
    have := congrArg v.pointMap h
    rwa [← Hom.comp_pointMap, hvu, Hom.id_pointMap, Hom.pointMap_zero] at this
  · rintro rfl; exact Hom.pointMap_zero u

/-- **Normalization is preserved by conjugation**: if `i` is normalized with respect to `ι`, so is its conjugate by an
isomorphism (the isomorphism multiplies the invariant differential by a unit, which cancels). -/
theorem isNormalizedCM_conj {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} (ι : K →+* F)
    (i : O.toSubalgebra ≃+* Hom W₁ W₁) (hi : IsNormalizedCM ι i) :
    IsNormalizedCM ι (i.trans (conjRingEquiv u v hvu huv)) := by
  intro a
  obtain ⟨l, hl, -⟩ := Hom.existsUnique_pullbackDifferential_invariantDifferential_eq_smul u
  obtain ⟨m, hm, -⟩ := Hom.existsUnique_pullbackDifferential_invariantDifferential_eq_smul v
  have hlm : l * m = 1 := by
    have h := congrArg (fun g : Hom W₂ W₂ ↦ g.pullbackDifferential (invariantDifferential W₂)) huv
    simp only [Hom.pullbackDifferential_comp, LinearMap.comp_apply, hl, map_smul, hm, smul_smul,
      Hom.pullbackDifferential_id, LinearMap.id_apply] at h
    exact smul_left_injective F (invariantDifferential_ne_zero W₂) (h.trans (one_smul F _).symm)
  show (u.comp ((i a).comp v)).pullbackDifferential (invariantDifferential W₂) = _
  simp only [Hom.pullbackDifferential_comp, LinearMap.comp_apply, hl, map_smul, hi a, hm, smul_smul]
  congr 1
  linear_combination (ι a) * hlm

end Generic

/-! ### Over `ℂ` -/

section Complex

/-- Every elliptic curve over `ℂ` is isomorphic to some `E(Λ)`, by morphisms inverse to each other, with the same
`j`-invariant (wave 5's uniformization). -/
theorem exists_iso_weierstrassCurve (W : WeierstrassCurve.Affine ℂ) [W.IsElliptic] :
    ∃ (L : PeriodPair) (u : Hom W L.weierstrassCurve.toAffine) (v : Hom L.weierstrassCurve.toAffine W),
      v.comp u = Hom.id W ∧ u.comp v = Hom.id _ ∧ L.weierstrassCurve.j = W.j := by
  obtain ⟨L, C, h⟩ := complexUniformization.exists_lattice W
  have h' : C⁻¹ • L.weierstrassCurve = W := by rw [← h, inv_smul_smul]
  refine ⟨L, Hom.ofIsogeny (variableChangeIsogeny C h), Hom.ofIsogeny (variableChangeIsogeny C⁻¹ h'), ?_, ?_,
    j_eq_of_variableChange h⟩
  · simp only [Hom.ofIsogeny_comp_ofIsogeny, variableChangeIsogeny_inv_comp C h h', Hom.id]
  · have := variableChangeIsogeny_inv_comp (C := C⁻¹) h' (by rw [inv_inv]; exact h)
    simp only [Hom.ofIsogeny_comp_ofIsogeny, inv_inv] at this ⊢
    rw [this]; rfl

/-- `c z ∈ Λ` for every `z` forces `c = 0`. -/
theorem eq_zero_of_forall_mul_mem {M : PeriodPair} {c : ℂ} (h : ∀ z, c * z ∈ M.lattice) : c = 0 := by
  by_contra hc
  obtain ⟨w, hw⟩ := exists_notMem_lattice M
  have := h (c⁻¹ * w)
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at this
  exact hw this

/-- Homothetic lattices give isomorphic curves: `z ↦ γz` and `z ↦ γ⁻¹z`. -/
theorem exists_iso_of_homothety (L L₀ : PeriodPair) {γ : ℂ} (hγ : γ ≠ 0)
    (h : L₀.lattice = L.lattice.map (LinearMap.mulLeft ℤ γ)) :
    ∃ (u : Hom L.weierstrassCurve.toAffine L₀.weierstrassCurve.toAffine)
      (v : Hom L₀.weierstrassCurve.toAffine L.weierstrassCurve.toAffine),
      v.comp u = Hom.id _ ∧ u.comp v = Hom.id _ := by
  obtain ⟨u, hu⟩ := exists_hom_of_mul_mem L L₀ γ fun x hx ↦ by
    rw [h]; exact ⟨x, hx, rfl⟩
  obtain ⟨v, hv⟩ := exists_hom_of_mul_mem L₀ L γ⁻¹ fun x hx ↦ by
    rw [h] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [LinearMap.mulLeft_apply, ← mul_assoc, inv_mul_cancel₀ hγ] using hy
  refine ⟨u, v, hom_ext_of_weierstrassPoint' fun z ↦ ?_, hom_ext_of_weierstrassPoint' fun z ↦ ?_⟩
  · rw [Hom.comp_pointMap, hu, hv, Hom.id_pointMap, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
  · rw [Hom.comp_pointMap, hv, hu, Hom.id_pointMap, ← mul_assoc, mul_inv_cancel₀ hγ, one_mul]

variable {K : Type*} [Field K] [NumberField K] (ι : K →+* ℂ) (O : NumberFieldOrder K)

/-- **A normalized action on `E(Λ)` is multiplication by `ι(a)`**: if `i : R ≅ End(E(Λ))` is normalized with respect
to `ι`, then `i(a)` is `[z] ↦ [ι(a) z]`. -/
theorem lift_eq_of_isNormalizedCM (L : PeriodPair)
    (i : O.toSubalgebra ≃+* Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine)
    (hi : IsNormalizedCM ι i) (a : O.toSubalgebra) (z : ℂ) :
    (i a).pointMap (L.weierstrassPoint z) = L.weierstrassPoint (ι a * z) := by
  obtain ⟨α, -, hα⟩ := exists_mul_of_hom L L (i a)
  have h1 := pullbackDifferential_eq_smul_of_lift (i a) hα
  rw [hi a] at h1
  have : ι a = α := smul_left_injective ℂ (invariantDifferential_ne_zero _) h1
  rw [this]; exact hα z

/-- With a normalized action of `R` on `E(Λ)`, `{β | βΛ ⊆ Λ} = ι(R)`. -/
theorem latticeEnd_eq_of_isNormalizedCM (L : PeriodPair)
    (i : O.toSubalgebra ≃+* Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine)
    (hi : IsNormalizedCM ι i) :
    (latticeEnd L.lattice : Set ℂ) = ι '' (O.toSubalgebra : Set K) := by
  ext β
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hβ
    obtain ⟨g, hg⟩ := exists_hom_of_mul_mem L L β hβ
    refine ⟨i.symm g, (i.symm g).2, ?_⟩
    have hz : ∀ z, (β - ι (i.symm g : K)) * z ∈ L.lattice := fun z ↦ by
      rw [← L.weierstrassPoint_eq_zero_iff, sub_mul, sub_eq_add_neg, weierstrassPoint_add,
        weierstrassPoint_neg, ← hg, ← lift_eq_of_isNormalizedCM ι O L i hi, RingEquiv.apply_symm_apply,
        add_neg_cancel]
    exact (sub_eq_zero.1 (eq_zero_of_forall_mul_mem hz)).symm
  · rintro ⟨a, ha, rfl⟩ x hx
    rw [← L.weierstrassPoint_eq_zero_iff]
    have := lift_eq_of_isNormalizedCM ι O L i hi ⟨a, ha⟩ x
    rw [L.weierstrassPoint_of_mem hx, Hom.pointMap_zero] at this
    exact this.symm

/-- **Kernels on `k`-points of an `𝔞`-isogeny**: a morphism whose kernel on points over `AlgebraicClosure k` is
`Ker(𝔞)` kills a `k`-point exactly when every `i(a)`, `a ∈ 𝔞`, does. -/
theorem pointMap_eq_zero_iff_of_isAIsogeny {k : Type*} [Field k] {W W' : WeierstrassCurve.Affine k} [W.IsElliptic]
    [W'.IsElliptic]
    (i : O.toSubalgebra ≃+* Hom W W) (J : Ideal O.toSubalgebra) (φ : Hom W W') (hφ : IsAIsogeny i J φ)
    (P : W.Point) : φ.pointMap P = 0 ↔ ∀ a ∈ J, (i a).pointMap P = 0 := by
  set f := algebraMap k (AlgebraicClosure k)
  have key : ∀ {W'' : WeierstrassCurve.Affine k} [W''.IsElliptic] (g : Hom W W''),
      g.pointMap P = 0 ↔ (g.map f).pointMap (P.mapAlong f f.injective) = 0 := by
    intro W'' _ g
    rw [Hom.pointMap_map, ← Point.mapAlong_zero f f.injective, (Point.mapAlong_injective f f.injective).eq_iff]
  rw [key φ, ← Hom.pointMapHom_apply, ← AddMonoidHom.mem_ker, hφ, cmKerAlg]
  simp only [AddSubgroup.mem_iInf, AddMonoidHom.mem_ker, Hom.pointMapHom_apply]
  exact forall₂_congr fun a _ ↦ (key (i a)).symm

/-- **Proposition 12.21, corrected, over `ℂ`, kernels on `ℂ`-points**: the action of wave 7 is compatible with
every `𝔞`-isogeny `φ : E → E'` between elliptic curves over `ℂ` (not only the curves `E(Λ)`), for `i` normalized by
`ι`, where `Ker(φ) = Ker(𝔞)` is read on `ℂ`-points. -/
theorem exists_act_complex (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (ι : K →+* ℂ) :
    ∃ act : Pic O → EllCMOver ℂ O → EllCMOver ℂ O,
      (∀ (W W' : WeierstrassCurve.Affine ℂ) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver ℂ O) → (hW' : W'.j ∈ EllCMOver ℂ O) → (φ : Hom W W') →
          (∀ P : W.Point, φ.pointMap P = 0 ↔ ∀ a ∈ J, (i a).pointMap P = 0) →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  have := hTC
  obtain ⟨act, -, -, hbij, hcompat⟩ := proposition_12_21_complex ι O hK
  refine ⟨act, ?_, hbij⟩
  intro W W' _ _ i hi I J hJI hW hW' φ hφ
  -- uniformize `E ≅ E(Λ)` and find the ideal
  obtain ⟨L, u₀, v₀, h₁, h₂, hjL⟩ := exists_iso_weierstrassCurve W
  have hEnd := latticeEnd_eq_of_isNormalizedCM ι O L _ (isNormalizedCM_conj u₀ v₀ h₁ h₂ ι i hi)
  obtain ⟨γ, Λ, hγ, hΛp, hγL⟩ := exists_idealLattice_of_latticeEnd ι O hK L hEnd
  have hΛu : IsUnit Λ := (O.isProperFractionalIdeal_iff_isUnit_of_finrank_eq_two hK Λ).1 hΛp
  obtain ⟨L₀, hL₀⟩ := exists_periodPair_idealLattice ι O hK Λ hΛu.ne_zero
  obtain ⟨u₁, v₁, h₃, h₄⟩ := exists_iso_of_homothety L L₀ hγ (hL₀.trans hγL.symm)
  have hjL₀ : L₀.weierstrassCurve.j = L.weierstrassCurve.j :=
    ((j_eq_iff_homothetic L L₀).2 ⟨γ, hγ, hL₀.trans hγL.symm⟩).symm
  set u := u₁.comp u₀
  set v := v₀.comp v₁
  have hvu : v.comp u = Hom.id W := by
    simp only [u, v, Hom.comp_assoc]
    rw [← Hom.comp_assoc v₁, h₃, Hom.id_comp, h₁]
  have huv : u.comp v = Hom.id _ := by
    simp only [u, v, Hom.comp_assoc]
    rw [← Hom.comp_assoc u₀, h₂, Hom.id_comp, h₄]
  have hlift := lift_eq_of_isNormalizedCM ι O L₀ _ (isNormalizedCM_conj u v hvu huv ι i hi)
  -- uniformize the target
  obtain ⟨L', u', v', h₅, h₆, hjL'⟩ := exists_iso_weierstrassCurve W'
  set φ₀ : Hom L₀.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine := u'.comp (φ.comp v)
  have hker : ∀ z, φ₀.pointMap (L₀.weierstrassPoint z) = 0 ↔ z ∈ latticeCMKer ι O Λ J := by
    intro z
    rw [Hom.comp_pointMap, Hom.comp_pointMap, pointMap_eq_zero_iff_of_comp_eq_id u' v' h₅,
      hφ]
    refine forall₂_congr fun a _ ↦ ?_
    rw [← pointMap_eq_zero_iff_of_comp_eq_id u v hvu, ← Hom.comp_pointMap, ← Hom.comp_pointMap]
    have e := hlift a z
    simp only [RingEquiv.trans_apply, conjRingEquiv_apply] at e
    rw [Hom.comp_assoc, e, L₀.weierstrassPoint_eq_zero_iff, hL₀]
  have hx : L₀.weierstrassCurve.j ∈ EllCM O := by rw [hjL₀, hjL]; exact hW
  have h := hcompat hΛu.unit I J hJI L₀ L' hL₀ φ₀ hker hx
  have e1 : (⟨W.j, hW⟩ : EllCMOver ℂ O) = ⟨L₀.weierstrassCurve.j, hx⟩ := Subtype.ext (hjL.symm.trans hjL₀.symm)
  rw [e1]
  exact Subtype.ext (h.trans hjL')

/-- **Proposition 12.21, corrected, over `ℂ`** (Milne; proof omitted in the book): the instance `k = ℂ` of the named
statement `ClassGroupActionPrincipalNormalized`. For an order `R` of an imaginary quadratic field `K` and an
embedding `ι : K → ℂ`, `Pic(R)` acts simply transitively on `Ell_ℂ(R)`, and for every elliptic curve `E` over `ℂ`
with complex multiplication `i : R ≅ End(E)` normalized by `ι`, every invertible integral ideal `𝔞` and every
`𝔞`-isogeny `φ : E → E'` (kernel `Ker(𝔞)` on points over `AlgebraicClosure ℂ`), `[𝔞] · j(E) = j(E')`. -/
@[kb "milne2017mf" "Section 12, Prop. 12.21 (pdf p. 126), corrected, over the complex numbers"]
theorem classGroupActionPrincipalNormalized_complex (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hK : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (ι : K →+* ℂ) :
    ∃ act : Pic O → EllCMOver ℂ O → EllCMOver ℂ O,
      (∀ (W W' : WeierstrassCurve.Affine ℂ) [W.IsElliptic] [W'.IsElliptic] (i : O.toSubalgebra ≃+* Hom W W),
          IsNormalizedCM ι i →
          ∀ (I : (FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)ˣ) (J : Ideal O.toSubalgebra),
          ((J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) = I) →
          (hW : W.j ∈ EllCMOver ℂ O) → (hW' : W'.j ∈ EllCMOver ℂ O) → (φ : Hom W W') → IsAIsogeny i J φ →
            act (ClassGroup.mk (K := K) I) ⟨W.j, hW⟩ = ⟨W'.j, hW'⟩) ∧
      ∀ x₀, Function.Bijective fun c ↦ act c x₀ := by
  obtain ⟨act, h, hbij⟩ := exists_act_complex K O hK hTC ι
  exact ⟨act, fun W W' _ _ i hi I J hJI hW hW' φ hφ ↦ h W W' i hi I J hJI hW hW' φ
    (pointMap_eq_zero_iff_of_isAIsogeny O i J φ hφ), hbij⟩

end Complex

end ModularFormsKB.Milne.Wave8
