import ModularFormsKB.Milne.Ch12.Isogenies
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Isogeny
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
import ModularFormsKB.Citation
/-!
# Milne, Section 12: existence of $\mathfrak a$-isogenies (Proposition 12.20)

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf p. 126.

Proof of the named statement `AIsogenyExists`. Let $E$ be an elliptic curve over a field $k$ of characteristic zero,
$\bar k$ an algebraic closure, and $\Phi \subseteq E(\bar k)$ a finite subgroup stable under $\mathrm{Gal}(\bar k/k)$.
Vélu's quotient $E_{\bar k} \to E_{\bar k}/\Phi$ (Tau Ceti `WeierstrassCurve.Affine.veluIsogeny`) is given by
coordinates that are symmetric in the points of $\Phi$, so the quotient curve and the isogeny are fixed by
$\mathrm{Gal}(\bar k/k)$ and descend to $k$ (Tau Ceti `WeierstrassCurve.exists_baseChange_eq_veluCurve`,
`TauCeti.Isogeny.existsUnique_map_eq_iff_galoisFixed`). The universal property descends too: the factorisation over
$\bar k$ is unique, hence Galois fixed (Silverman, *The Arithmetic of Elliptic Curves*, III.4.11–III.4.13.2).

For $\Phi = \mathrm{Ker}(\mathfrak a)$, $\mathfrak a \ne 0$, the group is finite (it lies in the kernel of one nonzero
endomorphism) and Galois stable (the endomorphisms are defined over $k$). The properness of $\mathfrak a$ is not used.

## Items

- `exists_descended_quotient`: the descended Vélu quotient with its universal property, for any finite Galois-stable
  subgroup in characteristic zero.
- `aIsogenyExists` (**Proposition 12.20**): `AIsogenyExists` holds.
-/

open NumberField TauCeti TauCeti.GlobalNumberFields TauCeti.Isogeny TauCeti.Isogeny.Hom WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve Classical

namespace ModularFormsKB.Milne

namespace AIsogeny

variable {k : Type*} [Field k] {L : Type*} [Field L] [Algebra k L]

/-- An elliptic base change comes from an elliptic curve. -/
theorem isElliptic_of_baseChange (V : WeierstrassCurve k) [h : (V⁄L).IsElliptic] : V.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff] at h ⊢
  have h' : algebraMap k L V.Δ ≠ 0 := by
    have : (V.map (algebraMap k L)).Δ ≠ 0 := h.ne_zero
    rwa [WeierstrassCurve.map_Δ] at this
  exact isUnit_iff_ne_zero.mpr fun h0 => h' (by rw [h0, map_zero])

/-- An isogeny between base changes whose pullback of the two generic coordinates is fixed by `σ` is fixed by the
Galois conjugation by `σ`. -/
theorem galoisConj_eq_of_genericX_genericY (W V : WeierstrassCurve k)
    (ν : Isogeny (W⁄L).toAffine (V⁄L).toAffine) (σ : L ≃ₐ[k] L)
    (hX : W.functionFieldGaloisAction σ (ν.fieldPullback (V⁄L).toAffine.genericX) =
      ν.fieldPullback (V⁄L).toAffine.genericX)
    (hY : W.functionFieldGaloisAction σ (ν.fieldPullback (V⁄L).toAffine.genericY) =
      ν.fieldPullback (V⁄L).toAffine.genericY) :
    ν.galoisConj W V σ = ν := by
  rw [galoisConj_eq_iff_fieldPullback_equivariant]
  have h : (W.functionFieldGaloisAction σ).toRingHom.comp ν.fieldPullback.toRingHom =
      ν.fieldPullback.toRingHom.comp (V.functionFieldGaloisAction σ).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := (V⁄L).toAffine.CoordinateRing)
    intro x
    have hc : ((W.functionFieldGaloisAction σ).toRingHom.comp ν.fieldPullback.toRingHom).comp
          (algebraMap (V⁄L).toAffine.CoordinateRing (V⁄L).toAffine.FunctionField) =
        (ν.fieldPullback.toRingHom.comp (V.functionFieldGaloisAction σ).toRingHom).comp
          (algebraMap (V⁄L).toAffine.CoordinateRing (V⁄L).toAffine.FunctionField) := by
      apply Affine.CoordinateRing.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [← IsScalarTower.algebraMap_apply, functionFieldGaloisAction_algebraMap, AlgHom.commutes,
          functionFieldGaloisAction_algebraMap, AlgHom.commutes]
      · have h := hX
        rw [Affine.genericX_def, fieldPullback_algebraMap] at h
        simpa using h
      · have h := hY
        rw [Affine.genericY_def, fieldPullback_algebraMap] at h
        simpa using h
    exact RingHom.congr_fun hc x
  intro z
  exact RingHom.congr_fun h z

variable [IsGalois k L] [IsAlgClosed L]

/-- The descent step, for an isogeny `ν` out of `E_L` whose target curve `C` is known to be the base change of `V`.
`C` is a variable so that the equation `V_L = C` can be substituted away. -/
theorem descend_of_eq [CharZero k] (W V : WeierstrassCurve k) [W.IsElliptic] (Φ : AddSubgroup (W⁄L).toAffine.Point)
    (C : WeierstrassCurve L) [C.IsElliptic] (hC : V⁄L = C) (ν : Isogeny (W⁄L).toAffine C.toAffine)
    [Algebra.IsSeparable ν.fieldPullback.fieldRange (W⁄L).toAffine.FunctionField]
    (hker : ν.ker = Φ.map (Affine.Point.equivBaseChangeSelf _).toAddMonoidHom)
    (huniv : ∀ (W₃ : Affine L) (ψ : Isogeny (W⁄L).toAffine W₃),
      Φ.map (Affine.Point.equivBaseChangeSelf _).toAddMonoidHom ≤ ψ.ker →
        ∃! χ : Isogeny C.toAffine W₃, χ.comp ν = ψ)
    (hX : ∀ σ : L ≃ₐ[k] L, WeierstrassCurve.functionFieldGaloisAction W σ
      (ν.fieldPullback C.toAffine.genericX) = ν.fieldPullback C.toAffine.genericX)
    (hY : ∀ σ : L ≃ₐ[k] L, WeierstrassCurve.functionFieldGaloisAction W σ
      (ν.fieldPullback C.toAffine.genericY) = ν.fieldPullback C.toAffine.genericY) :
    ∃ (_ : V.IsElliptic) (φ : Hom W.toAffine V.toAffine),
      (φ.map (algebraMap k L)).pointMapHom.ker = Φ ∧
      ∀ (W'' : WeierstrassCurve k) [W''.IsElliptic] (ψ : Hom W.toAffine W''.toAffine),
        Φ ≤ (ψ.map (algebraMap k L)).pointMapHom.ker → ∃! χ : Hom V.toAffine W''.toAffine, χ.comp φ = ψ := by
  subst hC
  have hV : V.IsElliptic := isElliptic_of_baseChange (L := L) V
  have hfix : ∀ σ, ν.galoisConj W V σ = ν := fun σ =>
    galoisConj_eq_of_genericX_genericY W V ν σ (hX σ) (hY σ)
  obtain ⟨φ₀, hφ₀, -⟩ := (existsUnique_map_eq_iff_galoisFixed W V ν).mpr hfix
  -- membership in the kernel of the point map of a separable isogeny over `L`
  have hmem : ∀ {W₃ : WeierstrassCurve L} [W₃.IsElliptic] (μ : Isogeny (W⁄L).toAffine W₃.toAffine)
      [Algebra.IsSeparable μ.fieldPullback.fieldRange (W⁄L).toAffine.FunctionField] (P : (W⁄L).toAffine.Point),
      (ofIsogeny μ).pointMap P = 0 ↔ Affine.Point.equivBaseChangeSelf _ P ∈ μ.ker := by
    intro W₃ _ μ _ P
    rw [pointMap_ofIsogeny_eq_toPointHom, mem_ker_iff_toPointHom_eq_zero]
  refine ⟨hV, ofIsogeny φ₀, ?_, ?_⟩
  · ext P
    show ((ofIsogeny φ₀).map (algebraMap k L)).pointMap P = 0 ↔ P ∈ Φ
    rw [ofIsogeny_map, hφ₀]
    have hΦmem : ∀ Q : (W⁄L).toAffine.Point, Affine.Point.equivBaseChangeSelf _ Q ∈
        Φ.map (Affine.Point.equivBaseChangeSelf _).toAddMonoidHom ↔ Q ∈ Φ := fun Q => by
      rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply]
    exact (hmem ν P).trans (by rw [hker]; exact hΦmem P)
  · intro W'' _ ψ hψ
    rcases ψ.eq_zero_or_exists_ofIsogeny with rfl | ⟨ψ₀, rfl⟩
    · refine ⟨0, zero_comp _, fun χ hχ => ?_⟩
      rcases comp_eq_zero_iff.mp hχ with h | h
      · exact h
      · exact absurd h (ofIsogeny_ne_zero _)
    set ψ' : Isogeny (W⁄L).toAffine (W''⁄L).toAffine := ψ₀.map (algebraMap k L) with hψ'
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
    have : CharZero ψ'.fieldPullback.fieldRange :=
      charZero_of_injective_algebraMap (algebraMap L ψ'.fieldPullback.fieldRange).injective
    have : Algebra.IsSeparable ψ'.fieldPullback.fieldRange (W⁄L).toAffine.FunctionField :=
      Algebra.IsSeparable.of_integral _ _
    have hker' : Φ.map (Affine.Point.equivBaseChangeSelf _).toAddMonoidHom ≤ ψ'.ker := by
      rintro _ ⟨P, hP, rfl⟩
      have h0 : ((ofIsogeny ψ₀).map (algebraMap k L)).pointMap P = 0 := hψ hP
      rw [ofIsogeny_map] at h0
      exact (hmem ψ' P).mp h0
    obtain ⟨χ', hχ', huniq⟩ := huniv _ ψ' hker'
    have hχfix : ∀ σ, χ'.galoisConj V W'' σ = χ' := fun σ => by
      apply huniq
      rw [← hfix σ, ← galoisConj_comp, hχ', hψ', galoisConj_map_algebraMap]
    obtain ⟨χ₀, hχ₀, -⟩ := (existsUnique_map_eq_iff_galoisFixed V W'' χ').mpr hχfix
    obtain ⟨_, -, huψ⟩ := (existsUnique_map_eq_iff_galoisFixed W W'' ψ').mpr
      fun σ => galoisConj_map_algebraMap _ _ _ _
    have hcomp : χ₀.comp φ₀ = ψ₀ :=
      (huψ _ ((Isogeny.comp_map χ₀ φ₀ (algebraMap k L)).trans
        ((congrArg₂ (fun a b => Isogeny.comp a b) hχ₀ hφ₀).trans hχ'))).trans (huψ _ rfl).symm
    refine ⟨ofIsogeny χ₀, (ofIsogeny_comp_ofIsogeny χ₀ φ₀).trans (congrArg ofIsogeny hcomp), fun χ hχ => ?_⟩
    rcases χ.eq_zero_or_exists_ofIsogeny with rfl | ⟨χ₁, rfl⟩
    · rw [zero_comp] at hχ
      exact absurd hχ.symm (ofIsogeny_ne_zero _)
    · rw [ofIsogeny_comp_ofIsogeny] at hχ
      have h1 := ofIsogeny_injective hχ
      have h2 : χ₁.map (algebraMap k L) = χ' := huniq _
        ((congrArg (fun b => (χ₁.map (algebraMap k L)).comp b) hφ₀.symm).trans
          ((Isogeny.comp_map χ₁ φ₀ _).symm.trans (congrArg (fun c => c.map (algebraMap k L)) h1)))
      obtain ⟨_, -, huχ⟩ := (existsUnique_map_eq_iff_galoisFixed V W'' χ').mpr hχfix
      rw [(huχ _ h2).trans (huχ _ hχ₀).symm]

/-- **The descended Vélu quotient.** Over a field `k` of characteristic zero, a finite subgroup `Φ` of `E(L)`, `L`
an algebraic closure, stable under `Gal(L/k)`, is the kernel of a morphism `φ : E → E'` defined over `k`, through
which every morphism over `k` killing `Φ` factors uniquely (Silverman III.4.11–III.4.13.2). -/
theorem exists_descended_quotient [CharZero k] (W : WeierstrassCurve k) [W.IsElliptic]
    (Φ : AddSubgroup (W⁄L).toAffine.Point) (hfin : Finite Φ)
    (hΦ : ∀ σ : L ≃ₐ[k] L, ∀ P ∈ Φ, Affine.Point.map σ.toAlgHom P ∈ Φ) :
    ∃ (V : WeierstrassCurve k) (_ : V.IsElliptic) (φ : Hom W.toAffine V.toAffine),
      (φ.map (algebraMap k L)).pointMapHom.ker = Φ ∧
      ∀ (W'' : WeierstrassCurve k) [W''.IsElliptic] (ψ : Hom W.toAffine W''.toAffine),
        Φ ≤ (ψ.map (algebraMap k L)).pointMapHom.ker → ∃! χ : Hom V.toAffine W''.toAffine, χ.comp φ = ψ := by
  have := hfin
  set e := (Affine.Point.equivBaseChangeSelf (W⁄L).toAffine)
  set Φ' := Φ.map e.toAddMonoidHom with hΦ'
  have : Finite Φ' := Finite.of_equiv Φ (Φ.equivMapOfInjective _ e.injective).toEquiv
  have hstab : ∀ σ : L ≃ₐ[k] L, ∀ P : (W⁄L).toAffine.Point, e P ∈ Φ' →
      e (Multiplicative.toAdd (W.pointGaloisAction σ) P) ∈ Φ' := by
    intro σ P hP
    rw [hΦ', AddSubgroup.mem_map_equiv] at hP ⊢
    simp only [AddEquiv.symm_apply_apply] at hP ⊢
    rw [pointGaloisAction_apply]
    exact hΦ σ P hP
  obtain ⟨V, hV⟩ := exists_baseChange_eq_veluCurve W Φ' hstab
  obtain ⟨hVe, φ, h1, h2⟩ := descend_of_eq W V Φ _ hV (Affine.veluIsogeny (W⁄L).toAffine Φ')
    (Affine.ker_veluIsogeny _ _)
    (fun W₃ ψ h => (Affine.existsUnique_comp_veluIsogeny_eq_iff_le_ker _ Φ' ψ).mpr h)
    (fun σ => by rw [Affine.fieldPullback_veluIsogeny_genericX, functionFieldGaloisAction_veluX W Φ' (hstab σ)])
    (fun σ => by rw [Affine.fieldPullback_veluIsogeny_genericY, functionFieldGaloisAction_veluY W Φ' (hstab σ)])
  exact ⟨V, hVe, φ, h1, h2⟩

end AIsogeny

open AIsogeny

/-- $\mathrm{Ker}(\mathfrak a)$ over $\bar k$ is finite for $\mathfrak a \ne 0$: it lies in the kernel of $i(a)$ for
one nonzero $a \in \mathfrak a$. -/
theorem finite_cmKerAlg {k : Type*} [Field k] {W : WeierstrassCurve.Affine k} [W.IsElliptic]
    {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} (i : O.toSubalgebra ≃+* Hom W W)
    {I : Ideal O.toSubalgebra} (hI : I ≠ ⊥) : Finite (cmKerAlg i I) := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hia : (i a).map (algebraMap k (AlgebraicClosure k)) ≠ 0 := by
    rw [Ne, Hom.map_eq_zero_iff, map_eq_zero_iff i i.injective]
    exact ha
  have hfin := Hom.finite_ker_pointMapHom _ hia
  have hle : cmKerAlg i I ≤ ((i a).map (algebraMap k (AlgebraicClosure k))).pointMapHom.ker :=
    iInf₂_le a haI
  exact Finite.of_injective _ (AddSubgroup.inclusion_injective hle)

/-- $\mathrm{Ker}(\mathfrak a)$ is stable under $\mathrm{Gal}(\bar k/k)$, the endomorphisms being defined over $k$. -/
theorem map_mem_cmKerAlg {k : Type*} [Field k] {W : WeierstrassCurve.Affine k} [W.IsElliptic]
    {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} (i : O.toSubalgebra ≃+* Hom W W)
    (I : Ideal O.toSubalgebra) (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    {P : (W.map (algebraMap k (AlgebraicClosure k))).Point} (hP : P ∈ cmKerAlg i I) :
    Affine.Point.map σ.toAlgHom P ∈ cmKerAlg i I := by
  refine AddSubgroup.mem_iInf.mpr fun a => AddSubgroup.mem_iInf.mpr fun ha => ?_
  have h0 : ((i a).map (algebraMap k (AlgebraicClosure k))).pointMap P = 0 :=
    AddSubgroup.mem_iInf.mp (AddSubgroup.mem_iInf.mp hP a) ha
  show ((i a).map (algebraMap k (AlgebraicClosure k))).pointMap (Affine.Point.map σ.toAlgHom P) = 0
  exact (Hom.pointMap_map_algebraMap_map (i a) σ.toAlgHom P).trans
    ((congrArg (Affine.Point.map σ.toAlgHom) h0).trans (map_zero _))

/-- **Proposition 12.20** (Milne; Silverman, *The Arithmetic of Elliptic Curves*, III.4.12, III.4.13.2): the named
statement `AIsogenyExists` holds. -/
@[kb "milne2017mf" "Section 12, Prop. 12.20 (pdf p. 126)"]
theorem aIsogenyExists : AIsogenyExists where
  exists_universal k _ _ W _ K _ _ O i I hI _ := by
    obtain ⟨V, hV, φ, hker, huniv⟩ := exists_descended_quotient (L := AlgebraicClosure k) W (cmKerAlg i I)
      (finite_cmKerAlg i hI) fun σ P hP => map_mem_cmKerAlg i I σ hP
    exact ⟨V, hV, φ, hker, fun W'' _ ψ hψ => huniv W'' ψ hψ⟩

end ModularFormsKB.Milne
