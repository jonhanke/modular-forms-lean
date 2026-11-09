import ModularFormsKB.Milne.Ch10.FrobeniusTwistRegular

/-!
# Milne, Proposition 10.2: the Frobenius twist is a curve

Being a curve (`IsCurve`: a variety of dimension one) is invariant under precomposition with an isomorphism of
schemes (`isCurve_iso_comp`) and, over an algebraically closed field, under postcomposition with
$\operatorname{Spec}\tau$ for a field automorphism $\tau$ of $k$ (`isCurve_comp_spec`: the affine charts keep their
rings, with the $k$-algebra structure twisted by $\tau$, and transcendence degrees do not change). The structure
morphism of $C^{(q)}$ is $\mathrm{pr}_1 \gg f \gg \operatorname{Spec}(\mathrm{Frob}^n)^{-1}$, so $C^{(q)}$ is a curve
when $C$ is (`isCurve_frobeniusTwistStructure`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace ModularFormsKB.Milne

/-! ### Transcendence degree under a twist of the base -/

theorem algIndep_twist {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A] [Algebra R A] [Algebra R' A]
    (σ : R ≃+* R') (h : ∀ r, algebraMap R A r = algebraMap R' A (σ r)) {ι : Type u} (x : ι → A) :
    AlgebraicIndependent R x ↔ AlgebraicIndependent R' x := by
  unfold AlgebraicIndependent
  have key : ((MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A) : MvPolynomial ι R →+* A) =
      ((MvPolynomial.aeval x : MvPolynomial ι R' →ₐ[R'] A) : MvPolynomial ι R' →+* A).comp
        (MvPolynomial.map (σ : R →+* R')) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [h]
    · simp
  have hb : Function.Bijective (MvPolynomial.map (σ : R →+* R') : MvPolynomial ι R →+* MvPolynomial ι R') :=
    (MvPolynomial.mapEquiv ι σ).bijective
  constructor
  · intro hi
    have : Function.Injective (((MvPolynomial.aeval x : MvPolynomial ι R' →ₐ[R'] A) : MvPolynomial ι R' →+* A).comp
        (MvPolynomial.map (σ : R →+* R'))) := by rw [← key]; exact hi
    exact (Function.Injective.of_comp_iff' _ hb).mp this
  · intro hi
    have : Function.Injective (((MvPolynomial.aeval x : MvPolynomial ι R →ₐ[R] A) : MvPolynomial ι R →+* A)) := by
      rw [key]; exact hi.comp hb.1
    exact this

theorem trdeg_congr {R R' A A' : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R' A'] (σ : R ≃+* R') (e : A ≃+* A')
    (h : ∀ r, e (algebraMap R A r) = algebraMap R' A' (σ r)) :
    Algebra.trdeg R A = Algebra.trdeg R' A' := by
  let _ : Algebra R A' := ((algebraMap R' A').comp (σ : R →+* R')).toAlgebra
  let e' : A ≃ₐ[R] A' := { e with commutes' := fun r => h r }
  rw [e'.trdeg_eq]
  unfold Algebra.trdeg
  refine Equiv.iSup_congr (Equiv.subtypeEquivRight fun s => ?_) (fun _ => rfl)
  exact algIndep_twist σ (fun r => rfl) _

/-! ### Function fields and dimension -/

section FunctionField

variable (k : Type u) [Field k]

theorem exists_functionField_ringEquiv {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    [Nonempty (⊤ : X.Opens)] [Nonempty (⊤ : X'.Opens)] (e : X' ≅ X) :
    ∃ ψ : X.functionField ≃+* X'.functionField, ∀ s : Γ(X, ⊤),
      ψ (X.germToFunctionField ⊤ s) = X'.germToFunctionField ⊤ (e.hom.appTop s) := by
  have hη : e.hom (genericPoint X') = genericPoint X := genericPoint_eq_of_isOpenImmersion e.hom
  have gen : ∀ (y : X) (_ : e.hom (genericPoint X') = y) (hm : y ∈ (⊤ : X.Opens)),
      ∃ ψ : X.presheaf.stalk y ≃+* X'.functionField, ∀ s : Γ(X, ⊤),
        ψ (X.presheaf.germ ⊤ y hm s) = X'.germToFunctionField ⊤ (e.hom.appTop s) := by
    intro y hy hm
    subst hy
    refine ⟨(asIso (e.hom.stalkMap (genericPoint X'))).commRingCatIsoToRingEquiv, fun s => ?_⟩
    exact Scheme.Hom.germ_stalkMap_apply e.hom ⊤ (genericPoint X') hm s
  obtain ⟨ψ, hψ⟩ := gen _ hη trivial
  exact ⟨ψ, fun s => hψ s⟩

theorem functionFieldAlgebraMap_comp_iso {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X']
    [Nonempty (⊤ : X.Opens)] [Nonempty (⊤ : X'.Opens)] (e : X' ≅ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (ψ : X.functionField ≃+* X'.functionField)
    (hψ : ∀ s : Γ(X, ⊤), ψ (X.germToFunctionField ⊤ s) = X'.germToFunctionField ⊤ (e.hom.appTop s)) (r : k) :
    ψ (functionFieldAlgebraMap k f r) = functionFieldAlgebraMap k (e.hom ≫ f) r := by
  simp only [functionFieldAlgebraMap, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [hψ]
  rfl

theorem dimension_iso_comp {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X'] (e : X' ≅ X)
    (f : X ⟶ Spec (CommRingCat.of k)) : dimension k (e.hom ≫ f) = dimension k f := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  haveI : Nonempty (⊤ : X'.Opens) := ⟨⟨genericPoint X', trivial⟩⟩
  obtain ⟨ψ, hψ⟩ := exists_functionField_ringEquiv e
  letI := (functionFieldAlgebraMap k f).toAlgebra
  letI := (functionFieldAlgebraMap k (e.hom ≫ f)).toAlgebra
  unfold dimension
  exact (trdeg_congr (RingEquiv.refl k) ψ (fun r => functionFieldAlgebraMap_comp_iso k e f ψ hψ r)).symm

theorem functionFieldAlgebraMap_comp_spec {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k))
    (τ : k ≃+* k) (r : k) :
    functionFieldAlgebraMap k (f ≫ Spec.map (CommRingCat.ofHom (τ : k →+* k))) r =
      functionFieldAlgebraMap k f (τ r) := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  simp only [functionFieldAlgebraMap, CommRingCat.hom_comp, RingHom.comp_apply]
  have := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : k →+* k)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← this]
  rfl

theorem dimension_comp_spec {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k))
    (τ : k ≃+* k) :
    dimension k (f ≫ Spec.map (CommRingCat.ofHom (τ : k →+* k))) = dimension k f := by
  unfold dimension
  exact @trdeg_congr k k X.functionField X.functionField _ _ _ _
    (functionFieldAlgebraMap k (f ≫ Spec.map (CommRingCat.ofHom (τ : k →+* k)))).toAlgebra
    (functionFieldAlgebraMap k f).toAlgebra τ (RingEquiv.refl _)
    (fun r => functionFieldAlgebraMap_comp_spec k f τ r)

end FunctionField

/-! ### Charts -/

section Charts

variable (k : Type u) [Field k]

theorem isAffineVariety_iso_comp {Y Y' : Scheme.{u}} (ε : Y' ≅ Y) {g : Y ⟶ Spec (CommRingCat.of k)}
    (h : IsAffineVariety k g) : IsAffineVariety k (ε.hom ≫ g) := by
  obtain ⟨A, _, _, hA, e, he⟩ := h
  exact ⟨A, inferInstance, inferInstance, hA, ε ≪≫ e, by rw [Iso.trans_hom, Category.assoc, he]⟩

/-- The isomorphism of an open subscheme with its preimage under an isomorphism. -/
def chartIso {X X' : Scheme.{u}} (e : X' ≅ X) (U : X.Opens) : (e.hom ⁻¹ᵁ U).toScheme ≅ U.toScheme :=
  haveI : IsOpenImmersion ((e.hom ⁻¹ᵁ U).ι ≫ e.hom) := inferInstance
  IsOpenImmersion.isoOfRangeEq ((e.hom ⁻¹ᵁ U).ι ≫ e.hom) U.ι (by
    ext x
    rw [Scheme.Opens.range_ι]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      have h1 : e.hom (e.inv x) = x := by
        rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
        rfl
      refine ⟨⟨e.inv x, ?_⟩, h1⟩
      show e.hom (e.inv x) ∈ U
      rw [h1]
      exact hx)

theorem chartIso_hom_fac {X X' : Scheme.{u}} (e : X' ≅ X) (U : X.Opens) :
    (chartIso e U).hom ≫ U.ι = (e.hom ⁻¹ᵁ U).ι ≫ e.hom :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem isPrevariety_iso_comp {X X' : Scheme.{u}} (e : X' ≅ X) (f : X ⟶ Spec (CommRingCat.of k))
    (hf : IsPrevariety k f) : IsPrevariety k (e.hom ≫ f) := by
  obtain ⟨n, U, hU, hA⟩ := hf
  refine ⟨n, fun i => e.hom ⁻¹ᵁ U i, ?_, fun i => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have : e.hom x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · have := isAffineVariety_iso_comp k (chartIso e (U i)) (hA i)
    rw [← Category.assoc, ← chartIso_hom_fac, Category.assoc]
    exact this

end Charts

variable (k : Type u) [Field k]

/-- Being a curve is invariant under precomposition with an isomorphism. -/
theorem isCurve_iso_comp {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X'] (e : X' ≅ X)
    (f : X ⟶ Spec (CommRingCat.of k)) (hf : IsCurve k f) : IsCurve k (e.hom ≫ f) := by
  obtain ⟨⟨hp, hs⟩, hd⟩ := hf
  haveI := hs
  exact ⟨⟨isPrevariety_iso_comp k e f hp, inferInstance⟩, (dimension_iso_comp k e f).trans hd⟩

/-! ### Twisting by a field automorphism -/

theorem isReduced_tensor_algebraicClosure [IsAlgClosed k] {A : Type u} [CommRing A] [Algebra k A]
    (h : _root_.IsReduced A) : _root_.IsReduced (TensorProduct k (AlgebraicClosure k) A) := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k (AlgebraicClosure k) A) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k (AlgebraicClosure k)).injective
  have hsurj : Function.Surjective
      (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k (AlgebraicClosure k) A) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x a =>
      obtain ⟨c, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := AlgebraicClosure k)).2 x
      refine ⟨c • a, ?_⟩
      simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  let E := RingEquiv.ofBijective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k (AlgebraicClosure k) A).toRingHom
    ⟨hinj, hsurj⟩
  exact isReduced_of_injective E.symm.toRingHom E.symm.injective

/-- The twisted $k$-algebra structure on a $k$-algebra. -/
def twistAlgebra {A : Type u} [CommRing A] [Algebra k A] (τ : k ≃+* k) : Algebra k A :=
  ((algebraMap k A).comp (τ : k →+* k)).toAlgebra

theorem isAffineAlgebra_twist [IsAlgClosed k] {A : Type u} [CommRing A] [Algebra k A] (τ : k ≃+* k)
    (h : IsAffineAlgebra k A) :
    @IsAffineAlgebra k _ A _ (twistAlgebra k τ) := by
  have hA : _root_.IsReduced A := by
    have := h.2
    exact isReduced_of_injective
      (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k (AlgebraicClosure k) A)
      (Algebra.TensorProduct.includeRight_injective (algebraMap k (AlgebraicClosure k)).injective)
  refine ⟨?_, @isReduced_tensor_algebraicClosure k _ _ A _ (twistAlgebra k τ) hA⟩
  have h1 : (algebraMap k A).FiniteType := RingHom.finiteType_algebraMap.mpr h.1
  exact @RingHom.finiteType_algebraMap k A _ _ (twistAlgebra k τ) |>.mp
    (RingHom.FiniteType.comp h1 (RingHom.FiniteType.of_surjective _ τ.surjective))

theorem isAffineVariety_comp_spec [IsAlgClosed k] {Y : Scheme.{u}} {g : Y ⟶ Spec (CommRingCat.of k)}
    (τ : k ≃+* k) (h : IsAffineVariety k g) :
    IsAffineVariety k (g ≫ Spec.map (CommRingCat.ofHom (τ : k →+* k))) := by
  obtain ⟨A, _, _, hA, e, he⟩ := h
  refine ⟨A, inferInstance, twistAlgebra k τ, isAffineAlgebra_twist k τ hA, e, ?_⟩
  rw [← he, Category.assoc, ← Spec.map_comp]
  rfl

theorem isPrevariety_comp_spec [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (τ : k ≃+* k) (hf : IsPrevariety k f) :
    IsPrevariety k (f ≫ Spec.map (CommRingCat.ofHom (τ : k →+* k))) := by
  obtain ⟨n, U, hU, hA⟩ := hf
  exact ⟨n, U, hU, fun i => by
    rw [← Category.assoc]
    exact isAffineVariety_comp_spec k τ (hA i)⟩

/-- Over an algebraically closed field, being a curve is invariant under twisting the base by an automorphism. -/
theorem isCurve_comp_spec [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k))
    (τ : k ≃+* k) (hf : IsCurve k f) :
    IsCurve k (f ≫ Spec.map (CommRingCat.ofHom (τ : k →+* k))) := by
  obtain ⟨⟨hp, hs⟩, hd⟩ := hf
  haveI := hs
  haveI : IsIso (CommRingCat.ofHom (τ : k →+* k)) := τ.toCommRingCatIso.isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom (τ : k →+* k))) := inferInstance
  exact ⟨⟨isPrevariety_comp_spec k f τ hp, inferInstance⟩, (dimension_comp_spec k f τ).trans hd⟩

variable (p : ℕ) [Fact p.Prime] (hk : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0)

/-- **The Frobenius twist of a curve is a curve.** -/
theorem isCurve_frobeniusTwistStructure [IsAlgClosed k] {C : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ Spec (CommRingCat.of k)) (hf : IsCurve k f) (n : ℕ) [IsIntegral (frobeniusTwist k p hk f n)] :
    IsCurve k (frobeniusTwistStructure k p hk f n) := by
  haveI := charP_of_natCast_eq_zero k p hk
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  haveI := isIso_frobeniusTwist_fst k p hk f n
  haveI := isIso_iterateFrobenius_spec k p hk n
  let τ : k ≃+* k := (iterateFrobeniusEquiv k p n).symm
  have hspec : inv ((Spec (CommRingCat.of k)).iterateFrobenius p hk n) =
      Spec.map (CommRingCat.ofHom (τ : k →+* k)) := by
    haveI := isIso_iterateFrobenius_spec k p hk n
    apply IsIso.inv_eq_of_hom_inv_id
    rw [← Scheme.Spec_map_iterateFrobenius (p := p) k n, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of k) using 2
    ext x
    simp [τ]
    rw [← iterateFrobeniusEquiv_apply]
    exact RingEquiv.apply_symm_apply _ _
  have h : frobeniusTwistStructure k p hk f n =
      (asIso (pullback.fst f ((Spec (CommRingCat.of k)).iterateFrobenius p hk n))).hom ≫
        (f ≫ Spec.map (CommRingCat.ofHom (τ : k →+* k))) := by
    haveI := isIso_iterateFrobenius_spec k p hk n
    rw [← hspec]
    simp only [asIso_hom]
    rw [← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  exact isCurve_iso_comp k _ _ (isCurve_comp_spec k f τ hf)

end ModularFormsKB.Milne
