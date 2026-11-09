import ModularFormsKB.Milne.Ch7.CompletionUniversal
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# The embedding of a regular curve into its completion is an open immersion: stalks

With the notation of `ModularFormsKB.Milne.Completion` ($\iota : U \to \bar U$ induced by
$e : k_0(\bar U) \cong k_0(U)$, all local rings valuation rings), the stalk maps of $\iota$ are isomorphisms
(`isIso_stalkMap_ι`): $\iota^\# : \mathcal O_{\bar U, \iota x} \to \mathcal O_{U, x}$ is compatible with $e$
(`stalkMap_ι_algebraMap`), injective, and surjective because a valuation ring is maximal for domination among local
subrings of its fraction field.
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ModularFormsKB.Milne.Completion

variable {k : Type u} [Field k] {U Ubar : Scheme.{u}}
  [U.Over (Spec (CommRingCat.of k))] [Ubar.Over (Spec (CommRingCat.of k))]
  [IsIntegral U] [IsIntegral Ubar] [IsProper (Ubar ↘ Spec (CommRingCat.of k))]
  (hU : ∀ x : U, ValuationRing (U.presheaf.stalk x))
  (e : Ubar.functionField ≃ₐ[k] U.functionField)

/-- The stalk map of $\iota$ is compatible with $e$ on function fields. -/
theorem stalkMap_ι_algebraMap (x : U) (a : Ubar.presheaf.stalk ((ι hU e) x)) :
    algebraMap (U.presheaf.stalk x) U.functionField ((ι hU e).stalkMap x a) =
      e (algebraMap (Ubar.presheaf.stalk ((ι hU e) x)) Ubar.functionField a) := by
  have hgen : genericPoint U ⤳ x := (genericPoint_spec U).specializes (Set.mem_univ x)
  have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply (ι hU e) (genericPoint U) x hgen a
  have hff := Scheme.functionFieldMap_homOfFunctionFieldAlgHom hU e.toAlgHom
  have h2 : (ι hU e).functionFieldMap
      (algebraMap (Ubar.presheaf.stalk ((ι hU e) x)) Ubar.functionField a) =
      e (algebraMap (Ubar.presheaf.stalk ((ι hU e) x)) Ubar.functionField a) := by
    rw [hff]
    rfl
  rw [← h2]
  change _ = ((Ubar.presheaf.stalkSpecializes _ ≫ (ι hU e).stalkMap (genericPoint U)).hom)
    ((Ubar.presheaf.stalkSpecializes _).hom a)
  rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact h1.symm

/-- **Valuation rings are maximal for domination**: a local homomorphism $s$ from a valuation ring $V$ (fraction
field $K$) to a local domain $R \subseteq L$, compatible with an isomorphism $K \cong L$, is bijective. -/
theorem bijective_of_valuationRing {V R K L : Type*} [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing R] [IsLocalRing R] [Field L] [Algebra R L]
    (hR : Function.Injective (algebraMap R L)) (e : K ≃+* L) (s : V →+* R) [IsLocalHom s]
    (hs : ∀ a, algebraMap R L (s a) = e (algebraMap V K a)) : Function.Bijective s := by
  have hinj : Function.Injective s := by
    intro a b hab
    have := congrArg (algebraMap R L) hab
    rw [hs, hs] at this
    exact IsFractionRing.injective V K (e.injective this)
  refine ⟨hinj, fun r ↦ ?_⟩
  by_cases hr : r = 0
  · exact ⟨0, by rw [hr, map_zero]⟩
  set t : K := e.symm (algebraMap R L r) with ht
  have ht0 : t ≠ 0 := by
    rw [ht, ne_eq, map_eq_zero_iff _ e.symm.injective, map_eq_zero_iff _ hR]
    exact hr
  rcases ValuationRing.isInteger_or_isInteger V t with ⟨a, ha⟩ | ⟨w, hw⟩
  · refine ⟨a, hR ?_⟩
    rw [hs, ha, ht, RingEquiv.apply_symm_apply]
  · -- `t⁻¹ = w`; `w` is a unit of `V`, otherwise `s w` would be a nonunit with inverse `r`.
    by_cases hwu : IsUnit w
    · obtain ⟨u, rfl⟩ := hwu
      refine ⟨↑u⁻¹, hR ?_⟩
      have h1 : algebraMap V K ↑u⁻¹ = t := by
        rw [map_units_inv, hw, inv_inv]
      rw [hs, h1, ht, RingEquiv.apply_symm_apply]
    · have h1 : algebraMap R L (s w * r) = 1 := by
        rw [map_mul, hs, hw, map_inv₀, ht, RingEquiv.apply_symm_apply, inv_mul_cancel₀]
        rw [ne_eq, map_eq_zero_iff _ hR]
        exact hr
      have h2 : s w * r = 1 := hR (by rw [h1, map_one])
      exact absurd ((isUnit_map_iff s w).1 (Units.mkOfMulEqOne _ _ h2).isUnit) hwu

include hU in
/-- **The stalk maps of $\iota$ are isomorphisms.** -/
theorem isIso_stalkMap_ι (hUbar : ∀ x : Ubar, ValuationRing (Ubar.presheaf.stalk x)) (x : U) :
    IsIso ((ι hU e).stalkMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have := hUbar ((ι hU e) x)
  exact bijective_of_valuationRing (V := Ubar.presheaf.stalk ((ι hU e) x)) (K := Ubar.functionField)
    (L := U.functionField) (IsFractionRing.injective _ _) e.toRingEquiv ((ι hU e).stalkMap x).hom
    (stalkMap_ι_algebraMap hU e x)

include hU in
/-- $\iota$ is flat and locally of finite presentation, hence an open map. -/
theorem isOpenMap_ι [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k))]
    (hUbar : ∀ x : Ubar, ValuationRing (Ubar.presheaf.stalk x)) : IsOpenMap (ι hU e).base := by
  have : Flat (ι hU e) := Flat.of_stalkMap _ fun x ↦ RingHom.Flat.of_bijective
    ((ConcreteCategory.isIso_iff_bijective _).1 (isIso_stalkMap_ι hU e hUbar x))
  have : LocallyOfFiniteType (ι hU e ≫ Ubar ↘ Spec (CommRingCat.of k)) := by
    rw [comp_over]; infer_instance
  have : LocallyOfFiniteType (ι hU e) := locallyOfFiniteType_of_comp _ (Ubar ↘ Spec (CommRingCat.of k))
  have : IsLocallyNoetherian Ubar := LocallyOfFiniteType.isLocallyNoetherian (Ubar ↘ Spec (CommRingCat.of k))
  have : LocallyOfFinitePresentation (ι hU e) := LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 ‹_›
  have : UniversallyOpen (ι hU e) := UniversallyOpen.of_flat _
  exact (ι hU e).isOpenMap

/-- The morphism $\operatorname{Spec} k_0(\bar U) \to U$ through the generic point. -/
abbrev genericTop : Spec Ubar.functionField ⟶ U :=
  Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫ U.fromSpecStalk (genericPoint U)

include hU in
/-- The lift $\operatorname{Spec} \mathcal O_{\bar U, p} \cong \operatorname{Spec} \mathcal O_{U, z} \to U$ for
$\iota z = p$. -/
theorem exists_lift (hUbar : ∀ x : Ubar, ValuationRing (Ubar.presheaf.stalk x)) (z : U) (p : Ubar)
    (hp : (ι hU e) z = p) :
    ∃ ℓ : Spec (Ubar.presheaf.stalk p) ⟶ U, ℓ ≫ ι hU e = Ubar.fromSpecStalk p ∧
      Spec.map (CommRingCat.ofHom (algebraMap (Ubar.presheaf.stalk p) Ubar.functionField)) ≫ ℓ =
        genericTop e ∧ ℓ (IsLocalRing.closedPoint (Ubar.presheaf.stalk p)) = z := by
  subst hp
  have := isIso_stalkMap_ι hU e hUbar z
  refine ⟨inv (Spec.map ((ι hU e).stalkMap z)) ≫ U.fromSpecStalk z, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, IsIso.inv_hom_id_assoc]
  · have hgen : genericPoint U ⤳ z := (genericPoint_spec U).specializes (Set.mem_univ z)
    rw [genericTop, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
      ← Category.assoc]
    congr 1
    rw [← cancel_mono (Spec.map ((ι hU e).stalkMap z)), Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Category.assoc]
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    change algebraMap _ _ a = e.symm (algebraMap (U.presheaf.stalk z) U.functionField
      ((ι hU e).stalkMap z a))
    rw [stalkMap_ι_algebraMap]
    simp
  · change (U.fromSpecStalk z) ((inv (Spec.map ((ι hU e).stalkMap z)))
      (IsLocalRing.closedPoint _)) = z
    rw [← Spec.map_inv]
    have : IsLocalHom (inv ((ι hU e).stalkMap z)).hom := by
      infer_instance
    erw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

include hU in
/-- **$\iota$ is injective** (uniqueness in the valuative criterion for the separated morphism $\iota$). -/
theorem injective_ι [IsSeparated (U ↘ Spec (CommRingCat.of k))]
    (hUbar : ∀ x : Ubar, ValuationRing (Ubar.presheaf.stalk x)) : Function.Injective (ι hU e) := by
  intro x y h
  obtain ⟨ℓx, hx1, hx2, hx3⟩ := exists_lift hU e hUbar x ((ι hU e) x) rfl
  obtain ⟨ℓy, hy1, hy2, hy3⟩ := exists_lift hU e hUbar y ((ι hU e) x) h.symm
  have : IsSeparated (ι hU e ≫ Ubar ↘ Spec (CommRingCat.of k)) := by
    rw [comp_over]; infer_instance
  have : IsSeparated (ι hU e) := IsSeparated.of_comp _ (Ubar ↘ Spec (CommRingCat.of k))
  set q := Spec.map (CommRingCat.ofHom
      (algebraMap (Ubar.presheaf.stalk ((ι hU e) x)) Ubar.functionField)) with hq
  have hdomi : IsDominant q :=
    ⟨RingHom.denseRange_comap_of_injective _ (IsFractionRing.injective _ _)⟩
  have hℓ : ℓx = ℓy := ext_of_isDominant_of_isSeparated (ι hU e) (hx1.trans hy1.symm) q
    (hx2.trans hy2.symm)
  rw [← hx3, ← hy3, hℓ]

include hU in
/-- **$\iota : U \to \bar U$ is an open immersion.** -/
theorem isOpenImmersion_ι [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k))]
    (hUbar : ∀ x : Ubar, ValuationRing (Ubar.presheaf.stalk x)) : IsOpenImmersion (ι hU e) := by
  have := isIso_stalkMap_ι hU e hUbar
  exact IsOpenImmersion.of_isIso_stalkMap _ (.of_continuous_injective_isOpenMap
    (ι hU e).base.hom.continuous (injective_ι hU e hUbar) (isOpenMap_ι hU e hUbar))

end ModularFormsKB.Milne.Completion
