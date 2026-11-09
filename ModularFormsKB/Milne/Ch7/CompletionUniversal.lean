import ModularFormsKB.Milne.Ch7.CurveBridge
import TauCeti.AlgebraicGeometry.Birational.AlgHom

/-!
# The universal property of the completion of a regular curve

Let $U$ be an integral $k_0$-scheme whose local rings are valuation rings, $\bar U$ an integral $k_0$-scheme whose
local rings are valuation rings, and $e : k_0(\bar U) \cong k_0(U)$. Let $\iota : U \to \bar U$ be the morphism
induced by $e$ (Tau Ceti's `Scheme.homOfFunctionFieldAlgHom`, defined when $\bar U$ is proper). Then every
$k_0$-morphism $\varphi : U \to C$ to a proper $k_0$-scheme $C$ extends uniquely along $\iota$
(`exists_unique_extension`): the extension is the morphism extending
$\operatorname{Spec} k_0(\bar U) \xrightarrow{e} \operatorname{Spec} k_0(U) \to U \to C$ from the generic point (Tau
Ceti's `Scheme.homOfFunctionField`), and morphisms into separated schemes are determined at the generic point.
This is the universality in Milne, Corollary 7.3.
-/

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace ModularFormsKB.Milne.Completion

variable {k : Type u} [Field k] {U Ubar C : Scheme.{u}}
  [U.Over (Spec (CommRingCat.of k))] [Ubar.Over (Spec (CommRingCat.of k))] [C.Over (Spec (CommRingCat.of k))]
  [IsIntegral U] [IsIntegral Ubar] [IsProper (Ubar ↘ Spec (CommRingCat.of k))]
  [IsProper (C ↘ Spec (CommRingCat.of k))]
  (hU : ∀ x : U, ValuationRing (U.presheaf.stalk x))
  (hUbar : ∀ x : Ubar, ValuationRing (Ubar.presheaf.stalk x))
  (e : Ubar.functionField ≃ₐ[k] U.functionField)

/-- The morphism $U \to \bar U$ induced by $e$. -/
abbrev ι : U ⟶ Ubar := Scheme.homOfFunctionFieldAlgHom hU e.toAlgHom

omit [IsProper (Ubar ↘ Spec (CommRingCat.of k))] [IsProper (C ↘ Spec (CommRingCat.of k))] in
theorem extend_compat (φ : U ⟶ C) [φ.IsOver (Spec (CommRingCat.of k))] :
    (Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫ U.fromSpecStalk (genericPoint U) ≫ φ) ≫
      C ↘ Spec (CommRingCat.of k) = Ubar.fromSpecStalk (genericPoint Ubar) ≫ Ubar ↘ Spec (CommRingCat.of k) := by
  rw [Category.assoc, Category.assoc, comp_over φ, ← Category.assoc]
  exact Scheme.specMap_comp_fromSpecStalk_genericPoint_comp_over (k := k)
    (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) e.symm.commutes

/-- The extension of $\varphi : U \to C$ to $\bar U$. -/
def extend (φ : U ⟶ C) [φ.IsOver (Spec (CommRingCat.of k))] : Ubar ⟶ C :=
  Scheme.homOfFunctionField (S := Spec (CommRingCat.of k)) hUbar
    (Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫ U.fromSpecStalk (genericPoint U) ≫ φ)
    (extend_compat e φ)

theorem fromSpecStalk_ι :
    U.fromSpecStalk (genericPoint U) ≫ ι hU e =
      Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫ Ubar.fromSpecStalk (genericPoint Ubar) :=
  Scheme.fromSpecStalk_homOfFunctionFieldAlgHom hU e.toAlgHom

omit [IsProper (Ubar ↘ Spec (CommRingCat.of k))] in
theorem specMap_comp_specMap_symm :
    Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) =
      𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (e.toAlgHom.toRingHom).comp (e.symm.toAlgHom.toRingHom) = RingHom.id _ := by
    ext x; simp
  rw [h, CommRingCat.ofHom_id, Spec.map_id]

instance : IsIso (Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom)) := by
  refine ⟨⟨Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom), specMap_comp_specMap_symm e, ?_⟩⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (e.symm.toAlgHom.toRingHom).comp (e.toAlgHom.toRingHom) = RingHom.id _ := by
    ext x; simp
  rw [h, CommRingCat.ofHom_id, Spec.map_id]

include hUbar in
/-- **Universal property**: every $k_0$-morphism $\varphi : U \to C$ to a proper $k_0$-scheme extends uniquely along
$\iota : U \to \bar U$. -/
theorem exists_unique_extension (φ : U ⟶ C) [φ.IsOver (Spec (CommRingCat.of k))] :
    ∃! φbar : Ubar ⟶ C, φbar.IsOver (Spec (CommRingCat.of k)) ∧ ι hU e ≫ φbar = φ := by
  have hgen : Ubar.fromSpecStalk (genericPoint Ubar) ≫ extend hUbar e φ =
      Spec.map (CommRingCat.ofHom e.symm.toAlgHom.toRingHom) ≫ U.fromSpecStalk (genericPoint U) ≫ φ :=
    Scheme.fromSpecStalk_homOfFunctionField _ _ _
  refine ⟨extend hUbar e φ, ⟨inferInstanceAs ((Scheme.homOfFunctionField (S := Spec (CommRingCat.of k))
      hUbar _ (extend_compat e φ)).IsOver _), ?_⟩, ?_⟩
  · have : (ι hU e ≫ extend hUbar e φ).IsOver (Spec (CommRingCat.of k)) := by
      have : (extend hUbar e φ).IsOver (Spec (CommRingCat.of k)) :=
        inferInstanceAs ((Scheme.homOfFunctionField (S := Spec (CommRingCat.of k)) hUbar _
          (extend_compat e φ)).IsOver _)
      infer_instance
    refine ext_of_isDominant_of_isSeparated' (Spec (CommRingCat.of k))
      (U.fromSpecStalk (genericPoint U)) ?_
    rw [← Category.assoc, fromSpecStalk_ι, Category.assoc, hgen, ← Category.assoc,
      specMap_comp_specMap_symm]
    exact Category.id_comp _
  · rintro ψ ⟨hψ, hψι⟩
    refine (Scheme.eq_homOfFunctionField_iff (S := Spec (CommRingCat.of k)) hUbar _
      (extend_compat e φ) ψ).2 ?_
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom)), ← Category.assoc,
      ← fromSpecStalk_ι hU, Category.assoc, hψι, ← Category.assoc, ← Category.assoc,
      specMap_comp_specMap_symm]
    exact (Category.id_comp _).symm

end ModularFormsKB.Milne.Completion
