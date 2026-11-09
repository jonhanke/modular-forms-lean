import ModularFormsKB.Milne.Ch11.TwistAut
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Fixed fields of the groups $\Gamma \otimes R$ in a constant field extension

Let $F/k$ be a function field with $k$ exact, $F' = F \cdot k'$ a finite separable constant field extension, and
$\Gamma$ a finite group of $k$-automorphisms of $F$. The group $\Omega = \Gamma \otimes \mathrm{Gal}(k'/k)$
(`twistGroup Γ ⊤`, image of $\Gamma \times \mathrm{Gal}(k'/k)$ under `twistAutHom`) has order
$|\Gamma| [k':k]$, and its fixed field is the image of $F^\Gamma$ (`fixedField_twistGroup_top`): the image is
contained in it, and $F'$ is spanned over the image by the $|\Gamma| [k':k]$ products $e_j b_i$ ($e_j$ a basis of
$F/F^\Gamma$, $b_i$ a basis of $k'/k$), so `IntermediateField.eq_of_le_of_finrank_le'` applies.
-/

open TauCeti Module IntermediateField

namespace ModularFormsKB.Milne

variable {k : Type*} {k' : Type*} {F : Type*} {F' : Type*}
  [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k']
  (hex : IsIntegrallyClosedIn k F) (h : constantCompositum F k' F' = ⊤)

/-- The group $\Gamma \otimes R$ of automorphisms of $F'$. -/
noncomputable def twistGroup (Γ : Subgroup (F ≃ₐ[k] F)) (R : Subgroup (k' ≃ₐ[k] k')) :
    Subgroup (F' ≃ₐ[k] F') :=
  (Γ.prod R).map (twistAutHom hex h)

theorem twistAut_mem_twistGroup {Γ : Subgroup (F ≃ₐ[k] F)} {R : Subgroup (k' ≃ₐ[k] k')} {τ : F ≃ₐ[k] F}
    {ρ : k' ≃ₐ[k] k'} (hτ : τ ∈ Γ) (hρ : ρ ∈ R) : twistAut hex h τ ρ ∈ twistGroup hex h Γ R :=
  ⟨(τ, ρ), ⟨hτ, hρ⟩, rfl⟩

theorem mem_twistGroup_iff {Γ : Subgroup (F ≃ₐ[k] F)} {R : Subgroup (k' ≃ₐ[k] k')} (σ : F' ≃ₐ[k] F') :
    σ ∈ twistGroup hex h Γ R ↔ ∃ τ ∈ Γ, ∃ ρ ∈ R, σ = twistAut hex h τ ρ := by
  constructor
  · rintro ⟨⟨τ, ρ⟩, ⟨hτ, hρ⟩, rfl⟩
    exact ⟨τ, hτ, ρ, hρ, rfl⟩
  · rintro ⟨τ, hτ, ρ, hρ, rfl⟩
    exact twistAut_mem_twistGroup hex h hτ hρ

theorem card_twistGroup (Γ : Subgroup (F ≃ₐ[k] F)) (R : Subgroup (k' ≃ₐ[k] k')) :
    Nat.card (twistGroup hex h Γ R) = Nat.card Γ * Nat.card R := by
  rw [twistGroup, Subgroup.card_map_of_injective (injective_twistAutHom hex h),
    Nat.card_congr (Subgroup.prodEquiv Γ R).toEquiv, Nat.card_prod]

theorem finite_twistGroup [FiniteDimensional k k'] (Γ : Subgroup (F ≃ₐ[k] F)) [Finite Γ]
    (R : Subgroup (k' ≃ₐ[k] k')) : Finite (twistGroup hex h Γ R) := by
  have : Finite (Γ.prod R) := by
    have : Finite (k' ≃ₐ[k] k') := inferInstance
    exact Finite.of_equiv _ (Subgroup.prodEquiv Γ R).symm.toEquiv
  exact Finite.Set.finite_image _ _

include hex h in
/-- $[F' : F] = [k' : k]$. -/
theorem finrank_eq_of_constantCompositum_eq_top [FiniteDimensional k k'] :
    finrank F F' = finrank k k' := by
  rw [finrank_eq_card_basis (constantBasis hex h (Module.finBasis k k')), Fintype.card_fin]

/-- **The fixed field of $\Gamma \otimes \mathrm{Gal}(k'/k)$ is the image of $F^\Gamma$.** -/
theorem fixedField_twistGroup_top [Finite k'] [FiniteDimensional k k'] (Γ : Subgroup (F ≃ₐ[k] F)) [Finite Γ] :
    (fixedField Γ).map (IsScalarTower.toAlgHom k F F') = fixedField (twistGroup hex h Γ ⊤) := by
  classical
  set ι := IsScalarTower.toAlgHom k F F' with hι
  set C := (fixedField Γ).map ι
  set M := fixedField (twistGroup hex h Γ ⊤)
  have hle : C ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    refine (mem_fixedField_iff _ _).mpr fun σ hσ => ?_
    obtain ⟨τ, hτ, ρ, -, rfl⟩ := (mem_twistGroup_iff hex h σ).mp hσ
    have : τ x = x := (mem_fixedField_iff _ _).mp hx τ hτ
    change twistAut hex h τ ρ (algebraMap F F' x) = algebraMap F F' x
    rw [twistAut_algebraMap_left, this]
  -- a spanning family of `F'` over `C`
  have : FiniteDimensional (fixedField Γ) F := inferInstanceAs (FiniteDimensional (FixedPoints.subfield Γ F) F)
  let e := Module.finBasis (fixedField Γ) F
  let b := Module.finBasis k k'
  let v : Fin (finrank (fixedField Γ) F) × Fin (finrank k k') → F' :=
    fun p => algebraMap F F' (e p.1) * algebraMap k' F' (b p.2)
  have hspan : Submodule.span C (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    let bF := constantBasis hex h b
    rw [← bF.sum_repr y]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← e.sum_repr (bF.repr y i), Algebra.smul_def, map_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hc : algebraMap F F' (algebraMap (fixedField Γ) F (e.repr (bF.repr y i) j)) ∈ C :=
      ⟨_, (e.repr (bF.repr y i) j).2, rfl⟩
    have : algebraMap F F' ((e.repr (bF.repr y i) j) • e j) * bF i =
        (⟨_, hc⟩ : C) • v (j, i) := by
      rw [Algebra.smul_def, map_mul, constantBasis_apply]
      simp only [v]
      rw [Subalgebra.smul_def]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, i), rfl⟩)
  have hfdC : FiniteDimensional C F' :=
    Module.Finite.of_fg_top ⟨(Finset.univ.image v), by rw [Finset.coe_image, Finset.coe_univ,
      Set.image_univ, hspan]⟩
  have hC : finrank C F' ≤ finrank (fixedField Γ) F * finrank k k' := by
    have := finrank_range_le_card (R := C) (b := v)
    unfold Set.finrank at this
    rw [hspan, finrank_top, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    exact this
  have hfinΩ := finite_twistGroup hex h Γ ⊤
  have := Fintype.ofFinite (twistGroup hex h Γ ⊤)
  have hM : finrank M F' = Nat.card Γ * finrank k k' := by
    have := FixedPoints.finrank_eq_card (twistGroup hex h Γ ⊤) F'
    rw [← Nat.card_eq_fintype_card, card_twistGroup, Subgroup.card_top,
      IsGalois.card_aut_eq_finrank] at this
    exact this
  have hΓ : finrank (fixedField Γ) F = Nat.card Γ := by
    have := Fintype.ofFinite Γ
    have := FixedPoints.finrank_eq_card Γ F
    rw [← Nat.card_eq_fintype_card] at this
    exact this
  exact eq_of_le_of_finrank_le' hle (by rw [hM, ← hΓ]; exact hC)

end ModularFormsKB.Milne
