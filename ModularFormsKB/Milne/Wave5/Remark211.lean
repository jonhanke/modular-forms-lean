import ModularFormsKB.Milne.Ch2.ModularGroup
import ModularFormsKB.Milne.Citations
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Milne, Remark 2.11: cusps and elliptic points of a subgroup of finite index

The first two claims of Remark 2.11 (the cusps of `Γ(1)` are `ℚ ∪ {∞}`, all equivalent to `∞`; every elliptic point of
`Γ(1)` is equivalent to exactly one of `i` and `ρ`) are `isCusp_SL2Z_iff_and_equiv_infty` and `isEllipticPoint_SL2Z_iff`.
Here is the last paragraph: for a subgroup `Γ` of finite index in `Γ(1)`, the cusps of `Γ` are those of `Γ(1)`, namely
`ℚ ∪ {∞}`; every elliptic point of `Γ` is an elliptic point of `Γ(1)`; and a point is an elliptic point of `Γ` exactly
when it is fixed by an element of `Γ` other than `±I` (the book states the last for elliptic points of `Γ(1)`; it holds
for every point of `ℍ`). The book's remark that the cusps "in general fall into more than one `Γ`-orbit" is an
observation, not a claim, and is not formalized.

The key fact is that a matrix of `SL₂(ℝ)` other than `±I` with a fixed point in `ℍ` is elliptic (Mathlib:
`UpperHalfPlane.isElliptic_of_exists_smul_eq_self`). Cusps: Mathlib `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`.
-/

open Matrix MatrixGroups UpperHalfPlane

namespace ModularFormsKB.Milne.Wave5

/-- A matrix of `SL₂(ℝ)` other than `±I` fixing a point of `ℍ` is elliptic. -/
theorem isElliptic_of_smul_eq_self_SL2R {g : SL(2, ℝ)} (h1 : g ≠ 1) (h2 : g ≠ -1) {z : ℍ} (hz : g • z = z) :
    (g : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic := by
  have hdet : 0 < (SpecialLinearGroup.mapGL ℝ g).val.det := by simp
  have hc : SpecialLinearGroup.mapGL ℝ g ∉ Subgroup.center (GL (Fin 2) ℝ) := by
    intro hmem
    obtain ⟨a, ha⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hmem
    have hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) a := by
      rw [ha]; simp
    have hd := g.det_coe
    rw [hg] at hd
    simp at hd
    rcases hd with rfl | rfl
    · apply h1; ext i j; rw [hg]; fin_cases i <;> fin_cases j <;> simp
    · apply h2; ext i j; rw [hg]; fin_cases i <;> fin_cases j <;> simp
  have := isElliptic_of_exists_smul_eq_self hdet hc ⟨z, hz⟩
  have e : ((SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = g := by
    ext i j; simp [SpecialLinearGroup.mapGL]
  have h' : ((SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).IsElliptic := this
  rwa [e] at h'

/-- The image of a subgroup of `SL₂(ℤ)` in `SL₂(ℝ)`. -/
noncomputable abbrev subgroupInSL2R (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℝ) :=
  Γ.map (SpecialLinearGroup.map (Int.castRingHom ℝ))

/-- **Milne, Remark 2.11** (pdf p. 31), last paragraph: let `Γ` be a subgroup of finite index of `Γ(1) = SL₂(ℤ)`.
(i) The cusps of `Γ` are the cusps of `Γ(1)`, namely the points of `ℚ ∪ {∞} = ℙ¹(ℚ)`. (ii) Every elliptic point of
`Γ` is an elliptic point of `Γ(1)`. (iii) A point of `ℍ` is an elliptic point of `Γ` if and only if it is fixed by an
element of `Γ` other than `±I`. -/
@[kb "milne2017mf" "Remark 2.11: cusps and elliptic points of a subgroup of finite index, pdf p. 31"]
theorem remark_2_11_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    (∀ c : OnePoint ℝ, IsCusp c (Γ : Subgroup (GL (Fin 2) ℝ)) ↔ IsCusp c 𝒮ℒ) ∧
    (∀ c : OnePoint ℝ, IsCusp c (Γ : Subgroup (GL (Fin 2) ℝ)) ↔
      c ∈ Set.range (OnePoint.map ((↑) : ℚ → ℝ))) ∧
    (∀ z : ℍ, IsEllipticPoint (subgroupInSL2R Γ) z → IsEllipticPoint SL2ZinSL2R z) ∧
    (∀ z : ℍ, IsEllipticPoint (subgroupInSL2R Γ) z ↔ ∃ γ ∈ Γ, γ ≠ 1 ∧ γ ≠ -1 ∧ γ • z = z) := by
  refine ⟨fun c ↦ Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _,
    fun c ↦ (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).trans isCusp_SL2Z_iff, ?_, ?_⟩
  · rintro z ⟨g, hg, hell, hfix⟩
    exact ⟨g, Subgroup.map_le_range _ _ hg, hell, hfix⟩
  · intro z
    constructor
    · rintro ⟨g, ⟨γ, hγ, rfl⟩, hell, hfix⟩
      exact ⟨γ, hγ, (Remark211.ne_of_isElliptic hell).1, (Remark211.ne_of_isElliptic hell).2,
        by rwa [Remark211.map_smul'] at hfix⟩
    · rintro ⟨γ, hγ, h1, h2, hfix⟩
      have hinj : Function.Injective (SpecialLinearGroup.map (Int.castRingHom ℝ) : SL(2, ℤ) →* SL(2, ℝ)) := by
        intro a b hab
        ext i j
        have := congrArg (fun g : SL(2, ℝ) ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) i j) hab
        simpa using this
      refine ⟨SpecialLinearGroup.map (Int.castRingHom ℝ) γ, ⟨γ, hγ, rfl⟩,
        isElliptic_of_smul_eq_self_SL2R ?_ ?_ (z := z) (by rwa [Remark211.map_smul']), by
          rwa [Remark211.map_smul']⟩
      · intro h; apply h1; apply hinj; rw [h, map_one]
      · intro h; apply h2; apply hinj; rw [h]; ext i j; simp

end ModularFormsKB.Milne.Wave5
