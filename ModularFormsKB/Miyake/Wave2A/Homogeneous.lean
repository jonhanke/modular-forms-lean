import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import ModularFormsKB.Citation
/-!
# Miyake §1.2: homogeneous spaces

Miyake, *Modular Forms* (Springer 1989), §1.2, p. 6.

* Theorem 1.2.1: if a locally compact topological group `G` with a countable basis acts
  continuously and transitively on a locally compact Hausdorff space `X`, then for every `x : X`
  the map `g G_x ↦ g x` is a homeomorphism `G / G_x ≃ₜ X`
  (`ModularFormsKB.Miyake.quotientStabilizerHomeomorph`).
* Corollary 1.2.2: `SL₂(ℝ) / SO₂(ℝ) ≃ₜ ℍ` by `α SO₂(ℝ) ↦ α i`
  (`ModularFormsKB.Miyake.SL2RQuotientSO2Homeomorph`), where `SO₂(ℝ)` is the subgroup
  `{α | αᵀ α = 1}` of `SL₂(ℝ)` (`ModularFormsKB.Miyake.SO2`), shown to be the stabilizer of `i`.

Miyake proves the openness of the orbit map by a Baire category argument; Mathlib's
`isOpenMap_smul_of_sigmaCompact` is that argument (a locally compact second countable group is
sigma-compact, and a locally compact Hausdorff space is a Baire space).
-/

open MulAction Topology Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ModularFormsKB.Miyake

section General

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [MulAction G X] [ContinuousSMul G X] [IsPretransitive G X]

/-- **Miyake, Theorem 1.2.1.** A locally compact group with a countable basis acting
continuously and transitively on a locally compact Hausdorff space `X`: for each `x : X` the
correspondence `g G_x ↦ g x` is a homeomorphism `G / G_x ≃ₜ X`. -/
@[kb "miyake1989" "Theorem 1.2.1, p. 6"]
noncomputable def quotientStabilizerHomeomorph (x : X) : G ⧸ stabilizer G x ≃ₜ X where
  toFun := ofQuotientStabilizer G x
  invFun := Function.surjInv (f := ofQuotientStabilizer G x) (by
    intro y
    obtain ⟨g, rfl⟩ := exists_smul_eq G x y
    exact ⟨QuotientGroup.mk g, rfl⟩)
  left_inv := Function.leftInverse_surjInv
    ⟨injective_ofQuotientStabilizer G x, fun y => by
      obtain ⟨g, rfl⟩ := exists_smul_eq G x y
      exact ⟨QuotientGroup.mk g, rfl⟩⟩
  right_inv := Function.rightInverse_surjInv _
  continuous_toFun := by
    refine (QuotientGroup.isQuotientMap_mk (stabilizer G x)).continuous_iff.2 ?_
    exact continuous_id.smul continuous_const
  continuous_invFun := by
    -- the inverse is continuous because the forward map is open
    have hopen : IsOpenMap (ofQuotientStabilizer G x) := by
      intro U hU
      have hpre : IsOpen ((QuotientGroup.mk : G → G ⧸ stabilizer G x) ⁻¹' U) :=
        hU.preimage QuotientGroup.continuous_mk
      have himg := isOpenMap_smul_of_sigmaCompact (G := G) x _ hpre
      convert himg using 1
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        exact ⟨g, hq, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨QuotientGroup.mk g, hg, rfl⟩
    rw [continuous_iff_isClosed]
    intro s hs
    have hbij : Function.Bijective (ofQuotientStabilizer G x) :=
      ⟨injective_ofQuotientStabilizer G x, fun y => by
        obtain ⟨g, rfl⟩ := exists_smul_eq G x y
        exact ⟨QuotientGroup.mk g, rfl⟩⟩
    let e := Equiv.ofBijective _ hbij
    have hinv : Function.surjInv hbij.2 = e.symm := by
      funext y
      apply hbij.1
      rw [Function.surjInv_eq hbij.2]
      exact (e.apply_symm_apply y).symm
    have : (Function.surjInv hbij.2) ⁻¹' s = (ofQuotientStabilizer G x) '' s := by
      rw [hinv, ← Equiv.image_eq_preimage_symm]
      rfl
    rw [this]
    have hc : IsOpen ((ofQuotientStabilizer G x) '' sᶜ) := hopen _ hs.isOpen_compl
    rw [Set.image_compl_eq hbij] at hc
    exact isOpen_compl_iff.1 hc

@[simp]
lemma quotientStabilizerHomeomorph_mk (x : X) (g : G) :
    quotientStabilizerHomeomorph x (QuotientGroup.mk g : G ⧸ stabilizer G x) = g • x :=
  rfl

end General

/-! ### Corollary 1.2.2 -/

namespace SL2R

instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))

instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))

instance : LocallyCompactSpace SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance : SecondCountableTopology SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.secondCountableTopology

end SL2R

/-- The special orthogonal group `SO₂(ℝ) = {α ∈ SL₂(ℝ) | αᵀ α = 1}` as a subgroup of `SL₂(ℝ)`. -/
def SO2 : Subgroup SL(2, ℝ) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * g = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul] at *
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((a : Matrix (Fin 2) (Fin 2) ℝ)ᵀ), ha,
      Matrix.one_mul, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    -- `a⁻¹ = adj a = aᵀ`, and `a aᵀ = 1` follows from `aᵀ a = 1`
    have hcomm : (a : Matrix (Fin 2) (Fin 2) ℝ) * (a : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 1 :=
      _root_.mul_eq_one_comm.1 ha
    have hadj : ((a⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = (a : Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by
      rw [Matrix.SpecialLinearGroup.coe_inv]
      calc adjugate (a : Matrix (Fin 2) (Fin 2) ℝ)
          = adjugate (a : Matrix (Fin 2) (Fin 2) ℝ) * ((a : Matrix (Fin 2) (Fin 2) ℝ) *
              (a : Matrix (Fin 2) (Fin 2) ℝ)ᵀ) := by rw [hcomm, Matrix.mul_one]
        _ = (a : Matrix (Fin 2) (Fin 2) ℝ)ᵀ := by
              rw [← Matrix.mul_assoc, Matrix.adjugate_mul, a.det_coe, one_smul, Matrix.one_mul]
    rw [hadj, Matrix.transpose_transpose, hcomm]

/-- Membership in `SO₂(ℝ)` in coordinates: `α = [[a, b], [c, d]]` with `a = d` and `b = -c`. -/
lemma mem_SO2_iff (g : SL(2, ℝ)) : g ∈ SO2 ↔ g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0 := by
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  change (g : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * g = 1 ↔ _
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h11 := congrFun (congrFun h 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
    -- a² + c² = 1, ab + cd = 0, b² + d² = 1, ad - bc = 1
    constructor <;> nlinarith [sq_nonneg (g 0 0 - g 1 1), sq_nonneg (g 0 1 + g 1 0)]
  · rintro ⟨h1, h2⟩
    rw [h1, h2] at hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2] <;> nlinarith [hdet]

/-- `SO₂(ℝ)` is the stabilizer of `i` in `SL₂(ℝ)` (Theorem 1.1.3 in Miyake's proof). -/
lemma stabilizer_I_eq_SO2 : stabilizer SL(2, ℝ) I = SO2 := by
  ext g
  rw [mem_stabilizer_iff, mem_SO2_iff, UpperHalfPlane.ext_iff, coe_specialLinearGroup_apply]
  have hdet := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  simp only [Algebra.algebraMap_self, RingHom.id_apply, coe_I]
  have hden : ((g 1 0 : ℝ) : ℂ) * Complex.I + ((g 1 1 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    rw [h1, h2] at hdet
    simp at hdet
  rw [div_eq_iff hden]
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    apply Complex.ext <;> simp [h1, h2]

/-- `quotientStabilizerHomeomorph` for a subgroup equal to the stabilizer. -/
noncomputable def quotientHomeomorphOfEq {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [MulAction G X] [ContinuousSMul G X] [IsPretransitive G X]
    (x : X) (H : Subgroup G) (hH : H = stabilizer G x) : G ⧸ H ≃ₜ X := by
  subst hH
  exact quotientStabilizerHomeomorph x

lemma quotientHomeomorphOfEq_mk {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [MulAction G X] [ContinuousSMul G X] [IsPretransitive G X]
    (x : X) (H : Subgroup G) (hH : H = stabilizer G x) (g : G) :
    quotientHomeomorphOfEq x H hH (QuotientGroup.mk g) = g • x := by
  subst hH
  rfl

/-- **Miyake, Corollary 1.2.2.** The coset space `SL₂(ℝ) / SO₂(ℝ)` is homeomorphic to `ℍ` by
`α SO₂(ℝ) ↦ α i`. -/
@[kb "miyake1989" "Corollary 1.2.2, p. 6"]
noncomputable def SL2RQuotientSO2Homeomorph : SL(2, ℝ) ⧸ SO2 ≃ₜ ℍ :=
  quotientHomeomorphOfEq I SO2 stabilizer_I_eq_SO2.symm

@[kb "miyake1989" "Corollary 1.2.2, p. 6"]
lemma SL2RQuotientSO2Homeomorph_mk (g : SL(2, ℝ)) :
    SL2RQuotientSO2Homeomorph (QuotientGroup.mk g) = g • I :=
  quotientHomeomorphOfEq_mk I SO2 _ g

end ModularFormsKB.Miyake
