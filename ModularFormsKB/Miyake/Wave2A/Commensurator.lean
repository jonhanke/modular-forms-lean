import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Commensurable
import ModularFormsKB.Citation
/-!
# Miyake §4.5: the commensurator of a modular group

Miyake, *Modular Forms* (Springer 1989), Lemma 4.5.1, p. 132: for any modular group `Γ`,
`Γ̃ = ℝ^× · GL₂⁺(ℚ)`, where `Γ̃` is the commensurator of `Γ` in `GL₂⁺(ℝ)` (Miyake §2.7).

Here `Γ` is any arithmetic subgroup of `GL₂(ℝ)` (Mathlib's `Subgroup.IsArithmetic`: commensurable
with `SL₂(ℤ)`), which contains the modular groups (finite-index subgroups of `SL₂(ℤ)`), and the
commensurator is Mathlib's `Subgroup.Commensurable.commensurator`. The statement is
(`ModularFormsKB.Miyake.mem_commensurator_iff`): for `α ∈ GL₂(ℝ)` with `det α > 0`,
`α ∈ Γ̃ ↔ α = r β` with `r ∈ ℝ^×` and `β` a rational matrix.

## Proof
`⊇`: Mathlib's `Subgroup.IsArithmetic.conj` (conjugation by `GL₂(ℚ)` preserves arithmeticity;
this is Miyake's `β⁻¹ Γ(m) β ⊆ Γ(1)`), and scalars act trivially by conjugation.

`⊆`: Miyake argues with cusps: `α` maps the cusps `ℚ ∪ {∞}` of `α⁻¹ Γ α` to cusps of `Γ`, so the
ratios of the entries of `α` are rational. Here the same rationality is read off directly from
the finite index: `α⁻¹ Γ(1) α ∩ Γ(1)` has finite index in `Γ(1)`, so it contains powers
`τⁿ = [[1, n], [0, 1]]` and `[[1, 0], [n, 1]]` (`n ≥ 1`), and likewise for `α Γ(1) α⁻¹`; the
integrality of `α⁻¹ τⁿ α` etc. shows that the products `a², b², ab, ac, bd, cd` of the entries
of `α = [[a, b], [c, d]]` are rational multiples of `det α`, which forces all ratios of entries to
be rational.
-/

open Matrix Subgroup ConjAct Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise

namespace ModularFormsKB.Miyake

namespace Commensurator

/-- `[[1, 1], [0, 1]] ∈ SL₂(ℤ)`. -/
def upperT : SL(2, ℤ) := ⟨!![1, 1; 0, 1], by simp [det_fin_two_of]⟩

/-- `[[1, 0], [1, 1]] ∈ SL₂(ℤ)`. -/
def lowerT : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by simp [det_fin_two_of]⟩

lemma upperT_pow (n : ℕ) :
    ((upperT ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (n : ℤ); 0, 1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperT, add_comm]

lemma lowerT_pow (n : ℕ) :
    ((lowerT ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; (n : ℤ), 1] := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, SpecialLinearGroup.coe_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerT, add_comm]

/-- If `α⁻¹ γ α = δ` with `γ, δ ∈ SL₂(ℤ)`, then `det α · δ = adj(α) γ α`. -/
lemma det_mul_conj_left {α : GL (Fin 2) ℝ} {γ δ : SL(2, ℤ)}
    (h : mapGL ℝ δ = α⁻¹ * mapGL ℝ γ * α) :
    (α : Matrix (Fin 2) (Fin 2) ℝ).det • (δ.map (algebraMap ℤ ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      adjugate (α : Matrix (Fin 2) (Fin 2) ℝ) * γ.map (algebraMap ℤ ℝ) *
        (α : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hv := congrArg Units.val h
  simp only [Units.val_mul, mapGL_coe_matrix, coe_units_inv] at hv
  rw [hv, inv_def, Ring.inverse_eq_inv',
    Matrix.smul_mul, Matrix.smul_mul, smul_smul,
    mul_inv_cancel₀ (α.det_ne_zero), one_smul]

/-- If `α γ α⁻¹ = δ` with `γ, δ ∈ SL₂(ℤ)`, then `det α · δ = α γ adj(α)`. -/
lemma det_mul_conj_right {α : GL (Fin 2) ℝ} {γ δ : SL(2, ℤ)}
    (h : mapGL ℝ δ = α * mapGL ℝ γ * α⁻¹) :
    (α : Matrix (Fin 2) (Fin 2) ℝ).det • (δ.map (algebraMap ℤ ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (α : Matrix (Fin 2) (Fin 2) ℝ) * γ.map (algebraMap ℤ ℝ) *
        adjugate (α : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hv := congrArg Units.val h
  simp only [Units.val_mul, mapGL_coe_matrix, coe_units_inv] at hv
  rw [hv, inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ (α.det_ne_zero), one_smul]

/-- An element of the commensurator of `SL₂(ℤ)` conjugates some positive power of any
`γ ∈ SL₂(ℤ)` back into `SL₂(ℤ)`: `α⁻¹ γⁿ α ∈ SL₂(ℤ)`. -/
lemma exists_conj_pow_mem {α : GL (Fin 2) ℝ} (hα : α ∈ Commensurable.commensurator 𝒮ℒ)
    (γ : SL(2, ℤ)) : ∃ n : ℕ, 0 < n ∧ ∃ δ : SL(2, ℤ),
      mapGL ℝ δ = α⁻¹ * mapGL ℝ (γ ^ n) * α := by
  rw [Commensurable.commensurator_mem_iff] at hα
  obtain ⟨n, hn, -, hmem⟩ := exists_pow_mem_of_relIndex_ne_zero hα.1.relIndex_ne_zero
    (MonoidHom.mem_range.2 ⟨γ, rfl⟩)
  refine ⟨n, hn, ?_⟩
  have h1 := (mem_inf.1 hmem).1
  rw [mem_pointwise_smul_iff_inv_smul_mem, ← map_pow] at h1
  obtain ⟨δ, hδ⟩ := h1
  refine ⟨δ, ?_⟩
  rw [hδ, MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]

/-- The rationals inside `ℝ`, as a subfield. -/
noncomputable abbrev ratField : Subfield ℝ := (Rat.castHom ℝ).fieldRange

lemma intCast_mem_ratField (z : ℤ) : (z : ℝ) ∈ ratField := ⟨z, by simp⟩

lemma natCast_mem_ratField (n : ℕ) : (n : ℝ) ∈ ratField := ⟨n, by simp⟩

/-- From `det α · δ = M` entrywise, with `M i j = n x` and `n ≥ 1`: `x / det α` is rational. -/
lemma div_det_mem {D x : ℝ} {n : ℕ} (hn : 0 < n) {z : ℤ} (h : D * z = n * x) (hD : D ≠ 0) :
    x / D ∈ ratField := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : x / D = z / n := by field_simp; linarith
  rw [this]
  exact div_mem (intCast_mem_ratField z) (natCast_mem_ratField n)

/-- The rationality facts behind Lemma 4.5.1 (`⊆`). For `α = [[a, b], [c, d]]` in the
commensurator of `SL₂(ℤ)` with `D = det α`, the numbers `a²/D, b²/D, ab/D, ac/D, bd/D, cd/D` are
rational. -/
lemma products_mem {α : GL (Fin 2) ℝ} (hα : α ∈ Commensurable.commensurator 𝒮ℒ) :
    (α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 / (α : Matrix (Fin 2) (Fin 2) ℝ).det ∈ ratField ∧
    (α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ^ 2 / (α : Matrix (Fin 2) (Fin 2) ℝ).det ∈ ratField ∧
    (α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 /
      (α : Matrix (Fin 2) (Fin 2) ℝ).det ∈ ratField ∧
    (α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 /
      (α : Matrix (Fin 2) (Fin 2) ℝ).det ∈ ratField ∧
    (α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 /
      (α : Matrix (Fin 2) (Fin 2) ℝ).det ∈ ratField ∧
    (α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 /
      (α : Matrix (Fin 2) (Fin 2) ℝ).det ∈ ratField := by
  have hD : (α : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := α.det_ne_zero
  have hdet := det_fin_two (α : Matrix (Fin 2) (Fin 2) ℝ)
  -- `α⁻¹ τⁿ α` and `α⁻¹ [[1, 0], [n, 1]] α` are integral
  obtain ⟨n₁, hn₁, δ₁, h₁⟩ := exists_conj_pow_mem hα upperT
  have e₁ := det_mul_conj_left h₁
  obtain ⟨n₂, hn₂, δ₂, h₂⟩ := exists_conj_pow_mem hα lowerT
  have e₂ := det_mul_conj_left h₂
  -- the same for `α⁻¹`
  have hαi : α⁻¹ ∈ Commensurable.commensurator 𝒮ℒ := inv_mem hα
  obtain ⟨n₃, hn₃, δ₃, h₃⟩ := exists_conj_pow_mem hαi upperT
  rw [inv_inv] at h₃
  have e₃ := det_mul_conj_right h₃
  obtain ⟨n₄, hn₄, δ₄, h₄⟩ := exists_conj_pow_mem hαi lowerT
  rw [inv_inv] at h₄
  have e₄ := det_mul_conj_right h₄
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at e₁ e₂ e₃ e₄
  rw [upperT_pow] at e₁ e₃
  rw [lowerT_pow] at e₂ e₄
  have hU : ∀ n : ℕ, (!![1, (n : ℤ); 0, 1]).map (algebraMap ℤ ℝ) = !![1, (n : ℝ); 0, 1] := by
    intro n; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hL : ∀ n : ℕ, (!![1, 0; (n : ℤ), 1]).map (algebraMap ℤ ℝ) = !![1, 0; (n : ℝ), 1] := by
    intro n; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hU] at e₁ e₃
  rw [hL] at e₂ e₄
  rw [adjugate_fin_two] at e₃ e₄
  have g₁ := congrFun (congrFun e₂ 1) 0
  have g₂ := congrFun (congrFun e₂ 0) 1
  have g₃ := congrFun (congrFun e₂ 0) 0
  have g₄ := congrFun (congrFun e₃ 0) 0
  have g₅ := congrFun (congrFun e₄ 0) 0
  have g₆ := congrFun (congrFun e₁ 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at g₄ g₅
  simp [adjugate_fin_two, mul_apply, Fin.sum_univ_two, vecMul, dotProduct, Matrix.map_apply,
    Matrix.mul_fin_two] at g₁ g₂ g₃ g₄ g₅ g₆
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_det_mem hn₂ (z := δ₂ 1 0) (by linear_combination g₁) hD
  · exact div_det_mem hn₂ (z := -δ₂ 0 1) (by push_cast; linear_combination -g₂) hD
  · exact div_det_mem hn₂ (z := 1 - δ₂ 0 0) (by push_cast; linear_combination -g₃ + hdet) hD
  · exact div_det_mem hn₃ (z := 1 - δ₃ 0 0) (by push_cast; linear_combination -g₄ + hdet) hD
  · exact div_det_mem hn₄ (z := δ₄ 0 0 - 1) (by push_cast; linear_combination g₅ - hdet) hD
  · exact div_det_mem hn₁ (z := δ₁ 0 0 - 1) (by push_cast; linear_combination g₆ - hdet) hD
end Commensurator

open Commensurator in
/-- **Miyake, Lemma 4.5.1.** For a modular group `Γ` (more generally an arithmetic subgroup of
`GL₂(ℝ)`), an element `α ∈ GL₂⁺(ℝ)` commensurates `Γ` if and only if `α ∈ ℝ^× · GL₂⁺(ℚ)`. -/
@[kb "miyake1989" "Lemma 4.5.1, p. 132"]
theorem mem_commensurator_iff (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]
    (α : GL (Fin 2) ℝ) (hα : 0 < (α : Matrix (Fin 2) (Fin 2) ℝ).det) :
    α ∈ Commensurable.commensurator 𝒢 ↔
      ∃ r : ℝ, r ≠ 0 ∧ ∃ β : Matrix (Fin 2) (Fin 2) ℚ,
        (α : Matrix (Fin 2) (Fin 2) ℝ) = r • β.map (Rat.cast : ℚ → ℝ) := by
  rw [Commensurable.eq (IsArithmetic.is_commensurable (𝒢 := 𝒢))]
  set A := (α : Matrix (Fin 2) (Fin 2) ℝ) with hAdef
  have hD : A.det ≠ 0 := hα.ne'
  have hdet : A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := det_fin_two A
  constructor
  · intro hcomm
    obtain ⟨haa, hbb, hab, hac, hbd, hcd⟩ := products_mem hcomm
    by_cases ha : A 0 0 = 0
    · -- `a = 0`: then `b ≠ 0`, and `α = b · [[0, 1], [c/b, d/b]]`
      have hb : A 0 1 ≠ 0 := by
        intro hb; apply hD; rw [hdet, ha, hb]; ring
      have hcb : A 1 0 / A 0 1 ∈ ratField := by
        have : A 1 0 / A 0 1 = -(A 0 1 ^ 2 / A.det)⁻¹ := by
          rw [hdet, ha]; field_simp; ring
        rw [this]; exact neg_mem (inv_mem hbb)
      have hdb : A 1 1 / A 0 1 ∈ ratField := by
        have : A 1 1 / A 0 1 = (A 0 1 * A 1 1 / A.det) / (A 0 1 ^ 2 / A.det) := by
          field_simp
        rw [this]; exact div_mem hbd hbb
      obtain ⟨q₁, hq₁⟩ := hcb
      obtain ⟨q₂, hq₂⟩ := hdb
      refine ⟨A 0 1, hb, !![0, 1; q₁, q₂], ?_⟩
      simp only [Rat.coe_castHom] at hq₁ hq₂
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq₁, hq₂, ha] <;> field_simp
    · -- `a ≠ 0`: `α = a · [[1, b/a], [c/a, d/a]]`
      have hba : A 0 1 / A 0 0 ∈ ratField := by
        have : A 0 1 / A 0 0 = (A 0 0 * A 0 1 / A.det) / (A 0 0 ^ 2 / A.det) := by
          field_simp
        rw [this]; exact div_mem hab haa
      have hca : A 1 0 / A 0 0 ∈ ratField := by
        have : A 1 0 / A 0 0 = (A 0 0 * A 1 0 / A.det) / (A 0 0 ^ 2 / A.det) := by
          field_simp
        rw [this]; exact div_mem hac haa
      have hda : A 1 1 / A 0 0 ∈ ratField := by
        by_cases hc : A 1 0 = 0
        · have : A 1 1 / A 0 0 = (A 0 0 ^ 2 / A.det)⁻¹ := by
            rw [hdet, hc]; field_simp; ring
          rw [this]; exact inv_mem haa
        · have : A 1 1 / A 0 0 = (A 1 0 * A 1 1 / A.det) / (A 0 0 * A 1 0 / A.det) := by
            field_simp
          rw [this]; exact div_mem hcd hac
      obtain ⟨q₁, hq₁⟩ := hba
      obtain ⟨q₂, hq₂⟩ := hca
      obtain ⟨q₃, hq₃⟩ := hda
      refine ⟨A 0 0, ha, !![1, q₁; q₂, q₃], ?_⟩
      simp only [Rat.coe_castHom] at hq₁ hq₂ hq₃
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq₁, hq₂, hq₃] <;> field_simp
  · rintro ⟨r, hr, β, hβ⟩
    have hdetβ : β.det ≠ 0 := by
      intro h0
      apply hD
      have hm := RingHom.map_det (Rat.castHom ℝ) β
      simp only [RingHom.mapMatrix_apply, Rat.coe_castHom] at hm
      rw [hβ, det_smul, ← hm, h0]
      simp
    -- `α = s g` with `s = r · 1` central and `g ∈ GL₂(ℚ)`
    set g : GL (Fin 2) ℚ := GeneralLinearGroup.mkOfDetNeZero β hdetβ
    set s : GL (Fin 2) ℝ := GeneralLinearGroup.mkOfDetNeZero (r • 1) (by simp [hr])
    have hαsg : α = s * g.map (Rat.castHom ℝ) := by
      ext i j
      simp [s, g, hβ, ← hAdef]
    rw [hαsg]
    refine mul_mem ?_ ?_
    · rw [Commensurable.commensurator_mem_iff]
      have hconj : MulAut.conj s = 1 := by
        ext x : 1
        rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
        ext i j
        simp [s]
      rw [hconj, one_smul]
    · rw [Commensurable.commensurator_mem_iff]
      have h := (CongruenceSubgroup.isArithmetic_conj_SL2Z g).is_commensurable
      have hbridge : toConjAct (g.map (Rat.castHom ℝ)) • 𝒮ℒ =
          MulAut.conj (g.map (Rat.castHom ℝ)) • 𝒮ℒ := by
        ext x
        rw [mem_pointwise_smul_iff_inv_smul_mem, mem_pointwise_smul_iff_inv_smul_mem,
          ← map_inv MulAut.conj, ← toConjAct_inv, toConjAct_smul_eq_mulAut_conj]
        rw [MulAut.smul_def]
      rwa [hbridge] at h

end ModularFormsKB.Miyake
