import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Coefficients
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
namespace F32Aux

open GaussianInt
local notation "ℤ[i]" => GaussianInt

/-- `α ≡ 1 mod (2+2i)`, in coordinates. -/
def Prim (α : ℤ[i]) : Prop := α.re % 2 = 1 ∧ α.im % 2 = 0 ∧ (α.re + α.im) % 4 = 1

instance : DecidablePred Prim := fun α => by unfold Prim; infer_instance

theorem prim_iff_dvd (α : ℤ[i]) : Prim α ↔ (⟨2, 2⟩ : ℤ[i]) ∣ α - 1 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨(α.re - 1 + α.im) / 4, (α.im - α.re + 1) / 4⟩, ?_⟩
    ext <;> simp <;> omega
  · rintro ⟨⟨u, v⟩, h⟩
    have h1 := congrArg Zsqrtd.re h
    have h2 := congrArg Zsqrtd.im h
    simp at h1 h2
    unfold Prim
    omega

theorem Prim.mul {α β : ℤ[i]} (hα : Prim α) (hβ : Prim β) : Prim (α * β) := by
  rw [prim_iff_dvd] at *
  have : α * β - 1 = (α - 1) * β + (β - 1) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left hα _) hβ

theorem Prim.star {α : ℤ[i]} (hα : Prim α) : Prim (star α) := by
  obtain ⟨h1, h2, h3⟩ := hα
  refine ⟨by simpa using h1, by simp; omega, by simp; omega⟩

theorem norm_odd_of_prim {α : ℤ[i]} (hα : Prim α) : α.norm % 2 = 1 := by
  obtain ⟨h1, h2, h3⟩ := hα
  obtain ⟨k, hk⟩ : ∃ k, α.re = 2 * k + 1 := ⟨α.re / 2, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l, α.im = 2 * l := ⟨α.im / 2, by omega⟩
  rw [Zsqrtd.norm_def, hk, hl]
  have : (2 * k + 1) * (2 * k + 1) - -1 * (2 * l) * (2 * l) = 2 * (2 * k * k + 2 * k + 2 * l * l) + 1 := by ring
  omega

theorem Prim.one : Prim 1 := by unfold Prim; simp

theorem Prim.unit_eq {ε : ℤ[i]} (hε : Prim ε) (hn : ε.norm = 1) : ε = 1 := by
  obtain ⟨h1, h2, h3⟩ := hε
  rw [Zsqrtd.norm_def] at hn
  have a1 : ε.re ≤ 1 := by nlinarith [mul_self_nonneg ε.im]
  have a2 : -1 ≤ ε.re := by nlinarith [mul_self_nonneg ε.im]
  have b1 : ε.im ≤ 1 := by nlinarith [mul_self_nonneg ε.re]
  have b2 : -1 ≤ ε.im := by nlinarith [mul_self_nonneg ε.re]
  have : ε.re = 1 ∧ ε.im = 0 := by omega
  ext <;> simp [this.1, this.2]

/-- Division closure: `α = β δ` with `α, β` primary gives `δ` primary. -/
theorem Prim.of_mul {α β δ : ℤ[i]} (hα : Prim α) (hβ : Prim β) (h : α = β * δ) : Prim δ := by
  have hN : (β * Star.star β) * δ = Star.star β * α := by rw [h]; ring
  have hs : Prim (Star.star β * α) := hβ.star.mul hα
  rw [← hN, ← Zsqrtd.norm_eq_mul_conj] at hs
  have hnβ4 : β.norm % 4 = 1 := by
    obtain ⟨h1, h2, h3⟩ := hβ
    obtain ⟨k, hk⟩ : ∃ k, β.re = 2 * k + 1 := ⟨β.re / 2, by omega⟩
    obtain ⟨l, hl⟩ : ∃ l, β.im = 2 * l := ⟨β.im / 2, by omega⟩
    rw [Zsqrtd.norm_def, hk, hl]
    have : (2 * k + 1) * (2 * k + 1) - -1 * (2 * l) * (2 * l) = 4 * (k * k + k + l * l) + 1 := by ring
    omega
  have hs' := (prim_iff_dvd _).1 hs
  rw [prim_iff_dvd]
  have hd : (⟨2, 2⟩ : ℤ[i]) ∣ (((β.norm - 1 : ℤ)) : ℤ[i]) := by
    obtain ⟨q, hq⟩ : ∃ q, β.norm - 1 = 4 * q := ⟨(β.norm - 1) / 4, by omega⟩
    refine ⟨⟨q, -q⟩, ?_⟩
    rw [hq]; ext <;> simp <;> ring
  have : δ - 1 = ((β.norm : ℤ[i]) * δ - 1) - ((β.norm - 1 : ℤ) : ℤ[i]) * δ := by push_cast; ring
  rw [this]
  exact dvd_sub hs' (dvd_mul_of_dvd_left hd _)

end F32Aux
end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
