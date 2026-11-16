import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32HeckeAux

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
namespace F32Aux

open GaussianInt
local notation "ℤ[i]" => GaussianInt

/-- The primary Gaussian integers of norm `m`. -/
def S (m : ℕ) : Finset ℤ[i] := (primaryOfNorm m).image (fun v => (⟨v.1, v.2⟩ : ℤ[i]))

theorem mem_S {m : ℕ} {α : ℤ[i]} : α ∈ S m ↔ Prim α ∧ α.norm = m := by
  constructor
  · intro h
    simp only [S, Finset.mem_image, primaryOfNorm, Finset.mem_filter] at h
    obtain ⟨⟨a, c⟩, ⟨_, h1, h2, h3, h4⟩, rfl⟩ := h
    refine ⟨⟨h2, h3, h4⟩, ?_⟩
    simp only [Zsqrtd.norm_def]; nlinarith
  · rintro ⟨⟨h2, h3, h4⟩, hn⟩
    rw [Zsqrtd.norm_def] at hn
    have e1 := Int.le_self_sq α.re
    have e2 := Int.le_self_sq (-α.re)
    have e3 := Int.le_self_sq α.im
    have e4 := Int.le_self_sq (-α.im)
    simp only [S, Finset.mem_image, primaryOfNorm, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    refine ⟨(α.re, α.im), ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, h2, h3, h4⟩, rfl⟩ <;>
      nlinarith [sq_nonneg α.re, sq_nonneg α.im]

theorem re_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[i]) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem im_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[i]) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- `B m = ∑_{α primary, Nα = m} α`. -/
def B (m : ℕ) : ℤ[i] := ∑ α ∈ S m, α

theorem B_re (m : ℕ) : (B m).re = f32Coeff m := by
  unfold B f32Coeff
  rw [re_sum, S, Finset.sum_image]
  intro v _ w _ h
  simp only [Zsqrtd.ext_iff] at h
  exact Prod.ext h.1 h.2

theorem B_im (m : ℕ) : (B m).im = 0 := by
  unfold B
  rw [im_sum]
  have : ∑ α ∈ S m, (star α).im = ∑ α ∈ S m, α.im := by
    refine Finset.sum_nbij' (fun a => star a) (fun a => star a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [mem_S] at *
      exact ⟨ha.1.star, by rw [Zsqrtd.norm_conj]; exact ha.2⟩
    · intro a ha
      rw [mem_S] at *
      exact ⟨ha.1.star, by rw [Zsqrtd.norm_conj]; exact ha.2⟩
    · intro a _; simp
    · intro a _; simp
    · intro a _; simp
  simp only [Zsqrtd.im_star, Finset.sum_neg_distrib] at this
  omega

theorem B_eq (m : ℕ) : B m = ((f32Coeff m : ℤ) : ℤ[i]) := by
  ext
  · simp [B_re]
  · simp [B_im]

theorem S_even {m : ℕ} (h : m % 2 = 0) : S m = ∅ := by
  ext α
  simp only [Finset.notMem_empty, iff_false]
  intro hα
  rw [mem_S] at hα
  have := norm_odd_of_prim hα.1
  rw [hα.2] at this
  omega

theorem f32Coeff_even {m : ℕ} (h : m % 2 = 0) : f32Coeff m = 0 := by
  rw [← B_re, B, S_even h]; simp

theorem S_one : S 1 = {1} := by
  ext α
  rw [mem_S, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact h1.unit_eq (by simpa using h2)
  · rintro rfl
    exact ⟨Prim.one, by simp⟩

theorem B_one : B 1 = 1 := by simp [B, S_one]

end F32Aux
end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
