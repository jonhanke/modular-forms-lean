import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32HeckeAux2
import Mathlib.NumberTheory.SumTwoSquares

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
namespace F32Aux

open GaussianInt
local notation "ℤ[i]" => GaussianInt

theorem prime_of_norm_prime {π : ℤ[i]} {p : ℕ} (hp : p.Prime) (h : π.norm = p) : Prime π := by
  apply Irreducible.prime
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro hu
    have := Zsqrtd.norm_eq_one_iff.2 hu
    rw [h] at this
    simp at this
    exact hp.one_lt.ne' this
  · intro a b hab
    have h1 : π.norm = a.norm * b.norm := by rw [hab, Zsqrtd.norm_mul]
    have h2 : p = a.norm.natAbs * b.norm.natAbs := by
      have := congrArg Int.natAbs h1
      rw [h] at this
      simpa [Int.natAbs_mul] using this
    have hp' : (a.norm.natAbs * b.norm.natAbs).Prime := by rw [← h2]; exact hp
    rcases Nat.prime_mul_iff.1 hp' with ⟨_, h3⟩ | ⟨_, h3⟩
    · right; exact Zsqrtd.norm_eq_one_iff.1 h3
    · left; exact Zsqrtd.norm_eq_one_iff.1 h3

theorem dvd_or {π α : ℤ[i]} {p n : ℕ} (hπ : Prime π) (hn : π.norm = p)
    (hα : α.norm = ((p * n : ℕ) : ℤ)) : π ∣ α ∨ star π ∣ α := by
  have h0 := Zsqrtd.norm_eq_mul_conj π
  rw [hn] at h0
  have h1 : α * star α = π * (star π * (n : ℤ[i])) := by
    rw [← Zsqrtd.norm_eq_mul_conj, hα]
    push_cast at h0 ⊢
    rw [h0, mul_assoc]
  rcases hπ.dvd_or_dvd ⟨_, h1⟩ with h | ⟨c, hc⟩
  · exact Or.inl h
  · right
    refine ⟨star c, ?_⟩
    have := congrArg star hc
    simpa [star_mul'] using this

theorem S_dvd {π α : ℤ[i]} {p n : ℕ} (hp : p ≠ 0) (hπ : Prim π) (hn : π.norm = p) :
    (α ∈ S (p * n) ∧ π ∣ α) ↔ ∃ δ ∈ S n, π * δ = α := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  constructor
  · rintro ⟨hα, c, rfl⟩
    rw [mem_S] at hα
    refine ⟨c, ?_, rfl⟩
    rw [mem_S]
    refine ⟨Prim.of_mul hα.1 hπ rfl, ?_⟩
    have := hα.2
    rw [Zsqrtd.norm_mul, hn] at this
    push_cast at this
    exact Int.eq_of_mul_eq_mul_left hp0 this
  · rintro ⟨δ, hδ, rfl⟩
    rw [mem_S] at hδ
    refine ⟨?_, Dvd.intro _ rfl⟩
    rw [mem_S]
    refine ⟨hπ.mul hδ.1, ?_⟩
    rw [Zsqrtd.norm_mul, hn, hδ.2]
    push_cast; rfl

theorem not_dvd_star {π : ℤ[i]} {p : ℕ} (hp : p.Prime) (hπ : Prim π) (hn : π.norm = p) :
    ¬ π ∣ star π := by
  rintro ⟨δ, hδ⟩
  have hδp : Prim δ := Prim.of_mul hπ.star hπ hδ
  have h1 : δ.norm = 1 := by
    have := congrArg Zsqrtd.norm hδ
    rw [Zsqrtd.norm_conj, Zsqrtd.norm_mul, hn] at this
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (p : ℤ) * 1 = p * δ.norm := by rw [mul_one]; exact this
    exact (Int.eq_of_mul_eq_mul_left hp0 this).symm
  have := hδp.unit_eq h1
  rw [this, mul_one] at hδ
  have him : π.im = 0 := by
    have := congrArg Zsqrtd.im hδ
    simp at this
    omega
  rw [Zsqrtd.norm_def, him] at hn
  have h2 : (p : ℤ) = π.re * π.re := by rw [← hn]; ring
  have h3 : p = π.re.natAbs * π.re.natAbs := by
    have := congrArg Int.natAbs h2
    simpa [Int.natAbs_mul] using this
  have hp' : (π.re.natAbs * π.re.natAbs).Prime := by rw [← h3]; exact hp
  rcases Nat.prime_mul_iff.1 hp' with ⟨_, h4⟩ | ⟨_, h4⟩
  · rw [h4] at h3; exact hp.one_lt.ne' (by omega)
  · rw [h4] at h3; exact hp.one_lt.ne' (by omega)

theorem inter_aux {π α : ℤ[i]} {p n : ℕ} (hp : p.Prime) (hπ : Prim π) (hn : π.norm = p)
    (h1 : α ∈ (S n).image (π * ·)) (h2 : α ∈ (S n).image (star π * ·)) :
    ∃ ε : ℤ[i], Prim ε ∧ (n : ℤ) = p * ε.norm ∧ (p : ℤ[i]) * ε = α := by
  have hprime := prime_of_norm_prime hp hn
  obtain ⟨δ, hδ, e⟩ := Finset.mem_image.1 h1
  obtain ⟨δ', hδ', e'⟩ := Finset.mem_image.1 h2
  have hd : π ∣ star π * δ' := ⟨δ, by rw [e', e]⟩
  rcases hprime.dvd_or_dvd hd with h | ⟨ε, hε⟩
  · exact absurd h (not_dvd_star hp hπ hn)
  · have hδ'm := mem_S.1 hδ'
    refine ⟨ε, Prim.of_mul hδ'm.1 hπ hε, ?_, ?_⟩
    · have := hδ'm.2
      rw [hε, Zsqrtd.norm_mul, hn] at this
      exact this.symm
    · have h0 := Zsqrtd.norm_eq_mul_conj π
      rw [hn] at h0
      push_cast at h0
      rw [← e', hε, h0]; ring

theorem S_split {π : ℤ[i]} {p : ℕ} (hp : p.Prime) (hπ : Prim π) (hn : π.norm = p) (n : ℕ) :
    S (p * n) = (S n).image (π * ·) ∪ (S n).image (star π * ·) := by
  have hπ' : Prim (star π) := hπ.star
  have hn' : (star π).norm = p := by rw [Zsqrtd.norm_conj]; exact hn
  have hprime := prime_of_norm_prime hp hn
  ext α
  rw [Finset.mem_union]
  constructor
  · intro hα
    have h := dvd_or hprime hn (mem_S.1 hα).2
    rcases h with h | h
    · left
      obtain ⟨δ, hδ, e⟩ := (S_dvd hp.ne_zero hπ hn).1 ⟨hα, h⟩
      exact Finset.mem_image.2 ⟨δ, hδ, e⟩
    · right
      obtain ⟨δ, hδ, e⟩ := (S_dvd hp.ne_zero hπ' hn').1 ⟨hα, h⟩
      exact Finset.mem_image.2 ⟨δ, hδ, e⟩
  · rintro (h | h)
    · obtain ⟨δ, hδ, e⟩ := Finset.mem_image.1 h
      exact ((S_dvd hp.ne_zero hπ hn).2 ⟨δ, hδ, e⟩).1
    · obtain ⟨δ, hδ, e⟩ := Finset.mem_image.1 h
      exact ((S_dvd hp.ne_zero hπ' hn').2 ⟨δ, hδ, e⟩).1

theorem hecke_split {π : ℤ[i]} {p : ℕ} (hp : p.Prime) (hπ : Prim π) (hn : π.norm = p) (n : ℕ) :
    B (p * n) + (if p ∣ n then (p : ℤ[i]) * B (n / p) else 0) = π * B n + star π * B n := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have : (0 : ℤ[i]).norm = 0 := by simp
    rw [this] at hn
    exact hp.ne_zero (by exact_mod_cast hn.symm)
  have hπ0' : star π ≠ 0 := by
    intro h
    apply hπ0
    simpa using congrArg star h
  have hpp : Prim (π * star π) := by
    refine hπ.mul hπ.star
  have hpC : (p : ℤ[i]) = π * star π := by
    have h0 := Zsqrtd.norm_eq_mul_conj π
    rw [hn] at h0
    simpa using h0
  have hI : (S n).image (π * ·) ∩ (S n).image (star π * ·) =
      if p ∣ n then (S (n / p)).image ((p : ℤ[i]) * ·) else ∅ := by
    ext α
    rw [Finset.mem_inter]
    by_cases hd : p ∣ n
    · obtain ⟨k, rfl⟩ := hd
      rw [if_pos (dvd_mul_right p k), Nat.mul_div_cancel_left k hp.pos]
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨ε, hε, hne, e⟩ := inter_aux hp hπ hn h1 h2
        refine Finset.mem_image.2 ⟨ε, ?_, e⟩
        rw [mem_S]
        refine ⟨hε, ?_⟩
        have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        push_cast at hne
        exact (Int.eq_of_mul_eq_mul_left hp0 hne).symm
      · intro h
        obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.1 h
        rw [mem_S] at hε
        have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        constructor
        · refine Finset.mem_image.2 ⟨star π * ε, ?_, ?_⟩
          · rw [mem_S]
            refine ⟨hπ.star.mul hε.1, ?_⟩
            rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, hn, hε.2]
            exact (Nat.cast_mul p k).symm
          · rw [← mul_assoc, ← hpC]
        · refine Finset.mem_image.2 ⟨π * ε, ?_, ?_⟩
          · rw [mem_S]
            refine ⟨hπ.mul hε.1, ?_⟩
            rw [Zsqrtd.norm_mul, hn, hε.2]
            exact (Nat.cast_mul p k).symm
          · rw [← mul_assoc, mul_comm (star π) π, ← hpC]
    · rw [if_neg hd]
      simp only [Finset.notMem_empty, iff_false, not_and]
      intro h1 h2
      obtain ⟨ε, hε, hne, e⟩ := inter_aux hp hπ hn h1 h2
      apply hd
      refine ⟨ε.norm.toNat, ?_⟩
      have := norm_nonneg ε
      zify
      rw [Int.toNat_of_nonneg this]
      exact hne
  have hsum := Finset.sum_union_inter (s₁ := (S n).image (π * ·))
    (s₂ := (S n).image (star π * ·)) (f := fun α => α)
  rw [← S_split hp hπ hn n, hI, Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hπ0 h),
    Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ hπ0' h)] at hsum
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  unfold B
  rw [← hsum]
  congr 1
  split_ifs
  · rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) h),
      ← Finset.mul_sum]
  · simp

theorem exists_assoc (z : ℤ[i]) (h : z.norm % 2 = 1) : ∃ β : ℤ[i], Prim β ∧ β.norm = z.norm := by
  have hx : (z.re * z.re) % 2 = z.re % 2 := by
    rcases Int.emod_two_eq_zero_or_one z.re with h | h <;> simp [Int.mul_emod, h]
  have hy : (z.im * z.im) % 2 = z.im % 2 := by
    rcases Int.emod_two_eq_zero_or_one z.im with h | h <;> simp [Int.mul_emod, h]
  have hn' : z.norm = z.re * z.re + z.im * z.im := by rw [Zsqrtd.norm_def]; ring
  rw [hn'] at h
  have hpar : (z.re + z.im) % 2 = 1 := by omega
  by_cases hr : z.re % 2 = 1
  · have hi : z.im % 2 = 0 := by omega
    by_cases h4 : (z.re + z.im) % 4 = 1
    · exact ⟨z, ⟨hr, hi, h4⟩, rfl⟩
    · refine ⟨⟨-z.re, -z.im⟩, ⟨by simp; omega, by simp; omega, by simp; omega⟩, ?_⟩
      simp [Zsqrtd.norm_def]
  · have hr0 : z.re % 2 = 0 := by omega
    have hi : z.im % 2 = 1 := by omega
    by_cases h4 : (z.re - z.im) % 4 = 1
    · refine ⟨⟨-z.im, z.re⟩, ⟨by simp; omega, by simpa using hr0, by simp; omega⟩, ?_⟩
      simp [Zsqrtd.norm_def]; ring
    · refine ⟨⟨z.im, -z.re⟩, ⟨by simpa using hi, by simp; omega, by simp; omega⟩, ?_⟩
      simp [Zsqrtd.norm_def]; ring

theorem B_split {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (n : ℕ) :
    B (p * n) + (if p ∣ n then (p : ℤ[i]) * B (n / p) else 0) = B p * B n := by
  haveI := Fact.mk hp
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have hn : (⟨a, b⟩ : ℤ[i]).norm % 2 = 1 := by
    rw [Zsqrtd.norm_def]
    have : ((a : ℤ) * a - -1 * b * b) = p := by rw [← hab]; push_cast; ring
    simp only
    omega
  obtain ⟨π, hπ, hnπ⟩ := exists_assoc _ hn
  have hnp : π.norm = p := by
    rw [hnπ, Zsqrtd.norm_def, ← hab]; push_cast; ring
  have h := hecke_split hp hπ hnp n
  have h1 := hecke_split hp hπ hnp 1
  rw [if_neg (by simpa using hp.one_lt.ne'), mul_one, add_zero, B_one, mul_one] at h1
  rw [h, h1]; ring

theorem B_inert {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (n : ℕ) :
    B (p * n) + (if p ∣ n then (p : ℤ[i]) * B (n / p) else 0) = B p * B n := by
  haveI := Fact.mk hp
  have hprime := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p hp3
  have hneg : Prim (-(p : ℤ[i])) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
  have hS : ∀ n : ℕ, S (p * n) =
      if p ∣ n then (S (n / p)).image (fun ε => -(p : ℤ[i]) * ε) else ∅ := by
    intro n
    ext α
    constructor
    · intro hα
      have hα' := mem_S.1 hα
      have h1 : (p : ℤ[i]) ∣ α * star α := ⟨n, by
        rw [← Zsqrtd.norm_eq_mul_conj, hα'.2]; push_cast; rfl⟩
      obtain ⟨c, hc⟩ : (p : ℤ[i]) ∣ α := by
        rcases hprime.dvd_or_dvd h1 with h | ⟨c, hc⟩
        · exact h
        · refine ⟨star c, ?_⟩
          have := congrArg star hc
          simpa [star_mul'] using this
      have hnc : (n : ℤ) = p * c.norm := by
        have := hα'.2
        rw [hc, Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at this
        have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        push_cast at this
        have : (p : ℤ) * n = p * (p * c.norm) := by linarith
        exact Int.eq_of_mul_eq_mul_left hp0 this
      have hd : p ∣ n := by
        refine ⟨c.norm.toNat, ?_⟩
        have := norm_nonneg c
        zify
        rw [Int.toNat_of_nonneg this]
        exact hnc
      rw [if_pos hd]
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      refine Finset.mem_image.2 ⟨-c, ?_, ?_⟩
      · rw [mem_S]
        refine ⟨Prim.of_mul hα'.1 hneg (by rw [hc]; ring), ?_⟩
        have : (-c).norm = c.norm := by simp [Zsqrtd.norm_def]
        rw [this]
        obtain ⟨k, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left k hp.pos]
        push_cast at hnc
        exact (Int.eq_of_mul_eq_mul_left hp0 hnc).symm
      · rw [hc]; ring
    · intro h
      by_cases hd : p ∣ n
      · rw [if_pos hd] at h
        obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.1 h
        rw [mem_S] at hε ⊢
        refine ⟨hneg.mul hε.1, ?_⟩
        rw [Zsqrtd.norm_mul, hε.2]
        have : (-(p : ℤ[i])).norm = p * p := by simp [Zsqrtd.norm_def]
        rw [this]
        obtain ⟨k, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left k hp.pos]
        push_cast; ring
      · rw [if_neg hd] at h
        simp at h
  have hBp : B p = 0 := by
    have := hS 1
    rw [mul_one, if_neg (by simpa using hp.one_lt.ne')] at this
    simp [B, this]
  rw [hBp, zero_mul]
  by_cases hd : p ∣ n
  · rw [if_pos hd]
    unfold B
    rw [hS, if_pos hd, Finset.sum_image (fun a _ b _ h => mul_left_cancel₀
      (by simpa using hp.ne_zero) h), ← Finset.mul_sum]
    ring
  · rw [if_neg hd]
    unfold B
    rw [hS, if_neg hd]; simp

theorem B_hecke {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    B (p * n) + (if p ∣ n then (p : ℤ[i]) * B (n / p) else 0) = B p * B n := by
  have := hp.eq_two_or_odd
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h4 with h | h
  · exact B_split hp h n
  · exact B_inert hp h n

end F32Aux
end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
