/-
# Elementary facts on the coefficients of $f_{32}$

$b$ vanishes at even $m$, $b(m) \ne 0 \Rightarrow m \equiv 1 \bmod 4$, and
$|b(m)| \le 6m$.
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.Coefficients

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

/-- $b(m) = 0$ for even $m$ ($a$ odd and $c$ even make $a^2 + c^2$ odd). -/
theorem f32Coeff_of_even {m : ℕ} (hm : Even m) : f32Coeff m = 0 := by
  unfold f32Coeff
  apply Finset.sum_eq_zero
  intro v hv
  exfalso
  simp only [primaryOfNorm, Finset.mem_filter] at hv
  obtain ⟨-, hs, h1, h2, -⟩ := hv
  obtain ⟨k, hk⟩ : ∃ k, v.1 = 2 * k + 1 := ⟨v.1 / 2, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l, v.2 = 2 * l := ⟨v.2 / 2, by omega⟩
  obtain ⟨j, hj⟩ := hm
  have : (m : ℤ) = 2 * (2 * k ^ 2 + 2 * k + 2 * l ^ 2) + 1 := by
    rw [← hs, hk, hl]; ring
  have hj' : (m : ℤ) = j + j := by exact_mod_cast hj
  omega

/-- $b(m) \ne 0$ forces $m \equiv 1 \bmod 4$. -/
theorem mod_four_eq_one_of_f32Coeff_ne_zero {m : ℕ} (hm : f32Coeff m ≠ 0) : m % 4 = 1 := by
  obtain ⟨v, hv, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  simp only [primaryOfNorm, Finset.mem_filter] at hv
  obtain ⟨-, hs, h1, h2, -⟩ := hv
  obtain ⟨k, hk⟩ : ∃ k, v.1 = 2 * k + 1 := ⟨v.1 / 2, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l, v.2 = 2 * l := ⟨v.2 / 2, by omega⟩
  have : (m : ℤ) = 4 * (k ^ 2 + k + l ^ 2) + 1 := by
    rw [← hs, hk, hl]; ring
  omega

/-- $|b(m)| \le 6m$. -/
theorem abs_f32Coeff_le (m : ℕ) : |f32Coeff m| ≤ 6 * m := by
  set s := Nat.sqrt m with hsdef
  have hs2 : s ^ 2 ≤ m := Nat.sqrt_le' m
  have hs3 : m < (s + 1) ^ 2 := Nat.lt_succ_sqrt' m
  have hsm : s ≤ m := Nat.sqrt_le_self m
  have habs : ∀ v ∈ primaryOfNorm m, |v.1| ≤ (s : ℤ) := by
    intro v hv
    simp only [primaryOfNorm, Finset.mem_filter] at hv
    obtain ⟨-, hsum, -⟩ := hv
    by_contra hcon
    push Not at hcon
    have h1 : (s : ℤ) + 1 ≤ |v.1| := by omega
    have h2 : ((s : ℤ) + 1) ^ 2 ≤ |v.1| ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) h1
    have h3 : |v.1| ^ 2 = v.1 ^ 2 := sq_abs _
    have h4 : (m : ℤ) < ((s : ℤ) + 1) ^ 2 := by exact_mod_cast hs3
    nlinarith [sq_nonneg v.2]
  have hcard : (primaryOfNorm m).card ≤ (2 * s + 1) * 2 := by
    have : (primaryOfNorm m).card ≤
        ((Finset.Icc (-(s : ℤ)) s) ×ˢ (Finset.univ : Finset Bool)).card := by
      apply Finset.card_le_card_of_injOn (fun v ↦ (v.1, decide (0 ≤ v.2)))
      · intro v hv
        have := habs v hv
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc,
          Finset.mem_univ, and_true]
        exact abs_le.mp this
      · intro v hv w hw hvw
        simp only [Prod.mk.injEq] at hvw
        obtain ⟨ha, hb⟩ := hvw
        have hv' := hv
        have hw' := hw
        simp only [Finset.mem_coe, primaryOfNorm, Finset.mem_filter] at hv' hw'
        have hsq : v.2 ^ 2 = w.2 ^ 2 := by
          have e1 := hv'.2.1; have e2 := hw'.2.1; rw [ha] at e1; linarith
        have : v.2 = w.2 := by
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
          · exact h
          · by_cases h0 : 0 ≤ v.2
            · have : 0 ≤ w.2 := by simpa [h0] using hb.symm
              omega
            · have : ¬ 0 ≤ w.2 := by simpa [h0] using hb.symm
              omega
        exact Prod.ext ha this
    simpa [Int.card_Icc] using (this.trans (by
      simp [Int.card_Icc]; omega))
  calc |f32Coeff m| ≤ ∑ v ∈ primaryOfNorm m, |v.1| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ primaryOfNorm m, (s : ℤ) := Finset.sum_le_sum habs
    _ = (primaryOfNorm m).card * (s : ℤ) := by simp
    _ ≤ ((2 * s + 1) * 2 : ℕ) * (s : ℤ) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ 6 * m := by
        push_cast
        have : (s : ℤ) ^ 2 ≤ m := by exact_mod_cast hs2
        have : (s : ℤ) ≤ m := by exact_mod_cast hsm
        nlinarith

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
