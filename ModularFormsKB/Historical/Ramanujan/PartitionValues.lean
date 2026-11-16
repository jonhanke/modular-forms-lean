import ModularFormsKB.Historical.Ramanujan.Congruences

/-!
# Values of the partition function

`p(100) = 190569292`, `p(200) = 3972999029388` and `p(61), p(62), p(63)` (Hardy–Ramanujan, *Collected
Papers*, No. 36, § 1.7, pp. 283–284, from MacMahon's table), and `p(243) = 133978259344888` (No. 28,
p. 230).

Route: from `partitionSeries * eulerSeries = 1` and the pentagonal number theorem
(`Congruences.lean`) we get Euler's recurrence
`p(N) = p(N-1) + p(N-2) - p(N-5) - p(N-7) + p(N-12) + ⋯`
(`partitionCount_recurrence`, with the pentagonal numbers `k(3k±1)/2` indexed as in
`PowerSeries.WithPiTopology.hasSum_pow_pentagonal_sub_pentagonalSeries`). A computable function `pList`
(structural recursion on `ℕ`, lists of integers, newest value first) implements the recurrence and is
proved to compute `partitionCount` (`pList_getD`); the numerical values are then checked by kernel
evaluation (`decide +kernel`, no `native_decide`).
-/

noncomputable section

open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

namespace ModularFormsKB.Historical.Ramanujan

/-! ### The recurrence -/

/-- `p(N - a)` if `a ≤ N`, and `0` otherwise. -/
def pcFun (N a : ℕ) : ℤ := if a ≤ N then (partitionCount (N - a) : ℤ) else 0

theorem pentagonal_neg_nat (k : ℕ) : pentagonal (-(k : ℤ)) = k * (3 * k + 1) / 2 := by
  have h : 2 * pentagonal (-(k : ℤ)) = k * (3 * k + 1) := by
    have := two_mul_natCast_pentagonal_neg (k : ℤ)
    exact_mod_cast this
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num)]

theorem pentagonal_succ_nat (k : ℕ) : pentagonal ((k : ℤ) + 1) = (k + 1) * (3 * k + 2) / 2 := by
  have h : 2 * pentagonal ((k : ℤ) + 1) = (k + 1) * (3 * k + 2) := by
    have h1 := two_mul_natCast_pentagonal ((k : ℤ) + 1)
    have h2 : (2 * (pentagonal ((k : ℤ) + 1) : ℤ)) = (((k + 1) * (3 * k + 2) : ℕ) : ℤ) := by
      rw [h1]; push_cast; ring
    exact_mod_cast h2
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num)]

theorem le_tri_div (k : ℕ) : k ≤ k * (3 * k + 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith [Nat.le_mul_self k]

theorem le_tri_div' (k : ℕ) : k ≤ (k + 1) * (3 * k + 2) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith [Nat.le_mul_self k]

theorem coeff_term (N k : ℕ) :
    coeff N (partitionSeries * ((-1 : ℤ⟦X⟧) ^ k * (X ^ pentagonal (-(k : ℤ)) - X ^ pentagonal ((k : ℤ) + 1)))) =
      (-1) ^ k * (pcFun N (k * (3 * k + 1) / 2) - pcFun N ((k + 1) * (3 * k + 2) / 2)) := by
  have hC : ((-1 : ℤ⟦X⟧)) ^ k = C ((-1 : ℤ) ^ k) := by simp
  rw [hC, show ∀ a b : ℕ, partitionSeries * (C ((-1 : ℤ) ^ k) * (X ^ a - X ^ b)) =
      C ((-1 : ℤ) ^ k) * (partitionSeries * X ^ a - partitionSeries * X ^ b) from
      fun a b ↦ by ring, coeff_C_mul, map_sub, coeff_mul_X_pow', coeff_mul_X_pow',
    pentagonal_neg_nat, pentagonal_succ_nat]
  simp [pcFun, partitionSeries]

/-- **Euler's recurrence** for the partition function, in the form
`p(N) = p(N-1) - ∑_{k ≥ 1} (-1)^k (p(N - k(3k+1)/2) - p(N - (k+1)(3k+2)/2))`, `N ≥ 1`. -/
theorem partitionCount_recurrence (N : ℕ) (hN : 1 ≤ N) :
    (partitionCount N : ℤ) = pcFun N 1 - ∑ k ∈ range N, (-1) ^ (k + 1) *
      (pcFun N ((k + 1) * (3 * (k + 1) + 1) / 2) - pcFun N ((k + 1 + 1) * (3 * (k + 1) + 2) / 2)) := by
  have hs := PowerSeries.WithPiTopology.hasSum_pow_pentagonal_sub_pentagonalSeries ℤ
  rw [← eulerSeries_eq_pentagonalSeries] at hs
  have h2 := hs.mul_left partitionSeries
  rw [partitionSeries_mul_eulerSeries] at h2
  have h3 := (PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff ℤ |>.mp h2) N
  have h1 : coeff N (1 : ℤ⟦X⟧) = 0 := by simp [coeff_one]; omega
  rw [h1] at h3
  simp_rw [coeff_term] at h3
  have h4 : HasSum (fun k : ℕ ↦ (-1 : ℤ) ^ k *
      (pcFun N (k * (3 * k + 1) / 2) - pcFun N ((k + 1) * (3 * k + 2) / 2)))
      (∑ k ∈ range (N + 1), (-1 : ℤ) ^ k *
        (pcFun N (k * (3 * k + 1) / 2) - pcFun N ((k + 1) * (3 * k + 2) / 2))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hk' : N < k := by simpa using hk
    have a1 := le_tri_div k
    have a2 := le_tri_div' k
    have b1 : ¬ k * (3 * k + 1) / 2 ≤ N := by omega
    have b2 : ¬ (k + 1) * (3 * k + 2) / 2 ≤ N := by omega
    simp [pcFun, b1, b2]
  have h5 := h4.unique h3
  rw [Finset.sum_range_succ'] at h5
  have e0 : (-1 : ℤ) ^ 0 * (pcFun N (0 * (3 * 0 + 1) / 2) - pcFun N ((0 + 1) * (3 * 0 + 2) / 2)) =
      (partitionCount N : ℤ) - pcFun N 1 := by
    simp [pcFun]
  rw [e0] at h5
  linarith

/-! ### A computable implementation of the recurrence -/

/-- `p(N - a)` read off the list `L = [p(N-1), p(N-2), …, p(0)]` (`1 ≤ a`), and `0` if `a > N`. -/
def pLookup (L : List ℤ) (N a : ℕ) : ℤ := if a ≤ N then L.getD (a - 1) 0 else 0

/-- The `k`-th term `(-1)^k (p(N - k(3k+1)/2) - p(N - (k+1)(3k+2)/2))` of Euler's recurrence. -/
def pTerm (L : List ℤ) (N k : ℕ) : ℤ :=
  (if k % 2 = 0 then 1 else -1) *
    (pLookup L N (k * (3 * k + 1) / 2) - pLookup L N ((k + 1) * (3 * k + 2) / 2))

/-- `p(N)` from `L = [p(N-1), …, p(0)]` by Euler's recurrence. -/
def pNext (L : List ℤ) (N : ℕ) : ℤ :=
  pLookup L N 1 - ((List.range N).map fun k ↦ pTerm L N (k + 1)).sum

/-- `pList n = [p(n), p(n-1), …, p(0)]`, as integers. -/
def pList : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => pNext (pList n) (n + 1) :: pList n

theorem list_map_range_sum {α : Type*} [AddCommMonoid α] (g : ℕ → α) (N : ℕ) :
    ((List.range N).map g).sum = ∑ k ∈ range N, g k := by
  induction N with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem partitionCount_zero : partitionCount 0 = 1 := by
  have h := congrArg (PowerSeries.coeff 0) partitionSeries_mul_eulerSeries
  have e := coeff_zero_eulerSeries
  rw [coeff_zero_eq_constantCoeff_apply] at e
  simp only [coeff_zero_eq_constantCoeff_apply, map_mul, map_one, e, mul_one] at h
  rw [← coeff_zero_eq_constantCoeff_apply] at h
  simpa [partitionSeries] using h

theorem pLookup_eq (n : ℕ) (ih : ∀ i ≤ n, (pList n).getD i 0 = (partitionCount (n - i) : ℤ))
    (a : ℕ) (ha : 1 ≤ a) : pLookup (pList n) (n + 1) a = pcFun (n + 1) a := by
  unfold pLookup pcFun
  by_cases h : a ≤ n + 1
  · simp only [h, ↓reduceIte]
    rw [ih (a - 1) (by omega)]
    congr 2
    omega
  · simp only [h, ↓reduceIte]

theorem pList_getD : ∀ n i : ℕ, i ≤ n → (pList n).getD i 0 = (partitionCount (n - i) : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    simp [pList, partitionCount_zero]
  | succ n ih =>
    intro i hi
    cases i with
    | succ i =>
      rw [pList, List.getD_cons_succ, ih i (by omega)]
      simp
    | zero =>
      rw [pList, List.getD_cons_zero, Nat.sub_zero, partitionCount_recurrence (n + 1) (by omega)]
      unfold pNext
      rw [list_map_range_sum, pLookup_eq n ih 1 le_rfl]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      have s1 : 1 ≤ (k + 1) * (3 * (k + 1) + 1) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
      have s2 : 1 ≤ (k + 1 + 1) * (3 * (k + 1) + 2) / 2 := Nat.div_pos (by nlinarith) (by norm_num)
      unfold pTerm
      rw [pLookup_eq n ih _ s1, pLookup_eq n ih _ s2]
      congr 1
      by_cases h : (k + 1) % 2 = 0
      · simp only [h, ↓reduceIte]
        exact ((Nat.even_iff.mpr h).neg_one_pow).symm
      · simp only [h, ↓reduceIte]
        exact ((Nat.odd_iff.mpr (by omega)).neg_one_pow).symm

/-- `p(n)` as the head of `pList n`. -/
theorem partitionCount_eq_pList (n : ℕ) : (partitionCount n : ℤ) = (pList n).getD 0 0 := by
  simpa using (pList_getD n 0 (Nat.zero_le n)).symm

theorem partitionCount_eq_pList' (n m : ℕ) (h : m ≤ n) :
    (partitionCount m : ℤ) = (pList n).getD (n - m) 0 := by
  rw [pList_getD n (n - m) (by omega)]
  congr 2
  omega

/-- Kernel evaluation of Euler's recurrence up to `243`. -/
theorem pList_values :
    (pList 243).getD 0 0 = 133978259344888 ∧ (pList 243).getD 43 0 = 3972999029388 ∧
      (pList 243).getD 143 0 = 190569292 ∧ (pList 243).getD 180 0 = 1505499 ∧
      (pList 243).getD 181 0 = 1300156 ∧ (pList 243).getD 182 0 = 1121505 := by
  decide +kernel

/-- **Values of `p(n)`** quoted by Hardy and Ramanujan (No. 36, § 1.7, pp. 283–284, from MacMahon's
table): `p(100) = 190569292`, `p(200) = 3972999029388`, `p(61) = 1121505`,
`p(62) = 1300156`, `p(63) = 1505499`. -/
@[kb "ramanujan1927" "No. 36, § 1.7, pp. 283–284"]
theorem hardyRamanujanValues : HardyRamanujanValues := by
  obtain ⟨-, h200, h100, h63, h62, h61⟩ := pList_values
  have e := fun m (hm : m ≤ 243) ↦ partitionCount_eq_pList' 243 m hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := e 100 (by norm_num); rw [h100] at this; exact_mod_cast this
  · have := e 200 (by norm_num); rw [h200] at this; exact_mod_cast this
  · have := e 61 (by norm_num); rw [h61] at this; exact_mod_cast this
  · have := e 62 (by norm_num); rw [h62] at this; exact_mod_cast this
  · have := e 63 (by norm_num); rw [h63] at this; exact_mod_cast this

/-- **The case `7³` fails** (a verification attached to No. 28, p. 230):
`p(243) = 133978259344888 ≡ 245 (mod 343)` although `24 · 243 ≡ 1 (mod 343)`. -/
@[kb "ramanujan1927" "No. 28, p. 230"]
theorem partitionCount243 : PartitionCount243 := by
  obtain ⟨h243, -⟩ := pList_values
  have h := partitionCount_eq_pList 243
  rw [h243] at h
  have h' : partitionCount 243 = 133978259344888 := by exact_mod_cast h
  refine ⟨h', ?_, by norm_num⟩
  rw [h']

end ModularFormsKB.Historical.Ramanujan
