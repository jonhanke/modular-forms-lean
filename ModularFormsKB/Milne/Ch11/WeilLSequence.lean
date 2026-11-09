import Mathlib

/-!
# The $L$-polynomial from the class sums: pure algebra

Let $q \ge 2$, $g$, $h$ be natural numbers, $A_n$ ($n \ge 0$) integers and $a : \mathbb Z \to \mathbb Q$ with

- $a_m = h$ for $m < 0$,
- $a_m = q^{m + 1 - g}\,a_{2g-2-m}$ for all $m$ (the Riemann–Roch duality summed over divisor classes),
- $(q - 1)A_n = a_n - h$ for $n \ge 0$, and $A_0 = 1$.

(For a function field, $a_m = \sum_{c \in \mathrm{Cl}^0} q^{\ell(mD_1 + R_c)}$ with $\deg D_1 = 1$.) Then
$(1 - t)(1 - qt)\sum_n A_n t^n$ is an integer polynomial $L$ of degree $2g$ with $L(0) = 1$ and
$q^i c_{2g-i} = q^g c_i$ (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., proof of Theorem 5.1.15).

Proof: with $c_n = A_n - (q+1)A_{n-1} + qA_{n-2}$ ($A_{<0} = 0$) one has $(q-1)c_n = a_n - (q+1)a_{n-1} + qa_{n-2}$
for every $n \in \mathbb Z$ (the $h$'s cancel); for $n > 2g$ the duality gives $a_j = hq^{j+1-g}$ for
$j \ge n - 2 > 2g - 2$ and the combination vanishes; and the duality turns $(q-1)c_{2g-i}$ into $q^{g-i}(q-1)c_i$.
-/

open Finset Polynomial

namespace ModularFormsKB.Milne

/-- **The $L$-polynomial from the class sums.** -/
theorem exists_lpoly_of_classSums (q g h : ℕ) (hq : 2 ≤ q) (A : ℕ → ℤ) (a : ℤ → ℚ)
    (hneg : ∀ m : ℤ, m < 0 → a m = h)
    (hdual : ∀ m : ℤ, a m = (q : ℚ) ^ (m + 1 - g) * a (2 * g - 2 - m))
    (hA : ∀ n : ℕ, ((q : ℚ) - 1) * A n = a n - h) (hA0 : A 0 = 1) :
    ∃ L : ℤ[X], L.natDegree = 2 * g ∧ L.coeff 0 = 1 ∧
      (∀ i, i ≤ 2 * g → (q : ℤ) ^ i * L.coeff (2 * g - i) = (q : ℤ) ^ g * L.coeff i) ∧
      (1 - PowerSeries.X) * (1 - PowerSeries.C (q : ℤ) * PowerSeries.X) * PowerSeries.mk A =
        (L : PowerSeries ℤ) := by
  classical
  have hq0 : (q : ℚ) ≠ 0 := by positivity
  have hq1 : (q : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  let Az : ℤ → ℤ := fun m => if m < 0 then 0 else A m.toNat
  have hAz : ∀ m : ℤ, ((q : ℚ) - 1) * (Az m : ℚ) = a m - h := by
    intro m
    by_cases hm : m < 0
    · simp [Az, hm, hneg m hm]
    · have := hA m.toNat
      rw [Int.toNat_of_nonneg (not_lt.mp hm)] at this
      simp only [Az, hm, ite_false]
      exact this
  let c : ℤ → ℤ := fun n => Az n - (q + 1) * Az (n - 1) + q * Az (n - 2)
  have hc : ∀ n : ℤ, ((q : ℚ) - 1) * (c n : ℚ) = a n - (q + 1) * a (n - 1) + q * a (n - 2) := by
    intro n
    simp only [c]
    push_cast
    linear_combination hAz n - ((q : ℚ) + 1) * hAz (n - 1) + (q : ℚ) * hAz (n - 2)
  have hbig : ∀ j : ℤ, 2 * (g : ℤ) - 2 < j → a j = h * (q : ℚ) ^ (j + 1 - g) := by
    intro j hj
    rw [hdual j, hneg _ (by omega)]
    ring
  have hcz : ∀ n : ℤ, 2 * (g : ℤ) < n → c n = 0 := by
    intro n hn
    have h1 := hbig n (by omega)
    have h2 := hbig (n - 1) (by omega)
    have h3 := hbig (n - 2) (by omega)
    have key := hc n
    rw [h1, h2, h3] at key
    rw [show n - 1 + 1 - (g : ℤ) = n - g by ring, show n - 2 + 1 - (g : ℤ) = (n - g) - 1 by ring,
      show n + 1 - (g : ℤ) = (n - g) + 1 by ring, zpow_sub_one₀ hq0, zpow_add_one₀ hq0] at key
    have : ((q : ℚ) - 1) * (c n : ℚ) = 0 := by
      rw [key]; field_simp; ring
    have := (mul_eq_zero.mp this).resolve_left hq1
    exact_mod_cast this
  have hFE : ∀ i : ℕ, i ≤ 2 * g → (q : ℚ) ^ i * (c (2 * g - i) : ℚ) = (q : ℚ) ^ g * (c i : ℚ) := by
    intro i hi
    have e1 := hdual (2 * (g : ℤ) - i)
    have e2 := hdual (2 * (g : ℤ) - i - 1)
    have e3 := hdual (2 * (g : ℤ) - i - 2)
    rw [show 2 * (g : ℤ) - 2 - (2 * (g : ℤ) - i) = i - 2 by ring,
      show 2 * (g : ℤ) - i + 1 - g = (g - i) + 1 by ring] at e1
    rw [show 2 * (g : ℤ) - 2 - (2 * (g : ℤ) - i - 1) = i - 1 by ring,
      show 2 * (g : ℤ) - i - 1 + 1 - g = (g - i) by ring] at e2
    rw [show 2 * (g : ℤ) - 2 - (2 * (g : ℤ) - i - 2) = i by ring,
      show 2 * (g : ℤ) - i - 2 + 1 - g = (g - i) - 1 by ring] at e3
    have key := hc (2 * g - i)
    rw [e1, e2, e3, zpow_sub_one₀ hq0, zpow_add_one₀ hq0] at key
    have key2 := hc i
    have hy : ((q : ℚ) - 1) * (c (2 * g - i) : ℚ) = ((q : ℚ) - 1) * ((q : ℚ) ^ ((g : ℤ) - i) * (c i : ℚ)) := by
      rw [key]
      have : ((q : ℚ) - 1) * ((q : ℚ) ^ ((g : ℤ) - i) * (c i : ℚ)) =
          (q : ℚ) ^ ((g : ℤ) - i) * (((q : ℚ) - 1) * (c i : ℚ)) := by ring
      rw [this, key2]
      field_simp
      ring
    have hy2 := mul_left_cancel₀ hq1 hy
    rw [hy2]
    have : (q : ℚ) ^ i * (q : ℚ) ^ ((g : ℤ) - i) = (q : ℚ) ^ g := by
      rw [← zpow_natCast, ← zpow_add₀ hq0]
      simp
    rw [← this]; ring
  have hc0 : c 0 = 1 := by
    simp [c, Az, hA0]
  let cN : ℕ → ℤ := fun n => c n
  let L : ℤ[X] := ∑ i ∈ range (2 * g + 1), C (cN i) * X ^ i
  have hL : ∀ n : ℕ, L.coeff n = cN n := by
    intro n
    simp only [L, finsetSum_coeff, coeff_C_mul_X_pow]
    by_cases hn : n ≤ 2 * g
    · rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro hn'; exact absurd (mem_range.mpr (by omega)) hn'
    · rw [Finset.sum_eq_zero]
      · have := hcz n (by omega)
        simp [cN, this]
      · intro b hb
        have := mem_range.mp hb
        simp only [ite_eq_right_iff]
        intro h'; omega
  have hFEz : ∀ i : ℕ, i ≤ 2 * g → (q : ℤ) ^ i * cN (2 * g - i) = (q : ℤ) ^ g * cN i := by
    intro i hi
    have := hFE i hi
    simp only [cN]
    rw [Nat.cast_sub hi]
    push_cast
    exact_mod_cast this
  have h2g : cN (2 * g) = (q : ℤ) ^ g := by
    have := hFEz 0 (by omega)
    simp only [pow_zero, one_mul, Nat.sub_zero] at this
    rw [this]
    simp [cN, hc0]
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hL]
      simp only [cN]
      exact hcz _ (by omega)
    · rw [hL, h2g]
      have : (q : ℤ) ≠ 0 := by positivity
      exact pow_ne_zero _ this
  · rw [hL]; simpa [cN] using hc0
  · intro i hi
    rw [hL, hL]
    exact hFEz i hi
  · ext n
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = (q : ℤ) + 1 := ⟨_, rfl⟩
    have hprod : (1 - PowerSeries.X) * (1 - PowerSeries.C (q : ℤ) * PowerSeries.X) * PowerSeries.mk A =
        PowerSeries.mk A - PowerSeries.C k * (PowerSeries.X * PowerSeries.mk A)
          + PowerSeries.C (q : ℤ) * (PowerSeries.X ^ 2 * PowerSeries.mk A) := by
      rw [hk, map_add, map_one]; ring
    rw [hprod, Polynomial.coeff_coe, hL]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    rcases n with _ | _ | n
    · simp [cN, c, Az, hA0]
    · simp [cN, c, Az, hk]
    · simp [cN, c, Az, hk]
      have e : ((n:ℤ) + 1 + 1 - 2).toNat = n := by omega
      have e2 : ¬ ((n:ℤ) + 1 + 1 < 0) := by omega
      rw [e]; simp [e2]

end ModularFormsKB.Milne
