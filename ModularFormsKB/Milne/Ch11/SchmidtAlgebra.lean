import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination

/-!
# F. K. Schmidt's theorem: the algebraic steps

Algebra for the proof of F. K. Schmidt's theorem (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Lemma 5.1.9 – Corollary 5.1.11), in which $\delta$ is the gcd of the degrees of the places of a function field over
$\mathbb F_q$ and $Q = q^\delta$.

- `exists_poly_of_eventually_geometric`: if $A_n = 0$ for $d \nmid n$, $(q-1)A_{dm} = a_m - h$ and eventually
  $a_m = h c Q^m$, then
  $(1 - s^d)(1 - Qs^d)\sum_n A_n s^n$ is a polynomial $P$ with $P(1) \ne 0$: telescoping,
  $\sum_{n \le N} c_n = A_N - QA_{N-1}$ and $(q-1)(A_N - QA_{N-1}) = h(Q - 1)$ for $N$ large.
- `eq_one_of_rootMultiplicity`: if $P'(u)((1-u)(1-Qu))^\delta = P(u)^\delta(1-u^{\delta'})(1-Q^{\delta'}u^{\delta'})$
  with $P(1), P'(1) \ne 0$ and $Q > 1$, then $\delta = 1$ (the multiplicity of the root $u = 1$ is $\delta$ on the
  left and $1$ on the right).
-/

open Finset Polynomial

namespace ModularFormsKB.Milne

/-- **The zeta series in $s = t^\delta$ is a polynomial over $(1-s)(1-Qs)$, not vanishing at $s = 1$.**
Here $A$ is supported on multiples of $d$. -/
theorem exists_poly_of_eventually_geometric (q Q h d : ℕ) (hq : 2 ≤ q) (hQ : 2 ≤ Q) (hh : 1 ≤ h) (hd : 1 ≤ d)
    (c : ℚ) (A : ℕ → ℤ) (hA0 : ∀ n, ¬ d ∣ n → A n = 0) (a : ℕ → ℚ)
    (hA : ∀ m, ((q : ℚ) - 1) * A (d * m) = a m - h) (M : ℕ)
    (hbig : ∀ m, M ≤ m → a m = h * c * (Q : ℚ) ^ m) :
    ∃ P : ℤ[X], (1 - PowerSeries.X ^ d) * (1 - PowerSeries.C (Q : ℤ) * PowerSeries.X ^ d) * PowerSeries.mk A =
        (P : PowerSeries ℤ) ∧ P.eval 1 ≠ 0 := by
  classical
  have hq1 : (q : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  let B : ℕ → ℤ := fun m => A (d * m)
  let cN : ℕ → ℤ := fun n => match n with
    | 0 => B 0
    | 1 => B 1 - ((Q : ℤ) + 1) * B 0
    | k + 2 => B (k + 2) - ((Q : ℤ) + 1) * B (k + 1) + (Q : ℤ) * B k
  have hcz : ∀ k : ℕ, M ≤ k → cN (k + 2) = 0 := by
    intro k hk
    have e0 := hA k
    have e1 := hA (k + 1)
    have e2 := hA (k + 2)
    rw [hbig k hk] at e0
    rw [hbig (k + 1) (by omega)] at e1
    rw [hbig (k + 2) (by omega)] at e2
    have : ((q : ℚ) - 1) * (cN (k + 2) : ℚ) = 0 := by
      simp only [cN, B]
      push_cast
      linear_combination e2 - ((Q : ℚ) + 1) * e1 + (Q : ℚ) * e0
    have := (mul_eq_zero.mp this).resolve_left hq1
    exact_mod_cast this
  have htel : ∀ k : ℕ, ∑ i ∈ range (k + 2), cN i = B (k + 1) - (Q : ℤ) * B k := by
    intro k
    induction k with
    | zero => simp [Finset.sum_range_succ, cN]; ring
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [cN]
      ring
  let P : ℤ[X] := ∑ i ∈ range (M + 2), C (cN i) * X ^ (d * i)
  have hPcoef : ∀ n : ℕ, P.coeff n = ∑ i ∈ range (M + 2), if n = d * i then cN i else 0 := by
    intro n
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
  have hP1 : ∀ m : ℕ, P.coeff (d * m) = if m < M + 2 then cN m else 0 := by
    intro m
    rw [hPcoef]
    by_cases hn : m < M + 2
    · rw [Finset.sum_eq_single m]
      · simp [hn]
      · intro b _ hb
        have : d * m ≠ d * b := fun h' => hb (Nat.eq_of_mul_eq_mul_left hd h').symm
        simp [this]
      · intro hn'; exact absurd (mem_range.mpr hn) hn'
    · rw [Finset.sum_eq_zero]
      · simp [hn]
      · intro b hb
        have := mem_range.mp hb
        have : d * m ≠ d * b := fun h' => by
          have := Nat.eq_of_mul_eq_mul_left hd h'; omega
        simp [this]
  have hP2 : ∀ n : ℕ, ¬ d ∣ n → P.coeff n = 0 := by
    intro n hn
    rw [hPcoef]
    apply Finset.sum_eq_zero
    intro b _
    have : n ≠ d * b := fun h' => hn ⟨b, h'⟩
    simp [this]
  refine ⟨P, ?_, ?_⟩
  · ext n
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = (Q : ℤ) + 1 := ⟨_, rfl⟩
    have hprod : (1 - PowerSeries.X ^ d) * (1 - PowerSeries.C (Q : ℤ) * PowerSeries.X ^ d) *
        PowerSeries.mk A =
        PowerSeries.mk A - PowerSeries.C k * (PowerSeries.X ^ d * PowerSeries.mk A)
          + PowerSeries.C (Q : ℤ) * (PowerSeries.X ^ (d * 2) * PowerSeries.mk A) := by
      rw [hk, map_add, map_one]; ring
    rw [hprod, Polynomial.coeff_coe]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_mk]
    by_cases hdn : d ∣ n
    · obtain ⟨m, rfl⟩ := hdn
      rw [hP1]
      rcases m with _ | _ | m
      · have hd0 : d ≠ 0 := by omega
        simp [cN, B, hd0]
      · have e : d * (0 + 1) - d = 0 := by simp
        have h2 : ¬ d * 2 ≤ d * (0 + 1) := by omega
        have hd0 : d ≠ 0 := by omega
        have h3 : ¬ d * 2 ≤ d := by omega
        simp [cN, B, hk, hd0, h3]
      · have e1 : d * (m + 1 + 1) - d = d * (m + 1) := by
          rw [Nat.mul_add_one (d) (m + 1)]; exact Nat.add_sub_cancel _ _
        have e2 : d * (m + 1 + 1) - d * 2 = d * m := by
          rw [← Nat.mul_sub]; congr 1
        have h1 : d ≤ d * (m + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have h2 : d * 2 ≤ d * (m + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
        rw [if_pos h1, if_pos h2, e1, e2]
        by_cases hn : m < M
        · have : m + 1 + 1 < M + 2 := by omega
          rw [if_pos this]
          simp only [cN, B, hk]
        · have h0 := hcz m (by omega)
          have : ¬ (m + 1 + 1 < M + 2) := by omega
          rw [if_neg this]
          simp only [cN, B] at h0
          have h0' : A (d * (m + 1 + 1)) - ((Q : ℤ) + 1) * A (d * (m + 1)) + (Q : ℤ) * A (d * m) = 0 := h0
          simp only [hk]
          linear_combination (1 : ℤ) * h0'
    · rw [hP2 n hdn, hA0 n hdn]
      have hn1 : ∀ j, j = d ∨ j = d * 2 → (if j ≤ n then A (n - j) else 0) = 0 := by
        intro j hj
        split_ifs with hjn
        · apply hA0
          intro hdv
          apply hdn
          have hdj : d ∣ j := by rcases hj with rfl | rfl; exacts [dvd_rfl, dvd_mul_right _ _]
          have := Nat.dvd_add hdv hdj
          rwa [Nat.sub_add_cancel hjn] at this
        · rfl
      rw [hn1 d (Or.inl rfl), hn1 (d * 2) (Or.inr rfl)]
      simp
  · have hev : P.eval 1 = ∑ i ∈ range (M + 2), cN i := by
      simp [P, eval_finsetSum]
    rw [hev, htel M]
    intro h0
    have h0q : ((B (M + 1) - (Q : ℤ) * B M : ℤ) : ℚ) = 0 := by exact_mod_cast h0
    have e0 := hA M
    have e1 := hA (M + 1)
    rw [hbig M le_rfl] at e0
    rw [hbig (M + 1) (by omega)] at e1
    simp only [B] at h0q
    push_cast at h0q
    have : ((q : ℚ) - 1) * ((A (d * (M + 1)) : ℚ) - Q * A (d * M)) = h * ((Q : ℚ) - 1) := by
      linear_combination e1 - (Q : ℚ) * e0
    rw [h0q, mul_zero] at this
    have hh' : (h : ℚ) ≠ 0 := by positivity
    have hQ' : (Q : ℚ) - 1 ≠ 0 := by
      have : (2 : ℚ) ≤ Q := by exact_mod_cast hQ
      linarith
    exact mul_ne_zero hh' hQ' this.symm

/-- **Comparing the multiplicity of the root $u = 1$.** -/
theorem eq_one_of_rootMultiplicity (P P' : ℤ[X]) (δ δ' Q : ℕ) (hδ : 1 ≤ δ) (hδ' : 1 ≤ δ') (hQ : 2 ≤ Q)
    (hP : P.eval 1 ≠ 0) (hP' : P'.eval 1 ≠ 0)
    (h : P' * ((1 - X) * (1 - C (Q : ℤ) * X)) ^ δ =
      P ^ δ * ((1 - X ^ δ') * (1 - C ((Q : ℤ) ^ δ') * X ^ δ'))) :
    δ = 1 := by
  have hne : ∀ p : ℤ[X], p.eval 1 ≠ 0 → p ≠ 0 := by
    intro p hp h0; apply hp; simp [h0]
  have hz : ∀ p : ℤ[X], p.eval 1 ≠ 0 → rootMultiplicity 1 p = 0 := by
    intro p hp
    exact rootMultiplicity_eq_zero (by simpa [IsRoot] using hp)
  have hpow : ∀ (p : ℤ[X]), p ≠ 0 → ∀ n : ℕ, rootMultiplicity 1 (p ^ n) = n * rootMultiplicity 1 p := by
    intro p hp n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ih]
      ring
  have hQ1 : (1 : ℤ) - Q ≠ 0 := by
    have : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
    omega
  have hQ1' : (1 : ℤ) - (Q : ℤ) ^ δ' ≠ 0 := by
    have : (2 : ℤ) ≤ Q := by exact_mod_cast hQ
    have : (2 : ℤ) ^ 1 ≤ (Q : ℤ) ^ δ' := by
      calc (2 : ℤ) ^ 1 ≤ 2 ^ δ' := pow_le_pow_right₀ (by norm_num) hδ'
        _ ≤ (Q : ℤ) ^ δ' := pow_le_pow_left₀ (by norm_num) this _
    omega
  have h1Xne : (1 - X : ℤ[X]) ≠ 0 := by
    intro h0
    have := congrArg (eval 0) h0
    simp at this
  have h1X : rootMultiplicity 1 (1 - X : ℤ[X]) = 1 := by
    have : (1 - X : ℤ[X]) = C (-1) * (X - C 1) := by simp
    rw [this] at h1Xne ⊢
    rw [rootMultiplicity_mul h1Xne, rootMultiplicity_X_sub_C_self, hz _ (by simp)]
  have hA1 : (1 - C (Q : ℤ) * X : ℤ[X]).eval 1 ≠ 0 := by simpa using hQ1
  have hA2 : (1 - C ((Q : ℤ) ^ δ') * X ^ δ' : ℤ[X]).eval 1 ≠ 0 := by simpa using hQ1'
  have h1Xne : (1 - X : ℤ[X]) ≠ 0 := by
    intro h0
    have := congrArg (eval 0) h0
    simp at this
  have hgeom : (1 - X ^ δ' : ℤ[X]) = (1 - X) * ∑ i ∈ range δ', X ^ i := by
    rw [mul_neg_geom_sum]
  have hgs : (∑ i ∈ range δ', (X : ℤ[X]) ^ i).eval 1 ≠ 0 := by
    have : δ' ≠ 0 := by omega
    simp [eval_finsetSum, this]
  have hXd : rootMultiplicity 1 (1 - X ^ δ' : ℤ[X]) = 1 := by
    rw [hgeom, rootMultiplicity_mul (mul_ne_zero h1Xne (hne _ hgs)), h1X, hz _ hgs]
  have hn : (1 - X ^ δ' : ℤ[X]) ≠ 0 := by
    rw [hgeom]; exact mul_ne_zero h1Xne (hne _ hgs)
  have hLne : ((1 - X) * (1 - C (Q : ℤ) * X) : ℤ[X]) ≠ 0 := mul_ne_zero h1Xne (hne _ hA1)
  have hL : rootMultiplicity 1 ((1 - X) * (1 - C (Q : ℤ) * X) : ℤ[X]) = 1 := by
    rw [rootMultiplicity_mul hLne, h1X, hz _ hA1]
  have hRne : ((1 - X ^ δ') * (1 - C ((Q : ℤ) ^ δ') * X ^ δ') : ℤ[X]) ≠ 0 :=
    mul_ne_zero hn (hne _ hA2)
  have hR : rootMultiplicity 1 ((1 - X ^ δ') * (1 - C ((Q : ℤ) ^ δ') * X ^ δ') : ℤ[X]) = 1 := by
    rw [rootMultiplicity_mul hRne, hXd, hz _ hA2]
  have hLm := congrArg (rootMultiplicity 1) h
  rw [rootMultiplicity_mul (mul_ne_zero (hne _ hP') (pow_ne_zero _ hLne)),
    rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (hne _ hP)) hRne),
    hpow _ hLne, hpow _ (hne _ hP), hL, hR, hz _ hP', hz _ hP] at hLm
  simpa using hLm

end ModularFormsKB.Milne
