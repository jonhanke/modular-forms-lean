import ModularFormsKB.Shimura2007.Ch2.EulerPolynomials
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Data.Nat.Choose.Cast

/-!
# Shimura 2007, §4.1: properties of the generalized Euler polynomials

G. Shimura, *Elementary Dirichlet Series and Modular Forms* (Springer 2007), §4.1, pp. 25-27.

For the polynomials $E_{c,n}(t)$ defined by the recursion (4.3b) (`eulerPoly`) we prove the
small values (4.3h), the derivative formula (4.3c), the translation identity (4.3d), the
Appell translation formula, and the generating function (4.2) in $K[t][[z]]$.
-/

open Polynomial

namespace ModularFormsKB.Shimura2007

variable {K : Type*} [Field K] [CharZero K] (c : K)

/-- $E_{c,0}(t) = 1$ (4.3h). -/
@[kb "shimura2007" "§4.1, (4.3h), p. 25"]
theorem eulerPoly_zero : eulerPoly c 0 = 1 := by
  rw [eulerPoly_eq]; simp

/-- $E_{c,1}(t) = t + b$ with $b = -(1+c)^{-1}$ (4.3h). -/
@[kb "shimura2007" "§4.1, (4.3h), p. 25"]
theorem eulerPoly_one : eulerPoly c 1 = X + C (eulerB c) := by
  rw [eulerPoly_eq]; simp [eulerPoly_zero]

/-- $E_{c,2}(t) = t^2 + 2bt + 2b^2 + b$ with $b = -(1+c)^{-1}$ (4.3h). -/
@[kb "shimura2007" "§4.1, (4.3h), p. 25"]
theorem eulerPoly_two :
    eulerPoly c 2 = X ^ 2 + C (2 * eulerB c) * X + C (2 * eulerB c ^ 2 + eulerB c) := by
  rw [eulerPoly_eq]
  simp [Finset.sum_range_succ, eulerPoly_zero, eulerPoly_one]
  rw [show (C (2 : K)) = 2 from map_ofNat C 2]
  ring

theorem one_add_mul_eulerB (hc : 1 + c ≠ 0) : (1 + c) * eulerB c = -1 := by
  unfold eulerB; field_simp

/-- Rewriting of the recursion: $\sum_{k<n}\binom nk E_{c,k} = -(1+c)(E_{c,n}-t^n)$. -/
theorem sum_choose_eulerPoly_lt (hc : 1 + c ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, (n.choose k : K[X]) * eulerPoly c k
      = C (-(1 + c)) * (eulerPoly c n - X ^ n) := by
  have h : eulerPoly c n - X ^ n
      = C (eulerB c) * ∑ k ∈ Finset.range n, (n.choose k : K[X]) * eulerPoly c k := by
    linear_combination eulerPoly_eq c n
  rw [h, ← mul_assoc, ← C_mul]
  have : -(1 + c) * eulerB c = 1 := by linear_combination -(one_add_mul_eulerB c hc)
  rw [this]; simp

/-- $\sum_{k\le n}\binom nk E_{c,k}(t) + c E_{c,n}(t) = (1+c)t^n$. -/
theorem sum_choose_eulerPoly (hc : 1 + c ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : K[X]) * eulerPoly c k
      = C (1 + c) * X ^ n - C c * eulerPoly c n := by
  rw [Finset.sum_range_succ, sum_choose_eulerPoly_lt c hc]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, map_neg, map_add, map_one]
  ring

/-- (4.3d): $E_{c,n}(t+1) + cE_{c,n}(t) = (1+c)t^n$. -/
@[kb "shimura2007" "§4.1, (4.3d), p. 25"]
theorem eulerPoly_comp_add_one (hc : 1 + c ≠ 0) (n : ℕ) :
    (eulerPoly c n).comp (X + 1) + C c * eulerPoly c n = C (1 + c) * X ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hs : (eulerPoly c n).comp (X + 1) = (X + 1) ^ n + C (eulerB c) *
        ∑ k ∈ Finset.range n, (n.choose k : K[X]) * (eulerPoly c k).comp (X + 1) := by
      conv_lhs => rw [eulerPoly_eq]
      simp [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.sum_comp, Finset.sum_comp]
    have hk : ∀ k ∈ Finset.range n, (n.choose k : K[X]) * (eulerPoly c k).comp (X + 1)
        = C (1 + c) * ((n.choose k : K[X]) * X ^ k) - C c * ((n.choose k : K[X]) * eulerPoly c k) := by
      intro k hk
      have := ih k (Finset.mem_range.1 hk)
      have h2 : (eulerPoly c k).comp (X + 1) = C (1 + c) * X ^ k - C c * eulerPoly c k := by
        linear_combination this
      rw [h2]; ring
    rw [hs, Finset.sum_congr rfl hk, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_choose_eulerPoly_lt c hc]
    have hpow : ∑ k ∈ Finset.range n, (n.choose k : K[X]) * X ^ k = (X + 1) ^ n - X ^ n := by
      rw [add_pow, Finset.sum_range_succ]
      simp only [Nat.choose_self, Nat.cast_one, one_pow, mul_one]
      simp [mul_comm]
    rw [hpow]
    have hA : C (1 + c) = 1 + C c := by simp
    have hb : C (eulerB c) * (1 + C c) = (-1 : K[X]) := by
      rw [← hA, ← C_mul, mul_comm, one_add_mul_eulerB c hc]; simp
    have hC : C (-(1 + c)) = -(1 + C c) := by simp
    rw [hC, hA]
    linear_combination (((X : K[X]) + 1) ^ n - X ^ n + C c * (eulerPoly c n - X ^ n)) * hb

/-- Appell translation formula: $E_{c,n}(t+1) = \sum_{k\le n}\binom nk E_{c,k}(t)$. -/
@[kb "shimura2007" "§4.1, (4.3b), (4.3d), p. 25"]
theorem eulerPoly_comp_add_one_eq_sum (hc : 1 + c ≠ 0) (n : ℕ) :
    (eulerPoly c n).comp (X + 1)
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : K[X]) * eulerPoly c k := by
  rw [sum_choose_eulerPoly c hc]
  linear_combination eulerPoly_comp_add_one c hc n

/-- (4.3c): $E_{c,n+1}'(t) = (n+1)E_{c,n}(t)$. -/
@[kb "shimura2007" "§4.1, (4.3c), p. 25"]
theorem derivative_eulerPoly_succ (n : ℕ) :
    derivative (eulerPoly c (n + 1)) = ((n + 1 : ℕ) : K[X]) * eulerPoly c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hsum : derivative (∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose k : K[X]) * eulerPoly c k)
        = ((n + 1 : ℕ) : K[X]) * ∑ k ∈ Finset.range n, (n.choose k : K[X]) * eulerPoly c k := by
      rw [derivative_sum, Finset.sum_range_succ', Finset.mul_sum]
      simp only [eulerPoly_zero, derivative_one, mul_zero, add_zero, derivative_natCast_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [ih k (Finset.mem_range.1 hk)]
      have := Nat.add_one_mul_choose_eq n k
      have h2 : ((n + 1 : ℕ) : K[X]) * (n.choose k : K[X]) = ((n + 1).choose (k + 1) : K[X]) * (k + 1 : ℕ) := by
        exact_mod_cast this
      linear_combination (-eulerPoly c k) * h2
    rw [eulerPoly_eq c (n + 1), derivative_add, derivative_X_pow, derivative_C_mul, hsum]
    conv_rhs => rw [eulerPoly_eq c n]
    simp
    ring

/-- The generating function (4.2) of the generalized Euler polynomials, in $K[t][[z]]$:
$(1+c)e^{tz} = (e^z + c)\sum_n E_{c,n}(t)z^n/n!$. -/
@[kb "shimura2007" "§4.1, (4.2), p. 25"]
theorem eulerPoly_generating_function (hc : 1 + c ≠ 0) :
    PowerSeries.C (C (1 + c)) * PowerSeries.mk (fun n ↦ C ((n.factorial : K)⁻¹) * X ^ n)
      = (PowerSeries.exp K[X] + PowerSeries.C (C c)) *
        PowerSeries.mk (fun n ↦ C ((n.factorial : K)⁻¹) * eulerPoly c n) := by
  refine PowerSeries.ext fun n => ?_
  rw [add_mul, LinearMap.map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, mul_comm (PowerSeries.exp K[X]), PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff k) (PowerSeries.mk fun n ↦ C ((n.factorial : K)⁻¹) * eulerPoly c n) *
        (PowerSeries.coeff (n - k)) (PowerSeries.exp K[X])
      = C ((n.factorial : K)⁻¹) * ((n.choose k : K[X]) * eulerPoly c k) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [PowerSeries.coeff_exp, PowerSeries.coeff_mk]
    have h1 : (algebraMap ℚ K[X]) (1 / ((n - k).factorial : ℚ)) = C (((n - k).factorial : K)⁻¹) := by
      simp
    rw [h1, mul_comm]
    have hK : ((n - k).factorial : K)⁻¹ * (k.factorial : K)⁻¹
        = (n.factorial : K)⁻¹ * (n.choose k : K) := by
      rw [Nat.cast_choose K hkn]
      have h1 : ((n - k).factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have h2 : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have h3 : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      field_simp
    have hch : (n.choose k : K[X]) = C (n.choose k : K) := by simp
    rw [hch, ← mul_assoc, ← C_mul, hK, C_mul, mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_choose_eulerPoly c hc n]
  ring

theorem derivative_binomial_sum (a : ℕ → K) (n : ℕ) :
    derivative (∑ k ∈ Finset.range (n + 2), C ((n + 1).choose k * a k) * (X : K[X]) ^ (n + 1 - k))
      = ((n + 1 : ℕ) : K[X]) *
        ∑ k ∈ Finset.range (n + 1), C (n.choose k * a k) * (X : K[X]) ^ (n - k) := by
  rw [derivative_sum, Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, mul_one, derivative_C, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [derivative_C_mul_X_pow]
  have h1 : n + 1 - k - 1 = n - k := by omega
  have h2 : (n.choose k : K) * (n + 1 : ℕ) = ((n + 1).choose k : K) * ((n + 1 - k : ℕ) : K) := by
    exact_mod_cast Nat.choose_mul_succ_eq n k
  rw [h1, show ((n + 1 : ℕ) : K[X]) = C ((n + 1 : ℕ) : K) by simp, ← mul_assoc, ← C_mul]
  congr 2
  linear_combination (a k) * (-h2)

/-- Binomial (Appell) form: $E_{c,n}(t) = \sum_{k\le n}\binom nk E_{c,k}(0)\,t^{n-k}$. -/
@[kb "shimura2007" "§4.1, (4.3c), p. 25"]
theorem eulerPoly_eq_sum_eval_zero (n : ℕ) :
    eulerPoly c n = ∑ k ∈ Finset.range (n + 1),
      C ((n.choose k : K) * (eulerPoly c k).eval 0) * (X : K[X]) ^ (n - k) := by
  induction n with
  | zero => simp [eulerPoly_zero]
  | succ n ih =>
    set S := ∑ k ∈ Finset.range (n + 1 + 1),
      C (((n + 1).choose k : K) * (eulerPoly c k).eval 0) * (X : K[X]) ^ (n + 1 - k) with hS
    have hder := derivative_binomial_sum (fun k => (eulerPoly c k).eval 0) n
    have hd : derivative (eulerPoly c (n + 1) - S) = 0 := by
      rw [derivative_sub, derivative_eulerPoly_succ, hS, hder, ← ih, sub_self]
    have ha := Polynomial.eq_C_of_derivative_eq_zero hd
    set a := (eulerPoly c (n + 1) - S).coeff 0
    have hS0 : S.eval 0 = (eulerPoly c (n + 1)).eval 0 := by
      rw [hS, eval_finsetSum, Finset.sum_range_succ, Finset.sum_eq_zero]
      · simp
      · intro k hk
        have : n + 1 - k ≠ 0 := by have := Finset.mem_range.1 hk; omega
        simp [zero_pow this]
    have ha0 : a = 0 := by
      have := congrArg (eval 0) ha
      rw [eval_sub, hS0, eval_C] at this
      linear_combination -this
    rw [ha0, map_zero, sub_eq_zero] at ha
    exact ha

end ModularFormsKB.Shimura2007
