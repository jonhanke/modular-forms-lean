import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Homogenized polynomials in a power series with constant term one

For $H = 1 + O(X)$ in $K[[X]]$ and $f_0, \dots, f_D \in K$, put
$\operatorname{homog}(H, D, f) = \sum_{i \le D} f_i X^{D-i} H^i$ (this is $X^D f(H/X)$; with $H = qj$ it is
$q^D f(j)$). The map $f \mapsto \operatorname{homog}(H, D, f)$ is unitriangular: its constant coefficient is $f_D$.
Hence it is injective (`eq_zero_of_homog_eq_zero`), and if $H$ and all coefficients of
$\operatorname{homog}(H, D, f)$ lie in a subring $S$ then so do all $f_i$ (`mem_of_homog_mem`). Over
$\mathbb Z/p$, $f^p = f(X^p)$ (`pow_char_eq_expand`). Used for the integrality of the modular polynomial and for
Kronecker's congruence (Milne, Section 6, proof of Theorem 6.1, pdf pp. 88–89).
-/

open PowerSeries

noncomputable section

namespace ModularFormsKB.Milne.Triangular

variable {K : Type*} [CommRing K]

/-- $\sum_{i \le D} f_i X^{D-i} H^i$. -/
def homog (H : PowerSeries K) (D : ℕ) (f : ℕ → K) : PowerSeries K :=
  ∑ i ∈ Finset.range (D + 1), C (f i) * X ^ (D - i) * H ^ i

theorem constantCoeff_homog (H : PowerSeries K) (hH0 : constantCoeff H = 1) (D : ℕ) (f : ℕ → K) :
    constantCoeff (homog H D f) = f D := by
  simp only [homog, map_sum, map_mul, map_pow, constantCoeff_C, constantCoeff_X, hH0, one_pow, mul_one]
  rw [Finset.sum_eq_single D]
  · simp
  · intro i hi hiD
    have : D - i ≠ 0 := by
      have := Finset.mem_range.1 hi
      omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self D)) h

theorem homog_succ (H : PowerSeries K) (D : ℕ) (f : ℕ → K) :
    homog H (D + 1) f = C (f (D + 1)) * H ^ (D + 1) + X * homog H D f := by
  simp only [homog]
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one,
    add_comm (C (f (D + 1)) * H ^ (D + 1))]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := Finset.mem_range.1 hi
  have : D + 1 - i = (D - i) + 1 := by omega
  rw [this, pow_succ]
  ring

theorem eq_zero_of_homog_eq_zero (H : PowerSeries K) (hH0 : constantCoeff H = 1) (D : ℕ) (f : ℕ → K)
    (h : homog H D f = 0) : ∀ i ≤ D, f i = 0 := by
  induction D with
  | zero =>
    intro i hi
    have := constantCoeff_homog H hH0 0 f
    rw [h, map_zero] at this
    obtain rfl : i = 0 := by omega
    exact this.symm
  | succ D ih =>
    have hD : f (D + 1) = 0 := by
      have := constantCoeff_homog H hH0 (D + 1) f
      rw [h, map_zero] at this
      exact this.symm
    have h2 : X * homog H D f = 0 := by
      have := homog_succ H D f
      rw [h, hD, map_zero, zero_mul, zero_add] at this
      exact this.symm
    have h3 : homog H D f = 0 := by
      ext n
      have := congrArg (coeff (n + 1)) h2
      rwa [coeff_succ_X_mul, map_zero] at this
    intro i hi
    rcases Nat.lt_or_ge i (D + 1) with hlt | hge
    · exact ih h3 i (by omega)
    · obtain rfl : i = D + 1 := by omega
      exact hD

theorem coeff_pow_mem (S : Subring K) (H : PowerSeries K) (hH : ∀ n, coeff n H ∈ S) (k n : ℕ) :
    coeff n (H ^ k) ∈ S := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ k ih =>
    rw [pow_succ, coeff_mul]
    exact S.sum_mem fun x _ ↦ S.mul_mem (ih _) (hH _)

theorem mem_of_homog_mem (S : Subring K) (H : PowerSeries K) (hH : ∀ n, coeff n H ∈ S)
    (hH0 : constantCoeff H = 1) (D : ℕ) (f : ℕ → K) (h : ∀ n, coeff n (homog H D f) ∈ S) :
    ∀ i ≤ D, f i ∈ S := by
  induction D with
  | zero =>
    intro i hi
    have := h 0
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_homog H hH0] at this
    obtain rfl : i = 0 := by omega
    exact this
  | succ D ih =>
    have hD : f (D + 1) ∈ S := by
      have := h 0
      rwa [coeff_zero_eq_constantCoeff_apply, constantCoeff_homog H hH0] at this
    have h3 : ∀ n, coeff n (homog H D f) ∈ S := by
      intro n
      have e : coeff n (homog H D f) =
          coeff (n + 1) (homog H (D + 1) f) - coeff (n + 1) (C (f (D + 1)) * H ^ (D + 1)) := by
        rw [homog_succ, map_add, coeff_succ_X_mul]
        ring
      rw [e, coeff_C_mul]
      exact S.sub_mem (h _) (S.mul_mem hD (coeff_pow_mem S H hH _ _))
    intro i hi
    rcases Nat.lt_or_ge i (D + 1) with hlt | hge
    · exact ih h3 i (by omega)
    · obtain rfl : i = D + 1 := by omega
      exact hD

theorem homog_sum_coeff {ι : Type*} (H : PowerSeries K) (D : ℕ) (s : Finset ι) (g : ι → Polynomial K) :
    homog H D (fun n ↦ (∑ j ∈ s, g j).coeff n) = ∑ j ∈ s, homog H D (fun n ↦ (g j).coeff n) := by
  simp only [homog, Polynomial.finsetSum_coeff, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem homog_C_mul_X_pow (H : PowerSeries K) (D : ℕ) (c : K) {m : ℕ} (hm : m ≤ D) :
    homog H D (fun n ↦ (Polynomial.C c * Polynomial.X ^ m).coeff n) = C c * X ^ (D - m) * H ^ m := by
  simp only [homog, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hm)) h

/-- **Frobenius on power series over $\mathbb Z/p$**: $f^p = f(X^p)$. -/
theorem pow_char_eq_expand (p : ℕ) [Fact p.Prime] (f : PowerSeries (ZMod p)) :
    f ^ p = expand p (Fact.out : p.Prime).ne_zero f := by
  have := FiniteField.PowerSeries.expand_card f
  simp only [ZMod.card] at this
  exact this.symm

end ModularFormsKB.Milne.Triangular
