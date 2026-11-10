import ModularFormsKB.Milne.Ch11.WeilZeta
import ModularFormsKB.Milne.Ch11.WeilLPolynomial
import ModularFormsKB.Milne.Ch11.WeilNewton
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Milne, Section 11: `WeilZetaRationality` from the $L$-polynomial

Assembly of `ModularFormsKB.Milne.Ch11.WeilZeta` and `ModularFormsKB.Milne.Ch11.WeilLPolynomial`: the named
statement `WeilZetaRationality` (the $\alpha_i$ and the point counts $N_n = 1 + q^n - \sum\alpha_i^n$) follows from
`ZetaLPolynomial` and `ZetaNewtonIdentity`. With `weilCurveTheorem_of_zetaRationality_of_hasseWeilBound` this
reduces `WeilCurveTheorem` (Milne, Theorem 11.4) to `ZetaLPolynomial`, `ZetaNewtonIdentity` and `HasseWeilBound`.
-/

open Finset Polynomial

namespace ModularFormsKB.Milne

universe u v

/-- Two sequences satisfying the same Newton recursion against a sequence with $A_0 = 1$ agree: if
$\sum_{j < n} D_{j+1} A_{n-1-j} = 0$ for all $n$, then $D_m = 0$ for all $m \ge 1$. -/
lemma eq_zero_of_newton_sum_eq_zero (D A : ℕ → ℂ) (hA0 : A 0 = 1)
    (h : ∀ n, ∑ j ∈ range n, D (j + 1) * A (n - 1 - j) = 0) (m : ℕ) : D (m + 1) = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hm := h (m + 1)
    rw [sum_range_succ, show m + 1 - 1 - m = 0 by omega, hA0, mul_one] at hm
    have : ∑ j ∈ range m, D (j + 1) * A (m + 1 - 1 - j) = 0 :=
      sum_eq_zero fun j hj => by rw [ih j (mem_range.mp hj), zero_mul]
    rw [this, zero_add] at hm
    exact hm

/-- **`WeilZetaRationality` from the $L$-polynomial and the Newton identity.** -/
theorem weilZetaRationality_of_zetaLPolynomial (hL : ZetaLPolynomial.{u, v})
    (hN : ZetaNewtonIdentity.{u, v}) : WeilZetaRationality.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  obtain ⟨L, hdeg, h0, hFE, hZ⟩ := hL.lpoly k F hF hex
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  obtain ⟨α, hint, hne, hfac, σ, hσ⟩ :=
    exists_reciprocalRoots (TauCeti.genus k F) (Nat.card k) hq L hdeg h0 hFE
  refine ⟨α, hint, hne, ?_, σ, hσ⟩
  set A : ℕ → ℂ := fun n => (effectiveDivisorCount k F n : ℂ) with hA
  -- the power series identity over `ℂ`
  have hZc : (1 - PowerSeries.X) * (1 - PowerSeries.C (Nat.card k : ℂ) * PowerSeries.X) *
      PowerSeries.mk A = ((∏ i, (1 - C (α i) * X) : ℂ[X]) : PowerSeries ℂ) := by
    rw [← hfac, Polynomial.polynomial_map_coe, ← hZ, map_mul, map_mul, map_sub, map_sub, map_one,
      PowerSeries.map_X, map_mul, PowerSeries.map_C, PowerSeries.map_X]
    congr 1
  -- coefficient zero gives `A 0 = 1`
  have hA0 : A 0 = 1 := by
    have h1 := congrArg PowerSeries.constantCoeff hZ
    simp only [map_mul, map_sub, map_one, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C,
      mul_zero, sub_zero, one_mul, Polynomial.constantCoeff_coe, PowerSeries.constantCoeff_mk,
      h0] at h1
    simp only [hA]
    exact_mod_cast h1
  have hM := newton_of_mul_eq_prod (Nat.card k : ℂ) α A hZc
  have hNc : ∀ n : ℕ, (n : ℂ) * A n =
      ∑ j ∈ range n, (curvePointCount k F (j + 1) : ℂ) * A (n - 1 - j) := by
    intro n
    have := hN.newton k F hF n
    simp only [hA]
    exact_mod_cast this
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := eq_zero_of_newton_sum_eq_zero
    (fun j => (curvePointCount k F j : ℂ) - (1 + (Nat.card k : ℂ) ^ j - ∑ i, α i ^ j)) A hA0
    (fun n => by
      have e := (hNc n).symm.trans (hM n)
      rw [← sub_eq_zero, ← sum_sub_distrib] at e
      rw [← e]
      exact sum_congr rfl fun j _ => by beta_reduce; ring) m
  exact sub_eq_zero.mp this

/-- **Theorem 11.4** (Milne; Weil) from the $L$-polynomial (`ZetaLPolynomial`) and the Hasse–Weil bound
(`HasseWeilBound`); the Newton identity is proved (`zetaNewtonIdentity`). -/
theorem weilCurveTheorem_of_zetaLPolynomial_of_hasseWeilBound (hL : ZetaLPolynomial.{u, v})
    (hB : HasseWeilBound.{u, v}) : WeilCurveTheorem.{u, v} :=
  weilCurveTheorem_of_zetaRationality_of_hasseWeilBound
    (weilZetaRationality_of_zetaLPolynomial hL zetaNewtonIdentity) hB

end ModularFormsKB.Milne
