import ModularFormsKB.Milne.Ch11.WeilRationality
import ModularFormsKB.Milne.Ch11.WeilAssembly

/-!
# Milne, Section 11: the Hasse–Weil bound from its even-degree case and F. K. Schmidt's theorem

Bombieri's method (Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section 5.2) bounds the number of
rational places of a function field over $\mathbb F_q$ only when $q$ is a square (and large); applied to the
constant field extensions $F\cdot\mathbb F_{q^n}$ (`card_degree_one_constantCompositum`) it bounds $N_n(F)$ for even
$n$ large. This file shows that this suffices, given the $L$-polynomial (from `SchmidtDegreeOne`): the bound along
even $n$ makes the power sums of $\alpha_i q^{-1/2}$ bounded along even $n$, so $|\alpha_i| \le q^{1/2}$
(`norm_le_one_of_norm_sum_pow_le_of_dvd`), and then $|N_n - (q^n + 1)| = |\sum_i\alpha_i^n| \le 2g\,q^{n/2}$ for every
$n \ge 1$ (Stichtenoth, Theorem 5.1.15 (c)).

- `HasseWeilBoundEven`: named statement, the bound for even $n \ge n_0$.
- `hasseWeilBound_of_schmidt_of_even`: `HasseWeilBound` from `SchmidtDegreeOne` and `HasseWeilBoundEven`.
- `weilCurveTheorem_of_schmidt_of_even`: **Theorem 11.4** from `SchmidtDegreeOne` and `HasseWeilBoundEven`.
-/

open Finset TauCeti

namespace ModularFormsKB.Milne

universe u v

/-- **The Hasse–Weil bound in even degrees, up to a constant** (Stichtenoth, Theorem 5.2.3 for the constant field
extensions $F\cdot\mathbb F_{q^n}$, $n$ even and large; Stepanov–Bombieri), as a named statement. -/
@[kb "stichtenoth2009" "Theorem 5.2.3, even-degree constant field extensions"]
structure HasseWeilBoundEven : Prop where
  bound : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    IsFunctionField k F → IsIntegrallyClosedIn k F →
    ∃ (C : ℝ) (n₀ : ℕ), ∀ n : ℕ, n₀ ≤ n → 2 ∣ n →
      |(curvePointCount k F n : ℝ) - ((Nat.card k : ℝ) ^ n + 1)| ≤ C * Real.sqrt (Nat.card k) ^ n

/-- **`HasseWeilBound` from `SchmidtDegreeOne` and `HasseWeilBoundEven`**, with constant $2g$. -/
theorem hasseWeilBound_of_schmidt_of_even (hS : SchmidtDegreeOne.{u, v})
    (hE : HasseWeilBoundEven.{u, v}) : HasseWeilBound.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  obtain ⟨α, -, -, hN, -⟩ := (weilZetaRationality_of_zetaLPolynomial (zetaLPolynomial_of_schmidt hS)
    zetaNewtonIdentity).rational k F hF hex
  obtain ⟨C, n₀, hC⟩ := hE.bound k F hF hex
  set q : ℝ := (Nat.card k : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Nat.card_pos
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  -- `∑ α_i^n = q^n + 1 - N_n`
  have hαsum : ∀ n, 1 ≤ n → ∑ j, α j ^ n = (((q ^ n + 1 - curvePointCount k F n : ℝ)) : ℂ) := by
    intro n hn
    push_cast
    rw [hN n hn, hq]; push_cast; ring
  -- `|α_i| ≤ √q`
  have hle : ∀ i, ‖α i‖ ≤ Real.sqrt q := by
    intro i
    set β : Fin (2 * genus k F) → ℂ := fun j => α j / (Real.sqrt q : ℂ) with hβ
    have hb := norm_le_one_of_norm_sum_pow_le_of_dvd β C (max n₀ 1) 2 (by norm_num) (fun n hn h2 => by
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
      have hsum : ∑ j, β j ^ n = (∑ j, α j ^ n) / (Real.sqrt q : ℂ) ^ n := by
        rw [sum_div]; exact sum_congr rfl fun j _ => by rw [hβ, div_pow]
      rw [hsum, hαsum n hn1, norm_div, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hs0, div_le_iff₀ (pow_pos hs0 n), abs_sub_comm]
      have := hC n (le_trans (le_max_left _ _) hn) h2
      convert this using 2) i
    rw [hβ, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, div_le_one hs0] at hb
    exact hb
  refine ⟨2 * genus k F, fun n hn => ?_⟩
  have h1 : |(curvePointCount k F n : ℝ) - (q ^ n + 1)| = ‖∑ j, α j ^ n‖ := by
    rw [hαsum n hn, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  rw [h1]
  calc ‖∑ j, α j ^ n‖ ≤ ∑ j, ‖α j‖ ^ n := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [norm_pow]
    _ ≤ ∑ _j : Fin (2 * genus k F), Real.sqrt q ^ n :=
        sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hle j) n
    _ = (2 * genus k F : ℕ) * Real.sqrt q ^ n := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := by push_cast; ring

/-- **Theorem 11.4** (Milne; Weil) from F. K. Schmidt's theorem and the even-degree Hasse–Weil bound. -/
theorem weilCurveTheorem_of_schmidt_of_even (hS : SchmidtDegreeOne.{u, v})
    (hE : HasseWeilBoundEven.{u, v}) : WeilCurveTheorem.{u, v} :=
  weilCurveTheorem_of_zetaLPolynomial_of_hasseWeilBound (zetaLPolynomial_of_schmidt hS)
    (hasseWeilBound_of_schmidt_of_even hS hE)

end ModularFormsKB.Milne
