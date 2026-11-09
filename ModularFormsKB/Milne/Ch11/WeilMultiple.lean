import ModularFormsKB.Milne.Ch11.SchmidtMain

/-!
# Milne, Section 11: Theorem 11.4 from a lower bound along multiples of some degree

A lower bound $N_n \ge q^n + 1 - Cq^{n/2}$ is only needed along the multiples $n$ of some $d \ge 1$ (with $n$ large):
together with Bombieri's upper bound (proved, `bombieriUpperBound`, for even $n$) it bounds the power sums of
$\alpha_i q^{-1/2}$ along the multiples of $2d$, which already forces $|\alpha_i| \le q^{1/2}$
(`norm_le_one_of_norm_sum_pow_le_of_dvd`). This weaker input (`HasseWeilLowerBoundMultiple`) is what the
Galois-closure argument produces after a constant field extension of degree $d$ (the constant field of the Galois
closure).

- `hasseWeilBound_of_schmidt_of_multiple`: the Hasse–Weil bound (constant $2g$) from F. K. Schmidt's theorem and a
  two-sided bound along multiples of $d$.
- `weilCurveTheorem_of_lowerBoundMultiple`: **Theorem 11.4** from `HasseWeilLowerBoundMultiple` alone.
-/

open Finset TauCeti

namespace ModularFormsKB.Milne

universe u v

/-- **A lower bound along the multiples of some degree** (Stichtenoth, Section 5.2, after a constant field
extension), as a named statement: there are $C$, $d \ge 1$ and $n_0$ with $N_n \ge q^n + 1 - Cq^{n/2}$ for all
$n \ge n_0$ divisible by $d$. -/
@[kb "stichtenoth2009" "Section 5.2, lower bound via a Galois closure"]
structure HasseWeilLowerBoundMultiple : Prop where
  bound : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
    IsFunctionField k F → IsIntegrallyClosedIn k F →
    ∃ (C : ℝ) (d n₀ : ℕ), 1 ≤ d ∧ ∀ n : ℕ, n₀ ≤ n → d ∣ n →
      (Nat.card k : ℝ) ^ n + 1 - C * Real.sqrt (Nat.card k) ^ n ≤ curvePointCount k F n

/-- The even-degree lower bound is the case $d = 2$. -/
theorem hasseWeilLowerBoundMultiple_of_even (h : HasseWeilLowerBoundEven.{u, v}) :
    HasseWeilLowerBoundMultiple.{u, v} :=
  ⟨fun k F _ _ _ _ hF hex => by
    obtain ⟨C, n₀, hC⟩ := h.bound k F hF hex
    exact ⟨C, 2, n₀, by norm_num, hC⟩⟩

/-- **The Hasse–Weil bound from F. K. Schmidt's theorem and a two-sided bound along multiples of $d$.** -/
theorem hasseWeilBound_of_schmidt_of_multiple (hS : SchmidtDegreeOne.{u, v})
    (hM : ∀ (k : Type u) (F : Type v) [Field k] [Finite k] [Field F] [Algebra k F],
      IsFunctionField k F → IsIntegrallyClosedIn k F →
      ∃ (C : ℝ) (d n₀ : ℕ), 1 ≤ d ∧ ∀ n : ℕ, n₀ ≤ n → d ∣ n →
        |(curvePointCount k F n : ℝ) - ((Nat.card k : ℝ) ^ n + 1)| ≤ C * Real.sqrt (Nat.card k) ^ n) :
    HasseWeilBound.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  obtain ⟨α, -, -, hN, -⟩ := (weilZetaRationality_of_zetaLPolynomial (zetaLPolynomial_of_schmidt hS)
    zetaNewtonIdentity).rational k F hF hex
  obtain ⟨C, d, n₀, hd, hC⟩ := hM k F hF hex
  set q : ℝ := (Nat.card k : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Nat.card_pos
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hαsum : ∀ n, 1 ≤ n → ∑ j, α j ^ n = (((q ^ n + 1 - curvePointCount k F n : ℝ)) : ℂ) := by
    intro n hn
    push_cast
    rw [hN n hn, hq]; push_cast; ring
  have hle : ∀ i, ‖α i‖ ≤ Real.sqrt q := by
    intro i
    set β : Fin (2 * genus k F) → ℂ := fun j => α j / (Real.sqrt q : ℂ) with hβ
    have hb := norm_le_one_of_norm_sum_pow_le_of_dvd β C (max n₀ 1) d hd (fun n hn h2 => by
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

/-- **Theorem 11.4** (Milne; Weil's Riemann hypothesis for curves over finite fields) from a lower bound along
the multiples of some degree: Bombieri's upper bound and F. K. Schmidt's theorem are proved. -/
theorem weilCurveTheorem_of_lowerBoundMultiple (hL : HasseWeilLowerBoundMultiple.{u, v}) :
    WeilCurveTheorem.{u, v} := by
  refine weilCurveTheorem_of_zetaLPolynomial_of_hasseWeilBound (zetaLPolynomial_of_schmidt schmidtDegreeOne)
    (hasseWeilBound_of_schmidt_of_multiple schmidtDegreeOne fun k F _ _ _ _ hF hex => ?_)
  obtain ⟨C, d, n₀, hd, hC⟩ := hL.bound k F hF hex
  refine ⟨max C (2 * genus k F + 1), 2 * d, max n₀ (4 * (genus k F + 1) + 1), by omega,
    fun n hn hdn => ?_⟩
  have h2 : 2 ∣ n := dvd_trans (dvd_mul_right 2 d) hdn
  have hdn' : d ∣ n := dvd_trans (dvd_mul_left d 2) hdn
  have hup := curvePointCount_le_of_bombieriUpper bombieriUpperBound hF hex n
    (le_trans (le_max_right _ _) hn) h2
  have hlow := hC n (le_trans (le_max_left _ _) hn) hdn'
  have hs : 0 ≤ Real.sqrt (Nat.card k) ^ n := by positivity
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_left C (2 * (genus k F : ℝ) + 1)) hs]
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_right C (2 * (genus k F : ℝ) + 1)) hs]

end ModularFormsKB.Milne
