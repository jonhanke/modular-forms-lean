import ModularFormsKB.Milne.Ch11.WeilUnconditional
import ModularFormsKB.Milne.Ch11.WeilAssembly
import ModularFormsKB.Milne.Ch11.WeilEven
import ModularFormsKB.Milne.Ch11.WeilBombieriSplit
import ModularFormsKB.Milne.Ch11.WeilBombieri

/-!
# Milne, Section 11: the intermediate named statements of Weil's theorem, unconditionally

The files of Section 11 prove `SchmidtDegreeOne`,
`ZetaNewtonIdentity`, `BombieriUpperBound` and `HasseWeilLowerBoundMultiple`, and reduce the other named steps of
the proof of Theorem 11.4 to them. Here the reductions are applied, so each step is a theorem with no hypothesis:

* `zetaLPolynomial`: the $L$-polynomial and functional equation of the zeta function (F. K. Schmidt);
* `weilZetaRationality`: the rationality of the zeta function with reciprocal roots;
* `hasseWeilBound`: $|N_n - (q^n + 1)| \le C q^{n/2}$ for all $n \ge 1$ (the argument of
  `weilCurveTheorem_of_lowerBoundMultiple`, kept as a statement of its own);
* `hasseWeilBoundEven`, `hasseWeilLowerBoundEven`: its even-degree consequences.
-/

open Finset TauCeti

namespace ModularFormsKB.Milne

universe u v

/-- The zeta function of a function field over a finite field is $L(t)/((1-t)(1-qt))$ with the functional
equation (Stichtenoth 5.1.15), proved: `zetaLPolynomial_of_schmidt` applied to F. K. Schmidt's theorem. -/
theorem zetaLPolynomial : ZetaLPolynomial.{u, v} :=
  zetaLPolynomial_of_schmidt schmidtDegreeOne

/-- Rationality of the zeta function (Milne, Section 11), proved. -/
theorem weilZetaRationality : WeilZetaRationality.{u, v} :=
  weilZetaRationality_of_zetaLPolynomial zetaLPolynomial zetaNewtonIdentity

/-- **The Hasse–Weil bound** $|N_n - (q^n + 1)| \le C\,q^{n/2}$, proved: Bombieri's upper bound and the lower
bound along multiples (`hasseWeilLowerBoundMultiple`), combined as in `weilCurveTheorem_of_lowerBoundMultiple`. -/
theorem hasseWeilBound : HasseWeilBound.{u, v} := by
  refine hasseWeilBound_of_schmidt_of_multiple schmidtDegreeOne fun k F _ _ _ _ hF hex => ?_
  obtain ⟨C, d, n₀, hd, hC⟩ := hasseWeilLowerBoundMultiple.{u, v}.bound k F hF hex
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

/-- The Hasse–Weil bound in even degree, proved (a special case of `hasseWeilBound`). -/
theorem hasseWeilBoundEven : HasseWeilBoundEven.{u, v} :=
  ⟨fun k F _ _ _ _ hF hex => by
    obtain ⟨C, hC⟩ := hasseWeilBound.{u, v}.bound k F hF hex
    exact ⟨C, 1, fun n hn _ => hC n hn⟩⟩

/-- The Hasse–Weil lower bound in even degree, proved (a special case of `hasseWeilBound`). -/
theorem hasseWeilLowerBoundEven : HasseWeilLowerBoundEven.{u, v} :=
  ⟨fun k F _ _ _ _ hF hex => by
    obtain ⟨C, hC⟩ := hasseWeilBound.{u, v}.bound k F hF hex
    refine ⟨C, 1, fun n hn _ => ?_⟩
    have h := (abs_le.mp (hC n hn)).1
    linarith⟩

/-- **Bombieri's bound** $|N_1 - (q + 1)| \le (2g + 1)\sqrt q$, proved: from Weil's theorem,
$N_1 - (q + 1) = -\sum_i \alpha_i$ with $|\alpha_i| = \sqrt q$, so the difference is at most $2g\sqrt q$. -/
theorem bombieriBound : BombieriBound.{u, v} :=
  ⟨fun k F _ _ _ _ hF hex _ _ => by
    obtain ⟨α, -, hN, -, hα⟩ := weilCurveTheorem.{u, v}.weil k F hF hex
    have h1 := hN 1 le_rfl
    have hc : curvePointCount k F 1 = Nat.card {P : Place k F // P.degree = 1} := by
      simp [curvePointCount]
    rw [hc] at h1
    simp only [pow_one] at h1
    set N : ℝ := (Nat.card {P : Place k F // P.degree = 1} : ℝ)
    set q : ℝ := (Nat.card k : ℝ)
    have key : (((N - (q + 1) : ℝ)) : ℂ) = -∑ i, α i := by
      simp only [N, q]
      push_cast
      rw [h1]
      ring
    have habs : |N - (q + 1)| = ‖∑ i, α i‖ := by
      rw [← norm_neg (∑ i, α i), ← key, Complex.norm_real, Real.norm_eq_abs]
    rw [habs]
    calc ‖∑ i, α i‖ ≤ ∑ i, ‖α i‖ := norm_sum_le _ _
      _ = (2 * genus k F : ℕ) * Real.sqrt q := by simp [hα, q]
      _ ≤ (2 * genus k F + 1) * Real.sqrt q := by
          push_cast
          nlinarith [Real.sqrt_nonneg q]⟩

end ModularFormsKB.Milne
