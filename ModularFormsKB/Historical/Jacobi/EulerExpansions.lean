import ModularFormsKB.Historical.Jacobi.TripleProduct
import ModularFormsKB.Historical.Jacobi.LambertSeries
import ModularFormsKB.Citation
/-!
# Jacobi's first Euler-type expansion (first lemma)

Jacobi, *Fundamenta nova* (1829), § 64, lemma 1), pp. 180–181: for `‖q‖ < 1` and every `z`,

  `∏_{n ≥ 1} (1 + q^{2n-1} z) = ∑_{m ≥ 0} q^{m²} z^m / ((1 - q²)(1 - q⁴)⋯(1 - q^{2m}))`.

This is the first half of `JacobiEulerExpansions` (`LambertSeries.lean`, loose end LE-MF-0323). The proof is not
Jacobi's (a functional equation in `z`) but the limit `N → ∞` of Cauchy's finite `q`-binomial theorem
(`q_binomial`, `TripleProduct.lean`) with `Q = q²`, `y = qz`: `∏_{n < N} (1 + q^{2n+1} z) =
∑_{m ≤ N} [N, m]_{q²} q^{m²} z^m`, the Gaussian binomials tending to `1/((q²; q²)_m)` and being uniformly bounded
(`norm_gaussBinom_le`), so that Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) applies.
-/

noncomputable section

open Complex Finset Filter Topology

namespace ModularFormsKB.Historical.Jacobi

private lemma two_choose_add (j : ℕ) : 2 * j.choose 2 + j = j ^ 2 := by
  induction j with
  | zero => simp
  | succ j ih => rw [choose_two_succ]; nlinarith

private lemma summable_norm_sq_pow (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun j : ℕ ↦ ‖q ^ (j ^ 2) * z ^ j‖ := by
  have ht : Tendsto (fun j : ℕ ↦ ‖q‖ ^ j * ‖z‖) atTop (𝓝 (0 * ‖z‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq).mul_const _
  rw [zero_mul] at ht
  have hev : ∀ᶠ j : ℕ in atTop, ‖q‖ ^ j * ‖z‖ < 1 / 2 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually (g := fun j : ℕ ↦ (1 / 2 : ℝ) ^ j)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with j hj
  have : ‖q ^ (j ^ 2) * z ^ j‖ = (‖q‖ ^ j * ‖z‖) ^ j := by
    rw [norm_mul, norm_pow, norm_pow, mul_pow, ← pow_mul, sq]
  rw [norm_norm, this]
  exact pow_le_pow_left₀ (by positivity) hj.le j

/-- **Jacobi, § 64, lemma 1)** (*Fundamenta nova*, pp. 180–181, first half):
`∏_{n ≥ 0} (1 + q^{2n+1} z) = ∑_{m ≥ 0} q^{m²} z^m / ∏_{j < m} (1 - q^{2(j+1)})` for `‖q‖ < 1`. -/
@[kb "jacobi1829" "§ 64, 1), pp. 180–181"]
theorem jacobiEulerExpansionOne (q z : ℂ) (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ ↦ 1 + q ^ (2 * n + 1) * z)
      (∑' m : ℕ, q ^ (m ^ 2) * z ^ m / ∏ j ∈ range m, (1 - q ^ (2 * (j + 1)))) := by
  have hQ : ‖q ^ 2‖ < 1 := norm_sq_lt_one hq
  have hE := eulerProd_ne_zero hQ
  set C : ℝ := Real.exp (‖q ^ 2‖ / (1 - ‖q ^ 2‖)) /
      (Real.exp (-(‖q ^ 2‖ / (1 - ‖q ^ 2‖) / (1 - ‖q ^ 2‖))) *
        Real.exp (-(‖q ^ 2‖ / (1 - ‖q ^ 2‖) / (1 - ‖q ^ 2‖)))) with hC
  -- finite product as a tsum
  have hfin : ∀ N : ℕ, ∏ n ∈ range N, (1 + q ^ (2 * n + 1) * z) =
      ∑' j : ℕ, gaussBinom (q ^ 2) N j * (q ^ (j ^ 2) * z ^ j) := by
    intro N
    have h := q_binomial hQ (q * z) N
    have e1 : ∏ n ∈ range N, (1 + q ^ (2 * n + 1) * z) =
        ∏ k ∈ range N, (1 + q * z * (q ^ 2) ^ k) :=
      prod_congr rfl fun n _ ↦ by rw [← pow_mul]; ring
    rw [e1, h, tsum_eq_sum (s := range (N + 1))]
    · refine sum_congr rfl fun j _ ↦ ?_
      have : (q ^ 2) ^ j.choose 2 * (q * z) ^ j = q ^ (j ^ 2) * z ^ j := by
        rw [← pow_mul, mul_pow, ← mul_assoc, ← pow_add, two_choose_add j]
      rw [mul_assoc, this]
    · intro j hj
      rw [gaussBinom_of_lt (by simpa using hj), zero_mul]
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun N j ↦ gaussBinom (q ^ 2) N j * (q ^ (j ^ 2) * z ^ j))
    (g := fun j : ℕ ↦ (qPoch (q ^ 2) j)⁻¹ * (q ^ (j ^ 2) * z ^ j))
    (bound := fun j : ℕ ↦ C * ‖q ^ (j ^ 2) * z ^ j‖)
    ((summable_norm_sq_pow q z hq).mul_left _) (fun j ↦ ?_)
    (Eventually.of_forall fun N j ↦ ?_)
  · have hmult : Multipliable fun n : ℕ ↦ 1 + q ^ (2 * n + 1) * z :=
      (multipliable_one_add_odd z hq).congr fun n ↦ by ring
    have hP := hmult.hasProd.tendsto_prod_nat
    have hT' := hT.congr fun N ↦ (hfin N).symm
    have h := tendsto_nhds_unique hP hT'
    have e : (∑' j : ℕ, (qPoch (q ^ 2) j)⁻¹ * (q ^ (j ^ 2) * z ^ j)) =
        ∑' m : ℕ, q ^ (m ^ 2) * z ^ m / ∏ j ∈ range m, (1 - q ^ (2 * (j + 1))) := by
      refine tsum_congr fun m ↦ ?_
      have : qPoch (q ^ 2) m = ∏ j ∈ range m, (1 - q ^ (2 * (j + 1))) := by
        unfold qPoch; exact prod_congr rfl fun i _ ↦ by rw [← pow_mul]
      rw [← this]; ring
    rw [← e, ← h]
    exact hmult.hasProd
  · have h1 : Tendsto (fun N : ℕ ↦ gaussBinom (q ^ 2) N j) atTop (𝓝 (qPoch (q ^ 2) j)⁻¹) := by
      have h2 : Tendsto (fun N : ℕ ↦ qPoch (q ^ 2) N) atTop (𝓝 (eulerProd (q ^ 2))) :=
        tendsto_qPoch hQ
      have h3 : Tendsto (fun N : ℕ ↦ qPoch (q ^ 2) (N - j)) atTop (𝓝 (eulerProd (q ^ 2))) :=
        (tendsto_qPoch hQ).comp
          (tendsto_atTop_atTop.mpr fun b ↦ ⟨b + j, fun a ha ↦ by omega⟩)
      have h4 := h2.div (h3.const_mul (qPoch (q ^ 2) j))
        (mul_ne_zero (qPoch_ne_zero hQ j) hE)
      have e : eulerProd (q ^ 2) / (qPoch (q ^ 2) j * eulerProd (q ^ 2)) =
          (qPoch (q ^ 2) j)⁻¹ := by
        have := qPoch_ne_zero hQ j
        field_simp
      rw [e] at h4
      refine h4.congr' ?_
      filter_upwards [eventually_ge_atTop j] with N hN
      unfold gaussBinom
      rw [if_pos hN]; rfl
    exact h1.mul_const _
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_gaussBinom_le hQ N j) (norm_nonneg _)

/-- The first conjunct of `JacobiEulerExpansions` holds. -/
theorem jacobiEulerExpansions_left :
    ∀ q z : ℂ, ‖q‖ < 1 →
      HasProd (fun n : ℕ ↦ 1 + q ^ (2 * n + 1) * z)
        (∑' m : ℕ, q ^ (m ^ 2) * z ^ m / ∏ j ∈ range m, (1 - q ^ (2 * (j + 1)))) :=
  jacobiEulerExpansionOne

end ModularFormsKB.Historical.Jacobi
