import ModularFormsKB.Historical.Ramanujan.PowerSeriesBridge
import ModularFormsKB.Historical.Ramanujan.Congruences
import ModularFormsKB.Historical.Jacobi.TripleProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Jacobi's cube identity and Ramanujan's congruences, unconditionally

**Jacobi's identity** (*Fundamenta nova* (1829) § 66; used by Ramanujan, *Collected Papers* No. 25, § 2):
`∏_{n ≥ 1} (1 - xⁿ)³ = ∑_{k ≥ 0} (-1)ᵏ (2k + 1) x^{k(k+1)/2}`.

Proof. The library's sine form of the triple product (`triple_product_sin`) with `q² = x` and
`y → 0⁺`, after division by `2 sin y`, gives the analytic identity (`jacobi_cube_hasSum`): the left
side tends to `∏ (1 - xⁿ) · ∏ (1 - xⁿ)²` (dominated convergence for infinite products) and the right
side to `∑ (-1)ᵏ x^{k(k+1)/2} (2k + 1)` (dominated convergence, with `|sin (m y)| ≤ m |sin y|`).
Via `PowerSeriesBridge` (Cauchy product and uniqueness of power series on the unit disc) it becomes
the formal identity `eulerSeries_cube` in `ℤ⟦X⟧`, which feeds the `_of_cube` theorems of
`Congruences.lean` to give `ramanujanModFive`, `ramanujanModSeven`, `ramanujanModThirtyFive`.
-/

noncomputable section

open Filter Topology PowerSeries Finset ModularFormsKB.Historical.Jacobi

namespace ModularFormsKB.Historical.Ramanujan

theorem abs_sin_nat_mul_le (m : ℕ) (y : ℝ) : |Real.sin (m * y)| ≤ m * |Real.sin y| := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : Real.sin (((m + 1 : ℕ) : ℝ) * y) =
        Real.sin (m * y) * Real.cos y + Real.cos (m * y) * Real.sin y := by
      rw [← Real.sin_add]; congr 1; push_cast; ring
    rw [h]
    calc _ ≤ |Real.sin (m * y) * Real.cos y| + |Real.cos (m * y) * Real.sin y| := abs_add_le _ _
      _ ≤ |Real.sin (m * y)| + |Real.sin y| := by
        rw [abs_mul, abs_mul]
        gcongr
        · calc _ ≤ |Real.sin (m * y)| * 1 := by gcongr; exact Real.abs_cos_le_one _
            _ = _ := mul_one _
        · calc _ ≤ 1 * |Real.sin y| := by gcongr; exact Real.abs_cos_le_one _
            _ = _ := one_mul _
      _ ≤ _ := by push_cast; linarith

theorem tendsto_sin_ratio (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun y : ℝ ↦ Real.sin (a * y) / Real.sin y) (𝓝[>] 0) (𝓝 a) := by
  have h : ContinuousAt (fun y : ℝ ↦ a * Real.sinc (a * y) / Real.sinc y) 0 :=
    ((continuous_const.mul (Real.continuous_sinc.comp
      (continuous_const.mul continuous_id))).continuousAt).div
      Real.continuous_sinc.continuousAt (by simp)
  have h' := h.tendsto
  simp only [mul_zero, Real.sinc_zero, mul_one, div_one] at h'
  refine (h'.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
  have hs : Real.sin y ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy.1 (by linarith [Real.pi_gt_three,
    hy.2])).ne'
  have hy0 : y ≠ 0 := hy.1.ne'
  simp only [Real.sinc_apply, mul_eq_zero, ha, hy0, or_self, ite_false]
  field_simp

theorem multipliable_one_sub_pow {x : ℂ} (hx : ‖x‖ < 1) :
    Multipliable (fun n : ℕ ↦ (1 - x ^ (n + 1))) :=
  (hasProd_eulerFunction hx).multipliable

/-- **Jacobi's cube identity** (analytic form; *Fundamenta nova* (1829) § 66, the cube of Euler's
product, used by Ramanujan, *Collected Papers* No. 25, § 2): for `‖x‖ < 1`,
`∏_{n ≥ 1} (1 - xⁿ)³ = ∑_{k ≥ 0} (-1)ᵏ (2k + 1) x^{k(k+1)/2}`. Deduced from `triple_product_sin`
with `q² = x`, dividing by `2 sin y` and letting `y → 0⁺`. -/
@[kb "jacobi1829" "§ 66"]
theorem jacobi_cube_hasSum {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ ↦ (-1 : ℂ) ^ k * (2 * k + 1) * x ^ (k * (k + 1) / 2))
      ((∏' n : ℕ, (1 - x ^ (n + 1))) ^ 3) := by
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq x (two_pos : 0 < 2)
  have hqn : ‖q‖ < 1 := by
    by_contra hcon
    have : 1 ≤ ‖q‖ ^ 2 := one_le_pow₀ (not_lt.mp hcon)
    rw [← norm_pow, hq] at this
    linarith
  have h1 : ∀ n : ℕ, q ^ (2 * n + 2) = x ^ (n + 1) := by
    intro n; rw [← hq, ← pow_mul]; ring_nf
  have h2 : ∀ n : ℕ, q ^ (4 * n + 4) = (x ^ (n + 1)) ^ 2 := by
    intro n; rw [← hq, ← pow_mul, ← pow_mul]; ring_nf
  have h3 : ∀ n : ℕ, q ^ (n * (n + 1)) = x ^ (n * (n + 1) / 2) := by
    intro n
    rw [← hq, ← pow_mul, two_mul_triangular n]
  -- notation
  obtain ⟨P, hP⟩ : ∃ P : ℂ, P = ∏' n : ℕ, (1 - x ^ (n + 1)) := ⟨_, rfl⟩
  set c : ℕ → ℂ := fun n ↦ (-1 : ℂ) ^ n * x ^ (n * (n + 1) / 2) with hc
  have hxr : ‖x‖ ≤ 1 := hx.le
  -- the identity for 0 < y < 1
  have key : ∀ y : ℝ, 0 < y → y < 1 →
      P * ∏' n : ℕ, (1 + (-2 * x ^ (n + 1) * (Real.cos (2 * y) : ℂ) + (x ^ (n + 1)) ^ 2)) =
        ∑' n : ℕ, c n * (((Real.sin ((2 * n + 1) * y) / Real.sin y : ℝ)) : ℂ) := by
    intro y hy0 hy1
    have hs : Real.sin y ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi hy0 (by linarith [Real.pi_gt_three])).ne'
    have hsC : Complex.sin (y : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sin]; exact_mod_cast hs
    have h := triple_product_sin hqn (y : ℂ)
    simp_rw [h1, h2, h3] at h
    have e1 : ∀ n : ℕ, (1 - 2 * x ^ (n + 1) * Complex.cos (2 * (y : ℂ)) + (x ^ (n + 1)) ^ 2) =
        1 + (-2 * x ^ (n + 1) * (Real.cos (2 * y) : ℂ) + (x ^ (n + 1)) ^ 2) := by
      intro n
      have : Complex.cos (2 * (y : ℂ)) = (Real.cos (2 * y) : ℂ) := by push_cast; rfl
      rw [this]; ring
    simp_rw [e1] at h
    have e2 : ∀ n : ℕ, (-1 : ℂ) ^ n * x ^ (n * (n + 1) / 2) * Complex.sin ((2 * n + 1) * y) =
        (c n * (((Real.sin ((2 * n + 1) * y) / Real.sin y : ℝ)) : ℂ)) * Complex.sin y := by
      intro n
      have : (((Real.sin ((2 * n + 1) * y) / Real.sin y : ℝ)) : ℂ) =
          Complex.sin ((2 * n + 1) * y) / Complex.sin y := by push_cast; rfl
      rw [this, hc]
      field_simp
    simp_rw [e2] at h
    rw [tsum_mul_right, ← hP] at h
    have h' : (P * ∏' n : ℕ, (1 + (-2 * x ^ (n + 1) * (Real.cos (2 * y) : ℂ) +
        (x ^ (n + 1)) ^ 2))) * Complex.sin y =
        (∑' n : ℕ, c n * (((Real.sin ((2 * n + 1) * y) / Real.sin y : ℝ)) : ℂ)) *
          Complex.sin y := by
      linear_combination (1 / 2 : ℂ) * h
    exact mul_right_cancel₀ hsC h'
  -- summability and bounds
  have hxn : ‖‖x‖‖ < 1 := by simpa using hx
  have hxs : Summable (fun n : ℕ ↦ ‖x‖ ^ (n + 1)) := by
    simpa [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg x) hx).mul_right ‖x‖
  have hbs : Summable (fun n : ℕ ↦ (2 * (n : ℝ) + 1) * ‖x‖ ^ n) := by
    have h := ((summable_pow_mul_geometric_of_norm_lt_one 1 hxn).mul_left 2).add
      (summable_geometric_of_lt_one (norm_nonneg x) hx)
    refine h.congr fun n ↦ ?_
    simp only [pow_one]; ring
  have hcn : ∀ n : ℕ, ‖c n‖ ≤ ‖x‖ ^ n := by
    intro n
    have hle : n ≤ n * (n + 1) / 2 := by
      rcases n with _ | m
      · simp
      · rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
    rw [hc]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg x) hxr hle
  -- the limit of the left side
  have hL : Tendsto (fun y : ℝ ↦ ∏' n : ℕ, (1 + (-2 * x ^ (n + 1) * (Real.cos (2 * y) : ℂ) +
      (x ^ (n + 1)) ^ 2))) (𝓝[>] 0)
      (𝓝 (∏' n : ℕ, (1 + (-2 * x ^ (n + 1) + (x ^ (n + 1)) ^ 2)))) := by
    refine tendsto_tprod_one_add_of_dominated_convergence
      (g := fun n : ℕ ↦ -2 * x ^ (n + 1) + (x ^ (n + 1)) ^ 2)
      (bound := fun n : ℕ ↦ 3 * ‖x‖ ^ (n + 1)) (hxs.mul_left 3) (fun n ↦ ?_) ?_
    · have hcont : Continuous (fun y : ℝ ↦
          -2 * x ^ (n + 1) * (Real.cos (2 * y) : ℂ) + (x ^ (n + 1)) ^ 2) := by fun_prop
      have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    · refine Eventually.of_forall fun y n ↦ ?_
      have hcos : ‖((Real.cos (2 * y) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real]; simpa using Real.abs_cos_le_one _
      have hu0 : 0 ≤ ‖x‖ ^ (n + 1) := pow_nonneg (norm_nonneg x) _
      have hu : ‖x‖ ^ (n + 1) ≤ 1 := pow_le_one₀ (norm_nonneg x) hxr
      calc _ ≤ ‖-2 * x ^ (n + 1) * ((Real.cos (2 * y) : ℝ) : ℂ)‖ + ‖(x ^ (n + 1)) ^ 2‖ :=
            norm_add_le _ _
        _ = 2 * ‖x‖ ^ (n + 1) * ‖((Real.cos (2 * y) : ℝ) : ℂ)‖ + (‖x‖ ^ (n + 1)) ^ 2 := by
            simp [norm_pow]
        _ ≤ 3 * ‖x‖ ^ (n + 1) := by
            nlinarith [mul_nonneg hu0 (sub_nonneg.2 hcos), mul_nonneg hu0 (sub_nonneg.2 hu)]
  have hmul : Multipliable (fun n : ℕ ↦ (1 - x ^ (n + 1))) := multipliable_one_sub_pow hx
  have hLval : ∏' n : ℕ, (1 + (-2 * x ^ (n + 1) + (x ^ (n + 1)) ^ 2)) = P * P := by
    have : ∀ n : ℕ, (1 + (-2 * x ^ (n + 1) + (x ^ (n + 1)) ^ 2)) =
        (1 - x ^ (n + 1)) * (1 - x ^ (n + 1)) := fun n ↦ by ring
    simp_rw [this]
    rw [hmul.tprod_mul hmul, hP]
  rw [hLval] at hL
  -- the limit of the right side
  have hR : Tendsto (fun y : ℝ ↦ ∑' n : ℕ, c n * (((Real.sin ((2 * n + 1) * y) / Real.sin y : ℝ)) : ℂ))
      (𝓝[>] 0) (𝓝 (∑' n : ℕ, c n * (((2 * n + 1 : ℝ)) : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence
      (g := fun n : ℕ ↦ c n * (((2 * n + 1 : ℝ)) : ℂ))
      (bound := fun n : ℕ ↦ (2 * (n : ℝ) + 1) * ‖x‖ ^ n) hbs (fun n ↦ ?_) ?_
    · have h := tendsto_sin_ratio (2 * (n : ℝ) + 1) (by positivity)
      exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp h)
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy n
      have hs : 0 < Real.sin y :=
        Real.sin_pos_of_pos_of_lt_pi hy.1 (by linarith [Real.pi_gt_three, hy.2])
      have hb := abs_sin_nat_mul_le (2 * n + 1) y
      push_cast at hb
      have hr : |Real.sin ((2 * n + 1) * y) / Real.sin y| ≤ 2 * n + 1 := by
        rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
        rwa [abs_of_pos hs] at hb
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc _ ≤ ‖x‖ ^ n * (2 * (n : ℝ) + 1) := by gcongr; exact hcn n
        _ = _ := mul_comm _ _
  have hlim : Tendsto (fun y : ℝ ↦ P * ∏' n : ℕ, (1 + (-2 * x ^ (n + 1) *
      (Real.cos (2 * y) : ℂ) + (x ^ (n + 1)) ^ 2))) (𝓝[>] 0) (𝓝 (P * (P * P))) :=
    tendsto_const_nhds.mul hL
  have hlim' := hlim.congr' (by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy using key y hy.1 hy.2)
  have heq := tendsto_nhds_unique hR hlim'
  have hsum : Summable (fun k : ℕ ↦ c k * (((2 * k + 1 : ℝ)) : ℂ)) := by
    refine Summable.of_norm_bounded hbs fun k ↦ ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc _ ≤ ‖x‖ ^ k * (2 * (k : ℝ) + 1) := by gcongr; exact hcn k
      _ = _ := mul_comm _ _
  have e3 : (fun k : ℕ ↦ (-1 : ℂ) ^ k * (2 * k + 1) * x ^ (k * (k + 1) / 2)) =
      fun k : ℕ ↦ c k * (((2 * k + 1 : ℝ)) : ℂ) := by
    funext k; rw [hc]; push_cast; ring
  rw [e3, ← hP, show P ^ 3 = P * (P * P) by ring, ← heq]
  exact hsum.hasSum

/-! ### The formal identity -/

theorem triangular_strictMono : StrictMono (fun k : ℕ ↦ k * (k + 1) / 2) := by
  refine strictMono_nat_of_lt_succ fun k ↦ ?_
  have h1 := two_mul_triangular k
  have h2 := two_mul_triangular (k + 1)
  show k * (k + 1) / 2 < (k + 1) * (k + 1 + 1) / 2
  nlinarith

theorem le_triangular (k : ℕ) : k ≤ k * (k + 1) / 2 := by
  rcases k with _ | m
  · simp
  · rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith

theorem jacobiCubeCoeff_triangular (k : ℕ) :
    jacobiCubeCoeff (k * (k + 1) / 2) = (-1) ^ k * (2 * k + 1) := by
  unfold jacobiCubeCoeff
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    exact ite_eq_right_iff.mpr fun h ↦ absurd (triangular_strictMono.injective h) hj
  · intro hk
    exfalso
    exact hk (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_triangular k)))

theorem jacobiCubeCoeff_eq_zero {N : ℕ} (h : N ∉ Set.range (fun k : ℕ ↦ k * (k + 1) / 2)) :
    jacobiCubeCoeff N = 0 := by
  unfold jacobiCubeCoeff
  apply Finset.sum_eq_zero
  intro k _
  exact ite_eq_right_iff.mpr fun hk ↦ absurd ⟨k, hk⟩ h

theorem sumsTo_jacobiCube :
    SumsTo (PowerSeries.map (Int.castRingHom ℂ) jacobiCubeSeries)
      (fun x ↦ (∏' n : ℕ, (1 - x ^ (n + 1))) ^ 3) := by
  intro x hx
  have hT := triangular_strictMono.injective
  have hcoeff : ∀ N : ℕ, coeff N (PowerSeries.map (Int.castRingHom ℂ) jacobiCubeSeries) =
      (jacobiCubeCoeff N : ℂ) := by
    intro N
    simp [jacobiCubeSeries, coeff_map]
  have hzero : ∀ N : ℕ, N ∉ Set.range (fun k : ℕ ↦ k * (k + 1) / 2) →
      coeff N (PowerSeries.map (Int.castRingHom ℂ) jacobiCubeSeries) = 0 := by
    intro N hN
    rw [hcoeff, jacobiCubeCoeff_eq_zero hN]; simp
  have hxn : ‖‖x‖‖ < 1 := by simpa using hx
  have hbs : Summable (fun n : ℕ ↦ (2 * (n : ℝ) + 1) * ‖x‖ ^ n) := by
    have h := ((summable_pow_mul_geometric_of_norm_lt_one 1 hxn).mul_left 2).add
      (summable_geometric_of_lt_one (norm_nonneg x) hx)
    refine h.congr fun n ↦ ?_
    simp only [pow_one]; ring
  refine ⟨?_, ?_⟩
  · rw [← hT.summable_iff (f := fun N : ℕ ↦
      ‖coeff N (PowerSeries.map (Int.castRingHom ℂ) jacobiCubeSeries)‖ * ‖x‖ ^ N)]
    · refine Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
        (fun k ↦ ?_) hbs
      simp only [Function.comp_apply, hcoeff, jacobiCubeCoeff_triangular]
      push_cast
      have : ‖x‖ ^ (k * (k + 1) / 2) ≤ ‖x‖ ^ k :=
        pow_le_pow_of_le_one (norm_nonneg x) hx.le (le_triangular k)
      have hn : ‖(-1 : ℂ) ^ k * (2 * (k : ℂ) + 1)‖ = 2 * (k : ℝ) + 1 := by
        have : (2 * (k : ℂ) + 1) = (((2 * (k : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
        rw [norm_mul, norm_pow, this, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show (0 : ℝ) ≤ 2 * (k : ℝ) + 1 by positivity)]
        simp
      rw [hn]
      gcongr
    · intro N hN
      rw [hzero N hN]; simp
  · rw [← hT.hasSum_iff (f := fun N : ℕ ↦
      coeff N (PowerSeries.map (Int.castRingHom ℂ) jacobiCubeSeries) * x ^ N)]
    · convert jacobi_cube_hasSum hx using 1
      funext k
      simp only [Function.comp_apply, hcoeff, jacobiCubeCoeff_triangular]
      push_cast
      ring
    · intro N hN
      rw [hzero N hN, zero_mul]

/-- **Jacobi's cube identity** (*Fundamenta nova* (1829) § 66; Ramanujan, *Collected Papers* No. 25,
§ 2) as an identity of formal power series: `∏_{n ≥ 1} (1 - Xⁿ)³ = ∑_{k ≥ 0} (-1)ᵏ (2k + 1) X^{k(k+1)/2}`.
It follows from `jacobi_cube_hasSum` by uniqueness of power series expansions on the unit disc. -/
theorem eulerSeries_cube : eulerSeries ^ 3 = jacobiCubeSeries := by
  have h := (sumsTo_euler.pow 3).unique sumsTo_jacobiCube
  apply map_intCast_injective
  rw [map_pow]
  exact h

/-- **Ramanujan's congruence modulo 5** (No. 25, (1), p. 210; proof § 2, p. 211):
`p(5m + 4) ≡ 0 (mod 5)`. Unconditional, from Jacobi's cube identity. -/
@[kb "ramanujan1927" "No. 25, § 1, (1), p. 210; § 2, p. 211"]
theorem ramanujanModFive : RamanujanModFive := ramanujanModFive_of_cube eulerSeries_cube

/-- **Ramanujan's congruence modulo 7** (No. 25, (2), p. 210; proof § 3, p. 212):
`p(7m + 5) ≡ 0 (mod 7)`. Unconditional, from Jacobi's cube identity. -/
@[kb "ramanujan1927" "No. 25, § 1, (2), p. 210; § 3, p. 212"]
theorem ramanujanModSeven : RamanujanModSeven := ramanujanModSeven_of_cube eulerSeries_cube

/-- **Ramanujan's corollary modulo 35** (No. 25, (3), p. 210):
`p(35m + 19) ≡ 0 (mod 35)`. Unconditional, from Jacobi's cube identity. -/
@[kb "ramanujan1927" "No. 25, § 1, (3), p. 210"]
theorem ramanujanModThirtyFive : RamanujanModThirtyFive :=
  ramanujanModThirtyFive_of_cube eulerSeries_cube

end ModularFormsKB.Historical.Ramanujan
