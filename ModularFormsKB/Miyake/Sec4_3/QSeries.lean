import ModularFormsKB.Miyake.Sec4_3.Defs
import ModularFormsKB.Citation
/-!
# Miyake §4.3: $q$-series with coefficients of polynomial growth

* `Miyake.qSeries_lemma_4_3_3` (Lemma 4.3.3).
* Working lemmas: summability, holomorphy, bounds near the real axis and at $i\infty$, periodicity,
  convergence of the Dirichlet series, and the Mellin transform on the imaginary axis
  (`Miyake.hasMellin_qSeries`), which equals $\Lambda_N(s; f)$.
-/

open Complex Filter Asymptotics
open scoped Real

noncomputable section

namespace Miyake

variable {a : ℕ → ℂ}

/-- Elementary bound `x^ν e^{-cx} ≤ (ν/c)^ν e^{-ν}`. -/
private lemma rpow_mul_exp_le {c x ν : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hν : 0 < ν) :
    x ^ ν * Real.exp (-c * x) ≤ (ν / c) ^ ν * Real.exp (-ν) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = c * x / ν := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have h1 : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have h2 : u ^ ν ≤ Real.exp (u - 1) ^ ν := Real.rpow_le_rpow hu0 h1 hν.le
  have h3 : Real.exp (u - 1) ^ ν = Real.exp (c * x) * Real.exp (-ν) := by
    rw [← Real.exp_mul, ← Real.exp_add]; congr 1; rw [hu]; field_simp; ring
  have h4 : x = (ν / c) * u := by rw [hu]; field_simp
  have h5 : x ^ ν = (ν / c) ^ ν * u ^ ν := by
    conv_lhs => rw [h4]
    exact Real.mul_rpow (by positivity) hu0
  have h6 : Real.exp (c * x) * Real.exp (-c * x) = 1 := by rw [← Real.exp_add]; simp
  calc x ^ ν * Real.exp (-c * x) = (ν / c) ^ ν * u ^ ν * Real.exp (-c * x) := by rw [h5]
    _ ≤ (ν / c) ^ ν * (Real.exp (c * x) * Real.exp (-ν)) * Real.exp (-c * x) := by
        rw [← h3]; gcongr
    _ = (ν / c) ^ ν * Real.exp (-ν) * (Real.exp (c * x) * Real.exp (-c * x)) := by ring
    _ = _ := by rw [h6, mul_one]

/-- Termwise bound for the geometric comparison. -/
private lemma term_le {ν l : ℝ} (hν : 0 < ν) (hl : 0 < l) (n : ℕ) :
    ((n : ℝ) + 1) ^ ν * Real.exp (-l * n) ≤
      Real.exp l * ((ν / (l / 2)) ^ ν * Real.exp (-ν)) * Real.exp (-(l / 2) * ((n : ℝ) + 1)) := by
  have h := rpow_mul_exp_le (c := l / 2) (x := (n : ℝ) + 1) (by positivity) (by positivity) hν
  have e : Real.exp (-l * n) =
      Real.exp l * Real.exp (-(l / 2) * ((n : ℝ) + 1)) * Real.exp (-(l / 2) * ((n : ℝ) + 1)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e]
  calc ((n : ℝ) + 1) ^ ν * (Real.exp l * Real.exp (-(l / 2) * ((n : ℝ) + 1)) *
        Real.exp (-(l / 2) * ((n : ℝ) + 1)))
      = Real.exp l * (((n : ℝ) + 1) ^ ν * Real.exp (-(l / 2) * ((n : ℝ) + 1))) *
        Real.exp (-(l / 2) * ((n : ℝ) + 1)) := by ring
    _ ≤ _ := by gcongr

/-- Summability and size of `∑ (n+1)^ν e^{-l n}`. -/
private lemma summable_tsum_le {ν l : ℝ} (hν : 0 < ν) (hl : 0 < l) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ ν * Real.exp (-l * n)) ∧
    ∑' n : ℕ, ((n : ℝ) + 1) ^ ν * Real.exp (-l * n) ≤
      Real.exp l * ((ν / (l / 2)) ^ ν * Real.exp (-ν)) * (2 / l) := by
  set K := Real.exp l * ((ν / (l / 2)) ^ ν * Real.exp (-ν)) with hK
  have hK0 : 0 ≤ K := by positivity
  set r := Real.exp (-(l / 2)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 :=
    (Real.exp_lt_exp.2 (show -(l / 2) < 0 by linarith)).trans_eq Real.exp_zero
  have hg : ∀ n : ℕ, Real.exp (-(l / 2) * ((n : ℝ) + 1)) = r * r ^ n := by
    intro n
    rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have hgeo : HasSum (fun n : ℕ ↦ K * (r * r ^ n)) (K * (r * (1 - r)⁻¹)) :=
    ((hasSum_geometric_of_lt_one hr0.le hr1).mul_left r).mul_left K
  have hle : ∀ n : ℕ, ((n : ℝ) + 1) ^ ν * Real.exp (-l * n) ≤ K * (r * r ^ n) := by
    intro n
    have := term_le hν hl n
    rw [hg n] at this
    exact this
  have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) ^ ν * Real.exp (-l * n) := fun n => by positivity
  have hs : Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ ν * Real.exp (-l * n)) :=
    Summable.of_nonneg_of_le hnn hle hgeo.summable
  refine ⟨hs, ?_⟩
  have h1 : ∑' n : ℕ, ((n : ℝ) + 1) ^ ν * Real.exp (-l * n) ≤ K * (r * (1 - r)⁻¹) :=
    hgeo.tsum_eq ▸ Summable.tsum_le_tsum hle hs hgeo.summable
  have h2 : r * (1 - r)⁻¹ ≤ 2 / l := by
    have hx : (l / 2) * r ≤ 1 - r := by
      have h6 : r * Real.exp (l / 2) = 1 := by
        rw [hr, ← Real.exp_add]; simp
      have := Real.add_one_le_exp (l / 2)
      nlinarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by linarith) hl]
    nlinarith
  calc _ ≤ K * (r * (1 - r)⁻¹) := h1
    _ ≤ K * (2 / l) := by gcongr

/-- A coefficient bound `‖a n‖ ≤ C (n+1)^ν` from `a = O(n^ν)` with `ν > 0`. -/
private lemma bound_of_isBigO {ν : ℝ} (hν : 0 < ν)
    (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν := by
  obtain ⟨c, hc0, hc⟩ := ha.exists_nonneg
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hc.bound
  have hS : 0 ≤ ∑ i ∈ Finset.range n₀, ‖a i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨c + ∑ i ∈ Finset.range n₀, ‖a i‖, by positivity, fun n => ?_⟩
  have hpos : 1 ≤ ((n : ℝ) + 1) ^ ν :=
    Real.one_le_rpow (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) hν.le
  rcases lt_or_ge n n₀ with h | h
  · have h1 : ‖a n‖ ≤ ∑ i ∈ Finset.range n₀, ‖a i‖ :=
      Finset.single_le_sum (f := fun i => ‖a i‖) (fun i _ => norm_nonneg _) (Finset.mem_range.2 h)
    have h2 : 0 ≤ c * ((n : ℝ) + 1) ^ ν := by positivity
    nlinarith
  · have h1 := hn₀ n h
    rw [Real.norm_of_nonneg (Real.rpow_nonneg n.cast_nonneg _)] at h1
    have h2 : (n : ℝ) ^ ν ≤ ((n : ℝ) + 1) ^ ν :=
      Real.rpow_le_rpow n.cast_nonneg (by linarith) hν.le
    have h3 : 0 ≤ (∑ i ∈ Finset.range n₀, ‖a i‖) * ((n : ℝ) + 1) ^ ν := by positivity
    nlinarith

/-- A coefficient bound with explicit constants: $\|a_n\| \le C (n+1)^\nu$ with $\nu > 0$. -/
lemma CoeffGrowth.exists_bound (ha : CoeffGrowth a) :
    ∃ C ν : ℝ, 0 < ν ∧ 0 ≤ C ∧ ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν := by
  obtain ⟨ν, hν⟩ := ha
  have h1 : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (max ν 1) := by
    refine hν.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_of_nonneg (Real.rpow_nonneg n.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg n.cast_nonneg _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hn' (le_max_left _ _)
  obtain ⟨C, hC, hb⟩ := bound_of_isBigO (lt_of_lt_of_le one_pos (le_max_right ν 1)) h1
  exact ⟨C, max ν 1, lt_of_lt_of_le one_pos (le_max_right ν 1), hC, hb⟩

/-- The twist of coefficients of polynomial growth has polynomial growth. -/
lemma CoeffGrowth.twist {m : ℕ} (ψ : DirichletCharacter ℂ m) (ha : CoeffGrowth a) :
    CoeffGrowth (twist ψ a) := by
  obtain ⟨ν, hν⟩ := ha
  refine ⟨ν, (IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)).trans hν⟩
  rw [Miyake.twist, norm_mul, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one ψ _)

/-- A scalar multiple of coefficients of polynomial growth has polynomial growth. -/
lemma CoeffGrowth.const_mul (c : ℂ) (ha : CoeffGrowth a) : CoeffGrowth fun n ↦ c * a n := by
  obtain ⟨ν, hν⟩ := ha
  exact ⟨ν, hν.const_mul_left c⟩

/-- Norm of a term of the `q`-series. -/
private lemma norm_term (a : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    ‖a n * cexp (2 * π * I * n * z)‖ = ‖a n‖ * Real.exp (-(2 * π * z.im) * n) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Uniform termwise bound on `Im z ≥ y₀`. -/
private lemma norm_term_le {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν) {y₀ : ℝ} {z : ℂ} (hz : y₀ ≤ z.im) (n : ℕ) :
    ‖a n * cexp (2 * π * I * n * z)‖ ≤
      C * (((n : ℝ) + 1) ^ ν * Real.exp (-(2 * π * y₀) * n)) := by
  rw [norm_term]
  have h : (2 * π * n) * y₀ ≤ (2 * π * n) * z.im :=
    mul_le_mul_of_nonneg_left hz (by positivity)
  calc ‖a n‖ * Real.exp (-(2 * π * z.im) * n)
      ≤ (C * ((n : ℝ) + 1) ^ ν) * Real.exp (-(2 * π * y₀) * n) :=
        mul_le_mul (hb n) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

private lemma summable_term {C ν : ℝ} (hν : 0 < ν) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    Summable (fun n : ℕ ↦ C * (((n : ℝ) + 1) ^ ν * Real.exp (-(2 * π * y₀) * n))) :=
  ((summable_tsum_le hν (by positivity : 0 < 2 * π * y₀)).1).mul_left C

private lemma summable_norm_of_bound {C ν : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℕ ↦ ‖a n * cexp (2 * π * I * n * z)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_term_le hC hb le_rfl n)
    (summable_term hν hz)

private lemma core_tendsto {C ν : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν) :
    TendstoLocallyUniformlyOn
      (fun (s : Finset ℕ) (z : ℂ) ↦ ∑ n ∈ s, a n * cexp (2 * π * I * n * z))
      (qSeries a) atTop {z : ℂ | 0 < z.im} := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  have hz' : 0 < z.im := hz
  refine ⟨{w : ℂ | z.im / 2 < w.im}, ?_, ?_⟩
  · apply mem_nhdsWithin_of_mem_nhds
    exact (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (show z.im / 2 < z.im by linarith)
  · exact tendstoUniformlyOn_tsum (summable_term hν (by linarith : 0 < z.im / 2))
      (fun n w hw => norm_term_le hC hb (le_of_lt hw) n)

private lemma core_diff {C ν : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν) :
    DifferentiableOn ℂ (qSeries a) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hopen : IsOpen {w : ℂ | z.im / 2 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd := differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℕ) (w : ℂ) => a n * cexp (2 * π * I * n * w))
    (summable_term (C := C) hν (by linarith : 0 < z.im / 2))
    (fun n => by fun_prop) hopen (fun n w hw => norm_term_le hC hb (le_of_lt hw) n)
  have hz2 : z ∈ {w : ℂ | z.im / 2 < w.im} := by
    show z.im / 2 < z.im
    linarith
  exact ((hd z hz2).differentiableAt (hopen.mem_nhds hz2)).differentiableWithinAt

/-- Splitting off the constant term. -/
private lemma sub_eq_tsum {z : ℂ}
    (hs : Summable fun n : ℕ ↦ a n * cexp (2 * π * I * n * z)) :
    qSeries a z - a 0 = ∑' n : ℕ, a (n + 1) * cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * z) := by
  unfold qSeries
  rw [hs.tsum_eq_zero_add]
  simp

private lemma core_small {C ν : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν) :
    ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → ‖qSeries a z‖ ≤ M * z.im ^ (-ν - 1) := by
  refine ⟨C * (Real.exp (2 * π) * ((ν / π) ^ ν * Real.exp (-ν)) / π), fun z hz hz1 => ?_⟩
  have hl : 0 < 2 * π * z.im := by positivity
  obtain ⟨hs, htsum⟩ := summable_tsum_le hν hl
  have h1 : ‖qSeries a z‖ ≤ C * ∑' n : ℕ, ((n : ℝ) + 1) ^ ν * Real.exp (-(2 * π * z.im) * n) := by
    have := tsum_of_norm_bounded ((hs.mul_left C).hasSum)
      (fun n => norm_term_le (z := z) hC hb le_rfl n)
    rw [tsum_mul_left] at this
    exact this
  have hy := hz
  have he : Real.exp (2 * π * z.im) ≤ Real.exp (2 * π) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  have hdiv : (ν / (2 * π * z.im / 2)) ^ ν = (ν / π) ^ ν / z.im ^ ν := by
    rw [show ν / (2 * π * z.im / 2) = (ν / π) / z.im by field_simp,
      Real.div_rpow (by positivity) hy.le]
  have hexp : z.im ^ (-ν - 1) = (z.im ^ ν)⁻¹ / z.im := by
    rw [Real.rpow_sub_one hy.ne', Real.rpow_neg hy.le]
  have hP : 0 < z.im ^ ν := Real.rpow_pos_of_pos hy ν
  calc ‖qSeries a z‖ ≤ C * ∑' n : ℕ, ((n : ℝ) + 1) ^ ν * Real.exp (-(2 * π * z.im) * n) := h1
    _ ≤ C * (Real.exp (2 * π * z.im) * ((ν / (2 * π * z.im / 2)) ^ ν * Real.exp (-ν)) *
          (2 / (2 * π * z.im))) := by gcongr
    _ = C * (Real.exp (2 * π * z.im) * ((ν / π) ^ ν * Real.exp (-ν)) / π *
          ((z.im ^ ν)⁻¹ / z.im)) := by
        rw [hdiv]; field_simp
    _ ≤ C * (Real.exp (2 * π) * ((ν / π) ^ ν * Real.exp (-ν)) / π *
          ((z.im ^ ν)⁻¹ / z.im)) := by gcongr
    _ = _ := by rw [hexp]; ring

private lemma core_large {C ν : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν) :
    ∃ M : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖qSeries a z - a 0‖ ≤ M * Real.exp (-2 * π * z.im) := by
  obtain ⟨hs, -⟩ := summable_tsum_le hν (show 0 < 2 * π by positivity)
  refine ⟨∑' n : ℕ, C * 2 ^ ν * (((n : ℝ) + 1) ^ ν * Real.exp (-(2 * π) * n)), fun z hz => ?_⟩
  have hz0 : 0 < z.im := by linarith
  have hsum : Summable (fun n : ℕ ↦ a n * cexp (2 * π * I * n * z)) :=
    (summable_norm_of_bound hν hC hb hz0).of_norm
  rw [sub_eq_tsum hsum]
  have hB : Summable fun n : ℕ ↦ C * 2 ^ ν * (((n : ℝ) + 1) ^ ν * Real.exp (-(2 * π) * n)) :=
    hs.mul_left _
  have key : ∀ n : ℕ, ‖a (n + 1) * cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * z)‖ ≤
      C * 2 ^ ν * (((n : ℝ) + 1) ^ ν * Real.exp (-(2 * π) * n)) * Real.exp (-2 * π * z.im) := by
    intro n
    rw [norm_term]
    have h1 : ‖a (n + 1)‖ ≤ C * 2 ^ ν * ((n : ℝ) + 1) ^ ν := by
      have := hb (n + 1)
      push_cast at this
      calc ‖a (n + 1)‖ ≤ C * ((n : ℝ) + 1 + 1) ^ ν := this
        _ ≤ C * (2 * ((n : ℝ) + 1)) ^ ν := by
            gcongr
            linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
        _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    have h2 : Real.exp (-(2 * π * z.im) * ((n + 1 : ℕ) : ℝ)) ≤
        Real.exp (-2 * π * z.im) * Real.exp (-(2 * π) * n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have : 0 ≤ (2 * π * n) * (z.im - 1) :=
        mul_nonneg (by positivity) (sub_nonneg.2 hz)
      push_cast
      nlinarith
    calc ‖a (n + 1)‖ * Real.exp (-(2 * π * z.im) * ((n + 1 : ℕ) : ℝ))
        ≤ (C * 2 ^ ν * ((n : ℝ) + 1) ^ ν) *
          (Real.exp (-2 * π * z.im) * Real.exp (-(2 * π) * n)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have := tsum_of_norm_bounded ((hB.mul_right (Real.exp (-2 * π * z.im))).hasSum) key
  rw [tsum_mul_right] at this
  exact this

/-- The $q$-series converges absolutely on $\operatorname{Im} z > 0$. -/
lemma summable_norm_qSeries (ha : CoeffGrowth a) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℕ ↦ ‖a n * cexp (2 * π * I * n * z)‖ := by
  obtain ⟨C, ν, hν, hC, hb⟩ := ha.exists_bound
  exact summable_norm_of_bound hν hC hb hz

lemma hasSum_qSeries (ha : CoeffGrowth a) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun n : ℕ ↦ a n * cexp (2 * π * I * n * z)) (qSeries a z) :=
  (summable_norm_qSeries ha hz).of_norm.hasSum

lemma differentiableOn_qSeries (ha : CoeffGrowth a) :
    DifferentiableOn ℂ (qSeries a) {z : ℂ | 0 < z.im} := by
  obtain ⟨C, ν, hν, hC, hb⟩ := ha.exists_bound
  exact core_diff hν hC hb

/-- The $q$-series has period $1$ (for every $z$; both sides are the same `tsum` termwise). -/
lemma qSeries_add_one (z : ℂ) : qSeries a (z + 1) = qSeries a z := by
  unfold qSeries
  congr 1
  ext n
  have : 2 * π * I * n * (z + 1) = 2 * π * I * n * z + n * (2 * π * I) := by ring
  rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma qSeries_add_nat (z : ℂ) (n : ℕ) : qSeries a (z + n) = qSeries a z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : z + ((n + 1 : ℕ) : ℂ) = (z + n) + 1 := by push_cast; ring
    rw [this, qSeries_add_one, ih]

/-- Growth near the real axis: $\|f(z)\| \le C \operatorname{Im}(z)^{-\mu}$ for $0 < \operatorname{Im} z \le 1$. -/
lemma qSeries_bound_small (ha : CoeffGrowth a) :
    ∃ C μ : ℝ, 0 < μ ∧ ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → ‖qSeries a z‖ ≤ C * z.im ^ (-μ) := by
  obtain ⟨C, ν, hν, hC, hb⟩ := ha.exists_bound
  obtain ⟨M, hM⟩ := core_small hν hC hb
  refine ⟨M, ν + 1, by linarith, fun z hz hz1 => ?_⟩
  have := hM z hz hz1
  rwa [show -(ν + 1) = -ν - 1 by ring]

/-- Exponential approach to $a_0$ at $i\infty$. -/
lemma qSeries_sub_bound_large (ha : CoeffGrowth a) :
    ∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖qSeries a z - a 0‖ ≤ C * Real.exp (-2 * π * z.im) := by
  obtain ⟨C, ν, hν, hC, hb⟩ := ha.exists_bound
  exact core_large hν hC hb

/-- **Miyake Lemma 4.3.3.** If $a_n = O(n^\nu)$ with $\nu > 0$, then
$f(z) = \sum_{n\ge0} a_n e^{2\pi i n z}$ converges absolutely and locally uniformly on $\mathbb H$, $f$ is
holomorphic on $\mathbb H$, $f(z) = O(\operatorname{Im}(z)^{-\nu-1})$ as $\operatorname{Im} z \to 0$ and
$f(z) - a_0 = O(e^{-2\pi \operatorname{Im} z})$ as $\operatorname{Im} z \to \infty$, both uniformly in
$\operatorname{Re} z$ (stated with explicit constants on $\operatorname{Im} z \le 1$ and
$\operatorname{Im} z \ge 1$). Relation: same. -/
@[kb "miyake1989" "§4.3, Lemma 4.3.3, p. 117"]
theorem qSeries_lemma_4_3_3 {ν : ℝ} (hν : 0 < ν)
    (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν) :
    (∀ z : ℂ, 0 < z.im → Summable fun n : ℕ ↦ ‖a n * cexp (2 * π * I * n * z)‖) ∧
    TendstoLocallyUniformlyOn (fun (s : Finset ℕ) (z : ℂ) ↦ ∑ n ∈ s, a n * cexp (2 * π * I * n * z))
      (qSeries a) atTop {z : ℂ | 0 < z.im} ∧
    DifferentiableOn ℂ (qSeries a) {z : ℂ | 0 < z.im} ∧
    (∃ C : ℝ, ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → ‖qSeries a z‖ ≤ C * z.im ^ (-ν - 1)) ∧
    (∃ C : ℝ, ∀ z : ℂ, 1 ≤ z.im → ‖qSeries a z - a 0‖ ≤ C * Real.exp (-2 * π * z.im)) := by
  obtain ⟨C, hC, hb⟩ := bound_of_isBigO hν ha
  exact ⟨fun z hz => summable_norm_of_bound hν hC hb hz, core_tendsto hν hC hb,
    core_diff hν hC hb, core_small hν hC hb, core_large hν hC hb⟩

/-- The Dirichlet series $\sum a_n n^{-s}$ converges absolutely for $\operatorname{Re} s > \nu + 1$. -/
lemma lSeriesSummable_of_isBigO {ν : ℝ} (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν) {s : ℂ}
    (hs : ν + 1 < s.re) : LSeriesSummable a s := by
  refine LSeriesSummable_of_isBigO_rpow (x := ν + 1) hs ?_
  simpa using ha

/-- The $q$-series on the imaginary axis, $t \mapsto f(it/\sqrt N)$, is continuous on $(0,\infty)$. -/
lemma continuousOn_qSeries_imag (ha : CoeffGrowth a) {N : ℝ} (hN : 0 < N) :
    ContinuousOn (fun t : ℝ ↦ qSeries a (I * ((t / √N : ℝ) : ℂ))) (Set.Ioi 0) := by
  have hsq : 0 < √N := Real.sqrt_pos.2 hN
  refine (differentiableOn_qSeries ha).continuousOn.comp (by fun_prop) (fun t ht => ?_)
  show 0 < (I * ((t / √N : ℝ) : ℂ)).im
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have : 0 < t := ht
  simp only [mul_zero, one_mul, zero_add]
  positivity

/-- Bound for `f - a₀` near the real axis from summability of `∑ ‖a_n‖ / n^σ`. -/
private lemma core_sub_small (ha : CoeffGrowth a) {σ : ℝ} (hσ : 0 < σ)
    (hsum : Summable fun n : ℕ ↦ ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ) :
    ∃ M : ℝ, ∀ z : ℂ, 0 < z.im → ‖qSeries a z - a 0‖ ≤ M * z.im ^ (-σ) := by
  refine ⟨(∑' n : ℕ, ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ) * ((σ / (2 * π)) ^ σ * Real.exp (-σ)),
    fun z hz => ?_⟩
  have hy := hz
  rw [sub_eq_tsum (summable_norm_qSeries ha hz).of_norm]
  have key : ∀ n : ℕ, ‖a (n + 1) * cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * z)‖ ≤
      ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ * ((σ / (2 * π)) ^ σ * Real.exp (-σ)) * z.im ^ (-σ) := by
    intro n
    rw [norm_term]
    have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ σ := by positivity
    have hn' := hn.ne'
    have hk := rpow_mul_exp_le (c := 2 * π * z.im) (x := (n : ℝ) + 1) (by positivity)
      (by positivity) hσ
    have hdiv : (σ / (2 * π * z.im)) ^ σ = (σ / (2 * π)) ^ σ * z.im ^ (-σ) := by
      rw [show σ / (2 * π * z.im) = (σ / (2 * π)) / z.im by field_simp,
        Real.div_rpow (by positivity) hy.le, Real.rpow_neg hy.le, div_eq_mul_inv]
    push_cast
    have e : ‖a (n + 1)‖ * Real.exp (-(2 * π * z.im) * ((n : ℝ) + 1)) =
        ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ *
          (((n : ℝ) + 1) ^ σ * Real.exp (-(2 * π * z.im) * ((n : ℝ) + 1))) := by
      field_simp
    rw [e]
    calc _ ≤ ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ *
          ((σ / (2 * π * z.im)) ^ σ * Real.exp (-σ)) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by rw [hdiv]; ring
  have := tsum_of_norm_bounded
    ((hsum.mul_right (((σ / (2 * π)) ^ σ * Real.exp (-σ)))).mul_right (z.im ^ (-σ))).hasSum key
  rw [tsum_mul_right, tsum_mul_right] at this
  exact this

/-- **Mellin transform on the imaginary axis**: for $\operatorname{Re} s > \max(0, \nu+1)$,
$$\int_0^\infty t^{s-1}\bigl(f(it/\sqrt N) - a_0\bigr)\,dt = \Lambda_N(s; f).$$ -/
lemma hasMellin_qSeries {ν : ℝ} (ha : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ν) {N : ℝ} (hN : 0 < N)
    {s : ℂ} (hs : ν + 1 < s.re) (hs0 : 0 < s.re) :
    HasMellin (fun t : ℝ ↦ qSeries a (I * ((t / √N : ℝ) : ℂ)) - a 0) s (completedL N a s) := by
  have ha' : CoeffGrowth a := ⟨ν, ha⟩
  have hsq : 0 < √N := Real.sqrt_pos.2 hN
  have hs' : s ≠ 0 := fun h => by simp [h] at hs0
  have himag : ∀ t : ℝ, 0 < t → (I * ((t / √N : ℝ) : ℂ)).im = t / √N := by
    intro t ht
    simp
  have himpos : ∀ t : ℝ, 0 < t → 0 < (I * ((t / √N : ℝ) : ℂ)).im := by
    intro t ht
    rw [himag t ht]; positivity
  set F : ℝ → ℂ := fun t : ℝ ↦ qSeries a (I * ((t / √N : ℝ) : ℂ)) - a 0 with hFdef
  have hLs : LSeriesSummable a s := lSeriesSummable_of_isBigO ha hs
  -- the sequence `p`
  set p : ℕ → ℝ := fun i => 2 * i / √N with hpdef
  have hp : ∀ i, 0 ≤ p i := fun i => by simp only [hpdef]; positivity
  have hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun i => if p i = 0 then 0 else a i * Real.exp (-π * p i * t)) (F t) := by
    intro t ht
    have ht' : 0 < t := ht
    have h1 := hasSum_ite_sub_hasSum (hasSum_qSeries ha' (himpos t ht')) 0
    have e : (fun i => if p i = 0 then (0 : ℂ) else a i * Real.exp (-π * p i * t)) =
        fun n : ℕ => if n = 0 then 0 else
          a n * cexp (2 * π * I * n * (I * ((t / √N : ℝ) : ℂ))) := by
      funext i
      by_cases hi : i = 0
      · simp [hi, hpdef]
      · have hpi : p i ≠ 0 := by
          simp only [hpdef]; positivity
        simp only [hpi, hi, ↓reduceIte]
        rw [Complex.ofReal_exp]
        congr 2
        simp only [hpdef]
        push_cast
        linear_combination (-(2 * (π : ℂ) * i * t / (√N : ℂ))) * Complex.I_sq
    rw [e]
    convert h1 using 1
    simp [hFdef]
  have h_sum : Summable fun i => ‖a i‖ / (p i) ^ s.re := by
    have h := (summable_norm_iff.2 hLs).mul_left (((2 / √N) ^ s.re)⁻¹)
    refine h.congr (fun i => ?_)
    rcases eq_or_ne i 0 with rfl | hi
    · simp [hpdef, Real.zero_rpow hs0.ne']
    · rw [LSeries.norm_term_eq]
      simp only [hi, ↓reduceIte, hpdef]
      rw [show 2 * (i : ℝ) / √N = (2 / √N) * i by ring,
        Real.mul_rpow (by positivity) (by positivity)]
      have : 0 < (2 / √N) ^ s.re := by positivity
      have : 0 < (i : ℝ) ^ s.re := Real.rpow_pos_of_pos (by positivity) _
      field_simp
  have hmain := hasSum_mellin_pi_mul₀ (a := a) (F := F) hp hs0 hF h_sum
  refine ⟨?_, ?_⟩
  · -- convergence
    set σ' : ℝ := (max (ν + 1) 0 + s.re) / 2 with hσ'
    have hmax : max (ν + 1) 0 < s.re := max_lt hs hs0
    have h1 : ν + 1 ≤ max (ν + 1) 0 := le_max_left _ _
    have h2 : 0 ≤ max (ν + 1) 0 := le_max_right _ _
    have hσ1 : ν + 1 < σ' := by rw [hσ']; linarith
    have hσ0 : 0 < σ' := by rw [hσ']; linarith
    have hσ2 : σ' < s.re := by rw [hσ']; linarith
    have hsum : Summable fun n : ℕ ↦ ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ' := by
      have h := (summable_nat_add_iff 1).2
        (summable_norm_iff.2 (lSeriesSummable_of_isBigO ha (s := (σ' : ℂ)) (by simpa using hσ1)))
      refine h.congr (fun n => ?_)
      rw [LSeries.norm_term_eq]
      simp
    obtain ⟨M, hM⟩ := core_sub_small ha' hσ0 hsum
    obtain ⟨C, hC⟩ := qSeries_sub_bound_large ha'
    have hcont : ContinuousOn F (Set.Ioi 0) :=
      (continuousOn_qSeries_imag ha' hN).sub continuousOn_const
    refine mellinConvergent_of_isBigO_rpow_exp (a := 2 * π / √N) (b := σ') (by positivity)
      (hcont.locallyIntegrableOn measurableSet_Ioi) ?_ ?_ hσ2
    · refine IsBigO.of_bound C ?_
      filter_upwards [eventually_ge_atTop √N] with t ht
      have ht0 : 0 < t := lt_of_lt_of_le hsq ht
      have h1y : 1 ≤ (I * ((t / √N : ℝ) : ℂ)).im := by
        rw [himag t ht0, le_div_iff₀ hsq]; linarith
      have := hC _ h1y
      rw [himag t ht0] at this
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      have e : -2 * π * (t / √N) = -(2 * π / √N) * t := by ring
      rw [e] at this
      exact this
    · refine IsBigO.of_bound (M / √N ^ (-σ')) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      have := hM _ (himpos t ht0)
      rw [himag t ht0, Real.div_rpow ht0.le hsq.le] at this
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
      calc ‖F t‖ ≤ M * (t ^ (-σ') / √N ^ (-σ')) := this
        _ = _ := by ring
  · -- value
    rw [← hmain.tsum_eq]
    unfold completedL LSeries
    rw [← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    rcases eq_or_ne i 0 with rfl | hi
    · simp [hpdef, LSeries.term, Complex.zero_cpow hs']
    · rw [LSeries.term_of_ne_zero hi]
      have e1 : ((p i : ℝ) : ℂ) = ((2 / √N : ℝ) : ℂ) * ((i : ℝ) : ℂ) := by
        simp only [hpdef]; push_cast; ring
      have e2 : ((2 * π / √N : ℝ) : ℂ) = ((π : ℝ) : ℂ) * ((2 / √N : ℝ) : ℂ) := by
        push_cast; ring
      rw [e1, e2, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (by positivity) (-s),
        Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) s,
        Complex.cpow_neg ((2 / √N : ℝ) : ℂ) s]
      simp only [Complex.ofReal_natCast]
      ring

end Miyake
