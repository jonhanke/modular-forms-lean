import ModularFormsKB.Miyake.Sec4_3.ModularQ

/-!
# Dilations of $q$-series and the Fricke involution

For a coefficient sequence $a$ and $e \ge 1$, `Miyake.dilate e a` is the sequence of $f(ez)$ when $f = \sum a_m q^m$:
- `qSeries_dilate`: $\sum_m (\text{dilate}_e a)_m q^m = f(ez)$;
- `qSeries_finset_sum`, `coeffGrowth_*`: finite linear combinations;
- `fricke_two_dilate`: in weight $2$, $f(d\,\cdot)|_2\,\omega_{Mde} = \frac ed\,(f|_2\,\omega_M)(e\,\cdot)$;
- `fricke_congr_upperHalfPlane`, `fricke_finset_sum`: $f|\omega_N$ on $\mathbb H$ depends only on $f$ on $\mathbb H$, and is linear.
-/

open Complex Filter Asymptotics
open scoped Real

noncomputable section

namespace Miyake

/-- The coefficients of $f(e z)$: $(\text{dilate}_e a)_m = a_{m/e}$ if $e \mid m$, else $0$. -/
def dilate (e : ℕ) (a : ℕ → ℂ) (m : ℕ) : ℂ := if e ∣ m then a (m / e) else 0

lemma dilate_one_apply (a : ℕ → ℂ) {e : ℕ} (he : 1 < e) : dilate e a 1 = 0 := by
  have : ¬ (e ∣ 1) := fun h => absurd (Nat.le_of_dvd one_pos h) (by omega)
  simp [dilate, this]

lemma dilate_one_left (a : ℕ → ℂ) : dilate 1 a = a := by
  funext m; simp [dilate]

lemma qSeries_dilate {e : ℕ} (he : 0 < e) (a : ℕ → ℂ) (z : ℂ) :
    qSeries (dilate e a) z = qSeries a (e * z) := by
  have hinj : Function.Injective (fun c : ℕ ↦ e * c) := fun x y h => Nat.eq_of_mul_eq_mul_left he h
  have hsupp : Function.support (fun n : ℕ ↦ dilate e a n * cexp (2 * π * I * n * z)) ⊆
      Set.range (fun c : ℕ ↦ e * c) := by
    intro n hn
    by_cases h : e ∣ n
    · obtain ⟨c, rfl⟩ := h; exact ⟨c, rfl⟩
    · exfalso; apply hn; simp [dilate, h]
  have key := hinj.tsum_eq hsupp
  unfold qSeries
  rw [← key]
  refine tsum_congr fun c => ?_
  have h1 : dilate e a (e * c) = a c := by simp [dilate, Nat.mul_div_cancel_left _ he]
  rw [h1]
  congr 2
  push_cast
  ring

private lemma coeffGrowth_of_bound {a : ℕ → ℂ} {C ν : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν) : CoeffGrowth a := by
  refine ⟨ν, IsBigO.of_bound (C * 2 ^ ν) ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (Real.rpow_nonneg n.cast_nonneg _)]
  have h1 : ((n : ℝ) + 1) ^ ν ≤ (2 * n) ^ ν :=
    Real.rpow_le_rpow (by positivity) (by linarith) hν.le
  rw [Real.mul_rpow (by norm_num) n.cast_nonneg] at h1
  calc ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ ν := hb n
    _ ≤ C * (2 ^ ν * (n : ℝ) ^ ν) := by gcongr
    _ = C * 2 ^ ν * (n : ℝ) ^ ν := by ring

lemma coeffGrowth_dilate {e : ℕ} (_he : 0 < e) {a : ℕ → ℂ} (ha : CoeffGrowth a) :
    CoeffGrowth (dilate e a) := by
  obtain ⟨C, ν, hν, hC, hb⟩ := ha.exists_bound
  refine coeffGrowth_of_bound hν hC fun m => ?_
  unfold dilate
  split_ifs with h
  · refine (hb _).trans ?_
    have : ((m / e : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m e
    gcongr
  · simp only [norm_zero]; positivity

lemma coeffGrowth_const_mul (c : ℂ) {a : ℕ → ℂ} (ha : CoeffGrowth a) :
    CoeffGrowth (fun m ↦ c * a m) := by
  exact ha.const_mul c

private lemma coeffGrowth_add {a b : ℕ → ℂ} (ha : CoeffGrowth a) (hb : CoeffGrowth b) :
    CoeffGrowth (fun m ↦ a m + b m) := by
  obtain ⟨C₁, ν₁, hν₁, hC₁, hb₁⟩ := ha.exists_bound
  obtain ⟨C₂, ν₂, hν₂, hC₂, hb₂⟩ := hb.exists_bound
  refine coeffGrowth_of_bound (lt_of_lt_of_le hν₁ (le_max_left ν₁ ν₂)) (add_nonneg hC₁ hC₂) fun n => ?_
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have e1 : ((n : ℝ) + 1) ^ ν₁ ≤ ((n : ℝ) + 1) ^ (max ν₁ ν₂) :=
    Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)
  have e2 : ((n : ℝ) + 1) ^ ν₂ ≤ ((n : ℝ) + 1) ^ (max ν₁ ν₂) :=
    Real.rpow_le_rpow_of_exponent_le h1 (le_max_right _ _)
  calc ‖a n + b n‖ ≤ ‖a n‖ + ‖b n‖ := norm_add_le _ _
    _ ≤ C₁ * ((n : ℝ) + 1) ^ ν₁ + C₂ * ((n : ℝ) + 1) ^ ν₂ := add_le_add (hb₁ n) (hb₂ n)
    _ ≤ C₁ * ((n : ℝ) + 1) ^ (max ν₁ ν₂) + C₂ * ((n : ℝ) + 1) ^ (max ν₁ ν₂) := by gcongr
    _ = (C₁ + C₂) * ((n : ℝ) + 1) ^ (max ν₁ ν₂) := by ring

lemma coeffGrowth_finset_sum {ι : Type*} (S : Finset ι) {a : ι → ℕ → ℂ}
    (h : ∀ i ∈ S, CoeffGrowth (a i)) : CoeffGrowth (fun m ↦ ∑ i ∈ S, a i m) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨0, Asymptotics.isBigO_zero _ _⟩
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact coeffGrowth_add (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma qSeries_finset_sum {ι : Type*} (S : Finset ι) {a : ι → ℕ → ℂ}
    (h : ∀ i ∈ S, CoeffGrowth (a i)) {z : ℂ} (hz : 0 < z.im) :
    qSeries (fun m ↦ ∑ i ∈ S, a i m) z = ∑ i ∈ S, qSeries (a i) z := by
  have hs : HasSum (fun n : ℕ ↦ ∑ i ∈ S, a i n * cexp (2 * π * I * n * z))
      (∑ i ∈ S, qSeries (a i) z) := hasSum_sum fun i hi => hasSum_qSeries (h i hi) hz
  calc qSeries (fun m ↦ ∑ i ∈ S, a i m) z
      = ∑' n : ℕ, ∑ i ∈ S, a i n * cexp (2 * π * I * n * z) := by
        unfold qSeries; simp only [Finset.sum_mul]
    _ = _ := hs.tsum_eq

lemma qSeries_const_mul' (c : ℂ) (a : ℕ → ℂ) (z : ℂ) :
    qSeries (fun m ↦ c * a m) z = c * qSeries a z := by
  simp only [qSeries, mul_assoc, tsum_mul_left]

/-- For $\operatorname{Im} z > 0$ and $N > 0$, `fricke k N f z` only depends on `f` on the upper half-plane. -/
lemma fricke_congr_upperHalfPlane {k : ℤ} {N : ℝ} (hN : 0 < N) {f g : ℂ → ℂ} (h : ∀ w : ℂ, 0 < w.im → f w = g w)
    {z : ℂ} (hz : 0 < z.im) : fricke k N f z = fricke k N g z := by
  unfold fricke
  congr 1
  apply h
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  have key : (-1 / ((N : ℂ) * z)).im = z.im / (N * Complex.normSq z) := by
    have : (-1 / ((N : ℂ) * z)) = (-(1 / (N : ℝ)) : ℝ) * (z⁻¹) := by
      push_cast; field_simp
    rw [this, Complex.im_ofReal_mul, Complex.inv_im]
    field_simp
  rw [key]
  have : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  positivity

lemma fricke_finset_sum {ι : Type*} (k : ℤ) (N : ℝ) (S : Finset ι) (c : ι → ℂ) (G : ι → ℂ → ℂ) (z : ℂ) :
    fricke k N (fun w ↦ ∑ i ∈ S, c i * G i w) z = ∑ i ∈ S, c i * fricke k N (G i) z := by
  unfold fricke
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **Fricke of a dilation, weight $2$**: $f(d\,\cdot)|_2\,\omega_{Mde}(z) = \frac ed\,(f|_2\,\omega_M)(ez)$. -/
lemma fricke_two_dilate {M d e : ℕ} (hM : 0 < M) (hd : 0 < d) (he : 0 < e) (G : ℂ → ℂ) {z : ℂ}
    (hz : z ≠ 0) :
    fricke 2 ((M : ℝ) * d * e) (fun w ↦ G (d * w)) z = ((e : ℂ) / d) * fricke 2 M G (e * z) := by
  unfold fricke
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h1 : (d : ℂ) * (-1 / (((M : ℝ) * d * e : ℝ) * z)) = -1 / (((M : ℝ) : ℂ) * (e * z)) := by
    push_cast; field_simp
  show _ * G (d * (-1 / (((M : ℝ) * d * e : ℝ) * z))) = _
  rw [h1]
  have s1 : ((√((M : ℝ) * d * e) : ℝ) : ℂ) ^ 2 = (M : ℂ) * d * e := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; simp
  have s2 : ((√(M : ℝ) : ℝ) : ℂ) ^ 2 = (M : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; simp
  have e1 : (((√((M : ℝ) * d * e) : ℝ) : ℂ) * z) ^ (-(2 : ℤ)) = 1 / ((M : ℂ) * d * e * z ^ 2) := by
    rw [zpow_neg, zpow_ofNat, mul_pow, s1]; simp
  have e2 : (((√(M : ℝ) : ℝ) : ℂ) * (e * z)) ^ (-(2 : ℤ)) = 1 / ((M : ℂ) * (e * z) ^ 2) := by
    rw [zpow_neg, zpow_ofNat, mul_pow, s2]; simp
  rw [e1, e2]
  field_simp

end Miyake
