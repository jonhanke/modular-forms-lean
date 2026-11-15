import Mathlib.NumberTheory.ModularForms.EisensteinSeries.IsBoundedAtImInfty
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The value at `i∞` of the Eisenstein series of level `N`

For `a : (ℤ/Nℤ)²` and `k ≥ 3`, Mathlib's Eisenstein series
`E_k^a(z) = ∑ (cz + d)^{-k}`, the sum over the coprime pairs `(c, d) ≡ a (mod N)`, tends along `z = it`, `t → ∞`, to
the sum of `d^{-k}` over its terms with `c = 0`, that is over `(c, d) = (0, ±1) ≡ a` (`tendsto_eisensteinSeries`;
Tannery's theorem, the terms being dominated by their values at `z = i`). So the limit is `0` unless `a ≡ (0, ±1)`
(`eisLim_eq_zero`), and for even `k` it is a sum of terms `0` and `1` (`eisLim_eq_ofReal`), at least `1` for
`a = (0, 1)` (`one_le_eisLimReal`).

This is the classical computation of the constant term of `E_k^a` at the cusp `∞` (Diamond–Shurman, *A First Course
in Modular Forms*, §4.2); it is used in `ModularFormsKB.Milne.Wave12.GammaNRiemannRoch` to show that two Eisenstein
series of level `N` are distinct functions.
-/

open UpperHalfPlane Complex Filter Topology EisensteinSeries

noncomputable section

namespace ModularFormsKB.Milne.Wave12

/-- The point `i · max(t, 1)` of `ℍ`. -/
def ptI (t : ℝ) : ℍ := ⟨Complex.I * (max t 1 : ℝ), by simp⟩

theorem ptI_coe (t : ℝ) : (ptI t : ℂ) = Complex.I * (max t 1 : ℝ) := rfl

variable {N : ℕ} (a : Fin 2 → ZMod N) (k : ℤ)

/-- The limit `∑_{(0, d) ≡ a} d^{-k}` of `E_k^a(it)` as `t → ∞`. -/
def eisLim : ℂ := ∑' v : gammaSet N 1 a, if v.1 0 = 0 then ((v.1 1 : ℂ) ^ (-k)) else 0

theorem normSq_le_normSq_ptI (v : Fin 2 → ℤ) (t : ℝ) :
    ‖((v 0 : ℂ) * (ptI 0 : ℂ) + v 1)‖ ≤ ‖((v 0 : ℂ) * (ptI t : ℂ) + v 1)‖ := by
  have h0 : max (0 : ℝ) 1 = 1 := by norm_num
  have h1 : (1 : ℝ) ≤ max t 1 := le_max_right _ _
  rw [ptI_coe, ptI_coe, h0]
  have key : ∀ m : ℝ, ‖((v 0 : ℂ) * (Complex.I * (m : ℂ)) + v 1)‖ =
      Real.sqrt ((v 1 : ℝ) ^ 2 + ((v 0 : ℝ) * m) ^ 2) := by
    intro m
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  rw [key, key]
  apply Real.sqrt_le_sqrt
  have : ((v 0 : ℝ) * 1) ^ 2 ≤ ((v 0 : ℝ) * max t 1) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
  push_cast at this ⊢
  linarith

theorem tendsto_eisSummand (hk : 0 < k) (v : Fin 2 → ℤ) :
    Tendsto (fun t ↦ eisSummand k v (ptI t)) atTop
      (𝓝 (if v 0 = 0 then ((v 1 : ℂ) ^ (-k)) else 0)) := by
  split_ifs with hv
  · simp [eisSummand, hv]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
    have hn : 0 < n := by exact_mod_cast hk
    apply squeeze_zero_norm (a := fun t ↦ ((max t 1) ^ n)⁻¹)
    · intro t
      simp only [eisSummand, zpow_neg, zpow_natCast, norm_inv, norm_pow]
      have h1 : (1 : ℝ) ≤ max t 1 := le_max_right _ _
      have hge : max t 1 ≤ ‖((v 0 : ℂ) * (ptI t : ℂ) + v 1)‖ := by
        have him : |((v 0 : ℂ) * (ptI t : ℂ) + v 1).im| ≤ ‖((v 0 : ℂ) * (ptI t : ℂ) + v 1)‖ :=
          Complex.abs_im_le_norm _
        have hv1 : (1 : ℝ) ≤ |(v 0 : ℝ)| := by
          have : (1 : ℤ) ≤ |v 0| := Int.one_le_abs hv
          exact_mod_cast this
        have : ((v 0 : ℂ) * (ptI t : ℂ) + v 1).im = (v 0 : ℝ) * max t 1 := by
          rw [ptI_coe]; simp
        rw [this, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < max t 1)] at him
        nlinarith
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hge n)
    · have : Tendsto (fun t : ℝ ↦ max t 1) atTop atTop := tendsto_atTop_mono (le_max_left · 1) tendsto_id
      exact (tendsto_pow_atTop (Nat.pos_iff_ne_zero.1 hn)).comp this |>.inv_tendsto_atTop

/-- **`E_k^a(it) → ∑_{(0, d) ≡ a} d^{-k}` as `t → ∞`.** -/
theorem tendsto_eisensteinSeries (hk : 3 ≤ k) :
    Tendsto (fun t ↦ eisensteinSeries a k (ptI t)) atTop (𝓝 (eisLim a k)) := by
  unfold eisensteinSeries eisLim
  refine tendsto_tsum_of_dominated_convergence (bound := fun v : gammaSet N 1 a ↦ ‖eisSummand k v.1 (ptI 0)‖)
    ((summable_norm_eisSummand hk _).subtype _) (fun v ↦ tendsto_eisSummand k (by omega) v.1)
    (.of_forall fun t v ↦ ?_)
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k)
  subst hn
  simp only [eisSummand, zpow_neg, zpow_natCast, norm_inv, norm_pow]
  have hle := normSq_le_normSq_ptI v.1 t
  rcases eq_or_lt_of_le (norm_nonneg ((v.1 0 : ℂ) * (ptI 0 : ℂ) + v.1 1)) with h0 | hpos
  · -- then `v = 0`, impossible for a coprime pair; both sides vanish anyway
    have hv : (v.1 0 : ℂ) * (ptI 0 : ℂ) + v.1 1 = 0 := norm_eq_zero.1 h0.symm
    have h00 : v.1 0 = 0 ∧ v.1 1 = 0 := by
      have him := congrArg Complex.im hv
      have hre := congrArg Complex.re hv
      rw [ptI_coe] at him hre
      simp at him hre
      exact ⟨by exact_mod_cast him, by exact_mod_cast hre⟩
    simp [h00.1, h00.2]
  · exact inv_anti₀ (pow_pos hpos n) (pow_le_pow_left₀ hpos.le hle n)

/-- If `a` is not `(0, ±1)`, the limit is `0`. -/
theorem eisLim_eq_zero (h : ∀ s : ℤ, (s = 1 ∨ s = -1) → a ≠ ![0, (s : ZMod N)]) : eisLim a k = 0 := by
  unfold eisLim
  convert tsum_zero with v
  split_ifs with hv
  · exfalso
    obtain ⟨hva, hg⟩ := v.2
    rw [hv, Int.gcd_zero_left] at hg
    have hs : v.1 1 = 1 ∨ v.1 1 = -1 := by
      rcases Int.natAbs_eq (v.1 1) with h1 | h1 <;> rw [hg] at h1 <;> simp [h1]
    apply h _ hs
    have hai : ∀ i, a i = ((v.1 i : ℤ) : ZMod N) := fun i ↦ (congrFun hva i).symm
    ext i
    fin_cases i <;> simp [hai, hv]
  · rfl

/-- The real number `#{s = ±1 : (0, s) ≡ a}`. -/
def eisLimReal : ℝ := ∑' v : gammaSet N 1 a, if v.1 0 = 0 then (1 : ℝ) else 0

theorem summable_eisLimReal : Summable fun v : gammaSet N 1 a ↦ if v.1 0 = 0 then (1 : ℝ) else 0 := by
  apply summable_of_hasFiniteSupport
  show (Function.support _).Finite
  have hfin : {v : Fin 2 → ℤ | v 0 = 0 ∧ (v 1 = 1 ∨ v 1 = -1)}.Finite := by
    have : {v : Fin 2 → ℤ | v 0 = 0 ∧ (v 1 = 1 ∨ v 1 = -1)} ⊆ {![0, 1], ![0, -1]} := by
      intro v ⟨h0, h1⟩
      rcases h1 with h1 | h1
      · left; ext i; fin_cases i <;> simp [h0, h1]
      · right; ext i; fin_cases i <;> simp [h0, h1]
    exact (Set.toFinite _).subset this
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro v hv
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hv
  refine ⟨hv, ?_⟩
  have hg := v.2.2
  rw [hv, Int.gcd_zero_left] at hg
  rcases Int.natAbs_eq (v.1 1) with h1 | h1 <;> rw [hg] at h1 <;> simp [h1]

/-- For even `k` the limit is the real number `eisLimReal a`. -/
theorem eisLim_eq_ofReal (hk : Even k) : eisLim a k = (eisLimReal a : ℂ) := by
  unfold eisLim eisLimReal
  rw [Complex.ofReal_tsum]
  congr 1
  ext v
  split_ifs with hv
  · have hg := v.2.2
    rw [hv, Int.gcd_zero_left] at hg
    rcases Int.natAbs_eq (v.1 1) with h1 | h1 <;> rw [hg] at h1 <;> simp [h1, hk.neg_one_zpow]
  · simp

theorem eisLimReal_nonneg : 0 ≤ eisLimReal a :=
  tsum_nonneg fun _ ↦ by split_ifs <;> norm_num

theorem one_le_eisLimReal : 1 ≤ eisLimReal (N := N) ![0, 1] := by
  have hmem : (![0, 1] : Fin 2 → ℤ) ∈ gammaSet N 1 ![0, 1] := by
    refine ⟨?_, by simp⟩
    ext i; fin_cases i <;> simp
  have := (summable_eisLimReal (N := N) ![0, 1]).le_tsum ⟨_, hmem⟩ (fun _ _ ↦ by split_ifs <;> norm_num)
  simpa [eisLimReal] using this

end ModularFormsKB.Milne.Wave12
