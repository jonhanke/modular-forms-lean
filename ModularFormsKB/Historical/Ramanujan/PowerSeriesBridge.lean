import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import ModularFormsKB.Historical.Ramanujan.PartitionDefs

/-!
# From analytic identities to formal power series identities

`SumsTo f F` says that the formal power series `f ∈ ℂ⟦X⟧` converges absolutely on the open unit disc
with sum the function `F`. Products of such series correspond to products of functions (Cauchy product),
and a function has at most one such series (uniqueness of power series expansions), so an identity of
functions on the disc lifts to an identity of formal power series. This is used to deduce Jacobi's cube
identity as an identity in `ℤ⟦X⟧` from its analytic form (`JacobiCube.lean`).

* `SumsTo.mul`, `SumsTo.pow`, `SumsTo.unique`;
* `map_intCast_injective`: `PowerSeries.map (Int.castRingHom ℂ)` is injective;
* `sumsTo_euler`: Euler's series `∏ (1 - Xⁿ)` (mapped to `ℂ`) sums to `∏ (1 - xⁿ)`, by Mathlib's
  pentagonal number theorem for the Euler function.
-/

noncomputable section

open PowerSeries Finset

namespace ModularFormsKB.Historical.Ramanujan

/-- The formal power series `f` converges absolutely on the open unit disc, with sum `F`. -/
def SumsTo (f : ℂ⟦X⟧) (F : ℂ → ℂ) : Prop :=
  ∀ x : ℂ, ‖x‖ < 1 → Summable (fun n ↦ ‖coeff n f‖ * ‖x‖ ^ n) ∧
    HasSum (fun n ↦ coeff n f * x ^ n) (F x)

theorem SumsTo.mul {f g : ℂ⟦X⟧} {F G : ℂ → ℂ} (hf : SumsTo f F) (hg : SumsTo g G) :
    SumsTo (f * g) (fun x ↦ F x * G x) := by
  intro x hx
  obtain ⟨sf, hf'⟩ := hf x hx
  obtain ⟨sg, hg'⟩ := hg x hx
  have na : Summable (fun n ↦ ‖coeff n f * x ^ n‖) := by simpa [norm_mul] using sf
  have nb : Summable (fun n ↦ ‖coeff n g * x ^ n‖) := by simpa [norm_mul] using sg
  have key : ∀ n, (∑ kl ∈ antidiagonal n, (coeff kl.1 f * x ^ kl.1) * (coeff kl.2 g * x ^ kl.2)) =
      coeff n (f * g) * x ^ n := by
    intro n
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [Finset.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm na nb
  simp_rw [key] at hs
  refine ⟨by simpa [norm_mul] using hs, ?_⟩
  have h2 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm na nb
  simp_rw [key] at h2
  rw [hf'.tsum_eq, hg'.tsum_eq] at h2
  beta_reduce
  rw [h2]
  exact hs.of_norm.hasSum

theorem SumsTo.pow {f : ℂ⟦X⟧} {F : ℂ → ℂ} (hf : SumsTo f F) (n : ℕ) :
    SumsTo (f ^ n) (fun x ↦ F x ^ n) := by
  induction n with
  | zero =>
    intro x hx
    refine ⟨?_, ?_⟩
    · simpa [coeff_one] using (summable_of_ne_finset_zero (s := {0}) (f := fun n : ℕ ↦
        ‖coeff n (1 : ℂ⟦X⟧)‖ * ‖x‖ ^ n) (by intro n hn; simp at hn; simp [coeff_one, hn]))
    · simpa [coeff_one] using hasSum_single (f := fun n : ℕ ↦ coeff n (1 : ℂ⟦X⟧) * x ^ n) 0
        (fun n hn ↦ by simp [coeff_one, hn])
  | succ n ih =>
    simpa [pow_succ] using ih.mul hf

theorem SumsTo.unique {f g : ℂ⟦X⟧} {F : ℂ → ℂ} (hf : SumsTo f F) (hg : SumsTo g F) : f = g := by
  set c : ℕ → ℂ := fun n ↦ coeff n f - coeff n g with hc
  have hrad : (1 : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
    have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
    have hx : ‖(r : ℂ)‖ < 1 := by simpa using hr'
    apply FormalMultilinearSeries.le_radius_of_summable_norm
    have h1 := (hf _ hx).1
    have h2 := (hg _ hx).1
    have e : ‖((r : ℝ) : ℂ)‖ = r := by simp
    rw [e] at h1 h2
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_) (h1.add h2)
    rw [FormalMultilinearSeries.ofScalars_norm, hc]
    simp only
    rw [← add_mul]
    gcongr
    exact norm_sub_le _ _
  have hp : HasFPowerSeriesOnBall (0 : ℂ → ℂ) (FormalMultilinearSeries.ofScalars ℂ c) 0 1 :=
    { r_le := hrad
      r_pos := by norm_num
      hasSum := by
        intro y hy
        have h : ‖y‖ₑ < 1 := by simpa [edist_zero_right] using hy
        have hy' : ‖y‖ < 1 := by
          rw [← ofReal_norm] at h
          exact ENNReal.ofReal_lt_one.mp h
        have := (hf y hy').2.sub ((hg y hy').2)
        simp only [sub_self] at this
        have e : ∀ n, FormalMultilinearSeries.ofScalars ℂ c n (fun _ ↦ y) =
            coeff n f * y ^ n - coeff n g * y ^ n := by
          intro n
          rw [FormalMultilinearSeries.ofScalars_apply_eq, hc]
          simp only [smul_eq_mul]
          ring
        simpa only [e, Pi.zero_apply, zero_add] using this }
  have h0 := HasFPowerSeriesAt.eq_zero hp.hasFPowerSeriesAt
  ext n
  have := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p n) h0
  simp only [FormalMultilinearSeries.zero_apply] at this
  have h3 := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp this
  exact sub_eq_zero.mp h3

theorem map_intCast_injective :
    Function.Injective (PowerSeries.map (Int.castRingHom ℂ)) :=
  PowerSeries.map_injective _ Int.cast_injective

theorem map_pentagonalSeries :
    PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.pentagonalSeries ℤ) =
      PowerSeries.pentagonalSeries ℂ := by
  ext n
  rw [coeff_map]
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    simp
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hn,
      PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hn]
    simp

theorem sumsTo_euler :
    SumsTo (PowerSeries.map (Int.castRingHom ℂ) eulerSeries)
      (fun x ↦ ∏' n : ℕ, (1 - x ^ (n + 1))) := by
  intro x hx
  rw [eulerSeries, PowerSeries.WithPiTopology.tprod_one_sub_X_pow, map_pentagonalSeries]
  refine ⟨?_, ?_⟩
  · refine (summable_geometric_of_lt_one (norm_nonneg x) hx).of_nonneg_of_le
      (fun _ ↦ by positivity) fun n ↦ ?_
    have : ‖coeff n (PowerSeries.pentagonalSeries ℂ)‖ ≤ 1 := by
      by_cases hn : n ∈ Set.range pentagonal
      · obtain ⟨k, rfl⟩ := hn
        rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
        simp
      · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℂ hn]; simp
    calc _ ≤ 1 * ‖x‖ ^ n := by gcongr
      _ = _ := one_mul _
  · beta_reduce
    rw [← eulerFunction_eq_tprod hx]
    exact hasSum_eulerFunction_pentagonalSeries hx

end ModularFormsKB.Historical.Ramanujan
