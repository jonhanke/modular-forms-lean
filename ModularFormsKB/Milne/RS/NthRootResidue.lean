import TauCeti.Analysis.Polynomial.RootSum
import TauCeti.Analysis.Contour.MeromorphicLaurent
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Residues along the branched cover `ζ ↦ ζ ^ m`

Local input for the residue theorem, Milne, *Modular Functions and Modular Forms* (`milne2017mf`),
Proposition 1.12 (b), proved via traces along a branched covering: if `G` is meromorphic at `0` then the
trace `s ↦ ∑_{ζ ^ m = s} G ζ` is meromorphic at `0`, and its residue is that of the differential
`G(ζ) d(ζ ^ m) = G(ζ) m ζ ^ (m - 1) dζ`.

* `meromorphicAt_sum_map_nthRoots`: the trace is meromorphic.
* `residue_sum_map_nthRoots`: `res_{s=0} ∑_{ζ ^ m = s} G ζ = res_{ζ=0} G(ζ) m ζ ^ (m - 1)`.

The proof splits `G` into its canonical Laurent data (Tau Ceti `exists_laurent_data_of_meromorphicAt`): an
analytic part, whose trace is analytic (Tau Ceti `analyticAt_sum_map_nthRoots`), plus a finite principal
part. The trace of `ζ⁻ʲ` is computed from the explicit description of `nthRoots` by a primitive root of unity:
it is `m / s ^ (j / m)` if `m ∣ j` and `0` otherwise.
-/

open Filter Topology Polynomial TauCeti.Contour

namespace ModularFormsKB.Milne.RS

/-- The trace of `ζ ↦ 1 / ζ ^ j` along `ζ ^ m = s` for `s ≠ 0`. -/
theorem sum_map_nthRoots_inv_pow {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : s ≠ 0) (j : ℕ) :
    ((nthRoots m s).map fun ζ : ℂ ↦ 1 / ζ ^ j).sum = if m ∣ j then (m : ℂ) / s ^ (j / m) else 0 := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq s hm
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hs (by simpa [hm.ne'] using hα.symm)
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  set ζ0 := Complex.exp (2 * Real.pi * Complex.I / m)
  rw [hζ.nthRoots_eq hα, Multiset.map_map]
  have hterm : ∀ i : ℕ, ((fun ζ : ℂ ↦ 1 / ζ ^ j) ∘ fun x ↦ ζ0 ^ x * α) i
      = (α ^ j)⁻¹ * ((ζ0 ^ j)⁻¹) ^ i := by
    intro i
    have : ζ0 ≠ 0 := hζ.ne_zero hm.ne'
    have h3 : ζ0 ^ j ≠ 0 := pow_ne_zero _ this
    simp only [Function.comp_apply, mul_pow, ← pow_mul, mul_comm i j]
    rw [pow_mul]
    simp [div_eq_mul_inv, mul_inv, inv_pow, mul_comm]
  have hsum : (Multiset.map ((fun ζ : ℂ ↦ 1 / ζ ^ j) ∘ fun x ↦ ζ0 ^ x * α) (Multiset.range m)).sum
      = (α ^ j)⁻¹ * ∑ i ∈ Finset.range m, ((ζ0 ^ j)⁻¹) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ (hterm i).symm) ▸ rfl
  rw [hsum]
  split_ifs with hd
  · have h1 : ζ0 ^ j = 1 := (hζ.pow_eq_one_iff_dvd j).2 hd
    obtain ⟨q, rfl⟩ := hd
    have : q = m * q / m := by rw [Nat.mul_div_cancel_left _ hm]
    rw [h1, ← this, ← hα, ← pow_mul]
    simp [div_eq_mul_inv]
    ring
  · have h1 : ζ0 ^ j ≠ 1 := fun h ↦ hd ((hζ.pow_eq_one_iff_dvd j).1 h)
    have h2 : (ζ0 ^ j)⁻¹ ≠ 1 := fun h ↦ h1 (inv_eq_one.1 h)
    rw [geom_sum_eq h2]
    have : ((ζ0 ^ j)⁻¹) ^ m = 1 := by
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one]; simp
    rw [this]; simp

/-- If a property holds on a punctured neighbourhood of `0`, then for small `s ≠ 0` it holds at all
`m`-th roots of `s`. -/
theorem eventually_forall_mem_nthRoots {m : ℕ} (hm : 0 < m) {P : ℂ → Prop}
    (hP : ∀ᶠ z in 𝓝[≠] (0 : ℂ), P z) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ ζ ∈ nthRoots m s, P ζ := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hP
  obtain ⟨ε, hε, hP⟩ := hP
  have hball : Metric.ball (0 : ℂ) (ε ^ m) ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with s hs hs0 ζ hζ
  rw [mem_nthRoots hm] at hζ
  subst hζ
  have hζ0 : ζ ≠ 0 := fun h ↦ hs0 (by simp [h, hm.ne'])
  refine hP ?_ hζ0
  rw [Metric.mem_ball, dist_zero_right, norm_pow] at hs
  rw [dist_zero_right]
  exact lt_of_pow_lt_pow_left₀ m hε.le hs

/-- Trace of the `k`-th principal part term: for `s ≠ 0` the term `a / ζ ^ (k + 1)` has trace
`a m / s ^ ((k + 1) / m)` if `m ∣ k + 1` and `0` otherwise. -/
noncomputable def traceTerm (m : ℕ) (a : ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  a * (if m ∣ k + 1 then (m : ℂ) / s ^ ((k + 1) / m) else 0)

theorem meromorphicAt_traceTerm (m : ℕ) (a : ℂ) (k : ℕ) : MeromorphicAt (traceTerm m a k) 0 := by
  unfold traceTerm
  by_cases h : m ∣ k + 1
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false, mul_zero]
    fun_prop

theorem residue_traceTerm {m : ℕ} (hm : 0 < m) (a : ℂ) (k : ℕ) :
    residue (traceTerm m a k) 0 = if k + 1 = m then a * m else 0 := by
  unfold traceTerm
  by_cases h : m ∣ k + 1
  · obtain ⟨q, hq⟩ := h
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with rfl | h
      · omega
      · exact h
    have hdiv : (k + 1) / m = (q - 1) + 1 := by
      rw [hq, Nat.mul_div_cancel_left _ hm]; omega
    have hfun : (fun s : ℂ ↦ a * (if m ∣ k + 1 then (m : ℂ) / s ^ ((k + 1) / m) else 0))
        = fun s ↦ (a * m) / (s - 0) ^ ((q - 1) + 1) := by
      funext s
      rw [if_pos ⟨q, hq⟩, hdiv, sub_zero]
      ring
    rw [hfun, residue_const_div_sub_pow]
    have : (q - 1 = 0) ↔ (k + 1 = m) := by
      constructor
      · intro h0; have : q = 1 := by omega
        rw [hq, this, mul_one]
      · intro h0
        have : m * q = m * 1 := by rw [← hq, h0, mul_one]
        have := Nat.eq_of_mul_eq_mul_left hm this
        omega
    simp only [this]
  · have hne : k + 1 ≠ m := fun h0 ↦ h (h0 ▸ dvd_refl _)
    simp only [h, if_false, mul_zero, hne]
    exact residue_eq_zero_of_analyticAt analyticAt_const

/-- Laurent splitting of the trace: for small `s ≠ 0`, the trace of `G` is the trace of the analytic
part of `G` plus the traces of the principal part terms. -/
theorem exists_trace_laurent {G : ℂ → ℂ} (hG : MeromorphicAt G 0) {m : ℕ} (hm : 0 < m) :
    ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 ∧
      (∀ᶠ ζ in 𝓝[≠] (0 : ℂ), G ζ = g ζ + ∑ k : Fin N, a k / (ζ - 0) ^ (k.val + 1)) ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), ((nthRoots m s).map G).sum =
        ((nthRoots m s).map g).sum + ∑ k : Fin N, traceTerm m (a k) k.val s := by
  obtain ⟨a, g, hg, heq⟩ := exists_laurent_data_of_meromorphicAt hG
  refine ⟨_, a, g, hg, heq, ?_⟩
  filter_upwards [eventually_forall_mem_nthRoots hm heq, self_mem_nhdsWithin] with s hs hs0
  have hs0 : s ≠ 0 := hs0
  rw [Multiset.map_congr rfl hs, Multiset.sum_map_add]
  congr 1
  have hswap : ∀ M : Multiset ℂ, (M.map fun ζ ↦ ∑ k : Fin _, a k / (ζ - 0) ^ (k.val + 1)).sum
      = ∑ k : Fin _, (M.map fun ζ ↦ a k * (1 / ζ ^ (k.val + 1))).sum := by
    intro M
    induction M using Multiset.induction_on with
    | empty => simp
    | cons x M ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [div_eq_mul_inv]
  rw [hswap]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Multiset.sum_map_mul_left, sum_map_nthRoots_inv_pow hm hs0]
  rfl

open Polynomial in
/-- The sum of a meromorphic function over the `m`-th roots of `s` is meromorphic in `s` at `0`. -/
theorem meromorphicAt_sum_map_nthRoots {G : ℂ → ℂ} (hG : MeromorphicAt G 0) {m : ℕ} (hm : 0 < m) :
    MeromorphicAt (fun s ↦ ((nthRoots m s).map G).sum) 0 := by
  obtain ⟨N, a, g, hg, -, hs⟩ := exists_trace_laurent hG hm
  have h1 : MeromorphicAt (fun s ↦ ((nthRoots m s).map g).sum +
      ∑ k : Fin N, traceTerm m (a k) k.val s) 0 := by
    have h2 : MeromorphicAt (fun s ↦ ((nthRoots m s).map g).sum) 0 :=
      (TauCeti.analyticAt_sum_map_nthRoots hg m).meromorphicAt
    have h3 : MeromorphicAt (∑ k : Fin N, traceTerm m (a k) k.val) 0 :=
      MeromorphicAt.sum fun k _ ↦ meromorphicAt_traceTerm m _ _
    exact (h2.add h3).congr (Filter.Eventually.of_forall fun s ↦ by simp [Finset.sum_apply])
  exact h1.congr (hs.mono fun s h ↦ h.symm)

open Polynomial in
/-- **Residues along `ζ ↦ ζ^m`**: `res_{s=0} ∑_{ζ^m = s} G(ζ) = res_{ζ=0} G(ζ) m ζ^{m-1}`. -/
theorem residue_sum_map_nthRoots {G : ℂ → ℂ} (hG : MeromorphicAt G 0) {m : ℕ} (hm : 0 < m) :
    TauCeti.Contour.residue (fun s ↦ ((nthRoots m s).map G).sum) 0 =
      TauCeti.Contour.residue (fun ζ ↦ G ζ * (m * ζ ^ (m - 1))) 0 := by
  obtain ⟨N, a, g, hg, hGe, hs⟩ := exists_trace_laurent hG hm
  have hmer : ∀ k : Fin N, MeromorphicAt (traceTerm m (a k) k.val) 0 :=
    fun k ↦ meromorphicAt_traceTerm m _ _
  -- left side
  have hL : residue (fun s ↦ ((nthRoots m s).map G).sum) 0 =
      ∑ k : Fin N, if k.val + 1 = m then a k * m else 0 := by
    have h1 : (fun s ↦ ((nthRoots m s).map G).sum) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun s ↦ ((nthRoots m s).map g).sum) + ∑ k : Fin N, traceTerm m (a k) k.val := by
      filter_upwards [hs] with s h
      simpa [Finset.sum_apply] using h
    have han : AnalyticAt ℂ (fun s ↦ ((nthRoots m s).map g).sum) 0 :=
      TauCeti.analyticAt_sum_map_nthRoots hg m
    rw [residue_congr_nhdsNE h1, residue_add han.meromorphicAt (MeromorphicAt.sum fun k _ ↦ hmer k),
      residue_eq_zero_of_analyticAt han, zero_add, residue_sum _ fun k _ ↦ hmer k]
    exact Finset.sum_congr rfl fun k _ ↦ residue_traceTerm hm _ _
  -- right side
  have hLk : ∀ k : Fin N, residue (fun ζ : ℂ ↦ a k * (m * ζ ^ (m - 1) / ζ ^ (k.val + 1))) 0
      = if k.val + 1 = m then a k * m else 0 := by
    intro k
    by_cases hk : k.val + 1 + 1 ≤ m
    · have hne : ¬ (k.val + 1 = m) := by omega
      rw [if_neg hne]
      have han : AnalyticAt ℂ (fun ζ : ℂ ↦ a k * m * ζ ^ (m - 1 - (k.val + 1))) 0 := by fun_prop
      refine Eq.trans (residue_congr_nhdsNE ?_) (residue_eq_zero_of_analyticAt han)
      filter_upwards [self_mem_nhdsWithin] with ζ hζ
      have hζ : ζ ≠ 0 := hζ
      have hp : ζ ^ (m - 1) = ζ ^ (k.val + 1) * ζ ^ (m - 1 - (k.val + 1)) := by
        rw [← pow_add]; congr 1; omega
      rw [hp]
      field_simp
    · have hfun : (fun ζ : ℂ ↦ a k * (m * ζ ^ (m - 1) / ζ ^ (k.val + 1))) =ᶠ[𝓝[≠] (0 : ℂ)]
          fun ζ ↦ (a k * m) / (ζ - 0) ^ ((k.val + 1 - m) + 1) := by
        filter_upwards [self_mem_nhdsWithin] with ζ hζ
        have hζ : ζ ≠ 0 := hζ
        have hp : ζ ^ (k.val + 1) = ζ ^ (m - 1) * ζ ^ ((k.val + 1 - m) + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [sub_zero]
        conv_lhs => rw [hp]
        field_simp
      rw [residue_congr_nhdsNE hfun, residue_const_div_sub_pow]
      have : (k.val + 1 - m = 0) ↔ (k.val + 1 = m) := by omega
      simp only [this]
  have h2 : (fun ζ ↦ G ζ * (m * ζ ^ (m - 1))) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun ζ ↦ g ζ * (m * ζ ^ (m - 1))) +
        ∑ k : Fin N, fun ζ : ℂ ↦ a k * (m * ζ ^ (m - 1) / ζ ^ (k.val + 1)) := by
    filter_upwards [hGe] with ζ h
    rw [h]
    simp only [Pi.add_apply, Finset.sum_apply, sub_zero]
    rw [add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have han : AnalyticAt ℂ (fun ζ : ℂ ↦ g ζ * (m * ζ ^ (m - 1))) 0 :=
    hg.mul (analyticAt_const.mul (analyticAt_id.pow _))
  have hmerL : ∀ k : Fin N, MeromorphicAt (fun ζ : ℂ ↦ a k * (m * ζ ^ (m - 1) / ζ ^ (k.val + 1))) 0 :=
    fun k ↦ by fun_prop
  rw [hL, residue_congr_nhdsNE h2, residue_add han.meromorphicAt (MeromorphicAt.sum fun k _ ↦ hmerL k),
    residue_eq_zero_of_analyticAt han, zero_add, residue_sum _ fun k _ ↦ hmerL k]
  exact Finset.sum_congr rfl fun k _ ↦ (hLk k).symm

end ModularFormsKB.Milne.RS
