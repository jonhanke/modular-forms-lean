import ModularFormsKB.Milne.Ch6.ModularEquation
import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Analysis.Analytic.ConvergenceRadius

/-!
# Functions on $\mathbb H$ given by absolutely convergent $q$-series

`Expands f A` says that $f(z) = \sum_n a_n q^n$ ($q = e^{2\pi i z}$) for every $z \in \mathbb H$, with
$\sum_n |a_n||q|^n < \infty$. Such representations add and multiply (Cauchy product), and determine the coefficients
(`Expands.unique`). The functions $qj(z)$ and $q^N j(Nz)$ expand with the coefficients of $qj$ and their expansion by
$N$ (`expands_qParam_mul_j`, `expands_qParam_pow_mul_j_scale`). This is the formal part of the rationality argument for
the modular polynomial (Milne, Section 6, proof of Theorem 6.1, pdf p. 88).
-/

open UpperHalfPlane Filter Topology PowerSeries
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.QSeries

open TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-- `f` is given on `ℍ` by the absolutely convergent power series `A` in `q = 𝕢 1 z`. -/
def Expands (f : ℍ → ℂ) (A : PowerSeries ℂ) : Prop :=
  ∀ z : ℍ, Summable (fun n ↦ ‖coeff n A‖ * ‖𝕢 1 (z : ℂ)‖ ^ n) ∧
    HasSum (fun n ↦ coeff n A * 𝕢 1 (z : ℂ) ^ n) (f z)

variable {f g : ℍ → ℂ} {A B : PowerSeries ℂ}

theorem Expands.add (hf : Expands f A) (hg : Expands g B) : Expands (fun z ↦ f z + g z) (A + B) := by
  intro z
  obtain ⟨hs1, hh1⟩ := hf z
  obtain ⟨hs2, hh2⟩ := hg z
  refine ⟨?_, ?_⟩
  · refine (hs1.add hs2).of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ ?_
    rw [map_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  · simpa [map_add, add_mul] using hh1.add hh2

theorem Expands.mul (hf : Expands f A) (hg : Expands g B) : Expands (fun z ↦ f z * g z) (A * B) := by
  intro z
  obtain ⟨hs1, hh1⟩ := hf z
  obtain ⟨hs2, hh2⟩ := hg z
  set q : ℂ := 𝕢 1 (z : ℂ)
  have ha : Summable fun n ↦ ‖coeff n A * q ^ n‖ := by simpa [norm_mul, norm_pow] using hs1
  have hb : Summable fun n ↦ ‖coeff n B * q ^ n‖ := by simpa [norm_mul, norm_pow] using hs2
  have key : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (coeff kl.1 A * q ^ kl.1) * (coeff kl.2 B * q ^ kl.2) =
      coeff n (A * B) * q ^ n := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · have := summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb
    simpa [key, norm_mul, norm_pow] using this
  · have h1 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb
    have h2 := (summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb).of_norm
    simp only [key] at h1 h2
    rw [hh1.tsum_eq, hh2.tsum_eq] at h1
    show HasSum _ (f z * g z)
    rw [h1]
    exact h2.hasSum

theorem Expands.const_mul (c : ℂ) (hf : Expands f A) : Expands (fun z ↦ c * f z) (C c * A) := by
  intro z
  obtain ⟨hs1, hh1⟩ := hf z
  refine ⟨?_, ?_⟩
  · refine (hs1.mul_left ‖c‖).congr fun n ↦ ?_
    rw [PowerSeries.coeff_C_mul, norm_mul]
    ring
  · simpa [PowerSeries.coeff_C_mul, mul_assoc] using hh1.mul_left c

theorem expands_one : Expands (fun _ ↦ 1) 1 := by
  intro z
  have h : ∀ n ∉ ({0} : Finset ℕ), coeff n (1 : PowerSeries ℂ) * 𝕢 1 (z : ℂ) ^ n = 0 := by
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [PowerSeries.coeff_one, hn]
  refine ⟨summable_of_ne_finset_zero (s := {0}) ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [PowerSeries.coeff_one, hn]
  · have : HasSum (fun n ↦ coeff n (1 : PowerSeries ℂ) * 𝕢 1 (z : ℂ) ^ n)
        (∑ n ∈ ({0} : Finset ℕ), coeff n (1 : PowerSeries ℂ) * 𝕢 1 (z : ℂ) ^ n) :=
      hasSum_sum_of_ne_finset_zero h
    simpa using this

theorem Expands.pow (hf : Expands f A) (n : ℕ) : Expands (fun z ↦ f z ^ n) (A ^ n) := by
  induction n with
  | zero => simpa using expands_one
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem expands_qParam_pow (m : ℕ) : Expands (fun z ↦ 𝕢 1 (z : ℂ) ^ m) (X ^ m) := by
  intro z
  refine ⟨summable_of_ne_finset_zero (s := {m}) ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [PowerSeries.coeff_X_pow, hn]
  · have h : ∀ n ∉ ({m} : Finset ℕ), coeff n (X ^ m : PowerSeries ℂ) * 𝕢 1 (z : ℂ) ^ n = 0 := by
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [PowerSeries.coeff_X_pow, hn]
    have : HasSum (fun n ↦ coeff n (X ^ m : PowerSeries ℂ) * 𝕢 1 (z : ℂ) ^ n)
        (∑ n ∈ ({m} : Finset ℕ), coeff n (X ^ m : PowerSeries ℂ) * 𝕢 1 (z : ℂ) ^ n) :=
      hasSum_sum_of_ne_finset_zero h
    simpa [PowerSeries.coeff_X_pow] using this

/-- **Uniqueness of the coefficients.** -/
theorem Expands.unique (hA : Expands f A) (hB : Expands f B) : A = B := by
  have hrad : ∀ {f : ℍ → ℂ} {A : PowerSeries ℂ}, Expands f A →
      (1 : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n A)).radius := by
    intro f A hA
    refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
    lift r to NNReal using hr.ne_top
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    have hr0' : (0 : ℝ) < r := by exact_mod_cast pos_iff_ne_zero.mpr hr0
    refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    have hq0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0'.ne'
    have hq1 : ‖((r : ℝ) : ℂ)‖ < 1 := by simpa using hr1
    have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq1 hq0
    have h2 := (hA ⟨_, h1⟩).1
    simp only [Function.Periodic.qParam_right_inv one_ne_zero hq0] at h2
    simpa [FormalMultilinearSeries.ofScalars_norm] using h2
  have hball : ∀ {f : ℍ → ℂ} {A : PowerSeries ℂ}, Expands f A →
      HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n A)).sum
        (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n A)) 0
        (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n A)).radius := fun hA ↦
    FormalMultilinearSeries.hasFPowerSeriesOnBall _ (lt_of_lt_of_le one_pos (hrad hA))
  have hsum : ∀ {f : ℍ → ℂ} {A : PowerSeries ℂ}, Expands f A → ∀ τ : ℍ,
      (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n A)).sum (𝕢 1 (τ : ℂ)) = f τ := by
    intro f A hA τ
    have hy : 𝕢 1 (τ : ℂ) ∈ Metric.eball (0 : ℂ)
        (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n A)).radius := by
      refine lt_of_lt_of_le ?_ (hrad hA)
      rw [edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2
        (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)
    have h := (hball hA).hasSum_sub hy
    simp only [sub_zero, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h
    exact h.unique (hA τ).2
  have hcont := fun {f : ℍ → ℂ} {A : PowerSeries ℂ} (hA : Expands f A) ↦
    (hball hA).hasFPowerSeriesAt.continuousAt
  have hev : (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n A)).sum =ᶠ[𝓝 (0 : ℂ)]
      (FormalMultilinearSeries.ofScalars ℂ (fun n ↦ coeff n B)).sum := by
    rw [← (hcont hA).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hcont hB)]
    have hb : ∀ᶠ y in 𝓝[≠] (0 : ℂ), ‖y‖ < 1 :=
      mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_norm continuous_const).mem_nhds (by simp))
    filter_upwards [hb, self_mem_nhdsWithin] with y hy1 hy0
    have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hy1 hy0
    have h2 := Function.Periodic.qParam_right_inv (h := 1) one_ne_zero hy0
    have e1 := hsum hA ⟨_, h1⟩
    have e2 := hsum hB ⟨_, h1⟩
    simp only [h2] at e1 e2
    rw [e1, e2]
  have := (hball hA).hasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    (hball hB).hasFPowerSeriesAt hev
  ext n
  simpa using congr(FormalMultilinearSeries.coeff $this n)

/-- $qj(z) = \sum_n c_n q^n$, absolutely convergent. -/
theorem expands_qParam_mul_j :
    Expands (fun z ↦ 𝕢 1 (z : ℂ) * j z) (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)) := by
  intro z
  refine ⟨?_, by simpa using hasSum_qExpansion_qParam_mul_j z⟩
  have hr : (1 : ENNReal) ≤ (FormalMultilinearSeries.ofScalars ℂ
      (fun m ↦ (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff m)).radius :=
    (hasFPowerSeriesOnBall_cuspFunction one_pos analyticAt_cuspFunction_qParam_mul_j
      hasSum_qExpansion_qParam_mul_j).r_le
  have hlt : ((‖𝕢 1 (z : ℂ)‖₊ : ENNReal)) < (FormalMultilinearSeries.ofScalars ℂ
      (fun m ↦ (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)).coeff m)).radius := by
    refine lt_of_lt_of_le ?_ hr
    rw [← ENNReal.coe_one, ENNReal.coe_lt_coe]
    exact_mod_cast Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
  simpa [FormalMultilinearSeries.ofScalars_norm] using
    FormalMultilinearSeries.summable_norm_mul_pow _ hlt

/-- $q^N j(Nz) = \sum_n c_n q^{Nn}$, absolutely convergent. -/
theorem expands_qParam_pow_mul_j_scale {N : ℕ} (hN : 0 < N) :
    Expands (fun z ↦ 𝕢 1 (z : ℂ) ^ N * j (scaleH N hN z))
      (expand N hN.ne' (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ))) := by
  intro z
  have hq : 𝕢 1 ((scaleH N hN z : ℍ) : ℂ) = 𝕢 1 (z : ℂ) ^ N := by
    simp only [Function.Periodic.qParam, scaleH, UpperHalfPlane.coe_mk]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  obtain ⟨hs, hh⟩ := expands_qParam_mul_j (scaleH N hN z)
  simp only [hq] at hs hh
  have hinj : Function.Injective (fun k : ℕ ↦ N * k) := mul_right_injective₀ hN.ne'
  have hco : ∀ n ∉ Set.range (fun k : ℕ ↦ N * k),
      coeff n (expand N hN.ne' (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ))) = 0 := by
    intro n hn
    rw [PowerSeries.coeff_expand, ite_eq_right_iff]
    rintro ⟨k, rfl⟩
    exact absurd ⟨k, rfl⟩ hn
  have hco' : ∀ k, coeff (N * k) (expand N hN.ne' (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ))) =
      coeff k (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)) := fun k ↦ by simp
  refine ⟨?_, ?_⟩
  · refine (hinj.summable_iff (f := fun n ↦ ‖coeff n (expand N hN.ne'
      (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ)))‖ * ‖𝕢 1 (z : ℂ)‖ ^ n) ?_).mp ?_
    · intro n hn
      simp [hco n hn]
    · refine hs.congr fun k ↦ ?_
      simp [hco', pow_mul, norm_pow]
  · refine (hinj.hasSum_iff (f := fun n ↦ coeff n (expand N hN.ne'
      (qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ * j τ))) * 𝕢 1 (z : ℂ) ^ n) ?_).mp ?_
    · intro n hn
      simp [hco n hn]
    · convert hh using 1
      funext k
      simp [hco', pow_mul]

end ModularFormsKB.Milne.QSeries
