import ModularFormsKB.Miyake.Sec4_3.QSeries
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# Fourier expansions of modular forms on $\Gamma_1(N)$ as `Miyake.qSeries`

Bridges between Mathlib's `qExpansion` and our `qSeries`:

* `Miyake.exists_qSeries_modularForm`: a modular form for $\Gamma_1(N)$ is `qSeries b` on
  $\mathbb H$ for coefficients $b$ of polynomial growth;
* `Miyake.exists_qSeries_cuspForm`: the same for cusp forms, with $b_0 = 0$;
* `Miyake.qSeries_coeff_unique`: coefficients of polynomial growth are determined by the
  $q$-series on $\mathbb H$;
* `Miyake.qSeries_zero_eq_zero_of_isZeroAtImInfty`: if `qSeries a` (polynomial growth) tends to $0$
  at $i\infty$, then $a_0 = 0$.
-/

open Complex Filter Asymptotics CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold

noncomputable section

namespace Miyake

private lemma tendsto_qSeries_atImInfty {a : ℕ → ℂ} (ha : CoeffGrowth a) :
    Tendsto (fun τ : ℍ ↦ qSeries a τ) atImInfty (nhds (a 0)) := by
  obtain ⟨C, hC⟩ := qSeries_sub_bound_large ha
  have h1 : Tendsto (fun y : ℝ ↦ C * Real.exp (-2 * π * y)) atTop (nhds 0) := by
    have := (Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.const_mul_atTop_of_neg (show (-2 * π) < 0 by linarith [Real.pi_pos])
        (tendsto_id (α := ℝ)))).const_mul C
    simpa using this
  have h2 : Tendsto (fun τ : ℍ ↦ C * Real.exp (-2 * π * τ.im)) atImInfty (nhds 0) :=
    h1.comp tendsto_comap
  have h3 : Tendsto (fun τ : ℍ ↦ qSeries a τ - a 0) atImInfty (nhds 0) := by
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [(atImInfty_mem {z : ℍ | 1 ≤ z.im}).2 ⟨1, fun z hz ↦ hz⟩] with τ hτ
    exact hC τ hτ
  simpa using h3.add_const (a 0)

private lemma hasSum_qParam_iff {b : ℕ → ℂ} {s : ℂ} {τ : ℍ} :
    HasSum (fun n : ℕ ↦ b n • Function.Periodic.qParam 1 (τ : ℂ) ^ n) s ↔
      HasSum (fun n : ℕ ↦ b n * cexp (2 * π * I * n * τ)) s := by
  have : (fun n : ℕ ↦ b n • Function.Periodic.qParam 1 (τ : ℂ) ^ n) =
      fun n : ℕ ↦ b n * cexp (2 * π * I * n * τ) := by
    funext n
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [this]

private lemma hasSum_qParam_one(b : ℕ → ℂ) (F : ℍ → ℂ)
    (h : ∀ τ : ℍ, HasSum (fun n : ℕ ↦ b n • Function.Periodic.qParam 1 (τ : ℂ) ^ n) (F τ))
    (τ : ℍ) : F τ = qSeries b τ := by
  have : (fun n : ℕ ↦ b n • Function.Periodic.qParam 1 (τ : ℂ) ^ n) =
      fun n : ℕ ↦ b n * cexp (2 * π * I * n * τ) := by
    funext n
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul, smul_eq_mul]
    congr 2
    push_cast
    ring
  have h' := h τ
  rw [this] at h'
  exact h'.tsum_eq.symm


/-- If `qSeries a` (with `CoeffGrowth a`) tends to $0$ at $i\infty$ then $a_0 = 0$. -/
lemma qSeries_zero_eq_zero_of_isZeroAtImInfty {a : ℕ → ℂ} (ha : CoeffGrowth a)
    (h : IsZeroAtImInfty fun τ : ℍ ↦ qSeries a τ) : a 0 = 0 :=
  tendsto_nhds_unique (tendsto_qSeries_atImInfty ha) h

/-- `qSeries a` with `CoeffGrowth a` is bounded at $i\infty$. -/
lemma isBoundedAtImInfty_qSeries {a : ℕ → ℂ} (ha : CoeffGrowth a) :
    IsBoundedAtImInfty fun τ : ℍ ↦ qSeries a τ := by
  obtain ⟨C, hC⟩ := qSeries_sub_bound_large ha
  rw [isBoundedAtImInfty_iff]
  refine ⟨|C| + ‖a 0‖, 1, fun z hz ↦ ?_⟩
  have h1 := hC z hz
  rw [UpperHalfPlane.coe_im] at h1
  have h2 : C * Real.exp (-2 * π * z.im) ≤ |C| := by
    calc C * Real.exp (-2 * π * z.im) ≤ |C| * Real.exp (-2 * π * z.im) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.2 (by have := Real.pi_pos; have := z.im_pos; nlinarith)) (abs_nonneg C)
      _ = |C| := mul_one _
  have h3 : ‖qSeries a z‖ ≤ ‖qSeries a z - a 0‖ + ‖a 0‖ := by
    have := norm_add_le (qSeries a z - a 0) (a 0)
    simpa using this
  linarith

/-- `qSeries a` with `CoeffGrowth a` and $a_0 = 0$ tends to $0$ at $i\infty$. -/
lemma isZeroAtImInfty_qSeries {a : ℕ → ℂ} (ha : CoeffGrowth a) (h0 : a 0 = 0) :
    IsZeroAtImInfty fun τ : ℍ ↦ qSeries a τ := by
  have := tendsto_qSeries_atImInfty ha
  rwa [h0] at this

/-- `qSeries a` with `CoeffGrowth a` is holomorphic as a function on $\mathbb H$ (`MDifferentiable`). -/
lemma mdifferentiable_qSeries {a : ℕ → ℂ} (ha : CoeffGrowth a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun τ : ℍ ↦ qSeries a τ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (differentiableOn_qSeries ha).congr fun z hz ↦ ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]

/-- Uniqueness of coefficients: two coefficient sequences of polynomial growth with the same
$q$-series on $\mathbb H$ are equal. -/
lemma qSeries_coeff_unique {a a' : ℕ → ℂ} (ha : CoeffGrowth a) (ha' : CoeffGrowth a')
    (h : ∀ z : ℂ, 0 < z.im → qSeries a z = qSeries a' z) : a = a' := by
  have hper : Function.Periodic
      ((fun τ : ℍ ↦ qSeries a τ) ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    refine UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ ?_
    show qSeries a (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) = qSeries a τ
    rw [UpperHalfPlane.coe_vadd, add_comm]
    exact qSeries_add_one _
  have han : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (fun τ : ℍ ↦ qSeries a τ)) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hper (mdifferentiable_qSeries ha)
      (isBoundedAtImInfty_qSeries ha)
  have h1 : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ a m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (qSeries a τ) := fun τ ↦ by
    rw [hasSum_qParam_iff]
    exact hasSum_qSeries ha τ.im_pos
  have h2 : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ a' m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (qSeries a τ) := fun τ ↦ by
    rw [hasSum_qParam_iff, h τ τ.im_pos]
    exact hasSum_qSeries ha' τ.im_pos
  funext m
  have p1 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction (h := (1 : ℝ))
    (f := fun τ : ℍ ↦ qSeries a τ) one_pos han h1).hasFPowerSeriesAt
  have p2 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction (h := (1 : ℝ))
    (f := fun τ : ℍ ↦ qSeries a τ) one_pos han h2).hasFPowerSeriesAt
  simpa using congr(FormalMultilinearSeries.coeff $(p1.eq_formalMultilinearSeries p2) m)

private lemma exists_qSeries_aux {k : ℤ} {N : ℕ} (_hN : 0 < N) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (hg : CoeffGrowth fun n ↦ (UpperHalfPlane.qExpansion 1 f).coeff n) :
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ ∀ τ : ℍ, f τ = qSeries b τ := by
  have hΓ : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _
  refine ⟨fun n ↦ (UpperHalfPlane.qExpansion 1 f).coeff n, hg, ?_⟩
  refine hasSum_qParam_one _ _ (fun τ ↦ ?_)
  have : Fact (IsCusp OnePoint.infty (Gamma1 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) τ

/-- A modular form of weight $k$ for $\Gamma_1(N)$ equals `qSeries b` on $\mathbb H$ for some
coefficients $b$ of polynomial growth (its $q$-expansion at $\infty$, of width $1$). -/
lemma exists_qSeries_modularForm {k : ℤ} {N : ℕ} (hN : 0 < N) (F : ModularForm (Gamma1 N) k) :
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ ∀ τ : ℍ, F τ = qSeries b τ := by
  have : NeZero N := ⟨hN.ne'⟩
  apply exists_qSeries_aux hN F
  rcases lt_or_ge k 0 with hk | hk
  · have h0 : F = 0 := ModularForm.isZero_of_neg_weight hk F
    subst h0
    have h1 : (fun n ↦ (UpperHalfPlane.qExpansion 1 (⇑(0 : ModularForm (Gamma1 N) k))).coeff n)
        = 0 := by
      ext n
      have : ⇑(0 : ModularForm (Gamma1 N) k) = (0 : ℍ → ℂ) := rfl
      simp [this, UpperHalfPlane.qExpansion_zero]
    rw [h1]
    exact ⟨0, Asymptotics.isBigO_zero _ _⟩
  · have := ModularFormClass.qExpansion_isBigO hk F
    rw [strictWidthInfty_Gamma1] at this
    exact ⟨k, by simpa [Real.rpow_intCast] using this⟩

/-- A cusp form of weight $k$ for $\Gamma_1(N)$ equals `qSeries b` on $\mathbb H$ for some
coefficients $b$ of polynomial growth with $b_0 = 0$. -/
lemma exists_qSeries_cuspForm {k : ℤ} {N : ℕ} (hN : 0 < N) (F : CuspForm (Gamma1 N) k) :
    ∃ b : ℕ → ℂ, CoeffGrowth b ∧ b 0 = 0 ∧ ∀ τ : ℍ, F τ = qSeries b τ := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨b, hb, hF⟩ := exists_qSeries_aux hN F (by
    have := CuspFormClass.qExpansion_isBigO F
    rw [strictWidthInfty_Gamma1] at this
    exact ⟨_, this⟩)
  refine ⟨b, hb, ?_, hF⟩
  apply qSeries_zero_eq_zero_of_isZeroAtImInfty hb
  have h0 : (fun τ : ℍ ↦ qSeries b τ) = F := funext fun τ ↦ (hF τ).symm
  rw [h0]
  exact CuspFormClass.zero_at_infty F

end Miyake
