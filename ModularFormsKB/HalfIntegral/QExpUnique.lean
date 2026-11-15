/-
# Uniqueness of $q$-expansions

If $f(\tau) = \sum_{n\ge0} a(n)e^{2\pi i n\tau}$ for every $\tau \in \mathbb H$, the coefficients $a$
are determined by $f$: the difference of two expansions is a power series in $q = e^{2\pi i\tau}$ that vanishes on the
punctured unit disc, so all its coefficients vanish. Used for the Kohnen isomorphism (`ModularFormsKB/HalfIntegral/Abstract/KohnenReduction.lean`).
-/
import ModularFormsKB.HalfIntegral.Abstract.Multiplier

namespace ModularFormsKB.HalfIntegral

open Complex
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **$q$-expansions are unique:** two coefficient sequences expanding the same function on $\mathbb H$ are equal. -/
theorem Abstract.hasQExp_unique {f : ℍ → ℂ} {a b : ℕ → ℂ} (ha : Abstract.HasQExp f a) (hb : Abstract.HasQExp f b) :
    a = b := by
  classical
  set c : ℕ → ℂ := a - b with hcdef
  have hc : ∀ τ : ℍ, HasSum (fun n : ℕ ↦ c n * cexp (2 * π * I * n * τ)) 0 := fun τ ↦ by
    have := (ha τ).sub (hb τ)
    simpa [hcdef, sub_mul] using this
  have hz : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → HasSum (fun n : ℕ ↦ c n * z ^ n) 0 := by
    intro z hz0 hz1
    have him : 0 < ((Complex.log z) / (2 * π * I)).im := by
      have : ((Complex.log z) / (2 * π * I)).im = -Real.log ‖z‖ / (2 * π) := by
        rw [Complex.div_im]
        have hpi := Real.pi_pos
        simp [Complex.log_re, Complex.log_im, Complex.normSq]
        field_simp
      rw [this]
      have := Real.log_neg (norm_pos_iff.mpr hz0) hz1
      have hpi := Real.pi_pos
      apply div_pos <;> linarith
    have h := hc ⟨_, him⟩
    convert h using 3 with n
    have hne : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have : 2 * π * I * n * ((Complex.log z) / (2 * π * I)) = n * Complex.log z := by
      field_simp
    show z ^ n = _
    rw [show (2 * π * I * n * ((⟨_, him⟩ : ℍ) : ℂ)) = n * Complex.log z from this,
      Complex.exp_nat_mul, Complex.exp_log hz0]
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : 1 ≤ p.radius := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    rcases eq_zero_or_pos r with h0 | hpos
    · simp [h0]
    have hne : ((r : ℝ) : ℂ) ≠ 0 := by
      simpa using hpos.ne'
    have hs := (hz (r : ℂ) hne (by simpa using hr1)).summable
    obtain ⟨C, hC⟩ := hs.tendsto_atTop_zero.norm.bddAbove_range
    apply p.le_radius_of_bound C
    intro n
    have := hC ⟨n, rfl⟩
    simpa [hp, norm_mul] using this
  have hps : HasFPowerSeriesOnBall p.sum p 0 p.radius := p.hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hrad)
  have hat : HasFPowerSeriesAt p.sum p 0 := hps.hasFPowerSeriesAt
  have hev : ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, p.sum z = 0 := by
    have h1 : ∀ᶠ z in nhds (0 : ℂ), z ∈ Metric.ball (0 : ℂ) 1 := Metric.ball_mem_nhds _ one_pos
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz1 hz0
    have hzr : z ∈ Metric.eball (0 : ℂ) p.radius := by
      simp only [Metric.mem_eball, edist_zero_right]
      refine lt_of_lt_of_le ?_ hrad
      have : ‖z‖₊ < 1 := by simpa [← NNReal.coe_lt_coe] using hz1
      rw [enorm_eq_nnnorm]
      exact_mod_cast this
    have := hps.hasSum (y := z) hzr
    simp only [zero_add] at this
    have h2 := hz z hz0 (by simpa using hz1)
    refine this.unique ?_
    convert h2 using 2 with n
    simp [hp, mul_comm]
  have hcont : ContinuousAt p.sum 0 := hat.analyticAt.continuousAt
  have h0 : p.sum 0 = 0 := by
    have : (nhdsWithin (0 : ℂ) {0}ᶜ).NeBot := inferInstance
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun z hz ↦ hz.symm))
  have hev2 : ∀ᶠ z in nhds (0 : ℂ), p.sum z = 0 := by
    rw [← nhdsNE_sup_pure, Filter.eventually_sup]
    exact ⟨hev, by simpa using h0⟩
  have hzero : HasFPowerSeriesAt (0 : ℂ → ℂ) p 0 := hat.congr hev2
  have hp0 : p = 0 := hzero.eq_zero
  funext n
  have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q n (fun _ ↦ (1 : ℂ))) hp0
  simp [hp, hcdef, sub_eq_zero] at this
  exact this
