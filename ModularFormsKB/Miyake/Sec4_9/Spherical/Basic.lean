import ModularFormsKB.Citation
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp

/-!
# Theta series with a polynomial weight: definitions, convergence, holomorphy

Miyake, *Modular Forms* (Springer 1989), §4.9.

Miyake's theta series carry a *spherical function* `P` (a harmonic homogeneous polynomial). We work
in the setting of Tau Ceti's lattice theta series: a discrete subgroup `L` of a real inner product
space `E`, the term `exp (π i ‖x‖² τ)`, and a weight `p : E → ℂ`:

`θ_{γ+L}(τ; p) = ∑_{v ∈ L} p (γ + v) exp (π i ‖γ + v‖² τ)`  (`thetaW L p γ τ`).

For `p = 1` this is Tau Ceti's `ZLattice.thetaCoset`. The spherical weights are the powers
`x ↦ (⟪u, x⟫ + i ⟪w, x⟫) ^ ν` of a complex linear form (`isoForm u w`), with `ν ≤ 1` or the form
isotropic: `‖u‖ = ‖w‖` and `⟪u, w⟫ = 0`, that is `⟪ζ, ζ⟫ = 0` for `ζ = u + i w` (`IsSphericalDatum`).
These are harmonic, and span the harmonic homogeneous polynomials of degree `ν` (classical; the
spanning statement is not formalized here, see the loose end recorded for row 5).

This file: the definition, absolute and locally uniform convergence for weights of polynomial
growth (`PolyBounded`), holomorphy on `ℍ`, boundedness at `i∞`, and vanishing at `i∞` when the
weight vanishes at the origin (so for a spherical weight of degree `ν ≥ 1`).
-/

open Complex Filter Topology
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos mdifferentiable_iff)
open scoped Real Manifold UpperHalfPlane RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Spherical weights -/

/-- The complex linear form `x ↦ ⟪u, x⟫ + i ⟪w, x⟫`, i.e. `x ↦ ⟪ζ, x⟫` for `ζ = u + i w`. -/
noncomputable def isoForm (u w : E) (x : E) : ℂ := (⟪u, x⟫ : ℂ) + I * (⟪w, x⟫ : ℂ)

/-- A datum `(ν, u, w)` gives a spherical weight `isoForm u w ^ ν` when `ν ≤ 1` or the vector
`ζ = u + i w` is isotropic, `⟪ζ, ζ⟫ = ‖u‖² - ‖w‖² + 2 i ⟪u, w⟫ = 0`. -/
def IsSphericalDatum (ν : ℕ) (u w : E) : Prop := ν ≤ 1 ∨ (‖u‖ = ‖w‖ ∧ ⟪u, w⟫ = 0)

theorem isoForm_add (u w x y : E) : isoForm u w (x + y) = isoForm u w x + isoForm u w y := by
  simp only [isoForm, inner_add_right]; push_cast; ring

theorem isoForm_smul (u w : E) (c : ℝ) (x : E) : isoForm u w (c • x) = c * isoForm u w x := by
  simp only [isoForm, inner_smul_right]; push_cast; ring

theorem isoForm_neg (u w x : E) : isoForm u w (-x) = -isoForm u w x := by
  simp only [isoForm, inner_neg_right]; push_cast; ring

theorem isoForm_zero (u w : E) : isoForm u w 0 = 0 := by simp [isoForm]

theorem norm_isoForm_le (u w x : E) : ‖isoForm u w x‖ ≤ (‖u‖ + ‖w‖) * ‖x‖ := by
  unfold isoForm
  calc ‖(⟪u, x⟫ : ℂ) + I * (⟪w, x⟫ : ℂ)‖ ≤ ‖(⟪u, x⟫ : ℂ)‖ + ‖I * (⟪w, x⟫ : ℂ)‖ := norm_add_le _ _
    _ = |⟪u, x⟫| + |⟪w, x⟫| := by simp
    _ ≤ ‖u‖ * ‖x‖ + ‖w‖ * ‖x‖ := add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = _ := by ring

/-- A weight of polynomial growth: `‖p x‖ ≤ C (1 + ‖x‖) ^ K`. -/
def PolyBounded (p : E → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ x, ‖p x‖ ≤ C * (1 + ‖x‖) ^ n

theorem polyBounded_isoForm_pow (u w : E) (ν : ℕ) : PolyBounded fun x ↦ isoForm u w x ^ ν := by
  refine ⟨(‖u‖ + ‖w‖) ^ ν, by positivity, ν, fun x ↦ ?_⟩
  rw [norm_pow, ← mul_pow]
  gcongr
  calc ‖isoForm u w x‖ ≤ (‖u‖ + ‖w‖) * ‖x‖ := norm_isoForm_le u w x
    _ ≤ (‖u‖ + ‖w‖) * (1 + ‖x‖) := by gcongr; linarith

theorem polyBounded_one : PolyBounded (fun _ : E ↦ (1 : ℂ)) :=
  ⟨1, zero_le_one, 0, fun x ↦ by simp⟩

/-- The elementary bound `(1 + t) ^ n exp (-2 a t²) ≤ exp (n² / (4 a)) exp (-a t²)` for `t ≥ 0`. -/
theorem one_add_pow_mul_exp_le {a : ℝ} (ha : 0 < a) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ n * Real.exp (-(2 * a) * t ^ 2) ≤
      Real.exp ((n : ℝ) ^ 2 / (4 * a)) * Real.exp (-a * t ^ 2) := by
  have h1 : (1 + t) ^ n ≤ Real.exp (n * t) := by
    rw [mul_comm, Real.exp_mul]
    calc (1 + t) ^ n ≤ Real.exp t ^ n := by
          gcongr
          linarith [Real.add_one_le_exp t]
      _ = _ := by rw [← Real.rpow_natCast]
  calc (1 + t) ^ n * Real.exp (-(2 * a) * t ^ 2) ≤ Real.exp (n * t) * Real.exp (-(2 * a) * t ^ 2) := by
        gcongr
    _ = Real.exp (n * t - 2 * a * t ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((n : ℝ) ^ 2 / (4 * a) - a * t ^ 2) := by
        apply Real.exp_le_exp.mpr
        have h : 0 ≤ a * (t - n / (2 * a)) ^ 2 := by positivity
        have h' : a * (t - n / (2 * a)) ^ 2 = a * t ^ 2 - n * t + (n : ℝ) ^ 2 / (4 * a) := by
          field_simp; ring
        linarith
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-! ### The weighted theta series -/

/-- **The theta series with weight `p`** of the translate `γ + L`:
`θ_{γ+L}(τ; p) = ∑_{v ∈ L} p (γ + v) exp (π i ‖γ + v‖² τ)`. -/
noncomputable def thetaW (L : Submodule ℤ E) (p : E → ℂ) (γ : E) (τ : ℍ) : ℂ :=
  ∑' v : L, p (γ + v) * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ)

/-- **Miyake's theta series with a spherical function** in lattice form: weight
`(⟪u, x⟫ + i ⟪w, x⟫) ^ ν`. -/
noncomputable def thetaSph (L : Submodule ℤ E) (ν : ℕ) (u w γ : E) (τ : ℍ) : ℂ :=
  thetaW L (fun x ↦ isoForm u w x ^ ν) γ τ

theorem thetaW_apply (L : Submodule ℤ E) (p : E → ℂ) (γ : E) (τ : ℍ) :
    thetaW L p γ τ = ∑' v : L, p (γ + v) * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ) := rfl

/-- With the constant weight `1`, `thetaW` is Tau Ceti's coset theta series. -/
theorem thetaW_one (L : Submodule ℤ E) (γ : E) : thetaW L (fun _ ↦ 1) γ = ZLattice.thetaCoset L γ := by
  ext τ; simp [thetaW, ZLattice.thetaCoset_apply]

theorem thetaW_add_mem (L : Submodule ℤ E) (p : E → ℂ) (γ : E) {w : E} (hw : w ∈ L) :
    thetaW L p (γ + w) = thetaW L p γ := by
  ext τ
  simp only [thetaW_apply, add_assoc]
  exact (Equiv.addLeft (⟨w, hw⟩ : L)).tsum_eq
    fun v : L => p (γ + v) * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ)

theorem thetaW_eq_of_sub_mem (L : Submodule ℤ E) (p : E → ℂ) {γ δ : E} (h : γ - δ ∈ L) :
    thetaW L p γ = thetaW L p δ := by
  rw [← thetaW_add_mem L p δ h, add_sub_cancel]

/-- Reflection: `θ_{-γ+L}(τ; p) = θ_{γ+L}(τ; p ∘ neg)`. -/
theorem thetaW_neg (L : Submodule ℤ E) (p : E → ℂ) (γ : E) :
    thetaW L p (-γ) = thetaW L (fun x ↦ p (-x)) γ := by
  ext τ
  rw [thetaW_apply, thetaW_apply,
    ← (Equiv.neg L).tsum_eq fun v : L => p (-γ + v) * cexp (π * I * (‖-γ + (v : E)‖ ^ 2 : ℝ) * τ)]
  refine tsum_congr fun v => ?_
  rw [Equiv.neg_apply, Submodule.coe_neg, ← neg_add, norm_neg]

/-- For an odd or even weight, `θ_{-γ+L} = ± θ_{γ+L}`. -/
theorem thetaSph_neg (L : Submodule ℤ E) (ν : ℕ) (u w γ : E) (τ : ℍ) :
    thetaSph L ν u w (-γ) τ = (-1) ^ ν * thetaSph L ν u w γ τ := by
  rw [thetaSph, thetaW_neg, thetaSph, thetaW_apply, thetaW_apply, ← tsum_mul_left]
  refine tsum_congr fun v ↦ ?_
  rw [isoForm_neg, neg_pow]
  ring

variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The Gaussian majorant of a weighted theta term: for `y ≤ im τ`,
`‖p x exp (π i ‖x‖² τ)‖ ≤ C exp (n² / (2 π y)) exp (-(π y / 2) ‖x‖²)`. -/
theorem norm_thetaWTerm_le {p : E → ℂ} {C : ℝ} (hC : 0 ≤ C) {n : ℕ}
    (hp : ∀ x, ‖p x‖ ≤ C * (1 + ‖x‖) ^ n)
    {y : ℝ} (hy : 0 < y) (x : E) {z : ℂ} (hz : y ≤ z.im) :
    ‖p x * cexp (π * I * (‖x‖ ^ 2 : ℝ) * z)‖ ≤
      C * Real.exp ((n : ℝ) ^ 2 / (4 * (π * y / 2))) * Real.exp (-(π * y / 2) * ‖x‖ ^ 2) := by
  rw [norm_mul]
  have he := Complex.norm_exp_pi_mul_I_mul_ofReal_mul_le (t := ‖x‖ ^ 2) (by positivity) hz
  have h2 := one_add_pow_mul_exp_le (a := π * y / 2) (by positivity) n (norm_nonneg x)
  calc ‖p x‖ * ‖cexp (π * I * (‖x‖ ^ 2 : ℝ) * z)‖
      ≤ (C * (1 + ‖x‖) ^ n) * Real.exp (-(π * y) * ‖x‖ ^ 2) := by
        gcongr
        exact hp x
    _ = C * ((1 + ‖x‖) ^ n * Real.exp (-(2 * (π * y / 2)) * ‖x‖ ^ 2)) := by ring_nf
    _ ≤ C * (Real.exp ((n : ℝ) ^ 2 / (4 * (π * y / 2))) * Real.exp (-(π * y / 2) * ‖x‖ ^ 2)) := by
        gcongr
    _ = _ := by ring

variable {L} in
/-- The weighted theta terms over `γ + L` are dominated, uniformly on `{y ≤ im τ}`, by a summable
Gaussian. -/
theorem exists_summable_thetaW_bound {p : E → ℂ} (hp : PolyBounded p) (γ : E) {y : ℝ} (hy : 0 < y) :
    ∃ u : L → ℝ, Summable u ∧ ∀ (v : L) (z : ℂ), y ≤ z.im →
      ‖p (γ + v) * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * z)‖ ≤ u v := by
  obtain ⟨C, hC, n, hpb⟩ := hp
  refine ⟨fun v ↦ C * Real.exp ((n : ℝ) ^ 2 / (4 * (π * y / 2))) *
      Real.exp (-(π * y / 2) * ‖γ + (v : E)‖ ^ 2), ?_, fun v z hz ↦
    norm_thetaWTerm_le hC hpb hy _ hz⟩
  exact (ZLattice.summable_exp_neg_mul_norm_add_sq L (c := π * y / 2) (by positivity) γ).mul_left _

theorem summable_norm_thetaW {p : E → ℂ} (hp : PolyBounded p) (γ : E) (τ : ℍ) :
    Summable fun v : L ↦ ‖p (γ + v) * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ)‖ := by
  obtain ⟨u, hu, hle⟩ := exists_summable_thetaW_bound (L := L) hp γ τ.im_pos
  exact hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun v ↦ hle v τ le_rfl

theorem summable_thetaW {p : E → ℂ} (hp : PolyBounded p) (γ : E) (τ : ℍ) :
    Summable fun v : L ↦ p (γ + v) * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ) :=
  (summable_norm_thetaW L hp γ τ).of_norm

/-- The weighted theta series is holomorphic on the upper half-plane. -/
theorem mdifferentiable_thetaW {p : E → ℂ} (hp : PolyBounded p) (γ : E) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaW L p γ) := by
  refine mdifferentiable_iff.mpr fun z hz ↦ ?_
  have hz' : 0 < z.im := hz
  set U : Set ℂ := {w : ℂ | z.im / 2 < w.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := half_lt_self hz'
  obtain ⟨u, hu, hle⟩ := exists_summable_thetaW_bound (L := L) hp γ (half_pos hz')
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => ∑' v : L, p (γ + v) * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * w)) U :=
    differentiableOn_tsum_of_summable_norm hu
      (fun v => (((differentiable_id.const_mul _).cexp).const_mul _).differentiableOn) hU
      fun v w hw => hle v w (le_of_lt hw)
  refine ((hdiff z hzU).differentiableAt (hU.mem_nhds hzU)).congr_of_eventuallyEq ?_
    |>.differentiableWithinAt
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans (half_pos hz') hw
  simp [thetaW_apply, ofComplex_apply_of_im_pos hw']

/-- The weighted theta series is bounded on `{1 ≤ im τ}`, hence at `i∞`. -/
theorem isBoundedAtImInfty_thetaW {p : E → ℂ} (hp : PolyBounded p) (γ : E) :
    UpperHalfPlane.IsBoundedAtImInfty (thetaW L p γ) := by
  obtain ⟨u, hu, hle⟩ := exists_summable_thetaW_bound (L := L) hp γ one_pos
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨∑' v, u v, 1, fun τ hτ ↦ ?_⟩
  rw [thetaW_apply]
  exact (norm_tsum_le_tsum_norm (summable_norm_thetaW L hp γ τ)).trans
    (Summable.tsum_le_tsum (fun v ↦ hle v τ hτ) (summable_norm_thetaW L hp γ τ) hu)

/-- If the weight vanishes at the origin, the weighted theta series tends to `0` at `i∞`: every
term tends to `0` (the term at `γ + v = 0` is `0`), with a summable dominating Gaussian. -/
theorem isZeroAtImInfty_thetaW {p : E → ℂ} (hp : PolyBounded p) (hp0 : p 0 = 0) (γ : E) :
    UpperHalfPlane.IsZeroAtImInfty (thetaW L p γ) := by
  obtain ⟨u, hu, hle⟩ := exists_summable_thetaW_bound (L := L) hp γ one_pos
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := UpperHalfPlane.atImInfty)
    (f := fun (τ : ℍ) (v : L) ↦ p (γ + v) * cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * τ))
    (g := fun _ ↦ 0) hu (fun v ↦ ?_) ?_
  · rw [tsum_zero] at h
    exact h
  · by_cases hv : γ + (v : E) = 0
    · simp [hv, hp0]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_mul, Complex.norm_exp_pi_mul_I_mul_ofReal_mul, UpperHalfPlane.coe_im]
    rw [← mul_zero ‖p (γ + v)‖]
    exact (Real.tendsto_exp_atBot.comp <|
      (tendsto_comap : Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty atTop).const_mul_atTop_of_neg
        (neg_lt_zero.mpr (mul_pos Real.pi_pos (pow_pos (norm_pos_iff.mpr hv) 2)))).const_mul _
  · filter_upwards [(UpperHalfPlane.atImInfty_mem {τ : ℍ | 1 ≤ τ.im}).mpr ⟨1, fun _ h => h⟩]
      with τ hτ v
    exact hle v τ hτ

end ModularFormsKB.Miyake.Sec4_9
