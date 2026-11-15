import ModularFormsKB.Miyake.Sec4_9.Spherical.Basic
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The inversion law of theta series with a spherical weight (Miyake, Lemma 4.9.1)

Miyake, *Modular Forms* (Springer 1989), Lemma 4.9.1, p. 187.

Let `L` be a full lattice in a real inner product space `E` of dimension `n` (any `n`, odd or even),
`ζ = u + i w` with `ν ≤ 1` or `⟪ζ, ζ⟫ = 0`, and `P(x) = ⟪ζ, x⟫ ^ ν` (`isoForm u w x ^ ν`). Then

`θ_{v+L}(-1/τ; P) = (covol L)⁻¹ (-τ)^ν (τ / i)^{n/2} ∑_{m ∈ L^∨} P(m) e(⟪v, m⟫) exp (π i ‖m‖² τ)`

(`thetaSph_S_smul`), with the principal branch of `(τ / i)^{n/2}` (`τ / i` has positive real
part). In even rank `n = 2k` the factor is `(-i)^k τ^k (-τ)^ν` (`thetaSph_S_smul_of_finrank_eq`).

**Proof.** The Fourier transform of the Schwartz function `P(x) exp (π i σ ‖x‖²)` is
`σ^{-ν} P(ξ) 𝓕(exp (π i σ ‖·‖²))(ξ)` (`fourier_isoForm_pow_mul_gaussian`): with
`D = ∂_u + i ∂_w`, `D (P_j G) = 2 π i σ P_{j+1} G` because `D ⟪ζ, x⟫ = ⟪ζ, ζ⟫ = 0`, so
`P_ν G = (2 π i σ)^{-ν} D^ν G`, and `𝓕 (∂_m f) = 2 π i ⟪·, m⟫ 𝓕 f` (Mathlib's
`SchwartzMap.fourier_lineDerivOp_eq`) turns `D^ν` into multiplication by `(2 π i)^ν P(ξ)`. Then
Poisson summation over `L` (Tau Ceti's `SchwartzMap.tsum_eq_tsum_dual_fourier`). Miyake's own
proof differentiates the theta function of a quadratic form with respect to a characteristic.
-/

open Complex Module
open scoped Real RealInnerProductSpace FourierTransform UpperHalfPlane LineDeriv SchwartzMap

namespace ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `isoForm u w (x + t m) = isoForm u w x + t isoForm u w m`. -/
theorem isoForm_add_smul (u w x m : E) (t : ℝ) :
    isoForm u w (x + t • m) = isoForm u w x + t * isoForm u w m := by
  rw [isoForm_add, isoForm_smul]

/-- The line derivative of `x ↦ ⟪ζ, x⟫ ^ j exp (-b ‖x‖²)` in direction `m`. -/
theorem hasLineDerivAt_isoForm_pow_mul_gauss (u w : E) (j : ℕ) (b : ℂ) (x m : E) :
    HasLineDerivAt ℝ (fun y : E ↦ isoForm u w y ^ j * cexp (-b * ‖y‖ ^ 2))
      ((j * isoForm u w x ^ (j - 1) * isoForm u w m +
        isoForm u w x ^ j * (-b * (2 * ⟪x, m⟫))) * cexp (-b * ‖x‖ ^ 2)) x m := by
  unfold HasLineDerivAt
  have hfun : (fun t : ℝ ↦ isoForm u w (x + t • m) ^ j * cexp (-b * ‖x + t • m‖ ^ 2)) =
      fun t : ℝ ↦ (isoForm u w x + (t : ℂ) * isoForm u w m) ^ j *
        cexp (-b * (((‖x‖ ^ 2 + 2 * t * ⟪x, m⟫ + t ^ 2 * ‖m‖ ^ 2 : ℝ)) : ℂ)) := by
    funext t
    rw [isoForm_add_smul]
    congr 3
    have : ‖x + t • m‖ ^ 2 = ‖x‖ ^ 2 + 2 * t * ⟪x, m⟫ + t ^ 2 * ‖m‖ ^ 2 := by
      rw [@norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    exact_mod_cast this
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ ↦ isoForm u w x + (t : ℂ) * isoForm u w m)
      (isoForm u w m) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (isoForm u w m)).const_add
      (isoForm u w x)
  have h2 : HasDerivAt (fun t : ℝ ↦ ((‖x‖ ^ 2 + 2 * t * ⟪x, m⟫ + t ^ 2 * ‖m‖ ^ 2 : ℝ) : ℂ))
      ((2 * ⟪x, m⟫ : ℝ) : ℂ) 0 := by
    have : HasDerivAt (fun t : ℝ ↦ ‖x‖ ^ 2 + 2 * t * ⟪x, m⟫ + t ^ 2 * ‖m‖ ^ 2)
        (2 * ⟪x, m⟫) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const ⟪x, m⟫).const_add (‖x‖ ^ 2) |>.add
        (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖m‖ ^ 2))
      convert this using 1
      · funext t; simp
      · simp
    exact this.ofReal_comp
  have h3 := (h1.pow j).mul ((h2.const_mul (-b)).cexp)
  convert h3 using 1
  simp only [Pi.pow_apply, zero_mul, add_zero, mul_zero, ofReal_zero, zero_pow two_ne_zero]
  push_cast
  ring

/-- The line derivative `∂_m` of `x ↦ ⟪ζ, x⟫ ^ j exp (-b ‖x‖²)`, as a value of `lineDeriv`. -/
theorem lineDeriv_isoForm_pow_mul_gauss (u w : E) (j : ℕ) (b : ℂ) (x m : E) :
    lineDeriv ℝ (fun y : E ↦ isoForm u w y ^ j * cexp (-b * ‖y‖ ^ 2)) x m =
      (j * isoForm u w x ^ (j - 1) * isoForm u w m +
        isoForm u w x ^ j * (-b * (2 * ⟪x, m⟫))) * cexp (-b * ‖x‖ ^ 2) :=
  (hasLineDerivAt_isoForm_pow_mul_gauss u w j b x m).lineDeriv

theorem isoForm_self_add (u w : E) :
    isoForm u w u + I * isoForm u w w = (‖u‖ ^ 2 - ‖w‖ ^ 2 : ℝ) + 2 * I * ⟪u, w⟫ := by
  simp only [isoForm, real_inner_self_eq_norm_sq, real_inner_comm u w]
  push_cast
  ring_nf
  rw [I_sq]
  ring

variable [FiniteDimensional ℝ E]

/-- The operator `D = ∂_u + i ∂_w` on Schwartz functions. -/
noncomputable def isoDeriv (u w : E) (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) := ∂_{u} f + I • ∂_{w} f

/-- **Iterated `D` of a Gaussian.** For `j ≤ ν` with `(ν, u, w)` spherical,
`D^j (exp (-b ‖x‖²)) = (-2 b)^j ⟪ζ, x⟫ ^ j exp (-b ‖x‖²)`. -/
theorem isoDeriv_iterate_gaussian_apply {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w)
    {b : ℂ} (hb : 0 < b.re) {j : ℕ} (hj : j ≤ ν) (x : E) :
    ((isoDeriv u w)^[j] (SchwartzMap.gaussian hb)) x =
      (-2 * b) ^ j * (isoForm u w x ^ j * cexp (-b * ‖x‖ ^ 2)) := by
  induction j generalizing x with
  | zero => simp [SchwartzMap.gaussian_apply]
  | succ j ih =>
    have hfun : ⇑((isoDeriv u w)^[j] (SchwartzMap.gaussian hb)) =
        fun y : E ↦ (-2 * b) ^ j * (isoForm u w y ^ j * cexp (-b * ‖y‖ ^ 2)) :=
      funext (ih (by omega))
    rw [Function.iterate_succ_apply', isoDeriv, SchwartzMap.add_apply, SchwartzMap.smul_apply,
      SchwartzMap.lineDerivOp_apply, SchwartzMap.lineDerivOp_apply, hfun]
    have hl (m : E) : lineDeriv ℝ (fun y : E ↦ (-2 * b) ^ j *
        (isoForm u w y ^ j * cexp (-b * ‖y‖ ^ 2))) x m = (-2 * b) ^ j *
        ((j * isoForm u w x ^ (j - 1) * isoForm u w m +
          isoForm u w x ^ j * (-b * (2 * ⟪x, m⟫))) * cexp (-b * ‖x‖ ^ 2)) := by
      have h := (hasLineDerivAt_isoForm_pow_mul_gauss u w j b x m).const_mul ((-2 * b) ^ j)
      exact HasLineDerivAt.lineDeriv (𝕜 := ℝ) (f := fun y : E ↦ (-2 * b) ^ j *
        (isoForm u w y ^ j * cexp (-b * ‖y‖ ^ 2))) h
    rw [hl, hl, smul_eq_mul]
    -- The `j`-term carries `⟪ζ, ζ⟫`, which vanishes (or `j = 0`).
    have hzero : (j : ℂ) * isoForm u w x ^ (j - 1) * (isoForm u w u + I * isoForm u w w) = 0 := by
      rcases hsph with hν | ⟨hn, hi⟩
      · have : j = 0 := by omega
        simp [this]
      · rw [isoForm_self_add, hn, hi]; simp
    have hx : isoForm u w x = (⟪u, x⟫ : ℂ) + I * (⟪w, x⟫ : ℂ) := rfl
    rw [real_inner_comm x u, real_inner_comm x w] at hx
    linear_combination (-2 * b) ^ j * cexp (-b * ‖x‖ ^ 2) * hzero +
      (-2 * b) ^ j * cexp (-b * ‖x‖ ^ 2) * isoForm u w x ^ j * (2 * b) * hx

/-- `𝓕 (D f) = 2 π i ⟪ζ, ·⟫ 𝓕 f`. -/
theorem fourier_isoDeriv_apply [MeasurableSpace E] [BorelSpace E] (u w : E) (f : 𝓢(E, ℂ))
    (ξ : E) : 𝓕 (isoDeriv u w f) ξ = 2 * π * I * isoForm u w ξ * 𝓕 f ξ := by
  have hu : (inner ℝ · u).HasTemperateGrowth := ((innerSL ℝ).flip u).hasTemperateGrowth
  have hw : (inner ℝ · w).HasTemperateGrowth := ((innerSL ℝ).flip w).hasTemperateGrowth
  rw [isoDeriv, FourierAdd.fourier_add, FourierSMul.fourier_smul, SchwartzMap.add_apply, SchwartzMap.smul_apply,
    SchwartzMap.fourier_lineDerivOp_eq, SchwartzMap.fourier_lineDerivOp_eq,
    SchwartzMap.smul_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hu,
    SchwartzMap.smulLeftCLM_apply_apply hw]
  simp only [isoForm, smul_eq_mul, real_inner_comm ξ u, real_inner_comm ξ w, Complex.real_smul]
  ring

theorem fourier_isoDeriv_iterate_apply [MeasurableSpace E] [BorelSpace E] (u w : E)
    (f : 𝓢(E, ℂ)) (j : ℕ) (ξ : E) :
    𝓕 ((isoDeriv u w)^[j] f) ξ = (2 * π * I * isoForm u w ξ) ^ j * 𝓕 f ξ := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', fourier_isoDeriv_apply, ih]; ring

variable [MeasurableSpace E] [BorelSpace E]

/-- The Schwartz function `x ↦ ⟪ζ, x⟫ ^ ν exp (-b ‖x‖²)`, as `(-2 b)^{-ν} D^ν` of the Gaussian. -/
noncomputable def sphGauss (ν : ℕ) (u w : E) {b : ℂ} (hb : 0 < b.re) : 𝓢(E, ℂ) :=
  ((-2 * b) ^ ν)⁻¹ • (isoDeriv u w)^[ν] (SchwartzMap.gaussian hb)

theorem sphGauss_apply {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) {b : ℂ} (hb : 0 < b.re)
    (x : E) : sphGauss ν u w hb x = isoForm u w x ^ ν * cexp (-b * ‖x‖ ^ 2) := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  rw [sphGauss, SchwartzMap.smul_apply, isoDeriv_iterate_gaussian_apply hsph hb le_rfl, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by simpa using hb0)), one_mul]

/-- **Fourier transform of a spherical weight times a Gaussian**:
`𝓕 (⟪ζ, ·⟫ ^ ν exp (-b ‖·‖²)) ξ = (-2b)^{-ν} (2 π i ⟪ζ, ξ⟫)^ν (π / b)^{n/2} exp (-π² ‖ξ‖² / b)`. -/
theorem fourier_sphGauss_apply {ν : ℕ} (u w : E) {b : ℂ} (hb : 0 < b.re) (ξ : E) :
    𝓕 (sphGauss ν u w hb : E → ℂ) ξ = ((-2 * b) ^ ν)⁻¹ * (2 * π * I * isoForm u w ξ) ^ ν *
      ((π / b) ^ (finrank ℝ E / 2 : ℂ) * cexp (-π ^ 2 * ‖ξ‖ ^ 2 / b)) := by
  rw [← SchwartzMap.fourier_coe, sphGauss, FourierSMul.fourier_smul, SchwartzMap.smul_apply,
    smul_eq_mul, fourier_isoDeriv_iterate_apply, SchwartzMap.fourier_coe]
  have hg : ((SchwartzMap.gaussian hb : 𝓢(E, ℂ)) : E → ℂ) = fun x ↦ cexp (-b * ‖x‖ ^ 2) := by
    funext x; exact SchwartzMap.gaussian_apply hb x
  rw [hg, fourier_gaussian_innerProductSpace hb]
  ring

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem scalar_identities {τ σ : ℂ} (hτ0 : τ ≠ 0) (hστ : σ = -τ⁻¹) (ν : ℕ) :
    π / (-(π * I * σ)) = τ / I ∧
      (∀ t : ℝ, -π ^ 2 * (t : ℂ) / (-(π * I * σ)) = π * I * t * τ) ∧
      ((-2 * (-(π * I * σ))) ^ ν)⁻¹ * (2 * π * I) ^ ν = (-τ) ^ ν := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  subst hστ
  refine ⟨?_, fun t ↦ ?_, ?_⟩
  · field_simp
    try ring_nf
    try simp [I_sq]
  · field_simp
    try ring_nf
    try simp only [I_sq]
    try ring
  · rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
    try ring_nf
    try simp [I_sq]

/-- **Miyake, Lemma 4.9.1 (lattice form, every rank).** For `(ν, u, w)` spherical, `v : E` and
`τ ∈ ℍ`, with `n = finrank ℝ E`:
`θ_{v+L}(-1/τ; ⟪ζ, ·⟫^ν) = (covol L)⁻¹ (-τ)^ν (τ / i)^{n/2}
  ∑_{m ∈ L^∨} ⟪ζ, m⟫^ν e(⟪v, m⟫) exp (π i ‖m‖² τ)`. -/
@[kb "miyake1989" "Lemma 4.9.1: theta series with a spherical function under z -> -1/z (lattice form, every rank)"]
theorem thetaSph_S_smul {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) (v : E) (τ : ℍ) :
    thetaSph L ν u w v (ModularGroup.S • τ) = (ZLattice.covolume L : ℂ)⁻¹ *
      ((-(τ : ℂ)) ^ ν * ((τ : ℂ) / I) ^ ((finrank ℝ E : ℂ) / 2)) *
      ∑' m : ZLattice.dual L, isoForm u w m ^ ν * cexp (2 * π * I * ⟪v, (m : E)⟫) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) := by
  generalize hσ : ModularGroup.S • τ = σ
  have hστ : (σ : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [← hσ, UpperHalfPlane.modular_S_smul]
    simp [inv_neg]
  have hb : 0 < (-(π * I * (σ : ℂ))).re := by simpa using mul_pos Real.pi_pos σ.im_pos
  obtain ⟨hpb, hexp, hcoef⟩ := scalar_identities τ.ne_zero hστ ν
  have hf (x : E) : sphGauss ν u w hb x =
      isoForm u w x ^ ν * cexp (π * I * (‖x‖ ^ 2 : ℝ) * σ) := by
    rw [sphGauss_apply hsph hb]
    congr 2
    push_cast
    ring
  have hF (m : E) : 𝓕 (sphGauss ν u w hb : E → ℂ) m =
      ((-(τ : ℂ)) ^ ν * ((τ : ℂ) / I) ^ ((finrank ℝ E : ℂ) / 2)) *
        (isoForm u w m ^ ν * cexp (π * I * (‖m‖ ^ 2 : ℝ) * τ)) := by
    have he := hexp (‖m‖ ^ 2)
    push_cast at he
    rw [fourier_sphGauss_apply, hpb, he, mul_pow (2 * (π : ℂ) * I), ← hcoef]
    push_cast
    ring
  calc thetaSph L ν u w v σ = ∑' ℓ : L, sphGauss ν u w hb (v + ℓ) := by
        rw [thetaSph, thetaW_apply]
        exact tsum_congr fun ℓ ↦ (hf _).symm
    _ = (ZLattice.covolume L : ℂ)⁻¹ * ∑' m : ZLattice.dual L,
          𝓕 (sphGauss ν u w hb : E → ℂ) m * cexp (2 * π * I * ⟪v, (m : E)⟫) :=
        by
          have hP := SchwartzMap.tsum_eq_tsum_dual_fourier (sphGauss ν u w hb) L v
          exact hP
    _ = _ := by
        simp_rw [hF]
        rw [← tsum_mul_left, ← tsum_mul_left]
        exact tsum_congr fun m ↦ by ring

/-- **Lemma 4.9.1 in even rank `n = 2k`**: the factor is `(-i)^k τ^k (-τ)^ν`. -/
theorem thetaSph_S_smul_of_finrank_eq {k ν : ℕ} (hk : finrank ℝ E = 2 * k) {u w : E}
    (hsph : IsSphericalDatum ν u w) (v : E) (τ : ℍ) :
    thetaSph L ν u w v (ModularGroup.S • τ) = (ZLattice.covolume L : ℂ)⁻¹ *
      ((-(τ : ℂ)) ^ ν * ((-I) ^ k * (τ : ℂ) ^ k)) *
      ∑' m : ZLattice.dual L, isoForm u w m ^ ν * cexp (2 * π * I * ⟪v, (m : E)⟫) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) := by
  rw [thetaSph_S_smul L hsph v τ]
  congr 3
  rw [hk, show ((2 * k : ℕ) : ℂ) / 2 = (k : ℕ) by push_cast; ring, cpow_natCast, ← mul_pow, div_I]
  ring_nf

end ModularFormsKB.Miyake.Sec4_9
