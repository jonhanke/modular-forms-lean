import ModularFormsKB.Miyake.Sec4_9.Spherical.Inversion
import TauCeti.NumberTheory.ModularForms.ThetaSeries.GaussSum
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Character
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.PositiveOdd.Slash
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Theta series with a spherical weight under `Γ₀(N)` (Miyake, Theorem 4.9.3, even rank)

Miyake, *Modular Forms* (Springer 1989), Theorem 4.9.3, p. 191.

Let `L` be an even full lattice of rank `n = 2k` and level `N` in `E`, `γ ∈ L^∨`, and
`P = ⟪ζ, ·⟫^ν` a spherical weight. For `A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`, `N ∣ c`:

`θ_{γ+L}(·; P) ∣[k + ν] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) e(a b ‖γ‖² / 2) θ_{aγ+L}(·; P)`

(`thetaSph_slash_eq_gaussSum_smul`): the constant is the one of Tau Ceti's `P = 1` law
(`ZLattice.IsEven.thetaCoset_slash_eq_gaussSum_smul`), **independent of `P`**. The proof follows
Tau Ceti's coset splitting (`ZLattice.IsEven.thetaCoset_smul_eq_tsum_gaussSumTwisted`) with the
weight carried along: the inversion with a spherical weight (`thetaSph_S_smul_of_finrank_eq`)
contributes the extra factor `c^ν (-σ)^ν = (-(cτ + d))^ν`, and the collapse onto the classes
`m ∈ -aγ + L` gives `θ_{-aγ+L}(·; P) = (-1)^ν θ_{aγ+L}(·; P)`.

With Tau Ceti's evaluation of the Gauss sum this gives the law with the quadratic character
(`thetaSph_slash_of_mem_Gamma0`): for `A ∈ Γ₀(N)`,
`θ_L(·; P) ∣[k + ν] A = χ_L(d) θ_L(·; P)`, `χ_L` Tau Ceti's `thetaCharacter` (the character
`((-1)^k det / d)` of Miyake's theorem).
-/

open Complex Module
open UpperHalfPlane (coe_vadd)
open scoped Pointwise Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups

namespace ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Translation, splitting into classes, scaling -/

/-- If `(‖γ + v‖² - ‖γ‖²) t` is an even integer for every `v ∈ L`, translation by `t` multiplies
the weighted theta series of `γ + L` by `exp (π i ‖γ‖² t)`. -/
theorem thetaW_vadd_eq_mul (L : Submodule ℤ E) (p : E → ℂ) (γ : E) {t : ℝ}
    (h : ∀ v ∈ L, ∃ m : ℤ, (‖γ + v‖ ^ 2 - ‖γ‖ ^ 2) * t = 2 * m) (τ : ℍ) :
    thetaW L p γ (t +ᵥ τ) = cexp (π * I * (‖γ‖ ^ 2 : ℝ) * t) * thetaW L p γ τ := by
  rw [thetaW_apply, thetaW_apply, ← tsum_mul_left]
  refine tsum_congr fun v ↦ ?_
  obtain ⟨m, hm⟩ := h v v.2
  have ht : cexp (π * I * (‖γ + (v : E)‖ ^ 2 : ℝ) * t) = cexp (π * I * (‖γ‖ ^ 2 : ℝ) * t) := by
    simpa only [mul_assoc] using Complex.exp_pi_mul_I_mul_eq_of_sub_eq
      (a := ((‖γ + (v : E)‖ ^ 2 : ℝ) : ℂ) * t) (b := ((‖γ‖ ^ 2 : ℝ) : ℂ) * t)
      (by rw [← sub_mul]; exact_mod_cast hm)
  rw [coe_vadd, mul_add, exp_add, ht]
  ring

/-- The fibre sums of a weighted theta series over `L → L / M`. -/
theorem tsum_thetaWTerm_fiber (L : Submodule ℤ E) (p : E → ℂ) {M : Submodule ℤ E} (hML : M ≤ L)
    (γ : E) (y : L ⧸ M.submoduleOf L) (τ : ℍ) :
    ∑' b : (Submodule.Quotient.mk ⁻¹' {y} : Set L),
      p (γ + ((b : L) : E)) * cexp (π * I * (‖γ + ((b : L) : E)‖ ^ 2 : ℝ) * τ) =
        thetaW M p (γ + (Quotient.out y : L)) τ := by
  let f := (M.submoduleOf L).mkQ.toAddMonoidHom
  have hker (x : L) : x ∈ M.submoduleOf L ↔ x ∈ f.ker := by simp [f]
  have hset : f ⁻¹' {f (Quotient.out y)} = Submodule.Quotient.mk ⁻¹' {y} := by ext; simp [f]
  let e : M ≃ (Submodule.Quotient.mk ⁻¹' {y} : Set L) :=
    ((Submodule.submoduleOfEquivOfLe hML).toEquiv.symm.trans (Equiv.subtypeEquivRight hker)).trans
      ((f.fiberEquivKer (Quotient.out y)).symm.trans (Set.equivOfEq hset))
  have he (v : M) : ((e v : L) : E) = ((Quotient.out y : L) : E) + v := by
    have hv : (((Submodule.submoduleOfEquivOfLe hML).symm v : L) : E) = v := rfl
    simp [e, AddMonoidHom.fiberEquivKer_symm_apply, hv]
  rw [thetaW_apply, ← e.tsum_eq]
  exact tsum_congr fun v => by rw [he, add_assoc]

variable [FiniteDimensional ℝ E]

theorem hasSum_thetaW_add_out (L : Submodule ℤ E) [DiscreteTopology L] {p : E → ℂ}
    (hp : PolyBounded p) {M : Submodule ℤ E} (hML : M ≤ L) (γ : E) (τ : ℍ) :
    HasSum (fun y : L ⧸ M.submoduleOf L => thetaW M p (γ + ((Quotient.out y : L) : E)) τ)
      (thetaW L p γ τ) := by
  rw [← funext (fun y ↦ tsum_thetaWTerm_fiber L p hML γ y τ), thetaW_apply]
  exact (summable_thetaW L hp γ τ).hasSum.tsum_fiberwise _

/-- Rescaling the lattice: `θ_{cγ + cL}(τ; P) = c^ν θ_{γ+L}(c² τ; P)`. -/
theorem thetaSph_smul (L : Submodule ℤ E) (ν : ℕ) (u w : E) {c : ℝ} (hc : c ≠ 0) (γ : E)
    (τ : ℍ) : thetaSph (c • L) ν u w (c • γ) τ =
      (c : ℂ) ^ ν * thetaSph L ν u w γ ((⟨c ^ 2, sq_pos_of_ne_zero hc⟩ : {r : ℝ // 0 < r}) • τ) := by
  let e := Submodule.equivMapOfInjective (DistribSMul.toLinearMap ℤ E c)
    (smul_right_injective E hc) L
  rw [Submodule.pointwise_smul_def, thetaSph, thetaSph, thetaW_apply, thetaW_apply,
    ← e.toEquiv.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun v ↦ ?_
  have he : (e v : E) = c • (v : E) :=
    Submodule.coe_equivMapOfInjective_apply _ _ _ v
  simp only [LinearEquiv.coe_toEquiv, he]
  simp only [← smul_add, norm_smul, mul_pow, isoForm_smul,
    Real.norm_eq_abs, sq_abs, UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]
  push_cast
  ring_nf

namespace IsEvenSph

variable [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L]
  [IsZLattice ℝ L] {k : ℕ} (hL : ZLattice.IsEven L)
include hL

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
/-- The analogue of Tau Ceti's `thetaCoset_vadd_eq_sum`: at `a / c + τ` the weighted theta series
of `γ + L` splits over the classes of `L / cL`. -/
theorem thetaSph_vadd_eq_sum (ν : ℕ) (u w : E) (a : ℤ) (c : ℕ) [NeZero c]
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (γ : ZLattice.dual L) (τ : ℍ) :
    thetaSph L ν u w γ (((a : ℝ) / c) +ᵥ τ) = ∑ y : L ⧸ ((c : ℝ) • L).submoduleOf L,
      cexp (2 * π * I * ((a * ‖(γ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
        ZLattice.gaussTerm L hL a c (a • γ) y *
        thetaSph ((c : ℝ) • L) ν u w ((γ : E) + (Quotient.out y : L)) τ := by
  simp only [thetaSph]
  rw [← (hasSum_thetaW_add_out L (polyBounded_isoForm_pow u w ν)
    (ZLattice.natCast_smul_le L c) _ _).tsum_eq, tsum_fintype]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have hc : (c : ℝ) ≠ 0 := NeZero.ne _
  rw [thetaW_vadd_eq_mul _ _ _ (fun w hw ↦ ?_)]
  · congr 1
    conv_rhs => rw [← Submodule.Quotient.mk_out y]
    rw [ZLattice.gaussTerm_mk, ← exp_add]
    congr 1
    simp only [SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, norm_add_sq_real,
      real_inner_comm (γ : E)]
    push_cast
    field_simp
    ring
  · obtain ⟨u, hu, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hw
    obtain ⟨i, hi⟩ := ZLattice.isIntegral_iff.mp hL.isIntegral _ (Quotient.out y).2 _ hu
    obtain ⟨i', hi'⟩ := ZLattice.mem_dual.mp γ.2 _ hu
    obtain ⟨j, hj⟩ := ZLattice.isEven_iff.mp hL _ hu
    refine ⟨a * i' + a * i + a * c * j, ?_⟩
    rw [norm_add_sq_real, norm_smul, inner_smul_right, inner_add_left, hi, hi', mul_pow, hj,
      Real.norm_natCast]
    push_cast
    field_simp
    ring

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] [FiniteDimensional ℝ E]
  [DiscreteTopology L] in
/-- Termwise in the coset splitting, the twisted Gauss sum collects the Gauss factors of the
classes (a copy of Tau Ceti's private `term_eq_sum_gaussTerm`). -/
theorem term_eq_sum_gaussTerm₀ (A : SL(2, ℤ)) {c : ℕ}
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (γ : ZLattice.dual L) (τ σ : ℍ)
    (hσ : σ = ((A 1 1 : ℝ) / c) +ᵥ τ) (m : ZLattice.dual L) :
    cexp (2 * π * I * (((A 0 0 * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
        ZLattice.gaussSumTwisted L hL (A 0 0) c (A 0 0 • γ + m) *
        cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
          cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) =
      ∑ y : L ⧸ ((c : ℝ) • L).submoduleOf L,
        cexp (2 * π * I * ((A 0 0 * ‖(γ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
          ZLattice.gaussTerm L hL (A 0 0) c (A 0 0 • γ) y *
          (cexp (2 * π * I * ⟪(c : ℝ)⁻¹ • ((γ : E) + (Quotient.out y : L)), (m : E)⟫) *
            cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ)) := by
  rw [ZLattice.gaussSumTwisted_def, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  generalize hv : Quotient.out y = v
  rw [← Submodule.Quotient.mk_out y, hv, ZLattice.gaussTerm_mk, ZLattice.gaussTerm_mk,
    Submodule.coe_add, inner_add_right, hσ, coe_vadd, inner_smul_left, inner_add_left, conj_trivial]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] [FiniteDimensional ℝ E]
  [DiscreteTopology L] in
/-- `term_eq_sum_gaussTerm₀` with the weight `q = P(m)` carried along. -/
theorem term_eq_sum_gaussTerm (A : SL(2, ℤ)) {c : ℕ}
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (γ : ZLattice.dual L) (τ σ : ℍ)
    (hσ : σ = ((A 1 1 : ℝ) / c) +ᵥ τ) (m : ZLattice.dual L) (q : ℂ) :
    cexp (2 * π * I * (((A 0 0 * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
        ZLattice.gaussSumTwisted L hL (A 0 0) c (A 0 0 • γ + m) *
        cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
          (q * cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)) =
      ∑ y : L ⧸ ((c : ℝ) • L).submoduleOf L,
        cexp (2 * π * I * ((A 0 0 * ‖(γ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
          ZLattice.gaussTerm L hL (A 0 0) c (A 0 0 • γ) y *
          (q * cexp (2 * π * I * ⟪(c : ℝ)⁻¹ • ((γ : E) + (Quotient.out y : L)), (m : E)⟫) *
            cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ)) := by
  have h := congrArg (q * ·) (term_eq_sum_gaussTerm₀ hL A γ τ σ hσ m)
  simp only [Finset.mul_sum] at h
  convert h using 1
  · ring
  · exact Finset.sum_congr rfl fun y _ ↦ by ring

/-- **The coset splitting with a spherical weight.** For `A = !![a, b; c, d] ∈ SL(2, ℤ)` with
`c > 0` and `γ ∈ L^∨`:
`θ_{γ+L}(A τ; P) = (covol L)⁻¹ ((c τ + d) / (i c))^k (-(c τ + d))^ν
  ∑_{m ∈ L^∨} e((a ‖γ‖² / 2 + ⟪γ, m⟫) / c) G_L(a, c; aγ + m) e(d ‖m‖² / (2c)) P(m) q_m(τ)`. -/
theorem thetaSph_smul_eq_tsum_gaussSumTwisted (hk : finrank ℝ E = 2 * k) {ν : ℕ} {u w : E}
    (hsph : IsSphericalDatum ν u w) (A : SL(2, ℤ))
    {c : ℕ} [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c)
    (γ : ZLattice.dual L) (τ : ℍ) :
    thetaSph L ν u w γ (A • τ) = (ZLattice.covolume L : ℂ)⁻¹ * ((c * τ + A 1 1) / (I * c)) ^ k *
      (-(c * τ + A 1 1)) ^ ν *
      ∑' m : ZLattice.dual L,
        cexp (2 * π * I * (((A 0 0 * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
          ZLattice.gaussSumTwisted L hL (A 0 0) c (A 0 0 • γ + m) *
          cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
            (isoForm u w m ^ ν * cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)) := by
  have hc0 : c ≠ 0 := NeZero.ne c
  have hcR : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  set σ : ℍ := ((A 1 1 : ℝ) / c) +ᵥ τ with hσ
  set τ' : ℍ := (⟨((c : ℝ) ^ 2)⁻¹, inv_pos.mpr (sq_pos_of_ne_zero hcR)⟩ : {r : ℝ // 0 < r}) •
    (ModularGroup.S • σ) with hτ'
  have hAτ : A • τ = ((A 0 0 : ℝ) / c) +ᵥ τ' := by
    have hA := congrArg UpperHalfPlane.coe
      (ModularGroup.sq_smul_smul_eq_vadd_S_smul_vadd A (by rw [hc]; exact_mod_cast hc0) τ)
    simp only [hc, Int.cast_natCast, UpperHalfPlane.coe_pos_real_smul, coe_vadd,
      Complex.real_smul] at hA
    rw [UpperHalfPlane.ext_iff, coe_vadd, hτ', UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]
    push_cast at hA ⊢
    field_simp
    linear_combination hA
  have hclass (v : E) : thetaSph ((c : ℝ) • L) ν u w v τ' =
      (c : ℂ) ^ ν * thetaSph L ν u w ((c : ℝ)⁻¹ • v) (ModularGroup.S • σ) := by
    conv_lhs => rw [← smul_inv_smul₀ hcR v]
    rw [thetaSph_smul L ν u w hcR]
    congr 2
    rw [UpperHalfPlane.ext_iff, UpperHalfPlane.coe_pos_real_smul, hτ',
      UpperHalfPlane.coe_pos_real_smul, smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 hcR), one_smul]
  have hsum (v : E) : Summable fun m : ZLattice.dual L =>
      isoForm u w m ^ ν * cexp (2 * π * I * ⟪v, (m : E)⟫) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ) := by
    refine (summable_norm_thetaW (ZLattice.dual L) (polyBounded_isoForm_pow u w ν) 0 σ).of_norm_bounded
      fun m => ?_
    rw [norm_mul, norm_mul, norm_exp_two_pi_mul_I_mul_ofReal, mul_one, zero_add, norm_mul]
  have hfac : (c : ℂ) ^ ν * ((-(σ : ℂ)) ^ ν * ((-I) ^ k * (σ : ℂ) ^ k)) =
      ((c * τ + A 1 1) / (I * c)) ^ k * (-(c * τ + A 1 1)) ^ ν := by
    have h1 : (-I) ^ k * (σ : ℂ) ^ k = ((c * τ + A 1 1) / (I * c)) ^ k := by
      rw [← mul_pow, hσ, coe_vadd]
      congr 1
      field_simp
      push_cast
      rw [I_sq]
      field_simp
      ring
    have h2 : (c : ℂ) ^ ν * (-(σ : ℂ)) ^ ν = (-(c * τ + A 1 1)) ^ ν := by
      rw [← mul_pow, hσ, coe_vadd]
      congr 1
      push_cast
      field_simp
      ring
    rw [h1, ← h2]
    ring
  have hterm := term_eq_sum_gaussTerm hL A γ τ σ hσ
  rw [hAτ, thetaSph_vadd_eq_sum hL]
  simp_rw [hclass, thetaSph_S_smul_of_finrank_eq L hk hsph, hterm,
    Summable.tsum_finsetSum fun _ _ => (hsum _).mul_left _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr (by first | rfl | congr | (congr; exact Subsingleton.elim _ _)) fun y _ => ?_
  simp only [← tsum_mul_left]
  refine tsum_congr fun m ↦ ?_
  linear_combination (ZLattice.covolume L : ℂ)⁻¹ *
    cexp (2 * π * I * ((A 0 0 * ‖(γ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
    ZLattice.gaussTerm L hL (A 0 0) c (A 0 0 • γ) y *
    (isoForm u w m ^ ν * cexp (2 * π * I * ⟪(c : ℝ)⁻¹ • ((γ : E) + (Quotient.out y : L)), (m : E)⟫) *
      cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ)) * hfac

omit [MeasurableSpace E] [BorelSpace E] in
/-- When the level divides `c`, the dual sum collapses onto the classes `m ∈ -aγ + L`. -/
theorem tsum_gaussSumTwisted_coset_eq_sph (ν : ℕ) (u w : E) (A : SL(2, ℤ)) {c : ℕ} [NeZero c]
    [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c) (hN : ZLattice.level L ∣ c)
    (γ : ZLattice.dual L) (τ : ℍ) :
    ∑' m : ZLattice.dual L,
      cexp (2 * π * I * (((A 0 0 * ‖(γ : E)‖ ^ 2 / 2 + ⟪(γ : E), (m : E)⟫) / c : ℝ) : ℂ)) *
          ZLattice.gaussSumTwisted L hL (A 0 0) c (A 0 0 • γ + m) *
          cexp (2 * π * I * ((A 1 1 * ‖(m : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ)) *
            (isoForm u w m ^ ν * cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)) =
      ZLattice.gaussSum L hL (A 0 0) c *
        cexp (2 * π * I * ((A 0 0 * A 0 1 * ‖(γ : E)‖ ^ 2 / 2 : ℝ) : ℂ)) *
        thetaSph L ν u w (-(A 0 0 • (γ : E))) τ := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have hdet : A 0 0 * A 1 1 - A 0 1 * c = 1 := by
    have h := A.det_coe
    rwa [Matrix.det_fin_two, hc] at h
  have had : A 0 0 * A 1 1 ≡ 1 [ZMOD c] :=
    Int.modEq_iff_dvd.mpr ⟨-A 0 1, by linear_combination -hdet⟩
  have hLd : L ≤ ZLattice.dual L := ZLattice.isIntegral_iff_le_dual.mp hL.isIntegral
  let f : L → ZLattice.dual L := fun ℓ => Submodule.inclusion hLd ℓ - A 0 0 • γ
  have hf : Function.Injective f := fun ℓ₁ ℓ₂ h =>
    Submodule.inclusion_injective hLd (sub_left_injective h)
  rw [← hf.tsum_eq, thetaSph, thetaW_apply, ← tsum_mul_left]
  · refine tsum_congr fun ℓ => ?_
    have hfℓ : A 0 0 • γ + f ℓ = Submodule.inclusion hLd ℓ := add_sub_cancel _ _
    have hfℓE : ((f ℓ : ZLattice.dual L) : E) = -(A 0 0 • (γ : E)) + ℓ := by
      simp [f, neg_add_eq_sub]
    obtain ⟨i, hi⟩ := ZLattice.mem_dual.mp γ.2 _ ℓ.2
    obtain ⟨j, hj⟩ := ZLattice.isEven_iff.mp hL _ ℓ.2
    rw [hfℓ, ZLattice.gaussSumTwisted_eq_of_mem hL had ℓ.2, hfℓE]
    simp only [Submodule.coe_inclusion]
    have h1 : cexp (2 * π * I * ((((A 0 0 : ℝ) * ‖(γ : E)‖ ^ 2 / 2 +
          ⟪(γ : E), -(A 0 0 • (γ : E)) + ℓ⟫) / c : ℝ) : ℂ)) *
        cexp (-(2 * π * I * ((A 0 0 * A 1 1 ^ 2 * ‖(ℓ : E)‖ ^ 2 / (2 * c) : ℝ) : ℂ))) *
        cexp (2 * π * I * ((A 1 1 * ‖-(A 0 0 • (γ : E)) + ℓ‖ ^ 2 / (2 * c) : ℝ) : ℂ)) =
        cexp (2 * π * I * ((A 0 0 * A 0 1 * ‖(γ : E)‖ ^ 2 / 2 : ℝ) : ℂ)) := by
      rw [← exp_add, ← exp_add, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-(A 0 1 * i + A 0 1 * A 1 1 * j), ?_⟩
      simp only [← Int.cast_smul_eq_zsmul ℝ, inner_add_right, inner_neg_right,
        inner_smul_right, real_inner_self_eq_norm_sq, norm_add_sq_real, norm_neg, norm_smul,
        inner_neg_left, inner_smul_left, conj_trivial, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hi, hj]
      push_cast
      linear_combination (norm := (field_simp; ring))
        (π * I * (A 0 0 * ‖(γ : E)‖ ^ 2 - 2 * i - 2 * A 1 1 * j) / c) *
          (by exact_mod_cast hdet : (A 0 0 : ℂ) * A 1 1 - A 0 1 * c = 1)
    linear_combination (ZLattice.gaussSum L hL (A 0 0) c *
      (isoForm u w (-(A 0 0 • (γ : E)) + ℓ) ^ ν *
      cexp (π * I * (‖-(A 0 0 • (γ : E)) + ℓ‖ ^ 2 : ℝ) * τ))) * h1
  · intro m hm
    by_contra h
    apply Function.mem_support.mp hm
    rw [ZLattice.gaussSumTwisted_eq_zero hL _ hN fun hmL => h ⟨⟨_, hmL⟩, ?_⟩, mul_zero, zero_mul,
      zero_mul]
    ext
    simp [f]

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] [FiniteDimensional ℝ E]
  [DiscreteTopology L] hL in
/-- The scalar bookkeeping of the slash law. -/
theorem slash_scalar_aux {k ν : ℕ} {D c : ℂ} (hD : D ≠ 0) (hc : c ≠ 0) (V G e θ : ℂ) :
    V * (D / (I * c)) ^ k * (-D) ^ ν * (G * e * ((-1) ^ ν * θ)) * (D ^ (k + ν))⁻¹ =
      (-I) ^ k * (c ^ k)⁻¹ * V * G * e * θ := by
  have hI : (-I) ^ k * I ^ k = 1 := by rw [← mul_pow, neg_mul, I_mul_I, neg_neg, one_pow]
  have h1 : ((-1 : ℂ)) ^ ν * (-1) ^ ν = 1 := by rw [← mul_pow]; norm_num
  have h2 : (I ^ k)⁻¹ = (-I) ^ k := (eq_inv_of_mul_eq_one_left hI).symm
  have h3 : D ^ k * (D ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hD)
  have h4 : D ^ ν * (D ^ ν)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hD)
  calc _ = V * (I ^ k)⁻¹ * (c ^ k)⁻¹ * G * e * θ * ((-1) ^ ν * (-1) ^ ν) *
        (D ^ k * (D ^ k)⁻¹) * (D ^ ν * (D ^ ν)⁻¹) := by
        rw [div_pow, mul_pow, neg_pow D, pow_add, mul_inv]
        ring
    _ = _ := by rw [h1, h3, h4, h2]; ring

/-- **Miyake, Theorem 4.9.3 (lattice form, even rank, Gauss sum unevaluated).** For an even full
lattice `L` of rank `2k` and level `N`, `γ ∈ L^∨`, a spherical weight `P` of degree `ν`, and
`A = !![a, b; c, d] ∈ SL(2, ℤ)` with `c > 0`, `N ∣ c`:
`θ_{γ+L}(·; P) ∣[k + ν] A = (-i)^k c^{-k} (covol L)⁻¹ G_L(a, c) e(a b ‖γ‖² / 2) θ_{aγ+L}(·; P)`. -/
theorem thetaSph_slash_eq_gaussSum_smul (hk : finrank ℝ E = 2 * k) {ν : ℕ} {u w : E}
    (hsph : IsSphericalDatum ν u w) (A : SL(2, ℤ)) {c : ℕ}
    [NeZero c] [Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L)] (hc : A 1 0 = c)
    (hN : ZLattice.level L ∣ c) (γ : ZLattice.dual L) :
    thetaSph L ν u w γ ∣[((k + ν : ℕ) : ℤ)] A =
      ((-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (ZLattice.covolume L : ℂ)⁻¹ *
        ZLattice.gaussSum L hL (A 0 0) c *
        cexp (2 * π * I * ((A 0 0 * A 0 1 * ‖(γ : E)‖ ^ 2 / 2 : ℝ) : ℂ))) •
        thetaSph L ν u w (A 0 0 • (γ : E)) := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  ext τ
  have hden : (c : ℂ) * τ + A 1 1 ≠ 0 := by
    simpa [ModularGroup.denom_apply, hc] using UpperHalfPlane.denom_ne_zero A τ
  rw [ModularForm.SL_slash_apply, thetaSph_smul_eq_tsum_gaussSumTwisted hL hk hsph A hc,
    tsum_gaussSumTwisted_coset_eq_sph hL ν u w A hc hN, thetaSph_neg,
    ModularGroup.denom_apply, hc, Pi.smul_apply, smul_eq_mul, zpow_neg, zpow_natCast]
  push_cast
  exact slash_scalar_aux hden hc' _ _ _ _

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] [FiniteDimensional ℝ E] [DiscreteTopology L] in
theorem thetaSph_intCast_vadd (ν : ℕ) (u w : E) (n : ℤ) (τ : ℍ) :
    thetaSph L ν u w 0 ((n : ℝ) +ᵥ τ) = thetaSph L ν u w 0 τ := by
  rw [thetaSph, thetaW_vadd_eq_mul L _ 0 (fun v hv ↦ ?_) τ]
  · simp [thetaSph]
  · obtain ⟨m, hm⟩ := ZLattice.isEven_iff.mp hL v hv
    exact ⟨m * n, by rw [zero_add, hm, norm_zero]; push_cast; ring⟩

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- The spherical theta series of an even lattice is invariant under `T` in every weight. -/
theorem thetaSph_slash_T (ν : ℕ) (u w : E) (j : ℤ) :
    thetaSph L ν u w 0 ∣[j] ModularGroup.T = thetaSph L ν u w 0 := by
  ext τ
  have := TauCeti.ModularForm.slash_T_zpow_apply j 1 (thetaSph L ν u w 0) τ
  simp only [zpow_one] at this
  rw [this, Int.cast_one]
  exact_mod_cast thetaSph_intCast_vadd hL ν u w 1 τ

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- For odd `ν` the spherical theta series of the lattice itself vanishes (`P(-x) = -P(x)`). -/
theorem thetaSph_zero_of_odd {ν : ℕ} (hν : Odd ν) (u w : E) (τ : ℍ) : thetaSph L ν u w 0 τ = 0 := by
  have h := thetaSph_neg L ν u w 0 τ
  rw [neg_zero, hν.neg_one_pow] at h
  linear_combination h / 2

/-- **Miyake, Theorem 4.9.3 with Corollary 4.9.4 (lattice form, even rank).** For an even full
lattice `L` of rank `2k` and level `N`, a spherical weight `P` of degree `ν` and `A ∈ Γ₀(N)`,
`θ_L(·; P) ∣[k + ν] A = χ_L(d) θ_L(·; P)`, `χ_L` the quadratic theta character of `L`. -/
@[kb "miyake1989" "Theorem 4.9.3 / Corollary 4.9.4: theta series with spherical function on Gamma0(N) with the quadratic character (lattice form, even rank)"]
theorem thetaSph_slash_of_mem_Gamma0 (hk : finrank ℝ E = 2 * k) {ν : ℕ} {u w : E}
    (hsph : IsSphericalDatum ν u w) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 (ZLattice.level L)) :
    thetaSph L ν u w 0 ∣[((k + ν : ℕ) : ℤ)] A =
      hL.thetaCharacter ⟨k, by omega⟩ (A 1 1 : ℤ) • thetaSph L ν u w 0 := by
  rcases Nat.even_or_odd ν with hν | hν
  · apply TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd
      (by
        rw [hL.thetaCharacter_neg_one ⟨k, by omega⟩ hk]
        push_cast
        rw [zpow_add₀ (by norm_num), zpow_natCast, zpow_natCast, hν.neg_one_pow, mul_one])
      (thetaSph_slash_T hL ν u w _) ?_ hA
    intro B hB hc ha hao
    obtain ⟨a, haeq⟩ := Int.eq_ofNat_of_zero_le ha.le
    obtain ⟨c, hceq⟩ := Int.eq_ofNat_of_zero_le hc.le
    have haodd : Odd a := by rw [haeq] at hao; exact_mod_cast hao
    have hN : ZLattice.level L ∣ c := by
      have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hB
      rw [hceq] at h
      exact_mod_cast h
    have hc0 : c ≠ 0 := by rintro rfl; simp at hceq; omega
    have : NeZero c := ⟨hc0⟩
    have hac : IsCoprime (a : ℤ) c := by
      simpa only [haeq, hceq] using B.isCoprime_col 0
    have hB0 : B ∈ CongruenceSubgroup.Gamma0 (ZLattice.level L) := hB
    have hunit := CongruenceSubgroup.isUnit_intCast_apply_zero_zero_of_mem_Gamma0 hB0
    have haN : IsCoprime (a : ℤ) (ZLattice.level L) := by
      rw [← haeq]
      exact isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime _ _).mp hunit)
    have hchar : hL.thetaCharacter ⟨k, by omega⟩ (a : ℤ) =
        hL.thetaCharacter ⟨k, by omega⟩ (B 1 1 : ℤ) := by
      rw [← haeq]
      exact ((hL.thetaCharacter_isQuadratic _).apply_one_one_eq_apply_zero_zero_of_mem_Gamma0
        hB0).symm
    have h := thetaSph_slash_eq_gaussSum_smul hL hk hsph B hceq hN 0
    rw [Submodule.coe_zero, smul_zero] at h
    have he : cexp (2 * π * I * ((B 0 0 * B 0 1 * ‖(0 : E)‖ ^ 2 / 2 : ℝ) : ℂ)) = 1 := by simp
    have hs : (-I) ^ k * ((c : ℂ) ^ k)⁻¹ * (ZLattice.covolume L : ℂ)⁻¹ *
        ZLattice.gaussSum L hL (B 0 0) c = hL.thetaCharacter ⟨k, by omega⟩ (B 1 1 : ℤ) := by
      rw [← hchar, hL.thetaCharacter_intCast ⟨k, by omega⟩ haN, TauCeti.kroneckerSym_eq_jacobiSym _ haodd,
        ZLattice.signedDiscr_of_finrank_eq L hk, haeq]
      exact_mod_cast hL.normalized_gaussSum_eq_jacobiSym hk haodd hN hac.natCoprime
    rw [h, he, mul_one, hs]
  · have h0 : thetaSph L ν u w 0 = 0 := funext (thetaSph_zero_of_odd hL hν u w)
    rw [h0, smul_zero]
    exact SlashAction.zero_slash _ _

end IsEvenSph

end ModularFormsKB.Miyake.Sec4_9
