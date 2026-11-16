import ModularFormsKB.Miyake.Sec4_9.Spherical.UnaryCusp
import ModularFormsKB.HalfIntegral.TotallyEven
import ModularFormsKB.Miyake.Sec4_3.Gauss

/-!
# The Serre–Stark cusp criterion in weight 1/2: the other direction

Loose end LE-MF-0239.

**Theorem** (`unaryThetaOf_not_mem_cusp_of_totallyEven`). For `(Φ, t) ∈ Ω₀(4N, χ)` with `ψ = Φ*` totally even,
`θ_{ψ,t}` is not a cusp form. With `unaryThetaOf_mem_cusp_of_not_totallyEven` this proves `UnaryThetaCuspCriterion`
(`unaryThetaCuspCriterion`) and `UnaryThetaModular 0 N χ` (`unaryThetaModular_zero`) with no input
(LE-MF-0239 closed).

**Proof.** Only the cusps `A_n = S Tⁿ S` (the cusps `-1/n`) are used.
1. For any even lattice and `Θ = ∑_i c_i θ_{x_i}`, applying the inversion law, the translation law and the inversion
   law again gives `Θ(A_n τ) = κ(σ) κ(τ) ∑_y K_n(y) θ_y(τ)`, `σ = n - 1/τ`, with `|κ(σ) κ(τ)| = (covol L)⁻² |nτ - 1|^{1/2}`
   (`thetaSph_STS`). If `Θ` vanishes at the cusp `A_n` then the coefficient of `θ_0`,
   `K_n = ∑_i c_i ∑_z e(b(x_i, z)) e(n q(z))`, is `0` (`sum_coeff_eq_zero_of_isZeroAtImInfty`).
2. For `L = √(2t) r ℤ`, the classes are `z_j = j/(√(2t) r)`, `j mod 2tr²`, and `c_b = ψ(b)`, `x_b = √(2t) b`:
   the inner sum over `b` is the Gauss sum `∑_b ψ(b) e(bj/r) = ψ̄(j) τ(ψ)` (ψ primitive), and `e(n q(z_j)) = e(nj²/4tr²)`.
3. Summing `K_n e(-n/4tr²)` over `n mod 4tr²` leaves `4tr² τ(ψ) ∑_{j² ≡ 1 mod 4tr²} ψ̄(j)`, and every such `j` has
   `ψ(j) = 1` because `ψ` is totally even (`psi_eq_one_of_isTotallyEven`). So the sum is `4tr² τ(ψ)` times a positive
   count (`j = 1`), not `0`.
-/

open Complex Module Filter
open scoped Real RealInnerProductSpace UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] [MeasurableSpace E] [BorelSpace E]

/-- **The translation law by `n ∈ ℤ`**: `θ_{δ+L}(n + σ; P) = e(n‖δ‖²/2) θ_{δ+L}(σ; P)`. -/
theorem thetaSph_int_vadd (hL : ZLattice.IsEven L) (ν : ℕ) (u w : E) {δ : E}
    (hδ : δ ∈ ZLattice.dual L) (n : ℤ) (σ : ℍ) :
    thetaSph L ν u w δ ((n : ℝ) +ᵥ σ) = cexp (π * I * (‖δ‖ ^ 2 : ℝ) * n) * thetaSph L ν u w δ σ := by
  rw [thetaSph, thetaW_vadd_eq_mul L _ δ (fun v hv ↦ ?_) σ, ← thetaSph]
  · push_cast; ring_nf
  · obtain ⟨i, hi⟩ := ZLattice.mem_dual.mp hδ _ hv
    obtain ⟨j, hj⟩ := ZLattice.isEven_iff.mp hL _ hv
    refine ⟨(i + j) * n, ?_⟩
    rw [norm_add_sq_real, hi, hj]
    push_cast
    ring

/-- The factor of the inversion law, `κ(σ) = (covol L)⁻¹ (σ/i)^{n/2}` (`ν = 0`). -/
noncomputable def invFactor (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (σ : ℍ) : ℂ :=
  (ZLattice.covolume L : ℂ)⁻¹ * ((-(σ : ℂ)) ^ (0 : ℕ) * ((σ : ℂ) / I) ^ ((finrank ℝ E : ℂ) / 2))

theorem norm_invFactor (σ : ℍ) :
    ‖invFactor L σ‖ = (ZLattice.covolume L)⁻¹ * ‖(σ : ℂ)‖ ^ ((finrank ℝ E : ℝ) / 2) := by
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  rw [invFactor, pow_zero, one_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hcov,
    show ((finrank ℝ E : ℂ) / 2) = (((finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_real, norm_div, Complex.norm_I, div_one]

/-- The coefficient `K_n(x, y) = ∑_z e(b(x, z)) e(n q(z)) e(b(z, y))` of `θ_y` in `θ_x(S Tⁿ S τ)`. -/
noncomputable def stsCoeff (n : ℤ) (x y : ZLattice.DiscriminantGroup L) [Fintype (ZLattice.DiscriminantGroup L)] : ℂ :=
  ∑ z : ZLattice.DiscriminantGroup L, cexp (2 * π * I * ⟪discRep x, discRep z⟫) *
    cexp (π * I * (‖discRep z‖ ^ 2 : ℝ) * n) *
    cexp (2 * π * I * ⟪discRep z, discRep y⟫)

/-- **The coset theta series at the cusp `-1/n`** (`ν = 0`): `θ_x(S(n + Sτ)) = κ(n + Sτ) κ(τ) ∑_y K_n(x, y) θ_y(τ)`. -/
theorem thetaSph_STS (hL : ZLattice.IsEven L) [Fintype (ZLattice.DiscriminantGroup L)] (u w : E)
    (x : ZLattice.DiscriminantGroup L) (n : ℤ) (τ : ℍ) :
    thetaSph L 0 u w (discRep x) (ModularGroup.S • ((n : ℝ) +ᵥ (ModularGroup.S • τ))) =
      invFactor L ((n : ℝ) +ᵥ (ModularGroup.S • τ)) * invFactor L τ *
        ∑ y, stsCoeff n x y * thetaSph L 0 u w (discRep y) τ := by
  have hsph : IsSphericalDatum 0 u w := Or.inl (Nat.zero_le 1)
  rw [thetaSph_S_smul_sum hL.isIntegral hsph (discRep_mem_dual x)]
  simp_rw [thetaSph_int_vadd hL 0 u w (discRep_mem_dual _) n,
    thetaSph_S_smul_sum hL.isIntegral hsph (discRep_mem_dual _)]
  simp only [invFactor, stsCoeff, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  ring

/-- `S Tⁿ S` acts by `τ ↦ S(n + Sτ)` and has bottom row `(n, -1)`. -/
theorem STS_smul (n : ℤ) (τ : ℍ) :
    (ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S) • τ =
      ModularGroup.S • ((n : ℝ) +ᵥ (ModularGroup.S • τ)) := by
  rw [mul_smul, mul_smul, UpperHalfPlane.modular_T_zpow_smul]

theorem STS_bottom (n : ℤ) :
    ((ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S : SL(2, ℤ)) 1 0 = n) ∧
      ((ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S : SL(2, ℤ)) 1 1 = -1) := by
  constructor <;>
  simp [ModularGroup.coe_S, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

/-- `|κ(n + Sτ) κ(τ)| = (covol L)⁻² |nτ - 1|^{n/2}`. -/
theorem norm_invFactor_STS (n : ℤ) (τ : ℍ) :
    ‖invFactor L ((n : ℝ) +ᵥ (ModularGroup.S • τ)) * invFactor L τ‖ =
      (ZLattice.covolume L)⁻¹ * (ZLattice.covolume L)⁻¹ *
        ‖(n : ℂ) * τ + (-1 : ℤ)‖ ^ ((finrank ℝ E : ℝ) / 2) := by
  rw [norm_mul, norm_invFactor, norm_invFactor]
  have hσ : (((n : ℝ) +ᵥ (ModularGroup.S • τ) : ℍ) : ℂ) * τ = (n : ℂ) * τ + (-1 : ℤ) := by
    rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.modular_S_smul]
    simp only [UpperHalfPlane.coe_mk, ofReal_intCast]
    have := τ.ne_zero
    field_simp
    push_cast
    ring
  rw [← hσ, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  ring

theorem STS_den_ne_zero (n : ℤ) (τ : ℍ) : (n : ℂ) * τ + ((-1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, zero_mul, add_zero, Complex.zero_im] at him
  rcases mul_eq_zero.mp him with hn | hτ
  · have hn' : n = 0 := by exact_mod_cast hn
    subst hn'
    norm_num at h
  · exact τ.im_pos.ne' hτ

/-- The absolute slash at the cusp `-1/n`: `(covol L)⁻² |∑_y K_n(y) θ_y(τ)|`. -/
theorem absSlash_STS_eq (hL : ZLattice.IsEven L) [Fintype (ZLattice.DiscriminantGroup L)] (u w : E)
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (x : ι → ZLattice.DiscriminantGroup L) (n : ℤ) (τ : ℍ) :
    absSlash ((0 : ℕ) + finrank ℝ E / 2) (fun τ ↦ ∑ i, c i * thetaSph L 0 u w (discRep (x i)) τ)
      (ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S) τ =
      (ZLattice.covolume L)⁻¹ * (ZLattice.covolume L)⁻¹ *
        ‖∑ y, (∑ i, c i * stsCoeff n (x i) y) * thetaSph L 0 u w (discRep y) τ‖ := by
  have hden : 0 < ‖(n : ℂ) * τ + ((-1 : ℤ) : ℂ)‖ := norm_pos_iff.mpr (STS_den_ne_zero n τ)
  obtain ⟨h0, h1⟩ := STS_bottom n
  have hsum : (∑ i, c i * thetaSph L 0 u w (discRep (x i))
      ((ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S) • τ)) =
      invFactor L ((n : ℝ) +ᵥ (ModularGroup.S • τ)) * invFactor L τ *
        ∑ y, (∑ i, c i * stsCoeff n (x i) y) * thetaSph L 0 u w (discRep y) τ := by
    rw [STS_smul]
    simp only [thetaSph_STS hL u w _ n τ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  unfold absSlash
  beta_reduce
  rw [h0, h1, hsum, norm_mul, norm_invFactor_STS, Nat.cast_zero, zero_add, Real.rpow_neg hden.le]
  have hp : 0 < ‖(n : ℂ) * τ + ((-1 : ℤ) : ℂ)‖ ^ ((finrank ℝ E : ℝ) / 2) := Real.rpow_pos_of_pos hden _
  field_simp

/-- **Vanishing at the cusp `-1/n` kills the coefficient of `θ_0`** (`ν = 0`, every rank). -/
theorem sum_coeff_eq_zero_of_isZeroAtImInfty (hL : ZLattice.IsEven L)
    [Fintype (ZLattice.DiscriminantGroup L)] (u w : E) {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (x : ι → ZLattice.DiscriminantGroup L) (n : ℤ)
    (h : UpperHalfPlane.IsZeroAtImInfty (absSlash ((0 : ℕ) + finrank ℝ E / 2)
      (fun τ ↦ ∑ i, c i * thetaSph L 0 u w (discRep (x i)) τ)
      (ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S))) :
    ∑ i, c i * ∑ z : ZLattice.DiscriminantGroup L, cexp (2 * π * I * ⟪discRep (x i), discRep z⟫) *
      cexp (π * I * (‖discRep z‖ ^ 2 : ℝ) * n) = 0 := by
  classical
  obtain ⟨K, hK⟩ : ∃ K : ZLattice.DiscriminantGroup L → ℂ, K = fun y ↦ ∑ i, c i * stsCoeff n (x i) y :=
    ⟨_, rfl⟩
  have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
  have hrw : ∀ τ, absSlash ((0 : ℕ) + finrank ℝ E / 2)
      (fun τ ↦ ∑ i, c i * thetaSph L 0 u w (discRep (x i)) τ)
      (ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S) τ =
      (ZLattice.covolume L)⁻¹ * (ZLattice.covolume L)⁻¹ *
        ‖∑ y, K y * thetaSph L 0 u w (discRep y) τ‖ := fun τ ↦ by
    rw [absSlash_STS_eq hL u w c x n τ, hK]
  -- the sum tends to `K 0`
  have hlim : Tendsto (fun τ ↦ ∑ y, K y * thetaSph L 0 u w (discRep y) τ) UpperHalfPlane.atImInfty
      (nhds (K 0)) := by
    have hterm : ∀ y, Tendsto (fun τ ↦ K y * thetaSph L 0 u w (discRep y) τ) UpperHalfPlane.atImInfty
        (nhds (if y = 0 then K 0 else 0)) := by
      intro y
      by_cases hy : y = 0
      · subst hy
        have hmem : discRep (0 : ZLattice.DiscriminantGroup L) ∈ L := by
          have h := mk_discRep (0 : ZLattice.DiscriminantGroup L)
          rw [Submodule.Quotient.mk_eq_zero] at h
          exact h
        rw [thetaSph_zero, ZLattice.thetaCoset_of_mem L hmem, if_pos rfl]
        have h1 := (ZLattice.tendsto_thetaSeries_atImInfty L).const_mul (K 0)
        rwa [mul_one] at h1
      · have hy' : discRep y ∉ L := by
          intro hmem
          apply hy
          rw [← mk_discRep y]
          exact (Submodule.Quotient.mk_eq_zero _).mpr hmem
        have h2 : Tendsto (thetaSph L 0 u w (discRep y)) UpperHalfPlane.atImInfty (nhds 0) := by
          rw [thetaSph_zero]
          exact ZLattice.isZeroAtImInfty_thetaCoset L hy'
        rw [if_neg hy]
        have h3 := h2.const_mul (K y)
        rwa [mul_zero] at h3
    have := tendsto_finsetSum Finset.univ fun y _ ↦ hterm y
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    exact this
  -- and to `0`
  have hzero : Tendsto (fun τ ↦ ∑ y, K y * thetaSph L 0 u w (discRep y) τ) UpperHalfPlane.atImInfty
      (nhds 0) := by
    have hc : 0 < (ZLattice.covolume L)⁻¹ * (ZLattice.covolume L)⁻¹ := by positivity
    have h' : Tendsto (fun τ ↦ ‖∑ y, K y * thetaSph L 0 u w (discRep y) τ‖) UpperHalfPlane.atImInfty
        (nhds 0) := by
      have := (h : Tendsto _ _ _).const_mul ((ZLattice.covolume L)⁻¹ * (ZLattice.covolume L)⁻¹)⁻¹
      rw [mul_zero] at this
      refine this.congr fun τ ↦ ?_
      rw [hrw τ, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr h'
  have hK0 : K 0 = 0 := tendsto_nhds_unique hlim hzero
  have hmem : discRep (0 : ZLattice.DiscriminantGroup L) ∈ L := by
    have h := mk_discRep (0 : ZLattice.DiscriminantGroup L)
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact h
  have hone : ∀ z : ZLattice.DiscriminantGroup L,
      cexp (2 * π * I * ⟪discRep z, discRep (0 : ZLattice.DiscriminantGroup L)⟫) = 1 := by
    intro z
    obtain ⟨m, hm⟩ := ZLattice.mem_dual.mp (discRep_mem_dual z) _ hmem
    rw [hm, Complex.exp_eq_one_iff]
    exact ⟨m, by push_cast; ring⟩
  have hfin : ∀ i, (∑ z : ZLattice.DiscriminantGroup L, cexp (2 * π * I * ⟪discRep (x i), discRep z⟫) *
      cexp (π * I * (‖discRep z‖ ^ 2 : ℝ) * n)) = stsCoeff n (x i) 0 := by
    intro i
    unfold stsCoeff
    exact Finset.sum_congr rfl fun z _ ↦ by rw [hone z, mul_one]
  calc _ = ∑ i, c i * stsCoeff n (x i) 0 := Finset.sum_congr rfl fun i _ ↦ by rw [hfin i]
    _ = K 0 := by rw [hK]
    _ = 0 := hK0

end ModularFormsKB.Miyake.Sec4_9

namespace ModularFormsKB.HalfIntegral

open ModularFormsKB.Miyake.Sec4_9

/-! ### Rank one: the classes `j / (√(2t) r)` -/

section RankOne

variable {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r)

theorem div_twistGen_mem_dual (j : ℤ) : (j : ℝ) / twistGen t r ∈ ZLattice.dual (twistLattice ht hr) := by
  rw [mem_dual_rankOneLattice]
  exact ⟨j, by field_simp [twistGen_ne_zero ht hr]⟩

/-- The class of `j / (√(2t) r)`, `j mod 2tr²`. -/
noncomputable def dualClass (j : ZMod (2 * t * r ^ 2)) : ZLattice.DiscriminantGroup (twistLattice ht hr) :=
  Submodule.Quotient.mk ⟨(j.val : ℤ) / twistGen t r, div_twistGen_mem_dual ht hr j.val⟩

theorem dualClass_bijective : Function.Bijective (dualClass ht hr) := by
  have hx := twistGen_ne_zero ht hr
  have hsq := twistGen_sq t r
  have hG : NeZero (2 * t * r ^ 2) := ⟨mul_ne_zero (mul_ne_zero two_ne_zero (by omega)) (pow_ne_zero _ (by omega))⟩
  constructor
  · intro j j' h
    rw [dualClass, dualClass, Submodule.Quotient.eq] at h
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at h
    obtain ⟨m, hm⟩ := (mem_rankOneLattice _).mp h
    simp only [Submodule.coe_sub] at hm
    have h' : ((j.val : ℤ) - (j'.val : ℤ) : ℝ) = ((m * (2 * t * r ^ 2) : ℤ) : ℝ) := by
      have : ((j.val : ℤ) : ℝ) - (j'.val : ℤ) = m * twistGen t r * twistGen t r := by
        rw [hm]; field_simp
      rw [this, mul_assoc, ← sq, hsq]
      push_cast; ring
    have h'' : (j.val : ℤ) - (j'.val : ℤ) = m * (2 * t * r ^ 2) := by exact_mod_cast h'
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (j'.val : ℤ) (j.val : ℤ) (2 * t * r ^ 2)).mpr
      ⟨m, by rw [h'']; push_cast; ring⟩
    simpa using this.symm
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨m, hm⟩ := (mem_dual_rankOneLattice _).mp y.2
      refine ⟨(m : ZMod (2 * t * r ^ 2)), ?_⟩
      rw [dualClass, Submodule.Quotient.eq]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
      rw [mem_rankOneLattice]
      have hv : (((m : ZMod (2 * t * r ^ 2)).val : ℤ) : ZMod (2 * t * r ^ 2)) = (m : ZMod _) := by simp
      obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hv
      refine ⟨-k, ?_⟩
      simp only [Submodule.coe_sub]
      have hy : (y : ℝ) = m / twistGen t r := by rw [← hm]; field_simp
      rw [hy]
      have hk' : (((m : ZMod (2 * t * r ^ 2)).val : ℤ) : ℝ) = m - (2 * t * r ^ 2 : ℕ) * k := by
        have : (m : ℝ) - (((m : ZMod (2 * t * r ^ 2)).val : ℤ) : ℝ) = ((2 * t * r ^ 2 : ℕ) : ℝ) * k := by
          exact_mod_cast hk
        linarith
      rw [hk']
      field_simp
      push_cast
      rw [← hsq]
      ring

/-- The pairing of `√(2t) b` with `j / (√(2t) r)` is `e(bj/r)`. -/
theorem pairing_twistClass_dualClass (b : ZMod r) (j : ZMod (2 * t * r ^ 2)) [NeZero r] :
    cexp (2 * π * I * ⟪discRep (twistClass ht hr b), discRep (dualClass ht hr j)⟫) =
      ZMod.stdAddChar (b * (j.val : ZMod r)) := by
  rw [← discriminantPairingChar_discRep (isEven_twistLattice ht hr).isIntegral, twistClass, dualClass,
    ZLattice.IsIntegral.discriminantPairingChar_mk_mk]
  have hx := twistGen_ne_zero ht hr
  have hval : ((b.val * j.val : ℤ) : ZMod r) = b * (j.val : ZMod r) := by push_cast; simp
  rw [← hval, ZMod.stdAddChar_coe]
  congr 1
  simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
  unfold twistVec twistGen
  have hs : √(2 * (t : ℝ)) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hs' : ((√(2 * (t : ℝ)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp

/-- The quadratic phase of `j / (√(2t) r)`, to the power `n`, is `e(nj²/4tr²)`. -/
theorem quad_dualClass [NeZero (4 * t * r ^ 2)] (j : ZMod (2 * t * r ^ 2)) (n : ℤ) :
    cexp (π * I * (‖discRep (dualClass ht hr j)‖ ^ 2 : ℝ) * n) =
      (ZMod.stdAddChar (((j.val : ℤ) ^ 2 * n : ℤ) : ZMod (4 * t * r ^ 2)) : ℂ) := by
  have hq := discriminantQuadraticChar_discRep (isEven_twistLattice ht hr) (dualClass ht hr j)
  rw [dualClass, ZLattice.IsEven.discriminantQuadraticChar_mk] at hq
  rw [mul_comm _ (n : ℂ), Complex.exp_int_mul, ← dualClass] at *
  rw [← hq, ← Complex.exp_int_mul, ZMod.stdAddChar_coe]
  congr 1
  have hx := twistGen_ne_zero ht hr
  simp only [Real.norm_eq_abs, sq_abs, div_pow, twistGen_sq]
  have hG : (2 * (t : ℝ) * r ^ 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end RankOne

/-! ### The Gauss sums and the Fourier inversion -/

/-- **The constant terms at the cusps `-1/n`, in rank one**: for `ψ` primitive modulo `r`,
`∑_b ψ(b) ∑_z e(b(x_b, z)) e(n q(z)) = τ(ψ) ∑_{j mod 2tr²} ψ̄(j) e(nj²/4tr²)`. -/
theorem sum_coeff_twist {t r : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r) [NeZero r] [NeZero (2 * t * r ^ 2)]
    [NeZero (4 * t * r ^ 2)] {ψ : DirichletCharacter ℂ r}
    (hψ : ψ.IsPrimitive) (n : ℤ) :
    ∑ b : ZMod r, ψ b * ∑ z : ZLattice.DiscriminantGroup (twistLattice ht hr),
      cexp (2 * π * I * ⟪discRep (twistClass ht hr b), discRep z⟫) *
      cexp (π * I * (‖discRep z‖ ^ 2 : ℝ) * n) =
      gaussSum ψ ZMod.stdAddChar * ∑ j : ZMod (2 * t * r ^ 2), ψ⁻¹ (j.val : ZMod r) *
        (ZMod.stdAddChar (((j.val : ℤ) ^ 2 * n : ℤ) : ZMod (4 * t * r ^ 2)) : ℂ) := by
  have hb := dualClass_bijective ht hr
  have hz : ∀ b : ZMod r, (∑ z : ZLattice.DiscriminantGroup (twistLattice ht hr), cexp (2 * π * I * ⟪discRep (twistClass ht hr b), discRep z⟫) *
      cexp (π * I * (‖discRep z‖ ^ 2 : ℝ) * n)) = ∑ j : ZMod (2 * t * r ^ 2),
        ZMod.stdAddChar (b * (j.val : ZMod r)) *
          (ZMod.stdAddChar (((j.val : ℤ) ^ 2 * n : ℤ) : ZMod (4 * t * r ^ 2)) : ℂ) := by
    intro b
    rw [← hb.sum_comp]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [pairing_twistClass_dualClass, quad_dualClass]
  simp_rw [hz, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hg := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hψ (j.val : ZMod r)
  rw [← mul_assoc, mul_comm (gaussSum ψ ZMod.stdAddChar), ← hg, gaussSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [AddChar.mulShift_apply, mul_comm (j.val : ZMod r) b]
  ring

/-- **Fourier inversion against a totally even character**: the sums `∑_j ψ̄(j) e(nj²/4tr²)` do not all vanish. -/
theorem not_forall_sum_eq_zero {t r : ℕ} (ht : 1 ≤ t) [NeZero r] [NeZero (2 * t * r ^ 2)]
    [NeZero (4 * t * r ^ 2)] {ψ : DirichletCharacter ℂ r}
    (hψ : IsTotallyEven ψ) :
    ¬ ∀ n : ℤ, ∑ j : ZMod (2 * t * r ^ 2), ψ⁻¹ (j.val : ZMod r) *
        (ZMod.stdAddChar (((j.val : ℤ) ^ 2 * n : ℤ) : ZMod (4 * t * r ^ 2)) : ℂ) = 0 := by
  classical
  intro h
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  have hQ : NeZero (4 * t * r ^ 2) := inferInstance
  set Q := 4 * t * r ^ 2
  set e : AddChar (ZMod Q) ℂ := ZMod.stdAddChar
  set bj : ZMod (2 * t * r ^ 2) → ZMod Q := fun j ↦ (((j.val : ℤ) ^ 2 - 1 : ℤ) : ZMod Q)
  have hS : ∑ m : ZMod Q, e (-m) * ∑ j : ZMod (2 * t * r ^ 2), ψ⁻¹ (j.val : ZMod r) *
      (e (((j.val : ℤ) ^ 2 * (m.val : ℤ) : ℤ) : ZMod Q)) = 0 :=
    Finset.sum_eq_zero fun m _ ↦ by rw [h m.val, mul_zero]
  have hS' : ∑ m : ZMod Q, e (-m) * ∑ j : ZMod (2 * t * r ^ 2), ψ⁻¹ (j.val : ZMod r) *
      (e (((j.val : ℤ) ^ 2 * (m.val : ℤ) : ℤ) : ZMod Q)) =
      ∑ j : ZMod (2 * t * r ^ 2), ψ⁻¹ (j.val : ZMod r) * (if bj j = 0 then (Q : ℂ) else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hm : ∀ m : ZMod Q, e (-m) * (ψ⁻¹ (j.val : ZMod r) *
        e (((j.val : ℤ) ^ 2 * (m.val : ℤ) : ℤ) : ZMod Q)) = ψ⁻¹ (j.val : ZMod r) * e (m * bj j) := by
      intro m
      rw [mul_left_comm, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [bj]
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    simp_rw [hm, ← Finset.mul_sum]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar Q)]
    simp [ZMod.card]
  have hS'' : ∑ j : ZMod (2 * t * r ^ 2), ψ⁻¹ (j.val : ZMod r) * (if bj j = 0 then (Q : ℂ) else 0) =
      ∑ j : ZMod (2 * t * r ^ 2), (if bj j = 0 then (Q : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    split_ifs with hj
    · have hdvd : (4 * (r : ℤ) ^ 2) ∣ (j.val : ℤ) ^ 2 - 1 := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ Q).mp hj
        exact dvd_trans ⟨t, by push_cast [Q]; ring⟩ this
      have h1 := psi_eq_one_of_isTotallyEven ψ hψ hdvd
      rw [MulChar.inv_apply_eq_inv', show ((j.val : ℤ) : ZMod r) = (j.val : ZMod r) by push_cast; rfl] at *
      rw [h1, inv_one, one_mul]
    · simp
  rw [hS', hS'', Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const] at hS
  have hmem : (1 : ZMod (2 * t * r ^ 2)) ∈ Finset.univ.filter fun j ↦ bj j = 0 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h1 : (1 : ZMod (2 * t * r ^ 2)).val = 1 := ZMod.val_one'' (by
      have : 2 ≤ 2 * t * r ^ 2 := by nlinarith [Nat.one_le_pow 2 r hr]
      omega)
    simp only [bj, h1]
    push_cast
    ring
  have hcard : 0 < (Finset.univ.filter fun j ↦ bj j = 0).card := Finset.card_pos.mpr ⟨_, hmem⟩
  rw [nsmul_eq_mul] at hS
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne
  exact mul_ne_zero (by exact_mod_cast hcard.ne') hQ0 hS

/-! ### The theorem -/

/-- **The other direction of the Serre–Stark cusp criterion** (Serre–Stark 1977 `serrestark1977`, §3 [unverified]): for `(Φ, t) ∈ Ω₀(4N, χ)` with `Φ*` totally even, `θ_{Φ*,t}` is not a cusp form: its constant term
at one of the cusps `-1/n` is not zero. -/
@[kb "serrestark1977" "§3: theta_{psi,t} is not a cusp form when psi is totally even (proved, cusps -1/n)"]
theorem unaryThetaOf_not_mem_cusp_of_totallyEven {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)}
    {p : DirichletCharacter ℂ (4 * N) × ℕ} (hp : p ∈ unaryIndex 0 N χ)
    (hψ : IsTotallyEven p.1.primitiveCharacter) :
    unaryThetaOf p ∉ halfIntCuspForms 0 N χ := by
  intro hc
  obtain ⟨hν, ht, -, -⟩ := hp
  have hr : 1 ≤ p.1.conductor := conductor_pos p.1
  haveI : NeZero p.1.conductor := ⟨by omega⟩
  set ψ := p.1.primitiveCharacter
  have hprim : ψ.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive p.1
  have hpar : charParity ψ⁻¹ = 0 := by rw [charParity_inv, charParity_primitiveCharacter, hν]
  set c : ℂ := (((√(2 * p.2) : ℝ) : ℂ) ^ charParity ψ⁻¹)⁻¹
  have hc0 : c ≠ 0 := inv_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr
    (Real.sqrt_ne_zero'.mpr (by have := ht; positivity))))
  have : NeZero (2 * p.2 * p.1.conductor ^ 2) :=
    ⟨mul_ne_zero (mul_ne_zero two_ne_zero (by omega)) (pow_ne_zero _ (by omega))⟩
  have : NeZero (4 * p.2 * p.1.conductor ^ 2) :=
    ⟨mul_ne_zero (mul_ne_zero four_ne_zero (by omega)) (pow_ne_zero _ (by omega))⟩
  have key : ∀ n : ℤ, ∑ j : ZMod (2 * p.2 * p.1.conductor ^ 2), ψ⁻¹ (j.val : ZMod p.1.conductor) *
      (ZMod.stdAddChar (((j.val : ℤ) ^ 2 * n : ℤ) : ZMod (4 * p.2 * p.1.conductor ^ 2)) : ℂ) = 0 := by
    intro n
    have hz := hc.zero_at_cusps (ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S)
    have hrw : cuspNorm 0 (unaryThetaOf p) (ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S) =
        fun τ ↦ ‖c‖ * absSlash ((0 : ℕ) + finrank ℝ ℝ / 2) (thetaLat ψ⁻¹ ht hr)
          (ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S) τ := by
      funext τ
      rw [cuspNorm_eq_absSlash', unaryThetaOf_eq p ht]
      simp only [absSlash, norm_mul]
      ring
    rw [hrw] at hz
    have hz' : UpperHalfPlane.IsZeroAtImInfty (absSlash ((0 : ℕ) + finrank ℝ ℝ / 2)
        (thetaLat ψ⁻¹ ht hr) (ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S)) := by
      have := (hz : Tendsto _ _ _).const_mul ‖c‖⁻¹
      rw [mul_zero] at this
      refine this.congr fun τ ↦ ?_
      rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc0), one_mul]
    rw [thetaLat_eq_sum_twistClass ψ⁻¹ ht hr hpar] at hz'
    have h0 := sum_coeff_eq_zero_of_isZeroAtImInfty (isEven_twistLattice ht hr) (1 : ℝ) 0
      (fun b ↦ ψ⁻¹⁻¹ b) (twistClass ht hr) n hz'
    simp only [inv_inv] at h0
    rw [sum_coeff_twist ht hr hprim n] at h0
    exact (mul_eq_zero.mp h0).resolve_left (Miyake.gaussW_ne_zero hprim)
  exact not_forall_sum_eq_zero ht hψ key

/-- **The Serre–Stark cusp criterion in weight `1/2`** (`UnaryThetaCuspCriterion`, LE-MF-0239), proved. -/
@[kb "serrestark1977" "§3: theta_{psi,t} in M_{1/2}(4N, chi) is a cusp form iff psi is not totally even (proved)"]
theorem unaryThetaCuspCriterion {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ (4 * N)) :
    UnaryThetaCuspCriterion N χ :=
  ⟨fun _ hp ↦ ⟨fun hc he ↦ unaryThetaOf_not_mem_cusp_of_totallyEven hp he hc,
    unaryThetaOf_mem_cusp_of_not_totallyEven hp⟩⟩

/-- **`UnaryThetaModular 0 N χ`** (Serre–Stark in weight `1/2`: membership and the cusp criterion), proved. -/
@[kb "serrestark1977" "UnaryThetaModular in weight 1/2 (nu = 0), proved"]
theorem unaryThetaModular_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ (4 * N)) :
    UnaryThetaModular 0 N χ :=
  unaryThetaModular_zero_of_cuspCriterion (unaryThetaCuspCriterion χ)

/-- **Serre–Stark, Theorem A, conditional on its spanning half only** (`SerreStarkSpan`): the `θ_{ψ,t}`,
`(ψ, t) ∈ Ω(4N, χ)`, form a basis of `M_{1/2}(4N, χ)`. -/
theorem serreStark_basis_of_spanOnly {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)}
    (hA : SerreStarkSpan N χ) :
    ∃ b : Module.Basis (unaryIndex 0 N χ) ℂ (halfIntModularForms 0 N χ),
      ∀ p, (b p : ℍ → ℂ) = unaryThetaOf p.1 :=
  serreStark_basis (unaryThetaModular_zero χ) hA

/-- **Serre–Stark, Theorem B, conditional on its spanning half only** (`SerreStarkCuspSpan`): the `θ_{ψ,t}` with
`ψ` not totally even form a basis of `S_{1/2}(4N, χ)`. -/
theorem serreStark_cusp_basis_of_spanOnly {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)}
    (hB : SerreStarkCuspSpan N χ) :
    ∃ b : Module.Basis (unaryIndexCusp N χ) ℂ (halfIntCuspForms 0 N χ),
      ∀ p, (b p : ℍ → ℂ) = unaryThetaOf p.1 :=
  serreStark_cusp_basis (unaryThetaModular_zero χ) hB

/-- `dim M_{1/2}(4N, χ) = #Ω(4N, χ)`, conditional on `SerreStarkSpan` only. -/
theorem serreStark_finrank_of_spanOnly {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ (4 * N)}
    (hA : SerreStarkSpan N χ) :
    Module.finrank ℂ (halfIntModularForms 0 N χ) = Nat.card (unaryIndex 0 N χ) :=
  serreStark_finrank (unaryThetaModular_zero χ) hA

end ModularFormsKB.HalfIntegral
