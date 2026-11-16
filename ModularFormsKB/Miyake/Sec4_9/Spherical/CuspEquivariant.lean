import ModularFormsKB.Miyake.Sec4_9.Spherical.Cusps

/-!
# The coset theta series at every cusp: an equivariant transformation law (every rank)

The expansion of a theta series at every cusp, in a
structural form.

Let `L` be an even lattice of any rank `n`, `D = L^∨ / L` its discriminant group and `θ_y = θ_{y+L}(·; P)` the coset
theta series with a spherical weight of degree `ν`. For every `A ∈ SL(2, ℤ)` there are a function `φ_A` on `ℍ` with
`|φ_A(τ)| = C_A |cτ + d|^{ν + n/2}` and a matrix `M_A : D × D → ℂ` such that
$$\theta_x(A\tau) = \varphi_A(\tau) \sum_{y \in D} M_A(x, y)\, \theta_y(\tau) \qquad (x \in D),$$
(`exists_thetaSph_smul_eq`; this is the Weil representation of `SL(2, ℤ)` on `ℂ[D]`, up to the factor `φ_A`). The
matrix commutes with every isometry of the discriminant form: if a bijection `ρ` of `D` preserves the quadratic phase
`e(q(x))` and the pairing `e(b(x, y))` (`IsDiscIsom`), then `M_A(ρx, ρy) = M_A(x, y)`.

**Proof.** By Mathlib's `FixedDetMatrices.induction_on` over the generators `S`, `T`, as in
`absSlash_thetaSph_induction` (`Cusps.lean`), but with equalities in place of bounds:
* `T`: `θ_x(τ + 1) = e(q(x)) θ_x(τ)` (`thetaSph_one_vadd`);
* `S`: `θ_x(-1/σ) = (covol L)⁻¹ (-σ)^ν (σ/i)^{n/2} ∑_y e(b(x, y)) θ_y(σ)` (`thetaSph_S_smul_sum`, from Miyake's
  Lemma 4.9.1 `thetaSph_S_smul` and the splitting of `L^∨` into cosets of `L`).
Both coefficient matrices are invariant under `ρ`, and invariance is preserved by products.

**Consequence: vanishing constant terms** (`isZeroAtImInfty_absSlash_sum_thetaSph`). Let `Θ = ∑_i c_i θ_{x_i}` be a
finite combination (`ν = 0`) and `σ` a permutation of the index set with `x_{σ i} = ρ(x_i)` and
`c_{σ i} = λ c_i`, `ρ 0 = 0`, `λ ≠ 1`. Then the constant term of `Θ` at every cusp, `∑_i c_i M_A(x_i, 0)`, equals
`λ` times itself, so it vanishes, and `Θ` vanishes at every cusp. This is the argument of the cusp criterion of
Serre–Stark in weight `1/2` (`UnaryCusp.lean`): no Gauss sum is evaluated.
-/

open Complex Module Filter
open scoped Real RealInnerProductSpace UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- A bijection of the discriminant group is an **isometry of the discriminant form** when it preserves the quadratic
phase `e(q(x))` and the pairing `e(b(x, y))`. -/
def IsDiscIsom (hL : ZLattice.IsEven L) (ρ : ZLattice.DiscriminantGroup L ≃ ZLattice.DiscriminantGroup L) : Prop :=
  (∀ x, hL.discriminantQuadraticChar (ρ x) = hL.discriminantQuadraticChar x) ∧
    ∀ x y, hL.isIntegral.discriminantPairingChar (ρ x) (ρ y) = hL.isIntegral.discriminantPairingChar x y

/-- The chosen representative of a class of the discriminant group, in `E`. -/
noncomputable abbrev discRep (y : ZLattice.DiscriminantGroup L) : E := ((Quotient.out y : ZLattice.dual L) : E)

theorem mk_discRep (y : ZLattice.DiscriminantGroup L) :
    (Submodule.Quotient.mk (Quotient.out y : ZLattice.dual L) : ZLattice.DiscriminantGroup L) = y :=
  Quotient.out_eq' y

theorem discRep_mem_dual (y : ZLattice.DiscriminantGroup L) : discRep y ∈ ZLattice.dual L :=
  (Quotient.out y).2

variable [MeasurableSpace E] [BorelSpace E]

/-- **The inversion law on the discriminant group** (Miyake, Lemma 4.9.1, as a finite sum): for an integral lattice
and `δ ∈ L^∨`, `θ_{δ+L}(-1/σ; P) = (covol L)⁻¹ (-σ)^ν (σ/i)^{n/2} ∑_{y ∈ L^∨/L} e(⟪δ, y⟫) θ_{y+L}(σ; P)`. -/
theorem thetaSph_S_smul_sum (hL : ZLattice.IsIntegral L) [Fintype (ZLattice.DiscriminantGroup L)]
    {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) {δ : E} (hδ : δ ∈ ZLattice.dual L) (σ : ℍ) :
    thetaSph L ν u w δ (ModularGroup.S • σ) = (ZLattice.covolume L : ℂ)⁻¹ *
      ((-(σ : ℂ)) ^ ν * ((σ : ℂ) / I) ^ ((finrank ℝ E : ℂ) / 2)) *
      ∑ y : ZLattice.DiscriminantGroup L,
        cexp (2 * π * I * ⟪δ, discRep y⟫) * thetaSph L ν u w (discRep y) σ := by
  have hLd : L ≤ ZLattice.dual L := ZLattice.isIntegral_iff_le_dual.mp hL
  have hsplit := hasSum_thetaW_add_out (ZLattice.dual L) (polyBounded_phaseWeight ν u w δ)
    (M := L) hLd 0 σ
  rw [thetaSph_S_smul L hsph δ σ]
  have hdual : (∑' m : ZLattice.dual L, isoForm u w m ^ ν * cexp (2 * π * I * ⟪δ, (m : E)⟫) *
      cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * σ)) = thetaW (ZLattice.dual L) (phaseWeight ν u w δ) 0 σ := by
    rw [thetaW_apply]
    exact tsum_congr fun m ↦ by simp [phaseWeight]
  rw [hdual, ← hsplit.tsum_eq, tsum_fintype]
  simp only [zero_add, thetaW_phaseWeight ν u w hδ]

/-- **The translation law**: for an even lattice and `δ ∈ L^∨`, `θ_{δ+L}(1 + σ; P) = e(‖δ‖²/2) θ_{δ+L}(σ; P)`. -/
theorem thetaSph_one_vadd (hL : ZLattice.IsEven L) (ν : ℕ) (u w : E) {δ : E}
    (hδ : δ ∈ ZLattice.dual L) (σ : ℍ) :
    thetaSph L ν u w δ ((1 : ℝ) +ᵥ σ) = cexp (π * I * (‖δ‖ ^ 2 : ℝ)) * thetaSph L ν u w δ σ := by
  rw [thetaSph, thetaW_vadd_eq_mul L _ δ (fun v hv ↦ ?_) σ, ← thetaSph]
  · push_cast; ring_nf
  · obtain ⟨i, hi⟩ := ZLattice.mem_dual.mp hδ _ hv
    obtain ⟨j, hj⟩ := ZLattice.isEven_iff.mp hL _ hv
    refine ⟨i + j, ?_⟩
    rw [norm_add_sq_real, hi, hj]
    push_cast
    ring

theorem discriminantQuadraticChar_discRep (hL : ZLattice.IsEven L) (x : ZLattice.DiscriminantGroup L) :
    hL.discriminantQuadraticChar x = cexp (π * I * (‖discRep x‖ ^ 2 : ℝ)) := by
  conv_lhs => rw [← mk_discRep x]
  exact hL.discriminantQuadraticChar_mk _

theorem discriminantPairingChar_discRep (hL : ZLattice.IsIntegral L) (x y : ZLattice.DiscriminantGroup L) :
    hL.discriminantPairingChar x y = cexp (2 * π * I * ⟪discRep x, discRep y⟫) := by
  conv_lhs => rw [← mk_discRep x, ← mk_discRep y]
  exact hL.discriminantPairingChar_mk_mk _ _

/-- **The equivariant transformation law of the coset theta series at every cusp** (in
structural form). For an even lattice of rank `n`, a spherical weight of degree `ν` and `A ∈ SL(2, ℤ)`:
`θ_x(Aτ) = φ_A(τ) ∑_y M_A(x, y) θ_y(τ)` with `|φ_A(τ)| = C_A |cτ + d|^{ν + n/2}`, and `M_A` commutes with every
isometry of the discriminant form. -/
theorem exists_thetaSph_smul_eq (hL : ZLattice.IsEven L) [Fintype (ZLattice.DiscriminantGroup L)]
    {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) (A : SL(2, ℤ)) :
    ∃ (C : ℝ) (φ : ℍ → ℂ) (M : ZLattice.DiscriminantGroup L → ZLattice.DiscriminantGroup L → ℂ),
      (∀ τ : ℍ, ‖φ τ‖ = C * ‖(A 1 0 : ℂ) * τ + A 1 1‖ ^ ((ν : ℝ) + finrank ℝ E / 2)) ∧
      (∀ ρ, IsDiscIsom hL ρ → ∀ x y, M (ρ x) (ρ y) = M x y) ∧
      ∀ x τ, thetaSph L ν u w (discRep x) (A • τ) =
        φ τ * ∑ y, M x y * thetaSph L ν u w (discRep y) τ := by
  classical
  set wt : ℝ := (ν : ℝ) + finrank ℝ E / 2
  induction A using (FixedDetMatrices.induction_on one_ne_zero) with
  | h0 A ha hc _ hd =>
    rw [FixedDetMatrices.reps_one_id A ha hc hd]
    refine ⟨1, fun _ ↦ 1, fun x y ↦ if x = y then 1 else 0, fun τ ↦ ?_, fun ρ _ x y ↦ ?_,
      fun x τ ↦ ?_⟩
    · simp
    · simp [ρ.injective.eq_iff]
    · simp
  | hS B ih =>
    change SL(2, ℤ) at B
    obtain ⟨C, φ, M, hφ, hM, hθ⟩ := ih
    change ∃ (C : ℝ) (φ : ℍ → ℂ) (M : ZLattice.DiscriminantGroup L → ZLattice.DiscriminantGroup L → ℂ),
      (∀ τ : ℍ, ‖φ τ‖ = C * ‖((ModularGroup.S * B) 1 0 : ℂ) * τ + (ModularGroup.S * B) 1 1‖ ^ wt) ∧
      (∀ ρ, IsDiscIsom hL ρ → ∀ x y, M (ρ x) (ρ y) = M x y) ∧
      ∀ x τ, thetaSph L ν u w (discRep x) ((ModularGroup.S * B) • τ) =
        φ τ * ∑ y, M x y * thetaSph L ν u w (discRep y) τ
    refine ⟨(ZLattice.covolume L)⁻¹ * C,
      fun τ ↦ (ZLattice.covolume L : ℂ)⁻¹ * ((-((B • τ : ℍ) : ℂ)) ^ ν *
        (((B • τ : ℍ) : ℂ) / I) ^ ((finrank ℝ E : ℂ) / 2)) * φ τ,
      fun x y ↦ ∑ z, hL.isIntegral.discriminantPairingChar x z * M z y, fun τ ↦ ?_, fun ρ hρ x y ↦ ?_,
      fun x τ ↦ ?_⟩
    · have hSB0 : ((ModularGroup.S * B) 1 0 : ℂ) = B 0 0 := by
        simp [ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
      have hSB1 : ((ModularGroup.S * B) 1 1 : ℂ) = B 0 1 := by
        simp [ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hSB0, hSB1, norm_top_eq]
      have hden : 0 < ‖(B 1 0 : ℂ) * τ + B 1 1‖ := norm_pos_iff.mpr (by
        simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero B τ)
      have hσ : 0 < ‖((B • τ : ℍ) : ℂ)‖ := norm_pos_iff.mpr (B • τ).ne_zero
      have hcov : 0 < ZLattice.covolume L := ZLattice.covolume_pos L
      have hc : ‖(((B • τ : ℍ) : ℂ) / I) ^ ((finrank ℝ E : ℂ) / 2)‖ =
          ‖((B • τ : ℍ) : ℂ)‖ ^ ((finrank ℝ E : ℝ) / 2) := by
        rw [show ((finrank ℝ E : ℂ) / 2) = (((finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_real, norm_div, Complex.norm_I, div_one]
      rw [norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcov,
        norm_pow, norm_neg, hc, hφ, Real.mul_rpow hσ.le hden.le]
      simp only [wt]
      rw [Real.rpow_add hσ, Real.rpow_natCast]
      ring
    · have hpair := hρ.2
      dsimp only
      rw [← Equiv.sum_comp ρ]
      exact Finset.sum_congr rfl fun z _ ↦ by rw [hpair, hM ρ hρ]
    · rw [mul_smul, thetaSph_S_smul_sum hL.isIntegral hsph (discRep_mem_dual x)]
      simp_rw [hθ]
      rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun z _ ↦ ?_
      rw [discriminantPairingChar_discRep]
      ring
  | hT B ih =>
    change SL(2, ℤ) at B
    obtain ⟨C, φ, M, hφ, hM, hθ⟩ := ih
    change ∃ (C : ℝ) (φ : ℍ → ℂ) (M : ZLattice.DiscriminantGroup L → ZLattice.DiscriminantGroup L → ℂ),
      (∀ τ : ℍ, ‖φ τ‖ = C * ‖((ModularGroup.T * B) 1 0 : ℂ) * τ + (ModularGroup.T * B) 1 1‖ ^ wt) ∧
      (∀ ρ, IsDiscIsom hL ρ → ∀ x y, M (ρ x) (ρ y) = M x y) ∧
      ∀ x τ, thetaSph L ν u w (discRep x) ((ModularGroup.T * B) • τ) =
        φ τ * ∑ y, M x y * thetaSph L ν u w (discRep y) τ
    refine ⟨C, φ, fun x y ↦ hL.discriminantQuadraticChar x * M x y, fun τ ↦ ?_, fun ρ hρ x y ↦ ?_,
      fun x τ ↦ ?_⟩
    · have hTB0 : ((ModularGroup.T * B) 1 0 : ℂ) = B 1 0 := by
        simp [ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
      have hTB1 : ((ModularGroup.T * B) 1 1 : ℂ) = B 1 1 := by
        simp [ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hTB0, hTB1]
      exact hφ τ
    · dsimp only
      rw [hρ.1, hM ρ hρ]
    · rw [mul_smul, UpperHalfPlane.modular_T_smul, thetaSph_one_vadd hL ν u w (discRep_mem_dual x), hθ]
      dsimp only
      rw [discriminantQuadraticChar_discRep, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ ↦ by ring

/-- With `ν = 0` the coset theta series is Tau Ceti's `thetaCoset`. -/
theorem thetaSph_zero (u w γ : E) : thetaSph L 0 u w γ = ZLattice.thetaCoset L γ := by
  rw [← thetaW_one]
  unfold thetaSph
  simp only [pow_zero]

/-- **Vanishing constant terms from a symmetry** (the cusp criterion argument). Let `Θ = ∑_i c_i θ_{x_i}` (`ν = 0`),
`ρ` an isometry of the discriminant form fixing `0`, and `σ` a permutation of the indices with `x_{σ i} = ρ(x_i)` and
`c_{σ i} = λ c_i` for some `λ ≠ 1`. Then `|cτ + d|^{-n/2} |Θ(Aτ)| → 0` at `i∞` for every `A ∈ SL(2, ℤ)`. -/
theorem isZeroAtImInfty_absSlash_sum_thetaSph (hL : ZLattice.IsEven L)
    [Fintype (ZLattice.DiscriminantGroup L)] (u w : E) {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (x : ι → ZLattice.DiscriminantGroup L) (ρ : ZLattice.DiscriminantGroup L ≃ ZLattice.DiscriminantGroup L)
    (hρ : IsDiscIsom hL ρ) (hρ0 : ρ 0 = 0) (σ : ι ≃ ι) {lam : ℂ} (hlam : lam ≠ 1)
    (hx : ∀ i, x (σ i) = ρ (x i)) (hc : ∀ i, c (σ i) = lam * c i) (A : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (absSlash ((0 : ℕ) + finrank ℝ E / 2)
      (fun τ ↦ ∑ i, c i * thetaSph L 0 u w (discRep (x i)) τ) A) := by
  classical
  obtain ⟨C, φ, M, hφ, hM, hθ⟩ := exists_thetaSph_smul_eq hL (u := u) (w := w) (ν := 0) (Or.inl (Nat.zero_le 1)) A
  set b : ZLattice.DiscriminantGroup L → ℂ := fun y ↦ ∑ i, c i * M (x i) y
  have hb0 : b 0 = 0 := by
    have h : b 0 = lam * b 0 := by
      calc b 0 = ∑ i, c (σ i) * M (x (σ i)) 0 := (Equiv.sum_comp σ (fun i ↦ c i * M (x i) 0)).symm
        _ = ∑ i, lam * (c i * M (x i) 0) := Finset.sum_congr rfl fun i _ ↦ by
            rw [hc, hx, ← hρ0, hM ρ hρ, hρ0]; ring
        _ = lam * b 0 := by rw [← Finset.mul_sum]
    have h' : (1 - lam) * b 0 = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hlam.symm)
  have hrw : ∀ τ : ℍ, absSlash ((0 : ℕ) + finrank ℝ E / 2)
      (fun τ ↦ ∑ i, c i * thetaSph L 0 u w (discRep (x i)) τ) A τ =
      C * ‖∑ y, b y * thetaSph L 0 u w (discRep y) τ‖ := by
    intro τ
    have hden : 0 < ‖(A 1 0 : ℂ) * τ + A 1 1‖ := norm_pos_iff.mpr (by
      simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero A τ)
    have hsum : (∑ i, c i * thetaSph L 0 u w (discRep (x i)) (A • τ)) =
        φ τ * ∑ y, b y * thetaSph L 0 u w (discRep y) τ := by
      simp_rw [hθ, b, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
    rw [absSlash, hsum, norm_mul, hφ, Real.rpow_neg hden.le]
    field_simp
  have hterm : ∀ y, Tendsto (fun τ ↦ b y * thetaSph L 0 u w (discRep y) τ) UpperHalfPlane.atImInfty
      (nhds 0) := by
    intro y
    by_cases hy : y = 0
    · simp [hy, hb0]
    · have hy' : discRep y ∉ L := by
        intro hmem
        apply hy
        rw [← mk_discRep y]
        exact (Submodule.Quotient.mk_eq_zero _).mpr hmem
      have h := (ZLattice.isZeroAtImInfty_thetaCoset L hy')
      rw [← thetaSph_zero u w] at h
      simpa using (h : Tendsto _ _ _).const_mul (b y)
  have hsum : Tendsto (fun τ ↦ ∑ y, b y * thetaSph L 0 u w (discRep y) τ) UpperHalfPlane.atImInfty
      (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ fun y _ ↦ hterm y
  have h := (hsum.norm.const_mul C)
  rw [norm_zero, mul_zero] at h
  exact h.congr fun τ ↦ (hrw τ).symm

end ModularFormsKB.Miyake.Sec4_9
