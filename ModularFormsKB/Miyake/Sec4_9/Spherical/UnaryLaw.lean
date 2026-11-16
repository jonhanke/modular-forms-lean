import ModularFormsKB.Miyake.Sec4_9.Spherical.Unary

/-!
# Shimura's twisted theta law for every character (Miyake, Corollary 4.9.7 (1))

For every `r ≥ 1`, every Dirichlet character `ψ` modulo `r`
(primitive or not) of parity `ν`, `t ≥ 1` and `γ ∈ Γ₀(4 t r²)`:

`θ_{ψ,t}(γτ) = ψ̄(d) (t / |d|) (cτ + d)^ν j(γ, τ) θ_{ψ,t}(τ)`

(`thetaTwist_law`), `j` the theta multiplier. This is the field `law` of
`HalfIntegral.ThetaTwistLaw` with the restriction "`r = 1` or an odd prime" removed.

**Proof.** `θ_{ψ,t} θ = (√(2t))^{-ν} F` with `F = ∑_{a mod r} ψ̄(a) θ_{(√(2t)a, 0) + L₂}(·; x₁^ν)`,
`L₂ = √(2t) r ℤ ⊕ √2 ℤ` even of rank `2` (`thetaSph_orthSum`, `thetaTwist_eq_sum`). The coset law
(`IsEvenSph.thetaSph_slash_eq_gaussSum_smul`) and Tau Ceti's evaluation of the Gauss sum give, for
`B = !![a, b; c, d] ∈ Γ₀(4tr²)` with `a > 0` odd and `c > 0`, `F ∣[1+ν] B = (D/a) ψ(a) F` after
reindexing the classes by `a`, with `D = -4tr²`; Tau Ceti's reduction to such matrices
(`TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd`) gives the law of `F` on `Γ₀(4tr²)`
with the character `χ_{L₂} ψ̄`, and the law of `θ` on `Γ₀(4)` is divided out as in odd rank
(`eq_zero_of_mul_theta_eq_zero`). The character becomes `ψ̄(d) (t/|d|)` by
`kronecker_twist_mul_chi4`.
-/

open Complex Module
open scoped Real RealInnerProductSpace UpperHalfPlane ModularForm MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

open HalfIntegral

variable {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r) {t : ℕ} (ht : 1 ≤ t) (hr : 1 ≤ r)

/-- `thetaLat` as a sum over `ZMod r`. -/
theorem thetaLat_eq_sum_zmod (τ : ℍ) :
    thetaLat ψ ht hr τ = ∑ a : ZMod r, ψ⁻¹ a *
      thetaSph (twistLattice ht hr) (charParity ψ) 1 0 (twistVec t (a.val : ℤ)) τ := by
  rw [thetaLat]
  refine Finset.sum_nbij' (fun a ↦ (a : ZMod r)) (fun a ↦ a.val) (by simp) (by simp [ZMod.val_lt])
    (fun a ha ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp ha)) (fun a _ ↦ ZMod.natCast_zmod_val a)
    fun a ha ↦ ?_
  rw [ZMod.val_cast_of_lt (Finset.mem_range.mp ha)]

/-- The doubled vector `(√(2t) n, 0)`. -/
noncomputable def twistVec₂ (t : ℕ) (n : ℤ) : WithLp 2 (ℝ × ℝ) := extVec (twistVec t n)

theorem twistVec₂_mem_dual (n : ℤ) : twistVec₂ t n ∈ ZLattice.dual (twistLattice₂ ht hr) := by
  rw [ZLattice.dual_orthSum, ZLattice.mem_orthSum]
  refine ⟨by simpa [twistVec₂, extVec] using twistVec_mem_dual ht hr n, by simp [twistVec₂, extVec]⟩

theorem norm_twistVec₂_sq (n : ℤ) : ‖twistVec₂ t n‖ ^ 2 = 2 * t * n ^ 2 := by
  rw [twistVec₂, extVec, WithLp.prod_norm_sq_eq_of_L2]
  have := norm_twistVec_sq t n
  simpa using this

theorem zsmul_twistVec₂ (m n : ℤ) : m • twistVec₂ t n = twistVec₂ t (m * n) := by
  simp only [twistVec₂, extVec, twistVec, ← WithLp.toLp_smul, Prod.smul_mk, smul_zero, zsmul_eq_mul]
  congr 2
  push_cast
  ring

/-- The doubled coset series depends only on `n` modulo `r`. -/
theorem thetaSph_twistVec₂_congr (ν : ℕ) {n n' : ℤ} (h : n ≡ n' [ZMOD r]) :
    thetaSph (twistLattice₂ ht hr) ν (extVec 1) (extVec 0) (twistVec₂ t n) =
      thetaSph (twistLattice₂ ht hr) ν (extVec 1) (extVec 0) (twistVec₂ t n') := by
  unfold thetaSph
  refine thetaW_eq_of_sub_mem _ _ ?_
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h.symm
  have hsub : twistVec₂ t n - twistVec₂ t n' = WithLp.toLp 2 ((k : ℝ) * twistGen t r, (0 : ℝ)) := by
    simp only [twistVec₂, extVec, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_zero]
    congr 2
    unfold twistVec twistGen
    rw [← mul_sub, ← Int.cast_sub, hk]
    push_cast
    ring
  rw [hsub, ZLattice.mem_orthSum]
  exact ⟨(mem_rankOneLattice _).mpr ⟨k, rfl⟩, zero_mem _⟩

/-- The doubled series `F = ∑_{a mod r} ψ̄(a) θ_{(√(2t)a, 0) + L₂}(·; x₁^ν)`. -/
noncomputable def thetaDbl (τ : ℍ) : ℂ :=
  ∑ a : ZMod r, ψ⁻¹ a *
    thetaSph (twistLattice₂ ht hr) (charParity ψ) (extVec 1) (extVec 0) (twistVec₂ t (a.val : ℤ)) τ

theorem thetaDbl_eq (τ : ℍ) : thetaDbl ψ ht hr τ = thetaLat ψ ht hr τ * HalfIntegral.theta τ := by
  rw [thetaDbl, thetaLat_eq_sum_zmod, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [twistVec₂, thetaSph_orthSum, mul_assoc]

/-- Each doubled coset series has period `1`. -/
theorem thetaSph_twistVec₂_one_vadd (ν : ℕ) (n : ℤ) (τ : ℍ) :
    thetaSph (twistLattice₂ ht hr) ν (extVec 1) (extVec 0) (twistVec₂ t n) ((1 : ℝ) +ᵥ τ) =
      thetaSph (twistLattice₂ ht hr) ν (extVec 1) (extVec 0) (twistVec₂ t n) τ := by
  have hL := isEven_orthSum_sqrtTwo (isEven_twistLattice ht hr)
  have hδ := twistVec₂_mem_dual ht hr (t := t) n
  rw [thetaSph, thetaW_vadd_eq_mul _ _ _ (fun v hv ↦ ?_) τ, ← thetaSph]
  · rw [norm_twistVec₂_sq]
    have : cexp (π * I * ((2 * t * n ^ 2 : ℝ) : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨t * n ^ 2, by push_cast; ring⟩
    rw [this, one_mul]
  · obtain ⟨i, hi⟩ := ZLattice.mem_dual.mp hδ _ hv
    obtain ⟨j, hj⟩ := ZLattice.isEven_iff.mp hL _ hv
    refine ⟨i + j, ?_⟩
    rw [norm_add_sq_real, hi, hj]
    push_cast
    ring

theorem thetaDbl_slash_T (k : ℤ) : thetaDbl ψ ht hr ∣[k] ModularGroup.T = thetaDbl ψ ht hr := by
  ext τ
  have h := TauCeti.ModularForm.slash_T_zpow_apply k 1 (thetaDbl ψ ht hr) τ
  simp only [zpow_one] at h
  rw [h, Int.cast_one, thetaDbl, thetaDbl]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [thetaSph_twistVec₂_one_vadd]

/-- **The law of one doubled coset series** under `B = !![a, b; c, d]`, `a > 0` odd, `c > 0`,
`N₂ ∣ c` (`N₂` the level of `L₂`): `θ_n ∣[1+ν] B = (-4tr² / a) θ_{an}`. -/
theorem thetaSph_twistVec₂_slash {ν : ℕ} (hν : ν ≤ 1) (n : ℤ) (B : SL(2, ℤ)) {a c : ℕ} [NeZero c]
    (ha : B 0 0 = a) (hc : B 1 0 = c) (haodd : Odd a)
    (hN : ZLattice.level (twistLattice₂ ht hr) ∣ c) (hac : a.Coprime c) :
    thetaSph (twistLattice₂ ht hr) ν (extVec 1) (extVec 0) (twistVec₂ t n) ∣[((1 + ν : ℕ) : ℤ)] B =
      (jacobiSym (-(4 * t * r ^ 2 : ℤ)) a : ℂ) •
        thetaSph (twistLattice₂ ht hr) ν (extVec 1) (extVec 0) (twistVec₂ t (a * n)) := by
  have hL := isEven_orthSum_sqrtTwo (isEven_twistLattice ht hr)
  have hsph : IsSphericalDatum ν (extVec (1 : ℝ)) (extVec (0 : ℝ)) :=
    isSphericalDatum_extVec (Or.inl hν)
  have h := IsEvenSph.thetaSph_slash_eq_gaussSum_smul hL finrank_twist₂ hsph B hc hN
    ⟨twistVec₂ t n, twistVec₂_mem_dual ht hr n⟩
  simp only at h
  rw [h, norm_twistVec₂_sq, ha, zsmul_twistVec₂]
  have he : cexp (2 * π * I * (((a : ℤ) : ℝ) * (B 0 1 : ℝ) * (2 * t * n ^ 2) / 2 : ℝ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨a * B 0 1 * t * n ^ 2, by push_cast; ring⟩
  rw [he, mul_one]
  congr 1
  have hn := hL.normalized_gaussSum_eq_jacobiSym finrank_twist₂ haodd hN hac
  rw [← ZLattice.signedDiscr_of_finrank_eq _ finrank_twist₂, signedDiscr_twistLattice₂] at hn
  push_cast at hn ⊢
  rw [← hn]

theorem isEven_twistLattice₂ : ZLattice.IsEven (twistLattice₂ ht hr) :=
  isEven_orthSum_sqrtTwo (isEven_twistLattice ht hr)

theorem dvd_four_t_r_sq : r ∣ 4 * t * r ^ 2 := ⟨4 * t * r, by ring⟩

theorem even_finrank_twist₂ : Even (finrank ℝ (WithLp 2 (ℝ × ℝ))) := ⟨1, by rw [finrank_twist₂]⟩

/-- The character `χ_{L₂} ψ̄` modulo `4 t r²` of the doubled series. -/
noncomputable def twistChar : DirichletCharacter ℂ (4 * t * r ^ 2) :=
  ((isEven_twistLattice₂ ht hr).thetaCharacter even_finrank_twist₂).changeLevel
      (level_twistLattice₂_dvd ht hr) *
    (ψ⁻¹).changeLevel (dvd_four_t_r_sq (t := t) (r := r))

/-- Reindexing the classes by a unit `a` with inverse `d` modulo `r`. -/
theorem sum_reindex (φ : DirichletCharacter ℂ r) (f : ℤ → ℍ → ℂ)
    (hf : ∀ n n' : ℤ, n ≡ n' [ZMOD r] → f n = f n') {a d : ℤ}
    (had : ((a : ZMod r) * (d : ZMod r)) = 1) (τ : ℍ) :
    ∑ x : ZMod r, φ x * f (a * x.val) τ = φ d * ∑ y : ZMod r, φ y * f y.val τ := by
  have hda : ((d : ZMod r) * (a : ZMod r)) = 1 := by rw [mul_comm]; exact had
  let e : ZMod r ≃ ZMod r :=
    { toFun := fun x ↦ (a : ZMod r) * x, invFun := fun y ↦ (d : ZMod r) * y,
      left_inv := fun x ↦ by simp only [← mul_assoc, hda, one_mul],
      right_inv := fun y ↦ by simp only [← mul_assoc, had, one_mul] }
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv e _ _ fun x ↦ ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [show φ x = φ (d : ZMod r) * φ ((a : ZMod r) * x) by
    rw [← map_mul, ← mul_assoc, hda, one_mul]]
  rw [hf (a * x.val) ((a : ZMod r) * x).val]
  · ring
  · rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp

/-- **The law of the doubled series for positive odd matrices.** -/
theorem thetaDbl_slash_pos_odd {B : SL(2, ℤ)} (hB : B ∈ CongruenceSubgroup.Gamma0 (4 * t * r ^ 2))
    (hc : 0 < B 1 0) (ha : 0 < B 0 0) (hao : Odd (B 0 0)) :
    thetaDbl ψ ht hr ∣[((1 + charParity ψ : ℕ) : ℤ)] B = twistChar ψ ht hr (B 1 1) • thetaDbl ψ ht hr := by
  obtain ⟨a, haeq⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨c, hceq⟩ := Int.eq_ofNat_of_zero_le hc.le
  have haodd : Odd a := by rw [haeq] at hao; exact_mod_cast hao
  have hdvd : 4 * t * r ^ 2 ∣ c := by
    have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hB
    rw [hceq] at h
    exact_mod_cast h
  have hN : ZLattice.level (twistLattice₂ ht hr) ∣ c := dvd_trans (level_twistLattice₂_dvd ht hr) hdvd
  have hc0 : c ≠ 0 := by rintro rfl; simp at hceq; omega
  have : NeZero c := ⟨hc0⟩
  have hac : IsCoprime (a : ℤ) c := by simpa only [haeq, hceq] using B.isCoprime_col 0
  have hBr : B ∈ CongruenceSubgroup.Gamma0 r :=
    CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr (dvd_trans (Int.natCast_dvd_natCast.mpr
      (dvd_four_t_r_sq (t := t) (r := r))) (CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hB))
  have had := CongruenceSubgroup.intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hBr
  rw [haeq] at had
  ext τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, thetaDbl, Finset.sum_mul]
  have hterm (x : ZMod r) : ψ⁻¹ x * thetaSph (twistLattice₂ ht hr) (charParity ψ) (extVec 1)
      (extVec 0) (twistVec₂ t (x.val : ℤ)) (B • τ) * UpperHalfPlane.denom B τ ^
        (-(((1 + charParity ψ : ℕ) : ℤ))) =
      (jacobiSym (-(4 * t * r ^ 2 : ℤ)) a : ℂ) * (ψ⁻¹ x * thetaSph (twistLattice₂ ht hr)
        (charParity ψ) (extVec 1) (extVec 0) (twistVec₂ t (a * x.val)) τ) := by
    have h := congrFun (thetaSph_twistVec₂_slash ht hr (charParity_le_one ψ) (x.val : ℤ) B haeq
      hceq haodd hN hac.natCoprime) τ
    rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [mul_assoc, h]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum,
    sum_reindex ψ⁻¹ (fun n ↦ thetaSph (twistLattice₂ ht hr) (charParity ψ) (extVec 1) (extVec 0)
      (twistVec₂ t n)) (fun n n' h ↦ thetaSph_twistVec₂_congr ht hr _ h) had τ]
  -- the character
  have hcopN : IsCoprime (B 1 1) (4 * t * r ^ 2 : ℕ) := by
    obtain ⟨u, hu⟩ := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hB
    have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
      have h := B.det_coe
      rwa [Matrix.det_fin_two] at h
    exact ⟨B 0 0, -(B 0 1 * u), by linear_combination hdet + B 0 1 * hu⟩
  have hBL : B ∈ CongruenceSubgroup.Gamma0 (ZLattice.level (twistLattice₂ ht hr)) :=
    CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr (dvd_trans (Int.natCast_dvd_natCast.mpr
      (level_twistLattice₂_dvd ht hr)) (CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hB))
  have haN : IsCoprime (a : ℤ) (ZLattice.level (twistLattice₂ ht hr)) := by
    have hunit := CongruenceSubgroup.isUnit_intCast_apply_zero_zero_of_mem_Gamma0 hBL
    rw [← haeq]
    exact isCoprime_comm.mp ((ZMod.isUnit_intCast_iff_isCoprime _ _).mp hunit)
  have hχ : twistChar ψ ht hr (B 1 1) = (jacobiSym (-(4 * t * r ^ 2 : ℤ)) a : ℂ) * ψ⁻¹ (B 1 1) := by
    have hq := ((isEven_twistLattice₂ ht hr).thetaCharacter_isQuadratic
      even_finrank_twist₂).apply_one_one_eq_apply_zero_zero_of_mem_Gamma0 hBL
    rw [twistChar, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcopN,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcopN, hq, haeq,
      (isEven_twistLattice₂ ht hr).thetaCharacter_intCast even_finrank_twist₂ haN,
      TauCeti.kroneckerSym_eq_jacobiSym _ haodd, signedDiscr_twistLattice₂]
  rw [hχ, thetaDbl]
  ring

omit [NeZero r] in
theorem charParity_spec : ψ (-1) = (-1) ^ charParity ψ := by
  unfold charParity
  split_ifs with h
  · simp [h]
  · have hsq : ψ (-1) ^ 2 = 1 := by rw [← map_pow]; simp
    rcases sq_eq_one_iff.mp hsq with h' | h'
    · exact absurd h' h
    · simp [h']

theorem twistChar_neg_one : twistChar ψ ht hr (-1) = (-1 : ℂ) ^ ((1 + charParity ψ : ℕ) : ℤ) := by
  have hcop : IsCoprime (-1 : ℤ) (4 * t * r ^ 2 : ℕ) := isCoprime_one_left.neg_left
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd'
    ((isEven_twistLattice₂ ht hr).thetaCharacter even_finrank_twist₂)
    (level_twistLattice₂_dvd ht hr) hcop
  have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ⁻¹
    (dvd_four_t_r_sq (t := t) (r := r)) hcop
  push_cast at h1 h2
  rw [twistChar, MulChar.mul_apply, h1, h2,
    (isEven_twistLattice₂ ht hr).thetaCharacter_neg_one even_finrank_twist₂ finrank_twist₂,
    MulChar.inv_apply_eq_inv', charParity_spec]
  push_cast
  rw [zpow_add₀ (by norm_num), zpow_one, zpow_natCast, pow_one]
  rcases Nat.even_or_odd (charParity ψ) with h | h <;> simp [h.neg_one_pow]

/-- **The law of the doubled series on `Γ₀(4tr²)`.** -/
theorem thetaDbl_slash_of_mem_Gamma0 {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma0 (4 * t * r ^ 2)) :
    thetaDbl ψ ht hr ∣[((1 + charParity ψ : ℕ) : ℤ)] A = twistChar ψ ht hr (A 1 1) • thetaDbl ψ ht hr :=
  TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd (twistChar_neg_one ψ ht hr)
    (thetaDbl_slash_T ψ ht hr _) (fun _ hB hc ha hao ↦ thetaDbl_slash_pos_odd ψ ht hr hB hc ha hao) hA

theorem continuous_thetaLat : Continuous (thetaLat ψ ht hr) := by
  unfold thetaLat
  refine continuous_finsetSum _ fun a _ ↦ continuous_const.mul ?_
  exact (mdifferentiable_thetaW _ (polyBounded_isoForm_pow 1 0 _) _).continuous

/-- **The law of the lattice combination** (division by `θ`): for `A ∈ Γ₀(4tr²)`,
`thetaLat(Aτ) = χ(d) χ_{-4}(d)^{1+ν} j(A, τ)^{2ν+1} thetaLat(τ)`. -/
theorem thetaLat_smul {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma0 (4 * t * r ^ 2)) (τ : ℍ) :
    thetaLat ψ ht hr (A • τ) = twistChar ψ ht hr (A 1 1) *
      (ZMod.χ₄ (A 1 1 : ZMod 4) : ℂ) ^ (1 + charParity ψ) *
      HalfIntegral.thetaMult A τ ^ (2 * charParity ψ + 1) * thetaLat ψ ht hr τ := by
  have hA4 : A ∈ CongruenceSubgroup.Gamma0 4 := by
    have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hA
    exact CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr
      (dvd_trans (by exact_mod_cast (⟨t * r ^ 2, by ring⟩ : (4 : ℕ) ∣ 4 * t * r ^ 2)) h)
  set ν := charParity ψ
  set χ' := twistChar ψ ht hr (A 1 1)
  set X : ℂ := (ZMod.χ₄ (A 1 1 : ZMod 4) : ℂ)
  have hX : X ^ 2 = 1 := by
    have hodd := HalfIntegral.Gamma0_four_odd hA4
    have h2 : (A 1 1) % 2 = 1 := Int.odd_iff.mp hodd
    have h := chi4_int_sq h2
    simp only [X]
    exact_mod_cast h
  set m := 1 + ν
  have hF := congrFun (thetaDbl_slash_of_mem_Gamma0 ψ ht hr hA)
  have hθ := HalfIntegral.theta_transformationLaw A hA4
  let G : ℍ → ℂ := fun σ ↦ thetaLat ψ ht hr (A • σ) -
    χ' * X ^ m * HalfIntegral.thetaMult A σ ^ (2 * ν + 1) * thetaLat ψ ht hr σ
  have hcont : Continuous G := by
    have h1 := continuous_thetaLat ψ ht hr
    have h2 : Continuous (HalfIntegral.thetaMult A ∘ ((↑) : ℍ → ℂ)) :=
      (HalfIntegral.thetaMultiplierSystem.holo A hA4).continuous
    have h3 : Continuous fun σ : ℍ ↦ A • σ :=
      (continuous_const_smul (A : GL (Fin 2) ℝ)).congr fun σ ↦ (ModularGroup.sl_moeb A σ).symm
    have h2' : Continuous fun σ : ℍ ↦ HalfIntegral.thetaMult A σ := h2
    exact (h1.comp h3).sub ((continuous_const.mul (h2'.pow _)).mul h1)
  have hzero : ∀ σ : ℍ, G σ * HalfIntegral.theta σ = 0 := by
    intro σ
    have hjσ0 : HalfIntegral.thetaMult A σ ≠ 0 := HalfIntegral.thetaMultiplierSystem.ne_zero A hA4 σ
    have hjσ2 := HalfIntegral.thetaMult_sq hA4 σ
    have hFσ := hF σ
    rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, thetaDbl_eq, thetaDbl_eq,
      ModularGroup.denom_apply, hθ σ] at hFσ
    have hD0 : ((A 1 0 : ℂ) * σ + A 1 1) ≠ 0 := by
      simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero A σ
    rw [zpow_neg, zpow_natCast] at hFσ
    have h1 : thetaLat ψ ht hr (A • σ) * (HalfIntegral.thetaMult A σ * HalfIntegral.theta σ) =
        χ' * (thetaLat ψ ht hr σ * HalfIntegral.theta σ) * ((A 1 0 : ℂ) * σ + A 1 1) ^ m := by
      rw [← hFσ, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hD0), mul_one]
    have hjpow : HalfIntegral.thetaMult A σ ^ (2 * ν + 1) * HalfIntegral.thetaMult A σ =
        X ^ m * ((A 1 0 : ℂ) * σ + A 1 1) ^ m := by
      rw [← pow_succ, show 2 * ν + 1 + 1 = 2 * m by ring, pow_mul, hjσ2, mul_pow]
    have hXm : X ^ m * X ^ m = 1 := by rw [← pow_add, ← two_mul, pow_mul, hX, one_pow]
    have key : (G σ * HalfIntegral.theta σ) * HalfIntegral.thetaMult A σ = 0 := by
      simp only [G]
      linear_combination h1 - χ' * X ^ m * thetaLat ψ ht hr σ * HalfIntegral.theta σ * hjpow -
        χ' * thetaLat ψ ht hr σ * HalfIntegral.theta σ * ((A 1 0 : ℂ) * σ + A 1 1) ^ m * hXm
    exact (mul_eq_zero.mp key).resolve_right hjσ0
  have := eq_zero_of_mul_theta_eq_zero hcont hzero τ
  simp only [G, sub_eq_zero] at this
  rw [this]

end ModularFormsKB.Miyake.Sec4_9

namespace ModularFormsKB.HalfIntegral

open ModularFormsKB.Miyake.Sec4_9

/-- **Shimura's twisted theta law for every character** (Shimura 1973, Prop. 2.2; Miyake,
Corollary 4.9.7 (1)): for `r ≥ 1`, every Dirichlet character `ψ` modulo `r` (primitive or not)
of parity `ν`, `t ≥ 1` and `γ ∈ Γ₀(4 t r²)`,
`θ_{ψ,t}(γτ) = ψ̄(d) (t / |d|) (cτ + d)^ν j(γ, τ) θ_{ψ,t}(τ)`, `j` the theta multiplier. -/
@[kb "shimura1973" "Prop. 2.2: the twisted theta series theta(z; psi) of weight 1/2 + nu on Gamma0(4 t r^2), every character psi mod r (proved)"]
theorem thetaTwist_law {r : ℕ} (ψ : DirichletCharacter ℂ r) (hr : 1 ≤ r) {t : ℕ} (ht : 1 ≤ t)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 (4 * t * r ^ 2)) (τ : ℍ) :
    thetaTwist ψ t ((γ • τ : ℍ) : ℂ) = ψ⁻¹ (γ 1 1 : ZMod r) * (jacobiSym t (γ 1 1).natAbs : ℂ) *
      ((γ 1 0 : ℂ) * τ + γ 1 1) ^ charParity ψ * thetaMult γ τ * thetaTwist ψ t τ := by
  have : NeZero r := ⟨by omega⟩
  have hγ4 : γ ∈ CongruenceSubgroup.Gamma0 4 := by
    have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
    exact CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr
      (dvd_trans (by exact_mod_cast (⟨t * r ^ 2, by ring⟩ : (4 : ℕ) ∣ 4 * t * r ^ 2)) h)
  rw [thetaTwist_eq_sum ψ ht hr, thetaLat_smul ψ ht hr hγ, thetaTwist_eq_sum ψ ht hr]
  set ν := charParity ψ
  set X : ℂ := (ZMod.χ₄ (γ 1 1 : ZMod 4) : ℂ)
  set j := thetaMult γ τ
  set D : ℂ := (γ 1 0 : ℂ) * τ + γ 1 1
  have hX : X ^ 2 = 1 := by
    have h2 : (γ 1 1) % 2 = 1 := Int.odd_iff.mp (Gamma0_four_odd hγ4)
    have h := chi4_int_sq h2
    simp only [X]
    exact_mod_cast h
  have hj2 : j ^ 2 = X * D := thetaMult_sq hγ4 τ
  have hD : D ^ ν * j = X ^ ν * j ^ (2 * ν + 1) := by
    have : D = X * j ^ 2 := by rw [hj2, ← mul_assoc, ← sq, hX, one_mul]
    rw [this, mul_pow, ← pow_mul, pow_succ]
    ring
  -- the character
  have hcopN : IsCoprime (γ 1 1) (4 * t * r ^ 2 : ℕ) := by
    obtain ⟨u, hu⟩ := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := γ.det_coe
      rwa [Matrix.det_fin_two] at h
    exact ⟨γ 0 0, -(γ 0 1 * u), by linear_combination hdet + γ 0 1 * hu⟩
  have hcopL : IsCoprime (γ 1 1) (ZLattice.level (twistLattice₂ ht hr)) := by
    obtain ⟨m, hm⟩ := level_twistLattice₂_dvd ht hr
    have := hcopN
    rw [hm] at this
    push_cast at this
    exact this.of_mul_right_left
  have hχ : twistChar ψ ht hr (γ 1 1) =
      (TauCeti.kroneckerSym (-(4 * t * r ^ 2 : ℤ)) (γ 1 1) : ℂ) * ψ⁻¹ (γ 1 1 : ZMod r) := by
    rw [twistChar, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcopN,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hcopN,
      (isEven_twistLattice₂ ht hr).thetaCharacter_intCast even_finrank_twist₂ hcopL,
      signedDiscr_twistLattice₂]
  have hKX := kronecker_twist_mul_chi4 ht hr hcopN
  rw [hχ]
  linear_combination (ψ⁻¹ (γ 1 1 : ZMod r) * X ^ ν * j ^ (2 * ν + 1) *
      ((((√(2 * t) : ℝ) : ℂ) ^ ν)⁻¹ * thetaLat ψ ht hr τ)) * hKX -
    (ψ⁻¹ (γ 1 1 : ZMod r) * (jacobiSym t (γ 1 1).natAbs : ℂ) *
      ((((√(2 * t) : ℝ) : ℂ) ^ ν)⁻¹ * thetaLat ψ ht hr τ)) * hD +
    0 * hX

/-- **`ThetaTwistLaw` holds for the theta multiplier** (headline 2, first half). -/
@[kb "shimura1973" "Prop. 2.2 for the theta multiplier: ThetaTwistLaw thetaMultiplierSystem (proved)"]
theorem thetaTwistLaw_thetaMultiplierSystem : ThetaTwistLaw thetaMultiplierSystem where
  law r ψ t ht hr γ hγ τ := by simpa using thetaTwist_law ψ hr ht hγ τ
  j_sq γ hγ τ := by simpa using thetaMult_sq hγ τ

end ModularFormsKB.HalfIntegral
