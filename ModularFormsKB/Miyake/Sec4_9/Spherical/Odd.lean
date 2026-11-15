import ModularFormsKB.Miyake.Sec4_9.Spherical.Forms
import ModularFormsKB.HalfIntegral.Abstract.ThetaInstance
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality

/-!
# Spherical theta series of odd rank: the half-integral weight law (Miyake §4.9, odd rank)

Miyake, *Modular Forms* (Springer 1989), Theorem 4.9.3 and Corollary 4.9.4 for odd rank `r`.
Miyake's Corollary 4.9.4 is stated for even `r`; the plan's headline 1 asks for every rank, with the half-integral weight space `HalfIntegral.halfIntModularForms`
(Shimura's `M_{k+1/2}(4N, χ)`, theta multiplier `thetaMult`) as the target in odd rank.

**Route (doubling).** Adjoin the even lattice `√2 ℤ ⊆ ℝ`, whose theta series is our `HalfIntegral.theta`
(`thetaSeries_span_sqrt_two`): `L ⊕ √2ℤ` is even of even rank `n + 1`, and its spherical theta series
with the weight `P ⊕ 0` is `θ_L(·; P) · θ` (`thetaSph_orthSum`). The even-rank law
(`IsEvenSph.thetaSph_slash_of_mem_Gamma0`) and the law `θ(γτ) = j(γ, τ) θ(τ)` on `Γ₀(4)`
(`HalfIntegral.theta_transformationLaw`) give `(F(γτ) - c j^{2m-1} F(τ)) θ(τ) = 0` for
`F = θ_L(·; P)`; since `θ` is holomorphic and not identically zero, its zeros have empty interior,
and the continuous factor vanishes identically (`eq_of_mul_theta_eq_zero`).
-/

open Complex Module Filter Topology
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

/-! ### The lattice `√2 ℤ` and its theta series -/

/-- The basis `(√2)` of `ℝ`. -/
noncomputable def sqrtTwoBasis : Module.Basis (Fin 1) ℝ ℝ :=
  (Module.Basis.singleton (Fin 1) ℝ).unitsSMul fun _ ↦ Units.mk0 √2 (Real.sqrt_ne_zero'.mpr two_pos)

/-- The lattice `√2 ℤ ⊆ ℝ`, as the span of a basis (so that it carries Mathlib's lattice
instances). -/
noncomputable abbrev sqrtTwoLattice : Submodule ℤ ℝ := Submodule.span ℤ (Set.range sqrtTwoBasis)

theorem sqrtTwoLattice_eq : sqrtTwoLattice = Submodule.span ℤ {√2} := by
  rw [sqrtTwoLattice, Set.range_unique]
  congr 2
  simp [sqrtTwoBasis, Module.Basis.unitsSMul_apply]

theorem isEven_sqrtTwoLattice : ZLattice.IsEven sqrtTwoLattice := by
  rw [sqrtTwoLattice_eq]; exact ZLattice.isEven_span_sqrt_two

theorem level_sqrtTwoLattice : ZLattice.level sqrtTwoLattice = 4 := by
  rw [sqrtTwoLattice_eq]; exact ZLattice.level_span_sqrt_two

/-- The theta series of `√2 ℤ` is `θ(τ) = ∑ e(n² τ)`. -/
theorem thetaSeries_span_sqrt_two (τ : ℍ) :
    ZLattice.thetaSeries sqrtTwoLattice τ = HalfIntegral.theta τ := by
  have h2 : (√2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  rw [sqrtTwoLattice_eq, ZLattice.thetaSeries_apply, HalfIntegral.theta_eq_tsum,
    ← (LinearEquiv.toSpanNonzeroSingleton ℤ ℝ √2 h2).toEquiv.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.toSpanNonzeroSingleton_apply]
  have hn : ‖n • (√2 : ℝ)‖ ^ 2 = 2 * (n : ℝ) ^ 2 := by
    rw [zsmul_eq_mul, norm_mul, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      Real.sq_sqrt zero_le_two]
    ring
  congr 1
  rw [hn]
  push_cast
  ring

theorem thetaW_one_span_sqrt_two (τ : ℍ) :
    thetaW sqrtTwoLattice (fun _ ↦ 1) 0 τ = HalfIntegral.theta τ := by
  rw [thetaW_one, ZLattice.thetaCoset_zero, thetaSeries_span_sqrt_two]

/-! ### The doubled lattice -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The spherical datum on `E ⊕ ℝ` extended by `0`. -/
noncomputable def extVec (u : E) : WithLp 2 (E × ℝ) := WithLp.toLp 2 (u, 0)

theorem isoForm_extVec (u w : E) (x : WithLp 2 (E × ℝ)) :
    isoForm (extVec u) (extVec w) x = isoForm u w x.fst := by
  simp [isoForm, extVec, WithLp.prod_inner_apply]

theorem isSphericalDatum_extVec {ν : ℕ} {u w : E} (h : IsSphericalDatum ν u w) :
    IsSphericalDatum ν (extVec u) (extVec w) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, ?_⟩
    · have hu : ‖extVec u‖ ^ 2 = ‖u‖ ^ 2 := by rw [extVec, WithLp.prod_norm_sq_eq_of_L2]; simp
      have hw : ‖extVec w‖ ^ 2 = ‖w‖ ^ 2 := by rw [extVec, WithLp.prod_norm_sq_eq_of_L2]; simp
      have : ‖u‖ ^ 2 = ‖w‖ ^ 2 := by rw [h1]
      nlinarith [norm_nonneg (extVec u), norm_nonneg (extVec w), sq_nonneg (‖extVec u‖ - ‖extVec w‖),
        sq_nonneg (‖extVec u‖ + ‖extVec w‖)]
    · simp [extVec, WithLp.prod_inner_apply, h2]

theorem finrank_withLp_prod_real :
    finrank ℝ (WithLp 2 (E × ℝ)) = finrank ℝ E + 1 := by
  rw [(WithLp.linearEquiv 2 ℝ (E × ℝ)).finrank_eq, Module.finrank_prod, Module.finrank_self]

variable (L : Submodule ℤ E) [DiscreteTopology L]

/-- **Doubling.** `θ_{(γ, 0) + (L ⊕ √2ℤ)}(·; P ⊕ 0) = θ_{γ+L}(·; P) · θ`. -/
theorem thetaSph_orthSum (ν : ℕ) (u w γ : E) (τ : ℍ) :
    thetaSph (ZLattice.orthSum L sqrtTwoLattice) ν (extVec u) (extVec w) (extVec γ) τ =
      thetaSph L ν u w γ τ * HalfIntegral.theta τ := by
  rw [← thetaW_one_span_sqrt_two, thetaSph, thetaSph, thetaW_apply, thetaW_apply, thetaW_apply,
    tsum_mul_tsum_of_summable_norm (summable_norm_thetaW L (polyBounded_isoForm_pow u w ν) γ τ)
      (summable_norm_thetaW sqrtTwoLattice polyBounded_one 0 τ),
    ← (ZLattice.orthSumEquivProd L sqrtTwoLattice).symm.toEquiv.tsum_eq]
  refine tsum_congr fun p ↦ ?_
  simp only [LinearEquiv.coe_toEquiv, ZLattice.coe_orthSumEquivProd_symm_apply, isoForm_extVec]
  rw [one_mul, zero_add]
  have hn : ‖extVec γ + WithLp.toLp 2 ((p.1 : E), (p.2 : ℝ))‖ ^ 2 =
      ‖γ + (p.1 : E)‖ ^ 2 + ‖(p.2 : ℝ)‖ ^ 2 := by
    simp [extVec, WithLp.prod_norm_sq_eq_of_L2]
  have hf : (extVec γ + WithLp.toLp 2 ((p.1 : E), (p.2 : ℝ))).fst = γ + p.1 := by simp [extVec]
  rw [hf, hn]
  push_cast
  rw [show (π : ℂ) * I * (‖γ + (p.1 : E)‖ ^ 2 + ‖(p.2 : ℝ)‖ ^ 2) * τ =
      π * I * ‖γ + (p.1 : E)‖ ^ 2 * τ + π * I * ‖(p.2 : ℝ)‖ ^ 2 * τ by ring, Complex.exp_add]
  ring

omit [FiniteDimensional ℝ E] in
theorem extVec_zero : extVec (0 : E) = 0 := by simp [extVec]

/-! ### Division by `θ` -/

/-- `θ` vanishes on no nonempty open subset of `ℍ`: a continuous `G` with `G θ = 0` is `0`. -/
theorem eq_zero_of_mul_theta_eq_zero {G : ℍ → ℂ} (hG : Continuous G)
    (h : ∀ τ : ℍ, G τ * HalfIntegral.theta τ = 0) (τ : ℍ) : G τ = 0 := by
  by_contra hne
  set U : Set ℍ := {σ | G σ ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hG continuous_const
  have hV : IsOpen (((↑) : ℍ → ℂ) '' U) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hU
  have hev : HalfIntegral.theta =ᶠ[𝓝 (τ : ℂ)] 0 := by
    filter_upwards [hV.mem_nhds ⟨τ, hne, rfl⟩] with z hz
    obtain ⟨σ, hσ, rfl⟩ := hz
    exact (mul_eq_zero.mp (h σ)).resolve_left hσ
  have han : AnalyticOnNhd ℂ HalfIntegral.theta {z : ℂ | 0 < z.im} :=
    HalfIntegral.theta_differentiableOn.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_im)
  have hpre : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre τ.im_pos hev
  have hz : (2 * I : ℂ) ∈ {z : ℂ | 0 < z.im} := by simp
  exact HalfIntegral.theta_ne_zero_of_one_lt_im (z := 2 * I) (by norm_num) (heq hz)

/-! ### The law in odd rank -/

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

theorem isEven_orthSum_sqrtTwo (hL : ZLattice.IsEven L) :
    ZLattice.IsEven (ZLattice.orthSum L sqrtTwoLattice) :=
  ZLattice.isEven_orthSum_iff.mpr ⟨hL, isEven_sqrtTwoLattice⟩

theorem four_dvd_level_orthSum : 4 ∣ ZLattice.level (ZLattice.orthSum L sqrtTwoLattice) := by
  rw [ZLattice.level_orthSum, level_sqrtTwoLattice]
  exact Nat.dvd_lcm_right _ _

theorem level_orthSum_dvd : ZLattice.level (ZLattice.orthSum L sqrtTwoLattice) ∣ 4 * ZLattice.level L := by
  rw [ZLattice.level_orthSum, level_sqrtTwoLattice]
  exact Nat.lcm_dvd (Dvd.intro_left 4 rfl) (Dvd.intro (ZLattice.level L) rfl)

/-- **Theorem 4.9.3 in odd rank `n = 2k + 1`** (spherical weight of degree `ν`, `m = k + ν + 1`):
for `A ∈ Γ₀(N')`, `N'` the level of `L ⊕ √2ℤ` (a multiple of `4` dividing `4 N`),
`θ_L(Aτ; P) = χ'(d) χ_{-4}(d)^m j(A, τ)^{2(k+ν)+1} θ_L(τ; P)`, with `χ'` the theta character of
`L ⊕ √2ℤ` and `j` the theta multiplier. -/
theorem thetaSph_smul_of_odd (hL : ZLattice.IsEven L) {k : ℕ} (hk : finrank ℝ E = 2 * k + 1)
    {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 (ZLattice.level (ZLattice.orthSum L sqrtTwoLattice)))
    (τ : ℍ) :
    thetaSph L ν u w 0 (A • τ) =
      (isEven_orthSum_sqrtTwo hL).thetaCharacter
          ⟨k + 1, by rw [finrank_withLp_prod_real, hk]; ring⟩ (A 1 1 : ℤ) *
        (ZMod.χ₄ (A 1 1 : ZMod 4) : ℂ) ^ (k + ν + 1) *
        HalfIntegral.thetaMult A τ ^ (2 * (k + ν) + 1) * thetaSph L ν u w 0 τ := by
  borelize E
  have hL' := isEven_orthSum_sqrtTwo hL
  have hk' : finrank ℝ (WithLp 2 (E × ℝ)) = 2 * (k + 1) := by
    rw [finrank_withLp_prod_real, hk]; ring
  have hA4 : A ∈ CongruenceSubgroup.Gamma0 4 := by
    have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hA
    exact CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr
      (dvd_trans (Int.natCast_dvd_natCast.mpr four_dvd_level_orthSum) h)
  set χ' := hL'.thetaCharacter ⟨k + 1, by rw [finrank_withLp_prod_real, hk]; ring⟩ (A 1 1 : ℤ)
  set X : ℂ := (ZMod.χ₄ (A 1 1 : ZMod 4) : ℂ)
  have hX : X ^ 2 = 1 := by
    have hodd := HalfIntegral.Gamma0_four_odd hA4
    have h2 : (A 1 1) % 2 = 1 := Int.odd_iff.mp hodd
    have hχ := ZMod.χ₄_int_eq_if_mod_four (A 1 1)
    simp only [X]
    rw [hχ]
    split_ifs <;> simp_all
  set j := HalfIntegral.thetaMult A τ
  set D : ℂ := (A 1 0 : ℂ) * τ + A 1 1
  have hj2 : j ^ 2 = X * D := HalfIntegral.thetaMult_sq hA4 τ
  have hj0 : j ≠ 0 := HalfIntegral.thetaMultiplierSystem.ne_zero A hA4 τ
  -- The law of the doubled series, pointwise.
  have hF := congrFun (IsEvenSph.thetaSph_slash_of_mem_Gamma0 hL' hk'
    (isSphericalDatum_extVec hsph) hA)
  have hθ := HalfIntegral.theta_transformationLaw A hA4
  -- `G` is the difference of the two sides; `G θ = 0` everywhere.
  set m := k + ν + 1
  let G : ℍ → ℂ := fun σ ↦ thetaSph L ν u w 0 (A • σ) -
    χ' * X ^ m * HalfIntegral.thetaMult A σ ^ (2 * (k + ν) + 1) * thetaSph L ν u w 0 σ
  have hcont : Continuous G := by
    have h1 : Continuous (thetaSph L ν u w 0) :=
      (mdifferentiable_thetaW L (polyBounded_isoForm_pow u w ν) 0).continuous
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
    rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, ← extVec_zero, thetaSph_orthSum,
      thetaSph_orthSum, ModularGroup.denom_apply] at hFσ
    rw [hθ σ] at hFσ
    have hD0 : ((A 1 0 : ℂ) * σ + A 1 1) ≠ 0 := by
      simpa [ModularGroup.denom_apply] using UpperHalfPlane.denom_ne_zero A σ
    rw [zpow_neg, zpow_natCast, show k + 1 + ν = m by ring] at hFσ
    have h1 : thetaSph L ν u w 0 (A • σ) * (HalfIntegral.thetaMult A σ * HalfIntegral.theta σ) =
        χ' * (thetaSph L ν u w 0 σ * HalfIntegral.theta σ) * ((A 1 0 : ℂ) * σ + A 1 1) ^ m := by
      rw [← hFσ, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hD0), mul_one]
    have hjpow : HalfIntegral.thetaMult A σ ^ (2 * (k + ν) + 1) * HalfIntegral.thetaMult A σ =
        X ^ m * ((A 1 0 : ℂ) * σ + A 1 1) ^ m := by
      rw [← pow_succ, show 2 * (k + ν) + 1 + 1 = 2 * m by ring, pow_mul, hjσ2, mul_pow]
    have hXm : X ^ m * X ^ m = 1 := by rw [← pow_add, ← two_mul, pow_mul, hX, one_pow]
    have key : (G σ * HalfIntegral.theta σ) * HalfIntegral.thetaMult A σ = 0 := by
      simp only [G]
      linear_combination h1 - χ' * X ^ m * thetaSph L ν u w 0 σ * HalfIntegral.theta σ * hjpow -
        χ' * thetaSph L ν u w 0 σ * HalfIntegral.theta σ * ((A 1 0 : ℂ) * σ + A 1 1) ^ m * hXm
    exact (mul_eq_zero.mp key).resolve_right hjσ0
  have := eq_zero_of_mul_theta_eq_zero hcont hzero τ
  simp only [G, sub_eq_zero] at this
  rw [this]

/-! ### Membership in `M_{k+ν+1/2}(4N, χ)` -/

/-- `χ_{-4}` as a complex Dirichlet character modulo `4`. -/
noncomputable def chi4C : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- The character of the odd-rank spherical theta series, modulo `4 N` (`N` the level of `L`):
`χ(d) = χ'(d) χ_{-4}(d)^{k+ν+1}`, `χ'` the theta character of `L ⊕ √2ℤ`. -/
noncomputable def oddThetaChar (hL : ZLattice.IsEven L) {k : ℕ} (hk : finrank ℝ E = 2 * k + 1)
    (ν : ℕ) : DirichletCharacter ℂ (4 * ZLattice.level L) :=
  ((isEven_orthSum_sqrtTwo hL).thetaCharacter
      ⟨k + 1, by rw [finrank_withLp_prod_real, hk]; ring⟩).changeLevel level_orthSum_dvd *
    (chi4C.changeLevel (Dvd.intro (ZLattice.level L) rfl)) ^ (k + ν + 1)

theorem oddThetaChar_apply (hL : ZLattice.IsEven L) {k : ℕ} (hk : finrank ℝ E = 2 * k + 1)
    (ν : ℕ) {d : ℤ} (hd : IsCoprime d (4 * ZLattice.level L : ℕ)) :
    oddThetaChar hL hk ν (d : ZMod (4 * ZLattice.level L)) =
      (isEven_orthSum_sqrtTwo hL).thetaCharacter
          ⟨k + 1, by rw [finrank_withLp_prod_real, hk]; ring⟩ (d : ℤ) *
        (ZMod.χ₄ (d : ZMod 4) : ℂ) ^ (k + ν + 1) := by
  rw [oddThetaChar, MulChar.mul_apply, MulChar.pow_apply' _ (by omega),
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hd]
  simp [chi4C, MulChar.ringHomComp_apply]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
theorem cuspNorm_eq_absSlash {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) {ν : ℕ} (f : ℍ → ℂ)
    (γ : SL(2, ℤ)) :
    HalfIntegral.cuspNorm (k + ν) (fun τ ↦ f τ) γ = absSlash ((ν : ℝ) + finrank ℝ E / 2) f γ := by
  funext τ
  simp only [HalfIntegral.cuspNorm, absSlash, hk]
  congr 2
  push_cast
  ring

/-- **Miyake, Theorem 4.9.3 and Corollary 4.9.4 in odd rank** (headline 1, odd rank): for an even
full lattice `L` of rank `2k + 1` and level `N` and a spherical weight `P` of degree `ν`, the theta
series `θ_L(·; P)` lies in Shimura's `M_{k+ν+1/2}(4N, χ)`, `χ = oddThetaChar`. -/
@[kb "miyake1989" "Theorem 4.9.3 / Corollary 4.9.4 in odd rank: theta series with a spherical function in M_{r/2+nu}(Gamma0(4N), chi), half-integral weight (lattice form)"]
theorem thetaSph_mem_halfIntModularForms (hL : ZLattice.IsEven L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k + 1) {ν : ℕ} {u w : E} (hsph : IsSphericalDatum ν u w) :
    (fun τ : ℍ ↦ thetaSph L ν u w 0 τ) ∈
      HalfIntegral.halfIntModularForms (k + ν) (ZLattice.level L) (oddThetaChar hL hk ν) := by
  borelize E
  refine ⟨mdifferentiable_thetaW L (polyBounded_isoForm_pow u w ν) 0, fun γ hγ τ ↦ ?_, fun γ ↦ ?_⟩
  · have hγ' : γ ∈ CongruenceSubgroup.Gamma0 (ZLattice.level (ZLattice.orthSum L sqrtTwoLattice)) := by
      have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
      exact CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr
        (dvd_trans (Int.natCast_dvd_natCast.mpr level_orthSum_dvd) h)
    have hd : IsCoprime (γ 1 1) (4 * ZLattice.level L : ℕ) := by
      obtain ⟨t, ht⟩ := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hγ
      have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
        have h := γ.det_coe
        rwa [Matrix.det_fin_two] at h
      refine ⟨γ 0 0, -(γ 0 1 * t), ?_⟩
      linear_combination hdet + γ 0 1 * ht
    rw [thetaSph_smul_of_odd hL hk hsph hγ' τ, oddThetaChar_apply hL hk ν hd]
  · rw [cuspNorm_eq_absSlash hk]
    exact isBoundedAtImInfty_absSlash_thetaSph hL hsph γ (zero_mem _)

/-- **Headline 1, odd rank, cusp forms:** for `ν ≥ 1` the odd-rank spherical theta series lies in
Shimura's `S_{k+ν+1/2}(4N, χ)`. -/
@[kb "miyake1989" "Corollary 4.9.4 in odd rank: for nu >= 1 the theta series with a spherical function is a cusp form of half-integral weight (lattice form)"]
theorem thetaSph_mem_halfIntCuspForms (hL : ZLattice.IsEven L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k + 1) {ν : ℕ} (hν : 1 ≤ ν) {u w : E} (hsph : IsSphericalDatum ν u w) :
    (fun τ : ℍ ↦ thetaSph L ν u w 0 τ) ∈
      HalfIntegral.halfIntCuspForms (k + ν) (ZLattice.level L) (oddThetaChar hL hk ν) := by
  borelize E
  obtain ⟨h1, h2, -⟩ := thetaSph_mem_halfIntModularForms hL hk hsph
  refine ⟨h1, h2, fun γ ↦ ?_⟩
  rw [cuspNorm_eq_absSlash hk]
  exact isZeroAtImInfty_absSlash_thetaSph hL hν hsph γ (zero_mem _)

end ModularFormsKB.Miyake.Sec4_9
