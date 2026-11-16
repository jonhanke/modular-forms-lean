import ModularFormsKB.ThetaGenus.Genus
import ModularFormsKB.Miyake.Sec4_9.Spherical.OddLevel

/-!
# Theta series of one genus differ by a cusp form, in every rank

Let `L ⊆ E` and `M ⊆ F` be even full lattices of the same rank `n` in one genus (`SameGenus`, the
congruence form of the genus), and let `N` be a common multiple of their levels. Write
`θ_L(τ) = ∑_{v ∈ L} exp (π i ‖v‖² τ)`, which is `∑ q^{Q(v)}` for `Q = ‖·‖²/2`.

* **Even rank** `n = 2k` (`sameGenus_thetaSph_sub_cuspForm`): `θ_L - θ_M` is a cusp form of
  weight `k` on `Γ₁(N)`.
* **Odd rank** `n = 2k + 1` (`sameGenus_thetaSph_sub_mem_halfIntCuspForms`): for `level ∣ 4N`,
  `θ_L - θ_M ∈ S_{k+1/2}(4N, χ)` (Shimura's space, theta multiplier), `χ = oddThetaCharOf`, the
  common character (`oddThetaCharOf_eq_of_sameGenus`).

**Proof.** Both series are modular forms (Miyake, Theorem 4.9.3, formalized in `Miyake.Sec4_9.Spherical`),
so only the vanishing at every cusp is new. In even rank the constant term of `θ_L` at the cusp
`a/c` is `(-i)^k c^{-k} (covol L)⁻¹ G_L(a, c)` (`ConstantTerm.lean`). The covolume and the Gauss sums
are genus invariants (`Genus.lean`). In odd rank the square of the difference is
`(θ_{L⊕L} - θ_{L⊕M}) - (θ_{M⊕L} - θ_{M⊕M})`, a combination of theta series of lattices of even rank
`2n`, with `L ⊕ L ~ L ⊕ M` and `M ⊕ L ~ M ⊕ M` in one genus (`SameGenus.orthSum_left`). The
weight-`n` cusp quantity of the square is the square of the weight-`(k + 1/2)` cusp quantity of the
difference.
-/

open Complex Module Filter Topology
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.ThetaGenus

open ModularFormsKB.Miyake.Sec4_9

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {M : Submodule ℤ F} [DiscreteTopology M] [IsZLattice ℝ M]

theorem finrank_withLp_prod :
    finrank ℝ (WithLp 2 (E × F)) = finrank ℝ E + finrank ℝ F := by
  rw [(WithLp.linearEquiv 2 ℝ (E × F)).finrank_eq, Module.finrank_prod]

/-- **Same genus ⇒ the difference vanishes at every cusp** (even rank `2k`, weight `k`). -/
theorem SameGenus.tendsto_slash_sub (h : SameGenus L M) (hL : ZLattice.IsEven L)
    (hM : ZLattice.IsEven M) {k : ℕ} (hk : finrank ℝ E = 2 * k) (hkM : finrank ℝ F = 2 * k)
    (A : SL(2, ℤ)) :
    Tendsto ((thetaSph L 0 0 0 0 - thetaSph M 0 0 0 0) ∣[(k : ℤ)] A) UpperHalfPlane.atImInfty
      (𝓝 0) :=
  tendsto_slash_sub_of_gaussSum_eq hL hM hk hkM h.covolume_eq
    (fun a c _ ↦ h.gaussSum_eq hL hM a c) A

/-! ### Even rank -/

theorem thetaSph_zero_slash_of_mem_Gamma1 (hL : ZLattice.IsEven L) {k : ℕ}
    (hk : finrank ℝ E = 2 * k) {N : ℕ} (hN : ZLattice.level L ∣ N) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma1 N) :
    thetaSph L 0 0 0 0 ∣[(k : ℤ)] A = thetaSph L 0 0 0 0 := by
  have hsph : IsSphericalDatum 0 (0 : E) 0 := Or.inl zero_le_one
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 (ZLattice.level L) := by
    have h := CongruenceSubgroup.Gamma1_in_Gamma0 N hA
    rw [CongruenceSubgroup.mem_Gamma0_iff_dvd] at h ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hN) h
  have h := IsEvenSph.thetaSph_slash_of_mem_Gamma0 hL hk hsph hA0
  have hd : ((A 1 1 : ℤ) : ZMod (ZLattice.level L)) = 1 := by
    have h1 := (CongruenceSubgroup.mem_Gamma1_iff.mp hA).2
    have h2 := congrArg (ZMod.castHom hN (ZMod (ZLattice.level L))) h1
    rwa [map_one, map_intCast] at h2
  rw [hd, map_one, one_smul] at h
  simpa using h

/-- **Headline H5, even rank.** Theta series of even lattices of rank `2k` in one genus differ by
a cusp form of weight `k` on `Γ₁(N)`, for every common multiple `N` of their levels. -/
@[kb "siegel1935" "theta series of lattices in one genus differ by a cusp form (even rank, lattice form; constant terms at the cusps are local Gauss sums)"]
theorem sameGenus_thetaSph_sub_cuspForm (h : SameGenus L M) (hL : ZLattice.IsEven L)
    (hM : ZLattice.IsEven M) {k : ℕ} (hk : finrank ℝ E = 2 * k) (hkM : finrank ℝ F = 2 * k)
    {N : ℕ} (hLN : ZLattice.level L ∣ N) (hMN : ZLattice.level M ∣ N) :
    ∃ f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k,
      ⇑f = thetaSph L 0 0 0 0 - thetaSph M 0 0 0 0 := by
  refine ⟨{ toFun := thetaSph L 0 0 0 0 - thetaSph M 0 0 0 0
            slash_action_eq' := ?_
            holo' := ?_
            zero_at_cusps' := ?_ }, rfl⟩
  · intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    rw [← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
      SlashAction.sub_slash, thetaSph_zero_slash_of_mem_Gamma1 hL hk hLN hA,
      thetaSph_zero_slash_of_mem_Gamma1 hM hkM hMN hA]
  · exact (mdifferentiable_thetaW L (polyBounded_isoForm_pow 0 0 0) 0).sub
      (mdifferentiable_thetaW M (polyBounded_isoForm_pow 0 0 0) 0)
  · intro c hc
    apply (OnePoint.isZeroAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))).mpr
    intro A _
    exact h.tendsto_slash_sub hL hM hk hkM A

/-! ### Odd rank -/

/-- Lattices in one genus have discriminant groups of the same order. -/
theorem SameGenus.card_discriminantGroup_eq (h : SameGenus L M) (hL : ZLattice.IsIntegral L)
    (hM : ZLattice.IsIntegral M) :
    Nat.card (ZLattice.DiscriminantGroup L) = Nat.card (ZLattice.DiscriminantGroup M) := by
  have h1 := hL.det_eq_card_discriminantGroup
  have h2 := hM.det_eq_card_discriminantGroup
  rw [ZLattice.det_def, h.covolume_eq, ← ZLattice.det_def, h2] at h1
  exact_mod_cast h1.symm

/-- **The two odd-rank characters agree** for lattices in one genus. -/
theorem oddThetaCharOf_eq_of_sameGenus (h : SameGenus L M) (hL : ZLattice.IsEven L)
    (hM : ZLattice.IsEven M) {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) (hkM : finrank ℝ F = 2 * k + 1)
    (ν : ℕ) {N : ℕ} [NeZero N] (hLN : ZLattice.level L ∣ 4 * N) (hMN : ZLattice.level M ∣ 4 * N) :
    oddThetaCharOf hM hkM ν hMN = oddThetaCharOf hL hk ν hLN := by
  have : NeZero (4 * N) := ⟨by have := NeZero.ne N; omega⟩
  refine MulChar.ext fun a ↦ ?_
  have hco : ((a : ZMod (4 * N)).val).Coprime (4 * N) := ZMod.val_coe_unit_coprime a
  have ha : (((a : ZMod (4 * N)).val : ℕ) : ZMod (4 * N)) = a := ZMod.natCast_zmod_val _
  rw [← ha, oddThetaCharOf_natCast hM hkM ν hMN hco, oddThetaCharOf_natCast hL hk ν hLN hco,
    h.card_discriminantGroup_eq hL.isIntegral hM.isIntegral]

/-- The weight-`(k + 1/2)` cusp quantity squared is the weight-`(2k + 1)` slash of the square. -/
theorem cuspNorm_sq_eq (k : ℕ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HalfIntegral.cuspNorm k f γ τ ^ 2 = ‖((f * f) ∣[((2 * k + 1 : ℕ) : ℤ)] γ) τ‖ := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, HalfIntegral.cuspNorm, mul_pow,
    norm_mul, Pi.mul_apply, norm_mul, norm_zpow, zpow_neg, zpow_natCast]
  have hA := norm_nonneg ((γ 1 0 : ℂ) * τ + γ 1 1)
  have key : (‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (-((k : ℝ) + 1 / 2))) ^ 2 =
      (‖(γ 1 0 : ℂ) * τ + γ 1 1‖ ^ (2 * k + 1))⁻¹ := by
    rw [← Real.rpow_natCast (_ ^ _) 2, ← Real.rpow_mul hA, ← Real.rpow_natCast _ (2 * k + 1),
      ← Real.rpow_neg hA]
    push_cast
    ring_nf
  rw [key]
  ring

/-- **Headline H5, odd rank.** Theta series of even lattices of rank `2k + 1` in one genus differ by
a cusp form in Shimura's `S_{k+1/2}(4N, χ)`, for every `N` with both levels dividing `4N`. -/
@[kb "siegel1935" "theta series of lattices in one genus differ by a cusp form (odd rank, half-integral weight, lattice form)"]
theorem sameGenus_thetaSph_sub_mem_halfIntCuspForms (h : SameGenus L M) (hL : ZLattice.IsEven L)
    (hM : ZLattice.IsEven M) {k : ℕ} (hk : finrank ℝ E = 2 * k + 1) (hkM : finrank ℝ F = 2 * k + 1)
    {N : ℕ} [NeZero N] (hLN : ZLattice.level L ∣ 4 * N) (hMN : ZLattice.level M ∣ 4 * N) :
    (fun τ : ℍ ↦ thetaSph L 0 0 0 0 τ - thetaSph M 0 0 0 0 τ) ∈
      HalfIntegral.halfIntCuspForms k N (oddThetaCharOf hL hk 0 hLN) := by
  have hsph : IsSphericalDatum 0 (0 : E) 0 := Or.inl zero_le_one
  have hsphM : IsSphericalDatum 0 (0 : F) 0 := Or.inl zero_le_one
  have h1 := thetaSph_mem_halfIntModularForms_of_dvd hL hk hsph hLN
  have h2 := thetaSph_mem_halfIntModularForms_of_dvd hM hkM hsphM hMN
  rw [oddThetaCharOf_eq_of_sameGenus h hL hM hk hkM 0 hLN hMN] at h2
  obtain ⟨hholo, htrans, -⟩ := Submodule.sub_mem _ h1 h2
  refine ⟨hholo, htrans, fun γ ↦ ?_⟩
  -- the square of the difference, through theta series of even rank `2(2k+1)`
  have hLL := (SameGenus.orthSum_left L h)
  have hML := (SameGenus.orthSum_left M h)
  have hEE : finrank ℝ (WithLp 2 (E × E)) = 2 * (2 * k + 1) := by
    rw [finrank_withLp_prod, hk]; ring
  have hEF : finrank ℝ (WithLp 2 (E × F)) = 2 * (2 * k + 1) := by
    rw [finrank_withLp_prod, hk, hkM]; ring
  have hFE : finrank ℝ (WithLp 2 (F × E)) = 2 * (2 * k + 1) := by
    rw [finrank_withLp_prod, hk, hkM]; ring
  have hFF : finrank ℝ (WithLp 2 (F × F)) = 2 * (2 * k + 1) := by
    rw [finrank_withLp_prod, hkM]; ring
  have eLL := ZLattice.isEven_orthSum_iff.mpr ⟨hL, hL⟩
  have eLM := ZLattice.isEven_orthSum_iff.mpr ⟨hL, hM⟩
  have eML := ZLattice.isEven_orthSum_iff.mpr ⟨hM, hL⟩
  have eMM := ZLattice.isEven_orthSum_iff.mpr ⟨hM, hM⟩
  have t1 := hLL.tendsto_slash_sub eLL eLM hEE hEF γ
  have t2 := hML.tendsto_slash_sub eML eMM hFE hFF γ
  have hsq : (fun τ : ℍ ↦ thetaSph L 0 0 0 0 τ - thetaSph M 0 0 0 0 τ) *
      (fun τ : ℍ ↦ thetaSph L 0 0 0 0 τ - thetaSph M 0 0 0 0 τ) =
      (thetaSph (ZLattice.orthSum L L) 0 0 0 0 - thetaSph (ZLattice.orthSum L M) 0 0 0 0) -
        (thetaSph (ZLattice.orthSum M L) 0 0 0 0 - thetaSph (ZLattice.orthSum M M) 0 0 0 0) := by
    rw [thetaSph_zero_orthSum, thetaSph_zero_orthSum, thetaSph_zero_orthSum, thetaSph_zero_orthSum]
    funext τ
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  have t : Tendsto (((fun τ : ℍ ↦ thetaSph L 0 0 0 0 τ - thetaSph M 0 0 0 0 τ) *
      (fun τ : ℍ ↦ thetaSph L 0 0 0 0 τ - thetaSph M 0 0 0 0 τ)) ∣[((2 * k + 1 : ℕ) : ℤ)] γ)
      UpperHalfPlane.atImInfty (𝓝 0) := by
    have t0 := t1.sub t2
    rw [sub_zero] at t0
    refine t0.congr fun τ ↦ ?_
    rw [hsq]
    simp only [SlashAction.sub_slash, Pi.sub_apply]
  have tn := t.norm
  rw [norm_zero] at tn
  have tsq : Tendsto (fun τ ↦ HalfIntegral.cuspNorm k
      (fun τ : ℍ ↦ thetaSph L 0 0 0 0 τ - thetaSph M 0 0 0 0 τ) γ τ ^ 2)
      UpperHalfPlane.atImInfty (𝓝 0) := by
    refine tn.congr fun τ ↦ ?_
    rw [cuspNorm_sq_eq]
  have ts := (Real.continuous_sqrt.tendsto 0).comp tsq
  rw [Real.sqrt_zero] at ts
  refine ts.congr fun τ ↦ ?_
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (HalfIntegral.cuspNorm_nonneg _ _ _ _)

end ModularFormsKB.ThetaGenus
