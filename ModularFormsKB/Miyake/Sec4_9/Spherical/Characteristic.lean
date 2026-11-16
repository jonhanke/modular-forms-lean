import ModularFormsKB.Miyake.Sec4_9.Spherical.Forms

/-!
# Theta series with a characteristic and a spherical weight on `Γ₀(M)`

Miyake, *Modular Forms* (Springer 1989), Theorem 4.9.3 with a characteristic `h` (p. 191), in
lattice form and even rank. Let `L` be an even full lattice of rank `2k` and level `N`, `γ ∈ L^∨`
and `P = ⟪ζ, ·⟫^ν` a spherical weight.

* `thetaSph_coset_slash_of_pos`: for `A = !![a, b; c, d] ∈ SL(2, ℤ)` with `a > 0` odd, `c > 0`
  and `N ∣ c`, the Gauss sum of `thetaSph_slash_eq_gaussSum_smul` evaluated:
  `θ_{γ+L}(·; P) ∣[k + ν] A = ((-1)^k |L^∨/L| / a) e(a b ‖γ‖² / 2) θ_{aγ+L}(·; P)`.
* `thetaSph_coset_slash_of_mem_Gamma0`: **the characteristic law on `Γ₀(M)`.** Suppose
  `N ∣ M`, `‖γ‖²/2 ∈ ℤ`, and the classes `aγ + L` of `a` prime to `M` act on the series through a
  Dirichlet character `ψ` modulo `M`: `θ_{aγ+L}(·; P) = ψ(a) θ_{γ+L}(·; P)`, with
  `ψ(-1) = (-1)^ν`. Then for every `A ∈ Γ₀(M)`,
  `θ_{γ+L}(·; P) ∣[k + ν] A = (χ_L ψ⁻¹)(d) θ_{γ+L}(·; P)`, `χ_L` the theta character
  (Tau Ceti's `thetaCharacter`) raised to level `M`.
* `thetaSphCosetCuspForm`: under the same hypotheses and `ν ≥ 1`, a cusp form of weight `k + ν`
  on `Γ₀(M)` (the cusp condition is `isZeroAtImInfty_absSlash_thetaSph`, which holds for every
  `γ ∈ L^∨`).

The hypothesis on `ψ` is where the characteristic enters: Miyake's theorem gives
`θ_h ∣ A = χ(d) e(ab Q(h)) θ_{ah}`, and a single coset is an eigenform of `Γ₀(M)` exactly when `a ↦ θ_{ah}`
is a character. The Gram-matrix form of row 7 (Iwaniec Theorem 10.9) is not done here: loose end.
-/

open Complex Module
open scoped Real RealInnerProductSpace ModularForm UpperHalfPlane MatrixGroups

set_option linter.unusedSectionVars false

namespace ModularFormsKB.Miyake.Sec4_9

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace IsEvenSph

variable [MeasurableSpace E] [BorelSpace E] {L : Submodule ℤ E} [DiscreteTopology L]
  [IsZLattice ℝ L] {k : ℕ} (hL : ZLattice.IsEven L)
include hL

/-- **Miyake, Theorem 4.9.3 with a characteristic (even rank, Gauss sum evaluated).** For
`A = !![a, b; c, d]` with `a > 0` odd, `c > 0` and `N ∣ c`:
`θ_{γ+L}(·; P) ∣[k + ν] A = ((-1)^k |L^∨/L| / a) e(a b ‖γ‖² / 2) θ_{aγ+L}(·; P)`. -/
theorem thetaSph_coset_slash_of_pos (hk : finrank ℝ E = 2 * k) {ν : ℕ} {u w : E}
    (hsph : IsSphericalDatum ν u w) (A : SL(2, ℤ)) {a c : ℕ} (ha : A 0 0 = a) (hc : A 1 0 = c)
    (haodd : Odd a) (hc0 : 0 < c) (hN : ZLattice.level L ∣ c) (γ : ZLattice.dual L) :
    thetaSph L ν u w γ ∣[((k + ν : ℕ) : ℤ)] A =
      ((jacobiSym ((-1) ^ k * Nat.card (ZLattice.DiscriminantGroup L)) a : ℂ) *
        cexp (2 * π * I * ((a * A 0 1 * ‖(γ : E)‖ ^ 2 / 2 : ℝ) : ℂ))) •
        thetaSph L ν u w ((a : ℝ) • (γ : E)) := by
  classical
  haveI : NeZero c := ⟨hc0.ne'⟩
  have hac : a.Coprime c := by
    have h := A.isCoprime_col 0
    rw [ha, hc] at h
    exact Nat.isCoprime_iff_coprime.mp h
  have h := thetaSph_slash_eq_gaussSum_smul hL hk hsph A hc hN γ
  have hz : (A 0 0 : ℤ) • (γ : E) = (a : ℝ) • (γ : E) := by
    rw [ha, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  rw [h, hz]
  congr 1
  have hn := hL.normalized_gaussSum_eq_jacobiSym hk haodd hN hac
  rw [ha]
  push_cast at hn ⊢
  rw [← hn]

/-- The theta series of `γ + L` is invariant under `T` when `‖γ‖²/2` is an integer. -/
theorem thetaSph_coset_slash_T {ν : ℕ} (u w : E) {γ : E} (hγ : γ ∈ ZLattice.dual L)
    (hnorm : ∃ m : ℤ, ‖γ‖ ^ 2 = 2 * m) (j : ℤ) :
    thetaSph L ν u w γ ∣[j] ModularGroup.T = thetaSph L ν u w γ := by
  obtain ⟨m, hm⟩ := hnorm
  ext τ
  have := TauCeti.ModularForm.slash_T_zpow_apply j 1 (thetaSph L ν u w γ) τ
  simp only [zpow_one] at this
  rw [this, Int.cast_one]
  rw [thetaSph, thetaW_vadd_eq_mul L _ γ (fun v hv ↦ ?_) τ]
  · rw [← thetaSph]
    have he : cexp (π * I * ((‖γ‖ ^ 2 : ℝ) : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [hm]
      have : (π : ℂ) * I * (((2 * m : ℝ)) : ℂ) * ((1 : ℝ) : ℂ) = (m : ℂ) * (2 * π * I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [he, one_mul]
  · obtain ⟨n, hn⟩ := ZLattice.isEven_iff.mp hL v hv
    have hip : ∃ z : ℤ, ⟪γ, v⟫ = z := by
      have := (ZLattice.mem_dual (L := L)).mp hγ v hv
      exact this
    obtain ⟨z, hz⟩ := hip
    refine ⟨z + n, ?_⟩
    rw [norm_add_sq_real, hz, hn]
    push_cast
    ring

/-- **The characteristic law on `Γ₀(M)` (Miyake, Theorem 4.9.3 with a characteristic, lattice
form, even rank).** If `N ∣ M`, `‖γ‖²/2 ∈ ℤ`, and `θ_{aγ+L}(·; P) = ψ(a) θ_{γ+L}(·; P)` for every `a`
prime to `M`, with `ψ(-1) = (-1)^ν`, then for `A ∈ Γ₀(M)`:
`θ_{γ+L}(·; P) ∣[k + ν] A = (χ_L ψ⁻¹)(d) θ_{γ+L}(·; P)`. -/
@[kb "miyake1989" "Theorem 4.9.3 with a characteristic: θ_h|A = χ(d) e(ab Q(h)) θ_{ah}; for a coset on which a ↦ θ_{ah} is a character ψ, θ_h ∈ M(Γ₀(M), χψ̄) (lattice form, even rank)"]
theorem thetaSph_coset_slash_of_mem_Gamma0 (hk : finrank ℝ E = 2 * k) {ν : ℕ} {u w : E}
    (hsph : IsSphericalDatum ν u w) {M : ℕ} (hNM : ZLattice.level L ∣ M) {γ : E}
    (hγ : γ ∈ ZLattice.dual L) (hnorm : ∃ m : ℤ, ‖γ‖ ^ 2 = 2 * m) (ψ : DirichletCharacter ℂ M)
    (hψ : ∀ a : ℕ, a.Coprime M → thetaSph L ν u w ((a : ℝ) • γ) = ψ a • thetaSph L ν u w γ)
    (hψneg : ψ (-1) = (-1) ^ ν) {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma0 M) :
    thetaSph L ν u w γ ∣[((k + ν : ℕ) : ℤ)] A =
      ((DirichletCharacter.changeLevel hNM (hL.thetaCharacter ⟨k, by omega⟩)) * ψ⁻¹) (A 1 1 : ℤ) •
        thetaSph L ν u w γ := by
  classical
  set χ : DirichletCharacter ℂ M :=
    (DirichletCharacter.changeLevel hNM (hL.thetaCharacter ⟨k, by omega⟩)) * ψ⁻¹ with hχdef
  have hNpos : 0 < ZLattice.level L := hL.isIntegral.level_pos
  have hχneg : χ (-1) = (-1 : ℂ) ^ (((k + ν : ℕ) : ℤ)) := by
    have h1 : IsUnit ((-1 : ℤ) : ZMod M) := by simp
    rw [hχdef, MulChar.mul_apply, MulChar.inv_apply_eq_inv' ψ]
    rw [show ((-1 : ZMod M)) = (((-1 : ℤ)) : ZMod M) by simp]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hNM
      (isCoprime_one_left.neg_left)]
    simp only [Int.cast_neg, Int.cast_one]
    rw [hL.thetaCharacter_neg_one ⟨k, by omega⟩ hk, hψneg]
    push_cast
    rw [zpow_add₀ (by norm_num), zpow_natCast, zpow_natCast]
    have : ((-1 : ℂ) ^ ν)⁻¹ = (-1) ^ ν := by rw [← inv_pow, inv_neg_one]
    rw [this]
  apply TauCeti.ModularForm.slash_eq_smul_of_mem_Gamma0_of_pos_odd hχneg
    (thetaSph_coset_slash_T hL u w hγ hnorm _) ?_ hA
  intro B hB hc ha hao
  obtain ⟨a, haeq⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨c, hceq⟩ := Int.eq_ofNat_of_zero_le hc.le
  have haodd : Odd a := by rw [haeq] at hao; exact_mod_cast hao
  have hMc : M ∣ c := by
    have h := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hB
    rw [hceq] at h
    exact_mod_cast h
  have hN : ZLattice.level L ∣ c := hNM.trans hMc
  have hdet : (a : ℤ) * B 1 1 = 1 + B 0 1 * c := by
    have h := B.det_coe
    rw [Matrix.det_fin_two, haeq, hceq] at h
    linarith
  have haM : a.Coprime M := by
    have : IsCoprime (a : ℤ) (M : ℤ) := by
      obtain ⟨t, ht⟩ := hMc
      refine ⟨B 1 1, -(B 0 1 * t), ?_⟩
      have : (c : ℤ) = M * t := by exact_mod_cast ht
      rw [this] at hdet
      linarith
    exact Int.isCoprime_iff_gcd_eq_one.mp this |> fun h ↦ by simpa [Int.gcd_natCast_natCast] using h
  rw [thetaSph_coset_slash_of_pos hL hk hsph B haeq hceq haodd (by omega) hN ⟨γ, hγ⟩, hψ a haM, smul_smul]
  congr 1
  obtain ⟨m, hm⟩ := hnorm
  have he : cexp (2 * π * I * ((a * B 0 1 * ‖γ‖ ^ 2 / 2 : ℝ) : ℂ)) = 1 := by
    rw [hm]
    have : (2 * π * I * (((a * B 0 1 * (2 * m) / 2 : ℝ)) : ℂ)) = ((a * B 0 1 * m : ℤ) : ℂ) * (2 * π * I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [he, mul_one]
  -- the Jacobi symbol is the theta character at `a`, which equals its value at `d`
  have haN : IsCoprime (a : ℤ) (ZLattice.level L) :=
    (Nat.Coprime.coprime_dvd_right hNM haM).isCoprime
  have hjac : (jacobiSym ((-1) ^ k * Nat.card (ZLattice.DiscriminantGroup L)) a : ℂ) =
      hL.thetaCharacter ⟨k, by omega⟩ (a : ℤ) := by
    rw [hL.thetaCharacter_intCast ⟨k, by omega⟩ haN, TauCeti.kroneckerSym_eq_jacobiSym _ haodd,
      ZLattice.signedDiscr_of_finrank_eq L hk]
  have hB0 : B ∈ CongruenceSubgroup.Gamma0 (ZLattice.level L) := by
    rw [CongruenceSubgroup.mem_Gamma0_iff_dvd] at hB ⊢
    exact (Int.natCast_dvd_natCast.mpr hNM).trans hB
  have hchar : hL.thetaCharacter ⟨k, by omega⟩ (a : ℤ) =
      hL.thetaCharacter ⟨k, by omega⟩ (B 1 1 : ℤ) := by
    rw [← haeq]
    exact ((hL.thetaCharacter_isQuadratic _).apply_one_one_eq_apply_zero_zero_of_mem_Gamma0
      hB0).symm
  have hdN : IsCoprime (B 1 1 : ℤ) (ZLattice.level L) := by
    obtain ⟨t, ht⟩ := hN
    refine ⟨a, -(B 0 1 * t), ?_⟩
    have : (c : ℤ) = ZLattice.level L * t := by exact_mod_cast ht
    rw [this] at hdet
    linarith
  have hdM : IsCoprime (B 1 1 : ℤ) M := by
    obtain ⟨t, ht⟩ := hMc
    refine ⟨a, -(B 0 1 * t), ?_⟩
    have : (c : ℤ) = M * t := by exact_mod_cast ht
    rw [this] at hdet
    linarith
  -- `ψ(a) ψ(d) = ψ(ad) = ψ(1 + bc) = 1`
  have hψad : ψ (a : ℤ) * ψ (B 1 1 : ℤ) = 1 := by
    rw [← map_mul, ← Int.cast_mul, hdet]
    have : ((1 + B 0 1 * (c : ℤ) : ℤ) : ZMod M) = 1 := by
      have : ((c : ℤ) : ZMod M) = 0 := by
        rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff c M).mpr hMc
      push_cast at this ⊢
      rw [this, mul_zero, add_zero]
    rw [this, map_one]
  rw [hχdef, MulChar.mul_apply, MulChar.inv_apply_eq_inv' ψ,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hNM hdM, ← hchar, ← hjac]
  have : ψ (a : ℤ) = (ψ (B 1 1 : ℤ))⁻¹ := eq_inv_of_mul_eq_one_left hψad
  simp only [Int.cast_natCast] at this
  rw [this]

/-- **A coset theta series with a spherical weight of degree `ν ≥ 1` is a cusp form on `Γ₀(M)`**
with character `χ_L ψ⁻¹`, under the hypotheses of `thetaSph_coset_slash_of_mem_Gamma0` (Miyake,
Theorem 4.9.3 and Corollary 4.9.4 with a characteristic). -/
noncomputable def thetaSphCosetCuspForm (hk : finrank ℝ E = 2 * k) {ν : ℕ} (hν : 1 ≤ ν) {u w : E}
    (hsph : IsSphericalDatum ν u w) {M : ℕ} (hNM : ZLattice.level L ∣ M) {γ : E}
    (hγ : γ ∈ ZLattice.dual L) (hnorm : ∃ m : ℤ, ‖γ‖ ^ 2 = 2 * m) (ψ : DirichletCharacter ℂ M)
    (hψ : ∀ a : ℕ, a.Coprime M → thetaSph L ν u w ((a : ℝ) • γ) = ψ a • thetaSph L ν u w γ)
    (hψneg : ψ (-1) = (-1) ^ ν)
    (htriv : ∀ d : ℤ, IsCoprime d M →
      ((DirichletCharacter.changeLevel hNM (hL.thetaCharacter ⟨k, by omega⟩)) * ψ⁻¹) d = 1) :
    CuspForm ((CongruenceSubgroup.Gamma0 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)) (k + ν : ℕ) where
  toFun := thetaSph L ν u w γ
  slash_action_eq' A hA := by
    borelize E
    obtain ⟨A, hA, rfl⟩ := hA
    rw [← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash,
      thetaSph_coset_slash_of_mem_Gamma0 hL hk hsph hNM hγ hnorm ψ hψ hψneg hA]
    have hdM : IsCoprime (A 1 1 : ℤ) M := by
      have hdet := A.det_coe
      rw [Matrix.det_fin_two] at hdet
      obtain ⟨t, ht⟩ := CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hA
      exact ⟨A 0 0, -(A 0 1 * t), by rw [ht] at hdet; linarith⟩
    rw [htriv _ hdM, one_smul]
  holo' := mdifferentiable_thetaW L (polyBounded_isoForm_pow u w ν) γ
  zero_at_cusps' hc := by
    borelize E
    apply (OnePoint.isZeroAt_iff_forall_SL2Z (hc.mono (Subgroup.map_le_range _ _))).mpr
    intro A _
    have h := isZeroAtImInfty_absSlash_thetaSph hL hν hsph A hγ
    rw [UpperHalfPlane.isZeroAtImInfty_iff] at h ⊢
    intro ε hε
    obtain ⟨B, hB⟩ := h ε hε
    refine ⟨B, fun τ hτ ↦ ?_⟩
    rw [norm_slash_eq_absSlash]
    have := hB τ hτ
    rw [Real.norm_of_nonneg (absSlash_nonneg _ _ _ _)] at this
    convert this using 2
    rw [hk]; push_cast; ring

@[simp]
theorem coe_thetaSphCosetCuspForm (hk : finrank ℝ E = 2 * k) {ν : ℕ} (hν : 1 ≤ ν) {u w : E}
    (hsph : IsSphericalDatum ν u w) {M : ℕ} (hNM : ZLattice.level L ∣ M) {γ : E}
    (hγ : γ ∈ ZLattice.dual L) (hnorm : ∃ m : ℤ, ‖γ‖ ^ 2 = 2 * m) (ψ : DirichletCharacter ℂ M)
    (hψ : ∀ a : ℕ, a.Coprime M → thetaSph L ν u w ((a : ℝ) • γ) = ψ a • thetaSph L ν u w γ)
    (hψneg : ψ (-1) = (-1) ^ ν)
    (htriv : ∀ d : ℤ, IsCoprime d M →
      ((DirichletCharacter.changeLevel hNM (hL.thetaCharacter ⟨k, by omega⟩)) * ψ⁻¹) d = 1) :
    ⇑(thetaSphCosetCuspForm hL hk hν hsph hNM hγ hnorm ψ hψ hψneg htriv) = thetaSph L ν u w γ :=
  rfl

end IsEvenSph

end ModularFormsKB.Miyake.Sec4_9
