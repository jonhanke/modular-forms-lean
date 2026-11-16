/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.KohnenKernel
import ModularFormsKB.HalfIntegral.Abstract.Shintani
import ModularFormsKB.HalfIntegral.KohnenTrace

/-!
# Shintani's lift by cycle integrals, and positivity of $L(F, D, k)$

**Shintani's lift.** With the unfolding (`ZagierKernelUnfolding`), the $m$-th coefficient of Kohnen–Zagier's kernel
$c_{k,D}^{-1}m^{k-1/2}\langle f_{k,D,|D|m}, G\rangle$ is $(-1)^{\lfloor k/2\rfloor}2^k\,r_{k,D}(G;m)$ for every $m$
(`kohnenKernelCoeff_eq_shintaniCoeff`): the powers of $m$ and $|D|$ cancel. So the kernel input `KohnenKernelModular`
gives Shintani's two statements:
- `shintaniCycleFormula_of_kernel`: `ShintaniCycleFormula` (the series of cycle integrals lies in $S^+_{k+1/2}(4)$);
- `shintaniShimuraAdjoint_of_kernel`: `ShintaniShimuraAdjoint` with the explicit constant
  $\lambda_{k,D} = (-1)^{\lfloor k/2\rfloor}2^k/6$ (the $1/6$ is the normalization of `peterssonFour`).

**Positivity.** From the Kohnen–Zagier formula, $L(F, D, k) \ge 0$ for a normalized eigenform $F$ of level one with a
corresponding $g$ (`twistedL_nonneg_of_kohnenZagier`), since $|c(|D|)|^2$, the two Petersson norms and the constant are
positive. With Kohnen's isomorphism every normalized eigenform has a corresponding $g$
(`exists_corresponds_of_kohnenIsomorphism`); together, `twistedL_nonneg_of_kernel` gives the positivity from the inputs of
H5 (Kohnen–Zagier 1981 `kohnenzagier1981`, Cor. 1 [unverified]).
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane ModularForm
open scoped Real

/-! ### Shintani's lift -/

/-- **The coefficients of Kohnen–Zagier's kernel are the Shintani coefficients**, up to $(-1)^{\lfloor k/2\rfloor}2^k$. -/
theorem kohnenKernelCoeff_eq_shintaniCoeff (k : ℕ) (hk : 2 ≤ k) (hU : ZagierKernelUnfolding k) {D : ℤ}
    (hD : KohnenDisc k D) (G : CuspForm 𝒮ℒ (2 * k : ℕ)) (m : ℕ) :
    kohnenKernelCoeff k D G m = ((-1) ^ (k / 2) * 2 ^ k : ℂ) * shintaniCoeff k D G m := by
  have hD0 : D ≠ 0 := by rintro rfl; exact absurd hD.2 (by simp)
  by_cases hidx : KernelIndex k m
  · rw [kohnenKernelCoeff, if_pos hidx, hU.unfold hk D hD m hidx G]
    have hm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hidx.1
    have hx0 : (0 : ℝ) < (D.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 hD0
    have hA0 := Real.rpow_pos_of_pos hx0 ((k : ℝ) - 1 / 2)
    have hB0 := Real.rpow_pos_of_pos hm ((k : ℝ) - 1 / 2)
    have hU' : ((D.natAbs * m : ℕ) : ℝ) ^ ((1 : ℝ) / 2 - k) =
        ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) * (m : ℝ) ^ ((k : ℝ) - 1 / 2))⁻¹ := by
      rw [Nat.cast_mul, Real.mul_rpow hx0.le hm.le,
        show (1 : ℝ) / 2 - k = -((k : ℝ) - 1 / 2) by ring, Real.rpow_neg hx0.le, Real.rpow_neg hm.le, mul_inv]
    have hBc : (0 : ℝ) < ((2 * k - 2).choose (k - 1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have h8 : (8 : ℝ) ^ k = 2 ^ k * 4 ^ k := by rw [← mul_pow]; norm_num
    have hreal : kohnenKernelConst k D m * zagierUnfoldConst k (D.natAbs * m) = (-1) ^ (k / 2) * 2 ^ k := by
      simp only [kohnenKernelConst, zagierUnfoldConst, hU']
      have hπ : (0 : ℝ) < π := Real.pi_pos
      field_simp
      rw [h8]
      ring
    have hc : ((kohnenKernelConst k D m : ℝ) : ℂ) * (zagierUnfoldConst k (D.natAbs * m) : ℂ) =
        ((-1) ^ (k / 2) * 2 ^ k : ℂ) := by
      rw [← ofReal_mul, hreal]; push_cast; ring
    rw [← mul_assoc, hc]
  · have : ¬ (1 ≤ m ∧ (((-1) ^ k * m : ℤ) % 4 = 0 ∨ ((-1) ^ k * m : ℤ) % 4 = 1)) := hidx
    rw [kohnenKernelCoeff, if_neg hidx, shintaniCoeff, if_neg this]
    simp

/-- **Row 34: Shintani's lift lies in the plus space**, from the kernel and the unfolding. -/
theorem shintaniCycleFormula_of_kernel (k : ℕ) (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) :
    ShintaniCycleFormula thetaMultiplierSystem k := by
  refine ⟨fun hk D hD hsign G ↦ ?_⟩
  obtain ⟨g, hg, hq, -⟩ := hK.kernel hk D ⟨hD, hsign⟩ G
  have hl : ((-1) ^ (k / 2) * 2 ^ k : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  refine ⟨((-1) ^ (k / 2) * 2 ^ k : ℂ)⁻¹ • g, Submodule.smul_mem _ _ hg, ?_⟩
  have h2 := hasQExp_smul hq (((-1) ^ (k / 2) * 2 ^ k : ℂ)⁻¹)
  have : (((-1) ^ (k / 2) * 2 ^ k : ℂ)⁻¹ • kohnenKernelCoeff k D G) = shintaniCoeff k D G := by
    funext n
    rw [Pi.smul_apply, kohnenKernelCoeff_eq_shintaniCoeff k hk hU ⟨hD, hsign⟩ G n, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hl, one_mul]
  rwa [this] at h2

/-- The constant $(-1)^{\lfloor k/2\rfloor}2^k/6$ is nonzero. -/
theorem adjoint_lam_ne_zero (k : ℕ) : ((-1) ^ (k / 2) * 2 ^ k / 6 : ℂ) ≠ 0 :=
  div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))) (by norm_num)

/-- The core of the adjointness: with the explicit constant. -/
theorem adjoint_core (k : ℕ) (hk : 2 ≤ k) (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) {D : ℤ}
    (hD : KohnenDisc k D) (g : ℍ → ℂ) (hg : g ∈ thetaMultiplierSystem.plusCuspForms k 1 1) (c : ℕ → ℂ)
    (hc : Abstract.HasQExp g c) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b)
    (hbc : ∀ n, 1 ≤ n → b n = kzShimuraCoeff k D c n) (G : CuspForm 𝒮ℒ (2 * k : ℕ)) (gs : ℍ → ℂ)
    (hgs : Abstract.HasQExp gs (shintaniCoeff k D G)) :
    peterssonReps [1] (2 * k) F G =
      ((-1) ^ (k / 2) * 2 ^ k / 6 : ℂ) * peterssonReps gamma0FourReps ((k : ℝ) + 1 / 2) g gs := by
  obtain ⟨gK, hgK, hqK, hadj⟩ := hK.kernel hk D hD G
  have hq2 : Abstract.HasQExp gK (((-1) ^ (k / 2) * 2 ^ k : ℂ) • shintaniCoeff k D G) := by
    have : kohnenKernelCoeff k D G = ((-1) ^ (k / 2) * 2 ^ k : ℂ) • shintaniCoeff k D G := by
      funext n
      rw [Pi.smul_apply, smul_eq_mul]
      exact kohnenKernelCoeff_eq_shintaniCoeff k hk hU hD G n
    rwa [this] at hqK
  have heq : gK = ((-1) ^ (k / 2) * 2 ^ k : ℂ) • gs := Abstract.HasQExp.unique hq2 (hasQExp_smul hgs _)
  have hbc' : ∀ n, 1 ≤ n → b n = kzLiftCoeff k D c n := by
    intro n hn
    rw [hbc n hn, kzShimuraCoeff, kzLiftCoeff]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have := hadj g hg c hc F b hb hbc'
  change peterssonReps [1] (2 * k) F G = peterssonFour k g gK at this
  rw [this, heq, peterssonFour, peterssonReps_smul_right]
  ring

/-- **Row 34: Shintani's lift is adjoint to the Shimura lift**, with $\lambda_{k,D} = (-1)^{\lfloor k/2\rfloor}2^k/6$. -/
theorem shintaniShimuraAdjoint_of_kernel (k : ℕ) (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) :
    ShintaniShimuraAdjoint thetaMultiplierSystem k := by
  refine ⟨fun hk D hD hsign ↦ ⟨_, adjoint_lam_ne_zero k, fun g hg c hc F b hb hbc G gs hgs hgsq ↦
    adjoint_core k hk hK hU ⟨hD, hsign⟩ g hg c hc F b hb hbc G gs hgsq⟩⟩

/-- **Row 34, explicit**: for $g \in S^+$, its $D$-th lift $F$ and every $G$,
$\langle F, G\rangle = \frac{(-1)^{\lfloor k/2\rfloor}2^k}{6}\langle g, \mathcal S^*_DG\rangle$ with $\mathcal S^*_DG$ = `shintaniLift`. -/
theorem shintani_adjoint_of_kernel (k : ℕ) (hk : 2 ≤ k) (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k)
    {D : ℤ} (hD : KohnenDisc k D) (g : ℍ → ℂ) (hg : g ∈ thetaMultiplierSystem.plusCuspForms k 1 1) (c : ℕ → ℂ)
    (hc : Abstract.HasQExp g c) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b)
    (hbc : ∀ n, 1 ≤ n → b n = kzShimuraCoeff k D c n) (G : CuspForm 𝒮ℒ (2 * k : ℕ)) :
    shintaniLift k D G ∈ thetaMultiplierSystem.plusCuspForms k 1 1 ∧
      peterssonReps [1] (2 * k) F G =
        ((-1) ^ (k / 2) * 2 ^ k / 6 : ℂ) * peterssonReps gamma0FourReps ((k : ℝ) + 1 / 2) g (shintaniLift k D G) := by
  obtain ⟨hmem, hq⟩ := shintaniLift_mem (shintaniCycleFormula_of_kernel k hK hU) hk hD.1 hD.2 G
  exact ⟨hmem, adjoint_core k hk hK hU hD g hg c hc F b hb hbc G _ hq⟩

/-! ### Row 35: positivity -/

/-- **Row 35 from the Kohnen–Zagier formula**: if $g$ and $F$ correspond and $D$ is a fundamental discriminant with
$(-1)^kD > 0$, every entire continuation $L$ of $L(F, D, s)$ has $L(k)$ real and $\ge 0$. -/
theorem twistedL_nonneg_of_kohnenZagier {k : ℕ} (hKZ : KohnenZagier thetaMultiplierSystem k) (hk : 1 ≤ k)
    {g : ℍ → ℂ} {c : ℕ → ℂ} {F : CuspForm 𝒮ℒ (2 * k : ℕ)} {b : ℕ → ℂ}
    (hgF : Corresponds thetaMultiplierSystem k g c F b) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) {L : ℂ → ℂ}
    (hL : IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) L) :
    (L k).im = 0 ∧ 0 ≤ (L k).re := by
  have hNg := (peterssonDefinite thetaMultiplierSystem k).four g hgF.plus hgF.ne_zero
  have hNF := (peterssonDefinite thetaMultiplierSystem k).one F
    (cuspForm_ne_zero_of_coeff_one F hgF.coeff_F hgF.normalized)
  obtain ⟨hg0, hgi⟩ := peterssonNormSqFour_nonneg k g
  obtain ⟨hF0, hFi⟩ := peterssonNormSqOne_nonneg k F
  set Ng := peterssonNormSqFour k g with hNgdef
  set NF := peterssonNormSqOne k F with hNFdef
  have hNg' : Ng = ((Ng.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hgi])
  have hNF' : NF = ((NF.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hFi])
  have hngpos : 0 < Ng.re := lt_of_le_of_ne hg0 fun h ↦ hNg (by rw [hNg', ← h]; simp)
  have hnfpos : 0 < NF.re := lt_of_le_of_ne hF0 fun h ↦ hNF (by rw [hNF', ← h]; simp)
  have hform := hKZ.formula hk g c F b hgF D hD hsign L hL
  have hD0 : D ≠ 0 := by rintro rfl; simp at hsign
  have hx0 : (0 : ℝ) < (D.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.2 hD0
  have hKpos : (0 : ℝ) < (k - 1).factorial / π ^ k * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) := by
    have := Real.pi_pos
    have := Real.rpow_pos_of_pos hx0 ((k : ℝ) - 1 / 2)
    have : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    positivity
  set K : ℝ := (k - 1).factorial / π ^ k * (D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) with hK
  have hKc : ((k - 1).factorial / (π : ℂ) ^ k) * ((D.natAbs : ℝ) ^ ((k : ℝ) - 1 / 2) : ℝ) = (K : ℂ) := by
    rw [hK]; push_cast; ring
  rw [hKc, ← hNgdef, ← hNFdef] at hform
  have hLk : L k = (((‖c D.natAbs‖ ^ 2 * NF.re / (Ng.re * K) : ℝ)) : ℂ) := by
    have hKne : (K : ℂ) ≠ 0 := by exact_mod_cast hKpos.ne'
    rw [hNg', hNF'] at hform
    have hne1 : ((Ng.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hngpos.ne'
    have hne2 : ((NF.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnfpos.ne'
    rw [div_eq_div_iff hne1 hne2] at hform
    push_cast at hform ⊢
    field_simp
    linear_combination (-1 : ℂ) * hform
  rw [hLk]
  refine ⟨ofReal_im _, ?_⟩
  rw [ofReal_re]
  positivity

/-- **Every normalized eigenform has a corresponding $g$** under Kohnen's isomorphism: $g = \Phi^{-1}F$. -/
theorem exists_corresponds_of_kohnenIsomorphism {k : ℕ} (hI : KohnenIsomorphism thetaMultiplierSystem k) (hk : 1 ≤ k)
    (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b) (h1 : b 1 = 1)
    (heig : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) :
    ∃ (g : ℍ → ℂ) (c : ℕ → ℂ), Corresponds thetaMultiplierSystem k g c F b := by
  obtain ⟨Φ, hΦ⟩ := hI.iso hk
  set g0 := Φ.symm F with hg0
  obtain ⟨c, hc⟩ := exists_hasQExp_plus g0
  have hΦg : Φ g0 = F := Φ.apply_symm_apply F
  refine ⟨g0.1, c, ⟨g0.2, ?_, hc, hb, h1, heig, ?_⟩⟩
  · intro h0
    have : g0 = 0 := Subtype.ext h0
    have hF0 : F = 0 := by rw [← hΦg, this, map_zero]
    exact cuspForm_ne_zero_of_coeff_one F hb h1 hF0
  · intro p hp hp2
    obtain ⟨f', hf', hcf'⟩ := plus_heckeStable k hp hp2 g0.2 hc
    have hb' : Abstract.HasQExp (Φ g0) b := by rw [hΦg]; exact hb
    have h2 := hΦ p hp hp2 g0 ⟨f', hf'⟩ c b hc hcf' hb'
    rw [heig p hp] at h2
    have h3 : Abstract.HasQExp (⇑(b p • F)) (b p • b) := by
      simpa using hasQExp_smul hb (b p)
    have h4 : Φ ⟨f', hf'⟩ = b p • F := cuspForm_ext_of_hasQExp h2 h3
    have h5 : (⟨f', hf'⟩ : thetaMultiplierSystem.plusCuspForms k 1 1) = b p • g0 := by
      apply Φ.injective
      rw [h4, map_smul, hΦg]
    have h6 : f' = b p • g0.1 := congrArg Subtype.val h5
    rw [h6] at hcf'
    exact Abstract.hasQExp_unique hcf' (hasQExp_smul hc (b p))

/-- **Row 35: $L(F, D, k) \ge 0$** (Kohnen–Zagier 1981 `kohnenzagier1981`, Cor. 1 [unverified]) for a normalized Hecke
eigenform $F \in S_{2k}(\mathrm{SL}_2(\mathbb Z))$ and a fundamental discriminant $D$ with $(-1)^kD > 0$, from the inputs of H5. -/
@[kb "kohnenzagier1981" "Cor. 1: L(F, D, k) ≥ 0 for (-1)^k D > 0, from the inputs of H5 [unverified]"]
theorem twistedL_nonneg_of_kernel (k : ℕ) (hk : 1 ≤ k) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k) (hS : PlusHeckeSelfAdjoint k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k)
    (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b) (h1 : b 1 = 1)
    (heig : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) {L : ℂ → ℂ}
    (hL : IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) L) :
    (L k).im = 0 ∧ 0 ≤ (L k).re := by
  have hKZ := kohnenZagier_of_kernel k h hT hS hK hU hQ
  have hI := kohnenIsomorphism_of_trace h hT
  obtain ⟨g, c, hgF⟩ := exists_corresponds_of_kohnenIsomorphism hI hk F b hb h1 heig
  exact twistedL_nonneg_of_kohnenZagier hKZ hk hgF hD hsign hL

end ModularFormsKB.HalfIntegral
