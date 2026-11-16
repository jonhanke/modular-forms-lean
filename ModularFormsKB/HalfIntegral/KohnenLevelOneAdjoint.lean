/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.KohnenZagierTrace
import TauCeti.NumberTheory.ModularForms.Petersson.Normal
import TauCeti.NumberTheory.ModularForms.LevelOne.Eigenbasis

/-!
# $T(p)$ is self-adjoint on $S_{2k}(\mathrm{SL}_2(\mathbb Z))$: a bridge to Tau Ceti

Loose end LE-MF-0270.

Earlier files assumed `LevelOneHeckeSelfAdjoint` (for this library's `peterssonOne`, one integral over the fundamental domain
`ModularGroup.fd`, and Tau Ceti's `heckeTCuspLevelOne`). Tau Ceti proves the adjointness of `heckeTCuspNat` for
`peterssonInnerCosets` on cusp forms of $\Gamma_1(N)$ (`peterssonInnerCosets_heckeTCuspNat_right`). At $N = 1$:
- `cuspFormGamma1OneEquiv` identifies the two spaces of cusp forms without changing the function;
- the diamond operators are trivial ($(\mathbb Z/1)^\times = 1$);
- `heckeTCuspNat` at a prime $p$ is $U_p f + f\mid\operatorname{diag}(p, 1)$ (`coe_heckeTCuspNat_prime`), which is
  `heckeSlashLevelOne` at $p$ (`heckeSlashLevelOne_eq_sum_heckeSlashUpperTri_slash`);
- `peterssonInnerCosets` is a sum over the single coset of $\mathrm{SL}_2(\mathbb Z)$, so it is the integral over the
  fundamental domain, which is `peterssonOne`.

**Proved here.**
- `levelOneHeckeSelfAdjoint`: `LevelOneHeckeSelfAdjoint k` for every `k`, with no input;
- `kohnenZagier_of_trace'`, `waldspurgerPlus_of_trace'`: H3 without that input.
-/

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane ModularForm HeckeRing.GL2 TauCeti
open scoped ComplexConjugate

/-- **The level-one Petersson product of Tau Ceti is `peterssonOne`**: for cusp forms of $\Gamma_1(1)$ of weight $2k$,
`peterssonInnerCosets` is this library's `peterssonOne` of the underlying functions. -/
theorem peterssonInnerCosets_gamma1One_eq_peterssonOne (k : ℕ)
    (f g : CuspForm ((Gamma1 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) ((2 * k : ℕ) : ℤ)) :
    _root_.CuspForm.peterssonInnerCosets f g = peterssonOne k f g := by
  have hmem : ∀ x : SL(2, ℤ), x ∈ (Gamma1 1).withCenter := fun x =>
    Subgroup.le_withCenter _ (by
      rw [Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩ <;> exact Subsingleton.elim _ _)
  have : Subsingleton (SL(2, ℤ) ⧸ (Gamma1 1).withCenter) :=
    ⟨fun a b => by
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      exact QuotientGroup.eq.mpr (hmem _)⟩
  have hslash : ∀ (F : CuspForm ((Gamma1 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) ((2 * k : ℕ) : ℤ))
      (x : SL(2, ℤ)), (⇑F ∣[((2 * k : ℕ) : ℤ)] x) = ⇑F := fun F x => by
    have := SlashInvariantFormClass.slash_action_eq F (Matrix.SpecialLinearGroup.mapGL ℝ x)
      (Subgroup.mem_map_of_mem _ (by
        rw [Gamma1_mem]
        refine ⟨?_, ?_, ?_⟩ <;> exact Subsingleton.elim _ _))
    exact this
  rw [_root_.CuspForm.peterssonInnerCosets_def,
    Fintype.sum_subsingleton _ (QuotientGroup.mk 1), hslash, hslash]
  simp only [UpperHalfPlane.peterssonInner, UpperHalfPlane.petersson, peterssonOne, peterssonReps,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have h2 : (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
  beta_reduce
  rw [h2]
  simp only [Real.rpow_natCast, Complex.ofReal_pow, zpow_natCast]

/-- **At level one, Tau Ceti's `heckeTCuspNat` at a prime is `heckeTCuspLevelOne`** across `cuspFormGamma1OneEquiv`. -/
theorem heckeTCuspNat_one_eq_heckeTCuspLevelOne (w : ℤ) {p : ℕ} [NeZero p] (hp : p.Prime)
    (f : CuspForm ((Gamma1 1).map (Matrix.SpecialLinearGroup.mapGL ℝ)) w) :
    ⇑(heckeTCuspNat (N := 1) w p f) = ⇑(heckeTCuspLevelOne w p (cuspFormGamma1OneEquiv w f)) := by
  have hd : (p.divisorsAntidiagonal) = {(1, p), (p, 1)} := by
    ext ⟨a, b⟩
    simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨h, -⟩
      rcases (Nat.dvd_prime hp).mp ⟨b, h.symm⟩ with rfl | rfl
      · left; exact ⟨rfl, by simpa using h⟩
      · right; refine ⟨rfl, ?_⟩
        have := hp.pos
        nlinarith [Nat.eq_of_mul_eq_mul_left this (h.trans (mul_one a).symm)]
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hp.ne_zero]
  have hdia : diamondOpCuspNat (N := 1) w p f = f := by
    rw [diamondOpCuspNat_of_coprime w (Nat.coprime_one_right p),
      Subsingleton.elim (ZMod.unitOfCoprime p (Nat.coprime_one_right p)) 1, diamondOpCusp_one]
    rfl
  rw [coe_heckeTCuspNat_prime w hp, hdia, coe_heckeTCuspLevelOne,
    heckeSlashLevelOne_eq_sum_heckeSlashUpperTri_slash, hd,
    Finset.sum_pair (by simp [hp.ne_one.symm]), CuspForm.coe_cuspFormGamma1OneEquiv_apply,
    heckeSlashUpperTri_one, scaleRep_def]
  simp only [HeckeRing.GL2.natDiagGL_one_one, SlashAction.slash_one]

/-- **$T(p)$ is self-adjoint on $S_{2k}(\mathrm{SL}_2(\mathbb Z))$ for `peterssonOne`** (row 21; Tau Ceti
`peterssonInnerCosets_heckeTCuspNat_right` at level one). This proves the former named input
`LevelOneHeckeSelfAdjoint`. -/
@[kb "miyake1989" "Thm. 4.5.4: T(p) is self-adjoint on S_{2k}(SL₂(ℤ)) (bridge to Tau Ceti) [unverified]"]
theorem levelOneHeckeSelfAdjoint (k : ℕ) : LevelOneHeckeSelfAdjoint k := by
  refine ⟨fun p _ hp F G => ?_⟩
  have hc : p.Coprime 1 := Nat.coprime_one_right p
  have key := peterssonInnerCosets_heckeTCuspNat_right (N := 1) (k := ((2 * k : ℕ) : ℤ)) (n := p) hc
    ((cuspFormGamma1OneEquiv _).symm F) ((cuspFormGamma1OneEquiv _).symm G)
  rw [Subsingleton.elim (ZMod.unitOfCoprime p hc)⁻¹ 1, diamondOpCusp_one] at key
  rw [peterssonInnerCosets_gamma1One_eq_peterssonOne, peterssonInnerCosets_gamma1One_eq_peterssonOne,
    LinearMap.id_apply] at key
  rw [heckeTCuspNat_one_eq_heckeTCuspLevelOne _ hp ((cuspFormGamma1OneEquiv _).symm G),
    heckeTCuspNat_one_eq_heckeTCuspLevelOne _ hp ((cuspFormGamma1OneEquiv _).symm F)] at key
  simpa using key.symm

/-- **H3 (Kohnen–Zagier) for the theta multiplier** from `KohnenTraceIdentity`, `KohnenTPlusFourStable`,
`PlusHeckeSelfAdjoint` and `KohnenAdjointCoeff`; the level-one adjointness is now proved. -/
@[kb "kohnenzagier1981" "Kohnen–Zagier formula, theta multiplier, from the trace identity, T⁺(4), plus-space Hecke adjointness and the kernel coefficient [unverified]"]
theorem kohnenZagier_of_trace' (k : ℕ) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k) (hS : PlusHeckeSelfAdjoint k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_of_trace k h hT hS (levelOneHeckeSelfAdjoint k) hcoeff

/-- **H3 (Waldspurger's plus-space theorem) for the theta multiplier**, from the same inputs as
`kohnenZagier_of_trace'`. -/
@[kb "kohnenzagier1981" "Waldspurger's theorem on the plus space, from the same inputs [unverified]"]
theorem waldspurgerPlus_of_trace' (k : ℕ) (h : KohnenTraceIdentity k)
    (hT : KohnenTPlusFourStable thetaMultiplierSystem k) (hS : PlusHeckeSelfAdjoint k)
    (hcoeff : ∀ D, KohnenDisc k D → ∀ Sstar : CuspForm 𝒮ℒ (2 * k : ℕ) → ℍ → ℂ,
      KohnenAdjoint thetaMultiplierSystem k D Sstar → KohnenAdjointCoeff thetaMultiplierSystem k D Sstar) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_of_trace k h hT hS (levelOneHeckeSelfAdjoint k) hcoeff

end ModularFormsKB.HalfIntegral
