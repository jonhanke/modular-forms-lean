/-
# H5 with the earlier inputs discharged

`KohnenKernel.lean` and `ShintaniPositivity.lean` take `KohnenTPlusFourStable` and `PlusHeckeSelfAdjoint` as
hypotheses. Here these are discharged:
* `PlusHeckeSelfAdjoint k` is proved for every `k` (`PlusHeckeAdjoint.plusHeckeSelfAdjoint`, LE-MF-0269 closed);
* `KohnenTPlusFourStable` follows from `KohnenLUFour` (`kohnenTPlusFourStable_of_LUFour`, LE-MF-0286), which stays
  an input.
So H5 is conditional on `KohnenTraceIdentity`, `KohnenLUFour` and the three kernel inputs
`KohnenKernelModular`, `ZagierKernelUnfolding`, `KohnenSquareCycle`. No new mathematics: only the wiring.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.KohnenKernel
import ModularFormsKB.HalfIntegral.ZagierKernel.ShintaniPositivity
import ModularFormsKB.HalfIntegral.KohnenTPlusFourLU

namespace ModularFormsKB.HalfIntegral

open MatrixGroups

/-- **H5 (Kohnen–Zagier through Zagier's kernel)** from `KohnenTraceIdentity`, `KohnenLUFour` and the three kernel
inputs; `PlusHeckeSelfAdjoint` is proved and `KohnenTPlusFourStable` is derived from `KohnenLUFour`. -/
@[kb "kohnenzagier1981" "Thm. 1 through Zagier's kernel, from the trace identity, the U(4) identity and the kernel inputs [unverified]"]
theorem kohnenZagier_of_kernel_LUFour (k : ℕ) (h : KohnenTraceIdentity k)
    (hL : KohnenLUFour thetaMultiplierSystem k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_of_kernel k h (kohnenTPlusFourStable_of_LUFour hL) (PlusHeckeAdjoint.plusHeckeSelfAdjoint k) hK hU hQ

/-- **H5 (Waldspurger's theorem on the plus space)** from the inputs of `kohnenZagier_of_kernel_LUFour`. -/
@[kb "kohnenzagier1981" "Waldspurger's theorem on the plus space through Zagier's kernel, from the U(4) identity and the kernel inputs [unverified]"]
theorem waldspurgerPlus_of_kernel_LUFour (k : ℕ) (h : KohnenTraceIdentity k)
    (hL : KohnenLUFour thetaMultiplierSystem k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_of_kernel k h (kohnenTPlusFourStable_of_LUFour hL) (PlusHeckeAdjoint.plusHeckeSelfAdjoint k) hK hU hQ

/-- **Row 35 ($L(F, D, k) \ge 0$)** from the inputs of `kohnenZagier_of_kernel_LUFour`. -/
@[kb "kohnenzagier1981" "Cor. 1: L(F, D, k) ≥ 0 for (-1)^k D > 0, from the U(4) identity and the kernel inputs [unverified]"]
theorem twistedL_nonneg_of_kernel_LUFour (k : ℕ) (hk : 1 ≤ k) (h : KohnenTraceIdentity k)
    (hL : KohnenLUFour thetaMultiplierSystem k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k)
    (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b) (h1 : b 1 = 1)
    (heig : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) {L : ℂ → ℂ}
    (hL' : IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) L) :
    (L k).im = 0 ∧ 0 ≤ (L k).re :=
  twistedL_nonneg_of_kernel k hk h (kohnenTPlusFourStable_of_LUFour hL) (PlusHeckeAdjoint.plusHeckeSelfAdjoint k)
    hK hU hQ F b hb h1 heig hD hsign hL'

end ModularFormsKB.HalfIntegral
