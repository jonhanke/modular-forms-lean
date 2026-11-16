/-
# The Kohnen–Zagier formula through Zagier's kernel, with `KohnenLUFour` proved

`KohnenLUFour thetaMultiplierSystem k` is proved (`kohnenLUFour_theta`, LE-MF-0286 closed), so the Kohnen–Zagier theorems of
`KohnenKernelIntegrated.lean` lose that hypothesis: they rest on `KohnenTraceIdentity` and the three kernel inputs
`KohnenKernelModular`, `ZagierKernelUnfolding`, `KohnenSquareCycle`. Only the wiring.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.KohnenKernelIntegrated
import ModularFormsKB.HalfIntegral.KohnenLUFourProof

namespace ModularFormsKB.HalfIntegral

open MatrixGroups

/-- **The Kohnen–Zagier formula through Zagier's kernel** from `KohnenTraceIdentity` and the three kernel inputs. -/
@[kb "kohnenzagier1981" "Thm. 1 through Zagier's kernel, from the trace identity and the kernel inputs [unverified]"]
theorem kohnenZagier_of_kernel_theta (k : ℕ) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_of_kernel_LUFour k h (kohnenLUFour_theta k) hK hU hQ

/-- **Waldspurger's theorem on the plus space** from the inputs of `kohnenZagier_of_kernel_theta`. -/
@[kb "kohnenzagier1981" "Waldspurger's theorem on the plus space through Zagier's kernel, from the trace identity and the kernel inputs [unverified]"]
theorem waldspurgerPlus_of_kernel_theta (k : ℕ) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_of_kernel_LUFour k h (kohnenLUFour_theta k) hK hU hQ

/-- **$L(F, D, k) \ge 0$** from the inputs of `kohnenZagier_of_kernel_theta`. -/
@[kb "kohnenzagier1981" "Cor. 1: L(F, D, k) ≥ 0 for (-1)^k D > 0, from the trace identity and the kernel inputs [unverified]"]
theorem twistedL_nonneg_of_kernel_theta (k : ℕ) (hk : 1 ≤ k) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) (hQ : KohnenSquareCycle k)
    (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b) (h1 : b 1 = 1)
    (heig : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) {L : ℂ → ℂ}
    (hL' : IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) L) :
    (L k).im = 0 ∧ 0 ≤ (L k).re :=
  twistedL_nonneg_of_kernel_LUFour k hk h (kohnenLUFour_theta k) hK hU hQ F b hb h1 heig hD hsign hL'

end ModularFormsKB.HalfIntegral
