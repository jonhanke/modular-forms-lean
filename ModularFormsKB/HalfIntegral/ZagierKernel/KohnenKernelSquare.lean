/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
-/
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle
import ModularFormsKB.HalfIntegral.ZagierKernel.SquareCycle.GaussSumProof
import ModularFormsKB.HalfIntegral.ZagierKernel.KohnenKernelTheta

/-!
# The Kohnen–Zagier formula through Zagier's kernel, with `KohnenSquareCycle` proved

`KohnenSquareCycle k` is proved for every `k` (`kohnenSquareCycle`): the cycle integrals of discriminant $D^2$ give
$(-1)^{\lfloor k/2\rfloor}|D|^{k-1/2}(k-1)!(2\pi)^{-k}L(G, D, k)$. The proof (`ZagierKernel/SquareCycle/`) classifies the forms of
discriminant $D^2$ (`BinQF.exists_equiv_squareRep`, `BinQF.eq_of_equiv_squareRep`), evaluates their genus character
without the named input `GenusCharacterWellDefined` (`BinQF.genusChar_of_equiv_squareRep`), shows that the cycle integrals
at square discriminants are class invariants by writing them as Tau Ceti's integrals between cusps
(`BinQF.cycleIntegral_eq_geodesicIntegral`, `BinQF.cycleIntegral_comp_SL`), and computes the sum over $c \bmod |D|$
through the twist of $G$ by $\left(\frac D\cdot\right)$, Gauss's sign of the quadratic Gauss sum (`kroneckerGaussSum`, from
Miyake's Lemma 4.8.1 (1) as proved in `Miyake.Sec4_8.kroneckerGaussSumStatement`) and Tau Ceti's evaluation of the
periods of a cusp form as $L$-values.

So the Kohnen–Zagier theorems lose that hypothesis: they rest on `KohnenTraceIdentity` and the two kernel inputs
`KohnenKernelModular` and `ZagierKernelUnfolding`.
-/

namespace ModularFormsKB.HalfIntegral

open MatrixGroups

/-- **The cycle integrals of discriminant $D^2$ give $L(G, D, k)$** (Kohnen–Zagier 1981 `kohnenzagier1981`, §II): proof of
the former named input `KohnenSquareCycle`. -/
@[kb "kohnenzagier1981" "§II: the cycle integrals of discriminant D² give (-1)^[k/2] |D|^{k-1/2} (k-1)! (2π)^{-k} L(G,D,k), proved [unverified]"]
theorem kohnenSquareCycle (k : ℕ) : KohnenSquareCycle k :=
  kohnenSquareCycle_of_gaussSum kroneckerGaussSum k

/-- **The Kohnen–Zagier formula through Zagier's kernel** from `KohnenTraceIdentity`, `KohnenKernelModular` and
`ZagierKernelUnfolding`. -/
@[kb "kohnenzagier1981" "Thm. 1 through Zagier's kernel, from the trace identity, the modularity of the kernel and the unfolding [unverified]"]
theorem kohnenZagier_of_kernel_square (k : ℕ) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) :
    KohnenZagier thetaMultiplierSystem k :=
  kohnenZagier_of_kernel_theta k h hK hU (kohnenSquareCycle k)

/-- **Waldspurger's theorem on the plus space** from the inputs of `kohnenZagier_of_kernel_square`. -/
@[kb "kohnenzagier1981" "Waldspurger's theorem on the plus space through Zagier's kernel, from the trace identity, the modularity of the kernel and the unfolding [unverified]"]
theorem waldspurgerPlus_of_kernel_square (k : ℕ) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k) :
    WaldspurgerPlus thetaMultiplierSystem k :=
  waldspurgerPlus_of_kernel_theta k h hK hU (kohnenSquareCycle k)

/-- **$L(F, D, k) \ge 0$** from the inputs of `kohnenZagier_of_kernel_square`. -/
@[kb "kohnenzagier1981" "Cor. 1: L(F, D, k) ≥ 0 for (-1)^k D > 0, from the trace identity, the modularity of the kernel and the unfolding [unverified]"]
theorem twistedL_nonneg_of_kernel_square (k : ℕ) (hk : 1 ≤ k) (h : KohnenTraceIdentity k)
    (hK : KohnenKernelModular k) (hU : ZagierKernelUnfolding k)
    (F : CuspForm 𝒮ℒ (2 * k : ℕ)) (b : ℕ → ℂ) (hb : Abstract.HasQExp F b) (h1 : b 1 = 1)
    (heig : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) {D : ℤ} (hD : IsFundamentalDiscriminant D)
    (hsign : 0 < (-1) ^ k * D) {L : ℂ → ℂ}
    (hL' : IsEntireLSeries (fun n ↦ (kroneckerDisc D n : ℂ) * b n) ((k : ℝ) + 1) L) :
    (L k).im = 0 ∧ 0 ≤ (L k).re :=
  twistedL_nonneg_of_kernel_theta k hk h hK hU (kohnenSquareCycle k) F b hb h1 heig hD hsign hL'

end ModularFormsKB.HalfIntegral
