/-
# `KohnenLiftEigen` from `KohnenDLift`

Let $g \leftrightarrow F$ correspond and $D$ be a fundamental
discriminant with $(-1)^kD > 0$. By `KohnenDLift` the $D$-th lift $\mathcal S_Dg$ is a level one cusp form $G$ with
coefficients `kohnenLiftCoeff k D c`. By Hecke equivariance on coefficients (`kohnenLiftCoeff_heckeT_of_fundamental`)
$G$ is a $T(p)$-eigenform with eigenvalue $b(p)$ for every odd prime $p$, as is $F$. By multiplicity one away from $2$
at level one (`eq_smul_of_odd_eigen`, from Tau Ceti's strong multiplicity one) $G = \lambda F$, and comparing
the coefficients at $1$ gives $\lambda = c(|D|)$ (`kohnenLiftEigen_of_dLift`).
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierLevelOne

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane ModularForm HeckeRing.GL2 TauCeti
open scoped Real

/-- **`KohnenLiftEigen` from `KohnenDLift`.** -/
theorem kohnenLiftEigen_of_dLift (M : MultiplierSystem) (k : ℕ)
    (hL : ∀ D, KohnenDisc k D → KohnenDLift M k D) : KohnenLiftEigen M k := by
  refine ⟨fun hk g c F b hgF D hD hsign n hn ↦ ?_⟩
  obtain ⟨G, hG⟩ := (hL D ⟨hD, hsign⟩).lift hk g hgF.plus c hgF.coeff_g
  have hFne : F ≠ 0 := cuspForm_ne_zero_of_coeff_one F hgF.coeff_F hgF.normalized
  obtain ⟨lam, hlam⟩ := eq_smul_of_odd_eigen ((2 * k : ℕ) : ℤ) F G hFne (fun p ↦ b p.1)
    (fun p _ ↦ heckeTCuspLevelOne_eq_smul (2 * k) p.2 F hgF.coeff_F (hgF.eigen_F p.1 p.2))
    (fun p hp ↦ heckeTCuspLevelOne_eq_smul (2 * k) p.2 G hG (by
      rw [← kohnenLiftCoeff_heckeT_of_fundamental k hD hsign p.2 hp, hgF.eigen_g p.1 p.2 hp]
      exact (kohnenLiftLin k D).map_smul (b p.1) c))
  have hcoef : kohnenLiftCoeff k D c = lam • b := by
    refine Abstract.hasQExp_unique hG ?_
    rw [hlam]
    simpa using Abstract.hasQExp_smul lam hgF.coeff_F
  have h1 : kohnenLiftCoeff k D c 1 = c D.natAbs := by
    simp [kohnenLiftCoeff]
  have hl : lam = c D.natAbs := by
    have := congrFun hcoef 1
    rw [h1, Pi.smul_apply, hgF.normalized, smul_eq_mul, mul_one] at this
    exact this.symm
  show kohnenLiftCoeff k D c n = _
  rw [hcoef, Pi.smul_apply, smul_eq_mul, hl]

end ModularFormsKB.HalfIntegral
