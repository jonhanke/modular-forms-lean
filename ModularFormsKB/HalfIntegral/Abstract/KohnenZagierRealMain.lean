/-
# `PlusRealCoefficients` for the theta multiplier

The hypothesis on the reality of the eigenvalues $b(p)$ is not obtainable from the reflection alone.

Let $g \leftrightarrow F$ correspond. The conjugate form $\hat g = \overline{g(-\bar\tau)}$ (`conjForm`) lies in $S^+$ with
coefficients $\bar c$ (`conjForm_mem_plus`, `hasQExp_conjForm`), and is $T(p^2)$-eigen with eigenvalues $\overline{b(p)} = b(p)$:
conjugation commutes with `heckeT` for the trivial character (`heckeT_conj`), and $b(p)$ is real because $T(p)$ is
self-adjoint on level one (`LevelOneHeckeSelfAdjoint`, `b_real`). By multiplicity one `KohnenPlusMultOne`, $\hat g = tg$, so
$\bar c = tc$; applying this twice gives $|t| = 1$, and with $u = e^{-i\arg t/2}$ the numbers $c(n)/u$ are real
(`plusRealCoefficients_theta`).
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierConj
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierHecke
import ModularFormsKB.HalfIntegral.Abstract.WaldspurgerGround

namespace ModularFormsKB.HalfIntegral

open Complex MatrixGroups CongruenceSubgroup UpperHalfPlane TauCeti
open scoped ComplexConjugate Real

/-- Conjugation of coefficients commutes with $T(p^2)$ for the trivial character. -/
theorem heckeT_conj (k p : ℕ) (a : ℕ → ℂ) :
    heckeT k 1 1 p (fun n ↦ conj (a n)) = fun n ↦ conj (heckeT k 1 1 p a n) := by
  funext n
  simp only [heckeT]
  have hc : ∀ x : ZMod (4 * 1), conj ((1 : DirichletCharacter ℂ (4 * 1)) x) = (1 : DirichletCharacter ℂ (4 * 1)) x :=
    conj_one_dirichlet
  by_cases hd : p ^ 2 ∣ n
  · simp only [hd, if_true, map_add, map_mul, map_intCast, map_zpow₀, map_natCast, map_pow, hc]
  · simp only [hd, if_false, map_add, map_mul, map_intCast, map_zpow₀, map_natCast, map_pow, hc, map_zero]

/-- **The eigenvalues of a level one eigenform are real** (from `LevelOneHeckeSelfAdjoint`). -/
theorem b_real (k : ℕ) (hO : LevelOneHeckeSelfAdjoint k) (F : CuspForm 𝒮ℒ (2 * k : ℕ)) {b : ℕ → ℂ}
    (hF : Abstract.HasQExp F b) (hb1 : b 1 = 1)
    (heig : ∀ p : ℕ, p.Prime → heckeTInt (2 * k) 1 1 p b = b p • b) {p : ℕ} (hp : p.Prime) : conj (b p) = b p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hT : heckeTCuspLevelOne ((2 * k : ℕ) : ℤ) p F = b p • F :=
    heckeTCuspLevelOne_eq_smul (2 * k) hp F hF (heig p hp)
  have h := hO.selfAdjoint p hp F F
  rw [hT] at h
  have hsm : ((b p • F : CuspForm 𝒮ℒ (2 * k : ℕ)) : ℍ → ℂ) = b p • ⇑F := rfl
  simp only [peterssonOne, hsm, peterssonReps_smul_left, peterssonReps_smul_right] at h
  have hne : peterssonReps [1] (2 * (k : ℝ)) F F ≠ 0 := by
    have := peterssonNormSqOne_ne_zero k F (cuspForm_ne_zero_of_coeff_one F hF hb1)
    simpa [peterssonNormSqOne] using this
  exact mul_right_cancel₀ hne h

/-- **Row 24: `PlusRealCoefficients` for the theta multiplier.** -/
theorem plusRealCoefficients_theta (k : ℕ) (hmult : KohnenPlusMultOne thetaMultiplierSystem k)
    (hO : LevelOneHeckeSelfAdjoint k) : PlusRealCoefficients thetaMultiplierSystem k := by
  refine ⟨fun hk g c F b h ↦ ?_⟩
  have hgc : Abstract.HasQExp (conjForm g) (fun n ↦ conj (c n)) := hasQExp_conjForm h.coeff_g
  have heig : IsPlusEigenform thetaMultiplierSystem k g (fun p ↦ b p) := ⟨h.plus, c, h.coeff_g, h.eigen_g⟩
  have heig' : IsPlusEigenform thetaMultiplierSystem k (conjForm g) (fun p ↦ b p) := by
    refine ⟨conjForm_mem_plus h.plus, _, hgc, fun p hp hp2 ↦ ?_⟩
    rw [heckeT_conj, h.eigen_g p hp hp2]
    funext n
    simp [b_real k hO F h.coeff_F h.normalized h.eigen_F hp]
  obtain ⟨t, ht⟩ := hmult.mult_one hk g (conjForm g) _ heig heig' h.ne_zero
  have hct : (fun n ↦ conj (c n)) = t • c := by
    refine Abstract.hasQExp_unique hgc ?_
    rw [ht]
    exact Abstract.hasQExp_smul t h.coeff_g
  have hct' : ∀ n, conj (c n) = t * c n := fun n ↦ congrFun hct n
  -- some coefficient is nonzero
  obtain ⟨n₀, hn₀⟩ : ∃ n, c n ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h.ne_zero
    funext τ
    have := h.coeff_g τ
    simp only [hall, zero_mul] at this
    exact this.unique hasSum_zero
  -- |t| = 1
  have e2 : c n₀ = conj t * (t * c n₀) := by
    have := congrArg conj (hct' n₀)
    rw [Complex.conj_conj, map_mul, hct' n₀] at this
    exact this
  have e3 : conj t * t = 1 := mul_right_cancel₀ hn₀ (by linear_combination (-1 : ℂ) * e2)
  have hns : Complex.normSq t = 1 := by
    have : ((Complex.normSq t : ℝ) : ℂ) = 1 := (Complex.normSq_eq_conj_mul_self).trans e3
    exact_mod_cast this
  have ht1 : ‖t‖ = 1 := by
    have : ‖t‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hns
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg t) two_ne_zero).1 this
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0] at ht1
    simp at ht1
  have h1 : t = Complex.exp ((t.arg : ℂ) * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I t
    rw [ht1, Complex.ofReal_one, one_mul] at this
    exact this.symm
  set u : ℂ := Complex.exp (-(t.arg : ℂ) / 2 * Complex.I) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hcu : conj u = u * t := by
    calc conj u = Complex.exp ((t.arg : ℂ) / 2 * Complex.I) := by
          rw [hu, ← Complex.exp_conj]
          congr 1
          simp only [map_mul, map_div₀, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
          ring
      _ = u * Complex.exp ((t.arg : ℂ) * Complex.I) := by
          rw [hu, ← Complex.exp_add]
          congr 1
          ring
      _ = u * t := by rw [← h1]
  refine ⟨u, fun n ↦ (c n / u).re, fun n ↦ ?_⟩
  have hreal : conj (c n / u) = c n / u := by
    rw [map_div₀, hct' n, hcu]
    field_simp
  have := Complex.conj_eq_iff_re.1 hreal
  rw [this]
  field_simp

end ModularFormsKB.HalfIntegral
