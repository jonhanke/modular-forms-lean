/-
# $f_{32}$ as a cusp form, and the entire continuation of its twists

`F32Modular` (named input): the $q$-series $f_{32} = \sum b(m)q^m$ is a cusp form of weight $2$ for
$\Gamma_0(32)$ (classical: $f_{32} = \eta(4\tau)^2\eta(8\tau)^2$, the newform of $y^2 = x^3 - x$; as the theta series of
the Hecke character $\alpha \mapsto \alpha$ of $\mathbb Q(i)$ of conductor $(2+2i)$ it is Hecke's theorem, Miyake
Theorem 4.8.2 `miyake1989` [unverified], which the library proves only in the Eisenstein case, LE-MF-0235).

Proved from it:
- `hasQExp_f32`: $f_{32}$ has the $q$-expansion $b$ (unconditional; $|b(m)| \le 6m$);
- `isIntCuspForm_f32`: $f_{32}$ satisfies the library's `IsIntCuspForm 2 128 1`, the form `LiftsTo` asks for;
- `hasEntireExtension_congruentCoeff`: for $n \ge 1$ the $L$-series $\sum \left(\frac nm\right)b(m)m^{-s}$ has an
  entire extension (Tau Ceti `CuspForm.twist` with $\Phi(m) = \left(\frac nm\right)$ on $\mathbb Z/4n$, which is
  well defined on odd $m$ by reciprocity, `jacobiSym.mod_right`, and $b$ vanishes at even $m$;
  then `CuspForm.hasEntireExtension_qExpansion_coeff`).
-/
import ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves.F32Basic
import ModularFormsKB.HalfIntegral.Abstract.Shimura
import ModularFormsKB.HalfIntegral.Abstract.TwistContinuationProof
import TauCeti.NumberTheory.LSeries.Continuation
import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.ModularForms.LFunction.Basic
import TauCeti.NumberTheory.LSeries.EntireExtension
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

namespace ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves

open Complex MatrixGroups CongruenceSubgroup ModularForm
open scoped Real

local notation "ℍ" => UpperHalfPlane

/-- **$f_{32}$ is a cusp form of weight $2$ on $\Gamma_0(32)$** (row 29; Hecke's theorem for the Hecke character
$\alpha \mapsto \alpha$ of $\mathbb Q(i)$, Miyake Theorem 4.8.2 `miyake1989` [unverified]; equivalently
$f_{32} = \eta(4\tau)^2\eta(8\tau)^2$). -/
@[kb "miyake1989" "Thm. 4.8.2 for the Hecke character α ↦ α of Q(i) mod (2+2i): Σ α q^{Nα} ∈ S₂(Γ₀(32)) [unverified]"]
structure F32Modular : Prop where
  exists_cuspForm : ∃ f : CuspForm ((Gamma0 32).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2, ⇑f = f32

/-- $f_{32}$ has the $q$-expansion $b$. -/
theorem hasQExp_f32 : Abstract.HasQExp f32 (fun m ↦ (f32Coeff m : ℂ)) := by
  intro τ
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := by
    rw [Complex.norm_exp, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have : (2 * π * I * (τ : ℂ)).re = -(2 * π * τ.im) := by
      simp [Complex.mul_re]
    rw [this]
    have := τ.im_pos
    have := Real.pi_pos
    nlinarith
  have hs : Summable (fun m : ℕ ↦ (f32Coeff m : ℂ) * cexp (2 * π * I * m * τ)) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := ‖cexp (2 * π * I * τ)‖) (by simpa using hq)
    refine Summable.of_norm_bounded (g := fun m : ℕ ↦ 6 * ((m : ℝ) ^ 1 * ‖cexp (2 * π * I * τ)‖ ^ m))
      (h1.mul_left 6) (fun m ↦ ?_)
    rw [norm_mul]
    have e : cexp (2 * π * I * m * τ) = cexp (2 * π * I * τ) ^ m := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    rw [e, norm_pow]
    have hb : ‖(f32Coeff m : ℂ)‖ ≤ 6 * m := by
      have := abs_f32Coeff_le m
      rw [Complex.norm_intCast]
      exact_mod_cast this
    rw [pow_one, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  exact hs.hasSum

/-- $f_{32}$ is a cusp form of weight $2$, level $128$, trivial character, in the library's sense. -/
theorem isIntCuspForm_f32 (h : F32Modular) : IsIntCuspForm 2 128 1 f32 := by
  obtain ⟨F, hF⟩ := h.exists_cuspForm
  have hd : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      UpperHalfPlane.denom γ τ = (γ 1 0 : ℂ) * τ + γ 1 1 := fun γ τ ↦ ModularGroup.denom_apply γ τ
  have hG0 : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 128 → γ ∈ Gamma0 32 := by
    intro γ hγ
    rw [Gamma0_mem] at hγ ⊢
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 128).mp hγ
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 32).mpr (dvd_trans (by norm_num) this)
  have hmem : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 32 → (F : ℍ → ℂ) ∣[(2 : ℤ)] γ = F := by
    intro γ hγ
    have := F.slash_action_eq' (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      ⟨γ, hγ, rfl⟩
    rwa [← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← ModularForm.SL_slash] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [← hF]; exact CuspFormClass.holo F
  · intro γ hγ τ
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod 128) := by
      have hdet := γ.det_coe
      rw [Matrix.det_fin_two] at hdet
      rw [Gamma0_mem] at hγ
      refine isUnit_iff_exists_inv.mpr ⟨((γ 0 0 : ℤ) : ZMod 128), ?_⟩
      have := congrArg (fun x : ℤ ↦ (x : ZMod 128)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hγ, mul_zero, sub_zero] at this
      rw [mul_comm]; exact this
    have h1 := congrFun (hmem γ (hG0 γ hγ)) τ
    rw [ModularForm.SL_slash_apply] at h1
    try simp only [Pi.smul_apply, smul_eq_mul] at h1
    have hne := UpperHalfPlane.denom_ne_zero γ τ
    rw [hd] at h1 hne
    have h2 : F (γ • τ) = F (γ • τ) * ((γ 1 0 : ℂ) * τ + γ 1 1) ^ (-(2 : ℤ)) *
        ((γ 1 0 : ℂ) * τ + γ 1 1) ^ 2 := by
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hne]
      simp
    rw [← hF, h2, h1, MulChar.one_apply hu]
    ring
  · intro γ
    have h := CuspFormClass.zero_at_infty_slash F γ
    rw [UpperHalfPlane.IsZeroAtImInfty, Filter.ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero] at h ⊢
    refine h.congr (fun τ ↦ ?_)
    rw [← hF, Real.norm_of_nonneg (by positivity), ModularForm.SL_slash_apply, norm_mul, norm_zpow, hd,
      Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, zpow_neg]
    simp [mul_comm]

/-- **Row 33: the twisted $L$-series has an entire extension.** -/
theorem hasEntireExtension_congruentCoeff (h : F32Modular) {n : ℕ} (hn : 0 < n) :
    LSeries.HasEntireExtension (fun m ↦ (congruentCoeff n m : ℂ)) := by
  obtain ⟨F, hF⟩ := h.exists_cuspForm
  have : NeZero (4 * n) := ⟨by omega⟩
  let G : CuspForm ((Gamma1 32).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2 :=
    CuspForm.restrict (Subgroup.map_mono (Gamma1_in_Gamma0 32)) F
  let Φ : ZMod (4 * n) → ℂ := fun x ↦ if Odd x.val then (jacobiSym n x.val : ℂ) else 0
  let T := CuspForm.twist (M := 4 * n) (N := 32) (L := 32 * (4 * n) * (4 * n)) Φ
    (dvd_mul_right _ _) ⟨32, by ring⟩ G
  have hb : ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 G).coeff m = (f32Coeff m : ℂ) := by
    intro m
    symm
    refine ModularFormClass.qExpansion_coeff_unique (Γ := (Gamma1 32).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) (k := 2) (f := G) (c := fun m : ℕ ↦ (f32Coeff m : ℂ)) one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map 32)
      (fun τ ↦ ?_) m
    have hG : G τ = f32 τ := congrFun hF τ
    rw [hG]
    convert hasQExp_f32 τ using 2 with j
    rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hcoef : ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 T).coeff m = (congruentCoeff n m : ℂ) := by
    intro m
    rw [CuspForm.qExpansion_twist_coeff, hb]
    rcases Nat.even_or_odd m with hm | hm
    · simp [congruentCoeff, f32Coeff_of_even hm]
    · have hv : Odd ((m : ZMod (4 * n)).val) := by
        rw [ZMod.val_natCast, Nat.odd_iff, Nat.mod_mod_of_dvd m ⟨2 * n, by ring⟩]
        exact Nat.odd_iff.mp hm
      rw [ZMod.val_natCast] at hv
      have := jacobiSym.mod_right (n : ℤ) hm
      rw [Int.natAbs_natCast] at this
      simp only [Φ, ZMod.val_natCast, if_pos hv]
      rw [← this]
      simp [congruentCoeff]
  have hw := CuspForm.hasEntireExtension_qExpansion_coeff T
  have hwidth : ((Gamma1 (32 * (4 * n) * (4 * n))).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictWidthInfty = 1 := by simp
  rw [hwidth] at hw
  have e : (fun m : ℕ ↦ (congruentCoeff n m : ℂ)) = fun m ↦ (UpperHalfPlane.qExpansion 1 T).coeff m :=
    funext fun m ↦ (hcoef m).symm
  rw [e]
  exact hw

/-- The abscissa of absolute convergence of $\sum \left(\frac nm\right) b(m) m^{-s}$ is at most $2$. -/
theorem abscissaOfAbsConv_congruentCoeff_le (n : ℕ) :
    LSeries.abscissaOfAbsConv (fun m ↦ (congruentCoeff n m : ℂ)) ≤ 2 := by
  have h : LSeries.abscissaOfAbsConv (fun m ↦ (congruentCoeff n m : ℂ)) ≤ (((1 : ℝ) + 1 : ℝ) : EReal) := by
    refine LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (x := 1) ?_
    refine Asymptotics.IsBigO.of_bound 6 (Filter.Eventually.of_forall fun m ↦ ?_)
    have hb := abs_f32Coeff_le m
    have hj : |jacobiSym n m| ≤ 1 := by
      rcases jacobiSym.trichotomy (n : ℤ) m with h | h | h <;> simp [h]
    have h1 : |congruentCoeff n m| ≤ 6 * m := by
      rw [congruentCoeff, abs_mul]
      calc |jacobiSym n m| * |f32Coeff m| ≤ 1 * |f32Coeff m| :=
            mul_le_mul_of_nonneg_right hj (abs_nonneg _)
        _ ≤ 6 * m := by linarith
    rw [Complex.norm_intCast, Real.rpow_one, Real.norm_natCast]
    exact_mod_cast h1
  have e : (((1 : ℝ) + 1 : ℝ) : EReal) = 2 := by
    rw [show ((1 : ℝ) + 1) = 2 by norm_num]; first | rfl | exact EReal.coe_ofNat 2 | simp
  rwa [e] at h

end ModularFormsKB.HalfIntegral.Waldspurger.CongruentCurves
