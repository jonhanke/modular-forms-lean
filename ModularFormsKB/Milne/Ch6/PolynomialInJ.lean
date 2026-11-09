import ModularFormsKB.Milne.Ch6.LevelTwoVanishing
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Level-one modular functions holomorphic on $\mathbb H$ are polynomials in $j$

A holomorphic function $f$ on $\mathbb H$ invariant under $\mathrm{SL}_2(\mathbb Z)$ with at most a pole of order $m$
at $i\infty$ (that is, $q^m f$ bounded at $i\infty$, $q = e^{2\pi i z}$) is $P(j)$ for a polynomial $P \in \mathbb C[X]$ of
degree at most $m$ (Milne, Section 6, proof of Theorem 6.1, pdf p. 88). Proof: induction on $m$; for $m = 0$ a level-one
modular form of weight $0$ is constant (Mathlib's `ModularFormClass.levelOne_weight_zero_const`); in general subtract
$c j^m$ with $c = \lim q^m f$, using $qj \to 1$ (Tau Ceti's `TauCeti.ModularForm.tendsto_qParam_mul_j_atImInfty`).
-/

open UpperHalfPlane ModularForm Filter Topology Polynomial ModularGroup
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne.LevelTwo

open TauCeti.ModularForm

theorem periodic_of_T {F : ℍ → ℂ} (hT : ∀ z, F (T • z) = F z) :
    Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1 := by
  refine UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ ?_
  rw [← hT τ]
  congr 1
  ext
  rw [coe_T_smul]
  simp [add_comm]

theorem tendsto_cusp {F : ℍ → ℂ} (hT : ∀ z, F (T • z) = F z) (hmd : MDiff F)
    (hb : IsBoundedAtImInfty F) :
    Tendsto F atImInfty (𝓝 (UpperHalfPlane.cuspFunction 1 F 0)) := by
  have hper := periodic_of_T hT
  have han := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hper hmd hb
  have : (UpperHalfPlane.cuspFunction 1 F ∘ fun τ ↦ Function.Periodic.qParam 1 (τ : ℂ) : ℍ → ℂ) = F := by
    funext τ
    simpa using UpperHalfPlane.eq_cuspFunction τ one_ne_zero hper
  simpa [this] using han.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)

theorem bdd_div_q {F : ℍ → ℂ} (hT : ∀ z, F (T • z) = F z) (hmd : MDiff F)
    (hb : IsBoundedAtImInfty F) (h0 : Tendsto F atImInfty (𝓝 0)) :
    IsBoundedAtImInfty (fun z : ℍ ↦ F z / Function.Periodic.qParam 1 (z : ℂ)) := by
  have hper := periodic_of_T hT
  have han := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hper hmd hb
  have hc : UpperHalfPlane.cuspFunction 1 F 0 = 0 :=
    tendsto_nhds_unique (tendsto_cusp hT hmd hb) h0
  have hq0 : (UpperHalfPlane.qExpansion 1 F).coeff 0 = 0 := by
    simp [UpperHalfPlane.qExpansion_coeff, hc]
  exact (TauCeti.UpperHalfPlane.tendsto_div_qParam_atImInfty one_pos hper han.differentiableAt
    hq0).isBigO_one ℝ

/-- **Polynomials in $j$.** -/
theorem exists_polynomial_of_invariant (m : ℕ) {f : ℍ → ℂ} (hmd : MDiff f)
    (hinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = f z)
    (hbdd : IsBoundedAtImInfty (fun z : ℍ ↦ Function.Periodic.qParam 1 (z : ℂ) ^ m * f z)) :
    ∃ P : ℂ[X], P.natDegree ≤ m ∧ ∀ z : ℍ, f z = P.eval (j z) := by
  induction m generalizing f with
  | zero =>
    simp only [pow_zero, one_mul] at hbdd
    have hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f := fun γ ↦ by
      funext τ; simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]; exact hinv γ τ
    let F : ModularForm 𝒮ℒ 0 :=
      { toFun := f
        slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hslash γ
        holo' := hmd
        bdd_at_cusps' := fun hc ↦ (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦
          (hslash γ).symm ▸ hbdd }
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
    have he : f = Function.const _ c := hc
    exact ⟨C c, by simp, fun z ↦ by simp [he]⟩
  | succ m ih =>
    have hT : ∀ z, f (T • z) = f z := fun z ↦ hinv T z
    have hqmd : MDiff (fun z : ℍ ↦ Function.Periodic.qParam 1 (z : ℂ)) :=
      Function.Periodic.differentiable_qParam.mdifferentiable.comp mdifferentiable_coe
    have hqT : ∀ z : ℍ, Function.Periodic.qParam 1 ((T • z : ℍ) : ℂ) =
        Function.Periodic.qParam 1 (z : ℂ) := fun z ↦ by
      rw [coe_T_smul]
      simp [Function.Periodic.qParam, mul_add, Complex.exp_add]
    set g : ℍ → ℂ := fun z ↦ Function.Periodic.qParam 1 (z : ℂ) ^ (m + 1) * f z with hg
    have hgmd : MDiff g := (hqmd.pow (m + 1)).mul hmd
    have hgT : ∀ z, g (T • z) = g z := fun z ↦ by simp only [hg, hT, hqT]
    set c := UpperHalfPlane.cuspFunction 1 g 0
    have hgc : Tendsto g atImInfty (𝓝 c) := tendsto_cusp hgT hgmd hbdd
    set h : ℍ → ℂ := fun z ↦ f z - c * j z ^ (m + 1) with hh
    have hjmd : MDiff (fun z ↦ j z ^ (m + 1)) := j_mdifferentiable.pow (m + 1)
    have hhmd : MDiff h := hmd.sub (hjmd.const_smul c)
    have hhinv : ∀ (γ : SL(2, ℤ)) (z : ℍ), h (γ • z) = h z := fun γ z ↦ by
      have hj : j (γ • z) = j z := j_smul γ z
      simp only [hh, hinv, hj]
    set k : ℍ → ℂ := fun z ↦ Function.Periodic.qParam 1 (z : ℂ) ^ (m + 1) * h z with hk
    have hkmd : MDiff k := (hqmd.pow (m + 1)).mul hhmd
    have hkT : ∀ z, k (T • z) = k z := fun z ↦ by simp only [hk, hhinv, hqT]
    have hkeq : ∀ z, k z = g z - c * (Function.Periodic.qParam 1 (z : ℂ) * j z) ^ (m + 1) :=
      fun z ↦ by simp only [hk, hg, hh]; ring
    have hk0 : Tendsto k atImInfty (𝓝 0) := by
      have := hgc.sub ((tendsto_qParam_mul_j_atImInfty.pow (m + 1)).const_mul c)
      simp only [one_pow, mul_one, sub_self] at this
      exact this.congr fun z ↦ (hkeq z).symm
    have hkb : IsBoundedAtImInfty k := hk0.isBigO_one ℝ
    have hdiv := bdd_div_q hkT hkmd hkb hk0
    have hdiv' : IsBoundedAtImInfty (fun z : ℍ ↦ Function.Periodic.qParam 1 (z : ℂ) ^ m * h z) := by
      refine hdiv.congr' (Eventually.of_forall fun z ↦ ?_) ?_
      · have : Function.Periodic.qParam 1 (z : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
        simp only [hk]
        field_simp
        ring
      · exact Filter.EventuallyEq.rfl
    obtain ⟨P, hP, hPe⟩ := ih hhmd hhinv hdiv'
    refine ⟨P + C c * X ^ (m + 1), ?_, fun z ↦ ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le (hP.trans (Nat.le_succ m)) ?_)
      exact (natDegree_C_mul_le _ _).trans (by simp)
    · have := hPe z
      simp only [hh] at this
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, ← this]
      ring

end ModularFormsKB.Milne.LevelTwo
