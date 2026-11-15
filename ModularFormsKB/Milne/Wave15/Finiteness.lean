import ModularFormsKB.Milne.Wave15.Splitting
import TauCeti.Analysis.Fredholm.Schwartz

/-!
# Finiteness of the bounded Čech cohomology `Z¹ / δC⁰` of a disc system

Forster, *Lectures on Riemann Surfaces*, Theorem 14.9 (`dim H¹(X, 𝒪) < ∞`), in the form needed for Milne,
*Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.17 (pdf p. 20).

* `surjective_T`: `Z¹(1/2) × C⁰(1/4) → Z¹(1/4)`, `(ζ, η) ↦ ζ|_{1/4} + δη` is surjective: for `ξ ∈ Z¹(1/4)` the
  Dolbeault solutions `fᵢ` of `Splitting.lean` give `ζᵢⱼ = fⱼ - fᵢ` and `ηᵢ = gᵢ - fᵢ`, holomorphic and bounded.
* `finiteDimensional_quotient`: Schwartz's lemma (Tau Ceti,
  `ContinuousLinearMap.cofg_range_add_of_surjective_of_isCompactOperator`) applied to that surjection and the compact
  perturbation `-(ζ ↦ ζ|_{1/4})` shows that `Z¹(1/4) / δC⁰(1/4)` is finite-dimensional.
-/

open Set Metric Topology TopologicalSpace TauCeti Filter
open scoped Manifold ContDiff ComplexConjugate

noncomputable section

namespace ModularFormsKB.Milne.Wave15

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]

namespace DiscSystem

variable {ι : Type*} [Fintype ι] (D : DiscSystem X ι) (ξ : D.Z1 (1 / 4))

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] in
theorem mem_ball_S {t : ℝ} (ht : t ≤ 1) {i : ι} {w : ℂ} (hw : w ∈ ball (D.c i) (t * D.S i)) :
    w ∈ ball (D.c i) (D.S i) := by
  simpa using D.ball_mono ht i hw

/-- The Dolbeault solutions `∂̄fᵢ = ωᵢ` on `B(cᵢ, Sᵢ)`. -/
def fsol : ι → ℂ → ℂ := (D.exists_f ξ).choose

theorem fsol_spec (i : ι) : ContDiffOn ℝ ∞ (D.fsol ξ i) (ball (D.c i) (D.S i)) ∧
    ∀ z ∈ ball (D.c i) (D.S i), conjWirtingerDeriv (D.fsol ξ i) z 1 = D.form ξ i z :=
  (D.exists_f ξ).choose_spec i

theorem differentiableAt_fsol {i : ι} {z : ℂ} (hz : z ∈ ball (D.c i) (D.S i)) :
    DifferentiableAt ℝ (D.fsol ξ i) z :=
  ((D.fsol_spec ξ i).1.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)

theorem exists_bound_fsol (i : ι) :
    ∃ M, ∀ z ∈ closedBall (D.c i) (1 / 2 * D.S i), ‖D.fsol ξ i z‖ ≤ M :=
  (isCompact_closedBall _ _).exists_bound_of_continuousOn ((D.fsol_spec ξ i).1.continuousOn.mono
    (closedBall_subset_ball (by nlinarith [D.S_pos i])))

/-- A bound for `fᵢ` on `B̄(cᵢ, Sᵢ/2)`. -/
def Mf (i : ι) : ℝ := (D.exists_bound_fsol ξ i).choose

theorem norm_fsol_le {i : ι} {z : ℂ} (hz : z ∈ ball (D.c i) (1 / 2 * D.S i)) : ‖D.fsol ξ i z‖ ≤ D.Mf ξ i :=
  (D.exists_bound_fsol ξ i).choose_spec z (ball_subset_closedBall hz)

/-! ### The `0`-cochain `ηᵢ = gᵢ - fᵢ` -/

/-- `ηᵢ = gᵢ - fᵢ`. -/
def etaFun (i : ι) (w : ℂ) : ℂ := D.g ξ i w - D.fsol ξ i w

theorem differentiableOn_etaFun (i : ι) : DifferentiableOn ℂ (D.etaFun ξ i) (D.B (1 / 4) i) := by
  intro w hw
  have hw' : w ∈ ball (D.c i) (1 / 4 * D.S i) := hw
  have hgd : DifferentiableAt ℝ (D.g ξ i) w := (D.contDiffAt_g ξ hw').differentiableAt (by simp)
  have hfd := D.differentiableAt_fsol ξ (D.mem_ball_S (by norm_num) hw')
  have hwt := D.ball_subset_target (by norm_num) i hw'
  have hdbar : conjWirtingerDeriv (D.etaFun ξ i) w 1 = 0 := by
    have h1 : D.etaFun ξ i = D.g ξ i - D.fsol ξ i := rfl
    have hgg : D.g ξ i ∘ D.τ i i =ᶠ[𝓝 w] D.g ξ i :=
      Filter.eventually_of_mem ((D.e i).open_target.mem_nhds hwt) fun w' hw' ↦ by simp [D.τ_self hw']
    rw [h1, conjWirtingerDeriv_sub hgd hfd, ContinuousLinearMap.sub_apply,
      (D.fsol_spec ξ i).2 w (D.mem_ball_S (by norm_num) hw'),
      D.form_eq ξ hwt (D.mem_V_symm (by norm_num) hw'), Dbar, hgg.conjWirtingerDeriv_eq, sub_self]
  exact ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hgd.sub hfd)).2
    hdbar).differentiableWithinAt

theorem norm_etaFun_le {i : ι} {w : ℂ} (hw : w ∈ D.B (1 / 4) i) :
    ‖D.etaFun ξ i w‖ ≤ ∑ k, ‖(ξ : D.C1 (1 / 4)) (i, k)‖ + D.Mf ξ i :=
  (norm_sub_le _ _).trans (add_le_add (D.norm_g_le ξ i w)
    (D.norm_fsol_le ξ (D.ball_mono (by norm_num) i hw)))

/-- The bounded `0`-cochain `η`. -/
def eta : D.C0 (1 / 4) := fun i ↦
  BoundedHolomorphicFunctions.of _ (D.etaFun ξ i) (D.differentiableOn_etaFun ξ i) _
    fun _ hw ↦ D.norm_etaFun_le ξ hw

theorem ext_eta {i : ι} {w : ℂ} (hw : w ∈ D.B (1 / 4) i) : ext (D.eta ξ i) w = D.etaFun ξ i w :=
  ext_of _ (D.differentiableOn_etaFun ξ i) _ (fun _ hw ↦ D.norm_etaFun_le ξ hw) hw

/-! ### The `1`-cocycle `ζᵢⱼ = fⱼ - fᵢ` -/

/-- The transformation law `ωᵢ = conj(τⱼᵢ') · ωⱼ ∘ τⱼᵢ` of the form `ω`. -/
theorem form_transform {i j : ι} {w : ℂ} (hw : w ∈ (D.e i).target) (hj : (D.e i).symm w ∈ (D.e j).source) :
    conj (deriv (D.τ j i) w) * D.form ξ j (D.τ j i w) = D.form ξ i w := by
  obtain ⟨m, hm⟩ := D.exists_V_symm i w
  have hτt : D.τ j i w ∈ (D.e j).target := (D.e j).map_source hj
  have hsym : (D.e j).symm (D.τ j i w) = (D.e i).symm w := (D.e j).left_inv hj
  have hm' : (D.e j).symm (D.τ j i w) ∈ D.V (1 / 4) m := hsym ▸ hm
  rw [D.form_eq ξ hτt hm', D.form_eq ξ hw hm, Dbar, Dbar,
    ← Wave14.conjWirtingerDeriv_comp_holomorphic (D.differentiableAt_g_τ ξ hτt hm')
      (D.differentiableAt_τ hw hj)]
  have : (D.g ξ m ∘ D.τ m j) ∘ D.τ j i =ᶠ[𝓝 w] D.g ξ m ∘ D.τ m i := by
    filter_upwards [(D.isOpen_target_inter_preimage i (D.e j).open_source).mem_nhds ⟨hw, hj⟩] with w' hw'
    simp only [Function.comp_apply, D.τ_τ hw'.2]
  rw [this.conjWirtingerDeriv_eq]

/-- `ζᵢⱼ = fⱼ ∘ τⱼᵢ - fᵢ`. -/
def zetaFun (i j : ι) (w : ℂ) : ℂ := D.fsol ξ j (D.τ j i w) - D.fsol ξ i w

theorem differentiableOn_zetaFun (i j : ι) : DifferentiableOn ℂ (D.zetaFun ξ i j) (D.Ω (1 / 2) i j) := by
  intro w hw
  have hτB : D.τ j i w ∈ ball (D.c j) (1 / 2 * D.S j) := D.τ_mem_B_of_mem_Ω hw
  have hτ : DifferentiableAt ℂ (D.τ j i) w := D.differentiableAt_τ_of_mem_Ω hw
  have hfj := D.differentiableAt_fsol ξ (D.mem_ball_S (by norm_num) hτB)
  have hfi := D.differentiableAt_fsol ξ (D.mem_ball_S (by norm_num) hw.1)
  have hcomp : DifferentiableAt ℝ (D.fsol ξ j ∘ D.τ j i) w := hfj.comp w (hτ.restrictScalars ℝ)
  have hdbar : conjWirtingerDeriv (D.zetaFun ξ i j) w 1 = 0 := by
    have h1 : D.zetaFun ξ i j = D.fsol ξ j ∘ D.τ j i - D.fsol ξ i := rfl
    rw [h1, conjWirtingerDeriv_sub hcomp hfi, ContinuousLinearMap.sub_apply,
      Wave14.conjWirtingerDeriv_comp_holomorphic hfj hτ,
      (D.fsol_spec ξ j).2 _ (D.mem_ball_S (by norm_num) hτB),
      (D.fsol_spec ξ i).2 _ (D.mem_ball_S (by norm_num) hw.1), D.form_transform ξ hw.2.1 hw.2.2.1, sub_self]
  exact ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hcomp.sub hfi)).2
    hdbar).differentiableWithinAt

theorem norm_zetaFun_le {i j : ι} {w : ℂ} (hw : w ∈ D.Ω (1 / 2) i j) :
    ‖D.zetaFun ξ i j w‖ ≤ D.Mf ξ j + D.Mf ξ i :=
  (norm_sub_le _ _).trans (add_le_add (D.norm_fsol_le ξ (D.τ_mem_B_of_mem_Ω hw)) (D.norm_fsol_le ξ hw.1))

/-- The bounded `1`-cochain `ζ` of level `1/2`. -/
def zetaC : D.C1 (1 / 2) := fun p ↦
  BoundedHolomorphicFunctions.of _ (D.zetaFun ξ p.1 p.2) (D.differentiableOn_zetaFun ξ p.1 p.2) _
    fun _ hw ↦ D.norm_zetaFun_le ξ hw

theorem ext_zetaC (p : ι × ι) {w : ℂ} (hw : w ∈ D.Ω (1 / 2) p.1 p.2) :
    ext (D.zetaC ξ p) w = D.zetaFun ξ p.1 p.2 w :=
  ext_of _ (D.differentiableOn_zetaFun ξ p.1 p.2) _ (fun _ hw ↦ D.norm_zetaFun_le ξ hw) hw

theorem zetaC_mem : D.zetaC ξ ∈ D.Z1 (1 / 2) := by
  intro i j k x hi hj hk
  rw [D.ext_zetaC ξ (i, j) (D.e_mem_Ω hi hj), D.ext_zetaC ξ (j, k) (D.e_mem_Ω hj hk),
    D.ext_zetaC ξ (i, k) (D.e_mem_Ω hi hk)]
  simp only [zetaFun, D.τ_apply_e hi.1, D.τ_apply_e hj.1]
  ring

/-- The cocycle `ζ ∈ Z¹(1/2)`. -/
def zeta : D.Z1 (1 / 2) := ⟨D.zetaC ξ, D.zetaC_mem ξ⟩

/-- **The decomposition** `ξ = ζ|_{1/4} + δη`. -/
theorem res_zeta_add_delta_eta :
    D.res (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) (D.zeta ξ) + D.delta (1 / 4) (D.eta ξ) = ξ := by
  refine Subtype.ext (funext fun p ↦ bhf_ext_eq fun w hw ↦ ?_)
  obtain ⟨i, j⟩ := p
  have hxi : (D.e i).symm w ∈ D.V (1 / 4) i := D.mem_V_symm (by norm_num) hw.1
  have hsplit := D.g_split ξ hxi hw.2.2
  rw [(D.e i).right_inv hw.2.1] at hsplit
  rw [Submodule.coe_add, D.C1_add_apply, ext_add, D.ext_res _ _ _ hw, D.ext_delta _ _ hw,
    D.ext_eta ξ (D.τ_mem_B_of_mem_Ω hw), D.ext_eta ξ hw.1]
  change ext (D.zetaC ξ (i, j)) w + _ = _
  rw [D.ext_zetaC ξ (i, j) (D.Ω_mono (by norm_num) i j hw), hsplit]
  simp only [zetaFun, etaFun, τ]
  ring

/-- The map `T(ζ, η) = ζ|_{1/4} + δη`. -/
def T : D.Z1 (1 / 2) × D.C0 (1 / 4) →L[ℂ] D.Z1 (1 / 4) :=
  (D.res (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)).comp (ContinuousLinearMap.fst ℂ (D.Z1 (1 / 2)) (D.C0 (1 / 4))) +
    (D.delta (1 / 4)).comp (ContinuousLinearMap.snd ℂ (D.Z1 (1 / 2)) (D.C0 (1 / 4)))

omit [T2Space X] in
theorem T_apply (z : D.Z1 (1 / 2) × D.C0 (1 / 4)) :
    D.T z = D.res (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) z.1 + D.delta (1 / 4) z.2 := rfl

theorem surjective_T : Function.Surjective D.T := fun ξ ↦
  ⟨(D.zeta ξ, D.eta ξ), by rw [T_apply]; exact D.res_zeta_add_delta_eta ξ⟩

/-- **Forster 14.9 for the disc system**: `Z¹(1/4) / δC⁰(1/4)` is finite-dimensional, in the form used below:
there is `N` such that for every linear map `Φ : ℂᴺ → Z¹(1/4)` some nonzero `c` has `Φ c ∈ δC⁰(1/4)`. -/
theorem exists_ne_zero_delta_eq :
    ∃ N : ℕ, ∀ Φ : (Fin N → ℂ) →ₗ[ℂ] D.Z1 (1 / 4), ∃ c ≠ 0, ∃ η : D.C0 (1 / 4), D.delta (1 / 4) η = Φ c := by
  let K : D.Z1 (1 / 2) × D.C0 (1 / 4) →L[ℂ] D.Z1 (1 / 4) :=
    -(D.res (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)).comp (ContinuousLinearMap.fst ℂ (D.Z1 (1 / 2)) (D.C0 (1 / 4)))
  have hK : IsCompactOperator K :=
    ((D.isCompactOperator_res (by norm_num : (1 / 4 : ℝ) < 1 / 2) (by norm_num)).comp_clm _).neg
  have h := ContinuousLinearMap.cofg_range_add_of_surjective_of_isCompactOperator D.T K D.surjective_T hK
  set R := LinearMap.range ((D.T + K : _ →L[ℂ] _) : D.Z1 (1 / 2) × D.C0 (1 / 4) →ₗ[ℂ] D.Z1 (1 / 4)) with hR
  have hfin : Module.Finite ℂ (D.Z1 (1 / 4) ⧸ R) := h
  refine ⟨Module.finrank ℂ (D.Z1 (1 / 4) ⧸ R) + 1, fun Φ ↦ ?_⟩
  have hk : LinearMap.ker (R.mkQ ∘ₗ Φ) ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hcR : Φ c ∈ R := by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
    exact hc
  obtain ⟨z, hz⟩ := hcR
  refine ⟨c, hc0, z.2, ?_⟩
  rw [← hz]
  simp [K, T_apply]

end DiscSystem

end ModularFormsKB.Milne.Wave15
