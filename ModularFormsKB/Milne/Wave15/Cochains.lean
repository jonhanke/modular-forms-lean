import ModularFormsKB.Milne.RiemannSurface.Basic
import TauCeti.Analysis.Complex.HolomorphicFunctions.Bounded
import TauCeti.Geometry.Manifold.Complex.Chart

/-!
# Bounded holomorphic Čech cochains on a finite disc cover of a Riemann surface

Forster, *Lectures on Riemann Surfaces*, §14 (the finiteness theorem for `H¹(X, 𝒪)`), as used for Milne,
*Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.17 (pdf p. 20).

A **disc system** on a Riemann surface `X` is a finite family of points `xᵢ` with radii `Sᵢ > 0` such that the closed
disc of radius `Sᵢ` about `zᵢ(xᵢ)` lies in the target of the preferred chart `zᵢ = chartAt ℂ xᵢ`, and the discs
`Vᵢ(1/8)` cover `X`, where `Vᵢ(t) = zᵢ⁻¹(B(zᵢ(xᵢ), t Sᵢ))`.

For `0 < t ≤ 1` the **cochains** of level `t` are, in the coordinate `zᵢ`,
* `C⁰(t) = ∏ᵢ H^∞(B(cᵢ, t Sᵢ))`,
* `C¹(t) = ∏_{i,j} H^∞(Ωᵢⱼ(t))`, `Ωᵢⱼ(t) = zᵢ(Vᵢ(t) ∩ Vⱼ(t))`,

with Tau Ceti's Banach spaces `H^∞` of bounded holomorphic functions (`TauCeti.boundedHolomorphicFunctions`). The
cocycles `Z¹(t)` form a closed subspace (`isClosed_Z1`), the coboundary `δ : C⁰(t) → Z¹(t)` is continuous
(`delta`), and restriction `Z¹(t') → Z¹(t)` is a compact operator for `t < t'` (`isCompactOperator_res`, Montel's
theorem in Tau Ceti's form `TauCeti.BoundedHolomorphicFunctions.isCompactOperator_restrict`).
-/

open Set Metric Topology TopologicalSpace TauCeti BoundedContinuousFunction
open scoped Manifold

noncomputable section

namespace ModularFormsKB.Milne.Wave15

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A **disc system** on `X`: finitely many preferred charts `zᵢ = chartAt ℂ (pt i)` with closed discs
`B̄(zᵢ(ptᵢ), Sᵢ)` inside their targets, such that the discs of radius `Sᵢ / 8` cover `X`. -/
structure DiscSystem (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] (ι : Type*) where
  /-- The centres. -/
  pt : ι → X
  /-- The outer radii. -/
  S : ι → ℝ
  S_pos : ∀ i, 0 < S i
  closedBall_subset : ∀ i, closedBall (chartAt ℂ (pt i) (pt i)) (S i) ⊆ (chartAt ℂ (pt i)).target
  cover : ∀ x : X, ∃ i, x ∈ (chartAt ℂ (pt i)).source ∧
    chartAt ℂ (pt i) x ∈ ball (chartAt ℂ (pt i) (pt i)) (S i / 8)

namespace DiscSystem

variable {ι : Type*} (D : DiscSystem X ι)

/-- The chart `zᵢ`. -/
abbrev e (i : ι) := chartAt ℂ (D.pt i)

/-- The centre `cᵢ = zᵢ(ptᵢ)`. -/
abbrev c (i : ι) : ℂ := D.e i (D.pt i)

/-- The disc `B(cᵢ, t Sᵢ)` as an open set of `ℂ`. -/
def B (t : ℝ) (i : ι) : Opens ℂ := ⟨ball (D.c i) (t * D.S i), isOpen_ball⟩

theorem mem_B {t : ℝ} {i : ι} {w : ℂ} : w ∈ D.B t i ↔ w ∈ ball (D.c i) (t * D.S i) := Iff.rfl

/-- The coordinate disc `Vᵢ(t) = zᵢ⁻¹(B(cᵢ, t Sᵢ))` on `X`. -/
def V (t : ℝ) (i : ι) : Set X := (D.e i).source ∩ D.e i ⁻¹' ball (D.c i) (t * D.S i)

theorem mem_V {t : ℝ} {i : ι} {x : X} :
    x ∈ D.V t i ↔ x ∈ (D.e i).source ∧ D.e i x ∈ ball (D.c i) (t * D.S i) := Iff.rfl

theorem isOpen_V (t : ℝ) (i : ι) : IsOpen (D.V t i) :=
  (D.e i).continuousOn.isOpen_inter_preimage (D.e i).open_source isOpen_ball

theorem ball_subset_target {t : ℝ} (ht : t ≤ 1) (i : ι) :
    ball (D.c i) (t * D.S i) ⊆ (D.e i).target := fun w hw ↦
  D.closedBall_subset i (mem_closedBall.2 ((mem_ball.1 hw).le.trans
    (by nlinarith [D.S_pos i])))

theorem closedBall_subset_target {t : ℝ} (ht : t ≤ 1) (i : ι) :
    closedBall (D.c i) (t * D.S i) ⊆ (D.e i).target := fun w hw ↦
  D.closedBall_subset i (mem_closedBall.2 ((mem_closedBall.1 hw).trans
    (by nlinarith [D.S_pos i])))

theorem ball_mono {t t' : ℝ} (h : t ≤ t') (i : ι) :
    ball (D.c i) (t * D.S i) ⊆ ball (D.c i) (t' * D.S i) :=
  ball_subset_ball (by nlinarith [D.S_pos i])

theorem V_mono {t t' : ℝ} (h : t ≤ t') (i : ι) : D.V t i ⊆ D.V t' i := fun _ hx ↦
  ⟨hx.1, D.ball_mono h i hx.2⟩

theorem mem_V_symm {t : ℝ} (ht : t ≤ 1) {i : ι} {w : ℂ} (hw : w ∈ ball (D.c i) (t * D.S i)) :
    (D.e i).symm w ∈ D.V t i :=
  ⟨(D.e i).map_target (D.ball_subset_target ht i hw), by
    show D.e i ((D.e i).symm w) ∈ ball (D.c i) (t * D.S i)
    rw [(D.e i).right_inv (D.ball_subset_target ht i hw)]; exact hw⟩

theorem exists_mem_V (x : X) : ∃ i, x ∈ D.V (1 / 8) i := by
  obtain ⟨i, h1, h2⟩ := D.cover x
  exact ⟨i, h1, by rwa [one_div, inv_mul_eq_div]⟩

/-- The transition map `τⱼᵢ = zⱼ ∘ zᵢ⁻¹`. -/
def τ (j i : ι) : ℂ → ℂ := fun w ↦ D.e j ((D.e i).symm w)

theorem τ_apply_e {i j : ι} {x : X} (hx : x ∈ (D.e i).source) : D.τ j i (D.e i x) = D.e j x := by
  simp [τ, (D.e i).left_inv hx]

theorem τ_self {i : ι} {w : ℂ} (hw : w ∈ (D.e i).target) : D.τ i i w = w :=
  (D.e i).right_inv hw

theorem τ_τ {i j k : ι} {w : ℂ} (hw : (D.e i).symm w ∈ (D.e j).source) :
    D.τ k j (D.τ j i w) = D.τ k i w := by
  simp [τ, (D.e j).left_inv hw]

/-- Transition maps are holomorphic. -/
theorem analyticAt_τ [IsManifold 𝓘(ℂ) 1 X] {i j : ι} {w : ℂ} (hw : w ∈ (D.e i).target)
    (hj : (D.e i).symm w ∈ (D.e j).source) : AnalyticAt ℂ (D.τ j i) w := by
  have h := TauCeti.analyticAt_symm_trans
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (D.pt i))
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := 1) (D.pt j))
    ((D.e i).map_target hw) hj
  rw [(D.e i).right_inv hw] at h
  exact h

theorem differentiableAt_τ [IsManifold 𝓘(ℂ) 1 X] {i j : ι} {w : ℂ} (hw : w ∈ (D.e i).target)
    (hj : (D.e i).symm w ∈ (D.e j).source) : DifferentiableAt ℂ (D.τ j i) w :=
  (D.analyticAt_τ hw hj).differentiableAt

/-- The nonempty open set `{w ∈ target zᵢ : zᵢ⁻¹ w ∈ s}` for an open set `s` of `X`. -/
theorem isOpen_target_inter_preimage (i : ι) {s : Set X} (hs : IsOpen s) :
    IsOpen ((D.e i).target ∩ (D.e i).symm ⁻¹' s) :=
  (D.e i).continuousOn_symm.isOpen_inter_preimage (D.e i).open_target hs

/-! ### The overlaps `Ωᵢⱼ(t)` -/

/-- The overlap `Ωᵢⱼ(t) = zᵢ(Vᵢ(t) ∩ Vⱼ(t))`, an open set of `ℂ`. -/
def Ω (t : ℝ) (i j : ι) : Opens ℂ :=
  ⟨ball (D.c i) (t * D.S i) ∩ ((D.e i).target ∩ (D.e i).symm ⁻¹' D.V t j),
    isOpen_ball.inter (D.isOpen_target_inter_preimage i (D.isOpen_V t j))⟩

theorem mem_Ω {t : ℝ} {i j : ι} {w : ℂ} :
    w ∈ D.Ω t i j ↔ w ∈ ball (D.c i) (t * D.S i) ∧ w ∈ (D.e i).target ∧ (D.e i).symm w ∈ D.V t j :=
  Iff.rfl

theorem e_mem_Ω {t : ℝ} {i j : ι} {x : X} (hi : x ∈ D.V t i) (hj : x ∈ D.V t j) :
    D.e i x ∈ D.Ω t i j :=
  ⟨hi.2, (D.e i).map_source hi.1, by
    show (D.e i).symm (D.e i x) ∈ D.V t j
    rwa [(D.e i).left_inv hi.1]⟩

theorem Ω_mono {t t' : ℝ} (h : t ≤ t') (i j : ι) : D.Ω t i j ≤ D.Ω t' i j := fun _ hw ↦
  ⟨D.ball_mono h i hw.1, hw.2.1, D.V_mono h j hw.2.2⟩

theorem τ_mem_B_of_mem_Ω {t : ℝ} {i j : ι} {w : ℂ} (hw : w ∈ D.Ω t i j) : D.τ j i w ∈ D.B t j :=
  hw.2.2.2

theorem differentiableAt_τ_of_mem_Ω [IsManifold 𝓘(ℂ) 1 X] {t : ℝ} {i j : ι} {w : ℂ} (hw : w ∈ D.Ω t i j) :
    DifferentiableAt ℂ (D.τ j i) w :=
  D.differentiableAt_τ hw.2.1 hw.2.2.1

end DiscSystem

/-! ### Values of bounded holomorphic functions -/

/-- The zero extension `ℂ → ℂ` of a bounded holomorphic function. -/
abbrev ext {U : Opens ℂ} (f : boundedHolomorphicFunctions ℂ U) : ℂ → ℂ :=
  BoundedHolomorphicFunctions.extend f

theorem ext_of_mem {U : Opens ℂ} (f : boundedHolomorphicFunctions ℂ U) {z : ℂ} (hz : z ∈ U) :
    ext f z = (f : U →ᵇ ℂ) ⟨z, hz⟩ :=
  BoundedHolomorphicFunctions.extend_apply f ⟨z, hz⟩

theorem ext_of_not_mem {U : Opens ℂ} (f : boundedHolomorphicFunctions ℂ U) {z : ℂ} (hz : z ∉ U) :
    ext f z = 0 :=
  BoundedHolomorphicFunctions.extend_apply_of_notMem f hz

@[simp]
theorem ext_add {U : Opens ℂ} (f g : boundedHolomorphicFunctions ℂ U) (z : ℂ) :
    ext (f + g) z = ext f z + ext g z := by
  by_cases hz : z ∈ U
  · simp [ext_of_mem _ hz]
  · simp [ext_of_not_mem _ hz]

@[simp]
theorem ext_smul {U : Opens ℂ} (a : ℂ) (f : boundedHolomorphicFunctions ℂ U) (z : ℂ) :
    ext (a • f) z = a * ext f z := by
  by_cases hz : z ∈ U
  · simp [ext_of_mem _ hz]
  · simp [ext_of_not_mem _ hz]

@[simp]
theorem ext_zero {U : Opens ℂ} (z : ℂ) : ext (0 : boundedHolomorphicFunctions ℂ U) z = 0 := by
  by_cases hz : z ∈ U
  · simp [ext_of_mem _ hz]
  · simp [ext_of_not_mem _ hz]

@[simp]
theorem ext_neg {U : Opens ℂ} (f : boundedHolomorphicFunctions ℂ U) (z : ℂ) :
    ext (-f) z = -ext f z := by
  by_cases hz : z ∈ U
  · simp [ext_of_mem _ hz]
  · simp [ext_of_not_mem _ hz]

@[simp]
theorem ext_sub {U : Opens ℂ} (f g : boundedHolomorphicFunctions ℂ U) (z : ℂ) :
    ext (f - g) z = ext f z - ext g z := by
  rw [sub_eq_add_neg, ext_add, ext_neg, sub_eq_add_neg]

theorem ext_of {U : Opens ℂ} (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g U) (C : ℝ)
    (hC : ∀ z ∈ U, ‖g z‖ ≤ C) {z : ℂ} (hz : z ∈ U) :
    ext (BoundedHolomorphicFunctions.of U g hg C hC) z = g z := by
  rw [ext_of_mem _ hz]; rfl

theorem ext_restrict {U U' : Opens ℂ} (h : U' ≤ U) (f : boundedHolomorphicFunctions ℂ U) {z : ℂ}
    (hz : z ∈ U') : ext (BoundedHolomorphicFunctions.restrict h f) z = ext f z := by
  rw [ext_of_mem _ hz, ext_of_mem _ (h hz)]; rfl

theorem norm_ext_le {U : Opens ℂ} (f : boundedHolomorphicFunctions ℂ U) (z : ℂ) : ‖ext f z‖ ≤ ‖f‖ :=
  BoundedHolomorphicFunctions.norm_extend_apply_le f z

theorem differentiableAt_ext {U : Opens ℂ} (f : boundedHolomorphicFunctions ℂ U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℂ (ext f) z :=
  (BoundedHolomorphicFunctions.differentiableOn_extend f).differentiableAt (U.isOpen.mem_nhds hz)

theorem continuous_ext_apply {U : Opens ℂ} (z : ℂ) :
    Continuous fun f : boundedHolomorphicFunctions ℂ U ↦ ext f z := by
  by_cases hz : z ∈ U
  · simp_rw [ext_of_mem _ hz]
    exact (continuous_eval_const _).comp continuous_subtype_val
  · simp_rw [ext_of_not_mem _ hz]
    exact continuous_const

theorem bhf_ext_eq {U : Opens ℂ} {f g : boundedHolomorphicFunctions ℂ U} (h : ∀ z ∈ U, ext f z = ext g z) :
    f = g := by
  refine Subtype.ext (BoundedContinuousFunction.ext fun z ↦ ?_)
  have := h z z.2
  rwa [ext_of_mem _ z.2, ext_of_mem _ z.2] at this

namespace DiscSystem

variable {ι : Type*} [Fintype ι] (D : DiscSystem X ι)

/-! ### Cochains and cocycles -/

/-- The `0`-cochains of level `t`. -/
def C0 (t : ℝ) : Type _ := ∀ i : ι, boundedHolomorphicFunctions ℂ (D.B t i)

noncomputable instance (t : ℝ) : NormedAddCommGroup (D.C0 t) :=
  inferInstanceAs (NormedAddCommGroup (∀ i : ι, boundedHolomorphicFunctions ℂ (D.B t i)))
noncomputable instance (t : ℝ) : NormedSpace ℂ (D.C0 t) :=
  inferInstanceAs (NormedSpace ℂ (∀ i : ι, boundedHolomorphicFunctions ℂ (D.B t i)))
instance (t : ℝ) : CompleteSpace (D.C0 t) :=
  inferInstanceAs (CompleteSpace (∀ i : ι, boundedHolomorphicFunctions ℂ (D.B t i)))
instance (t : ℝ) : CoeFun (D.C0 t) fun _ ↦ ∀ i : ι, boundedHolomorphicFunctions ℂ (D.B t i) := ⟨id⟩

/-- The `1`-cochains of level `t`. -/
def C1 (t : ℝ) : Type _ := ∀ p : ι × ι, boundedHolomorphicFunctions ℂ (D.Ω t p.1 p.2)

noncomputable instance (t : ℝ) : NormedAddCommGroup (D.C1 t) :=
  inferInstanceAs (NormedAddCommGroup (∀ p : ι × ι, boundedHolomorphicFunctions ℂ (D.Ω t p.1 p.2)))
noncomputable instance (t : ℝ) : NormedSpace ℂ (D.C1 t) :=
  inferInstanceAs (NormedSpace ℂ (∀ p : ι × ι, boundedHolomorphicFunctions ℂ (D.Ω t p.1 p.2)))
instance (t : ℝ) : CompleteSpace (D.C1 t) :=
  inferInstanceAs (CompleteSpace (∀ p : ι × ι, boundedHolomorphicFunctions ℂ (D.Ω t p.1 p.2)))
instance (t : ℝ) : CoeFun (D.C1 t) fun _ ↦ ∀ p : ι × ι, boundedHolomorphicFunctions ℂ (D.Ω t p.1 p.2) :=
  ⟨id⟩

@[simp] theorem C1_add_apply {t : ℝ} (ξ ζ : D.C1 t) (p : ι × ι) : (ξ + ζ) p = ξ p + ζ p := rfl
@[simp] theorem C1_smul_apply {t : ℝ} (a : ℂ) (ξ : D.C1 t) (p : ι × ι) : (a • ξ) p = a • ξ p := rfl
@[simp] theorem C1_zero_apply {t : ℝ} (p : ι × ι) : (0 : D.C1 t) p = 0 := rfl
@[simp] theorem C0_add_apply {t : ℝ} (ξ ζ : D.C0 t) (i : ι) : (ξ + ζ) i = ξ i + ζ i := rfl
@[simp] theorem C0_smul_apply {t : ℝ} (a : ℂ) (ξ : D.C0 t) (i : ι) : (a • ξ) i = a • ξ i := rfl
theorem C1_norm_apply_le {t : ℝ} (ξ : D.C1 t) (p : ι × ι) : ‖ξ p‖ ≤ ‖ξ‖ :=
  norm_le_pi_norm (f := fun p : ι × ι ↦ (ξ p : boundedHolomorphicFunctions ℂ (D.Ω t p.1 p.2))) p
theorem C0_norm_apply_le {t : ℝ} (η : D.C0 t) (i : ι) : ‖η i‖ ≤ ‖η‖ :=
  norm_le_pi_norm (f := fun i : ι ↦ (η i : boundedHolomorphicFunctions ℂ (D.B t i))) i
theorem C1_norm_le {t : ℝ} {ξ : D.C1 t} {r : ℝ} (hr : 0 ≤ r) (h : ∀ p, ‖ξ p‖ ≤ r) : ‖ξ‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg (x := fun p : ι × ι ↦ (ξ p : boundedHolomorphicFunctions ℂ (D.Ω t p.1 p.2)))
    hr).2 h
theorem C1_ext {t : ℝ} {ξ ζ : D.C1 t} (h : ∀ p, ξ p = ζ p) : ξ = ζ := funext h

/-- The cocycle condition `ξᵢⱼ + ξⱼₖ = ξᵢₖ` on `Vᵢ ∩ Vⱼ ∩ Vₖ`, read in the coordinates of the first index. -/
def IsCocycle {t : ℝ} (ξ : D.C1 t) : Prop :=
  ∀ i j k : ι, ∀ x ∈ D.V t i, x ∈ D.V t j → x ∈ D.V t k →
    ext (ξ (i, j)) (D.e i x) + ext (ξ (j, k)) (D.e j x) = ext (ξ (i, k)) (D.e i x)

/-- The cocycles `Z¹(t)`. -/
def Z1 (t : ℝ) : Submodule ℂ (D.C1 t) where
  carrier := {ξ | D.IsCocycle ξ}
  zero_mem' := by intro i j k x _ _ _; simp
  add_mem' := by
    intro ξ ζ hξ hζ i j k x hi hj hk
    simp only [C1_add_apply, ext_add]
    rw [← hξ i j k x hi hj hk, ← hζ i j k x hi hj hk]; ring
  smul_mem' := by
    intro a ξ hξ i j k x hi hj hk
    simp only [C1_smul_apply, ext_smul]
    rw [← hξ i j k x hi hj hk]; ring

theorem isClosed_Z1 (t : ℝ) : IsClosed (D.Z1 t : Set (D.C1 t)) := by
  have : (D.Z1 t : Set (D.C1 t)) = ⋂ (i : ι) (j : ι) (k : ι) (x : X)
      (_ : x ∈ D.V t i ∧ x ∈ D.V t j ∧ x ∈ D.V t k),
      {ξ | ext (ξ (i, j)) (D.e i x) + ext (ξ (j, k)) (D.e j x) = ext (ξ (i, k)) (D.e i x)} := by
    ext ξ
    simp only [SetLike.mem_coe, mem_iInter, mem_ofPred_eq]
    exact ⟨fun h i j k x hx ↦ h i j k x hx.1 hx.2.1 hx.2.2, fun h i j k x hi hj hk ↦ h i j k x ⟨hi, hj, hk⟩⟩
  rw [this]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun k ↦ isClosed_iInter fun x ↦
    isClosed_iInter fun _ ↦ isClosed_eq ?_ ?_
  · exact Continuous.add ((continuous_ext_apply (D.e i x)).comp (continuous_apply (i, j)))
      ((continuous_ext_apply (D.e j x)).comp (continuous_apply (j, k)))
  · exact (continuous_ext_apply (D.e i x)).comp (continuous_apply (i, k))

instance (t : ℝ) : CompleteSpace (D.Z1 t) := (D.isClosed_Z1 t).completeSpace_coe

/-- Addition on `Z¹(t)` is continuous (stated separately: instance search does not find it through the
submodule's own additive structure). -/
instance (t : ℝ) : ContinuousAdd (D.Z1 t) := (inferInstance : IsTopologicalAddGroup (D.Z1 t)).toContinuousAdd

/-! ### The coboundary -/

variable [IsManifold 𝓘(ℂ) 1 X]

/-- The function `w ↦ ηⱼ(τⱼᵢ w) - ηᵢ(w)` on `Ωᵢⱼ(t)`. -/
def deltaFun {t : ℝ} (η : D.C0 t) (i j : ι) : ℂ → ℂ := fun w ↦ ext (η j) (D.τ j i w) - ext (η i) w

theorem differentiableOn_deltaFun {t : ℝ} (η : D.C0 t) (i j : ι) :
    DifferentiableOn ℂ (D.deltaFun η i j) (D.Ω t i j) := by
  intro w hw
  refine (DifferentiableAt.sub ?_ (differentiableAt_ext _ hw.1)).differentiableWithinAt
  exact (differentiableAt_ext _ (D.τ_mem_B_of_mem_Ω hw)).comp w (D.differentiableAt_τ_of_mem_Ω hw)

theorem norm_deltaFun_le {t : ℝ} (η : D.C0 t) (i j : ι) (w : ℂ) :
    ‖D.deltaFun η i j w‖ ≤ 2 * ‖η‖ := by
  have h1 := (norm_ext_le (η j) (D.τ j i w)).trans (D.C0_norm_apply_le η j)
  have h2 := (norm_ext_le (η i) w).trans (D.C0_norm_apply_le η i)
  calc ‖D.deltaFun η i j w‖ ≤ ‖ext (η j) (D.τ j i w)‖ + ‖ext (η i) w‖ := norm_sub_le _ _
    _ ≤ 2 * ‖η‖ := by linarith

/-- The component `(δη)ᵢⱼ`. -/
def deltaComp {t : ℝ} (η : D.C0 t) (p : ι × ι) : boundedHolomorphicFunctions ℂ (D.Ω t p.1 p.2) :=
  BoundedHolomorphicFunctions.of _ (D.deltaFun η p.1 p.2) (D.differentiableOn_deltaFun η _ _)
    (2 * ‖η‖) fun w _ ↦ D.norm_deltaFun_le η _ _ w

theorem ext_deltaComp {t : ℝ} (η : D.C0 t) (p : ι × ι) {w : ℂ} (hw : w ∈ D.Ω t p.1 p.2) :
    ext (D.deltaComp η p) w = ext (η p.2) (D.τ p.2 p.1 w) - ext (η p.1) w :=
  ext_of _ (D.differentiableOn_deltaFun η _ _) _ (fun w _ ↦ D.norm_deltaFun_le η _ _ w) hw

theorem norm_deltaComp_le {t : ℝ} (η : D.C0 t) (p : ι × ι) : ‖D.deltaComp η p‖ ≤ 2 * ‖η‖ := by
  change ‖((D.deltaComp η p : _) : D.Ω t p.1 p.2 →ᵇ ℂ)‖ ≤ _
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun w ↦ ?_
  rw [← ext_of_mem _ w.2, D.ext_deltaComp η p w.2]
  exact D.norm_deltaFun_le η _ _ _

/-- The coboundary `C⁰(t) → C¹(t)` as a linear map. -/
def deltaLin (t : ℝ) : D.C0 t →ₗ[ℂ] D.C1 t where
  toFun η p := D.deltaComp η p
  map_add' η η' := by
    refine D.C1_ext fun p ↦ bhf_ext_eq fun w hw ↦ ?_
    show ext (D.deltaComp (η + η') p) w = ext (D.deltaComp η p + D.deltaComp η' p) w
    simp only [C0_add_apply, ext_add, D.ext_deltaComp _ _ hw]
    ring
  map_smul' a η := by
    refine D.C1_ext fun p ↦ bhf_ext_eq fun w hw ↦ ?_
    show ext (D.deltaComp (a • η) p) w = ext (a • D.deltaComp η p) w
    simp only [C0_smul_apply, ext_smul, D.ext_deltaComp _ _ hw]
    ring

theorem ext_deltaLin {t : ℝ} (η : D.C0 t) (p : ι × ι) {w : ℂ} (hw : w ∈ D.Ω t p.1 p.2) :
    ext (D.deltaLin t η p) w = ext (η p.2) (D.τ p.2 p.1 w) - ext (η p.1) w :=
  D.ext_deltaComp η p hw

theorem isCocycle_deltaLin {t : ℝ} (η : D.C0 t) : D.IsCocycle (D.deltaLin t η) := by
  intro i j k x hi hj hk
  rw [D.ext_deltaLin η (i, j) (D.e_mem_Ω hi hj), D.ext_deltaLin η (j, k) (D.e_mem_Ω hj hk),
    D.ext_deltaLin η (i, k) (D.e_mem_Ω hi hk)]
  simp only [D.τ_apply_e hi.1, D.τ_apply_e hj.1]
  ring

/-- **The coboundary** `δ : C⁰(t) → Z¹(t)`, `(δη)ᵢⱼ = ηⱼ - ηᵢ`, a continuous linear map. -/
def delta (t : ℝ) : D.C0 t →L[ℂ] D.Z1 t :=
  ((D.deltaLin t).mkContinuous 2 fun η ↦
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p ↦ D.norm_deltaComp_le η p).codRestrict
    (D.Z1 t) fun η ↦ D.isCocycle_deltaLin η

theorem ext_delta {t : ℝ} (η : D.C0 t) (p : ι × ι) {w : ℂ} (hw : w ∈ D.Ω t p.1 p.2) :
    ext ((D.delta t η : D.C1 t) p) w = ext (η p.2) (D.τ p.2 p.1 w) - ext (η p.1) w :=
  D.ext_deltaLin η p hw

/-! ### Restriction -/

/-- Restriction `C¹(t') → C¹(t)` for `t ≤ t'`. -/
def resC1 {t t' : ℝ} (h : t ≤ t') : D.C1 t' →L[ℂ] D.C1 t :=
  ContinuousLinearMap.pi fun p ↦
    (BoundedHolomorphicFunctions.restrict (D.Ω_mono h p.1 p.2)).comp (ContinuousLinearMap.proj p)

theorem ext_resC1 {t t' : ℝ} (h : t ≤ t') (ξ : D.C1 t') (p : ι × ι) {w : ℂ} (hw : w ∈ D.Ω t p.1 p.2) :
    ext (D.resC1 h ξ p) w = ext (ξ p) w :=
  ext_restrict (D.Ω_mono h p.1 p.2) _ hw

theorem resC1_mem {t t' : ℝ} (h : t ≤ t') {ξ : D.C1 t'} (hξ : ξ ∈ D.Z1 t') : D.resC1 h ξ ∈ D.Z1 t := by
  intro i j k x hi hj hk
  rw [D.ext_resC1 h ξ (i, j) (D.e_mem_Ω hi hj), D.ext_resC1 h ξ (j, k) (D.e_mem_Ω hj hk),
    D.ext_resC1 h ξ (i, k) (D.e_mem_Ω hi hk)]
  exact hξ i j k x (D.V_mono h i hi) (D.V_mono h j hj) (D.V_mono h k hk)

/-- Restriction of cocycles `Z¹(t') → Z¹(t)` for `t ≤ t'`. -/
def res {t t' : ℝ} (h : t ≤ t') : D.Z1 t' →L[ℂ] D.Z1 t :=
  ((D.resC1 h).comp (D.Z1 t').subtypeL).codRestrict (D.Z1 t) fun ξ ↦ D.resC1_mem h ξ.2

theorem ext_res {t t' : ℝ} (h : t ≤ t') (ξ : D.Z1 t') (p : ι × ι) {w : ℂ} (hw : w ∈ D.Ω t p.1 p.2) :
    ext ((D.res h ξ : D.C1 t) p) w = ext ((ξ : D.C1 t') p) w :=
  D.ext_resC1 h ξ p hw

/-! ### Compactness of restriction -/

/-- The compact set `zᵢ⁻¹(B̄(cᵢ, t Sᵢ))`. -/
def Vbar (t : ℝ) (i : ι) : Set X := (D.e i).symm '' closedBall (D.c i) (t * D.S i)

theorem isCompact_Vbar {t : ℝ} (ht : t ≤ 1) (i : ι) : IsCompact (D.Vbar t i) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((D.e i).continuousOn_symm.mono (D.closedBall_subset_target ht i))

theorem Vbar_subset_source {t : ℝ} (ht : t ≤ 1) (i : ι) : D.Vbar t i ⊆ (D.e i).source := by
  rintro _ ⟨w, hw, rfl⟩
  exact (D.e i).map_target (D.closedBall_subset_target ht i hw)

theorem V_subset_Vbar {t : ℝ} (i : ι) : D.V t i ⊆ D.Vbar t i := fun x hx ↦
  ⟨D.e i x, ball_subset_closedBall hx.2, (D.e i).left_inv hx.1⟩

theorem Vbar_subset_V {t t' : ℝ} (ht : t < t') (ht' : t ≤ 1) (i : ι) : D.Vbar t i ⊆ D.V t' i := by
  rintro _ ⟨w, hw, rfl⟩
  have hwt := D.closedBall_subset_target ht' i hw
  refine ⟨(D.e i).map_target hwt, ?_⟩
  rw [mem_preimage, (D.e i).right_inv hwt, mem_ball]
  exact (mem_closedBall.1 hw).trans_lt (by nlinarith [D.S_pos i])

/-- Each component of the restriction is compact: `Ωᵢⱼ(t) ⊆ zᵢ(V̄ᵢ ∩ V̄ⱼ) ⊆ Ωᵢⱼ(t')`. -/
theorem isCompactOperator_restrict_Ω [T2Space X] {t t' : ℝ} (ht : t < t') (ht1 : t ≤ 1) (i j : ι) :
    IsCompactOperator (BoundedHolomorphicFunctions.restrict (E := ℂ) (D.Ω_mono ht.le i j)) := by
  have hK : IsCompact (D.e i '' (D.Vbar t i ∩ D.Vbar t j)) :=
    ((D.isCompact_Vbar ht1 i).inter_right (D.isCompact_Vbar ht1 j).isClosed).image_of_continuousOn
      ((D.e i).continuousOn.mono (inter_subset_left.trans (D.Vbar_subset_source ht1 i)))
  have h1 : ((D.Ω t i j : Opens ℂ) : Set ℂ) ⊆ D.e i '' (D.Vbar t i ∩ D.Vbar t j) := by
    intro w hw
    exact ⟨(D.e i).symm w, ⟨⟨w, ball_subset_closedBall hw.1, rfl⟩, D.V_subset_Vbar j hw.2.2⟩,
      (D.e i).right_inv hw.2.1⟩
  have h2 : D.e i '' (D.Vbar t i ∩ D.Vbar t j) ⊆ ((D.Ω t' i j : Opens ℂ) : Set ℂ) := by
    rintro _ ⟨x, ⟨hxi, hxj⟩, rfl⟩
    exact D.e_mem_Ω (D.Vbar_subset_V ht ht1 i hxi) (D.Vbar_subset_V ht ht1 j hxj)
  exact BoundedHolomorphicFunctions.isCompactOperator_restrict hK h1 h2

omit [Fintype ι] [IsManifold 𝓘(ℂ) 1 X] in
/-- A finite product of compact operators is compact. -/
theorem _root_.ModularFormsKB.Milne.Wave15.isCompactOperator_pi {κ E : Type*} [Fintype κ]
    {F : κ → Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [∀ k, NormedAddCommGroup (F k)]
    [∀ k, NormedSpace ℂ (F k)] (f : ∀ k, E →L[ℂ] F k) (hf : ∀ k, IsCompactOperator (f k)) :
    IsCompactOperator (ContinuousLinearMap.pi f) := by
  choose K hK hpre using hf
  refine ⟨Set.pi univ K, isCompact_univ_pi hK, ?_⟩
  have : (ContinuousLinearMap.pi f : E → ∀ k, F k) ⁻¹' Set.pi univ K =
      ⋂ k, (f k : E → F k) ⁻¹' K k := by
    ext x; simp
  rw [this]
  exact Filter.iInter_mem.2 hpre

theorem isCompactOperator_resC1 [T2Space X] {t t' : ℝ} (ht : t < t') (ht1 : t ≤ 1) :
    IsCompactOperator (D.resC1 ht.le) :=
  isCompactOperator_pi _ fun p ↦ (D.isCompactOperator_restrict_Ω ht ht1 p.1 p.2).comp_clm _

theorem isCompactOperator_res [T2Space X] {t t' : ℝ} (ht : t < t') (ht1 : t ≤ 1) :
    IsCompactOperator (D.res ht.le) := by
  obtain ⟨K, hK, hpre⟩ := (D.isCompactOperator_resC1 ht ht1).comp_clm (D.Z1 t').subtypeL
  refine ⟨(↑) ⁻¹' (K ∩ D.Z1 t), ?_, ?_⟩
  · exact (D.isClosed_Z1 t).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hK.inter_right (D.isClosed_Z1 t))
  · refine Filter.mem_of_superset hpre fun ξ hξ ↦ ?_
    exact ⟨hξ, (D.res ht.le ξ).2⟩

end DiscSystem

end ModularFormsKB.Milne.Wave15
