import ModularFormsKB.Milne.Wave15.Finiteness
import ModularFormsKB.Milne.Wave15.AdaptedSystem
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField
import Mathlib.Topology.Algebra.Polynomial

/-!
# A meromorphic function with a single pole (Forster 14.12)

Forster, *Lectures on Riemann Surfaces*, Theorem 14.12 and Corollary 14.13, for Milne, *Modular Functions and
Modular Forms* (`milne2017mf`), Theorem 1.17 (pdf p. 20).

Let `a` be a point of a compact Riemann surface and `D` a disc system adapted to `a` (`exists_adapted`). For
`c ∈ ℂᴺ` the principal part `P_c = ∑ₖ cₖ (z₀ - z₀(a))^{-(k+1)}` on the disc at `a` (and `0` on the other discs)
defines a bounded cocycle `ml c ∈ Z¹(1/4)` (`ml`). Since `Z¹(1/4) / δC⁰(1/4)` is finite-dimensional
(`DiscSystem.exists_ne_zero_delta_eq`), some `c ≠ 0` has `ml c = δη`, and `P_c - η` glues to a meromorphic function
on `X` whose only pole is `a` (`exists_pole_only_at`). Consequently the meromorphic functions separate points
(`separates`) and there is a nonconstant one.
-/

open Set Metric Topology TopologicalSpace TauCeti Filter OnePoint
open scoped Manifold

universe u

noncomputable section

namespace ModularFormsKB.Milne.Wave15

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]

namespace DiscSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (D : DiscSystem X ι) (i₀ : ι)

/-! ### Principal parts -/

/-- The principal part `∑ₖ cₖ (w - c₀)^{-(k+1)}`. -/
def pp {N : ℕ} (c : Fin N → ℂ) (w : ℂ) : ℂ := ∑ k, c k * (w - D.c i₀)⁻¹ ^ (k.1 + 1)

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] [DecidableEq ι] in
theorem pp_add {N : ℕ} (c c' : Fin N → ℂ) (w : ℂ) : D.pp i₀ (c + c') w = D.pp i₀ c w + D.pp i₀ c' w := by
  simp only [pp, Pi.add_apply, add_mul, Finset.sum_add_distrib]

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] [DecidableEq ι] in
theorem pp_smul {N : ℕ} (a : ℂ) (c : Fin N → ℂ) (w : ℂ) : D.pp i₀ (a • c) w = a * D.pp i₀ c w := by
  simp only [pp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] [DecidableEq ι] in
theorem differentiableAt_pp {N : ℕ} (c : Fin N → ℂ) {w : ℂ} (hw : w ≠ D.c i₀) :
    DifferentiableAt ℂ (D.pp i₀ c) w := by
  have hw' : w - D.c i₀ ≠ 0 := sub_ne_zero.2 hw
  have h : D.pp i₀ c = fun w ↦ ∑ k, c k * (w - D.c i₀)⁻¹ ^ (k.1 + 1) := rfl
  rw [h]
  refine DifferentiableAt.fun_sum fun k _ ↦ ?_
  have h1 : DifferentiableAt ℂ (fun w : ℂ ↦ w - D.c i₀) w := differentiableAt_id.sub_const (D.c i₀)
  exact ((h1.inv hw').pow (k.1 + 1)).const_mul (c k)

/-- The bound `∑ₖ ‖cₖ‖ ρ^{-(k+1)}` for the principal part off `B(c₀, ρ)`, `ρ = S₀/16`. -/
def ppBound {N : ℕ} (c : Fin N → ℂ) : ℝ := ∑ k, ‖c k‖ * (D.S i₀ / 16)⁻¹ ^ (k.1 + 1)

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] [DecidableEq ι] in
theorem norm_pp_le {N : ℕ} (c : Fin N → ℂ) {w : ℂ} (hw : D.S i₀ / 16 < ‖w - D.c i₀‖) :
    ‖D.pp i₀ c w‖ ≤ D.ppBound i₀ c := by
  have hρ : 0 < D.S i₀ / 16 := by have := D.S_pos i₀; positivity
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [norm_mul, norm_pow, norm_inv]
  gcongr

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] [DecidableEq ι] in
theorem ppBound_nonneg {N : ℕ} (c : Fin N → ℂ) : 0 ≤ D.ppBound i₀ c := by
  have hρ : 0 < D.S i₀ / 16 := by have := D.S_pos i₀; positivity
  exact Finset.sum_nonneg fun k _ ↦ by positivity

/-- The principal part on the disc `l`, as a function on `X`: `P_c ∘ z₀` on the disc at `a`, `0` elsewhere. -/
def Fl {N : ℕ} (c : Fin N → ℂ) (l : ι) (x : X) : ℂ := if l = i₀ then D.pp i₀ c (D.e i₀ x) else 0

/-- The Mittag-Leffler cocycle `(Fⱼ - Fᵢ)` read in the chart `zᵢ`. -/
def mlFun {N : ℕ} (c : Fin N → ℂ) (i j : ι) (w : ℂ) : ℂ :=
  (if j = i₀ then D.pp i₀ c (D.τ i₀ i w) else 0) - (if i = i₀ then D.pp i₀ c w else 0)

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] in
theorem mlFun_e {N : ℕ} (c : Fin N → ℂ) {i : ι} (j : ι) {x : X} (hx : x ∈ (D.e i).source) :
    D.mlFun i₀ c i j (D.e i x) = D.Fl i₀ c j x - D.Fl i₀ c i x := by
  unfold mlFun Fl
  rw [D.τ_apply_e hx]
  by_cases hi : i = i₀
  · subst hi; rfl
  · simp [hi]

variable {i₀}

/-- The hypothesis that `D` is adapted to its `i₀`-th centre. -/
def Adapted (i₀ : ι) : Prop :=
  ∀ j, j ≠ i₀ → ∀ x ∈ D.V (1 / 4) j, x ∈ (D.e i₀).source → D.S i₀ / 16 < ‖D.e i₀ x - D.c i₀‖

variable {D} (hA : D.Adapted i₀)
include hA

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] in
theorem norm_Fl_sub_le {N : ℕ} (c : Fin N → ℂ) {i j : ι} {x : X} (hi : x ∈ D.V (1 / 4) i)
    (hj : x ∈ D.V (1 / 4) j) : ‖D.Fl i₀ c j x - D.Fl i₀ c i x‖ ≤ D.ppBound i₀ c := by
  unfold Fl
  by_cases hi0 : i = i₀ <;> by_cases hj0 : j = i₀
  · subst hi0; subst hj0; simpa using D.ppBound_nonneg _ c
  · subst hi0
    simpa [hj0] using D.norm_pp_le i c (hA j hj0 x hj hi.1)
  · subst hj0
    simpa [hi0] using D.norm_pp_le j c (hA i hi0 x hi hj.1)
  · simpa [hi0, hj0] using D.ppBound_nonneg i₀ c

theorem differentiableOn_mlFun {N : ℕ} (c : Fin N → ℂ) (i j : ι) :
    DifferentiableOn ℂ (D.mlFun i₀ c i j) (D.Ω (1 / 4) i j) := by
  intro w hw
  have hxi : (D.e i).symm w ∈ D.V (1 / 4) i := D.mem_V_symm (by norm_num) hw.1
  have hxj : (D.e i).symm w ∈ D.V (1 / 4) j := hw.2.2
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases hi0 : i = i₀ <;> by_cases hj0 : j = i₀
  · subst hi0; subst hj0
    refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [(D.e j).open_target.mem_nhds hw.2.1] with w' hw'
    simp [mlFun, D.τ_self hw']
  · subst hi0
    have hne : w ≠ D.c i := by
      intro h
      have := hA j hj0 _ hxj hxi.1
      rw [(D.e i).right_inv hw.2.1, h, sub_self, norm_zero] at this
      linarith [D.S_pos i]
    have : D.mlFun i c i j = fun w ↦ 0 - D.pp i c w := by
      funext w'; simp [mlFun, hj0]
    rw [this]
    exact (differentiableAt_const _).sub (D.differentiableAt_pp i c hne)
  · subst hj0
    have hne : D.τ j i w ≠ D.c j := by
      intro h
      have := hA i hi0 _ hxi hxj.1
      change D.S j / 16 < ‖D.τ j i w - D.c j‖ at this
      rw [h, sub_self, norm_zero] at this
      linarith [D.S_pos j]
    have : D.mlFun j c i j = fun w ↦ D.pp j c (D.τ j i w) - 0 := by
      funext w'; simp [mlFun, hi0]
    rw [this]
    exact ((D.differentiableAt_pp j c hne).comp w (D.differentiableAt_τ hw.2.1 hxj.1)).sub
      (differentiableAt_const _)
  · have : D.mlFun i₀ c i j = fun _ ↦ 0 := by funext w'; simp [mlFun, hi0, hj0]
    rw [this]
    exact differentiableAt_const _

theorem norm_mlFun_le {N : ℕ} (c : Fin N → ℂ) {i j : ι} {w : ℂ} (hw : w ∈ D.Ω (1 / 4) i j) :
    ‖D.mlFun i₀ c i j w‖ ≤ D.ppBound i₀ c := by
  have hxi : (D.e i).symm w ∈ D.V (1 / 4) i := D.mem_V_symm (by norm_num) hw.1
  have h := D.mlFun_e i₀ c j hxi.1
  rw [(D.e i).right_inv hw.2.1] at h
  rw [h]
  exact norm_Fl_sub_le hA c hxi hw.2.2

/-- The Mittag-Leffler cochain. -/
def mlC {N : ℕ} (c : Fin N → ℂ) : D.C1 (1 / 4) := fun p ↦
  BoundedHolomorphicFunctions.of _ (D.mlFun i₀ c p.1 p.2) (differentiableOn_mlFun hA c p.1 p.2) _
    fun _ hw ↦ norm_mlFun_le hA c hw

theorem ext_mlC {N : ℕ} (c : Fin N → ℂ) (p : ι × ι) {w : ℂ} (hw : w ∈ D.Ω (1 / 4) p.1 p.2) :
    ext (mlC hA c p) w = D.mlFun i₀ c p.1 p.2 w :=
  ext_of _ (differentiableOn_mlFun hA c p.1 p.2) _ (fun _ hw ↦ norm_mlFun_le hA c hw) hw

theorem ext_mlC_e {N : ℕ} (c : Fin N → ℂ) {i j : ι} {x : X} (hi : x ∈ D.V (1 / 4) i)
    (hj : x ∈ D.V (1 / 4) j) : ext (mlC hA c (i, j)) (D.e i x) = D.Fl i₀ c j x - D.Fl i₀ c i x := by
  rw [ext_mlC hA c (i, j) (D.e_mem_Ω hi hj)]
  exact D.mlFun_e i₀ c j hi.1

theorem mlC_mem {N : ℕ} (c : Fin N → ℂ) : mlC hA c ∈ D.Z1 (1 / 4) := by
  intro i j k x hi hj hk
  rw [ext_mlC_e hA c hi hj, ext_mlC_e hA c hj hk, ext_mlC_e hA c hi hk]
  ring

/-- **The Mittag-Leffler map** `ℂᴺ → Z¹(1/4)`. -/
def ml (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] D.Z1 (1 / 4) where
  toFun c := ⟨mlC hA c, mlC_mem hA c⟩
  map_add' c c' := by
    refine Subtype.ext (D.C1_ext fun p ↦ bhf_ext_eq fun w hw ↦ ?_)
    show ext (mlC hA (c + c') p) w = ext (mlC hA c p + mlC hA c' p) w
    rw [ext_add, ext_mlC hA _ p hw, ext_mlC hA _ p hw, ext_mlC hA _ p hw]
    simp only [mlFun, D.pp_add]
    split_ifs <;> ring
  map_smul' a c := by
    refine Subtype.ext (D.C1_ext fun p ↦ bhf_ext_eq fun w hw ↦ ?_)
    show ext (mlC hA (a • c) p) w = ext (a • mlC hA c p) w
    rw [ext_smul, ext_mlC hA _ p hw, ext_mlC hA _ p hw]
    simp only [mlFun, D.pp_smul]
    split_ifs <;> ring

theorem ext_ml_e {N : ℕ} (c : Fin N → ℂ) {i j : ι} {x : X} (hi : x ∈ D.V (1 / 4) i)
    (hj : x ∈ D.V (1 / 4) j) :
    ext (((ml hA N c : D.Z1 (1 / 4)) : D.C1 (1 / 4)) (i, j)) (D.e i x) = D.Fl i₀ c j x - D.Fl i₀ c i x :=
  ext_mlC_e hA c hi hj

end DiscSystem

end ModularFormsKB.Milne.Wave15
