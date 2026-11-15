import ModularFormsKB.Milne.Wave15.MittagLeffler
import ModularFormsKB.Milne.Wave11.Separation

/-!
# The existence theorem on a compact Riemann surface

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.17 (pdf p. 20), and through it Theorem 1.20
(Riemann–Roch, p. 21), proved for **every** compact Riemann surface, following Forster, *Lectures on Riemann
Surfaces*, §14 (Theorems 14.9 and 14.12, Corollary 14.13).

* `exists_pole_only_at`: for every point `a` there is a meromorphic function whose only pole is `a`.
* `separates`: meromorphic functions separate points.
* `existsNonconstantStatement`: Milne's named statement `ExistsNonconstantStatement X` (Theorem 1.17) holds.
* `riemannRochStatement`: Milne's named statement `RiemannRochStatement X` (Theorem 1.20) holds, by the
  library's reduction `Wave11.riemannRoch_of_separates`.
-/

open Set Metric Topology TopologicalSpace TauCeti Filter OnePoint
open TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface
open scoped Manifold

universe u

noncomputable section

namespace ModularFormsKB.Milne.Wave15

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [T2Space X]

namespace DiscSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] [DecidableEq ι] in
theorem exists_V_quarter (D : DiscSystem X ι) (x : X) : ∃ i, x ∈ D.V (1 / 4) i := by
  obtain ⟨i, hi⟩ := D.exists_mem_V x
  exact ⟨i, D.V_mono (by norm_num) i hi⟩

/-- A disc of radius `S/4` containing `x`. -/
def idx (D : DiscSystem X ι) (x : X) : ι := (D.exists_V_quarter x).choose

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] [DecidableEq ι] in
theorem idx_spec (D : DiscSystem X ι) (x : X) : x ∈ D.V (1 / 4) (D.idx x) :=
  (D.exists_V_quarter x).choose_spec

variable {D : DiscSystem X ι} {i₀ : ι} (hA : D.Adapted i₀) {N : ℕ} (c : Fin N → ℂ) (η : D.C0 (1 / 4))

/-- The glued function `Fᵢ - ηᵢ ∘ zᵢ`. -/
def glue (D : DiscSystem X ι) (i₀ : ι) {N : ℕ} (c : Fin N → ℂ) (η : D.C0 (1 / 4)) (x : X) : ℂ :=
  D.Fl i₀ c (D.idx x) x - ext (η (D.idx x)) (D.e (D.idx x) x)

variable {c η}

theorem glue_eq (hη : D.delta (1 / 4) η = DiscSystem.ml hA N c) {i : ι} {x : X} (hi : x ∈ D.V (1 / 4) i) :
    glue D i₀ c η x = D.Fl i₀ c i x - ext (η i) (D.e i x) := by
  have hi' := D.idx_spec x
  have h1 := congrArg (fun z : D.Z1 (1 / 4) ↦ ext ((z : D.C1 (1 / 4)) (D.idx x, i)) (D.e (D.idx x) x)) hη
  simp only at h1
  rw [D.ext_delta η (D.idx x, i) (D.e_mem_Ω hi' hi), DiscSystem.ext_ml_e hA c hi' hi] at h1
  rw [D.τ_apply_e hi'.1] at h1
  unfold glue
  linear_combination h1

omit [T2Space X] [Fintype ι] in
theorem Fl_symm {i : ι} {w : ℂ} (hw : w ∈ (D.e i).target) :
    D.Fl i₀ c i ((D.e i).symm w) = if i = i₀ then D.pp i₀ c w else 0 := by
  unfold DiscSystem.Fl
  by_cases hi : i = i₀
  · subst hi; simp [(D.e i).right_inv hw]
  · simp [hi]

theorem meromorphicAt_glue (hη : D.delta (1 / 4) η = DiscSystem.ml hA N c) (y : X) :
    TauCeti.RiemannSurface.MeromorphicAt (glue D i₀ c η) y := by
  set i := D.idx y
  have hy := D.idx_spec y
  rw [meromorphicAt_iff_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (D.pt i)) hy.1]
  set G : ℂ → ℂ := fun w ↦ (if i = i₀ then D.pp i₀ c w else 0) - ext (η i) w
  have hpp : ∀ w, _root_.MeromorphicAt (D.pp i₀ c) w := fun w ↦ by
    have h : D.pp i₀ c = fun w ↦ ∑ k, c k * (w - D.c i₀)⁻¹ ^ (k.1 + 1) := rfl
    rw [h]
    exact MeromorphicAt.fun_sum fun k _ ↦ (MeromorphicAt.const (c k) w).mul
      (((MeromorphicAt.id w).sub (MeromorphicAt.const (D.c i₀) w)).inv.pow (k.1 + 1))
  have hball : D.e i y ∈ D.B (1 / 4) i := hy.2
  have hG : _root_.MeromorphicAt G (D.e i y) := by
    refine MeromorphicAt.sub ?_ ?_
    · split_ifs
      · exact hpp _
      · exact MeromorphicAt.const _ _
    · exact ((BoundedHolomorphicFunctions.differentiableOn_extend (η i)).analyticAt
        ((D.B (1 / 4) i).isOpen.mem_nhds hball)).meromorphicAt
  refine hG.congr ?_
  have hev : ∀ᶠ w in 𝓝 (D.e i y), w ∈ ball (D.c i) (1 / 4 * D.S i) := isOpen_ball.mem_nhds hy.2
  refine (hev.mono fun w hw ↦ ?_).filter_mono nhdsWithin_le_nhds
  have hwt := D.ball_subset_target (by norm_num) i hw
  simp only [Function.comp_apply, G]
  rw [glue_eq hA hη (D.mem_V_symm (by norm_num) hw), Fl_symm hwt, (D.e i).right_inv hwt]

theorem continuousAt_glue (hη : D.delta (1 / 4) η = DiscSystem.ml hA N c) {y : X} (hy : y ≠ D.pt i₀) :
    ContinuousAt (glue D i₀ c η) y := by
  set i := D.idx y
  have hyi := D.idx_spec y
  have heq : glue D i₀ c η =ᶠ[𝓝 y] fun x ↦ D.Fl i₀ c i x - ext (η i) (D.e i x) :=
    Filter.eventually_of_mem ((D.isOpen_V _ i).mem_nhds hyi) fun x hx ↦ glue_eq hA hη hx
  refine ContinuousAt.congr ?_ heq.symm
  refine ContinuousAt.sub ?_ ((differentiableAt_ext (η i) hyi.2).continuousAt.comp
    ((D.e i).continuousAt hyi.1))
  unfold DiscSystem.Fl
  by_cases hi : i = i₀
  · simp only [hi, if_true]
    have hy0 : y ∈ (D.e i₀).source := hi ▸ hyi.1
    have hne : D.e i₀ y ≠ D.c i₀ := fun h ↦
      hy ((D.e i₀).injOn hy0 (mem_chart_source ℂ (D.pt i₀)) h)
    exact (D.differentiableAt_pp i₀ c hne).continuousAt.comp ((D.e i₀).continuousAt hy0)
  · simp only [hi, if_false]
    exact continuousAt_const

/-- The polynomial `∑ₖ cₖ Xᵏ⁺¹` with `P_c(w) = P((w - c₀)⁻¹)`. -/
def ppPoly (c : Fin N → ℂ) : Polynomial ℂ := ∑ k, Polynomial.C (c k) * Polynomial.X ^ (k.1 + 1)

omit [IsManifold 𝓘(ℂ) 1 X] [T2Space X] [Fintype ι] [DecidableEq ι] in
theorem pp_eq_eval (D : DiscSystem X ι) (i₀ : ι) (c : Fin N → ℂ) (w : ℂ) :
    D.pp i₀ c w = (ppPoly c).eval ((w - D.c i₀)⁻¹) := by
  simp [DiscSystem.pp, ppPoly, Polynomial.eval_finsetSum]

theorem degree_ppPoly_pos (hc : c ≠ 0) : 0 < (ppPoly c).degree := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hc
  have hcoeff : (ppPoly c).coeff (k.1 + 1) = c k := by
    simp only [ppPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by omega))
    · simp
  have hne : ppPoly c ≠ 0 := fun h ↦ hk (by rw [← hcoeff, h, Polynomial.coeff_zero]; rfl)
  have hdeg : k.1 + 1 ≤ (ppPoly c).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hk)
  exact Polynomial.natDegree_pos_iff_degree_pos.1 (by omega)

theorem tendsto_glue (hη : D.delta (1 / 4) η = DiscSystem.ml hA N c) (hc : c ≠ 0) :
    Tendsto (fun y ↦ (glue D i₀ c η y : OnePoint ℂ)) (𝓝[≠] (D.pt i₀)) (𝓝 ∞) := by
  have hsub : Tendsto (fun y ↦ D.e i₀ y - D.c i₀) (𝓝[≠] (D.pt i₀)) (𝓝[≠] 0) := by
    have h1 : Tendsto (fun w : ℂ ↦ w - D.c i₀) (𝓝[≠] (D.c i₀)) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact ((continuous_sub_right (D.c i₀)).tendsto' _ _ (sub_self _)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        exact sub_ne_zero.2 hw
    exact h1.comp (tendsto_chartAt_nhdsNE (D.pt i₀))
  have ht1 := (ppPoly c).tendsto_norm_atTop (degree_ppPoly_pos hc)
    (tendsto_norm_inv_nhdsNE_zero_atTop.comp hsub)
  have hV : ∀ᶠ y in 𝓝[≠] (D.pt i₀), y ∈ D.V (1 / 4) i₀ := by
    refine nhdsWithin_le_nhds ((D.isOpen_V _ i₀).mem_nhds ⟨mem_chart_source ℂ (D.pt i₀), ?_⟩)
    simp only [mem_preimage, mem_ball, dist_self]
    have := D.S_pos i₀
    positivity
  have ht2 : Tendsto (fun y ↦ ‖glue D i₀ c η y‖) (𝓝[≠] (D.pt i₀)) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-‖η i₀‖) ht1)
    filter_upwards [hV] with y hy
    rw [glue_eq hA hη hy]
    simp only [DiscSystem.Fl, if_true, Function.comp_apply, pp_eq_eval]
    have h1 := norm_ext_le (η i₀) (D.e i₀ y)
    have h2 := norm_sub_norm_le ((ppPoly c).eval ((D.e i₀ y - D.c i₀)⁻¹)) (ext (η i₀) (D.e i₀ y))
    linarith
  have ht3 : Tendsto (glue D i₀ c η) (𝓝[≠] (D.pt i₀)) (coclosedCompact ℂ) := by
    rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.1 ht2
  exact tendsto_coe_infty.comp ht3

end DiscSystem

variable [CompactSpace X] [ConnectedSpace X]

/-- **Forster 14.12.** For every point `a` of a compact Riemann surface there is a meromorphic function whose only
pole is `a`. -/
theorem exists_pole_only_at (a : X) :
    ∃ g : MeromorphicFunction X, g a = ∞ ∧ ∀ y, y ≠ a → g y ≠ ∞ := by
  obtain ⟨ι, _, _, D, i₀, hpt, hA⟩ := exists_adapted a
  obtain ⟨N, hN⟩ := D.exists_ne_zero_delta_eq
  obtain ⟨c, hc, η, hη⟩ := hN (DiscSystem.ml hA N)
  subst hpt
  have hmero := DiscSystem.meromorphicAt_glue hA (c := c) (η := η) hη
  refine ⟨MeromorphicFunction.ofMeromorphic hmero, ?_, fun y hy ↦ ?_⟩
  · rw [MeromorphicFunction.coe_ofMeromorphic]
    exact sphereMap_eq_of_tendsto (DiscSystem.tendsto_glue hA hη hc)
  · rw [MeromorphicFunction.ofMeromorphic_apply_of_continuousAt hmero
      (DiscSystem.continuousAt_glue hA hη hy)]
    exact coe_ne_infty _

/-- **Forster 14.13.** The meromorphic functions on a compact Riemann surface separate points. -/
@[kb "milne2017mf" "Theorem 1.17: the meromorphic functions separate points (existence theorem), pdf p. 20"]
theorem separates (x y : X) (h : x ≠ y) : ∃ g : MeromorphicFunction X, g x ≠ g y := by
  obtain ⟨g, hgx, hgy⟩ := exists_pole_only_at x
  exact ⟨g, by rw [hgx]; exact (hgy y h.symm).symm⟩

/-- A Riemann surface has a point other than any given one. -/
theorem exists_ne (a : X) : ∃ y, y ≠ a := by
  obtain ⟨S, hS, hSt⟩ := exists_closedBall_subset (chartAt ℂ a).open_target (mem_chart_target ℂ a)
  have hw : chartAt ℂ a a + S ∈ (chartAt ℂ a).target :=
    hSt (mem_closedBall.2 (by simp [abs_of_pos hS]))
  refine ⟨(chartAt ℂ a).symm (chartAt ℂ a a + S), fun h ↦ ?_⟩
  have := congrArg (chartAt ℂ a) h
  rw [(chartAt ℂ a).right_inv hw] at this
  have h2 : (S : ℂ) = 0 := by linear_combination this
  exact hS.ne' (by exact_mod_cast h2)

/-- **Milne, Theorem 1.17** (first statement): every compact Riemann surface has a nonconstant meromorphic
function. -/
@[kb "milne2017mf" "Theorem 1.17: existence of a nonconstant meromorphic function, pdf p. 20"]
theorem existsNonconstantStatement : ExistsNonconstantStatement X := by
  obtain ⟨a⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, hy⟩ := exists_ne a
  obtain ⟨g, hga, hgy⟩ := exists_pole_only_at a
  exact ⟨⟨g, a, y, by rw [hga]; exact (hgy y hy).symm⟩⟩

/-- **Milne, Theorem 1.20 (Riemann–Roch)** on every compact Riemann surface. -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21"]
theorem riemannRochStatement : RiemannRochStatement X :=
  Wave11.riemannRoch_of_separates existsNonconstantStatement separates

end ModularFormsKB.Milne.Wave15
