import ModularFormsKB.Milne.Wave15.Cochains
import ModularFormsKB.Milne.Wave14.DbarUpper
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Every bounded cocycle comes from a larger cover up to a coboundary

Forster, *Lectures on Riemann Surfaces*, §14 (the step "`H¹(𝔘, 𝒪) → H¹(𝔙, 𝒪)` is surjective" of the finiteness
theorem), for Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.17 (pdf p. 20).

For a disc system `D` and a bounded cocycle `ξ ∈ Z¹(1/4)` we construct `ζ ∈ Z¹(1/2)` and `η ∈ C⁰(1/4)` with
`ξ = ζ|_{1/4} + δη` (`surjective_res_add_delta`). The proof is the Dolbeault argument:

1. a partition of unity `ψₖ` subordinate to the discs, built from bump functions in the charts (`ψ`);
2. `gᵢ = -∑ₖ ψₖ ξᵢₖ` is smooth on `Vᵢ` and `ξᵢⱼ = gⱼ - gᵢ` (`g_split`);
3. the `(0,1)`-forms `∂̄gᵢ` glue to a smooth form `ω`, read in each chart as `ωᵢ` (`form_eventuallyEq`);
4. Tau Ceti's Dolbeault lemma on the whole disc `B(cᵢ, Sᵢ)` gives `fᵢ` with `∂̄fᵢ = ωᵢ`;
5. `ηᵢ = gᵢ - fᵢ` and `ζᵢⱼ = fⱼ - fᵢ` are holomorphic and bounded, and `ξ = ζ + δη`.
-/

open Set Metric Topology TopologicalSpace TauCeti Filter
open scoped Manifold ContDiff ComplexConjugate

noncomputable section

namespace ModularFormsKB.Milne.Wave15

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

namespace DiscSystem

variable [T2Space X] {ι : Type*} [Fintype ι] (D : DiscSystem X ι)

/-- Transition maps are real smooth. -/
theorem contDiffAt_τ {i j : ι} {w : ℂ} (hw : w ∈ (D.e i).target)
    (hj : (D.e i).symm w ∈ (D.e j).source) : ContDiffAt ℝ ∞ (D.τ j i) w :=
  (D.analyticAt_τ hw hj).contDiffAt.restrict_scalars ℝ

/-- Bounded holomorphic functions are real smooth. -/
theorem _root_.ModularFormsKB.Milne.Wave15.contDiffAt_ext {U : Opens ℂ}
    (f : boundedHolomorphicFunctions ℂ U) {z : ℂ} (hz : z ∈ U) : ContDiffAt ℝ ∞ (ext f) z :=
  (((BoundedHolomorphicFunctions.differentiableOn_extend f).contDiffOn U.isOpen).contDiffAt
    (U.isOpen.mem_nhds hz)).restrict_scalars ℝ

/-- A function on `X` vanishing off a closed set `K` vanishes, read in a chart, near every point off `K`. -/
theorem eventually_eq_zero_of_not_mem {φ : X → ℝ} {K : Set X} (hK : IsClosed K)
    (hφ : ∀ x, φ x ≠ 0 → x ∈ K) {i : ι} {w : ℂ} (hw : w ∈ (D.e i).target) (h : (D.e i).symm w ∉ K) :
    ∀ᶠ w' in 𝓝 w, φ ((D.e i).symm w') = 0 := by
  have hev : ∀ᶠ w' in 𝓝 w, (D.e i).symm w' ∉ K :=
    ((D.e i).continuousAt_symm hw).preimage_mem_nhds (hK.isOpen_compl.mem_nhds h)
  exact hev.mono fun w' hw' ↦ by_contra fun hne ↦ hw' (hφ _ hne)

/-! ### A partition of unity in the charts -/

/-- The bump function on `B(cᵢ, 3Sᵢ/16)`, equal to `1` on `B̄(cᵢ, Sᵢ/8)`. -/
def bump (i : ι) : ContDiffBump (D.c i) :=
  ⟨D.S i / 8, 3 * D.S i / 16, by have := D.S_pos i; positivity, by have := D.S_pos i; linarith⟩

open Classical in
/-- The bump function transported to `X`. -/
def b (i : ι) (x : X) : ℝ := if x ∈ (D.e i).source then D.bump i (D.e i x) else 0

theorem b_nonneg (i : ι) (x : X) : 0 ≤ D.b i x := by
  unfold b; split_ifs
  · exact (D.bump i).nonneg
  · exact le_rfl

theorem b_le_one (i : ι) (x : X) : D.b i x ≤ 1 := by
  unfold b; split_ifs
  · exact (D.bump i).le_one
  · exact zero_le_one

theorem b_eq_one {i : ι} {x : X} (hx : x ∈ D.V (1 / 8) i) : D.b i x = 1 := by
  simp only [b, hx.1, ↓reduceIte]
  refine (D.bump i).one_of_mem_closedBall (mem_closedBall.2 ?_)
  have h2 : D.e i x ∈ ball (D.c i) (1 / 8 * D.S i) := hx.2
  have := mem_ball.1 h2
  change dist _ _ ≤ D.S i / 8
  linarith

theorem mem_Vbar_of_b_ne_zero {i : ι} {x : X} (h : D.b i x ≠ 0) : x ∈ D.Vbar (3 / 16) i := by
  unfold b at h
  split_ifs at h with hx
  · have hs : D.e i x ∈ Function.support (D.bump i) := h
    rw [(D.bump i).support_eq] at hs
    refine ⟨D.e i x, mem_closedBall.2 ?_, (D.e i).left_inv hx⟩
    have := mem_ball.1 hs
    change dist _ _ < 3 * D.S i / 16 at this
    linarith
  · exact absurd rfl h

theorem contDiffAt_b (k : ι) {i : ι} {w : ℂ} (hw : w ∈ (D.e i).target) :
    ContDiffAt ℝ ∞ (fun w ↦ D.b k ((D.e i).symm w)) w := by
  by_cases h : (D.e i).symm w ∈ (D.e k).source
  · have hev : ∀ᶠ w' in 𝓝 w, (D.e i).symm w' ∈ (D.e k).source :=
      ((D.e i).continuousAt_symm hw).preimage_mem_nhds ((D.e k).open_source.mem_nhds h)
    have heq : (fun w ↦ D.b k ((D.e i).symm w)) =ᶠ[𝓝 w] fun w ↦ D.bump k (D.τ k i w) :=
      hev.mono fun w' h' ↦ by simp only [b, h', ↓reduceIte, τ]
    exact ((D.bump k).contDiff.contDiffAt.comp w (D.contDiffAt_τ hw h)).congr_of_eventuallyEq heq
  · have hnot : (D.e i).symm w ∉ D.Vbar (3 / 16) k := fun h' ↦
      h (D.Vbar_subset_source (by norm_num) k h')
    have hev := D.eventually_eq_zero_of_not_mem (D.isCompact_Vbar (by norm_num) k).isClosed
      (fun x hx ↦ D.mem_Vbar_of_b_ne_zero hx) hw hnot
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- The sum `∑ₖ bₖ ≥ 1`. -/
def sumb (x : X) : ℝ := ∑ k, D.b k x

theorem one_le_sumb (x : X) : 1 ≤ D.sumb x := by
  obtain ⟨i, hi⟩ := D.exists_mem_V x
  calc (1 : ℝ) = D.b i x := (D.b_eq_one hi).symm
    _ ≤ D.sumb x := Finset.single_le_sum (fun k _ ↦ D.b_nonneg k x) (Finset.mem_univ i)

theorem sumb_pos (x : X) : 0 < D.sumb x := zero_lt_one.trans_le (D.one_le_sumb x)

/-- The partition of unity `ψₖ = bₖ / ∑ bₗ`. -/
def ψ (k : ι) (x : X) : ℝ := D.b k x / D.sumb x

theorem ψ_nonneg (k : ι) (x : X) : 0 ≤ D.ψ k x := div_nonneg (D.b_nonneg k x) (D.sumb_pos x).le

theorem ψ_le_one (k : ι) (x : X) : D.ψ k x ≤ 1 :=
  (div_le_one (D.sumb_pos x)).2 (Finset.single_le_sum (fun k _ ↦ D.b_nonneg k x) (Finset.mem_univ k))

theorem sum_ψ (x : X) : ∑ k, D.ψ k x = 1 := by
  simp only [ψ, ← Finset.sum_div]
  exact div_self (D.sumb_pos x).ne'

theorem mem_Vbar_of_ψ_ne_zero {k : ι} {x : X} (h : D.ψ k x ≠ 0) : x ∈ D.Vbar (3 / 16) k :=
  D.mem_Vbar_of_b_ne_zero fun hb ↦ h (by simp [ψ, hb])

theorem mem_V_of_ψ_ne_zero {k : ι} {x : X} (h : D.ψ k x ≠ 0) : x ∈ D.V (1 / 4) k :=
  D.Vbar_subset_V (by norm_num) (by norm_num) k (D.mem_Vbar_of_ψ_ne_zero h)

theorem contDiffAt_ψ (k : ι) {i : ι} {w : ℂ} (hw : w ∈ (D.e i).target) :
    ContDiffAt ℝ ∞ (fun w ↦ D.ψ k ((D.e i).symm w)) w := by
  have hs : ContDiffAt ℝ ∞ (fun w ↦ D.sumb ((D.e i).symm w)) w := by
    simp only [sumb]
    exact ContDiffAt.sum fun l _ ↦ D.contDiffAt_b l hw
  exact (D.contDiffAt_b k hw).div hs (D.sumb_pos _).ne'

theorem eventually_ψ_eq_zero {k i : ι} {w : ℂ} (hw : w ∈ (D.e i).target)
    (h : (D.e i).symm w ∉ D.Vbar (3 / 16) k) : ∀ᶠ w' in 𝓝 w, D.ψ k ((D.e i).symm w') = 0 :=
  D.eventually_eq_zero_of_not_mem (D.isCompact_Vbar (by norm_num) k).isClosed
    (fun _ hx ↦ D.mem_Vbar_of_ψ_ne_zero hx) hw h

/-! ### The splitting `ξᵢⱼ = gⱼ - gᵢ` -/

variable (ξ : D.Z1 (1 / 4))

/-- `gᵢ = -∑ₖ ψₖ ξᵢₖ`, in the chart `zᵢ`. -/
def g (i : ι) (w : ℂ) : ℂ := -∑ k, (D.ψ k ((D.e i).symm w) : ℂ) * ext ((ξ : D.C1 (1 / 4)) (i, k)) w

theorem contDiffAt_g {i : ι} {w : ℂ} (hw : w ∈ ball (D.c i) (1 / 4 * D.S i)) :
    ContDiffAt ℝ ∞ (D.g ξ i) w := by
  have hwt := D.ball_subset_target (by norm_num) i hw
  refine (ContDiffAt.sum fun k _ ↦ ?_).neg
  by_cases h : (D.e i).symm w ∈ D.Vbar (3 / 16) k
  · have hΩ : w ∈ D.Ω (1 / 4) i k :=
      ⟨hw, hwt, D.Vbar_subset_V (by norm_num) (by norm_num) k h⟩
    exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp w (D.contDiffAt_ψ k hwt)).mul
      (contDiffAt_ext _ hΩ)
  · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [D.eventually_ψ_eq_zero hwt h] with w' hw'
    simp [hw']

theorem norm_g_le (i : ι) (w : ℂ) : ‖D.g ξ i w‖ ≤ ∑ k, ‖(ξ : D.C1 (1 / 4)) (i, k)‖ := by
  rw [g, norm_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (D.ψ_nonneg _ _)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (D.ψ_le_one _ _)).trans (norm_ext_le _ _)

theorem g_split {i j : ι} {x : X} (hi : x ∈ D.V (1 / 4) i) (hj : x ∈ D.V (1 / 4) j) :
    ext ((ξ : D.C1 (1 / 4)) (i, j)) (D.e i x) = D.g ξ j (D.e j x) - D.g ξ i (D.e i x) := by
  have key : ∀ k, (D.ψ k x : ℂ) * (ext ((ξ : D.C1 (1 / 4)) (i, k)) (D.e i x) -
      ext ((ξ : D.C1 (1 / 4)) (j, k)) (D.e j x)) =
      (D.ψ k x : ℂ) * ext ((ξ : D.C1 (1 / 4)) (i, j)) (D.e i x) := by
    intro k
    by_cases h : D.ψ k x = 0
    · simp [h]
    · rw [← ξ.2 i j k x hi hj (D.mem_V_of_ψ_ne_zero h)]; ring
  have h1 : D.g ξ j (D.e j x) - D.g ξ i (D.e i x) = ∑ k, (D.ψ k x : ℂ) *
      (ext ((ξ : D.C1 (1 / 4)) (i, k)) (D.e i x) - ext ((ξ : D.C1 (1 / 4)) (j, k)) (D.e j x)) := by
    simp only [g, (D.e j).left_inv hj.1, (D.e i).left_inv hi.1, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [h1, Finset.sum_congr rfl fun k _ ↦ key k, ← Finset.sum_mul, ← Complex.ofReal_sum, D.sum_ψ,
    Complex.ofReal_one, one_mul]

/-! ### The `(0,1)`-form `ω = ∂̄g` -/

/-- `∂̄(gⱼ ∘ τⱼᵢ)`, in the chart `zᵢ`. -/
def Dbar (j i : ι) (w : ℂ) : ℂ := conjWirtingerDeriv (D.g ξ j ∘ D.τ j i) w 1

theorem contDiffAt_g_τ {i m : ι} {w : ℂ} (hw : w ∈ (D.e i).target)
    (hm : (D.e i).symm w ∈ D.V (1 / 4) m) : ContDiffAt ℝ ∞ (D.g ξ m ∘ D.τ m i) w :=
  (D.contDiffAt_g ξ hm.2).comp w (D.contDiffAt_τ hw hm.1)

theorem differentiableAt_g_τ {i m : ι} {w : ℂ} (hw : w ∈ (D.e i).target)
    (hm : (D.e i).symm w ∈ D.V (1 / 4) m) : DifferentiableAt ℝ (D.g ξ m ∘ D.τ m i) w :=
  (D.contDiffAt_g_τ ξ hw hm).differentiableAt (by simp)

theorem Dbar_eq {i j m : ι} {w : ℂ} (hw : w ∈ (D.e i).target) (hm : (D.e i).symm w ∈ D.V (1 / 4) m)
    (hj : (D.e i).symm w ∈ D.V (1 / 4) j) : D.Dbar ξ j i w = D.Dbar ξ m i w := by
  have hN : ∀ᶠ w' in 𝓝 w, w' ∈ (D.e i).target ∧ (D.e i).symm w' ∈ D.V (1 / 4) m ∩ D.V (1 / 4) j :=
    (D.isOpen_target_inter_preimage i ((D.isOpen_V _ m).inter (D.isOpen_V _ j))).mem_nhds ⟨hw, hm, hj⟩
  have heq : D.g ξ j ∘ D.τ j i =ᶠ[𝓝 w]
      (D.g ξ m ∘ D.τ m i) + ext ((ξ : D.C1 (1 / 4)) (m, j)) ∘ D.τ m i := by
    filter_upwards [hN] with w' ⟨_, hm', hj'⟩
    have := D.g_split ξ hm' hj'
    simp only [Function.comp_apply, Pi.add_apply, τ]
    rw [this]; ring
  have hhol : DifferentiableAt ℂ (ext ((ξ : D.C1 (1 / 4)) (m, j)) ∘ D.τ m i) w :=
    (differentiableAt_ext _ (D.e_mem_Ω hm hj)).comp w (D.differentiableAt_τ hw hm.1)
  rw [Dbar, Dbar, heq.conjWirtingerDeriv_eq, conjWirtingerDeriv_add (D.differentiableAt_g_τ ξ hw hm)
    (hhol.restrictScalars ℝ), hhol.conjWirtingerDeriv_eq_zero]
  simp

/-- The form `ω`, in the chart `zᵢ`: `ωᵢ = ∑ⱼ ψⱼ ∂̄(gⱼ ∘ τⱼᵢ)`. -/
def form (i : ι) (w : ℂ) : ℂ := ∑ j, (D.ψ j ((D.e i).symm w) : ℂ) * D.Dbar ξ j i w

theorem form_eq {i m : ι} {w : ℂ} (hw : w ∈ (D.e i).target) (hm : (D.e i).symm w ∈ D.V (1 / 4) m) :
    D.form ξ i w = D.Dbar ξ m i w := by
  have key : ∀ j, (D.ψ j ((D.e i).symm w) : ℂ) * D.Dbar ξ j i w =
      (D.ψ j ((D.e i).symm w) : ℂ) * D.Dbar ξ m i w := by
    intro j
    by_cases h : D.ψ j ((D.e i).symm w) = 0
    · simp [h]
    · rw [D.Dbar_eq ξ hw hm (D.mem_V_of_ψ_ne_zero h)]
  rw [form, Finset.sum_congr rfl fun j _ ↦ key j, ← Finset.sum_mul, ← Complex.ofReal_sum, D.sum_ψ,
    Complex.ofReal_one, one_mul]

theorem form_eventuallyEq {i m : ι} {w : ℂ} (hw : w ∈ (D.e i).target)
    (hm : (D.e i).symm w ∈ D.V (1 / 4) m) : D.form ξ i =ᶠ[𝓝 w] D.Dbar ξ m i := by
  filter_upwards [(D.isOpen_target_inter_preimage i (D.isOpen_V _ m)).mem_nhds ⟨hw, hm⟩] with w' hw'
  exact D.form_eq ξ hw'.1 hw'.2

theorem exists_V_symm (i : ι) (w : ℂ) : ∃ m, (D.e i).symm w ∈ D.V (1 / 4) m := by
  obtain ⟨m, hm⟩ := D.exists_mem_V ((D.e i).symm w)
  exact ⟨m, D.V_mono (by norm_num) m hm⟩

theorem contDiffAt_form {i : ι} {w : ℂ} (hw : w ∈ (D.e i).target) : ContDiffAt ℝ ∞ (D.form ξ i) w := by
  obtain ⟨m, hm⟩ := D.exists_V_symm i w
  refine ContDiffAt.congr_of_eventuallyEq ?_ (D.form_eventuallyEq ξ hw hm)
  exact (D.contDiffAt_g_τ ξ hw hm).conjWirtingerDeriv_apply (by simp) 1

/-! ### Solving `∂̄f = ω` on each disc -/

theorem exists_f : ∃ f : ι → ℂ → ℂ, ∀ i, ContDiffOn ℝ ∞ (f i) (ball (D.c i) (D.S i)) ∧
    ∀ z ∈ ball (D.c i) (D.S i), conjWirtingerDeriv (f i) z 1 = D.form ξ i z := by
  have h : ∀ i, ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f (ball (D.c i) (D.S i)) ∧
      ∀ z ∈ ball (D.c i) (D.S i), conjWirtingerDeriv f z 1 = D.form ξ i z := fun i ↦
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_of_ball (by simp) fun z hz ↦
      (D.contDiffAt_form ξ (D.closedBall_subset i (ball_subset_closedBall hz))).contDiffWithinAt
  choose f hf using h
  exact ⟨f, hf⟩

end DiscSystem

end ModularFormsKB.Milne.Wave15
