import ModularFormsKB.Milne.RiemannSurface.Basic
import Mathlib.Analysis.Complex.Liouville
import ModularFormsKB.Citation
/-!
# Milne, Chapter 1: the Riemann sphere has genus zero

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, Example 1.23 (pdf p. 22), and §2,
Proposition 2.21 (pdf p. 36).

The genus of a compact Riemann surface is the dimension of its space of holomorphic differential forms
(`ModularFormsKB.Milne.RiemannSurface.genus`). On the Riemann sphere `OnePoint ℂ` (Tau Ceti's charts: the affine
chart at finite points, the inverted chart `w = 1/z` at `∞`) every holomorphic differential vanishes: its coefficient
`F` in the affine chart is entire, and near `∞` it is `F(z) = -G(1/z)/z²` with `G` its holomorphic coefficient in the
inverted chart, so `F → 0` at infinity and `F = 0` by Liouville's theorem. Hence `genus (OnePoint ℂ) = 0`.

The book obtains `g = 0` for the sphere from the Riemann–Roch theorem (Example 1.23; conditional form
`genus_eq_zero_of_riemannRoch` in `RiemannSurface/Examples.lean`); the direct proof here needs no input.
-/

open Filter Topology Set OnePoint
open scoped Manifold

namespace ModularFormsKB.Milne.RiemannSurface

/-- The transition from the inverted chart at `∞` to the affine chart at a finite point is `w ↦ w⁻¹`. -/
theorem transition_infty_coe (z : ℂ) :
    transition (∞ : OnePoint ℂ) (z : OnePoint ℂ) = fun w ↦ w⁻¹ := by
  funext w
  simp only [transition, chartAt_infty, chartAt_coe]
  exact congrFun affineChart_comp_invChart_symm w

/-- The transition between the charts at two finite points is the identity (both are the affine chart). -/
theorem transition_coe_coe (z z' : ℂ) :
    transition (z : OnePoint ℂ) (z' : OnePoint ℂ) = id := by
  funext w
  simp only [transition, chartAt_coe, id]
  exact affineChart.right_inv (by simp)

/-- Every holomorphic differential form on the Riemann sphere is zero. -/
theorem holomorphicDifferentials_onePoint_eq_bot :
    holomorphicDifferentials (OnePoint ℂ) = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨h0, hdiff, hcompat⟩
  rw [Submodule.mem_bot]
  set F : ℂ → ℂ := c ((0 : ℂ) : OnePoint ℂ) with hFdef
  set G : ℂ → ℂ := c (∞ : OnePoint ℂ) with hGdef
  have hF : Differentiable ℂ F := by
    intro z
    have := hdiff ((0 : ℂ) : OnePoint ℂ)
    rw [chartAt_coe, affineChart_target] at this
    exact (this z (mem_univ z)).differentiableAt (by simp)
  have hG : Differentiable ℂ G := by
    intro z
    have := hdiff (∞ : OnePoint ℂ)
    rw [chartAt_infty, invChart_target] at this
    exact (this z (mem_univ z)).differentiableAt (by simp)
  -- the overlap relation `G w = F (1/w) · (-1/w²)` for `w ≠ 0`
  have hrel : ∀ w : ℂ, w ≠ 0 → G w = F w⁻¹ * -(w ^ 2)⁻¹ := by
    intro w hw
    have hmem : (chartAt ℂ (∞ : OnePoint ℂ)).symm w ∈ (chartAt ℂ ((0 : ℂ) : OnePoint ℂ)).source := by
      rw [chartAt_infty, chartAt_coe, invChart_symm_of_ne_zero hw, affineChart_source]
      simp
    have := hcompat (∞ : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ) w (by simp [chartAt_infty]) hmem
    rw [transition_infty_coe, deriv_inv'] at this
    exact this
  -- `F → 0` at infinity
  have hlim : Tendsto F (cocompact ℂ) (𝓝 0) := by
    have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    have h1 : Tendsto (fun z : ℂ ↦ -(G z⁻¹ * (z⁻¹) ^ 2)) (cocompact ℂ) (𝓝 0) := by
      have hGc : Tendsto (fun z : ℂ ↦ G z⁻¹) (cocompact ℂ) (𝓝 (G 0)) :=
        (hG.continuous.tendsto 0).comp hinv
      have := (hGc.mul (hinv.pow 2)).neg
      simpa using this
    refine h1.congr' ?_
    have hne : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
      have := (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
      filter_upwards [this] with z hz
      exact hz
    filter_upwards [hne] with z hz
    have hz' : z⁻¹ ≠ 0 := inv_ne_zero hz
    rw [hrel z⁻¹ hz', inv_inv]
    field_simp
  have hF0 : F = fun _ ↦ 0 := Differentiable.eq_const_of_tendsto_cocompact hF hlim
  have hG0 : G = 0 := by
    have hoff : ∀ w : ℂ, w ≠ 0 → G w = 0 := fun w hw ↦ by
      rw [hrel w hw, hF0]; simp
    funext w
    by_cases hw : w = 0
    · subst hw
      have hc : ContinuousAt G 0 := hG.continuous.continuousAt
      have : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact (hoff w hw).symm
      exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) this
    · exact hoff w hw
  funext x w
  induction x using OnePoint.rec with
  | infty => exact congrFun hG0 w
  | coe z =>
    have hmem : (chartAt ℂ (z : OnePoint ℂ)).symm w ∈ (chartAt ℂ ((0 : ℂ) : OnePoint ℂ)).source := by
      rw [chartAt_coe, chartAt_coe, affineChart_source]
      simp [affineChart_symm_apply]
    have := hcompat (z : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ) w (by simp [chartAt_coe]) hmem
    rw [transition_coe_coe] at this
    rw [this]
    show F (id w) * _ = 0
    rw [hF0]
    simp

/-- **The Riemann sphere has genus zero** (Milne, Example 1.23 and Proposition 2.21): there is no nonzero
holomorphic differential form on `OnePoint ℂ`. Proved directly (Liouville's theorem), without Riemann–Roch. -/
@[kb "milne2017mf" "Example 1.23: the Riemann sphere has genus 0, pdf p. 22"]
theorem genus_onePoint : genus (OnePoint ℂ) = 0 := by
  rw [genus, holomorphicDifferentials_onePoint_eq_bot]
  exact finrank_bot ℂ _

end ModularFormsKB.Milne.RiemannSurface
