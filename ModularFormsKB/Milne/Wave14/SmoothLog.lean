import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Homotopy.Lifting

/-!
# Smooth logarithms on convex open subsets of the plane

Part of the proof of Milne, Remark 4.26 (every holomorphic line bundle on $\mathbb H$ is trivial).

A set $S \subseteq \mathbb C$ *has smooth logarithms* (`HasSmoothLog S`) if every real-smooth nowhere-vanishing
function on $S$ is $\exp \psi$ for a real-smooth $\psi$ on $S$. Convex open sets have smooth logarithms
(`Convex.hasSmoothLog`): $\exp : \mathbb C \to \mathbb C^\times$ is a covering map (Mathlib's
`Complex.isCoveringMapOn_exp`) and a convex set is simply connected, so $\varphi$ lifts to a continuous $\psi$; near
each point $\psi = \psi(x_0) + \log(\varphi/\varphi(x_0))$ with the principal branch, which is smooth. Pairwise
disjoint unions of open sets with smooth logarithms have smooth logarithms (`hasSmoothLog_iUnion`).
-/

open Set Topology Filter
open scoped ContDiff

noncomputable section

namespace ModularFormsKB.Milne.Wave14

/-- Quotients of real-smooth complex-valued functions. -/
theorem contDiffOn_div' {f g : ℂ → ℂ} {s : Set ℂ} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s)
    (h : ∀ x ∈ s, g x ≠ 0) : ContDiffOn ℝ ∞ (fun x ↦ f x / g x) s := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv h)

theorem contDiffAt_div' {f g : ℂ → ℂ} {x : ℂ} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (h : g x ≠ 0) : ContDiffAt ℝ ∞ (fun x ↦ f x / g x) x := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv h)

/-- Every real-smooth nowhere-vanishing function on `S` has a real-smooth logarithm on `S`. -/
def HasSmoothLog (S : Set ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiffOn ℝ ∞ φ S → (∀ x ∈ S, φ x ≠ 0) →
    ∃ ψ : ℂ → ℂ, ContDiffOn ℝ ∞ ψ S ∧ ∀ x ∈ S, φ x = Complex.exp (ψ x)

theorem hasSmoothLog_empty : HasSmoothLog ∅ :=
  fun _ _ _ ↦ ⟨0, contDiffOn_empty, fun _ h ↦ h.elim⟩

/-- A continuous logarithm of a smooth nowhere-vanishing function on an open set is smooth. -/
theorem contDiffOn_of_continuousOn_exp_eq {S : Set ℂ} (hS : IsOpen S) {φ ψ : ℂ → ℂ}
    (hφ : ContDiffOn ℝ ∞ φ S) (hφ0 : ∀ x ∈ S, φ x ≠ 0) (hψ : ContinuousOn ψ S)
    (heq : ∀ x ∈ S, φ x = Complex.exp (ψ x)) : ContDiffOn ℝ ∞ ψ S := by
  intro x₀ hx₀
  have hx₀n : S ∈ 𝓝 x₀ := hS.mem_nhds hx₀
  have hcont : ContinuousAt ψ x₀ := hψ.continuousAt hx₀n
  -- near `x₀`, `ψ - ψ x₀` is small, so it is the principal logarithm of `φ / φ x₀`
  have hsmall : ∀ᶠ y in 𝓝 x₀, ‖ψ y - ψ x₀‖ < Real.pi := by
    have := hcont.sub (continuousAt_const (y := ψ x₀))
    exact this.norm.eventually (gt_mem_nhds (by simpa using Real.pi_pos))
  have hev : ψ =ᶠ[𝓝 x₀] fun y ↦ ψ x₀ + Complex.log (φ y / φ x₀) := by
    filter_upwards [hsmall, hx₀n] with y hy hyS
    have him : |(ψ y - ψ x₀).im| < Real.pi := (Complex.abs_im_le_norm _).trans_lt hy
    rw [abs_lt] at him
    have hexp : φ y / φ x₀ = Complex.exp (ψ y - ψ x₀) := by
      rw [Complex.exp_sub, ← heq y hyS, ← heq x₀ hx₀]
    rw [hexp, Complex.log_exp him.1 him.2.le]
    ring
  refine (ContDiffAt.contDiffWithinAt ?_).congr_of_eventuallyEq
    (hev.filter_mono nhdsWithin_le_nhds) (hev.eq_of_nhds)
  refine contDiffAt_const.add ?_
  have h1 : φ x₀ / φ x₀ = 1 := div_self (hφ0 x₀ hx₀)
  have hlog : ContDiffAt ℝ ∞ Complex.log (φ x₀ / φ x₀) := by
    rw [h1]
    exact (Complex.contDiffAt_log (by simp [Complex.slitPlane])).restrict_scalars ℝ
  exact hlog.comp x₀ (((hφ x₀ hx₀).contDiffAt hx₀n).div_const _)

/-- **Convex open sets have smooth logarithms.** -/
theorem Convex.hasSmoothLog {S : Set ℂ} (hS : IsOpen S) (hc : Convex ℝ S) : HasSmoothLog S := by
  intro φ hφ hφ0
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact hasSmoothLog_empty φ hφ hφ0
  have : ContractibleSpace S := hc.contractibleSpace hne
  have : LocallyPathConnectedSpace S := hS.locallyPathConnectedSpace
  obtain ⟨a₀, ha₀⟩ := hne
  let f : C(S, ℂ) := ⟨fun x ↦ φ x, hφ.continuousOn.domRestrict⟩
  have hf0 : ∀ a : S, f a ∈ ({0}ᶜ : Set ℂ) := fun a ↦ hφ0 a a.2
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (a₀ := ⟨a₀, ha₀⟩) (e₀ := Complex.log (φ a₀)) (Complex.exp_log (hφ0 a₀ ha₀)) hf0
  classical
  let ψ : ℂ → ℂ := fun x ↦ if h : x ∈ S then F ⟨x, h⟩ else 0
  have hψS : ∀ x (h : x ∈ S), ψ x = F ⟨x, h⟩ := fun x h ↦ dite_eq_left_of_eq_true (eq_true h)
  have heq : ∀ x ∈ S, φ x = Complex.exp (ψ x) := by
    intro x hx
    rw [hψS x hx]
    exact (congrFun hF ⟨x, hx⟩).symm
  have hψc : ContinuousOn ψ S := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert F.continuous using 1
    ext ⟨x, hx⟩
    exact hψS x hx
  exact ⟨ψ, contDiffOn_of_continuousOn_exp_eq hS hφ hφ0 hψc heq, heq⟩

/-- **Disjoint unions.** A union of pairwise disjoint open sets with smooth logarithms has smooth logarithms. -/
theorem hasSmoothLog_iUnion {ι : Type*} {S : ι → Set ℂ} (hS : ∀ i, IsOpen (S i))
    (hd : Pairwise (Function.onFun Disjoint S)) (hL : ∀ i, HasSmoothLog (S i)) : HasSmoothLog (⋃ i, S i) := by
  intro φ hφ hφ0
  have hloc : ∀ i, ∃ ψ : ℂ → ℂ, ContDiffOn ℝ ∞ ψ (S i) ∧ ∀ x ∈ S i, φ x = Complex.exp (ψ x) :=
    fun i ↦ hL i φ (hφ.mono (subset_iUnion _ i)) (fun x hx ↦ hφ0 x (mem_iUnion.2 ⟨i, hx⟩))
  choose ψ hψ hψe using hloc
  classical
  let Ψ : ℂ → ℂ := fun x ↦ if h : ∃ i, x ∈ S i then ψ h.choose x else 0
  have hΨ : ∀ i, ∀ x ∈ S i, Ψ x = ψ i x := by
    intro i x hx
    have h : ∃ i, x ∈ S i := ⟨i, hx⟩
    have hi : h.choose = i := by
      by_contra hne
      exact (hd hne).le_bot ⟨h.choose_spec, hx⟩
    simp only [Ψ, dite_eq_left_of_eq_true (eq_true h), hi]
  refine ⟨Ψ, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    refine ⟨S i, hS i, hi, ?_⟩
    have : (⋃ j, S j) ∩ S i = S i := inter_eq_right.2 (subset_iUnion _ i)
    rw [this]
    exact (hψ i).congr (hΨ i)
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    rw [hΨ i x hi]
    exact hψe i x hi

end ModularFormsKB.Milne.Wave14
