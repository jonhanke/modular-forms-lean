import ModularFormsKB.Milne.RS.CanonicalGenus
import ModularFormsKB.Milne.RS.ResidueChangeOfVariables

/-!
# Auxiliary results for the residue theorem on a compact Riemann surface

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Proposition 1.12 (b), pdf p. 19.

* `smulDiff F ω`: the differential `F ω` for a meromorphic function `F` and a meromorphic differential `ω`;
* `residue_comp_add_const`: residues are invariant under translation;
* `res_eq_zero_of_ordZ_eq_zero` and `finite_support_res`: a differential has finitely many nonzero residues on a
  compact Riemann surface;
* `finsum_res_eq_finsum_fiber`: the sum of the residues, grouped along the fibres of a map.
-/

open Filter Topology Set
open scoped Manifold

namespace ModularFormsKB.Milne.RS

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction ModularFormsKB.Milne.RiemannSurface

theorem residue_comp_add_const {f : ℂ → ℂ} {c : ℂ} (hf : _root_.MeromorphicAt f c) :
    TauCeti.Contour.residue (fun s ↦ f (s + c)) 0 = TauCeti.Contour.residue f c := by
  have h := residue_comp_mul_deriv_of_deriv_ne_zero (φ := fun s ↦ s + c) (z₀ := 0)
    (by simpa using hf) (analyticAt_id.add analyticAt_const) (by simp)
  simp only [deriv_add_const, deriv_id'', mul_one, zero_add] at h
  exact h

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
  [CompactSpace X] [T2Space X]

/-- The differential `F ω`. -/
noncomputable def smulDiff (F : MeromorphicFunction X) (ω : MeromorphicDifferential X) :
    MeromorphicDifferential X where
  coeff := mulCoeff ω F
  meromorphicAt x w hw := meromorphicOn_mulCoeff ω F x w hw
  compat x y w hw hy := mulCoeff_compat ω F x y hw hy

theorem smulDiff_coeff (F : MeromorphicFunction X) (ω : MeromorphicDifferential X) (x : X) (w : ℂ) :
    (smulDiff F ω).coeff x w = F.finitePart ((chartAt ℂ x).symm w) * ω.coeff x w := rfl

/-- A differential has residue `0` where its order is nonnegative. -/
theorem res_eq_zero_of_ord_nonneg (ω : MeromorphicDifferential X) {x : X} (hx : 0 ≤ ω.ord x) : ω.res x = 0 :=
  TauCeti.Contour.residue_eq_zero_of_meromorphicOrderAt_nonneg hx

theorem support_res_subset (ω : MeromorphicDifferential X) (hω : ¬ ω.IsZero) :
    Function.support ω.res ⊆ Function.support ω.ordZ := by
  intro x hx
  by_contra h0
  apply hx
  apply res_eq_zero_of_ord_nonneg
  have h : ω.ordZ x = 0 := by simpa using h0
  rw [← coe_ordZ hω x, h]
  rfl

theorem finite_support_res (ω : MeromorphicDifferential X) : (Function.support ω.res).Finite := by
  by_cases hω : ω.IsZero
  · refine Set.finite_empty.subset fun x hx ↦ hx (res_eq_zero_of_ord_nonneg ω ?_)
    rw [hω x]; exact le_top
  · exact (MeromorphicDifferential.finite_support_ordZ hω).subset (support_res_subset ω hω)

/-- The sum of a finitely supported function, grouped along the (finite) fibres of a map. -/
theorem finsum_eq_finsum_fiber {α β : Type*} (u : α → ℂ) (hu : (Function.support u).Finite) (p : α → β)
    (hp : ∀ b, (p ⁻¹' {b}).Finite) :
    ∑ᶠ a, u a = ∑ᶠ b, ∑ a ∈ (hp b).toFinset, u a := by
  classical
  set S := hu.toFinset
  have h1 : ∑ᶠ a, u a = ∑ a ∈ S, u a := finsum_eq_sum_of_support_subset _ (by simp [S])
  have hsupp : Function.support (fun b ↦ ∑ a ∈ (hp b).toFinset, u a) ⊆ (S.image p : Set β) := by
    intro b hb
    obtain ⟨a, ha, hua⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    simp only [Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff] at ha
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨a, by simpa [S] using hua, ha⟩)
  rw [h1, finsum_eq_sum_of_support_subset _ hsupp, ← Finset.sum_fiberwise_of_maps_to
    (g := p) (t := S.image p) (fun a ha ↦ Finset.mem_image_of_mem p ha)]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  refine Finset.sum_subset (fun a ha ↦ ?_) (fun a ha hna ↦ ?_)
  · simp only [Finset.mem_filter] at ha
    simp [ha.2]
  · by_contra hne
    apply hna
    simp only [Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff] at ha
    simp [Finset.mem_filter, S, hne, ha]

end ModularFormsKB.Milne.RS
