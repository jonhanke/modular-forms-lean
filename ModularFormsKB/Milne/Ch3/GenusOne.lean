import ModularFormsKB.Milne.Ch3.Tori

/-!
# Milne, Proposition 3.13: a reduction to the covering form of uniformization

`GenusOneStatement` (every pointed compact Riemann surface of genus one is a complex torus) is reduced to the
named statement `GenusOneCoveringStatement`: such a surface `E` has a holomorphic covering `π : ℂ → E` that is a
local biholomorphism, sends `0` to the base point, and whose fibres are the cosets of a lattice. This is the
uniformization theorem for genus one: the universal cover is `ℂ` and the deck group is a lattice of translations
(Forster, *Lectures on Riemann Surfaces*, §21; Farkas–Kra, *Riemann Surfaces*, IV.6) [unverified]. Its proof needs
the existence of a nowhere-vanishing holomorphic 1-form (Riemann–Roch, itself open in this repository) and the
uniformization of simply connected surfaces; neither is available.

Given the covering, the induced bijection `E ≃ ℂ/Λ` is biholomorphic: locally it is `[·] ∘ π⁻¹`, and its inverse is
`π ∘ [·]⁻¹`, with the local inverse of the quotient map from Tau Ceti
(`TauCeti.isLocalDiffeomorph_addQuotientMk`) (`genusOneStatement_of_covering`).
-/

open Topology Filter
open scoped Manifold ContDiff

namespace ModularFormsKB.Milne

/-- **The universal cover of a genus-one compact Riemann surface** (named statement): a holomorphic local
biholomorphism `π : ℂ → E`, surjective, with `π 0 = x₀` and fibres the cosets of a lattice. -/
structure GenusOneCoveringStatement : Prop where
  out : ∀ (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) 1 E] (x₀ : E),
    Nonempty (E ≃ₜ AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) →
    ∃ (L : PeriodPair) (π : ℂ → E), IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) 1 π ∧ Function.Surjective π ∧
      π 0 = x₀ ∧ ∀ z w, π z = π w ↔ z - w ∈ L.lattice

/-- **Milne, Proposition 3.13**, from the covering form of uniformization. -/
theorem genusOneStatement_of_covering (h : GenusOneCoveringStatement) : GenusOneStatement := by
  refine ⟨fun E _ _ _ x₀ hE ↦ ?_⟩
  obtain ⟨L, π, hπ, hsurj, h0, hfib⟩ := h.out E x₀ hE
  -- the inverse map `ℂ/Λ → E`
  let g : ComplexTorus L → E := Quotient.lift π fun a b ⟨⟨c, hc⟩, hab⟩ ↦ by
    have : c + b = a := hab
    exact (hfib a b).2 (by rw [← this]; simpa using hc)
  have hg : ∀ z, g (ComplexTorus.mk L z) = π z := fun _ ↦ rfl
  have hmk_eq : ∀ z w, z - w ∈ L.lattice → ComplexTorus.mk L z = ComplexTorus.mk L w := by
    intro z w hzw
    unfold ComplexTorus.mk
    exact Quotient.sound ⟨⟨z - w, hzw⟩, by show (z - w) + w = z; ring⟩
  let σ : E → ℂ := fun q ↦ (hsurj q).choose
  have hσ : ∀ q, π (σ q) = q := fun q ↦ (hsurj q).choose_spec
  let e : E ≃ ComplexTorus L :=
    { toFun := fun q ↦ ComplexTorus.mk L (σ q)
      invFun := g
      left_inv := fun q ↦ by simp only [hg, hσ]
      right_inv := fun x ↦ by
        induction x using Quotient.inductionOn with | h z => ?_
        exact hmk_eq _ _ ((hfib _ _).1 (by rw [hσ]; rfl)) }
  have he : ∀ z, e (π z) = ComplexTorus.mk L z := fun z ↦
    hmk_eq _ _ ((hfib _ _).1 (hσ (π z)))
  have hmk := TauCeti.isLocalDiffeomorph_addQuotientMk (I := 𝓘(ℂ)) (n := ω) (G := L.lattice) (M := ℂ)
  refine ⟨L, e, ?_, ?_, ?_⟩
  · -- `e` is locally `[·] ∘ π⁻¹`
    intro q
    obtain ⟨z, rfl⟩ := hsurj q
    have hz := hπ z
    have hloc : (ComplexTorus.mk L ∘ hz.localInverse) =ᶠ[𝓝 (π z)] e := by
      filter_upwards [hz.localInverse_eventuallyEq_right] with q hq
      have hq' : π (hz.localInverse q) = q := hq
      simp only [Function.comp_apply]
      rw [← he]
      exact congrArg e hq'
    have hd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (ComplexTorus.mk L ∘ hz.localInverse) (π z) :=
      ((contMDiff_mk L) _).mdifferentiableAt (by simp) |>.comp _
        (hz.mdifferentiableAt_localInverse one_ne_zero)
    exact hd.congr_of_eventuallyEq hloc.symm
  · -- `e.symm = g` is locally `π ∘ [·]⁻¹`
    intro x
    induction x using Quotient.inductionOn with | h z => ?_
    have hz := hmk z
    have hloc : (π ∘ hz.localInverse) =ᶠ[𝓝 (Quotient.mk _ z)] e.symm := by
      filter_upwards [hz.localInverse_eventuallyEq_right] with y hy
      have hy' : Quotient.mk _ (hz.localInverse y) = y := hy
      simp only [Function.comp_apply]
      show π _ = g y
      conv_rhs => rw [← hy']
      rfl
    have hd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (π ∘ hz.localInverse) (Quotient.mk _ z) :=
      (hπ.mdifferentiable one_ne_zero _).comp _ (hz.mdifferentiableAt_localInverse (by simp))
    exact hd.congr_of_eventuallyEq hloc.symm
  · rw [← h0]; exact he 0

end ModularFormsKB.Milne
