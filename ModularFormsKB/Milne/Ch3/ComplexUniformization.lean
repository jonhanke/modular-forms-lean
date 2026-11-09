import ModularFormsKB.Milne.Ch3.GroupLaw
import ModularFormsKB.Milne.Ch12.CMDefs

/-!
# The analytic theory of elliptic curves over `ℂ` (Milne, Section 12)

`ComplexUniformization` has three fields. Two are proved here unconditionally:

* `exists_lattice`: every elliptic curve over `ℂ` is `E(Λ)` (`exists_periodPair_variableChange`, from the
  surjectivity of `j`);
* `j_eq_iff`: `j(Λ) = j(Λ')` exactly when `Λ' = αΛ` (`j_eq_iff_homothetic`, from the fact that `g₂, g₃` determine
  the lattice).

The third, `endRingEquiv` (`End(E(Λ)) ≅ {α | αΛ ⊆ Λ}`), is reduced to two named statements about Tau Ceti's
endomorphisms `TauCeti.Isogeny.Hom`:

* `EndomorphismLiftStatement`: every endomorphism of `E(Λ)` is induced by `z ↦ αz` on `ℂ` (the analytic lifting
  of a holomorphic map of complex tori, Milne Proposition 3.3, through the analytic isomorphism `ℂ/Λ ≅ E(Λ)`);
* `MultiplicationIsogenyStatement`: for `αΛ ⊆ Λ`, the map `[z] ↦ [αz]` is an endomorphism of the curve (it is
  given by rational functions of `℘, ℘'`, by Proposition 3.11).

Given these, `endRingEquiv` follows from the injectivity of the point map modulo `Λ`, the group law
(`weierstrassPoint_add`) and Tau Ceti's rigidity `TauCeti.Isogeny.Hom.ext_pointMap_of_prime_zsmul_eq_zero`
(`complexUniformization_of_endomorphisms`).
-/

open Complex PeriodPair TauCeti TauCeti.Isogeny

namespace ModularFormsKB.Milne

/-- **Every endomorphism of `E(Λ)` lifts to `ℂ`** (named statement): it is induced by multiplication by a complex
number. Milne, Proposition 3.3 with Proposition 3.12; Silverman, *The Arithmetic of Elliptic Curves*, VI.4.1. -/
structure EndomorphismLiftStatement : Prop where
  out : ∀ (L : PeriodPair) (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine),
    ∃ α : ℂ, ∀ z, f.pointMap (L.weierstrassPoint z) = L.weierstrassPoint (α * z)

/-- **Multiplication by `α` with `αΛ ⊆ Λ` is an endomorphism of `E(Λ)`** (named statement). Silverman, *The
Arithmetic of Elliptic Curves*, VI.4.1. -/
structure MultiplicationIsogenyStatement : Prop where
  out : ∀ (L : PeriodPair) (α : ℂ), (∀ x ∈ L.lattice, α * x ∈ L.lattice) →
    ∃ f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine,
      ∀ z, f.pointMap (L.weierstrassPoint z) = L.weierstrassPoint (α * z)

/-- Multiplication maps inducing the same map on points are equal. -/
theorem eq_of_weierstrassPoint_mul_eq {L : PeriodPair} {α β : ℂ}
    (h : ∀ z, L.weierstrassPoint (α * z) = L.weierstrassPoint (β * z)) : α = β := by
  by_contra hne
  have hd : α - β ≠ 0 := sub_ne_zero.2 hne
  have := sub_mem_of_weierstrassPoint_eq (h ((α - β)⁻¹ * (L.ω₁ / 2)))
  rw [← sub_mul, mul_inv_cancel_left₀ hd] at this
  exact L.ω₁_div_two_notMem_lattice this

theorem hom_pointMap_zero {L : PeriodPair}
    (f : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine) : f.pointMap 0 = 0 := by
  have := Hom.pointMap_add f 0 0
  rw [add_zero] at this
  exact (add_eq_left.1 this.symm)

theorem hom_ext_of_weierstrassPoint {L : PeriodPair}
    {f g : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine}
    (h : ∀ z, f.pointMap (L.weierstrassPoint z) = g.pointMap (L.weierstrassPoint z)) : f = g := by
  refine Hom.ext_pointMap_of_prime_zsmul_eq_zero fun _ _ _ P _ ↦ ?_
  obtain ⟨x, rfl⟩ := surjective_torusPoint (L := L) P
  induction x using Quotient.inductionOn with | h z => exact h z

/-- **`End(E(Λ)) ≅ {α | αΛ ⊆ Λ}`**, from the two named statements. -/
theorem endRingEquiv_of (h₁ : EndomorphismLiftStatement) (h₂ : MultiplicationIsogenyStatement)
    (L : PeriodPair) :
    ∃ e : Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine ≃+* latticeEnd L.lattice,
      ∀ f z, f.pointMap (L.weierstrassPoint z) = L.weierstrassPoint ((e f : ℂ) * z) := by
  classical
  set E := Hom L.weierstrassCurve.toAffine L.weierstrassCurve.toAffine
  let α : E → ℂ := fun f ↦ (h₁.out L f).choose
  have hα : ∀ f z, f.pointMap (L.weierstrassPoint z) = L.weierstrassPoint (α f * z) :=
    fun f ↦ (h₁.out L f).choose_spec
  have hmem : ∀ f, α f ∈ latticeEnd L.lattice := by
    intro f x hx
    have := hα f x
    rw [L.weierstrassPoint_of_mem hx, hom_pointMap_zero, eq_comm,
      L.weierstrassPoint_eq_zero_iff] at this
    exact this
  let β : latticeEnd L.lattice → E := fun a ↦ (h₂.out L a a.2).choose
  have hβ : ∀ a z, (β a).pointMap (L.weierstrassPoint z) = L.weierstrassPoint ((a : ℂ) * z) :=
    fun a ↦ (h₂.out L a a.2).choose_spec
  refine ⟨{ toFun := fun f ↦ ⟨α f, hmem f⟩
            invFun := β
            left_inv := fun f ↦ hom_ext_of_weierstrassPoint fun z ↦ by rw [hβ, hα]
            right_inv := fun a ↦ Subtype.ext (eq_of_weierstrassPoint_mul_eq fun z ↦ by
              rw [← hα, hβ])
            map_mul' := fun f g ↦ Subtype.ext (eq_of_weierstrassPoint_mul_eq fun z ↦ by
              simp only [Subring.coe_mul]
              rw [← hα, Hom.mul_def, Hom.comp_pointMap, hα, hα, mul_assoc])
            map_add' := fun f g ↦ Subtype.ext (eq_of_weierstrassPoint_mul_eq fun z ↦ by
              simp only [Subring.coe_add]
              rw [← hα, Hom.add_pointMap, hα, hα, add_mul, weierstrassPoint_add]) }, ?_⟩
  intro f z
  exact hα f z

/-- **`ComplexUniformization`**, conditional on the two named statements about endomorphisms; its fields
`exists_lattice` and `j_eq_iff` are proved unconditionally. -/
theorem complexUniformization_of_endomorphisms (h₁ : EndomorphismLiftStatement)
    (h₂ : MultiplicationIsogenyStatement) : ComplexUniformization where
  exists_lattice W _ := exists_periodPair_variableChange W
  endRingEquiv := endRingEquiv_of h₁ h₂
  j_eq_iff := j_eq_iff_homothetic

end ModularFormsKB.Milne
