import ModularFormsKB.Milne.RS.SphereConj
import ModularFormsKB.Milne.RS.IsoFunctionField

/-!
# Milne, Theorem 7.5: the uniqueness clause of the named statement is false

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Section 7, Theorem 7.5, pdf p. 95.

The named statement `ModularFormsKB.Milne.RiemannSurfaceAlgebraicStructure X` has two fields. `exists_structure`
asks for a complete regular curve `C` over `ℂ`, a bijection `e` of `X` with the closed points of `C` and a ring
isomorphism `Φ : 𝓜(X) ≃+* ℂ(C)` that is ℂ-linear and matches holomorphy with regularity. The field `unique` asserts
that any two such data `(C, e, Φ)`, `(C', e', Φ')` are related by a unique ℂ-isomorphism `C ≅ C'` compatible with
`e, e'`, but it does **not** require `Φ, Φ'` to be ℂ-linear. This makes it false, already for the Riemann sphere:

* from `(C, e, Φ)` given by `exists_structure`, complex conjugation `σ` of the sphere gives a second datum
  `(C, e ∘ σ, Φ ∘ τ)`, where `τ g = σ ∘ g ∘ σ` is the conjugation automorphism of `𝓜(ℙ¹)` (`RS.conjAut`, a ring
  automorphism that is not ℂ-linear);
* `unique` then gives a ℂ-automorphism `i` of `C` with `i(e x) = e(σ x)`; it induces a ℂ-linear endomorphism of
  `ℂ(C)` (`RS.exists_functionField_hom_of_iso`) and hence a ℂ-algebra endomorphism `ψ` of `𝓜(ℙ¹)` carrying functions
  holomorphic at `σ x` to functions holomorphic at `x`;
* no such `ψ` exists (`RS.no_conj_algHom`): `ψ(z)` would agree with `z ↦ z̄` on `ℂ`, which is not holomorphic.

The corrected statement, with `Φ` and `Φ'` required to be ℂ-linear in `unique`, is
`RiemannSurfaceAlgebraicStructureLinear` (a named statement; Riemann's existence theorem is not available).
-/

open AlgebraicGeometry CategoryTheory TauCeti.RiemannSurface OnePoint
open scoped Manifold

namespace ModularFormsKB.Milne.RS

theorem sphereConj_ne_infty_iff (y : OnePoint ℂ) : sphereConj y ≠ ∞ ↔ y ≠ ∞ := by
  induction y using OnePoint.rec with
  | infty => simp
  | coe z => simp

/-- **Milne, Theorem 7.5, as recorded, is false** for the Riemann sphere: the uniqueness clause fails because it does
not require the field isomorphisms to be ℂ-linear. -/
@[kb "milne2017mf" "Section 7, Theorem 7.5 (pdf p. 95): the uniqueness clause needs C-linear field isomorphisms"]
theorem not_riemannSurfaceAlgebraicStructure_sphere : ¬ RiemannSurfaceAlgebraicStructure (OnePoint ℂ) := by
  intro h
  obtain ⟨C, hC, f, hf, e, Φ, hΦ, hhol⟩ := h.exists_structure
  let e' : OnePoint ℂ ≃ {c : C // IsClosed ({c} : Set C)} := sphereConjEquiv.trans e
  let Φ' : MeromorphicFunction (OnePoint ℂ) ≃+* C.functionField := conjAut.trans Φ
  have hhol' : ∀ (x : OnePoint ℂ) (g : MeromorphicFunction (OnePoint ℂ)),
      (g x ≠ ∞ ↔ ∃ s, (stalkToFunctionField (e' x).1).hom s = Φ' g) := by
    intro x g
    have := hhol (sphereConj x) (conjAut g)
    rw [conjAut_apply, sphereConj_sphereConj, sphereConj_ne_infty_iff] at this
    exact this
  obtain ⟨i, ⟨hif, hie⟩, -⟩ := h.unique C C f f hf hf e e' Φ Φ' hhol hhol'
  obtain ⟨ψ₀, hψℂ, hψloc⟩ := exists_functionField_hom_of_iso f i hif
  let ψ : MeromorphicFunction (OnePoint ℂ) →ₐ[ℂ] MeromorphicFunction (OnePoint ℂ) :=
    { toRingHom := (Φ.symm.toRingHom.comp ψ₀).comp Φ.toRingHom
      commutes' := fun a ↦ by
        change Φ.symm (ψ₀ (Φ (algebraMap ℂ _ a))) = _
        rw [hΦ a, hψℂ a, Φ.symm_apply_eq, hΦ a] }
  refine no_conj_algHom ψ fun g x hg ↦ ?_
  have hex := (hhol (sphereConj x) g).1 hg
  have hx : (e (sphereConj x)).1 = i.hom (e x).1 := (hie x).symm
  rw [hx] at hex
  obtain ⟨s', hs'⟩ := hψloc _ _ hex
  refine (hhol x (ψ g)).2 ⟨s', ?_⟩
  rw [hs']
  change ψ₀ (Φ g) = Φ (Φ.symm (ψ₀ (Φ g)))
  rw [RingEquiv.apply_symm_apply]

open TauCeti.RiemannSurface in
/-- **Milne, Theorem 7.5, corrected** (named statement; Riemann's existence theorem): as
`RiemannSurfaceAlgebraicStructure`, but in the uniqueness clause the field isomorphisms `Φ, Φ'` are required to be
ℂ-linear (as they are in the existence clause). -/
@[kb "milne2017mf" "Section 7, Theorem 7.5 (pdf p. 95), with C-linear field isomorphisms in the uniqueness clause"]
structure RiemannSurfaceAlgebraicStructureLinear (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [ConnectedSpace X] [CompactSpace X] [T2Space X] : Prop where
  exists_structure : ∃ (C : Scheme.{0}) (_ : IsIntegral C) (f : C ⟶ Spec (CommRingCat.of ℂ)),
    IsCompleteRegularCurve ℂ f ∧
    ∃ (e : X ≃ {c : C // IsClosed ({c} : Set C)}) (Φ : MeromorphicFunction X ≃+* C.functionField),
      (∀ z : ℂ, Φ (algebraMap ℂ (MeromorphicFunction X) z) = functionFieldAlgebraMap ℂ f z) ∧
      ∀ (x : X) (g : MeromorphicFunction X),
        (g x ≠ OnePoint.infty ↔ ∃ s, (stalkToFunctionField (e x).1).hom s = Φ g)
  unique : ∀ (C C' : Scheme.{0}) [IsIntegral C] [IsIntegral C'] (f : C ⟶ Spec (CommRingCat.of ℂ))
    (f' : C' ⟶ Spec (CommRingCat.of ℂ)),
    IsCompleteRegularCurve ℂ f → IsCompleteRegularCurve ℂ f' →
    ∀ (e : X ≃ {c : C // IsClosed ({c} : Set C)}) (e' : X ≃ {c : C' // IsClosed ({c} : Set C')})
      (Φ : MeromorphicFunction X ≃+* C.functionField) (Φ' : MeromorphicFunction X ≃+* C'.functionField),
      (∀ z : ℂ, Φ (algebraMap ℂ (MeromorphicFunction X) z) = functionFieldAlgebraMap ℂ f z) →
      (∀ z : ℂ, Φ' (algebraMap ℂ (MeromorphicFunction X) z) = functionFieldAlgebraMap ℂ f' z) →
      (∀ (x : X) (g : MeromorphicFunction X),
        (g x ≠ OnePoint.infty ↔ ∃ s, (stalkToFunctionField (e x).1).hom s = Φ g)) →
      (∀ (x : X) (g : MeromorphicFunction X),
        (g x ≠ OnePoint.infty ↔ ∃ s, (stalkToFunctionField (e' x).1).hom s = Φ' g)) →
      ∃! i : C ≅ C', i.hom ≫ f' = f ∧ ∀ x : X, i.hom (e x).1 = (e' x).1

end ModularFormsKB.Milne.RS
