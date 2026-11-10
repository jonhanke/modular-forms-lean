import ModularFormsKB.Milne.Wave4A.GenusZero
import ModularFormsKB.Milne.Ch4.UncondDimension

/-!
# Riemann–Roch on `X(1)`, and Theorem 4.9 for `Γ(1)`

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, Theorem 1.20, and §4, Theorem 4.9 (pdf pp. 21, 51).

A finite holomorphic map `f : X → Y` of degree one is a biholomorphism (Tau Ceti's `biholomorphOfDegreeEqOne`) with
all local multiplicities `1`. Pulling back meromorphic functions along `f` identifies `L(f^*D)` with `L(D)`
(`ell_divisorPullback_of_degree_eq_one`), every divisor on `X` is a pullback, and `div d(h ∘ f) = f^* div(dh)`. Hence
the Riemann–Roch theorem (the named statement `RiemannRochStatement`) transfers from `Y` to `X`
(`riemannRochStatement_of_degree_eq_one`).

Applied to `j : X(Γ(1)) → ℙ¹` and Exercise 1.24 (`riemannRoch_sphere`): the Riemann–Roch theorem holds on `X(1)`
(`riemannRochStatement_modularCurveX_top`), and with the canonical degree (`genus_and_canonicalDegree_top`) the
dimension formula, Theorem 4.9, holds for `Γ(1)` (`dimensionFormula_top`), unconditionally.
-/

open Set
open scoped MatrixGroups Manifold

noncomputable section

namespace ModularFormsKB.Milne

open TauCeti TauCeti.RiemannSurface TauCeti.AlgebraicGeometry RiemannSurface MeromorphicFunction

section Transfer

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [ConnectedSpace X] [T2Space X] [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace Y] [ConnectedSpace Y] [T2Space Y]
  (f : FiniteHolomorphicMap X Y) (hf : degree f = 1)

include hf

theorem localMultiplicity_eq_one_of_degree_eq_one (x : X) : localMultiplicity f x = 1 := by
  have h1 := localMultiplicity_le_degree f x
  have h2 := localMultiplicity_pos f x
  omega

/-- Pullback of divisors along a degree-one map: `(f^*D)(x) = D(f x)`. -/
theorem divisorPullback_apply_of_degree_eq_one (D : WeilDivisor Y) (x : X) :
    divisorPullback f D x = D (f x) := by
  show (localMultiplicity f x : ℤ) * D (f x) = D (f x)
  rw [localMultiplicity_eq_one_of_degree_eq_one f hf x]
  simp

/-- The order of the pullback `h ∘ f` along the biholomorphism `f`. -/
theorem order_comapAlgEquiv_of_degree_eq_one (h : MeromorphicFunction Y) (x : X) :
    order x (comapAlgEquiv (biholomorphOfDegreeEqOne f hf) h) = order (f x) h := by
  rw [order_apply, order_apply, finitePart_comapAlgEquiv]
  rw [meromorphicOrderAt_comp (h.meromorphicAt_finitePart _)
    (.of_forall fun y ↦ (biholomorphOfDegreeEqOne f hf).mdifferentiable (by simp) y)
    (by simpa using f.not_eventuallyConst x)]
  simp [localMultiplicity_eq_one_of_degree_eq_one f hf x]

/-- `L(f^*D) ≅ L(D)` for a degree-one map `f`. -/
theorem ell_divisorPullback_of_degree_eq_one (D : WeilDivisor Y) :
    ell X (divisorPullback f D) = ell Y D := by
  set e := (comapAlgEquiv (biholomorphOfDegreeEqOne f hf)).toLinearEquiv
  have hmap : (rrSpace Y D).map (e : MeromorphicFunction Y →ₗ[ℂ] MeromorphicFunction X) =
      rrSpace X (divisorPullback f D) := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩ x
      rw [divisorPullback_apply_of_degree_eq_one f hf]
      show _ ≤ order x (comapAlgEquiv (biholomorphOfDegreeEqOne f hf) h)
      rw [order_comapAlgEquiv_of_degree_eq_one f hf]
      exact hh (f x)
    · intro hg
      refine ⟨(comapAlgEquiv (biholomorphOfDegreeEqOne f hf)).symm g, fun y ↦ ?_, ?_⟩
      · obtain ⟨x, rfl⟩ := f.surjective y
        rw [← order_comapAlgEquiv_of_degree_eq_one f hf, AlgEquiv.apply_symm_apply]
        have := hg x
        rwa [divisorPullback_apply_of_degree_eq_one f hf] at this
      · exact (comapAlgEquiv (biholomorphOfDegreeEqOne f hf)).apply_symm_apply g
  unfold ell
  rw [← hmap]
  exact (e.submoduleMap (rrSpace Y D)).finrank_eq.symm

theorem finiteDimensional_divisorPullback_of_degree_eq_one (D : WeilDivisor Y)
    (hD : FiniteDimensional ℂ (rrSpace Y D)) : FiniteDimensional ℂ (rrSpace X (divisorPullback f D)) := by
  set e := (comapAlgEquiv (biholomorphOfDegreeEqOne f hf)).toLinearEquiv
  have hmap : (rrSpace Y D).map (e : MeromorphicFunction Y →ₗ[ℂ] MeromorphicFunction X) =
      rrSpace X (divisorPullback f D) := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩ x
      rw [divisorPullback_apply_of_degree_eq_one f hf]
      show _ ≤ order x (comapAlgEquiv (biholomorphOfDegreeEqOne f hf) h)
      rw [order_comapAlgEquiv_of_degree_eq_one f hf]
      exact hh (f x)
    · intro hg
      refine ⟨(comapAlgEquiv (biholomorphOfDegreeEqOne f hf)).symm g, fun y ↦ ?_, ?_⟩
      · obtain ⟨x, rfl⟩ := f.surjective y
        rw [← order_comapAlgEquiv_of_degree_eq_one f hf, AlgEquiv.apply_symm_apply]
        have := hg x
        rwa [divisorPullback_apply_of_degree_eq_one f hf] at this
      · exact (comapAlgEquiv (biholomorphOfDegreeEqOne f hf)).apply_symm_apply g
  rw [← hmap]
  exact Module.Finite.equiv (e.submoduleMap (rrSpace Y D))

/-- Every divisor on `X` is a pullback along the degree-one map `f`. -/
theorem exists_divisorPullback_eq_of_degree_eq_one (D : WeilDivisor X) :
    ∃ D' : WeilDivisor Y, divisorPullback f D' = D := by
  refine ⟨Finsupp.equivMapDomain (biholomorphOfDegreeEqOne f hf).toEquiv D, Finsupp.ext fun x ↦ ?_⟩
  rw [divisorPullback_apply_of_degree_eq_one f hf, Finsupp.equivMapDomain_apply]
  congr 1
  exact (biholomorphOfDegreeEqOne f hf).toEquiv.symm_apply_apply x

/-- A degree-one map is unramified: `R_f = 0` as a divisor. -/
theorem ramificationDivisor_eq_zero_of_degree_eq_one : ramificationDivisor f = 0 := by
  refine Finsupp.ext fun x ↦ ?_
  show (localMultiplicity f x : ℤ) - 1 = 0
  rw [localMultiplicity_eq_one_of_degree_eq_one f hf x]
  simp

omit hf in
/-- `ℓ` is invariant under linear equivalence: `ℓ(div ω - D) = ℓ(div ω₀ - D)` for nonzero `ω`, `ω₀`. -/
theorem ell_divisor_sub_eq {ω ω₀ : MeromorphicDifferential X} (hω : ¬ ω.IsZero) (hω₀ : ¬ ω₀.IsZero)
    (D : WeilDivisor X) : ell X (ω.divisor - D) = ell X (ω₀.divisor - D) := by
  have h := ell_sub_principalDivisor (RS.diffQuot_ne_zero hω hω₀) (ω.divisor - D)
  rw [← h, RS.divisor_eq_principalDivisor_diffQuot_add hω hω₀]
  congr 1
  abel

/-- **The Riemann–Roch theorem transfers along degree-one maps.** If `f : X → Y` has degree one and `Y` satisfies
the Riemann–Roch theorem and has a nonconstant meromorphic function, so does `X`. -/
theorem riemannRochStatement_of_degree_eq_one (hRR : RiemannRochStatement Y)
    {h : MeromorphicFunction Y} (hh : IsNonconstant h) : RiemannRochStatement X where
  finiteDimensional D := by
    obtain ⟨D', rfl⟩ := exists_divisorPullback_eq_of_degree_eq_one f hf D
    exact finiteDimensional_divisorPullback_of_degree_eq_one f hf D' (hRR.finiteDimensional D')
  exists_genus := by
    obtain ⟨g, hg⟩ := hRR.exists_genus
    refine ⟨g, fun ω hω D ↦ ?_⟩
    obtain ⟨D', rfl⟩ := exists_divisorPullback_eq_of_degree_eq_one f hf D
    have hωY := RS.differential_not_isZero hh
    have hωX := RS.differential_not_isZero (RS.isNonconstant_pullbackFun f hh)
    have hdiv := RS.divisor_differential_pullbackFun f hh
    rw [ramificationDivisor_eq_zero_of_degree_eq_one f hf, add_zero] at hdiv
    rw [ell_divisor_sub_eq hω hωX, hdiv, ← map_sub, ell_divisorPullback_of_degree_eq_one f hf,
      ell_divisorPullback_of_degree_eq_one f hf, degree_divisorPullback, hf]
    have := hg _ hωY D'
    push_cast
    linarith

end Transfer

/-- **The Riemann–Roch theorem on `X(1)`** (Theorem 1.20 for `X(Γ(1))`), from Exercise 1.24 along the degree-one
map `j`. -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), for X(1), pdf p. 21"]
theorem riemannRochStatement_modularCurveX_top : RiemannRochStatement (ModularCurveX ⊤) :=
  riemannRochStatement_of_degree_eq_one (modularCurveXJ ⊤)
    (by rw [degree_modularCurveXJ, genusIndex_top]) riemannRoch_sphere RS.isNonconstant_coordinate

/-- **Milne, Theorem 4.9 for `Γ(1)`** (the dimension formula `dim M_k(Γ(1)) = (2k - 1)(g - 1) + ε∞ k + ∑_P ⌊k(1 -
1/e_P)⌋`, `k ≥ 1`), unconditional: Riemann–Roch on `X(1)` and the canonical degree. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51)"]
theorem dimensionFormula_top : DimensionFormula ⊤ :=
  dimensionFormula_of_riemannRoch ⊤ riemannRochStatement_modularCurveX_top genus_and_canonicalDegree_top.2

end ModularFormsKB.Milne
