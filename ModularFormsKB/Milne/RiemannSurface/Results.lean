import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Degree
import TauCeti.Analysis.Complex.RiemannSurface.RationalFunction
import TauCeti.Analysis.Complex.RiemannSurface.Ramification
import TauCeti.FieldTheory.FunctionField.Basic
import ModularFormsKB.Milne.RiemannSurface.Basic

/-!
# Milne, Chapter 1: analysis on compact Riemann surfaces

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, pdf pp. 18–23.

* Proposition 1.12 (a): `deg div(f) = 0` (a meromorphic function has as many zeros as poles).
* Corollary 1.13: a nonconstant meromorphic function takes every value `n = valence > 0` times (Tau Ceti
  `TauCeti.RiemannSurface.fiberMultiplicitySum_eq_degree`, restated).
* Proposition 1.14: the meromorphic functions on the Riemann sphere are `ℂ(z)` (Tau Ceti
  `TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv`, restated).
* Proposition 1.16: every meromorphic function is a root of a polynomial of degree `≤ valence f` over `ℂ(f)` (Tau Ceti
  `TauCeti.RiemannSurface.MeromorphicFunction.exists_monic_natDegree_eq_degree_eval₂_eq_zero`, restated).
* Theorem 1.17: the existence of a nonconstant meromorphic function is a named statement; from it, `M(X)` is a
  finitely generated field of transcendence degree one (Tau Ceti's `TauCeti.IsFunctionField`).
* Example 1.18: on the sphere, `M(S) = ℂ(f)` for `f` of valence one.
* Corollaries 1.21 and 1.22, from the named Riemann–Roch statement.
* Theorem 1.27 (Riemann–Hurwitz): named statement, with Tau Ceti's ramification degree
  `TauCeti.RiemannSurface.ramificationDegree f = ∑ (e_P - 1)`.
-/

open Filter Topology Set
open scoped Manifold

namespace ModularFormsKB.Milne.RiemannSurface

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-! ### Proposition 1.12 (a) -/

/-- The coordinate of the Riemann sphere has a simple zero at `0`. -/
theorem order_coordinate_zero :
    order ((0 : ℂ) : OnePoint ℂ) coordinate = 1 := by
  rw [order_apply, TauCeti.RiemannSurface.meromorphicOrderAt_def, OnePoint.chartAt_coe]
  have h : (coordinate.finitePart ∘ (OnePoint.affineChart (𝕜 := ℂ)).symm) =
      fun z : ℂ ↦ z - 0 := by
    funext z
    simp only [Function.comp_apply, OnePoint.affineChart_symm_apply, sub_zero]
    exact finitePart_of_eq_coe (coordinate_apply _)
  rw [h, OnePoint.affineChart_coe]
  exact meromorphicOrderAt_id_sub_const

/-- The coordinate of the Riemann sphere has a simple pole at `∞`. -/
theorem order_coordinate_infty :
    order OnePoint.infty coordinate = -1 := by
  rw [order_apply, TauCeti.RiemannSurface.meromorphicOrderAt_def, OnePoint.chartAt_infty]
  have h : (coordinate.finitePart ∘ (OnePoint.invChart (𝕜 := ℂ)).symm) =ᶠ[nhdsWithin 0 {0}ᶜ]
      fun z : ℂ ↦ ((z - 0) ^ (-1 : ℤ)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := hz
    simp only [Function.comp_apply, OnePoint.invChart_symm_of_ne_zero hz', sub_zero, zpow_neg,
      zpow_one]
    exact finitePart_of_eq_coe (coordinate_apply _)
  rw [OnePoint.invChart_infty, _root_.meromorphicOrderAt_congr h]
  exact meromorphicOrderAt_zpow_id_sub_const

section Compact

variable [CompactSpace X] [ConnectedSpace X] [T2Space X]

omit [T2Space X] in
theorem coe_principalDivisor_apply {f : MeromorphicFunction X} (hf : f ≠ 0) (x : X) :
    ((principalDivisor X f x : ℤ) : WithTop ℤ) = order x f := by
  classical
  unfold principalDivisor
  rw [dif_neg hf]
  exact coe_coeff_principalDivisor_orderSystem (Additive.ofMul (Units.mk0 f hf)) x

omit [CompactSpace X] [T2Space X] in
/-- The order of a nonconstant meromorphic function is the order of the coordinate at its value times the
local multiplicity. -/
theorem order_eq_order_coordinate_mul {f : MeromorphicFunction X} (hne : ∃ x x', f x ≠ f x') (x : X) :
    order x f = order (f x) coordinate * (localMultiplicity (⇑f) x : WithTop ℤ) := by
  have h := meromorphicOrderAt_finitePart_comap (⇑f) f.mdifferentiable hne coordinate x
  have hc : comap (⇑f) f.mdifferentiable hne coordinate = f :=
    MeromorphicFunction.ext fun y ↦ by simp
  rw [hc] at h
  rw [order_apply, order_apply]
  exact h

omit [T2Space X] in
theorem principalDivisor_apply_zero {f : MeromorphicFunction X} (hne : ∃ x x', f x ≠ f x') (x : X)
    (hx : f x = ((0 : ℂ) : OnePoint ℂ)) :
    principalDivisor X f x = (localMultiplicity (⇑f) x : ℤ) := by
  have hf0 : f ≠ 0 := fun h ↦ by
    obtain ⟨y, y', hh⟩ := hne
    exact hh (by simp [h])
  have h := coe_principalDivisor_apply hf0 x
  rw [order_eq_order_coordinate_mul hne x, hx, order_coordinate_zero, one_mul] at h
  exact_mod_cast h

omit [T2Space X] in
theorem principalDivisor_apply_infty {f : MeromorphicFunction X} (hne : ∃ x x', f x ≠ f x') (x : X)
    (hx : f x = OnePoint.infty) :
    principalDivisor X f x = -(localMultiplicity (⇑f) x : ℤ) := by
  have hf0 : f ≠ 0 := fun h ↦ by
    obtain ⟨y, y', hh⟩ := hne
    exact hh (by simp [h])
  have h := coe_principalDivisor_apply hf0 x
  rw [order_eq_order_coordinate_mul hne x, hx, order_coordinate_infty] at h
  have h2 : (((principalDivisor X f x : ℤ)) : WithTop ℤ) =
      (((-(localMultiplicity (⇑f) x : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [h]
    have e1 : (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := rfl
    have e2 : ((localMultiplicity (⇑f) x : ℕ) : WithTop ℤ) =
        (((localMultiplicity (⇑f) x : ℕ) : ℤ) : WithTop ℤ) := rfl
    rw [e1, e2, ← WithTop.coe_mul, neg_one_mul]
  exact_mod_cast h2

omit [T2Space X] in
theorem principalDivisor_apply_eq_zero {f : MeromorphicFunction X} (hf0 : f ≠ 0) (x : X)
    (h0 : f x ≠ ((0 : ℂ) : OnePoint ℂ)) (hinf : f x ≠ OnePoint.infty) :
    principalDivisor X f x = 0 := by
  have h := coe_principalDivisor_apply hf0 x
  rw [order_eq_zero_iff.2 ⟨h0, hinf⟩] at h
  exact_mod_cast h

/-- **Milne, Proposition 1.12 (a).** A meromorphic function on a compact Riemann surface has as many zeros as poles,
counted with multiplicity: the degree of its divisor is `0`. -/
@[kb "milne2017mf" "Proposition 1.12 (a), pdf p. 19"]
theorem degree_principalDivisor (f : MeromorphicFunction X) :
    WeilDivisor.degree (principalDivisor X f) = 0 := by
  classical
  by_cases hf0 : f = 0
  · unfold principalDivisor
    rw [dif_pos hf0]
    exact WeilDivisor.degree_zero
  by_cases hne : ∃ x x', f x ≠ f x'
  swap
  · push_neg at hne
    have : principalDivisor X f = 0 := by
      ext x
      refine principalDivisor_apply_eq_zero hf0 x (fun h ↦ hf0 ?_) (fun h ↦ ?_)
      · refine MeromorphicFunction.ext fun y ↦ ?_
        rw [hne y x, h, coe_zero]
      · exact f.coe_ne_infty (funext fun y ↦ by rw [hne y x, h])
    rw [this]
    exact WeilDivisor.degree_zero
  let β : FiniteHolomorphicMap X (OnePoint ℂ) := .ofMDifferentiable f.mdifferentiable hne
  have hZ := β.finite_fiber ((0 : ℂ) : OnePoint ℂ)
  have hP := β.finite_fiber OnePoint.infty
  have hmemZ : ∀ x, x ∈ hZ.toFinset ↔ f x = ((0 : ℂ) : OnePoint ℂ) := fun x ↦ by
    simp [β]
  have hmemP : ∀ x, x ∈ hP.toFinset ↔ f x = OnePoint.infty := fun x ↦ by
    simp [β]
  have hsupp : (principalDivisor X f).support ⊆ hZ.toFinset ∪ hP.toFinset := by
    intro x hx
    rw [Finsupp.mem_support_iff] at hx
    rw [Finset.mem_union, hmemZ, hmemP]
    by_contra hcon
    push_neg at hcon
    exact hx (principalDivisor_apply_eq_zero hf0 x hcon.1 hcon.2)
  rw [WeilDivisor.degree_apply, Finset.sum_subset hsupp (fun x _ hx ↦ by
    simpa using hx), Finset.sum_union (Finset.disjoint_left.2 fun x h1 h2 ↦ by
      rw [hmemZ] at h1
      rw [hmemP] at h2
      exact OnePoint.coe_ne_infty 0 (h1.symm.trans h2))]
  have h1 : ∑ x ∈ hZ.toFinset, principalDivisor X f x = (degree β : ℤ) := by
    rw [degree_eq_fiber_sum β ((0 : ℂ) : OnePoint ℂ), Nat.cast_sum]
    exact Finset.sum_congr rfl fun x hx ↦ principalDivisor_apply_zero hne x ((hmemZ x).1 hx)
  have h2 : ∑ x ∈ hP.toFinset, principalDivisor X f x = -(degree β : ℤ) := by
    rw [degree_eq_fiber_sum β OnePoint.infty, Nat.cast_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x hx ↦ principalDivisor_apply_infty hne x ((hmemP x).1 hx)
  rw [h1, h2, add_neg_cancel]

/-! ### Corollary 1.13 and Proposition 1.16 -/

/-- A meromorphic function is **constant** if it takes only one value (as a map to the Riemann sphere). -/
def IsNonconstant (f : MeromorphicFunction X) : Prop := ∃ x x', f x ≠ f x'

/-- **Valence** of a meromorphic function on a compact Riemann surface (Milne, p. 19): the number of times it takes
each value, i.e. the degree of the map to the Riemann sphere (Tau Ceti's `TauCeti.RiemannSurface.degree`); `0` for a
constant function. -/
@[kb "milne2017mf" "§1, valence of a meromorphic function, pdf p. 19"]
noncomputable def valence (f : MeromorphicFunction X) : ℕ :=
  haveI := Classical.propDecidable
  if IsNonconstant f then degree (⇑f) else 0

/-- **Milne, Corollary 1.13.** A nonconstant meromorphic function `f` on a compact Riemann surface takes every value
`c` of the Riemann sphere exactly `n = valence f > 0` times, counted with multiplicity (the multiplicity being Tau
Ceti's `localMultiplicity`, the order of `f - c`, or of `1/f` at a pole). -/
@[kb "milne2017mf" "Corollary 1.13, pdf p. 19"]
theorem valence_pos_and_forall_fiber {f : MeromorphicFunction X} (hf : IsNonconstant f) :
    0 < valence f ∧ ∀ c : OnePoint ℂ, fiberMultiplicitySum (⇑f) c = valence f := by
  have hv : valence f = degree (⇑f) := by
    simp only [valence, if_pos hf]
  let β : FiniteHolomorphicMap X (OnePoint ℂ) := .ofMDifferentiable f.mdifferentiable hf
  refine ⟨?_, fun c ↦ ?_⟩
  · rw [hv]
    exact degree_pos β
  · rw [hv]
    exact fiberMultiplicitySum_eq_degree β.holomorphic β.not_eventuallyConst c

/-- The finite holomorphic map to the sphere defined by a nonconstant meromorphic function. -/
noncomputable def toFiniteHolomorphicMap (f : MeromorphicFunction X) (hf : IsNonconstant f) :
    FiniteHolomorphicMap X (OnePoint ℂ) :=
  .ofMDifferentiable f.mdifferentiable hf

/-- **Milne, Proposition 1.16.** If `f` is a nonconstant meromorphic function of valence `n` on a compact Riemann
surface, every meromorphic function `g` is a root of a (monic) polynomial of degree `≤ n` with coefficients in `ℂ(f)`,
the field of functions `r ∘ f`, `r` meromorphic on the sphere (Tau Ceti's `comapₐ`). Tau Ceti:
`TauCeti.RiemannSurface.MeromorphicFunction.exists_monic_natDegree_eq_degree_eval₂_eq_zero`. -/
@[kb "milne2017mf" "Proposition 1.16, pdf p. 20"]
theorem exists_monic_natDegree_le_valence {f : MeromorphicFunction X} (hf : IsNonconstant f)
    (g : MeromorphicFunction X) :
    ∃ p : Polynomial (MeromorphicFunction (OnePoint ℂ)), p.Monic ∧ p.natDegree ≤ valence f ∧
      p.eval₂ (comapₐ (toFiniteHolomorphicMap f hf) (toFiniteHolomorphicMap f hf).holomorphic
        (toFiniteHolomorphicMap f hf).nonconstant).toRingHom g = 0 := by
  obtain ⟨p, hp, hdeg, hpf⟩ :=
    exists_monic_natDegree_eq_degree_eval₂_eq_zero (toFiniteHolomorphicMap f hf) g
  refine ⟨p, hp, ?_, hpf⟩
  rw [hdeg]
  simp only [valence, if_pos hf]
  exact le_of_eq rfl

/-! ### Theorem 1.17 -/

/-- **Milne, Theorem 1.17** (first statement, the fundamental existence theorem; named statement): a compact Riemann
surface has a nonconstant meromorphic function. The book cites Gunning (it follows from Riemann–Roch). -/
@[kb "milne2017mf" "Theorem 1.17: existence of a nonconstant meromorphic function, pdf p. 20"]
structure ExistsNonconstantStatement (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    [ConnectedSpace X] : Prop where
  out : ∃ f : MeromorphicFunction X, IsNonconstant f

open IntermediateField in
/-- An algebraic extension of an infinite perfect field with uniformly bounded degrees is finite (primitive
element theorem applied to an element of maximal degree). -/
theorem finiteDimensional_of_bounded_minpoly (K E : Type*) [Field K] [Field E] [Algebra K E]
    [Infinite K] [PerfectField K] (n : ℕ) (hint : ∀ x : E, IsIntegral K x)
    (hn : ∀ x : E, (minpoly K x).natDegree ≤ n) : FiniteDimensional K E := by
  have : Algebra.IsAlgebraic K E := ⟨fun x ↦ (hint x).isAlgebraic⟩
  have : Algebra.IsSeparable K E := inferInstance
  have hbdd : BddAbove (Set.range fun x : E ↦ (minpoly K x).natDegree) := ⟨n, by
    rintro _ ⟨x, rfl⟩; exact hn x⟩
  obtain ⟨g, hg⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hmax : ∀ x : E, (minpoly K x).natDegree ≤ (minpoly K g).natDegree := fun x ↦ by
    have hg' : (minpoly K g).natDegree = sSup (Set.range fun x : E ↦ (minpoly K x).natDegree) := hg
    rw [hg']; exact le_csSup hbdd ⟨x, rfl⟩
  have htop : K⟮g⟯ = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨γ, hγ⟩ := Field.primitive_element_inf_aux K g h
    have hle : K⟮g⟯ ≤ K⟮γ⟯ := by
      rw [← hγ]
      exact adjoin.mono K _ _ (by simp)
    have hfin : FiniteDimensional K K⟮γ⟯ := adjoin.finiteDimensional (hint γ)
    have heq : K⟮g⟯ = K⟮γ⟯ := by
      refine eq_of_le_of_finrank_le hle ?_
      rw [adjoin.finrank (hint γ), adjoin.finrank (hint g)]
      exact hmax γ
    have : h ∈ K⟮γ⟯ := by
      rw [← hγ]
      exact subset_adjoin K _ (by simp)
    rwa [← heq] at this
  have : FiniteDimensional K (⊤ : IntermediateField K E) := by
    rw [← htop]; exact adjoin.finiteDimensional (hint g)
  exact Module.Finite.equiv (IntermediateField.topEquiv (F := K) (E := E)).toLinearEquiv

/-- **Milne, Theorem 1.17** (second statement, from the first): the meromorphic functions on a compact Riemann surface
form a finitely generated field of transcendence degree one over `ℂ` (an algebraic function field of one variable,
Tau Ceti's `TauCeti.IsFunctionField`). -/
@[kb "milne2017mf" "Theorem 1.17, pdf p. 20"]
theorem isFunctionField_of_exists_nonconstant (h : ExistsNonconstantStatement X) :
    TauCeti.IsFunctionField ℂ (MeromorphicFunction X) ∧
      (⊤ : IntermediateField ℂ (MeromorphicFunction X)).FG := by
  obtain ⟨f, hf⟩ := h.out
  let β := toFiniteHolomorphicMap f hf
  letI : Algebra (RatFunc ℂ) (MeromorphicFunction X) :=
    ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom.toAlgebra
  have hh : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
      ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom := rfl
  haveI : IsScalarTower ℂ (RatFunc ℂ) (MeromorphicFunction X) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [hh]
      exact ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).commutes x |>.symm
  haveI : FiniteDimensional (RatFunc ℂ) (MeromorphicFunction X) :=
    finiteDimensional_of_bounded_minpoly (RatFunc ℂ) (MeromorphicFunction X) (degree β)
      (fun g ↦ isIntegral_ratFunc β g hh) (fun g ↦ natDegree_minpoly_ratFunc_le β g hh)
  have hF : TauCeti.IsFunctionField ℂ (MeromorphicFunction X) :=
    TauCeti.isFunctionField_iff_functionField.mpr
      (‹FiniteDimensional (RatFunc ℂ) (MeromorphicFunction X)›)
  haveI := hF.essFiniteType
  exact ⟨hF, IntermediateField.fg_top ℂ _⟩

/-! ### Riemann–Roch consequences -/

/-- `L(0)` is the space of constant functions, so `ℓ(0) = 1` (Milne, proof of Corollary 1.21: "the only functions with
`div(f) ≥ 0` are the constant functions"). -/
@[kb "milne2017mf" "Corollary 1.21, proof: l(0) = 1, pdf p. 21"]
theorem ell_zero : ell X 0 = 1 := by
  have h : rrSpace X 0 = Submodule.span ℂ {(1 : MeromorphicFunction X)} := by
    apply le_antisymm
    · intro f hf
      have hf' : ∀ x, f x ≠ OnePoint.infty := fun x ↦ by
        rw [← order_nonneg_iff]
        simpa using hf x
      obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_forall_ne_infty hf'
      rw [Submodule.mem_span_singleton]
      exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      intro x
      simp
  unfold ell
  rw [h, finrank_span_singleton one_ne_zero]

/-- **Milne, Corollary 1.21.** If `g` is the integer of the Riemann–Roch theorem and `K = div(ω)` a canonical divisor,
then `deg K = 2g - 2` and `ℓ(K) = g`. -/
@[kb "milne2017mf" "Corollary 1.21, pdf p. 21"]
theorem degree_canonical_and_ell_canonical {g : ℕ}
    (hg : ∀ ω : MeromorphicDifferential X, ¬ ω.IsZero → ∀ D : WeilDivisor X,
      (ell X D : ℤ) = WeilDivisor.degree D + 1 - g + ell X (ω.divisor - D))
    {ω : MeromorphicDifferential X} (hω : ¬ ω.IsZero) :
    WeilDivisor.degree ω.divisor = 2 * g - 2 ∧ ell X ω.divisor = g := by
  have h0 := hg ω hω 0
  have h1 := hg ω hω ω.divisor
  rw [sub_zero, ell_zero, WeilDivisor.degree_zero] at h0
  rw [sub_self, ell_zero] at h1
  constructor <;> omega

/-- A divisor of negative degree has `ℓ(D) = 0` (Milne, before Corollary 1.22, using Proposition 1.12 (a)). -/
@[kb "milne2017mf" "§1, before Corollary 1.22: L(D) = 0 when deg D < 0, pdf p. 22"]
theorem ell_eq_zero_of_degree_neg {D : WeilDivisor X}
    (hD : WeilDivisor.degree D < 0) : ell X D = 0 := by
  have h : rrSpace X D = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    by_contra hf0
    have heff : 0 ≤ (D + principalDivisor X f) := by
      intro x
      have h1 := hf x
      rw [← coe_principalDivisor_apply hf0 x] at h1
      have h2 : -(D x) ≤ principalDivisor X f x := by exact_mod_cast h1
      show 0 ≤ (D + principalDivisor X f) x
      rw [Finsupp.add_apply]
      omega
    have h3 := WeilDivisor.degree_nonneg heff
    rw [WeilDivisor.degree_add, degree_principalDivisor] at h3
    omega
  unfold ell
  rw [h]
  simp

/-- **Milne, Corollary 1.22.** If `deg D > 2g - 2`, then `ℓ(D) = deg D + 1 - g`. -/
@[kb "milne2017mf" "Corollary 1.22, pdf p. 22"]
theorem ell_eq_of_degree_gt {g : ℕ}
    (hg : ∀ ω : MeromorphicDifferential X, ¬ ω.IsZero → ∀ D : WeilDivisor X,
      (ell X D : ℤ) = WeilDivisor.degree D + 1 - g + ell X (ω.divisor - D))
    (hω : ∃ ω : MeromorphicDifferential X, ¬ ω.IsZero) {D : WeilDivisor X}
    (hD : 2 * (g : ℤ) - 2 < WeilDivisor.degree D) :
    (ell X D : ℤ) = WeilDivisor.degree D + 1 - g := by
  obtain ⟨ω, hω'⟩ := hω
  have hK := (degree_canonical_and_ell_canonical hg hω').1
  have h1 := hg ω hω' D
  have h2 : ell X (ω.divisor - D) = 0 := by
    apply ell_eq_zero_of_degree_neg
    rw [WeilDivisor.degree_sub]
    omega
  rw [h2] at h1
  omega

end Compact

/-! ### Theorem 1.27 (Riemann–Hurwitz) -/

/-- **Milne, Theorem 1.27 (Riemann–Hurwitz formula)** (named statement): for a holomorphic map `f : Y → X` of compact
Riemann surfaces of degree `m` (`m : 1` off finitely many points),
`2g(Y) - 2 = m (2g(X) - 2) + ∑_P (e_P - 1)`, with `g` the genus (dimension of holomorphic differentials) and
`∑ (e_P - 1)` Tau Ceti's `ramificationDegree f`. The book proves it by pulling back a differential form and applying
Corollary 1.21. -/
@[kb "milne2017mf" "Theorem 1.27 (Riemann-Hurwitz), pdf p. 22"]
structure RiemannHurwitzStatement (Y X : Type*) [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    [CompactSpace Y] [ConnectedSpace Y] [T2Space Y] [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [ConnectedSpace X] [T2Space X] : Prop where
  out : ∀ f : FiniteHolomorphicMap Y X,
    2 * (genus Y : ℤ) - 2 = degree (⇑f) * (2 * (genus X : ℤ) - 2) + ramificationDegree f

end ModularFormsKB.Milne.RiemannSurface
