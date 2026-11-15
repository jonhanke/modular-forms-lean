import ModularFormsKB.Milne.Wave15.Corollaries
import ModularFormsKB.Milne.Wave11.Bijection

/-!
# Milne, Theorem 0.5 (a) and (b) on every compact Riemann surface

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 0.5 (pdf p. 9), in the function-field form
of the library's named statement `CompactRiemannSurfaceAlgebraicStatement`:

* (a) `M(X)` is an algebraic function field of one variable over `ℂ` (`Wave15.isFunctionField`);
* (b) the points of `X` correspond bijectively to the places of `M(X)/ℂ`, `x ↦ P_x` with `v_{P_x} = exp(-ord_x)`
  (`places`).

Proof of (b): the separation of points (`Wave15.separates`) gives `[M(X) : ℂ(f)] = deg f` for a nonconstant `f`
(Tau Ceti), so the library's points-places bijection (`Wave11.pointPlace_bijective`, `Wave11.ordAt_eq_ord_pointPlace`)
applies. Part (c) (isomorphic function fields give isomorphic surfaces) is not proved here.
-/

open TauCeti TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface MeromorphicFunction
open scoped Manifold

universe u

noncomputable section

namespace ModularFormsKB.Milne.Wave15

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [ConnectedSpace X] [T2Space X]

/-- **Milne, Theorem 0.5 (b)** on every compact Riemann surface: every point `x` defines a place `P_x` of `M(X)/ℂ`
with valuation `exp(-ord_x)`, and every place is `P_x` for exactly one `x`. -/
@[kb "milne2017mf" "Theorem 0.5 (b): points and places, pdf p. 9"]
theorem places :
    (∀ x : X, ∃ P : Place ℂ (MeromorphicFunction X), ∀ f, f ≠ 0 →
      P.valuation f = WithZero.exp (-(order x f).untop₀)) ∧
    ∀ P : Place ℂ (MeromorphicFunction X), ∃! x : X, ∀ f, f ≠ 0 →
      P.valuation f = WithZero.exp (-(order x f).untop₀) := by
  obtain ⟨f, hf⟩ := (existsNonconstantStatement (X := X)).out
  have hF := (isFunctionField (X := X)).1
  have hx := Wave11.transcendental_of_isNonconstant hf
  let _ := ratFuncAlgebraOfTranscendental hx
  have _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  have hX : algebraMap (RatFunc ℂ) (MeromorphicFunction X) RatFunc.X = f :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hx
  obtain ⟨c, hc⟩ := ((toFiniteHolomorphicMap f hf).finite_branchValues.infinite_compl).nonempty
  have hdeg := finrank_ratFunc_eq_degree_of_pairwise_separated_fiber (toFiniteHolomorphicMap f hf)
    (Wave11.algebraMap_eq_comap hf hX) hc fun x _ y _ hxy ↦ separates x y hxy
  have _ : FiniteDimensional (RatFunc ℂ) (MeromorphicFunction X) :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact degree_pos _)
  have key : ∀ (x : X) (g : MeromorphicFunction X), g ≠ 0 →
      (Wave11.pointPlace hF hf x).valuation g = WithZero.exp (-(order x g).untop₀) := fun x g hg ↦ by
    rw [Place.valuation_eq_exp_neg_ord _ hg, ← Wave11.ordAt_eq_ord_pointPlace hF hf hX hdeg x g hg]
    rfl
  refine ⟨fun x ↦ ⟨_, key x⟩, fun P ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (Wave11.pointPlace_bijective hF hf hX hdeg).2 P
  refine ⟨x, key x, fun y hy ↦ ?_⟩
  by_contra hyx
  -- a function with a pole at `x` only has negative order at `x` and nonnegative order at `y`
  obtain ⟨g, hgx, hgy⟩ := exists_pole_only_at x
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hgy y hyx (by simp at hgx)
  have h1 := (key x g hg0).symm.trans (hy g hg0)
  have h2 : (order x g).untop₀ = (order y g).untop₀ := by
    simpa using WithZero.exp_injective h1
  have hxneg : order x g < 0 := order_neg_iff.2 hgx
  have hynn : 0 ≤ order y g := order_nonneg_iff.2 (hgy y hyx)
  have hxne : order x g ≠ ⊤ := ne_top_of_lt hxneg
  have hyne : order y g ≠ ⊤ := by
    intro h
    exact hg0 ((AddValuation.top_iff _).1 h)
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hxne
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hyne
  rw [← ha, ← hb, WithTop.untop₀_coe, WithTop.untop₀_coe] at h2
  rw [← ha] at hxneg
  rw [← hb] at hynn
  subst h2
  exact absurd (WithTop.coe_lt_coe.1 hxneg) (not_lt.2 (WithTop.coe_le_coe.1 hynn))

end ModularFormsKB.Milne.Wave15
