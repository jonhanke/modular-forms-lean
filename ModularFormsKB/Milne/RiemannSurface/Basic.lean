import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
import ModularFormsKB.Citation
/-!
# Milne, Chapter 1: differential forms, divisors and the Riemann–Roch space

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, pdf pp. 17–22.

A Riemann surface is a type `X` with `[TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]`, plus
`[ConnectedSpace X] [T2Space X]` where needed (complex differentiability of the transition maps makes them
holomorphic; Milne's "nowhere vanishing derivative" is automatic for holomorphic bijections). Meromorphic functions
are Tau Ceti's field `TauCeti.RiemannSurface.MeromorphicFunction X` (holomorphic maps to the Riemann sphere, as Milne
notes on p. 18), with the order valuations `TauCeti.RiemannSurface.MeromorphicFunction.order x`; divisors are Tau
Ceti's `TauCeti.AlgebraicGeometry.WeilDivisor X = X →₀ ℤ` with its `degree`; principal divisors come from Tau Ceti's
`orderSystem`.

New here (not in Mathlib or Tau Ceti):
* `MeromorphicDifferential X`: Milne's "naive" differential forms (p. 18): a family of coefficients `f_x` in the
  coordinate covering by the charts `chartAt ℂ x`, meromorphic on the chart targets, agreeing on overlaps in the sense
  `f_x(v) = f_y(w(v)) w'(v)`, `w = z_y ∘ z_x⁻¹`. As for functions in Mathlib, the coefficients may take arbitrary
  values at poles, so the overlap condition is required on punctured neighbourhoods.
* the order, residue, the three kinds, and the divisor of a differential form (pp. 18, 21);
* the space `holomorphicDifferentials X` of holomorphic differential forms and `genus X`, its dimension (p. 22);
* the Riemann–Roch space `rrSpace D = L(D)` and `ell D = ℓ(D)` (p. 21);
* the named statements `ResidueTheoremStatement` (Proposition 1.12 (b)) and `RiemannRochStatement` (Theorem 1.20).
-/

open Filter Topology Set
open scoped Manifold

namespace ModularFormsKB.Milne.RiemannSurface

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry

section Differentials

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The transition map `w = z_y ∘ z_x⁻¹` from the chart at `x` to the chart at `y`. -/
noncomputable def transition {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x y : X) : ℂ → ℂ :=
  fun v ↦ chartAt ℂ y ((chartAt ℂ x).symm v)

/-- **Meromorphic differential form on a Riemann surface** (Milne, p. 18): for the coordinate covering by the charts
`z_x = chartAt ℂ x`, a differential form `f_x(z_x) dz_x` on each chart target, with `f_x` meromorphic there, such that
on overlaps `f_x(v) dz_x = f_y(w(v)) w'(v) dz_x`, `w = z_y ∘ z_x⁻¹` (equality off the poles, i.e. on punctured
neighbourhoods). -/
@[kb "milne2017mf" "§1, differential forms on a Riemann surface, pdf p. 18"]
structure MeromorphicDifferential where
  /-- The coefficient `f_x` of the form in the chart `chartAt ℂ x`. -/
  coeff : X → ℂ → ℂ
  meromorphicAt : ∀ x : X, ∀ w ∈ (chartAt ℂ x).target, _root_.MeromorphicAt (coeff x) w
  compat : ∀ x y : X, ∀ w ∈ (chartAt ℂ x).target, (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source →
    coeff x =ᶠ[𝓝[≠] w] fun v ↦ coeff y (transition x y v) * deriv (transition x y) v

namespace MeromorphicDifferential

variable {X}

/-- The order `ord_P(ω)` of a differential form at `P` (Milne, p. 21): the order of its coefficient in the chart
at `P`. -/
@[kb "milne2017mf" "§1, order of a differential form, pdf p. 21"]
noncomputable def ord (ω : MeromorphicDifferential X) (x : X) : WithTop ℤ :=
  _root_.meromorphicOrderAt (ω.coeff x) (chartAt ℂ x x)

/-- The residue `Res_P(ω)` of a differential form at `P` (Milne, p. 18): the residue of its coefficient in the chart
at `P` (Tau Ceti's `TauCeti.Contour.residue`). -/
@[kb "milne2017mf" "§1, residue of a differential form, pdf p. 18"]
noncomputable def res (ω : MeromorphicDifferential X) (x : X) : ℂ :=
  TauCeti.Contour.residue (ω.coeff x) (chartAt ℂ x x)

/-- The zero differential form: its coefficients vanish near every point (order `⊤` everywhere). -/
def IsZero (ω : MeromorphicDifferential X) : Prop := ∀ x, ω.ord x = ⊤

/-- **First kind** (holomorphic) differential form (Milne, p. 18): no poles. -/
@[kb "milne2017mf" "§1, differential form of the first kind, pdf p. 18"]
def IsFirstKind (ω : MeromorphicDifferential X) : Prop := ∀ x, 0 ≤ ω.ord x

/-- **Second kind** differential form (Milne, p. 18): residue `0` at each pole. -/
@[kb "milne2017mf" "§1, differential form of the second kind, pdf p. 18"]
def IsSecondKind (ω : MeromorphicDifferential X) : Prop := ∀ x, ω.ord x < 0 → ω.res x = 0

/-- **Third kind** differential form (Milne, p. 18): not of the second kind. -/
@[kb "milne2017mf" "§1, differential form of the third kind, pdf p. 18"]
def IsThirdKind (ω : MeromorphicDifferential X) : Prop := ¬ ω.IsSecondKind

/-- The order as an integer (`0` where the order is `⊤`). -/
noncomputable def ordZ (ω : MeromorphicDifferential X) (x : X) : ℤ := (ω.ord x).untop₀

/-- **The divisor of a differential form** (Milne, p. 21): `div(ω) = ∑ ord_P(ω) P`. The sum is finite for a nonzero
form on a compact Riemann surface (`MeromorphicDifferential.finite_support_ordZ`); the definition returns `0` if the
support is infinite. -/
@[kb "milne2017mf" "§1, divisor of a differential form, pdf p. 21"]
noncomputable def divisor (ω : MeromorphicDifferential X) : WeilDivisor X :=
  haveI := Classical.propDecidable
  if h : (Function.support ω.ordZ).Finite then Finsupp.ofSupportFinite ω.ordZ h else 0

end MeromorphicDifferential

/-- **Holomorphic differential forms** (Milne, pp. 18, 22): families of coefficients `f_x`, holomorphic on the chart
targets (and set to `0` outside them), with `f_x(v) = f_y(w(v)) w'(v)` on overlaps. A ℂ-vector space. -/
@[kb "milne2017mf" "§1, the space of holomorphic differential forms, pdf p. 22"]
def holomorphicDifferentials : Submodule ℂ (X → ℂ → ℂ) where
  carrier := {c | (∀ x w, w ∉ (chartAt ℂ x).target → c x w = 0) ∧
    (∀ x, DifferentiableOn ℂ (c x) (chartAt ℂ x).target) ∧
    ∀ x y : X, ∀ w ∈ (chartAt ℂ x).target, (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source →
      c x w = c y (transition x y w) * deriv (transition x y) w}
  add_mem' := by
    rintro c d ⟨hc0, hc1, hc2⟩ ⟨hd0, hd1, hd2⟩
    refine ⟨fun x w hw ↦ ?_, fun x ↦ (hc1 x).add (hd1 x), fun x y w hw hwy ↦ ?_⟩
    · simp [hc0 x w hw, hd0 x w hw]
    · simp only [Pi.add_apply]
      rw [hc2 x y w hw hwy, hd2 x y w hw hwy]
      ring
  zero_mem' := ⟨fun _ _ _ ↦ rfl, fun _ ↦ differentiableOn_const 0, fun _ _ _ _ _ ↦ by simp⟩
  smul_mem' := by
    rintro a c ⟨hc0, hc1, hc2⟩
    refine ⟨fun x w hw ↦ ?_, fun x ↦ (hc1 x).const_smul a, fun x y w hw hwy ↦ ?_⟩
    · simp [hc0 x w hw]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hc2 x y w hw hwy]
      ring

/-- **The genus** of a compact Riemann surface: the dimension of the space of holomorphic differential forms
(Milne, p. 22: "the space of holomorphic differential forms on `X` ... has dimension `g`", Corollary 1.21). -/
@[kb "milne2017mf" "§1, the genus as dimension of holomorphic differentials, pdf p. 22"]
noncomputable def genus : ℕ := Module.finrank ℂ (holomorphicDifferentials X)

end Differentials

section RiemannRoch

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

open MeromorphicFunction

/-- **The Riemann–Roch space** `L(D) = {f ∈ M(X) | div(f) + D ≥ 0} ∪ {0}` (Milne, p. 21), as a ℂ-subspace of the
field of meromorphic functions: `ord_x(f) ≥ -D(x)` for every `x` (the zero function has order `⊤`). -/
@[kb "milne2017mf" "§1, the space L(D), pdf p. 21"]
def rrSpace (D : WeilDivisor X) : Submodule ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ order x f}
  add_mem' := by
    intro f g hf hg x
    exact le_trans (le_min (hf x) (hg x)) ((order x).map_add f g)
  zero_mem' := by
    intro x
    simp
  smul_mem' := by
    intro c f hf x
    rw [Algebra.smul_def, (order x).map_mul]
    by_cases hc : c = 0
    · simp [hc]
    · rw [order_algebraMap hc, zero_add]
      exact hf x

/-- `ℓ(D) = dim L(D)` (Milne, p. 21). -/
@[kb "milne2017mf" "§1, l(D) = dim L(D), pdf p. 21"]
noncomputable def ell (D : WeilDivisor X) : ℕ := Module.finrank ℂ (rrSpace X D)

variable [CompactSpace X]

/-- **The divisor of a meromorphic function** (Milne, p. 20): `div(f) = ∑ ord_P(f) P` for `f ≠ 0` (Tau Ceti's
principal divisor of the order system); `div(0) = 0` by convention. -/
@[kb "milne2017mf" "§1, divisor of a meromorphic function, pdf p. 20"]
noncomputable def principalDivisor (f : MeromorphicFunction X) : WeilDivisor X :=
  haveI := Classical.propDecidable
  if hf : f = 0 then 0 else (orderSystem X).principalDivisor (Additive.ofMul (Units.mk0 f hf))

variable [T2Space X]

/-- **Milne, Proposition 1.12 (b)** (named statement): on a compact Riemann surface the residues of a differential
form sum to zero. The book sketches a proof by triangulation and the residue theorem. -/
@[kb "milne2017mf" "Proposition 1.12 (b), pdf p. 19"]
structure ResidueTheoremStatement : Prop where
  out : ∀ ω : MeromorphicDifferential X, ∑ᶠ x, ω.res x = 0

/-- **Milne, Theorem 1.20 (Riemann–Roch)** (named statement): on a compact Riemann surface `X` the spaces `L(D)` are
finite-dimensional, and there is an integer `g ≥ 0` such that for every nonzero differential form `ω` (with
canonical divisor `K = div(ω)`) and every divisor `D`, `ℓ(D) = deg(D) + 1 - g + ℓ(K - D)`. The book refers to
Gunning for the proof. -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21"]
structure RiemannRochStatement : Prop where
  finiteDimensional : ∀ D : WeilDivisor X, FiniteDimensional ℂ (rrSpace X D)
  exists_genus : ∃ g : ℕ, ∀ ω : MeromorphicDifferential X, ¬ ω.IsZero → ∀ D : WeilDivisor X,
    (ell X D : ℤ) = WeilDivisor.degree D + 1 - g + ell X (ω.divisor - D)

end RiemannRoch

end ModularFormsKB.Milne.RiemannSurface
