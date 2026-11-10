import ModularFormsKB.Milne.RS.DifferentialQuotient
import ModularFormsKB.Milne.RiemannSurface.Results

/-!
# Milne, Chapter 1: the canonical class

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), §1, pdf p. 21 (D035): for nonzero differential forms
`η`, `ω` on a compact Riemann surface, `η = (η/ω) ω` (`RS.diffQuot`), so `div(η) = div(η/ω) + div(ω)`
(`divisor_eq_principalDivisor_diffQuot_add`): the divisors of nonzero differential forms form one linear equivalence
class `𝔨`, the canonical class, and they all have the same degree (`degree_divisor_eq_of_not_isZero`).
-/

open Filter Topology Set
open scoped Manifold

namespace ModularFormsKB.Milne.RS

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]
  [CompactSpace X] [T2Space X]

/-- `ord_P(η) = ord_P(η/ω) + ord_P(ω)` for `ω ≠ 0`. -/
theorem ord_eq_order_diffQuot_add (η : MeromorphicDifferential X) {ω : MeromorphicDifferential X}
    (hω : ¬ ω.IsZero) (p : X) :
    η.ord p = order p (diffQuot η ω) + ω.ord p := by
  have hw : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have h1 := coeff_eventuallyEq_diffQuot_mul η hω p hw
  unfold MeromorphicDifferential.ord
  rw [_root_.meromorphicOrderAt_congr h1]
  have hF : _root_.MeromorphicAt ((diffQuot η ω).finitePart ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) :=
    meromorphicAt_comp_chart_symm (fun q ↦ (diffQuot η ω).meromorphicAt_finitePart q) p hw
  have hω' := ω.meromorphicAt p _ hw
  rw [show (fun v ↦ (diffQuot η ω).finitePart ((chartAt ℂ p).symm v) * ω.coeff p v) =
      ((diffQuot η ω).finitePart ∘ (chartAt ℂ p).symm) * ω.coeff p from rfl,
    _root_.meromorphicOrderAt_mul hF hω', meromorphicOrderAt_comp_chart_symm _ p hw,
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p), order_apply]

/-- For nonzero `η`, `ω`, the quotient `η/ω` is a nonzero meromorphic function. -/
theorem diffQuot_ne_zero {η ω : MeromorphicDifferential X} (hη : ¬ η.IsZero) (hω : ¬ ω.IsZero) :
    diffQuot η ω ≠ 0 := by
  intro h
  apply hη
  intro p
  rw [ord_eq_order_diffQuot_add η hω p, h, AddValuation.map_zero, top_add]

/-- **The canonical class** (Milne, p. 21): for nonzero differential forms `η`, `ω` on a compact Riemann surface,
`div(η) = div(η/ω) + div(ω)`; the divisors of nonzero differential forms are linearly equivalent. -/
@[kb "milne2017mf" "§1, the canonical class: div(eta) = div(eta/omega) + div(omega), pdf p. 21"]
theorem divisor_eq_principalDivisor_diffQuot_add {η ω : MeromorphicDifferential X} (hη : ¬ η.IsZero)
    (hω : ¬ ω.IsZero) :
    η.divisor = principalDivisor X (diffQuot η ω) + ω.divisor := by
  refine Finsupp.ext fun p ↦ ?_
  rw [Finsupp.add_apply, divisor_apply hη, divisor_apply hω]
  have h := ord_eq_order_diffQuot_add η hω p
  rw [← coe_ordZ hη, ← coe_ordZ hω, ← coe_principalDivisor_apply (diffQuot_ne_zero hη hω) p] at h
  exact_mod_cast h

/-- All canonical divisors have the same degree. -/
theorem degree_divisor_eq_of_not_isZero {η ω : MeromorphicDifferential X} (hη : ¬ η.IsZero)
    (hω : ¬ ω.IsZero) :
    WeilDivisor.degree η.divisor = WeilDivisor.degree ω.divisor := by
  rw [divisor_eq_principalDivisor_diffQuot_add hη hω, map_add, degree_principalDivisor, zero_add]

end ModularFormsKB.Milne.RS
