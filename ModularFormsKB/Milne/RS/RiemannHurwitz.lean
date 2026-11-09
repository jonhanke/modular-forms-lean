import ModularFormsKB.Milne.RS.HurwitzOrder
import ModularFormsKB.Milne.RS.CanonicalGenus

/-!
# Milne, Theorem 1.27 (Riemann–Hurwitz) from the Riemann–Roch theorem

Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.27, pdf p. 22.

Milne's proof: pull a nonzero differential `ω` on `X` back to `Y` along `f`; then `div(f^*ω) = f^* div(ω) + R_f`, so
`deg div(f^*ω) = m deg div(ω) + ∑ (e_P - 1)`, and `deg div(ω) = 2g - 2` on both surfaces (Corollary 1.21).

Here `ω = dh` for a nonconstant meromorphic function `h` on `X` (Theorem 1.17), `f^*ω = d(h ∘ f)`
(`RS.divisor_differential_pullbackFun`), the degree of the divisor of a nonzero differential is `2g - 2` with `g` the
integer of the Riemann–Roch theorem (`RiemannSurface.degree_canonical_and_ell_canonical`), and this integer is the
genus, the dimension of the holomorphic differentials (`RS.ell_divisor_eq_genus`).

Main result: `riemannHurwitzStatement_of_riemannRoch`, the named statement `RiemannHurwitzStatement Y X` from
`RiemannRochStatement` for `Y` and `X` and `ExistsNonconstantStatement X` (Milne's Theorem 1.17 for the compact
Hausdorff surface `X`).
-/

open TauCeti.RiemannSurface TauCeti.AlgebraicGeometry MeromorphicFunction ModularFormsKB.Milne.RiemannSurface
open scoped Manifold

namespace ModularFormsKB.Milne.RS

variable {Y X : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [CompactSpace Y]
  [ConnectedSpace Y] [T2Space Y] [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [ConnectedSpace X] [T2Space X]

/-- The degree of the divisor of a nonzero differential is `2 g - 2`, `g` the genus, given the Riemann–Roch
theorem. -/
theorem degree_divisor_eq_two_mul_genus_sub_two (hRR : RiemannRochStatement X) {ω : MeromorphicDifferential X}
    (hω : ¬ ω.IsZero) : WeilDivisor.degree ω.divisor = 2 * (genus X : ℤ) - 2 := by
  obtain ⟨g, hg⟩ := hRR.exists_genus
  have h := degree_canonical_and_ell_canonical hg hω
  have e : genus X = g := (ell_divisor_eq_genus hω).symm.trans h.2
  rw [e, h.1]

/-- **Milne, Theorem 1.27 (Riemann–Hurwitz)**, from the Riemann–Roch theorem on `Y` and `X` and the existence of a
nonconstant meromorphic function on `X`. -/
@[kb "milne2017mf" "Theorem 1.27 (Riemann-Hurwitz), pdf p. 22, from Theorems 1.17 and 1.20"]
theorem riemannHurwitzStatement_of_riemannRoch (hY : RiemannRochStatement Y) (hX : RiemannRochStatement X)
    (hN : ExistsNonconstantStatement X) : RiemannHurwitzStatement Y X := by
  refine ⟨fun f ↦ ?_⟩
  obtain ⟨h, hh⟩ := hN.out
  have hω := differential_not_isZero hh
  have hωY := differential_not_isZero (isNonconstant_pullbackFun f hh)
  have hdeg := congrArg WeilDivisor.degree (divisor_differential_pullbackFun f hh)
  rw [map_add, degree_divisorPullback, degree_ramificationDivisor,
    degree_divisor_eq_two_mul_genus_sub_two hY hωY, degree_divisor_eq_two_mul_genus_sub_two hX hω] at hdeg
  exact hdeg

end ModularFormsKB.Milne.RS
