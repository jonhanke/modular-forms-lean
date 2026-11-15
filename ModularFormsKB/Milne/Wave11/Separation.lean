import ModularFormsKB.Milne.Wave11.RiemannRochTransfer
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Generator

/-!
# Riemann–Roch from the separation of points

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorems 1.17 and 1.20 (pdf pp. 20–21).

The existence theorem for compact Riemann surfaces is often stated as: the meromorphic functions separate points
(Forster, *Lectures on Riemann Surfaces*, Corollary 14.13). From it, with one nonconstant function `f`, the points of
an unbranched fibre of `f` are separated, so `[M(X) : ℂ(f)] = valence f` (Tau Ceti
`TauCeti.RiemannSurface.MeromorphicFunction.finrank_ratFunc_eq_degree_of_pairwise_separated_fiber`), and
`riemannRoch_of_finrank_eq` gives Riemann–Roch (`riemannRoch_of_separates`). It suffices that the points of one
unbranched fibre of one nonconstant function be separated (`riemannRoch_of_separated_fiber`).
-/

open TauCeti TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface MeromorphicFunction
open scoped Manifold IntermediateField

noncomputable section

namespace ModularFormsKB.Milne.Wave11

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]

/-- **Riemann–Roch when one unbranched fibre of a nonconstant function is separated.** -/
theorem riemannRoch_of_separated_fiber {f : MeromorphicFunction X} (hf : IsNonconstant f) {c : OnePoint ℂ}
    (hc : c ∉ (toFiniteHolomorphicMap f hf).branchValues)
    (hsep : ((toFiniteHolomorphicMap f hf) ⁻¹' {c}).Pairwise fun x x' ↦ ∃ g : MeromorphicFunction X, g x ≠ g x') :
    RiemannRochStatement X := by
  have hF := (isFunctionField_of_exists_nonconstant ⟨⟨f, hf⟩⟩).1
  have hx := transcendental_of_isNonconstant hf
  letI := ratFuncAlgebraOfTranscendental hx
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hx
  have hX : algebraMap (RatFunc ℂ) (MeromorphicFunction X) RatFunc.X = f :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hx
  have h := finrank_ratFunc_eq_degree_of_pairwise_separated_fiber (toFiniteHolomorphicMap f hf)
    (algebraMap_eq_comap hf hX) hc hsep
  refine riemannRoch_of_finrank_eq hf ?_
  have hv : valence f = degree (toFiniteHolomorphicMap f hf) := by
    simp only [valence, if_pos hf]; rfl
  rw [hv, ← h]
  refine (Algebra.finrank_eq_of_equiv_equiv (RatFunc.algEquivOfTranscendental f hx).toRingEquiv
    (RingEquiv.refl _) ?_).symm
  ext r
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_ratFuncAlgebraOfTranscendental_apply]
  rfl

/-- **Milne, Theorem 1.20 (Riemann–Roch) from the existence theorem**: on a compact connected Riemann surface with a
nonconstant meromorphic function, if the meromorphic functions separate points, Riemann–Roch holds. -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, from the separation of points"]
theorem riemannRoch_of_separates (hne : ExistsNonconstantStatement X)
    (hsep : ∀ x y : X, x ≠ y → ∃ g : MeromorphicFunction X, g x ≠ g y) : RiemannRochStatement X := by
  obtain ⟨f, hf⟩ := hne.out
  obtain ⟨c, hc⟩ := ((toFiniteHolomorphicMap f hf).finite_branchValues.infinite_compl).nonempty
  exact riemannRoch_of_separated_fiber hf hc fun x _ y _ hxy ↦ hsep x y hxy

end ModularFormsKB.Milne.Wave11
