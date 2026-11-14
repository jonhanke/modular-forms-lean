import ModularFormsKB.Milne.Wave9.PuncturedSphere
import ModularFormsKB.Milne.Wave4A.GenusGammaN
import ModularFormsKB.Citation
/-!
# Milne, Example 2.23: the genus of `X(N)` in topological form, unconditional

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Example 2.23 (pdf p. 38).

Wave 4A proved the genus formula `g(X(N)) = 1 + μ_N (N - 6) / (12 N)` (`N ≥ 2`) for the analytic genus, conditional on
the Riemann–Hurwitz formula (`genus_modularCurveX_Gamma`). Wave 9 made Theorem 2.22 unconditional in punctured
Euler-characteristic form (`Wave9.eulerChar_puncture_modularCurveX'`). Specialized to `Γ = Γ(N)` with the right side
computed in wave 4A (`genusFormula_Gamma`), this gives Example 2.23 in the same topological form: with `F ⊆ X(N)` the
preimage of the branch values of `j : X(N) → ℙ¹`, `χ(X(N) ∖ F) + #F = 2 - 2 (1 + μ_N (N - 6) / (12 N))`.
-/

open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Milne.Wave10

open TauCeti TauCeti.RiemannSurface CongruenceSubgroup

/-- **Milne, Example 2.23, topological form (punctured), unconditional.** For `N ≥ 2`, with `F ⊆ X(N)` the preimage of
the branch values of `j`, `χ(X(N) ∖ F) + #F = 2 - 2 g` with `g = 1 + μ_N (N - 6) / (12 N)` and `μ_N` the index of
`±Γ(N)` in `SL₂(ℤ)`. -/
@[kb "milne2017mf" "Example 2.23: the genus of X(N), Euler characteristic form, pdf p. 38"]
theorem eulerChar_puncture_modularCurveX_Gamma {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    haveI := Wave9.puncturedSphereFiniteCWType.out _ (modularCurveXJ (Gamma N)).finite_branchValues
    haveI := (modularCurveXJ (Gamma N)).finiteCWType_compl_preimage
      (S := (modularCurveXJ (Gamma N)).branchValues) subset_rfl
    ((eulerChar ↥((modularCurveXJ (Gamma N)) ⁻¹' (modularCurveXJ (Gamma N)).branchValues)ᶜ : ℤ) : ℚ) +
        ((modularCurveXJ (Gamma N)) ⁻¹' (modularCurveXJ (Gamma N)).branchValues).ncard =
      2 - 2 * (1 + ((Miyake.adjoinNegOne (Gamma N)).index : ℚ) * (N - 6) / (12 * N)) := by
  rw [← genusFormula_Gamma hN]
  exact Wave9.eulerChar_puncture_modularCurveX' (Gamma N)

end ModularFormsKB.Milne.Wave10
