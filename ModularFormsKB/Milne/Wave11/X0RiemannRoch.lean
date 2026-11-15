import ModularFormsKB.Milne.Wave11.RiemannRochTransfer
import ModularFormsKB.Milne.Ch6.X0MinPoly
import ModularFormsKB.Milne.Wave10.ModularCurveJ
import ModularFormsKB.Milne.Wave10.RiemannRochInputs

/-!
# Riemann–Roch on `X₀(N)`, and Theorems 1.27, 2.22, 4.9 and Proposition 4.12 for `Γ₀(N)`

J. S. Milne, *Modular Functions and Modular Forms* (`milne2017mf`), Theorem 1.20 (pdf p. 21), Theorem 1.27 (p. 22),
Theorem 2.22 (p. 37), Theorem 4.9 (p. 51), Proposition 4.12 (p. 53), with the proof of Theorem 6.1 (p. 88).

The library proves, following Milne's proof of Theorem 6.1, that `j_N = j(Nz)` has degree `ψ(N) = (Γ(1) : Γ₀(N))`
over `ℂ(j)` in the field of meromorphic functions of `X₀(N)` (`LevelTwo.natDegree_minpoly_jNX`) and generates it
over `ℂ(j)` (`adjoin_eq_top`). Since `j : X₀(N) → ℙ¹` has degree `ψ(N)` (`degree_jXMap`), this is the field-degree
hypothesis of `riemannRoch_of_finrank_eq`, so Riemann–Roch holds on `X₀(N)` (`riemannRoch_X0`). The results of
earlier waves that were conditional on Riemann–Roch on `X(Γ)` become unconditional for `Γ = Γ₀(N)`:

* **`dimensionFormula_Gamma0`**: Theorem 4.9, the dimension of `M_{2k}(Γ₀(N))`;
* **`valenceFormula_Gamma0`**: Proposition 4.12, the valence formula on `X₀(N)`;
* **`genus_X0`**: Theorem 2.22, the genus of `X₀(N)`, `1 + ψ/12 - ν₂/4 - ν₃/3 - ν∞/2`;
* **`riemannHurwitz_X0`**: Theorem 1.27 for maps `X₀(N) → ℙ¹`.
-/

open TauCeti.RiemannSurface ModularFormsKB.Milne.RiemannSurface MeromorphicFunction CongruenceSubgroup
open scoped Manifold IntermediateField

noncomputable section

namespace ModularFormsKB.Milne.Wave11

variable (N : ℕ) [NeZero N]

theorem isNonconstant_jX : IsNonconstant (jX N) := by
  obtain ⟨a, b, hab⟩ := (jXMap N).nonconstant
  exact ⟨a, b, by simpa [coe_jXMap] using hab⟩

theorem valence_jX : valence (jX N) = (Gamma0 N).index := by
  rw [valence, if_pos (isNonconstant_jX N), ← coe_jXMap, degree_jXMap]

/-- **`[M(X₀(N)) : ℂ(j)] = ψ(N)`**, from Milne's proof of Theorem 6.1: `j_N` generates and has degree `ψ(N)`. -/
theorem finrank_jX : Module.finrank ℂ⟮jX N⟯ (MeromorphicFunction (X0 N)) = (Gamma0 N).index := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set K := ℂ⟮jX N⟯
  have hdeg := LevelTwo.natDegree_minpoly_jNX hN
  have hint : IsIntegral K (jNX N hN) := (natDegree_minpoly_le N (jNX N hN)).1
  have htop : K⟮jNX N hN⟯ = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : g ∈ IntermediateField.adjoin ℂ {jX N, jNX N hN} := by
      rw [adjoin_eq_top N (jNX N hN) hdeg]; trivial
    have hle : IntermediateField.adjoin ℂ {jX N, jNX N hN} ≤ (K⟮jNX N hN⟯).restrictScalars ℂ := by
      rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, IntermediateField.mem_adjoin_simple_self K _⟩
      have : jX N ∈ K := IntermediateField.mem_adjoin_simple_self ℂ _
      exact (K⟮jNX N hN⟯).algebraMap_mem ⟨jX N, this⟩
    exact hle hg
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint, hdeg]

/-- **Milne, Theorem 1.20 (Riemann–Roch) on `X₀(N)`.** -/
@[kb "milne2017mf" "Theorem 1.20 (Riemann-Roch), pdf p. 21, for X_0(N)"]
theorem riemannRoch_X0 : RiemannRochStatement (X0 N) :=
  riemannRoch_of_finrank_eq (isNonconstant_jX N) (by rw [finrank_jX, valence_jX])

/-- **Milne, Theorem 4.9 (the dimension formula) for `Γ₀(N)`**, unconditional. -/
@[kb "milne2017mf" "Section 4, Theorem 4.9 (pdf p. 51), for Gamma_0(N)"]
theorem dimensionFormula_Gamma0 : DimensionFormula (Gamma0 N) :=
  Wave10.dimensionFormula_of_riemannRoch' (Gamma0 N) (riemannRoch_X0 N)

/-- **Milne, Proposition 4.12 (the valence formula) for `Γ₀(N)`**, unconditional. -/
@[kb "milne2017mf" "Section 4, Proposition 4.12 (pdf p. 53), for Gamma_0(N)"]
theorem valenceFormula_Gamma0 : ValenceFormula (Gamma0 N) :=
  Wave10.valenceFormula_of_riemannRoch (Gamma0 N) (riemannRoch_X0 N)

/-- **Milne, Theorem 1.27 (Riemann–Hurwitz) for maps `X₀(N) → ℙ¹`**, unconditional. -/
@[kb "milne2017mf" "Theorem 1.27 (Riemann-Hurwitz), pdf p. 22, for X_0(N) -> P^1"]
theorem riemannHurwitz_X0 : RiemannHurwitzStatement (ModularCurveX (Gamma0 N)) (OnePoint ℂ) :=
  Wave10.riemannHurwitz_modularCurveX (Gamma0 N) (riemannRoch_X0 N)

/-- **Milne, Theorem 2.22 (the genus formula) for `X₀(N)`**, unconditional: the analytic genus (the dimension of
the holomorphic differentials) is `1 + ψ/12 - ν₂/4 - ν₃/3 - ν∞/2`. -/
@[kb "milne2017mf" "Theorem 2.22, pdf p. 37, for X_0(N)"]
theorem genus_X0 :
    (genus (ModularCurveX (Gamma0 N)) : ℚ) =
      1 + (genusIndex (Gamma0 N) : ℚ) / 12 - (nuTwo (Gamma0 N) : ℚ) / 4 - (nuThree (Gamma0 N) : ℚ) / 3 -
        (nuInfty (Gamma0 N) : ℚ) / 2 :=
  Wave10.genus_modularCurveX_of_riemannRoch (Gamma0 N) (riemannRoch_X0 N)

end ModularFormsKB.Milne.Wave11
