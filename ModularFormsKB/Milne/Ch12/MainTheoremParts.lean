import ModularFormsKB.Milne.Ch12.MainTheorem
import ModularFormsKB.Milne.Ch12.CMBaseChange
import ModularFormsKB.Citation
/-!
# Milne, Theorem 12.18: the parts that are proved

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, Thm. 12.18 (pdf p. 126).

`MainTheoremCM` stays a named statement (its clauses (a), the transitivity in (b), and (c) need the reduction theory
of curves with complex multiplication: the reduction of the $\mathfrak p$-isogeny $E \to \mathfrak p^{-1} * E$ modulo
a prime above $\mathfrak p$ is the Frobenius, Milne's Proposition 12.24 / Silverman, *Advanced Topics*, II.4.4
[unverified]). The stability clause of (b) holds for every automorphism of $\mathbb C$, not only those over $K$,
because $\mathrm{Ell}(R)$ is $\mathrm{Aut}(\mathbb C)$-stable (`j_map_mem_ellCM`).
-/

open NumberField TauCeti TauCeti.GlobalNumberFields

namespace ModularFormsKB.Milne

/-- **Theorem 12.18 (b), stability** (Milne): an automorphism of $\mathbb C$ over $K$ maps $\mathrm{Ell}(\mathcal O_K)$
to itself. -/
@[kb "milne2017mf" "Section 12, Thm. 12.18 (b), stability (pdf p. 126)"]
theorem mainTheoremCM_stable (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (_ : Module.finrank ℚ K = 2)
    (_ : IsTotallyComplex K) (τ : ℂ ≃+* ℂ) (_ : IsAutOver ι τ) (x : ℂ)
    (hx : x ∈ EllCM (maximalNumberFieldOrder K)) : τ x ∈ EllCM (maximalNumberFieldOrder K) :=
  j_map_mem_ellCM τ hx

end ModularFormsKB.Milne
