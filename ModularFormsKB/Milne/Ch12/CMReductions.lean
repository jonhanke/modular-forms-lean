import ModularFormsKB.Milne.Ch12.ComplexMultiplication
import ModularFormsKB.Milne.Ch12.MainTheorem
import ModularFormsKB.Citation
/-!
# Milne, Section 12: reductions between the named statements

J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (`milne2017mf`), Section 12, pdf pp. 125–128.

## Items

- `CMJIntegral` (**Corollary 12.15** as a named statement): an elliptic curve over a number field $k$ with complex
  multiplication over $k$ has integral $j$-invariant.
- `cmPotentialGoodReduction_iff_cmJIntegral`: **Theorem 12.14 is equivalent to Corollary 12.15.** Milne derives 12.15
  from 12.14 (`isIntegral_j_of_hasCMBy`); conversely an elliptic curve with integral $j$ has potential good reduction
  at every prime (Silverman VII.5.5, Tau Ceti `WeierstrassCurve.hasPotentialGoodReduction_of_isInteger_j`). So the
  only missing input for 12.14 is the integrality of $j$ (Silverman, *Advanced Topics*, II.6.1).
- `frobeniusClassLemma_of_mainTheoremCM`: Lemma 12.25 is the special case $T = \emptyset$ of Theorem 12.18(c).
-/

open NumberField TauCeti TauCeti.GlobalNumberFields

namespace ModularFormsKB.Milne

/-- **Corollary 12.15** (Milne; Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, II.6.1
[unverified]), as a named statement: an elliptic curve over a number field $k$ with complex multiplication by an order
$R$ over $k$ has $j(E)$ an algebraic integer. -/
@[kb "milne2017mf" "Section 12, Cor. 12.15 (pdf p. 125)"]
structure CMJIntegral : Prop where
  isIntegral : ∀ (k : Type) [Field k] [NumberField k] (W : WeierstrassCurve k) [W.IsElliptic]
    (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K), HasCMBy W O → IsIntegral ℤ W.j

/-- An algebraic integer of a number field is integral at every prime. -/
theorem isInteger_localization_of_isIntegral {k : Type} [Field k] [NumberField k] {x : k} (hx : IsIntegral ℤ x)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 k)) :
    IsLocalization.IsInteger (Localization.AtPrime v.asIdeal) x := by
  refine ⟨algebraMap (𝓞 k) (Localization.AtPrime v.asIdeal) ⟨x, (mem_integralClosure_iff ℤ k).mpr hx⟩, ?_⟩
  exact (IsScalarTower.algebraMap_apply (𝓞 k) (Localization.AtPrime v.asIdeal) k _).symm

/-- **Theorem 12.14 is equivalent to Corollary 12.15.** -/
@[kb "milne2017mf" "Section 12, Thm. 12.14 and Cor. 12.15 (pdf p. 125)"]
theorem cmPotentialGoodReduction_iff_cmJIntegral : CMPotentialGoodReduction ↔ CMJIntegral := by
  constructor
  · intro h
    exact ⟨fun k _ _ W _ K _ _ O hW => isIntegral_j_of_hasCMBy h W O hW⟩
  · intro h
    refine ⟨fun k _ _ W _ K _ _ O hW v => ?_⟩
    have : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 k) v.ne_bot _
    exact WeierstrassCurve.hasPotentialGoodReduction_of_isInteger_j _
      (isInteger_localization_of_isIntegral (h.isIntegral k W K O hW) v)

/-- **Lemma 12.25 from Theorem 12.18(c)**, with the empty exceptional set. -/
@[kb "milne2017mf" "Section 12, Lemma 12.25 (pdf p. 128)"]
theorem frobeniusClassLemma_of_mainTheoremCM (h : MainTheoremCM) : FrobeniusClassLemma :=
  ⟨fun K _ _ ι hK hc I hI => ⟨∅, Set.finite_empty, fun 𝔭 h𝔭 _ hp τ hτ x y hx hy =>
    h.frobenius K ι hK hc I hI 𝔭 h𝔭
      (fun h0 => by rw [h0, Ideal.absNorm_bot] at hp; exact Nat.not_prime_zero hp) τ hτ x y hx hy⟩⟩

end ModularFormsKB.Milne
