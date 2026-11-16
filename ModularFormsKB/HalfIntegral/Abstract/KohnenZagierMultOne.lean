/-
# `PlusMultiplicityOne` and `KohnenPlusMultOne` are one statement

The input `PlusMultiplicityOne`
(`KohnenZagierReduction.lean`) and the input `KohnenPlusMultOne` (`KohnenEigen.lean`) both say that eigenforms of the
Hecke operators $T(p^2)$, $p$ odd, in Kohnen's plus space with the same eigenvalues are proportional. They differ only
in how an eigenform is presented: `PlusMultiplicityOne` lists the $q$-expansion and the eigenvalue equations, while
`KohnenPlusMultOne` packages them as `IsPlusEigenform`. Each is derived from the other
(`plusMultiplicityOne_iff_kohnenPlusMultOne`), so the Kohnen–Zagier formula needs the one statement once.
-/
import ModularFormsKB.HalfIntegral.Abstract.KohnenZagierReduction
import ModularFormsKB.HalfIntegral.Abstract.KohnenEigen

namespace ModularFormsKB.HalfIntegral

open Complex

/-- `KohnenPlusMultOne` gives `PlusMultiplicityOne`. -/
theorem plusMultiplicityOne_of_kohnenPlusMultOne {M : MultiplierSystem} {k : ℕ} (h : KohnenPlusMultOne M k) :
    PlusMultiplicityOne M k where
  mult_one hk g hg hg0 g' hg' c c' e hc hc' hcg hcg' :=
    h.mult_one hk g g' e ⟨hg, c, hc, hcg⟩ ⟨hg', c', hc', hcg'⟩ hg0

/-- `PlusMultiplicityOne` gives `KohnenPlusMultOne`. -/
theorem kohnenPlusMultOne_of_plusMultiplicityOne {M : MultiplierSystem} {k : ℕ} (h : PlusMultiplicityOne M k) :
    KohnenPlusMultOne M k where
  mult_one hk g g' μ hg hg' hg0 := by
    obtain ⟨hgp, c, hc, hcg⟩ := hg
    obtain ⟨hgp', c', hc', hcg'⟩ := hg'
    exact h.mult_one hk g hgp hg0 g' hgp' c c' μ hc hc' hcg hcg'

/-- **The two multiplicity one statements are equivalent.** -/
theorem plusMultiplicityOne_iff_kohnenPlusMultOne {M : MultiplierSystem} {k : ℕ} :
    PlusMultiplicityOne M k ↔ KohnenPlusMultOne M k :=
  ⟨kohnenPlusMultOne_of_plusMultiplicityOne, plusMultiplicityOne_of_kohnenPlusMultOne⟩

end ModularFormsKB.HalfIntegral
