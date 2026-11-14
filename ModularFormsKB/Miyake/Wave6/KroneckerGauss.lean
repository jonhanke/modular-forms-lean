import ModularFormsKB.Miyake.Sec4_3.Gauss
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol

/-!
# Miyake §4.8: the Gauss sum of the Kronecker symbol, Lemma 4.8.1 (1)

Miyake, *Modular Forms* (Springer 1989), Lemma 4.8.1 (1), p. 183: for the discriminant `d` of a
quadratic field `K = ℚ(√d)` and the Kronecker symbol `χ_d = (d/·)`,
`W(χ_d) = √d` if `d > 0` and `W(χ_d) = i √|d|` if `d < 0`.

`W` is Miyake's Gauss sum (`Miyake.gaussW`, Sec4_3/Defs.lean). The discriminants of quadratic
fields are the fundamental discriminants other than `1` (Mathlib's `Int.IsFundamentalDiscr`), and
`χ_d` is Tau Ceti's Kronecker character `TauCeti.kroneckerChar ℂ d`, a primitive character modulo
`|d|`.

Miyake proves (1) by comparing the functional equations of `ζ_K(s) = ζ(s) L(s, χ_d)` (his
Theorem 3.3.1, Hecke's functional equation of the Dedekind zeta function of `K`), which is not
available. Here the lemma is **stated** as the proposition `KroneckerGaussSumStatement`; it is not
proved and no result of this repository assumes it (LE-MF-0202).

Part (2), `W(ψ ∘ N_K) = χ_d(p) ψ(|d|) W(ψ)²` for the Hecke character `ψ ∘ N_K` of `K`, needs Gauss
sums of Hecke characters of `K` (Miyake §3.3), which this repository does not define; it is not
formalized (LE-MF-0201).
-/

open Complex

noncomputable section

namespace ModularFormsKB.Miyake.Wave6

/-- **Miyake, Lemma 4.8.1 (1)** (stated, not proved): for a fundamental discriminant `d ≠ 1`
(the discriminant of the quadratic field `ℚ(√d)`), the Gauss sum of the Kronecker symbol
`χ_d = (d/·)` modulo `|d|` is `√d` if `d > 0` and `i √|d|` if `d < 0`. -/
@[kb "miyake1989" "Lemma 4.8.1 (1), p. 183 (stated)"]
def KroneckerGaussSumStatement : Prop :=
  ∀ (d : ℤ) (hd : Int.IsFundamentalDiscr d), d ≠ 1 →
    haveI : NeZero d.natAbs := ⟨Int.natAbs_ne_zero.mpr hd.ne_zero⟩
    Miyake.gaussW (TauCeti.kroneckerChar ℂ d (hd.emod_four_eq_zero_or_one.imp id id) hd.ne_zero) =
      if 0 < d then ((Real.sqrt d : ℝ) : ℂ) else I * ((Real.sqrt |(d : ℝ)| : ℝ) : ℂ)

end ModularFormsKB.Miyake.Wave6
