import ModularFormsKB.Miyake.Wave6.KroneckerGauss
import ModularFormsKB.HalfIntegral.GaussSign
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Character

/-!
# Miyake Lemma 4.8.1 (1) for the odd prime discriminants

Miyake, *Modular Forms* (Springer 1989), Lemma 4.8.1 (1), p. 183: `W(χ_d) = √d` if `d > 0` and
`i √|d|` if `d < 0`, for the discriminant `d` of a quadratic field (the named statement
`Wave6.KroneckerGaussSumStatement`).

Proved here for the odd prime discriminants `d = p* = (-1)^{(p-1)/2} p`, `p` an odd prime
(Tau Ceti's `TauCeti.Multiquadratic.oddPrimeDiscriminant p`): the Kronecker character `(p*/·)` is
the Legendre symbol `(·/p)`, so `W(χ_{p*}) = G_p`, which is `ε_p √p` by Gauss's sign
(`HalfIntegral.quadGaussSumSign`, from Tau Ceti's evaluation of `Σ e(r²/p)`).

The general fundamental discriminant (products of prime discriminants, and `d = -4, ±8`) is open
(LE-MF-0202): it needs the multiplicativity `W(χ₁χ₂) = χ₁(m₂) χ₂(m₁) W(χ₁) W(χ₂)` of Gauss sums
of characters of coprime moduli and the reciprocity of prime-discriminant characters, neither of
which is in Mathlib or Tau Ceti main.
-/

open Complex TauCeti.Multiquadratic

noncomputable section

namespace ModularFormsKB.Miyake.Sec4_8

/-- **Miyake, Lemma 4.8.1 (1), for `d = p*`**: for an odd prime `p` and `d = p*` the odd prime
discriminant, `W(χ_d) = √d` if `d > 0` (`p ≡ 1 mod 4`) and `i √|d|` if `d < 0`
(`p ≡ 3 mod 4`). -/
@[kb "miyake1989" "Lemma 4.8.1 (1), p. 183, for d an odd prime discriminant"]
theorem gaussW_kroneckerChar_oddPrimeDiscriminant {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (d : ℤ) (hdp : d = oddPrimeDiscriminant p) (hd : Int.IsFundamentalDiscr d) :
    haveI : NeZero d.natAbs := ⟨Int.natAbs_ne_zero.mpr hd.ne_zero⟩
    Miyake.gaussW (TauCeti.kroneckerChar ℂ d (hd.emod_four_eq_zero_or_one.imp id id) hd.ne_zero) =
      if 0 < d then ((Real.sqrt d : ℝ) : ℂ) else I * ((Real.sqrt |(d : ℝ)| : ℝ) : ℂ) := by
  haveI : NeZero d.natAbs := ⟨Int.natAbs_ne_zero.mpr hd.ne_zero⟩
  have hPD : IsPrimeDiscriminant d := hdp ▸ isPrimeDiscriminant_iff.mpr (Or.inr ⟨p, hp, hodd, rfl⟩)
  have hnat : d.natAbs = p := by rw [hdp, oddPrimeDiscriminant_natAbs]
  have hp2 : p ≠ 2 := fun h ↦ by subst h; exact absurd hodd (by decide)
  -- the Gauss sum as a sum over `x < |d|`
  have hW : Miyake.gaussW (TauCeti.kroneckerChar ℂ d (hd.emod_four_eq_zero_or_one.imp id id)
      hd.ne_zero) = HalfIntegral.gaussQ p := by
    rw [Miyake.gaussW, gaussSum, HalfIntegral.gaussQ,
      ← HalfIntegral.sum_range_eq_sum_zmod (fun x : ZMod d.natAbs ↦
        TauCeti.kroneckerChar ℂ d (hd.emod_four_eq_zero_or_one.imp id id) hd.ne_zero x *
          ZMod.stdAddChar x)]
    have hterm : ∀ x : ℕ,
        TauCeti.kroneckerChar ℂ d (hd.emod_four_eq_zero_or_one.imp id id) hd.ne_zero
            (x : ZMod d.natAbs) * ZMod.stdAddChar (x : ZMod d.natAbs) =
          (jacobiSym x p : ℂ) * cexp (2 * Real.pi * I * x / p) := by
      intro x
      have h1 : TauCeti.kroneckerChar ℂ d (hd.emod_four_eq_zero_or_one.imp id id) hd.ne_zero
          (((x : ℤ)) : ZMod d.natAbs) = (TauCeti.kroneckerSym d x : ℂ) :=
        TauCeti.kroneckerChar_intCast _ _ _
      push_cast at h1
      rw [h1, ← HalfIntegral.cexp_eq_stdAddChar, hnat, ← primeDiscriminantCharFun_eq_kroneckerSym hPD,
        hdp, primeDiscriminantCharFun_oddPrimeDiscriminant hodd]
    simp_rw [hterm]
    rw [hnat]
  rw [hW, HalfIntegral.quadGaussSumSign.sign p hp hp2]
  unfold HalfIntegral.epsD
  rw [hdp, oddPrimeDiscriminant]
  by_cases h4 : p % 4 = 1
  · have hz : (p : ℤ) % 4 = 1 := by omega
    rw [if_pos h4, if_pos hz, if_pos (by exact_mod_cast hp.pos)]
    simp
  · have hz : ¬ (p : ℤ) % 4 = 1 := by omega
    rw [if_neg h4, if_neg hz, if_neg (by have := hp.pos; omega)]
    push_cast
    rw [abs_neg, Nat.abs_cast]

end ModularFormsKB.Miyake.Sec4_8
