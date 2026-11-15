import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.OrderOfConductor
import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.Units
import ModularFormsKB.Citation
/-!
# Miyake, Theorem 6.7.2 (1): class numbers of orders of imaginary quadratic fields

Miyake, *Modular Forms* (Springer 1989), §6.7, p. 257, Theorem 6.7.2 (with the local index of
Lemma 6.7.1): an order `O` of index `n` (its conductor) in an imaginary quadratic field `K` of
discriminant `d` has class number

`h(O) = h_K · n / [O_K^× : O^×] · ∏_{p ∣ n} (1 - (d / p) p⁻¹)`.

**Status: proved for the quadratic part, as a bridge to Tau Ceti main.** The orders of a quadratic
field are the `ℤ + f 𝓞 K` (`TauCeti.GlobalNumberFields.NumberFieldOrder.intAddMulOrder K f`, every
order is one of them by `eq_intAddMulOrder_index`, and `f` is the index `[𝓞 K : O]`); the class
number of `O` is `Nat.card (Pic O)`. Tau Ceti main proves the formula (Cox, Theorem 7.24) as
`card_pic_intAddMulOrder_eq` and the unit index as `index_range_unitsMap_intAddMulOrder`. This file
restates both in Miyake's form, for an imaginary quadratic `K` (Miyake's hypothesis), and records
the explicit unit index: `1` for `f = 1`; for `f > 1`, `2` if `d = -4`, `3` if `d = -3`, `1`
otherwise.

Not covered: the part of Theorem 6.7.2 about orders of the split algebra `M₂(ℚ)` and the
quaternion case of Lemma 6.7.1 (Miyake's unified treatment through local indices of orders of
quadratic and quaternion algebras); see loose end LE-MF-0062.
-/

open NumberField TauCeti.Multiquadratic TauCeti.GlobalNumberFields NumberFieldOrder

namespace ModularFormsKB.Miyake.Sec6_7

variable {K : Type*} [Field K] [NumberField K]

/-- **Miyake, Theorem 6.7.2 (1)**: the class number of the order `O_f = ℤ + f 𝓞 K` of index `f`
in a quadratic field `K` of discriminant `d` is
`h(O_f) = h_K · f / [(𝓞 K)ˣ : O_fˣ] · ∏_{p ∣ f} (1 - χ_d(p) / p)`. -/
@[kb "miyake1989" "Theorem 6.7.2 (1), p. 257 (quadratic orders)"]
theorem theorem_6_7_2 (hK : Module.finrank ℚ K = 2) (f : ℕ) [NeZero f] :
    (Nat.card (Pic (intAddMulOrder K f)) : ℚ) =
      Nat.card (ClassGroup (𝓞 K)) * f /
          (Units.map ((intAddMulOrder K f).toRingOfIntegers.val :
            (intAddMulOrder K f).toRingOfIntegers →* 𝓞 K)).range.index *
        ∏ p ∈ f.primeFactors,
          (1 - (fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) p : ℚ) / p) :=
  card_pic_intAddMulOrder_eq hK f

/-- **Miyake, Theorem 6.7.2 (1)** for imaginary quadratic `K`, with the unit index made explicit:
`[(𝓞 K)ˣ : O_fˣ]` is `1` for `f = 1`, and for `f > 1` it is `2` if `d = -4`, `3` if `d = -3`,
and `1` otherwise. -/
@[kb "miyake1989" "Theorem 6.7.2 (1), p. 257 (imaginary quadratic, unit index explicit)"]
theorem theorem_6_7_2_imaginary [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (f : ℕ)
    [NeZero f] :
    (Nat.card (Pic (intAddMulOrder K f)) : ℚ) =
      Nat.card (ClassGroup (𝓞 K)) * f /
          ((if f = 1 then 1 else if discr K = -4 then 2 else if discr K = -3 then 3 else 1 : ℕ) :
            ℚ) *
        ∏ p ∈ f.primeFactors,
          (1 - (fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) p : ℚ) / p) := by
  rw [theorem_6_7_2 hK f, index_range_unitsMap_intAddMulOrder hK]

end ModularFormsKB.Miyake.Sec6_7
