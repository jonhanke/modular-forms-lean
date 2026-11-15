import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character
import TauCeti.NumberTheory.NumberField.Quadratic.Model
import ModularFormsKB.Citation
/-!
# Miyake, Theorem 3.1.4: the splitting of primes in `ℚ(√m)`

Miyake, *Modular Forms* (Springer 1989), §3.1, p. 83, Theorem 3.1.4: for a square-free integer
`m`, `F = ℚ(√m)` and a prime `p`, `p` splits in `F` if `(m / p) = 1`, remains prime if
`(m / p) = -1`, and ramifies if `(m / p) = 0`.

**Status: proved, as a bridge to Tau Ceti main.** Tau Ceti proves the decomposition law for any
quadratic field `K` through the character `χ_D` of its discriminant `D`
(`TauCeti.Multiquadratic.fundamentalDiscriminantChar_discr_eq_zero_iff`, `_eq_one_iff`,
`_eq_neg_one_iff`, file `NumberTheory/Multiquadratic/Quadratic/Character.lean`):
* `χ_D(p) = 0` iff `p` ramifies (`p ∈ ramifiedPrimes K`);
* `χ_D(p) = 1` iff there are two primes of `𝓞 K` over `p`;
* `χ_D(p) = -1` iff `p` is unramified with one prime over it (inert).

`theorem_3_1_4_discr` is this law for every quadratic field and every prime, `p = 2` included.
`theorem_3_1_4` is Miyake's form for the model `ℚ(√m) = QuadraticAlgebra ℚ m 0` of Tau Ceti and
an odd prime `p`, with the Legendre symbol `(m / p)`: at odd `p`, `χ_D(p) = (D / p)` and `D` is
`m` or `4m`, so `(D / p) = (m / p)`.

At `p = 2` the Legendre symbol is not defined; Miyake's `(m / 2)` must be read as the Kronecker
symbol of the discriminant (for `m ≡ 3 mod 4`, `2` ramifies although `m` is odd). The book page
could not be consulted by the job that wrote this file, so the reading at `p = 2` is recorded as
loose end LE-MF-0244; the statement for `p = 2` is covered by `theorem_3_1_4_discr`.
-/

open NumberField TauCeti.Multiquadratic Ideal

namespace ModularFormsKB.Miyake.Sec3_1

/-- **Miyake, Theorem 3.1.4**, for every quadratic field and every prime: with `χ_D` the
character of the discriminant `D` of `K`, `p` ramifies iff `χ_D(p) = 0`, splits (two primes over
`p`) iff `χ_D(p) = 1`, and is inert (unramified, one prime over `p`) iff `χ_D(p) = -1`. -/
@[kb "miyake1989" "Theorem 3.1.4, p. 83 (any quadratic field, character of the discriminant)"]
theorem theorem_3_1_4_discr {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (p : ℕ) [Fact p.Prime] :
    (fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) p = 0 ↔
        p ∈ ramifiedPrimes K) ∧
    (fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) p = 1 ↔
        (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2) ∧
    (fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) p = -1 ↔
        p ∉ ramifiedPrimes K ∧ (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1) :=
  ⟨fundamentalDiscriminantChar_discr_eq_zero_iff hK p,
    fundamentalDiscriminantChar_discr_eq_one_iff hK p,
    fundamentalDiscriminantChar_discr_eq_neg_one_iff hK p⟩

/-- For square-free `m ≠ 1` and an odd prime `p`, the character of the discriminant of `ℚ(√m)`
at `p` is the Legendre symbol `(m / p)`. -/
lemma fundamentalDiscriminantChar_eq_legendreSym {m : ℤ} [Fact (¬ IsSquare m)]
    (hsf : Squarefree m) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    fundamentalDiscriminantChar (discr (QuadraticAlgebra ℚ (m : ℚ) 0))
        (isFundamentalDiscr_discr (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0)) p = legendreSym p m := by
  have h := fundamentalDiscriminantChar_natCast_eq_legendreSym
    (isFundamentalDiscr_discr (K := QuadraticAlgebra ℚ (m : ℚ) 0) (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0)) hp2
  simp only [Int.cast_natCast] at h
  rw [h]
  by_cases hm : m % 4 = 1
  · rw [QuadraticAlgebra.discr_eq_of_mod_four_eq_one hsf hm]
  · rw [QuadraticAlgebra.discr_eq_four_mul_of_mod_four_ne_one hsf hm, legendreSym.mul]
    have h4 : legendreSym p 4 = 1 := by
      have : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [this]
      refine legendreSym.sq_one' p ?_
      have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        have : (p : ℤ) ∣ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp h0
        have hp := (Fact.out : p.Prime)
        have : p ∣ 2 := by exact_mod_cast this
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
      exact h2
    rw [h4, one_mul]

/-- **Miyake, Theorem 3.1.4**: let `m` be a square-free integer, `m ≠ 1`, `F = ℚ(√m)` and `p` an
odd prime. Then `p` ramifies in `F` iff `(m / p) = 0`, splits (two primes of `𝓞_F` over `p`) iff
`(m / p) = 1`, and remains prime (unramified, a single prime over `p`) iff `(m / p) = -1`. -/
@[kb "miyake1989" "Theorem 3.1.4, p. 83 (odd p, Legendre symbol)"]
theorem theorem_3_1_4 {m : ℤ} [Fact (¬ IsSquare m)] (hsf : Squarefree m) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (legendreSym p m = 0 ↔ p ∈ ramifiedPrimes (QuadraticAlgebra ℚ (m : ℚ) 0)) ∧
    (legendreSym p m = 1 ↔
        (primesOver (span {(p : ℤ)}) (𝓞 (QuadraticAlgebra ℚ (m : ℚ) 0))).ncard = 2) ∧
    (legendreSym p m = -1 ↔ p ∉ ramifiedPrimes (QuadraticAlgebra ℚ (m : ℚ) 0) ∧
        (primesOver (span {(p : ℤ)}) (𝓞 (QuadraticAlgebra ℚ (m : ℚ) 0))).ncard = 1) := by
  rw [← fundamentalDiscriminantChar_eq_legendreSym hsf p hp2]
  exact theorem_3_1_4_discr (K := QuadraticAlgebra ℚ (m : ℚ) 0) (QuadraticAlgebra.finrank_eq_two (m : ℚ) 0) p

end ModularFormsKB.Miyake.Sec3_1
