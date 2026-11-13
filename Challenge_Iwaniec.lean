/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import ModularFormsKB.Iwaniec1997.KloostermanMult
import ModularFormsKB.Iwaniec1997.KloostermanMoments

/-!
# Headline statements of modular-forms-lean 0.3.0: Iwaniec, *Topics in Classical Automorphic Forms*

The main results of the library for Iwaniec's *Topics in Classical Automorphic Forms* (1997), one theorem each, with
every proof a deliberate `sorry`: to check what is claimed, read this file. `Solution_Iwaniec.lean` proves the same
statements from the library, and `lake comparator` (configured by `comparator/Iwaniec.json`) checks that each proved
statement is exactly the one here and uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied. Neither Mathlib nor Tau Ceti (main, 2026-11-10) defines
Kloosterman sums. The statements were not yet reviewed by a human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library; a reader checking a statement should check
these too:

* `ModularFormsKB.Iwaniec1997.kloostermanMod` (`S(m, n; c) = ∑_{d ∈ (ℤ/c)ˣ} e((m d⁻¹ + n d)/c)` for residues
  `m, n` modulo `c`, with Mathlib's `ZMod.stdAddChar`), `ModularFormsKB.Iwaniec1997.kloosterman` (the same for
  integers `m, n` and `c ≥ 1`; `0` for `c = 0`), `ModularFormsKB.Iwaniec1997.kloostermanMoment`
  (`V_k(p) = ∑_{a ∈ (ℤ/p)ˣ} S(a, 1; p)^k`)
-/

namespace ModularFormsKB.Headlines

section Kloosterman

open ModularFormsKB.Iwaniec1997

/-- **Twisted multiplicativity of Kloosterman sums** (Iwaniec, (4.12)). If `q, r ≥ 1` are coprime, `q q̄ ≡ 1 (mod r)`
and `r r̄ ≡ 1 (mod q)`, then `S(m, n; qr) = S(q̄ m, q̄ n; r) S(r̄ m, r̄ n; q)`. -/
theorem kloosterman_mul_of_coprime {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : Nat.Coprime q r)
    (m n qbar rbar : ℤ) (hqbar : (q : ℤ) * qbar ≡ 1 [ZMOD r]) (hrbar : (r : ℤ) * rbar ≡ 1 [ZMOD q]) :
    kloosterman m n (q * r) =
      kloosterman (qbar * m) (qbar * n) r * kloosterman (rbar * m) (rbar * n) q := by
  sorry

/-- **The second moment of Kloosterman sums at a prime** (Iwaniec, (4.23)): for a prime `p`,
`V_2(p) = ∑_{a ≢ 0 (mod p)} S(a, 1; p)² = p² - p - 1`. -/
theorem kloostermanMoment_two (p : ℕ) [Fact p.Prime] :
    kloostermanMoment 2 p = (p : ℂ) ^ 2 - p - 1 := by
  sorry

end Kloosterman

end ModularFormsKB.Headlines
