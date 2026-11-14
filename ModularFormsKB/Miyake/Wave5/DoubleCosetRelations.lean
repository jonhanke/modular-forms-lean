import ModularFormsKB.Miyake.Wave5.CoprimeProduct
import ModularFormsKB.Miyake.Wave5.BadPrime
import ModularFormsKB.Miyake.Wave5.GoodPrime
import ModularFormsKB.Miyake.Wave5.HeckeGeneration

/-!
# Miyake, Lemmas 4.5.7 and 4.5.8 at level `Γ₀(N)`, unconditionally

Miyake, *Modular Forms* (Springer 1989), §4.5, pp. 140–142.

Wave 4 assumed the double-coset relations of Lemma 4.5.7 (1) and Lemma 4.5.8 (1) as the named
input `ModularFormsKB.Miyake.Wave4.DoubleCosetRelations N` (loose end LE-MF-0180). The three
files `CoprimeProduct.lean`, `BadPrime.lean` and `GoodPrime.lean` prove them, so the input holds
for every level (`doubleCosetRelations`), and every wave 4 result stated from it becomes
unconditional:

* Lemma 4.5.7 (2) for Miyake's `T(n)` (`miyakeHeckeT_prime_mul'`, `miyakeHeckeT_prime_mul_of_dvd'`);
* Lemma 4.5.8 (2) for Miyake's `T(n)` (`miyakeHeckeT_mul_of_coprime'`);
* Miyake's `T(n)` (the sum of the double cosets of determinant `n`) is Tau Ceti's composite
  Hecke element (`miyakeHeckeT_eq_heckeTCompositeGamma0'`), so every statement of waves 4 and 5
  written with Tau Ceti's `heckeTCompositeGamma0` is about Miyake's `T(n)`;
* Theorem 4.5.9, generation half (`closure_heckeGenerator_eq_top`).
-/

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups HeckeCosetModule

noncomputable section

namespace ModularFormsKB.Miyake.Wave5

open ModularFormsKB.Miyake.Wave4

variable (N : ℕ) [NeZero N]

/-- **Miyake, Lemmas 4.5.7 (1) and 4.5.8 (1)** at every level: the input of wave 4 holds. -/
@[kb "miyake1989" "Lemma 4.5.7 (1), p. 140; Lemma 4.5.8 (1), p. 141"]
theorem doubleCosetRelations : DoubleCosetRelations N where
  mul_of_coprime hl hl' hc := heckeTPair_mul_of_coprime N hl hl' hc
  one_prime_mul hp hpN _ he := heckeTPair_one_prime_mul N hp hpN he
  one_prime_mul_of_dvd hp hpN e := heckeTPair_one_prime_mul_of_dvd N hp hpN e

/-- **Miyake, Lemma 4.5.7 (2)** for Miyake's `T(n)`, unconditionally: for a prime `p ∤ N` and
`e ≥ 1`, `T(p) T(p^e) = T(p^{e+1}) + p T(p, p) T(p^{e-1})`. -/
@[kb "miyake1989" "Lemma 4.5.7 (2), p. 140 (p prime to N, unconditional)"]
theorem miyakeHeckeT_prime_mul' {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {e : ℕ} (he : 1 ≤ e) :
    miyakeHeckeT N p * miyakeHeckeT N (p ^ e) =
      miyakeHeckeT N (p ^ (e + 1)) +
        (p : ℤ) • (heckeTPair N p p * miyakeHeckeT N (p ^ (e - 1))) :=
  miyakeHeckeT_prime_mul N (doubleCosetRelations N) hp hpN he

/-- **Miyake, Lemma 4.5.7 (2)** for Miyake's `T(n)`, unconditionally: for a prime `p ∣ N`,
`T(p) T(p^e) = T(p^{e+1})`. -/
@[kb "miyake1989" "Lemma 4.5.7 (2), p. 140 (p dividing N, unconditional)"]
theorem miyakeHeckeT_prime_mul_of_dvd' {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (e : ℕ) :
    miyakeHeckeT N p * miyakeHeckeT N (p ^ e) = miyakeHeckeT N (p ^ (e + 1)) :=
  miyakeHeckeT_prime_mul_of_dvd N (doubleCosetRelations N) hp hpN e

/-- **Miyake, Lemma 4.5.8 (2)** for Miyake's `T(n)`, unconditionally: `T(m) T(n) = T(mn)` for
coprime `m`, `n`. -/
@[kb "miyake1989" "Lemma 4.5.8 (2), p. 141 (Miyake's T(n), unconditional)"]
theorem miyakeHeckeT_mul_of_coprime' {m n : ℕ} (hmn : m.Coprime n) :
    miyakeHeckeT N m * miyakeHeckeT N n = miyakeHeckeT N (m * n) :=
  miyakeHeckeT_mul_of_coprime N (doubleCosetRelations N) hmn

/-- **Miyake's `T(n)` is Tau Ceti's composite Hecke element** for `n ≥ 1`, unconditionally. -/
theorem miyakeHeckeT_eq_heckeTCompositeGamma0' {n : ℕ} (hn : n ≠ 0) :
    miyakeHeckeT N n = HeckeRing.GL2.heckeTCompositeGamma0 N n :=
  miyakeHeckeT_eq_heckeTCompositeGamma0 N (doubleCosetRelations N) hn

/-- **Miyake, Theorem 4.5.9**, generation half: the Hecke ring `ℛ(N)` is generated as a ring by
`T(p)`, `T(p, p)` for the primes `p ∤ N` and `T(q)` for the primes `q ∣ N`. (The algebraic
independence of these generators, the other half, is not proved.) -/
@[kb "miyake1989" "Theorem 4.5.9, p. 142 (generation)"]
theorem closure_heckeGenerator_eq_top :
    Subring.closure (Set.range (heckeGenerator N)) = ⊤ :=
  closure_heckeGenerator_eq_top_of_relations N (doubleCosetRelations N)

end ModularFormsKB.Miyake.Wave5
