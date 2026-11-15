import ModularFormsKB.Miyake.Wave10.WeightOne
import ModularFormsKB.Miyake.Wave10.WeightTwo

/-!
# Miyake, Theorem 4.7.1 in weights one and two (coefficient form)

Miyake, *Modular Forms* (Springer 1989), §4.7, p. 177.

Theorem 4.7.1: for `χ₁`, `χ₂` modulo `M₁`, `M₂` satisfying (4.7.2), `M = M₁ M₂`, `χ = χ₁ χ₂` and
`χ(-1) = (-1)^k`, there is `f ∈ 𝒢_k(M, χ)` with `L(s; f) = L(s, χ₁) L(s - k + 1, χ₂)`, that is
`aₙ = Σ_{0 < d ∣ n} χ₁(n/d) χ₂(d) d^{k-1}` for `n ≥ 1`. Wave 4
(`ModularFormsKB.Miyake.Wave4.exists_modSpace_coeff_eq`) covers `k ≥ 3`. Here:

* `exists_modSpace_coeff_eq_weightOne`: `k = 1` (case (ii): both characters primitive);
* `exists_modSpace_coeff_eq_weightTwo`: `k = 2`, case (ii) (both primitive, not both trivial);
* `exists_modSpace_coeff_eq_weightTwo_trivial`: `k = 2`, case (i) (`M₁ = 1`, `M₂ = p` prime,
  both characters trivial): `aₙ = Σ_{d ∣ n, p ∤ d} d`.

**Not covered:** the constant term `a₀` of Theorem 4.7.1 in these weights (LE-MF-0228); the `L`-series
identity is the coefficient identity summed (as in wave 4) and is not restated.

Proofs: Tau Ceti's weight-one and weight-two Eisenstein series with `t = 1`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup DirichletCharacter
open scoped MatrixGroups

noncomputable section

namespace ModularFormsKB.Miyake.Wave10

open ModularFormsKB.Miyake.Wave4 TauCeti.EisensteinSeries

/-- **Miyake, Theorem 4.7.1**, `k = 1` (case (ii) of (4.7.2)), coefficient form: for primitive
`χ₁ mod M₁`, `χ₂ mod M₂` with `χ₁(-1) χ₂(-1) = -1`, there is `f ∈ 𝒢₁(M₁ M₂, χ₁ χ₂)` with
`aₙ(f) = Σ_{d ∣ n} χ₁(n/d) χ₂(d)` for `n ≥ 1`. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 1, coefficients)"]
theorem exists_modSpace_coeff_eq_weightOne {M₁ M₂ : ℕ} [NeZero (M₁ * M₂)]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hpar : χ₁ (-1) * χ₂ (-1) = -1) :
    ∃ f : modSpace (N := M₁ * M₂) 1
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      ∀ n : ℕ, n ≠ 0 → coeffMod f n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d := by
  let a : CharIndex (M₁ * M₂) 1 := ⟨M₁, M₂, 1, χ₁, χ₂, h₁, h₂, by simpa using hpar, by simp⟩
  have ha : a.nebentypus = (χ₁.changeLevel (dvd_mul_right M₁ M₂) *
      χ₂.changeLevel (dvd_mul_left M₂ M₁)).toUnitHom := (nebentypus_eq_iff a _).2 rfl
  refine ⟨a.weightOneInCharSpace ha, fun n hn ↦ ?_⟩
  show (qExpansion 1 a.weightOneForm).coeff n = _
  rw [CharIndex.qExpansion_weightOneForm_coeff _ hn]
  simp only [a, one_dvd, ↓reduceIte, Nat.div_one, twistedDivisorSum_apply, pow_zero, mul_one]

/-- **Miyake, Theorem 4.7.1**, `k = 2`, case (ii) of (4.7.2), coefficient form: for primitive
`χ₁ mod M₁`, `χ₂ mod M₂`, not both trivial, with `χ₁(-1) χ₂(-1) = 1`, there is
`f ∈ 𝒢₂(M₁ M₂, χ₁ χ₂)` with `aₙ(f) = Σ_{d ∣ n} χ₁(n/d) χ₂(d) d` for `n ≥ 1`. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 2, case (ii), coefficients)"]
theorem exists_modSpace_coeff_eq_weightTwo {M₁ M₂ : ℕ} [NeZero (M₁ * M₂)]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (hne : ¬ (χ₁ = 1 ∧ χ₂ = 1)) (hpar : χ₁ (-1) * χ₂ (-1) = 1) :
    ∃ f : modSpace (N := M₁ * M₂) 2
        (χ₁.changeLevel (dvd_mul_right M₁ M₂) * χ₂.changeLevel (dvd_mul_left M₂ M₁)),
      ∀ n : ℕ, n ≠ 0 → coeffMod f n = ∑ d ∈ n.divisors, χ₁ (n / d : ℕ) * χ₂ d * (d : ℂ) := by
  let a : CharIndex (M₁ * M₂) 2 := ⟨M₁, M₂, 1, χ₁, χ₂, h₁, h₂, by simpa using hpar, by simp⟩
  have ha : a.nebentypus = (χ₁.changeLevel (dvd_mul_right M₁ M₂) *
      χ₂.changeLevel (dvd_mul_left M₂ M₁)).toUnitHom := (nebentypus_eq_iff a _).2 rfl
  refine ⟨a.weightTwoInCharSpace ha, fun n hn ↦ ?_⟩
  show (qExpansion 1 a.weightTwoForm).coeff n = _
  rw [CharIndex.qExpansion_weightTwoForm_coeff_of_ne_one a (not_and_or.mp hne) hn]
  simp only [a, one_dvd, ↓reduceIte, Nat.div_one, twistedDivisorSum_apply, pow_one]

/-- **Miyake, Theorem 4.7.1**, `k = 2`, case (i) of (4.7.2), coefficient form: for a prime `p`
there is `f ∈ 𝒢₂(p, 1)` with `aₙ(f) = Σ_{d ∣ n, p ∤ d} d` for `n ≥ 1`, i.e.
`L(s; f) = ζ(s) L(s - 1, 1_p)`. -/
@[kb "miyake1989" "Theorem 4.7.1, p. 177 (k = 2, case (i), coefficients)"]
theorem exists_modSpace_coeff_eq_weightTwo_trivial {p : ℕ} (hp : p.Prime) [NeZero p] :
    ∃ f : modSpace (N := p) 2 1, ∀ n : ℕ, n ≠ 0 →
      coeffMod f n = ∑ d ∈ n.divisors, (1 : DirichletCharacter ℂ p) d * (d : ℂ) := by
  refine ⟨trivGen 1 p (by simp), fun n hn ↦ ?_⟩
  rw [coeffMod_trivGen hp (by simp) (Nat.pos_of_ne_zero hn), eisCoeff]
  simp only [one_dvd, ↓reduceIte, Nat.div_one]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [show ((1 : DirichletCharacter ℂ 1) ((n / d : ℕ) : ZMod 1)) = 1 from
    MulChar.one_apply (isUnit_of_subsingleton _)]
  simp

end ModularFormsKB.Miyake.Wave10
