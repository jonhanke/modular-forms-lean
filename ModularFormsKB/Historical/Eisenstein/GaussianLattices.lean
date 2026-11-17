import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Analysis.Complex.Basic
import ModularFormsKB.Citation
/-!
# Eisenstein's lattices with multiplication by `i`

Eisenstein, *Mathematische Abhandlungen* (1847).
Let `ω = β/α` be non-real and `(λ, μ; ν, ρ)` unimodular with `α' = ϖ α`, `β' = ϖ β`, i.e. `ϖ = λ + ν ω = μ/ω + ρ`.
For `ϖ = ±i`: `ρ = -λ`, `ω = (-λ ± i)/ν` with `ν ∣ λ² + 1` (`-μ ν = λ² + 1`), so `ν` (or `ν/2`) has only prime
factors `≡ 1 (mod 4)`, and `ν` is divisible neither by `4` nor by a prime `≡ 3 (mod 4)`; every `λ` and every
factorization `λ² + 1 = (-μ) ν` gives a solution. The value set is stable under `ω ↦ (-λ ∓ i)/(-μ)`, the two
partners having product `1`.

Formalized: `eisensteinLatticeI` (the derivation from `ϖ = i`), `eisensteinLatticeIConverse` (every factorization
gives a solution, and the partner), their complex conjugates for `ϖ = -i` (`eisensteinLatticeNegI`,
`eisensteinLatticeNegIConverse`), and the arithmetic of `ν` in `eisensteinNuDivisibility`.
-/

noncomputable section

open Complex

namespace ModularFormsKB.Historical.Eisenstein

/-- **Eisenstein, `ϖ = i`** (1847, the derivation): if `λ ρ - μ ν = 1`, `ω` is not real,
and `λ + ν ω = i = μ/ω + ρ`, then `ρ = -λ`, `ν ≠ 0`, `-μ ν = λ² + 1` and `ω = (-λ + i)/ν`. -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
def EisensteinLatticeI : Prop :=
  ∀ (l m n r : ℤ) (ω : ℂ), l * r - m * n = 1 → ω.im ≠ 0 →
    (l : ℂ) + n * ω = I → (m : ℂ) / ω + r = I →
      r = -l ∧ n ≠ 0 ∧ -m * n = l ^ 2 + 1 ∧ ω = (-l + I) / n

/-- **Eisenstein, `ϖ = i`** (1847, the converse and the partner): if `-μ ν = λ² + 1`,
then `(λ, μ; ν, -λ)` is unimodular, `ω = (-λ + i)/ν` is not real and satisfies `λ + ν ω = i = μ/ω - λ`, and its
partner `ω' = (-λ - i)/(-μ)` satisfies `ω ω' = 1`. -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
def EisensteinLatticeIConverse : Prop :=
  ∀ l m n : ℤ, -m * n = l ^ 2 + 1 →
    l * (-l) - m * n = 1 ∧ ((-l + I) / n).im ≠ 0 ∧ (l : ℂ) + n * ((-l + I) / n) = I ∧
      (m : ℂ) / ((-l + I) / n) - l = I ∧ ((-l + I) / n) * ((-l - I) / (-m)) = 1

/-- **Eisenstein's divisibility of `ν`** (1847): if `ν ∣ λ² + 1` then `4 ∤ ν`, no prime
`≡ 3 (mod 4)` divides `ν`, and every odd prime factor of `ν` is `≡ 1 (mod 4)`. -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
def EisensteinNuDivisibility : Prop :=
  ∀ l n : ℤ, n ∣ l ^ 2 + 1 →
    ¬ (4 : ℤ) ∣ n ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ n → p = 2 ∨ p % 4 = 1

/-- **Eisenstein's divisibility of `ν`**: `-1` is not a square modulo `4`, and a prime
`p` with `-1` a square modulo `p` is `2` or `≡ 1 (mod 4)` (Mathlib's `ZMod.mod_four_ne_three_of_sq_eq_neg_one`). -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
theorem eisensteinNuDivisibility : EisensteinNuDivisibility := by
  intro l n hn
  refine ⟨fun h4 ↦ ?_, fun p hp hpn ↦ ?_⟩
  · have h : ((l ^ 2 + 1 : ℤ) : ZMod 4) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 (by exact_mod_cast h4.trans hn)
    push_cast at h
    generalize (l : ZMod 4) = x at h
    revert x
    decide
  · have := Fact.mk hp
    have h : ((l ^ 2 + 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 (hpn.trans hn)
    push_cast at h
    have h3 : p % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one (y := (l : ZMod p)) (by linear_combination h)
    rcases hp.eq_two_or_odd' with h2 | h2
    · exact Or.inl h2
    · right
      obtain ⟨k, rfl⟩ := h2
      omega

/-- **Eisenstein, `ϖ = i`** (the derivation): `ν ≠ 0` since `λ` is real; then
`ω = (i - λ)/ν`, and the real and imaginary parts of `μ + ρ ω = i ω` give `ρ = -λ` and `-μ ν = λ² + 1`. -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
theorem eisensteinLatticeI : EisensteinLatticeI := by
  intro l m n r ω hdet hω h1 h2
  have hn : n ≠ 0 := by
    rintro rfl
    have := congrArg Complex.im h1
    simp at this
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hωe : ω = (-l + I) / n := by
    field_simp
    linear_combination h1
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω
    simp at hω
  have h3 : (m : ℂ) + r * ω = I * ω := by
    field_simp at h2
    linear_combination h2
  rw [hωe] at h3
  field_simp at h3
  have hre := congrArg Complex.re h3
  have him := congrArg Complex.im h3
  simp at hre him
  have hr : r = -l := by
    have : (r : ℝ) = -l := by linarith
    exact_mod_cast this
  refine ⟨hr, hn, ?_, hωe⟩
  have : ((m * n : ℤ) : ℝ) + l ^ 2 + 1 = 0 := by
    push_cast
    subst hr
    push_cast at hre
    nlinarith [hre]
  have : (m * n : ℤ) + l ^ 2 + 1 = 0 := by exact_mod_cast this
  linear_combination -this

/-- **Eisenstein, `ϖ = i`** (the converse and the partner): direct computation, with
`ν ≠ 0 ≠ μ` because `-μ ν = λ² + 1 > 0`. -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
theorem eisensteinLatticeIConverse : EisensteinLatticeIConverse := by
  intro l m n h
  have hn : n ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg l]
  have hm : m ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg l]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hc : -(m : ℂ) * n = l ^ 2 + 1 := by exact_mod_cast h
  have hI : (-(l : ℂ) + I) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
  refine ⟨by linear_combination h, ?_, ?_, ?_, ?_⟩
  · rw [Complex.div_im]
    simp
    exact hn
  · field_simp
    ring
  · field_simp
    linear_combination (-1 : ℂ) * hc - Complex.I_sq
  · rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hn' (neg_ne_zero.2 hm'))]
    linear_combination (-1 : ℂ) * hc - Complex.I_sq

/-- **Eisenstein, `ϖ = -i`** (1847, the derivation): if `λ ρ - μ ν = 1`, `ω` is not
real, and `λ + ν ω = -i = μ/ω + ρ`, then `ρ = -λ`, `ν ≠ 0`, `-μ ν = λ² + 1` and `ω = (-λ - i)/ν`. -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
def EisensteinLatticeNegI : Prop :=
  ∀ (l m n r : ℤ) (ω : ℂ), l * r - m * n = 1 → ω.im ≠ 0 →
    (l : ℂ) + n * ω = -I → (m : ℂ) / ω + r = -I →
      r = -l ∧ n ≠ 0 ∧ -m * n = l ^ 2 + 1 ∧ ω = (-l - I) / n

/-- **Eisenstein, `ϖ = -i`** (1847, the converse and the partner): if
`-μ ν = λ² + 1`, then `ω = (-λ - i)/ν` is not real and satisfies `λ + ν ω = -i = μ/ω - λ`, and its partner
`ω' = (-λ + i)/(-μ)` satisfies `ω ω' = 1`. -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
def EisensteinLatticeNegIConverse : Prop :=
  ∀ l m n : ℤ, -m * n = l ^ 2 + 1 →
    ((-l - I) / n).im ≠ 0 ∧ (l : ℂ) + n * ((-l - I) / n) = -I ∧
      (m : ℂ) / ((-l - I) / n) - l = -I ∧ ((-l - I) / n) * ((-l + I) / (-m)) = 1

/-- **Eisenstein, `ϖ = -i`**: the complex conjugate of the case `ϖ = i`
(`eisensteinLatticeI` applied to `ω̄`; the integers `λ, μ, ν, ρ` are fixed by conjugation). -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
theorem eisensteinLatticeNegI : EisensteinLatticeNegI := by
  intro l m n r ω hdet hω h1 h2
  have h1' := congrArg (starRingEnd ℂ) h1
  have h2' := congrArg (starRingEnd ℂ) h2
  simp only [map_add, map_mul, map_intCast, map_div₀, map_neg, Complex.conj_I] at h1' h2'
  obtain ⟨hr, hn, hc, he⟩ := eisensteinLatticeI l m n r (starRingEnd ℂ ω) hdet
    (by simpa using hω) h1' h2'
  refine ⟨hr, hn, hc, ?_⟩
  have := congrArg (starRingEnd ℂ) he
  simp only [map_div₀, map_add, map_neg, map_intCast, Complex.conj_I, Complex.conj_conj] at this
  rw [this]
  ring

/-- **Eisenstein, `ϖ = -i`** (the converse and the partner): the complex conjugate of
`eisensteinLatticeIConverse`. -/
@[kb "eisenstein1847" "Abhandlungen, complex multiplication"]
theorem eisensteinLatticeNegIConverse : EisensteinLatticeNegIConverse := by
  intro l m n h
  have hn : n ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg l]
  have hm : m ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg l]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hc : -(m : ℂ) * n = l ^ 2 + 1 := by exact_mod_cast h
  have hI : (-(l : ℂ) - I) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Complex.div_im]
    simp
    exact hn
  · field_simp
    ring
  · field_simp
    linear_combination (-1 : ℂ) * hc - Complex.I_sq
  · rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hn' (neg_ne_zero.2 hm'))]
    linear_combination (-1 : ℂ) * hc - Complex.I_sq

end ModularFormsKB.Historical.Eisenstein
