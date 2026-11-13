import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.Complex.Basic

/-!
# Elements of a cubic field: Heegner's algebra

Heegner's argument takes place in a cubic number field `L ⊆ ℂ` (the field `ℚ(j(√-p))`). This file proves
the algebraic steps that do not involve modular functions.

* `finrank_adjoin_eq_three`: an irrational element of `L` has degree `3`.
* `eq_zero_of_mul_sq_add_mul_add_eq_zero`: an irrational element of `L` is not a root of a nonzero rational
  polynomial of degree at most `2`.
* `eq_of_pow_three_eq_pow_three`: in `L`, `u³ = v³` implies `u = v` (`L` contains no primitive cube root of
  unity, since `2 ∤ 3`).
* `exists_coeffs_of_pow_four`: **Heegner's coefficient comparison.** If `x ∈ L` is an algebraic integer whose
  fourth power is irrational and a root of `X³ - γX - 16` with `γ ∈ ℤ`, then the minimal polynomial
  `X³ + aX² + bX + c` of `x` has integer coefficients with `(a² - 2b)² = 2(b² - 2ac)`, `c⁴ = 16` and
  `γ = -((b² - 2ac)² - 2(a² - 2b)c²)`. These say that the cubic whose roots are the fourth powers of the
  roots of `X³ + aX² + bX + c` (computed by squaring the roots twice) is `X³ - γX - 16`.

The squaring-the-roots identities replace Tau Ceti's Tschirnhaus polynomials
(`TauCeti.tschirnhausPolynomial_X_pow_four_eq_iff`).
-/

open IntermediateField Module Polynomial

namespace ModularFormsKB.WeberHeegnerStark

variable {L : IntermediateField ℚ ℂ}

/-- An element of a cubic field that is not rational has degree `3`. -/
theorem finrank_adjoin_eq_three (hL : finrank ℚ L = 3) {z : ℂ} (hz : z ∈ L)
    (hzq : z ∉ (⊥ : IntermediateField ℚ ℂ)) : finrank ℚ ℚ⟮z⟯ = 3 := by
  have : FiniteDimensional ℚ L := FiniteDimensional.of_finrank_pos (by omega)
  have hd := finrank_dvd_of_le_right (K := ℚ) (adjoin_simple_le_iff.2 hz)
  rw [hL] at hd
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · exact absurd (adjoin_simple_eq_bot_iff.1 (finrank_eq_one_iff.1 h)) hzq
  · exact h

/-- An irrational element of a cubic field is not a root of a nonzero rational polynomial of degree
at most `2`. -/
theorem eq_zero_of_mul_sq_add_mul_add_eq_zero (hL : finrank ℚ L = 3) {z : ℂ} (hz : z ∈ L)
    (hzq : z ∉ (⊥ : IntermediateField ℚ ℂ)) {α β δ : ℚ}
    (h : (α : ℂ) * z ^ 2 + β * z + δ = 0) : α = 0 ∧ β = 0 ∧ δ = 0 := by
  by_contra hne
  set p : ℚ[X] := C α * X ^ 2 + C β * X + C δ with hp
  have hcoeff : p.coeff 2 = α ∧ p.coeff 1 = β ∧ p.coeff 0 = δ := by
    simp [hp, coeff_X, coeff_C]
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0] at hcoeff
    simp only [coeff_zero] at hcoeff
    exact hne ⟨hcoeff.1.symm, hcoeff.2.1.symm, hcoeff.2.2.symm⟩
  have hroot : aeval z p = 0 := by
    simp only [hp, map_add, map_mul, aeval_C, aeval_X, map_pow]
    simpa [Complex.ofReal_ratCast] using h
  have hint : IsIntegral ℚ z := (isAlgebraic_iff_isIntegral).1 ⟨p, hp0, hroot⟩
  have hdeg : p.natDegree ≤ 2 := by
    rw [hp]
    compute_degree
  have hmin := natDegree_le_of_dvd (minpoly.dvd ℚ z hroot) hp0
  have h3 := finrank_adjoin_eq_three hL hz hzq
  rw [adjoin.finrank hint] at h3
  omega

/-- In a cubic field, `u³ = v³` implies `u = v`. -/
theorem eq_of_pow_three_eq_pow_three (hL : finrank ℚ L = 3) {u v : ℂ} (hu : u ∈ L) (hv : v ∈ L)
    (h : u ^ 3 = v ^ 3) : u = v := by
  by_cases hv0 : v = 0
  · subst hv0
    simpa using h
  set ω := u / v with hω
  have hωL : ω ∈ L := div_mem hu hv
  have hω3 : ω ^ 3 = 1 := by rw [hω, div_pow, h, div_self (pow_ne_zero 3 hv0)]
  have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
  rcases mul_eq_zero.1 hfac with h1 | h2
  · have : ω = 1 := by linear_combination h1
    rw [hω, div_eq_one_iff_eq hv0] at this
    exact this
  · exfalso
    by_cases hq : ω ∈ (⊥ : IntermediateField ℚ ℂ)
    · obtain ⟨r, hr⟩ := IntermediateField.mem_bot.1 hq
      have : ((r ^ 2 + r + 1 : ℚ) : ℂ) = 0 := by
        rw [← hr] at h2
        push_cast
        simpa using h2
      have hr0 : r ^ 2 + r + 1 = 0 := by exact_mod_cast this
      nlinarith [sq_nonneg (2 * r + 1)]
    · have := eq_zero_of_mul_sq_add_mul_add_eq_zero (α := 1) (β := 1) (δ := 1) hL hωL hq
        (by push_cast; linear_combination h2)
      exact one_ne_zero this.1

/-- A rational algebraic integer is a rational integer. -/
theorem exists_intCast_eq_of_mem_bot {z : ℂ} (hz : z ∈ (⊥ : IntermediateField ℚ ℂ))
    (hint : IsIntegral ℤ z) : ∃ n : ℤ, (n : ℂ) = z := by
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hz
  have hr : IsIntegral ℤ r := by
    have h' : IsIntegral ℤ (algebraMap ℚ ℂ r) := hint
    exact isIntegral_algebraMap_iff.1 h'
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hr
  exact ⟨n, by rw [← hn]; simp⟩

/-- Squaring the roots of a monic cubic: if `t³ - E₁t² + E₂t - E₃ = 0`, then
`(t²)³ - (E₁² - 2E₂)(t²)² + (E₂² - 2E₁E₃)t² - E₃² = 0`. -/
theorem sq_root_of_cubic {t E₁ E₂ E₃ : ℂ} (h : t ^ 3 - E₁ * t ^ 2 + E₂ * t - E₃ = 0) :
    (t ^ 2) ^ 3 - (E₁ ^ 2 - 2 * E₂) * (t ^ 2) ^ 2 + (E₂ ^ 2 - 2 * E₁ * E₃) * t ^ 2 - E₃ ^ 2 = 0 := by
  linear_combination (t ^ 3 + E₁ * t ^ 2 + E₂ * t + E₃) * h

/-- **Heegner's coefficient comparison.** Let `L ⊆ ℂ` be a cubic field and `x ∈ L` an algebraic integer
whose fourth power `w = x⁴` is irrational and satisfies `w³ - γw - 16 = 0` with `γ ∈ ℤ`. Then the
minimal polynomial `X³ + aX² + bX + c` of `x` has integer coefficients with `(a² - 2b)² = 2(b² - 2ac)`,
`c⁴ = 16` and `γ = -((b² - 2ac)² - 2(a² - 2b)c²)`. -/
theorem exists_coeffs_of_pow_four (hL : finrank ℚ L = 3) {x : ℂ} (hx : x ∈ L)
    (hxint : IsIntegral ℤ x) (hw : x ^ 4 ∉ (⊥ : IntermediateField ℚ ℂ)) {γ : ℤ}
    (hcub : (x ^ 4) ^ 3 - γ * x ^ 4 - 16 = 0) :
    ∃ a b c : ℤ, (a ^ 2 - 2 * b) ^ 2 = 2 * (b ^ 2 - 2 * a * c) ∧ c ^ 4 = 16 ∧
      γ = -((b ^ 2 - 2 * a * c) ^ 2 - 2 * (a ^ 2 - 2 * b) * c ^ 2) := by
  have hxq : x ∉ (⊥ : IntermediateField ℚ ℂ) := fun h ↦ hw (pow_mem h 4)
  have h3 := finrank_adjoin_eq_three hL hx hxq
  rw [adjoin.finrank (hxint.tower_top (A := ℚ))] at h3
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hxint] at h3
  set P := minpoly ℤ x with hP
  have hmon : P.Monic := minpoly.monic hxint
  rw [hmon.natDegree_map] at h3
  set a := P.coeff 2
  set b := P.coeff 1
  set c := P.coeff 0
  have hxroot : x ^ 3 + (a : ℂ) * x ^ 2 + b * x + c = 0 := by
    have h0 := minpoly.aeval ℤ x
    rw [← hP, hmon.as_sum, h3] at h0
    simp [Finset.sum_range_succ] at h0
    linear_combination h0
  -- Square the roots twice.
  have ht := sq_root_of_cubic (t := x) (E₁ := -a) (E₂ := b) (E₃ := -c)
    (by linear_combination hxroot)
  have hw4 := sq_root_of_cubic ht
  rw [← pow_mul] at hw4
  norm_num at hw4
  -- Compare with `w³ - γw - 16`.
  have hdiff : (((-((a ^ 2 - 2 * b) ^ 2 - 2 * (b ^ 2 - 2 * a * c)) : ℤ) : ℚ) : ℂ) * (x ^ 4) ^ 2 +
      ((((b ^ 2 - 2 * a * c) ^ 2 - 2 * (a ^ 2 - 2 * b) * c ^ 2 + γ : ℤ) : ℚ) : ℂ) * x ^ 4 +
      (((16 - c ^ 4 : ℤ) : ℚ) : ℂ) = 0 := by
    push_cast
    linear_combination hw4 - hcub
  obtain ⟨h1, h2, h3'⟩ := eq_zero_of_mul_sq_add_mul_add_eq_zero hL (pow_mem hx 4) hw hdiff
  have h1' : (a ^ 2 - 2 * b) ^ 2 - 2 * (b ^ 2 - 2 * a * c) = 0 := by
    have h1'' : (-((a ^ 2 - 2 * b) ^ 2 - 2 * (b ^ 2 - 2 * a * c)) : ℤ) = 0 := by exact_mod_cast h1
    linarith
  refine ⟨a, b, c, by linarith, ?_, ?_⟩
  · have : (16 - c ^ 4 : ℤ) = 0 := by exact_mod_cast h3'
    linarith
  · have : ((b ^ 2 - 2 * a * c) ^ 2 - 2 * (a ^ 2 - 2 * b) * c ^ 2 + γ : ℤ) = 0 := by
      exact_mod_cast h2
    linarith

end ModularFormsKB.WeberHeegnerStark
