import ModularFormsKB.Milne.Ch11.WeilRationality
import ModularFormsKB.Milne.Ch11.WeilAssembly

/-!
# Milne, Section 11: F. K. Schmidt's theorem from the Hasse–Weil bound, and Theorem 11.4

The two-sided bound `HasseWeilBound` makes $N_n = \sum_{d \mid n} d B_d$ positive for all large $n$. For a prime
$\ell$ the divisors of $\ell$ are $1$ and $\ell$, so $N_\ell = B_1 + \ell B_\ell$; taking two large primes
$\ell_1 \ne \ell_2$, either there is a place of degree $1$ or there are places of the coprime degrees $\ell_1$, $\ell_2$,
and a Bézout combination of them has degree $1$. This proves `SchmidtDegreeOne` from `HasseWeilBound` (the
Stepanov–Bombieri proof of the bound does not use the zeta function, so there is no circularity).

Hence **Theorem 11.4** (`WeilCurveTheorem`) follows from `HasseWeilBound` alone:
`weilCurveTheorem_of_hasseWeilBound`.
-/

open Finset TauCeti TauCeti.AlgebraicGeometry

namespace ModularFormsKB.Milne

universe u v

/-- For a prime $\ell$, $N_\ell = B_1 + \ell B_\ell$. -/
lemma curvePointCount_prime (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F] {ℓ : ℕ}
    (hℓ : ℓ.Prime) :
    curvePointCount k F ℓ = Nat.card {P : Place k F // P.degree = 1} +
      ℓ * Nat.card {P : Place k F // P.degree = ℓ} := by
  unfold curvePointCount
  rw [Nat.Prime.divisors hℓ, sum_insert (by simpa using hℓ.one_lt.ne), sum_singleton, one_mul]

/-- If $s > 1$ and $C$ is real, then $s^{2n} + 1 - C s^n > 0$ for all large $n$. -/
lemma eventually_pos (s C : ℝ) (hs : 1 < s) : ∃ N : ℕ, ∀ n, N ≤ n → 0 < s ^ n * s ^ n + 1 - C * s ^ n := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max C 0) hs
  refine ⟨N, fun n hn => ?_⟩
  have h1 : s ^ N ≤ s ^ n := pow_le_pow_right₀ hs.le hn
  have h2 : C < s ^ n := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN h1)
  have h3 : 0 < s ^ n := pow_pos (by linarith) n
  nlinarith

/-- **F. K. Schmidt's theorem from the Hasse–Weil bound.** -/
theorem schmidtDegreeOne_of_hasseWeilBound (hB : HasseWeilBound.{u, v}) : SchmidtDegreeOne.{u, v} := by
  refine ⟨fun k F _ _ _ _ hF hex => ?_⟩
  classical
  obtain ⟨C, hC⟩ := hB.bound k F hF hex
  set q : ℝ := (Nat.card k : ℝ) with hq
  have hq2 : (2 : ℝ) ≤ q := by rw [hq]; exact_mod_cast (Finite.one_lt_card : 1 < Nat.card k)
  have hs : 1 < Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  obtain ⟨N, hN⟩ := eventually_pos (Real.sqrt q) C hs
  -- `N_n > 0` for `n ≥ max N 1`
  have hpos : ∀ n, max N 1 ≤ n → 0 < curvePointCount k F n := by
    intro n hn
    have h := hC n (le_trans (le_max_right _ _) hn)
    have hsq : Real.sqrt q ^ n * Real.sqrt q ^ n = q ^ n := by
      rw [← mul_pow, Real.mul_self_sqrt (by linarith)]
    have hp := hN n (le_trans (le_max_left _ _) hn)
    rw [hsq] at hp
    have : (0 : ℝ) < curvePointCount k F n := by
      have := (abs_le.mp h).1
      linarith
    exact_mod_cast this
  -- two distinct large primes
  obtain ⟨ℓ₁, hℓ₁, hp₁⟩ := Nat.exists_infinite_primes (max N 1)
  obtain ⟨ℓ₂, hℓ₂, hp₂⟩ := Nat.exists_infinite_primes (ℓ₁ + 1)
  have hne : ℓ₁ ≠ ℓ₂ := by omega
  have hcop : Nat.Coprime ℓ₁ ℓ₂ := (Nat.coprime_primes hp₁ hp₂).mpr hne
  by_cases h1 : 0 < Nat.card {P : Place k F // P.degree = 1}
  · obtain ⟨⟨P, hP⟩⟩ := (Nat.card_pos_iff.mp h1).1
    exact ⟨WeilDivisor.ofPoint P, by rw [Divisor.degree_ofPoint, hP]; rfl⟩
  · push Not at h1
    have hz : Nat.card {P : Place k F // P.degree = 1} = 0 := by omega
    have hex' : ∀ ℓ, ℓ.Prime → max N 1 ≤ ℓ → ∃ P : Place k F, P.degree = ℓ := by
      intro ℓ hℓ hle
      have := hpos ℓ hle
      rw [curvePointCount_prime k F hℓ, hz, zero_add] at this
      have hc : 0 < Nat.card {P : Place k F // P.degree = ℓ} := Nat.pos_of_mul_pos_left this
      obtain ⟨⟨P, hP⟩⟩ := (Nat.card_pos_iff.mp hc).1
      exact ⟨P, hP⟩
    obtain ⟨P₁, hP₁⟩ := hex' ℓ₁ hp₁ hℓ₁
    obtain ⟨P₂, hP₂⟩ := hex' ℓ₂ hp₂ (by omega)
    -- Bézout
    have hb : (Nat.gcd ℓ₁ ℓ₂ : ℤ) = ℓ₁ * Nat.gcdA ℓ₁ ℓ₂ + ℓ₂ * Nat.gcdB ℓ₁ ℓ₂ := Nat.gcd_eq_gcd_ab ℓ₁ ℓ₂
    rw [hcop, Nat.cast_one] at hb
    refine ⟨Nat.gcdA ℓ₁ ℓ₂ • WeilDivisor.ofPoint P₁ + Nat.gcdB ℓ₁ ℓ₂ • WeilDivisor.ofPoint P₂, ?_⟩
    rw [Divisor.degree_add, Divisor.degree_zsmul, Divisor.degree_zsmul, Divisor.degree_ofPoint,
      Divisor.degree_ofPoint, hP₁, hP₂, hb]
    ring

/-- **Theorem 11.4** (Milne; Weil's Riemann hypothesis for curves over finite fields) from the Hasse–Weil bound
alone: the $L$-polynomial comes from Riemann–Roch and F. K. Schmidt's theorem, which itself follows from the bound. -/
theorem weilCurveTheorem_of_hasseWeilBound (hB : HasseWeilBound.{u, v}) : WeilCurveTheorem.{u, v} :=
  weilCurveTheorem_of_zetaLPolynomial_of_hasseWeilBound
    (zetaLPolynomial_of_schmidt (schmidtDegreeOne_of_hasseWeilBound hB)) hB

end ModularFormsKB.Milne
