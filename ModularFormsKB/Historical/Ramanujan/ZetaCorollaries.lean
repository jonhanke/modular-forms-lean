import ModularFormsKB.Historical.Ramanujan.ZetaProducts
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import ModularFormsKB.Citation
/-!
# Ramanujan, *Irregular numbers* (No. 4): Euler products with a completely multiplicative weight and their
corollaries

Ramanujan, *Collected Papers*, No. 4 (*Irregular numbers*, J. Indian Math. Soc. 5 (1913)), pp. 20–21:

* §§ 1–2, (1)–(2): for numbers `a_p` (`p` prime) with `|a_p| < 1`,
  `∏_p (1 - a_p)⁻¹ = ∑_n a(n)` and `∏_p (1 + a_p)⁻¹ = ∑_n (-1)^{Ω(n)} a(n)`, where `a(n) = ∏ a_p^{e_p}` for
  `n = ∏ p^{e_p}`. Here `a` is a completely multiplicative function `ℕ →*₀ ℂ` with `∑ |a(n)| < ∞`
  (Ramanujan's tacit hypothesis: the expansions are used only for absolutely convergent cases);
* § 4, unnumbered display and (7)–(8): `∑_{Ω(k) odd} k^{-s} = (ζ(s)² - ζ(2s))/(2ζ(s))`, with the
  examples `π²/20` (`s = 2`) and `π⁴/1260` (`s = 4`);
* § 7, (12)–(14): `∑_{k squarefree, ω(k) odd} k^{-s} = (ζ(s)² - ζ(2s))/(2ζ(s)ζ(2s))`, with the
  examples `9/(2π²)` (`s = 2`) and `15/(2π⁴)` (`s = 4`);
* § 8, (15): `∑_{k not squarefree} k^{-s} = ζ(s)(1 - 1/ζ(2s))`.

Ramanujan states the zeta identities for real `n > 1`; they are stated here for complex `s` with `Re s > 1`.
`Ω` is Mathlib's `ArithmeticFunction.cardFactors` (prime factors with multiplicity), `ω` is
`ArithmeticFunction.cardDistinctFactors`. The term `k = 0` of each sum is `0` (`0^{-s} = 0` for `s ≠ 0`, and
`a(0) = 0`).
-/

noncomputable section

open Complex
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega ArithmeticFunction.omega Real

namespace ModularFormsKB.Historical.Ramanujan

/-- **Ramanujan, No. 4, §§ 1–2, (1)–(2)** (p. 20): for a completely multiplicative
`a : ℕ →*₀ ℂ` with `∑ |a(n)| < ∞`, `∏_p (1 - a(p))⁻¹ = ∑_n a(n)` and `∏_p (1 + a(p))⁻¹ = ∑_n (-1)^{Ω(n)} a(n)`. -/
@[kb "ramanujan1927" "No. 4, §§ 1-2, (1)-(2), p. 20"]
def CompletelyMultiplicativeEulerProducts : Prop :=
  ∀ a : ℕ →*₀ ℂ, Summable (fun n ↦ ‖a n‖) →
    HasProd (fun p : Nat.Primes ↦ (1 - a p)⁻¹) (∑' n, a n) ∧
    HasProd (fun p : Nat.Primes ↦ (1 + a p)⁻¹) (∑' n, (-1 : ℂ) ^ Ω n * a n)

/-- **Ramanujan, No. 4, § 4** (pp. 20–21, the unnumbered display): for `Re s > 1`,
`∑_{Ω(k) odd} k^{-s} = (ζ(s)² - ζ(2s))/(2ζ(s))`. -/
@[kb "ramanujan1927" "No. 4, § 4, p. 20"]
def OddOmegaZetaQuotient : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasSum (fun k : ℕ ↦ if Odd (Ω k) then (k : ℂ) ^ (-s) else 0)
      ((riemannZeta s ^ 2 - riemannZeta (2 * s)) / (2 * riemannZeta s))

/-- **Ramanujan, No. 4, § 4, (7)–(8)** (pp. 20–21, the examples):
`∑_{Ω(k) odd} k^{-2} = π²/20` and `∑_{Ω(k) odd} k^{-4} = π⁴/1260`. -/
@[kb "ramanujan1927" "No. 4, § 4, (7)-(8), pp. 20-21"]
def OddOmegaValues : Prop :=
  HasSum (fun k : ℕ ↦ if Odd (Ω k) then ((k : ℂ) ^ 2)⁻¹ else 0) ((π : ℂ) ^ 2 / 20) ∧
  HasSum (fun k : ℕ ↦ if Odd (Ω k) then ((k : ℂ) ^ 4)⁻¹ else 0) ((π : ℂ) ^ 4 / 1260)

/-- **Ramanujan, No. 4, § 7, (12)** (p. 21): for `Re s > 1`,
`∑_{k squarefree, ω(k) odd} k^{-s} = (ζ(s)² - ζ(2s))/(2ζ(s)ζ(2s))`. -/
@[kb "ramanujan1927" "No. 4, § 7, (12), p. 21"]
def SquarefreeOddZetaQuotient : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasSum (fun k : ℕ ↦ if Squarefree k ∧ Odd (ω k) then (k : ℂ) ^ (-s) else 0)
      ((riemannZeta s ^ 2 - riemannZeta (2 * s)) / (2 * riemannZeta s * riemannZeta (2 * s)))

/-- **Ramanujan, No. 4, § 7, (13)–(14)** (p. 21, the examples):
`∑_{k squarefree, ω(k) odd} k^{-2} = 9/(2π²)` and `∑_{k squarefree, ω(k) odd} k^{-4} = 15/(2π⁴)`. -/
@[kb "ramanujan1927" "No. 4, § 7, (13)-(14), p. 21"]
def SquarefreeOddValues : Prop :=
  HasSum (fun k : ℕ ↦ if Squarefree k ∧ Odd (ω k) then ((k : ℂ) ^ 2)⁻¹ else 0) (9 / (2 * (π : ℂ) ^ 2)) ∧
  HasSum (fun k : ℕ ↦ if Squarefree k ∧ Odd (ω k) then ((k : ℂ) ^ 4)⁻¹ else 0) (15 / (2 * (π : ℂ) ^ 4))

/-- **Ramanujan, No. 4, § 8, (15)** (p. 21): for `Re s > 1`,
`∑_{k not squarefree} k^{-s} = ζ(s)(1 - 1/ζ(2s))`. -/
@[kb "ramanujan1927" "No. 4, § 8, (15), p. 21"]
def NonSquarefreeZetaQuotient : Prop :=
  ∀ s : ℂ, 1 < s.re →
    HasSum (fun k : ℕ ↦ if Squarefree k then 0 else (k : ℂ) ^ (-s))
      (riemannZeta s * (1 - 1 / riemannZeta (2 * s)))

/-- The completely multiplicative function `n ↦ (-1)^{Ω n} a n`. -/
private def signedHom (a : ℕ →*₀ ℂ) : ℕ →*₀ ℂ where
  toFun n := (-1 : ℂ) ^ Ω n * a n
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    simp only [ArithmeticFunction.cardFactors_mul hm hn, pow_add, map_mul]
    ring

private lemma signedHom_apply (a : ℕ →*₀ ℂ) (n : ℕ) :
    signedHom a n = (-1 : ℂ) ^ Ω n * a n := rfl

private lemma signedHom_norm (a : ℕ →*₀ ℂ) (n : ℕ) : ‖signedHom a n‖ = ‖a n‖ := by
  simp [signedHom_apply]

/-- Ramanujan, No. 4, §§ 1–2, (1)–(2). -/
@[kb "ramanujan1927" "No. 4, §§ 1-2, (1)-(2), p. 20"]
theorem completelyMultiplicativeEulerProducts : CompletelyMultiplicativeEulerProducts := by
  intro a ha
  refine ⟨EulerProduct.eulerProduct_completely_multiplicative_hasProd ha, ?_⟩
  have hb : Summable (fun n ↦ ‖signedHom a n‖) := by simpa [signedHom_norm] using ha
  have h := EulerProduct.eulerProduct_completely_multiplicative_hasProd hb
  have hf : (fun p : Nat.Primes ↦ (1 + a p)⁻¹) = fun p : Nat.Primes ↦ (1 - signedHom a p)⁻¹ := by
    funext p
    simp [signedHom_apply, ArithmeticFunction.cardFactors_apply_prime p.2]
  rw [hf]
  exact h

private lemma norm_prime_cpow_lt (s : ℂ) (hs : 1 < s.re) (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg _)
    (by simp; linarith), neg_re]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast p.2.one_lt
  · linarith

private lemma local_inv (s : ℂ) (hs : 1 < s.re) (p : Nat.Primes) :
    (1 + (p : ℂ) ^ (-s))⁻¹ = (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ / (1 - (p : ℂ) ^ (-s))⁻¹ := by
  have hp : (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 := by
    rw [show -(2 * s) = (2 : ℕ) * (-s) by push_cast; ring, cpow_nat_mul]
  have hlt := norm_prime_cpow_lt s hs p
  generalize (p : ℂ) ^ (-s) = x at hp hlt ⊢
  have h1 : 1 - x ≠ 0 := by
    intro h
    have : x = 1 := by linear_combination -h
    rw [this, norm_one] at hlt
    exact lt_irrefl _ hlt
  have h2 : 1 + x ≠ 0 := by
    intro h
    have : x = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hlt
    exact lt_irrefl _ hlt
  rw [hp, show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
  field_simp

private lemma zeta_hasSum (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun k : ℕ ↦ (k : ℂ) ^ (-s)) (riemannZeta s) := by
  have h := (summable_riemannZetaSummand hs).of_norm.hasSum
  rw [tsum_riemannZetaSummand hs] at h
  exact h

private lemma liouville_hasSum (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun k : ℕ ↦ (-1 : ℂ) ^ Ω k * (k : ℂ) ^ (-s)) (riemannZeta (2 * s) / riemannZeta s) := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hb : Summable (fun n ↦ ‖signedHom (riemannZetaSummandHom hs0) n‖) :=
    (summable_riemannZetaSummand hs).congr fun n ↦ (signedHom_norm _ n).symm
  have hP := EulerProduct.eulerProduct_completely_multiplicative_hasProd hb
  have h1 := riemannZeta_eulerProduct_hasProd hs
  have h2 := riemannZeta_eulerProduct_hasProd hs2
  have hQ := h2.div₀ h1 (riemannZeta_ne_zero_of_one_lt_re hs)
  have hf : (fun p : Nat.Primes ↦ (1 - signedHom (riemannZetaSummandHom hs0) p)⁻¹) =
      fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ / (1 - (p : ℂ) ^ (-s))⁻¹ := by
    funext p
    rw [← local_inv s hs p]
    simp [signedHom_apply, riemannZetaSummandHom, ArithmeticFunction.cardFactors_apply_prime p.2]
  rw [hf] at hP
  have hu := hP.unique hQ
  have hs' : HasSum (fun k ↦ signedHom (riemannZetaSummandHom hs0) k)
      (∑' n, signedHom (riemannZetaSummandHom hs0) n) := hb.of_norm.hasSum
  rw [hu] at hs'
  exact hs'

/-- Ramanujan, No. 4, § 4. -/
@[kb "ramanujan1927" "No. 4, § 4, p. 20"]
theorem oddOmegaZetaQuotient : OddOmegaZetaQuotient := by
  intro s hs
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have h := ((zeta_hasSum s hs).sub (liouville_hasSum s hs)).div_const 2
  convert h using 1
  · funext k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
    · by_cases ho : Odd (Ω k)
      · rw [if_pos ho, ho.neg_one_pow]; ring
      · have he : Even (Ω k) := Nat.not_odd_iff_even.mp ho
        rw [if_neg ho, he.neg_one_pow]; ring
  · field_simp

private lemma zeta_eight : riemannZeta 8 = (π : ℂ) ^ 8 / 9450 := by
  have hb : bernoulli 8 = -1 / 30 := by
    have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
    have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
    have h6 : bernoulli' 6 = 1 / 42 := by
      rw [bernoulli'_def]
      simp [Finset.sum_range_succ, Nat.choose, h5]
      norm_num
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    simp [Finset.sum_range_succ, Nat.choose, h5, h6, h7]
    norm_num
  have := riemannZeta_two_mul_nat (k := 4) (by norm_num)
  norm_num [hb, Nat.factorial] at this
  rw [this]
  ring

private lemma cpow_neg_two (k : ℕ) : (k : ℂ) ^ (-(2 : ℂ)) = ((k : ℂ) ^ 2)⁻¹ := by
  rw [show (-(2 : ℂ)) = -((2 : ℕ) : ℂ) by norm_num, cpow_neg, cpow_natCast]

private lemma cpow_neg_four (k : ℕ) : (k : ℂ) ^ (-(4 : ℂ)) = ((k : ℂ) ^ 4)⁻¹ := by
  rw [show (-(4 : ℂ)) = -((4 : ℕ) : ℂ) by norm_num, cpow_neg, cpow_natCast]

/-- Ramanujan, No. 4, § 4, (7)-(8). -/
@[kb "ramanujan1927" "No. 4, § 4, (7)-(8), pp. 20-21"]
theorem oddOmegaValues : OddOmegaValues := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · have h := oddOmegaZetaQuotient (2 : ℂ) (by simp)
    simp only [cpow_neg_two, show (2 : ℂ) * 2 = 4 by norm_num, riemannZeta_two,
      riemannZeta_four] at h
    convert h using 1
    field_simp
    norm_num
  · have h := oddOmegaZetaQuotient (4 : ℂ) (by simp)
    simp only [cpow_neg_four, show (2 : ℂ) * 4 = 8 by norm_num, zeta_eight,
      riemannZeta_four] at h
    convert h using 1
    field_simp
    norm_num

/-- Ramanujan, No. 4, § 7, (12). -/
@[kb "ramanujan1927" "No. 4, § 7, (12), p. 21"]
theorem squarefreeOddZetaQuotient : SquarefreeOddZetaQuotient := by
  intro s hs
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hz2 := riemannZeta_ne_zero_of_one_lt_re hs2
  have h := ((squarefreeZetaQuotient s hs).sub (moebiusZetaInverse s hs)).div_const 2
  convert h using 1
  · funext k
    rcases eq_or_ne k 0 with rfl | hk
    · simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
    · by_cases hq : Squarefree k
      · have hom : ω k = Ω k :=
          (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hk).mpr hq
        have hmu := ArithmeticFunction.moebius_apply_of_squarefree hq
        by_cases ho : Odd (ω k)
        · have ho' : Odd (Ω k) := hom ▸ ho
          rw [if_pos ⟨hq, ho⟩, if_pos hq]
          simp only [hmu, ho'.neg_one_pow]
          push_cast
          ring
        · have he : Even (Ω k) := Nat.not_odd_iff_even.mp (hom ▸ ho)
          rw [if_neg (fun hh ↦ ho hh.2), if_pos hq]
          simp only [hmu, he.neg_one_pow]
          push_cast
          ring
      · rw [if_neg (fun hh ↦ hq hh.1), if_neg hq,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]
        simp
  · field_simp

/-- Ramanujan, No. 4, § 7, (13)-(14). -/
@[kb "ramanujan1927" "No. 4, § 7, (13)-(14), p. 21"]
theorem squarefreeOddValues : SquarefreeOddValues := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · have h := squarefreeOddZetaQuotient (2 : ℂ) (by simp)
    simp only [cpow_neg_two, show (2 : ℂ) * 2 = 4 by norm_num, riemannZeta_two,
      riemannZeta_four] at h
    convert h using 1
    field_simp
    norm_num
  · have h := squarefreeOddZetaQuotient (4 : ℂ) (by simp)
    simp only [cpow_neg_four, show (2 : ℂ) * 4 = 8 by norm_num, zeta_eight,
      riemannZeta_four] at h
    convert h using 1
    field_simp
    norm_num

/-- Ramanujan, No. 4, § 8, (15). -/
@[kb "ramanujan1927" "No. 4, § 8, (15), p. 21"]
theorem nonSquarefreeZetaQuotient : NonSquarefreeZetaQuotient := by
  intro s hs
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have hz2 := riemannZeta_ne_zero_of_one_lt_re hs2
  have h := (zeta_hasSum s hs).sub (squarefreeZetaQuotient s hs)
  convert h using 1
  · funext k
    by_cases hq : Squarefree k
    · simp [hq]
    · simp [hq]
  · field_simp

end ModularFormsKB.Historical.Ramanujan
